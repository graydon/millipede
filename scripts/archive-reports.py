#!/usr/bin/env python3
"""Top up doc/history/reports/ from the agent transcripts of the orchestrator session.

Usage:  scripts/archive-reports.py [--session DIR] [--dry-run]

DIR is the session directory (default: the one named in SESSION below) holding `subagents/`
(agent-<id>.jsonl and agent-<id>.meta.json).  One run:
  * refreshes an archived entry whose report was missing (or that was resumed and has since sent
    more reports): the whole file is rewritten with every report, dated, in order;
  * adds a numbered file for every agent that is not archived yet and has finished (numbers
    continue the sequence, in start order);
  * skips agents still running (meta `finished` not true and no hand-back yet) and names them in
    README.md ("Not archived:");
  * updates the index tables of README.md.
A second run changes nothing.  See doc/history/reports/README.md for what is included.
"""
import argparse, glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "doc/history/reports")
SESSION = os.path.expanduser(
    "~/.claude/projects/-workspaces-millipede/573cc8a4-298d-42bc-a994-ed6af922f09e")
BRIEF_LINES = 150


def scrub(t):
    t = t.replace(os.path.expanduser("~"), "<home>").replace("/home/dev", "<home>")
    # the patterns are assembled so that this file does not itself contain what it scrubs
    first, mail, users = "gray" + "don", "po" + "box", "/Us" + "ers/"
    t = re.sub(first + r" hoare", "<owner>", t, flags=re.I)
    t = re.sub(r"[\w.+-]+@" + mail + r"\.com", "<owner-email>", t, flags=re.I)
    t = re.sub(first, "<owner>", t, flags=re.I)
    t = re.sub(mail, "<mail>", t, flags=re.I)
    return t.replace(users, "<users>/")


def text_of(content):
    if isinstance(content, str):
        return content
    return "\n".join(b.get("text", "") for b in content if b.get("type") == "text")


def load_agent(path):
    aid = os.path.basename(path)[len("agent-"):-len(".jsonl")]
    meta = {}
    mp = path[:-len(".jsonl")] + ".meta.json"
    if os.path.exists(mp):
        meta = json.load(open(mp))
    ev = [json.loads(l) for l in open(path) if l.strip()]
    brief = text_of(ev[0]["message"]["content"]) if ev else ""
    model, reports, last_text = "unknown", [], ""
    for e in ev:
        m = e.get("message")
        if e.get("type") != "assistant" or not isinstance(m, dict):
            continue
        model = m.get("model", model) if m.get("model") != "<synthetic>" else model
        if isinstance(m.get("content"), list):
            for b in m["content"]:
                if b.get("type") == "tool_use" and b.get("name") == "SubagentHandback":
                    reports.append((e["timestamp"], b["input"].get("message", "")))
                elif b.get("type") == "text" and b["text"].strip():
                    last_text = b["text"].strip()
    return dict(id=aid, meta=meta, ev=ev, brief=brief, model=model, reports=reports,
                last_text=last_text, start=ev[0]["timestamp"], end=ev[-1]["timestamp"],
                finished=bool(meta.get("finished")) or bool(reports))


def stamp(ts):
    return ts[:19].replace("T", " ")


def slug(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def branch_of(brief):
    m = re.search(r"git checkout -b \S+ (\S+)", brief) or re.search(r"branch `([^`]+)`", brief)
    return m.group(1).strip("`") if m else "not stated"


def group_of(desc):
    d = desc.lower()
    if d.startswith("phase 4"):
        return "Phase 4"
    if "usability" in d:
        return "usability"
    if any(w in d for w in ("tutorial", "docs", "archive", "orientation", "documentation")):
        return "Docs"
    return "Other"


def outcome(text):
    for line in text.splitlines():
        line = line.strip().lstrip("#").strip().replace("**", "")
        if line:
            s = re.split(r"(?<=[.!?])\s", line, maxsplit=1)[0]
            return (s[:217] + "...") if len(s) > 220 else s
    return "(empty report)"


def render(num, a, stage):
    lines = a["brief"].splitlines()
    brief = "\n".join(lines[:BRIEF_LINES])
    if len(lines) > BRIEF_LINES:
        brief += f"\n[... {len(lines) - BRIEF_LINES} more lines not archived]"
    n = len(a["reports"])
    src = "SubagentHandback" if n else "lastmsg"
    out = [f"# {num:03d} {stage}", "",
           f"- Started (UTC): {stamp(a['start'])}", f"- Ended (UTC): {stamp(a['end'])}",
           f"- Model: {a['model']}", f"- Stage: {stage}", "- Run: direct agent",
           f"- Branch named in brief: {branch_of(a['brief'])}",
           f"- Agent id: {a['id']}; report source: {src}"]
    if n:
        out.append(f"- Reports: {n}")
    out += ["", "## Task brief", "", "```", brief, "```", ""]
    if n == 0:
        out += ["## Final report", "",
                "No final report: the agent produced no hand-back before it ended. "
                "Its last assistant message was:", "", a["last_text"]]
    for i, (ts, msg) in enumerate(a["reports"], 1):
        out += [f"## Final report {i} of {n} ({stamp(ts)} UTC)" if n > 1 else "## Final report",
                "", msg.strip(), ""]
    return scrub("\n".join(out).rstrip() + "\n")


def parse_existing():
    ex = {}
    for p in sorted(glob.glob(os.path.join(OUT, "[0-9][0-9][0-9]-*.md"))):
        t = open(p, encoding="utf8").read()
        m = re.search(r"Agent id: (\w+); report source: (\w+)", t)
        if not m:
            continue
        r = re.search(r"^- Reports: (\d+)", t, re.M)
        n = int(r.group(1)) if r else (1 if m.group(2) == "SubagentHandback" else 0)
        ex[m.group(1)] = dict(num=int(os.path.basename(p)[:3]), path=p, source=m.group(2), nreports=n)
    return ex


def parse_readme(text):
    """-> (preamble, [[title, [rows]]]); a row is [num, line]."""
    parts = re.split(r"^## ", text, flags=re.M)
    groups = []
    for g in parts[1:]:
        title = re.sub(r" \(\d+\)\s*$", "", g.splitlines()[0])
        rows = [[int(l.split("|")[1]), l] for l in g.splitlines() if re.match(r"\| \d{3} \|", l)]
        groups.append([title, rows])
    return parts[0], groups


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--session", default=SESSION)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    agents = {}
    for p in glob.glob(os.path.join(args.session, "subagents", "agent-*.jsonl")):
        a = load_agent(p)
        agents[a["id"]] = a
    ex = parse_existing()
    readme_p = os.path.join(OUT, "README.md")
    pre, groups = parse_readme(open(readme_p, encoding="utf8").read())
    rows = {r[0]: (g, r) for g in groups for r in g[1]}
    nextnum = max([e["num"] for e in ex.values()] + [0]) + 1
    changed, running = [], []

    def write(path, text):
        old = open(path, encoding="utf8").read() if os.path.exists(path) else None
        if old != text:
            changed.append(os.path.relpath(path, ROOT))
            if not args.dry_run:
                open(path, "w", encoding="utf8").write(text)

    def row(num, a, stage, fname):
        d = stamp(a["start"])[:10]
        o = outcome(scrub(a["reports"][0][1] if a["reports"] else "")) if a["reports"] else \
            "(no final report)"
        return f"| {num:03d} | {d} | {stage} | {o.replace('|', chr(92) + '|')} | [{fname}]({fname}) |"

    # refresh archived entries that gained reports
    for aid, e in ex.items():
        a = agents.get(aid)
        if a and len(a["reports"]) > e["nreports"]:
            stage = re.search(r"^- Stage: (.*)$", open(e["path"], encoding="utf8").read(), re.M).group(1)
            write(e["path"], render(e["num"], a, stage))
            g, r = rows[e["num"]]
            r[1] = row(e["num"], a, stage, os.path.basename(e["path"]))
    # archived files that lack an index row, or whose row still says "no final report"
    for aid, e in sorted(ex.items(), key=lambda kv: kv[1]["num"]):
        if e["num"] in rows:
            if not (e["nreports"] and "(no final report" in rows[e["num"]][1][1]):
                continue
            rows[e["num"]][0][1].remove(rows[e["num"]][1])      # stale row: rebuilt below
        t = open(e["path"], encoding="utf8").read()
        stage = re.search(r"^- Stage: (.*)$", t, re.M).group(1)
        d = re.search(r"^- Started \(UTC\): (\S+)", t, re.M).group(1)
        rep = t.split("\n## Final report", 1)[1].split("\n", 1)[1] if "\n## Final report" in t else ""
        rep = rep.split("\n## Final report", 1)[0]
        o = outcome(rep) if e["nreports"] else "(no final report)"
        fname = os.path.basename(e["path"])
        title = group_of(stage)
        g = next((g for g in groups if g[0] == title), None)
        if g is None:
            g = [title, []]
            groups.append(g)
        r = [e["num"], f"| {e['num']:03d} | {d} | {stage} | {o.replace('|', chr(92) + '|')} | [{fname}]({fname}) |"]
        g[1].append(r)
        rows[e["num"]] = (g, r)
    # new agents, in start order
    new = sorted((a for i, a in agents.items() if i not in ex), key=lambda a: (a["start"], a["id"]))
    for a in new:
        if not a["finished"]:
            running.append(a)
            continue
        stage = a["meta"].get("description") or a["id"]
        num, nextnum = nextnum, nextnum + 1
        fname = f"{num:03d}-{slug(stage)}.md"
        write(os.path.join(OUT, fname), render(num, a, stage))
        title = group_of(stage)
        g = next((g for g in groups if g[0] == title or g[0].startswith(title)), None)
        if g is None:
            g = [title, []]
            groups.append(g)
        g[1].append([num, row(num, a, stage, fname)])
    # README
    if running:
        names = ", ".join(f"agent {a['id']} ({a['meta'].get('description', '?')})" for a in running)
        na = f"Not archived: {names}, still running at the last extraction. Every other transcript and journal result is archived (see the tables; entries marked \"no final report\" are agents that were interrupted)."
    else:
        na = "Not archived: none. Every transcript and journal result is archived (entries marked \"no final report\" were interrupted)."
    if re.search(r"^Not archived:.*$", pre, re.M):
        pre = re.sub(r"^Not archived:.*$", lambda m: na, pre, flags=re.M)
    else:
        pre = pre.rstrip() + "\n\n" + na + "\n\n"
    body = ""
    for title, rs in groups:
        rs.sort(key=lambda r: r[0])
        body += f"## {title} ({len(rs)})\n\n| # | Date | Stage | Outcome | File |\n|---|---|---|---|---|\n"
        body += "\n".join(r[1] for r in rs) + "\n\n"
    write(readme_p, pre + body.rstrip() + "\n")
    print(("would change" if args.dry_run else "changed") + f": {len(changed)} file(s)")
    for c in changed:
        print("  " + c)
    for a in running:
        print(f"skipped (still running): {a['id']} {a['meta'].get('description', '')}")


if __name__ == "__main__":
    sys.exit(main())
