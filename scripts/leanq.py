"""leanq: query Lean's language server from the shell (goals, diagnostics, tactic attempts).

Run through the wrapper `scripts/leanq`. Lines are 1-based, as editors and Lean's error
messages show them. Nothing here writes to disk: `try` edits the file only in the server's memory.

  leanq goal FILE LINE [LINE ...]     goal before and after the tactic on each line
  leanq diag FILE [START END]         errors/warnings/infos (optionally only lines START..END)
  leanq try  FILE LINE TAC [TAC ...]  replace line LINE by each TAC in turn; report the goal
                                      left after it and any messages on that line
  leanq hover FILE LINE COL           type/doc of the term at a position (COL 1-based)
  leanq selftest                      a seeded error must be reported by `diag` (exit 1 if not)

Any failure (server, protocol, unexpected reply) prints the exception and exits non-zero, so a
crash never looks like a clean file.

The file's imports must already be built (`lake build <Module>` for what it imports).
"""
import contextlib
import io
import logging
import os
import subprocess
import sys
import leanclient

# leanclient's shutdown may leave an unretrieved asyncio future ("Future exception was never
# retrieved ... Language server process exited"), which is noise and not a result.
logging.getLogger("asyncio").setLevel(logging.CRITICAL)

def _root():
    """Git toplevel of the current directory (works from a worktree); else the repo of this script."""
    try:
        return subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    except Exception:
        return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


ROOT = _root()
SEV = {1: "error", 2: "warning", 3: "info", 4: "hint"}


def show_goal(g):
    if g is None:
        return "  (no goal information here)"
    goals = g.get("goals", [])
    if not goals:
        return "  no goals"
    return "\n".join("  " + ln for gl in goals for ln in (gl + "\n").split("\n")).rstrip()


def _start(d):
    """Start of a diagnostic: `range`, else `fullRange` (Lean sends either); line 0 if neither."""
    r = d.get("range") or d.get("fullRange") or {}
    return r.get("start", {"line": 0, "character": 0})


def diags(c, f, lo=None, hi=None):
    r = c.get_diagnostics(f)  # whole file: waits for elaboration; filtered below
    items = getattr(r, "diagnostics", r)
    out = []
    for d in items:
        s = _start(d)
        if lo is not None and not (lo <= s["line"] <= (hi if hi is not None else lo)):
            continue
        out.append(f"{f}:{s['line'] + 1}:{s['character'] + 1}: "
                   f"{SEV.get(d.get('severity'), '?')}: {d['message']}")
    return out


def selftest():
    """`diag` on an in-memory file with a seeded error must report it as an error."""
    f = "Millipede/Core/Ty.lean"
    c = leanclient.LeanLSPClient(ROOT, initial_build=False)
    try:
        c.open_file(f)
        c.update_file_content(f, "theorem leanqSeeded : 1 = 2 := rfl\n")
        errs = [m for m in diags(c, f) if ": error: " in m]
    finally:
        with contextlib.redirect_stderr(io.StringIO()):
            try:
                c.close()
            except Exception:
                pass
    print("leanq selftest: " + ("ok (seeded error reported)" if errs else "FAILED (seeded error not reported)"))
    return 0 if errs else 1


def main(argv):
    if len(argv) >= 2 and argv[1] == "selftest":
        return selftest()
    if len(argv) < 3 or argv[1] in ("-h", "--help"):
        print(__doc__)
        return 2
    cmd, f = argv[1], argv[2]
    c = leanclient.LeanLSPClient(ROOT, initial_build=False)
    try:
        src = open(f"{ROOT}/{f}" if not f.startswith("/") else f).read()
        lines = src.split("\n")
        c.open_file(f)
        if cmd == "goal":
            for a in argv[3:]:
                n = int(a) - 1
                text = lines[n]
                col = len(text) - len(text.lstrip())
                print(f"== {f}:{n + 1}: {text.strip()}")
                print(" before:")
                print(show_goal(c.get_goal(f, n, col)))
                print(" after:")
                print(show_goal(c.get_goal(f, n, len(text))))
        elif cmd == "diag":
            lo = int(argv[3]) - 1 if len(argv) > 3 else None
            hi = int(argv[4]) - 1 if len(argv) > 4 else lo
            out = diags(c, f, lo, hi)
            print("\n".join(out) if out else "no messages")
        elif cmd == "try":
            n = int(argv[3]) - 1
            indent = lines[n][: len(lines[n]) - len(lines[n].lstrip())]
            for tac in argv[4:]:
                new = lines[:n] + [indent + tac] + lines[n + 1:]
                c.update_file_content(f, "\n".join(new))
                print(f"== try at {f}:{n + 1}: {tac}")
                msgs = diags(c, f, n, n)
                errs = [m for m in msgs if ": error: " in m]
                before = c.get_goal(f, n, len(indent))
                after = c.get_goal(f, n, len(indent + tac))
                if before is None and after is None:
                    print("  no goal information here (not a tactic position)")
                elif errs:
                    print("  FAILED (the goal below is Lean's error recovery, not a result):")
                    print(show_goal(after))
                else:
                    print(show_goal(after))
                for m in msgs:
                    print("  " + m.replace("\n", "\n  "))
                if not msgs:
                    print("  (no messages on this line)")
            c.update_file_content(f, src)
        elif cmd == "hover":
            h = c.get_hover(f, int(argv[3]) - 1, int(argv[4]) - 1)
            print(h["contents"]["value"] if h else "(nothing)")
        else:
            print(__doc__)
            return 2
    finally:
        with contextlib.redirect_stderr(io.StringIO()):
            try:
                c.close()
            except Exception:
                pass
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except SystemExit:
        raise
    except BaseException as e:  # never let a crash look like "no messages"
        import traceback
        traceback.print_exc()
        print(f"leanq: FAILED: {type(e).__name__}: {e}", file=sys.stderr)
        sys.exit(1)
