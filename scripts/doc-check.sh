#!/usr/bin/env bash
# The documentation check. It only greps and runs no Lean. For now it is warn-only: it prints its
# findings and always exits 0, and scripts/run-tests.sh runs it as a stage that never fails the
# gate. It checks the documents README.md, doc/open-claims.md, doc/status.md, doc/roadmap.md,
# doc/measurements.md, doc/reference/*.md, doc/design/*.md, doc/guide/*.md, doc/phases/README.md
# and doc/history/README.md, those that exist; the rest of doc/history/ is never checked.
#
#  (a) names: every backticked dotted Lean identifier (`Namespace.name`) and every file path cited
#      in a checked document exists in the tree. A path is tried as written, under Millipede/,
#      and relative to the document. An identifier is found when its last component is declared
#      (`def`, `theorem`, `structure`, `mp def`, `mp instance`, … `X.y.last`), or, when the last
#      component is a name that `mp def`, `mp program` or `deriving Data` generates (`.spec`,
#      `.safe`, …), when the component before it is declared. Placeholders whose first component
#      is one letter (`f.spec`, `M.f.spec`, `I.h`) are not checked. An option (`register_option`),
#      a module (`Millipede.Lib.Units` as a file), a constructor (`| addNuw`) and a name under
#      `Std.` or `Lean.` are also accepted. Text between `<!-- doc-check: off -->` and
#      `<!-- doc-check: on -->` is not checked for names, which allows planned or deliberately
#      absent names.
#  (b) links: every relative Markdown link of the checked documents resolves.
#  (c) sizes: line caps per document (README 120, CLAUDE.md 150, roadmap 150, status 250,
#      open-claims 170, measurements 150, tour 900, tutorial 500, a design file 250; the decision
#      log design/decisions.md 400, as it only grows; design/limits.md 170, so that the limits of
#      the claim stay short enough to read whole).
#  (d) section references: any `§<digit>` citation outside doc/history/ draws a warning, because
#      a citation names a file and a heading. The old numbers are mapped in
#      doc/history/section-map.md.
#  (e) surface coverage: every command or term `syntax`/`elab` token, `register_option` and
#      attribute declared in Millipede/Meta/ is mentioned in the surface reference, which is
#      doc/reference/surface.md and the parts it indexes (doc/reference/*.md except the glossary).
#  (f) tutorial excerpts: each ```lean block of doc/guide/tutorial.md that starts with a marker
#      `-- [tutorial:NAME]` is the text of Tests/Tutorial.lean from that marker to its end marker.
#
# Usage: scripts/doc-check.sh [FILE.md ...]   (default: the checked documents above)
set -uo pipefail
cd "$(dirname "$0")/.."

if [ "$#" -gt 0 ]; then
  docs=("$@")
else
  docs=()
  for f in README.md doc/open-claims.md doc/status.md doc/roadmap.md doc/measurements.md \
           doc/reference/*.md doc/design/*.md doc/guide/*.md doc/phases/README.md doc/history/README.md; do
    [ -f "$f" ] && docs+=("$f")
  done
fi

warn=0
say() { echo "doc-check: $*"; warn=$((warn + 1)); }

# The names that the elaborators generate after a declared name: `f.spec` exists when `f` does.
gen='spec|safe|post|reach|events_reach|initRel|stepRel|regOk|binI|stI|exp|wf|wf_eq|SafeGoal|SpecGoal|Safe|analysed|relaxed|expR|fn|fnRef|req|exp_denote|exp_run|exp_denoteM|inv|inv_init|inv_step|invariant|InvInitGoal|InvStepGoal|generic|scale_eq|instData|lens|lens_get|lens_set|ctor|ctor_build|mpMatch|mpMatch_eq|prog|impl|noCalls|syms|init'
decl='(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|mp def|mp program|mp instance|mp module|mp unit|mp dimension|mp capability|mp extern( noreturn)? "[^"]*")'

declared() {  # is the name $1 (one component) declared in a .lean file?
  local n
  n=$(printf '%s' "$1" | sed 's/[][\.*^$?+(){}|]/\\&/g')
  rg -q -g '*.lean' --no-ignore -e "${decl} +([A-Za-z0-9_.!?'₀-₉]*\.)?${n}([^A-Za-z0-9_!?'₀-₉]|$)" \
    Millipede Tests Mpc.lean scripts 2>/dev/null
}

resolve_path() {  # $1 path, $2 document: exists as written, under Millipede/, or next to the doc?
  local p="${1%/}" d
  d=$(dirname "$2")
  [ -e "$p" ] || [ -e "Millipede/$p" ] || [ -e "$d/$p" ]
}

# (a) names and paths
for doc in "${docs[@]}"; do
  # the checked text: no fenced code blocks, no doc-check: off regions
  body=$(awk '/<!-- doc-check: off -->/{o=1} /<!-- doc-check: on -->/{o=0; next} /^```/{c=!c; next} !c && !o' "$doc")
  spans=$(grep -oE '`[^`]+`' <<< "$body" | tr -d '`' | sort -u)
  while IFS= read -r s; do
    [ -z "$s" ] && continue
    case "$s" in *" "*) continue ;; esac
    if [[ "$s" =~ ^[A-Za-z0-9_./-]+\.(lean|sh|md|c|py|toml)$ ]] || [[ "$s" =~ ^(Millipede|Tests|scripts|doc)/ ]]; then
      case "$s" in *"<"*) continue ;; esac  # a placeholder
      resolve_path "$s" "$doc" || say "$doc: path \`$s\` does not exist"
      continue
    fi
    [[ "$s" =~ ^[A-Za-z_][A-Za-z0-9_\'!?.₀-₉κφω]*$ ]] || continue
    [[ "$s" == *.* ]] || continue
    first=${s%%.*}
    [ "${#first}" -le 1 ] && continue
    case "$s" in Std.*|Lean.*|HMul.*|HAdd.*|HSub.*|OfNat.*|Nat.*|List.*|UInt8.*|UInt64.*|Int.*|Vector.*|Except.*|Option.*|BitVec.*|ByteArray.*|Decidable.*) continue ;; esac
    rg -q -g '*.lean' -e "^\s*namespace ([A-Za-z0-9_.]*\.)?${s//./\\.}\s*$" Millipede 2>/dev/null && continue
    rg -q -g '*.lean' -F "register_option $s " Millipede 2>/dev/null && continue
    [ -f "${s//.//}.lean" ] && continue
    last=${s##*.}; last=${last%!}; last=${last%\?}
    rest=${s%.*}; prev=${rest##*.}
    if declared "$last"; then continue; fi
    rg -q -g '*.lean' -e "^\s*\| *${last}\b" Millipede 2>/dev/null && continue
    rg -q -g '*.lean' -e "^\s+${last} *:[^=]" Millipede/Core 2>/dev/null && continue  # a structure or class field
    if [[ "$last" =~ ^(${gen})$ ]] && declared "$prev"; then continue; fi
    say "$doc: identifier \`$s\` not found as a declaration"
  done <<< "$spans"
  # unbackticked paths in prose and tables
  for p in $(sed -E 's/`[^`]*`//g; s/\]\([^)]*\)/]/g' \
             <<< "$body" | grep -oE '(Millipede|Tests|scripts)/[A-Za-z0-9_./-]*[A-Za-z0-9_/]' | sort -u); do
    resolve_path "$p" "$doc" || say "$doc: path $p does not exist"
  done
done

# (b) relative links
for doc in "${docs[@]}"; do
  d=$(dirname "$doc")
  for t in $(grep -oE '\]\([^)[:space:]]+\)' "$doc" | sed -E 's/^\]\(//; s/\)$//' | sort -u); do
    case "$t" in http:*|https:*|mailto:*|\#*) continue ;; esac
    t=${t%%#*}
    [ -e "$d/$t" ] || say "$doc: link ($t) does not resolve"
  done
done

# (c) size caps
cap() {  # file, cap
  [ -f "$1" ] || return 0
  local n; n=$(wc -l < "$1")
  [ "$n" -le "$2" ] || say "$1: $n lines, cap $2"
}
cap README.md 120; cap CLAUDE.md 150; cap doc/roadmap.md 150; cap doc/status.md 250
cap doc/open-claims.md 170; cap doc/measurements.md 150; cap doc/guide/tour.md 900
cap doc/guide/tutorial.md 500
for f in doc/design/*.md; do
  case "$f" in doc/design/decisions.md) cap "$f" 400 ;; doc/design/limits.md) cap "$f" 170 ;; *) cap "$f" 250 ;; esac
done

# (f) tutorial excerpts: each ```lean block of doc/guide/tutorial.md whose first line is
#     `-- [tutorial:NAME]` equals Tests/Tutorial.lean from that line up to `-- [/tutorial:NAME]`.
if [ -f doc/guide/tutorial.md ] && [ -f Tests/Tutorial.lean ]; then
  while IFS= read -r m; do say "$m"; done < <(python3 - <<'EOF'
import re
md = open('doc/guide/tutorial.md').read(); src = open('Tests/Tutorial.lean').read()
for body, name in re.findall(r'```lean\n(-- \[tutorial:([\w-]+)\]\n.*?)```', md, re.S):
    m = re.search(r'(-- \[tutorial:%s\]\n.*?)-- \[/tutorial:%s\]' % (re.escape(name), re.escape(name)), src, re.S)
    if not m: print(f'doc/guide/tutorial.md: excerpt {name} is not marked in Tests/Tutorial.lean')
    elif m.group(1) != body: print(f'doc/guide/tutorial.md: excerpt {name} differs from Tests/Tutorial.lean')
EOF
)
fi

# (e) surface coverage: the Meta/ declarations mentioned in the surface reference (surface.md and
# its parts, which are all doc/reference/*.md except glossary.md)
surf=doc/reference/surface.md
surfAll=$(ls doc/reference/*.md 2>/dev/null | grep -v '/glossary\.md$' | xargs cat 2>/dev/null)
if [ -f "$surf" ]; then
  # options and attributes, by name
  for n in $(rg --no-filename -o '^register_option [A-Za-z0-9_.]+' Millipede/Meta | awk '{print $2}') \
           $(rg --no-filename -o '^register_label_attr [A-Za-z0-9_]+' Millipede/Meta | awk '{print $2}') \
           $(rg --no-filename -o 'registerTagAttribute `[A-Za-z0-9_]+' Millipede/Meta | sed 's/.*`//'); do
    grep -qF -- "$n" <<< "$surfAll" || say "$surf: \`$n\` (Millipede/Meta) is not mentioned in the surface reference"
  done
  # syntax and elab: the first string token; after mpKw it is the keyword following `mp`
  while IFS= read -r line; do
    tok=$(sed -E 's/^[^"]*"([^"]*)".*/\1/' <<< "$line" | sed -E 's/^ +| +$//g')
    [ -z "$tok" ] && continue
    if grep -q 'mpKw' <<< "$line"; then tok="mp $tok"; fi
    grep -qF -- "$tok" <<< "$surfAll" || say "$surf: syntax \`$tok\` (Millipede/Meta) is not mentioned in the surface reference"
  done < <(rg --no-filename '^\s*(syntax|elab)[ :(].*"' Millipede/Meta)
fi

# (d) section-number references: citations name a file and a heading (`doc/design/obligations.md`)
# and never a section sign and a number. Any such reference outside doc/history/ draws a warning;
# the old numbers are mapped by doc/history/section-map.md.
refs=$(rg -n --no-ignore -g '!doc/history/**' -g '!scratch/**' -g '!.lake/**' -g '!.claude/**' \
          -g '!.git/**' '§[0-9]' . 2>/dev/null || true)
if [ -n "$refs" ]; then
  while IFS= read -r line; do say "section-number reference (cite the file and heading instead): ${line:0:140}"; done <<< "$refs"
fi

echo "doc-check: ${#docs[@]} document(s) checked, $warn finding(s) (warn-only)"
exit 0
