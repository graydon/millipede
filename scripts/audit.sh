#!/usr/bin/env bash
# The semantic audit. It runs `#audit` over the whole library and the assumption-ledger skeleton,
# prints the axioms of the two headline theorems, and checks the open claims: every `.Statement`
# definition must be the type of some `theorem` in Millipede/ (which `#audit` guarantees has no
# sorry or axiom) or be an entry of the open-claims list in doc/open-claims.md, a line of the form
# "- `X.Statement` — file — what blocks it". A name mentioned elsewhere in that file does not
# count. Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"

lake build Millipede Millipede.Meta.Audit >/dev/null

echo "-- #audit (all of Millipede) --"
out=$(lake env lean --stdin <<'LEAN' 2>&1
import Millipede
import Millipede.Meta.Audit
#audit
#audit_ledger
LEAN
) && rc=0 || rc=$?
echo "$out"
if [ "$rc" -ne 0 ] || grep -q 'error' <<<"$out"; then
  echo "audit: #audit reported errors"; exit 1
fi

echo "-- headline theorems: CompileSound.Statement for each target, and their axioms --"
# Each headline theorem has exactly the statement's type at its target, which the kernel checks,
# and depends only on propext, Classical.choice, Quot.sound and the axioms `bv_decide` adds for
# encode/decode lemmas (`…._native.bv_decide.ax_…`).
hl=$(lake env lean --stdin <<'LEAN' 2>&1
import Millipede
open Millipede
example : CompileSound.Statement compile x64Linux := compile_sound
example : CompileSound.Statement compile arm64Linux := compile_sound_arm64
#print axioms Millipede.compile_sound
#print axioms Millipede.compile_sound_arm64
LEAN
) && rc=0 || rc=$?
if [ "$rc" -ne 0 ] || grep -q 'error' <<<"$hl"; then echo "$hl"; echo "audit: headline check failed"; exit 1; fi
bad=$(tr ',[]' '\n\n\n' <<<"$hl" | sed -E 's/.*depends on axioms: *//; s/^ +//' | grep -vE '^$|^(propext|Classical\.choice|Quot\.sound)$|\._native\.bv_decide\.ax_[0-9_]+$' || true)
if [ -n "$bad" ]; then echo "$hl"; echo "audit: a headline depends on other axioms: $bad"; exit 1; fi
echo "proved: CompileSound.Statement compile x64Linux (Millipede.compile_sound)"
echo "proved: CompileSound.Statement compile arm64Linux (Millipede.compile_sound_arm64)"
echo "  axioms: propext, Classical.choice, Quot.sound, bv_decide (encode/decode lemmas: $(grep -oE '[A-Za-z0-9_.]+\._native' <<<"$hl" | sed 's/\._native//' | sort -u | tr '\n' ' '))"

echo "-- seeded translation bugs: \`mp.selftest.doMutant\` only in Tests/Differential/DoFuncs.lean --"
# The option changes the Core term that `mp def` produces, which seeds a bug into the `do`
# translation for the differential self-test. The elaborator refuses it outside that module
# (`doMutant` in Meta/Elab.lean, with the refusal tested in Tests/DoNotation.lean). This check
# refuses any other file that sets it, except under `#guard_msgs`, and shows that it finds a
# seeded use.
mutant_uses() {
  grep -rlE 'set_option[[:space:]]+mp\.selftest\.doMutant' --include='*.lean' "$@" 2>/dev/null \
    | grep -vE '(^|/)(Tests/Differential/DoFuncs|Millipede/Meta/Elab)\.lean$' \
    | while IFS= read -r f; do
        awk '/set_option[[:space:]]+mp\.selftest\.doMutant/ && prev !~ /^#guard_msgs in$/ { bad = 1 } { prev = $0 }
             END { exit !bad }' "$f" && echo "$f"
      done || true
}
bad=$(mutant_uses Millipede Tests Mpc.lean)
if [ -n "$bad" ]; then echo "audit: mp.selftest.doMutant is set outside Tests/Differential/DoFuncs.lean: $bad"; exit 1; fi
seed="$(mktemp -d)"; mkdir -p "$seed/Tests"
printf 'set_option mp.selftest.doMutant "break-ignored" in\n' > "$seed/Tests/Seeded.lean"
found=$(cd "$seed" && mutant_uses Tests); rm -rf "$seed"
if [ -z "$found" ]; then echo "audit: the mp.selftest.doMutant check misses a seeded use"; exit 1; fi
echo "audit: mp.selftest.doMutant only in Tests/Differential/DoFuncs.lean (a seeded use is found)"

echo "-- open claims (doc/open-claims.md) --"
cat doc/open-claims.md
missing=0
# the entries of the open-claims list: "- `name` — …"
listed=$(grep -oE '^- `[A-Za-z0-9_.'"'"']+\.Statement` —' doc/open-claims.md | sed -E 's/^- `([^`]+)` —$/\1/' || true)
while IFS= read -r name; do
  [ -z "$name" ] && continue
  if grep -rqE "^\s*theorem [A-Za-z0-9_.']+ *: *([A-Za-z0-9_]+\.)*${name//./\\.}( |$)" \
       --include='*.lean' Millipede; then
    echo "proved: $name"; continue
  fi
  if grep -qxF "$name" <<<"$listed"; then echo "open (listed): $name"; continue; fi
  echo "audit: '$name' is a .Statement def but is neither proved nor an entry of the open-claims list of doc/open-claims.md"
  missing=1
done < <(grep -rhoE '^\s*(private |protected )?(noncomputable )?def [A-Za-z0-9_.'"'"']+\.Statement\b' \
           --include='*.lean' Millipede Tests 2>/dev/null \
         | sed -E 's/.* def ([A-Za-z0-9_.'"'"']+)$/\1/; s/^def //' | sort -u)
[ "$missing" -eq 0 ] || exit 1
echo "audit: ok"
