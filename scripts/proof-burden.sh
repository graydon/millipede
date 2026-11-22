#!/usr/bin/env bash
# Measures the proof burden of one program: the lines of program text against the text a user
# writes beyond it, which is contracts and proofs. The classifier is
# `Millipede.Meta.Burden.classify`, the one `#mp_report` uses for a module, run on the text by
# scripts/burden.lean, which defines what counts as program, contract and proof.
#
# Usage: scripts/proof-burden.sh FILE [FROM_REGEX [TO_REGEX]]
# It counts the lines of FILE from the first line matching FROM_REGEX up to, but not including,
# the next line matching TO_REGEX; the default is the whole file. FILE may be `REV:path` to
# measure a git revision, for example `HEAD~3:Tests/Lib.lean`.
set -euo pipefail
cd "$(dirname "$0")/.."
file="$1"; from="${2:-}"; to="${3:-}"
if [[ "$file" == *:* ]]; then src="$(git show "$file")"; else src="$(cat "$file")"; fi
lake build -q Millipede.Meta.Burden >/dev/null
awk -v from="$from" -v to="$to" '
  BEGIN { on = (from == "") }
  { if (!on && $0 ~ from) { on = 1; print; next }
    if (on && from != "" && to != "" && $0 ~ to) exit
    if (on) print }' <<<"$src" | lake env lean --run scripts/burden.lean
