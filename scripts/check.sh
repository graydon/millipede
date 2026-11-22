#!/usr/bin/env bash
# The full gate: builds the library and the tests, runs scripts/run-tests.sh and the audit. Exit status 0 means all passed.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
echo "== build ==";  lake build Millipede
echo "== tests ==";  lake build Tests
if [ -x scripts/run-tests.sh ]; then scripts/run-tests.sh; fi
echo "== audit =="
# Forbids sorry, axiom and native_decide outside scratch/ with a textual check; `#audit` does the
# semantic one. An axiom declaration may carry attributes, a doc comment and modifiers before the
# keyword, for example `@[simp] private axiom`, `/-- doc -/ protected axiom` or `noncomputable axiom`.
mods='((private|protected|public|noncomputable|unsafe|partial|nonrec|meta)[[:space:]]+)*'
axiom_re="(^|-/|;)[[:space:]]*(@\\[[^]]*\\][[:space:]]*)*${mods}axiom\\b"
if grep -rnE "\\bsorry\\b|${axiom_re}|native_decide" --include='*.lean' Millipede Tests Mpc.lean 2>/dev/null \
     | grep -vE '^\S+:[0-9]+:\s*--' ; then
  echo "audit: forbidden sorry/axiom/native_decide found"; exit 1
fi
if [ -x scripts/audit.sh ]; then scripts/audit.sh; fi
echo "== OK =="
