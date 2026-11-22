#!/usr/bin/env bash
# The inner-loop tier. It builds the library and a small subset of the test modules, chosen for
# low cost and broad coverage: Core semantics and checker, the elaborator, `lower` and the Flat
# interpreter, `linearize`, the whole pipeline `compile` run in the x64 model against the source,
# the x64 encoder, the ELF writer, data layout, contracts, program invariants, the clients of the
# pool and allocator modules, the analyser, quantities, and the tutorial's program, so that the
# code and messages of doc/guide/tutorial.md stay true. It prints the modules it skipped.
# scripts/check.sh is the full gate: all test modules, the differential, cosim and mpc runs with
# their seeded-bug self-tests, and the audit.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
quick=(Tests.Core Tests.MpDef Tests.Lower Tests.Lin Tests.Top Tests.X64 Tests.Elf Tests.Layout
  Tests.Contracts Tests.ProgramInv Tests.Lib Tests.Analysis Tests.Units Tests.Tutorial Tests.Driver)
s=$(date +%s)
lake build Millipede "${quick[@]}"
echo "quick: Millipede and ${quick[*]} built in $(( $(date +%s) - s ))s"
skipped=$(grep '^import ' Tests.lean | sed 's/^import //' | grep -vxF -f <(printf '%s\n' "${quick[@]}") \
  | tr '\n' ' ')
echo "quick: skipped (scripts/check.sh builds them): $skipped"
echo "quick: skipped scripts/run-tests.sh (differential, cosim, mpc, ELF, encoder, layout checks)"
