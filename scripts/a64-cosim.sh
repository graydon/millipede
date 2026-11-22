#!/usr/bin/env bash
# Compares the arm64 instruction model with the CPU this runs on. Random instruction sequences
# from the modelled subset are encoded by Millipede's encoder and run natively by a small C
# harness; registers, sp, NZCV, a 512-byte memory window and faults must equal what the Lean model
# (`A64.exec`) computes. The generator and the model run are in Tests/A64CoSim/Main.lean, the
# harness in Tests/A64CoSim/harness.c.
#
#   scripts/a64-cosim.sh              run (A64_COSIM_SEED and A64_COSIM_N set the seed and case count;
#                                     the seed is the current time unless given, and is printed)
#   scripts/a64-cosim.sh --selftest   require each seeded bug to be caught
#
# About one case in eight makes `read`, `write` and `exit` system calls, in a child process with
# pipes for standard input and output. Exit status 0 means every case agreed (or the host is not
# arm64 and the run was skipped); in the self-test it means every bug was caught. The seeded bugs
# are numbered. Model bugs: 1 `subs` carry inverted, 2 32-bit shift amount taken mod 64, 3 `ldrb`
# sign-extends, 7 no stack-alignment check, 8 the result of a system call one too large. Every bug number also runs the encoder bug of that number in Tests/A64.lean: 4 swaps the
# source registers of a register add or subtract, 5 drops the flag-setting bit of an immediate
# add or subtract, and 6 keeps only the low eight bits of an unscaled store offset.
set -euo pipefail
cd "$(dirname "$0")/.."
SEED="${A64_COSIM_SEED:-$(date +%s)}"   # a new seed each run unless given; printed below
N="${A64_COSIM_N:-20000}"
if [ "$(uname -m)" != aarch64 ]; then
  echo "a64-cosim: SKIPPED (host is $(uname -m), not aarch64)"; exit 0
fi
echo "a64-cosim: seed $SEED"
lake build a64cosim >/dev/null
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
gcc -O1 -fno-stack-protector -o "$tmp/run" Tests/A64CoSim/harness.c Tests/A64CoSim/stub.S
EXE=".lake/build/bin/a64cosim"

if [ "${1:-}" = "--selftest" ]; then
  ok=0
  for bug in 1 2 3 4 5 6 7 8; do
    "$EXE" gen "$tmp/c$bug" "$tmp/e$bug" "$SEED" 1000 "$bug"
    if "$tmp/run" "$tmp/c$bug" "$tmp/e$bug" > "$tmp/log$bug" 2>&1; then
      echo "a64-cosim selftest: seeded bug $bug NOT caught"; ok=1
    else
      echo "a64-cosim selftest: caught seeded bug $bug ($(tail -1 "$tmp/log$bug"))"
    fi
  done
  exit "$ok"
fi

"$EXE" gen "$tmp/cases" "$tmp/expect" "$SEED" "$N"
"$tmp/run" "$tmp/cases" "$tmp/expect"
