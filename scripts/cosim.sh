#!/usr/bin/env bash
# Compares the x64 instruction model with qemu. Random instruction sequences from the modelled
# subset are encoded by Millipede's encoder into harness ELFs that write the register state
# (registers, flags, scratch memory) with `write`. The dump produced under qemu-x86_64 must equal,
# byte for byte, the dump of the Lean model (`X64.exec`). Tests/CoSim/Main.lean holds the
# generator, the coverage and the way undefined flags are avoided.
#
#   scripts/cosim.sh [SEED]              run (COSIM_CHUNKS and COSIM_PER set the size)
#   scripts/cosim.sh --selftest [SEED]   seed encoder and model bugs and require each to be caught
#
# The seed is the argument, else $COSIM_SEED, else the current time, so each run of the gate tests
# new sequences; it is printed, and passing it again repeats the run. Exit status 0 means every
# dump agreed; in the self-test it means every bug was caught. The bugs are applied by `cosim gen
# ... <bug>`: 1 the encoder swaps the two registers of `add/sub/...` reg,reg; 2 `setb` is encoded
# as `setae`; 3 `shl r, cl` as `shr r, cl`; 4 the sign bit of a `lea` displacement is cleared; 5
# the model's standard input lacks its first byte, which checks the `read` system calls; 6 the
# model inverts the carry after `sub` and `cmp`; 7 the model masks a shift count to 7 bits instead
# of 6; 8 the model's `div` remainder is one too large; 9 the encoder gives a SIB byte scale 2; 10 a byte-store immediate one too large. `cosim gen` fails when a sequence set lacks
# one of the addressing forms the selector emits.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
selftest=0
[ "${1:-}" = "--selftest" ] && { selftest=1; shift; }
SEED="${1:-${COSIM_SEED:-$(date +%s)}}"
echo "cosim: seed $SEED"
CHUNKS="${COSIM_CHUNKS:-12}"
PER="${COSIM_PER:-200}"
lake build cosim >/dev/null
EXE=".lake/build/bin/cosim"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# compare <dir> <chunks>: run each ELF under qemu; return 1 on any difference.
compare() {
  local dir="$1" n="$2" bad=0 k
  for k in $(seq 0 $((n - 1))); do
    if ! "$QEMU" "$dir/cosim.$k.elf" 2>/dev/null < "$dir/cosim.$k.in" | cmp -s - "$dir/cosim.$k.expect"; then
      local off
      off="$("$QEMU" "$dir/cosim.$k.elf" 2>/dev/null < "$dir/cosim.$k.in" | cmp - "$dir/cosim.$k.expect" 2>&1 | sed -n 's/.*differ: byte \([0-9]*\),.*/\1/p')"
      if [ -n "$off" ]; then
        local sq=$(( (off - 1) / 216 )) w=$(( ((off - 1) % 216) / 8 ))
        echo "cosim: chunk $k: sequence $sq differs at dump word $w (0-14 registers, 15-18 flags o b e s, 19-26 slots)"
        [ "$dir" = "$tmp/real" ] && "$EXE" show "$SEED" "$k" "$sq" "$PER" | head -60
      else
        echo "cosim: chunk $k: output length differs or qemu failed"
      fi
      bad=1
    fi
  done
  return "$bad"
}

if [ "$selftest" = 1 ]; then
  ok=0
  for bug in 1 2 3 4 5 6 7 8 9 10; do
    "$EXE" gen "$tmp/bug$bug" "$SEED" 1 100 "$bug"
    if compare "$tmp/bug$bug" 1 >/dev/null 2>&1; then
      echo "cosim selftest: seeded bug $bug NOT caught"; ok=1
    else
      echo "cosim selftest: caught seeded bug $bug"
    fi
  done
  exit "$ok"
fi

"$EXE" gen "$tmp/real" "$SEED" "$CHUNKS" "$PER"
if compare "$tmp/real" "$CHUNKS"; then
  echo "cosim: OK ($((CHUNKS * PER)) random sequences agree with qemu)"
else
  exit 1
fi
