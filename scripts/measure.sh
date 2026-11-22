#!/usr/bin/env bash
# Measures code size and executed instructions: the static text bytes and instruction lines of the
# executable segment of the `mpc` instances and of one-case differential harnesses, and the
# instructions qemu executes for the cost programs (Tests/Differential/Cost.lean). The results
# are recorded in doc/measurements.md. The stack bound each image asks for, which is its
# PT_GNU_STACK p_memsz and the proved Lin bound, is printed with its text.
#
# Usage: scripts/measure.sh [extra differential function names...]
# The slot-resident value functions of SlotFuncs.lean are always measured.
#   MP_REGALLOC=0       register allocation off
#   MP_REGALLOC=slots   slot locations only
#   MP_REGALLOC=<k>     k register locations (default 6, both targets)
# `mpc` follows only MP_REGALLOC=0, as `--no-regalloc`.
#   MP_TARGET=arm64-linux   the same for arm64 Linux, where instructions are text bytes / 4 up to
#                           the last non-zero word of the page-padded segment, and qemu-aarch64
#                           counts the executed ones.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
A64=0
if [ "${MP_TARGET:-}" = arm64-linux ]; then A64=1; QEMU="$(command -v qemu-aarch64)"; fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
text() {  # elf -> "text=<bytes> bytes  insns=<n>  stack=<bytes>"
  local f="$1" off sz
  read -r off sz < <(readelf -lW "$f" | awk '$1=="LOAD" && / E / {print $2, $5; exit}')
  dd if="$f" of="$tmp/seg" bs=1 skip=$((off)) count=$((sz)) status=none
  local n
  if [ "$A64" = 1 ]; then  # the segment is padded to whole 64 KiB pages: count to the last non-zero word
    n="$(od -An -v -tx4 -w4 "$tmp/seg" | awk '{ i++; if ($1 != "00000000") last = i } END { print last + 0 }')"
    sz=$((4 * n)); else
  n="$(x64-objdump -D -b binary -mi386:x86-64 "$tmp/seg" | grep -cE '^ +[0-9a-f]+:'$'\t')"; fi
  echo "text=$((sz)) bytes  insns=$n  stack=$(( $(readelf -lW "$f" | awk '$1=="GNU_STACK" {print $6}') ))"
}
echo "## (a) mpc instances: text segment bytes / instruction lines"
for i in exit42 hello sum ticks readcount pooltally revchunks; do
  lake exe mpc $( [ "${MP_REGALLOC:-}" = 0 ] && echo --no-regalloc ) "$i" -o "$tmp/$i" >/dev/null 2>&1
  printf '%-12s %s\n' "$i" "$(text "$tmp/$i")"
done
echo
echo "## differential functions (one-case harness ELF): text bytes / instruction lines"
lake build differential >/dev/null
EXE=.lake/build/bin/differential
for f in addClamp divmod mBorrow mop mSliceArg pRet sRev rPlainSum pSwapArg iBubble alAFill iRoot \
    $($EXE list-slot) "$@"; do
  rm -rf "$tmp/d"; mkdir -p "$tmp/d"
  $EXE gen "$tmp/d" "$f" 1 >/dev/null
  printf '%-12s %s\n' "$f" "$(text "$(ls "$tmp/d"/*.elf | head -1)")"
done
echo
echo "## Cost regression: qemu instructions executed (ops6, ops2, extra = 6 ops minus 2 ops)"
$EXE cost "$tmp/c" >/dev/null
icount() { "$QEMU" -one-insn-per-tb -d exec,nochain -D "$tmp/tr" "$tmp/c/cost.$1.elf" < /dev/null > /dev/null || true
  grep -c '^Trace' "$tmp/tr"; }
for k in mut shr bmut bshr slm sls sla slma root lpm lps lpr val lpv; do
  s6=$(icount "s-${k}6"); s2=$(icount "s-${k}2"); l6=$(icount "l-${k}6"); l2=$(icount "l-${k}2")
  printf '%-5s s:ops6=%s ops2=%s extra=%s l:ops6=%s ops2=%s extra=%s\n' "$k" "$s6" "$s2" $((s6 - s2)) "$l6" "$l2" $((l6 - l2))
done
