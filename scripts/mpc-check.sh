#!/usr/bin/env bash
# Checks the compiler driver end to end. `lake exe mpc <instance> -o <file>` compiles every
# registered instance, the script runs the ELF under qemu-x86_64, and it compares the exit status
# and the output with the source program's meaning. It also checks that the ledger is written
# next to the file. Exit status 0 means every check passed.
#
# The instance `pooltally` is a reactor whose root holds a Pool arena in static memory. It reads
# its input byte by byte with `read`, allocates a node with the unchecked `alloc!`, which the
# root invariant discharges, and frees the node, and its exit status is the sum of the bytes
# modulo 256. It is run on fixed inputs, on random adversarial inputs whose expected status this
# script computes independently, and with stdin closed so that `read` fails.
# `--selftest` runs the image with a wrong expectation and requires the check to fail.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
# MP_TARGET=arm64-linux compiles for arm64Linux and runs the images natively, because the host is
# aarch64; the ledger of an arm64 image names Millipede.compile_sound_arm64.
ARCH="X86-64"; LEDGER="Millipede.compile_sound (no hypotheses)"
if [ "${MP_TARGET:-}" = arm64-linux ]; then QEMU="env"; ARCH="AArch64"; LEDGER="Millipede.compile_sound_arm64 (no hypotheses)"; fi
lake build mpc >/dev/null
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
fail=0
# each line of the table: instance, expected exit status, expected stdout (a printf format)
check() {
  local name="$1" code="$2" out="$3"
  lake exe mpc "$name" -o "$tmp/$name" >/dev/null
  [ -s "$tmp/$name.ledger.txt" ] || { echo "mpc-check: $name: no ledger"; fail=1; }
  grep -q "$LEDGER" "$tmp/$name.ledger.txt" || { echo "mpc-check: $name: ledger lacks the theorem"; fail=1; }
  grep -q "^safety    : .*\.safe : p.Safe" "$tmp/$name.ledger.txt" || { echo "mpc-check: $name: ledger lacks the safety theorem"; fail=1; }
  readelf -h "$tmp/$name" | grep -q "$ARCH" || { echo "mpc-check: $name: not an $ARCH ELF"; fail=1; }
  local got rc=0
  got="$("$QEMU" "$tmp/$name")" || rc=$?
  local want
  want="$(printf "$out")"
  if [ "$rc" != "$code" ]; then echo "mpc-check: $name: exit $rc, expected $code"; fail=1; fi
  if [ "$got" != "$want" ]; then echo "mpc-check: $name: output '$got', expected '$want'"; fail=1; fi
}
# pooltally: input file and expected exit status, which is computed here independently of the compiler
check_in() {
  local name="$1" input="$2" code="$3"
  local rc=0
  "$QEMU" "$tmp/$name" < "$input" > "$tmp/out" || rc=$?
  if [ "$rc" != "$code" ]; then echo "mpc-check: $name < $(basename "$input"): exit $rc, expected $code"; return 1; fi
  if [ -s "$tmp/out" ]; then echo "mpc-check: $name: unexpected output"; return 1; fi
}
sum256() { od -An -v -tu1 "$1" | awk '{for(i=1;i<=NF;i++) s+=$i} END {print s % 256}'; }
check exit42 42 ''
check hello 0 'hello, world\n'
check sum 45 ''
check ticks 3 'tick\ntick\ntick\ntick\n'
# readcount reads its input through `read`; its exit status is the number of input bytes
lake exe mpc readcount -o "$tmp/readcount" >/dev/null
grep -q "$LEDGER" "$tmp/readcount.ledger.txt" || { echo "mpc-check: readcount: ledger lacks the theorem"; fail=1; }
if lake exe mpc nosuch -o "$tmp/x" >/dev/null 2>&1; then echo "mpc-check: unknown instance accepted"; fail=1; fi
# Every instance compiles with every Core pass on, without the fallback to a shorter prefix of
# the passes, and the ledger names the passes that ran. `--no-opt` compiles it unoptimised.
for name in $(lake exe mpc --list | cut -f1); do
  lake exe mpc "$name" -o "$tmp/opt-$name" >/dev/null || { echo "mpc-check: $name: refused"; fail=1; continue; }
  { grep -q "^optimised : " "$tmp/opt-$name.ledger.txt" && ! grep -q "^optimised : none\|FALLBACK" "$tmp/opt-$name.ledger.txt"; } ||
    { echo "mpc-check: $name: not compiled with every pass: $(grep '^optimised' "$tmp/opt-$name.ledger.txt")"; fail=1; }
  lake exe mpc --no-opt "$name" -o "$tmp/noopt-$name" >/dev/null || { echo "mpc-check: $name --no-opt: refused"; fail=1; continue; }
  grep -q "^optimised : none (" "$tmp/noopt-$name.ledger.txt" || { echo "mpc-check: $name --no-opt: ledger names passes"; fail=1; }
done

printf 'hello' > "$tmp/c5"; check_in readcount "$tmp/c5" 5 || fail=1
head -c 200 /dev/urandom > "$tmp/c200"; check_in readcount "$tmp/c200" 200 || fail=1

# The pool in the root: pooltally on its inputs.
lake exe mpc pooltally -o "$tmp/pooltally" >/dev/null
readelf -h "$tmp/pooltally" | grep -q "$ARCH" || { echo "mpc-check: pooltally: not an $ARCH ELF"; fail=1; }
readelf -lW "$tmp/pooltally" | grep -q "LOAD.*RW" || { echo "mpc-check: pooltally: no read-write data segment"; fail=1; }
grep -q "$LEDGER" "$tmp/pooltally.ledger.txt" || { echo "mpc-check: pooltally: ledger lacks the theorem"; fail=1; }
grep -A1 "== Open claims" "$tmp/pooltally.ledger.txt" | grep -qx "none" || { echo "mpc-check: pooltally: ledger lists open claims"; fail=1; }
printf '' > "$tmp/in0";        check_in pooltally "$tmp/in0" 0 || fail=1
printf 'abc' > "$tmp/in1";     check_in pooltally "$tmp/in1" 38 || fail=1
printf '\377\377\001' > "$tmp/in2"; check_in pooltally "$tmp/in2" "$(sum256 "$tmp/in2")" || fail=1
n=0
for len in 1 7 8 9 64 255 1000 4096; do
  head -c "$len" /dev/urandom > "$tmp/rnd$len"
  check_in pooltally "$tmp/rnd$len" "$(sum256 "$tmp/rnd$len")" || fail=1
  n=$((n + 1))
done
# with stdin closed `read` fails; the result is an error and not 1, and the program exits with 0
rc=0; "$QEMU" "$tmp/pooltally" <&- >/dev/null 2>&1 || rc=$?
[ "$rc" = 0 ] || { echo "mpc-check: pooltally with stdin closed: exit $rc, expected 0"; fail=1; }
# `revchunks` reads its input into a byte buffer (`read` into a mutable slice), reverses each
# chunk in place through a slice passed to a helper, writes it out (`write` of a slice), and
# exits 0 at end of input. The expected output, computed here independently, is each 16-byte
# block of the input reversed, because a regular file is read in full blocks.
lake exe mpc revchunks -o "$tmp/revchunks" >/dev/null
grep -q "$LEDGER" "$tmp/revchunks.ledger.txt" || { echo "mpc-check: revchunks: ledger lacks the theorem"; fail=1; }
grep -A1 "== Open claims" "$tmp/revchunks.ledger.txt" | grep -qx "none" || { echo "mpc-check: revchunks: ledger lists open claims"; fail=1; }
revexp() { python3 -c 'import sys; d=open(sys.argv[1],"rb").read(); sys.stdout.buffer.write(b"".join(d[i:i+16][::-1] for i in range(0,len(d),16)))' "$1"; }
check_rev() {
  local input="$1" want="$2" rc=0
  "$QEMU" "$tmp/revchunks" < "$input" > "$tmp/revout" || rc=$?
  if [ "$rc" != 0 ]; then echo "mpc-check: revchunks < $(basename "$input"): exit $rc, expected 0"; return 1; fi
  if ! cmp -s "$tmp/revout" "$want"; then echo "mpc-check: revchunks < $(basename "$input"): wrong output"; return 1; fi
}
nr=0
printf 'hello, world\n' > "$tmp/r0"; printf '\ndlrow ,olleh' > "$tmp/r0.want"
check_rev "$tmp/r0" "$tmp/r0.want" || fail=1; nr=$((nr + 1))
printf '' > "$tmp/r1"; printf '' > "$tmp/r1.want"; check_rev "$tmp/r1" "$tmp/r1.want" || fail=1; nr=$((nr + 1))
for len in 1 2 3 4 5 7 8 9 15 16 17 31 33 255 1000 4096; do
  head -c "$len" /dev/urandom > "$tmp/rr$len"
  revexp "$tmp/rr$len" > "$tmp/rr$len.want"
  check_rev "$tmp/rr$len" "$tmp/rr$len.want" || fail=1
  nr=$((nr + 1))
done
# with stdin closed `read` fails with a count above 16, and the program exits with status 1 and writes nothing
rc=0; "$QEMU" "$tmp/revchunks" <&- > "$tmp/revout" 2>/dev/null || rc=$?
[ "$rc" = 1 ] || { echo "mpc-check: revchunks with stdin closed: exit $rc, expected 1"; fail=1; }
[ -s "$tmp/revout" ] && { echo "mpc-check: revchunks with stdin closed: unexpected output"; fail=1; }
# One client of the allocator interface (`Reqs`, proved once against `Alloc`) is compiled against
# the bitmap pool (`reqspool`) and the bump arena (`reqsbump`). Each input byte c is served in a
# fresh arena and the exit status is sum(3c + 3) modulo 256, computed here independently. Both
# binaries must agree with it, and so with each other, on every input.
sumreq() { od -An -v -tu1 "$1" | awk '{for(i=1;i<=NF;i++) s+=3*$i+3} END {print s % 256}'; }
nq=0
for impl in reqspool reqsbump; do
  lake exe mpc "$impl" -o "$tmp/$impl" >/dev/null
  grep -q "$LEDGER" "$tmp/$impl.ledger.txt" || { echo "mpc-check: $impl: ledger lacks the theorem"; fail=1; }
  grep -A1 "== Open claims" "$tmp/$impl.ledger.txt" | grep -qx "none" || { echo "mpc-check: $impl: ledger lists open claims"; fail=1; }
done
for f in in0 in1 in2 rnd1 rnd7 rnd8 rnd9 rnd64 rnd255 rnd1000 rnd4096; do
  want="$(sumreq "$tmp/$f")"
  for impl in reqspool reqsbump; do check_in "$impl" "$tmp/$f" "$want" || fail=1; done
  nq=$((nq + 1))
done
for impl in reqspool reqsbump; do
  rc=0; "$QEMU" "$tmp/$impl" <&- >/dev/null 2>&1 || rc=$?
  [ "$rc" = 0 ] || { echo "mpc-check: $impl with stdin closed: exit $rc, expected 0"; fail=1; }
done
if [ "${1:-}" = "--selftest" ]; then
  # a wrong status for either implementation must be caught
  for impl in reqspool reqsbump; do
    if check_in "$impl" "$tmp/in1" "$(( ($(sumreq "$tmp/in1") + 1) % 256 ))" >/dev/null; then
      echo "mpc-check: selftest: a wrong $impl status was accepted"; fail=1; fi
  done
fi
if [ "${1:-}" = "--selftest" ]; then
  # a wrong expected output must be caught
  printf 'hello, world\n' > "$tmp/r0.bad"
  if check_rev "$tmp/r0" "$tmp/r0.bad" >/dev/null; then echo "mpc-check: selftest: a wrong revchunks output was accepted"; fail=1; fi
fi
if [ "${1:-}" = "--selftest" ]; then
  # a wrong expectation must be caught
  if check_in pooltally "$tmp/in1" 39 >/dev/null; then echo "mpc-check: selftest: a wrong status was accepted"; fail=1; fi
  echo "mpc-check: selftest OK"
fi
[ "$fail" = 0 ] && echo "mpc-check: OK (9 instances on $ARCH; pooltally on $((n + 3)) inputs and closed stdin; revchunks on $nr inputs and closed stdin; reqspool and reqsbump on $nq inputs each, agreeing, and closed stdin)"
exit "$fail"
