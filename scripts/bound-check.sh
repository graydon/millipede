#!/usr/bin/env bash
# Compares the proved resource bounds of registered programs with runs under qemu, on both
# targets. `compile_sound` bounds the instructions of each reactor step by `p.stepCost` and the
# stack by `p.stackBytes`; `compile_stack_tight` bounds the stack by the size the image asks for in
# its `PT_GNU_STACK` header, which is at most `p.stackBytes`. Tests/Top.lean checks the bounds on
# the machine model, and this script checks them on qemu-x86_64 and qemu-aarch64, which execute the
# bytes independently of the model.
#
# For each program and target, `mpc` compiles the image and `differential budgets` prints the
# stack bound and, for each event of the source run on the input file, the sum of the step bounds
# up to the event's reactor step, and that step. qemu runs the image on the same input and logs
# every executed instruction with the registers before it (`-one-insn-per-tb -d
# exec,cpu,strace,nochain`). The check requires the same number of system calls as source events,
# at most the bound of event j instructions executed when the j-th system call is made, and a stack
# pointer never more than either stack bound below its first value. It prints each figure with its
# bound, and the largest step: the most instructions between the last events of two consecutive
# reactor steps, against the step bound.
#
# `--selftest` divides the instruction bounds by 32 and the stack bounds by 2, and every run must
# then exceed both an instruction bound and a stack bound. The largest ratio of an instruction bound
# to the run is 25.0 (revchunks, arm64), so with a factor of 32 every run exceeds its bound.
#
# Usage: scripts/bound-check.sh [--selftest]; BOUND_PROGRAMS="p q ..." checks other registered
# programs.
set -euo pipefail
cd "$(dirname "$0")/.."
selftest=0
[ "${1:-}" = "--selftest" ] && selftest=1
QX64="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
QA64="${QCOUNT:-$HOME/tools/bin/qemu-aarch64}"
command -v "$QA64" >/dev/null || QA64=qemu-aarch64
lake build mpc differential >/dev/null
MPC=.lake/build/bin/mpc
EXE=.lake/build/bin/differential
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
printf 'hello, world, this is forty bytes long!\n' > "$tmp/input"

# check NAME TARGET QEMU SPREG: compile, run under qemu, compare with the bounds
check() {
  local name="$1" target="$2" qemu="$3" spreg="$4" img="$tmp/$1.$2"
  "$MPC" --target "$target" "$name" -o "$img" >/dev/null
  MP_TARGET="$target" "$EXE" budgets "$name" "$tmp/input" > "$img.bounds"
  local st=0
  "$qemu" -one-insn-per-tb -d exec,cpu,strace,nochain -D "$img.log" "$img" < "$tmp/input" > /dev/null || st=$?
  local req
  req=$(readelf -lW "$img" | awk '/GNU_STACK/ { print $6 }')
  python3 -I - "$img.log" "$img.bounds" "$name" "$target" "$spreg" "$req" \
    "$([ "$selftest" = 1 ] && echo 32 || echo 1)" "$([ "$selftest" = 1 ] && echo 2 || echo 1)" \
    "$selftest" <<'PY'
import re, sys
log, bounds, name, target, spreg, req, iscale, sscale, selftest = sys.argv[1:10]
stack = None
budgets = []
stepOf = []
image = int(req, 0) // int(sscale)
for line in open(bounds):
    w = line.split()
    if w[0] == "stack": stack = int(w[1]) // int(sscale)
    elif w[0] == "event": budgets.append(int(w[2]) // int(iscale)); stepOf.append(int(w[3]))
    elif w[0] == "steps": steps, init, step = int(w[1]), int(w[2]), int(w[3])
n = 0; at = []; sp0 = None; spmin = None
sp_re = re.compile(r"\b" + spreg + r"=([0-9a-f]{16})")
call_re = re.compile(r"^\d+ (read|write|exit)\(")
for line in open(log, errors="replace"):
    if line.startswith("Trace"):
        n += 1
    elif call_re.match(line):
        at.append(n)
    else:
        m = sp_re.search(line)
        if m:
            sp = int(m.group(1), 16)
            if sp0 is None: sp0 = sp
            spmin = sp if spmin is None else min(spmin, sp)
depth = sp0 - spmin
bad = []
if len(at) != len(budgets):
    bad.append(f"{len(at)} system calls, {len(budgets)} source events")
ibad = [f"event {j} after {a} instructions, bound {b}" for j, (a, b) in enumerate(zip(at, budgets)) if a > b]
sbad = ([f"stack depth {depth} bytes, bound {stack}"] if depth > stack else []) + \
    ([f"stack depth {depth} bytes, image's request {image}"] if depth > image else [])
bad += ibad + sbad
# the last event of each reactor step, and the largest step after the first
last = {}
for a, k in zip(at, stepOf): last[k] = a
big = max([last[k] - last[k - 1] for k in last if k >= 2 and k - 1 in last] or [0])
print(f"bound-check: {name} {target}: {steps} reactor steps (bounds: init {init}, step {step}), "
      f"{n} instructions executed, bound {budgets[-1] if budgets else '?'} "
      f"({(budgets[-1] / max(n, 1)) if budgets else 0:.1f}x); largest step {big} "
      f"({step / max(big, 1):.1f}x); stack {depth} bytes, bound {stack} "
      f"({stack / max(depth, 1):.1f}x), image's request {image} ({image / max(depth, 1):.1f}x)")
for b in bad: print(f"bound-check: {name} {target}: {b}")
if selftest == "1": sys.exit(1 if ibad and sbad else 0)
sys.exit(1 if bad else 0)
PY
}

fail=0; passed=0
for name in ${BOUND_PROGRAMS:-ticks revchunks}; do
  for t in "x64-linux $QX64 RSP" "arm64-linux $QA64 SP"; do
    # shellcheck disable=SC2086
    if check "$name" $t; then passed=$((passed + 1)); else fail=1; fi
  done
done
if [ "$selftest" = 1 ]; then
  if [ "$passed" != 0 ]; then echo "bound-check selftest: $passed runs within the reduced bounds"; exit 1; fi
  echo "bound-check selftest: every run exceeds its reduced bounds"; exit 0
fi
exit "$fail"
