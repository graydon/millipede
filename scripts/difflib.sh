# Functions shared by scripts/differential.sh (x64, under qemu) and scripts/differential-a64.sh
# (arm64, native). The caller sets $tmp (the image directory), $QEMU (how to run an image: a qemu
# binary, or `env` to run it natively), $QCOUNT (the qemu that counts executed instructions),
# $EXE (the `differential` executable) and $JOBS, and exports QEMU and EXE because run_one runs
# under xargs in a fresh bash.
# shellcheck shell=bash

# Counts the instructions executed by the cost program `cost.$1.elf`, using qemu's
# per-instruction trace, after checking its exit status.
icount() {
  local tr="$tmp/trace.$1"
  rm -f "$tr"
  local st=0
  "$QCOUNT" -one-insn-per-tb -d exec,nochain -D "$tr" "$tmp/cost.$1.elf" < /dev/null > /dev/null || st=$?
  # each program exits with the status its source computes, the same for both sizes; any
  # other status (a fault, a wrong value) is a failure and not a measurement
  local want
  case "${1#*-}" in
    mut2|mut6) want=0 ;; shr2|val2|bshr2) want=23 ;; shr6|val6|bshr6) want=153 ;;
    bmut2|root2) want=2 ;; bmut6|root6) want=6 ;; slm2) want=9 ;; slm6) want=13 ;;
    sls2|sls6|sla2|sla6) want=44 ;; slma2) want=9 ;; slma6) want=13 ;;
    lpm2) want=22 ;; lpm6) want=24 ;; lps2) want=14 ;; lps6) want=42 ;; lpr2) want=12 ;; lpr6) want=34 ;;
    lpv2) want=15 ;; lpv6) want=57 ;; *) want=unknown ;;
  esac
  if [ "$st" != "$want" ]; then echo "cost: $1 exited with status $st, expected $want" >&2; return 1; fi
  grep -c '^Trace' "$tr"
}
extra() {  # size kind -> the instructions of 4 more operations
  local a b; a="$(icount "$1-${2}6")" || return 1; b="$(icount "$1-${2}2")" || return 1
  echo $((a - b))
}
# The two sizes may differ by two instructions per operation, 8 in all: register allocation chooses
# over the whole function, so the programs of the two sizes, whose construction differs (a loop
# writes the large struct), can save a register more or less around a call or a step, or keep a
# value in a result register or not (measured: at most 8, for `root` on arm64, and the large
# struct always the cheaper). A size-dependent copy costs at least one instruction per word, 60
# or more per operation for the large struct, which the self-test requires to see.
cost_check() {  # kind ; require equal for both sizes, up to the allocation's slack
  local kind="$1" s l
  s="$(extra s "$kind")" || return 2; l="$(extra l "$kind")" || return 2
  if [ "$s" -gt $((l + 8)) ] || [ "$l" -gt $((s + 8)) ]; then
    echo "cost: $kind: 4 more cost $s (4-word struct) but $l (64-word struct)"; return 1; fi
  echo "cost: $kind: 4 more cost $s instructions for the 4-word struct and $l for the 64-word one"
}

# The lock-step driver of the I/O test: run ELF $1 on script $2 (lines `I <hex>` / `O <hex>`).
io_drive() {
  python3 -I - "$QEMU" "$1" "$2" <<'PY'
import os, subprocess, select, sys, time
qemu, elf, script = sys.argv[1:4]
lines = open(script).read().split("\n")
pairs = [(bytes.fromhex(lines[i][2:]), bytes.fromhex(lines[i + 1][2:]))
         for i in range(0, len(lines) - 1, 2)]
p = subprocess.Popen([qemu, elf], stdin=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=0)
def read_exact(n, secs=5.0):
    buf = b""
    end = time.time() + secs
    while len(buf) < n:
        left = end - time.time()
        if left <= 0 or not select.select([p.stdout], [], [], left)[0]:
            return buf
        chunk = os.read(p.stdout.fileno(), n - len(buf))
        if not chunk:
            return buf
        buf += chunk
    return buf
def fail(msg):
    p.kill(); p.wait()
    print("io: " + msg); sys.exit(1)
for k, (inp, exp) in enumerate(pairs):
    try:
        os.write(p.stdin.fileno(), inp)
    except OSError:
        fail("block %d: the program closed its input" % k)
    got = read_exact(len(exp))
    if got != exp:
        fail("block %d: wrote %s, expected %s" % (k, got.hex(), exp.hex()))
p.stdin.close()
try:
    rc = p.wait(timeout=5)
except subprocess.TimeoutExpired:
    fail("no exit at end of input")
rest = p.stdout.read()
if rc != 0 or rest:
    fail("exit %d, %d stray bytes at end of input" % (rc, len(rest)))
print("ok   io (%d blocks, %d bytes, lock-step pipes)" % (len(pairs), sum(len(a) for a, _ in pairs)))
PY
}

# Runs the images of test function $1 in directory $2, one per chunk listed in $2/$1.cases (lines
# `k cases mode`). Every chunk must print exactly one dot per case and exit with status 0.
run_one() {
  local name="$1" tmp="$2"
  local k cases mode want got rc total=0 bad=0 modes=""
  while read -r k cases mode; do
    want="$(head -c "$cases" < /dev/zero | tr '\0' '.')"
    rc=0
    local inp=/dev/null
    [ "$mode" = stdin ] && inp="$tmp/$name.$k.in"
    got="$(timeout "${RUN_TIMEOUT:-20}" "$QEMU" "$tmp/$name.$k.elf" < "$inp")" || rc=$?
    total=$((total + cases))
    case " $modes " in *" $mode "*) ;; *) modes="$modes $mode" ;; esac
    if [ "$rc" != 0 ] || [ "$got" != "$want" ]; then
      local first
      first="$(printf '%s' "$got" | awk '{ print index($0, "X") - 1 }')"
      echo "FAIL $name chunk $k: exit $rc, got ${#got} of $cases bytes, first mismatch at case $first of the chunk"
      bad=1
    fi
  done < "$tmp/$name.cases"
  [ "$bad" = 0 ] && echo "ok   $name ($total cases,$modes)"
  return "$bad"
}
export -f run_one

# The mutant loop of both self-tests: `mutant_run GEN M DIR F...` generates the images of the
# functions F... with mutant M applied (`$EXE GEN DIR M f`, in parallel), runs them with run_one
# into DIR/results.txt and prints the number of functions that fail. A mutant whose generation
# fails is an error (status 2) and not a catch, because the self-test must show that the run of
# the mutated code fails.
mutant_run() {
  local gen="$1" m="$2" d="$3"; shift 3
  mkdir -p "$d"; rm -f "$d/gen-failed"
  printf '%s\n' "$@" | xargs -P "$JOBS" -I{} sh -c "$EXE $gen '$d' '$m' {} 2>>'$d/err' || echo {} >> '$d/gen-failed'"
  if [ -e "$d/gen-failed" ]; then
    echo "selftest: mutant $m: generation failed for $(tr '\n' ' ' < "$d/gen-failed")" >&2; return 2
  fi
  printf '%s\n' "$@" | RUN_TIMEOUT=2 xargs -P "$JOBS" -I{} bash -c "run_one {} '$d'" > "$d/results.txt" 2>&1 || true
  { grep '^FAIL' "$d/results.txt" || true; } | awk '{ print $2 }' | sort -u | wc -l
}

# The guard against compile-time evaluation of the test calls: `div_guard DISASM RE` requires
# that the disassembly of the image of each function that divides by a run-time value contains
# an instruction matching RE.
div_guard() {
  local f n
  for f in divmod divc checked uCeilSec uMixed; do
    n="$($1 "$tmp/$f.0.elf" | grep -cwE "$2" || true)"
    if [ "$n" = 0 ]; then
      echo "differential: the image of $f contains no division: its calls were evaluated when it was compiled"
      return 1
    fi
  done
}
