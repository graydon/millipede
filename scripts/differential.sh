#!/usr/bin/env bash
# The differential tests for x64. For every test function of Tests/Differential/, `differential
# gen` builds a program that reads hundreds of edge-biased inputs from standard input, runs the
# function on each and compares the result with the value of an independent reference, writing
# `.` for each agreeing case and `X` for each mismatch. It compiles the program to an x64 ELF, and this script
# runs the ELF under qemu-x86_64. A function passes when stdout is exactly one dot per case and
# the exit status is 0. The script also runs the cost regression and the lock-step I/O test
# below. Exit status 0 means everything passed, or in the self-test that every seeded bug was
# caught.
#
# The I/O test (Tests/Differential/IoTest.lean, `differential io`) is a program that reads into a
# ByteBuf 16, reverses what it got through slice arguments and writes it. A driver feeds it 360
# adversarially short blocks through pipes in lock step: it writes a block, waits for exactly the
# bytes that the plain-Lean reference predicts, then writes the next. Every `read` therefore
# returns exactly that block, or 16 bytes of a longer one.
#
# `--selftest` shows that the suite has teeth by seeding bugs, which must each be caught. They
# are of three kinds.
#  * Byte patches of the generated ELFs, which have the effect of a code-generation bug without
#    rebuilding the compiler: `setb r8` becomes `setbe r8` (an unsigned less-than becomes
#    less-or-equal), `div rcx` becomes `idiv rcx` (unsigned division becomes signed), and
#    `shl r64,cl` becomes `shr r64,cl`. The qemu run of the affected functions must fail for
#    each patch.
#  * Pipeline mutants (Tests/Differential/Mutants.lean). The pipeline is run pass by pass with a
#    mutation of the Flat, Lin or Asm program between two passes, and the memory functions must
#    fail for each mutant. The mutants are seed pointer bugs, copies instead of pointers, a loop
#    that updates a copy of its carried binder, a pair borrow whose second pointer aliases the
#    first, and bugs in slot-resident values, including multi-word ones. A copy mutant (a
#    borrow, a reference argument, a scoped slice borrow or a slice argument that points at a copy
#    of its lender, so that reads are right and writes are lost) must fail every aliasing harness
#    of its kind, and a slot mutant must fail every function that uses its feature
#    (`differential list-alias`, `aliasFor` and `slotFor` in SliceFuncs.lean). A copy-in/copy-out
#    bug therefore cannot hide behind harnesses that never read the lender after the call.
#  * Pipeline mutants against the I/O test, and the register-selector mutants.
# The oracle itself was checked once by hand: changing `s < 2 ^ 64` to `s ≤ 2 ^ 64` in
# `refAddClamp` in Funcs.lean makes `differential gen` abort with "reference, mp def and
# denotation disagree".
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
JOBS="${JOBS:-8}"
selftest=0
[ "${1:-}" = "--selftest" ] && selftest=1
# Every program is compiled with the passes of $MP_OPT (default: all) and must be accepted as
# optimised, with no fallback to a shorter prefix of the passes (`compileRun`).
[ "$selftest" = 0 ] && export MP_OPT_STRICT=1
lake build differential >/dev/null
EXE=".lake/build/bin/differential"
# Constructs outside the pipeline's fragment must be refused with an error and never produce a binary.
if [ "${1:-}" != "--selftest" ]; then $EXE refuse >/dev/null || { echo "differential: refusal test failed"; exit 1; }; fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
# Shared with scripts/differential-a64.sh: icount, extra and cost_check (instruction counts under
# qemu, $QCOUNT), io_drive (the lock-step I/O driver, which runs images with $QEMU), run_one (run
# the images of one function) and mutant_run (the self-test's mutant loop).
QCOUNT="$QEMU"
export QEMU EXE
source scripts/difflib.sh
# The memory backend's `write` from a memory buffer, a slice given as pointer and length. A
# hand-built Flat program (`membufFlat` in Tests/Select.lean) computes "hi!\n" in its data region
# and writes 4 bytes, then 2, from it. Its ELF must print exactly that under qemu.
if [ "${1:-}" != "--selftest" ]; then
  $EXE membuf "$tmp/membuf" || { echo "differential: membuf image failed"; exit 1; }
  chmod +x "$tmp/membuf"
  got="$("$QEMU" "$tmp/membuf" | od -An -tx1 | tr -d ' \n')"
  [ "$got" = "6869210a6869" ] || { echo "differential: membuf printed $got, expected 6869210a6869"; exit 1; }
fi

# Cost regression (Tests/Differential/Cost.lean). For a struct of 4 words and one of 64 words,
# qemu counts the instructions executed by 4 more operations (6 versus 2, so that the struct's
# construction cancels), using `-one-insn-per-tb -d exec`, which traces one line per executed
# instruction. Each kind must cost the same for both sizes, up to 4 instructions of register
# allocation (scripts/difflib.sh), because it passes a pointer and does not copy. The kinds are:
#   mut / shr    calls taking the struct by `&mut` / `&` (Exp.callRef);
#   bmut / bshr  scoped borrows `let r := &mut s` / `let r := &s` (borrowMut / borrowShr);
#   slm / sls    scoped slice borrows `&mut s.items[1:hi]` / `&s.items[1:hi]`, a 2-word window
#                for the small struct and a 60-word window for the large one;
#   slma / sla   calls with that window as a slice argument, `&mut` / shared (a pointer and a length);
#   root         reactor steps on a root of that size (`step` gets the root by pointer);
#   lpm / lps / lpr   in-place loops of 2 versus 6 iterations, over a `&mut` slice window of the
#                struct (a callee filling it), over a shared window (a callee summing it) and
#                over the `&mut` struct's fields (a callee updating two of them). An in-place
#                loop costs the same per iteration for a struct of 8 and one of 64 words.
# Passing by value (`val`) must cost more for the larger struct, and so must a loop whose body
# passes the struct by value (`lpv`). The self-test requires both, which shows that the
# measurement can see a copy.
cost_kinds="mut shr bmut bshr slm sls sla slma root lpm lps lpr"
for k in s l; do for m in $cost_kinds val lpv; do for n in 2 6; do echo "$k-$m$n"; done; done; done \
  | xargs -P "$JOBS" -I{} sh -c "$EXE cost '$tmp' {} || echo {} >> '$tmp/cost-failed'"
[ -e "$tmp/cost-failed" ] && { echo "differential: cost programs failed to compile"; exit 1; }
if [ "$selftest" = 0 ]; then
  for kind in $cost_kinds; do cost_check "$kind" || exit 1; done
  # the control: a by-value struct is copied, so its cost grows with the size
  st=0; cost_check val >/dev/null || st=$?
  [ "$st" = 2 ] && { echo "cost: val programs failed to run"; exit 1; }
  if [ "$st" = 0 ]; then echo "cost: by-value passing did not grow with the struct's size: the measurement is blind"; exit 1; fi
  echo "cost: by value grows with size (as it must)"
  st=0; cost_check lpv >/dev/null || st=$?
  [ "$st" = 2 ] && { echo "cost: lpv programs failed to run"; exit 1; }
  if [ "$st" = 0 ]; then echo "cost: a loop passing the struct by value did not grow with its size: the loop measurement is blind"; exit 1; fi
  echo "cost: a loop copying the struct per iteration grows with size (as it must)"
else
  st=0; cost_check val >/dev/null || st=$?
  [ "$st" = 2 ] && { echo "selftest: val programs failed to run"; exit 1; }
  if [ "$st" = 0 ]; then echo "selftest: cost check NOT sensitive to a size-dependent (copying) call"; exit 1; fi
  echo "selftest: cost check catches size-dependent passing (by value)"
  st=0; cost_check lpv >/dev/null || st=$?
  [ "$st" = 2 ] && { echo "selftest: lpv programs failed to run"; exit 1; }
  if [ "$st" = 0 ]; then echo "selftest: loop cost check NOT sensitive to a copy per iteration"; exit 1; fi
  echo "selftest: loop cost check catches a size-dependent (copying) loop body"
fi


if [ "$selftest" = 1 ]; then names="cmps divmod shifts addClamp divc checked uCeilSec uMixed"; else names="$($EXE list)"; fi
names="$(echo $names | tr ' ' '\n')"
# Generate (compile) all programs in parallel.
echo "$names" | xargs -P "$JOBS" -I{} sh -c "$EXE gen '$tmp' {} || echo {} >> '$tmp/gen-failed'"
if [ -e "$tmp/gen-failed" ]; then
  echo "differential: generation failed for: $(tr '\n' ' ' < "$tmp/gen-failed")"
  exit 1
fi

# Self-test: patches the ELFs of $1, replacing hex pattern $2 by $3 over all chunks, and prints
# the number of places patched.
patch_elfs() {
  python3 -I - "$tmp" "$1" "$2" "$3" <<'PY'
import sys, glob
tmp, name = sys.argv[1], sys.argv[2]
# comma-separated lists of patterns and their replacements (the same instruction on each register)
pairs = list(zip(sys.argv[3].split(","), sys.argv[4].split(",")))
n = 0
for f in glob.glob(f"{tmp}/{name}.*.elf"):
    b = open(f, "rb").read()
    for old, new in pairs:
        old, new = bytes.fromhex(old), bytes.fromhex(new)
        n += b.count(old)
        b = b.replace(old, new)
    open(f, "wb").write(b)
print(n)
PY
}

if [ "$selftest" = 1 ]; then
  catches() {  # name old new: patch a copy, require failure
    local name="$1" old="$2" new="$3" n
    rm -rf "$tmp/p"; mkdir "$tmp/p"; cp "$tmp/$name".* "$tmp/p/"
    n="$(tmp="$tmp/p" patch_elfs "$name" "$old" "$new")"
    if [ "$n" = 0 ]; then echo "selftest: pattern $old not found in $name"; return 1; fi
    if bash -c "$(declare -f run_one); QEMU='$QEMU'; EXE='$EXE'; run_one $name '$tmp/p'" >/dev/null 2>&1; then
      echo "selftest: seeded bug ($old -> $new, $n sites) NOT caught in $name"; return 1
    fi
    echo "selftest: caught seeded bug $old -> $new in $name ($n sites)"
  }
  ok=0
  # Seeded bugs inside the pipeline (Tests/Differential/Mutants.lean): the pipeline is run pass
  # by pass with a mutation between two passes, and the memory functions must fail for each.
  mutant_caught() {
    local m="$1" d="$tmp/mut-$1" n
    # `bTok` loads bytes of a byte slice between non-zero bytes.
    local sub="mBump mEnum mChecked mNested mop mGuarded mSlots mMixed bTok"
    case "$m" in ptr-*|copy-*) sub="$($EXE list-ptr | tr '\n' ' ')" ;; flat-trunc8|flat-zext8) sub="bTok bOps ovByte" ;;
      slot-*) sub="$($EXE list-slot | tr '\n' ' ') lNest" ;; loop-*) sub="bFill bCopy" ;; esac
    # shellcheck disable=SC2086
    n="$(mutant_run genmut "$m" "$d" $sub)" || return 1
    if [ "$n" = 0 ]; then echo "selftest: mutant $m NOT caught"; return 1; fi
    # a copy mutant must fail every aliasing harness of its kind and a slot mutant every function
    # that uses its feature (`differential list-alias`)
    local a missed=""
    for a in $($EXE list-alias "$m"); do grep -q "^FAIL $a " "$d/results.txt" || missed="$missed $a"; done
    if [ -n "$missed" ]; then echo "selftest: mutant $m NOT caught by:$missed"; return 1; fi
    echo "selftest: caught mutant $m ($n of $(echo $sub | wc -w) functions fail$( [ -n "$($EXE list-alias "$m")" ] && echo "; all of: $($EXE list-alias "$m" | tr '\n' ' ')"))"
  }
  for m in $($EXE list-mutants); do mutant_caught "$m" || ok=1; done
  # Register-selector mutants (Tests/Differential/X64RegMutants.lean), which exist only in the
  # default configuration and not with `MP_REGALLOC=0` or `slots`. They are a register not saved
  # across a call, a register restored from the wrong word, a location in `rcx`, `rdx` (division)
  # or `r11` (`syscall`), the wrong register for a location, an omitted two-operand copy, a
  # skipped save, a move between two slots selected as nothing, and a skipped register argument.
  case "${MP_REGALLOC:-}" in 0|slots) xregs="" ;; *) xregs="$($EXE list-xreg-mutants)" ;; esac
  for m in $xregs; do
    sub="$($EXE list-xreg-mutant-funcs "$m")"
    # shellcheck disable=SC2086
    n="$(mutant_run genmut-xreg "$m" "$tmp/$m" $sub)" || { ok=1; continue; }
    if [ "$n" = 0 ]; then echo "selftest: register-selector mutant $m NOT caught"; ok=1
    else echo "selftest: caught register-selector mutant $m ($n of $(echo $sub | wc -w) functions fail)"; fi
  done
  # the I/O test must fail for seeded bugs of the pipeline and for a wrong expectation
  mkdir -p "$tmp/io" && $EXE io "$tmp/io" >/dev/null || { echo "selftest: io program failed to compile"; exit 1; }
  io_drive "$tmp/io/io.elf" "$tmp/io/io.script" >/dev/null || { echo "selftest: the unseeded I/O test fails"; ok=1; }
  for m in flat-store-off ptr-write-off ptr-read-off copy-slice-arg sel-store8 lin-store-width; do
    mkdir -p "$tmp/io-$m" && $EXE io "$tmp/io-$m" "$m" >/dev/null || { echo "selftest: io mutant $m failed to compile"; ok=1; continue; }
    if io_drive "$tmp/io-$m/io.elf" "$tmp/io-$m/io.script" >/dev/null 2>&1; then
      echo "selftest: I/O test does NOT catch mutant $m"; ok=1
    else echo "selftest: I/O test catches mutant $m"; fi
  done
  sed 's/^O \([0-9a-f]\{2\}\)/O 00/' "$tmp/io/io.script" > "$tmp/io/wrong.script"
  if io_drive "$tmp/io/io.elf" "$tmp/io/wrong.script" >/dev/null 2>&1; then
    echo "selftest: I/O driver accepts a wrong expectation"; ok=1
  else echo "selftest: I/O driver rejects a wrong expectation"; fi
  # `setb r8` on any register, the result's location register or `al`, becomes `setbe`; `div rcx`
  # becomes `idiv rcx`; `shl r64, cl` becomes `shr` on `rax` or a location register `rbx rbp r12 …`
  # or `r8 r9 r10`
  setb="$(for m in c0 c1 c2 c3 c4 c5 c6 c7; do printf '0f92%s,' $m; done | sed 's/,$//')"
  setbe="$(for m in c0 c1 c2 c3 c4 c5 c6 c7; do printf '0f96%s,' $m; done | sed 's/,$//')"
  shl="48d3e0,48d3e3,48d3e5,49d3e0,49d3e1,49d3e2,49d3e4,49d3e5,49d3e6,49d3e7"
  shr="48d3e8,48d3eb,48d3ed,49d3e8,49d3e9,49d3ea,49d3ec,49d3ed,49d3ee,49d3ef"
  catches cmps "$setb" "$setbe" || ok=1
  catches addClamp "$setb" "$setbe" || ok=1
  catches divmod 48f7f1 48f7f9 || ok=1
  # the guard against compile-time evaluation fails on an image without a division
  rm -rf "$tmp/g"; mkdir "$tmp/g"; cp "$tmp"/*.0.elf "$tmp/g/"; cp "$tmp/g/addClamp.0.elf" "$tmp/g/divmod.0.elf"
  if tmp="$tmp/g" div_guard "x64-objdump -D -b binary -mi386:x86-64" 'i?div' >/dev/null; then
    echo "selftest: the division guard accepts an image without a division"; ok=1
  else echo "selftest: the division guard rejects an image without a division"; fi
  catches shifts "$shl" "$shr" || ok=1
  # Seeded bugs of the `do` translation (`doMutants` in Tests/Differential/DoFuncs.lean): a
  # `break` ignored, a `continue` falling through, a return's value lost, a return that does not
  # leave, an inclusive bound off by one, the lower bound ignored, a joined statement's
  # assignment lost (`join-lost`), a jumping statement's join losing the jump (`jump-join-lost`),
  # a shadowing binder not renamed (`bind-name`), a leading exit test not negated (`neg-cond`),
  # the accumulator not assigned back (`acc-lost`) and an inner `break` leaving the outer loop
  # (`inner-break-outer`). Each must disagree with its reference. The disagreement is found at the
  # denotation, by comparing the mutant's `exp_denote` with the reference, so the check does not
  # depend on the target.
  if ! $EXE domut | sed 's/^/selftest: do translation: /'; then ok=1; fi
  exit "$ok"
fi
# Every test program reads its cases from standard input, so no call is evaluated at compile
# time. The guard fails if an image of a function that divides by a run-time value has no `div`.
div_guard "x64-objdump -D -b binary -mi386:x86-64" 'i?div' || exit 1
fail=0
echo "$names" | xargs -P "$JOBS" -I{} bash -c 'run_one {} '"'$tmp'" > "$tmp/results.txt" || fail=1
sort "$tmp/results.txt"
mkdir -p "$tmp/io" && $EXE io "$tmp/io" > /dev/null || { echo "differential: the I/O program failed to compile"; exit 1; }
io_drive "$tmp/io/io.elf" "$tmp/io/io.script" || fail=1
total="$(cat "$tmp"/*.cases | awk '{ s += $2 } END { print s }')"
if [ "$fail" = 0 ]; then echo "differential: OK ($total cases over $(echo "$names" | wc -l) functions)"; fi
exit "$fail"
