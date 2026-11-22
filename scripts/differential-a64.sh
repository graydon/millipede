#!/usr/bin/env bash
# The differential suite on arm64, run natively. Every test function of Tests/Differential
# (`differential list`) is compiled with `compile … arm64Linux` (`MP_TARGET=arm64-linux
# differential gen`) and its ELFs run directly. A function passes when its output is exactly one
# dot per case and its exit status is 0, as in scripts/differential.sh for x64 under qemu.
#
# With `--selftest`, each arm64 selection mutant (`a64Mutants` in Tests/Differential/Mutants.lean,
# a mutation of the selected arm64 Asm program before assembly) must make some function of its
# list fail. The mutants are a wrong condition after `cmp`, a wrong frame-offset scaling, a missing
# `x30` save, a wrong `movk` shift in a constant, sign instead of zero extension of a byte load
# and a misaligned frame. The register selector's mutants (`aregMutants`) and the seeded bugs of
# the `do` translation (`differential domut`, Tests/Differential/DoFuncs.lean) are run too.
# Exit status 0 means every function passed, or in the self-test every mutant was caught.
set -euo pipefail
cd "$(dirname "$0")/.."
JOBS="${JOBS:-8}"
selftest=0
[ "${1:-}" = "--selftest" ] && selftest=1
lake build differential >/dev/null
EXE=".lake/build/bin/differential"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
QEMU=env                                         # run images natively
QCOUNT="${QCOUNT:-$HOME/tools/bin/qemu-aarch64}" # count instructions (cost programs)
command -v "$QCOUNT" >/dev/null || QCOUNT=qemu-aarch64
export QEMU EXE
source scripts/difflib.sh

if [ "$selftest" = 0 ]; then
  # every program is compiled with the passes of $MP_OPT (default: all) and must be accepted as
  # optimised, with no fallback to a shorter prefix of the passes (`compileRun`)
  export MP_OPT_STRICT=1
  names="$($EXE list)"
  echo "$names" | MP_TARGET=arm64-linux xargs -P "$JOBS" -I{} sh -c "$EXE gen '$tmp' {} || echo {} >> '$tmp/gen-failed'"
  if [ -e "$tmp/gen-failed" ]; then
    echo "differential-a64: generation failed for: $(tr '\n' ' ' < "$tmp/gen-failed")"; exit 1
  fi
  # the test programs read their cases at run time, so the images of the dividing functions divide
  div_guard "objdump -D -b binary -maarch64" '[us]div' || exit 1
  echo "$names" | xargs -P "$JOBS" -I{} bash -c "run_one {} '$tmp'" > "$tmp/results.txt" || true
  if grep -q '^FAIL' "$tmp/results.txt"; then grep '^FAIL' "$tmp/results.txt"; exit 1; fi
  echo "differential-a64: $(grep -c '^ok' "$tmp/results.txt") functions pass natively on arm64"
  # constructs outside the fragment are refused (never an image)
  MP_TARGET=arm64-linux $EXE refuse >/dev/null || { echo "differential-a64: refusal test failed"; exit 1; }
  # the lock-step I/O program, natively
  mkdir -p "$tmp/io" && MP_TARGET=arm64-linux $EXE io "$tmp/io" > /dev/null || { echo "differential-a64: the I/O program failed to compile"; exit 1; }
  io_drive "$tmp/io/io.elf" "$tmp/io/io.script"
  # the cost regression, as for x64: 4 more operations cost the same for a 4-word and a 64-word
  # struct passed by reference, and more for one passed by value
  cost_kinds="mut shr bmut bshr slm sls sla slma root lpm lps lpr"
  for k in s l; do for m in $cost_kinds val lpv; do for n in 2 6; do echo "$k-$m$n"; done; done; done \
    | MP_TARGET=arm64-linux xargs -P "$JOBS" -I{} sh -c "$EXE cost '$tmp' {} || echo {} >> '$tmp/cost-failed'"
  [ -e "$tmp/cost-failed" ] && { echo "differential-a64: cost programs failed to compile"; exit 1; }
  for kind in $cost_kinds; do cost_check "$kind" || exit 1; done
  st=0; cost_check val >/dev/null || st=$?
  if [ "$st" != 1 ]; then echo "cost: by-value passing did not grow with the struct's size"; exit 1; fi
  echo "cost: by value grows with size (as it must)"
  exit 0
fi

ok=0
for m in $($EXE list-a64-mutants); do
  sub="$($EXE list-a64-mutant-funcs "$m")"
  # shellcheck disable=SC2086
  n="$(mutant_run genmut-a64 "$m" "$tmp/$m" $sub)" || { ok=1; continue; }
  if [ "$n" = 0 ]; then echo "selftest: arm64 mutant $m NOT caught"; ok=1
  else echo "selftest: caught arm64 mutant $m ($n of $(echo $sub | wc -w) functions fail)"; fi
done
# Register-selector mutants, which exist only in the default configuration with `A64Reg.kDefault`
# register locations and not with `MP_REGALLOC=0` or `slots`. They are a register not saved
# across a call, a register restored from the wrong word, a location in a scratch or system-call
# register, the wrong register for a location, a skipped save, a move between two slots
# selected as nothing, a skipped register argument, a wrong `add`/`sub` immediate, and a one
# stored where the selector stores a zero from `xzr`.
case "${MP_REGALLOC:-}" in 0|slots) aregs="" ;; *) aregs="$($EXE list-areg-mutants)" ;; esac
for m in $aregs; do
  sub="$($EXE list-areg-mutant-funcs "$m")"
  # shellcheck disable=SC2086
  n="$(mutant_run genmut-areg "$m" "$tmp/$m" $sub)" || { ok=1; continue; }
  if [ "$n" = 0 ]; then echo "selftest: register-selector mutant $m NOT caught"; ok=1
  else echo "selftest: caught register-selector mutant $m ($n of $(echo $sub | wc -w) functions fail)"; fi
done
# Seeded bugs of the `do` translation, which are independent of the target because the term is
# wrong before any pass (Tests/Differential/DoFuncs.lean): each must disagree with its reference.
if ! $EXE domut | sed 's/^/selftest: do translation: /'; then ok=1; fi
exit "$ok"
