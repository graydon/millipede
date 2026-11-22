#!/usr/bin/env bash
# Compares the optimised pipeline with the unoptimised one. Images of differential functions are
# generated twice, with every Core pass off (MP_OPT=none) and with the passes of $OPT (default
# `all`). The optimised build sets MP_OPT_STRICT, so the pipeline must accept the optimised
# program itself: `compileRun` may not fall back to a shorter prefix of the passes, and a refusal
# is a failure. Both builds are run with `run_one`, which expects exactly the right dots, and the
# static instructions of the executable segment of each function's first image are summed. The
# script prints the totals and their ratio, and with -v one line per function. Exit status is
# nonzero if any image of either build fails or any generation fails. MP_TARGET=arm64-linux does
# the same for arm64 Linux.
#   scripts/opt-compare.sh [-v] [function names...]   default: every function; the measurement
#   scripts/opt-compare.sh [-v] --sample              the gate's stage
# `--sample` takes, for each pass, the first two functions on which it fires on its own
# (`differential fires`), and six others chosen at random with the day of the year as seed. The
# sample rotates; the seed is printed, and `SEED=<n>` reproduces it. scripts/differential.sh and
# scripts/differential-a64.sh generate the whole suite optimised and strict, and run it.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
verbose=0
[ "${1:-}" = "-v" ] && { verbose=1; shift; }
sample=0
[ "${1:-}" = "--sample" ] && { sample=1; shift; }
A64=0
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
if [ "${MP_TARGET:-}" = arm64-linux ]; then A64=1; QEMU="$(command -v qemu-aarch64)"; fi
JOBS="${JOBS:-8}"
OPT="${OPT:-all}"
lake build differential >/dev/null
EXE=.lake/build/bin/differential
export QEMU EXE
source scripts/difflib.sh
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
if [ "$sample" = 1 ]; then
  SEED="${SEED:-$((10#$(date +%j)))}"
  $EXE fires > "$tmp/fires"
  passes="$(cut -s -d' ' -f2- "$tmp/fires" | tr ' ' '\n' | grep -v '^$' | sort -u)"
  picked="$(for q in $passes; do
      awk -v q="$q" '{ for (i = 2; i <= NF; i++) if ($i == q) print $1 }' "$tmp/fires" | head -2
    done | sort -u)"
  echo "opt-compare: passes that fire in the suite: $(echo $passes)"
  others="$(cut -d' ' -f1 "$tmp/fires" | grep -vxF "$picked" | awk -v s="$SEED" 'BEGIN { srand(s) } { print rand() "\t" $0 }' | sort | head -6 | cut -f2)"
  names="$(echo $picked $others)"
  echo "opt-compare: sample (seed $SEED): $names"
else
  names="${*:-$($EXE list)}"
fi
insns() {  # elf -> instruction count of the executable segment
  local f="$1" off sz
  read -r off sz < <(readelf -lW "$f" | awk '$1=="LOAD" && / E / {print $2, $5; exit}')
  dd if="$f" of="$f.seg" bs=1 skip=$((off)) count=$((sz)) status=none
  if [ "$A64" = 1 ]; then
    od -An -v -tx4 -w4 "$f.seg" | awk '{ i++; if ($1 != "00000000") last = i } END { print last + 0 }'
  else
    x64-objdump -D -b binary -mi386:x86-64 "$f.seg" | grep -cE '^ +[0-9a-f]+:'$'\t'
  fi
}
fail=0
for mode in none opt; do
  mkdir -p "$tmp/$mode"
  if [ "$mode" = none ]; then env_opt=none; strict=; else env_opt="$OPT"; strict=1; fi
  echo "$names" | tr ' ' '\n' | grep -v '^$' |
    MP_OPT="$env_opt" MP_OPT_STRICT="$strict" xargs -P "$JOBS" -I{} sh -c \
      "$EXE gen '$tmp/$mode' {} >/dev/null 2>>'$tmp/$mode.err' || echo {} >> '$tmp/$mode.genfail'"
  if [ -s "$tmp/$mode.genfail" ]; then
    echo "opt-compare: generation failed ($mode):"; cat "$tmp/$mode.genfail"; cat "$tmp/$mode.err" | head -5
    fail=1
  fi
  echo "$names" | tr ' ' '\n' | grep -v '^$' |
    xargs -P "$JOBS" -I{} bash -c 'run_one {} '"'$tmp/$mode'" > "$tmp/$mode.results" || true
  if grep -q '^FAIL' "$tmp/$mode.results"; then
    echo "opt-compare: runs failed ($mode):"; grep '^FAIL' "$tmp/$mode.results"; fail=1
  fi
done
tn=0; to=0
for f in $names; do
  [ -f "$tmp/none/$f.0.elf" ] && [ -f "$tmp/opt/$f.0.elf" ] || continue
  a="$(insns "$tmp/none/$f.0.elf")"; b="$(insns "$tmp/opt/$f.0.elf")"
  tn=$((tn + a)); to=$((to + b))
  [ "$verbose" = 1 ] && printf '%-14s none=%6d opt=%6d\n' "$f" "$a" "$b"
done
echo "opt-compare (${MP_TARGET:-x64-linux}, OPT=$OPT): $(echo "$names" | wc -w) functions," \
  "static instructions none=$tn opt=$to ratio=$(awk -v a="$tn" -v b="$to" 'BEGIN { printf "%.3f", (b > 0 ? a / b : 0) }')"
exit "$fail"
