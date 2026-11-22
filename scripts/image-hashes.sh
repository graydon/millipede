#!/usr/bin/env bash
# Prints a hash of every generated x64 image: each differential harness (`differential gen`),
# each cost program (`differential cost`) and each `mpc` instance. Running it before and after a
# change and comparing the outputs with `diff` shows whether the change leaves the generated code
# byte-identical.
#   scripts/image-hashes.sh > before.txt ; …change… ; scripts/image-hashes.sh > after.txt
# `MP_TARGET=arm64-linux` hashes the same images for arm64 Linux, because `differential gen`,
# `cost` and `mpc` read it. `MP_REGALLOC=0` hashes the images with register allocation off:
# `differential` reads the variable and `mpc` gets `--no-regalloc`. `MP_MEMBASE=0` hashes them with
# `Options.memBase` off (`mpc --no-membase`).
set -euo pipefail
cd "$(dirname "$0")/.."
JOBS="${JOBS:-8}"
lake build differential mpc >/dev/null
EXE=.lake/build/bin/differential
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
$EXE list | xargs -P "$JOBS" -I{} sh -c "$EXE gen '$tmp' {} >/dev/null"
for k in s l; do for m in mut shr bmut bshr slm sls sla slma root lpm lps lpr val lpv; do
  for n in 2 6; do echo "$k-$m$n"; done; done; done |
  xargs -P "$JOBS" -I{} sh -c "$EXE cost '$tmp' {} >/dev/null"
for i in exit42 hello sum ticks readcount pooltally revchunks reqspool reqsbump; do
  lake exe mpc $( [ "${MP_REGALLOC:-}" = 0 ] && echo --no-regalloc ) \
    $( [ "${MP_MEMBASE:-}" = 0 ] && echo --no-membase ) "$i" -o "$tmp/mpc.$i" >/dev/null 2>&1
done
(cd "$tmp" && find . -type f ! -name '*.txt' | sort | xargs sha256sum)
