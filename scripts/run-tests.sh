#!/usr/bin/env bash
# The script-level tests that scripts/check.sh runs. Each subsystem appends its line to `stages`.
# The stages are independent. What they build is built first by one lake process, so that no two
# lake builds race in the tree; then they run concurrently, each into its own log. The logs are
# printed in order with each stage's wall time, and the script fails if any stage failed.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
stages=(
  "scripts/elf-check.sh"
  "scripts/x64-encode-check.sh"
  "scripts/a64-encode-check.sh"
  "scripts/a64-encode-check.sh --selftest"
  "scripts/a64-cosim.sh"
  "scripts/a64-cosim.sh --selftest"
  "scripts/mpc-check.sh"
  "scripts/mpc-check.sh --selftest"
  "scripts/differential.sh"
  "scripts/differential.sh --selftest"
  "scripts/cosim.sh"
  "scripts/cosim.sh --selftest"
  "scripts/layout-check.sh"
  "scripts/layout-check.sh --selftest"
  "scripts/a64-elf-check.sh"
  "scripts/differential-a64.sh"
  "scripts/differential-a64.sh --selftest"
  "env MP_REGALLOC=0 scripts/differential.sh"            # register allocation off: same results
  "env MP_REGALLOC=0 scripts/differential.sh --selftest"
  "env MP_REGALLOC=0 scripts/differential-a64.sh"
  "env MP_REGALLOC=0 scripts/differential-a64.sh --selftest"
  "env MP_REGALLOC=slots scripts/differential.sh"         # x64 slot locations only (no registers)
  "env MP_MEMBASE=0 scripts/differential.sh"              # x64 with every data access computing its full address
  "env MP_REGALLOC=slots scripts/differential-a64.sh"     # arm64 slot locations only (no registers)
  "env MP_TARGET=arm64-linux scripts/mpc-check.sh"
  "env MP_TARGET=arm64-linux scripts/mpc-check.sh --selftest"
  "scripts/loader-a64.sh"
  "scripts/loader-a64.sh --selftest"
  "scripts/opt-compare.sh --sample"   # Core passes on versus off, x64 (doc/phases/phase-4b-core.md)
  "env MP_TARGET=arm64-linux scripts/opt-compare.sh --sample"
  "scripts/bound-check.sh"   # proved instruction and stack bounds against runs under qemu, both targets
  "scripts/bound-check.sh --selftest"
  "scripts/leanq selftest"   # a seeded error must be reported by `leanq diag`
  "scripts/doc-check.sh"   # documentation findings; warn-only, always exits 0
  "scripts/format-check.sh"   # the key-value server over format descriptions, both targets
  "scripts/format-check.sh --selftest"
  "scripts/pe-check.sh --selftest"   # PE32+ writer and loader model: llvm tools, lld-link, wine
  "scripts/macho-check.sh --selftest"   # Mach-O writer and loader model against LLVM tools (doc/phases/p5-macho.md)
  "scripts/elfrel-check.sh --selftest"   # ELF relocatable objects: tools, system linkers, C (doc/phases/p5-elfrel.md)
)
lake build differential cosim a64cosim mpc Tests.Elf Tests.X64 Tests.A64 Tests.Layout Tests.A64Obj Tests.Pe Tests.MachO Tests.FormatKVSrv Tests.ElfRelEmit >/dev/null
logs="$(mktemp -d)"
trap 'rm -rf "$logs"' EXIT
pids=()
for k in "${!stages[@]}"; do
  ( s=$(date +%s)
    rc=0; ${stages[$k]} > "$logs/$k.log" 2>&1 || rc=$?
    echo "$rc $(( $(date +%s) - s ))" > "$logs/$k.rc" ) &
  pids+=($!)
done
wait "${pids[@]}"
fail=0
for k in "${!stages[@]}"; do
  read -r rc secs < "$logs/$k.rc"
  echo "== ${stages[$k]} (${secs}s, exit $rc)"
  cat "$logs/$k.log"
  [ "$rc" = 0 ] || fail=1
done
if [ "$fail" != 0 ]; then echo "run-tests: a stage failed"; exit 1; fi
