#!/usr/bin/env bash
# Checks the ELF64 writer and the loader model end to end.
#  1. The Lean writer emits hello.elf (mov eax,60; mov edi,42; syscall), a two-segment file and
#     corrupted variants; the Lean loader model's verdict on each is printed and checked.
#  2. readelf -h -l accepts the good files and shows the expected headers.
#  3. qemu-x86_64 runs them and they exit with status 42.
#  4. qemu refuses the corrupted files it can detect: bad magic, class, machine, phentsize and a
#     truncated header.
# Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"

lake build Tests.Elf >/dev/null

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT

cat > "$src/ElfEmit.lean" <<'LEAN'
import Tests.Elf
def main (args : List String) : IO UInt32 :=
  Millipede.Elf.Tests.emit (args.headD ".")
LEAN

fail=0
note() { echo "elf-check: $*"; }
bad() { echo "elf-check: FAIL: $*"; fail=1; }

if ! lake env lean --run "$src/ElfEmit.lean" "$work"; then
  bad "Lean loader model gave unexpected verdicts"
fi

for f in hello two; do
  out=$(readelf -h -l "$work/$f.elf" 2>&1) || { bad "readelf rejected $f.elf"; echo "$out"; continue; }
  for pat in 'Class:[[:space:]]+ELF64' 'Data:[[:space:]]+2.s complement, little endian' \
             'Type:[[:space:]]+EXEC' 'Machine:[[:space:]]+Advanced Micro Devices X86-64' \
             'Entry point address:[[:space:]]+0x400000' 'LOAD' 'GNU_STACK' ; do
    grep -Eq "$pat" <<<"$out" || bad "$f.elf: readelf output lacks /$pat/"
  done
  # the stack must not be executable: GNU_STACK flags RW
  grep -A1 'GNU_STACK' <<<"$out" | grep -Eq 'RW[[:space:]]' || bad "$f.elf: GNU_STACK is not RW"
  grep -Eq 'LOAD.*' <<<"$out" && grep -A1 'LOAD' <<<"$out" | grep -q 'R E' \
    || bad "$f.elf: code segment is not R E"
  if readelf -h -l "$work/$f.elf" 2>&1 | grep -qi 'warning\|error'; then
    bad "$f.elf: readelf warnings"; readelf -h -l "$work/$f.elf" 2>&1 | grep -i 'warning\|error'
  fi
  chmod +x "$work/$f.elf"
  set +e; "$QEMU" "$work/$f.elf"; rc=$?; set -e
  if [ "$rc" -eq 42 ]; then note "$f.elf runs under qemu, exit status 42"
  else bad "$f.elf: exit status $rc under qemu (expected 42)"; fi
done

# A header cut short is refused by qemu too.
head -c 40 "$work/hello.elf" > "$work/bad-short-header.elf"
for n in bad-magic class32 machine-arm64 phentsize short-header; do
  f="$work/bad-$n.elf"; chmod +x "$f"
  set +e; "$QEMU" "$f" >/dev/null 2>&1; rc=$?; set -e
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 42 ]; then note "qemu refuses bad-$n.elf (status $rc)"
  else bad "qemu ran bad-$n.elf (status $rc)"; fi
done

[ "$fail" -eq 0 ] && echo "elf-check: OK" || { echo "elf-check: FAILED"; exit 1; }
