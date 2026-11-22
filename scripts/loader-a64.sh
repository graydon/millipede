#!/usr/bin/env bash
# Compares the arm64 loader model with the kernel. `differential loader-a64` compiles a program
# with a data region for arm64Linux, writes the ELF and prints the facts of the model's initial
# state `img.init A64.linux`, which `A64.Init` uses (Tests/Differential/LoaderA64.lean). This
# script starts the ELF natively under gdb, stopped before its first instruction (`starti`), and
# compares those facts with what the kernel gave: pc is the entry; sp is 16-byte aligned; x0 … x30
# are zero; the `fw F` frame words of main below sp are zero; the data region mp_mem is readable,
# writable and zero; and the page at pc is r-x. The model's sp is not the kernel's stack top,
# which the compiled code never observes, so only the alignment and the zero memory below sp are
# compared. Exit status 0 means the model agrees with the kernel on every fact.
#   --selftest: the model with a seeded error (sp 8 bytes lower, entry pc + 4, x0 = 1) must
#   disagree with the kernel.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build differential >/dev/null
EXE=.lake/build/bin/differential
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# the kernel's facts about the start of $1, one `key value` per line with the model's keys
kernel_facts() {
  local elf=$1 F=$2 mem=$3 msz=$4 cmds="$work/cmds.gdb"
  {
    echo 'set pagination off'
    echo 'starti'
    echo 'printf "pc %lu\n", $pc'
    echo 'printf "sp16 %lu\n", (unsigned long)$sp % 16'
    for i in $(seq 0 30); do echo "printf \"x$i %lu\\n\", \$x$i"; done
    [ "$F" -gt 0 ] && echo "dump binary memory $work/frame.bin \$sp-8*$F \$sp"
    [ "$msz" -gt 0 ] && echo "dump binary memory $work/mem.bin $mem $mem+$msz"
    echo 'info proc mappings'
    echo 'kill'
  } > "$cmds"
  : > "$work/frame.bin"; : > "$work/mem.bin"
  gdb -batch -nx -x "$cmds" "$elf" > "$work/gdb.out" 2>&1 || true
  local pc sp16 xz=1
  pc=$(awk '$1=="pc"{print $2}' "$work/gdb.out")
  sp16=$(awk '$1=="sp16"{print $2}' "$work/gdb.out")
  for i in $(seq 0 30); do
    [ "$(awk -v k="x$i" '$1==k{print $2}' "$work/gdb.out")" = 0 ] || xz=0
  done
  echo "pc $pc"
  echo "sp16 $sp16"
  echo "xzero $xz"
  # zero bytes: the dump has the expected length and no non-zero byte
  zero() { [ "$(stat -c %s "$1")" = "$2" ] && ! od -An -v -tx1 "$1" | grep -q '[1-9a-f]'; }
  if zero "$work/frame.bin" $((8 * F)); then echo "framezero 1"; else echo "framezero 0"; fi
  # the permissions of the mapping holding an address (gdb's `info proc mappings`, Perms column)
  perms() {
    local s e rest p
    while read -r s e rest; do
      [[ "$s" == 0x* && "$e" == 0x* ]] || continue
      if (( s <= $1 && $1 < e )); then
        for p in $rest; do [[ "$p" =~ ^[r-][w-][x-][ps]$ ]] && { echo "$p"; return; }; done
      fi
    done < "$work/gdb.out"
  }
  local mp tp
  mp=$(perms "$mem"); tp=$(perms "$pc")
  if zero "$work/mem.bin" "$msz" && [[ "$mp" == rw-* ]]; then echo "memrw 1"; else echo "memrw 0"; fi
  if [[ "$tp" == r-x* ]]; then echo "textrx 1"; else echo "textrx 0"; fi
}

# compare the model (with seed $1) with the kernel: status 0 iff they agree on every fact
check() {
  local seed=${1:-}
  $EXE loader-a64 "$work" $seed > "$work/model.txt"
  local F mem msz
  F=$(awk '$1=="frame"{print $2}' "$work/model.txt")
  mem=$(awk '$1=="mem"{print $2}' "$work/model.txt")
  msz=$(awk '$1=="memsize"{print $2}' "$work/model.txt")
  kernel_facts "$work/loader.elf" "$F" "$mem" "$msz" > "$work/kernel.txt"
  local ok=0
  [ "$(awk '$1=="sptop"{print $2}' "$work/model.txt")" = 1 ] || { echo "model: sp is not the stack region's top"; ok=1; }
  for k in pc sp16 xzero framezero memrw textrx; do
    local m r
    m=$(awk -v k=$k '$1==k{print $2}' "$work/model.txt")
    r=$(awk -v k=$k '$1==k{print $2}' "$work/kernel.txt")
    if [ -z "$r" ] || [ "$m" != "$r" ]; then echo "$k: model '$m', kernel '$r'"; ok=1; fi
  done
  # the facts A64.Init asserts must hold in the kernel's process
  for k in sp16:0 xzero:1 framezero:1 memrw:1 textrx:1; do
    [ "$(awk -v k=${k%%:*} '$1==k{print $2}' "$work/kernel.txt")" = "${k##*:}" ] ||
      { echo "kernel: ${k%%:*} is not ${k##*:}"; ok=1; }
  done
  return $ok
}

if [ "${1:-}" = "--selftest" ]; then
  fail=0
  for s in sp pc x0; do
    if check "$s" > "$work/seed.txt"; then
      echo "loader-a64 selftest: seed $s NOT caught"; fail=1
    else
      echo "loader-a64 selftest: seed $s caught ($(head -1 "$work/seed.txt"))"
    fi
  done
  exit $fail
fi

if check; then
  echo "loader-a64: model and kernel agree: $(tr '\n' ' ' < "$work/kernel.txt")"
  echo "loader-a64: frame $(awk '$1=="frame"{print $2}' "$work/model.txt") words, mp_mem $(awk '$1=="memsize"{print $2}' "$work/model.txt") bytes"
else
  echo "loader-a64: FAIL"; cat "$work/gdb.out" | tail -20; exit 1
fi
