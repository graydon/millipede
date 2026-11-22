#!/usr/bin/env bash
# Checks the arm64 object layer end to end. Tests/A64Obj.lean `emit` pushes the hand-assembled
# program scripts/a64/echo.s, written as literal instruction words with a fixup for every
# reference, through assembling (Asm.wordAsm), linking (Link.Config.a64Linux) and the ELF writer
# (Elf.Config.a64Linux); the loader model reads the file back and refuses its corruptions. The
# script then checks that
#  1. every literal word equals what llvm-mc assembles from the same source line;
#  2. readelf (AArch64, 64 KiB-aligned PT_LOADs, RW GNU_STACK) and eu-elflint --strict accept it;
#  3. it runs natively: with input "abc" it prints "hello\n", echoes "abc" through read and write,
#     prints "far\n" from a function 1.25 MiB away, which needs a bl beyond the reach of
#     cond19/adr21, and exits with 42, a word it loads through adrp, add :lo12: and ldr;
#  4. the same source assembled by llvm-mc and linked by ld.lld, and by gcc with GNU ld, at the
#     same section addresses gives a byte-identical .text and the same behaviour;
#  5. each seeded bug is caught: a wrong e_machine, a misaligned segment, a branch fixup without
#     the /4 scaling, x64's system-call number for write, and an adrp one page off.
# Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Tests.A64Obj >/dev/null

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT
fail=0
note() { echo "a64-elf-check: $*"; }
bad() { echo "a64-elf-check: FAIL: $*"; fail=1; }

cat > "$src/A64Emit.lean" <<'LEAN'
import Tests.A64Obj
def main (args : List String) : IO UInt32 :=
  Millipede.Tests.A64Obj.emit (args.headD ".")
LEAN
if ! lake env lean --run "$src/A64Emit.lean" "$work"; then
  bad "Lean emitter failed or the loader model gave unexpected verdicts"
fi
elf="$work/echo.elf"
[ -s "$elf" ] || { echo "a64-elf-check: no echo.elf"; exit 1; }
chmod +x "$elf"

# 1. literal words against llvm-mc
nw=0
while IFS=$'\t' read -r asm word; do
  enc=$(echo "$asm" | llvm-mc -triple=aarch64 -show-encoding 2>/dev/null | sed -n 's/.*encoding: \[\(.*\)\].*/\1/p')
  got=$(python3 -c "import sys; b=[int(x,16) for x in sys.argv[1].split(',')]; print(b[0]|b[1]<<8|b[2]<<16|b[3]<<24)" "$enc")
  [ "$got" = "$word" ] || bad "word for '$asm': Millipede $word, llvm-mc $got"
  nw=$((nw + 1))
done < "$work/words.txt"
note "$nw literal words agree with llvm-mc"

# 2. structure
out=$(readelf -h -l -W "$elf" 2>&1) || { bad "readelf rejected echo.elf"; echo "$out"; }
for pat in 'Class:[[:space:]]+ELF64' 'Type:[[:space:]]+EXEC' 'Machine:[[:space:]]+AArch64' \
           'Entry point address:[[:space:]]+0x400000' 'GNU_STACK'; do
  grep -Eq "$pat" <<<"$out" || bad "echo.elf: readelf output lacks /$pat/"
done
[ "$(grep -c 'LOAD.*0x10000$' <<<"$out")" = 3 ] || bad "echo.elf: expected three PT_LOADs aligned to 64 KiB"
grep 'GNU_STACK' <<<"$out" | grep -Eq ' RW ' || bad "echo.elf: GNU_STACK is not RW"
if grep -qi 'warning\|error' <<<"$out"; then bad "echo.elf: readelf warnings"; fi
if lint=$(eu-elflint --strict "$elf" 2>&1); then note "eu-elflint --strict accepts echo.elf"
else bad "eu-elflint --strict: $lint"; fi

# 3. run it
run() {  # file -> "status|stdout as hex"
  local rc=0 o
  o=$(printf 'abc' | "$1" 2>/dev/null | od -An -tx1 | tr -d ' \n') || rc=$?
  [ "$rc" = 0 ] && rc=$(printf 'abc' | { "$1" >/dev/null 2>&1; echo $?; })
  echo "$rc|$o"
}
want="42|$(printf 'hello\nabcfar\n' | od -An -tx1 | tr -d ' \n')"
got=$(run "$elf")
if [ "$got" = "$want" ]; then note "echo.elf runs: exit 42, prints hello / echoes abc / far"
else bad "echo.elf: got $got, expected $want"; fi

# 4. reference links
read -r _ textBase textLen < <(grep '^text' "$work/layout.txt")
read -r _ roBase < <(grep '^rodata' "$work/layout.txt")
read -r _ rwBase < <(grep '^bss' "$work/layout.txt")
hex() { printf '0x%x' "$1"; }
llvm-mc -triple=aarch64 -filetype=obj scripts/a64/echo.s -o "$work/echo.o"
ld.lld -static -e _start -z max-page-size=65536 --section-start=.text="$(hex "$textBase")" \
  --section-start=.rodata="$(hex "$roBase")" --section-start=.bss="$(hex "$rwBase")" \
  -o "$work/ref-lld.elf" "$work/echo.o"
gcc -nostdlib -static -Wl,--build-id=none -Wl,-z,max-page-size=65536 -Wl,--section-start=.text="$(hex "$textBase")" \
  -Wl,--section-start=.rodata="$(hex "$roBase")" -Wl,--section-start=.bss="$(hex "$rwBase")" \
  -o "$work/ref-gcc.elf" scripts/a64/echo.s
ourText() { dd if="$1" iflag=skip_bytes,count_bytes skip=$((0x10000)) count="$textLen" bs=65536 status=none; }
ourText "$elf" > "$work/our.text"
for r in lld gcc; do
  objcopy -O binary --only-section=.text "$work/ref-$r.elf" "$work/ref-$r.text"
  if cmp -s "$work/our.text" "$work/ref-$r.text"; then
    note ".text ($textLen bytes) identical to the $r reference"
  else bad ".text differs from the $r reference"; fi
  rgot=$(run "$work/ref-$r.elf")
  [ "$rgot" = "$got" ] || bad "the $r reference behaves differently: $rgot (ours $got)"
done

# 5. seeded bugs
patch() {  # in out offset hexbytes...
  python3 - "$@" <<'PY'
import sys
src, dst, off = sys.argv[1], sys.argv[2], int(sys.argv[3])
b = bytearray(open(src, 'rb').read())
mode = sys.argv[4]
w = int.from_bytes(b[off:off+4], 'little')
if mode == 'bytes':
    new = bytes(int(x, 16) for x in sys.argv[5:])
    b[off:off+len(new)] = new
elif mode == 'bl-bytes':      # branch26 field holding the byte distance instead of words
    imm = w & 0x3ffffff
    b[off:off+4] = ((w & ~0x3ffffff) | ((imm * 4) & 0x3ffffff)).to_bytes(4, 'little')
elif mode == 'adrp+1':        # adrp one 4 KiB page too far
    imm = ((w >> 5) & 0x7ffff) << 2 | ((w >> 29) & 3)
    imm = (imm + 1) & 0x1fffff
    w = (w & ~((0x7ffff << 5) | (3 << 29))) | ((imm >> 2) << 5) | ((imm & 3) << 29)
    b[off:off+4] = w.to_bytes(4, 'little')
elif mode == 'word':
    b[off:off+4] = int(sys.argv[5], 16).to_bytes(4, 'little')
open(dst, 'wb').write(b)
PY
  chmod +x "$2"
}
site() { grep "^$1 " "$work/sites.txt" | cut -d' ' -f2; }
patch "$elf" "$work/bad-machine.elf" 18 bytes 3e 00
patch "$elf" "$work/bad-misaligned.elf" $((64 + 56 + 16)) bytes 00 10
patch "$elf" "$work/bad-branch.elf" "$(site bl)" bl-bytes
patch "$elf" "$work/bad-sysnr.elf" "$(site svcnr)" word d2800028
patch "$elf" "$work/bad-adrp.elf" "$(site adrp)" adrp+1
for m in machine misaligned branch sysnr adrp; do
  f="$work/bad-$m.elf"
  cmp -s "$f" "$elf" && { bad "seeded bug $m did not change the file"; continue; }
  how=""
  b=$(run "$f")
  [ "$b" != "$got" ] && how="run: $b"
  ourText "$f" > "$work/bad.text"
  cmp -s "$work/bad.text" "$work/ref-lld.text" || how="$how${how:+; }.text differs from ld.lld"
  case $m in
    machine) readelf -h "$f" | grep -q 'AArch64' || how="$how${how:+; }readelf: not AArch64" ;;
    misaligned) eu-elflint --strict "$f" >/dev/null 2>&1 || how="$how${how:+; }eu-elflint" ;;
  esac
  if [ -n "$how" ]; then note "seeded bug $m caught ($how)"
  else bad "seeded bug $m NOT caught"; fi
done

if [ "$fail" = 0 ]; then echo "a64-elf-check: OK"; else echo "a64-elf-check: FAILED"; exit 1; fi
