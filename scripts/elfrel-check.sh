#!/usr/bin/env bash
# Checks the ELF64 relocatable-object writer and reader model against tools and system linkers
# (doc/phases/p5-elfrel.md).
#  1. Constants: every constant and relocation type the writer uses equals the number that
#     /usr/include/elf.h gives the same name.
#  2. Tools: `readelf -a -W` and `llvm-readobj --all` read every written object without an error
#     or a warning. An independent reader in Python, written from the gABI and the psABIs on top
#     of `llvm-readobj`'s JSON output and the file's bytes, and the Lean reader model each describe
#     the file, and both descriptions must equal that of the object the file was written from:
#     sections with their kinds, alignments, sizes and bytes, symbols, and relocations with their
#     kinds, symbols and addends. Every section named `.text`, `.rodata`, `.data` or `.bss`, or
#     with one of these names and a suffix, has the type and flags that GNU as gives a section of
#     that name.
#  3. System linkers: the objects of `hello`, `sum` and `revchunks` are linked by GNU ld and by
#     ld.lld for each machine (x86-64 with the cross linker, run under qemu-x86_64; arm64
#     natively), and each result prints the same output and exits with the same status as the
#     executable that Millipede's own linker and ELF writer make from the same object.
#  4. C: a hand-made Millipede-format object that calls `c_add` is linked with a C object that
#     defines it, and a C object whose `_start` calls the entry of `hello` is linked with that
#     program's object; both run as expected. No compiled program's object has an undefined
#     symbol, since compiled code calls nothing outside itself.
# With --selftest, every seeded bug of Tests/ElfRelEmit.lean must make at least one of these
# checks fail, and the script prints which ones.
# Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
selftest=0
[ "${1:-}" = "--selftest" ] && selftest=1

lake build Tests.ElfRelEmit >/dev/null

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT
fail=0
note() { echo "elfrel-check: $*"; }

QEMU="$HOME/tools/bin/qemu-x86_64"
XLD=x86_64-linux-gnu-ld
XCC=x86_64-linux-gnu-gcc
for t in readelf llvm-readobj as x86_64-linux-gnu-as ld ld.lld gcc "$XLD" "$XCC" "$QEMU" python3; do
  command -v "$t" >/dev/null || { note "FAIL: $t not found"; exit 1; }
done

cat > "$src/Emit.lean" <<'LEAN'
import Tests.ElfRelEmit
def main (args : List String) : IO UInt32 := Millipede.ElfRel.Emit.emit args
LEAN

# The independent reader. `describe FILE ARCH` prints the description in the Lean model's format,
# or `refused` with a reason; `undefs FILE` prints the undefined symbols.
cat > "$src/elfrel.py" <<'PY'
import json, subprocess, sys

RELOCS = {
  'x64': {'R_X86_64_PC32': 'pc32', 'R_X86_64_PLT32': 'pc32', 'R_X86_64_64': 'abs64'},
  'a64': {'R_AARCH64_ABS64': 'abs64', 'R_AARCH64_PREL32': 'pc32',
          'R_AARCH64_CALL26': 'branch26', 'R_AARCH64_JUMP26': 'branch26',
          'R_AARCH64_CONDBR19': 'cond19', 'R_AARCH64_LD_PREL_LO19': 'cond19',
          'R_AARCH64_ADR_PREL_LO21': 'adr21', 'R_AARCH64_ADR_PREL_PG_HI21': 'page21',
          'R_AARCH64_ADD_ABS_LO12_NC': 'lo12.0', 'R_AARCH64_LDST8_ABS_LO12_NC': 'lo12.0',
          'R_AARCH64_LDST16_ABS_LO12_NC': 'lo12.1', 'R_AARCH64_LDST32_ABS_LO12_NC': 'lo12.2',
          'R_AARCH64_LDST64_ABS_LO12_NC': 'lo12.3', 'R_AARCH64_LDST128_ABS_LO12_NC': 'lo12.4'}}
MACHINE = {'x64': 'EM_X86_64', 'a64': 'EM_AARCH64'}

class Refused(Exception):
    pass

def need(c, why):
    if not c:
        raise Refused(why)

def readobj(path):
    r = subprocess.run(['llvm-readobj', '--elf-output-style=JSON', '--file-header', '--sections',
                        '--symbols', '--relocations', path], capture_output=True, text=True)
    need(r.returncode == 0 and not r.stderr.strip(), 'llvm-readobj: ' + r.stderr.strip())
    return json.loads(r.stdout)[0]

STD = {'text': '.text', 'rodata': '.rodata', 'data': '.data', 'bss': '.bss'}

def kind_of(s):
    t = s['Type']['Name']
    f = sorted(x['Name'] for x in s['Flags']['Flags'])
    k = kind_flags(t, f)
    if k is not None:
        n, std = s['Name']['Name'], STD[k]
        need(n == std or n.startswith(std + '.'), 'section %s of kind %s' % (n, k))
    return k

def kind_flags(t, f):
    if t == 'SHT_PROGBITS':
        if f == ['SHF_ALLOC', 'SHF_EXECINSTR']: return 'text'
        if f == ['SHF_ALLOC']: return 'rodata'
        if f == ['SHF_ALLOC', 'SHF_WRITE']: return 'data'
        need('SHF_ALLOC' not in f, 'allocated section with flags %s' % f)
        return None
    if t == 'SHT_NOBITS':
        need(f == ['SHF_ALLOC', 'SHF_WRITE'], 'NOBITS with flags %s' % f)
        return 'bss'
    need(t in ('SHT_NULL', 'SHT_SYMTAB', 'SHT_STRTAB', 'SHT_RELA'), 'section type ' + t)
    return None

def describe(path, arch):
    d = readobj(path)
    data = open(path, 'rb').read()
    h = d['ElfHeader']
    need(h['Type'].startswith('Relocatable'), 'type ' + h['Type'])
    need(h['Machine']['Name'] == MACHINE[arch], 'machine ' + h['Machine']['Name'])
    secs = [s['Section'] for s in d['Sections']]
    objidx, out = {}, []
    for s in secs:
        k = kind_of(s)
        if k is None:
            continue
        objidx[s['Index']] = len(objidx)
        body = b'' if k == 'bss' else data[s['Offset']:s['Offset'] + s['Size']]
        out.append('section %s %s %d %d %s' % (s['Name']['Name'], k, s['AddressAlignment'],
                                               s['Size'], body.hex()))
    syms = [x['Symbol'] for x in d['Symbols']]
    need(len(syms) >= 1 and syms[0]['Name']['Name'] == '', 'no null symbol')
    for y in syms[1:]:
        if y['Type']['Name'] in ('Section', 'File') or y['Name']['Name'] == '':
            continue
        need(y['Binding']['Name'] in ('Local', 'Global'), 'binding ' + y['Binding']['Name'])
        need(y['Other']['Value'] == 0, 'visibility')
        if y['Section']['Name'] == 'Undefined':
            need(y['Binding']['Name'] == 'Global', 'undefined local')
            continue
        need(y['Section']['Value'] in objidx, 'symbol in section ' + y['Section']['Name'])
        out.append('symbol %s %d %d %s' % (y['Name']['Name'], objidx[y['Section']['Value']],
                                         y['Value'], y['Binding']['Name'].lower()))
    for rs in d.get('Relocations', []):
        target = secs[rs['SectionIndex']]['Info']
        need(target in objidx, 'relocations of section %d' % target)
        for r in rs['Relocs']:
            r = r['Relocation']
            t = r['Type']['Name']
            need(t in RELOCS[arch], 'relocation type ' + t)
            need(r['Symbol']['Name'] != '', 'relocation against an unnamed symbol')
            a = r['Addend']           # r_addend is an Elf64_Sxword; the JSON prints its bits
            a = a - 2 ** 64 if a >= 2 ** 63 else a
            out.append('reloc %d %d %s %s %d' % (objidx[target], r['Offset'], RELOCS[arch][t],
                                               r['Symbol']['Name'], a))
    # sections first, then symbols, then relocations, as the Lean description lists them
    order = {'section': 0, 'symbol': 1, 'reloc': 2}
    out.sort(key=lambda l: order[l.split(' ')[0]])
    return '\n'.join(out) + '\n'

def base_name(n):
    for std in STD.values():
        if n == std or n.startswith(std + '.'):
            return std
    return None

def flags(path, ref):
    """Sections of `path` whose type or flags differ from those GNU as gives the same name in
    the object `ref`."""
    want = {}
    for s in readobj(ref)['Sections']:
        s = s['Section']
        want[s['Name']['Name']] = (s['Type']['Name'], sorted(x['Name'] for x in s['Flags']['Flags']))
    bad = []
    for s in readobj(path)['Sections']:
        s = s['Section']
        b = base_name(s['Name']['Name'])
        if b is None:
            continue
        got = (s['Type']['Name'], sorted(x['Name'] for x in s['Flags']['Flags']))
        if got != want[b]:
            bad.append('%s is %s, GNU as gives %s' % (s['Name']['Name'], got, want[b]))
    return bad

def undefs(path):
    d = readobj(path)
    return [y['Symbol']['Name']['Name'] for y in d['Symbols'][1:]
            if y['Symbol']['Section']['Name'] == 'Undefined']

if sys.argv[1] == 'describe':
    try:
        sys.stdout.write(describe(sys.argv[2], sys.argv[3]))
    except Refused as e:
        print('refused: %s' % e)
elif sys.argv[1] == 'flags':
    try:
        print('; '.join(flags(sys.argv[2], sys.argv[3])))
    except Refused as e:
        print('unreadable: %s' % str(e)[:160])
elif sys.argv[1] == 'undefs':
    print(' '.join(undefs(sys.argv[2])))
PY
py() { python3 -I "$src/elfrel.py" "$@"; }

cat > "$src/c_add.c" <<'C'
int c_add(int a, int b) { return a + b; }
C
CFLAGS="-c -O2 -ffreestanding -fno-pic -fno-stack-protector -fno-asynchronous-unwind-tables"

# Runs a program with input $2 and prints its output and exit status.
run() {
  local exe=$1 input=$2 arch=$3 out rc=0
  if [ "$arch" = x64 ]; then
    out=$(printf '%s' "$input" | "$QEMU" "$exe" 2>&1 | tr -d '\000'; exit "${PIPESTATUS[1]}") || rc=$?
  else
    out=$(printf '%s' "$input" | "$exe" 2>&1 | tr -d '\000'; exit "${PIPESTATUS[1]}") || rc=$?
  fi
  printf '%s|exit %s' "$out" "$rc"
}

input_of() {
  case $1 in
    revchunks-*) echo "abcdefghijklmnopqrstuvwxyz0123456789" ;;
    *) echo -n "" ;;
  esac
}

# check DIR: runs checks 2 to 4 on the files in DIR and prints `FAIL[check]: ...` for each
# failure.
check() {
  local d=$1 f n arch exp got entry ldo lldo
  for f in "$d"/*.o; do
    n=$(basename "$f" .o); arch=${n##*-}
    # 2. tools
    if ! readelf -a -W "$f" >"$d/$n.readelf" 2>"$d/$n.readelf.err" || [ -s "$d/$n.readelf.err" ]; then
      echo "FAIL[readelf]: $n: $(head -c 200 "$d/$n.readelf.err")"
    fi
    if ! llvm-readobj --all "$f" >/dev/null 2>"$d/$n.readobj.err" || [ -s "$d/$n.readobj.err" ]; then
      echo "FAIL[llvm-readobj]: $n: $(head -c 200 "$d/$n.readobj.err")"
    fi
    if ! cmp -s "$d/$n.desc" "$d/$n.model"; then
      echo "FAIL[model]: $n: the Lean reader model does not read the file as the object written:"
      diff "$d/$n.desc" "$d/$n.model" | head -6 | cut -c1-160
    fi
    py describe "$f" "$arch" > "$d/$n.pydesc"
    if ! cmp -s "$d/$n.desc" "$d/$n.pydesc"; then
      echo "FAIL[describe]: $n: the Python reader does not read the file as the object written:"
      diff "$d/$n.desc" "$d/$n.pydesc" | head -6 | cut -c1-160
    fi
    got=$(py flags "$f" "$src/std-$arch.o")
    [ -z "$got" ] || echo "FAIL[flags]: $n: $got"
  done
  # 3. system linkers
  for f in "$d"/hello-*.o "$d"/sum-*.o "$d"/revchunks-*.o; do
    n=$(basename "$f" .o); arch=${n##*-}
    entry=$(cat "$d/$n.entry")
    exp=$(run "$d/$n.mp" "$(input_of "$n")" "$arch")
    if [ "$arch" = x64 ]; then
      ldo=$($XLD -static -e "$entry" -o "$d/$n.ld" "$f" 2>&1) || echo "FAIL[ld]: $n: $ldo"
      lldo=$(ld.lld -m elf_x86_64 -static -e "$entry" -o "$d/$n.lld" "$f" 2>&1) || echo "FAIL[ld.lld]: $n: $lldo"
    else
      ldo=$(ld -static -e "$entry" -o "$d/$n.ld" "$f" 2>&1) || echo "FAIL[ld]: $n: $ldo"
      lldo=$(ld.lld -static -e "$entry" -o "$d/$n.lld" "$f" 2>&1) || echo "FAIL[ld.lld]: $n: $lldo"
    fi
    [ -n "$ldo" ] && echo "FAIL[ld]: $n: warning: $ldo"
    [ -n "$lldo" ] && echo "FAIL[ld.lld]: $n: warning: $lldo"
    for l in ld lld; do
      [ -x "$d/$n.$l" ] || continue
      got=$(run "$d/$n.$l" "$(input_of "$n")" "$arch")
      if [ "$got" != "$exp" ]; then
        echo "FAIL[run-$l]: $n: system-linked '$got' but Millipede-linked '$exp'"
      fi
    done
    [ -z "$(py undefs "$f")" ] || echo "FAIL[undefs]: $n: undefined symbols $(py undefs "$f")"
  done
  # 4. C: Millipede code calls C
  gcc $CFLAGS -o "$d/c_add-a64.co" "$src/c_add.c"
  $XCC $CFLAGS -o "$d/c_add-x64.co" "$src/c_add.c"
  $XLD -static -e _start -o "$d/c-x64.exe" "$d/c-x64.o" "$d/c_add-x64.co" 2>/dev/null \
    || echo "FAIL[c-calls]: x64 link"
  ld -static -e _start -o "$d/c-a64.exe" "$d/c-a64.o" "$d/c_add-a64.co" 2>/dev/null \
    || echo "FAIL[c-calls]: a64 link"
  for arch in x64 a64; do
    [ -x "$d/c-$arch.exe" ] || continue
    got=$(run "$d/c-$arch.exe" "" "$arch")
    [ "$got" = "|exit 42" ] || echo "FAIL[c-calls]: $arch: '$got', expected exit 42"
  done
  # 4. C: C calls the entry of a compiled program
  for arch in x64 a64; do
    entry=$(cat "$d/hello-$arch.entry")
    printf 'extern void %s(void) __attribute__((noreturn));\nvoid _start(void) { %s(); }\n' \
      "$entry" "$entry" > "$d/start-$arch.c"
    if [ "$arch" = x64 ]; then
      $XCC $CFLAGS -o "$d/start-$arch.co" "$d/start-$arch.c"
      $XLD -static -e _start -o "$d/start-$arch.exe" "$d/start-$arch.co" "$d/hello-$arch.o" 2>/dev/null \
        || echo "FAIL[c-entry]: $arch link"
    else
      gcc $CFLAGS -o "$d/start-$arch.co" "$d/start-$arch.c"
      ld -static -e _start -o "$d/start-$arch.exe" "$d/start-$arch.co" "$d/hello-$arch.o" 2>/dev/null \
        || echo "FAIL[c-entry]: $arch link"
    fi
    [ -x "$d/start-$arch.exe" ] || continue
    got=$(run "$d/start-$arch.exe" "" "$arch")
    [ "$got" = "hello, world|exit 0" ] || echo "FAIL[c-entry]: $arch: '$got'"
  done
}

# The sections that GNU as makes for the standard names, for the flags check.
printf '.text\n.section .rodata\n.data\n.bss\n' > "$src/std.s"
as -o "$src/std-a64.o" "$src/std.s"
x86_64-linux-gnu-as -o "$src/std-x64.o" "$src/std.s"

# 1. constants against <elf.h>
seedarg=(); [ "$selftest" = 1 ] && seedarg=(--seeds)
lake env lean --run "$src/Emit.lean" "$work" "${seedarg[@]}" >"$work/emit.log" 2>&1 || {
  cat "$work/emit.log"; note "FAIL: emit"; exit 1; }
[ "$selftest" = 1 ] && base="$work/none" || base="$work"
bad_consts=$(python3 -I - "$work/consts.txt" <<'PY'
import re, sys
h = open('/usr/include/elf.h').read()
for line in open(sys.argv[1]):
    name, val = line.split()
    m = re.search(r'^#define\s+%s\s+(.+?)\s*(/\*.*)?$' % name, h, re.M)
    if not m or eval(m.group(1)) != int(val):
        print('%s is %s, <elf.h> says %s' % (name, val, m.group(1) if m else 'nothing'))
PY
)
[ -z "$bad_consts" ] || { note "FAIL: $bad_consts"; fail=1; }
note "constants: $(wc -l < "$work/consts.txt") compared with <elf.h>"

out=$(check "$base")
if [ -n "$out" ]; then
  echo "$out"; fail=1
else
  note "$(ls "$base"/*.o | wc -l) objects: readelf and llvm-readobj accept them, the model and the Python reader read each as the object written, and the section flags are those of GNU as"
  note "hello, sum, revchunks: GNU ld and ld.lld executables behave as Millipede's own (x64 and arm64)"
  note "C: Millipede code calls c_add (exit 42), and a C _start calls hello's entry (both machines)"
fi

if [ "$selftest" = 1 ]; then
  for s in reltype addend textflags machine symorder symglobal bssndx; do
    out=$(check "$work/$s")
    if [ -z "$out" ]; then
      note "FAIL: seeded bug '$s' was not caught"; fail=1
    else
      caught=$(echo "$out" | grep -o '^FAIL\[[a-z0-9.-]*\]' | sort -u | tr -d '[]' | sed 's/FAIL//' | tr '\n' ' ')
      note "seeded bug '$s' caught by: $caught"
    fi
  done
fi

[ "$fail" = 0 ] && note "all checks passed"
exit "$fail"
