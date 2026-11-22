#!/usr/bin/env bash
# Checks the PE32+ writer and loader model (Millipede/Object/Pe/) against LLVM's tools and runs
# the files under wine (box64 + amd64 wine64). There is no Windows machine here: wine's loader is
# more lenient than Windows', so the structural checks against llvm-readobj and lld-link stay.
#  1. Tests/Pe.lean `emit` writes ret42.exe, exit42.exe and hello.exe with the Lean writer, the
#     loader model's description of each (<name>.model), and the corrupted files of
#     Tests/Pe.lean, each of which the loader model must refuse.
#  2. llvm-readobj reads each file without a warning, and what it reports agrees with the model:
#     machine, PE32+, console subsystem, DYNAMIC_BASE / HIGH_ENTROPY_VA / NX_COMPAT, no base
#     relocations, image base, entry point, stack reserve = commit = the model's stack plus the
#     64 KiB margin, each section's address, size and permission, and the imports (DLL, address
#     table RVA, functions in order).
#  3. The same programs, written in assembly, are assembled by llvm-mc and linked by lld-link
#     against an import library for kernel32.dll made by llvm-dlltool, with the same base and
#     stack. The headers the loader relies on agree with lld-link's file, the program sections
#     have the same addresses and permissions, lld-link's imports are among ours, and
#     llvm-objdump disassembles both .text sections to the same instructions once every
#     rip-relative target is named (an import address table slot by its function, other targets
#     by section and offset).
#  4. Under wine, ret42.exe and exit42.exe exit with status 42, and hello.exe prints "hello\n" and
#     exits with 7. Skipped with a note when box64 or wine is missing.
# With --selftest, each of a set of seeded bugs is patched into a good file (a wrong machine, a
# call through the wrong address table slot, a writable .rdata, a misspelt import, a different
# stack reserve, an image base off by a page, a moved entry point, a truncated file) and some
# check must catch each one; under wine the wrong machine is refused and the call through the
# wrong slot runs differently.
# With PE_OUT=<dir>, the three good files are copied to <dir> (to run them on Windows).
# Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
selftest=0
[ "${1:-}" = --selftest ] && selftest=1

lake build Tests.Pe >/dev/null

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT
fail=0
note() { echo "pe-check: $*"; }
bad() { echo "pe-check: FAIL: $*"; fail=1; }

cat > "$src/PeEmit.lean" <<'LEAN'
import Tests.Pe
def main (args : List String) : IO UInt32 :=
  match args with
  | "verdict" :: fs => Millipede.Pe.Tests.verdicts fs
  | dir :: _ => Millipede.Pe.Tests.emit dir
  | [] => Millipede.Pe.Tests.emit "."
LEAN
lean_run() { lake env lean --run "$src/PeEmit.lean" "$@"; }

# 1. the Lean writer and loader model
if ! lean_run "$work" > "$work/emit.log"; then
  cat "$work/emit.log"; bad "Lean emitter failed or the loader model gave unexpected verdicts"
fi
grep -q 'unexpected' "$work/emit.log" && note "$(grep 'corrupted files' "$work/emit.log")"
if [ -n "${PE_OUT:-}" ]; then mkdir -p "$PE_OUT"; cp "$work"/ret42.exe "$work"/exit42.exe "$work"/hello.exe "$PE_OUT"/; note "copied ret42.exe exit42.exe hello.exe to $PE_OUT"; fi

# 3. reference files from lld-link
cat > "$src/kernel32.def" <<'DEF'
LIBRARY kernel32.dll
EXPORTS
ExitProcess
GetStdHandle
WriteFile
ReadFile
DEF
cat > "$src/ret42.s" <<'ASM'
  .text
  .globl start
start:
  movl $42, %eax
  retq
ASM
cat > "$src/exit42.s" <<'ASM'
  .text
  .globl start
start:
  subq $40, %rsp
  movl $42, %ecx
  callq *__imp_ExitProcess(%rip)
  int3
ASM
cat > "$src/hello.s" <<'ASM'
  .text
  .globl start
start:
  subq $56, %rsp
  movl $-11, %ecx
  callq *__imp_GetStdHandle(%rip)
  movq %rax, %rcx
  leaq msg(%rip), %rdx
  movl $6, %r8d
  leaq written(%rip), %r9
  movq $0, 32(%rsp)
  callq *__imp_WriteFile(%rip)
  movl $7, %ecx
  callq *__imp_ExitProcess(%rip)
  int3
  .section .rdata,"dr"
msg:
  .ascii "hello\n"
  .bss
  .p2align 3
written:
  .zero 8
ASM
llvm-dlltool -m i386:x86-64 -d "$src/kernel32.def" -l "$work/kernel32.lib"
for p in ret42 exit42 hello; do
  case $p in hello) stack=0x20000 ;; *) stack=0x12000 ;; esac
  llvm-mc -triple=x86_64-pc-windows-msvc -filetype=obj "$src/$p.s" -o "$work/$p.obj"
  lld-link /nologo /subsystem:console /entry:start /nodefaultlib /dynamicbase /highentropyva \
    /base:0x140000000 /stack:$stack,$stack /out:"$work/ref-$p.exe" "$work/$p.obj" \
    "$work/kernel32.lib"
done

cat > "$src/pecmp.py" <<'PY'
import re, subprocess, sys

def readobj(path):
    r = subprocess.run(['llvm-readobj', '--file-headers', '--sections', '--coff-imports',
                        '--coff-basereloc', path], capture_output=True, text=True)
    if r.returncode != 0 or r.stderr.strip():
        return None, (r.stderr.strip() or 'llvm-readobj failed').splitlines()[0]
    d = {'sections': [], 'imports': [], 'dllchars': set(), 'relocs': 0}
    cur = None; where = None
    for line in r.stdout.splitlines():
        s = line.strip()
        if s == 'Section {': cur = {}; d['sections'].append(cur); where = 'sec'; continue
        if s == 'Import {': cur = {'syms': []}; d['imports'].append(cur); where = 'imp'; continue
        if s.startswith('ImageOptionalHeader'): where = 'opt'
        if s.startswith('Entry {') and where == 'reloc': d['relocs'] += 1
        if s.startswith('BaseReloc ['): where = 'reloc'
        if where == 'sec' and s.startswith('Characteristics ['):
            cur['Characteristics'] = int(re.search(r'\((0x[0-9A-Fa-f]+)\)', s).group(1), 16)
            continue
        m = re.match(r'IMAGE_DLL_CHARACTERISTICS_(\w+)', s)
        if m: d['dllchars'].add(m.group(1))
        m = re.match(r'([A-Za-z]+): (.*)', s)
        if not m: continue
        k, v = m.group(1), m.group(2)
        if where == 'sec' and k in ('Name', 'VirtualSize', 'VirtualAddress', 'RawDataSize'):
            cur[k] = v.split()[0]
        elif where == 'imp' and k == 'Symbol':
            cur['syms'].append(v.split()[0])
        elif where == 'imp':
            cur[k] = v
        elif k not in d:
            d[k] = v
    return d, None

def num(v): return int(v.split()[0], 0)

def perm(ch):
    return ('r' if ch & 0x40000000 else '-') + ('w' if ch & 0x80000000 else '-') + \
           ('x' if ch & 0x20000000 else '-')

def model(path):
    m = {'sections': [], 'imports': []}
    for line in open(path):
        w = line.split()
        if w[0] in ('section', 'idata'): m['sections'].append((int(w[1]), int(w[2]), w[3]))
        elif w[0] == 'import': m['imports'].append(w[1])
        else: m[w[0]] = w[1]
    return m

def disasm(path, d):
    """The .text instructions, with each rip-relative target named."""
    base = num(d['ImageBase'])
    slots = {}
    for imp in d['imports']:
        iat = base + num(imp['ImportAddressTableRVA'])
        for k, f in enumerate(imp['syms']): slots[iat + 8 * k] = 'iat:' + f
    secs = [(base + num(s['VirtualAddress']), s['Name'], perm(s['Characteristics']))
            for s in d['sections']]
    def name(a):
        if a in slots: return slots[a]
        own = [s for s in secs if s[0] <= a]
        if not own: return hex(a)
        s = max(own); return '%s+%d' % (s[2], a - s[0])
    r = subprocess.run(['llvm-objdump', '-d', '--no-show-raw-insn', '-j', '.text', path],
                       capture_output=True, text=True)
    out = []
    for line in r.stdout.splitlines():
        m = re.match(r'\s*[0-9a-f]+:\s+(.*)', line)
        if not m: continue
        ins = m.group(1)
        t = re.search(r'#\s*0x([0-9a-f]+)', ins)
        ins = re.sub(r'-?0x[0-9a-f]+\(%rip\)', '(%rip)', ins.split('#')[0]).split()
        out.append(' '.join(ins) + (' -> ' + name(int(t.group(1), 16)) if t else ''))
    return out

def check(ours, modelf, ref):
    d, err = readobj(ours)
    if d is None: return ['llvm-readobj: ' + err]
    p = []
    def want(cond, what):
        if not cond: p.append(what)
    m = model(modelf)
    want(d.get('Machine', '').startswith('IMAGE_FILE_MACHINE_AMD64'), 'machine')
    want(d.get('Magic') == '0x20B', 'not PE32+')
    want('WINDOWS_CUI' in d.get('Subsystem', ''), 'subsystem')
    want({'DYNAMIC_BASE', 'HIGH_ENTROPY_VA', 'NX_COMPAT'} <= d['dllchars'], 'dll characteristics')
    want(num(d['BaseRelocationTableRVA']) == 0 and d['relocs'] == 0, 'base relocations')
    want(num(d['ImageBase']) == int(m['base']), 'image base %s, model %s' % (d['ImageBase'], m['base']))
    want(num(d['AddressOfEntryPoint']) == int(m['entry']), 'entry point')
    want(num(d['SizeOfStackReserve']) == int(m['stack']) + 0x10000, 'stack reserve')
    want(d['SizeOfStackCommit'] == d['SizeOfStackReserve'], 'stack commit')
    got = [(num(s['VirtualAddress']), num(s['VirtualSize']), perm(s['Characteristics']))
           for s in d['sections']]
    want(got == m['sections'], 'sections %s, model %s' % (got, m['sections']))
    want(len(d['imports']) == 1, 'one import descriptor')
    if d['imports']:
        imp = d['imports'][0]
        want(imp['Name'] == m['dll'], 'dll name')
        want(num(imp['ImportAddressTableRVA']) == int(m['iat']), 'address table RVA')
        want(imp['syms'] == m['imports'], 'imports %s, model %s' % (imp['syms'], m['imports']))
    # against lld-link
    r, err = readobj(ref)
    if r is None: return p + ['reference: ' + err]
    for k in ('Machine', 'Magic', 'SectionAlignment', 'FileAlignment', 'MajorOperatingSystemVersion',
              'MajorSubsystemVersion', 'Subsystem', 'ImageBase', 'AddressOfEntryPoint',
              'SizeOfStackReserve', 'SizeOfStackCommit', 'SizeOfHeapReserve', 'SizeOfHeapCommit',
              'NumberOfRvaAndSize', 'BaseRelocationTableRVA'):
        want(d.get(k) == r.get(k), '%s: ours %s, lld-link %s' % (k, d.get(k), r.get(k)))
    want(d['dllchars'] == r['dllchars'], 'dll characteristics differ from lld-link')
    for a, b in zip(d['sections'], r['sections']):
        want((a['Name'], a['VirtualAddress'], a['Characteristics']) ==
             (b['Name'], b['VirtualAddress'], b['Characteristics']),
             'section %s differs from lld-link %s' % (a, b))
    if r['imports']:
        ri = r['imports'][0]
        want(d['imports'] and d['imports'][0]['Name'].lower() == ri['Name'].lower()
             and set(ri['syms']) <= set(d['imports'][0]['syms']), 'imports differ from lld-link')
    da, db = disasm(ours, d), disasm(ref, r)
    want(da and da == db, 'disassembly differs from lld-link:\n  ' + '\n  '.join(
        '%-50s | %s' % (x, y) for x, y in zip(da + [''] * len(db), db + [''] * len(da))))
    return p

if __name__ == '__main__':
    try:
        probs = check(*sys.argv[1:4])
    except Exception as e:
        print('internal error: %r' % e); sys.exit(3)
    for q in probs: print(q)
    sys.exit(1 if probs else 0)
PY
cmp_() { python3 -I "$src/pecmp.py" "$@"; }

# 2 and 3 on the good files
for p in ret42 exit42 hello; do
  if out=$(cmp_ "$work/$p.exe" "$work/$p.model" "$work/ref-$p.exe"); then
    note "$p.exe: llvm-readobj agrees with the model, headers and disassembly agree with lld-link"
  else
    bad "$p.exe:"; echo "$out" | sed 's/^/    /'
  fi
done

# 4. run under wine
WINE=/usr/lib/wine/wine64
havewine=0
if command -v box64 >/dev/null && [ -x "$WINE" ]; then havewine=1
else note "box64 or wine missing: files not run"; fi
prefix="${PE_WINEPREFIX:-$HOME/.cache/millipede-pe-wine}"
wrun() {  # file -> "status|stdout as hex"
  local rc=0
  (cd "$(dirname "$1")" && WINEPREFIX="$prefix" WINEDEBUG=-all BOX64_LOG=0 BOX64_NOBANNER=1 \
    timeout 300 box64 "$WINE" "./$(basename "$1")" > "$work/wine.out" 2>/dev/null) || rc=$?
  echo "$rc|$(od -An -tx1 "$work/wine.out" | tr -d ' \n')"
}
hexof() { printf '%s' "$1" | od -An -tx1 | tr -d ' \n'; }
if [ "$havewine" = 1 ]; then
  mkdir -p "$prefix"
  for t in "ret42|42|" "exit42|42|" "hello|7|$(hexof $'hello\n')"; do
    IFS='|' read -r p st out <<<"$t"
    got=$(wrun "$work/$p.exe")
    if [ "$got" = "$st|$out" ]; then note "$p.exe runs under wine: exit $st${out:+, prints hello}"
    else bad "$p.exe under wine: got $got, expected $st|$out"; fi
  done
fi

if [ "$selftest" = 1 ]; then
  patch() {  # in out offset hexbytes... | in out truncate n
    python3 -I - "$@" <<'PY'
import sys
src, dst, off = sys.argv[1], sys.argv[2], sys.argv[3]
b = bytearray(open(src, 'rb').read())
if off == 'truncate':
    b = b[:int(sys.argv[4])]
else:
    off = int(off); new = bytes(int(x, 16) for x in sys.argv[4:]); b[off:off + len(new)] = new
open(dst, 'wb').write(b)
PY
  }
  h="$work/hello.exe"
  # hello: .text raw data at 512; `call [GetStdHandle]` displacement at 512 + 11
  patch "$h" "$work/seed-machine.exe" 68 4c 01
  patch "$h" "$work/seed-slot.exe" $((512 + 11)) 51
  patch "$h" "$work/seed-rdata-rw.exe" $((328 + 40 + 39)) c0
  patch "$h" "$work/seed-import-name.exe" $((1536 + 134 + 14 + 16 + 2 + 8)) 66
  patch "$h" "$work/seed-stack.exe" 162 03
  patch "$h" "$work/seed-base.exe" 113 10
  patch "$h" "$work/seed-entry.exe" 104 01 10
  patch "$h" "$work/seed-truncated.exe" truncate 1700
  seeds=(machine slot rdata-rw import-name stack base entry truncated)
  lean_run verdict $(for s in "${seeds[@]}"; do echo "$work/seed-$s.exe"; done) > "$work/verdicts"
  for s in "${seeds[@]}"; do
    f="$work/seed-$s.exe"
    cmp -s "$f" "$h" && { bad "seeded bug $s did not change the file"; continue; }
    how=""
    rc=0; out=$(cmp_ "$f" "$work/hello.model" "$work/ref-hello.exe") || rc=$?
    [ "$rc" = 3 ] && { bad "seeded bug $s: $out"; continue; }
    if [ "$rc" = 1 ]; then first=${out%%$'\n'*}; how="tools: ${first:0:70}"; fi
    grep -q "seed-$s.exe refused" "$work/verdicts" && how="$how${how:+; }loader model refuses"
    if [ "$havewine" = 1 ] && { [ "$s" = machine ] || [ "$s" = slot ]; }; then
      w=$(wrun "$f")
      if [ "$w" != "7|$(hexof $'hello\n')" ]; then how="$how${how:+; }wine: exit ${w%%|*}"
      else bad "seeded bug $s runs like the good file under wine"; fi
    fi
    if [ -n "$how" ]; then note "seeded bug $s caught ($how)"
    else bad "seeded bug $s NOT caught"; fi
  done
fi

if [ "$fail" = 0 ]; then echo "pe-check: OK"; else echo "pe-check: FAILED"; exit 1; fi
