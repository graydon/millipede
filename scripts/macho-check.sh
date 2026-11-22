#!/usr/bin/env bash
# Checks the Mach-O writer, the loader model and SHA-256 against tools. This machine is not a
# Mac, so nothing here runs a file; doc/phases/p5-macho.md says how to run one on a Mac.
#  1. SHA-256: the Lean function hashes files of 0 to 70000 bytes exactly as sha256sum does.
#  2. Tests/MachO.lean `emit` writes hello, two and three (.macho), the loader model's description
#     of each (.model) and the corruptions; every good file must load and every corruption must
#     be refused by the model.
#  3. An independent checker, written in Python from Apple's headers (mach-o/loader.h and the
#     code-signing blob layout), parses each good file, checks the platform rules (arm64
#     MH_EXECUTE, PIE, __PAGEZERO, dyld, libSystem, LC_MAIN, W^X, page alignment, no overlap),
#     rebuilds the ad-hoc signature from scratch and requires it byte-identical, recomputing every
#     page hash with hashlib; its description of the segments, entry point and stack must equal
#     the model's. It must reject every corruption.
#  4. llvm-readobj --all and llvm-otool -l read each good file without complaint, and their
#     segments, protections, entry offset and stack size give the model's description;
#     llvm-objdump -d disassembles the code to the expected instructions.
#  5. The same programs, assembled by llvm-mc and linked by ld64.lld-19 (with a TAPI stub of
#     libSystem), have the same header, the same sequence of load commands, the same dyld and
#     libSystem paths, platform, __PAGEZERO, stack size and signature parameters, and the same
#     instructions (byte-identical code for hello).
# With --selftest, seeded bugs must each be caught: a SHA-256 with one round constant wrong;
# files that were corrupted and then re-signed, so that only the model's rules or the comparison
# with the expected description can catch them (W+X data, a section of initialiser pointers, a
# segment moved by a page, an entry point moved by one instruction, a smaller stack, platform
# iOS); a signature whose identifier differs from the one the writer uses; and a writer that
# hashes the last, partial page of the file padded with zeros.
# Exit status 0 means every check passed.
set -euo pipefail
cd "$(dirname "$0")/.."
selftest=0
[ "${1:-}" = "--selftest" ] && selftest=1

lake build Tests.MachO >/dev/null

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT
fail=0
note() { echo "macho-check: $*"; }
bad() { echo "macho-check: FAIL: $*"; fail=1; }

cat > "$src/MachOEmit.lean" <<'LEAN'
import Tests.MachO
open Millipede Millipede.MachO
def main (args : List String) : IO UInt32 := do
  match args with
  | "hash" :: fs => Tests.hashFiles fs; return 0
  | "parse" :: fs =>
    for f in fs do
      let b ← IO.FS.readBinFile f
      match parse Tests.cfg 14 Tests.top b.toList with
      | some img => IO.FS.writeFile (f ++ ".lean-model") (Tests.describe img)
      | none => IO.FS.writeFile (f ++ ".lean-model") "refused\n"
    return 0
  | dir :: _ => Tests.emit dir
  | [] => return 1
LEAN
emit() { lake env lean --run "$src/MachOEmit.lean" "$@"; }

# The independent checker. `describe FILE` prints the description in the model's format, or
# "refused: reason"; `resign FILE` recomputes the page hashes of a file in place.
cat > "$src/macho.py" <<'PY'
import hashlib, struct, sys

P = 16384                     # arm64 macOS page size
RESERVE = 1 << 19             # stack bytes the format reserves for dyld and the arguments
LC_SEGMENT_64, LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLIB, LC_LOAD_DYLINKER = 0x19, 0x2, 0xb, 0xc, 0xe
LC_UUID, LC_CODE_SIGNATURE, LC_BUILD_VERSION = 0x1b, 0x1d, 0x32
LC_DYLD_INFO_ONLY, LC_MAIN = 0x80000022, 0x80000028

class Refused(Exception):
    pass

def need(c, why):
    if not c:
        raise Refused(why)

def cstr(b):
    return b.split(b'\0', 1)[0].decode()

def commands(b):
    magic, cpu, sub, ft, ncmds, sizeof, flags, _ = struct.unpack_from('<8I', b, 0)
    need(magic == 0xfeedfacf, 'magic'); need(cpu == 0x0100000c, 'cputype')
    need(ft == 2, 'filetype'); need(flags & 0x200000, 'not PIE'); need(flags & 4, 'not DYLDLINK')
    off, cmds = 32, []
    for _ in range(ncmds):
        cmd, size = struct.unpack_from('<2I', b, off)
        need(size >= 8 and size % 8 == 0, 'cmdsize')
        cmds.append((cmd, b[off + 8:off + size]))
        off += size
    need(off == 32 + sizeof, 'sizeofcmds')
    need(32 + sizeof <= P, 'commands beyond the header page')
    return cmds

def segment(body):
    name = cstr(body[:16])
    vmaddr, vmsize, fileoff, filesize = struct.unpack_from('<4Q', body, 16)
    maxprot, initprot, nsects, flags = struct.unpack_from('<4I', body, 48)
    need(len(body) == 64 + 80 * nsects, 'segment size')
    for i in range(nsects):
        s = body[64 + 80 * i:144 + 80 * i]
        need(cstr(s[16:32]) == name, 'section in the wrong segment')
        addr, size = struct.unpack_from('<2Q', s, 32)
        off = struct.unpack_from('<I', s, 48)[0]
        need(vmaddr <= addr and addr + size <= vmaddr + vmsize, 'section outside its segment')
        need(fileoff <= off and off + size <= fileoff + filesize, 'section outside the file range')
        need(struct.unpack_from('<I', s, 64)[0] & 0xff == 0, 'section type not S_REGULAR')
        need(struct.unpack_from('<I', s, 60)[0] == 0, 'relocations')
    return dict(name=name, vmaddr=vmaddr, vmsize=vmsize, fileoff=fileoff, filesize=filesize,
                maxprot=maxprot, initprot=initprot)

def signature(code, exec_limit, ident=b'millipede\0'):
    """The ad-hoc CodeDirectory in a SuperBlob, as cs_blobs.h lays it out."""
    n = (len(code) + 4095) // 4096
    hashes = b''.join(hashlib.sha256(code[i * 4096:(i + 1) * 4096]).digest() for i in range(n))
    head = 24 + 88 + len(ident)
    head = (head + 15) // 16 * 16
    total = head + len(hashes)
    cd = struct.pack('>9I4B4I4Q', 0xfade0c02, total - 24, 0x20400, 0x20002, head - 24, 88, 0, n,
                     len(code), 32, 2, 0, 12, 0, 0, 0, 0, 0, 0, exec_limit, 1)
    blob = struct.pack('>5I', 0xfade0cc0, total, 1, 0, 24) + b'\0' * 4 + cd + ident
    return blob + b'\0' * (head - len(blob)) + hashes

def describe(b):
    cmds = commands(b)
    kinds = [c for c, _ in cmds]
    nseg = sum(1 for k in kinds if k == LC_SEGMENT_64)
    need(kinds[:nseg] == [LC_SEGMENT_64] * nseg, 'segments not first')
    need(kinds[nseg:] == [LC_DYLD_INFO_ONLY, LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLINKER, LC_UUID,
                          LC_BUILD_VERSION, LC_MAIN, LC_LOAD_DYLIB, LC_CODE_SIGNATURE],
         'load commands')
    body = dict(cmds[nseg:])
    segs = [segment(bd) for _, bd in cmds[:nseg]]
    pz, text, link = segs[0], segs[1], segs[-1]
    need(pz['name'] == '__PAGEZERO' and pz['vmaddr'] == 0 and pz['vmsize'] >= 1 << 32
         and pz['initprot'] == 0 and pz['filesize'] == 0, '__PAGEZERO')
    need(text['name'] == '__TEXT' and text['fileoff'] == 0 and text['initprot'] == 5, '__TEXT')
    need(link['name'] == '__LINKEDIT' and link['initprot'] == 1, '__LINKEDIT')
    need(cstr(body[LC_LOAD_DYLINKER][struct.unpack_from('<I', body[LC_LOAD_DYLINKER])[0] - 8:])
         == '/usr/lib/dyld', 'dynamic linker')
    need(cstr(body[LC_LOAD_DYLIB][struct.unpack_from('<I', body[LC_LOAD_DYLIB])[0] - 8:])
         == '/usr/lib/libSystem.B.dylib', 'libSystem')
    need(struct.unpack_from('<I', body[LC_BUILD_VERSION])[0] == 1, 'platform')
    need(body[LC_DYLD_INFO_ONLY] == bytes(40) and body[LC_DYSYMTAB] == bytes(72), 'fixups')
    need(struct.unpack_from('<4I', body[LC_SYMTAB])[1] == 0, 'symbols')
    end = 0
    for s in segs[1:]:
        need(s['vmaddr'] % P == 0 and s['fileoff'] % P == 0, 'alignment')
        need(s['maxprot'] == s['initprot'], 'maxprot')
        need(s['initprot'] & 6 != 6, 'writable and executable')
        need(s is text or s['initprot'] & 4 == 0, 'executable segment other than __TEXT')
        need(s['filesize'] <= s['vmsize'] or s is link, 'filesize > vmsize')
        need(s['vmaddr'] >= end, 'overlap or unsorted')
        end = s['vmaddr'] + s['vmsize']
    dataoff, datasize = struct.unpack_from('<2I', body[LC_CODE_SIGNATURE])
    need(dataoff + datasize == len(b), 'signature not at the end')
    need(link['fileoff'] + link['filesize'] == len(b), '__LINKEDIT not at the end')
    for s in segs[1:-1]:
        need(s['fileoff'] + s['filesize'] <= link['fileoff'], 'segment in __LINKEDIT')
    need(b[dataoff:] == signature(b[:dataoff], text['filesize']), 'code signature')
    entryoff, stack = struct.unpack_from('<2Q', body[LC_MAIN])
    need(P <= entryoff < text['vmsize'], 'entry point')
    need(stack > RESERVE and (stack - RESERVE) % P == 0, 'stack size')
    out = []
    for s in segs[1:-1]:
        a, m, f = s['vmaddr'], s['vmsize'], s['filesize']
        if s is text:
            a, m, f = a + P, m - P, f - P
        out.append('segment 0x%x %d %d %d' % (a, m, f, s['initprot']))
    out.append('entry 0x%x' % (text['vmaddr'] + entryoff))
    out.append('stack %d' % (stack - RESERVE))
    return '\n'.join(out) + '\n'

def resign(path):
    b = bytearray(open(path, 'rb').read())
    cmds = commands(bytes(b))
    dataoff, _ = struct.unpack_from('<2I', dict(cmds)[LC_CODE_SIGNATURE])
    cd = dataoff + 24
    hoff = cd + struct.unpack_from('>I', b, cd + 16)[0]
    n = struct.unpack_from('>I', b, cd + 28)[0]
    for i in range(n):
        b[hoff + 32 * i:hoff + 32 * (i + 1)] = hashlib.sha256(b[i * 4096:min((i + 1) * 4096, dataoff)]).digest()
    open(path, 'wb').write(b)

def patch(path, out, off, fmt, value):
    b = bytearray(open(path, 'rb').read())
    struct.pack_into(fmt, b, off, value)
    open(out, 'wb').write(b)

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'describe':
        try:
            sys.stdout.write(describe(open(sys.argv[2], 'rb').read()))
        except (Refused, struct.error, KeyError, IndexError, UnicodeDecodeError) as e:
            print('refused: %s' % e)
    elif cmd == 'resign':
        resign(sys.argv[2])
    elif cmd == 'patch':
        patch(sys.argv[2], sys.argv[3], int(sys.argv[4], 0), sys.argv[5], int(sys.argv[6], 0))
    elif cmd == 'sign-ident':   # re-sign with another identifier, to test the comparison
        b = open(sys.argv[2], 'rb').read()
        dataoff = struct.unpack_from('<2I', dict(commands(b))[LC_CODE_SIGNATURE])[0]
        open(sys.argv[3], 'wb').write(b[:dataoff] + signature(b[:dataoff], 32768, b'millipedf\0'))
PY
py() { python3 -I "$src/macho.py" "$@"; }

# 1. SHA-256 against sha256sum
python3 -I - "$work" <<'PY'
import sys
for n in [0, 1, 3, 55, 56, 63, 64, 65, 119, 120, 128, 4095, 4096, 4097, 70000]:
    open('%s/sha-%d.bin' % (sys.argv[1], n), 'wb').write(bytes((i * 131 + n) % 256 for i in range(n)))
PY
shafiles=("$work"/sha-*.bin)
leansha=$(emit hash "${shafiles[@]}")
refsha=$(sha256sum "${shafiles[@]}")
if [ "$leansha" = "$refsha" ]; then note "SHA-256 agrees with sha256sum on ${#shafiles[@]} inputs"
else bad "SHA-256 differs from sha256sum"; diff <(echo "$leansha") <(echo "$refsha") || true; fi

# 2. the writer and the loader model
if ! emit "$work"; then bad "Lean loader model gave unexpected verdicts"; fi

# 3 and 4: the independent checker and the LLVM tools
readobj_describe() {  # file -> the description from llvm-readobj and llvm-otool
  local f=$1
  python3 -I - "$(llvm-readobj --all --macho-segment "$f" 2>&1)" "$(llvm-otool-19 -l "$f" 2>&1)" <<'PY'
import re, sys
ro, ot = sys.argv[1], sys.argv[2]
P, RESERVE = 16384, 1 << 19
prot = lambda s: (('r' in s) * 1) | (('w' in s) * 2) | (('x' in s) * 4)
segs = []
for blk in re.findall(r'Segment \{(.*?)\}', ro, re.S):
    g = lambda k: re.search(r'\b' + k + r': (\S+)', blk).group(1)
    segs.append((g('Name'), int(g('vmaddr'), 16), int(g('vmsize'), 16), int(g('filesize')), prot(g('initprot'))))
entryoff = int(re.search(r'entryoff (\d+)', ot).group(1))
stack = int(re.search(r'stacksize (\d+)', ot).group(1))
out = []
for name, a, m, f, p in segs:
    if name in ('__PAGEZERO', '__LINKEDIT'):
        continue
    if name == '__TEXT':
        a, m, f = a + P, m - P, f - P
    out.append('segment 0x%x %d %d %d' % (a, m, f, p))
text = [s for s in segs if s[0] == '__TEXT'][0]
out.append('entry 0x%x' % (text[1] + entryoff))
out.append('stack %d' % (stack - RESERVE))
print('\n'.join(out))
PY
}
declare -A insns=(
  [hello]="mov mov svc"
  [two]="mov adrp add mov mov svc mov mov svc"
  [three]="mov adrp add mov mov svc adrp add ldr add str ldr mov svc")
for f in hello two three; do
  m="$work/$f.model"
  [ -s "$m" ] || { bad "$f: no model description"; continue; }
  d=$(py describe "$work/$f.macho")
  if [ "$d" = "$(cat "$m")" ]; then note "$f: independent checker agrees with the model (signature rebuilt byte-identical)"
  else bad "$f: independent checker: $d"; fi
  ro=$(llvm-readobj --all --macho-segment "$work/$f.macho" 2>&1) || bad "$f: llvm-readobj failed"
  if grep -qi 'warning\|error\|invalid\|truncated' <<<"$ro"; then bad "$f: llvm-readobj complains"; fi
  for pat in 'Format: Mach-O arm64' 'FileType: Executable' 'MH_PIE' 'Name: __PAGEZERO' 'Name: __LINKEDIT'; do
    grep -q "$pat" <<<"$ro" || bad "$f: llvm-readobj output lacks '$pat'"
  done
  r=$(readobj_describe "$work/$f.macho")
  if [ "$r" = "$(cat "$m")" ]; then note "$f: llvm-readobj and llvm-otool agree with the model"
  else bad "$f: llvm-readobj/otool give"; echo "$r"; echo "model:"; cat "$m"; fi
  dis=$(llvm-objdump -d --no-show-raw-insn "$work/$f.macho" 2>&1)
  got=$(awk '/^ *[0-9a-f]+:/{print $2}' <<<"$dis" | tr '\n' ' ' | sed 's/ $//')
  if [ "$got" = "${insns[$f]}" ]; then note "$f: llvm-objdump disassembles: $got"
  else bad "$f: llvm-objdump gives '$got', expected '${insns[$f]}'"; fi
done
for b in "$work"/bad-*.macho; do
  v=$(py describe "$b")
  case $v in refused*) ;; *) bad "$(basename "$b"): the independent checker accepts it" ;; esac
done
note "the independent checker rejects all $(ls "$work"/bad-*.macho | wc -l) corruptions"

# 5. ld64.lld references
cat > "$work/libSystem.tbd" <<'TBD'
--- !tapi-tbd
tbd-version:     4
targets:         [ arm64-macos ]
install-name:    '/usr/lib/libSystem.B.dylib'
current-version: 1319
exports:
  - targets:         [ arm64-macos ]
    symbols:         [ _exit, _write ]
...
TBD
cat > "$work/hello.s" <<'S'
.globl _main
.p2align 2
_main:
  mov x0, #42
  mov x16, #1
  svc #0x80
S
cat > "$work/two.s" <<'S'
.globl _main
.p2align 2
_main:
  mov x0, #1
  adrp x1, msg@PAGE
  add x1, x1, msg@PAGEOFF
  mov x2, #3
  mov x16, #4
  svc #0x80
  mov x0, #7
  mov x16, #1
  svc #0x80
.section __TEXT,__const
msg: .ascii "hi\n"
S
cat > "$work/three.s" <<'S'
.globl _main
.p2align 2
_main:
  mov x0, #1
  adrp x1, msg@PAGE
  add x1, x1, msg@PAGEOFF
  mov x2, #3
  mov x16, #4
  svc #0x80
  adrp x1, d@PAGE
  add x1, x1, d@PAGEOFF
  ldr x0, [x1]
  add x3, x1, #0x1000
  str x0, [x3]
  ldr x0, [x3]
  mov x16, #1
  svc #0x80
.section __TEXT,__const
msg: .ascii "hi\n"
.data
d: .quad 5
.zerofill __DATA,__bss,b,8192,3
S
shape() {  # file -> header and load-command shape, from llvm-otool: the segments (name and
  # protection, sorted by name, since ld64.lld orders a renamed segment after __DATA), then the
  # header and the other commands in order
  local o
  o=$(llvm-otool-19 -hlv "$1" | awk '
    /MH_MAGIC_64/ { print "header", $2, $3, $5, $8, $9, $10, $11 }
    / cmd / && $2 != "LC_SEGMENT_64" { print "cmd", $2 }
    / cmd LC_SEGMENT_64/ { seg = 1 }
    /^  segname / && seg { name = $2 }
    /^ initprot / && seg { print "segment", name, $2; seg = 0 }
    /^ *name / { print "name", $2 }
    /^ *platform / || /^ *minos / { print $1, $2 }
    /segname __PAGEZERO/ { pz = 1 } pz && /vmsize/ { print "pagezero", $2; pz = 0 }')
  grep '^segment' <<<"$o" | sort
  grep -v '^segment' <<<"$o"
}
cdparams() {  # file -> CodeDirectory version, flags, hash size and type, page size, special slots, exec-segment flags
  python3 -I - "$1" <<'PY'
import struct, sys
b = open(sys.argv[1], 'rb').read()
ncmds = struct.unpack_from('<I', b, 16)[0]
off = 32
for _ in range(ncmds):
    cmd, size = struct.unpack_from('<2I', b, off)
    if cmd == 0x1d:
        dataoff = struct.unpack_from('<I', b, off + 8)[0]
    off += size
magic, length, count = struct.unpack_from('>3I', b, dataoff)
cd = dataoff + [struct.unpack_from('>2I', b, dataoff + 12 + 8 * i)[1] for i in range(count)
                if struct.unpack_from('>2I', b, dataoff + 12 + 8 * i)[0] == 0][0]
f = struct.unpack_from('>9I4B', b, cd)
print('superblob', hex(magic), count, 'cd', hex(f[0]), hex(f[2]), hex(f[3]), 'special', f[6],
      'hash', f[9], f[10], 'page', f[12], 'execflags', struct.unpack_from('>Q', b, cd + 80)[0])
PY
}
for f in hello two three; do
  llvm-mc -triple=arm64-apple-macos11 -filetype=obj "$work/$f.s" -o "$work/$f.o"
  ld64.lld-19 -arch arm64 -platform_version macos 11.0 11.0 -e _main -x -no_function_starts \
    -no_data_in_code_info -no_exported_symbols -rename_section __TEXT __const __RODATA __const \
    -segprot __RODATA r r \
    -o "$work/$f.lld" "$work/$f.o" "$work/libSystem.tbd"
  ours=$(shape "$work/$f.macho"); ref=$(shape "$work/$f.lld")
  if [ "$ours" = "$ref" ]; then note "$f: header, load commands, segment names and protections match ld64.lld ($(grep -c '^segment' <<<"$ours") segments, $(grep -c '^cmd' <<<"$ours") other commands)"
  else bad "$f: shape differs from ld64.lld"; diff <(echo "$ours") <(echo "$ref") || true; fi
  ours=$(cdparams "$work/$f.macho"); ref=$(cdparams "$work/$f.lld")
  if [ "$ours" = "$ref" ]; then note "$f: code-signature parameters match ld64.lld ($ours)"
  else bad "$f: signature parameters: ours '$ours', ld64.lld '$ref'"; fi
  ours=$(llvm-objdump -d --no-show-raw-insn "$work/$f.macho" | awk '/^ *[0-9a-f]+:/{print $2}')
  ref=$(llvm-objdump -d --no-show-raw-insn "$work/$f.lld" | awk '/^ *[0-9a-f]+:/{print $2}')
  [ "$ours" = "$ref" ] && note "$f: same instructions as ld64.lld" || bad "$f: instructions differ from ld64.lld"
done
if cmp -s <(llvm-objcopy-19 --dump-section __TEXT,__text=/dev/stdout "$work/hello.macho" 2>/dev/null) \
          <(llvm-objcopy-19 --dump-section __TEXT,__text=/dev/stdout "$work/hello.lld" 2>/dev/null) &&
   [ -n "$(llvm-objcopy-19 --dump-section __TEXT,__text=/dev/stdout "$work/hello.lld" 2>/dev/null | od -An -tx1)" ]; then
  note "hello: __text byte-identical to ld64.lld"
else bad "hello: __text differs from ld64.lld"; fi

# seeded bugs
if [ "$selftest" = 1 ]; then
  # a wrong SHA-256 round constant must make the hashes disagree with sha256sum
  sed 's/0x428a2f98/0x428a2f99/' Millipede/Object/MachO/Sha256.lean > "$src/BadSha.lean"
  cat >> "$src/BadSha.lean" <<'LEAN'
def main (fs : List String) : IO Unit := do
  for f in fs do
    let b ← IO.FS.readBinFile f
    let h := Millipede.MachO.Sha256.hash b.toList
    let d := h.map fun x => let s := Nat.toDigits 16 x.toNat; String.ofList (if s.length = 1 then '0' :: s else s)
    IO.println s!"{String.join d}  {f}"
LEAN
  cmp -s "$src/BadSha.lean" Millipede/Object/MachO/Sha256.lean && bad "the SHA-256 mutation did not apply"
  badsha=$(lake env lean --run "$src/BadSha.lean" "${shafiles[@]}")
  if [ "$badsha" != "$refsha" ]; then note "seeded bug sha-constant caught (differs from sha256sum)"
  else bad "seeded bug sha-constant NOT caught"; fi
  # a writer that hashes the last, partial page padded with zeros to 4 KiB must be refused by the
  # independent checker; the loader model shares `codeSignature` and cannot catch it
  { echo "import Millipede.Object.Elf.Write"; echo "import Millipede.Object.MachO.Sha256"
    sed '/^import/d' Millipede/Object/MachO/Format.lean |
      sed 's/Sha256.hash (bs.take CS_PAGE) ++/Sha256.hash (bs.take CS_PAGE ++ zeros (CS_PAGE - bs.length)) ++/'
    sed '/^import/d' Millipede/Object/MachO/Write.lean
    cat <<'LEAN'
open Millipede Millipede.MachO in
def main (args : List String) : IO UInt32 := do
  let code : List UInt8 := [0x40, 0x05, 0x80, 0xd2, 0x30, 0x00, 0x80, 0xd2, 0x01, 0x10, 0x00, 0xd4]
  let sg : Segment := { vaddr := 0x100004000, bytes := code, memSize := 16384, perm := Perm.rx }
  let img : Image := { segments := [sg], entry := 0x100004000, stackSize := 16384 }
  match write Config.a64Macos 14 0x7ff000000000 img with
  | .ok bs => IO.FS.writeBinFile (args.headD "") ⟨bs.toArray⟩; return 0
  | .error e => IO.eprintln e; return 1
LEAN
  } > "$src/BadSig.lean"
  grep -q 'zeros (CS_PAGE - bs.length)' "$src/BadSig.lean" || bad "the page-hash mutation did not apply"
  lake env lean --run "$src/BadSig.lean" "$work/seed-lastpage.bin"
  d=$(py describe "$work/seed-lastpage.bin")
  case $d in
    "refused: code signature") note "seeded bug last-page-hash caught (checker: code signature)" ;;
    *) bad "seeded bug last-page-hash NOT caught: $d" ;;
  esac
  # re-signed corruptions of three.macho: header offsets as in Tests/MachO.lean
  t=$((32 + 72)); ro=$((t + 152)); da=$((ro + 152)); mn=$((da + 152 + 72 + 48 + 24 + 80 + 32 + 24 + 24))
  seeds=(
    "data-wx $((da + 56)) <I 7"
    "data-wx2 $((da + 60)) <I 7"
    "init-func $((da + 72 + 64)) <I 9"
    "rodata-moved $((ro + 24)) <Q 0x10000c000"
    "entry-moved $((mn + 8)) <Q 0x4004"
    "stack-smaller $((mn + 16)) <Q 0x84000"
    "platform-ios $((mn - 16)) <I 2")
  for s in "${seeds[@]}"; do
    read -r name off fmt val <<<"$s"
    py patch "$work/three.macho" "$work/seed-$name.macho" "$off" "$fmt" "$val"
    py resign "$work/seed-$name.macho"
  done
  py sign-ident "$work/three.macho" "$work/seed-ident.macho"
  seeded=("$work"/seed-*.macho)
  emit parse "${seeded[@]}"
  for f in "${seeded[@]}"; do
    name=$(basename "$f" .macho)
    cmp -s "$f" "$work/three.macho" && { bad "$name did not change the file"; continue; }
    how=""
    lm=$(cat "$f.lean-model")
    [ "$lm" = "refused" ] && how="model refuses"
    [ "$lm" != "refused" ] && [ "$lm" != "$(cat "$work/three.model")" ] && how="model's description changes"
    d=$(py describe "$f")
    case $d in refused*) how="$how${how:+; }checker: ${d#refused: }" ;; esac
    case $d in
      refused*) ;;
      *) [ "$(readobj_describe "$f")" != "$(cat "$work/three.model")" ] &&
           how="$how${how:+; }llvm-readobj differs from the expected description" ;;
    esac
    [ "$(shape "$f")" != "$(shape "$work/three.lld")" ] && how="$how${how:+; }shape differs from ld64.lld"
    if [ -n "$how" ]; then note "seeded bug $name caught ($how)"
    else bad "seeded bug $name NOT caught"; fi
  done
fi

if [ "$fail" = 0 ]; then echo "macho-check: OK"; else echo "macho-check: FAILED"; exit 1; fi
