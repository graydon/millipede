import Millipede.Object.Elf.Format
import Millipede.Object.MachO.Sha256

/-!
# The Mach-O 64 executable format for arm64 macOS

This file describes the shape of the position-independent `MH_EXECUTE` files that the writer
produces and the loader model accepts, as far as both need it. Mach-O headers and load commands
are little-endian; the code signature is big-endian. Fields are byte lists read with
`Elf.takeNat` and `natOfBytes`. Everything is over `List UInt8` and `Nat`, by structural
recursion.

A file is a 32-byte header, a list of load commands and the data they point to. A load command is
a `Cmd`: a command number and a body, encoded as the number, the total size and the body. The
commands this format uses are

* `LC_SEGMENT_64`, a segment: name, address and size in memory, offset and size in the file,
  protections, and its sections (`SegCmd`);
* `LC_DYLD_INFO_ONLY`, `LC_SYMTAB` and `LC_DYSYMTAB`, all empty (no rebasing, binding, exports or
  symbols), which dyld expects to find;
* `LC_LOAD_DYLINKER` naming `/usr/lib/dyld`, without which arm64 macOS refuses to run the file;
* `LC_UUID`, `LC_BUILD_VERSION` (macOS 11.0) and `LC_MAIN` (the entry point as an offset from the
  header, and the stack size);
* `LC_LOAD_DYLIB` naming `/usr/lib/libSystem.B.dylib`, without which dyld halts with "program does
  not link with libSystem.B.dylib", even when no symbol from it is used;
* `LC_CODE_SIGNATURE`, the offset and size of an ad-hoc signature, which arm64 macOS requires of
  every executable.

The signature (`codeSignature`) is a `SuperBlob` holding one `CodeDirectory` with the SHA-256
hash of every 4 KiB page of the file before the signature, in the form ld64 and lld write for
"linker-signed" ad-hoc code. The loader model recomputes it, so it is specification shared by the
writer and the loader model, and scripts/macho-check.sh checks it independently with Python's
`hashlib`.

`Config` holds the facts about the operating system that the loader model depends on, and
`imageOk` the image checks that the writer and the loader model both make.
-/

namespace Millipede.MachO

open Millipede.Elf (takeNat zeros chunkLen pad validAt)

/-! ### Constants -/

def MH_MAGIC_64 : Nat := 0xfeedfacf
def CPU_TYPE_ARM64 : Nat := 0x0100000c
def MH_EXECUTE : Nat := 2
/-- `MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_PIE`. -/
def MH_FLAGS : Nat := 0x200085
def LC_SEGMENT_64 : Nat := 0x19
def LC_SYMTAB : Nat := 0x2
def LC_DYSYMTAB : Nat := 0xb
def LC_LOAD_DYLIB : Nat := 0xc
def LC_LOAD_DYLINKER : Nat := 0xe
def LC_UUID : Nat := 0x1b
def LC_CODE_SIGNATURE : Nat := 0x1d
def LC_BUILD_VERSION : Nat := 0x32
def LC_DYLD_INFO_ONLY : Nat := 0x80000022
def LC_MAIN : Nat := 0x80000028
def HDR_SIZE : Nat := 32
/-- The size of a section header. -/
def SECT_SIZE : Nat := 80
/-- The size of the page that one code-signature hash covers, 4 KiB. -/
def CS_PAGE : Nat := 4096

/-- An ASCII name as a NUL-padded field of `n` bytes. -/
def cstr (cs : List UInt8) (n : Nat) : List UInt8 := cs ++ zeros (n - cs.length)

def nPAGEZERO : List UInt8 := cstr [0x5f, 0x5f, 0x50, 0x41, 0x47, 0x45, 0x5a, 0x45, 0x52, 0x4f] 16
def nTEXT : List UInt8 := cstr [0x5f, 0x5f, 0x54, 0x45, 0x58, 0x54] 16
def nRODATA : List UInt8 := cstr [0x5f, 0x5f, 0x52, 0x4f, 0x44, 0x41, 0x54, 0x41] 16
def nDATA : List UInt8 := cstr [0x5f, 0x5f, 0x44, 0x41, 0x54, 0x41] 16
def nLINKEDIT : List UInt8 := cstr [0x5f, 0x5f, 0x4c, 0x49, 0x4e, 0x4b, 0x45, 0x44, 0x49, 0x54] 16
/-- A name no segment of this format has. -/
def nOTHER : List UInt8 := cstr [0x5f, 0x5f, 0x4f, 0x54, 0x48, 0x45, 0x52] 16
def ntext : List UInt8 := cstr [0x5f, 0x5f, 0x74, 0x65, 0x78, 0x74] 16
def nconst : List UInt8 := cstr [0x5f, 0x5f, 0x63, 0x6f, 0x6e, 0x73, 0x74] 16
def ndata : List UInt8 := cstr [0x5f, 0x5f, 0x64, 0x61, 0x74, 0x61] 16

/-! ### Protections and names -/

/-- The `vm_prot_t` of a permission: read 1, write 2, execute 4. -/
def protOf (p : Perm) : Nat := (if p.r then 1 else 0) + (if p.w then 2 else 0) + (if p.x then 4 else 0)

/-- The permission of a `vm_prot_t`. The loader checks that it is below 8. -/
def permOf (n : Nat) : Perm := ⟨n % 2 == 1, n / 2 % 2 == 1, n / 4 % 2 == 1⟩

theorem permOf_protOf (p : Perm) : permOf (protOf p) = p := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

theorem protOf_lt (p : Perm) : protOf p < 8 := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

/-- The segment name for a permission: code is `__TEXT`, constants `__RODATA`, data `__DATA`. -/
def segName (p : Perm) : List UInt8 :=
  if p = Perm.rx then nTEXT else if p = Perm.r_ then nRODATA else if p = Perm.rw then nDATA
  else nOTHER

/-- The name of the one section of a segment. -/
def sectName (p : Perm) : List UInt8 :=
  if p = Perm.rx then ntext else if p = Perm.r_ then nconst else ndata

/-- Section flags: `S_REGULAR`, with `S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS` for
code. -/
def sectFlags (p : Perm) : Nat := if p.x then 0x80000400 else 0

/-- The section alignment, as a power of two: 4 bytes for code, else 1. -/
def sectAlign (p : Perm) : Nat := if p.x then 2 else 0

/-! ### Operating-system facts -/

/-- What the loader model assumes about arm64 macOS, which the phase file lists.

`pageBits` is 14: arm64 macOS uses 16 KiB pages, and segments must start on them. `pageZero` is
the size of `__PAGEZERO`, the inaccessible region from address 0 that every 64-bit executable
reserves, 4 GiB as ld64 and lld make it; segments lie above it, after one page for the headers.
`maxAddr` is the end of user address space (`MACH_VM_MAX_ADDRESS` for arm64 macOS,
`0x7ffffe000000`), below which the stack must lie.

The stack size is recorded in `LC_MAIN.stacksize`, which makes the kernel allocate a main-thread
stack of that size instead of the default 8 MiB. dyld runs on that stack before `main`, and the
kernel puts the arguments, environment and `apple` strings at its top, so the file asks for
`stackReserve` bytes more than the image needs. The loader model gives the image `stacksize -
stackReserve` bytes and refuses requests above `maxStack`. -/
structure Config where
  pageBits : Nat
  pageZero : Nat
  maxAddr : Nat
  stackReserve : Nat
  maxStack : Nat
deriving DecidableEq, Repr

/-- arm64 macOS: 16 KiB pages, a 4 GiB `__PAGEZERO`, 512 KiB of stack for dyld and the
arguments, and at most 64 MiB of stack in all, the default hard limit of `RLIMIT_STACK`. -/
def Config.a64Macos : Config where
  pageBits := 14
  pageZero := 2 ^ 32
  maxAddr := 0x7ffffe000000
  stackReserve := 2 ^ 19
  maxStack := 2 ^ 26

/-! ### Header -/

/-- The 32-byte header of an arm64 executable with `ncmds` commands of `sizeofcmds` bytes. -/
def encodeHdr (ncmds sizeofcmds : Nat) : List UInt8 :=
  natBytes 4 MH_MAGIC_64 ++ natBytes 4 CPU_TYPE_ARM64 ++ natBytes 4 0 ++ natBytes 4 MH_EXECUTE ++
    natBytes 4 ncmds ++ natBytes 4 sizeofcmds ++ natBytes 4 MH_FLAGS ++ natBytes 4 0

@[simp] theorem encodeHdr_length (n s : Nat) : (encodeHdr n s).length = HDR_SIZE := by
  simp [encodeHdr, HDR_SIZE]

/-! ### Load commands -/

/-- A load command: its number and its body, which follows the number and the size. -/
structure Cmd where
  cmd : Nat
  body : List UInt8
deriving DecidableEq, Repr

/-- The bytes of a command, whose size counts the 8 bytes of number and size. -/
def encodeCmd (c : Cmd) : List UInt8 := natBytes 4 c.cmd ++ natBytes 4 (8 + c.body.length) ++ c.body

def encodeCmds : List Cmd → List UInt8
  | [] => []
  | c :: cs => encodeCmd c ++ encodeCmds cs

/-- Decodes `n` commands that fill the bytes exactly. A command's size must be a multiple of 8,
at least 8, and within the bytes. -/
def decodeCmds : Nat → List UInt8 → Option (List Cmd)
  | 0, bs => if bs = [] then some [] else none
  | n + 1, bs =>
    let sz := natOfBytes ((bs.drop 4).take 4)
    if 8 ≤ sz ∧ sz % 8 = 0 ∧ sz ≤ bs.length then
      (decodeCmds n (bs.drop sz)).map (⟨natOfBytes (bs.take 4), (bs.take sz).drop 8⟩ :: ·)
    else none

/-- A segment command. `sects` is the bytes of its section headers. -/
structure SegCmd where
  name : List UInt8
  vmaddr : Nat
  vmsize : Nat
  fileoff : Nat
  filesize : Nat
  maxprot : Nat
  initprot : Nat
  nsects : Nat
  flags : Nat
  sects : List UInt8
deriving DecidableEq, Repr

/-- The body of an `LC_SEGMENT_64` command. -/
def encodeSeg (s : SegCmd) : List UInt8 :=
  s.name ++ natBytes 8 s.vmaddr ++ natBytes 8 s.vmsize ++ natBytes 8 s.fileoff ++
    natBytes 8 s.filesize ++ natBytes 4 s.maxprot ++ natBytes 4 s.initprot ++
    natBytes 4 s.nsects ++ natBytes 4 s.flags ++ s.sects

/-- Decodes the body of an `LC_SEGMENT_64` command, reading missing bytes as zero. -/
def decodeSeg (bs : List UInt8) : SegCmd :=
  let name := bs.take 16
  let bs := bs.drop 16
  let (vmaddr, bs) := takeNat 8 bs
  let (vmsize, bs) := takeNat 8 bs
  let (fileoff, bs) := takeNat 8 bs
  let (filesize, bs) := takeNat 8 bs
  let (maxprot, bs) := takeNat 4 bs
  let (initprot, bs) := takeNat 4 bs
  let (nsects, bs) := takeNat 4 bs
  let (flags, bs) := takeNat 4 bs
  { name, vmaddr, vmsize, fileoff, filesize, maxprot, initprot, nsects, flags, sects := bs }

/-- The fields of a segment command fit their widths. -/
def SegCmd.fits (s : SegCmd) : Bool :=
  s.name.length == 16 && Elf.fits 8 s.vmaddr && Elf.fits 8 s.vmsize && Elf.fits 8 s.fileoff &&
    Elf.fits 8 s.filesize && Elf.fits 4 s.maxprot && Elf.fits 4 s.initprot &&
    Elf.fits 4 s.nsects && Elf.fits 4 s.flags

/-- The section header of the one section of a segment with permission `p`, covering `size`
bytes at address `addr` and file offset `off`. -/
def encodeSect (p : Perm) (addr size off : Nat) : List UInt8 :=
  sectName p ++ segName p ++ natBytes 8 addr ++ natBytes 8 size ++ natBytes 4 off ++
    natBytes 4 (sectAlign p) ++ natBytes 4 0 ++ natBytes 4 0 ++ natBytes 4 (sectFlags p) ++
    zeros 12

/-- The section of a segment with permission `p`, address `addr`, file offset `off` and file size
`filesize`, as the loader model reads it. The section starts where the segment does, in memory
and in the file, and its size is decoded and at most `filesize`, so it lies within the segment,
which dyld requires. The rest must be exactly what `encodeSect` writes, so the section is
`S_REGULAR`, has no relocations and carries the segment's name. -/
def sectOk (p : Perm) (addr off filesize : Nat) (bs : List UInt8) : Bool :=
  let size := natOfBytes ((bs.drop 40).take 8)
  decide (size ≤ filesize) && bs == encodeSect p addr size off

/-- `__PAGEZERO`: `pageZero` bytes from address 0, no access, nothing from the file. -/
def pageZeroCmd (c : Config) : Cmd :=
  ⟨LC_SEGMENT_64, encodeSeg ⟨nPAGEZERO, 0, c.pageZero, 0, 0, 0, 0, 0, 0, []⟩⟩

/-- `LC_DYLD_INFO_ONLY` with no rebase, bind or export information. -/
def dyldInfoCmd : Cmd := ⟨LC_DYLD_INFO_ONLY, zeros 40⟩

/-- `LC_SYMTAB` with no symbols and a string table of 8 bytes at offset `L`. -/
def symtabCmd (L : Nat) : Cmd :=
  ⟨LC_SYMTAB, natBytes 4 L ++ natBytes 4 0 ++ natBytes 4 L ++ natBytes 4 8⟩

/-- `LC_DYSYMTAB` with every table empty. -/
def dysymtabCmd : Cmd := ⟨LC_DYSYMTAB, zeros 72⟩

/-- `LC_LOAD_DYLINKER` naming `/usr/lib/dyld`. -/
def dylinkerCmd : Cmd :=
  ⟨LC_LOAD_DYLINKER, natBytes 4 12 ++
    cstr [0x2f, 0x75, 0x73, 0x72, 0x2f, 0x6c, 0x69, 0x62, 0x2f, 0x64, 0x79, 0x6c, 0x64] 20⟩

/-- `LC_BUILD_VERSION`: platform macOS (1), minimum OS and SDK 11.0, no tools. -/
def buildCmd : Cmd :=
  ⟨LC_BUILD_VERSION, natBytes 4 1 ++ natBytes 4 0xb0000 ++ natBytes 4 0xb0000 ++ natBytes 4 0⟩

/-- `LC_LOAD_DYLIB` naming `/usr/lib/libSystem.B.dylib`, current version 1319, compatibility
version 1. -/
def dylibCmd : Cmd :=
  ⟨LC_LOAD_DYLIB, natBytes 4 24 ++ natBytes 4 0 ++ natBytes 4 0x05270000 ++ natBytes 4 0x10000 ++
    cstr [0x2f, 0x75, 0x73, 0x72, 0x2f, 0x6c, 0x69, 0x62, 0x2f, 0x6c, 0x69, 0x62, 0x53, 0x79,
      0x73, 0x74, 0x65, 0x6d, 0x2e, 0x42, 0x2e, 0x64, 0x79, 0x6c, 0x69, 0x62] 32⟩

/-- `LC_MAIN`: the entry point as an offset from the header, and the stack size. -/
def mainCmd (entryoff stacksize : Nat) : Cmd :=
  ⟨LC_MAIN, natBytes 8 entryoff ++ natBytes 8 stacksize⟩

/-- `LC_CODE_SIGNATURE`: the offset and size of the signature. -/
def sigCmd (off size : Nat) : Cmd := ⟨LC_CODE_SIGNATURE, natBytes 4 off ++ natBytes 4 size⟩

/-- The start of `__LINKEDIT`: the string table, a single space and NUL padding to 8 bytes,
then 8 bytes of padding so that the signature is 16-byte aligned. -/
def linkeditPre : List UInt8 := 0x20 :: zeros 15

/-! ### The code signature -/

/-- The SHA-256 hash of each 4 KiB page of the bytes, the last page possibly short, as one list
of bytes. `n` bounds the number of pages. -/
def pageHashes : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | n + 1, bs => if bs = [] then [] else Sha256.hash (bs.take CS_PAGE) ++ pageHashes n (bs.drop CS_PAGE)

/-- The number of 4 KiB pages in `len` bytes, the last possibly short. -/
def nPages (len : Nat) : Nat := (len + CS_PAGE - 1) / CS_PAGE

/-- Big-endian fields of the signature. -/
abbrev be := Sha256.beBytes

/-- The signing identifier, `millipede` and a NUL. -/
def identifier : List UInt8 := [0x6d, 0x69, 0x6c, 0x6c, 0x69, 0x70, 0x65, 0x64, 0x65, 0]

/-- The size of the signature of `len` bytes: a 128-byte header and a 32-byte hash per page. -/
def sigSize (len : Nat) : Nat := 128 + 32 * nPages len

/-- The ad-hoc code signature of `code`, the bytes of the file before the signature. It is a
`SuperBlob` (magic `0xfade0cc0`) with one index entry, for slot 0, pointing at offset 24, where a
`CodeDirectory` (magic `0xfade0c02`) of version `0x20400` lies, with flags
`CS_ADHOC | CS_LINKER_SIGNED`, the hash offset 104 and identifier offset 88, no special slots,
one code slot per 4 KiB page, the code limit, 32-byte SHA-256 hashes (type 2), page size `2^12`,
and the executable segment `[0, execLimit)` marked as the main binary's. The identifier and NUL
padding to offset 128 follow, then the page hashes. -/
def codeSignature (code : List UInt8) (execLimit : Nat) : List UInt8 :=
  be 4 0xfade0cc0 ++ be 4 (sigSize code.length) ++ be 4 1 ++ be 4 0 ++ be 4 24 ++ zeros 4 ++
  be 4 0xfade0c02 ++ be 4 (sigSize code.length - 24) ++ be 4 0x20400 ++ be 4 0x20002 ++
  be 4 104 ++ be 4 88 ++ be 4 0 ++ be 4 (nPages code.length) ++ be 4 code.length ++
  [32, 2, 0, 12] ++ be 4 0 ++ be 4 0 ++ be 4 0 ++ be 4 0 ++ be 8 0 ++ be 8 0 ++ be 8 execLimit ++
  be 8 1 ++ identifier ++ zeros 6 ++ pageHashes code.length code

/-! ### Image checks shared by writer and loader -/

/-- The end address of the last segment, where `__LINKEDIT` goes. -/
def lastEnd : List Segment → Nat
  | [] => 0
  | [s] => s.vaddr.toNat + s.memSize
  | _ :: s :: rest => lastEnd (s :: rest)

/-- The bytes of the header and load commands for `n` image segments: the header, `__PAGEZERO`
and `__LINKEDIT` (72 bytes each), a 152-byte command per image segment, and the nine other
commands (328 bytes). -/
def headerSize (n : Nat) : Nat := HDR_SIZE + 72 + 152 * n + 72 + 328

/-- The image checks that both the writer and the loader make: `Image.valid`; the page size is
the operating system's and every segment is whole pages; the first segment is the code,
read-execute, above `__PAGEZERO` and a header page, and holds the entry point; every other
segment is read-only or read-write; the stack size is whole pages and with `stackReserve` at
most `maxStack`; the stack top is in user space; and the headers fit in one page. -/
def imageOk (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) : Bool :=
  let P := 2 ^ pageBits
  pageBits == c.pageBits && validAt pageBits stackTop img &&
    img.segments.all (fun sg => sg.memSize % P == 0) &&
    (match img.segments with
     | [] => false
     | s0 :: rest =>
       s0.perm == Perm.rx && decide (c.pageZero + P ≤ s0.vaddr.toNat) &&
         decide (s0.vaddr.toNat ≤ img.entry.toNat) &&
         decide (img.entry.toNat < s0.vaddr.toNat + s0.memSize) &&
         rest.all (fun sg => sg.perm == Perm.r_ || sg.perm == Perm.rw)) &&
    img.stackSize % P == 0 && decide (img.stackSize + c.stackReserve ≤ c.maxStack) &&
    decide (stackTop.toNat ≤ c.maxAddr) && decide (headerSize img.segments.length ≤ P)

end Millipede.MachO
