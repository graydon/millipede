import Millipede.Object.Elf.Format

/-!
# The PE32+ file format

This file describes the shape of a Windows x64 console executable as far as the writer and the
loader model need it. The headers are sequences of little-endian fields, each a width in bytes
and a value. `putFields` encodes such a sequence and `getFields` decodes one from its widths, and
the two are proved inverse for values that fit their widths. A header record lists the fields
that vary between files, and its field list (`hdrFields`, `shdrFields`, `descFields`) gives every
field of the header in file order, with the required value of each fixed field. The loader model
accepts a header only if the decoded fields are exactly the field list of the record it reads
from them.

`Config` holds the facts about Windows on which the loader model depends, and the import list:
one DLL and the names of the functions taken from it. `imgOk` is the image check that the writer
and the loader both make.
-/

namespace Millipede.Pe

open Millipede.Elf (zeros chunkLen pad fits)

/-! ### Field sequences -/

/-- Encodes fields, each a width in bytes and a value, little-endian and in order. -/
def putFields : List (Nat × Nat) → List UInt8
  | [] => []
  | (w, v) :: fs => natBytes w v ++ putFields fs

/-- Decodes fields of the given widths, reading missing bytes as zero. -/
def getFields : List Nat → List UInt8 → List Nat
  | [], _ => []
  | w :: ws, bs => natOfBytes (bs.take w) :: getFields ws (bs.drop w)

/-- Every value fits its width. -/
def fieldsFit (fs : List (Nat × Nat)) : Bool := fs.all (fun f => fits f.1 f.2)

@[simp] theorem putFields_length : ∀ fs : List (Nat × Nat),
    (putFields fs).length = (fs.map Prod.fst).sum
  | [] => rfl
  | (w, v) :: fs => by simp [putFields, putFields_length fs]

theorem getFields_putFields : ∀ (fs : List (Nat × Nat)), fieldsFit fs = true →
    ∀ rest, getFields (fs.map Prod.fst) (putFields fs ++ rest) = fs.map Prod.snd
  | [], _, _ => rfl
  | (w, v) :: fs, hf, rest => by
    simp only [fieldsFit, List.all_cons, Bool.and_eq_true] at hf
    have hl : (natBytes w v).length = w := natBytes_length w v
    simp only [List.map_cons, getFields, putFields, List.append_assoc, List.take_left' hl,
      List.drop_left' hl, natOfBytes_natBytes, Elf.mod_of_fits hf.1,
      getFields_putFields fs hf.2 rest]

/-! ### Constants -/

/-- The file alignment: section data starts at multiples of 512 bytes. -/
def FA : Nat := 512
/-- The section alignment, which is the page size: sections start at multiples of 4 KiB. -/
def SA : Nat := 4096
/-- The header bytes before the section table: the DOS header (64), the signature (4), the
COFF header (20) and the PE32+ optional header (240). -/
def HDR_LEN : Nat := 328
/-- The size of a section header. -/
def SHDR_LEN : Nat := 40
/-- The size of an import descriptor. -/
def DESC_LEN : Nat := 20

/-- `IMAGE_SCN_*` bits: code, initialised data, execute, read, write. -/
def SCN_CODE : Nat := 0x20
def SCN_DATA : Nat := 0x40
def SCN_X : Nat := 0x20000000
def SCN_R : Nat := 0x40000000
def SCN_W : Nat := 0x80000000

/-- The section characteristics of a permission: code if executable, else initialised data,
with the memory bits of the permission. -/
def permChars (p : Perm) : Nat :=
  (if p.x then SCN_CODE else SCN_DATA) + (if p.x then SCN_X else 0) +
    (if p.r then SCN_R else 0) + (if p.w then SCN_W else 0)

/-- The characteristics the loader model accepts: a content bit (`CNT_CODE`,
`CNT_INITIALIZED_DATA` or `CNT_UNINITIALIZED_DATA`) and any of the three memory bits. -/
def charsOk (ch : Nat) : Bool :=
  ch / 2 ^ 29 < 8 && (ch % 2 ^ 29 == 0x20 || ch % 2 ^ 29 == 0x40 || ch % 2 ^ 29 == 0x80)

/-- The permission given by the memory bits of the characteristics. -/
def charsPerm (ch : Nat) : Perm := ⟨ch / 2 ^ 30 % 2 == 1, ch / 2 ^ 31 % 2 == 1, ch / 2 ^ 29 % 2 == 1⟩

theorem charsPerm_permChars (p : Perm) : charsPerm (permChars p) = p := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

theorem charsOk_permChars (p : Perm) : charsOk (permChars p) = true := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

/-- The eight-byte section name for a permission, which the loader ignores: `.text`, `.rdata` or
`.data`. -/
def permName (p : Perm) : Nat :=
  if p.x then 0x747865742e else if p.w then 0x617461642e else 0x61746164722e

/-! ### Platform facts and imports -/

/-- What the loader model assumes about Windows, and the imports of the file. `minBase` is the
lowest image base, `maxAddr` the end of the user address space, below which the image and the
stack lie. `maxStack` is the largest stack the model promises. `stackMargin` is the stack the
loader's own frames use above the entry point's stack pointer: the file asks for
`stackSize + stackMargin` bytes, all committed. `dll` is the name of the one DLL the file imports
from and `funcs` the names of the functions it imports, as ASCII bytes. -/
structure Config where
  minBase : Nat
  maxAddr : Nat
  maxStack : Nat
  stackMargin : Nat
  dll : List UInt8
  funcs : List (List UInt8)
deriving DecidableEq, Repr

/-- The ASCII bytes of a string. -/
def ascii (s : String) : List UInt8 := s.toList.map (fun ch => ch.toNat.toUInt8)

/-- Windows on x64: images at or above 64 KiB, a 47-bit user address space less 64 KiB, at most
4 MiB of stack plus a margin of 64 KiB, and the four functions of `kernel32.dll` that a console
program needs: `ExitProcess`, `GetStdHandle`, `WriteFile` and `ReadFile`. -/
def Config.win64 : Config where
  minBase := 0x10000
  maxAddr := 2 ^ 47 - 2 ^ 16
  maxStack := 2 ^ 22
  stackMargin := 0x10000
  dll := ascii "kernel32.dll"
  funcs := [ascii "ExitProcess", ascii "GetStdHandle", ascii "WriteFile", ascii "ReadFile"]

/-! ### Headers -/

/-- The fields of the DOS header, the PE signature, the COFF header and the optional header that
vary between files. All addresses except `base` are relative to the image base (RVAs). -/
structure Hdr where
  nsec : Nat
  entry : Nat
  base : Nat
  sizeOfImage : Nat
  sizeOfHeaders : Nat
  stackReserve : Nat
  stackCommit : Nat
  importRva : Nat
  importSize : Nat
  iatRva : Nat
  iatSize : Nat
deriving DecidableEq, Repr, Inhabited

/-- Every field of the first 328 bytes of the file, in order: width in bytes and value. -/
def hdrFields (h : Hdr) : List (Nat × Nat) :=
  [ -- DOS header: `e_magic` "MZ", 58 bytes of zero, `e_lfanew` = 64; no DOS stub program
    (2, 0x5a4d), (58, 0), (4, 64),
    -- "PE\0\0"
    (4, 0x4550),
    -- COFF header: `Machine` AMD64, `NumberOfSections`, `TimeDateStamp`, `PointerToSymbolTable`,
    -- `NumberOfSymbols`, `SizeOfOptionalHeader` = 240, `Characteristics` =
    -- `EXECUTABLE_IMAGE | LARGE_ADDRESS_AWARE` (relocations not stripped)
    (2, 0x8664), (2, h.nsec), (4, 0), (4, 0), (4, 0), (2, 240), (2, 0x22),
    -- optional header: `Magic` PE32+, linker version 14.0, `SizeOfCode`,
    -- `SizeOfInitializedData`, `SizeOfUninitializedData` (unused by the loader, zero),
    -- `AddressOfEntryPoint`, `BaseOfCode` (zero), `ImageBase`, `SectionAlignment` 4096,
    -- `FileAlignment` 512
    (2, 0x20b), (1, 14), (1, 0), (4, 0), (4, 0), (4, 0), (4, h.entry), (4, 0), (8, h.base),
    (4, SA), (4, FA),
    -- OS version 6.0, image version 0.0, subsystem version 6.0, `Win32VersionValue` 0
    (2, 6), (2, 0), (2, 0), (2, 0), (2, 6), (2, 0), (4, 0),
    -- `SizeOfImage`, `SizeOfHeaders`, `CheckSum` 0, `Subsystem` = console (3),
    -- `DllCharacteristics` = `HIGH_ENTROPY_VA | DYNAMIC_BASE | NX_COMPAT |
    -- TERMINAL_SERVER_AWARE`
    (4, h.sizeOfImage), (4, h.sizeOfHeaders), (4, 0), (2, 3), (2, 0x8160),
    -- stack reserve and commit, heap reserve 1 MiB and commit 4 KiB, `LoaderFlags` 0,
    -- `NumberOfRvaAndSizes` 16
    (8, h.stackReserve), (8, h.stackCommit), (8, 0x100000), (8, 0x1000), (4, 0), (4, 16),
    -- data directories: export (none), import
    (4, 0), (4, 0), (4, h.importRva), (4, h.importSize),
    -- resource, exception, certificate, base relocation, debug, architecture, global pointer,
    -- TLS, load configuration, bound import: none
    (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0),
    (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0),
    -- import address table
    (4, h.iatRva), (4, h.iatSize),
    -- delay import, CLR runtime header, reserved: none
    (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0) ]

/-- The widths of the header fields. -/
def hdrWidths : List Nat := (hdrFields default).map Prod.fst

theorem hdrFields_widths (h : Hdr) : (hdrFields h).map Prod.fst = hdrWidths := rfl

/-- Reads the varying fields from decoded header fields. -/
def Hdr.ofFields (vs : List Nat) : Hdr where
  nsec := vs.getD 5 0
  entry := vs.getD 17 0
  base := vs.getD 19 0
  sizeOfImage := vs.getD 29 0
  sizeOfHeaders := vs.getD 30 0
  stackReserve := vs.getD 34 0
  stackCommit := vs.getD 35 0
  importRva := vs.getD 42 0
  importSize := vs.getD 43 0
  iatRva := vs.getD 64 0
  iatSize := vs.getD 65 0

theorem Hdr.ofFields_hdrFields (h : Hdr) : Hdr.ofFields ((hdrFields h).map Prod.snd) = h := rfl

/-- A section header's varying fields. -/
structure Shdr where
  name : Nat
  vsize : Nat
  rva : Nat
  rawSize : Nat
  rawPtr : Nat
  chars : Nat
deriving DecidableEq, Repr, Inhabited

/-- Every field of a section header, in order: `Name`, `VirtualSize`, `VirtualAddress`,
`SizeOfRawData`, `PointerToRawData`, then no relocations and no line numbers, and
`Characteristics`. -/
def shdrFields (s : Shdr) : List (Nat × Nat) :=
  [(8, s.name), (4, s.vsize), (4, s.rva), (4, s.rawSize), (4, s.rawPtr), (4, 0), (4, 0), (2, 0),
   (2, 0), (4, s.chars)]

def shdrWidths : List Nat := (shdrFields default).map Prod.fst

theorem shdrFields_widths (s : Shdr) : (shdrFields s).map Prod.fst = shdrWidths := rfl

def Shdr.ofFields (vs : List Nat) : Shdr where
  name := vs.getD 0 0
  vsize := vs.getD 1 0
  rva := vs.getD 2 0
  rawSize := vs.getD 3 0
  rawPtr := vs.getD 4 0
  chars := vs.getD 9 0

theorem Shdr.ofFields_shdrFields (s : Shdr) :
    Shdr.ofFields ((shdrFields s).map Prod.snd) = s := rfl

/-- The section table. -/
def encodeShdrs : List Shdr → List UInt8
  | [] => []
  | s :: ss => putFields (shdrFields s) ++ encodeShdrs ss

/-- Decodes `n` section headers, or `none` if one is not of the form `shdrFields`. -/
def decodeShdrs : Nat → List UInt8 → Option (List Shdr)
  | 0, _ => some []
  | n + 1, bs =>
    let vs := getFields shdrWidths bs
    let s := Shdr.ofFields vs
    if (shdrFields s).map Prod.snd = vs then (decodeShdrs n (bs.drop SHDR_LEN)).map (s :: ·)
    else none

@[simp] theorem putFields_shdr_length (s : Shdr) : (putFields (shdrFields s)).length = SHDR_LEN := by
  simp [shdrFields, SHDR_LEN]

@[simp] theorem encodeShdrs_length : ∀ ss : List Shdr,
    (encodeShdrs ss).length = SHDR_LEN * ss.length
  | [] => rfl
  | s :: ss => by
    simp only [encodeShdrs, List.length_append, putFields_shdr_length, encodeShdrs_length ss,
      List.length_cons, Nat.mul_succ]
    omega

theorem decodeShdrs_encodeShdrs : ∀ (ss : List Shdr), ss.all (fieldsFit ∘ shdrFields) = true →
    ∀ rest, decodeShdrs ss.length (encodeShdrs ss ++ rest) = some ss
  | [], _, _ => rfl
  | s :: ss, hf, rest => by
    simp only [List.all_cons, Bool.and_eq_true, Function.comp] at hf
    have hg : getFields shdrWidths (putFields (shdrFields s) ++ (encodeShdrs ss ++ rest)) =
        (shdrFields s).map Prod.snd := by
      rw [← shdrFields_widths s]; exact getFields_putFields _ hf.1 _
    simp only [List.length_cons, decodeShdrs, encodeShdrs, List.append_assoc, hg,
      Shdr.ofFields_shdrFields, ite_true, List.drop_left' (putFields_shdr_length s),
      decodeShdrs_encodeShdrs ss hf.2 rest, Option.map_some]

/-- Every field of an import descriptor: `OriginalFirstThunk` (the lookup table), no time stamp,
no forwarder chain, `Name`, `FirstThunk` (the address table). -/
def descFields (ilt name iat : Nat) : List (Nat × Nat) :=
  [(4, ilt), (4, 0), (4, 0), (4, name), (4, iat)]

def descWidths : List Nat := [4, 4, 4, 4, 4]

/-! ### Page arithmetic and the image check -/

/-- `a` rounded up to a page. -/
def pageUp (a : Nat) : Nat := chunkLen SA a

/-- The segments follow one another without a gap from address `cur`: each starts at the page
after the end of the previous one. -/
def contig : Nat → List Segment → Bool
  | _, [] => true
  | cur, sg :: sgs => sg.vaddr.toNat == cur && contig (pageUp (sg.vaddr.toNat + sg.memSize)) sgs

/-- The page after the last of the segments laid out from `cur`. -/
def nextAddr : Nat → List Segment → Nat
  | cur, [] => cur
  | _, sg :: sgs => nextAddr (pageUp (sg.vaddr.toNat + sg.memSize)) sgs

/-- The image base for an image: the page before its first segment, where the headers lie. -/
def baseOf (img : Image) : Nat := (img.segments.headD default).vaddr.toNat - SA

/-- The image checks that both the writer and the loader make, for an image based at `base`.
They are a layout in 4 KiB pages, `Image.valid`, at least one segment, a base aligned to 64 KiB
and at or above `minBase`, segments that follow each other without a gap from the page after the
headers, a stack top at or below `maxAddr`, and a stack of at most `maxStack` bytes. -/
def imgOk (c : Config) (pageBits : Nat) (stackTop : UInt64) (base : Nat) (img : Image) : Bool :=
  pageBits == 12 && Elf.validAt pageBits stackTop img && !img.segments.isEmpty &&
    base % 0x10000 == 0 && decide (c.minBase ≤ base) && contig (base + SA) img.segments &&
    decide (stackTop.toNat ≤ c.maxAddr) && decide (img.stackSize ≤ c.maxStack)

/-- The lowest stack address of the model, below which the image must end. -/
def stackBottom (stackTop : UInt64) (img : Image) : Nat :=
  (stackTop.toNat / SA - img.stackPages 12) * SA

end Millipede.Pe
