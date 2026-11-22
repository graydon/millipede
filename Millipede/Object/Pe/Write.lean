import Millipede.Object.Pe.Format
import Millipede.Object.Elf.Write

/-!
# The PE32+ writer

`Pe.write c pageBits stackTop img` serialises an `Image` as a Windows x64 console executable,
laid out as follows:

```
offset 0      DOS header (64 bytes), e_lfanew = 64, no DOS stub program
offset 64     "PE\0\0", COFF header (20 bytes), PE32+ optional header (240 bytes)
offset 328    section table: one section per segment, in order, then the import section
…             zero padding to a multiple of 512 (SizeOfHeaders)
per section   its bytes, then zeros up to a multiple of 512
```

The image base is the page before the first segment, where Windows maps the headers. The
segments must follow each other without a gap, as Windows requires of sections. Each section's
`VirtualAddress` is its segment's address less the base, its `VirtualSize` the segment's size in
memory, its `SizeOfRawData` the segment's bytes rounded up to 512, and its characteristics come
from the permission. The import section comes last, on the page after the last segment, and is
read-only. It holds one import descriptor and a null descriptor, the import lookup table, the
import address table (IAT), the DLL name and the hint/name entries:

```
0             descriptor: lookup table, 0, 0, DLL name, address table (RVAs); then 20 zero bytes
40            lookup table: the RVA of each hint/name entry, then 8 zero bytes
40 + 8(n+1)   address table: the same on disk; the loader overwrites slot k with the address
              of function k
40 + 16(n+1)  the DLL name, NUL-terminated, padded to an even length
…             per function: a zero hint (2 bytes), the name, NUL, padded to an even length
```

The import list is a parameter of the writer (`Config.dll`, `Config.funcs`). The file has no
base relocations, since the code is position-independent, and sets `DYNAMIC_BASE` with
relocations not stripped, so Windows may load it at any 64 KiB-aligned base. Stack reserve and
commit are both the image's stack size plus `Config.stackMargin`, so the whole stack is
committed when the program starts and no guard-page probing is needed.

The writer refuses an image that fails `imgOk`, whose import section would not lie below the
stack or would end at or above 2³¹ bytes from the base, whose headers do not fit in a page, whose
entry is below the base, whose import names are empty or contain a zero byte, or whose header
fields do not fit their widths.
-/

namespace Millipede.Pe

open Millipede.Elf (zeros chunkLen pad blob)

/-! ### The import section -/

/-- A hint/name entry: a zero hint, the name, NUL, and a zero to make the length even. -/
def nameEntry (nm : List UInt8) : List UInt8 := [0, 0] ++ nm ++ [0] ++ zeros ((nm.length + 1) % 2)

/-- The hint/name entries of the functions. -/
def nameTable : List (List UInt8) → List UInt8
  | [] => []
  | nm :: nms => nameEntry nm ++ nameTable nms

/-- The offsets of the hint/name entries, the first at `off`. -/
def nameOffsets : Nat → List (List UInt8) → List Nat
  | _, [] => []
  | off, nm :: nms => off :: nameOffsets (off + (nameEntry nm).length) nms

/-- A lookup table: the RVA `R + o` of each entry, then a zero entry. -/
def thunks (R : Nat) : List Nat → List UInt8
  | [] => natBytes 8 0
  | o :: os => natBytes 8 (R + o) ++ thunks R os

/-- The offset of the address table in the import section, for `n` functions. -/
def iatOff (n : Nat) : Nat := 40 + 8 * (n + 1)

/-- The offset of the DLL name. -/
def dllOff (n : Nat) : Nat := 40 + 16 * (n + 1)

/-- The DLL name, NUL-terminated and padded to an even length. -/
def dllEntry (dll : List UInt8) : List UInt8 := dll ++ [0] ++ zeros ((dll.length + 1) % 2)

/-- The offsets of the hint/name entries of `c`'s imports. -/
def importOffsets (c : Config) : List Nat :=
  nameOffsets (dllOff c.funcs.length + (dllEntry c.dll).length) c.funcs

/-- The import descriptor's fields, for an import section at RVA `R`. -/
def descOf (c : Config) (R : Nat) : List (Nat × Nat) :=
  descFields (R + 40) (R + dllOff c.funcs.length) (R + iatOff c.funcs.length)

/-- The contents of the import section at RVA `R`. -/
def idata (c : Config) (R : Nat) : List UInt8 :=
  putFields (descOf c R) ++ zeros DESC_LEN ++ thunks R (importOffsets c) ++
    thunks R (importOffsets c) ++ dllEntry c.dll ++ nameTable c.funcs

/-! ### Layout -/

/-- The number of sections: the segments and the import section. -/
def nsecOf (img : Image) : Nat := img.segments.length + 1

/-- `SizeOfHeaders`: the headers and the section table, rounded up to 512. -/
def headerSize (img : Image) : Nat := chunkLen FA (HDR_LEN + SHDR_LEN * nsecOf img)

/-- The RVA of the import section, the page after the last segment. -/
def idataRva (img : Image) : Nat := nextAddr (baseOf img + SA) img.segments - baseOf img

/-- The import section as a read-only segment. -/
def idataSeg (c : Config) (img : Image) : Segment where
  vaddr := UInt64.ofNat (baseOf img + idataRva img)
  bytes := idata c (idataRva img)
  memSize := (idata c (idataRva img)).length
  perm := Perm.r_

/-- All the sections of the file, as segments. -/
def sectionsOf (c : Config) (img : Image) : List Segment := img.segments ++ [idataSeg c img]

/-- The section header of a segment whose bytes start at file offset `off`. -/
def secShdr (base off : Nat) (sg : Segment) : Shdr where
  name := permName sg.perm
  vsize := sg.memSize
  rva := sg.vaddr.toNat - base
  rawSize := chunkLen FA sg.bytes.length
  rawPtr := off
  chars := permChars sg.perm

/-- The section headers, with the first section's bytes at file offset `off`. -/
def shdrsOf (base : Nat) : Nat → List Segment → List Shdr
  | _, [] => []
  | off, sg :: sgs => secShdr base off sg :: shdrsOf base (off + chunkLen FA sg.bytes.length) sgs

/-- The varying header fields. -/
def hdrOf (c : Config) (img : Image) : Hdr where
  nsec := nsecOf img
  entry := img.entry.toNat - baseOf img
  base := baseOf img
  sizeOfImage := idataRva img + pageUp (idata c (idataRva img)).length
  sizeOfHeaders := headerSize img
  stackReserve := img.stackSize + c.stackMargin
  stackCommit := img.stackSize + c.stackMargin
  importRva := idataRva img
  importSize := 2 * DESC_LEN
  iatRva := idataRva img + iatOff c.funcs.length
  iatSize := 8 * (c.funcs.length + 1)

/-- The file, assuming that the checks passed. -/
def fileBytes (c : Config) (img : Image) : List UInt8 :=
  putFields (hdrFields (hdrOf c img)) ++
    encodeShdrs (shdrsOf (baseOf img) (headerSize img) (sectionsOf c img)) ++
    zeros (headerSize img - (HDR_LEN + SHDR_LEN * nsecOf img)) ++ blob FA (sectionsOf c img)

/-- An import name is non-empty and has no zero byte. -/
def nameOk (nm : List UInt8) : Bool := !nm.isEmpty && nm.all (· != 0)

/-- The checks of the writer beyond `imgOk`, as listed in the module documentation. -/
def fileOk (c : Config) (stackTop : UInt64) (img : Image) : Bool :=
  let h := hdrOf c img
  decide (baseOf img + h.sizeOfImage ≤ stackBottom stackTop img) &&
    decide (HDR_LEN + SHDR_LEN * nsecOf img ≤ SA) && decide (baseOf img ≤ img.entry.toNat) &&
    decide (idataRva img + (idata c (idataRva img)).length < 2 ^ 31) &&
    nameOk c.dll && !c.funcs.isEmpty && c.funcs.all nameOk &&
    fieldsFit (hdrFields h) &&
    (shdrsOf (baseOf img) (headerSize img) (sectionsOf c img)).all (fieldsFit ∘ shdrFields) &&
    fieldsFit (descOf c (idataRva img))

/-- The PE writer, which refuses images that are not valid for the platform or whose header
fields would not fit. -/
def write (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) :
    Except String (List UInt8) :=
  if imgOk c pageBits stackTop (baseOf img) img = false then
    .error "pe: image not valid for this platform"
  else if fileOk c stackTop img = false then
    .error "pe: image cannot be written as a PE32+ file"
  else .ok (fileBytes c img)

end Millipede.Pe
