import Millipede.Object.Pe.Format
import Millipede.Object.Obj

/-!
# The PE32+ loader model

The loader model describes what Windows does when it starts a process from an x64 console
executable, and it is a trusted specification. It is written from the PE/COFF specification and
describes the subset of the Windows loader that the writer's files use. It is stricter than
Windows: it accepts only files of one shape and refuses, among much else, DLLs, base relocations,
TLS, bound and delay imports, several import descriptors, imports by ordinal, and sections that
leave a gap.

`Pe.parse c pageBits stackTop bs` reads the file, or returns `none`, by checking the following:

1. The first 328 bytes are exactly the fields of `hdrFields h` for the record `h` they hold: the
   DOS header with `e_lfanew = 64`, the signature, an AMD64 COFF header with an optional header
   of 240 bytes, a PE32+ optional header for a console program with section alignment 4096, file
   alignment 512, `DYNAMIC_BASE`, `HIGH_ENTROPY_VA` and `NX_COMPAT`, and data directories that
   are all empty except the import table and the import address table. `SizeOfHeaders` is a
   multiple of 512, covers the section table, fits in the first page and lies inside the file.
   The stack commit equals the reserve, and the reserve is at least `c.stackMargin`. The writer
   encodes the same field list, so the laws cannot catch a wrong fixed value in it; the tests
   compare those values with the offsets of the PE/COFF specification and with lld-link's files.
2. The section table has `NumberOfSections` entries, each exactly of the form `shdrFields s`.
   Each section's raw data offset and size are multiples of 512 and lie inside the file, after
   the headers and after the previous section's raw data, its
   characteristics are a content bit with memory bits, and any raw bytes beyond `VirtualSize`
   are zero. The section maps at `base + VirtualAddress` the first
   `min SizeOfRawData VirtualSize` bytes of its raw data followed by zeros up to `VirtualSize`,
   with the permission of its memory bits. Windows copies the raw data and zero-fills the rest,
   and the check on the bytes beyond `VirtualSize` makes the page tail zero as the model says.
3. The last section holds the imports and the others the program. The program's image, with its
   entry at `base + AddressOfEntryPoint` and a stack of `reserve - c.stackMargin` bytes, passes
   `imgOk`, so its sections follow each other without a gap from the page after the headers.
   The import section is read-only, starts on the page after the last program section, is
   wholly initialised, and ends, rounded up to a page, at `SizeOfImage`, which lies below the
   model's stack. The import directory is the import section's first 40 bytes, and the import
   address table directory covers the table that the descriptor names.
4. The import section holds one import descriptor followed by a null descriptor, with no time
   stamp and no forwarder chain. Its DLL name and the hint/name entry of each function are
   NUL-terminated strings inside the section, the hint/name entries at or after the DLL name.
   The lookup table ends with a zero entry, and every
   other entry is an import by name, an RVA below 2³¹. The section is laid out in the order
   descriptors, lookup table, address table, names, so the loader's writes to the address table
   change nothing it reads.

`load` is then `Image.init abi` of the program's image. Its memory holds the program's sections
with zero fill and their permissions, and a read-write stack of the recorded size below
`abi.stackTop`. The headers and the import section are left unmapped, which makes the model
stricter than Windows, since Windows maps both read-only. Compiled code does not read them.

`loadWith c abi resolve bs` is the fuller model. `resolve dll f` is the address at which the
system has function `f` of DLL `dll`, or `none` if it has none, in which case Windows refuses
to start the process and so does the model. It maps the headers read-only at the base and the
import section read-only with slot `k` of the address table holding, as 8 little-endian bytes,
the address of function `k`, which is what the Windows loader writes there.

The model assumes 4 KiB pages, that the image is mapped at its preferred base, that the stack is
at `abi.stackTop`, and that at least the recorded size is available below the entry point's
stack pointer. Windows may load the image at another base, since it is relocatable and has no
relocations; compiled code is position-independent and never observes an address, so the
difference cannot be seen. On x64, `X` and `W` imply that a page is readable in hardware, and the
model does not grant that, which again only makes it stricter.
-/

namespace Millipede.Pe

open Millipede.Elf (zeros chunkLen pad)

/-! ### Sections -/

/-- One section as a segment of an image based at `base`, or `none` if it breaks one of the rules
in the module documentation. Its raw data must start at or after file offset `lo`. -/
def secSeg (base : Nat) (bs : List UInt8) (lo : Nat) (s : Shdr) : Option Segment :=
  if lo ≤ s.rawPtr ∧ s.rawPtr % FA = 0 ∧ s.rawSize % FA = 0 ∧ s.rawPtr + s.rawSize ≤ bs.length ∧
      charsOk s.chars = true ∧
      ((bs.drop (s.rawPtr + s.vsize)).take (s.rawSize - s.vsize)).all (· == 0) = true then
    some { vaddr := UInt64.ofNat (base + s.rva),
           bytes := (bs.drop s.rawPtr).take (min s.rawSize s.vsize),
           memSize := s.vsize, perm := charsPerm s.chars }
  else none

/-- All sections as segments, in order, with the raw data of each starting at or after `lo` and
after the end of the previous section's raw data. -/
def secSegs (base : Nat) (bs : List UInt8) : Nat → List Shdr → Option (List Segment)
  | _, [] => some []
  | lo, s :: ss =>
    match secSeg base bs lo s, secSegs base bs (s.rawPtr + s.rawSize) ss with
    | some sg, some sgs => some (sg :: sgs)
    | _, _ => none

/-- Splits off the last element. -/
def splitLast {α : Type} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: b :: rest => (splitLast (b :: rest)).map (fun r => (a :: r.1, r.2))

/-! ### Imports -/

/-- The NUL-terminated string at the start of `bs`, which must contain the NUL. -/
def cstr (bs : List UInt8) : Option (List UInt8) :=
  let s := bs.takeWhile (· != 0)
  if s.length < bs.length then some s else none

/-- The names of the import lookup table at offset `off` of the import section `sec`, which lies
at RVA `R`. Each non-zero entry is the RVA of a hint/name entry at or after offset `lo`; the
table ends with a zero entry. `fuel` bounds the number of entries. -/
def readNames (sec : List UInt8) (R lo : Nat) : Nat → Nat → Option (List (List UInt8))
  | 0, _ => none
  | fuel + 1, off =>
    if off + 8 ≤ sec.length then
      let e := natOfBytes ((sec.drop off).take 8)
      if e = 0 then some []
      else if R + lo ≤ e ∧ e < 2 ^ 31 then
        match cstr (sec.drop (e - R + 2)), readNames sec R lo fuel (off + 8) with
        | some nm, some nms => some (nm :: nms)
        | _, _ => none
      else none
    else none

/-- What the import section names: the DLL, its functions in order, and the RVA of the import
address table. -/
structure Imports where
  dll : List UInt8
  funcs : List (List UInt8)
  iat : Nat
deriving DecidableEq, Repr

/-- Reads the import section `sec` at RVA `R`, as listed in the module documentation. -/
def parseImports (R : Nat) (sec : List UInt8) : Option Imports :=
  match getFields descWidths sec with
  | [ilt, ts, fwd, name, iat] =>
    if ts = 0 ∧ fwd = 0 ∧ (sec.drop DESC_LEN).take DESC_LEN = zeros DESC_LEN ∧
        R + 2 * DESC_LEN ≤ ilt ∧ R ≤ iat ∧ R ≤ name then
      match readNames sec R (name - R) sec.length (ilt - R) with
      | none => none
      | some funcs =>
        let n := funcs.length
        if ilt + 8 * (n + 1) ≤ iat ∧ iat + 8 * (n + 1) ≤ name then
          match cstr (sec.drop (name - R)) with
          | some dll => some ⟨dll, funcs, iat⟩
          | none => none
        else none
    else none
  | _ => none

/-! ### The loader -/

/-- What the loader finds in a file: the program's image, the base, the headers and the import
section as read-only segments, and the imports. -/
structure Parsed where
  img : Image
  base : Nat
  headers : Segment
  idata : Segment
  imports : Imports
deriving DecidableEq, Repr

/-- The checks on the varying header fields, as listed in the module documentation. -/
def hdrOk (c : Config) (h : Hdr) (fileLen : Nat) : Bool :=
  h.sizeOfHeaders % FA == 0 && decide (HDR_LEN + SHDR_LEN * h.nsec ≤ h.sizeOfHeaders) &&
    decide (h.sizeOfHeaders ≤ SA) && decide (h.sizeOfHeaders ≤ fileLen) &&
    h.stackCommit == h.stackReserve && decide (c.stackMargin ≤ h.stackReserve)

/-- The checks on the import section and the directories that point into it, as listed in the
module documentation. -/
def idataOk (stackTop : UInt64) (h : Hdr) (img : Image) (id : Segment)
    (im : Imports) : Bool :=
  let R := id.vaddr.toNat - h.base
  id.vaddr.toNat == nextAddr (h.base + SA) img.segments && id.perm == Perm.r_ &&
    id.bytes.length == id.memSize && h.importRva == R && h.importSize == 2 * DESC_LEN &&
    h.iatRva == im.iat && h.iatSize == 8 * (im.funcs.length + 1) &&
    h.sizeOfImage == R + pageUp id.memSize &&
    decide (h.base + h.sizeOfImage ≤ stackBottom stackTop img)

/-- Parses a PE32+ executable, or returns `none`. -/
def parse (c : Config) (pageBits : Nat) (stackTop : UInt64) (bs : List UInt8) : Option Parsed :=
  let vs := getFields hdrWidths bs
  let h := Hdr.ofFields vs
  if (hdrFields h).map Prod.snd = vs ∧ hdrOk c h bs.length = true then
    match decodeShdrs h.nsec (bs.drop HDR_LEN) with
    | none => none
    | some shs =>
      match secSegs h.base bs h.sizeOfHeaders shs with
      | none => none
      | some segs =>
        match splitLast segs with
        | none => none
        | some (prog, id) =>
          let img : Image := { segments := prog, entry := UInt64.ofNat (h.base + h.entry),
                               stackSize := h.stackReserve - c.stackMargin }
          match parseImports (id.vaddr.toNat - h.base) id.bytes with
          | none => none
          | some im =>
            if imgOk c pageBits stackTop h.base img ∧ idataOk stackTop h img id im then
              some { img, base := h.base, idata := id, imports := im,
                     headers := { vaddr := UInt64.ofNat h.base, bytes := bs.take h.sizeOfHeaders,
                                  memSize := h.sizeOfHeaders, perm := Perm.r_ } }
            else none
  else none

/-- The loader model, which gives the machine state of the program's image, with the headers and
the import section left unmapped, or `none` when the file is refused. -/
def load (c : Config) {isa : Isa} (abi : Abi isa) (bs : List UInt8) : Option (MState isa.Regs) :=
  (parse c abi.pageBits abi.stackTop bs).map (·.img.init abi)

/-! ### Imports resolved -/

/-- The address of each function, or `none` if one is missing. -/
def resolveAll (resolve : List UInt8 → List UInt8 → Option UInt64) (dll : List UInt8) :
    List (List UInt8) → Option (List UInt64)
  | [] => some []
  | f :: fs =>
    match resolve dll f, resolveAll resolve dll fs with
    | some a, some as => some (a :: as)
    | _, _ => none

/-- Writes the addresses as 8-byte little-endian slots from offset `off`. -/
def fillSlots (sec : List UInt8) : Nat → List UInt64 → List UInt8
  | _, [] => sec
  | off, a :: as => fillSlots (patchBytes sec off (natBytes 8 a.toNat)) (off + 8) as

/-- The image Windows maps, with the headers first, then the program's sections, then the import
section with its address table filled with `addrs`. -/
def Parsed.withImports (p : Parsed) (addrs : List UInt64) : Image :=
  { p.img with
    segments := p.headers :: p.img.segments ++
      [{ p.idata with bytes := fillSlots p.idata.bytes (p.imports.iat - (p.idata.vaddr.toNat - p.base)) addrs }] }

/-- The fuller loader model, in which `resolve` gives the address of each imported function. -/
def loadWith (c : Config) {isa : Isa} (abi : Abi isa)
    (resolve : List UInt8 → List UInt8 → Option UInt64) (bs : List UInt8) :
    Option (MState isa.Regs) :=
  match parse c abi.pageBits abi.stackTop bs with
  | none => none
  | some p =>
    (resolveAll resolve p.imports.dll p.imports.funcs).map fun addrs => (p.withImports addrs).init abi

end Millipede.Pe
