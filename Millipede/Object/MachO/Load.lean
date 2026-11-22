import Millipede.Object.MachO.Format

/-!
# The Mach-O loader model

The loader model describes what arm64 macOS does when it starts an executable: the kernel's
`execve` (`load_machfile` in XNU) maps the segments and checks the code signature, and dyld,
which the kernel starts first, loads `libSystem` and calls the entry point that `LC_MAIN` gives.
It is a trusted specification. It accepts only files of the narrow shape described in
Format.lean, and it is deliberately stricter than macOS: whatever the model accepts, macOS loads
to the same memory, while the model refuses much that macOS accepts, such as symbols, fixups,
initialisers, more than one section per segment, and unsigned or differently signed files.

`MachO.parse c pageBits stackTop bs` reads the file into an `Image`, or returns `none`, by
checking the following:

1. The header is exactly that of an arm64 `MH_EXECUTE` file with the flags
   `MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_PIE`. Its `ncmds` commands fill its
   `sizeofcmds` bytes exactly, and each has a size that is a multiple of 8.
2. The commands are `__PAGEZERO` of `c.pageZero` bytes, then `__TEXT`, then zero or more further
   segments, then `__LINKEDIT`, `LC_DYLD_INFO_ONLY`, `LC_SYMTAB`, `LC_DYSYMTAB`,
   `LC_LOAD_DYLINKER`, `LC_UUID`, `LC_BUILD_VERSION`, `LC_MAIN`, `LC_LOAD_DYLIB` and
   `LC_CODE_SIGNATURE`, and nothing else. The dyld-information, symbol-table, dynamic-linker,
   build-version and library commands are exactly the constants of Format.lean, so there is no
   fixup, symbol, exported or imported name, and the only library is libSystem.
3. Each image segment's command is in canonical form, with one `S_REGULAR` section that has no
   relocations and lies within the segment, its name is the one for its protection, its maximum and initial protections are
   equal, its file offset and file size are whole pages, and its file range lies before
   `__LINKEDIT`. It becomes a segment with the command's address, its file bytes, its memory size
   and its protection. The kernel fills memory past the file bytes with zeros.
4. `__TEXT` starts at file offset 0 and covers the header page, which is mapped but which the
   model leaves out, followed by the code. Its image segment starts one page after `__TEXT`.
5. `__LINKEDIT` starts on a page boundary, is read-only, follows the last segment in memory, and
   runs to the end of the file. It starts with the 16 bytes `linkeditPre`, and the code signature
   follows, which must equal `codeSignature` of every byte before it. The kernel checks a page's
   hash only when the page is first touched, so the model, which checks every page, is stricter.
6. The entry point is `__TEXT`'s address plus `LC_MAIN.entryoff`, and the stack size is
   `LC_MAIN.stacksize` less `c.stackReserve`.
7. The image passes `imageOk`, which requires `Image.valid` and the facts of `Config`.

`load` is then `Image.init abi` of the parsed image.

The model assumes that the program is loaded at the addresses in the file. macOS slides a
position-independent executable by a random amount; compiled code addresses everything relative
to the program counter and never observes an address, as for the stack, whose address the model
fixes at `abi.stackTop`. The model also leaves unmapped what the program does not use: the header
page, `__LINKEDIT`, dyld, libSystem and the rest of the process, which only makes it stricter.
-/

namespace Millipede.MachO

open Millipede.Elf (takeNat zeros)

/-- An image segment from its segment command, or `none` if it breaks a rule of rule 3. `limit`
is the file offset of `__LINKEDIT`. -/
def loadSeg (P limit : Nat) (bs : List UInt8) (s : SegCmd) : Option Segment :=
  let p := permOf s.initprot
  if s.initprot < 8 ∧ s.maxprot = s.initprot ∧ s.name = segName p ∧ s.flags = 0 ∧
      s.nsects = 1 ∧ sectOk p s.vmaddr s.fileoff s.filesize s.sects = true ∧ s.fileoff % P = 0 ∧ s.filesize % P = 0 ∧
      s.fileoff + s.filesize ≤ limit then
    some { vaddr := UInt64.ofNat s.vmaddr, bytes := (bs.drop s.fileoff).take s.filesize,
           memSize := s.vmsize, perm := p }
  else none

/-- A segment command, which must be in canonical form. -/
def segOf (c : Cmd) : Option SegCmd :=
  if c.cmd = LC_SEGMENT_64 ∧ encodeSeg (decodeSeg c.body) = c.body then some (decodeSeg c.body)
  else none

/-- The image segments of the commands between `__TEXT` and `__LINKEDIT`. -/
def loadSegs (P limit : Nat) (bs : List UInt8) : List Cmd → Option (List Segment)
  | [] => some []
  | c :: cs =>
    match segOf c >>= loadSeg P limit bs, loadSegs P limit bs cs with
    | some sg, some sgs => some (sg :: sgs)
    | _, _ => none

/-- The code segment that `__TEXT` maps after the header page. -/
def textSeg (P limit : Nat) (bs : List UInt8) (t : SegCmd) : Option Segment :=
  if t.fileoff = 0 ∧ P ≤ t.filesize ∧ P ≤ t.vmsize ∧ t.vmaddr + t.vmsize < 2 ^ 64 then
    loadSeg P limit bs { t with vmaddr := t.vmaddr + P, vmsize := t.vmsize - P, fileoff := P,
                                filesize := t.filesize - P }
  else none

/-- Reads the commands after `__TEXT`: the image segments, then the ten fixed commands. -/
def parseCmds (c : Config) (P : Nat) (bs : List UInt8) (t : SegCmd) (rest : List Cmd) :
    Option Image :=
  match rest.drop (rest.length - 10) with
  | [le, di, st, ds, dl, uu, bv, mn, lb, cs] =>
    match segOf le with
    | none => none
    | some lk =>
      let L := lk.fileoff
      match textSeg P L bs t, loadSegs P L bs (rest.take (rest.length - 10)) with
      | some s0, some sgs =>
        let segs := s0 :: sgs
        let entryoff := natOfBytes (mn.body.take 8)
        let stacksize := natOfBytes (mn.body.drop 8)
        if L % P = 0 ∧ lk = ⟨nLINKEDIT, lastEnd segs, bs.length - L, L, bs.length - L, 1, 1, 0,
              0, []⟩ ∧ di = dyldInfoCmd ∧ st = symtabCmd L ∧ ds = dysymtabCmd ∧
            dl = dylinkerCmd ∧ uu.cmd = LC_UUID ∧ uu.body.length = 16 ∧ bv = buildCmd ∧
            mn = mainCmd entryoff stacksize ∧ entryoff < t.vmsize ∧ lb = dylibCmd ∧
            cs = sigCmd (L + 16) (bs.length - (L + 16)) ∧ (bs.drop L).take 16 = linkeditPre ∧
            bs.drop (L + 16) = codeSignature (bs.take (L + 16)) t.filesize then
          some { segments := segs, entry := UInt64.ofNat (t.vmaddr + entryoff),
                 stackSize := stacksize - c.stackReserve }
        else none
      | _, _ => none
  | _ => none

/-- Parses an executable into the image that macOS maps, or returns `none`. -/
def parse (c : Config) (pageBits : Nat) (stackTop : UInt64) (bs : List UInt8) : Option Image :=
  let ncmds := natOfBytes ((bs.drop 16).take 4)
  let sizeofcmds := natOfBytes ((bs.drop 20).take 4)
  if bs.take HDR_SIZE = encodeHdr ncmds sizeofcmds then
    match decodeCmds ncmds ((bs.drop HDR_SIZE).take sizeofcmds) with
    | some (pz :: tx :: rest) =>
      if pz = pageZeroCmd c then
        match segOf tx with
        | some t =>
          match parseCmds c (2 ^ pageBits) bs t rest with
          | some img => if imageOk c pageBits stackTop img then some img else none
          | none => none
        | none => none
      else none
    | _ => none
  else none

/-- The loader model, which gives the machine state in which the process starts, or `none` when
the file is refused. -/
def load (c : Config) {isa : Isa} (abi : Abi isa) (bs : List UInt8) : Option (MState isa.Regs) :=
  (parse c abi.pageBits abi.stackTop bs).map (·.init abi)

end Millipede.MachO
