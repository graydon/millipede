import Millipede.Object.MachO.Format
import Millipede.Object.Elf.Write

/-!
# The Mach-O writer

`MachO.write c pageBits stackTop img` serialises an `Image` as a position-independent arm64
macOS executable, laid out as follows, with `P = 2 ^ pageBits` (16 KiB):

```
offset 0            header (32 bytes) and load commands, then zeros to P
offset P            the first segment (the code), then zeros to a page boundary
                    each further segment, then zeros to a page boundary
offset L            __LINKEDIT: an 8-byte string table, 8 bytes of padding,
offset L + 16       the code signature
```

The load commands are, in order: `__PAGEZERO`; `__TEXT`, which maps the file from offset 0, so
the header page followed by the code, at one page below the code's address; one segment per
further image segment (`__RODATA` or `__DATA`, by permission); `__LINKEDIT`; and then
`LC_DYLD_INFO_ONLY`, `LC_SYMTAB`, `LC_DYSYMTAB`, `LC_LOAD_DYLINKER`, `LC_UUID`,
`LC_BUILD_VERSION`, `LC_MAIN`, `LC_LOAD_DYLIB` and `LC_CODE_SIGNATURE`. This is the order lld
uses. Each image segment has one section covering its initialised bytes, so that tools can
disassemble the code.

A segment's file size is its bytes rounded up to whole pages, and its memory size the image's,
which must be whole pages, so the kernel maps the bytes, the zero padding after them, and zero
fill to the end. The UUID is the first 16 bytes of the SHA-256 hash of the segments' contents.
`LC_MAIN` gives the entry point as an offset from the header and asks for `stackSize +
stackReserve` bytes of stack. The signature covers every byte before it.

The writer refuses an image that fails `imageOk`, a segment field that does not fit, and a file
of 4 GiB or more, since signature and table offsets are 32 bits.
-/

namespace Millipede.MachO

open Millipede.Elf (zeros chunkLen pad blob)

/-- The segment command of an image segment whose bytes start at file offset `off`. -/
def segCmdOf (P off : Nat) (sg : Segment) : SegCmd where
  name := segName sg.perm
  vmaddr := sg.vaddr.toNat
  vmsize := sg.memSize
  fileoff := off
  filesize := chunkLen P sg.bytes.length
  maxprot := protOf sg.perm
  initprot := protOf sg.perm
  nsects := 1
  flags := 0
  sects := encodeSect sg.perm sg.vaddr.toNat sg.bytes.length off

/-- `__TEXT`, which maps the header page and then the code segment `s0`. -/
def textCmdOf (P : Nat) (s0 : Segment) : SegCmd :=
  { segCmdOf P P s0 with
    vmaddr := s0.vaddr.toNat - P, vmsize := P + s0.memSize, fileoff := 0,
    filesize := P + chunkLen P s0.bytes.length }

/-- The segment commands of the segments, the first one's bytes at file offset `off`. -/
def layout (P : Nat) : Nat → List Segment → List SegCmd
  | _, [] => []
  | off, sg :: sgs => segCmdOf P off sg :: layout P (off + chunkLen P sg.bytes.length) sgs

/-- A segment command as a load command. -/
def segLC (s : SegCmd) : Cmd := ⟨LC_SEGMENT_64, encodeSeg s⟩

/-- `__LINKEDIT`, read-only, holding `size` bytes at file offset `L` and mapped at `vmaddr`. -/
def linkeditSeg (vmaddr L size : Nat) : SegCmd :=
  ⟨nLINKEDIT, vmaddr, size, L, size, 1, 1, 0, 0, []⟩

/-- The file offset of `__LINKEDIT`: the header page and every segment's whole pages. -/
def linkOff (P : Nat) (img : Image) : Nat := P + (blob P img.segments).length

/-- The load commands of an image whose first segment is `s0`. -/
def cmdsOf (c : Config) (P : Nat) (img : Image) (s0 : Segment) (rest : List Segment) :
    List Cmd :=
  let L := linkOff P img
  let sz := sigSize (L + 16)
  pageZeroCmd c :: segLC (textCmdOf P s0) ::
    ((layout P (P + chunkLen P s0.bytes.length) rest).map segLC ++
      [segLC (linkeditSeg (lastEnd img.segments) L (16 + sz)), dyldInfoCmd, symtabCmd L,
       dysymtabCmd, dylinkerCmd, ⟨LC_UUID, (Sha256.hash (blob P img.segments)).take 16⟩,
       buildCmd, mainCmd (img.entry.toNat - (s0.vaddr.toNat - P)) (img.stackSize + c.stackReserve),
       dylibCmd, sigCmd (L + 16) sz])

/-- The header and the load commands. -/
def hdrBytes (c : Config) (P : Nat) (img : Image) (s0 : Segment) (rest : List Segment) :
    List UInt8 :=
  let cmds := cmdsOf c P img s0 rest
  encodeHdr cmds.length (encodeCmds cmds).length ++ encodeCmds cmds

/-- The file before the signature. -/
def unsigned (c : Config) (P : Nat) (img : Image) (s0 : Segment) (rest : List Segment) :
    List UInt8 :=
  let hdr := hdrBytes c P img s0 rest
  hdr ++ zeros (P - hdr.length) ++ blob P img.segments ++ linkeditPre

/-- The file, assuming that the checks passed. -/
def fileBytes (c : Config) (P : Nat) (img : Image) : List UInt8 :=
  match img.segments with
  | [] => []
  | s0 :: rest =>
    let u := unsigned c P img s0 rest
    u ++ codeSignature u (P + chunkLen P s0.bytes.length)

/-- The fields of the file that are 64 bits wide fit: the segment commands, the end of the code
segment and of the last segment, and the stack size asked for. -/
def fitsOk (c : Config) (P : Nat) (img : Image) : Bool :=
  match img.segments with
  | [] => false
  | s0 :: rest =>
    (textCmdOf P s0).fits && (layout P (P + chunkLen P s0.bytes.length) rest).all SegCmd.fits &&
      decide (s0.vaddr.toNat + s0.memSize < 2 ^ 64) && decide (lastEnd img.segments < 2 ^ 64) &&
      decide (img.stackSize + c.stackReserve < 2 ^ 64)

/-- The Mach-O writer, which refuses images that are not valid for the platform or whose fields
would not fit. -/
def write (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) :
    Except String (List UInt8) :=
  let P := 2 ^ pageBits
  if imageOk c pageBits stackTop img = false then
    .error "macho: image not valid for this platform"
  else if fitsOk c P img = false then
    .error "macho: field out of range"
  else if (fileBytes c P img).length < 2 ^ 32 then .ok (fileBytes c P img)
  else .error "macho: file of 4 GiB or more"

/-- The writer with a `ByteArray` result, used to write the file. -/
def writeByteArray (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) :
    Except String ByteArray :=
  (write c pageBits stackTop img).map (fun bs => ⟨bs.toArray⟩)

end Millipede.MachO
