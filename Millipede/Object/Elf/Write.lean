import Millipede.Object.Elf.Format

/-!
# The static ELF64 writer

`Elf.write c pageBits stackTop img` serialises an `Image` as a static executable of type `ET_EXEC`,
laid out as follows:

```
offset 0            ELF header (64 bytes), e_phoff = 64, no section headers
offset 64           program headers: one PT_LOAD per segment (in order), then PT_GNU_STACK
… zero padding to a page boundary
for each segment    its bytes, then zeros up to the next page boundary
```

Each `PT_LOAD` has a page-aligned `p_offset` and `p_vaddr`, so `p_offset ≡ p_vaddr (mod p_align)`
with `p_align` the page size. Its `p_filesz` is the segment's initialised bytes, its `p_memsz` the
segment's size in memory, which the kernel fills with zeros beyond `p_filesz`, and its flags come
from the segment's permission. Each segment's file bytes are followed by zeros up to the end of the
page, so the whole-page `mmap` that the kernel performs maps exactly the segment's bytes followed
by zeros. `PT_GNU_STACK` has the flags `RW`, which make the stack non-executable, because without
it Linux on x86-64 would make every readable mapping executable. Its `p_memsz` is the requested
stack size.

The writer refuses an image that fails `imageOk` or whose header fields do not fit their widths.
-/

namespace Millipede.Elf

/-- The program header of a segment whose bytes start at file offset `off`. -/
def segPhdr (P off : Nat) (sg : Segment) : Phdr where
  type := PT_LOAD
  flags := permFlags sg.perm
  offset := off
  vaddr := sg.vaddr.toNat
  paddr := sg.vaddr.toNat
  filesz := sg.bytes.length
  memsz := sg.memSize
  align := P

/-- The `PT_LOAD` headers for the segments, with the first one's bytes at file offset `off`. -/
def layout (P : Nat) : Nat → List Segment → List Phdr
  | _, [] => []
  | off, sg :: sgs => segPhdr P off sg :: layout P (off + chunkLen P sg.bytes.length) sgs

/-- The file contents of the segments, each one's bytes padded with zeros to a multiple of the
page size. -/
def blob (P : Nat) : List Segment → List UInt8
  | [] => []
  | sg :: sgs => sg.bytes ++ zeros (pad P sg.bytes.length) ++ blob P sgs

/-- `PT_GNU_STACK`, which is read-write and not executable, and whose `p_memsz` records the stack
size. -/
def stackPhdr (size : Nat) : Phdr where
  type := PT_GNU_STACK
  flags := PF_R + PF_W
  offset := 0
  vaddr := 0
  paddr := 0
  filesz := 0
  memsz := size
  align := 16

/-- The bytes of the ELF header plus `n` program headers. -/
def headerSize (n : Nat) : Nat := EHDR_SIZE + PHDR_SIZE * n

/-- The ELF header for an image with `phnum` program headers. -/
def ehdrOf (c : Config) (img : Image) (phnum : Nat) : Ehdr where
  type := ET_EXEC
  machine := c.machine
  version := EV_CURRENT
  entry := img.entry.toNat
  phoff := EHDR_SIZE
  shoff := 0
  flags := 0
  ehsize := EHDR_SIZE
  phentsize := PHDR_SIZE
  phnum := phnum
  shentsize := SHDR_SIZE
  shnum := 0
  shstrndx := 0

/-- The file offset of the first segment's bytes, which is the headers rounded up to a page. -/
def dataStart (P : Nat) (img : Image) : Nat := chunkLen P (headerSize (img.segments.length + 1))

/-- All the program headers of the file. -/
def phdrsOf (P : Nat) (img : Image) : List Phdr :=
  layout P (dataStart P img) img.segments ++ [stackPhdr img.stackSize]

/-- The file, assuming that the checks passed. -/
def fileBytes (c : Config) (P : Nat) (img : Image) : List UInt8 :=
  let phs := phdrsOf P img
  encodeEhdr (ehdrOf c img phs.length) ++ encodePhdrs phs ++
    zeros (dataStart P img - headerSize phs.length) ++ blob P img.segments

/-- The ELF writer, which refuses images that are not valid for the platform or whose header
fields would not fit. -/
def write (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) :
    Except String (List UInt8) :=
  let P := 2 ^ pageBits
  let phs := phdrsOf P img
  if imageOk c pageBits stackTop img = false then
    .error "elf: image not valid for this platform"
  else if ((ehdrOf c img phs.length).fits && phs.all Phdr.fits) = false then
    .error "elf: header field out of range"
  else .ok (fileBytes c P img)

/-- The writer with a `ByteArray` result, used to write the file. -/
def writeByteArray (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) :
    Except String ByteArray :=
  (write c pageBits stackTop img).map (fun bs => ⟨bs.toArray⟩)

end Millipede.Elf
