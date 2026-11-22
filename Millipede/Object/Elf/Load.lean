import Millipede.Object.Elf.Format

/-!
# The ELF64 loader model

The loader model describes what `execve` does with a static executable, and it is a trusted
specification listed in the assumption ledger. It describes the subset of Linux's
`load_elf_binary` that the compiler's files use, and it is deliberately stricter than the kernel.
Whatever the model accepts, the kernel loads to the same memory, while the model refuses much that
the kernel would accept, such as dynamic executables, position-independent executables, TLS, and
unsorted or overlapping segments.

`Elf.parse c pageBits stackTop bs` reads the file into an `Image`, or returns `none`, by checking
the following:

1. The ELF header has an `e_ident` of exactly `ELFCLASS64`, little-endian, `EV_CURRENT` and the
   SysV ABI, with `e_type = ET_EXEC`, `e_machine = c.machine`, `e_version = 1`, `e_flags = 0`,
   `e_ehsize = 64` and `e_phentsize = 56`, and the program-header table lies inside the file.
   Section headers are ignored, as the kernel ignores them.
2. The program headers are zero or more `PT_LOAD` headers followed by exactly one `PT_GNU_STACK`,
   and nothing else, so there is no `PT_INTERP`, `PT_DYNAMIC` or `PT_TLS`. The stack header's
   flags are exactly `R|W`, for a non-executable stack, and its `p_memsz` is the stack size.
3. Each `PT_LOAD` becomes a segment. Its flags are only `R`, `W` and `X`, its `p_offset` is
   page-aligned, and its `p_align` is the page size, so the congruence
   `p_offset ≡ p_vaddr (mod p_align)` holds once `p_vaddr` is page-aligned, which the image check
   requires. `p_filesz ≤ p_memsz`, the file bytes lie inside the file, and the file bytes after
   them up to the end of the page are zero. The last check makes the model faithful to
   whole-page `mmap`, since the kernel maps the file page by page, so those bytes become visible
   in memory, and the model says they are zero. Bytes past `p_filesz` up to `p_memsz` are zero,
   as the kernel's zero fill of `.bss` makes them.
4. The image passes `imageOk`. This requires `Image.valid` and the facts of `Config`, which are
   that the page size is the operating system's, or with `fullPages` the largest it may use with
   every segment ending on such a page boundary, that segments lie at or above `minAddr`, that
   the stack top is at or below `maxAddr`, and that the stack size is at most `maxStack`. The
   program-header table must also fit in one page, because the kernel refuses larger ones.

`load` is then `Image.init abi` of the parsed image. Its memory holds the segment bytes with zero
fill, page permissions come from the segment flags, and a read-write stack of the recorded size
lies below `abi.stackTop`. The registers are the ABI's entry registers at `e_entry`, and the world
is empty.

The model assumes that the kernel's page size is `2 ^ c.osPageBits`, that the stack is at
`abi.stackTop` with no address randomisation, and that at least the recorded size is available,
since Linux grows the stack on demand up to `RLIMIT_STACK`. Compiled code uses nothing that the
model leaves unmapped, such as the vDSO or the `argv` area, and leaving them unmapped only makes
the model stricter, which is sound. On x86-64, `X` and `W` imply that a page is readable in
hardware, and the model does not grant that, which again only makes it stricter.
-/

namespace Millipede.Elf

/-- One `PT_LOAD` header as a segment, or `none` if it breaks one of the rules in the module
documentation. -/
def loadSeg (P : Nat) (bs : List UInt8) (p : Phdr) : Option Segment :=
  if p.flags < 8 ∧ p.offset % P = 0 ∧ p.align = P ∧ p.filesz ≤ p.memsz ∧
      p.offset + p.filesz ≤ bs.length ∧
      ((bs.drop (p.offset + p.filesz)).take (pad P p.filesz)).all (· == 0) = true then
    some { vaddr := UInt64.ofNat p.vaddr, bytes := (bs.drop p.offset).take p.filesz,
           memSize := p.memsz, perm := flagsPerm p.flags }
  else none

/-- All `PT_LOAD` headers as segments, in order. -/
def loadSegs (P : Nat) (bs : List UInt8) : List Phdr → Option (List Segment)
  | [] => some []
  | p :: ps =>
    match loadSeg P bs p, loadSegs P bs ps with
    | some sg, some sgs => some (sg :: sgs)
    | _, _ => none

/-- Splits the program headers into the `PT_LOAD` headers and the final `PT_GNU_STACK`. -/
def splitPhdrs : List Phdr → Option (List Phdr × Phdr)
  | [] => none
  | p :: ps =>
    if p.type = PT_LOAD then (splitPhdrs ps).map (fun r => (p :: r.1, r.2))
    else if p.type = PT_GNU_STACK ∧ ps = [] then some ([], p)
    else none

/-- The checks on the ELF header, as listed in the module documentation. -/
def ehdrOk (c : Config) (h : Ehdr) (fileLen : Nat) : Bool :=
  h.type == ET_EXEC && h.machine == c.machine && h.version == EV_CURRENT && h.flags == 0 &&
    h.ehsize == EHDR_SIZE && h.phentsize == PHDR_SIZE &&
    decide (h.phoff + PHDR_SIZE * h.phnum ≤ fileLen)

/-- Parses a static executable into the image that the kernel maps, or returns `none`. -/
def parse (c : Config) (pageBits : Nat) (stackTop : UInt64) (bs : List UInt8) : Option Image :=
  match decodeEhdr bs with
  | none => none
  | some h =>
    if ehdrOk c h bs.length then
      match splitPhdrs (decodePhdrs h.phnum (bs.drop h.phoff)) with
      | none => none
      | some (loads, st) =>
        if st.flags = PF_R + PF_W then
          match loadSegs (2 ^ pageBits) bs loads with
          | none => none
          | some segs =>
            let img : Image :=
              { segments := segs, entry := UInt64.ofNat h.entry, stackSize := st.memsz }
            if imageOk c pageBits stackTop img then some img else none
        else none
    else none

/-- The loader model, which gives the machine state in which `execve` starts the process, or
`none` when the file is refused. -/
def load (c : Config) {isa : Isa} (abi : Abi isa) (bs : List UInt8) : Option (MState isa.Regs) :=
  (parse c abi.pageBits abi.stackTop bs).map (·.init abi)

end Millipede.Elf
