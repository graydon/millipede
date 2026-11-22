import Millipede.Object.Image

/-!
# The ELF64 file format

This file describes the shape of a static ELF64 executable as far as the writer and the loader
model need it. Fixed-width little-endian fields are byte lists, read with `takeNat`. The ELF
header `Ehdr`, 64 bytes long, and the program header `Phdr`, 56 bytes long, are records of `Nat`
fields with encoders and sequential decoders, which are proved inverse for headers whose fields
fit their widths. `Config` holds the facts about the operating system on which the loader model
depends. Everything is defined over `List UInt8` and `Nat` by structural recursion.
-/

namespace Millipede.Elf

/-! ### Little-endian fields -/

/-- Reads a `k`-byte little-endian field and returns it with the rest of the bytes. -/
def takeNat (k : Nat) (bs : List UInt8) : Nat × List UInt8 := (natOfBytes (bs.take k), bs.drop k)

@[simp] theorem takeNat_natBytes (n k : Nat) (rest : List UInt8) :
    takeNat k (natBytes k n ++ rest) = (n % 256 ^ k, rest) := by
  simp [takeNat, List.take_left' (natBytes_length k n), List.drop_left' (natBytes_length k n),
    natOfBytes_natBytes]

/-- A field value fits in `k` bytes. -/
def fits (k n : Nat) : Bool := n < 256 ^ k

@[simp] theorem fits_iff (k n : Nat) : fits k n = true ↔ n < 256 ^ k := by simp [fits]

theorem mod_of_fits {k n : Nat} (h : fits k n = true) : n % 256 ^ k = n :=
  Nat.mod_eq_of_lt (by simpa [fits] using h)

/-- `n` zero bytes. -/
def zeros (n : Nat) : List UInt8 := List.replicate n 0

@[simp] theorem zeros_length (n : Nat) : (zeros n).length = n := List.length_replicate

/-! ### Constants -/

/-- `e_ident`, which holds the magic number, `ELFCLASS64`, `ELFDATA2LSB`, `EV_CURRENT`,
`ELFOSABI_SYSV`, ABI version 0 and padding. -/
def ident : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def ET_EXEC : Nat := 2
def EV_CURRENT : Nat := 1
def EHDR_SIZE : Nat := 64
def PHDR_SIZE : Nat := 56
def SHDR_SIZE : Nat := 64
def PT_LOAD : Nat := 1
def PT_GNU_STACK : Nat := 0x6474e551
def PF_X : Nat := 1
def PF_W : Nat := 2
def PF_R : Nat := 4

/-- The program-header flags for a permission. -/
def permFlags (p : Perm) : Nat :=
  (if p.r then PF_R else 0) + (if p.w then PF_W else 0) + (if p.x then PF_X else 0)

/-- The permission given by program-header flags. The loader checks that `flags < 8`. -/
def flagsPerm (f : Nat) : Perm := ⟨f / 4 % 2 == 1, f / 2 % 2 == 1, f % 2 == 1⟩

theorem flagsPerm_permFlags (p : Perm) : flagsPerm (permFlags p) = p := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

theorem permFlags_lt (p : Perm) : permFlags p < 8 := by
  obtain ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;> decide

/-! ### Operating-system facts -/

/-- What the loader model assumes about the operating system, which the assumption ledger lists.
`machine` is the `e_machine` the kernel runs, 62 for x86-64. `osPageBits` is the base-2 logarithm
of the kernel's page size, which the ABI's layout page size must equal, because mappings are made
in whole pages. `minAddr` is the lowest address at which a segment may be mapped, the kernel's
`vm.mmap_min_addr`, and `maxAddr` the end of user address space, below which the whole image and
the stack lie.

`maxStack` is the largest stack the model promises. ELF cannot make Linux reserve a stack, which
grows on demand up to `RLIMIT_STACK`, 8 MiB by default, and also holds `argv` and `envp`. The
requested size is recorded in `PT_GNU_STACK.p_memsz`, as `ld -z stack-size` does, and the loader
model refuses requests above `maxStack`.

When `fullPages` holds, `osPageBits` is the largest page size of the platform's kernels, 64 KiB on
arm64 Linux, whose kernels use 4, 16 or 64 KiB pages, and every segment must end at a boundary of
such a page. The kernel maps `[p_vaddr, p_vaddr + p_memsz)` in its own pages, which are no larger,
so it maps exactly the pages that the model's segments cover whatever its page size. -/
structure Config where
  machine : Nat
  osPageBits : Nat
  minAddr : Nat
  maxAddr : Nat
  maxStack : Nat
  fullPages : Bool := false
deriving DecidableEq, Repr

/-- Linux on x86-64, with `EM_X86_64`, 4 KiB pages, an `mmap_min_addr` of 64 KiB, a 47-bit user
space less the guard page, and at most 4 MiB of stack. -/
def Config.x64Linux : Config where
  machine := 62
  osPageBits := 12
  minAddr := 0x10000
  maxAddr := 2 ^ 47 - 2 ^ 12
  maxStack := 2 ^ 22

/-- Linux on AArch64, with `EM_AARCH64` (183), segments laid out in 64 KiB pages and extended to
whole pages, which kernels with 4, 16 or 64 KiB pages map alike, an `mmap_min_addr` of 64 KiB, a
user space of at least 39 bits, which is the smallest common configuration of 4 KiB pages and 3
levels, and at most 4 MiB of stack. -/
def Config.a64Linux : Config where
  machine := 183
  osPageBits := 16
  minAddr := 0x10000
  maxAddr := 2 ^ 39 - 2 ^ 16
  maxStack := 2 ^ 22
  fullPages := true

/-! ### ELF header -/

/-- The fields of the ELF header after `e_ident`, all little-endian. -/
structure Ehdr where
  type : Nat
  machine : Nat
  version : Nat
  entry : Nat
  phoff : Nat
  shoff : Nat
  flags : Nat
  ehsize : Nat
  phentsize : Nat
  phnum : Nat
  shentsize : Nat
  shnum : Nat
  shstrndx : Nat
deriving DecidableEq, Repr

/-- Every field fits its width. -/
def Ehdr.fits (h : Ehdr) : Bool :=
  Elf.fits 2 h.type && Elf.fits 2 h.machine && Elf.fits 4 h.version && Elf.fits 8 h.entry &&
  Elf.fits 8 h.phoff && Elf.fits 8 h.shoff && Elf.fits 4 h.flags && Elf.fits 2 h.ehsize &&
  Elf.fits 2 h.phentsize && Elf.fits 2 h.phnum && Elf.fits 2 h.shentsize &&
  Elf.fits 2 h.shnum && Elf.fits 2 h.shstrndx

/-- The 64-byte ELF header. -/
def encodeEhdr (h : Ehdr) : List UInt8 :=
  ident ++ natBytes 2 h.type ++ natBytes 2 h.machine ++ natBytes 4 h.version ++
  natBytes 8 h.entry ++ natBytes 8 h.phoff ++ natBytes 8 h.shoff ++ natBytes 4 h.flags ++
  natBytes 2 h.ehsize ++ natBytes 2 h.phentsize ++ natBytes 2 h.phnum ++
  natBytes 2 h.shentsize ++ natBytes 2 h.shnum ++ natBytes 2 h.shstrndx

/-- Decodes the fields after `e_ident`, reading missing bytes as zero. -/
def decodeFields (bs : List UInt8) : Ehdr :=
  let (type, bs) := takeNat 2 bs
  let (machine, bs) := takeNat 2 bs
  let (version, bs) := takeNat 4 bs
  let (entry, bs) := takeNat 8 bs
  let (phoff, bs) := takeNat 8 bs
  let (shoff, bs) := takeNat 8 bs
  let (flags, bs) := takeNat 4 bs
  let (ehsize, bs) := takeNat 2 bs
  let (phentsize, bs) := takeNat 2 bs
  let (phnum, bs) := takeNat 2 bs
  let (shentsize, bs) := takeNat 2 bs
  let (shnum, bs) := takeNat 2 bs
  let (shstrndx, _) := takeNat 2 bs
  { type, machine, version, entry, phoff, shoff, flags, ehsize, phentsize, phnum, shentsize,
    shnum, shstrndx }

/-- Decodes the ELF header, which is `none` unless the file starts with exactly `ident`. -/
def decodeEhdr (bs : List UInt8) : Option Ehdr :=
  if bs.take 16 = ident then some (decodeFields (bs.drop 16)) else none

@[simp] theorem encodeEhdr_length (h : Ehdr) : (encodeEhdr h).length = EHDR_SIZE := by
  simp [encodeEhdr, ident, EHDR_SIZE]

theorem decodeEhdr_encodeEhdr (h : Ehdr) (hf : h.fits = true) (rest : List UInt8) :
    decodeEhdr (encodeEhdr h ++ rest) = some h := by
  simp only [Ehdr.fits, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hf
  have hi : ident.length = 16 := rfl
  simp only [decodeEhdr, encodeEhdr, List.append_assoc, List.take_left' hi,
    List.drop_left' hi, ite_true, decodeFields, takeNat_natBytes, mod_of_fits h1,
    mod_of_fits h2, mod_of_fits h3, mod_of_fits h4, mod_of_fits h5, mod_of_fits h6,
    mod_of_fits h7, mod_of_fits h8, mod_of_fits h9, mod_of_fits h10, mod_of_fits h11,
    mod_of_fits h12, mod_of_fits h13]

/-! ### Program headers -/

/-- An ELF64 program header. -/
structure Phdr where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  paddr : Nat
  filesz : Nat
  memsz : Nat
  align : Nat
deriving DecidableEq, Repr

/-- Every field fits its width. -/
def Phdr.fits (p : Phdr) : Bool :=
  Elf.fits 4 p.type && Elf.fits 4 p.flags && Elf.fits 8 p.offset && Elf.fits 8 p.vaddr &&
  Elf.fits 8 p.paddr && Elf.fits 8 p.filesz && Elf.fits 8 p.memsz && Elf.fits 8 p.align

/-- The 56-byte program header. -/
def encodePhdr (p : Phdr) : List UInt8 :=
  natBytes 4 p.type ++ natBytes 4 p.flags ++ natBytes 8 p.offset ++ natBytes 8 p.vaddr ++
  natBytes 8 p.paddr ++ natBytes 8 p.filesz ++ natBytes 8 p.memsz ++ natBytes 8 p.align

/-- Decodes one program header, reading missing bytes as zero. -/
def decodePhdr (bs : List UInt8) : Phdr :=
  let (type, bs) := takeNat 4 bs
  let (flags, bs) := takeNat 4 bs
  let (offset, bs) := takeNat 8 bs
  let (vaddr, bs) := takeNat 8 bs
  let (paddr, bs) := takeNat 8 bs
  let (filesz, bs) := takeNat 8 bs
  let (memsz, bs) := takeNat 8 bs
  let (align, _) := takeNat 8 bs
  { type, flags, offset, vaddr, paddr, filesz, memsz, align }

/-- The program-header table. -/
def encodePhdrs : List Phdr → List UInt8
  | [] => []
  | p :: ps => encodePhdr p ++ encodePhdrs ps

/-- Decodes `n` consecutive program headers. -/
def decodePhdrs : Nat → List UInt8 → List Phdr
  | 0, _ => []
  | n + 1, bs => decodePhdr bs :: decodePhdrs n (bs.drop PHDR_SIZE)

@[simp] theorem encodePhdr_length (p : Phdr) : (encodePhdr p).length = PHDR_SIZE := by
  simp [encodePhdr, PHDR_SIZE]

@[simp] theorem encodePhdrs_length : ∀ ps : List Phdr,
    (encodePhdrs ps).length = PHDR_SIZE * ps.length
  | [] => rfl
  | p :: ps => by
    simp [encodePhdrs, encodePhdrs_length ps, Nat.mul_succ, Nat.add_comm]

theorem decodePhdr_encodePhdr (p : Phdr) (hf : p.fits = true) (rest : List UInt8) :
    decodePhdr (encodePhdr p ++ rest) = p := by
  simp only [Phdr.fits, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hf
  simp only [decodePhdr, encodePhdr, List.append_assoc, takeNat_natBytes, mod_of_fits h1,
    mod_of_fits h2, mod_of_fits h3, mod_of_fits h4, mod_of_fits h5, mod_of_fits h6,
    mod_of_fits h7, mod_of_fits h8]

theorem decodePhdrs_encodePhdrs : ∀ (ps : List Phdr), ps.all Phdr.fits = true →
    ∀ rest, decodePhdrs ps.length (encodePhdrs ps ++ rest) = ps
  | [], _, _ => rfl
  | p :: ps, hf, rest => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [List.length_cons, decodePhdrs, encodePhdrs, List.append_assoc,
      decodePhdr_encodePhdr p hf.1, List.drop_left' (encodePhdr_length p),
      decodePhdrs_encodePhdrs ps hf.2]

end Millipede.Elf

namespace Millipede.Elf

/-! ### Page arithmetic and image checks shared by writer and loader -/

/-- `l` rounded up to a multiple of `P`, which is the file space that a segment's bytes occupy. -/
def chunkLen (P l : Nat) : Nat := (l + P - 1) / P * P

/-- The zero padding after `l` bytes up to the next multiple of `P`. -/
def pad (P l : Nat) : Nat := chunkLen P l - l

theorem le_chunkLen {P : Nat} (hP : 0 < P) (l : Nat) : l ≤ chunkLen P l := by
  unfold chunkLen
  have h1 := Nat.div_add_mod (l + P - 1) P
  have h2 := Nat.mod_lt (l + P - 1) hP
  rw [Nat.mul_comm] at h1
  omega

theorem chunkLen_mod (P l : Nat) : chunkLen P l % P = 0 := Nat.mul_mod_left _ _

/-- `Image.valid` with only the two ABI fields it reads, so that `Image.valid abi = validAt ..`
holds by `rfl`. -/
def validAt (pageBits : Nat) (stackTop : UInt64) (img : Image) : Bool :=
  let P := 2 ^ pageBits
  let top := stackTop.toNat / P
  let n := img.stackPages pageBits
  0 < img.stackSize && stackTop.toNat % P == 0 && n ≤ top &&
    img.segments.all (Image.segOk pageBits ((top - n) * P)) &&
    Image.sortedDisjoint pageBits img.segments

theorem valid_eq {isa : Isa} (abi : Abi isa) (img : Image) :
    img.valid abi = validAt abi.pageBits abi.stackTop img := rfl

/-- The image checks that both the writer and the loader make. They are `Image.valid`, the
operating-system facts of `Config`, and that the program headers, one per segment plus
`PT_GNU_STACK`, fit in one page, because Linux refuses larger tables. -/
def imageOk (c : Config) (pageBits : Nat) (stackTop : UInt64) (img : Image) : Bool :=
  (pageBits == c.osPageBits &&
    (!c.fullPages || img.segments.all (fun sg => sg.memSize % 2 ^ pageBits == 0))) &&
    validAt pageBits stackTop img &&
    decide (stackTop.toNat ≤ c.maxAddr) && decide (img.stackSize ≤ c.maxStack) &&
    img.segments.all (fun sg => decide (c.minAddr ≤ sg.vaddr.toNat)) &&
    decide (PHDR_SIZE * (img.segments.length + 1) ≤ 2 ^ pageBits)

end Millipede.Elf
