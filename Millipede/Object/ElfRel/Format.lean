import Millipede.Object.Elf.Format
import Millipede.Object.Link

/-!
# The ELF64 relocatable object format

This file describes what the writer and the reader of ELF64 relocatable objects (`ET_REL`, `.o`
files) share. The numbers come from the System V gABI and the two processor supplements, the
x86-64 psABI and ARM IHI 0056, "ELF for the Arm 64-bit Architecture". A record of the file, such
as a section header, a symbol or a relocation entry, is a list of little-endian fields whose
widths a list of numbers gives. `encodeW` writes such a record and `decodeW` reads it back, and
`decodeW_encodeW` proves the two inverse when every field fits its width. The file also defines
string tables, which hold NUL-terminated names, and `Mach`, which gives a machine's `e_machine`
and the relocation types that correspond to each `RelocKind`.
-/

namespace Millipede.ElfRel

open Elf (fits mod_of_fits zeros)

/-! ### Constants of the gABI and the psABIs -/

def ET_REL : Nat := 1
def SHT_NULL : Nat := 0
def SHT_PROGBITS : Nat := 1
def SHT_SYMTAB : Nat := 2
def SHT_STRTAB : Nat := 3
def SHT_RELA : Nat := 4
def SHT_NOBITS : Nat := 8
def SHF_WRITE : Nat := 1
def SHF_ALLOC : Nat := 2
def SHF_EXECINSTR : Nat := 4
def SHF_INFO_LINK : Nat := 0x40
def STB_LOCAL : Nat := 0
def STB_GLOBAL : Nat := 1
def STT_NOTYPE : Nat := 0
def STT_OBJECT : Nat := 1
def STT_FUNC : Nat := 2
def STT_SECTION : Nat := 3
def STT_FILE : Nat := 4
/-- The first reserved section index; indices from here on are not section numbers. -/
def SHN_LORESERVE : Nat := 0xff00
def SHDR_SIZE : Nat := 64
def SYM_SIZE : Nat := 24
def RELA_SIZE : Nat := 24

def EM_X86_64 : Nat := 62
def EM_AARCH64 : Nat := 183

def R_X86_64_64 : Nat := 1
def R_X86_64_PC32 : Nat := 2
def R_X86_64_PLT32 : Nat := 4

def R_AARCH64_ABS64 : Nat := 257
def R_AARCH64_PREL32 : Nat := 261
def R_AARCH64_LD_PREL_LO19 : Nat := 273
def R_AARCH64_ADR_PREL_LO21 : Nat := 274
def R_AARCH64_ADR_PREL_PG_HI21 : Nat := 275
def R_AARCH64_ADD_ABS_LO12_NC : Nat := 277
def R_AARCH64_LDST8_ABS_LO12_NC : Nat := 278
def R_AARCH64_CONDBR19 : Nat := 280
def R_AARCH64_JUMP26 : Nat := 282
def R_AARCH64_CALL26 : Nat := 283
def R_AARCH64_LDST16_ABS_LO12_NC : Nat := 284
def R_AARCH64_LDST32_ABS_LO12_NC : Nat := 285
def R_AARCH64_LDST64_ABS_LO12_NC : Nat := 286
def R_AARCH64_LDST128_ABS_LO12_NC : Nat := 299

/-- `a` is 0 or a power of 2, as `sh_addralign` must be. -/
def isAlign (a : Nat) : Bool := a == 0 || a == 2 ^ Nat.log2 a

/-- The name of the output section into which the default linker scripts of GNU ld and ld.lld
gather the sections of kind `k`. -/
def stdName : SecKind → String
  | .text => ".text"
  | .rodata => ".rodata"
  | .data => ".data"
  | .bss => ".bss"

/-- A section of kind `k` may be named `n`: `n` is `stdName k`, alone or followed by a dot and a
suffix. A system linker places an input section by its name, so a section named `.text` that is
writable would land in the read-only and executable segment, and a name such as `.tdata` or
`.init_array` would give the section a meaning that its kind does not have. -/
def nameFits (k : SecKind) (n : String) : Bool := n == stdName k || n.startsWith (stdName k ++ ".")

/-! ### Records of little-endian fields -/

/-- Writes the values `vs` as little-endian fields of the widths `ws`. -/
def encodeW : List Nat → List Nat → List UInt8
  | w :: ws, v :: vs => natBytes w v ++ encodeW ws vs
  | _, _ => []

/-- Reads one little-endian field of each width in `ws`, reading missing bytes as zero. -/
def decodeW : List Nat → List UInt8 → List Nat
  | [], _ => []
  | w :: ws, bs => natOfBytes (bs.take w) :: decodeW ws (bs.drop w)

/-- Each value fits its width, and there is one value per width. -/
def fitsW : List Nat → List Nat → Bool
  | [], [] => true
  | w :: ws, v :: vs => fits w v && fitsW ws vs
  | _, _ => false

theorem encodeW_length : ∀ (ws vs : List Nat), fitsW ws vs = true →
    (encodeW ws vs).length = ws.sum
  | [], [], _ => rfl
  | w :: ws, v :: vs, h => by
    simp only [fitsW, Bool.and_eq_true] at h
    simp [encodeW, encodeW_length ws vs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [fitsW] at h

theorem decodeW_encodeW : ∀ (ws vs : List Nat), fitsW ws vs = true → ∀ rest : List UInt8,
    decodeW ws (encodeW ws vs ++ rest) = vs
  | [], [], _, _ => rfl
  | w :: ws, v :: vs, h, rest => by
    simp only [fitsW, Bool.and_eq_true] at h
    simp only [encodeW, decodeW, List.append_assoc, List.take_left' (natBytes_length w v),
      List.drop_left' (natBytes_length w v), natOfBytes_natBytes, mod_of_fits h.1,
      decodeW_encodeW ws vs h.2]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [fitsW] at h

/-- A table of records, one after the other. -/
def encodeTab (ws : List Nat) : List (List Nat) → List UInt8
  | [] => []
  | e :: es => encodeW ws e ++ encodeTab ws es

/-- Reads `n` consecutive records of widths `ws`. -/
def decodeTab (ws : List Nat) : Nat → List UInt8 → List (List Nat)
  | 0, _ => []
  | n + 1, bs => decodeW ws bs :: decodeTab ws n (bs.drop ws.sum)

theorem encodeTab_length (ws : List Nat) : ∀ es : List (List Nat), es.all (fitsW ws) = true →
    (encodeTab ws es).length = ws.sum * es.length
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [encodeTab, encodeW_length ws e h.1, encodeTab_length ws es h.2, Nat.mul_succ,
      Nat.add_comm]

theorem decodeTab_encodeTab (ws : List Nat) : ∀ es : List (List Nat), es.all (fitsW ws) = true →
    ∀ rest, decodeTab ws es.length (encodeTab ws es ++ rest) = es
  | [], _, _ => rfl
  | e :: es, h, rest => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.length_cons, decodeTab, encodeTab, List.append_assoc,
      decodeW_encodeW ws e h.1, List.drop_left' (encodeW_length ws e h.1),
      decodeTab_encodeTab ws es h.2]

/-! ### Section headers, symbols and relocation entries -/

/-- The widths of the fields of `Elf64_Shdr`: `sh_name`, `sh_type`, `sh_flags`, `sh_addr`,
`sh_offset`, `sh_size`, `sh_link`, `sh_info`, `sh_addralign` and `sh_entsize`. -/
def shdrW : List Nat := [4, 4, 8, 8, 8, 8, 4, 4, 8, 8]
/-- The widths of the fields of `Elf64_Sym`: `st_name`, `st_info`, `st_other`, `st_shndx`,
`st_value` and `st_size`. -/
def symW : List Nat := [4, 1, 1, 2, 8, 8]
/-- The widths of the fields of `Elf64_Rela`: `r_offset`, `r_info` and `r_addend`. -/
def relaW : List Nat := [8, 8, 8]

theorem shdrW_sum : shdrW.sum = SHDR_SIZE := rfl
theorem symW_sum : symW.sum = SYM_SIZE := rfl
theorem relaW_sum : relaW.sum = RELA_SIZE := rfl

/-- A section header. -/
structure Shdr where
  name : Nat
  type : Nat
  flags : Nat
  addr : Nat
  offset : Nat
  size : Nat
  link : Nat
  info : Nat
  addralign : Nat
  entsize : Nat
deriving DecidableEq, Repr, Inhabited

def Shdr.toList (h : Shdr) : List Nat :=
  [h.name, h.type, h.flags, h.addr, h.offset, h.size, h.link, h.info, h.addralign, h.entsize]

/-- The header of a record of `shdrW`, with zeros for missing fields. -/
def Shdr.ofList : List Nat → Shdr
  | [name, type, flags, addr, offset, size, link, info, addralign, entsize] =>
    { name, type, flags, addr, offset, size, link, info, addralign, entsize }
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem Shdr.ofList_toList (h : Shdr) : Shdr.ofList h.toList = h := rfl

/-- The all-zero header that index 0 must hold. -/
def Shdr.null : Shdr := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A symbol-table entry. `info` holds the binding in its high 4 bits and the type in its low 4
bits. -/
structure Sym where
  name : Nat
  info : Nat
  other : Nat
  shndx : Nat
  value : Nat
  size : Nat
deriving DecidableEq, Repr, Inhabited

def Sym.toList (s : Sym) : List Nat := [s.name, s.info, s.other, s.shndx, s.value, s.size]

def Sym.ofList : List Nat → Sym
  | [name, info, other, shndx, value, size] => { name, info, other, shndx, value, size }
  | _ => ⟨0, 0, 0, 0, 0, 0⟩

@[simp] theorem Sym.ofList_toList (s : Sym) : Sym.ofList s.toList = s := rfl

def Sym.bind (s : Sym) : Nat := s.info / 16
def Sym.type (s : Sym) : Nat := s.info % 16

/-! ### String tables -/

/-- The UTF-8 bytes of a string. -/
def strBytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The string that UTF-8 bytes encode, if they are valid UTF-8. -/
def ofBytes (b : List UInt8) : Option String := String.fromUTF8? ⟨b.toArray⟩

theorem ofBytes_strBytes (s : String) : ofBytes (strBytes s) = some s := by
  have hv : s.toByteArray.IsValidUTF8 := s.isValidUTF8
  simp only [ofBytes, strBytes, Array.toArray_toList, String.toUTF8_eq_toByteArray,
    String.fromUTF8?, hv, dite_true]
  rfl

/-- A string table: a NUL byte, then each name followed by a NUL byte. -/
def strtab (names : List (List UInt8)) : List UInt8 := 0 :: names.flatMap (· ++ [0])

/-- The offsets of the names in a table whose part after the first NUL starts at `cur`. -/
def strOffs : Nat → List (List UInt8) → List Nat
  | _, [] => []
  | cur, n :: ns => cur :: strOffs (cur + n.length + 1) ns

@[simp] theorem strOffs_length : ∀ (cur : Nat) (ns : List (List UInt8)),
    (strOffs cur ns).length = ns.length
  | _, [] => rfl
  | cur, _ :: ns => by simp [strOffs, strOffs_length _ ns]

/-- The name at offset `off` of a string table, which runs up to the next NUL byte. A name that
is not terminated inside the table is `none`, as the gABI requires every name to end inside it. -/
def cstr (tbl : List UInt8) (off : Nat) : Option (List UInt8) :=
  let r := tbl.drop off
  if (0 : UInt8) ∈ r then some (r.takeWhile (· != 0)) else none

/-- The string at offset `off` of a string table. -/
def strAt (tbl : List UInt8) (off : Nat) : Option String := (cstr tbl off).bind ofBytes

theorem cstr_name (pre b rest : List UInt8) (hb : (0 : UInt8) ∉ b) :
    cstr (pre ++ (b ++ 0 :: rest)) pre.length = some b := by
  have h1 : (b ++ 0 :: rest).takeWhile (· != 0) = b := by
    induction b with
    | nil => simp
    | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hb
      simp [Ne.symm hb.1, ih hb.2]
  simp [cstr, List.drop_left', h1]

/-- Every name of a string table is found at its offset. -/
theorem cstr_strtab : ∀ (ns : List (List UInt8)) (pre post : List UInt8),
    (∀ n ∈ ns, (0 : UInt8) ∉ n) → ∀ i (hi : i < ns.length),
    cstr (pre ++ ns.flatMap (· ++ [0]) ++ post) ((strOffs pre.length ns)[i]'(by simpa)) = some ns[i]
  | [], _, _, _, _, hi => by simp at hi
  | n :: ns, pre, post, h0, i, hi => by
    cases i with
    | zero =>
      simp only [List.flatMap_cons, strOffs, List.getElem_cons_zero, List.append_assoc]
      exact cstr_name pre n _ (h0 n (by simp))
    | succ i =>
      have := cstr_strtab ns (pre ++ (n ++ [0])) post (fun m hm => h0 m (by simp [hm])) i
        (by simpa using hi)
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      simpa [strOffs, List.flatMap_cons, List.append_assoc, Nat.add_assoc] using this

/-! ### Machines -/

/-- What the format needs to know of a machine: its `e_machine` and its relocation types. A
`RelocKind` is written with the type `relType` gives, and a relocation type is read as the kind
`relKind` gives. `relKind` is written from the processor supplement: it also accepts types the
writer never emits, such as `R_X86_64_PLT32`, whose effect in a static link is that of a kind. -/
structure Mach where
  em : Nat
  relType : RelocKind → Option Nat
  relKind : Nat → Option RelocKind

/-- x86-64. `pc32` is `R_X86_64_PC32` and `abs64` is `R_X86_64_64`. `R_X86_64_PLT32` is read as
`pc32`, because it resolves to `S + A - P` when the symbol is defined in the link, as it always is
in a static link. The psABI calls for `PLT32` on calls; the writer uses `PC32` for every `pc32`
field, which a static link resolves alike. -/
def x64 : Mach where
  em := EM_X86_64
  relType
    | .pc32 => some R_X86_64_PC32
    | .abs64 => some R_X86_64_64
    | .word _ => none
  relKind t :=
    if t = R_X86_64_PC32 ∨ t = R_X86_64_PLT32 then some .pc32
    else if t = R_X86_64_64 then some .abs64
    else none

/-- The AArch64 relocation type of a fixup. -/
def a64FixType : Fixup → Option Nat
  | .branch26 => some R_AARCH64_CALL26
  | .cond19 => some R_AARCH64_CONDBR19
  | .adr21 => some R_AARCH64_ADR_PREL_LO21
  | .page21 => some R_AARCH64_ADR_PREL_PG_HI21
  | .lo12 0 => some R_AARCH64_ADD_ABS_LO12_NC
  | .lo12 1 => some R_AARCH64_LDST16_ABS_LO12_NC
  | .lo12 2 => some R_AARCH64_LDST32_ABS_LO12_NC
  | .lo12 3 => some R_AARCH64_LDST64_ABS_LO12_NC
  | .lo12 4 => some R_AARCH64_LDST128_ABS_LO12_NC
  | .lo12 _ => none

/-- The relocation kind of an AArch64 relocation type, from the table of ARM IHI 0056. `JUMP26`
and `CALL26` compute the same field, as do `LD_PREL_LO19` and `CONDBR19`, and `LDST8_ABS_LO12_NC`
and `ADD_ABS_LO12_NC`. `PREL32` is read as `pc32`, whose range check, signed 32 bits, is stricter
than the psABI's. -/
def a64Kind (t : Nat) : Option RelocKind :=
  if t = R_AARCH64_ABS64 then some .abs64
  else if t = R_AARCH64_PREL32 then some .pc32
  else if t = R_AARCH64_CALL26 ∨ t = R_AARCH64_JUMP26 then some (.word .branch26)
  else if t = R_AARCH64_CONDBR19 ∨ t = R_AARCH64_LD_PREL_LO19 then some (.word .cond19)
  else if t = R_AARCH64_ADR_PREL_LO21 then some (.word .adr21)
  else if t = R_AARCH64_ADR_PREL_PG_HI21 then some (.word .page21)
  else if t = R_AARCH64_ADD_ABS_LO12_NC ∨ t = R_AARCH64_LDST8_ABS_LO12_NC then some (.word (.lo12 0))
  else if t = R_AARCH64_LDST16_ABS_LO12_NC then some (.word (.lo12 1))
  else if t = R_AARCH64_LDST32_ABS_LO12_NC then some (.word (.lo12 2))
  else if t = R_AARCH64_LDST64_ABS_LO12_NC then some (.word (.lo12 3))
  else if t = R_AARCH64_LDST128_ABS_LO12_NC then some (.word (.lo12 4))
  else none

/-- AArch64. -/
def a64 : Mach where
  em := EM_AARCH64
  relType
    | .pc32 => some R_AARCH64_PREL32
    | .abs64 => some R_AARCH64_ABS64
    | .word f => a64FixType f
  relKind := a64Kind

/-- A machine reads back the kind of every type it writes, and its types fit the 32 bits that
`r_info` gives them. -/
def Mach.Lawful (m : Mach) : Prop :=
  ∀ k t, m.relType k = some t → m.relKind t = some k ∧ t < 2 ^ 32

theorem x64_lawful : x64.Lawful := by
  intro k t h
  cases k <;> simp only [x64, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

theorem a64_lawful : a64.Lawful := by
  intro k t h
  cases k with
  | pc32 => cases h; decide
  | abs64 => cases h; decide
  | word f =>
    cases f with
    | lo12 s =>
      match s, h with
      | 0, h | 1, h | 2, h | 3, h | 4, h => cases h; decide
    | _ => cases h; decide

end Millipede.ElfRel
