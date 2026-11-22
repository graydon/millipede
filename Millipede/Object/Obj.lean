import Millipede.Target.Machine

/-!
# Relocatable objects

An `Obj` is the output of the assembler, independent of the file format. It holds sections of
bytes, symbols defined at section offsets, and relocations that the linker patches. All code is
position-independent, since code refers to code and data with pc-relative relocations, which the
linker resolves once addresses are assigned, so a linked image needs no relocation at load time.
On x64 these are `pc32` relocations, and on arm64 they are `word` fixups of the branch, `adrp` and
`lo12` fields of instruction words.

A section has a kind, which fixes its permissions, an alignment, its bytes, and a number of zero
bytes appended after them for `bss`. A symbol names an offset in a section, and a relocation names
the field to patch, its kind, the symbol and an addend. `RelocKind.patch` computes the new bytes of
a field from the old ones, and `patchBytes` overwrites bytes in place for the linker.
-/

namespace Millipede

/-- What a section holds, which determines its permissions in the image. -/
inductive SecKind where
  | text
  | rodata
  | data
  | bss
deriving DecidableEq, Repr, Inhabited

/-- The permissions that a section's bytes get when loaded. Code is never writable. -/
def SecKind.perm : SecKind → Perm
  | .text => Perm.rx
  | .rodata => Perm.r_
  | .data => Perm.rw
  | .bss => Perm.rw

/-- A section, which holds initialised bytes followed by `bssSize` zero bytes. -/
structure Section where
  name : String
  kind : SecKind
  /-- the required alignment of the section's address, in bytes -/
  align : Nat := 1
  bytes : List UInt8
  bssSize : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- The size of a section in memory. -/
def Section.size (s : Section) : Nat := s.bytes.length + s.bssSize

/-- A symbol defined at an offset in a section. -/
structure Symbol where
  name : String
  /-- the index of the section in `Obj.sections` -/
  sec : Nat
  offset : Nat
  global : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- The fixups of a field inside a 32-bit little-endian arm64 instruction word, where `T` is the
target `S + A` and `P` the address of the instruction word. The field values and bit positions are
those of the AArch64 ELF relocations named below, from ARM IHI 0056. The fixups are the following:
* `branch26`, for `B` and `BL`, puts `imm26 = (T - P) / 4` at bits `[0, 26)`, where `T - P` must be
  a multiple of 4 within ±128 MiB, as `R_AARCH64_JUMP26` and `R_AARCH64_CALL26` do.
* `cond19`, for `B.cond`, `CBZ`, `CBNZ` and literal `LDR`, puts `imm19 = (T - P) / 4` at bits
  `[5, 24)`, a multiple of 4 within ±1 MiB, as `R_AARCH64_CONDBR19` and `R_AARCH64_LD_PREL_LO19`
  do.
* `adr21`, for `ADR`, takes `imm21 = T - P` within ±1 MiB and puts its low 2 bits, `immlo`, at bits
  `[29, 31)` and the rest, `immhi`, at bits `[5, 24)`, as `R_AARCH64_ADR_PREL_LO21` does.
* `page21`, for `ADRP`, takes `imm21 = Page(T) - Page(P)` in 4 KiB pages, within ±4 GiB, with the
  bit positions of `adr21`, as `R_AARCH64_ADR_PREL_PG_HI21` does. `Page(x)` is `x` with the low 12
  bits cleared, whatever the OS page size.
* `lo12 s`, for `ADD` with an immediate when `s = 0` and for `LDR` and `STR` with an unsigned offset
  and access size `2^s`, puts `imm12 = (T mod 4096) / 2^s` at bits `[10, 22)`, where `T mod 4096`
  must be a multiple of `2^s`, as `R_AARCH64_ADD_ABS_LO12_NC` and
  `R_AARCH64_LDST{8,16,32,64,128}_ABS_LO12_NC` do. Together with `page21` it materialises an
  address as `adrp x, T; add x, x, :lo12:T`. -/
inductive Fixup where
  | branch26
  | cond19
  | adr21
  | page21
  | lo12 (scale : Nat)
deriving DecidableEq, Repr, Inhabited

/-- `w` with the bits `[lo, lo + n)` replaced by the low `n` bits of `v`, computed on `Nat`. -/
def setBits (w lo n v : Nat) : Nat := w - w / 2 ^ lo % 2 ^ n * 2 ^ lo + v % 2 ^ n * 2 ^ lo

/-- A pc-relative distance in words, `d / 4` as an `n`-bit field, when `d` is a multiple of 4 and
`d / 4` fits in `n` signed bits. -/
def wordsField (n : Nat) (d : Int) : Option Nat :=
  if d % 4 = 0 ∧ -2 ^ (n + 1) ≤ d ∧ d < 2 ^ (n + 1) then some ((d / 4) % 2 ^ n).toNat else none

/-- A signed value as a 21-bit field, if it fits. -/
def field21 (d : Int) : Option Nat :=
  if -2 ^ 20 ≤ d ∧ d < 2 ^ 20 then some (d % 2 ^ 21).toNat else none

/-- The field value of fixup `k` for target `T` and instruction address `P`. It is `none` when the
target is out of reach or misaligned, and the linker and the assembler then refuse. -/
def Fixup.value : Fixup → UInt64 → UInt64 → Option Nat
  | .branch26, T, P => wordsField 26 ((T.toNat : Int) - P.toNat)
  | .cond19, T, P => wordsField 19 ((T.toNat : Int) - P.toNat)
  | .adr21, T, P => field21 ((T.toNat : Int) - P.toNat)
  | .page21, T, P => field21 (((T.toNat / 4096 : Nat) : Int) - (P.toNat / 4096 : Nat))
  | .lo12 s, T, _ => if T.toNat % 4096 % 2 ^ s = 0 then some (T.toNat % 4096 / 2 ^ s) else none

/-- Inserts the field value `v` of fixup `k` into the instruction word `w`. -/
def Fixup.insert : Fixup → Nat → Nat → Nat
  | .branch26, w, v => setBits w 0 26 v
  | .cond19, w, v => setBits w 5 19 v
  | .adr21, w, v => setBits (setBits w 29 2 v) 5 19 (v / 4)
  | .page21, w, v => setBits (setBits w 29 2 v) 5 19 (v / 4)
  | .lo12 _, w, v => setBits w 10 12 v

/-- Applies fixup `k` for target `T` to the instruction word `w` at `P`. -/
def Fixup.apply (k : Fixup) (T P : UInt64) (w : Nat) : Option Nat :=
  (k.value T P).map (k.insert w)

/-- The relocation kinds, where `S` is the symbol's address, `A` the addend and `P` the address of
the field being patched. -/
inductive RelocKind where
  /-- a 32-bit signed little-endian `S + A - P`, as x64's `R_X86_64_PC32` -/
  | pc32
  /-- a 64-bit little-endian `S + A` -/
  | abs64
  /-- an arm64 fixup of a field inside the 32-bit little-endian instruction word at `P`, with the
  target `S + A` -/
  | word (k : Fixup)
deriving DecidableEq, Repr, Inhabited

/-- The width of the patched field in bytes. -/
def RelocKind.width : RelocKind → Nat
  | .pc32 => 4
  | .abs64 => 8
  | .word _ => 4

/-- The bytes to write into the field, given the bytes `old` that it holds, or `none` when the
value does not fit and the linker refuses. Only `word` fixups read `old`, to keep the
instruction's other bits. -/
def RelocKind.patch (k : RelocKind) (S P : UInt64) (A : Int) (old : List UInt8) :
    Option (List UInt8) :=
  match k with
  | .pc32 =>
    let v : Int := (S.toNat : Int) + A - (P.toNat : Int)
    if -2147483648 ≤ v ∧ v < 2147483648 then some (natBytes 4 (UInt64.ofInt v).toNat) else none
  | .abs64 => some (natBytes 8 (UInt64.ofInt ((S.toNat : Int) + A)).toNat)
  | .word f => (f.apply (UInt64.ofInt ((S.toNat : Int) + A)) P (natOfBytes old)).map (natBytes 4)

/-- A relocation, which patches the field at `offset` in section `sec` with `kind` applied to the
address of `sym` plus `addend`. -/
structure Reloc where
  sec : Nat
  offset : Nat
  kind : RelocKind
  sym : String
  addend : Int := 0
deriving DecidableEq, Repr, Inhabited

/-- A relocatable object. -/
structure Obj where
  sections : List Section
  symbols : List Symbol
  relocs : List Reloc
deriving Repr, Inhabited

/-- Overwrites `bs` at `off` with `new`, dropping bytes past the end of `bs`. -/
def patchBytes : List UInt8 → Nat → List UInt8 → List UInt8
  | [], _, _ => []
  | bs, _, [] => bs
  | _ :: bs, 0, n :: ns => n :: patchBytes bs 0 ns
  | b :: bs, off + 1, ns => b :: patchBytes bs off ns

/-- Applies the relocations of section `sec`, placed at `base` with the symbols at `σ`, to its
bytes, and returns `none` when a symbol is unknown or a value is out of reach. The proofs of the
linker and of the assembler share it. -/
def applyRelocs (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    List Reloc → List UInt8 → Option (List UInt8)
  | [], bs => some bs
  | r :: rs, bs =>
    if r.sec = sec then
      match σ r.sym with
      | none => none
      | some S =>
        match r.kind.patch S (base + UInt64.ofNat r.offset) r.addend
            ((bs.drop r.offset).take r.kind.width) with
        | none => none
        | some v => applyRelocs σ base sec rs (patchBytes bs r.offset v)
    else applyRelocs σ base sec rs bs

theorem patchBytes_length : ∀ (bs : List UInt8) (off : Nat) (ns : List UInt8),
    (patchBytes bs off ns).length = bs.length
  | [], _, _ => by simp [patchBytes]
  | _ :: _, _, [] => by simp [patchBytes]
  | _ :: bs, 0, _ :: ns => by simp [patchBytes, patchBytes_length bs 0 ns]
  | _ :: bs, off + 1, ns => by
    cases ns with
    | nil => simp [patchBytes]
    | cons _ _ => simp [patchBytes, patchBytes_length bs off]

/-- Patching a field at the start of a byte list. -/
theorem patchBytes_same : ∀ (old ys new : List UInt8), old.length = new.length →
    patchBytes (old ++ ys) 0 new = new ++ ys
  | [], ys, [], _ => by cases ys <;> rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | _ :: old, ys, n :: new, h => by
    simp only [List.cons_append, patchBytes]
    rw [patchBytes_same old ys new (by simpa using h)]

/-- Patching a field in the middle of a byte list. -/
theorem patchBytes_mid : ∀ (xs old ys new : List UInt8), old.length = new.length →
    patchBytes (xs ++ old ++ ys) xs.length new = xs ++ new ++ ys
  | [], old, ys, new, h => by simpa using patchBytes_same old ys new h
  | x :: xs, old, ys, new, h => by
    cases new with
    | nil =>
      have : old = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst this; simp [patchBytes]
    | cons n new =>
      simp only [List.cons_append, List.length_cons, patchBytes]
      rw [patchBytes_mid xs old ys (n :: new) h]

/-- Patching inside a list replaces the bytes at the offset and keeps the rest. -/
theorem patchBytes_eq (bs ns : List UInt8) (off : Nat) (h : off + ns.length ≤ bs.length) :
    patchBytes bs off ns = bs.take off ++ ns ++ bs.drop (off + ns.length) := by
  have e : bs = bs.take off ++ (bs.drop off).take ns.length ++ bs.drop (off + ns.length) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hl : (bs.take off).length = off := by simp; omega
  have := patchBytes_mid (bs.take off) ((bs.drop off).take ns.length) (bs.drop (off + ns.length))
    ns (by simp; omega)
  rw [hl, ← e] at this
  exact this

theorem applyRelocs_length (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    ∀ (rs : List Reloc) (bs X : List UInt8), applyRelocs σ base sec rs bs = some X →
      X.length = bs.length
  | [], bs, X, h => by cases h; rfl
  | r :: rs, bs, X, h => by
    simp only [applyRelocs] at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rw [applyRelocs_length σ base sec rs _ X h, patchBytes_length]
    · exact applyRelocs_length σ base sec rs bs X h

end Millipede
