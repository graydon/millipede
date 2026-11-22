import Millipede.Core.Shape
import Millipede.Core.LE

/-!
# Object types

An object type `Ty` bundles a Lean type, its carrier, with a `Data` instance. The value semantics
computes with carriers, and the universe of object types is open, so any Lean type with a `Data`
instance is one.

`Data α` records the memory layout of `α` as a closed `Shape` and a relation `repr` that says which
memory contents represent a value. `repr` is a relation because padding bytes and the bytes of
empty `Slots` cells may hold anything. `encode` computes one representation, with all padding
zero, and `linear` says whether values must be used exactly once. The memory lowering needs two
further properties to read a value back from its bytes, which are the classes
`Data.Determinate`, when the bytes determine the value, and `Data.Canonical`, when `encode`
gives the only representation.

This file defines the class, `Ty`, and the instances for `UInt64`, `Bool`, `Unit`, `Except` and the
other scalars, which are encoded little-endian by `natBytes`. The instances of composite types
are in `Millipede/Core/Data.lean`.
-/

namespace Millipede

/-- `n` zero bytes. -/
abbrev zeroBytes (n : Nat) : List UInt8 := List.replicate n 0

/-! ## The class -/

/-- What the compiler and the checkers need to know about a carrier type. -/
class Data (α : Type) where
  /-- the memory layout -/
  shape : Shape
  /-- whether a value is used exactly once, or freely copied -/
  linear : Bool
  /-- which memory contents represent a value, where padding and empty cells may hold anything -/
  repr : α → shape.Val → Prop
  /-- the representation with zero padding -/
  encode : α → shape.Val
  encode_repr : ∀ a, repr a (encode a)
  /-- For a `Slots` value, which cells are full, and `none` for every other type. No byte shows
  it, so it exists only in proofs. The memory refinement uses it to know that a slice view's full
  cells are exactly its first `len`, whatever the element type is called where it is used. -/
  occ : α → Option (List Bool) := fun _ => none
  /-- The occupancies of a value's components, which are `[occ a]` for a value that is not a
  pair, the components' lists concatenated for a pair, and none for `Unit`. Like `occ`, it exists
  only in proofs. A hand-back constructor's certificate says that the value it builds has its
  arguments' occupancies, so the full cells of a view it hands back are those of the view
  binder. -/
  occs : α → List (Option (List Bool)) := fun a => [occ a]
  /-- The number of components does not depend on the value. -/
  occs_len : ∀ a b : α, (occs a).length = (occs b).length := by intros; rfl
  /-- The number of components in `occs`, which is the same for every value. -/
  occsN : Nat := 1
  occsN_eq : ∀ a : α, (occs a).length = occsN := by intros; rfl
  /-- Where field `i`'s components start in `occs`, after those of the fields before it. A lens's
  certificate says that its field's occupancies are `occs` at this offset, so the compiler can
  decide that the occupancies of two fields are apart. -/
  occsOff : Nat → Nat := fun _ => 0

/-- `repr` on raw byte lists, which is false unless the length is the shape's size. -/
def Data.reprBytes {α : Type} [Data α] (a : α) (bs : List UInt8) : Prop :=
  ∃ h : bs.length = (Data.shape α).size, Data.repr a ⟨bs, h⟩

/-- `encode` as a raw byte list. -/
abbrev Data.encodeBytes {α : Type} [Data α] (a : α) : List UInt8 := (Data.encode a).val

@[simp] theorem Data.encodeBytes_length {α : Type} [Data α] (a : α) :
    (Data.encodeBytes a).length = (Data.shape α).size := (Data.encode a).property

theorem Data.reprBytes_encode {α : Type} [Data α] (a : α) :
    Data.reprBytes a (Data.encodeBytes a) := ⟨(Data.encode a).property, Data.encode_repr a⟩

theorem Data.reprBytes_length {α : Type} [Data α] {a : α} {bs : List UInt8}
    (h : Data.reprBytes a bs) : bs.length = (Data.shape α).size := h.1

/-- The bytes determine the value. This holds for scalars and for arrays, structs and sums of
determinate types, and fails for `Slots`, which have no tags, and for ghosts. -/
class Data.Determinate (α : Type) [Data α] : Prop where
  inj : ∀ (a b : α) (v : (Data.shape α).Val), Data.repr a v → Data.repr b v → a = b

/-- The only representation of a value is `encode`, so nothing depends on padding. -/
class Data.Canonical (α : Type) [Data α] : Prop where
  canon : ∀ (a : α) (v : (Data.shape α).Val), Data.repr a v → v = Data.encode a

theorem Data.reprBytes_inj {α : Type} [Data α] [Data.Determinate α] {a b : α}
    {bs : List UInt8} (ha : Data.reprBytes a bs) (hb : Data.reprBytes b bs) : a = b := by
  obtain ⟨h, ha⟩ := ha; obtain ⟨_, hb⟩ := hb
  exact Data.Determinate.inj a b ⟨bs, h⟩ ha hb

theorem Data.reprBytes_canon {α : Type} [Data α] [Data.Canonical α] {a : α}
    {bs : List UInt8} (ha : Data.reprBytes a bs) : bs = Data.encodeBytes a := by
  obtain ⟨h, ha⟩ := ha
  exact congrArg Subtype.val (Data.Canonical.canon a ⟨bs, h⟩ ha)

/-- An object type, which is a Lean carrier with a `Data` instance. -/
structure Ty where
  carrier : Type
  [data : Data carrier]

attribute [instance] Ty.data

/-- Whether values of this type are linear, which means each must be used exactly once. -/
abbrev Ty.linear (t : Ty) : Bool := t.data.linear

/-- The size in bytes of a type. -/
abbrev Ty.size (t : Ty) : Nat := t.data.shape.size

/-- The alignment in bytes of a type. -/
abbrev Ty.align (t : Ty) : Nat := t.data.shape.align

/-! ## Scalars -/

/-- A scalar of width `w`, stored as the low `w.bytes` little-endian bytes of `toNat a`. -/
abbrev Data.scalar {α : Type} (w : Width) (toNat : α → Nat) : Data α where
  shape := .word w
  linear := false
  repr a v := v.val = natBytes w.bytes (toNat a)
  encode a := ⟨natBytes w.bytes (toNat a), natBytes_length _ _⟩
  encode_repr _ := rfl

/-- Scalars are canonical. -/
theorem Data.scalar_canonical {α : Type} (w : Width) (toNat : α → Nat) :
    @Data.Canonical α (Data.scalar w toNat) :=
  @Data.Canonical.mk α (Data.scalar w toNat) fun _ _ h => Subtype.ext h

/-- Scalars whose `toNat` is injective and below `256 ^ w.bytes` are determinate. -/
theorem Data.scalar_determinate {α : Type} (w : Width) (toNat : α → Nat)
    (hlt : ∀ a, toNat a < 256 ^ w.bytes) (hinj : ∀ a b, toNat a = toNat b → a = b) :
    @Data.Determinate α (Data.scalar w toNat) :=
  @Data.Determinate.mk α (Data.scalar w toNat) fun a b _ ha hb =>
    hinj a b (natBytes_inj (hlt a) (hlt b) (ha.symm.trans hb))

instance : Data UInt64 where
  shape := .word .w64
  linear := false
  repr x v := v.val = natBytes 8 x.toNat
  encode x := ⟨natBytes 8 x.toNat, natBytes_length _ _⟩
  encode_repr _ := rfl

instance : Data Bool where
  shape := .word .w8
  linear := false
  repr b v := v.val = natBytes 1 (if b then 1 else 0)
  encode b := ⟨natBytes 1 (if b then 1 else 0), natBytes_length _ _⟩
  encode_repr _ := rfl

instance : Data Unit where
  shape := .prod []
  linear := false
  repr _ _ := True
  encode _ := ⟨[], rfl⟩
  encode_repr _ := trivial
  occs _ := []
  occsN := 0

instance : Data UInt8 := Data.scalar .w8 UInt8.toNat
instance : Data UInt16 := Data.scalar .w16 UInt16.toNat
instance : Data UInt32 := Data.scalar .w32 UInt32.toNat
instance : Data Int8 := Data.scalar .w8 (fun x => x.toBitVec.toNat)
instance : Data Int16 := Data.scalar .w16 (fun x => x.toBitVec.toNat)
instance : Data Int32 := Data.scalar .w32 (fun x => x.toBitVec.toNat)
instance : Data Int64 := Data.scalar .w64 (fun x => x.toBitVec.toNat)

/-- `Fin n` is an index whose bound `n` is a ghost argument, and at run time it is a 64-bit word.
Indices of `2^64` or more are truncated, so `Fin.determinate` needs `n ≤ 2^64`. -/
instance (n : Nat) : Data (Fin n) := Data.scalar .w64 Fin.val

instance : Data.Determinate UInt64 :=
  ⟨fun a b _ ha hb => UInt64.toNat_inj.mp
    (natBytes_inj (UInt64.toNat_lt a) (UInt64.toNat_lt b) (ha.symm.trans hb))⟩
instance : Data.Canonical UInt64 := ⟨fun _ _ h => Subtype.ext h⟩
instance : Data.Determinate Bool :=
  ⟨fun a b _ ha hb => by
    have := ha.symm.trans hb
    cases a <;> cases b <;> simp_all [natBytes]⟩
instance : Data.Canonical Bool := ⟨fun _ _ h => Subtype.ext h⟩
instance : Data.Determinate Unit := ⟨fun _ _ _ _ _ => rfl⟩
instance : Data.Canonical Unit := ⟨fun _ v _ => Subtype.ext (List.eq_nil_of_length_eq_zero v.2)⟩

instance : Data.Determinate UInt8 :=
  Data.scalar_determinate _ _ UInt8.toNat_lt fun _ _ h => UInt8.toNat_inj.mp h
instance : Data.Determinate UInt16 :=
  Data.scalar_determinate _ _ UInt16.toNat_lt fun _ _ h => UInt16.toNat_inj.mp h
instance : Data.Determinate UInt32 :=
  Data.scalar_determinate _ _ UInt32.toNat_lt fun _ _ h => UInt32.toNat_inj.mp h
instance : Data.Determinate Int8 :=
  Data.scalar_determinate _ _ (fun x => x.toBitVec.isLt)
    fun _ _ h => Int8.toBitVec_inj.mp (BitVec.toNat_inj.mp h)
instance : Data.Determinate Int16 :=
  Data.scalar_determinate _ _ (fun x => x.toBitVec.isLt)
    fun _ _ h => Int16.toBitVec_inj.mp (BitVec.toNat_inj.mp h)
instance : Data.Determinate Int32 :=
  Data.scalar_determinate _ _ (fun x => x.toBitVec.isLt)
    fun _ _ h => Int32.toBitVec_inj.mp (BitVec.toNat_inj.mp h)
instance : Data.Determinate Int64 :=
  Data.scalar_determinate _ _ (fun x => x.toBitVec.isLt)
    fun _ _ h => Int64.toBitVec_inj.mp (BitVec.toNat_inj.mp h)
instance : Data.Canonical UInt8 := Data.scalar_canonical _ _
instance : Data.Canonical UInt16 := Data.scalar_canonical _ _
instance : Data.Canonical UInt32 := Data.scalar_canonical _ _
instance : Data.Canonical Int8 := Data.scalar_canonical _ _
instance : Data.Canonical Int16 := Data.scalar_canonical _ _
instance : Data.Canonical Int32 := Data.scalar_canonical _ _
instance : Data.Canonical Int64 := Data.scalar_canonical _ _
instance (n : Nat) : Data.Canonical (Fin n) := Data.scalar_canonical _ _

/-! ## Sums: shared byte layout -/

/-- The bytes of variant `i` of `sum vs` with payload `p`, which are the tag, zero padding, the
payload, and zero padding up to the size. -/
def sumBytes (vs : List Shape) (i : Nat) (p : List UInt8) : List UInt8 :=
  natBytes (Shape.tagBytes vs) i ++ zeroBytes (Shape.payloadOffset vs - Shape.tagBytes vs) ++ p ++
    zeroBytes ((Shape.sum vs).size - Shape.payloadOffset vs - p.length)

/-- `bs` holds variant `i` of `sum vs`, with tag `i`, and its payload bytes satisfy `P`. -/
def sumRepr (vs : List Shape) (i : Nat) (len : Nat) (P : List UInt8 → Prop)
    (bs : List UInt8) : Prop :=
  slice bs 0 (Shape.tagBytes vs) = natBytes (Shape.tagBytes vs) i ∧
    P (slice bs (Shape.payloadOffset vs) len)

theorem sumBytes_length (vs : List Shape) (i : Nat) (p : List UInt8) (v : Shape) (hv : v ∈ vs)
    (hp : p.length = v.size) : (sumBytes vs i p).length = (Shape.sum vs).size := by
  have h1 := Shape.tagBytes_le_payloadOffset vs
  have h2 := Shape.payload_add_size_le vs v hv
  simp [sumBytes]; omega

theorem sumRepr_sumBytes (vs : List Shape) (i : Nat) (p : List UInt8) (P : List UInt8 → Prop)
    (hP : P p) : sumRepr vs i p.length P (sumBytes vs i p) := by
  have h1 := Shape.tagBytes_le_payloadOffset vs
  constructor
  · simp [sumBytes, slice]
  · show P (slice (sumBytes vs i p) _ _)
    unfold sumBytes
    rw [slice_append_mid' (by simp; omega) rfl]; exact hP

/-- The tags of a sum with at most `2^64` variants are determined by their bytes. -/
theorem sumRepr_tag_inj {vs : List Shape} {i j li lj : Nat} {P Q : List UInt8 → Prop}
    {bs : List UInt8} (hi : i < vs.length) (hj : j < vs.length) (hn : vs.length ≤ 2 ^ 64)
    (h₁ : sumRepr vs i li P bs) (h₂ : sumRepr vs j lj Q bs) : i = j := by
  have hb : ∀ k, k < vs.length → k < 256 ^ Shape.tagBytes vs := fun k hk => by
    have := tagWidth_fits vs.length k hk hn
    simp only [Width.bits] at this
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; exact this
  exact natBytes_inj (hb i hi) (hb j hj) (h₁.1.symm.trans h₂.1)

/-- The memory representation of `Except ε α` as `sum [ε, α]`, with tag 0 for an error and 1 for
a success. -/
def exceptRepr {ε α : Type} [Data ε] [Data α] : Except ε α → List UInt8 → Prop
  | .error e, bs => sumRepr [Data.shape ε, Data.shape α] 0 (Data.shape ε).size
      (Data.reprBytes e) bs
  | .ok a, bs => sumRepr [Data.shape ε, Data.shape α] 1 (Data.shape α).size
      (Data.reprBytes a) bs

/-- The zero-padded bytes of `Except ε α`. -/
def exceptBytes {ε α : Type} [Data ε] [Data α] : Except ε α → List UInt8
  | .error e => sumBytes [Data.shape ε, Data.shape α] 0 (Data.encodeBytes e)
  | .ok a => sumBytes [Data.shape ε, Data.shape α] 1 (Data.encodeBytes a)

theorem exceptBytes_length {ε α : Type} [Data ε] [Data α] (r : Except ε α) :
    (exceptBytes r).length = (Shape.sum [Data.shape ε, Data.shape α]).size := by
  cases r
  · exact sumBytes_length _ _ _ (Data.shape ε) (by simp) (by simp)
  · exact sumBytes_length _ _ _ (Data.shape α) (by simp) (by simp)

theorem exceptRepr_bytes {ε α : Type} [Data ε] [Data α] (r : Except ε α) :
    exceptRepr r (exceptBytes r) := by
  cases r with
  | error e =>
    have := sumRepr_sumBytes [Data.shape ε, Data.shape α] 0 _ _ (Data.reprBytes_encode e)
    simpa [exceptRepr, exceptBytes] using this
  | ok a =>
    have := sumRepr_sumBytes [Data.shape ε, Data.shape α] 1 _ _ (Data.reprBytes_encode a)
    simpa [exceptRepr, exceptBytes] using this

/-- `Result ε α` is `Except ε α`, a linear type with the layout `sum [ε, α]`, where tag 0 is an
error and 1 a success. -/
instance instDataExcept {ε α : Type} [Data ε] [Data α] : Data (Except ε α) where
  shape := .sum [Data.shape ε, Data.shape α]
  linear := true
  repr r v := exceptRepr r v.val
  encode r := ⟨exceptBytes r, exceptBytes_length r⟩
  encode_repr r := exceptRepr_bytes r

instance {ε α : Type} [Data ε] [Data α] [Data.Determinate ε] [Data.Determinate α] :
    Data.Determinate (Except ε α) where
  inj a b v ha hb := by
    change exceptRepr a v.val at ha; change exceptRepr b v.val at hb
    cases a <;> cases b <;> simp only [exceptRepr] at ha hb
    · exact congrArg _ (Data.reprBytes_inj ha.2 hb.2)
    · exact absurd (sumRepr_tag_inj (by simp) (by simp) (by simp) ha hb) (by decide)
    · exact absurd (sumRepr_tag_inj (by simp) (by simp) (by simp) ha hb) (by decide)
    · exact congrArg _ (Data.reprBytes_inj ha.2 hb.2)

/-- Unsigned 64-bit words. -/
abbrev Ty.u64 : Ty := ⟨UInt64⟩
/-- `Bool`, one byte holding 0 or 1, which takes one register word. -/
abbrev Ty.bool : Ty := ⟨Bool⟩
/-- `Unit`, which has no bytes. -/
abbrev Ty.unit : Ty := ⟨Unit⟩
/-- The linear `Result ε α`. -/
abbrev Ty.result (ε α : Ty) : Ty := ⟨Except ε.carrier α.carrier⟩
abbrev Ty.u8 : Ty := ⟨UInt8⟩

end Millipede
