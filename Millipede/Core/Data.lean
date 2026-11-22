import Millipede.Core.Ty

/-!
# Composite `Data` instances

This file builds the `Data` instances of composite types from the instances of their parts.
`Data.struct fs` builds the instance of a struct from a list of fields, each a type with its
`Data` and a projection. The fields are laid out as in C, a value is represented when each
field's bytes at its offset represent the field, and `encode` fills the padding with zeros. It is
what `deriving Data` produces for a `structure`, and a pair `α × β` is the struct of its two
components.

`Data.sum vs cover` builds the instance of a sum from a list of variants, each a payload type with
its `Data` and a partial projection. A value's variant is the first one whose projection succeeds,
and `cover` says that one always does. The bytes are the tag, which is the variant's index,
followed by the payload at the payload offset. It is what `deriving Data` produces for an
`inductive`, and `Option T` is the sum of `none` and `some`.

An array `Arr T n` is a `Vector T n` with element `i` at `i * size T`. `Slots T n` is a distinct
type over `Vector (Option T) n` whose cells carry no tags, so an empty cell's bytes may be
anything and the bytes do not determine the value. `Ghost α`, for any Lean type, and `PLift p`,
for any proposition, take no bytes and are erased by the memory lowering. For each builder the
file proves that every value has a zero-padded representation, and that the bytes determine the
value under the evident hypotheses.
-/

namespace Millipede

/-! ## Byte-list lemmas for fixed-size chunks -/

theorem length_flatMap_const {T : Type} (g : T → List UInt8) (sz : Nat)
    (hg : ∀ x, (g x).length = sz) (l : List T) : (l.flatMap g).length = l.length * sz := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, hg, ih, Nat.succ_mul]; omega

/-- Chunk `i` of a concatenation of chunks of equal length. -/
theorem slice_flatMap {T : Type} (g : T → List UInt8) (sz : Nat) (hg : ∀ x, (g x).length = sz)
    (l : List T) (i : Nat) (hi : i < l.length) : slice (l.flatMap g) (i * sz) sz = g l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, List.getElem_cons_zero]
      simpa using slice_append_mid' (pre := []) (post := l.flatMap g) rfl (hg x)
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [← ih i (by simp at hi; omega), slice, slice, Nat.succ_mul, Nat.add_comm,
        ← List.drop_drop, List.drop_left' (hg x)]

/-- A byte list whose chunks are `g l[i]` is their concatenation. -/
theorem eq_flatMap_of_slices {T : Type} (g : T → List UInt8) (sz : Nat)
    (_hg : ∀ x, (g x).length = sz) (l : List T) (bs : List UInt8)
    (hlen : bs.length = l.length * sz)
    (h : ∀ i (hi : i < l.length), slice bs (i * sz) sz = g l[i]) : bs = l.flatMap g := by
  induction l generalizing bs with
  | nil => simpa using hlen
  | cons x l ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.zero_mul, List.getElem_cons_zero, slice, List.drop_zero] at h0
    rw [← List.take_append_drop sz bs, h0, List.flatMap_cons]
    congr 1
    refine ih _ (by simp [Nat.succ_mul] at hlen ⊢; omega) fun i hi => ?_
    have := h (i + 1) (by simp; omega)
    simp only [slice, List.getElem_cons_succ, Nat.succ_mul] at this ⊢
    rw [List.drop_drop, Nat.add_comm sz]; exact this

/-! ## Structs -/

/-- A field of a struct `S`, which is a type with `Data` and the projection to it. -/
structure Field (S : Type) where
  {T : Type}
  [inst : Data T]
  get : S → T

attribute [instance] Field.inst

/-- The field's shape. -/
abbrev Field.shape {S : Type} (f : Field S) : Shape := Data.shape f.T

namespace Fields
variable {S : Type}

/-- The occupancies of the fields, in order, which are the components of a struct. -/
def occs : List (Field S) → S → List (Option (List Bool))
  | [], _ => []
  | f :: fs, s => Data.occs (f.get s) ++ occs fs s

theorem occs_len : ∀ (fs : List (Field S)) (a b : S), (occs fs a).length = (occs fs b).length
  | [], _, _ => rfl
  | f :: fs, a, b => by
    simp only [occs, List.length_append, Data.occs_len (f.get a) (f.get b), occs_len fs a b]

/-- The number of components of the fields. -/
def occsN : List (Field S) → Nat
  | [] => 0
  | f :: fs => Data.occsN f.T + occsN fs

theorem occsN_eq : ∀ (fs : List (Field S)) (a : S), (occs fs a).length = occsN fs
  | [], _ => rfl
  | f :: fs, a => by
    simp only [occs, occsN, List.length_append, Data.occsN_eq (f.get a), occsN_eq fs a]

/-- Where field `i`'s components start in `occs`. -/
def occsOff (fs : List (Field S)) (i : Nat) : Nat := occsN (fs.take i)

/-- The shapes of the fields. -/
def shapes (fs : List (Field S)) : List Shape := fs.map Field.shape

/-- Each field, laid out from offset `off`, is represented in `bs` at its absolute offset. -/
def reprAt : Nat → List (Field S) → S → List UInt8 → Prop
  | _, [], _, _ => True
  | off, f :: fs, s, bs =>
    Data.reprBytes (f.get s) (slice bs (alignUp off f.shape.align) f.shape.size) ∧
      reprAt (alignUp off f.shape.align + f.shape.size) fs s bs

/-- The bytes of the fields laid out from offset `off`, with zero padding, starting at `off`. -/
def encodeFrom : Nat → List (Field S) → S → List UInt8
  | _, [], _ => []
  | off, f :: fs, s =>
    zeroBytes (alignUp off f.shape.align - off) ++ Data.encodeBytes (f.get s) ++
      encodeFrom (alignUp off f.shape.align + f.shape.size) fs s

/-- A struct is linear when any of its fields is. -/
def linear : List (Field S) → Bool
  | [] => false
  | f :: fs => Data.linear f.T || linear fs

@[simp] theorem shapes_nil : shapes ([] : List (Field S)) = [] := rfl
@[simp] theorem shapes_cons (f : Field S) (fs : List (Field S)) :
    shapes (f :: fs) = f.shape :: shapes fs := rfl

theorem encodeFrom_length (off : Nat) (fs : List (Field S)) (s : S) :
    (encodeFrom off fs s).length + off = Shape.prodEnd off (shapes fs) := by
  induction fs generalizing off with
  | nil => simp [encodeFrom, Shape.prodEnd]
  | cons f fs ih =>
    have := le_alignUp off f.shape.align f.shape.align_pos
    have := ih (alignUp off f.shape.align + f.shape.size)
    simp only [encodeFrom, List.length_append, List.length_replicate, Data.encodeBytes_length,
      shapes_cons, Shape.prodEnd, Field.shape] at *
    omega

theorem reprAt_encodeFrom (off : Nat) (fs : List (Field S)) (s : S) (pre suf : List UInt8)
    (h : pre.length = off) : reprAt off fs s (pre ++ encodeFrom off fs s ++ suf) := by
  induction fs generalizing off pre with
  | nil => trivial
  | cons f fs ih =>
    have hle := le_alignUp off f.shape.align f.shape.align_pos
    simp only [Field.shape] at hle
    simp only [reprAt, encodeFrom]
    constructor
    · rw [show pre ++ (zeroBytes (alignUp off f.shape.align - off) ++
          Data.encodeBytes (f.get s) ++ encodeFrom (alignUp off f.shape.align + f.shape.size)
          fs s) ++ suf = (pre ++ zeroBytes (alignUp off f.shape.align - off)) ++
          Data.encodeBytes (f.get s) ++
          (encodeFrom (alignUp off f.shape.align + f.shape.size) fs s ++ suf) by simp,
        slice_append_mid' (by simp [Field.shape]; omega) (Data.encodeBytes_length _)]
      exact Data.reprBytes_encode _
    · have := ih (alignUp off f.shape.align + f.shape.size)
        (pre ++ zeroBytes (alignUp off f.shape.align - off) ++ Data.encodeBytes (f.get s))
        (by simp [Field.shape]; omega)
      simpa using this

theorem reprAt_inj (off : Nat) (fs : List (Field S))
    (hdet : ∀ f ∈ fs, Data.Determinate f.T) (s t : S) (bs : List UInt8)
    (hs : reprAt off fs s bs) (ht : reprAt off fs t bs) : ∀ f ∈ fs, f.get s = f.get t := by
  induction fs generalizing off with
  | nil => intro f hf; cases hf
  | cons g fs ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · have := hdet f (List.mem_cons_self ..)
      exact Data.reprBytes_inj hs.1 ht.1
    · exact ih _ (fun f hf => hdet f (List.mem_cons_of_mem _ hf)) hs.2 ht.2 f hf

end Fields

/-- The struct builder, which `deriving Data` uses for a `structure`. It lays out the fields as in
C, the padding may hold anything, and `encode` fills it with zeros. -/
@[instance_reducible] def Data.struct {S : Type} (fs : List (Field S)) : Data S where
  shape := .prod (Fields.shapes fs)
  linear := Fields.linear fs
  repr s v := Fields.reprAt 0 fs s v.val
  encode s := ⟨Fields.encodeFrom 0 fs s ++ zeroBytes ((Shape.prod (Fields.shapes fs)).size -
      Shape.prodEnd 0 (Fields.shapes fs)), by
    have h1 := Fields.encodeFrom_length 0 fs s
    have h2 := le_alignUp (Shape.prodEnd 0 (Fields.shapes fs)) _
      (Shape.alignMax_pos (Fields.shapes fs))
    simp only [List.length_append, List.length_replicate, Shape.size] at *
    omega⟩
  encode_repr s := by
    have := Fields.reprAt_encodeFrom 0 fs s [] (zeroBytes ((Shape.prod (Fields.shapes fs)).size -
      Shape.prodEnd 0 (Fields.shapes fs))) rfl
    simpa using this
  occs s := Fields.occs fs s
  occs_len := Fields.occs_len fs
  occsN := Fields.occsN fs
  occsN_eq := Fields.occsN_eq fs
  occsOff := Fields.occsOff fs

/-- A struct is determinate when its fields are and the fields determine the value. -/
theorem Data.struct_determinate {S : Type} (fs : List (Field S))
    (hdet : ∀ f ∈ fs, Data.Determinate f.T)
    (ext : ∀ s t : S, (∀ f ∈ fs, f.get s = f.get t) → s = t) :
    @Data.Determinate S (Data.struct fs) :=
  @Data.Determinate.mk S (Data.struct fs) fun s t v hs ht =>
    ext s t (Fields.reprAt_inj 0 fs hdet s t v.val hs ht)

/-- Field `i` of a struct value `s` lies at `Shape.fieldOffset`, the offset the memory lowering
uses. -/
theorem Fields.reprAt_field {S : Type} (fs : List (Field S)) (s : S) (bs : List UInt8)
    (h : Fields.reprAt 0 fs s bs) (i : Nat) (hi : i < fs.length) :
    Data.reprBytes ((fs[i]).get s)
      (slice bs (Shape.fieldOffset (Fields.shapes fs) i) (fs[i]).shape.size) := by
  rw [Shape.fieldOffset_eq _ _ (by simpa [Fields.shapes] using hi)]
  suffices ∀ off (fs : List (Field S)), Fields.reprAt off fs s bs → ∀ i (hi : i < fs.length),
      Data.reprBytes ((fs[i]).get s)
        (slice bs ((Shape.prodOffsets off (Fields.shapes fs))[i]'(by simpa [Fields.shapes]))
          (fs[i]).shape.size) from this 0 fs h i hi
  intro off fs h
  induction fs generalizing off with
  | nil => intro i hi; simp at hi
  | cons f fs ih =>
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i =>
      simp only [Fields.shapes_cons, Shape.prodOffsets, List.getElem_cons_succ]
      exact ih _ h.2 i _

/-- Pairs are two-field structs. -/
instance {α β : Type} [Data α] [Data β] : Data (α × β) :=
  Data.struct [⟨Prod.fst⟩, ⟨Prod.snd⟩]

@[simp] theorem Data.occs_pair {α β : Type} [Data α] [Data β] (x : α) (y : β) :
    Data.occs (x, y) = Data.occs x ++ Data.occs y := by
  show Data.occs x ++ (Data.occs y ++ []) = _; rw [List.append_nil]

instance {α β : Type} [Data α] [Data β] [Data.Determinate α] [Data.Determinate β] :
    Data.Determinate (α × β) :=
  Data.struct_determinate _
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> assumption)
    (fun s t h => Prod.ext (h ⟨Prod.fst⟩ (by simp)) (h ⟨Prod.snd⟩ (by simp)))

/-! ## Sums -/

/-- A variant of a sum type `S`, which is a payload type with `Data` and the partial projection
to it. -/
structure Variant (S : Type) where
  {T : Type}
  [inst : Data T]
  proj : S → Option T

attribute [instance] Variant.inst

/-- The payload's shape. -/
abbrev Variant.shape {S : Type} (v : Variant S) : Shape := Data.shape v.T

namespace Variants
variable {S : Type}

/-- The shapes of the payloads. -/
def shapes (vs : List (Variant S)) : List Shape := vs.map Variant.shape

@[simp] theorem shapes_cons (v : Variant S) (vs : List (Variant S)) :
    shapes (v :: vs) = v.shape :: shapes vs := rfl
@[simp] theorem length_shapes (vs : List (Variant S)) : (shapes vs).length = vs.length := by
  simp [shapes]

/-- `bs` represents `s` in `sum sh`, where the first variant of `vs` has index `i`. -/
def reprAt (sh : List Shape) : Nat → List (Variant S) → S → List UInt8 → Prop
  | _, [], _, _ => False
  | i, v :: vs, s, bs =>
    match v.proj s with
    | some p => sumRepr sh i v.shape.size (Data.reprBytes p) bs
    | none => reprAt sh (i + 1) vs s bs

/-- The zero-padded bytes of a value, which are all zeros when no variant matches. -/
def encodeAt (sh : List Shape) : Nat → List (Variant S) → S → List UInt8
  | _, [], _ => zeroBytes (Shape.sum sh).size
  | i, v :: vs, s =>
    match v.proj s with
    | some p => sumBytes sh i (Data.encodeBytes p)
    | none => encodeAt sh (i + 1) vs s

/-- A sum is linear when any of its variants is. -/
def linear : List (Variant S) → Bool
  | [] => false
  | v :: vs => Data.linear v.T || linear vs

theorem encodeAt_length (sh : List Shape) (i : Nat) (vs : List (Variant S)) (s : S)
    (hsh : ∀ v ∈ vs, v.shape ∈ sh) : (encodeAt sh i vs s).length = (Shape.sum sh).size := by
  induction vs generalizing i with
  | nil => simp [encodeAt]
  | cons v vs ih =>
    simp only [encodeAt]
    split
    · exact sumBytes_length _ _ _ v.shape (hsh v (List.mem_cons_self ..))
        (Data.encodeBytes_length _)
    · exact ih _ fun w hw => hsh w (List.mem_cons_of_mem _ hw)

theorem reprAt_encodeAt (sh : List Shape) (i : Nat) (vs : List (Variant S)) (s : S)
    (hcov : ∃ v ∈ vs, (v.proj s).isSome) : reprAt sh i vs s (encodeAt sh i vs s) := by
  induction vs generalizing i with
  | nil => obtain ⟨v, hv, _⟩ := hcov; cases hv
  | cons v vs ih =>
    simp only [reprAt, encodeAt]
    split
    · next p _ =>
      have := sumRepr_sumBytes sh i (Data.encodeBytes p) _ (Data.reprBytes_encode p)
      simpa using this
    · next hn =>
      refine ih _ ?_
      obtain ⟨w, hw, hs⟩ := hcov
      rcases List.mem_cons.mp hw with rfl | hw
      · simp [hn] at hs
      · exact ⟨w, hw, hs⟩

/-- `reprAt` holds when some variant `k` matches and the bytes hold the tag `i + k` and its
payload. -/
theorem reprAt_spec (sh : List Shape) (i : Nat) (vs : List (Variant S)) (s : S)
    (bs : List UInt8) (h : reprAt sh i vs s bs) :
    ∃ k, ∃ hk : k < vs.length, ∃ p, (vs[k]).proj s = some p ∧
      sumRepr sh (i + k) (vs[k]).shape.size (Data.reprBytes p) bs := by
  induction vs generalizing i with
  | nil => cases h
  | cons v vs ih =>
    simp only [reprAt] at h
    split at h
    · next p hp => exact ⟨0, by simp, p, hp, by simpa using h⟩
    · obtain ⟨k, hk, p, hp, hr⟩ := ih _ h
      exact ⟨k + 1, by simp; omega, p, hp, by
        rw [show i + (k + 1) = i + 1 + k by omega]; exact hr⟩

end Variants

/-- The sum builder, which `deriving Data` uses for an `inductive`. The tag is the index of the
first variant whose projection succeeds, which `cover` guarantees exists, and the payload of that
variant follows. -/
@[instance_reducible] def Data.sum {S : Type} (vs : List (Variant S)) (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) :
    Data S where
  shape := .sum (Variants.shapes vs)
  linear := Variants.linear vs
  repr s v := Variants.reprAt (Variants.shapes vs) 0 vs s v.val
  encode s := ⟨Variants.encodeAt (Variants.shapes vs) 0 vs s,
    Variants.encodeAt_length _ _ _ _ fun v hv => List.mem_map_of_mem hv⟩
  encode_repr s := Variants.reprAt_encodeAt _ _ _ _ (cover s)

/-- A sum is determinate when its payloads are, it has at most `2^64` variants, and a variant's
payload determines the value. -/
theorem Data.sum_determinate {S : Type} (vs : List (Variant S)) (cover)
    (hdet : ∀ v ∈ vs, Data.Determinate v.T) (hn : vs.length ≤ 2 ^ 64)
    (ext : ∀ v ∈ vs, ∀ (s t : S) (p : v.T), v.proj s = some p → v.proj t = some p → s = t) :
    @Data.Determinate S (Data.sum vs cover) :=
  @Data.Determinate.mk S (Data.sum vs cover) fun s t bs hs ht => by
    obtain ⟨k, hk, p, hp, hrs⟩ := Variants.reprAt_spec _ 0 vs s bs.val hs
    obtain ⟨k', hk', q, hq, hrt⟩ := Variants.reprAt_spec _ 0 vs t bs.val ht
    have hkk : k = k' := by
      simpa using sumRepr_tag_inj (by simpa using hk) (by simpa using hk') (by simpa using hn)
        hrs hrt
    subst hkk
    have := hdet _ (List.getElem_mem hk)
    have hpq : p = q := Data.reprBytes_inj hrs.2 hrt.2
    subst hpq
    exact ext _ (List.getElem_mem hk) s t p hp hq

/-- `Option T`, where variant 0 is `none` with no payload and variant 1 is `some`. -/
instance {α : Type} [Data α] : Data (Option α) :=
  Data.sum [⟨fun o => match o with | none => some () | some _ => none⟩, ⟨id⟩]
    (fun o => by cases o <;> simp)

instance {α : Type} [Data α] [Data.Determinate α] : Data.Determinate (Option α) :=
  Data.sum_determinate _ _
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> infer_instance)
    (by simp)
    (by
      intro f hf s t p hs ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · cases s <;> cases t <;> simp_all
      · simp_all)

/-! ## Arrays -/

/-- `Arr T n` is an array of `n` elements, a `Vector T n` with the shape `array n (shape T)`. -/
abbrev Arr (T : Type) (n : Nat) : Type := Vector T n

instance {α : Type} [Data α] (n : Nat) : Data (Vector α n) where
  shape := .array n (Data.shape α)
  linear := Data.linear α
  repr v bs := ∀ i (h : i < n),
    Data.reprBytes v[i] (slice bs.val ((Data.shape α).elemOffset i) (Data.shape α).size)
  encode v := ⟨v.toList.flatMap Data.encodeBytes, by
    rw [length_flatMap_const _ _ Data.encodeBytes_length]; simp [Shape.size]⟩
  encode_repr v i h := by
    have := slice_flatMap Data.encodeBytes _ Data.encodeBytes_length v.toList i (by simpa)
    simp only [Shape.elemOffset]
    rw [this]; simpa using Data.reprBytes_encode v[i]

instance {α : Type} [Data α] [Data.Determinate α] (n : Nat) : Data.Determinate (Vector α n) :=
  ⟨fun _ _ _ ha hb => Vector.ext fun i h => Data.reprBytes_inj (ha i h) (hb i h)⟩

instance {α : Type} [Data α] [Data.Canonical α] (n : Nat) : Data.Canonical (Vector α n) :=
  ⟨fun a bs ha => Subtype.ext <| by
    show bs.val = a.toList.flatMap Data.encodeBytes
    have hb : bs.val.length = n * (Data.shape α).size := bs.2
    refine eq_flatMap_of_slices _ _ Data.encodeBytes_length _ _ (by rw [hb]; simp) fun i hi => ?_
    simpa [Shape.elemOffset] using Data.reprBytes_canon (ha i (by simpa using hi))⟩

/-! ## Slots -/

/-- `Slots T n` is an array of `n` cells, each empty or full, over `Vector (Option T) n`. Its shape
`slots n (shape T)` has no tags, so an empty cell's bytes may be anything. -/
def Slots (T : Type) (n : Nat) : Type := Vector (Option T) n

/-- The cells. -/
abbrev Slots.cells {T : Type} {n : Nat} (s : Slots T n) : Vector (Option T) n := s

/-- The zero-padded bytes of one cell, which are zeros when it is empty. -/
def Slots.cellBytes {T : Type} [Data T] : Option T → List UInt8
  | some x => Data.encodeBytes x
  | none => zeroBytes (Data.shape T).size

/-- A cell's bytes represent its content, and an empty cell's bytes are unconstrained. -/
def Slots.cellRepr {T : Type} [Data T] : Option T → List UInt8 → Prop
  | some x, bs => Data.reprBytes x bs
  | none, _ => True

theorem Slots.cellBytes_length {T : Type} [Data T] (o : Option T) :
    (Slots.cellBytes o).length = (Data.shape T).size := by
  cases o <;> simp [Slots.cellBytes]

instance {α : Type} [Data α] (n : Nat) : Data (Slots α n) where
  shape := .slots n (Data.shape α)
  linear := Data.linear α
  repr s bs := ∀ i (h : i < n),
    Slots.cellRepr s.cells[i] (slice bs.val ((Data.shape α).elemOffset i) (Data.shape α).size)
  encode s := ⟨s.cells.toList.flatMap Slots.cellBytes, by
    rw [length_flatMap_const _ _ Slots.cellBytes_length]; simp [Shape.size]⟩
  encode_repr s i h := by
    have := slice_flatMap Slots.cellBytes _ Slots.cellBytes_length s.cells.toList i (by simpa)
    simp only [Shape.elemOffset]
    rw [this]
    simp only [Vector.getElem_toList]
    cases s.cells[i] with
    | some x => exact Data.reprBytes_encode x
    | none => trivial
  occ s := some (s.cells.toList.map Option.isSome)

/-! ## Ghosts -/

/-- Ghost data of any Lean type, which has no run-time representation. -/
structure Ghost (α : Type) where
  val : α

instance {α : Type} : Data (Ghost α) where
  shape := .ghost
  linear := false
  repr _ _ := True
  encode _ := ⟨[], rfl⟩
  encode_repr _ := trivial

/-- A proposition as ghost data, for proof fields. -/
instance {p : Prop} : Data (PLift p) where
  shape := .ghost
  linear := false
  repr _ _ := True
  encode _ := ⟨[], rfl⟩
  encode_repr _ := trivial

instance {p : Prop} : Data.Determinate (PLift p) := ⟨fun a b _ _ _ => by cases a; cases b; rfl⟩
instance {α : Type} [Subsingleton α] : Data.Determinate (Ghost α) :=
  ⟨fun a b _ _ _ => by cases a; cases b; congr 1; exact Subsingleton.elim _ _⟩

/-- A ghost field of a struct, such as a proof field whose type depends on other fields. It has
the shape `ghost` and no bytes. Its value is not recorded, since a proof field is determined by
proof irrelevance. -/
def Field.ghost (S : Type) : Field S := ⟨fun _ => (⟨()⟩ : Ghost Unit)⟩

instance : Data.Determinate (Ghost Unit) := ⟨fun a b _ _ _ => by cases a; cases b; rfl⟩

/-! ## Object types -/

/-- `Arr T n`. -/
abbrev Ty.arr (t : Ty) (n : Nat) : Ty := ⟨Vector t.carrier n⟩
/-- `Slots T n`. -/
abbrev Ty.slots (t : Ty) (n : Nat) : Ty := ⟨Slots t.carrier n⟩
/-- The pair type. -/
abbrev Ty.pair (a b : Ty) : Ty := ⟨a.carrier × b.carrier⟩
/-- `Option T`. -/
abbrev Ty.option (t : Ty) : Ty := ⟨Option t.carrier⟩
/-- Ghost data of any Lean type. -/
abbrev Ty.ghost (α : Type) : Ty := ⟨Ghost α⟩
/-- A ghost index below `n`, which is a 64-bit word at run time. -/
abbrev Ty.fin (n : Nat) : Ty := ⟨Fin n⟩
/-- The value of a slice view of at most `n` elements of type `t`.

A slice is not a type of values, so it has no `Data` instance and no value holds one. A slice is
a kind of binder, a view binder, which only borrowing the slice place `p[lo..lo+len]` or passing
it as a reference argument introduces. At the machine a view binder is a pointer and a length. In
the value semantics it holds the viewed run of elements as the `Slots T n` whose full cells are
exactly the cells below `len`. Element `i` of a view is the cell place `r[i]!`, whose obligation
that the cell is full means `i < len`. The checker forbids assigning a view whole and `put` or
`take` on it, which could fill a cell past the length, where there is no storage. Reading a view,
or handing it back from a borrow, copies its first `len` cells into a `Slots` value. -/
abbrev Ty.view (t : Ty) (n : Nat) : Ty := .slots t n

/-- Tuples as nested pairs ending in `Unit`, so that `tup [a, b] = pair a (pair b unit)`. A
function with `mut` parameters hands back their updated values as a tuple. -/
def Ty.tup : List Ty → Ty
  | [] => .unit
  | t :: ts => .pair t (Ty.tup ts)

@[simp] theorem Ty.tup_nil : Ty.tup [] = .unit := rfl
@[simp] theorem Ty.tup_cons (t : Ty) (ts : List Ty) : Ty.tup (t :: ts) = .pair t (Ty.tup ts) := rfl

/-! ## Sizes and alignments of the instances -/

section Sizes
variable {α β : Type} [Data α] [Data β]

@[simp] theorem size_u8 : (Data.shape UInt8).size = 1 := rfl
@[simp] theorem size_u16 : (Data.shape UInt16).size = 2 := rfl
@[simp] theorem size_u32 : (Data.shape UInt32).size = 4 := rfl
@[simp] theorem size_u64 : (Data.shape UInt64).size = 8 := rfl
@[simp] theorem size_i8 : (Data.shape Int8).size = 1 := rfl
@[simp] theorem size_i16 : (Data.shape Int16).size = 2 := rfl
@[simp] theorem size_i32 : (Data.shape Int32).size = 4 := rfl
@[simp] theorem size_i64 : (Data.shape Int64).size = 8 := rfl
@[simp] theorem size_bool : (Data.shape Bool).size = 1 := rfl
@[simp] theorem size_unit : (Data.shape Unit).size = 0 := by decide
@[simp] theorem size_fin (n : Nat) : (Data.shape (Fin n)).size = 8 := rfl
@[simp] theorem align_u8 : (Data.shape UInt8).align = 1 := rfl
@[simp] theorem align_u16 : (Data.shape UInt16).align = 2 := rfl
@[simp] theorem align_u32 : (Data.shape UInt32).align = 4 := rfl
@[simp] theorem align_u64 : (Data.shape UInt64).align = 8 := rfl
@[simp] theorem align_i8 : (Data.shape Int8).align = 1 := rfl
@[simp] theorem align_i16 : (Data.shape Int16).align = 2 := rfl
@[simp] theorem align_i32 : (Data.shape Int32).align = 4 := rfl
@[simp] theorem align_i64 : (Data.shape Int64).align = 8 := rfl
@[simp] theorem align_bool : (Data.shape Bool).align = 1 := rfl
@[simp] theorem align_unit : (Data.shape Unit).align = 1 := rfl
@[simp] theorem align_fin (n : Nat) : (Data.shape (Fin n)).align = 8 := rfl
@[simp] theorem size_ghost {γ : Type} : (Data.shape (Ghost γ)).size = 0 := rfl
@[simp] theorem align_ghost {γ : Type} : (Data.shape (Ghost γ)).align = 1 := rfl
@[simp] theorem size_plift {p : Prop} : (Data.shape (PLift p)).size = 0 := rfl

@[simp] theorem size_vector (n : Nat) :
    (Data.shape (Vector α n)).size = n * (Data.shape α).size := rfl
@[simp] theorem align_vector (n : Nat) :
    (Data.shape (Vector α n)).align = (Data.shape α).align := rfl
@[simp] theorem size_slots (n : Nat) :
    (Data.shape (Slots α n)).size = n * (Data.shape α).size := rfl
@[simp] theorem align_slots (n : Nat) :
    (Data.shape (Slots α n)).align = (Data.shape α).align := rfl

@[simp] theorem shape_pair :
    Data.shape (α × β) = .prod [Data.shape α, Data.shape β] := rfl
@[simp] theorem shape_except :
    Data.shape (Except α β) = .sum [Data.shape α, Data.shape β] := rfl
@[simp] theorem shape_option :
    Data.shape (Option α) = .sum [Data.shape Unit, Data.shape α] := rfl

example : (Data.shape (UInt8 × UInt64)).size = 16 := by decide
example : (Data.shape (Except UInt64 UInt64)).size = 16 := by decide
example : (Data.shape (Except Unit Bool)).size = 2 := by decide
example : (Data.shape (Option UInt32)).size = 8 := by decide
example : (Data.shape (Vector (UInt16 × UInt8) 5)).size = 20 := by decide
example : (Data.shape (Slots UInt64 4)).size = 32 := by decide
example : (Data.shape (UInt64 × Ghost Nat)).size = 8 := by decide

end Sizes

end Millipede
