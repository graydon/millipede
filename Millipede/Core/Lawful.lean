import Millipede.Core.Place

/-!
# Laws of the derived building blocks

A lens, constructor or split carries a certificate of its law, which says that its Lean
functions agree with the byte layout that the memory lowering reads off the shapes, and the
compiler refuses a building block without one. This file proves the laws once for the shapes
that `deriving Data` produces, in a form that `deriving Data` can discharge for a concrete type
with `rfl`, `decide` and case analysis.

The laws of a struct rest on two facts about its bytes. A struct's representation depends only
on the bytes and values of its fields, and splicing a new representation of field `i` into the
bytes represents the struct with field `i` replaced. From these follow the laws of struct
lenses and struct constructors. The laws of a sum's constructors and splits rest on its first
byte being the tag, which holds when the sum has at most 256 variants.

The main results are `LensLaw.struct`, `CtorLaw.struct`, `CtorLaw.variant`, the three split laws
`SplitLaw.whole`, `SplitLaw.pair` and `SplitLaw.unit`, and the certified building blocks of the
core library: the pair lenses `Lens.fst` and `Lens.snd`, and the constructors `CtorLaw.pair`,
`CtorLaw.tuple`, `CtorLaw.fill` and `CtorLaw.slotsEmpty`.
-/

namespace Millipede.Flat

theorem splice_length (bs : List UInt8) (o : Nat) (vb : List UInt8) (h : o + vb.length ≤ bs.length) :
    (splice bs o vb).length = bs.length := by
  simp [splice]; omega

theorem slice_splice_same (bs : List UInt8) (o : Nat) (vb : List UInt8)
    (h : o + vb.length ≤ bs.length) : slice (splice bs o vb) o vb.length = vb := by
  unfold splice
  exact slice_append_mid' (by simp; omega) rfl

/-! ## Splices -/

theorem slice_splice_of_le (bs : List UInt8) (o : Nat) (vb : List UInt8) (a m : Nat)
    (h : a + m ≤ o) (ho : o ≤ bs.length) : slice (splice bs o vb) a m = slice bs a m := by
  simp only [slice, splice, List.append_assoc]
  rw [List.drop_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega)]
  rw [List.drop_take, List.take_take]
  congr 1; omega

theorem slice_splice_of_ge (bs : List UInt8) (o : Nat) (vb : List UInt8) (a m : Nat)
    (h : o + vb.length ≤ a) (ho : o ≤ bs.length) : slice (splice bs o vb) a m = slice bs a m := by
  simp only [slice, splice, List.append_assoc]
  have hl : (List.take o bs ++ vb).length = o + vb.length := by simp; omega
  rw [← List.append_assoc, List.drop_append, hl, List.drop_eq_nil_of_le (by omega),
    List.nil_append, List.drop_drop]
  congr 2; omega

/-! ## Struct representations -/

section Fields
variable {S : Type}

/-- The fields' slices from a struct's representation. -/
theorem fields_slices_of_reprAt (off : Nat) (fs : List (Field S)) (s : S) (bs : List UInt8)
    (h : Fields.reprAt off fs s bs) : ∀ j (hj : j < fs.length), Data.reprBytes ((fs[j]).get s)
      (slice bs ((Shape.prodOffsets off (Fields.shapes fs))[j]'(by simpa [Fields.shapes] using hj))
        (fs[j]).shape.size) := by
  induction fs generalizing off with
  | nil => intro j hj; simp at hj
  | cons f fs ih =>
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j => exact ih _ h.2 j (by simp at hj; omega)

/-- A struct laid out from `off` is still represented when the bytes from `off` on stay the same
and its fields keep their values. -/
theorem fields_reprAt_frame (off : Nat) (fs : List (Field S)) (s s' : S) (bs bs' : List UInt8)
    (h : Fields.reprAt off fs s bs) (hsame : ∀ j (hj : j < fs.length), (fs[j]).get s' = (fs[j]).get s)
    (hb : ∀ a m, off ≤ a → slice bs' a m = slice bs a m) : Fields.reprAt off fs s' bs' := by
  induction fs generalizing off with
  | nil => trivial
  | cons f fs ih =>
    have hle := le_alignUp off f.shape.align f.shape.align_pos
    refine ⟨?_, ih _ h.2 (fun j hj => hsame (j + 1) (by simp; omega)) fun a m ha => hb a m (by omega)⟩
    have h0 := hsame 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, hb _ _ hle]; exact h.1

/-- Replacing field `i`'s bytes by a representation of its new value represents the struct whose
field `i` changed and whose other fields did not. -/
theorem fields_reprAt_splice (off : Nat) (fs : List (Field S)) (s s' : S) (bs vb : List UInt8)
    (i : Nat) (hi : i < fs.length) (h : Fields.reprAt off fs s bs)
    (hsame : ∀ j (hj : j < fs.length), j ≠ i → (fs[j]).get s' = (fs[j]).get s)
    (hv : Data.reprBytes ((fs[i]).get s') vb)
    (hlen : Shape.prodEnd off (Fields.shapes fs) ≤ bs.length) :
    Fields.reprAt off fs s' (splice bs ((Shape.prodOffsets off (Fields.shapes fs))[i]'(by simpa [Fields.shapes] using hi))
      vb) := by
  induction fs generalizing off i with
  | nil => simp at hi
  | cons f fs ih =>
    have hle := le_alignUp off f.shape.align f.shape.align_pos
    have hend := Shape.le_prodEnd (alignUp off f.shape.align + f.shape.size) (Fields.shapes fs)
    simp only [Fields.shapes_cons, Shape.prodEnd] at hlen
    cases i with
    | zero =>
      have hvl : vb.length = f.shape.size := Data.reprBytes_length hv
      simp only [Fields.shapes_cons, Shape.prodOffsets, List.getElem_cons_zero]
      refine ⟨?_, ?_⟩
      · have := slice_splice_same bs (alignUp off f.shape.align) vb (by omega)
        rw [hvl] at this; rw [this]; exact hv
      · refine fields_reprAt_frame _ fs s s' _ _ h.2 (fun j hj => hsame (j + 1) (by simp; omega)
          (by omega)) fun a m ha => slice_splice_of_ge _ _ _ _ _ (by omega) (by omega)
    | succ i =>
      simp only [Fields.shapes_cons, Shape.prodOffsets, List.getElem_cons_succ]
      have hge := Shape.prodOffsets_ge (alignUp off f.shape.align + f.shape.size) (Fields.shapes fs) i
        (by simp [Fields.shapes]; simp at hi; omega)
      have hk := Shape.prodOffsets_end (alignUp off f.shape.align + f.shape.size) (Fields.shapes fs) i
        (by simp [Fields.shapes]; simp at hi; omega)
      refine ⟨?_, ih _ i (by simp at hi; omega) h.2
        (fun j hj hne => hsame (j + 1) (by simp; omega) (by omega)) hv hlen⟩
      have h0 := hsame 0 (by simp) (by omega)
      simp only [List.getElem_cons_zero] at h0
      rw [h0, slice_splice_of_le _ _ _ _ _ (by omega) (by omega)]; exact h.1

end Fields


/-! ## Struct lenses -/

section Fields
variable {S : Type}

/-- The fields `fs` of `s'` and `s` have the same values. -/
def Fields.SameAll : List (Field S) → S → S → Prop
  | [], _, _ => True
  | f :: fs, s', s => f.get s' = f.get s ∧ Fields.SameAll fs s' s

/-- The fields `fs` of `s'` and `s` have the same values, except field `i`. -/
def Fields.SameExcept : List (Field S) → Nat → S → S → Prop
  | [], _, _, _ => True
  | _ :: fs, 0, s', s => Fields.SameAll fs s' s
  | f :: fs, i + 1, s', s => f.get s' = f.get s ∧ Fields.SameExcept fs i s' s

theorem Fields.sameAll_spec (fs : List (Field S)) (s' s : S) (h : Fields.SameAll fs s' s) :
    ∀ j (hj : j < fs.length), (fs[j]).get s' = (fs[j]).get s := by
  induction fs with
  | nil => intro j hj; simp at hj
  | cons f fs ih =>
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j => exact ih h.2 j (by simp at hj; omega)

theorem Fields.sameExcept_spec (fs : List (Field S)) (i : Nat) (s' s : S)
    (h : Fields.SameExcept fs i s' s) :
    ∀ j (hj : j < fs.length), j ≠ i → (fs[j]).get s' = (fs[j]).get s := by
  induction fs generalizing i with
  | nil => intro j hj; simp at hj
  | cons f fs ih =>
    intro j hj hne
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j => exact Fields.sameAll_spec fs s' s h j (by simp at hj; omega)
    | succ i =>
      cases j with
      | zero => exact h.1
      | succ j => exact ih i h.2 j (by simp at hj; omega) (by omega)

theorem Fields.occs_set : ∀ (fs : List (Field S)) (i : Nat) (hi : i < fs.length) (x y : S),
    (∀ j (hj : j < fs.length), j ≠ i → (fs[j]).get y = (fs[j]).get x) →
    Fields.occs fs y = Fields.occs (fs.take i) x ++ Data.occs ((fs[i]).get y) ++
      Fields.occs (fs.drop (i + 1)) x
  | [], _, hi, _, _, _ => by simp at hi
  | f :: fs, 0, _, x, y, h => by
    have : Fields.occs fs y = Fields.occs fs x := by
      suffices ∀ (gs : List (Field S)), (∀ j (hj : j < gs.length), (gs[j]).get y = (gs[j]).get x) →
          Fields.occs gs y = Fields.occs gs x from
        this fs fun j hj => h (j + 1) (by simp; omega) (by omega)
      intro gs hg
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        simp only [Fields.occs]
        rw [show g.get y = g.get x from hg 0 (by simp), ih fun j hj => hg (j + 1) (by simp; omega)]
    simp [Fields.occs, this]
  | f :: fs, i + 1, hi, x, y, h => by
    simp only [Fields.occs, List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
    rw [show f.get y = f.get x from h 0 (by simp) (by omega), Fields.occs_set fs i (by simp at hi; omega) x y
      fun j hj hne => h (j + 1) (by simp; omega) (by omega)]
    simp [List.append_assoc]

theorem Fields.occsN_split : ∀ (fs : List (Field S)) (i : Nat) (hi : i < fs.length),
    Fields.occsN fs = Fields.occsN (fs.take i) + Data.occsN (fs[i]).T + Fields.occsN (fs.drop (i + 1))
  | [], _, hi => by simp at hi
  | f :: fs, 0, _ => by simp [Fields.occsN]
  | f :: fs, i + 1, hi => by
    simp only [Fields.occsN, List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
    rw [Fields.occsN_split fs i (by simp at hi; omega)]; omega

end Fields

/-- The occupancy law of the lens of field `i` of `Data.struct fs`, whose `get` has the field's
occupancies and whose `set` gives field `i` the new value's occupancies and keeps the others. -/
theorem LensOccs.struct {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) {t : Ty} (index : Nat) (get : S → t.carrier)
    (set : S → t.carrier → S) (i : Nat) (hi : i < fs.length) (hidx : index = i)
    (hN : Data.occsN t.carrier = Data.occsN (fs[i]).T)
    (hgetO : ∀ x, Data.occs (get x) = Data.occs ((fs[i]).get x))
    (hsetO : ∀ x v, Data.occs ((fs[i]).get (set x v)) = Data.occs v)
    (hkeep : ∀ x v j (hj : j < fs.length), j ≠ i → (fs[j]).get (set x v) = (fs[j]).get x) :
    LensOccs ⟨S⟩ t index get set := by
  subst hinst hidx
  letI : Data S := Data.struct fs
  have hoff : @Data.occsOff S (Data.struct fs) index = Fields.occsN (fs.take index) := rfl
  have hA : ∀ x, (Fields.occs (fs.take index) x).length = Fields.occsN (fs.take index) :=
    fun x => Fields.occsN_eq _ x
  have hB : ∀ x, (Data.occs ((fs[index]).get x)).length = Data.occsN t.carrier :=
    fun x => by rw [Data.occsN_eq, hN]
  refine ⟨?_, fun x => ?_, fun x v => ?_⟩
  · show Fields.occsN (fs.take index) + _ ≤ Fields.occsN fs
    rw [Fields.occsN_split fs index hi, hN]; omega
  · show Data.occs (get x) = ((Fields.occs fs x).drop (Data.occsOff S index)).take _
    rw [Fields.occs_set fs index hi x x (fun _ _ _ => rfl), hoff, hgetO, List.append_assoc,
      List.drop_left' (hA x), List.take_left' (hB x)]
  · show Fields.occs fs (set x v) = (Fields.occs fs x).take (Data.occsOff S index) ++ Data.occs v ++
      (Fields.occs fs x).drop (Data.occsOff S index + Data.occsN t.carrier)
    rw [Fields.occs_set fs index hi x (set x v) (hkeep x v), hsetO,
      Fields.occs_set fs index hi x x (fun _ _ _ => rfl), hoff]
    have hv : (Data.occs v).length = Data.occsN t.carrier := Data.occsN_eq v
    simp only [List.append_assoc]
    rw [← hA x, List.take_left, List.drop_append, ← hB x]
    simp

/-- The byte law of the lens of field `i` of `Data.struct fs`, whose `get` is the field's
projection and whose `set` gives field `i` the new value and keeps the other fields. -/
theorem LensBytes.struct {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) {t : Ty} (index : Nat) (get : S → t.carrier)
    (set : S → t.carrier → S) (i : Nat) (hi : i < fs.length)
    (hidx : index = i) (hsz : (fs[i]).shape.size = t.size)
    (hget : ∀ x bs, Data.reprBytes ((fs[i]).get x) bs → Data.reprBytes (get x) bs)
    (hset : ∀ x v vb, Data.reprBytes v vb → Data.reprBytes ((fs[i]).get (set x v)) vb)
    (hkeep : ∀ x v j (hj : j < fs.length), j ≠ i → (fs[j]).get (set x v) = (fs[j]).get x) :
    LensBytes ⟨S⟩ t index get set := by
  subst hinst
  have hoff : lensOffAt (@Ty.mk S (Data.struct fs)) index =
      (Shape.prodOffsets 0 (Fields.shapes fs))[i]'(by simpa [Fields.shapes]) := by
    show Shape.fieldOffset (Fields.shapes fs) index = _
    rw [hidx, Shape.fieldOffset_eq _ _ (by simpa [Fields.shapes])]
  have hb : lensOffAt (@Ty.mk S (Data.struct fs)) index + t.size ≤ (Shape.prod (Fields.shapes fs)).size := by
    rw [← hsz]
    have := Shape.fieldOffset_add_size_le (Fields.shapes fs) i (by simpa [Fields.shapes])
    rw [Shape.fieldOffset_eq _ _ (by simpa [Fields.shapes])] at this
    rw [hoff]; simpa [Fields.shapes] using this
  refine ⟨hb, fun x bs h => ?_, fun x v bs vb h hv => ?_⟩
  · obtain ⟨hl, hr⟩ := h
    have := fields_slices_of_reprAt 0 fs x bs hr i hi
    rw [hoff, ← hsz]; exact hget x _ this
  · obtain ⟨hl, hr⟩ := h
    have hend : Shape.prodEnd 0 (Fields.shapes fs) ≤ bs.length := by
      rw [hl]; exact le_alignUp _ _ (Shape.alignMax_pos _)
    refine ⟨?_, ?_⟩
    · rw [splice_length _ _ _ (by
        have : bs.length = (Shape.prod (Fields.shapes fs)).size := hl
        have hvl : vb.length = t.size := Data.reprBytes_length hv
        omega)]; exact hl
    · show Fields.reprAt 0 fs (set x v) (splice bs (lensOffAt (@Ty.mk S (Data.struct fs)) index) vb)
      rw [hoff]
      exact fields_reprAt_splice 0 fs x (set x v) bs vb i hi hr
        (fun j hj hne => hkeep x v j hj hne) (hset x v vb hv) hend

/-- The law of the lens of field `i` of `Data.struct fs`, which is its byte law and its occupancy
law together. -/
theorem LensLaw.struct {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) {t : Ty} (index : Nat) (get : S → t.carrier)
    (set : S → t.carrier → S) (i : Nat) (hi : i < fs.length)
    (hidx : index = i) (hsz : (fs[i]).shape.size = t.size)
    (hget : ∀ x bs, Data.reprBytes ((fs[i]).get x) bs → Data.reprBytes (get x) bs)
    (hset : ∀ x v vb, Data.reprBytes v vb → Data.reprBytes ((fs[i]).get (set x v)) vb)
    (hkeep : ∀ x v j (hj : j < fs.length), j ≠ i → (fs[j]).get (set x v) = (fs[j]).get x)
    (hN : Data.occsN t.carrier = Data.occsN (fs[i]).T)
    (hgetO : ∀ x, Data.occs (get x) = Data.occs ((fs[i]).get x))
    (hsetO : ∀ x v, Data.occs ((fs[i]).get (set x v)) = Data.occs v) :
    LensLaw ⟨S⟩ t index get set :=
  ⟨LensBytes.struct fs hinst index get set i hi hidx hsz hget hset hkeep,
    LensOccs.struct fs hinst index get set i hi hidx hN hgetO hsetO hkeep⟩

/-- `LensLaw.struct` with the other fields' preservation stated as `Fields.SameExcept`, which
`deriving Data` proves by `rfl` for each field. -/
theorem LensLaw.field {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) {t : Ty} (get : S → t.carrier)
    (set : S → t.carrier → S) (i : Nat) (hi : i < fs.length) (hsz : (fs[i]).shape.size = t.size)
    (hget : ∀ x bs, Data.reprBytes ((fs[i]).get x) bs → Data.reprBytes (get x) bs)
    (hset : ∀ x v vb, Data.reprBytes v vb → Data.reprBytes ((fs[i]).get (set x v)) vb)
    (hkeep : ∀ x v, Fields.SameExcept fs i (set x v) x)
    (hN : Data.occsN t.carrier = Data.occsN (fs[i]).T)
    (hgetO : ∀ x, Data.occs (get x) = Data.occs ((fs[i]).get x))
    (hsetO : ∀ x v, Data.occs ((fs[i]).get (set x v)) = Data.occs v) :
    LensLaw ⟨S⟩ t i get set :=
  LensLaw.struct fs hinst i get set i hi rfl hsz hget hset
    (fun x v j hj hne => Fields.sameExcept_spec fs i _ _ (hkeep x v) j hj hne) hN hgetO hsetO

/-! ## Struct constructors -/

/-- The law of a struct constructor. Its placements are inside the value and disjoint, which is
decidable for a concrete type, and any bytes that hold its arguments at the field offsets
represent the built value. -/
theorem CtorLaw.struct {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) {ps : List Ty} (build : Env ps → S)
    (hplan : (∀ q ∈ placements ps (planOf ps ⟨S⟩ .struct).1, q.1 + q.2 ≤ (Data.shape S).size ∧
        ((planOf ps ⟨S⟩ .struct).2.isSome → 1 ≤ q.1)) ∧
      (placements ps (planOf ps ⟨S⟩ .struct).1).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2))
    (hbuild : ∀ (env : Env ps) (bs : List UInt8), ArgsAt (planOf ps ⟨S⟩ .struct).1 env bs →
      Fields.reprAt 0 fs (build env) bs) :
    CtorLaw ps ⟨S⟩ .struct build := by
  have h2 : (planOf ps ⟨S⟩ .struct).2 = none := by
    unfold planOf; split <;> first | rfl | simp_all
  refine ⟨hplan.1, hplan.2, by simp [h2], fun env bs hl _ ha => ?_⟩
  subst hinst
  exact ⟨hl, hbuild env bs ha⟩

/-- Every constructor into `Unit` is lawful, because a `Unit` value has no bytes. -/
theorem CtorLaw.unit (ps : List Ty) (kind : CtorKind) (build : Env ps → Unit) :
    CtorLaw ps Ty.unit kind build := by
  have hp : planOf ps Ty.unit kind = ([], none) := by
    unfold planOf; cases kind <;> rfl
  refine ⟨?_, ?_, ?_, fun _ bs hl _ _ => ⟨hl, trivial⟩⟩ <;> rw [hp]
  · intro q hq; cases ps <;> simp [placements] at hq
  · cases ps <;> simp [placements]
  · simp

/-- The pair constructor is lawful, with both components at their C-layout offsets. -/
theorem CtorLaw.pair (a b : Ty) :
    CtorLaw [a, b] (.pair a b) .struct fun env => (env.get .here, env.get (.there .here)) := by
  have hp : planOf [a, b] (.pair a b) .struct =
      ([[alignUp 0 a.align], [alignUp (alignUp 0 a.align + a.size) b.align]], none) := rfl
  have h1 := le_alignUp (alignUp 0 a.align + a.size) b.align (Shape.align_pos _)
  have h2 := le_alignUp (alignUp (alignUp 0 a.align + a.size) b.align + b.size)
    (Shape.alignMax [Data.shape a.carrier, Data.shape b.carrier]) (Shape.alignMax_pos _)
  have hs : (Data.shape (a.carrier × b.carrier)).size =
      alignUp (alignUp (alignUp 0 a.align + a.size) b.align + b.size)
        (Shape.alignMax [Data.shape a.carrier, Data.shape b.carrier]) := rfl
  refine CtorLaw.struct (S := a.carrier × b.carrier) [⟨Prod.fst⟩, ⟨Prod.snd⟩] rfl _
    ⟨?_, ?_⟩ ?_
  · intro q hq
    rw [hp] at hq
    simp [placements] at hq
    rcases hq with rfl | rfl <;> refine ⟨?_, by simp [hp]⟩ <;> dsimp only <;> rw [hs] <;> omega
  · rw [hp]; simp [placements, Disj]; omega
  · rintro (env : Env [a, b]) bs ha
    match env, ha with
    | .cons x (.cons y .nil), ⟨h1, h2, _⟩ =>
      exact ⟨h1 _ (List.mem_singleton_self _), h2 _ (List.mem_singleton_self _), trivial⟩

/-- Bytes holding the two components of a pair at their offsets represent the pair. -/
theorem pair_of_slices {a b : Ty} (x : a.carrier) (y : b.carrier) (bs : List UInt8)
    (hl : bs.length = (Ty.pair a b).size) (hx : Data.reprBytes x (slice bs 0 a.size))
    (hy : Data.reprBytes y (slice bs (fieldOff (Data.shape (a.carrier × b.carrier)) 1) b.size)) :
    @Data.reprBytes (Ty.pair a b).carrier _ (x, y) bs :=
  (CtorLaw.pair a b).2.2.2 (.cons x (.cons y .nil)) bs hl trivial
    ⟨fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; rw [alignUp_zero]; exact hx,
     fun o ho => by simp only [List.mem_singleton] at ho; subst ho; exact hy, trivial⟩

/-- The second component of a pair starts after the first. -/
theorem fst_le_sndOff (a b : Ty) : a.size ≤ fieldOff (Data.shape (a.carrier × b.carrier)) 1 := by
  show a.size ≤ alignUp (alignUp 0 a.align + a.size) b.align
  rw [alignUp_zero, Nat.zero_add]; exact le_alignUp _ _ (Shape.align_pos (Data.shape b.carrier))

/-- The second component of a pair lies inside the pair. -/
theorem sndOff_add_le (a b : Ty) :
    fieldOff (Data.shape (a.carrier × b.carrier)) 1 + b.size ≤ (Ty.pair a b).size :=
  Shape.fieldOffset_add_size_le [Data.shape a.carrier, Data.shape b.carrier] 1 (by simp)

/-- The tuple of the values of an environment. -/
def tupBuild : (ps : List Ty) → Env ps → (Ty.tup ps).carrier
  | [], .nil => ()
  | _ :: ts, .cons v env => (v, tupBuild ts env)

@[simp] theorem tupBuild_nil : tupBuild [] .nil = () := rfl
@[simp] theorem tupBuild_cons (t : Ty) (ts : List Ty) (v : t.carrier) (env : Env ts) :
    tupBuild (t :: ts) (.cons v env) = (v, tupBuild ts env) := rfl

/-- The tuple of an environment's values has the occupancies of those values, which is the
certificate `Ctor.occs` of `Ctor.tupMk`. -/
theorem tupBuild_occs : (ps : List Ty) → (env : Env ps) → Data.occs (tupBuild ps env) = env.occs
  | [], .nil => rfl
  | _ :: ts, .cons v env => by
    show Data.occs v ++ (Data.occs (tupBuild ts env) ++ []) = _
    rw [List.append_nil, tupBuild_occs ts env]; rfl

theorem tupOffs_add : ∀ (ts : List Ty) (o : Nat), tupOffs ts o = (tupOffs ts 0).map (· + o)
  | [], _ => rfl
  | t :: ts, o => by
    simp only [tupOffs, List.map_cons, Nat.zero_add]
    rw [tupOffs_add ts (o + _), tupOffs_add ts (fieldOff _ 1), List.map_map]
    congr 1
    apply List.map_congr_left; intro x _; simp only [Function.comp]; omega

@[simp] theorem tupOffs_length : ∀ (ts : List Ty) (o : Nat), (tupOffs ts o).length = ts.length
  | [], _ => rfl
  | _ :: ts, _ => by simp only [tupOffs, List.length_cons, tupOffs_length ts]

/-- The components of a tuple lie inside it. -/
theorem tupOffs_bound : ∀ (ts : List Ty) (i : Nat) (hi : i < ts.length),
    (tupOffs ts 0)[i]'(by simpa using hi) + (ts[i]).size ≤ (Ty.tup ts).size := by
  intro ts
  induction ts with
  | nil => intro i hi; simp at hi
  | cons t ts ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [tupOffs, List.getElem_cons_zero, Nat.zero_add]
      have := fst_le_sndOff t (Ty.tup ts); have := sndOff_add_le t (Ty.tup ts)
      show t.size ≤ (Ty.pair t (Ty.tup ts)).size; omega
    | succ i =>
      simp only [tupOffs, List.getElem_cons_succ, Nat.zero_add]
      simp only [tupOffs_add ts (fieldOff _ 1), List.getElem_map]
      have := ih i (by simpa using hi)
      have := sndOff_add_le t (Ty.tup ts)
      show _ ≤ (Ty.pair t (Ty.tup ts)).size
      omega

theorem slice_slice (bs : List UInt8) (s L o m : Nat) (h : o + m ≤ L) :
    slice (slice bs s L) o m = slice bs (s + o) m := by
  simp only [slice, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-- The placements of single offsets. -/
theorem placements_single : ∀ (ps : List Ty) (os : List Nat), os.length = ps.length →
    placements ps (os.map fun o => [o]) = List.zipWith (fun o t => (o, t.size)) os ps
  | [], [], _ => rfl
  | t :: ts, o :: os, h => by
    simp only [List.map_cons, placements, List.map_cons, List.map_nil, List.singleton_append,
      List.zipWith_cons_cons]
    rw [placements_single ts os (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The value of the variable at position `i`. -/
def _root_.Millipede.Env.getI : {Γ : List Ty} → Env Γ → (i : Nat) → (hi : i < Γ.length) →
    (Γ[i]'hi).carrier
  | _ :: _, .cons v _, 0, _ => v
  | _ :: _, .cons _ env, i + 1, hi => env.getI i (by simp at hi; omega)

/-- `ArgsAt` for single offsets, element by element. -/
theorem argsAt_single : ∀ {ps : List Ty} (os : List Nat) (env : Env ps) (bs : List UInt8)
    (hl : os.length = ps.length),
    ((∀ (i : Nat) (hi : i < ps.length), Data.reprBytes (env.getI i hi)
      (slice bs (os[i]'(by omega)) (ps[i]).size)) ↔ ArgsAt (os.map fun o => [o]) env bs)
  | [], [], .nil, _, _ => by simp [ArgsAt]
  | t :: ts, o :: os, .cons v env, bs, h => by
    simp only [List.map_cons, ArgsAt, List.mem_singleton, forall_eq]
    rw [← argsAt_single os env bs (by simpa using h)]
    constructor
    · intro hh; exact ⟨hh 0 (by simp), fun i hi => hh (i + 1) (by simp; omega)⟩
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact hr i (by simp at hi; omega)
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

/-- The components of a tuple come one after the other, so component `i` ends before a later
component `j` starts. -/
theorem tupOffs_disj : ∀ (ts : List Ty) (i j : Nat) (hij : i < j) (hj : j < ts.length),
    (tupOffs ts 0)[i]'(by simp; omega) + (ts[i]'(by omega)).size ≤ (tupOffs ts 0)[j]'(by simpa using hj) := by
  intro ts
  induction ts with
  | nil => intro i j _ hj; simp at hj
  | cons t ts ih =>
    intro i j hij hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [tupOffs, List.getElem_cons_succ, Nat.zero_add]
      simp only [tupOffs_add ts (fieldOff _ 1), List.getElem_map]
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        have := fst_le_sndOff t (Ty.tup ts); omega
      | succ i =>
        simp only [List.getElem_cons_succ, List.getElem_map]
        have := ih i j (by omega) (by simpa using hj); omega

/-- Bytes holding the components of a tuple at their offsets represent the tuple. -/
theorem tup_repr : ∀ (ts : List Ty) (env : Env ts) (bs : List UInt8),
    bs.length = (Ty.tup ts).size → ArgsAt ((tupOffs ts 0).map fun o => [o]) env bs →
    Data.reprBytes (tupBuild ts env) bs
  | [], .nil, bs, hl, _ => ⟨hl, trivial⟩
  | t :: ts, .cons v env, bs, hl, ha => by
    simp only [tupOffs, List.map_cons, ArgsAt, List.mem_singleton, forall_eq, Nat.zero_add] at ha
    have hs := sndOff_add_le t (Ty.tup ts)
    refine pair_of_slices v (tupBuild ts env) bs hl ha.1 (tup_repr ts env _ ?_ ?_)
    · rw [slice_length_of_le (by show _ ≤ bs.length; rw [hl]; exact hs)]
    · have h2 := ha.2
      rw [tupOffs_add ts] at h2
      rw [← argsAt_single (tupOffs ts 0) env _ (by simp)]
      rw [← argsAt_single ((tupOffs ts 0).map (· + fieldOff (Data.shape (t.carrier × (Ty.tup ts).carrier)) 1))
        env bs (by simp)] at h2
      intro i hi
      have := h2 i hi
      rw [slice_slice _ _ _ _ _ (tupOffs_bound ts i hi)]
      simpa [Nat.add_comm] using this

/-- The law of the tuple constructor, which places the components at `tupOffs`. -/
theorem CtorLaw.tuple (t : Ty) (ts : List Ty) :
    CtorLaw (t :: ts) (Ty.tup (t :: ts)) .tuple (tupBuild (t :: ts)) := by
  have hp : planOf (t :: ts) (Ty.tup (t :: ts)) .tuple =
      ((tupOffs (t :: ts) 0).map fun o => [o], none) := rfl
  have hpl := placements_single (t :: ts) (tupOffs (t :: ts) 0) (by simp)
  refine ⟨?_, ?_, by rw [hp]; simp, fun env bs hl _ ha => ?_⟩
  · rw [hp]; intro q hq
    rw [hpl] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_zipWith, tupOffs_length, Nat.min_self] at hi
    simp only [List.getElem_zipWith]
    exact ⟨tupOffs_bound (t :: ts) i hi, by simp⟩
  · rw [hp, hpl]
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_zipWith, tupOffs_length, Nat.min_self] at hi hj
    simp only [List.getElem_zipWith]
    left; exact tupOffs_disj (t :: ts) i j hij hj
  · rw [hp] at ha
    exact tup_repr (t :: ts) env bs hl ha

/-- The constructor `Vector.replicate n x` into an array is lawful, since it copies `x` to every
element. -/
theorem CtorLaw.fill (t : Ty) (n : Nat) :
    CtorLaw [t] (.arr t n) .fill fun env => Vector.replicate n (env.get .here) := by
  have hp : planOf [t] (.arr t n) .fill = ([(List.range n).map fun j => j * t.size], none) := rfl
  have hsz : (Ty.arr t n).size = n * t.size := rfl
  refine ⟨?_, ?_, by rw [hp]; simp, fun env bs hl _ ha => ⟨hl, fun i h => ?_⟩⟩
  · rw [hp, hsz]; intro q hq
    simp [placements] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    refine ⟨?_, by simp⟩
    show j * t.size + t.size ≤ n * t.size
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  · rw [hp]
    simp only [placements, List.append_nil, List.map_map]
    refine List.pairwise_map.mpr ((List.pairwise_lt_range (n := n)).imp fun {a b} hab => ?_)
    left; show a * t.size + t.size ≤ b * t.size
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hab
  · rw [hp] at ha
    match env, ha with
    | .cons x .nil, ⟨hx, _⟩ =>
      show Data.reprBytes (Vector.replicate n x)[i] _
      simp only [Vector.getElem_replicate]
      exact hx _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩)

/-- The constructor `Slots.empty n` is lawful, since the bytes of an empty cell may be anything. -/
theorem CtorLaw.slotsEmpty (t : Ty) (n : Nat) :
    CtorLaw [] (.slots t n) .fill fun _ => Slots.empty n := by
  refine ⟨fun q hq => by simp [placements] at hq, by simp [placements], ?_,
    fun env bs hl _ _ => ⟨hl, fun i h => ?_⟩⟩
  · have hp : (planOf [] (.slots t n) .fill).2 = none := rfl
    simp [hp]
  · show Slots.cellRepr (Vector.replicate n none)[i] _
    simp [Slots.cellRepr]

/-! ## The pair lenses -/

/-- The lens of the first component of a pair. -/
def _root_.Millipede.Lens.fst (a b : Ty) : Lens (.pair a b) a :=
  ⟨"fst", 0, Prod.fst, fun p x => (x, p.2), some ⟨LensLaw.field (S := a.carrier × b.carrier)
    [⟨Prod.fst⟩, ⟨Prod.snd⟩] rfl _ _ 0 (by simp) rfl (fun _ _ h => h) (fun _ _ _ h => h)
    (fun _ _ => ⟨rfl, trivial⟩) rfl (fun _ => rfl) (fun _ _ => rfl)⟩⟩

/-- The lens of the second component of a pair. -/
def _root_.Millipede.Lens.snd (a b : Ty) : Lens (.pair a b) b :=
  ⟨"snd", 1, Prod.snd, fun p x => (p.1, x), some ⟨LensLaw.field (S := a.carrier × b.carrier)
    [⟨Prod.fst⟩, ⟨Prod.snd⟩] rfl _ _ 1 (by simp) rfl (fun _ _ h => h) (fun _ _ _ h => h)
    (fun _ _ => ⟨rfl, trivial⟩) rfl (fun _ => rfl) (fun _ _ => rfl)⟩⟩

/-! ## Sums: tags -/

theorem tag_eq_iff {k i : Nat} (hk : k < 256) (hi : i < 256) :
    (UInt8.ofNat k).toUInt64 = UInt64.ofNat i ↔ k = i := by
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    simp at this
    omega
  · rintro rfl
    apply UInt64.toNat_inj.mp
    simp; omega

theorem head_of_slice {bs : List UInt8} {b : UInt8} (h : slice bs 0 1 = [b]) : bs.headD 0 = b := by
  cases bs with
  | nil => simp [slice] at h
  | cons c bs => simp [slice] at h; simp [h]

theorem slice_of_head {bs : List UInt8} {b : UInt8} (h : bs.head? = some b) :
    slice bs 0 1 = [b] := by
  cases bs with
  | nil => simp at h
  | cons c bs => simp at h; simp [slice, h]

theorem tagBytes_one {sh : List Shape} (h : sh.length ≤ 256) : Shape.tagBytes sh = 1 := by
  simp [Shape.tagBytes, tagWidth, h]; rfl

/-- The first byte of a sum value of at most `2^8` variants is its tag. -/
theorem head_of_sumRepr {sh : List Shape} {k len : Nat} {P : List UInt8 → Prop} {bs : List UInt8}
    (hn : sh.length ≤ 256) (h : sumRepr sh k len P bs) : bs.headD 0 = UInt8.ofNat k := by
  have h1 := h.1
  rw [tagBytes_one hn] at h1
  rw [head_of_slice h1]
  apply UInt8.toNat_inj.mp; simp

/-- When none of the first variants `pre` matches, the representation is that of the remaining
variants, renumbered from zero. -/
theorem Variants.reprAt_skip {S : Type} (sh : List Shape) (n : Nat) (pre vs : List (Variant S))
    (s : S) (bs : List UInt8) (hpre : pre.all (fun w => (w.proj s).isNone) = true) :
    Variants.reprAt sh n (pre ++ vs) s bs ↔ Variants.reprAt sh (n + pre.length) vs s bs := by
  induction pre generalizing n with
  | nil => simp
  | cons w pre ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    have hw : w.proj s = none := Option.isNone_iff_eq_none.mp hpre.1
    simp only [List.cons_append, Variants.reprAt, hw]
    rw [ih (n + 1) hpre.2]
    simp only [List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]

/-- A represented value's tag differs from `i` when variant `i`'s projection fails on it. -/
theorem Variants.tag_ne {S : Type} (pre post : List (Variant S)) (v : Variant S) (s : S)
    (bs : List UInt8) (hn : (pre ++ v :: post).length ≤ 256)
    (h : Variants.reprAt (Variants.shapes (pre ++ v :: post)) 0 (pre ++ v :: post) s bs)
    (hv : v.proj s = none) :
    (bs.headD 0).toUInt64 ≠ UInt64.ofNat pre.length := by
  obtain ⟨k, hk, p, hp, hr⟩ := Variants.reprAt_spec _ 0 _ s bs h
  have hsome : ((pre ++ v :: post)[k].proj s).isSome = true := by rw [hp]; rfl
  have hsh : (Variants.shapes (pre ++ v :: post)).length ≤ 256 := by simpa using hn
  rw [head_of_sumRepr hsh hr, Nat.zero_add]
  intro heq
  rw [tag_eq_iff (by omega) (by simp at hn; omega)] at heq
  subst heq
  have hv' : (pre ++ v :: post)[pre.length]'hk = v := by simp
  rw [hv', hv] at hsome
  cases hsome

/-! ## Sums: constructors -/

/-- The law of constructor `i` of `Data.sum vs`, for at most 256 variants. Its argument is
variant `i`'s payload, and it builds a value that no earlier variant matches. -/
theorem CtorLaw.variant {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) {P : Ty} (pre post : List (Variant S)) (proj : S → Option P.carrier)
    (hvs : vs = pre ++ (⟨proj⟩ : Variant S) :: post) (i : Nat) (hi : pre.length = i)
    (build : Env [P] → S)
    (hpre : ∀ env, pre.all (fun w => (w.proj (build env)).isNone) = true)
    (hproj : ∀ env, proj (build env) = some (env.get .here)) :
    CtorLaw [P] ⟨S⟩ (.variant i) build := by
  subst hvs hinst hi
  have hp : planOf [P] (@Ty.mk S (Data.sum _ cover)) (.variant pre.length) =
      ([[Shape.payloadOffset (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post))]],
        some pre.length) := rfl
  have hmem : Data.shape P.carrier ∈ Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post) :=
    List.mem_map_of_mem (f := Variant.shape) (List.mem_append_right _ List.mem_cons_self)
  have hpo := Shape.payload_add_size_le _ _ hmem
  have hsh : (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post)).length ≤ 256 := by simpa using hn
  have htb := Shape.tagBytes_le_payloadOffset (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post))
  rw [tagBytes_one hsh] at htb
  refine ⟨?_, ?_, ?_, fun env bs hl htag ha => ?_⟩
  · rw [hp]; intro q hq
    simp only [placements, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hq
    subst hq
    exact ⟨hpo, fun _ => htb⟩
  · rw [hp]; simp [placements]
  · intro _; show 1 ≤ (Shape.sum _).size; omega
  · rw [hp] at htag ha
    refine ⟨hl, (Variants.reprAt_skip _ 0 pre _ _ bs (hpre env)).mpr ?_⟩
    simp only [Variants.reprAt, hproj, Nat.zero_add]
    match env, ha with
    | .cons v .nil, ⟨hv, _⟩ =>
      refine ⟨?_, hv _ (List.mem_singleton_self _)⟩
      rw [tagBytes_one hsh, slice_of_head htag]
      simp only [natBytes, UInt64.toUInt8_ofNat']
      congr 1
      apply UInt8.toNat_inj.mp; simp

/-! ## Sums: splits -/

/-- The law of a split whose rest is the value itself, the mode `whole` used for three or more
variants. It tests variant `i` of `Data.sum vs`, for at most 256 variants, whose projection gives
the payload of a value that no earlier variant matches, and it hands back the value otherwise. -/
theorem SplitLaw.whole {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) (hk : 2 < vs.length) {P : Ty} (pre post : List (Variant S))
    (proj : S → Option P.carrier) (hvs : vs = pre ++ (⟨proj⟩ : Variant S) :: post)
    (i : Nat) (hi : pre.length = i) (split : S → P.carrier ⊕ S)
    (hinl : ∀ x a, split x = .inl a →
      proj x = some a ∧ pre.all (fun w => (w.proj x).isNone) = true)
    (hinr : ∀ x b, split x = .inr b → b = x ∧ proj x = none) :
    SplitLaw ⟨S⟩ P ⟨S⟩ i split := by
  subst hvs hinst hi
  have hmem : Data.shape P.carrier ∈ Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post) :=
    List.mem_map_of_mem (f := Variant.shape) (List.mem_append_right _ List.mem_cons_self)
  have hpo := Shape.payload_add_size_le _ _ hmem
  have hsh : (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post)).length ≤ 256 := by simpa using hn
  have htb := Shape.tagBytes_le_payloadOffset (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post))
  rw [tagBytes_one hsh] at htb
  have hmode : modeOf (@Ty.mk S (Data.sum _ cover)) (@Ty.mk S (Data.sum _ cover)) = .whole := by
    show (if _ then _ else _) = _
    simp [Variants.shapes] at hk ⊢; omega
  refine ⟨hpo, by show 1 ≤ (Shape.sum _).size; omega, by rw [hmode], fun x bs hx => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨hp, hpre⟩ := hinl x a ha
    have hr := (Variants.reprAt_skip _ 0 pre _ _ bs hpre).mp hx.2
    simp only [Variants.reprAt, hp, Nat.zero_add] at hr
    refine ⟨?_, hr.2⟩
    rw [head_of_sumRepr hsh hr, tag_eq_iff (by simp at hn; omega) (by simp at hn; omega)]
  · intro b hb
    obtain ⟨rfl, hp⟩ := hinr x b hb
    refine ⟨Variants.tag_ne pre post _ b bs hn hx.2 hp, fun qb _ hq => ?_⟩
    rw [hmode] at hq
    cases hq
    exact hx

/-- The law of the split of a two-variant sum, in the mode `payload`. It tests variant 0 and
hands back the payload of variant 1 otherwise. -/
theorem SplitLaw.pair {S : Type} [inst : Data S] {P Q : Ty} (proj : S → Option P.carrier)
    (proj' : S → Option Q.carrier) (cover : ∀ s, ∃ v ∈ [(⟨proj⟩ : Variant S), ⟨proj'⟩], (v.proj s).isSome)
    (hinst : inst = Data.sum _ cover) (split : S → P.carrier ⊕ Q.carrier)
    (hinl : ∀ x a, split x = .inl a → proj x = some a)
    (hinr : ∀ x b, split x = .inr b → proj x = none ∧ proj' x = some b) :
    SplitLaw ⟨S⟩ P Q 0 split := by
  subst hinst
  have hmem : Data.shape P.carrier ∈ Variants.shapes [(⟨proj⟩ : Variant S), ⟨proj'⟩] := by
    simp [Variants.shapes]
  have hmem' : Data.shape Q.carrier ∈ Variants.shapes [(⟨proj⟩ : Variant S), ⟨proj'⟩] := by
    simp [Variants.shapes]
  have hpo := Shape.payload_add_size_le _ _ hmem
  have hpo' := Shape.payload_add_size_le _ _ hmem'
  have hsh : (Variants.shapes [(⟨proj⟩ : Variant S), ⟨proj'⟩]).length ≤ 256 := by simp
  have htb := Shape.tagBytes_le_payloadOffset (Variants.shapes [(⟨proj⟩ : Variant S), ⟨proj'⟩])
  rw [tagBytes_one hsh] at htb
  have hmode : modeOf (@Ty.mk S (Data.sum _ cover)) Q = .payload := by
    unfold modeOf
    split
    · next vs vs' h1 _ => cases h1; simp [Variants.shapes]
    · rfl
  refine ⟨hpo, by show 1 ≤ (Shape.sum _).size; omega, by rw [hmode]; exact hpo',
    fun x bs hx => ⟨?_, ?_⟩⟩
  · intro a ha
    have hp := hinl x a ha
    have hr : Variants.reprAt _ 0 [(⟨proj⟩ : Variant S), ⟨proj'⟩] x bs := hx.2
    simp only [Variants.reprAt, hp] at hr
    refine ⟨?_, hr.2⟩
    rw [head_of_sumRepr hsh hr, tag_eq_iff (by omega) (by omega)]
  · intro b hb
    obtain ⟨hp, hp'⟩ := hinr x b hb
    refine ⟨Variants.tag_ne [] [⟨proj'⟩] _ x bs (by simp) hx.2 hp, fun qb _ hq => ?_⟩
    rw [hmode] at hq
    have hr : Variants.reprAt _ 0 [(⟨proj⟩ : Variant S), ⟨proj'⟩] x bs := hx.2
    simp only [Variants.reprAt, hp, hp'] at hr
    cases hq
    exact hr.2

/-- The law of a split whose rest is `Unit`, in the mode `payload`, which `deriving Data` uses
as the last test of its chain for three or more variants. It tests variant `i` of `Data.sum vs`,
for at most 256 variants, whose projection gives the payload of a value that no earlier variant
matches. -/
theorem SplitLaw.unit {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) {P : Ty} (pre post : List (Variant S))
    (proj : S → Option P.carrier) (hvs : vs = pre ++ (⟨proj⟩ : Variant S) :: post)
    (i : Nat) (hi : pre.length = i) (split : S → P.carrier ⊕ Unit)
    (hinl : ∀ x a, split x = .inl a →
      proj x = some a ∧ pre.all (fun w => (w.proj x).isNone) = true)
    (hinr : ∀ x b, split x = .inr b → proj x = none) :
    SplitLaw ⟨S⟩ P Ty.unit i split := by
  subst hvs hinst hi
  have hmem : Data.shape P.carrier ∈ Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post) :=
    List.mem_map_of_mem (f := Variant.shape) (List.mem_append_right _ List.mem_cons_self)
  have hpo := Shape.payload_add_size_le _ _ hmem
  have hsh : (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post)).length ≤ 256 := by simpa using hn
  have htb := Shape.tagBytes_le_payloadOffset (Variants.shapes (pre ++ (⟨proj⟩ : Variant S) :: post))
  rw [tagBytes_one hsh] at htb
  have hmode : modeOf (@Ty.mk S (Data.sum _ cover)) Ty.unit = .payload := by
    unfold modeOf; split
    · next h => cases h
    · rfl
  refine ⟨hpo, by show 1 ≤ (Shape.sum _).size; omega,
    by rw [hmode]; show Shape.payloadOffset _ + 0 ≤ (Shape.sum _).size; omega, fun x bs hx => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨hp, hpre⟩ := hinl x a ha
    have hr := (Variants.reprAt_skip _ 0 pre _ _ bs hpre).mp hx.2
    simp only [Variants.reprAt, hp, Nat.zero_add] at hr
    refine ⟨?_, hr.2⟩
    rw [head_of_sumRepr hsh hr, tag_eq_iff (by simp at hn; omega) (by simp at hn; omega)]
  · intro b hb
    exact ⟨Variants.tag_ne pre post _ x bs hn hx.2 (hinr x b hb), fun qb hl _ => ⟨hl, trivial⟩⟩

/-! ## Sums: the forms `deriving Data` uses, with variant `i` given by its index -/

theorem list_split_at {α : Type 1} (vs : List α) (i : Nat) (v : α) (h : vs[i]? = some v) :
    vs = vs.take i ++ v :: vs.drop (i + 1) ∧ (vs.take i).length = i := by
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨?_, by simp; omega⟩
  conv => lhs; rw [← List.take_append_drop i vs]
  rw [List.drop_eq_getElem_cons hi, hv]

/-- `CtorLaw.variant` with variant `i` given by `vs[i]?`. -/
theorem CtorLaw.variantAt {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) {P : Ty} (i : Nat) (proj : S → Option P.carrier)
    (hvs : vs[i]? = some (⟨proj⟩ : Variant S)) (build : Env [P] → S)
    (hpre : ∀ env, (vs.take i).all (fun w => (w.proj (build env)).isNone) = true)
    (hproj : ∀ env, proj (build env) = some (env.get .here)) :
    CtorLaw [P] ⟨S⟩ (.variant i) build :=
  have h := list_split_at vs i _ hvs
  CtorLaw.variant vs cover hinst hn _ _ proj h.1 i h.2 build hpre hproj

/-- `SplitLaw.whole` with variant `i` given by `vs[i]?`. -/
theorem SplitLaw.wholeAt {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) (hk : 2 < vs.length) {P : Ty} (i : Nat)
    (proj : S → Option P.carrier) (hvs : vs[i]? = some (⟨proj⟩ : Variant S))
    (split : S → P.carrier ⊕ S)
    (hinl : ∀ x a, split x = .inl a →
      proj x = some a ∧ (vs.take i).all (fun w => (w.proj x).isNone) = true)
    (hinr : ∀ x b, split x = .inr b → b = x ∧ proj x = none) :
    SplitLaw ⟨S⟩ P ⟨S⟩ i split :=
  have h := list_split_at vs i _ hvs
  SplitLaw.whole vs cover hinst hn hk _ _ proj h.1 i h.2 split hinl hinr

/-- `SplitLaw.unit` with variant `i` given by `vs[i]?`. -/
theorem SplitLaw.unitAt {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hn : vs.length ≤ 256) {P : Ty} (i : Nat)
    (proj : S → Option P.carrier) (hvs : vs[i]? = some (⟨proj⟩ : Variant S))
    (split : S → P.carrier ⊕ Unit)
    (hinl : ∀ x a, split x = .inl a →
      proj x = some a ∧ (vs.take i).all (fun w => (w.proj x).isNone) = true)
    (hinr : ∀ x b, split x = .inr b → proj x = none) :
    SplitLaw ⟨S⟩ P Ty.unit i split :=
  have h := list_split_at vs i _ hvs
  SplitLaw.unit vs cover hinst hn _ _ proj h.1 i h.2 split hinl hinr

/-- `SplitLaw.pair` with the variants given by `vs[0]?` and `vs[1]?`. -/
theorem SplitLaw.pairAt {S : Type} [inst : Data S] (vs : List (Variant S))
    (cover : ∀ s, ∃ v ∈ vs, (v.proj s).isSome) (hinst : inst = Data.sum vs cover)
    (hk : vs.length = 2) {P Q : Ty} (proj : S → Option P.carrier) (proj' : S → Option Q.carrier)
    (hv0 : vs[0]? = some (⟨proj⟩ : Variant S)) (hv1 : vs[1]? = some (⟨proj'⟩ : Variant S))
    (split : S → P.carrier ⊕ Q.carrier)
    (hinl : ∀ x a, split x = .inl a → proj x = some a)
    (hinr : ∀ x b, split x = .inr b → proj x = none ∧ proj' x = some b) :
    SplitLaw ⟨S⟩ P Q 0 split := by
  match vs, hk, hv0, hv1, cover, hinst with
  | [_, _], _, hv0, hv1, cover, hinst =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hv0 hv1
    subst hv0 hv1
    exact SplitLaw.pair proj proj' cover hinst split hinl hinr

end Millipede.Flat

namespace Millipede

/-- The constructor that builds the tuple `(a, m₁, …, mₖ)` of `Ty.tup (t :: ts)` at once. A
function with `&mut` parameters, or a loop body, hands back such a tuple of its result `a` and the
final values of its references or carried variables. The memory lowering writes only `a`,
because the other values are already in place. -/
def Ctor.tupMk (t : Ty) (ts : List Ty) : Ctor (t :: ts) (.tup (t :: ts)) :=
  ⟨"tuple", .tuple, Flat.tupBuild (t :: ts), some ⟨Flat.CtorLaw.tuple t ts⟩,
    some ⟨Flat.tupBuild_occs (t :: ts)⟩⟩

/-- The loop `Exp.loop` with no carried variables, whose body hands back only its new
accumulator and whose continuation returns the final accumulator. It denotes
`for i in [0:n] do if !c then break; acc := body`, followed by `acc`. -/
abbrev Exp.loop0 {Γ : List Ty} {s : Ty} (n : Nat) (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) s) : Exp Γ s :=
  .loop n .nil init c (.let_ body (.mk (Ctor.tupMk s []) (.cons (.var .here) .nil)))
    (.atom (.var .here))

end Millipede
