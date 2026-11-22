import Millipede.Compile.LowerProof
import Millipede.Core.WfSound

/-!
# Invariants and hypotheses of the memory refinement

This module defines what the refinement theorem of `lower` is stated with. Every variable has a
static location `Loc` and, at run time, the absolute address of its value and possibly a hole,
which the structure `SI` records. A hole is the place that a variable has lent with `&mut`. The
lender is outside the borrow's block, so it is read-only while the hole exists. The theorem uses
four kinds of hypothesis:

* The layout `Lay bp n Γ ρ S W` says that the variables' slots lie below the watermark `n` and are
  pairwise disjoint, that an owned variable's value is its slot, that a referenced value lies below
  `bp + n` and away from every reference slot, and that the storage of a writable variable overlaps
  no other variable's storage except inside that variable's hole. `HoleOK` records that a place of
  the lender whose path does not overlap the lent path is outside the hole.
* The representation `MEnvRel h bp env ρ S` says that the bytes at each variable's address
  represent its value, except inside its hole, and that each reference slot holds its address.
  Inside the hole the lent place lives on as the borrow binder's storage, and the lender's value
  there is stale until the borrow ends, which the borrow checker makes unobservable.
* The restraint `Exp.Restr e W` is the block rule as the lowering needs it. `W` marks the
  variables that `e` may write; a `let`'s bound term, a loop, a borrow body and a callee may not
  write variables bound outside them, and a `&` binder is never written. `Exp.check` implies it.
* The lawfulness `Exp.Lawful e` says that the building blocks of the term agree with the layouts.
  A lens reads and splices the field's bytes at `lensOff`, and its target's shape is the field's
  shape, so distinct fields are disjoint storage. A constructor's value is represented by any bytes
  that hold its arguments at its plan's offsets, and a split's tag test and payloads match the sum
  layout. `compile` refuses a building block without a certificate.

A destination is a region away from every slot and every value. The proof method is described in
doc/design/compiler.md.
-/

namespace Millipede.Flat

/-! ## Run-time knowledge of the variables -/

/-- The storage `[a, a + len)` of a place lent with `&mut`, which is a hole in the lender's value,
and the place's path. -/
structure Hole where
  a : Nat
  len : Nat
  path : List Sel

/-- What the refinement knows of a variable at run time: the address of its value, the lent place
while it is lent with `&mut`, and the extent of a slice view. A slice view is a pointer and a length
at the machine, so only its first `e` bytes, its first `len` elements, are its storage, and the
rest of its nominal `Slots` layout belongs to others. -/
structure SI where
  A : Nat
  hole : Option Hole := none
  ext : Option Nat := none
  /-- For a reference to the pair of elements `p[i], p[j]` borrowed together, `some (f, A2)` says
  that the value's bytes from `f` on, its second component, live at `A2`, and its first `f` bytes
  at `A`. -/
  snd : Option (Nat × Nat) := none

instance : Inhabited SI := ⟨⟨0, none, none, none⟩⟩

/-- The bytes of a variable's storage, out of `n` nominal ones: all of them, or its extent. -/
def SI.lim (s : SI) (n : Nat) : Nat :=
  match s.ext with
  | none => n
  | some e => min e n


theorem SI.lim_le (s : SI) (n : Nat) : s.lim n ≤ n := by
  unfold SI.lim; split <;> omega

@[simp] theorem SI.lim_mk_none (A : Nat) (H : Option Hole) (P : Option (Nat × Nat)) (n : Nat) :
    (SI.mk A H none P).lim n = n := rfl

/-- The bytes of the storage of a variable of type `t`. -/
def SI.sz (s : SI) (t : Ty) : Nat := s.lim t.size

theorem SI.sz_le (s : SI) (t : Ty) : s.sz t ≤ t.size := s.lim_le t.size

theorem SI.sz_none {s : SI} (h : s.ext = none) (t : Ty) : s.sz t = t.size := by
  simp [SI.sz, SI.lim, h]

@[simp] theorem SI.sz_mk_none (A : Nat) (H : Option Hole) (P : Option (Nat × Nat)) (t : Ty) :
    (SI.mk A H none P).sz t = t.size := rfl

/-- The address of byte `k` of a variable's value: `A + k`, except for a reference to the pair
`p[i], p[j]` with `snd = some (f, A2)`, whose bytes from `f` on live at `A2`. -/
def SI.at (s : SI) (k : Nat) : Nat :=
  match s.snd with
  | none => s.A + k
  | some (f, A2) => if k < f then s.A + k else A2 + (k - f)

theorem SI.at_none {s : SI} (h : s.snd = none) (k : Nat) : s.at k = s.A + k := by
  simp [SI.at, h]

/-- A slice view's value with extent `e`, as a `Slots` value whose full cells are the viewed
elements. Its full cells are exactly its first `len`, which fill its first `e = len · size` bytes.
The statement goes through the type's `Data` instance only, so it means the same whatever the
element type is called where the view is used. -/
def ViewOK (t : Ty) (v : t.carrier) (e : Nat) : Prop :=
  ∃ (cnt len : Nat) (sh : Shape), t.data.shape = .slots cnt sh ∧ len ≤ cnt ∧ e = len * sh.size ∧
    Data.occs v = [some ((List.range cnt).map fun k => decide (k < len))]

/-- `x ∈ [a, a + len)`. -/
def InR (a len x : Nat) : Prop := a ≤ x ∧ x < a + len

instance (a len x : Nat) : Decidable (InR a len x) := inferInstanceAs (Decidable (_ ∧ _))

/-- `x` is in the variable's hole. -/
def SI.inHole (s : SI) (x : Nat) : Prop :=
  match s.hole with
  | none => False
  | some H => InR H.a H.len x

/-- `x` is in the storage of a variable of type `t`: it is the address of one of its bytes, or of
its extent for a view. -/
def SI.In (s : SI) (t : Ty) (x : Nat) : Prop := ∃ k, k < s.sz t ∧ s.at k = x

instance (s : SI) (t : Ty) (x : Nat) : Decidable (s.In t x) :=
  inferInstanceAs (Decidable (∃ k, k < s.sz t ∧ s.at k = x))

theorem SI.In_none {s : SI} (h : s.snd = none) {t : Ty} {x : Nat} :
    s.In t x ↔ InR s.A (s.sz t) x := by
  simp only [SI.In, SI.at_none h, InR]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro hx; exact ⟨x - s.A, by omega, by omega⟩

@[simp] theorem SI.In_mk {A : Nat} {H : Option Hole} {E : Option Nat} {t : Ty} {x : Nat} :
    (SI.mk A H E none).In t x ↔ InR A ((SI.mk A H E none).sz t) x := SI.In_none rfl

theorem SI.In_at {s : SI} {t : Ty} {k : Nat} (hk : k < s.sz t) : s.In t (s.at k) := ⟨k, hk, rfl⟩

/-- The storage of a variable, both pieces for a pair reference, is away from `[a, a + len)`. -/
def SI.Out (s : SI) (t : Ty) (a len : Nat) : Prop :=
  match s.snd with
  | none => Disj a len s.A (s.sz t)
  | some (f, A2) => Disj a len s.A f ∧ Disj a len A2 (s.sz t - f)

theorem SI.Out_none {s : SI} (h : s.snd = none) {t : Ty} {a len : Nat} :
    s.Out t a len ↔ Disj a len s.A (s.sz t) := by
  simp [SI.Out, h]

@[simp] theorem SI.Out_mk {A : Nat} {H : Option Hole} {E : Option Nat} {t : Ty} {a len : Nat} :
    (SI.mk A H E none).Out t a len ↔ Disj a len A ((SI.mk A H E none).sz t) := Iff.rfl

theorem SI.Out.not_In {s : SI} {t : Ty} {a len x : Nat} (ho : s.Out t a len) (hx : InR a len x) :
    ¬ s.In t x := by
  rintro ⟨k, hk, rfl⟩
  unfold SI.Out at ho
  unfold SI.at at hx
  split at ho
  · rename_i hs; simp only [hs] at hx; unfold Disj at ho; unfold InR at hx; omega
  · rename_i f A2 hs
    simp only [hs] at hx
    split at hx
    · unfold Disj at ho; unfold InR at hx; omega
    · unfold Disj at ho; unfold InR at hx; omega

/-- The storage of a variable, both pieces for a pair reference, ends below `L`. -/
def SI.Below (s : SI) (t : Ty) (L : Nat) : Prop :=
  match s.snd with
  | none => s.A + s.sz t ≤ L
  | some (f, A2) => s.A + f ≤ L ∧ A2 + (s.sz t - f) ≤ L

theorem SI.Below.mono {s : SI} {t : Ty} {L L' : Nat} (h : s.Below t L) (hL : L ≤ L') :
    s.Below t L' := by
  unfold SI.Below at *; split at h <;> omega

theorem SI.Below.out {s : SI} {t : Ty} {L a len : Nat} (h : s.Below t L) (ha : L ≤ a) :
    s.Out t a len := by
  unfold SI.Below SI.Out Disj at *
  cases hs : s.snd with
  | none => simp only [hs] at h ⊢; omega
  | some p => obtain ⟨f, A2⟩ := p; simp only [hs] at h ⊢; omega

theorem SI.Below.lt {s : SI} {t : Ty} {L x : Nat} (h : s.Below t L) (hx : s.In t x) : x < L := by
  obtain ⟨k, hk, rfl⟩ := hx
  unfold SI.Below SI.at at *
  cases hs : s.snd with
  | none => simp only [hs] at h ⊢; omega
  | some p => obtain ⟨f, A2⟩ := p; simp only [hs] at h ⊢; split <;> omega

/-- `[a, a + len)` lies inside one piece of a variable's storage. -/
def SI.Holds (s : SI) (t : Ty) (a len : Nat) : Prop :=
  match s.snd with
  | none => s.A ≤ a ∧ a + len ≤ s.A + s.sz t
  | some (f, A2) => (s.A ≤ a ∧ a + len ≤ s.A + min f (s.sz t)) ∨ (A2 ≤ a ∧ a + len ≤ A2 + (s.sz t - f))

theorem SI.Out.holds {s : SI} {t : Ty} {a len b lb : Nat} (ho : s.Out t a len)
    (hh : s.Holds t b lb) : Disj a len b lb := by
  unfold SI.Out at ho; unfold SI.Holds at hh; unfold Disj at *
  cases hs : s.snd with
  | none => simp only [hs] at ho hh; omega
  | some q =>
    obtain ⟨f, A2⟩ := q
    simp only [hs] at ho hh
    rcases hh with hh | hh <;> omega

theorem SI.Holds.sub {s : SI} {t : Ty} {a len a' len' : Nat} (h : s.Holds t a len) (h1 : a ≤ a')
    (h2 : a' + len' ≤ a + len) : s.Holds t a' len' := by
  unfold SI.Holds at *
  cases hs : s.snd with
  | none => simp only [hs] at h ⊢; omega
  | some q => obtain ⟨f, A2⟩ := q; simp only [hs] at h ⊢; omega

theorem SI.Holds.In {s : SI} {t : Ty} {b lb x : Nat} (hh : s.Holds t b lb) (hx : InR b lb x) :
    s.In t x := by
  unfold SI.Holds at hh; unfold InR at hx
  cases hs : s.snd with
  | none =>
    simp only [hs] at hh
    exact ⟨x - s.A, by omega, by rw [SI.at_none hs]; omega⟩
  | some q =>
    obtain ⟨f, A2⟩ := q
    simp only [hs] at hh
    rcases hh with hh | hh
    · exact ⟨x - s.A, by omega, by simp only [SI.at, hs]; rw [ite_eq_left (by omega)]; omega⟩
    · exact ⟨f + (x - A2), by omega, by simp only [SI.at, hs]; rw [ite_eq_right (by omega)]; omega⟩

/-- The pointer slot of a location: none for an owned value, `8` bytes at its offset for a
reference, and `16` for a reference to a pair of elements. -/
def Loc.ptr : Loc → Option (Nat × Nat)
  | .own _ => none
  | .slot _ _ _ => none
  | .ref o => some (o, 8)
  | .ref2 o => some (o, 16)

@[simp] theorem Loc.ptr_own (o : Nat) : (Loc.own o).ptr = none := rfl
@[simp] theorem Loc.ptr_slot (o k n : Nat) : (Loc.slot o k n).ptr = none := rfl
@[simp] theorem Loc.ptr_ref (o : Nat) : (Loc.ref o).ptr = some (o, 8) := rfl
@[simp] theorem Loc.ptr_ref2 (o : Nat) : (Loc.ref2 o).ptr = some (o, 16) := rfl

theorem Loc.ptr_size {l : Loc} {o w : Nat} (h : l.ptr = some (o, w)) (t : Ty) :
    l.off = o ∧ l.size t = w := by
  cases l <;> simp [Loc.ptr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

/-! ## Places: roots, offsets, alignment -/

/-- The type of the root variable of a place. -/
def _root_.Millipede.Place.rootTy {Γ : List Ty} : {t : Ty} → Place Γ t → Ty
  | t, .var _ => t
  | _, .field p _ => p.rootTy
  | _, .index (dflt := _) p _ => p.rootTy
  | _, .slot (dflt := _) p _ => p.rootTy
  | _, .range p _ _ => p.rootTy
  | _, .pair2 (dflt := _) p _ _ => p.rootTy
  | _, .rangeS (t := t) (n := n) _ _ _ => .slots t n
  | _, .pair2S (t := t) (n := n) (dflt := _) _ _ _ => .slots t n

/-- The offset of a contiguous place inside its root variable. -/
def _root_.Millipede.Place.off {Γ : List Ty} : {t : Ty} → Place Γ t → Env Γ → Nat
  | _, .var _, _ => 0
  | _, .field p l, env => p.off env + lensOff l
  | _, .index (t := t) (dflt := _) p i, env => p.off env + (i.denote env).toNat * t.size
  | _, .slot (t := t) (dflt := _) p i, env => p.off env + (i.denote env).toNat * t.size
  | _, _, _ => 0

/-- A lens's target is its field: field number `index` of the structure has the target's shape. -/
def _root_.Millipede.Lens.Aligned {s t : Ty} (l : Lens s t) : Prop :=
  ∃ fs, s.data.shape = .prod fs ∧ fs[l.index]? = some t.data.shape

/-- `Lens.Aligned`, decided. -/
def _root_.Millipede.Lens.aligned {s t : Ty} (l : Lens s t) : Bool :=
  match s.data.shape with
  | .prod fs => match fs[l.index]? with
    | some sh => Shape.eqb sh t.data.shape
    | none => false
  | _ => false

theorem _root_.Millipede.Lens.aligned_spec {s t : Ty} (l : Lens s t) (h : l.aligned = true) :
    l.Aligned := by
  unfold Lens.aligned at h
  split at h
  · rename_i fs hfs
    split at h
    · rename_i sh hsh
      exact ⟨fs, hfs, by rw [hsh, Shape.eqb_spec _ _ h]⟩
    · cases h
  · cases h

/-! ## Lawful building blocks -/

/-- A lens agrees with the layout: the field is at `lensOff l` inside the struct, `get` reads
its bytes, `set` splices them, and the target's shape is the field's. -/
def _root_.Millipede.Lens.Lawful {s t : Ty} (l : Lens s t) : Prop :=
  (lensOff l + t.size ≤ s.size ∧
  (∀ (x : s.carrier) (bs : List UInt8), Data.reprBytes x bs →
    Data.reprBytes (l.get x) (slice bs (lensOff l) t.size)) ∧
  (∀ (x : s.carrier) (v : t.carrier) (bs vb : List UInt8), Data.reprBytes x bs →
    Data.reprBytes v vb → Data.reprBytes (l.set x v) (splice bs (lensOff l) vb))) ∧
  l.Aligned

/-- Every lens of a place is lawful. -/
def _root_.Millipede.Place.Lawful {Γ : List Ty} : {t : Ty} → Place Γ t → Prop
  | _, .var _ => True
  | _, .field p l => p.Lawful ∧ l.Lawful
  | _, .index (dflt := _) p _ => p.Lawful
  | _, .slot (dflt := _) p _ => p.Lawful
  | _, .range p _ _ => p.Lawful
  | _, .pair2 (dflt := _) p _ _ => p.Lawful
  | _, .rangeS _ _ _ => True
  | _, .pair2S (dflt := _) _ _ _ => True

/-- The argument places of a reference call are lawful. -/
def _root_.Millipede.RArgs.Lawful {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own _ as => as.Lawful
  | _, _, .shr p as => p.Lawful ∧ as.Lawful
  | _, _, .mut p as => p.Lawful ∧ as.Lawful

/-- The array places of an extern call's slices are lawful. -/
def _root_.Millipede.EArgs.Lawful {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Prop
  | _, .nil => True
  | _, .word _ as => as.Lawful
  | _, .bufIn (.const _) as => as.Lawful
  | _, .bufIn (.slice a _ _) as => a.Lawful ∧ as.Lawful
  | _, .bufOut as => as.Lawful
  | _, .sliceOut a _ _ as => a.Lawful ∧ as.Lawful

/-- The roots of an extern call's mutable slices are writable. -/
def _root_.Millipede.EArgs.outW {Γ : List Ty} (W : List Bool) : {ps : List ExtParam} → EArgs Γ ps → Prop
  | _, .nil => True
  | _, .word _ as => as.outW W
  | _, .bufIn _ as => as.outW W
  | _, .bufOut as => as.outW W
  | _, .sliceOut a _ _ as => W.getD a.root false = true ∧ as.outW W

/-- A constructor agrees with the layout: its placements are inside the value, pairwise disjoint and
after the tag byte, and any bytes that hold the arguments and the tag represent the built value. -/
def _root_.Millipede.Ctor.Lawful {ps : List Ty} {t : Ty} (c : Ctor ps t) : Prop :=
  (∀ q ∈ placements ps c.plan.1, q.1 + q.2 ≤ t.size ∧ (c.plan.2.isSome → 1 ≤ q.1)) ∧
  (placements ps c.plan.1).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) ∧
  (c.plan.2.isSome → 1 ≤ t.size) ∧
  ∀ (env : Env ps) (bs : List UInt8), bs.length = t.size → TagAt c.plan.2 bs →
    ArgsAt c.plan.1 env bs → Data.reprBytes (c.build env) bs

/-- A split agrees with the sum layout: the tag byte decides the arm, the payload of the tested
variant is at the payload offset, and the rest is built by `RestOk`. -/
def _root_.Millipede.Split.Lawful {t p q : Ty} (sp : Split t p q) : Prop :=
  payloadOff t.data.shape + p.size ≤ t.size ∧ 1 ≤ t.size ∧
  (match sp.mode with
   | .payload => payloadOff t.data.shape + q.size ≤ t.size
   | .whole => q.size = t.size
   | .retag po' m => 1 ≤ po' ∧ po' + m ≤ q.size ∧ payloadOff t.data.shape + m ≤ t.size) ∧
  ∀ (x : t.carrier) (bs : List UInt8), Data.reprBytes x bs →
    (∀ a, sp.split x = .inl a → (bs.headD 0).toUInt64 = UInt64.ofNat sp.tag ∧
      Data.reprBytes a (slice bs (payloadOff t.data.shape) p.size)) ∧
    (∀ b, sp.split x = .inr b → (bs.headD 0).toUInt64 ≠ UInt64.ofNat sp.tag ∧
      ∀ qb, qb.length = q.size → RestOk sp.mode sp.tag (payloadOff t.data.shape) q.size bs qb →
        Data.reprBytes b qb)

/-- Every building block of a term, callees included, is lawful. -/
def _root_.Millipede.Exp.Lawful : {Γ : List Ty} → {t : Ty} → Exp Γ t → Prop
  | _, _, .atom _ => True
  | _, _, .let_ e₁ e₂ => e₁.Lawful ∧ e₂.Lawful
  | _, _, .ite _ e₁ e₂ => e₁.Lawful ∧ e₂.Lawful
  | _, _, .prim _ _ => True
  | _, _, .call _ body _ => body.Lawful
  | _, _, .ok _ => True
  | _, _, .err _ => True
  | _, _, .match_ _ eE eO => eE.Lawful ∧ eO.Lawful
  | _, _, .ext _ args => args.Lawful
  | _, _, .extMut _ args k => args.Lawful ∧ k.Lawful
  | _, _, .mk c _ => c.Lawful
  | _, _, .read p => p.Lawful
  | _, _, .assign p _ k => p.Lawful ∧ k.Lawful
  | _, _, .case _ sp eP eQ => sp.Lawful ∧ eP.Lawful ∧ eQ.Lawful
  | _, _, .put p _ _ k => p.Lawful ∧ k.Lawful
  | _, _, .take (dflt := _) p _ k => p.Lawful ∧ k.Lawful
  | _, _, .borrowShr p body k => p.Lawful ∧ body.Lawful ∧ k.Lawful
  | _, _, .borrowMut p body k => p.Lawful ∧ body.Lawful ∧ k.Lawful
  | _, _, .callRef _ _ body args k => args.Lawful ∧ body.Lawful ∧ k.Lawful
  | _, _, .guard g =>
    match g with
    | .valid p _ => p.Lawful
  | _, _, .loop _ _ _ c body k => c.Lawful ∧ body.Lawful ∧ k.Lawful

/-! ## Layout -/

/-- `x` is in the storage of a writable variable, where `W` marks the writable ones. -/
def InW : List Ty → List SI → List Bool → Nat → Prop
  | t :: ts, s :: S, W, x => (W.headD false = true ∧ s.In t x) ∨ InW ts S W.tail x
  | _, _, _, _ => False

/-- `[o, o + sz)`, relative to `bp`, is away from every slot and every value. -/
def Away (bp o sz : Nat) : List Ty → List Loc → List SI → Prop
  | t :: ts, l :: ρ, s :: S =>
    Disj o sz l.off (l.size t) ∧ s.Out t (bp + o) sz ∧ Away bp o sz ts ρ S
  | _, _, _ => True

/-- A hole's guarantee: every contiguous place of the lender, in any context and environment, whose
path does not overlap the lent path is outside the hole. -/
def HoleOK (s : SI) (T : Ty) (H : Hole) : Prop :=
  ∀ {Γ' : List Ty} {t' : Ty} (q : Place Γ' t') (env' : Env Γ'), q.rootTy = T →
    q.contig = true → q.Lawful → q.ok env' → Sel.overlap H.path q.path = false →
    ∀ k, k < t'.size → ¬ InR H.a H.len (s.at (q.off env' + k))

/-- A reference to the pair of elements `p[i], p[j]`. Its type is a pair of two fields of one shape
`sh`, its first `sh.size` bytes are at `A` and the others at `A2`, in two disjoint pieces. It has an
extent, its whole size, so that it is used only through its fields, as a slice view is used only
through its elements. -/
def PairSI (t : Ty) (s : SI) : Prop :=
  ∃ (sh : Shape) (A2 : Nat), t.data.shape = .prod [sh, sh] ∧ s.snd = some (sh.size, A2) ∧
    s.ext = some t.size ∧ Disj s.A sh.size A2 sh.size

/-- The layout of a pair of two fields of one shape: the second field is at `sh.size` and the whole
has size `2 · sh.size`, with no padding because a shape's alignment divides its size. -/
theorem pairShape (sh : Shape) :
    Shape.fieldOffset [sh, sh] 1 = sh.size ∧ (Shape.prod [sh, sh]).size = 2 * sh.size := by
  have ha := Shape.align_pos sh
  have hd := Shape.align_dvd_size sh
  have e1 : alignUp sh.size sh.align = sh.size := alignUp_of_dvd hd ha
  have hm : Shape.alignMax [sh, sh] = sh.align := by
    simp only [Shape.alignMax]; omega
  have hd2 : sh.align ∣ sh.size + sh.size := Nat.dvd_add hd hd
  refine ⟨?_, ?_⟩
  · simp [Shape.fieldOffset, Shape.prodOffsets, alignUp_zero, e1]
  · simp only [Shape.size, Shape.prodEnd, alignUp_zero, Nat.zero_add, e1, hm]
    rw [alignUp_of_dvd hd2 ha]; omega

/-- A pair reference's facts, unfolded. -/
theorem PairSI.facts {t : Ty} {s : SI} (h : PairSI t s) :
    ∃ (f A2 : Nat), s.snd = some (f, A2) ∧ s.ext = some t.size ∧ t.size = 2 * f ∧
      Disj s.A f A2 f := by
  obtain ⟨sh, A2, hsh, hs, he, hd⟩ := h
  refine ⟨sh.size, A2, hs, he, ?_, hd⟩
  show t.data.shape.size = _
  rw [hsh]; exact (pairShape sh).2

/-- The storage of a pair reference is its whole size, since its extent is its size. -/
theorem PairSI.sz {t : Ty} {s : SI} (h : PairSI t s) : s.sz t = t.size := by
  obtain ⟨_, _, _, he, _⟩ := h.facts
  simp [SI.sz, SI.lim, he]

/-- A variable's run-time knowledge is well formed for its type: one piece, or a pair reference. -/
def SI.Ok (s : SI) (t : Ty) : Prop := s.snd = none ∨ PairSI t s

/-- Distinct bytes of a variable live at distinct addresses. -/
theorem SI.at_inj {s : SI} {t : Ty} (hs : s.Ok t) {i j : Nat} (hi : i < t.size) (hj : j < t.size)
    (h : s.at i = s.at j) : i = j := by
  rcases hs with hs | hs
  · rw [SI.at_none hs, SI.at_none hs] at h; omega
  · obtain ⟨f, A2, hsn, _, hsz, hd⟩ := hs.facts
    simp only [SI.at, hsn] at h
    unfold Disj at hd
    split at h <;> split at h <;> omega

/-- The address of the byte at offset `o` of a variable's value, reached through its field number
`fi` as the code computes it. A pair reference's second field is at `A2`. -/
def SI.addr (s : SI) (fi o : Nat) : Nat :=
  match s.snd with
  | none => s.A + o
  | some (f, A2) => if fi = 1 then A2 + (o - f) else s.A + o

/-- The facts about one variable, with slot `l`, run-time knowledge `s` and writable flag `w`. -/
def Single (bp n : Nat) (t : Ty) (l : Loc) (s : SI) (w : Bool) : Prop :=
  l.off + l.size t ≤ n ∧
  (match l with
   | .own o | .slot o _ _ => s.A = bp + o ∧ s.ext = none ∧ s.snd = none
   | .ref o => s.snd = none ∧ s.A + s.sz t ≤ bp + n ∧ Disj (bp + o) 8 s.A (s.sz t)
   | .ref2 o => PairSI t s ∧ s.Below t (bp + n) ∧ s.Out t (bp + o) 16) ∧
  (w = true → s.hole = none) ∧
  (∀ H, s.hole = some H → (∀ x, InR H.a H.len x → s.In t x) ∧ HoleOK s t H)

/-- The facts about two distinct variables: their slots are disjoint, a pointer slot is away from
the other value, and a writable variable's storage overlaps the other's only in the other's hole. -/
def Compat (bp : Nat) (t : Ty) (l : Loc) (s : SI) (w : Bool) (t' : Ty) (l' : Loc) (s' : SI)
    (w' : Bool) : Prop :=
  Disj l.off (l.size t) l'.off (l'.size t') ∧
  (∀ o w, l.ptr = some (o, w) → s'.Out t' (bp + o) w) ∧
  (∀ o w, l'.ptr = some (o, w) → s.Out t (bp + o) w) ∧
  (w = true → ∀ x, s.In t x → s'.In t' x → s'.inHole x) ∧
  (w' = true → ∀ x, s'.In t' x → s.In t x → s.inHole x)

/-- `Compat` of one variable with every later one. -/
def CompatAll (bp : Nat) (t : Ty) (l : Loc) (s : SI) (w : Bool) :
    List Ty → List Loc → List SI → List Bool → Prop
  | t' :: ts, l' :: ρ, s' :: S, W =>
    Compat bp t l s w t' l' s' (W.headD false) ∧ CompatAll bp t l s w ts ρ S W.tail
  | _, _, _, _ => True

/-- The layout invariant, described in the module doc. -/
def Lay (bp n : Nat) : List Ty → List Loc → List SI → List Bool → Prop
  | [], [], [], _ => True
  | t :: ts, l :: ρ, s :: S, W =>
    Single bp n t l s (W.headD false) ∧ CompatAll bp t l s (W.headD false) ts ρ S W.tail ∧
      Lay bp n ts ρ S W.tail
  | _, _, _, _ => False

/-- The addresses that a term must not change: below the watermark, outside its destination and
outside the storage of the variables it may write. -/
def Prot (bp n d sz : Nat) (Γ : List Ty) (S : List SI) (W : List Bool) (a : Nat) : Prop :=
  a < bp + n ∧ ¬ InR (bp + d) sz a ∧ ¬ InW Γ S W a

/-! ## Representation -/

/-- The variable's value is represented by the bytes of its storage outside its hole, which is its
extent for a view and its two pieces for a pair reference. A view's value is a view of its extent. -/
def VarRel (h : Heap) (t : Ty) (v : t.carrier) (s : SI) : Prop :=
  ∃ B : List UInt8, Data.reprBytes v B ∧
    (∀ i, i < s.sz t → ¬ s.inHole (s.at i) → h (UInt64.ofNat (s.at i)) = B.getD i 0) ∧
    ∀ e, s.ext = some e → s.snd = none → ViewOK t v e

/-- A reference slot holds the address of the value, or for a pair reference the addresses of its
two pieces. -/
def PtrOk (h : Heap) (bp : Nat) (l : Loc) (s : SI) : Prop :=
  match l with
  | .own _ | .slot _ _ _ => True
  | .ref o => decodeLE (rd h (bp + o) 8) = UInt64.ofNat s.A
  | .ref2 o => decodeLE (rd h (bp + o) 8) = UInt64.ofNat s.A ∧
      ∀ f A2, s.snd = some (f, A2) → decodeLE (rd h (bp + o + 8) 8) = UInt64.ofNat A2

/-- Each variable in memory has its value represented at its address, and each reference slot
holds its address. A slot-resident variable's value is in its frame slots instead, and only a
variable of a type that can be slot-resident may be one. -/
def MEnvRel (h : Heap) (bp : Nat) : {Γ : List Ty} → Env Γ → List Loc → List SI → Prop
  | _, .nil, _, _ => True
  | _, .cons (t := t) v env, l :: ρ, s :: S =>
    (l.isSlot = false ∨ t.slotTy = false → VarRel h t v s) ∧ PtrOk h bp l s ∧ MEnvRel h bp env ρ S
  | _, .cons _ _, _, _ => False

/-! ## Slot-resident variables -/

/-- A word holds a value when it decodes some bytes that represent the value. The decoding is
little-endian, so the bytes past the value's size are zero. -/
def WordRel (t : Ty) (v : t.carrier) (w : UInt64) : Prop :=
  ∃ B : List UInt8, Data.reprBytes v B ∧ decodeLE B = w

/-- Frame slots hold the chunks of bytes `B`: slot `k + j` holds the little-endian word of bytes
`8j … 8j + 7` of `B`, for `j < n`. -/
def WordsAt (f : Frame) : Nat → List UInt8 → Nat → Prop
  | _, _, 0 => True
  | k, B, n + 1 => f k = decodeLE (B.take 8) ∧ WordsAt f (k + 1) (B.drop 8) n

/-- Frame slots hold a value: the `t.slotN` slots from `k` hold the chunks of bytes that represent
it. For a one-word scalar this is `WordRel` of slot `k`. -/
def WordsRel (t : Ty) (v : t.carrier) (f : Frame) (k : Nat) : Prop :=
  ∃ B : List UInt8, Data.reprBytes v B ∧ WordsAt f k B t.slotN

/-- A slot-resident variable has its value in its `t.slotN` frame slots. -/
def SlotRel (f : Frame) (t : Ty) (v : t.carrier) : Loc → Prop
  | .slot _ k n => FR ≤ k ∧ t.slotTy = true ∧ n = t.slotN ∧ WordsRel t v f k
  | _ => True

/-- The frame represents the slot-resident variables. -/
def FEnvRel (f : Frame) : {Γ : List Ty} → Env Γ → List Loc → Prop
  | _, .nil, ρ => ρ = []
  | _, .cons (t := t) v env, l :: ρ => SlotRel f t v l ∧ FEnvRel f env ρ
  | _, .cons _ _, [] => False

/-- The frame slots that a term must not change: those of the slot-resident variables it may not
write. -/
def SProt (ρ : List Loc) (W : List Bool) (x : Nat) : Prop :=
  ∃ i, (ρ.getD i default).holds x = true ∧ W.getD i false = false

/-- The term respects every live hole's loan: it accesses no place of the lender that overlaps
the lent place. -/
def HoleAv {Γ : List Ty} {t : Ty} (e : Exp Γ t) (S : List SI) : Prop :=
  ∀ i H, (S.getD i default).hole = some H → e.Avoids i ⟨true, H.path⟩

/-! ## The block rule -/

/-- The writable flags of `ps`, all writable. -/
abbrev allW (ps : List Ty) : List Bool := ps.map fun _ => true

/-- No outer variable is writable, as on entering a block. -/
abbrev noW (W : List Bool) : List Bool := W.map fun _ => false

@[simp] theorem noW_getD (W : List Bool) (i : Nat) : (noW W).getD i false = false := by
  induction W generalizing i with
  | nil => rfl
  | cons b W ih => cases i <;> simp_all

/-- The writable flags of a callee's parameters: owned and `&mut` parameters are writable,
`&` parameters are not. -/
def _root_.Millipede.RArgs.modeW {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → List Bool
  | _, _, .nil => []
  | _, _, .own _ as => true :: as.modeW
  | _, _, .shr _ as => false :: as.modeW
  | _, _, .mut _ as => true :: as.modeW

/-- The roots of the `&mut` arguments are writable. -/
def _root_.Millipede.RArgs.mutW {Γ : List Ty} (W : List Bool) : {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own _ as => as.mutW W
  | _, _, .shr _ as => as.mutW W
  | _, _, .mut p as => W.getD p.root false = true ∧ as.mutW W

/-- The writable flags inside a loop body that carries the variables `xs`, with flags numbered from
`k`: only the carried variables keep theirs. -/
def selW (xs : List Nat) : Nat → List Bool → List Bool
  | _, [] => []
  | k, b :: W => (b && xs.contains k) :: selW xs (k + 1) W

theorem getD_selW (xs : List Nat) :
    ∀ (k : Nat) (W : List Bool) (j : Nat),
      (selW xs k W).getD j false = (W.getD j false && xs.contains (k + j))
  | _, [], _ => rfl
  | k, b :: W, 0 => by simp [selW]
  | k, b :: W, j + 1 => by
    simp only [selW, List.getD_cons_succ]
    rw [getD_selW xs (k + 1) W j, show k + 1 + j = k + (j + 1) by omega]

/-- The restraint the lowering relies on, described in the module doc. -/
def _root_.Millipede.Exp.Restr : {Γ : List Ty} → {t : Ty} → Exp Γ t → List Bool → Prop
  | _, _, .atom _, _ => True
  | _, _, .let_ e₁ e₂, W => e₁.Restr (noW W) ∧ e₂.Restr (true :: W)
  | _, _, .ite _ e₁ e₂, W => e₁.Restr W ∧ e₂.Restr W
  | _, _, .prim _ _, _ => True
  | _, _, .call (ps := ps) _ body _, _ => body.Restr (allW ps)
  | _, _, .ok _, _ => True
  | _, _, .err _, _ => True
  | _, _, .match_ _ eE eO, W => eE.Restr (true :: W) ∧ eO.Restr (true :: W)
  | _, _, .ext _ _, _ => True
  | _, _, .extMut _ args k, W => args.outW W ∧ k.Restr (true :: W)
  | _, _, .mk _ _, _ => True
  | _, _, .read _, _ => True
  | _, _, .assign p _ k, W => W.getD p.root false = true ∧ k.Restr W
  | _, _, .case _ _ eP eQ, W => eP.Restr (true :: W) ∧ eQ.Restr (true :: W)
  | _, _, .put p _ _ k, W => W.getD p.root false = true ∧ k.Restr W
  | _, _, .take (dflt := _) p _ k, W => W.getD p.root false = true ∧ k.Restr (true :: W)
  | _, _, .borrowShr _ body k, W => body.Restr (false :: noW W) ∧ k.Restr (true :: W)
  | _, _, .borrowMut p body k, W =>
    W.getD p.root false = true ∧ body.Restr (true :: noW W) ∧ k.Restr (true :: W)
  | _, _, .callRef _ _ body args k, W =>
    args.mutW W ∧ body.Restr args.modeW ∧ k.Restr (true :: W)
  | _, _, .guard _, _ => True
  | _, _, .loop _ cs _ c body k, W =>
    (∀ x ∈ cs.idxs, W.getD x false = true) ∧ c.Restr (false :: false :: noW W) ∧
      body.Restr (true :: true :: selW cs.idxs 0 W) ∧ k.Restr (true :: W)

end Millipede.Flat
