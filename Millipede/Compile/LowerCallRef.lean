import Millipede.Compile.LowerSubView
import Millipede.Compile.LowerOccs

/-!
# The memory refinement of reference calls

A call with reference parameters, `callRef name req body args k`, passes each owned argument by
copying it into the callee's region, and each `&p` or `&mut p` argument as the address of `p`. The
callee reads and writes its caller's storage directly and hands back its `&mut` parameters in
place, so nothing is copied back after the return. The caller's memory then already represents
the sequential write-backs that the value semantics performs through the arguments' lenses.

This is sound because the borrow checker separates the arguments. In the callee's layout, the
storage of a `&mut` parameter overlaps no other parameter's storage. Two places of one variable
with non-overlapping paths are disjoint, places of different variables are disjoint because the
root of the `&mut` place is writable, and the other place avoids its own root's hole. After the
call, the bytes of each `&mut` place represent the handed-back component. The later argument
places are evaluated at the call, because their index atoms read no earlier `&mut` argument's
root, and their obligations still hold after the earlier write-backs.

See doc/design/memory.md.
-/

namespace Millipede.Flat

/-! ## Environments that agree outside one variable -/

theorem _root_.Millipede.Place.get_eqExcept {Γ : List Ty} {k : Nat} {π : List Sel} {t : Ty} (q : Place Γ t)
    (hr : q.root ≠ k) (hq : q.IdxAvoids k ⟨true, π⟩) {env env' : Env Γ} (he : EqExcept k env env') :
    q.get env = q.get env' := by
  induction q with
  | var m => exact he m hr
  | field q l ih => simp only [Place.get]; rw [ih hr hq]
  | index q i ih => simp only [Place.get]; rw [ih hr hq.1, i.denote_eqExcept hq.2 he]
  | slot q i ih => simp only [Place.get]; rw [ih hr hq.1, i.denote_eqExcept hq.2 he]
  | range q lo len ih =>
    simp only [Place.get]; rw [ih hr hq.1, lo.denote_eqExcept hq.2.1 he, len.denote_eqExcept hq.2.2 he]
  | pair2 q i j ih =>
    simp only [Place.get]; rw [ih hr hq.1, i.denote_eqExcept hq.2.1 he, j.denote_eqExcept hq.2.2 he]
  | rangeS m lo len =>
    simp only [Place.get]; rw [he m hr, lo.denote_eqExcept hq.1 he, len.denote_eqExcept hq.2 he]
  | pair2S m i j =>
    simp only [Place.get]; rw [he m hr, i.denote_eqExcept hq.1 he, j.denote_eqExcept hq.2 he]

/-- The obligations of a place survive a change of another variable, or of its own root when the
place has no `Slots` cell, because its obligations are then index bounds only. -/
theorem _root_.Millipede.Place.ok_eqExcept {Γ : List Ty} {k : Nat} {π : List Sel} {t : Ty} (q : Place Γ t)
    (hr : q.root ≠ k ∨ q.noSlot = true) (hq : q.IdxAvoids k ⟨true, π⟩) {env env' : Env Γ}
    (he : EqExcept k env env') (hok : q.ok env) : q.ok env' := by
  induction q with
  | var m => trivial
  | field q l ih => exact ih hr hq hok
  | index q i ih =>
    exact ⟨ih hr hq.1 hok.1, by rw [← i.denote_eqExcept hq.2 he]; exact hok.2⟩
  | slot q i ih =>
    rcases hr with hr | hr
    · refine ⟨ih (Or.inl hr) hq.1 hok.1, ?_⟩
      rw [← i.denote_eqExcept hq.2 he, ← q.get_eqExcept hr hq.1 he]; exact hok.2
    · simp [Place.noSlot] at hr
  | range q lo len ih =>
    exact ⟨ih hr hq.1 hok.1, by
      rw [← lo.denote_eqExcept hq.2.1 he, ← len.denote_eqExcept hq.2.2 he]; exact hok.2⟩
  | pair2 q i j ih =>
    refine ⟨ih hr hq.1 hok.1, ?_⟩
    rw [← i.denote_eqExcept hq.2.1 he, ← j.denote_eqExcept hq.2.2 he]; exact hok.2
  | rangeS m lo len =>
    have hr : m.idx ≠ k := hr.resolve_right (by simp [Place.noSlot])
    simp only [Place.ok] at hok ⊢
    rw [← he m hr, ← lo.denote_eqExcept hq.1 he, ← len.denote_eqExcept hq.2 he]; exact hok
  | pair2S m i j =>
    have hr : m.idx ≠ k := hr.resolve_right (by simp [Place.noSlot])
    simp only [Place.ok] at hok ⊢
    rw [← he m hr, ← i.denote_eqExcept hq.1 he, ← j.denote_eqExcept hq.2 he]; exact hok

theorem _root_.Millipede.Place.set_eqExcept {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) (v : t.carrier) :
    EqExcept p.root env (p.set env v) :=
  fun m hm => (Place.get_set_ne p env v m hm).symm

/-! ## Two argument places -/

/-- The type of a variable is determined by its position. -/
theorem _root_.Millipede.Mem.ty_eq : ∀ {t t' : Ty} {Γ : List Ty} (m : Mem t Γ) (m' : Mem t' Γ),
    m.idx = m'.idx → t = t'
  | _, _, _ :: _, .here, .here, _ => rfl
  | _, _, _ :: _, .there m, .there m', h => Mem.ty_eq m m' (by simpa [Mem.idx] using h)
  | _, _, _ :: _, .here, .there _, h => by simp [Mem.idx] at h
  | _, _, _ :: _, .there _, .here, h => by simp [Mem.idx] at h

theorem _root_.Millipede.Place.rootTy_eq {Γ : List Ty} {t t' : Ty} (p : Place Γ t) (q : Place Γ t')
    (h : p.root = q.root) : p.rootTy = q.rootTy :=
  Mem.ty_eq p.rootMem q.rootMem (by simpa using h)

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}

/-- A place the borrow checker lets a term use avoids its root's hole. -/
theorem place_avoids_hole {t : Ty} (hl : Lay bp n Γ ρ S W) (q : Place Γ t) {env : Env Γ} {h : Heap}
    (henv : MEnvRel h bp env ρ S) (hc : q.contig = true) (hL : q.Lawful) (hok : q.ok env)
    (hnh : q.NH S) (hpv : q.ExtOk S) {x : Nat}
    (hx : InR (placeA q S env) t.size x) : ¬ (S.getD q.root default).inHole x := by
  intro hh
  unfold SI.inHole at hh
  split at hh
  · exact hh
  · rename_i H hH
    obtain ⟨-, -, hat, -⟩ := place_at q hc hL hok henv hl hpv
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < t.size ∧ x = placeA q S env + k :=
      ⟨x - placeA q S env, by unfold InR at hx; omega, by unfold InR at hx; omega⟩
    rw [hat k hk] at hh
    exact ((hl.root q).2.2.2 H hH).2 q env rfl hc hL hok (hnh.2 H hH) k hk hh

/-- Two places that the borrow checker separates, one of whose roots is writable, have no byte in
common. Places with the same root are separated when their paths do not overlap. -/
theorem place_disj {t t' : Ty} (hl : Lay bp n Γ ρ S W) (p : Place Γ t) (q : Place Γ t')
    {env : Env Γ} (hc : p.contig = true) (hc' : q.contig = true) (hL : p.Lawful) (hL' : q.Lawful)
    (hok : p.ok env) (hok' : q.ok env) (hnh : p.NH S) (hnh' : q.NH S) {h : Heap}
    (henv : MEnvRel h bp env ρ S) (hpv : p.ExtOk S) (hpv' : q.ExtOk S)
    (hsame : p.root = q.root → Sel.overlap p.path q.path = false)
    (hw : p.root ≠ q.root → W.getD p.root false = true ∨ W.getD q.root false = true) :
    ∀ x, InR (placeA p S env) t.size x → ¬ InR (placeA q S env) t'.size x := by
  intro x hxp hxq
  by_cases hr : p.root = q.root
  · have := Place.disj_of_overlap p q env env (Place.rootTy_eq p q hr) hc hc' hL hL' hok hok'
      (hsame hr)
    obtain ⟨-, -, hat, -⟩ := place_at p hc hL hok henv hl hpv
    obtain ⟨-, -, hat', -⟩ := place_at q hc' hL' hok' henv hl hpv'
    have hpl := p.off_le env hc hL hok
    have hql := q.off_le env hc' hL' hok'
    rw [← Place.rootTy_eq p q hr] at hql
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < t.size ∧ x = placeA p S env + k :=
      ⟨x - placeA p S env, by unfold InR at hxp; omega, by unfold InR at hxp; omega⟩
    obtain ⟨k', hk', e⟩ : ∃ k', k' < t'.size ∧ placeA p S env + k = placeA q S env + k' :=
      ⟨placeA p S env + k - placeA q S env, by unfold InR at hxq; omega, by unfold InR at hxq; omega⟩
    rw [hat k hk, hat' k' hk', ← hr] at e
    have := SI.at_inj (hl.root p).ok (by omega) (by omega) e
    unfold Disj at *; omega
  · have hpr := hl.pair p.rootMem q.rootMem (by simpa using hr)
    simp only [Place.rootMem_idx] at hpr
    have hxp' := place_in p hc hL hok henv hl hpv hxp
    have hxq' := place_in q hc' hL' hok' henv hl hpv' hxq
    rcases hw hr with hw | hw
    · exact place_avoids_hole hl q henv hc' hL' hok' hnh' hpv' hxq (hpr.2.2.2.1 hw x hxp' hxq')
    · exact place_avoids_hole hl p henv hc hL hok hnh hpv hxp (hpr.2.2.2.2 hw x hxq' hxp')

end

/-! ## Argument places

A `&` or `&mut` argument is a contiguous place, passed as its address, or a slice
`q[lo..lo+len]` of a contiguous place, passed as the address of element `lo` and the length. The
callee's parameter for it is described by `Place.argSI`, which records the address and, for a
slice, the extent `len · size` of the viewed run of elements. Every fact the call needs about an
argument place is reduced to its base, a contiguous place whose storage contains the argument's,
which is the place itself or the sliced array. -/

/-- What is known at run time about the callee's parameter for a reference argument place. It is
the place's address, for a slice the address of element `lo` with the extent `len · size`, and for
the pair `q[i], q[j]` the two elements. -/
def _root_.Millipede.Place.argSI {Γ : List Ty} (S : List SI) (env : Env Γ) : {t : Ty} → Place Γ t → SI
  | _, .range (t := T) q lo len =>
    ⟨placeA q S env + (lo.denote env).toNat * T.size, none, some ((len.denote env).toNat * T.size), none⟩
  | _, .pair2 (t := T) (dflt := _) q i j =>
    pairSI T (placeA q S env + (i.denote env).toNat * T.size) (placeA q S env + (j.denote env).toNat * T.size)
  | _, .rangeS (t := T) m lo len =>
    ⟨(S.getD m.idx default).A + (lo.denote env).toNat * T.size, none,
      some ((len.denote env).toNat * T.size), none⟩
  | _, .pair2S (t := T) (dflt := _) m i j =>
    pairSI T ((S.getD m.idx default).A + (i.denote env).toNat * T.size)
      ((S.getD m.idx default).A + (j.denote env).toNat * T.size)
  | _, .var m => ⟨placeA (.var m) S env, none, (S.getD m.idx default).ext, none⟩
  | _, p => ⟨placeA p S env, none, none, none⟩

/-- The place is a sub-slice or a pair of cells of a view or `Slots` variable, so its storage is
part of the variable's and is reached from the variable's address. -/
def _root_.Millipede.Place.onView {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .rangeS _ _ _ => true
  | _, .pair2S (dflt := _) _ _ _ => true
  | _, _ => false

theorem _root_.Millipede.Place.path_onView {Γ : List Ty} {t : Ty} (p : Place Γ t)
    (h : p.onView = true) : p.path = [.dyn] := by
  cases p <;> first | rfl | simp [Place.onView] at h

/-- A usable reference argument place is contiguous, a slice of a contiguous place, or the pair of
two elements of one. It is lawful, its obligations hold, the borrow checker lets the call use it,
and its root is in memory, because a reference argument takes the root's address. -/
def _root_.Millipede.Place.ArgGood {Γ : List Ty} {t : Ty} (ρ : List Loc) (S : List SI) (env : Env Γ)
    (p : Place Γ t) : Prop :=
  p.refOk = true ∧ p.Lawful ∧ p.ok env ∧ p.NH S ∧ (ρ.getD p.root default).isSlot = false

theorem _root_.Millipede.Place.refLoc_borrowOk {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat)
    (hb : p.isPair2 = false) : p.refLoc o = .ref o := by
  cases p <;> first | rfl | simp [Place.isPair2] at hb

theorem _root_.Millipede.Place.refLoc_pair {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat)
    (hb : p.isPair2 = true) : p.refLoc o = .ref2 o := by
  cases p <;> first | rfl | simp [Place.isPair2] at hb

theorem _root_.Millipede.Place.refLoc_off {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat) :
    (p.refLoc o).off = o := by
  cases p <;> rfl

theorem _root_.Millipede.Place.refLoc_size {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat) (t' : Ty) :
    Loc.size t' (p.refLoc o) ≤ p.slotW := by
  cases p <;> simp [Place.refLoc, Loc.size, Place.slotW]

theorem _root_.Millipede.Place.refLoc_ptr {Γ : List Ty} {t : Ty} (p : Place Γ t) {o o' w : Nat}
    (e : (p.refLoc o).ptr = some (o', w)) : o' = o ∧ w ≤ p.slotW := by
  cases p <;> simp [Place.refLoc, Loc.ptr, Place.slotW] at e ⊢ <;> omega

theorem _root_.Millipede.Place.slotW_ge {Γ : List Ty} {t : Ty} (p : Place Γ t) : 8 ≤ p.slotW := by
  cases p <;> simp [Place.slotW]

theorem _root_.Millipede.Place.argSI_hole {Γ : List Ty} {t : Ty} (S : List SI) (env : Env Γ)
    (p : Place Γ t) : (p.argSI S env).hole = none := by
  cases p <;> rfl

theorem _root_.Millipede.Place.argSI_snd {Γ : List Ty} {t : Ty} (S : List SI) (env : Env Γ)
    (p : Place Γ t) (hp : p.isPair2 = false) : (p.argSI S env).snd = none := by
  cases p <;> first | rfl | simp [Place.isPair2] at hp

theorem _root_.Millipede.Place.argSI_contig {Γ : List Ty} {t : Ty} (S : List SI) (env : Env Γ)
    (p : Place Γ t) (hc : p.contig = true) (hpv : p.ExtOk S) :
    p.argSI S env = ⟨placeA p S env, none, none, none⟩ := by
  cases p <;> first | rfl | simp [Place.contig] at hc
  rename_i m
  rcases hpv with h | h
  · simp only [Place.argSI]; rw [show (S.getD m.idx default).ext = none from h]
  · simp [Place.isVarAt, Place.root] at h

theorem _root_.Millipede.Place.argSI_A {Γ : List Ty} {t : Ty} (S : List SI) (env : Env Γ)
    (p : Place Γ t) (hc : p.contig = true) : (p.argSI S env).A = placeA p S env := by
  cases p <;> first | rfl | simp [Place.contig] at hc

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {env : Env Γ}
  {h : Heap}

/-- The base of an argument place is a contiguous place with the same root, obligations and
borrow-checker facts, whose storage contains the argument's storage and whose path is separated
from every path that the argument's is separated from. -/
theorem _root_.Millipede.Place.arg_base (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hpv : p.ExtOk S) (hov : p.onView = false) :
    ∃ (t' : Ty) (b : Place Γ t'), b.contig = true ∧ b.Lawful ∧ b.ok env ∧ b.NH S ∧ b.ExtOk S ∧
      b.root = p.root ∧
      (∀ π, Sel.overlap π p.path = false → Sel.overlap π b.path = false) ∧
      (∀ π, Sel.overlap p.path π = false → Sel.overlap b.path π = false) ∧
      (∀ x, (p.argSI S env).In t x → InR (placeA b S env) t'.size x) ∧
      (p.argSI S env).Below t (placeA b S env + t'.size) := by
  obtain ⟨hb, hL, hok, hnh, -⟩ := hg
  cases p with
  | @range T N q lo len =>
    have h1 : ((lo.denote env).toNat + (len.denote env).toNat) * T.size ≤ N * T.size :=
      Nat.mul_le_mul_right _ hok.2
    have h2 : (Place.argSI S env (.range q lo len)).sz (Ty.view T N) ≤
        (len.denote env).toNat * T.size := Nat.min_le_left _ _
    have h3 : (Ty.arr T N).size = N * T.size := rfl
    rw [Nat.add_mul] at h1
    refine ⟨_, q, hb, hL, hok.1, hnh.range, extOk_parent_arr q henv hl, rfl,
      fun π h => Sel.overlap_append_dyn_right π q.path h, fun π h => Sel.overlap_append_dyn q.path π h,
      fun x hx => ?_, ?_⟩
    · rw [SI.In_none rfl] at hx
      rw [h3]; simp only [Place.argSI, InR] at h2 hx ⊢; omega
    · simp only [SI.Below, Place.argSI] at h2 ⊢; rw [h3]; omega
  | @pair2 T N _ q i j =>
    obtain ⟨hokq, hi, hj, -⟩ := hok
    have hbi := elem_bound (sz := T.size) hi
    have hbj := elem_bound (sz := T.size) hj
    have h3 : (Ty.arr T N).size = N * T.size := rfl
    refine ⟨_, q, hb, hL, hokq, ⟨hnh.1.1, fun H hH => Sel.overlap_append_dyn_right _ _ (hnh.2 H hH)⟩,
      extOk_parent_arr q henv hl, rfl,
      fun π h => Sel.overlap_append_dyn_right π q.path h, fun π h => Sel.overlap_append_dyn q.path π h,
      fun x hx => ?_, ?_⟩
    · rw [h3]; simp only [Place.argSI] at hx
      rcases pairSI_In.1 hx with hx | hx <;> unfold InR at hx ⊢ <;> omega
    · simp only [Place.argSI]; rw [h3]; exact pairSI_Below (by omega) (by omega)
  | rangeS => simp [Place.onView] at hov
  | pair2S => simp [Place.onView] at hov
  | _ =>
    simp only [Place.refOk, Place.borrowOk] at hb
    refine ⟨_, _, hb, hL, hok, hnh, hpv, rfl, fun _ h => h, fun _ h => h, fun x hx => ?_, ?_⟩
    · rw [Place.argSI_contig _ _ _ hb hpv, SI.In_mk, SI.sz_mk_none] at hx; exact hx
    · rw [Place.argSI_contig _ _ _ hb hpv]; simp [SI.Below]

/-- An argument's storage, read in memory, lies within the watermark and represents the argument's
value, which is the view for a slice and the two elements for a pair. -/
theorem _root_.Millipede.Place.arg_get (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hpv : p.ExtOk S) (hov : p.onView = false) :
    (p.argSI S env).Below t (bp + n) ∧ VarRel h t (p.get env) (p.argSI S env) := by
  obtain ⟨t', b, hc, hL, hok, hnh, hbv, hrb, -, -, -, hbel⟩ := p.arg_base henv hl hg hpv hov
  obtain ⟨hb, hL', hok', hnh', hns⟩ := hg
  have hgb := place_get b hc hL hok henv hl hnh.2 hbv (by rw [hrb]; exact hns)
  refine ⟨hbel.mono hgb.1, ?_⟩
  cases p with
  | range q lo len =>
    have hg' := place_get q hb hL' hok'.1 henv hl hnh'.range.2 (extOk_parent_arr q henv hl) hns
    have hfit := hok'.2
    refine VarRel.of_exact' ?_ ?_ rfl
    · exact vview_repr _ hg'.2 hfit
    · intro e he; cases he
      exact viewOK_of_slots (by omega) (vview_cells _ _ _ hfit)
  | pair2 q i j =>
    exact (pair2_at (W := W) hl henv q i j hb hL' hok' hnh' hns).varRel (fun _ _ => rfl)
  | rangeS => simp [Place.onView] at hov
  | pair2S => simp [Place.onView] at hov
  | _ =>
    simp only [Place.refOk, Place.borrowOk] at hb
    rw [Place.argSI_contig _ _ _ hb hpv]
    exact VarRel.of_exact (place_get _ hb hL' hok' henv hl hnh'.2 hpv hns).2

/-- An argument's storage lies inside its root's storage. -/
theorem _root_.Millipede.Place.arg_in (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hpv : p.ExtOk S) (hov : p.onView = false)
    {x : Nat} (hx : (p.argSI S env).In t x) : (S.getD p.root default).In p.rootTy x := by
  obtain ⟨t', b, hc, hL, hok, -, hbv, hr, -, -, hin, -⟩ := p.arg_base henv hl hg hpv hov
  have := place_in b hc hL hok henv hl hbv (hin x hx)
  rw [hr, Place.rootTy_eq b p hr] at this; exact this

/-- An argument's storage avoids its root's hole. -/
theorem _root_.Millipede.Place.arg_avoids_hole (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hpv : p.ExtOk S) (hov : p.onView = false)
    {x : Nat} (hx : (p.argSI S env).In t x) : ¬ (S.getD p.root default).inHole x := by
  obtain ⟨t', b, hc, hL, hok, hnh, hbv, hr, -, -, hin, -⟩ := p.arg_base henv hl hg hpv hov
  rw [← hr]
  exact place_avoids_hole hl b henv hc hL hok hnh hbv (hin x hx)

/-- Two argument places that the borrow checker separates, one of whose roots is writable, have no
byte in common. -/
theorem arg_disj (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {t t' : Ty} (p : Place Γ t)
    (q : Place Γ t') (hg : p.ArgGood ρ S env) (hg' : q.ArgGood ρ S env) (hpv : p.ExtOk S)
    (hpv' : q.ExtOk S) (hov : p.onView = false) (hov' : q.onView = false)
    (hsame : p.root = q.root → Sel.overlap p.path q.path = false)
    (hw : p.root ≠ q.root → W.getD p.root false = true ∨ W.getD q.root false = true) :
    ∀ x, (p.argSI S env).In t x → ¬ (q.argSI S env).In t' x := by
  obtain ⟨_, b, hc, hL, hok, hnh, hbv, hr, -, hpr, hin, -⟩ := p.arg_base henv hl hg hpv hov
  obtain ⟨_, b', hc', hL', hok', hnh', hbv', hr', hpl', -, hin2, -⟩ := q.arg_base henv hl hg' hpv' hov'
  intro x hx hx'
  refine place_disj hl b b' hc hc' hL hL' hok hok' hnh hnh' henv hbv hbv'
    (fun e => hpl' _ (hpr _ (hsame (by rw [← hr, ← hr', e])))) (fun e => by
      rw [hr, hr']; exact hw fun e' => e (by rw [hr, hr', e'])) x (hin x hx) (hin2 x hx')

/-! ### A sub-slice or a pair of cells of a view variable as an argument

The storage of such an argument is part of the variable's, which has no hole. The variable's path
`[dyn]` overlaps every path, so the borrow checker lets the call use it only while nothing of the
variable is lent. -/

theorem _root_.Millipede.Place.onView_hole {t : Ty} (p : Place Γ t) (hov : p.onView = true)
    (hg : p.ArgGood ρ S env) : (S.getD p.root default).hole = none :=
  hole_none_of_dyn (p.path_onView hov) hg.2.2.2.1.2

/-- A view place argument's storage lies inside its root's storage and below the watermark, and
represents its value. -/
theorem _root_.Millipede.Place.view_arg (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} (p : Place Γ t) (hov : p.onView = true) (hg : p.ArgGood ρ S env) :
    (∀ x, (p.argSI S env).In t x → (S.getD p.root default).In p.rootTy x) ∧
      (p.argSI S env).Below t (bp + n) ∧ VarRel h t (p.get env) (p.argSI S env) := by
  have hH := p.onView_hole hov hg
  obtain ⟨-, -, hok, -, -⟩ := hg
  cases p with
  | @rangeS T N m lo len =>
    obtain ⟨hle, hb, hhold, hrep, hvok⟩ := rangeS_facts hl henv m lo len hok hH
    have hsz := sz_view (A := (S.getD m.idx default).A + (lo.denote env).toNat * T.size) (T := T) hle
    refine ⟨fun x hx => hhold.In ?_, ?_, VarRel.of_exact' hrep (fun e he => by cases he; exact hvok) rfl⟩
    · simp only [Place.argSI] at hx; rw [SI.In_mk, hsz] at hx; exact hx
    · simp only [Place.argSI, SI.Below]; rw [hsz]; exact hb
  | @pair2S T N _ m i j =>
    obtain ⟨-, hbi, hbj, hhi, hhj, hgi, hgj⟩ := pair2S_facts hl henv m i j hok hH
    refine ⟨fun x hx => ?_, pairSI_Below hbi hbj, pair_varRel hgi hgj⟩
    simp only [Place.argSI] at hx
    rcases pairSI_In.1 hx with hx | hx
    · exact hhi.In hx
    · exact hhj.In hx
  | _ => simp [Place.onView] at hov

/-! ### A whole variable as an argument

A `&` argument may be a whole variable, including a slice view passed on whole as its address,
for which the callee's parameter has the same extent. Its storage is the variable's, which has no
hole because the borrow checker forbids it. The primed lemmas below hold for every usable argument
place that is either a whole variable other than a pair reference, or reaches no view as a
whole. -/

theorem _root_.Millipede.Place.var_hole {t : Ty} {m : Mem t Γ} (hg : (Place.var m).ArgGood ρ S env) :
    (S.getD m.idx default).hole = none := by
  cases hH : (S.getD m.idx default).hole with
  | none => rfl
  | some H =>
    have := hg.2.2.2.1.2 H hH
    simp [Place.path, Sel.overlap_nil_right] at this

theorem _root_.Millipede.Place.var_argSI {t : Ty} {m : Mem t Γ} (hH : (S.getD m.idx default).hole = none)
    (hs : (S.getD m.idx default).snd = none) :
    (Place.var m).argSI S env = S.getD m.idx default := by
  cases e : S.getD m.idx default
  simp_all [Place.argSI, placeA]

theorem _root_.Millipede.Place.arg_get' (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hnp : p.NotPair S) :
    (p.argSI S env).Below t (bp + n) ∧ VarRel h t (p.get env) (p.argSI S env) := by
  by_cases hv : p.isVarAt p.root = true
  · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
    have hs : (S.getD m.idx default).snd = none := hnp hv
    rw [Place.var_argSI (Place.var_hole hg) hs]
    exact ⟨(hl.var m).below, (henv.get m hg.2.2.2.2).1⟩
  · cases hov : p.onView
    · exact p.arg_get hl henv hg (Or.inr (by simpa using hv)) hov
    · exact (p.view_arg hl henv hov hg).2

theorem _root_.Millipede.Place.arg_in' (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hnp : p.NotPair S) {x : Nat}
    (hx : (p.argSI S env).In t x) : (S.getD p.root default).In p.rootTy x := by
  by_cases hv : p.isVarAt p.root = true
  · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
    have hs : (S.getD m.idx default).snd = none := hnp hv
    rw [Place.var_argSI (Place.var_hole hg) hs] at hx
    exact hx
  · cases hov : p.onView
    · exact p.arg_in henv hl hg (Or.inr (by simpa using hv)) hov hx
    · exact (p.view_arg hl henv hov hg).1 x hx

theorem _root_.Millipede.Place.arg_avoids_hole' (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) {x : Nat}
    (hx : (p.argSI S env).In t x) : ¬ (S.getD p.root default).inHole x := by
  by_cases hv : p.isVarAt p.root = true
  · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
    intro hh
    have := Place.var_hole hg
    unfold SI.inHole at hh
    simp only [Place.root] at hh
    rw [this] at hh; exact hh
  · cases hov : p.onView
    · exact p.arg_avoids_hole hl henv hg (Or.inr (by simpa using hv)) hov hx
    · intro hh; unfold SI.inHole at hh; rw [p.onView_hole hov hg] at hh; exact hh

/-- `arg_disj` for every usable argument place except a pair reference passed whole. -/
theorem arg_disj' (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {t t' : Ty} (p : Place Γ t)
    (q : Place Γ t') (hg : p.ArgGood ρ S env) (hg' : q.ArgGood ρ S env) (hnp : p.NotPair S)
    (hnp' : q.NotPair S) (hsame : p.root = q.root → Sel.overlap p.path q.path = false)
    (hw : p.root ≠ q.root → W.getD p.root false = true ∨ W.getD q.root false = true) :
    ∀ x, (p.argSI S env).In t x → ¬ (q.argSI S env).In t' x := by
  intro x hx hx'
  by_cases hr : p.root = q.root
  · by_cases hv : p.isVarAt p.root = true
    · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
      simp [Place.path, Sel.overlap] at hsame; exact hsame hr
    by_cases hv' : q.isVarAt q.root = true
    · obtain ⟨m, rfl⟩ := q.eq_var_of_isVarAt hv'
      simp [Place.path, Sel.overlap_nil_right] at hsame; exact hsame hr
    cases hov : p.onView
    · cases hov' : q.onView
      · exact arg_disj hl henv p q hg hg' (Or.inr (by simpa using hv)) (Or.inr (by simpa using hv'))
          hov hov' hsame (fun e => absurd hr e) x hx hx'
      · have := hsame hr; rw [q.path_onView hov', Sel.overlap_dyn_right] at this; cases this
    · have := hsame hr; rw [p.path_onView hov, Sel.overlap_dyn_left] at this; cases this
  · have hpr := hl.pair p.rootMem q.rootMem (by simpa using hr)
    simp only [Place.rootMem_idx] at hpr
    have h1 := p.arg_in' henv hl hg hnp hx
    have h2 := q.arg_in' henv hl hg' hnp' hx'
    rcases hw hr with hw | hw
    · exact q.arg_avoids_hole' hl henv hg' hx' (hpr.2.2.2.1 hw x h1 h2)
    · exact p.arg_avoids_hole' hl henv hg hx (hpr.2.2.2.2 hw x h2 h1)

/-- The address of a place does not change when another variable does, or its own root along a
path its index atoms avoid. -/
theorem _root_.Millipede.Place.placeA_eqExcept {k : Nat} {π : List Sel} {t : Ty} (q : Place Γ t)
    (hq : q.IdxAvoids k ⟨true, π⟩) {env' : Env Γ} (he : EqExcept k env env') :
    placeA q S env = placeA q S env' := by
  induction q with
  | var m => rfl
  | field q l ih => simp only [placeA]; rw [ih hq]
  | index q i ih => simp only [placeA]; rw [ih hq.1, i.denote_eqExcept hq.2 he]
  | slot q i ih => simp only [placeA]; rw [ih hq.1, i.denote_eqExcept hq.2 he]
  | range q lo len ih => rfl
  | pair2 q i j ih => rfl
  | rangeS => rfl
  | pair2S => rfl

/-- The argument's knowledge does not change when another variable does, or its own root along a
path its index atoms avoid. -/
theorem _root_.Millipede.Place.argSI_eqExcept {k : Nat} {π : List Sel} {t : Ty} (p : Place Γ t)
    (hq : p.IdxAvoids k ⟨true, π⟩) {env' : Env Γ} (he : EqExcept k env env') :
    p.argSI S env = p.argSI S env' := by
  cases p with
  | range q lo len =>
    simp only [Place.argSI]
    rw [q.placeA_eqExcept hq.1 he, lo.denote_eqExcept hq.2.1 he, len.denote_eqExcept hq.2.2 he]
  | pair2 q i j =>
    simp only [Place.argSI]
    rw [q.placeA_eqExcept hq.1 he, i.denote_eqExcept hq.2.1 he, j.denote_eqExcept hq.2.2 he]
  | rangeS m lo len =>
    simp only [Place.argSI]; rw [lo.denote_eqExcept hq.1 he, len.denote_eqExcept hq.2 he]
  | pair2S m i j =>
    simp only [Place.argSI]; rw [i.denote_eqExcept hq.1 he, j.denote_eqExcept hq.2 he]
  | _ => simp only [Place.argSI]; rw [Place.placeA_eqExcept _ hq he]

/-- Writing an argument place back. When the argument's storage holds a prefix of bytes
representing `v` and the memory is unchanged elsewhere below the watermark, the memory represents
the environment in which the place holds `v`. For a slice, the cells `0 … len-1` of `v` must be
full, which is the write-back condition `Place.backOk`. -/
theorem _root_.Millipede.Place.arg_set (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    (hbn : bp + n ≤ UInt64.size) {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env) (hpv : p.ExtOk S)
    (hW : W.getD p.root false = true) (h' : Heap) (v : t.carrier) (hfull : p.backOk env v)
    (hout : ∀ a, a < bp + n → ¬ (p.argSI S env).In t a → h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (V : List UInt8) (hV : Data.reprBytes v V)
    (hVm : slice V 0 ((p.argSI S env).sz t) = rdS h' (p.argSI S env) ((p.argSI S env).sz t)) :
    MEnvRel h' bp (p.set env v) ρ S := by
  obtain ⟨hb, hL, hok, hnh, hns⟩ := hg
  cases p with
  | @range T N q lo len =>
    rw [rdS_none rfl] at hVm
    simp only [SI.In_none (Place.argSI_snd S env (.range q lo len) rfl)] at hout
    have hpq := extOk_parent_arr q henv hl
    have hg' := place_get q hb hL hok.1 henv hl hnh.range.2 hpq hns
    have hfit := hok.2
    have h1 : ((lo.denote env).toNat + (len.denote env).toNat) * T.size ≤ N * T.size :=
      Nat.mul_le_mul_right _ hfit
    rw [Nat.add_mul] at h1
    have h3 : (Ty.arr T N).size = N * T.size := rfl
    rw [h3] at hg'
    have hle : (len.denote env).toNat ≤ N := Nat.le_trans (Nat.le_add_left _ _) hfit
    have hsz : (Place.argSI S env (.range q lo len)).sz (Ty.view T N) =
        (len.denote env).toNat * T.size := sz_view hle
    rw [hsz] at hout hVm
    have hA : (Place.argSI S env (.range q lo len)).A =
        placeA q S env + (lo.denote env).toNat * T.size := rfl
    rw [hA] at hout hVm
    have hrep := vunview_repr (q.get env) v (h := h) (m := h') hfit hg'.2 hfull V hV hVm
      (fun i hi hn => hout _ (by omega) (fun hin => hn (by unfold InR at hin ⊢; omega)))
    exact place_set q hb hL hok.1 henv hl hW hbn hpq hns h' _
      (fun a ha hn => hout a ha fun hin => hn (by rw [h3]; unfold InR at hin ⊢; omega)) hrep
  | @pair2 T N _ q i j =>
    simp only [Place.argSI] at hout hVm
    obtain ⟨hv1, hv2⟩ := pair_back_repr v V hV hVm
    exact place_set_pair2 q i j hb hL hok henv hl hW hns hbn h' v
      (fun a ha h1 h2 => hout a ha fun hin => by
        rcases pairSI_In.1 hin with h | h
        · exact h1 h
        · exact h2 h) hv1 hv2
  | @rangeS T N m lo len =>
    have hH := hole_none_of_dyn (p := Place.rangeS m lo len) rfl hnh.2
    have hle : (len.denote env).toNat ≤ N := by have := hok.1; omega
    have hsz : (Place.argSI S env (.rangeS m lo len)).sz (Ty.view T N) =
        (len.denote env).toNat * T.size := sz_view hle
    rw [rdS_none rfl, hsz] at hVm
    simp only [SI.In_none (Place.argSI_snd S env (.rangeS m lo len) rfl), hsz] at hout
    exact rangeS_set_rel hl henv hbn m lo len hok hH hW h' v hfull V hV hVm hout
  | @pair2S T N _ m i j =>
    have hH := hole_none_of_dyn (p := Place.pair2S m i j) rfl hnh.2
    simp only [Place.argSI] at hout hVm
    obtain ⟨hv1, hv2⟩ := pair_back_repr v V hV hVm
    exact pair2S_set_rel hl henv hbn m i j hok hH hW h' v
      (fun a ha h1 h2 => hout a ha fun hin => by
        rcases pairSI_In.1 hin with h | h
        · exact h1 h
        · exact h2 h) hv1 hv2
  | _ =>
    simp only [Place.refOk, Place.borrowOk] at hb
    rw [Place.argSI_contig _ _ _ hb hpv] at hout hVm
    simp only [SI.sz_mk_none, SI.In_mk] at hout hVm
    rw [rdS_none rfl, slice_full V _ (Data.reprBytes_length hV)] at hVm
    exact place_set _ hb hL hok henv hl hW hbn hpv hns h' v hout (hVm ▸ hV)

/-- `arg_set` for every usable argument place. A variable passed on whole, which is a view, gets the
handed-back value, which must be a view of the same extent. -/
theorem _root_.Millipede.Place.arg_set' (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    (hbn : bp + n ≤ UInt64.size) {t : Ty} (p : Place Γ t) (hg : p.ArgGood ρ S env)
    (hnp : p.NotPair S)
    (hW : W.getD p.root false = true) (h' : Heap) (v : t.carrier) (hfull : p.backOk env v)
    (hview : p.isVarAt p.root = true → ∀ e, (p.argSI S env).ext = some e → ViewOK t v e)
    (hout : ∀ a, a < bp + n → ¬ (p.argSI S env).In t a → h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (V : List UInt8) (hV : Data.reprBytes v V)
    (hVm : slice V 0 ((p.argSI S env).sz t) = rdS h' (p.argSI S env) ((p.argSI S env).sz t)) :
    MEnvRel h' bp (p.set env v) ρ S := by
  by_cases hv : p.isVarAt p.root = true
  · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
    have hH : (S.getD m.idx default).hole = none := (hl.var m).2.2.1 hW
    have hs : (S.getD m.idx default).snd = none := hnp hv
    rw [Place.var_argSI hH hs] at hout hVm hview
    rw [rdS_none hs] at hVm
    refine henv.set_var' m v hl hW hbn hout fun _ => ⟨V, hV, fun i hi _ => ?_, fun e he _ => hview hv e he⟩
    rw [SI.at_none hs, ← rd_getD h' _ _ i hi, ← hVm]
    have hVl := Data.reprBytes_length hV
    have : t.size = (Data.shape t.carrier).size := rfl
    have : i < V.length := by have := (S.getD m.idx default).sz_le t; omega
    generalize (S.getD m.idx default).sz t = z at hi ⊢; simp [slice, List.getD_eq_getElem?_getD, hi]
  · exact p.arg_set hl henv hbn hg (Or.inr (by simpa using hv)) hW h' v hfull hout V hV hVm

end

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- Passing a slice of a contiguous base place `q`, an array or a view variable, stores the
address of element `lo` and the length at `bp + d`. Only the slot changes. -/
theorem slicePass_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} (hl : Lay bp n Γ ρ S W) {t' : Ty} (T : Ty) (q : Place Γ t') (lo len : Atom Γ .u64)
    (d : Nat) (f : Frame) (h : Heap) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ)
    (hc : q.contig = true) (hL : q.Lawful) (hnp : q.NotPair S) (hnq : q.IdxNH S)
    (hnlo : ∀ m, lo = .var m → (S.getD m.idx default).hole = none)
    (hnlen : ∀ m, len = .var m → (S.getD m.idx default).hole = none)
    (hdn : n ≤ d) (hU : bp + d + 16 ≤ UInt64.size) (hL16 : bp + d + 16 ≤ L) :
    ∃ f' h', Runs κ ω L (.seq (.seq (placeAddr q ρ) (elemAddr lo ρ T.size)) (sliceStore len ρ d))
        f h f' h' ∧ f' BP = f BP ∧
      (∀ a, a < UInt64.size → ¬ InR (bp + d) 16 a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      decodeLE (rd h' (bp + d) 8) = UInt64.ofNat (placeA q S env + (lo.denote env).toNat * T.size) ∧
      decodeLE (rd h' (bp + d + 8) 8) = len.denote env := by
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) q hc hf henv hfe hl
    hnq hL hnp (by omega) (by omega)
  obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) lo _ _
    (hb₁.trans hf) ha₁ henv (hfe.keep hr₁.keep) hl hnlo (by omega) (by omega)
  have hfb₂ : f₂ BP = UInt64.ofNat bp := hb₂.trans (hb₁.trans hf)
  have hst := store_ptr (κ := κ) (ω := ω) (L := L) (h := h) (n := d) hfb₂ ha₂ (by omega) (by omega)
  have hH₁o : ∀ x, x < bp + d → (wr h (bp + d) (natBytes 8 (UInt64.ofNat
      (placeA q S env + (lo.denote env).toNat * T.size)).toNat)) (UInt64.ofNat x) =
        h (UInt64.ofNat x) :=
    fun x hx => wr_out (by simp; omega) (by omega) (by simp; omega)
  have hlw := atomWord_u64 (κ := κ) (ω := ω) (L := L) len RX hfb₂
    (henv.above hl fun x hx => hH₁o x (by omega)) (hfe.keep (Runs.seq hr₁ hr₂).keep) hl hnlen
    (by omega) (by omega)
  have hfb₃ : (f₂.set RX (len.denote env)) BP = UInt64.ofNat bp := by
    rw [Frame.set_ne _ _ (by decide)]; exact hfb₂
  have hst2 := store_word (κ := κ) (ω := ω) (L := L) (m := d + 8)
    (h := wr h (bp + d) (natBytes 8 (UInt64.ofNat
      (placeA q S env + (lo.denote env).toNat * T.size)).toNat)) RX (len.denote env)
    hfb₃ (by simp) (by omega) (by omega)
  refine ⟨_, _, Runs.seq (Runs.seq hr₁ hr₂) (Runs.seq hst (Runs.seq hlw hst2)),
    by rw [Frame.set_ne _ _ (by decide), hb₂, hb₁], fun a ha hn => ?_, ?_, ?_⟩
  · unfold InR at hn
    rw [wr_out (by simp; omega) ha (by simp; omega)]
    exact wr_out (by simp; omega) ha (by simp; omega)
  · rw [rd_congr fun j hj => wr_out (by simp; omega) (by omega) (by simp; omega)]
    exact ptr_bytes h bp d _ (by omega)
  · rw [show bp + d + 8 = bp + (d + 8) by omega]
    have := rd_wr (wr h (bp + d) (natBytes 8 (UInt64.ofNat
      (placeA q S env + (lo.denote env).toNat * T.size)).toNat)) (bp + (d + 8))
      (natBytes 8 (len.denote env).toNat) (by simp; omega)
    rw [natBytes_length] at this
    rw [this, decodeLE_natBytes8]

/-- Passing one reference argument computes the place's address, which for a slice is element
`lo`'s, and stores it at `bp + d`, with a slice's length at `bp + d + 8`. Only the slot changes. -/
theorem argPass_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} (hl : Lay bp n Γ ρ S W) {t : Ty} (p : Place Γ t) (d : Nat) (f : Frame) (h : Heap)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hg : p.ArgGood ρ S env) (hnp : p.NotPair S)
    (hdn : n ≤ d) (hU : bp + d + p.slotW ≤ UInt64.size) (hL : bp + d + p.slotW ≤ L) :
    ∃ f' h', Runs κ ω L (.seq (placeAddr p ρ) (refStore p ρ d)) f h f' h' ∧ f' BP = f BP ∧
      (∀ a, a < UInt64.size → ¬ InR (bp + d) p.slotW a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      decodeLE (rd h' (bp + d) 8) = UInt64.ofNat (p.argSI S env).A ∧
      ∀ f' A2, (p.argSI S env).snd = some (f', A2) →
        decodeLE (rd h' (bp + d + 8) 8) = UInt64.ofNat A2 := by
  obtain ⟨hb, hL', hok, hnh, -⟩ := hg
  cases p with
  | @range T N q lo len =>
    obtain ⟨f', h', hr, hb', hout, hp1, -⟩ := slicePass_runs (κ := κ) (ω := ω) (L := L) hl T q lo len
      d f h hf henv hfe hb hL' (q.notPair_of_ty hl (arr_not_prod T N)) hnh.range.1 hnh.1.2.1 hnh.1.2.2
      hdn hU hL
    exact ⟨f', h', hr, hb', hout, hp1, fun _ _ e => by cases e⟩
  | @rangeS T N m lo len =>
    obtain ⟨f', h', hr, hb', hout, hp1, -⟩ := slicePass_runs (κ := κ) (ω := ω) (L := L) hl T (.var m)
      lo len d f h hf henv hfe rfl trivial ((Place.var m).notPair_of_ty hl (slots_not_prod T N)) trivial
      hnh.1.1 hnh.1.2 hdn hU hL
    exact ⟨f', h', hr, hb', hout, hp1, fun _ _ e => by cases e⟩
  | @pair2 T N _ q i j =>
    obtain ⟨f₁, hr₁, hb₁, ha₁, hB₁⟩ := pairAddr_runs (κ := κ) (ω := ω) (L := L) hl T q i j f h hf henv
      hfe hb hL' (q.notPair_of_ty hl (arr_not_prod T N)) hnh.1.1 hnh.1.2.1 hnh.1.2.2 (by omega) (by omega)
    obtain ⟨h', hr₂, hout, hp1, hp2⟩ := pairStore_runs (κ := κ) (ω := ω) (L := L) (d := d)
      (hb₁.trans hf) ha₁ hB₁ hU hL
    refine ⟨f₁, h', Runs.seq hr₁ hr₂, hb₁, hout, hp1, fun f'' A2 e => ?_⟩
    simp only [Place.argSI, pairSI, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e; exact hp2
  | @pair2S T N _ m i j =>
    obtain ⟨f₁, hr₁, hb₁, ha₁, hB₁⟩ := pairAddr_runs (κ := κ) (ω := ω) (L := L) hl T (.var m) i j f h
      hf henv hfe rfl trivial ((Place.var m).notPair_of_ty hl (slots_not_prod T N)) trivial hnh.1.1
      hnh.1.2 (by omega) (by omega)
    obtain ⟨h', hr₂, hout, hp1, hp2⟩ := pairStore_runs (κ := κ) (ω := ω) (L := L) (d := d)
      (hb₁.trans hf) ha₁ hB₁ hU hL
    refine ⟨f₁, h', Runs.seq hr₁ hr₂, hb₁, hout, hp1, fun f'' A2 e => ?_⟩
    simp only [Place.argSI, pairSI, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e; exact hp2
  | _ =>
    simp only [Place.refOk, Place.borrowOk] at hb
    have hs8 := Place.slotW_contig _ hb
    rw [refStore_contig _ ρ d hb, Place.argSI_A _ _ _ hb, hs8]
    rw [hs8] at hU hL
    obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) _ hb hf henv hfe hl
      hnh.1 hL' hnp (by omega) (by omega)
    have hst := store_ptr (κ := κ) (ω := ω) (L := L) (h := h) (n := d) (hb₁.trans hf) ha₁
      (by omega) (by omega)
    refine ⟨_, _, Runs.seq hr₁ hst, hb₁, fun a ha hn => ?_, ptr_bytes h bp d _ (by omega),
      fun _ _ e => by rw [Place.argSI_snd _ _ _ rfl] at e; cases e⟩
    exact wr_out (by simp; omega) ha (by simp; unfold InR at hn; omega)

end

/-! ## The callee's parameters -/

/-- What is known at run time about a callee's parameters in its region at `bp'`. An owned
parameter is at its slot, and a reference parameter is at its argument place's storage, with the
extent for a slice. -/
def _root_.Millipede.RArgs.semS {Γ : List Ty} (bp' : Nat) (S : List SI) (env : Env Γ) :
    {ps os : List Ty} → RArgs Γ ps os → Nat → List SI
  | _, _, .nil, _ => []
  | _, _, .own (t := t) _ as, o => ⟨bp' + o, none, none, none⟩ :: as.semS bp' S env (o + t.size)
  | _, _, .shr p as, o => p.argSI S env :: as.semS bp' S env (o + p.slotW)
  | _, _, .mut p as, o => p.argSI S env :: as.semS bp' S env (o + p.slotW)

/-- The arguments are usable when owned atoms read no variable with a hole and argument places are
usable. -/
def _root_.Millipede.RArgs.Good {Γ : List Ty} (ρ : List Loc) (S : List SI) (env : Env Γ) :
    {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own a as => (∀ m, a = .var m → (S.getD m.idx default).hole = none) ∧ as.Good ρ S env
  | _, _, .shr p as => p.ArgGood ρ S env ∧ as.Good ρ S env
  | _, _, .mut p as => p.ArgGood ρ S env ∧ as.Good ρ S env

/-- The arguments touch no slice view as a whole when owned atoms read no view and `&mut` argument
places reach only inside views. A `&` argument may still be a view as a whole. -/
def _root_.Millipede.RArgs.ExtOk {Γ : List Ty} (S : List SI) :
    {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own a as => (∀ m, a = .var m → (S.getD m.idx default).ext = none) ∧ as.ExtOk S
  | _, _, .shr p as => p.NotPair S ∧ as.ExtOk S
  | _, _, .mut p as => p.NotPair S ∧ as.ExtOk S

/-- A whole variable passed on by reference is not a pair reference, because only a view, which
has a `Slots` type, may be passed on whole. -/
theorem _root_.Millipede.Place.notPair_of_vsafe {Γ : List Ty} {t : Ty} {S : List SI} {P : Nat → Bool}
    {bp n : Nat} {ρ : List Loc} {W : List Bool} (hl : Lay bp n Γ ρ S W) (hV : VS S P) (p : Place Γ t)
    {b : Bool} (h : ∀ i, P i = true → (p.VSafe i || p.isVarAt i && t.isViewTy && b) = true) :
    p.NotPair S := by
  intro hv
  cases hs : (S.getD p.root default).snd with
  | none => rfl
  | some q =>
    exfalso
    obtain ⟨o, -, hp⟩ := (hl.root p).snd_some hs
    obtain ⟨sh, A2, hsh, -, he, -⟩ := hp
    have := h _ (hV _ (by rw [he]; nofun))
    rw [Place.VSafe, hv] at this
    simp only [Bool.not_true, Bool.and_false, Bool.false_or, Bool.true_and,
      Bool.and_eq_true] at this
    rw [p.rootTy_of_isVarAt hv] at hsh
    simp [Ty.isViewTy, hsh] at this

theorem _root_.Millipede.RArgs.extOk_of {Γ : List Ty} {S : List SI} {P : Nat → Bool}
    {bp n : Nat} {ρ : List Loc} {W : List Bool} (hl : Lay bp n Γ ρ S W)
    (hV : VS S P) {vok mok : Nat → Bool} : {ps os : List Ty} → (as : RArgs Γ ps os) → (j : Nat) →
    (∀ i, P i = true → as.VSafe i vok mok j = true) → as.ExtOk S
  | _, _, .nil, _, _ => trivial
  | _, _, .own a as, j, h => ⟨hV.atom a fun i hi => by
      have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1, RArgs.extOk_of hl hV as (j + 1) fun i hi => by
        have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true] at this; exact this.2⟩
  | _, _, .shr p as, j, h => ⟨p.notPair_of_vsafe hl hV fun i hi => by
      have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true] at this; exact this.1,
    RArgs.extOk_of hl hV as (j + 1) fun i hi => by
      have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true] at this; exact this.2⟩
  | _, _, .mut p as, j, h => ⟨p.notPair_of_vsafe hl hV fun i hi => by
      have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true] at this; exact this.1,
    RArgs.extOk_of hl hV as (j + 1) fun i hi => by
      have := h i hi; simp only [RArgs.VSafe, Bool.and_eq_true] at this; exact this.2⟩

/-- No reference argument is rooted at a slot-resident variable. -/
theorem _root_.Millipede.RArgs.noAddr_root {Γ : List Ty} {ρ : List Loc} {ps os : List Ty}
    {as : RArgs Γ ps os} (hna : ∀ i, (ρ.getD i default).isSlot = true → as.noAddr i = true)
    {t : Ty} (p : Place Γ t) (hp : as.noAddr p.root = true → False) :
    (ρ.getD p.root default).isSlot = false := by
  cases hs : (ρ.getD p.root default).isSlot
  · rfl
  · exact (hp (hna _ hs)).elim

theorem _root_.Millipede.RArgs.good_of {Γ : List Ty} {ρ : List Loc} {S : List SI} {env : Env Γ} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → as.memOk = true → as.Lawful → as.ok env →
    (∀ i H, (S.getD i default).hole = some H → as.Avoids i ⟨true, H.path⟩) →
    (∀ i, (ρ.getD i default).isSlot = true → as.noAddr i = true) → as.Good ρ S env
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .own a as, hm, hL, hok, hH, hna =>
    ⟨a.noHole fun i H h' => (hH i H h').1, RArgs.good_of as hm hL hok (fun i H h' => (hH i H h').2)
      fun i h => by have := hna i h; simpa [RArgs.noAddr] using this⟩
  | _, _, .shr p as, hm, hL, hok, hH, hna => by
    simp only [RArgs.memOk, Bool.and_eq_true] at hm
    exact ⟨⟨hm.1, hL.1, hok.1, p.nh_of .read fun i H h' => (hH i H h').1,
        RArgs.noAddr_root hna p fun h => by simp [RArgs.noAddr] at h⟩,
      RArgs.good_of as hm.2 hL.2 hok.2 (fun i H h' => (hH i H h').2) fun i h => by
        have := hna i h; simp only [RArgs.noAddr, Bool.and_eq_true] at this; exact this.2⟩
  | _, _, .mut p as, hm, hL, hok, hH, hna => by
    simp only [RArgs.memOk, Bool.and_eq_true] at hm
    exact ⟨⟨hm.1, hL.1, hok.1, p.nh_of .write fun i H h' => (hH i H h').1,
        RArgs.noAddr_root hna p fun h => by simp [RArgs.noAddr] at h⟩,
      RArgs.good_of as hm.2 hL.2 hok.2 (fun i H h' => (hH i H h').2) fun i h => by
        have := hna i h; simp only [RArgs.noAddr, Bool.and_eq_true] at this; exact this.2⟩

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- Passing the arguments copies the owned ones into the callee's region and stores the references
as addresses, with a length for a slice. Only the parameter slots change, and afterwards the
callee's parameters are represented. -/
theorem rargsPass_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} (hl : Lay bp n Γ ρ S W) :
    ∀ {ps os : List Ty} (args : RArgs Γ ps os) (o : Nat) (f : Frame) (h : Heap),
      f BP = UInt64.ofNat bp → MEnvRel h bp env ρ S → FEnvRel f env ρ → args.Good ρ S env →
      args.ExtOk S →
      bp + n + o + args.frame ≤ UInt64.size → bp + n + o + args.frame ≤ L →
      ∃ f' h', Runs κ ω L (rargsPass args ρ (n + o)) f h f' h' ∧ f' BP = f BP ∧
        (∀ a, a < UInt64.size → ¬ InR (bp + n + o) args.frame a →
          h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
        MEnvRel h' (bp + n) (args.denote env) (args.locs o) (args.semS (bp + n) S env o)
  | _, _, .nil, _, f, h, _, _, _, _, _, _, _ => ⟨f, h, Runs.skip _ _, rfl, fun _ _ _ => rfl, trivial⟩
  | _, _, .own (t := t) a as, o, f, h, hf, henv, hfe, hg, hx, hb, hbL => by
    simp only [RArgs.frame] at hb hbL
    obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := n + o) hl
      (hl.away (by omega)) (by omega) (by omega) hf henv hfe hg.1 (by omega) (by omega) hx.1
    have henv₁ : MEnvRel (wr h (bp + (n + o)) B) bp env ρ S :=
      henv.above hl fun x hx => wr_out (by omega) (by omega) (by omega)
    obtain ⟨f', h', hr, hb', hout, hrel⟩ := rargsPass_runs hl as (o + t.size) f₁
      (wr h (bp + (n + o)) B) ((hf₁ BP (by decide) (by decide)).trans hf) henv₁ (hfe.keep hr₁.keep)
      hg.2 hx.2
      (by omega) (by omega)
    refine ⟨f', h', Runs.seq hr₁ (by rw [show n + o + t.size = n + (o + t.size) by omega]; exact hr),
      hb'.trans (hf₁ BP (by decide) (by decide)), fun x hx hn => ?_, ⟨fun _ => ?_, trivial, hrel⟩⟩
    · simp only [RArgs.frame, InR] at hn
      rw [hout x hx (by unfold InR; omega)]; exact wr_out (by omega) hx (by omega)
    · have e : rd h' (bp + n + o) t.size = B := by
        rw [rd_congr fun i hi => hout _ (by omega) (by unfold InR; omega), ← hBl, ← Nat.add_assoc,
          rd_wr _ _ _ (by omega)]
      exact VarRel.of_exact (by show Data.reprBytes _ (rd h' (bp + n + o) t.size); rw [e]; exact hBr)
  | _, _, .shr (t := t) p as, o, f, h, hf, henv, hfe, hg, hx, hb, hbL
  | _, _, .mut (t := t) p as, o, f, h, hf, henv, hfe, hg, hx, hb, hbL => by
    simp only [RArgs.frame] at hb hbL
    have hsw : 8 ≤ p.slotW := by cases p <;> simp [Place.slotW]
    obtain ⟨f₁, h₁, hr₁, hb₁, hout₁, hptr⟩ := argPass_runs (κ := κ) (ω := ω) (L := L) hl p (n + o) f h
      hf henv hfe hg.1 hx.1 (by omega) (by omega) (by omega)
    have henv₁ : MEnvRel h₁ bp env ρ S :=
      henv.above hl fun x hx => hout₁ x (by omega) (by unfold InR; omega)
    obtain ⟨f', h', hr, hb', hout, hrel⟩ := rargsPass_runs hl as (o + p.slotW) f₁ h₁
      (hb₁.trans hf) henv₁ (hfe.keep hr₁.keep) hg.2 hx.2 (by omega) (by omega)
    have hout' : ∀ a, a < UInt64.size → ¬ InR (bp + n + o) (p.slotW + as.frame) a →
        h' (UInt64.ofNat a) = h (UInt64.ofNat a) := fun x hx hn => by
      unfold InR at hn
      rw [hout x hx (by unfold InR; omega)]; exact hout₁ x hx (by unfold InR; omega)
    have henv' : MEnvRel h' bp env ρ S :=
      henv.above hl fun x hx => hout' x (by omega) (by unfold InR; omega)
    refine ⟨f', h', Runs.seq hr₁ (by rw [show n + o + p.slotW = n + (o + p.slotW) by omega]; exact hr),
      hb'.trans hb₁, hout', ⟨fun _ => (p.arg_get' hl henv' hg.1 hx.1).2, ?_, hrel⟩⟩
    have e1 : rd h' (bp + n + o) 8 = rd h₁ (bp + (n + o)) 8 := by
      rw [rd_congr fun i hi => hout _ (by omega) (by unfold InR; omega), Nat.add_assoc]
    cases hp2 : p.isPair2
    · rw [p.refLoc_borrowOk o hp2]
      show decodeLE (rd h' (bp + n + o) 8) = _
      rw [e1]; exact hptr.1
    · rw [p.refLoc_pair o hp2]
      have hs16 : p.slotW = 16 := by cases p <;> simp_all [Place.isPair2, Place.slotW]
      refine ⟨by rw [e1]; exact hptr.1, fun f'' A2 e => ?_⟩
      rw [rd_congr fun i hi => hout _ (by omega) (by unfold InR; omega),
        show bp + n + o + 8 = bp + (n + o) + 8 by omega]
      exact hptr.2 f'' A2 e

end

/-! ## The callee's layout -/

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {env : Env Γ}

/-- The storage of a reference parameter is its argument place's storage, below the caller's
watermark. -/
theorem argSI_In {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {t : Ty}
    (p : Place Γ t) (hg : p.ArgGood ρ S env) (hnp : p.NotPair S) {x : Nat}
    (hx : (p.argSI S env).In t x) : x < bp + n :=
  (p.arg_get' hl henv hg hnp).1.lt hx

theorem compat_own_head {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} {oh : Nat} {w : Bool} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o : Nat), oh + t.size ≤ o → as.Good ρ S env →
      as.ExtOk S → CompatAll (bp + n) t (.own oh) ⟨bp + n + oh, none, none, none⟩ w ps (as.locs o)
        (as.semS (bp + n) S env o) as.modeW
  | _, _, .nil, _, _, _, _ => trivial
  | _, _, .own (t := t') _ as, o, ho, hg, hx =>
    ⟨⟨Or.inl (by simp only [Loc.off, Loc.size]; omega), (fun _ _ e => by cases e),
      (fun _ _ e => by cases e),
      (fun _ x hx hx' => by simp only [SI.In_mk, InR, SI.sz_mk_none] at hx hx'; omega),
      (fun _ x hx hx' => by simp only [SI.In_mk, InR, SI.sz_mk_none] at hx hx'; omega)⟩,
     compat_own_head hl henv as (o + t'.size) (by omega) hg.2 hx.2⟩
  | _, _, .shr (t := t') p as, o, ho, hg, hx
  | _, _, .mut (t := t') p as, o, ho, hg, hx => by
    have hsw := p.slotW_ge
    have hsz := p.refLoc_size o t'
    rw [RArgs.locs]
    exact ⟨⟨Or.inl (by show oh + t.size ≤ (p.refLoc o).off; rw [p.refLoc_off]; omega),
      (fun _ _ e => by cases e),
      (fun o' w' e => by
        obtain ⟨rfl, hw'⟩ := p.refLoc_ptr e
        rw [SI.Out_mk, SI.sz_mk_none]; unfold Disj; right; omega),
      (fun _ x hy hy' => by
        simp only [SI.In_mk, InR, SI.sz_mk_none] at hy
        have := argSI_In hl henv p hg.1 hx.1 hy'; omega),
      (fun _ x hy hy' => by
        simp only [SI.In_mk, InR, SI.sz_mk_none] at hy'
        have := argSI_In hl henv p hg.1 hx.1 hy; omega)⟩,
     compat_own_head hl henv as (o + p.slotW) (by omega) hg.2 hx.2⟩

theorem compat_ref_head {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    {t : Ty} {oh : Nat} {wh : Bool} (ph : Place Γ t) (hgh : ph.ArgGood ρ S env) (hnph : ph.NotPair S)
    (hwh : wh = true → W.getD ph.root false = true) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o : Nat), oh + ph.slotW ≤ o → as.Good ρ S env →
      as.ExtOk S → as.Avoids ph.root ⟨wh, ph.path⟩ → as.mutW W →
      CompatAll (bp + n) t (ph.refLoc oh) (ph.argSI S env) wh ps (as.locs o)
        (as.semS (bp + n) S env o) as.modeW
  | _, _, .nil, _, _, _, _, _, _ => trivial
  | _, _, .own (t := t') _ as, o, ho, hg, hxo, hav, hmw => by
    have := (ph.arg_get' hl henv hgh hnph).1
    have hszh := ph.refLoc_size oh t
    exact ⟨⟨Or.inl (by
        show (ph.refLoc oh).off + Loc.size t (ph.refLoc oh) ≤ o
        rw [ph.refLoc_off]; omega),
      (fun o' w' e => by
        obtain ⟨rfl, hw'⟩ := ph.refLoc_ptr e
        rw [SI.Out_mk, SI.sz_mk_none]; unfold Disj; left; omega),
      (fun _ _ e => by cases e),
      (fun _ x hx hx' => by
        have := argSI_In hl henv ph hgh hnph hx
        simp only [SI.In_mk, InR, SI.sz_mk_none] at hx'; omega),
      (fun _ x hx hx' => by
        have := argSI_In hl henv ph hgh hnph hx'
        simp only [SI.In_mk, InR, SI.sz_mk_none] at hx; omega)⟩,
     compat_ref_head hl henv ph hgh hnph hwh as (o + t'.size) (by omega) hg.2 hxo.2
       hav.2 hmw⟩
  | _, _, .shr (t := t') q as, o, ho, hg, hxo, hav, hmw => by
    have h1 := (ph.arg_get' hl henv hgh hnph).1
    have h2 := (q.arg_get' hl henv hg.1 hxo.1).1
    have hszh := ph.refLoc_size oh t
    have hsz := q.refLoc_size o t'
    rw [RArgs.locs]
    refine ⟨⟨Or.inl (by simp only [ph.refLoc_off, q.refLoc_off]; omega),
      (fun o' w' e => by
        obtain ⟨rfl, -⟩ := ph.refLoc_ptr e; exact h2.out (by omega)),
      (fun o' w' e => by
        obtain ⟨rfl, -⟩ := q.refLoc_ptr e; exact h1.out (by omega)),
      (fun hw x hx hx' => ?_), (fun hw x hx hx' => by cases hw)⟩,
     compat_ref_head hl henv ph hgh hnph hwh as (o + q.slotW) (by have := q.slotW_ge; omega) hg.2 hxo.2
       hav.2 hmw⟩
    exfalso
    refine arg_disj' hl henv ph q hgh hg.1 hnph hxo.1 (fun hr => ?_)
      (fun _ => Or.inl (hwh hw)) x hx hx'
    have := hav.1.2 hr.symm
    simpa [Loan.blocks, hw] using this
  | _, _, .mut (t := t') q as, o, ho, hg, hxo, hav, hmw => by
    have h1 := (ph.arg_get' hl henv hgh hnph).1
    have h2 := (q.arg_get' hl henv hg.1 hxo.1).1
    have hszh := ph.refLoc_size oh t
    have hsz := q.refLoc_size o t'
    have hsame : ph.root = q.root → Sel.overlap ph.path q.path = false := fun hr => by
      have := hav.1.2 hr.symm
      simpa [Loan.blocks] using this
    rw [RArgs.locs]
    refine ⟨⟨Or.inl (by simp only [ph.refLoc_off, q.refLoc_off]; omega),
      (fun o' w' e => by
        obtain ⟨rfl, -⟩ := ph.refLoc_ptr e; exact h2.out (by omega)),
      (fun o' w' e => by
        obtain ⟨rfl, -⟩ := q.refLoc_ptr e; exact h1.out (by omega)),
      (fun hw x hx hx' => ?_), (fun _ x hx hx' => ?_)⟩,
     compat_ref_head hl henv ph hgh hnph hwh as (o + q.slotW) (by have := q.slotW_ge; omega) hg.2 hxo.2
       hav.2 hmw.2⟩
    · exact absurd hx' (arg_disj' hl henv ph q hgh hg.1 hnph hxo.1 hsame
        (fun _ => Or.inl (hwh hw)) x hx)
    · exact absurd hx (arg_disj' hl henv ph q hgh hg.1 hnph hxo.1 hsame
        (fun _ => Or.inr hmw.1) x hx')

/-- A reference parameter's slot, which holds an address or for the pair `q[i], q[j]` two, is below
the callee's watermark, and its storage, the argument place's, is below the caller's. -/
theorem arg_single {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {t : Ty}
    (p : Place Γ t) (hg : p.ArgGood ρ S env) (hnp : p.NotPair S) (o m : Nat) (w : Bool)
    (hm : o + p.slotW ≤ m) :
    Single (bp + n) m t (p.refLoc o) (p.argSI S env) w := by
  have hb := (p.arg_get' hl henv hg hnp).1
  have hsz := p.refLoc_size o t
  refine ⟨by rw [p.refLoc_off]; omega, ?_, fun _ => Place.argSI_hole _ _ _,
    fun H e => by rw [Place.argSI_hole] at e; cases e⟩
  cases hp2 : p.isPair2
  · rw [p.refLoc_borrowOk o hp2]
    have hs := Place.argSI_snd S env p hp2
    simp only [SI.Below, hs] at hb
    exact ⟨hs, by omega, Or.inr (by omega)⟩
  · rw [p.refLoc_pair o hp2]
    cases p with
    | @pair2 T N _ q i j =>
      have hd := (pair2_at (W := W) hl henv q i j hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2).disj
      exact ⟨pairSI_pair hd, hb.mono (by omega), hb.out (by omega)⟩
    | @pair2S T N _ m' i j =>
      have hd := (pair2S_at (W := W) hl henv m' i j hg.2.2.1 hg.2.2.2.1).disj
      exact ⟨pairSI_pair hd, hb.mono (by omega), hb.out (by omega)⟩
    | _ => simp [Place.isPair2] at hp2

/-- The callee's layout has its parameters' slots, its owned parameters in its region, and its
reference parameters at their argument places' storage, which the borrow checker separates. -/
theorem rargs_lay {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) :
    ∀ {ps os : List Ty} (args : RArgs Γ ps os) (o : Nat), args.Good ρ S env → args.ExtOk S →
      args.Sep → args.mutW W →
      Lay (bp + n) (o + args.frame) ps (args.locs o) (args.semS (bp + n) S env o) args.modeW
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .own (t := t) a as, o, hg, hx, hsep, hmw => by
    have ih := rargs_lay hl henv as (o + t.size) hg.2 hx.2 hsep hmw
    simp only [RArgs.frame, ← Nat.add_assoc] at ih ⊢
    exact ⟨⟨by simp only [Loc.off, Loc.size]; omega, ⟨rfl, rfl, rfl⟩, (fun _ => rfl),
      (fun H e => by cases e)⟩, compat_own_head hl henv as (o + t.size) (Nat.le_refl _) hg.2 hx.2,
      ih⟩
  | _, _, .shr (t := t) p as, o, hg, hx, hsep, hmw => by
    have ih := rargs_lay hl henv as (o + p.slotW) hg.2 hx.2 hsep.2 hmw
    simp only [RArgs.frame, ← Nat.add_assoc] at ih ⊢
    rw [RArgs.locs]
    exact ⟨arg_single hl henv p hg.1 hx.1 o _ false (by omega),
      compat_ref_head hl henv p hg.1 hx.1 (fun e => by cases e) as (o + p.slotW)
        (by omega) hg.2 hx.2 hsep.1 hmw, ih⟩
  | _, _, .mut (t := t) p as, o, hg, hx, hsep, hmw => by
    have ih := rargs_lay hl henv as (o + p.slotW) hg.2 hx.2 hsep.2 hmw.2
    simp only [RArgs.frame, ← Nat.add_assoc] at ih ⊢
    rw [RArgs.locs]
    exact ⟨arg_single hl henv p hg.1 hx.1 o _ true (by omega),
      compat_ref_head hl henv p hg.1 hx.1 (fun _ => hmw.1) as (o + p.slotW)
        (by omega) hg.2 hx.2 hsep.1 hmw.2, ih⟩

end

/-! ## The `&mut` arguments -/

/-- `x` is in the storage of one of the `&mut` argument places. -/
def _root_.Millipede.RArgs.InMut {Γ : List Ty} (S : List SI) (env : Env Γ) (x : Nat) :
    {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => False
  | _, _, .own _ as => as.InMut S env x
  | _, _, .shr _ as => as.InMut S env x
  | _, _, .mut (t := t) p as => (p.argSI S env).In t x ∨ as.InMut S env x

/-- The `&mut` argument places are usable. -/
def _root_.Millipede.RArgs.MutGood {Γ : List Ty} (ρ : List Loc) (S : List SI) (env : Env Γ) :
    {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own _ as => as.MutGood ρ S env
  | _, _, .shr _ as => as.MutGood ρ S env
  | _, _, .mut p as => p.ArgGood ρ S env ∧ as.MutGood ρ S env

theorem _root_.Millipede.RArgs.Good.mutGood {Γ : List Ty} {S : List SI} {env : Env Γ} :
    {ps os : List Ty} → {as : RArgs Γ ps os} → as.Good ρ S env → as.MutGood ρ S env
  | _, _, .nil, _ => trivial
  | _, _, .own _ as, h => RArgs.Good.mutGood (as := as) h.2
  | _, _, .shr _ as, h => RArgs.Good.mutGood (as := as) h.2
  | _, _, .mut _ as, h => ⟨h.1, RArgs.Good.mutGood (as := as) h.2⟩

/-- The bytes of each `&mut` argument place's storage hold the matching component of the
handed-back tuple, whose bytes are `TB`. For a slice, the component is the first `len` elements of
the view. -/
def _root_.Millipede.RArgs.CompAt {Γ : List Ty} (S : List SI) (env : Env Γ) (m : Heap) :
    {ps os : List Ty} → RArgs Γ ps os → List UInt8 → Prop
  | _, _, .nil, _ => True
  | _, _, .own _ as, TB => as.CompAt S env m TB
  | _, _, .shr _ as, TB => as.CompAt S env m TB
  | _, _, .mut (t := t) (os := os') p as, TB =>
    slice TB 0 ((p.argSI S env).sz t) = rdS m (p.argSI S env) ((p.argSI S env).sz t) ∧
      as.CompAt S env m (slice TB (fieldOff (Data.shape (t.carrier × (Ty.tup os').carrier)) 1)
        (Ty.tup os').size)

theorem _root_.Millipede.RArgs.inW_semS {Γ : List Ty} {S : List SI} {env : Env Γ} {bp' x : Nat} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o : Nat),
      InW ps (as.semS bp' S env o) as.modeW x → bp' + o ≤ x ∨ as.InMut S env x
  | _, _, .nil, _, h => (h : False).elim
  | _, _, .own (t := t) _ as, o, h => by
    rcases h with ⟨_, h⟩ | h
    · left; simp only [SI.In_mk, InR] at h; omega
    · rcases RArgs.inW_semS as (o + t.size) h with h | h
      · left; omega
      · right; exact h
  | _, _, .shr p as, o, h => by
    rcases h with ⟨e, _⟩ | h
    · cases e
    · rcases RArgs.inW_semS as (o + p.slotW) h with h | h
      · left; omega
      · right; exact h
  | _, _, .mut p as, o, h => by
    rcases h with ⟨_, h⟩ | h
    · right; exact Or.inl h
    · rcases RArgs.inW_semS as (o + p.slotW) h with h | h
      · left; omega
      · right; exact Or.inr h

theorem _root_.Millipede.RArgs.inMut_inW {Γ : List Ty} {S : List SI} {W : List Bool} {env : Env Γ}
    {x : Nat} {h : Heap} {bp n : Nat} {ρ : List Loc} {W' : List Bool} (henv : MEnvRel h bp env ρ S)
    (hl : Lay bp n Γ ρ S W') :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os), as.MutGood ρ S env → as.ExtOk S → as.mutW W →
      as.InMut S env x → InW Γ S W x
  | _, _, .nil, _, _, _, h => h.elim
  | _, _, .own _ as, hg, hx, hw, h => RArgs.inMut_inW henv hl as hg hx.2 hw h
  | _, _, .shr _ as, hg, hx, hw, h => RArgs.inMut_inW henv hl as hg hx.2 hw h
  | _, _, .mut p as, hg, hx, hw, h => by
    rcases h with h | h
    · exact InW.place p hw.1 (p.arg_in' henv hl hg.1 hx.1 h) hl.length.2
    · exact RArgs.inMut_inW henv hl as hg.2 hx.2 hw.2 h

/-- The in-place components of a callee are its `&mut` parameters, which are writable. -/
theorem _root_.Millipede.RArgs.mutIdx_modeW {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j x : Nat), x ∈ as.mutIdx j →
      j ≤ x ∧ as.modeW.getD (x - j) false = true
  | _, _, .nil, _, _, h => by simp [RArgs.mutIdx] at h
  | _, _, .own _ as, j, x, h => by
    have := RArgs.mutIdx_modeW as (j + 1) x h
    refine ⟨by omega, ?_⟩
    rw [show x - j = (x - (j + 1)) + 1 by omega]; simpa [RArgs.modeW] using this.2
  | _, _, .shr _ as, j, x, h => by
    have := RArgs.mutIdx_modeW as (j + 1) x h
    refine ⟨by omega, ?_⟩
    rw [show x - j = (x - (j + 1)) + 1 by omega]; simpa [RArgs.modeW] using this.2
  | _, _, .mut _ as, j, x, h => by
    simp only [RArgs.mutIdx, List.mem_cons] at h
    rcases h with rfl | h
    · simp [RArgs.modeW]
    · have := RArgs.mutIdx_modeW as (j + 1) x h
      refine ⟨by omega, ?_⟩
      rw [show x - j = (x - (j + 1)) + 1 by omega]; simpa [RArgs.modeW] using this.2

theorem callTl_ok {Γ ps os : List Ty} (r : Ty) (as : RArgs Γ ps os) (ρ : List Loc) :
    (callTl r as).Ok as.modeW ρ := by
  intro c hc
  have := RArgs.mutIdx_modeW as 0 c.1 (List.of_mem_zip hc).1
  simpa using this.2

/-- The components the callee's tail mode leaves in place are the `&mut` argument places. -/
theorem _root_.Millipede.RArgs.compAt_of {Γ : List Ty} {S : List SI} {env : Env Γ} {m : Heap}
    {bp' : Nat} {SS : List SI} (bs : List UInt8) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j o b : Nat),
      (∀ i, SS.getD (j + i) default = (as.semS bp' S env o).getD i default) →
      (∀ c ∈ (as.mutIdx j).zip ((tupOffs os b).zip (os.map Ty.size)),
        slice bs c.2.1 ((SS.getD c.1 default).lim c.2.2) =
          rdS m (SS.getD c.1 default) ((SS.getD c.1 default).lim c.2.2)) →
      as.CompAt S env m (slice bs b (Ty.tup os).size)
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .own (t := t) _ as, j, o, b, hal, hc =>
    RArgs.compAt_of bs as (j + 1) (o + t.size) b (fun i => by
      rw [show j + 1 + i = j + (i + 1) by omega, hal (i + 1)]; rfl) hc
  | _, _, .shr p as, j, o, b, hal, hc =>
    RArgs.compAt_of bs as (j + 1) (o + p.slotW) b (fun i => by
      rw [show j + 1 + i = j + (i + 1) by omega, hal (i + 1)]; rfl) hc
  | _, _, .mut (t := t) (os := os') p as, j, o, b, hal, hc => by
    have hs := sndOff_add_le t (Ty.tup os')
    have hf := fst_le_sndOff t (Ty.tup os')
    simp only [RArgs.mutIdx, tupOffs, List.map_cons, List.zip_cons_cons, List.mem_cons,
      forall_eq_or_imp] at hc
    obtain ⟨h0, hc⟩ := hc
    have e := hal 0
    rw [Nat.add_zero] at e
    simp only [e] at h0
    have e0 : (RArgs.semS bp' S env (RArgs.mut p as) o).getD 0 default = p.argSI S env := rfl
    rw [e0] at h0
    have hsz := (p.argSI S env).sz_le t
    refine ⟨?_, ?_⟩
    · rw [slice_slice bs b (Ty.tup (t :: os')).size 0 _
        (by simp only [Nat.zero_add]; show _ ≤ (Ty.pair t (Ty.tup os')).size; omega), Nat.add_zero]
      exact h0
    · rw [slice_slice bs b (Ty.tup (t :: os')).size _ _ hs]
      exact RArgs.compAt_of bs as (j + 1) (o + p.slotW) _ (fun i => by
        rw [show j + 1 + i = j + (i + 1) by omega, hal (i + 1)]; rfl) hc

/-! ## The sequential write-backs -/

theorem _root_.Millipede.Place.backOk_eqExcept {Γ : List Ty} {k : Nat} {π : List Sel} {t : Ty}
    (q : Place Γ t) (hq : q.IdxAvoids k ⟨true, π⟩) {env env' : Env Γ} (he : EqExcept k env env')
    (v : t.carrier) (h : q.backOk env v) : q.backOk env' v := by
  cases q with
  | range q lo len => intro j hj; rw [← len.denote_eqExcept hq.2.2 he] at hj; exact h j hj
  | rangeS m lo len => intro j hj; rw [← len.denote_eqExcept hq.2 he] at hj; exact h j hj
  | _ => trivial

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}

/-- The handed-back values of the `&mut` arguments that are variables passed on whole are views of
those variables' extents. The callee's exact hand-back condition provides this. -/
def _root_.Millipede.RArgs.ViewBack {Γ : List Ty} (S : List SI) (env : Env Γ) :
    {ps os : List Ty} → RArgs Γ ps os → (Ty.tup os).carrier → Prop
  | _, _, .nil, _ => True
  | _, _, .own _ as, vs => as.ViewBack S env vs
  | _, _, .shr _ as, vs => as.ViewBack S env vs
  | _, _, .mut (t := t) p as, vs =>
    (p.isVarAt p.root = true → ∀ e, (p.argSI S env).ext = some e → ViewOK t vs.1 e) ∧
      as.ViewBack S env vs.2

/-- After the call, the caller's memory represents the sequential lens write-backs. Each `&mut`
argument place's storage holds its handed-back component, which for a slice means its full cells,
and nothing else below the watermark changed. The later argument places are where they were at
the call, because the borrow checker separates them, and their obligations still hold. -/
theorem writeBack_rel (hl : Lay bp n Γ ρ S W) (hbn : bp + n ≤ UInt64.size) (m : Heap) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (env : Env Γ) (m₀ : Heap)
      (vs : (Ty.tup os).carrier) (TB : List UInt8) (prev : List (Nat × (Nat × Nat))),
      MEnvRel m₀ bp env ρ S → as.MutGood ρ S env → as.ExtOk S → as.Sep → as.mutW W →
      as.mutOk prev = true → as.backOk env vs → as.ViewBack S env vs →
      Data.reprBytes vs TB → as.CompAt S env m TB →
      (∀ a, a < bp + n → ¬ as.InMut S env a → m (UInt64.ofNat a) = m₀ (UInt64.ofNat a)) →
      MEnvRel m bp (as.writeBack env vs) ρ S
  | _, _, .nil, env, m₀, _, _, _, henv, _, _, _, _, _, _, _, _, _, hm =>
    henv.congr fun x hx => hm x (hl.vis_lt hx) id
  | _, _, .own _ as, env, m₀, vs, TB, prev, henv, hg, hx, hsep, hw, hmo, hbk, hvb, hvs, hc, hm =>
    writeBack_rel hl hbn m as env m₀ vs TB prev henv hg hx.2 hsep hw hmo hbk hvb hvs hc hm
  | _, _, .shr _ as, env, m₀, vs, TB, prev, henv, hg, hx, hsep, hw, hmo, hbk, hvb, hvs, hc, hm =>
    writeBack_rel hl hbn m as env m₀ vs TB prev henv hg hx.2 hsep.2 hw hmo hbk hvb hvs hc hm
  | _, _, .mut (t := t) (os := os') p as, env, m₀, vs, TB, prev, henv, hg, hx, hsep, hw, hmo,
      hbk, hvb, hvs, hc, hm => by
    obtain ⟨hgp, hg⟩ := hg
    simp only [RArgs.mutOk, Bool.and_eq_true] at hmo
    have hpb := (p.arg_get' hl henv hgp hx.1).1
    obtain ⟨hv1, hv2⟩ := pair_repr vs TB hvs
    -- the memory with only this place updated
    let m₁ : Heap := fun x =>
      if (p.argSI S env).In t x.toNat then m x else m₀ x
    have hm₁ : ∀ a, a < UInt64.size → m₁ (UInt64.ofNat a) =
        if (p.argSI S env).In t a then m (UInt64.ofNat a)
        else m₀ (UInt64.ofNat a) :=
      fun a ha => by simp only [m₁, UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha]
    have henv₁ := p.arg_set' hl henv hbn hgp hx.1 hw.1 m₁ vs.1 hbk.1 hvb.1
      (fun a ha hn => by rw [hm₁ a (by omega), ite_eq_right hn]) _ hv1
      (by
        rw [rdS_congr (h' := m₁) (h := m) fun i hi => by
          have := hpb.lt (SI.In_at hi)
          rw [hm₁ _ (by omega), ite_eq_left (SI.In_at hi)]]
        rw [slice_slice TB 0 t.size 0 _ (by have := (p.argSI S env).sz_le t; omega), Nat.add_zero]
        exact hc.1)
    -- the later places are where they were
    have he : EqExcept p.root env (p.set env vs.1) := p.set_eqExcept env vs.1
    have hav := hsep.1
    have hmut : ∀ {ps₂ os₂ : List Ty} (bs : RArgs Γ ps₂ os₂), bs.Avoids p.root ⟨true, p.path⟩ →
        (∀ a, bs.InMut S (p.set env vs.1) a ↔ bs.InMut S env a) ∧
        (∀ TB', bs.CompAt S env m TB' → bs.CompAt S (p.set env vs.1) m TB') := by
      intro ps₂ os₂ bs hbs
      induction bs with
      | nil => exact ⟨fun _ => Iff.rfl, fun _ h => h⟩
      | own _ _ ih => exact ih hbs.2
      | shr _ _ ih => exact ih hbs.2
      | «mut» q _ ih =>
        obtain ⟨ih1, ih2⟩ := ih hbs.2
        refine ⟨fun a => ?_, fun TB' h => ⟨by rw [← q.argSI_eqExcept hbs.1.1 he]; exact h.1, ih2 _ h.2⟩⟩
        simp only [RArgs.InMut]; rw [← q.argSI_eqExcept hbs.1.1 he, ih1]
    have hgood : ∀ {ps₂ os₂ : List Ty} (bs : RArgs Γ ps₂ os₂) (rs : List (Nat × (Nat × Nat))),
        (p.root, p.setWin) ∈ rs →
        bs.Avoids p.root ⟨true, p.path⟩ → bs.MutGood ρ S env → bs.mutOk rs = true →
        bs.MutGood ρ S (p.set env vs.1) := by
      intro ps₂ os₂ bs rs hrs hbs hgb hmb
      induction bs generalizing rs with
      | nil => trivial
      | own _ _ ih => exact ih rs hrs hbs.2 hgb hmb
      | shr _ _ ih => exact ih rs hrs hbs.2 hgb hmb
      | «mut» q _ ih =>
        simp only [RArgs.mutOk, Bool.and_eq_true] at hmb
        obtain ⟨⟨hcq, hLq, hokq, hnhq, hnsq⟩, hgb⟩ := hgb
        refine ⟨⟨hcq, hLq, ?_, hnhq, hnsq⟩,
          ih ((q.root, q.setWin) :: rs) (List.mem_cons_of_mem _ hrs) hbs.2 hgb hmb.2⟩
        by_cases hr : q.root = p.root
        · -- an earlier write on the same root: the cells of `q` are apart from its window
          have h := List.all_eq_true.mp hmb.1 _ hrs
          simp only [hr, bne_self_eq_false, Bool.false_or] at h
          exact p.ok_of_slotsAway env vs.1 hgp.2.2.1 q hr h hbs.1.1 hokq
        · exact q.ok_eqExcept (Or.inl hr) hbs.1.1 he hokq
    have hback : ∀ {ps₂ os₂ : List Ty} (bs : RArgs Γ ps₂ os₂) (ws : (Ty.tup os₂).carrier),
        bs.Avoids p.root ⟨true, p.path⟩ → bs.backOk env ws → bs.backOk (p.set env vs.1) ws := by
      intro ps₂ os₂ bs ws hbs hb
      induction bs with
      | nil => trivial
      | own _ _ ih => exact ih ws hbs.2 hb
      | shr _ _ ih => exact ih ws hbs.2 hb
      | «mut» q _ ih => exact ⟨q.backOk_eqExcept hbs.1.1 he _ hb.1, ih ws.2 hbs.2 hb.2⟩
    have hvback : ∀ {ps₂ os₂ : List Ty} (bs : RArgs Γ ps₂ os₂) (ws : (Ty.tup os₂).carrier),
        bs.Avoids p.root ⟨true, p.path⟩ → bs.ViewBack S env ws → bs.ViewBack S (p.set env vs.1) ws := by
      intro ps₂ os₂ bs ws hbs hb
      induction bs with
      | nil => trivial
      | own _ _ ih => exact ih ws hbs.2 hb
      | shr _ _ ih => exact ih ws hbs.2 hb
      | «mut» q _ ih =>
        exact ⟨by rw [← q.argSI_eqExcept hbs.1.1 he]; exact hb.1, ih ws.2 hbs.2 hb.2⟩
    exact writeBack_rel hl hbn m as (p.set env vs.1) m₁ vs.2 _ ((p.root, p.setWin) :: prev) henv₁
      (hgood as ((p.root, p.setWin) :: prev) (List.mem_cons_self) hav hg hmo.2) hx.2 hsep.2 hw.2 hmo.2
      (hback as vs.2 hav hbk.2) (hvback as vs.2 hav hvb.2) hv2
      ((hmut as hav).2 _ hc.2)
      (fun a ha hn => by
        rw [(hmut as hav).1] at hn
        rw [hm₁ a (by omega)]
        split
        · rfl
        · rename_i hin
          exact hm a ha fun h => h.elim hin hn)

end

/-! ## The write-back condition of slice arguments, from the callee's hand-back condition -/

theorem _root_.Millipede.RArgs.views_succ {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat),
      as.views (j + 1) = (as.views j).map fun c => (c.1 + 1, c.2)
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, j => RArgs.views_succ as (j + 1)
  | _, _, .shr p as, j => by
    simp only [RArgs.views, RArgs.views_succ as (j + 1), List.map_append]; split <;> simp
  | _, _, .mut p as, j => by
    simp only [RArgs.views, RArgs.views_succ as (j + 1), List.map_append]; split <;> simp

/-- The write-back conditions of the slice arguments follow from what the callee's hand-back
condition gives for each `&mut` slice parameter. -/
theorem _root_.Millipede.RArgs.backOk_of {Γ : List Ty} (env : Env Γ) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (vs : (Ty.tup os).carrier)
      (pre : List (Option (List Bool))), as.ok env →
      (∀ i, (i, true) ∈ as.views 0 → ∀ len, OccsFull len ((as.denote env).occsAt i) →
        CompFull len ((as.denote env).occsLen ((as.mutIdx 0).filter (i < ·))) (pre ++ Data.occs vs)) →
      as.backOk env vs
  | _, _, .nil, _, _, _, _ => trivial
  | _, _, .own a as, vs, pre, hok, h => RArgs.backOk_of env as vs pre hok fun i hi len hF => by
      have hmem : (i + 1, true) ∈ (RArgs.own a as).views 0 := by
        simp only [RArgs.views, RArgs.views_succ]; exact List.mem_map.mpr ⟨_, hi, rfl⟩
      have := h (i + 1) hmem len hF
      simpa [RArgs.denote, RArgs.mutIdx, RArgs.mutIdx_succ, List.filter_map, Function.comp_def,
        Env.occsLen] using this
  | _, _, .shr q as, vs, pre, hok, h => RArgs.backOk_of env as vs pre hok.2 fun i hi len hF => by
      have hmem : (i + 1, true) ∈ (RArgs.shr q as).views 0 := by
        simp only [RArgs.views, RArgs.views_succ, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨_, hi, rfl⟩)
      have := h (i + 1) hmem len hF
      simpa [RArgs.denote, RArgs.mutIdx, RArgs.mutIdx_succ, List.filter_map, Function.comp_def,
        Env.occsLen] using this
  | _, _, .mut (t := t) (os := os') p as, vs, pre, hok, h => by
    obtain ⟨v, vs'⟩ := vs
    have e : Data.occs (α := (Ty.tup (t :: os')).carrier) (v, vs') = Data.occs v ++ Data.occs vs' :=
      Data.occs_pair v vs'
    refine ⟨?_, RArgs.backOk_of env as vs' (pre ++ Data.occs v) hok.2 fun i hi len hF => ?_⟩
    · -- the slice's handed-back view is the last component of a full one
      have hP : ((RArgs.mut p as).denote env).occsLen
          (((RArgs.mut p as).mutIdx 0).filter (0 < ·)) = (Data.occs vs').length := by
        have hfilt : ((as.mutIdx 0).map (· + 1)).filter (0 < ·) = (as.mutIdx 0).map (· + 1) := by
          rw [List.filter_eq_self]; intro x hx
          obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; simp
        simp only [RArgs.mutIdx, RArgs.mutIdx_succ, RArgs.denote, List.filter_cons,
          Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [hfilt, Env.occsLen_cons, RArgs.occs_length env as vs']
      have gen : ∀ {T : Ty} {N : Nat} (v' : Slots T.carrier N), Data.occs v' = Data.occs v →
          ∀ L, OccsFull L (((RArgs.mut p as).denote env).occsAt 0) → p.isRange = true →
          ∀ k, k < L → v'.isFull k = true := by
        intro T N v' hv' L hF hr k hk
        have := h 0 (by simp [RArgs.views, hr]) _ hF
        rw [hP, e, ← hv', Slots.occs_eq] at this
        simp only [List.singleton_append] at this
        obtain ⟨l, hl, hf⟩ := compFull_split this
        simp only [Option.some.injEq] at hl
        rw [← Slots.getD_occ, hl]; exact hf k hk
      cases p with
      | @range T N q lo len =>
        have hfit := hok.1.2
        exact gen v rfl _ ⟨_, Slots.occs_eq _, fun k hk => by
            rw [Slots.getD_occ]; simp only [Place.get, vview_isFull]; simp; omega⟩ rfl
      | @rangeS T N m lo len =>
        exact gen v rfl _ ⟨_, Slots.occs_eq _, fun k hk => by
            rw [Slots.getD_occ]; exact sview_full _ hok.1.1 hok.1.2 hk⟩ rfl
      | _ => trivial
    · have hmem : (i + 1, true) ∈ (RArgs.mut p as).views 0 := by
        simp only [RArgs.views, RArgs.views_succ, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨_, hi, rfl⟩)
      have := h (i + 1) hmem len hF
      rw [e, ← List.append_assoc] at this
      simpa [RArgs.denote, RArgs.mutIdx, RArgs.mutIdx_succ, List.filter_map, Function.comp_def,
        Env.occsLen] using this

/-! ## The case lemma -/

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem conf_callRef {Γ ps os : List Ty} {r u : Ty} {name : String} {req : Env ps → Prop}
    {body : Exp ps (.pair r (.tup os))} {args : RArgs Γ ps os} {k : Exp (r :: Γ) u} {tm : Tl}
    (h : (Exp.callRef name req body args k).Conf tm = true) : k.Conf tm.up = true := by
  cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using h

theorem semS_hole {Γ : List Ty} {S : List SI} {env : Env Γ} {bp' : Nat} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o i : Nat),
      ((as.semS bp' S env o).getD i default).hole = none
  | _, _, .nil, _, _ => rfl
  | _, _, .own (t := t) _ as, o, i => by
    cases i with
    | zero => rfl
    | succ i => simp only [RArgs.semS, List.getD_cons_succ]; exact semS_hole as _ i
  | _, _, .shr p as, o, i => by
    cases i with
    | zero => exact Place.argSI_hole _ _ p
    | succ i => simp only [RArgs.semS, List.getD_cons_succ]; exact semS_hole as _ i
  | _, _, .mut p as, o, i => by
    cases i with
    | zero => exact Place.argSI_hole _ _ p
    | succ i => simp only [RArgs.semS, List.getD_cons_succ]; exact semS_hole as _ i

/-- The view lists of the arguments after one more parameter. -/
theorem views_mem_succ {Γ : List Ty} {ps os : List Ty} (as : RArgs Γ ps os) {i : Nat} {m : Bool}
    (hm : (i, m) ∈ as.views 0) (l : List (Nat × Bool)) : (i + 1, m) ∈ l ++ as.views 1 := by
  rw [RArgs.views_succ]; exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, rfl⟩)

theorem _root_.Millipede.RArgs.pairs_succ {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat),
      as.pairs (j + 1) = (as.pairs j).map (· + 1)
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, j => RArgs.pairs_succ as (j + 1)
  | _, _, .shr p as, j => by
    simp only [RArgs.pairs, RArgs.pairs_succ as (j + 1), List.map_append]; split <;> simp
  | _, _, .mut p as, j => by
    simp only [RArgs.pairs, RArgs.pairs_succ as (j + 1), List.map_append]; split <;> simp

theorem pairs_mem_succ {Γ : List Ty} {ps os : List Ty} (as : RArgs Γ ps os) {i : Nat}
    (hm : i ∈ as.pairs 0) (l : List Nat) : i + 1 ∈ l ++ as.pairs 1 := by
  rw [RArgs.pairs_succ]; exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, rfl⟩)

/-- A callee's parameter with an extent is a slice argument, a pair of elements, or a view passed
on whole. For a view passed on whole, the caller's `RArgs.VSafe` requires the callee to use the
parameter through its elements, and for `&mut` also to hand it back exactly. -/
theorem semS_ext {Γ : List Ty} {S : List SI} {env : Env Γ} {bp' : Nat} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o i : Nat),
      ((as.semS bp' S env o).getD i default).ext ≠ none →
      (∃ m, (i, m) ∈ as.views 0) ∨ i ∈ as.pairs 0 ∨
        ∃ x, (S.getD x default).ext ≠ none ∧
          ∀ vok mok j, as.VSafe x vok mok j = true → vok (j + i) = true ∨ mok (j + i) = true
  | _, _, .nil, _, _, h => absurd rfl h
  | _, _, .own (t := t) _ as, o, i, h => by
    cases i with
    | zero => exact absurd rfl h
    | succ i =>
      simp only [RArgs.semS, List.getD_cons_succ] at h
      rcases semS_ext as _ i h with ⟨m, hm⟩ | hp | ⟨x, hxe, hv⟩
      · exact Or.inl ⟨m, by simpa [RArgs.views] using views_mem_succ as hm []⟩
      · exact Or.inr (Or.inl (by simpa [RArgs.pairs] using pairs_mem_succ as hp []))
      · refine Or.inr (Or.inr ⟨x, hxe, fun vok mok j h' => ?_⟩)
        simp only [RArgs.VSafe, Bool.and_eq_true] at h'
        have := hv vok mok (j + 1) h'.2; rwa [show j + 1 + i = j + (i + 1) by omega] at this
  | _, _, .shr p as, o, i, h | _, _, .mut p as, o, i, h => by
    cases i with
    | zero =>
      cases p with
      | range =>
        simp only [RArgs.views, Place.isRange, ↓reduceIte]
        exact Or.inl ⟨_, List.mem_append_left _ (List.mem_singleton_self _)⟩
      | pair2 =>
        simp only [RArgs.pairs, Place.isPair2, ↓reduceIte]
        exact Or.inr (Or.inl (List.mem_append_left _ (List.mem_singleton_self _)))
      | rangeS =>
        simp only [RArgs.views, Place.isRange, ↓reduceIte]
        exact Or.inl ⟨_, List.mem_append_left _ (List.mem_singleton_self _)⟩
      | pair2S =>
        simp only [RArgs.pairs, Place.isPair2, ↓reduceIte]
        exact Or.inr (Or.inl (List.mem_append_left _ (List.mem_singleton_self _)))
      | var m =>
        refine Or.inr (Or.inr ⟨m.idx, by simpa [RArgs.semS, Place.argSI] using h,
          fun vok mok j h' => ?_⟩)
        simp only [RArgs.VSafe, Place.VSafe, Place.isVarAt, beq_self_eq_true, Bool.not_true,
          Bool.and_false, Bool.true_and, Bool.false_or, Bool.and_eq_true] at h'
        simp [h'.1]
      | _ => exact absurd rfl h
    | succ i =>
      simp only [RArgs.semS, List.getD_cons_succ] at h
      rcases semS_ext as _ i h with ⟨m, hm⟩ | hp | ⟨x, hxe, hv⟩
      · exact Or.inl ⟨m, by simp only [RArgs.views]; exact views_mem_succ as hm _⟩
      · exact Or.inr (Or.inl (by simp only [RArgs.pairs]; exact pairs_mem_succ as hp _))
      · refine Or.inr (Or.inr ⟨x, hxe, fun vok mok j h' => ?_⟩)
        simp only [RArgs.VSafe, Bool.and_eq_true] at h'
        have := hv vok mok (j + 1) h'.2; rwa [show j + 1 + i = j + (i + 1) by omega] at this

/-- The handed-back values of the views passed on whole are views of the same extents, if they
have the views' occupancies. -/
theorem _root_.Millipede.RArgs.viewBack_of {Γ : List Ty} {S : List SI} {env : Env Γ} {h : Heap}
    {bp n : Nat} {ρ : List Loc} {W : List Bool} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (vs : (Ty.tup os).carrier), as.ExtOk S →
      (∀ x, (S.getD x default).ext ≠ none → as.WholeP x (· = env.occsAt x) vs) →
      as.ViewBack S env vs
  | _, _, .nil, _, _, _ => trivial
  | _, _, .own _ as, vs, hxo, hx => RArgs.viewBack_of hl henv as vs hxo.2 hx
  | _, _, .shr _ as, vs, hxo, hx => RArgs.viewBack_of hl henv as vs hxo.2 hx
  | _, _, .mut p as, vs, hxo, hx => by
    refine ⟨fun hv e he => ?_, RArgs.viewBack_of hl henv as vs.2 hxo.2 fun x h' => (hx x h').2⟩
    have hs := hxo.1 hv
    obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
    have he' : (S.getD m.idx default).ext = some e := by simpa [Place.argSI] using he
    have hW : Data.occs vs.1 = env.occsAt m.idx := (hx m.idx (by rw [he']; nofun)).1 (by simp [Place.isVarAt])
    rw [Env.occsAt_get] at hW
    obtain ⟨_, _, _, hvo⟩ := (henv.get m ((hl.var m).ns_of_ext (Or.inl (by rw [he']; nofun)))).1
    exact ViewOK.of_occs (hvo e he' hs) hW

/-- A `&mut` argument that is the view itself is allowed by `RArgs.VSafe` only with `mok`. -/
theorem _root_.Millipede.RArgs.vsafe_mok {Γ : List Ty} {x : Nat} {vok mok : Nat → Bool} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j j' : Nat), as.VSafe x vok mok j = true →
      j' ∈ as.mutVarAt x 0 → mok (j + j') = true
  | _, _, .nil, _, _, _, h => by simp [RArgs.mutVarAt] at h
  | _, _, .own _ as, j, j', hk, h | _, _, .shr _ as, j, j', hk, h => by
    simp only [RArgs.VSafe, Bool.and_eq_true] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ] at h
    obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
    have := RArgs.vsafe_mok as (j + 1) j'' hk.2 hj''
    rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this
  | _, _, .mut p as, j, j', hk, h => by
    simp only [RArgs.VSafe, Bool.and_eq_true, Bool.or_eq_true] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hv
        simp only [List.mem_singleton] at h; subst h
        rcases hk.1 with hk1 | ⟨_, hb'⟩
        · simp [Place.VSafe, hv] at hk1
        · simpa using hb'
      · simp at h
    · obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
      have := RArgs.vsafe_mok as (j + 1) j'' hk.2 hj''
      rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this

theorem _root_.Millipede.RArgs.locs_length {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o : Nat), (as.locs o).length = ps.length
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, o | _, _, .shr _ as, o | _, _, .mut _ as, o => by
    simp only [RArgs.locs, List.length_cons]; rw [RArgs.locs_length as]

/-- The write-backs of a call leave a variable no argument is rooted at unchanged. -/
theorem _root_.Millipede.RArgs.writeBack_get_ne {Γ : List Ty} {s : Ty} (m : Mem s Γ) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (env : Env Γ) (vs : (Ty.tup os).carrier),
      as.noAddr m.idx = true → (as.writeBack env vs).get m = env.get m
  | _, _, .nil, _, _, _ => rfl
  | _, _, .own _ as, env, vs, h | _, _, .shr _ as, env, vs, h => by
    simp only [RArgs.noAddr, Bool.and_eq_true] at h
    first | exact RArgs.writeBack_get_ne m as env vs h | exact RArgs.writeBack_get_ne m as env vs h.2
  | _, _, .mut p as, env, vs, h => by
    simp only [RArgs.noAddr, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [RArgs.writeBack]
    rw [RArgs.writeBack_get_ne m as _ vs.2 h.2]
    exact Place.get_set_ne p env vs.1 m (Ne.symm h.1)

/-- The case of a reference call. The owned arguments are passed by copy and the references as
addresses, with a length for a slice. The callee runs in its region at the watermark, updating the
`&mut` argument places and handing them back in place, and the continuation then runs with the
result at the watermark. -/
theorem msound_callRef {Γ ps os : List Ty} {r u : Ty} (name : String) (req : Env ps → Prop)
    (body : Exp ps (.pair r (.tup os))) (args : RArgs Γ ps os) (k : Exp (r :: Γ) u)
    (hm : args.memOk = true) (hmo : args.mutOk [] = true) (hvw : args.viewsOk body = true)
    (hCb : body.Conf (callTl r args) = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.callRef name req body args k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hCk := conf_callRef H.conf
  have hmb := Nat.le_max_left body.memNeed k.memNeed
  have hmk := Nat.le_max_right body.memNeed k.memNeed
  have hlen := H.lay.length
  have hg := args.good_of (ρ := ρ) hm H.lawful.1 H.safe.1 (fun i H' h' => (H.hole i H' h').1)
    fun i hs => by have := (H.sl.na i hs).1; simp only [Exp.noAddr, Bool.and_eq_true] at this; exact this.1
  have hxo : args.ExtOk S := RArgs.extOk_of H.lay H.vs args 0 fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1
  have hvw' : ∀ i m, (i, m) ∈ args.views 0 → body.VSafe i (callTl r args) = true ∧
      (m = true → body.HBv i ((args.mutIdx 0).filter (i < ·)) = true) := by
    intro i m hm
    simp only [RArgs.viewsOk, Bool.and_eq_true] at hvw
    have := List.all_eq_true.mp hvw.1 _ hm
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    exact ⟨this.1, fun e => this.2.resolve_left (by simp [e])⟩
  have hvp : ∀ i, i ∈ args.pairs 0 → body.VSafe i (callTl r args) = true := by
    intro i hi
    simp only [RArgs.viewsOk, Bool.and_eq_true] at hvw
    exact List.all_eq_true.mp hvw.2 _ hi
  let P := args.frame
  obtain ⟨f₁, h₁, hr₁, hb₁, hout₁, hrel⟩ := rargsPass_runs (κ := κ) (ω := ω) (L := L) H.lay args 0 f h
    H.bpOk H.envRel H.sl.rel hg hxo (by omega) (by omega)
  simp only [Nat.add_zero] at hr₁ hout₁
  let f₂ := f₁.set RX (UInt64.ofNat (bp + n))
  have hf₂ : f₂ BP = UInt64.ofNat bp := by
    simp only [f₂, Frame.set, show (BP = RX) = False by decide, ite_false]; rw [hb₁, H.bpOk]
  have hrun₂ : Runs κ ω L (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n))) f₁ h₁ f₂ h₁ :=
    Runs.congr (Runs.bin _ _ _ _ _ _) (by
      simp only [f₂, eval_slot, eval_imm, BinOp.eval, hb₁, H.bpOk, ofNat_add_ofNat]) rfl
  have hRX : f₂ RX = UInt64.ofNat (bp + n) := by simp [f₂]
  have henv₁ : MEnvRel h₁ bp env ρ S :=
    H.envRel.above H.lay fun x hx => hout₁ x (by omega) (by unfold InR; omega)
  have hlay0 := rargs_lay H.lay H.envRel args 0 hg hxo H.frozen.1 H.restr.1
  simp only [Nat.zero_add] at hlay0
  have hcallee := ihb.app (L := L) (n := P + r.size) (d := P) (env := args.denote env) (h := h₁)
    ⟨hCb, callTl_ok r args _, H.restr.2.1, H.lawful.2.1, H.frozen.2.1,
      HoleAv.none_of (semS_hole args 0), hlay0.mono (by omega), by simp [Tl.dsz],
      by simp only [Tl.dsz]; exact hlay0.away (Nat.le_refl _), by omega,
      (by simp [Frame.ofList, hRX] : (Frame.ofList [f₂ RX]) BP = _), hrel,
      H.safe.2.2.1 _ _ H.safe.2.1, H.run, by omega, fun i hi => by
        rcases semS_ext args 0 i hi with ⟨m, hm⟩ | hp | ⟨x, hxe, hv⟩
        · exact (hvw' _ _ hm).1
        · exact hvp i hp
        · have := H.vs x hxe
          simp only [Exp.VSafe, Bool.and_eq_true] at this
          rcases hv _ _ 0 this.1 with h' | h'
          · simpa using h'
          · simp only [Nat.zero_add, Bool.and_eq_true] at h'; exact h'.1,
      SlotHyp.of_none (args.locs_length 0) (args.locs_slot? 0)⟩
    (.ret [] 0 f₂ :: .seq (lowerM k tm.up (.own (n + P) :: ρ) (n + P + r.size) d) :: kk)
    (c + (Tick.callR args.depth args.refs args.ownWords).cost κ)
  -- the write-back conditions of the slice arguments
  have hbk : args.backOk env (body.denote ω (args.denote env) w).1.2 := by
    refine args.backOk_of env _ (Data.occs (body.denote ω (args.denote env) w).1.1) H.safe.1
      fun i hi len hF => ?_
    have := body.hbv_sound ω len i _ ((hvw' _ _ hi).2 rfl) (args.denote env) w hF
    have e : Data.occs (body.denote ω (args.denote env) w).1 =
        Data.occs (body.denote ω (args.denote env) w).1.1 ++
          Data.occs (body.denote ω (args.denote env) w).1.2 := Data.occs_pair _ _
    rw [e] at this; exact this
  rw [callTl_hb] at hcallee
  generalize hBV : body.exec ω κ (Hb.of !os.isEmpty) (args.denote env) w = rb at hcallee
  have hbk' : args.backOk env rb.val.2 := by rw [← hBV, Exp.exec_val]; exact hbk
  -- the views passed on whole come back with their occupancies, by the callee's exact hand-back
  have hvb : args.ViewBack S env rb.val.2 := by
    rw [← hBV, Exp.exec_val]
    refine args.viewBack_of H.lay H.envRel _ hxo fun x hx => ?_
    have hvs := H.vs x hx
    simp only [Exp.VSafe, Bool.and_eq_true] at hvs
    refine args.wholeEq_of ω env x body w (fun j hj => ?_)
      (fun j hj => body.hbx_exact ω j _ hj _ w (H.safe.2.2.1 _ _ H.safe.2.1))
    have := args.vsafe_mok 0 j hvs.1 hj
    simp only [Nat.zero_add, Bool.and_eq_true] at this; exact this.2
  have hstep := MSim.call_step (name := name) (fr := FR + body.slotNeed) (k := kk) (Q := TQ tm bp d ρ S u)
    (ops := [.slot RX]) (ret := []) (dst := 0)
    (pf := SProt ρ W)
    (prot := Prot bp n d (tm.dsz u) Γ S W) (prot₂ := Prot bp n d (tm.dsz u) Γ S W)
    (r₂ := k.exec ω κ tm.up.hb (.cons rb.val.1 (args.writeBack env rb.val.2)) rb.world) H.run hcallee
    (fun hh => exec_halted ω κ k _ _ hh)
    (fun a ha => by
      refine ⟨?_, ha⟩
      obtain ⟨h1, h2, h3⟩ := ha
      refine ⟨by omega, fun e => by simp only [Tl.dsz, InR] at e; omega, fun e => ?_⟩
      rcases args.inW_semS 0 e with e | e
      · omega
      · exact h3 (args.inMut_inW H.envRel H.lay hg.mutGood hxo H.restr.1 e))
    (fun _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ m₁ hv hm hh => by
      obtain ⟨bs, hbs, hs0, hsc⟩ := hv
      obtain ⟨hv1, hv2⟩ := pair_repr rb.val bs hbs
      rw [hs0] at hv1
      have hcomp := args.compAt_of (m := m₁) (SS := args.semS (bp + n) S env 0) bs 0 0
        (fieldOff (Data.shape (r.carrier × (Ty.tup os).carrier)) 1) (fun i => by rw [Nat.zero_add])
        fun c hc => (CompAt.mem (args.locs_slot? 0 c.1)).1 (hsc c hc)
      have hwb := writeBack_rel H.lay (by omega) m₁ args env h₁ rb.val.2 _ [] henv₁ hg.mutGood hxo
        H.frozen.1 H.restr.1 hmo hbk' hvb hv2 hcomp (fun a ha hn => hm a ⟨by omega,
          by simp only [Tl.dsz, InR]; omega,
          fun e => by
            rcases args.inW_semS 0 e with e | e
            · omega
            · exact hn e⟩)
      have hsk := H.safe.2.2.2
      rw [← Exp.exec_val ω κ, ← Exp.exec_world ω κ, hBV] at hsk
      exact .unpush (by omega) (ihk.app (H.push _ (n' := n + P) (by omega) hCk H.restr.2.2
        H.lawful.2.2 H.frozen.2.2 (H.hole.push _ rfl fun _ _ h => h.2) (by omega) (by omega) hf₂ hwb
        ((H.sl.rel.keep (Runs.seq hr₁ hrun₂).keep).env_congr fun m hm =>
          RArgs.writeBack_get_ne m args env _ (by
            have := (H.sl.na _ hm).1; simp only [Exp.noAddr, Bool.and_eq_true] at this; exact this.1))
        (by rw [← Nat.add_assoc]; exact hv1) hsk (H.vs.mono fun i h => by
          simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2) hh) kk _))
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run
    (MSim.runs H.run hr₁ hb₁
    (fun x hx => hout₁ x (by unfold Prot at hx; omega) (by unfold Prot at hx; unfold InR; omega))
    (MSim.runs H.run hrun₂ (by rw [hf₂, hb₁, H.bpOk]) (fun _ _ => rfl) hstep))).of_eq ?_ ?_ ?_
  · simp [Exp.exec, hBV, Tl.hb_up]
  · simp [Exp.exec, hBV, Tl.hb_up]
  · simp only [Exp.exec, Tick.cost, RArgs.cost, width, Ty.words, hBV, Nat.add_mul, Tl.hb_up]; omega

end

end Millipede.Flat
