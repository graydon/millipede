import Millipede.Compile.LowerInv

/-!
# Disjoint paths are disjoint storage

The borrow checker reasons about places by their paths, lists of field numbers with `dyn` for any
element, and treats two places as disjoint when their paths do not overlap, which is when they
diverge at two different field numbers. The memory lowering stores a place at an offset inside its
root variable. This module connects the two. Two contiguous places of variables of the same type
whose paths do not overlap occupy disjoint bytes, in every environment, because elements compared
as `dyn` are either the same element, compared further, or different elements, which are disjoint.

The proof rests on lawful lenses being aligned, which means that a lens's target has the shape of
its field, so that a path determines the shapes it walks through. A place is then a walk through
its root type's shape, whose result is the place's offset and shape.

Two results depend on this. The hole that a `&mut` borrow makes in its lender is avoided by every
place that the borrow checker lets the body use, and the arguments of a reference call are
separated.

See doc/design/memory.md.
-/

namespace Millipede.Flat

/-- A concrete selector, either field number `i` or element number `k`. -/
inductive CSel where
  | fld (i : Nat)
  | elm (k : Nat)

/-- The checker's view of a concrete selector. -/
def CSel.abs : CSel → Sel
  | .fld i => .field i
  | .elm _ => .dyn

/-- One step through a shape, giving the offset of the selected part and its shape. -/
def CSel.step : CSel → Shape → Option (Nat × Shape)
  | .fld i, .prod fs => (fs[i]?).map fun s => (Shape.fieldOffset fs i, s)
  | .elm k, .array n s => if k < n then some (k * s.size, s) else none
  | .elm k, .slots n s => if k < n then some (k * s.size, s) else none
  | _, _ => none

/-- Walks a list of selectors through a shape, giving the offset of the part reached and its
shape. -/
def walk : Shape → List CSel → Option (Nat × Shape)
  | sh, [] => some (0, sh)
  | sh, c :: cs => match c.step sh with
    | some (o, s) => (walk s cs).map fun r => (o + r.1, r.2)
    | none => none

theorem walk_append (sh : Shape) (cs : List CSel) (c : CSel) :
    walk sh (cs ++ [c]) = match walk sh cs with
      | some (o, s) => (c.step s).map fun r => (o + r.1, r.2)
      | none => none := by
  induction cs generalizing sh with
  | nil =>
    simp only [List.nil_append, walk]
    cases c.step sh <;> simp
  | cons c' cs ih =>
    simp only [List.cons_append, walk]
    cases hs : c'.step sh with
    | none => rfl
    | some r =>
      simp only [ih]
      cases walk r.2 cs with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        cases c.step q.2 <;> simp [Nat.add_assoc]

/-- A step stays inside the shape. -/
theorem CSel.step_le {c : CSel} {sh s : Shape} {o : Nat} (h : c.step sh = some (o, s)) :
    o + s.size ≤ sh.size := by
  cases c with
  | fld i =>
    cases sh with
    | prod fs =>
      simp only [CSel.step, Option.map_eq_some_iff] at h
      obtain ⟨s', hs', he⟩ := h
      cases he
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hs'
      exact Shape.fieldOffset_add_size_le fs i hi
    | _ => simp [CSel.step] at h
  | elm k =>
    cases sh with
    | array n s' =>
      simp only [CSel.step] at h
      split at h
      · cases h; exact Shape.elemOffset_add_size_le n _ k ‹_›
      · cases h
    | slots n s' =>
      simp only [CSel.step] at h
      split at h
      · cases h; exact Shape.cellOffset_add_size_le n _ k ‹_›
      · cases h
    | _ => simp [CSel.step] at h

/-- A walk stays inside the shape. -/
theorem walk_le : ∀ {sh : Shape} {cs : List CSel} {o : Nat} {s : Shape},
    walk sh cs = some (o, s) → o + s.size ≤ sh.size
  | sh, [], o, s, h => by simp only [walk] at h; cases h; omega
  | sh, c :: cs, o, s, h => by
    simp only [walk] at h
    split at h
    · rename_i o₁ s₁ hs
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      have := walk_le hr; have := CSel.step_le hs; omega
    · cases h

/-- Elements of distinct indices are disjoint, at `A + i * sz` and `A + j * sz` with `sz` bytes
each. -/
theorem elem_disj_of_ne {A i j sz : Nat} (h : i ≠ j) : Disj (A + i * sz) sz (A + j * sz) sz := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · have : (i + 1) * sz ≤ j * sz := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at this; left; omega
  · have : (j + 1) * sz ≤ i * sz := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at this; right; omega

/-- Pointwise, element ranges of distinct indices are disjoint. -/
theorem elem_disj {k a sz x : Nat} (h : k ≠ a) (h1 : k * sz ≤ x) (h2 : x < k * sz + sz) :
    ¬ (a * sz ≤ x ∧ x < a * sz + sz) := by
  have := elem_disj_of_ne (A := 0) (sz := sz) h; unfold Disj at this; omega

theorem elem_case {s : Shape} {k k' x₁ x₂ : Nat} {y₁ y₂ : Shape} (hl₁ : x₁ + y₁.size ≤ s.size)
    (hl₂ : x₂ + y₂.size ≤ s.size) (hsame : k = k' → Disj x₁ y₁.size x₂ y₂.size) :
    Disj (k * s.size + x₁) y₁.size (k' * s.size + x₂) y₂.size := by
  by_cases hkk : k = k'
  · subst hkk; have := hsame rfl; unfold Disj at this ⊢; omega
  · have := elem_disj_of_ne (A := 0) (sz := s.size) hkk; unfold Disj at this ⊢; omega

/-- Walks along non-overlapping paths reach disjoint parts. -/
theorem walk_disj : ∀ (sh : Shape) (cs₁ cs₂ : List CSel) (o₁ o₂ : Nat) (s₁ s₂ : Shape),
    walk sh cs₁ = some (o₁, s₁) → walk sh cs₂ = some (o₂, s₂) →
    Sel.overlap (cs₁.map CSel.abs) (cs₂.map CSel.abs) = false → Disj o₁ s₁.size o₂ s₂.size
  | _, [], _, _, _, _, _, _, _, h => by simp [Sel.overlap] at h
  | _, _ :: _, [], _, _, _, _, _, _, h => by simp [Sel.overlap] at h
  | sh, c₁ :: cs₁, c₂ :: cs₂, o₁, o₂, s₁, s₂, h₁, h₂, hov => by
    simp only [walk] at h₁ h₂
    split at h₁
    · rename_i a₁ t₁ hs₁
      split at h₂
      · rename_i a₂ t₂ hs₂
        obtain ⟨⟨x₁, y₁⟩, hr₁, e₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨⟨x₂, y₂⟩, hr₂, e₂⟩ := Option.map_eq_some_iff.mp h₂
        simp only [Prod.mk.injEq] at e₁ e₂
        obtain ⟨rfl, rfl⟩ := e₁
        obtain ⟨rfl, rfl⟩ := e₂
        have hl₁ := walk_le hr₁; have hl₂ := walk_le hr₂
        cases c₁ with
        | fld i =>
          cases c₂ with
          | fld j =>
            cases sh with
            | prod fs =>
              simp only [CSel.step, Option.map_eq_some_iff] at hs₁ hs₂
              obtain ⟨_, hi, e₁⟩ := hs₁; obtain ⟨_, hj, e₂⟩ := hs₂
              cases e₁; cases e₂
              obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
              obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
              simp only [List.map_cons, CSel.abs, Sel.overlap, Bool.and_eq_false_iff,
                beq_eq_false_iff_ne] at hov
              by_cases hij : i = j
              · subst hij
                rcases hov with hov | hov
                · exact absurd rfl hov
                · have := walk_disj _ _ _ _ _ _ _ hr₁ hr₂ hov
                  unfold Disj at this ⊢; omega
              · rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
                · have := Shape.fieldOffset_disjoint fs i j hlt hj'
                  left; omega
                · have := Shape.fieldOffset_disjoint fs j i hlt hi'
                  right; omega
            | _ => simp [CSel.step] at hs₁
          | elm k =>
            cases sh <;> simp [CSel.step] at hs₁ hs₂
        | elm k =>
          cases c₂ with
          | fld j => cases sh <;> simp [CSel.step] at hs₁ hs₂
          | elm k' =>
            simp only [List.map_cons, CSel.abs, Sel.overlap] at hov
            cases sh with
            | array n s =>
              simp only [CSel.step] at hs₁ hs₂
              split at hs₁ <;> split at hs₂ <;> (try cases hs₁) <;> (try cases hs₂)
              exact elem_case hl₁ hl₂ fun e => by
                subst e; exact walk_disj _ _ _ _ _ _ _ hr₁ hr₂ hov
            | slots n s =>
              simp only [CSel.step] at hs₁ hs₂
              split at hs₁ <;> split at hs₂ <;> (try cases hs₁) <;> (try cases hs₂)
              exact elem_case hl₁ hl₂ fun e => by
                subst e; exact walk_disj _ _ _ _ _ _ _ hr₁ hr₂ hov
            | _ => simp [CSel.step] at hs₁
      · cases h₂
    · cases h₁

/-! ## Places as walks -/

/-- The concrete selectors of a contiguous place, from the root. -/
def _root_.Millipede.Place.csels {Γ : List Ty} : {t : Ty} → Place Γ t → Env Γ → List CSel
  | _, .var _, _ => []
  | _, .field p l, env => p.csels env ++ [.fld l.index]
  | _, .index (dflt := _) p i, env => p.csels env ++ [.elm (i.denote env).toNat]
  | _, .slot (dflt := _) p i, env => p.csels env ++ [.elm (i.denote env).toNat]
  | _, _, _ => []

theorem _root_.Millipede.Place.path_csels {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ)
    (hc : p.contig = true) : (p.csels env).map CSel.abs = p.path := by
  induction p with
  | var => rfl
  | field p l ih => simp [Place.csels, Place.path, ih hc, CSel.abs]
  | index p i ih => simp [Place.csels, Place.path, ih hc, CSel.abs]
  | slot p i ih => simp [Place.csels, Place.path, ih hc, CSel.abs]
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-- A contiguous, lawful place whose obligation holds is a walk through its root's shape, to its
offset and its type's shape. -/
theorem _root_.Millipede.Place.walk_eq {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ)
    (hc : p.contig = true) (hL : p.Lawful) (hok : p.ok env) :
    walk p.rootTy.data.shape (p.csels env) = some (p.off env, t.data.shape) := by
  induction p with
  | var => rfl
  | @field s t' p l ih =>
    obtain ⟨fs, hfs, hfi⟩ := hL.2.2
    show walk p.rootTy.data.shape (p.csels env ++ [.fld l.index]) = _
    rw [walk_append, ih hc hL.1 hok]
    show (CSel.step (.fld l.index) s.data.shape).map _ = _
    rw [hfs]
    simp only [CSel.step, hfi, Option.map_some]
    simp only [Place.off, lensOff, hfs]
  | @index t' n' _ p i ih =>
    show walk p.rootTy.data.shape (p.csels env ++ [.elm (i.denote env).toNat]) = _
    rw [walk_append, ih hc hL hok.1]
    show (CSel.step (.elm _) (.array n' (Data.shape t'.carrier))).map _ = _
    simp only [CSel.step, hok.2, ↓reduceIte, Option.map_some]
    rfl
  | @slot t' n' _ p i ih =>
    show walk p.rootTy.data.shape (p.csels env ++ [.elm (i.denote env).toNat]) = _
    rw [walk_append, ih hc hL hok.1]
    have hj : (i.denote env).toNat < n' := by
      rcases Nat.lt_or_ge (i.denote env).toNat n' with hj | hj
      · exact hj
      · exfalso; have := hok.2; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at this
    show (CSel.step (.elm _) (.slots n' (Data.shape t'.carrier))).map _ = _
    simp only [CSel.step, hj, ↓reduceIte, Option.map_some]
    rfl
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-- Places with non-overlapping paths are disjoint storage. Two contiguous, lawful places of root
variables of the same type, whose obligations hold, each in its own context and environment, and
whose paths do not overlap, occupy disjoint bytes of the root. -/
theorem _root_.Millipede.Place.disj_of_overlap {Γ₁ Γ₂ : List Ty} {t₁ t₂ : Ty} (p : Place Γ₁ t₁)
    (q : Place Γ₂ t₂) (env₁ : Env Γ₁) (env₂ : Env Γ₂) (hT : p.rootTy = q.rootTy)
    (hc₁ : p.contig = true) (hc₂ : q.contig = true) (hL₁ : p.Lawful) (hL₂ : q.Lawful)
    (hok₁ : p.ok env₁) (hok₂ : q.ok env₂) (hov : Sel.overlap p.path q.path = false) :
    Disj (p.off env₁) t₁.size (q.off env₂) t₂.size := by
  have h₁ := p.walk_eq env₁ hc₁ hL₁ hok₁
  have h₂ := q.walk_eq env₂ hc₂ hL₂ hok₂
  rw [hT] at h₁
  rw [← p.path_csels env₁ hc₁, ← q.path_csels env₂ hc₂] at hov
  exact walk_disj _ _ _ _ _ _ _ h₁ h₂ hov

/-- The offset of a contiguous place is inside its root. -/
theorem _root_.Millipede.Place.off_le {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ)
    (hc : p.contig = true) (hL : p.Lawful) (hok : p.ok env) :
    p.off env + t.size ≤ p.rootTy.size :=
  walk_le (p.walk_eq env hc hL hok)

/-- The hole of a `&mut` borrow of a contiguous place `p` of a variable is avoided by every place
of the variable whose path does not overlap `p`'s. Here `s` is the variable's run-time knowledge
and the place's bytes are consecutive from its address `a`. -/
theorem holeOK_of_place {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) (s : SI) (a : Nat)
    (hc : p.contig = true) (hL : p.Lawful) (hok : p.ok env) (hs : s.Ok p.rootTy)
    (hp : ∀ k, k < t.size → a + k = s.at (p.off env + k)) :
    HoleOK s p.rootTy ⟨a, t.size, p.path⟩ := by
  intro Γ' t' q env' hT hc' hL' hok' hov k hk hin
  have hd := Place.disj_of_overlap p q env env' hT.symm hc hc' hL hL' hok hok' hov
  have hq := q.off_le env' hc' hL' hok'
  have hpl := p.off_le env hc hL hok
  rw [hT] at hq
  simp only [InR] at hin
  generalize ha : s.at (q.off env' + k) = x at hin
  obtain ⟨k', rfl⟩ : ∃ k', x = a + k' := ⟨x - a, by omega⟩
  rw [hp k' (by omega)] at ha
  have := s.at_inj hs (by omega) (by omega) ha
  unfold Disj at hd; omega

end Millipede.Flat
