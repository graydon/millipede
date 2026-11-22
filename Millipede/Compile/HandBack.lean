import Millipede.Compile.Lower

/-!
# The hand-back condition and the write-back obligation

A `&mut` slice borrow `let x := { let r = &mut q[lo..lo+len]; body }; k` writes the view that
`body` hands back into the array with `vunview`, which takes element `lo + k` from the view's cell
`k` only if that cell is full. On the machine the view is the run of elements itself, a pointer and
a length, and it is written in place. The two agree when the handed-back view still has its first
`len` cells full, which is the write-back condition `Place.backOk`.

This module derives the write-back condition from a syntactic condition that `compile` checks,
the hand-back condition `Exp.HB`. Along every path to a tail, the view variable is written only
through its cells, and every tail is a constructor whose last argument is the view variable and
which carries the hand-back certificate `Ctor.occs`, so the value it builds has its arguments'
occupancies. Occupancy is ghost information that lets the statement speak about the full cells of
the last component of a value whose type is known only through its `Data` instance, without casts.
`Exp.hb_sound` states that when the view variable's cells `0 … len-1` are full, the value of a term
satisfying `Exp.HB` ends with a component whose cells `0 … len-1` are full, and `hb_backOk`
specialises it to a borrow body.

A view passed on whole to a callee by `&mut`, as in `f (&mut s)`, comes back as the callee's
handed-back value, so the caller needs its exact occupancy, with the first `len` cells full and the
others empty. The exact hand-back condition `Exp.HBx` allows writes to the view only by assignments
through its cells, whose obligation is that the cell is full, or by passing it on whole again.
`Exp.hbx_exact` proves that a safe term satisfying it hands the view's occupancy back unchanged,
and the caller's own hand-back condition `Exp.HBv` accepts such a pass.

See doc/design/memory.md.
-/

namespace Millipede

/-! ## Occupancies -/

/-- The occupancies of the value at position `i` of an environment, or `[]` past its end. -/
def Env.occsAt : {Γ : List Ty} → Env Γ → Nat → List (Option (List Bool))
  | _, .nil, _ => []
  | _, .cons v _, 0 => Data.occs v
  | _, .cons _ env, i + 1 => env.occsAt i

@[simp] theorem Env.occsAt_cons_zero {t : Ty} {Γ : List Ty} (v : t.carrier) (env : Env Γ) :
    (Env.cons v env).occsAt 0 = Data.occs v := rfl
@[simp] theorem Env.occsAt_cons_succ {t : Ty} {Γ : List Ty} (v : t.carrier) (env : Env Γ) (i : Nat) :
    (Env.cons v env).occsAt (i + 1) = env.occsAt i := rfl

/-- The list is one component whose cells `0 … len-1` are full. -/
def OccsFull (len : Nat) (os : List (Option (List Bool))) : Prop :=
  ∃ l, os = [some l] ∧ ∀ k, k < len → l.getD k false = true

/-- The last component's cells `0 … len-1` are full. -/
def LastFull (len : Nat) (os : List (Option (List Bool))) : Prop :=
  ∃ pre l, os = pre ++ [some l] ∧ ∀ k, k < len → l.getD k false = true

theorem Env.occsAt_get {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    env.occsAt m.idx = Data.occs (env.get m)
  | _, .cons _ _, .here => rfl
  | _, .cons _ env, .there m => Env.occsAt_get env m

theorem Env.occsAt_set_same {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    (v : t.carrier) → (env.set m v).occsAt m.idx = Data.occs v
  | _, .cons _ _, .here, _ => rfl
  | _, .cons _ env, .there m, v => Env.occsAt_set_same env m v

theorem Env.occsAt_set_ne {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    (v : t.carrier) → (i : Nat) → m.idx ≠ i → (env.set m v).occsAt i = env.occsAt i
  | _, .cons _ _, .here, _, 0, h => absurd rfl h
  | _, .cons _ _, .here, _, _ + 1, _ => rfl
  | _, .cons _ _, .there _, _, 0, _ => rfl
  | _, .cons _ env, .there m, v, i + 1, h =>
    Env.occsAt_set_ne env m v i fun e => h (by simp [Mem.idx, e])

/-- The occupancy of a `Slots` value is its cells' fullness. -/
theorem Slots.occs_eq {α : Type} [Data α] {n : Nat} (s : Slots α n) :
    Data.occs s = [some (s.cells.toList.map Option.isSome)] := rfl

theorem Slots.getD_occ {α : Type} {n : Nat} (s : Slots α n) (k : Nat) :
    (s.cells.toList.map Option.isSome).getD k false = s.isFull k := by
  unfold Slots.isFull Slots.cell vget
  by_cases hk : k < n <;> simp [hk, List.getD_eq_getElem?_getD]

theorem OccsFull.setCell {α : Type} [Data α] {n len : Nat} {s : Slots α n} (j : Nat) (x : α)
    (h : OccsFull len (Data.occs s)) : OccsFull len (Data.occs (s.setCell j (some x))) := by
  obtain ⟨l, hl, hf⟩ := h
  rw [Slots.occs_eq] at hl
  simp only [List.cons.injEq, Option.some.injEq, and_true] at hl
  refine ⟨_, Slots.occs_eq _, fun k hk => ?_⟩
  have := hf k hk
  rw [← hl, Slots.getD_occ] at this
  rw [Slots.getD_occ, Slots.isFull_setCell]
  split <;> simp_all

/-- Two `Slots` with the same full cells have the same occupancy. -/
theorem Slots.occs_congr {α : Type} [Data α] {n : Nat} {s s' : Slots α n}
    (h : ∀ k, s'.isFull k = s.isFull k) : Data.occs s' = Data.occs s := by
  rw [Slots.occs_eq, Slots.occs_eq]
  congr 2
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have e1 := Slots.getD_occ s' k
  have e2 := Slots.getD_occ s k
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e2
  rw [e1, e2, h]

/-- A written-back sub-slice keeps every full cell full. -/
theorem sunview_full_of {α : Type} {n : Nat} {s : Slots α n} {k : Nat} (lo len : Nat)
    (v : Slots α n) (h : s.isFull k = true) : (sunview s lo len v).isFull k = true := by
  rw [sunview_isFull]; simp [h]

/-- A written-back sub-slice whose range was full has the view's occupancy. -/
theorem sunview_occs {α : Type} [Data α] {n : Nat} (s : Slots α n) (lo len : Nat) (v : Slots α n)
    (hf : ∀ k, k < len → s.isFull (lo + k) = true) :
    Data.occs (sunview s lo len v) = Data.occs s :=
  Slots.occs_congr fun k => by
    rw [sunview_isFull]
    by_cases h3 : k < n ∧ lo ≤ k ∧ k - lo < len
    · have := hf (k - lo) h3.2.2; rw [show lo + (k - lo) = k by omega] at this; simp [this]
    · simp [h3]

theorem OccsFull.mono {α : Type} [Data α] {n len : Nat} {s s' : Slots α n}
    (hm : ∀ k, s.isFull k = true → s'.isFull k = true)
    (h : OccsFull len (Data.occs s)) : OccsFull len (Data.occs s') := by
  obtain ⟨l, hl, hf⟩ := h
  rw [Slots.occs_eq] at hl
  simp only [List.cons.injEq, Option.some.injEq, and_true] at hl
  refine ⟨_, Slots.occs_eq _, fun k hk => ?_⟩
  have := hf k hk
  rw [← hl, Slots.getD_occ] at this
  rw [Slots.getD_occ]; exact hm k this

/-! ## Writes that keep the view's cells full -/

namespace Place
variable {Γ : List Ty}

theorem isVarAt_occs {i : Nat} : {t : Ty} → (p : Place Γ t) → p.isVarAt i = true →
    ∀ (env : Env Γ) (v : t.carrier),
      (p.set env v).occsAt i = Data.occs v ∧ env.occsAt i = Data.occs (p.get env)
  | _, .var m, h, env, v => by
    simp only [isVarAt, beq_iff_eq] at h; subst h
    exact ⟨Env.occsAt_set_same env m v, Env.occsAt_get env m⟩
  | _, .field _ _, h, _, _ => by simp [isVarAt] at h
  | _, .index (dflt := _) _ _, h, _, _ => by simp [isVarAt] at h
  | _, .slot (dflt := _) _ _, h, _, _ => by simp [isVarAt] at h
  | _, .range _ _ _, h, _, _ => by simp [isVarAt] at h
  | _, .pair2 (dflt := _) _ _ _, h, _, _ => by simp [isVarAt] at h
  | _, .rangeS _ _ _, h, _, _ => by simp [isVarAt] at h
  | _, .pair2S (dflt := _) _ _ _, h, _, _ => by simp [isVarAt] at h

/-- A write at a place that keeps the view variable `i` leaves its cells `0 … len-1` full. -/
theorem keeps_full {i len : Nat} {t : Ty} (p : Place Γ t) (hk : p.keeps i = true) (env : Env Γ)
    (hF : OccsFull len (env.occsAt i)) (v : t.carrier) : OccsFull len ((p.set env v).occsAt i) := by
  induction p with
  | var m =>
    simp only [keeps, bne_iff_ne, ne_eq] at hk
    rw [Place.set, Env.occsAt_set_ne env m v i hk]; exact hF
  | field p l ih => exact ih hk _
  | index p _ ih => exact ih hk _
  | range p _ _ ih => exact ih hk _
  | pair2 p _ _ ih => exact ih hk _
  | rangeS m lo len =>
    simp only [Place.set]
    by_cases he : m.idx = i
    · subst he; rw [Env.occsAt_set_same]; rw [Env.occsAt_get] at hF
      exact hF.mono fun k hk => sunview_full_of _ _ _ hk
    · rw [Env.occsAt_set_ne env m _ i he]; exact hF
  | pair2S m j k =>
    simp only [Place.set]
    by_cases he : m.idx = i
    · subst he; rw [Env.occsAt_set_same]; rw [Env.occsAt_get] at hF
      exact (hF.setCell _ _).setCell _ _
    · rw [Env.occsAt_set_ne env m _ i he]; exact hF
  | slot p j ih =>
    simp only [keeps, Bool.or_eq_true] at hk
    by_cases hv : p.isVarAt i = true
    · obtain ⟨h1, h2⟩ := p.isVarAt_occs hv env
        (Slots.setCell (p.get env) (j.denote env).toNat (some v))
      simp only [Place.set]; rw [h1]
      rw [h2] at hF
      exact hF.setCell _ _
    · exact ih (hk.resolve_left hv) _

end Place

/-- The handed-back values of the `&mut` arguments that are the variable `i` itself, a view passed
on whole, have occupancies satisfying `P`. -/
def RArgs.WholeP {Γ : List Ty} (i : Nat) (P : List (Option (List Bool)) → Prop) :
    {ps os : List Ty} → RArgs Γ ps os → (Ty.tup os).carrier → Prop
  | _, _, .nil, _ => True
  | _, _, .own _ as, vs => as.WholeP i P vs
  | _, _, .shr _ as, vs => as.WholeP i P vs
  | _, _, .mut p as, vs => (p.isVarAt i = true → P (Data.occs vs.1)) ∧ as.WholeP i P vs.2

theorem RArgs.keeps_full {Γ : List Ty} {i len : Nat} {hb : Nat → Bool} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → (j : Nat) →
    as.keeps i hb j = true → (env : Env Γ) → OccsFull len (env.occsAt i) →
    (vs : (Ty.tup os).carrier) → as.WholeP i (OccsFull len) vs →
    OccsFull len ((as.writeBack env vs).occsAt i)
  | _, _, .nil, _, _, _, hF, _, _ => hF
  | _, _, .own _ as, j, hk, env, hF, vs, hW => RArgs.keeps_full as (j + 1) hk env hF vs hW
  | _, _, .shr _ as, j, hk, env, hF, vs, hW => RArgs.keeps_full as (j + 1) hk env hF vs hW
  | _, _, .mut p as, j, hk, env, hF, vs, hW => by
    simp only [RArgs.keeps, Bool.and_eq_true, Bool.or_eq_true] at hk
    refine RArgs.keeps_full as (j + 1) hk.2 _ ?_ vs.2 hW.2
    rcases hk.1 with hk1 | ⟨hv, _⟩
    · exact p.keeps_full hk1 env hF vs.1
    · rw [(p.isVarAt_occs hv env vs.1).1]; exact hW.1 hv

theorem EArgs.keeps_full {Γ : List Ty} {i len : Nat} {ps : List ExtParam} (as : EArgs Γ ps)
    (hk : as.keeps i = true) (env : Env Γ) :
    ∀ (env' : Env Γ) (bss : List (List UInt8)), OccsFull len (env'.occsAt i) →
      OccsFull len ((as.fill env env' bss).occsAt i) := by
  induction as with
  | nil => intro _ _ hF; exact hF
  | word _ _ ih | bufIn _ _ ih | bufOut _ ih => intro env' bss hF; exact ih hk _ _ hF
  | sliceOut a _ _ _ ih =>
    simp only [EArgs.keeps, Bool.and_eq_true] at hk
    intro env' bss hF
    exact ih hk.2 _ _ (a.keeps_full hk.1 env' hF _)

theorem Atom.occs_of_isVar {Γ : List Ty} {t : Ty} {i : Nat} (a : Atom Γ t) (h : a.isVar i = true)
    (env : Env Γ) : Data.occs (a.denote env) = env.occsAt i := by
  cases a with
  | var m => simp only [Atom.isVar, beq_iff_eq] at h; subst h; exact (Env.occsAt_get env m).symm
  | lit _ => simp [Atom.isVar] at h

/-- Arguments that are exactly the variables `ys` have their occupancies. -/
theorem Args.occs_allVars {Γ : List Ty} (env : Env Γ) : {ps : List Ty} → (as : Args Γ ps) →
    (ys : List Nat) → ps.length = ys.length → as.endVars ys = true →
    (as.denote env).occs = (ys.map env.occsAt).flatten
  | _, .nil, [], _, _ => rfl
  | _, .nil, _ :: _, hl, _ => by simp at hl
  | _, .cons _ _, [], hl, _ => by simp at hl
  | _, .cons (ts := ts) a as, y :: ys, hl, h => by
    simp only [List.length_cons] at hl
    simp only [Args.endVars, List.length_cons, hl, ↓reduceIte, Bool.and_eq_true] at h
    simp [Args.denote, a.occs_of_isVar h.1 env, Args.occs_allVars env as ys (by omega) h.2]

theorem Args.occs_endVars {Γ : List Ty} (env : Env Γ) : {ps : List Ty} → (as : Args Γ ps) →
    (ys : List Nat) → as.endVars ys = true →
    ∃ pre, (as.denote env).occs = pre ++ (ys.map env.occsAt).flatten
  | _, .nil, ys, h => by
    simp only [Args.endVars, List.isEmpty_iff] at h; subst h; exact ⟨[], rfl⟩
  | _, .cons (ts := ts) a as, ys, h => by
    by_cases hl : ts.length + 1 = ys.length
    · exact ⟨[], by rw [List.nil_append]; exact Args.occs_allVars env (.cons a as) ys hl h⟩
    · simp only [Args.endVars, hl, ↓reduceIte] at h
      obtain ⟨pre, hp⟩ := Args.occs_endVars env as ys h
      exact ⟨Data.occs (a.denote env) ++ pre, by simp [Args.denote, hp]⟩

/-! ## The number of components of variables -/

/-- The number of components, as counted by `Data.occs`, of the variables `xs`. -/
def Env.occsLen {Γ : List Ty} (env : Env Γ) (xs : List Nat) : Nat :=
  (xs.map fun x => (env.occsAt x).length).sum

@[simp] theorem Env.occsLen_cons {t : Ty} {Γ : List Ty} (v : t.carrier) (env : Env Γ) (xs : List Nat) :
    (Env.cons v env).occsLen (xs.map (· + 1)) = env.occsLen xs := by
  simp [Env.occsLen, Function.comp_def]

theorem Env.occsAt_set_length {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    (v : t.carrier) → (x : Nat) → ((env.set m v).occsAt x).length = (env.occsAt x).length
  | _, .cons _ _, .here, _, 0 => Data.occs_len _ _
  | _, .cons _ _, .here, _, _ + 1 => rfl
  | _, .cons _ _, .there _, _, 0 => rfl
  | _, .cons _ env, .there m, v, x + 1 => Env.occsAt_set_length env m v x

theorem Place.set_occsAt_length {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) (x : Nat) :
    ∀ v, ((p.set env v).occsAt x).length = (env.occsAt x).length := by
  induction p with
  | var m => exact fun v => Env.occsAt_set_length env m v x
  | rangeS m => exact fun _ => Env.occsAt_set_length env m _ x
  | pair2S m => exact fun _ => Env.occsAt_set_length env m _ x
  | _ => intro v; simp only [Place.set]; grind

theorem Place.set_occsLen {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) (v : t.carrier)
    (xs : List Nat) : (p.set env v).occsLen xs = env.occsLen xs := by
  simp only [Env.occsLen, p.set_occsAt_length]

theorem RArgs.writeBack_occsLen {Γ : List Ty} (xs : List Nat) : {ps os : List Ty} → (as : RArgs Γ ps os) →
    (env : Env Γ) → (vs : (Ty.tup os).carrier) → (as.writeBack env vs).occsLen xs = env.occsLen xs
  | _, _, .nil, _, _ => rfl
  | _, _, .own _ as, env, vs => RArgs.writeBack_occsLen xs as env vs
  | _, _, .shr _ as, env, vs => RArgs.writeBack_occsLen xs as env vs
  | _, _, .mut p as, env, vs => by
    simp only [RArgs.writeBack]; rw [RArgs.writeBack_occsLen xs as, p.set_occsLen]

theorem EArgs.fill_occsLen {Γ : List Ty} (xs : List Nat) {ps : List ExtParam} (as : EArgs Γ ps)
    (env : Env Γ) : ∀ (env' : Env Γ) (bss : List (List UInt8)),
      (as.fill env env' bss).occsLen xs = env'.occsLen xs := by
  induction as with
  | nil => intros; rfl
  | word _ _ ih | bufIn _ _ ih | bufOut _ ih => intro env' bss; exact ih _ _
  | sliceOut a _ _ _ ih => intro env' bss; simp only [EArgs.fill]; rw [ih, a.set_occsLen]

/-! ## The tail lemma -/

/-- A component whose cells `0 … len-1` are full, followed by `P` components. -/
def CompFull (len P : Nat) (os : List (Option (List Bool))) : Prop :=
  ∃ pre l post, os = pre ++ some l :: post ∧ post.length = P ∧ ∀ k, k < len → l.getD k false = true

theorem RArgs.mutIdx_succ {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat),
      as.mutIdx (j + 1) = (as.mutIdx j).map (· + 1)
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, j => RArgs.mutIdx_succ as (j + 1)
  | _, _, .shr _ as, j => RArgs.mutIdx_succ as (j + 1)
  | _, _, .mut _ as, j => by simp [RArgs.mutIdx, RArgs.mutIdx_succ as (j + 1)]

/-- The handed-back `&mut` values have as many components as the `&mut` arguments' values. -/
theorem RArgs.occs_length {Γ : List Ty} (env : Env Γ) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (vs : (Ty.tup os).carrier),
      (Data.occs vs).length = (as.denote env).occsLen (as.mutIdx 0)
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, vs => by
    rw [RArgs.occs_length env as vs]; simp only [RArgs.mutIdx, RArgs.denote]
    rw [RArgs.mutIdx_succ, Env.occsLen_cons]
  | _, _, .shr _ as, vs => by
    rw [RArgs.occs_length env as vs]; simp only [RArgs.mutIdx, RArgs.denote]
    rw [RArgs.mutIdx_succ, Env.occsLen_cons]
  | _, _, .mut (t := t) (os := os') p as, vs => by
    obtain ⟨v, vs'⟩ := vs
    have e : Data.occs (α := (Ty.tup (t :: os')).carrier) (v, vs') = Data.occs v ++ Data.occs vs' :=
      Data.occs_pair v vs'
    rw [e, List.length_append, RArgs.occs_length env as vs', RArgs.mutIdx, RArgs.mutIdx_succ]
    simp only [RArgs.denote, Env.occsLen, List.map_cons, List.sum_cons, Env.occsAt_cons_zero,
      List.map_map]
    rw [Data.occs_len v (p.get env)]
    simp [Function.comp_def]

/-- One component in a list of components, found from the right. -/
theorem compFull_split {len : Nat} {pre post : List (Option (List Bool))} {x : Option (List Bool)}
    (h : CompFull len post.length (pre ++ x :: post)) :
    ∃ l, x = some l ∧ ∀ k, k < len → l.getD k false = true := by
  obtain ⟨pre', l, post', he, hl, hf⟩ := h
  have := List.append_inj' he (by simp [hl])
  simp only [List.cons.injEq] at this
  exact ⟨l, this.2.1, hf⟩

/-! ## Views passed on whole to a callee -/

/-- The `&mut` parameters, numbered from `j`, whose argument is the variable `x` itself. -/
def RArgs.mutVarAt {Γ : List Ty} (x : Nat) : {ps os : List Ty} → RArgs Γ ps os → Nat → List Nat
  | _, _, .nil, _ => []
  | _, _, .own _ as, j => as.mutVarAt x (j + 1)
  | _, _, .shr _ as, j => as.mutVarAt x (j + 1)
  | _, _, .mut p as, j => (if p.isVarAt x then [j] else []) ++ as.mutVarAt x (j + 1)

theorem RArgs.mutVarAt_succ {Γ : List Ty} (x : Nat) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat),
      as.mutVarAt x (j + 1) = (as.mutVarAt x j).map (· + 1)
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, j => RArgs.mutVarAt_succ x as (j + 1)
  | _, _, .shr _ as, j => RArgs.mutVarAt_succ x as (j + 1)
  | _, _, .mut p as, j => by
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ x as (j + 1), List.map_append]; split <;> simp

/-- The callee's parameter for a `&mut` argument that is the variable `x` holds `x`'s value. -/
theorem RArgs.occsAt_mutVarAt {Γ : List Ty} (env : Env Γ) (x : Nat) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat), j ∈ as.mutVarAt x 0 →
      (as.denote env).occsAt j = env.occsAt x
  | _, _, .nil, _, h => by simp [RArgs.mutVarAt] at h
  | _, _, .own _ as, j, h | _, _, .shr _ as, j, h => by
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ] at h
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp h
    exact RArgs.occsAt_mutVarAt env x as j' hj'
  | _, _, .mut p as, j, h => by
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hv
        simp only [List.mem_singleton] at h; subst h
        exact ((p.isVarAt_occs hv env (p.get env)).2).symm
      · simp at h
    · obtain ⟨j', hj', rfl⟩ := List.mem_map.mp h
      exact RArgs.occsAt_mutVarAt env x as j' hj'

/-- A `&mut` argument that is the view itself is allowed by `keeps` only with `hb`. -/
theorem RArgs.keeps_hb {Γ : List Ty} {x : Nat} {hb : Nat → Bool} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j j' : Nat), as.keeps x hb j = true →
      j' ∈ as.mutVarAt x 0 → hb (j + j') = true
  | _, _, .nil, _, _, _, h => by simp [RArgs.mutVarAt] at h
  | _, _, .own _ as, j, j', hk, h | _, _, .shr _ as, j, j', hk, h => by
    simp only [RArgs.keeps] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ] at h
    obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
    have := RArgs.keeps_hb as (j + 1) j'' hk hj''
    rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this
  | _, _, .mut p as, j, j', hk, h => by
    simp only [RArgs.keeps, Bool.and_eq_true, Bool.or_eq_true] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hv
        simp only [List.mem_singleton] at h; subst h
        rcases hk.1 with hk1 | ⟨_, hb'⟩
        · obtain ⟨m, rfl⟩ : ∃ m, p = .var m := by
            cases p <;> simp_all [Place.isVarAt]
          simp_all [Place.keeps, Place.isVarAt]
        · simpa using hb'
      · simp at h
    · obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
      have := RArgs.keeps_hb as (j + 1) j'' hk.2 hj''
      rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this

theorem RArgs.keepsX_hb {Γ : List Ty} {x : Nat} {hb : Nat → Bool} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j j' : Nat) (sn : Bool), as.keepsX x hb j sn = true →
      j' ∈ as.mutVarAt x 0 → hb (j + j') = true
  | _, _, .nil, _, _, _, _, h => by simp [RArgs.mutVarAt] at h
  | _, _, .own _ as, j, j', sn, hk, h | _, _, .shr _ as, j, j', sn, hk, h => by
    simp only [RArgs.keepsX] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ] at h
    obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
    have := RArgs.keepsX_hb as (j + 1) j'' sn hk hj''
    rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this
  | _, _, .mut p as, j, j', sn, hk, h => by
    simp only [RArgs.keepsX, Bool.and_eq_true, Bool.or_eq_true] at hk
    simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hv
        simp only [List.mem_singleton] at h; subst h
        obtain ⟨m, rfl⟩ : ∃ m, p = .var m := by
          cases p <;> simp_all [Place.isVarAt]
        rcases hk.1 with (hk1 | ⟨_, hb'⟩) | ⟨_, hk3⟩
        · simp_all [Place.root, Place.isVarAt]
        · simpa using hb'
        · simp_all [Place.keeps, Place.isVarAt]
      · simp at h
    · obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp h
      have := RArgs.keepsX_hb as (j + 1) j'' true hk.2 hj''
      rwa [show j + 1 + j'' = j + (j'' + 1) by omega] at this

/-- The handed-back values of a view passed on whole each satisfy `P`, if every component at the
position of such an argument in the handed-back tuple's occupancies does. Here `pre` is the list
of occupancies before it. -/
theorem RArgs.wholeP_of {Γ : List Ty} (env : Env Γ) (i : Nat) (P : List (Option (List Bool)) → Prop) :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (vs : (Ty.tup os).carrier)
      (pre : List (Option (List Bool))),
      (∀ j ∈ as.mutVarAt i 0, ∀ A c B, pre ++ Data.occs vs = A ++ c ++ B →
        B.length = (as.denote env).occsLen ((as.mutIdx 0).filter (j < ·)) →
        c.length = (env.occsAt i).length → P c) →
      as.WholeP i P vs
  | _, _, .nil, _, _, _ => trivial
  | _, _, .own a as, vs, pre, h | _, _, .shr a as, vs, pre, h =>
    RArgs.wholeP_of env i P as vs pre fun j hj A c B he hB hc => by
      refine h (j + 1) (by
        simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ]
        exact List.mem_map.mpr ⟨_, hj, rfl⟩) A c B he ?_ hc
      simpa [RArgs.denote, RArgs.mutIdx, RArgs.mutIdx_succ, List.filter_map, Function.comp_def,
        Env.occsLen] using hB
  | _, _, .mut (t := t) (os := os') p as, vs, pre, h => by
    obtain ⟨v, vs'⟩ := vs
    have e : Data.occs (α := (Ty.tup (t :: os')).carrier) (v, vs') = Data.occs v ++ Data.occs vs' :=
      Data.occs_pair v vs'
    refine ⟨fun hv => ?_, RArgs.wholeP_of env i P as vs' (pre ++ Data.occs v)
      fun j hj A c B he hB hc => ?_⟩
    · refine h 0 (by simp [RArgs.mutVarAt, hv]) pre (Data.occs v) (Data.occs vs')
        (by rw [e, List.append_assoc]) ?_ ?_
      · have hfilt : ((as.mutIdx 0).map (· + 1)).filter (0 < ·) = (as.mutIdx 0).map (· + 1) := by
          rw [List.filter_eq_self]; intro x hx
          obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; simp
        simp only [RArgs.mutIdx, RArgs.mutIdx_succ, RArgs.denote, List.filter_cons,
          Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [hfilt, Env.occsLen_cons, RArgs.occs_length env as vs']
      · rw [(p.isVarAt_occs hv env v).2]; exact Data.occs_len _ _
    · refine h (j + 1) (by
          simp only [RArgs.mutVarAt, RArgs.mutVarAt_succ, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨_, hj, rfl⟩)) A c B
        (by rw [e, ← List.append_assoc]; exact he) ?_ hc
      simpa [RArgs.denote, RArgs.mutIdx, RArgs.mutIdx_succ, List.filter_map, Function.comp_def,
        Env.occsLen] using hB

/-- A one-entry component in a list of components, found from the right. -/
theorem compFull_one {len : Nat} {A c B : List (Option (List Bool))}
    (h : CompFull len B.length (A ++ c ++ B)) (hc : c.length = 1) : OccsFull len c := by
  obtain ⟨pre', l, post', he, hl, hf⟩ := h
  match c, hc with
  | [x], _ =>
    have := List.append_inj' (by simpa using he : (A ++ [x]) ++ B = (pre' ++ [some l]) ++ post')
      (by simp [hl])
    have := List.append_inj' this.1 rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨l, by rw [this.2], hf⟩

/-- A component in a list of components, found from the right. -/
theorem occs_mid {A c B A' c' B' : List (Option (List Bool))} (h : A ++ c ++ B = A' ++ c' ++ B')
    (hB : B.length = B'.length) (hc : c.length = c'.length) : c = c' :=
  (List.append_inj' (List.append_inj' h hB).1 hc).2

theorem Place.keeps_of_root {Γ : List Ty} {i : Nat} {t : Ty} (p : Place Γ t) (h : p.root ≠ i) :
    p.keeps i = true := by
  induction p <;> simp_all [Place.keeps, Place.root]

theorem RArgs.keeps_of_keepsX {Γ : List Ty} {i : Nat} {hb : Nat → Bool} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat) (sn : Bool), as.keepsX i hb j sn = true →
      as.keeps i hb j = true
  | _, _, .nil, _, _, _ => rfl
  | _, _, .own _ as, j, sn, h | _, _, .shr _ as, j, sn, h => RArgs.keeps_of_keepsX as (j + 1) sn h
  | _, _, .mut p as, j, sn, h => by
    simp only [RArgs.keepsX, RArgs.keeps, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
      ne_eq] at h ⊢
    refine ⟨?_, RArgs.keeps_of_keepsX as (j + 1) true h.2⟩
    rcases h.1 with (h1 | h2) | h3
    · exact Or.inl (p.keeps_of_root h1)
    · exact Or.inr h2
    · exact Or.inl h3.2

theorem EArgs.keeps_of_rootsNe {Γ : List Ty} {i : Nat} {ps : List ExtParam} (as : EArgs Γ ps)
    (h : as.rootsNe i = true) : as.keeps i = true := by
  induction as with
  | nil => rfl
  | word _ _ ih | bufIn _ _ ih | bufOut _ ih => exact ih h
  | sliceOut a _ _ _ ih =>
    simp only [EArgs.rootsNe, EArgs.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h ⊢
    exact ⟨a.keeps_of_root h.1, ih h.2⟩

/-! ## Loops writing carried variables -/

theorem Env.set_get_self {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    env.set m (env.get m) = env
  | _, .cons _ _, .here => rfl
  | _, .cons x env, .there m => by simp [Env.set_get_self env m]

/-- Storing the carried variables' own values changes nothing. -/
theorem Carry.set_get {Γ : List Ty} : {ts : List Ty} → (cs : Carry Γ ts) → (env : Env Γ) →
    cs.set env (cs.get env) = env
  | _, .nil, _ => rfl
  | _, .cons m cs, env => by
    simp only [Carry.set, Carry.get]; rw [Env.set_get_self, Carry.set_get cs env]

theorem Carry.set_occsAt_ne {Γ : List Ty} {i : Nat} : {ts : List Ty} → (cs : Carry Γ ts) →
    i ∉ cs.idxs → (env : Env Γ) → (vs : (Ty.tup ts).carrier) → (cs.set env vs).occsAt i = env.occsAt i
  | _, .nil, _, _, _ => rfl
  | _, .cons m cs, h, env, vs => by
    simp only [Carry.idxs, List.mem_cons, not_or] at h
    simp only [Carry.set]
    rw [Carry.set_occsAt_ne cs h.2, Env.occsAt_set_ne env m vs.1 i (Ne.symm h.1)]

theorem Carry.set_occsAt_length {Γ : List Ty} (x : Nat) : {ts : List Ty} → (cs : Carry Γ ts) →
    (env : Env Γ) → (vs : (Ty.tup ts).carrier) →
    ((cs.set env vs).occsAt x).length = (env.occsAt x).length
  | _, .nil, _, _ => rfl
  | _, .cons m cs, env, vs => by
    simp only [Carry.set]; rw [Carry.set_occsAt_length x cs, Env.occsAt_set_length]

theorem Carry.set_occsLen {Γ : List Ty} {ts : List Ty} (cs : Carry Γ ts) (env : Env Γ)
    (vs : (Ty.tup ts).carrier) (xs : List Nat) : (cs.set env vs).occsLen xs = env.occsLen xs := by
  simp only [Env.occsLen, Carry.set_occsAt_length]

/-- The handed-back values have as many components as the carried variables' values. -/
theorem Carry.occs_length {Γ : List Ty} (env : Env Γ) : {ts : List Ty} → (cs : Carry Γ ts) →
    (vs : (Ty.tup ts).carrier) → (Data.occs vs).length = env.occsLen cs.idxs
  | _, .nil, _ => rfl
  | _, .cons (t := t) (ts := ts') m cs, vs => by
    obtain ⟨v, vs'⟩ := vs
    have e : Data.occs (α := (Ty.tup (t :: ts')).carrier) (v, vs') = Data.occs v ++ Data.occs vs' :=
      Data.occs_pair v vs'
    rw [e, List.length_append, Carry.occs_length env cs vs', Data.occs_len v (env.get m),
      ← Env.occsAt_get]
    simp [Env.occsLen, Carry.idxs]

/-- The handed-back value of a carried variable is a component of the handed-back values, followed
by those of the carried variables after it. -/
theorem Carry.occs_split {Γ : List Ty} {i : Nat} : {ts : List Ty} → (cs : Carry Γ ts) →
    cs.distinct = true → i ∈ cs.idxs → (env : Env Γ) → (vs : (Ty.tup ts).carrier) →
    ∃ A B, Data.occs vs = A ++ (cs.set env vs).occsAt i ++ B ∧
      B.length = env.occsLen (cs.after i)
  | _, .nil, _, h, _, _ => by simp [Carry.idxs] at h
  | _, .cons (t := t) (ts := ts') m cs, hd, hi, env, vs => by
    obtain ⟨v, vs'⟩ := vs
    simp only [Carry.distinct, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hd
    have e : Data.occs (α := (Ty.tup (t :: ts')).carrier) (v, vs') = Data.occs v ++ Data.occs vs' :=
      Data.occs_pair v vs'
    simp only [Carry.set, Carry.after]
    by_cases hm : m.idx = i
    · subst hm
      refine ⟨[], Data.occs vs', ?_, ?_⟩
      · rw [Carry.set_occsAt_ne cs hd.1, Env.occsAt_set_same, e]; simp
      · simp only [↓reduceIte]; rw [Carry.occs_length env cs]
    · simp only [Carry.idxs, List.mem_cons] at hi
      obtain ⟨A, B, hAB, hB⟩ := Carry.occs_split cs hd.2 (hi.resolve_left (Ne.symm hm))
        (env.set m v) vs'
      refine ⟨Data.occs v ++ A, B, ?_, ?_⟩
      · rw [e, hAB]; simp
      · simp only [hm, ↓reduceIte]; rw [hB]; simp only [Env.occsLen, Env.occsAt_set_length]

theorem Env.set_set_same {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    (v v' : t.carrier) → (env.set m v).set m v' = env.set m v'
  | _, .cons _ _, .here, _, _ => rfl
  | _, .cons x env, .there m, v, v' => by simp [Env.set_set_same env m v v']

theorem Env.set_comm {t t' : Ty} {Γ : List Ty} (env : Env Γ) (m : Mem t Γ) (m' : Mem t' Γ)
    (h : m.idx ≠ m'.idx) (v : t.carrier) (v' : t'.carrier) :
    (env.set m v).set m' v' = (env.set m' v').set m v := by
  induction env with
  | nil => cases m
  | cons x env ih =>
    cases m with
    | here =>
      cases m' with
      | here => exact absurd rfl h
      | there m' => rfl
    | there m =>
      cases m' with
      | here => rfl
      | there m' =>
        simp only [Env.set_there]; rw [ih m m' (fun e => h (by simp [Mem.idx, e]))]

theorem Carry.set_comm_set {Γ : List Ty} {t : Ty} (m : Mem t Γ) (v : t.carrier) :
    {ts : List Ty} → (cs : Carry Γ ts) → m.idx ∉ cs.idxs → (env : Env Γ) →
    (vs : (Ty.tup ts).carrier) → (cs.set env vs).set m v = cs.set (env.set m v) vs
  | _, .nil, _, _, _ => rfl
  | _, .cons m' cs, h, env, vs => by
    simp only [Carry.idxs, List.mem_cons, not_or] at h
    simp only [Carry.set]
    rw [Carry.set_comm_set m v cs h.2, Env.set_comm env m' m (Ne.symm h.1)]

/-- Storing the carried variables twice is storing the second values. -/
theorem Carry.set_set {Γ : List Ty} : {ts : List Ty} → (cs : Carry Γ ts) → cs.distinct = true →
    (env : Env Γ) → (vs vs' : (Ty.tup ts).carrier) → cs.set (cs.set env vs) vs' = cs.set env vs'
  | _, .nil, _, _, _, _ => rfl
  | _, .cons m cs, hd, env, vs, vs' => by
    simp only [Carry.distinct, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hd
    simp only [Carry.set]
    rw [Carry.set_comm_set m vs'.1 cs hd.1, Env.set_set_same, Carry.set_set cs hd.2]

/-- An invariant of the loop state, kept by every iteration. -/
theorem loopDenote_inv {σ : Type} (P : σ → Prop) (cond : UInt64 → σ → World → Bool × World)
    (body : UInt64 → σ → World → σ × World) (hb : ∀ i a w, P a → P (body i a w).1) :
    ∀ n i acc w, P acc → P (loopDenote cond body n i acc w).1 := by
  intro n
  induction n with
  | zero => intro _ _ _ h; exact h
  | succ n ih =>
    intro i acc w h
    simp only [loopDenote]
    split
    · exact h
    · exact ih _ _ _ (hb _ _ _ h)

/-- An invariant of the loop state, kept by every iteration whose obligations hold. -/
theorem loopDenote_inv_safe {σ : Type} (P : σ → Prop) (condS bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (hb : ∀ i a w, P a → bodyS i a w → P (body i a w).1) :
    ∀ n i acc w, P acc → loopSafe condS bodyS cond body n i acc w →
      P (loopDenote cond body n i acc w).1 := by
  intro n
  induction n with
  | zero => intro _ _ _ h _; exact h
  | succ n ih =>
    intro i acc w h hs
    simp only [loopDenote]
    split
    · exact h
    · rename_i hc
      exact ih _ _ _ (hb _ _ _ h (hs.2 hc).1) (hs.2 hc).2

theorem Env.occsLen_cons2 {t t' : Ty} {Γ : List Ty} (v : t.carrier) (v' : t'.carrier) (env : Env Γ)
    (xs : List Nat) : (Env.cons v (Env.cons v' env)).occsLen (xs.map (· + 2)) = env.occsLen xs := by
  simp [Env.occsLen, Function.comp_def]

/-- The exact hand-back condition implies the hand-back condition. -/
theorem Exp.hbx_hbv {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (i : Nat) (xs : List Nat), e.HBx i xs = true → e.HBv i xs = true := by
  induction e <;> intro i xs h
  case callRef body args k ihb ihk =>
    simp only [Exp.HBx, Exp.HBv, Bool.and_eq_true] at h ⊢
    exact ⟨args.keeps_of_keepsX 0 false h.1, ihk _ _ h.2⟩
  case extMut args k ihk =>
    simp only [Exp.HBx, Exp.HBv, Bool.and_eq_true] at h ⊢
    exact ⟨args.keeps_of_rootsNe h.1, ihk _ _ h.2⟩
  case loop ihc ihb ihk =>
    simp only [Exp.HBx, Exp.HBv, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨⟨h.1.1, h.1.2.imp_right (ihb _ _)⟩, ihk _ _ h.2⟩
  all_goals simp_all [Exp.HBx, Exp.HBv, bne_iff_ne, Place.keeps_of_root]

/-- The statement of `Exp.hbv_sound` for one term. -/
def Exp.HBvSound (ω : Oracle) (len : Nat) {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Prop :=
  ∀ (i : Nat) (xs : List Nat), e.HBv i xs = true → ∀ (env : Env Γ) (w : World),
    OccsFull len (env.occsAt i) → CompFull len (env.occsLen xs) (Data.occs (e.denote ω env w).1)

/-- `Exp.hbv_sound` for a call with reference arguments, where a view passed on whole is handed
back full by the callee's hand-back condition. -/
theorem Exp.hbvSound_callRef (ω : Oracle) (len : Nat) {Γ ps os : List Ty} {r u : Ty}
    (name : String) (req : Env ps → Prop) (body : Exp ps (.pair r (.tup os))) (args : RArgs Γ ps os)
    (k : Exp (r :: Γ) u) (ihb : body.HBvSound ω len) (ihk : k.HBvSound ω len) :
    (Exp.callRef name req body args k).HBvSound ω len := by
  intro i xs h env w hF
  simp only [Exp.HBv, Bool.and_eq_true] at h
  simp only [Exp.denote]
  rw [← args.writeBack_occsLen xs env, ← Env.occsLen_cons _ (args.writeBack env _)]
  refine ihk _ _ h.2 _ _ (args.keeps_full 0 h.1 env hF _ ?_)
  -- a view passed on whole is covered by the callee's hand-back condition for that parameter
  have hl1 : (env.occsAt i).length = 1 := by obtain ⟨l0, hl0, -⟩ := hF; rw [hl0]; rfl
  refine args.wholeP_of env i _ _ (Data.occs (body.denote ω (args.denote env) w).1.1)
    fun j hj A c B he hB hc => compFull_one (A := A) (B := B) ?_ (hc.trans hl1)
  have hx := args.keeps_hb 0 j h.1 hj
  simp only [Nat.zero_add] at hx
  have hF' : OccsFull len ((args.denote env).occsAt j) := by
    rw [args.occsAt_mutVarAt env i j hj]; exact hF
  have := ihb j _ (Exp.hbx_hbv _ j _ hx) (args.denote env) w hF'
  rw [Data.occs_pair, he, ← hB] at this
  exact this

/-- `Exp.hbv_sound` for a loop with carried variables, where the view's cells stay full through
the iterations. -/
theorem Exp.hbvSound_loop (ω : Oracle) (len : Nat) {Γ ts : List Ty} {s u : Ty} (n : Nat)
    (cs : Carry Γ ts) (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u)
    (ihb : body.HBvSound ω len) (ihk : k.HBvSound ω len) :
    (Exp.loop n cs init c body k).HBvSound ω len := by
  intro i xs h env w hF
  simp only [Exp.HBv, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨⟨hd, hc⟩, hk⟩ := h
  have hl1 : (env.occsAt i).length = 1 := by obtain ⟨l0, hl0, -⟩ := hF; rw [hl0]; rfl
  simp only [Exp.denote]
  rw [← Carry.set_occsLen cs env _ xs, ← Env.occsLen_cons _ (cs.set env _)]
  refine ihk _ _ hk _ _ ?_
  rw [Env.occsAt_cons_succ]
  refine loopDenote_inv (fun (st : _ × _) => OccsFull len ((cs.set env st.2).occsAt i)) _ _ ?_ n 0 _ w
    (by rw [Carry.set_get]; exact hF)
  intro j st w' hst
  by_cases hi : i ∈ cs.idxs
  · have hb := hc.resolve_left (fun h => h hi)
    have := ihb _ _ hb (.cons j (.cons st.1 (cs.set env st.2))) w' hst
    rw [Env.occsLen_cons2, Carry.set_occsLen] at this
    generalize body.denote ω (.cons j (.cons st.1 (cs.set env st.2))) w' = r at this ⊢
    obtain ⟨⟨a, vs⟩, _⟩ := r
    obtain ⟨A, B, hAB, hB⟩ := cs.occs_split hd hi env vs
    rw [Data.occs_pair, hAB, ← hB] at this
    exact compFull_one (A := Data.occs a ++ A) (by simpa only [List.append_assoc] using this)
      (by rw [Carry.set_occsAt_length, hl1])
  · rw [Carry.set_occsAt_ne cs hi]; exact hF

/-- The hand-back condition is sound. If the view variable `i` has its cells `0 … len-1` full in
the environment, then in every world and under every oracle the value of a term satisfying
`Exp.HBv i xs` has a component whose cells `0 … len-1` are full, followed by as many components as
the variables `xs` have. -/
theorem Exp.hbv_sound (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (len : Nat) :
    ∀ (i : Nat) (xs : List Nat), e.HBv i xs = true → ∀ (env : Env Γ) (w : World),
      OccsFull len (env.occsAt i) → CompFull len (env.occsLen xs) (Data.occs (e.denote ω env w).1) := by
  induction e with
  | let_ _ _ _ ih₂ =>
    intro i xs h env w hF; rw [← Env.occsLen_cons _ env]; exact ih₂ _ _ h _ _ hF
  | ite c _ _ ih₁ ih₂ =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    split
    · exact ih₁ i xs h.1 env w hF
    · exact ih₂ i xs h.2 env w hF
  | match_ s _ _ ihE ihO =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    cases (s.denote env) with
    | error x => rw [← Env.occsLen_cons x env]; exact ihE _ _ h.1 _ w hF
    | ok x => rw [← Env.occsLen_cons x env]; exact ihO _ _ h.2 _ w hF
  | case s sp _ _ ihP ihQ =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    cases sp.split (s.denote env) with
    | inl x => rw [← Env.occsLen_cons x env]; exact ihP _ _ h.1 _ w hF
    | inr y => rw [← Env.occsLen_cons y env]; exact ihQ _ _ h.2 _ w hF
  | mk c args =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨cert⟩, hc⟩, hl⟩ := h
    obtain ⟨pre, hp⟩ := args.occs_endVars env _ hl
    obtain ⟨l, hl', hf⟩ := hF
    refine ⟨pre, l, (xs.map env.occsAt).flatten, ?_, ?_, hf⟩
    · simp only [Exp.denote, cert, hp, List.map_cons, List.flatten_cons, hl']; simp
    · simp [Env.occsLen, List.length_flatten, Function.comp_def]
  | assign p a _ ih =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    rw [← p.set_occsLen env (a.denote env)]
    exact ih i xs h.2 _ w (p.keeps_full h.1 env hF _)
  | put p j a _ ih =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    rw [← p.set_occsLen env]
    exact ih i xs h.2 _ w (p.keeps_full h.1 env hF _)
  | take p j _ ih =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    rw [← p.set_occsLen env, ← Env.occsLen_cons _ (p.set env _)]
    exact ih _ _ h.2 _ w (p.keeps_full h.1 env hF _)
  | borrowShr p _ _ _ ihk =>
    intro i xs h env w hF
    simp only [Exp.denote]
    rw [← Env.occsLen_cons _ env]; exact ihk _ _ h _ _ hF
  | borrowMut p _ _ _ ihk =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    rw [← p.set_occsLen env, ← Env.occsLen_cons _ (p.set env _)]
    exact ihk _ _ h.2 _ _ (p.keeps_full h.1 env hF _)
  | callRef name req body args k ihb ihk =>
    exact Exp.hbvSound_callRef ω len name req body args k ihb ihk
  | extMut _ args _ ihk =>
    intro i xs h env w hF
    simp only [Exp.HBv, Bool.and_eq_true] at h
    simp only [Exp.denote]
    rw [← args.fill_occsLen xs env env, ← Env.occsLen_cons _ (args.fill env env _)]
    exact ihk _ _ h.2 _ _ (args.keeps_full h.1 env env _ hF)
  | loop n cs init c body k _ ihb ihk => exact Exp.hbvSound_loop ω len n cs init c body k ihb ihk
  | _ => intro i xs h; simp [Exp.HBv] at h

/-- `Exp.hbv_sound` for the hand-back condition `Exp.HB`, where the view's component is the last
one. -/
theorem Exp.hb_sound (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (len : Nat) (i : Nat)
    (h : e.HB i = true) (env : Env Γ) (w : World) (hF : OccsFull len (env.occsAt i)) :
    LastFull len (Data.occs (e.denote ω env w).1) := by
  obtain ⟨pre, l, post, he, hl, hf⟩ := e.hbv_sound ω len i [] h env w hF
  have : post = [] := List.eq_nil_of_length_eq_zero (by simpa [Env.occsLen] using hl)
  subst this
  exact ⟨pre, l, he, hf⟩

/-! ## The exact hand-back condition

A view passed on whole to a callee by `&mut` becomes the callee's handed-back value, so the
caller's view must keep its exact occupancy, with its first `len` cells full and the others empty.
A write through a cell keeps the occupancy exactly when the cell is full, which is the write's
obligation, so the exact condition is proved for safe terms. -/

theorem Slots.occs_setCell_full {α : Type} [Data α] {n : Nat} (s : Slots α n) (j : Nat) (x : α)
    (h : s.isFull j = true) : Data.occs (s.setCell j (some x)) = Data.occs s := by
  rw [Slots.occs_eq, Slots.occs_eq]
  congr 2
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have e1 := Slots.getD_occ (s.setCell j (some x)) k
  have e2 := Slots.getD_occ s k
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e2
  rw [e1, e2, Slots.isFull_setCell]
  split
  · rename_i hk; obtain ⟨rfl, -⟩ := hk; simp [h]
  · rfl

namespace Place
variable {Γ : List Ty}

/-- A write at a place that keeps the view variable `i` leaves its occupancy unchanged when the
write's obligations hold. -/
theorem keeps_exact {i : Nat} {t : Ty} (p : Place Γ t) (hk : p.keeps i = true) (env : Env Γ)
    (hok : p.ok env) (v : t.carrier) : (p.set env v).occsAt i = env.occsAt i := by
  induction p with
  | var m =>
    simp only [keeps, bne_iff_ne, ne_eq] at hk
    exact Env.occsAt_set_ne env m v i hk
  | field p l ih => exact ih hk hok _
  | index p _ ih => exact ih hk hok.1 _
  | range p _ _ ih => exact ih hk hok.1 _
  | pair2 p _ _ ih => exact ih hk hok.1 _
  | rangeS m lo len =>
    simp only [Place.set]
    by_cases he : m.idx = i
    · subst he; rw [Env.occsAt_set_same, Env.occsAt_get]
      exact sunview_occs _ _ _ _ fun k hk => hok.2 _ (by omega)
    · exact Env.occsAt_set_ne env m _ i he
  | pair2S m j k =>
    simp only [Place.set]
    by_cases he : m.idx = i
    · subst he; rw [Env.occsAt_set_same, Env.occsAt_get]
      rw [Slots.occs_setCell_full _ _ _ (by rw [Slots.isFull_setCell]; split <;> simp_all [hok.2.1]),
        Slots.occs_setCell_full _ _ _ hok.1]
    · exact Env.occsAt_set_ne env m _ i he
  | slot p j ih =>
    simp only [keeps, Bool.or_eq_true] at hk
    by_cases hv : p.isVarAt i = true
    · obtain ⟨h1, h2⟩ := p.isVarAt_occs hv env
        (Slots.setCell (p.get env) (j.denote env).toNat (some v))
      simp only [Place.set]; rw [h1, h2]
      exact Slots.occs_setCell_full _ _ _ hok.2
    · exact ih (hk.resolve_left hv) hok.1 _

/-- A write at a place rooted elsewhere leaves variable `i` alone. -/
theorem set_occsAt_ne {i : Nat} {t : Ty} (p : Place Γ t) (h : p.root ≠ i) (env : Env Γ)
    (v : t.carrier) : (p.set env v).occsAt i = env.occsAt i := by
  induction p with
  | var m => exact Env.occsAt_set_ne env m v i h
  | rangeS m => exact Env.occsAt_set_ne env m _ i h
  | pair2S m => exact Env.occsAt_set_ne env m _ i h
  | _ => simp only [Place.set]; simp_all [Place.root]

end Place

theorem EArgs.fill_occsAt_ne {Γ : List Ty} {i : Nat} {ps : List ExtParam} (as : EArgs Γ ps)
    (h : as.rootsNe i = true) (env : Env Γ) :
    ∀ (env' : Env Γ) (bss : List (List UInt8)), (as.fill env env' bss).occsAt i = env'.occsAt i := by
  induction as with
  | nil => intro _ _; rfl
  | word _ _ ih | bufIn _ _ ih | bufOut _ ih => intro env' bss; exact ih h _ _
  | sliceOut a _ _ _ ih =>
    simp only [EArgs.rootsNe, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro env' bss
    simp only [EArgs.fill]; rw [ih h.2, a.set_occsAt_ne h.1]

theorem RArgs.keepsX_exact {Γ : List Ty} {i : Nat} {hb : Nat → Bool}
    {O : List (Option (List Bool))} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (j : Nat) (sn : Bool), as.keepsX i hb j sn = true →
      ∀ (env₀ env : Env Γ), (sn = false → env = env₀) → as.ok env₀ → env.occsAt i = O →
      ∀ (vs : (Ty.tup os).carrier), as.WholeP i (· = O) vs → (as.writeBack env vs).occsAt i = O
  | _, _, .nil, _, _, _, _, _, _, _, hO, _, _ => hO
  | _, _, .own _ as, j, sn, hk, env₀, env, he, hok, hO, vs, hW =>
    RArgs.keepsX_exact as (j + 1) sn hk env₀ env he hok hO vs hW
  | _, _, .shr _ as, j, sn, hk, env₀, env, he, hok, hO, vs, hW =>
    RArgs.keepsX_exact as (j + 1) sn hk env₀ env he hok.2 hO vs hW
  | _, _, .mut p as, j, sn, hk, env₀, env, he, hok, hO, vs, hW => by
    simp only [RArgs.keepsX, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk
    refine RArgs.keepsX_exact as (j + 1) true hk.2 env₀ _ (fun e => by cases e) hok.2 ?_ vs.2 hW.2
    rcases hk.1 with (hk1 | ⟨hv, _⟩) | ⟨hs, hk3⟩
    · rw [p.set_occsAt_ne hk1]; exact hO
    · rw [(p.isVarAt_occs hv env vs.1).1]; exact hW.1 hv
    · have e := he (by simpa using hs)
      subst e
      rw [p.keeps_exact hk3 _ hok.1]; exact hO

/-- The handed-back values of a view `x` passed on whole to a callee that satisfies the exact
hand-back condition for those parameters have the occupancies of `x`. -/
theorem RArgs.wholeEq_of (ω : Oracle) {Γ ps os : List Ty} {r : Ty} {as : RArgs Γ ps os}
    (env : Env Γ) (x : Nat) (body : Exp ps (.pair r (.tup os))) (w : World)
    (hx : ∀ j ∈ as.mutVarAt x 0, body.HBx j ((as.mutIdx 0).filter (j < ·)) = true)
    (hb : ∀ j, body.HBx j ((as.mutIdx 0).filter (j < ·)) = true →
      ∃ pre post, Data.occs (body.denote ω (as.denote env) w).1 =
        pre ++ (as.denote env).occsAt j ++ post ∧
        post.length = (as.denote env).occsLen ((as.mutIdx 0).filter (j < ·))) :
    as.WholeP x (· = env.occsAt x) (body.denote ω (as.denote env) w).1.2 :=
  as.wholeP_of env x _ _ (Data.occs (body.denote ω (as.denote env) w).1.1)
    fun j hj A c B he hB hc => by
      obtain ⟨pre', post', he', hl'⟩ := hb j (hx j hj)
      rw [Data.occs_pair, he, as.occsAt_mutVarAt env x j hj] at he'
      exact occs_mid he' (by rw [hB, hl']) (by rw [hc])

/-- One iteration of a loop keeps a carried view's occupancy when its body satisfies the exact
hand-back condition for the view, given `Exp.hbx_exact` for the body. -/
theorem Carry.exact_step {Γ ts : List Ty} {s : Ty} (cs : Carry Γ ts) (hd : cs.distinct = true)
    {i : Nat} (hi : i ∈ cs.idxs) (env : Env Γ) (j : UInt64) (a : s.carrier)
    (r : (Ty.pair s (Ty.tup ts)).carrier)
    (hb : ∃ pre post,
      Data.occs r = pre ++ (Env.cons (t := .u64) j (Env.cons a env)).occsAt (i + 2) ++ post ∧
        post.length = (Env.cons (t := .u64) j (Env.cons a env)).occsLen ((cs.after i).map (· + 2))) :
    (cs.set env r.2).occsAt i = env.occsAt i := by
  obtain ⟨pre, post, he, hp⟩ := hb
  rw [Env.occsLen_cons2] at hp
  simp only [Env.occsAt_cons_succ] at he
  obtain ⟨A, B, hAB, hB⟩ := cs.occs_split hd hi env r.2
  have e : Data.occs r = Data.occs r.1 ++ Data.occs r.2 := Data.occs_pair r.1 r.2
  rw [e, hAB] at he
  exact occs_mid (A := Data.occs r.1 ++ A) (by simpa only [List.append_assoc] using he)
    (hB.trans hp.symm) (by rw [Carry.set_occsAt_length])

/-- The statement of `Exp.hbx_exact` for one term. -/
def Exp.HBxExact (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Prop :=
  ∀ (i : Nat) (xs : List Nat), e.HBx i xs = true → ∀ (env : Env Γ) (w : World),
    e.safe ω env w → ∃ pre post, Data.occs (e.denote ω env w).1 = pre ++ env.occsAt i ++ post ∧
      post.length = env.occsLen xs

/-- `Exp.hbx_exact` for a call with reference arguments. -/
theorem Exp.hbxExact_callRef (ω : Oracle) {Γ ps os : List Ty} {r u : Ty}
    (name : String) (req : Env ps → Prop) (body : Exp ps (.pair r (.tup os))) (args : RArgs Γ ps os)
    (k : Exp (r :: Γ) u) (ihb : body.HBxExact ω) (ihk : k.HBxExact ω) :
    (Exp.callRef name req body args k).HBxExact ω := by
  intro i xs h env w hs
  simp only [Exp.HBx, Bool.and_eq_true] at h
  simp only [Exp.denote]
  have hwb : (args.writeBack env (body.denote ω (args.denote env) w).1.2).occsAt i =
      env.occsAt i :=
    args.keepsX_exact 0 false h.1 env env (fun _ => rfl) hs.1 rfl _ (args.wholeEq_of ω env i body w
      (fun j hj => by simpa using args.keepsX_hb 0 j false h.1 hj)
      (fun j hx => ihb j _ hx (args.denote env) w (hs.2.2.1 _ _ hs.2.1)))
  rw [← args.writeBack_occsLen xs env, ← Env.occsLen_cons _ (args.writeBack env _), ← hwb,
    ← Env.occsAt_cons_succ _ (args.writeBack env _)]
  exact ihk _ _ h.2 _ _ hs.2.2.2

/-- `Exp.hbx_exact` for a loop with carried variables, where each iteration keeps a carried view's
occupancy. -/
theorem Exp.hbxExact_loop (ω : Oracle) {Γ ts : List Ty} {s u : Ty} (n : Nat)
    (cs : Carry Γ ts) (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u)
    (ihb : body.HBxExact ω) (ihk : k.HBxExact ω) :
    (Exp.loop n cs init c body k).HBxExact ω := by
  intro i xs h env w hs
  simp only [Exp.HBx, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨⟨hd, hc⟩, hk⟩ := h
  simp only [Exp.denote]
  have hinv := loopDenote_inv_safe (fun (st : _ × _) => (cs.set env st.2).occsAt i = env.occsAt i) _ _ _ _
    (by
      intro j st w' hst hbs
      by_cases hi : i ∈ cs.idxs
      · rw [← hst, ← Carry.set_set cs hd env st.2]
        exact cs.exact_step hd hi _ j st.1 _ (ihb _ _ (hc.resolve_left (fun h => h hi)) _ w' hbs)
      · rw [Carry.set_occsAt_ne cs hi])
    n 0 (init.denote env, cs.get env) w (by rw [Carry.set_get]) hs.1
  rw [← Carry.set_occsLen cs env _ xs, ← Env.occsLen_cons _ (cs.set env _), ← hinv,
    ← Env.occsAt_cons_succ _ (cs.set env _)]
  exact ihk _ _ hk _ _ hs.2

/-- The exact hand-back condition is sound. In a safe term satisfying `Exp.HBx i xs`, the
occupancies of the view variable `i` are a component of the value, followed by as many components
as the variables `xs` have. -/
theorem Exp.hbx_exact (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (i : Nat) (xs : List Nat), e.HBx i xs = true → ∀ (env : Env Γ) (w : World),
      e.safe ω env w → ∃ pre post, Data.occs (e.denote ω env w).1 = pre ++ env.occsAt i ++ post ∧
        post.length = env.occsLen xs := by
  induction e with
  | let_ _ _ _ ih₂ =>
    intro i xs h env w hs
    rw [← Env.occsLen_cons _ env, ← Env.occsAt_cons_succ _ env]; exact ih₂ _ _ h _ _ hs.2
  | ite c _ _ ih₁ ih₂ =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    simp only [Exp.denote]
    split
    · exact ih₁ i xs h.1 env w (hs.1 (by assumption))
    · exact ih₂ i xs h.2 env w (hs.2 (by simpa using (by assumption)))
  | match_ s _ _ ihE ihO =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    simp only [Exp.denote]
    cases hsd : (s.denote env) with
    | error x =>
      rw [← Env.occsLen_cons x env, ← Env.occsAt_cons_succ x env]
      exact ihE _ _ h.1 _ w (hs.1 x hsd)
    | ok x =>
      rw [← Env.occsLen_cons x env, ← Env.occsAt_cons_succ x env]
      exact ihO _ _ h.2 _ w (hs.2 x hsd)
  | case s sp _ _ ihP ihQ =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    simp only [Exp.denote]
    cases hsp : sp.split (s.denote env) with
    | inl x =>
      rw [← Env.occsLen_cons x env, ← Env.occsAt_cons_succ x env]
      exact ihP _ _ h.1 _ w (hs.1 x hsp)
    | inr y =>
      rw [← Env.occsLen_cons y env, ← Env.occsAt_cons_succ y env]
      exact ihQ _ _ h.2 _ w (hs.2 y hsp)
  | mk c args =>
    intro i xs h env w _
    simp only [Exp.HBx, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨cert⟩, hc⟩, hl⟩ := h
    obtain ⟨pre, hp⟩ := args.occs_endVars env _ hl
    refine ⟨pre, (xs.map env.occsAt).flatten, ?_, ?_⟩
    · simp only [Exp.denote, cert, hp, List.map_cons, List.flatten_cons]; simp
    · simp [Env.occsLen, List.length_flatten, Function.comp_def]
  | assign p a _ ih =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    rw [← p.set_occsLen env (a.denote env), ← p.keeps_exact h.1 env hs.1 (a.denote env)]
    exact ih i xs h.2 _ w hs.2
  | put p j a _ ih =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [← p.set_occsLen env, ← p.set_occsAt_ne h.1 env]
    exact ih i xs h.2 _ w hs.2
  | take p j _ ih =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [Exp.denote]
    rw [← p.set_occsLen env, ← Env.occsLen_cons _ (p.set env _), ← p.set_occsAt_ne h.1 env,
      ← Env.occsAt_cons_succ _ (p.set env _)]
    exact ih _ _ h.2 _ w hs.2
  | borrowShr p _ _ _ ihk =>
    intro i xs h env w hs
    simp only [Exp.denote]
    rw [← Env.occsLen_cons _ env, ← Env.occsAt_cons_succ _ env]; exact ihk _ _ h _ _ hs.2.2
  | borrowMut p _ _ _ ihk =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    simp only [Exp.denote]
    rw [← p.set_occsLen env, ← Env.occsLen_cons _ (p.set env _), ← p.keeps_exact h.1 env hs.1,
      ← Env.occsAt_cons_succ _ (p.set env _)]
    exact ihk _ _ h.2 _ _ hs.2.2
  | callRef name req body args k ihb ihk => exact Exp.hbxExact_callRef ω name req body args k ihb ihk
  | extMut _ args _ ihk =>
    intro i xs h env w hs
    simp only [Exp.HBx, Bool.and_eq_true] at h
    simp only [Exp.denote]
    rw [← args.fill_occsLen xs env env, ← Env.occsLen_cons _ (args.fill env env _),
      ← args.fill_occsAt_ne h.1 env env, ← Env.occsAt_cons_succ _ (args.fill env env _)]
    exact ihk _ _ h.2 _ _ hs.2
  | loop n cs init c body k _ ihb ihk => exact Exp.hbxExact_loop ω n cs init c body k ihb ihk
  | _ => intro i xs h; simp [Exp.HBx] at h

/-- The write-back obligation of a `&mut` slice borrow follows from the hand-back condition. A
body satisfying `Exp.HB 0`, entered with a view whose cells `0 … len-1` are full, hands back a view
whose cells `0 … len-1` are full. The entry view is `vview arr lo len` of an array range that fits,
or `sview` of a sub-slice. -/
theorem hb_backOk (ω : Oracle) {Γ : List Ty} {T u : Ty} {N : Nat}
    (body : Exp (Ty.view T N :: Γ) (.pair u (Ty.view T N))) (hHB : body.HB 0 = true)
    (v₀ : Slots T.carrier N) (len : Nat) (hv₀ : ∀ k, k < len → v₀.isFull k = true) (env : Env Γ)
    (w : World) : ∀ k, k < len → (body.denote ω (.cons v₀ env) w).1.2.isFull k = true := by
  have hF : OccsFull len ((Env.cons (t := Ty.view T N) v₀ env).occsAt 0) :=
    ⟨_, Slots.occs_eq _, fun k hk => by rw [Slots.getD_occ]; exact hv₀ k hk⟩
  obtain ⟨pre, l, he, hf⟩ := body.hb_sound ω len 0 hHB _ w hF
  generalize body.denote ω (.cons v₀ env) w = r at he
  obtain ⟨⟨x, s⟩, _⟩ := r
  intro k hk
  have e2 : Data.occs (x, s) = Data.occs x ++ [some (s.cells.toList.map Option.isSome)] := rfl
  rw [e2] at he
  have := (List.append_inj' he rfl).2
  simp only [List.cons.injEq, Option.some.injEq, and_true] at this
  rw [← Slots.getD_occ, this]; exact hf k hk

end Millipede
