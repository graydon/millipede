import Millipede.Compile.LowerPairRef

/-!
# Places over a view variable

The sub-slice `s[lo..lo+len]` and the pair of cells `s[i], s[j]` of a slice view or `Slots`
variable `s` are lowered by pointer arithmetic on the variable's address, which for a view is the
address its slot holds. Element `k` is at `A + k · size`, and nothing is copied. This module proves
the facts about the variable that these places rest on:

* a full cell lies inside the variable's storage, which for a view is its extent, and its bytes
  represent its content;
* the variable has no hole, because the places' path is `[dyn]`, which overlaps every path, so the
  borrow checker lets them be used only while nothing of `s` is lent;
* the value of a sub-slice is represented by the bytes from element `lo` on, and is a view of `len`
  elements;
* memory whose full cells represent a new value with the same occupancy, and which is unchanged
  elsewhere, represents the environment with the new value, which covers writing back a sub-slice
  whose range was full and writing two cells.

The design of slices is described in doc/design/memory.md.
-/

namespace Millipede.Flat

theorem Sel.overlap_dyn_right : ∀ π : List Sel, Sel.overlap π [.dyn] = true
  | [] => rfl
  | [_] => by simp [Sel.overlap]
  | _ :: _ :: _ => by simp [Sel.overlap]

theorem Sel.overlap_dyn_left (π : List Sel) : Sel.overlap [.dyn] π = true := by
  cases π <;> simp [Sel.overlap]

theorem ViewOK.of_occs {t : Ty} {v v' : t.carrier} {e : Nat} (h : ViewOK t v' e)
    (ho : Data.occs v = Data.occs v') : ViewOK t v e := by
  obtain ⟨cnt, len, sh, h1, h2, h3, h4⟩ := h
  exact ⟨cnt, len, sh, h1, h2, h3, ho.trans h4⟩

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {env : Env Γ}
  {h : Heap}

/-- A place whose path is `[dyn]` and that the borrow checker lets a term use has a root without a
hole. -/
theorem hole_none_of_dyn {t : Ty} {p : Place Γ t} (hp : p.path = [.dyn])
    (hnh : ∀ H, (S.getD p.root default).hole = some H → Sel.overlap H.path p.path = false) :
    (S.getD p.root default).hole = none := by
  cases e : (S.getD p.root default).hole with
  | none => rfl
  | some H => have := hnh H e; rw [hp, Sel.overlap_dyn_right] at this; cases this

theorem slots_snd {T : Ty} {N : Nat} (hl : Lay bp n Γ ρ S W) (m : Mem (.slots T N) Γ) :
    (S.getD m.idx default).snd = none :=
  (hl.var m).snd_none_of_ty (slots_not_prod T N)

/-- A full cell of a `Slots` or view variable lies in its storage. For a view the storage is its
extent, and its full cells are its first ones. -/
theorem slots_cell_bound (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (m : Mem (.slots T N) Γ) {k : Nat} (hk : (env.get m : Slots T.carrier N).isFull k = true) :
    k * T.size + T.size ≤ (S.getD m.idx default).sz (.slots T N) := by
  have hkN : k < N := by
    rcases Nat.lt_or_ge k N with h | h
    · exact h
    · simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr h] at hk
  have hsz : (Ty.slots T N).size = N * T.size := rfl
  cases he : (S.getD m.idx default).ext with
  | none =>
    rw [SI.sz_none he, hsz, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hkN
  | some e =>
    obtain ⟨_, _, _, hx⟩ := (henv.get_ty m rfl).1
    obtain ⟨len, hle, he', hcells⟩ := viewOK_slots (hx e he (slots_snd hl m))
    have hck := hcells k hkN
    have hf : ((env.get m : Slots T.carrier N).cells[k]).isSome = true := by
      simpa [Slots.isFull, Slots.cell, vget, hkN] using hk
    rw [hf] at hck
    have hkl : k < len := by simpa using hck.symm
    simp only [SI.sz, SI.lim, he]
    rw [he', hsz, Nat.min_eq_left (Nat.mul_le_mul_right _ hle), ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hkl

/-- When the cells below `hi` are full, the first `hi` elements lie in the storage. -/
theorem slots_run_bound (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (m : Mem (.slots T N) Γ) {hi : Nat}
    (hf : ∀ k, k < hi → (env.get m : Slots T.carrier N).isFull k = true) :
    hi * T.size ≤ (S.getD m.idx default).sz (.slots T N) := by
  cases hi with
  | zero => simp
  | succ k => rw [Nat.succ_mul]; exact slots_cell_bound hl henv m (hf k (by omega))

/-- A full cell's bytes represent its content, when the variable has no hole. -/
theorem slots_var_repr (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (m : Mem (.slots T N) Γ) (hH : (S.getD m.idx default).hole = none) {k : Nat} {x : T.carrier}
    (hk : (env.get m : Slots T.carrier N).cell k = some x) :
    Data.reprBytes x (rd h ((S.getD m.idx default).A + k * T.size) T.size) :=
  (slots_cell_repr _ hk (VarRel.exact_slots (henv.get_ty m rfl).1 hH (slots_snd hl m))).2

/-- A sub-slice's view is represented by the bytes from element `lo` on: its cell `k < len` is cell
`lo + k`, and its other cells are empty, whatever their bytes. -/
theorem sview_repr {T : Ty} {N lo len : Nat} (v : Slots T.carrier N) {m : Heap} {A : Nat}
    (hv : Data.reprBytes (α := Slots T.carrier N) v (rd m A (N * T.size)))
    (_hfit : lo + len ≤ N) :
    Data.reprBytes (α := Slots T.carrier N) (sview v lo len) (rd m (A + lo * T.size) (N * T.size)) := by
  refine ⟨rd_length _ _ _, fun k hk => ?_⟩
  show Slots.cellRepr (sview v lo len).cells[k]
    (slice (rd m (A + lo * T.size) (N * T.size)) (k * T.size) T.size)
  have hc : (sview v lo len).cells[k] = if h : k < len ∧ lo + k < N then v.cells[lo + k] else none := by
    have := sview_cell v lo len k
    simp only [Slots.cell, vget, hk, ↓reduceDIte] at this
    rw [this]
    by_cases h1 : k < len <;> by_cases h2 : lo + k < N <;> simp [h1, h2]
  rw [hc]
  split
  · rename_i hkl
    have hj : lo + k < N := hkl.2
    have hkN : k * T.size + T.size ≤ N * T.size := elem_bound hk
    have hjN : (lo + k) * T.size + T.size ≤ N * T.size := elem_bound hj
    rw [← rd_slice _ _ _ _ _ hkN, show A + lo * T.size + k * T.size = A + (lo + k) * T.size by
      rw [Nat.add_mul]; omega, rd_slice _ _ (N * T.size) _ _ hjN]
    have := hv.2 (lo + k) hj
    simpa [Shape.elemOffset] using this
  · trivial

/-- A sub-slice's view of a range whose cells are full is a view of `len` elements. -/
theorem viewOK_sview {T : Ty} {N lo len : Nat} (v : Slots T.carrier N) (hfit : lo + len ≤ N)
    (hf : ∀ k, k < lo + len → v.isFull k = true) :
    ViewOK (.slots T N) (sview v lo len) (len * T.size) := by
  refine viewOK_of_slots (by omega) fun k hk => ?_
  have := sview_cell v lo len k
  simp only [Slots.cell, vget, hk, ↓reduceDIte] at this
  rw [this]
  by_cases hkl : k < len
  · have h2 := hf (lo + k) (by omega)
    simp only [Slots.isFull, Slots.cell, vget, show lo + k < N by omega, ↓reduceDIte] at h2
    simp [hkl, show lo + k < N by omega, h2]
  · simp [hkl]

/-- The sub-slice's cells `0 … len-1` are full, as the hand-back condition needs. -/
theorem sview_full {α : Type} {N lo len : Nat} (v : Slots α N) (hfit : lo + len ≤ N)
    (hf : ∀ k, k < lo + len → v.isFull k = true) {k : Nat} (hk : k < len) :
    (sview v lo len).isFull k = true := by
  unfold Slots.isFull; rw [sview_cell]
  have := hf (lo + k) (by omega)
  simp only [Slots.isFull] at this
  simp [hk, show k < N by omega, this]

/-- Writing a `Slots` or view variable whose storage changed. Memory that is unchanged below the
watermark outside the variable's storage, and whose bytes at each full cell of the new value
represent its content, represents the environment with the new value, provided the new value has
the old value's occupancy, so that a view stays a view of its extent. -/
theorem slots_set_rel (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    (hbn : bp + n ≤ UInt64.size) {T : Ty} {N : Nat} (m : Mem (.slots T N) Γ)
    (hW : W.getD m.idx false = true) (h' : Heap) (v : Slots T.carrier N)
    (hocc : Data.occs v = Data.occs (env.get m))
    (hcell : ∀ k x, v.cell k = some x →
      Data.reprBytes x (rd h' ((S.getD m.idx default).A + k * T.size) T.size))
    (hout : ∀ a, a < bp + n → ¬ InR (S.getD m.idx default).A ((S.getD m.idx default).sz (.slots T N)) a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MEnvRel h' bp (env.set m v) ρ S := by
  have hsn := slots_snd hl m
  have hsz : (Ty.slots T N).size = N * T.size := rfl
  refine henv.set_var' m v hl hW hbn (fun a ha hn => hout a ha (by rwa [← SI.In_none hsn])) fun _ =>
    ⟨rd h' (S.getD m.idx default).A (N * T.size), ⟨rd_length _ _ _, fun k hk => ?_⟩,
      fun i hi _ => ?_, fun e he _ => ?_⟩
  · show Slots.cellRepr v.cells[k] (slice _ ((Data.shape T.carrier).elemOffset k) _)
    cases hc : v.cells[k] with
    | none => trivial
    | some x =>
      have := hcell k x (by simp [Slots.cell, vget, hk, hc])
      simp only [Slots.cellRepr, Shape.elemOffset]
      rw [← rd_slice _ _ _ _ _ (elem_bound hk)]; exact this
  · rw [SI.at_none hsn]
    exact (rd_getD h' _ _ i (by have := (S.getD m.idx default).sz_le (.slots T N); omega)).symm
  · obtain ⟨_, _, _, hx⟩ := (henv.get_ty m rfl).1
    exact ViewOK.of_occs (hx e he hsn) hocc

/-! ## The sub-slice `s[lo..lo+len]` -/

/-- The facts about a sub-slice of a `Slots` or view variable without a hole, whose cells below
`lo + len` are full. Its `len` elements from `A' = A + lo · size` lie inside the variable's
storage, below the watermark, and represent its view. -/
theorem rangeS_facts (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (m : Mem (.slots T N) Γ) (lo len : Atom Γ .u64) (hok : (Place.rangeS m lo len).ok env)
    (hH : (S.getD m.idx default).hole = none) :
    let A' := (S.getD m.idx default).A + (lo.denote env).toNat * T.size
    (len.denote env).toNat ≤ N ∧ A' + (len.denote env).toNat * T.size ≤ bp + n ∧
      (S.getD m.idx default).Holds (.slots T N) A' ((len.denote env).toNat * T.size) ∧
      Data.reprBytes (α := Slots T.carrier N) ((Place.rangeS m lo len).get env) (rd h A' (N * T.size)) ∧
      ViewOK (.slots T N) ((Place.rangeS m lo len).get env) ((len.denote env).toNat * T.size) := by
  intro A'
  obtain ⟨hfit, hf⟩ := hok
  have hsn := slots_snd hl m
  have hrun := slots_run_bound hl henv m hf
  have hdl := (hl.var m).dataLe hsn
  rw [Nat.add_mul] at hrun
  refine ⟨by omega, by simp only [A']; omega, ?_, ?_, viewOK_sview _ hfit hf⟩
  · simp only [SI.Holds, hsn, A']; omega
  · exact sview_repr _ (VarRel.exact_slots (henv.get_ty m rfl).1 hH hsn) hfit

/-- Writing a sub-slice back. Memory whose sub-slice elements hold the bytes of the handed-back
view, all of whose cells `0 … len-1` are full, and which is unchanged elsewhere below the
watermark, represents the write-back. -/
theorem rangeS_set_rel (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    (hbn : bp + n ≤ UInt64.size) {T : Ty} {N : Nat} (m : Mem (.slots T N) Γ) (lo len : Atom Γ .u64)
    (hok : (Place.rangeS m lo len).ok env) (hH : (S.getD m.idx default).hole = none)
    (hW : W.getD m.idx false = true) (h' : Heap) (v : Slots T.carrier N)
    (hfull : ∀ k, k < (len.denote env).toNat → v.isFull k = true) (V : List UInt8)
    (hV : Data.reprBytes (α := Slots T.carrier N) v V)
    (hVm : slice V 0 ((len.denote env).toNat * T.size) =
      rd h' ((S.getD m.idx default).A + (lo.denote env).toNat * T.size) ((len.denote env).toNat * T.size))
    (hout : ∀ a, a < bp + n → ¬ InR ((S.getD m.idx default).A + (lo.denote env).toNat * T.size)
      ((len.denote env).toNat * T.size) a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MEnvRel h' bp ((Place.rangeS m lo len).set env v) ρ S := by
  obtain ⟨hfit, hf⟩ := hok
  generalize hlo : (lo.denote env).toNat = lo' at *
  generalize hle : (len.denote env).toNat = len' at *
  have hsn := slots_snd hl m
  have hrun := slots_run_bound hl henv m hf
  have hdl := (hl.var m).dataLe hsn
  rw [Nat.add_mul] at hrun
  show MEnvRel h' bp (env.set m (sunview (env.get m) (lo.denote env).toNat (len.denote env).toNat v)) ρ S
  rw [hlo, hle]
  refine slots_set_rel hl henv hbn m hW h' _ (sunview_occs _ _ _ _ fun k hk => hf _ (by omega))
    (fun k x hx => ?_) (fun a ha hn => hout a ha fun hin => hn (by
      unfold InR at hin ⊢; omega))
  rw [sunview_cell] at hx
  split at hx
  · rename_i hc
    obtain ⟨hkN, hlok, hkl, -⟩ := hc
    have hkb : (k - lo') * T.size + T.size ≤ len' * T.size := elem_bound hkl
    have hcell := hV.2 (k - lo') (by omega)
    have hx' : v.cells[k - lo'] = some x := by simpa [Slots.cell, vget, show k - lo' < N by omega] using hx
    rw [hx'] at hcell
    simp only [Slots.cellRepr, Shape.elemOffset] at hcell
    have e1 : slice V ((k - lo') * T.size) T.size =
        rd h' ((S.getD m.idx default).A + k * T.size) T.size := by
      rw [show slice V ((k - lo') * T.size) T.size =
          slice (slice V 0 (len' * T.size)) ((k - lo') * T.size) T.size by
        rw [slice_slice _ _ _ _ _ hkb, Nat.zero_add], hVm, ← rd_slice _ _ _ _ _ hkb]
      congr 1
      rw [show k * T.size = lo' * T.size + (k - lo') * T.size by rw [← Nat.add_mul]; congr 1; omega]
      omega
    rw [← e1]; exact hcell
  · rename_i hc
    have hkf : (env.get m : Slots T.carrier N).isFull k = true := by simp [Slots.isFull, hx]
    have hkb := slots_cell_bound hl henv m hkf
    have hkin : ¬ (lo' ≤ k ∧ k < lo' + len') := by
      rintro ⟨h1, h2⟩
      have hkN : k < N := by omega
      exact hc ⟨hkN, h1, by omega, by have := hfull (k - lo') (by omega); simpa [Slots.isFull] using this⟩
    have e : rd h' ((S.getD m.idx default).A + k * T.size) T.size =
        rd h ((S.getD m.idx default).A + k * T.size) T.size :=
      rd_congr fun i hi => hout _ (by omega)
        (fun hin => hkin (by
          unfold InR at hin
          constructor
          · rcases Nat.lt_or_ge k lo' with h1 | h1
            · have : (k + 1) * T.size ≤ lo' * T.size := Nat.mul_le_mul_right _ h1
              rw [Nat.succ_mul] at this; omega
            · exact h1
          · rcases Nat.lt_or_ge k (lo' + len') with h1 | h1
            · exact h1
            · have : (lo' + len') * T.size ≤ k * T.size := Nat.mul_le_mul_right _ h1
              rw [Nat.add_mul] at this; omega))
    rw [e]; exact slots_var_repr hl henv m hH hx

/-! ## The pair of cells `s[i], s[j]` -/

/-- The facts about the pair of cells `s[i], s[j]` of a `Slots` or view variable without a hole:
the cells are disjoint, inside the variable's storage and below the watermark, and they represent
their contents. -/
theorem pair2S_facts (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    [Inhabited T.carrier] (m : Mem (.slots T N) Γ) (i j : Atom Γ .u64)
    (hok : (Place.pair2S m i j).ok env) (hH : (S.getD m.idx default).hole = none) :
    let Ai := (S.getD m.idx default).A + (i.denote env).toNat * T.size
    let Aj := (S.getD m.idx default).A + (j.denote env).toNat * T.size
    Disj Ai T.size Aj T.size ∧ Ai + T.size ≤ bp + n ∧ Aj + T.size ≤ bp + n ∧
      (S.getD m.idx default).Holds (.slots T N) Ai T.size ∧
      (S.getD m.idx default).Holds (.slots T N) Aj T.size ∧
      Data.reprBytes ((Place.pair2S m i j).get env).1 (rd h Ai T.size) ∧
      Data.reprBytes ((Place.pair2S m i j).get env).2 (rd h Aj T.size) := by
  intro Ai Aj
  obtain ⟨hi, hj, hij⟩ := hok
  have hsn := slots_snd hl m
  have hbi := slots_cell_bound hl henv m hi
  have hbj := slots_cell_bound hl henv m hj
  have hdl := (hl.var m).dataLe hsn
  obtain ⟨x, hx⟩ : ∃ x, (env.get m : Slots T.carrier N).cell (i.denote env).toNat = some x :=
    Option.isSome_iff_exists.mp hi
  obtain ⟨y, hy⟩ : ∃ y, (env.get m : Slots T.carrier N).cell (j.denote env).toNat = some y :=
    Option.isSome_iff_exists.mp hj
  refine ⟨?_, by simp only [Ai]; omega, by simp only [Aj]; omega,
    by simp only [SI.Holds, hsn, Ai]; omega, by simp only [SI.Holds, hsn, Aj]; omega, ?_, ?_⟩
  · exact elem_disj_of_ne hij
  · show Data.reprBytes ((env.get m : Slots T.carrier N).cell _ |>.getD default) _
    rw [hx]; exact slots_var_repr hl henv m hH hx
  · show Data.reprBytes ((env.get m : Slots T.carrier N).cell _ |>.getD default) _
    rw [hy]; exact slots_var_repr hl henv m hH hy

/-- Writing the pair of cells back: bytes that represent the two components, written over the two
cells and nowhere else, represent the write-back. -/
theorem pair2S_set_rel (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S)
    (hbn : bp + n ≤ UInt64.size) {T : Ty} {N : Nat} [Inhabited T.carrier] (m : Mem (.slots T N) Γ)
    (i j : Atom Γ .u64) (hok : (Place.pair2S m i j).ok env) (hH : (S.getD m.idx default).hole = none)
    (hW : W.getD m.idx false = true) (h' : Heap) (v : (Ty.pair T T).carrier)
    (hout : ∀ a, a < bp + n →
      ¬ InR ((S.getD m.idx default).A + (i.denote env).toNat * T.size) T.size a →
      ¬ InR ((S.getD m.idx default).A + (j.denote env).toNat * T.size) T.size a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hv1 : Data.reprBytes v.1 (rd h' ((S.getD m.idx default).A + (i.denote env).toNat * T.size) T.size))
    (hv2 : Data.reprBytes v.2 (rd h' ((S.getD m.idx default).A + (j.denote env).toNat * T.size) T.size)) :
    MEnvRel h' bp ((Place.pair2S m i j).set env v) ρ S := by
  obtain ⟨hi, hj, hij⟩ := hok
  generalize hi' : (i.denote env).toNat = i' at *
  generalize hj' : (j.denote env).toNat = j' at *
  have hsn := slots_snd hl m
  have hbi := slots_cell_bound hl henv m hi
  have hbj := slots_cell_bound hl henv m hj
  have hdl := (hl.var m).dataLe hsn
  show MEnvRel h' bp (env.set m (((env.get m : Slots _ _).setCell (i.denote env).toNat (some v.1)).setCell
      (j.denote env).toNat (some v.2))) ρ S
  rw [hi', hj']
  refine slots_set_rel hl henv hbn m hW h' _ ?_ (fun k x hx => ?_) (fun a ha hn => hout a ha
      (fun hin => hn (by unfold InR at hin ⊢; omega))
      (fun hin => hn (by unfold InR at hin ⊢; omega)))
  · rw [Slots.occs_setCell_full _ _ _ (by rw [Slots.isFull_setCell]; split <;> simp_all),
      Slots.occs_setCell_full _ _ _ hi]
  · rw [Slots.cell_setCell, Slots.cell_setCell] at hx
    by_cases ekj : k = j' ∧ j' < N
    · simp only [ekj, and_self, ↓reduceIte, Option.some.injEq] at hx
      subst hx; rw [ekj.1]; exact hv2
    · simp only [ekj, ↓reduceIte] at hx
      by_cases eki : k = i' ∧ i' < N
      · simp only [eki, and_self, ↓reduceIte, Option.some.injEq] at hx
        subst hx; rw [eki.1]; exact hv1
      · simp only [eki, ↓reduceIte] at hx
        have hkf : (env.get m : Slots T.carrier N).isFull k = true := by simp [Slots.isFull, hx]
        have hkb := slots_cell_bound hl henv m hkf
        have hki : k ≠ i' := fun e => by subst e; exact eki ⟨rfl, Slots.lt_of_isFull hi⟩
        have hkj : k ≠ j' := fun e => by subst e; exact ekj ⟨rfl, Slots.lt_of_isFull hj⟩
        have e : rd h' ((S.getD m.idx default).A + k * T.size) T.size =
            rd h ((S.getD m.idx default).A + k * T.size) T.size :=
          rd_congr fun y hy => hout _ (by omega)
            (fun hin => elem_disj hki (sz := T.size) (x := k * T.size + y) (by omega) (by omega)
              (by unfold InR at hin; omega))
            (fun hin => elem_disj hkj (sz := T.size) (x := k * T.size + y) (by omega) (by omega)
              (by unfold InR at hin; omega))
        rw [e]; exact slots_var_repr hl henv m hH hx

/-- The pair of cells `s[i], s[j]` of a view variable as a two-element place. Its hole is the
variable's storage, and the hole's guarantee holds trivially because the path `[dyn]` overlaps
every place of the variable. -/
theorem pair2S_at (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    [Inhabited T.carrier] (m : Mem (.slots T N) Γ) (i j : Atom Γ .u64)
    (hok : (Place.pair2S m i j).ok env) (hnh : (Place.pair2S m i j).NH S) :
    PairAt (.pair2S m i j) ρ S W n bp env h
      ((S.getD m.idx default).A + (i.denote env).toNat * T.size)
      ((S.getD m.idx default).A + (j.denote env).toNat * T.size)
      ⟨(S.getD m.idx default).A, (S.getD m.idx default).sz (.slots T N), [.dyn]⟩ := by
  have hH := hole_none_of_dyn (p := Place.pair2S m i j) rfl hnh.2
  have hsn := slots_snd hl m
  obtain ⟨hd, hbi, hbj, hhi, hhj, hgi, hgj⟩ := pair2S_facts hl henv m i j hok hH
  refine ⟨fun κ ω L f hf hfe hnL hnU => pairAddr_runs hl T (.var m) i j f h hf henv hfe rfl trivial
      ((Place.var m).notPair_of_ty hl (slots_not_prod T N)) trivial hnh.1.1 hnh.1.2 hnL hnU,
    fun _ => rfl, hd, hbi, hbj, hhi, hhj, hgi, hgj, rfl,
    fun x hx => (SI.In_none hsn).2 hx, ?_, ?_,
    fun hW hbn m' v hm hv1 hv2 => pair2S_set_rel hl henv hbn m i j hok hH hW m' v hm hv1 hv2⟩
  · intro _ _ q _ _ _ _ _ hov
    rw [Sel.overlap_dyn_left] at hov; cases hov
  · simp only [SI.Holds, hsn] at hhi hhj
    show ∀ x, _ → InR (S.getD m.idx default).A ((S.getD m.idx default).sz (.slots T N)) x
    rintro x (hx | hx) <;> unfold InR at hx ⊢ <;> omega

end

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- `let x := { let r = &(s[i], s[j]); body }; k` for a view variable `s`. -/
theorem msound_borrowShr_pair2S {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty} [Inhabited T.carrier]
    (m : Mem (.slots T N) Γ) (i j : Atom Γ .u64) (body : Exp (Ty.pair T T :: Γ) u)
    (k : Exp (u :: Γ) v) (hVb : body.VSafe 0 .none = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr (.pair2S m i j) body k) :=
  msound_borrowShr_pairG _ body k rfl (fun _ => rfl) hVb
    (fun hl henv hok hnh _ _ => ⟨_, _, _, pair2S_at hl henv m i j hok hnh⟩) ihb ihk

/-- `let x := { let r = &mut (s[i], s[j]); body }; k` for a view variable `s`. The two cells are
updated in place, and when the borrow ends the memory represents the write-back. -/
theorem msound_borrowMut_pair2S {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty} [Inhabited T.carrier]
    (m : Mem (.slots T N) Γ) (i j : Atom Γ .u64)
    (body : Exp (Ty.pair T T :: Γ) (.pair u (Ty.pair T T))) (k : Exp (u :: Γ) v)
    (hCb : body.Conf (borrowTl u (Ty.pair T T)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.pair T T)) = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut (.pair2S m i j) body k) :=
  msound_borrowMut_pairG _ body k rfl (fun _ => rfl) hCb hVb
    (fun hl henv hok hnh _ _ => ⟨_, _, _, pair2S_at hl henv m i j hok hnh⟩) ihb ihk

end

end Millipede.Flat
