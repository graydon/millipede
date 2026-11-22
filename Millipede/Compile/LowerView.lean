import Millipede.Compile.LowerRef
import Millipede.Compile.HandBack

/-!
# Shared lemmas on slice views in memory

At the machine, a slice `q[lo..lo+len]` is the address of element `lo` and a length. The view
binder's value `vview arr lo len` is represented by the array's bytes from element `lo` on, and
writing a view back with `vunview` is represented by the elements in place. Scoped slice borrows
and slices passed as reference arguments both use these lemmas.
-/

namespace Millipede.Flat

/-! ## Paths -/

/-- A path that does not overlap `p ++ [dyn]` does not overlap `p`, since `dyn` overlaps every
selector. -/
theorem Sel.overlap_append_dyn : ∀ (p q : List Sel), Sel.overlap (p ++ [.dyn]) q = false →
    Sel.overlap p q = false
  | [], [], h => by simp [Sel.overlap] at h
  | [], _ :: q, h => by simp [Sel.overlap] at h
  | _ :: _, [], h => by simp [Sel.overlap] at h
  | .field a :: p, .field b :: q, h => by
    simp only [List.cons_append, Sel.overlap, Bool.and_eq_false_iff] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Sel.overlap_append_dyn p q h)
  | .field _ :: p, .dyn :: q, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn p q h
  | .dyn :: p, .field _ :: q, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn p q h
  | .dyn :: p, .dyn :: q, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn p q h

/-- `Sel.overlap_append_dyn` with the slice on the right. -/
theorem Sel.overlap_append_dyn_right : ∀ (q p : List Sel), Sel.overlap q (p ++ [.dyn]) = false →
    Sel.overlap q p = false
  | [], _, h => by simp [Sel.overlap] at h
  | _ :: _, [], h => by cases ‹Sel› <;> simp [Sel.overlap, Sel.overlap_nil_right] at h
  | .field a :: q, .field b :: p, h => by
    simp only [List.cons_append, Sel.overlap, Bool.and_eq_false_iff] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Sel.overlap_append_dyn_right q p h)
  | .field _ :: q, .dyn :: p, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn_right q p h
  | .dyn :: q, .field _ :: p, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn_right q p h
  | .dyn :: q, .dyn :: p, h => by
    simp only [List.cons_append, Sel.overlap] at h ⊢; exact Sel.overlap_append_dyn_right q p h

/-- The array place of a slice the borrow checker lets a term use is usable too. -/
theorem _root_.Millipede.Place.NH.range {Γ : List Ty} {T : Ty} {N : Nat} {S : List SI}
    {q : Place Γ (.arr T N)} {lo len : Atom Γ .u64} (h : (Place.range q lo len).NH S) : q.NH S :=
  ⟨h.1.1, fun H hH => Sel.overlap_append_dyn_right _ _ (h.2 H hH)⟩


/-! ## Representations -/

/-- A view is represented by the array's bytes from its first element on: cell `k < len` is element
`lo + k`, and the other cells are empty, whatever their bytes, including those beyond the array. -/
theorem vview_repr {T : Ty} {N lo len : Nat} (arr : Vector T.carrier N) {m : Heap} {Aq : Nat}
    (harr : Data.reprBytes (α := Vector T.carrier N) arr (rd m Aq (N * T.size)))
    (hfit : lo + len ≤ N) :
    Data.reprBytes (α := Slots T.carrier N) (vview arr lo len) (rd m (Aq + lo * T.size) (N * T.size)) := by
  refine ⟨rd_length _ _ _, fun k hk => ?_⟩
  show Slots.cellRepr (vview arr lo len).cells[k]
    (slice (rd m (Aq + lo * T.size) (N * T.size)) (k * T.size) T.size)
  have hc : (vview arr lo len).cells[k] = if k < len then arr.toList[lo + k]? else none := by
    simp [vview, Slots.cells]
  rw [hc]
  split
  · rename_i hkl
    have hj : lo + k < N := by omega
    have hkN : k * T.size + T.size ≤ N * T.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
    have hjN : (lo + k) * T.size + T.size ≤ N * T.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    rw [show arr.toList[lo + k]? = some arr[lo + k] by simp [hj]]
    show Data.reprBytes arr[lo + k] _
    rw [← rd_slice _ _ _ _ _ hkN, show Aq + lo * T.size + k * T.size = Aq + (lo + k) * T.size by
      rw [Nat.add_mul]; omega, rd_slice _ _ (N * T.size) _ _ hjN]
    have := harr.2 (lo + k) hj
    simpa [Shape.elemOffset] using this
  · trivial

/-- Writing a view back: memory whose viewed elements hold the bytes of the handed-back view, all of
whose cells `0 … len-1` are full, and whose other elements are the array's, represents
`vunview arr lo len s`. -/
theorem vunview_repr {T : Ty} {N lo len : Nat} (arr : Vector T.carrier N) (s : Slots T.carrier N)
    {h m : Heap} {Aq : Nat} (hfit : lo + len ≤ N)
    (harr : Data.reprBytes (α := Vector T.carrier N) arr (rd h Aq (N * T.size)))
    (hfull : ∀ k, k < len → s.isFull k = true) (V : List UInt8)
    (hV : Data.reprBytes (α := Slots T.carrier N) s V)
    (hVm : slice V 0 (len * T.size) = rd m (Aq + lo * T.size) (len * T.size))
    (hout : ∀ i, i < N * T.size → ¬ InR (lo * T.size) (len * T.size) i →
      m (UInt64.ofNat (Aq + i)) = h (UInt64.ofNat (Aq + i))) :
    Data.reprBytes (α := Vector T.carrier N) (vunview arr lo len s) (rd m Aq (N * T.size)) := by
  refine ⟨rd_length _ _ _, fun j hj => ?_⟩
  have hjN : j * T.size + T.size ≤ N * T.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  show Data.reprBytes (vunview arr lo len s)[j]
    (slice (rd m Aq (N * T.size)) ((Data.shape T.carrier).elemOffset j) (Data.shape T.carrier).size)
  simp only [Shape.elemOffset]
  rw [← rd_slice _ _ _ _ _ hjN]
  simp only [vunview, Vector.getElem_ofFn]
  split
  · rename_i hin
    obtain ⟨hlo, hlt⟩ := hin
    have hk := hfull (j - lo) hlt
    obtain ⟨x, hx⟩ : ∃ x, s.cell (j - lo) = some x := by
      simp only [Slots.isFull] at hk; exact Option.isSome_iff_exists.mp hk
    rw [hx]
    show Data.reprBytes x _
    have hkN : j - lo < N := by omega
    have hkb : (j - lo) * T.size + T.size ≤ len * T.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have hkb' : (j - lo) * T.size + T.size ≤ N * T.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hkN
    have hcell := hV.2 (j - lo) hkN
    have hx' : s.cells[j - lo] = some x := by
      simpa [Slots.cell, vget, hkN] using hx
    rw [hx'] at hcell
    simp only [Slots.cellRepr, Shape.elemOffset] at hcell
    have e1 : slice V ((j - lo) * T.size) T.size = rd m (Aq + j * T.size) T.size := by
      rw [show slice V ((j - lo) * T.size) T.size =
          slice (slice V 0 (len * T.size)) ((j - lo) * T.size) T.size by
        rw [slice_slice _ _ _ _ _ hkb, Nat.zero_add], hVm, ← rd_slice _ _ _ _ _ hkb]
      congr 1
      rw [show j * T.size = lo * T.size + (j - lo) * T.size by rw [← Nat.add_mul]; congr 1; omega]
      omega
    rw [← e1]; exact hcell
  · rename_i hnin
    have e : rd m (Aq + j * T.size) T.size = rd h (Aq + j * T.size) T.size := by
      refine rd_congr fun i hi => ?_
      rw [Nat.add_assoc]
      refine hout _ (by omega) fun ⟨h1, h2⟩ => ?_
      rcases Nat.lt_or_ge j lo with hjl | hjl
      · have : (j + 1) * T.size ≤ lo * T.size := Nat.mul_le_mul_right _ hjl
        rw [Nat.succ_mul] at this; omega
      · have hjl' : lo + len ≤ j := by
          rcases Nat.lt_or_ge (j - lo) len with h3 | h3
          · exact absurd ⟨hjl, h3⟩ hnin
          · omega
        have : (lo + len) * T.size ≤ j * T.size := Nat.mul_le_mul_right _ hjl'
        rw [Nat.add_mul] at this; omega
    rw [e, rd_slice _ _ _ _ _ hjN]
    have := harr.2 j hj
    simpa [Shape.elemOffset] using this

/-- The extent of a view of `len` elements. -/
theorem sz_view {A : Nat} {T : Ty} {N len : Nat} (hle : len ≤ N) :
    (SI.mk A none (some (len * T.size)) none).sz (Ty.slots T N) = len * T.size := by
  show min (len * T.size) (N * T.size) = len * T.size
  exact Nat.min_eq_left (Nat.mul_le_mul_right _ hle)

/-- The hole of a `&mut` slice `q[lo..lo+len]` of a variable is avoided by every place of the
variable whose path does not overlap the slice's. Here `s` is the variable's run-time knowledge, the
array's bytes are consecutive from `a`, and the hole is the viewed elements. -/
theorem holeOK_range {Γ : List Ty} {T : Ty} {N : Nat} (q : Place Γ (.arr T N)) (env : Env Γ)
    (s : SI) (a lo len : Nat) (hc : q.contig = true) (hL : q.Lawful) (hok : q.ok env)
    (hs : s.Ok q.rootTy) (hp : ∀ k, k < (Ty.arr T N).size → a + k = s.at (q.off env + k))
    (hfit : lo + len ≤ N) :
    HoleOK s q.rootTy ⟨a + lo * T.size, len * T.size, q.path ++ [.dyn]⟩ := by
  intro Γ' t' q' env' hT hc' hL' hok' hov k hk hin
  have := holeOK_of_place q env s a hc hL hok hs hp q' env' hT hc' hL' hok'
    (Sel.overlap_append_dyn _ _ hov) k hk
  have hb : (lo + len) * T.size ≤ N * T.size := Nat.mul_le_mul_right _ hfit
  have hsz : (Ty.arr T N).size = N * T.size := rfl
  rw [Nat.add_mul] at hb
  simp only [hsz, InR] at this hin
  omega

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- Storing the word in slot `x` into the slot at `bp + m`. -/
theorem store_word {m bp : Nat} {f : Frame} {h : Heap} (x : Nat) (v : UInt64)
    (hf : f BP = UInt64.ofNat bp) (hx : f x = v) (hL : bp + m + 8 ≤ L)
    (hU : bp + m + 8 ≤ UInt64.size) :
    Runs κ ω L (.store .w64 (.slot BP) (UInt64.ofNat m) (.slot x)) f h f
      (wr h (bp + m) (natBytes 8 v.toNat)) :=
  Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (b := 8) hL (by omega) hf)) rfl (by
    simp only [eval_slot, hf, hx, ofNat_add_ofNat]; rw [store64_eq])

/-- The cells of a fresh view are full exactly below its length. -/
theorem vview_cells {α : Type} {N : Nat} (arr : Vector α N) (lo len : Nat) (hfit : lo + len ≤ N) :
    ∀ k (hk : k < N), ((vview arr lo len : Slots α N).cells[k]).isSome = decide (k < len) := by
  intro k hk
  have := vview_full_iff arr lo len k hfit
  simp only [Slots.isFull, Slots.cell, vget, hk, ↓reduceDIte] at this
  cases hc : ((vview arr lo len : Slots α N).cells[k]).isSome with
  | true => exact (decide_eq_true (this.mp hc)).symm
  | false =>
    refine (decide_eq_false fun hkl => ?_).symm
    have := this.mpr hkl; simp_all

end

end Millipede.Flat
