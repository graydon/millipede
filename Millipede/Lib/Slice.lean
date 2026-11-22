import Millipede.Lib.Pool
import Std.Tactic.Do
import Std.WP

/-!
# Slice helpers that fill, copy and reverse in place

When a loop body assigns the cells of a `&mut` slice parameter, the elaborator makes the loop
carry the view and the compiler updates the cells in place, so nothing is copied. This module
provides the common uses `Slice.fill s v`, `Slice.copy dst src` and `Slice.reverse s` on slices
`&mut [T; n]`, each one definition for every element type `T` and bound `n < 2 ^ 64`. A caller
writes `Slice.reverse (&mut b.bytes[0..n])`, and the element type, the bound and `n < 2 ^ 64` are
inferred at the call.

Every loop is `for i in 0...s.len do …`, so `mp def` discharges the obligations, which are that
`s[i]` is accessed under `i < s.len` and that the cells of a view below its length are full and
stay full. The contracts describe cell `k < n` of the result.
- After `fill`, a cell below the length is `some v`, and a cell above it is unchanged.
- After `copy`, a cell below both lengths holds the cell of `src`, and a cell above is unchanged.
- After `reverse`, cell `k` below the length holds cell `len-1-k` of the argument, and a cell
  above is unchanged.

The cell arithmetic is proved once in `FillInv`, `CopyInv`, `RevInv` and their step lemmas, and
so is each contract. Slices are described in doc/design/memory.md.
-/

namespace Millipede.Lib

open Millipede Std.WP

set_option experimental.vcgen true

/-! ## The functions, for every element type and bound -/

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
include hn
set_option mp.autoSpec false

/-- Fill a slice with `v`. -/
mp def Slice.fill (s : &mut [T; n]) (v : T)
    ensures ∀ k < n, s'.cell k = if k < s.len.toNat then some v else s.cell k : Unit := do
  for i in 0...s.len do
    s[i] := v

/-- Copy `src` into `dst`, as many cells as both have. -/
mp def Slice.copy (dst : &mut [T; n]) (src : &[T; n])
    ensures ∀ k < n, dst'.cell k =
      if k < dst.len.toNat ∧ k < src.len.toNat then src.cell k else dst.cell k : Unit := do
  for i in 0...dst.len do
    if i ≥ src.len then break
    dst[i] := src[i]!

/-- Reverse a slice in place, swapping cell `i` with cell `len-1-i` for `i < len / 2`. -/
mp def Slice.reverse (s : &mut [T; n])
    ensures ∀ k < n, s'.cell k =
      if k < s.len.toNat then s.cell (s.len.toNat - 1 - k) else s.cell k : Unit := do
  for i in 0...s.len do
    if i ≥ s.len / 2 then break
    let j := s.len -! 1 -! i
    let a := s[i]
    let b := s[j]!
    s[i] := b
    s[j]! := a

end

/-! ## Cell arithmetic, once for every element type and bound -/

namespace Slice

variable {α : Type} {n : Nat}

/-- The loop counter as a word, where `ofNat d < x ↔ d < x.toNat` for `d < 2^64`. -/
theorem ofNat_lt_iff {d : Nat} (x : UInt64) (hd : d < 2 ^ 64) :
    UInt64.ofNat d < x ↔ d < x.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hd]

/-- The mirror index `len - 1 - d` as a word, for `d < len / 2`. -/
theorem toNat_mirror {len : UInt64} {d : Nat} (hd : d < len.toNat / 2) :
    (len - 1 - UInt64.ofNat d).toNat = len.toNat - 1 - d := by
  have : len.toNat < 2 ^ 64 := len.toNat_lt
  have h1 : (UInt64.ofNat d).toNat = d := UInt64.toNat_ofNat_of_lt' (show d < 2 ^ 64 by omega)
  rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, h1, UInt64.toNat_one]
  · rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; omega
  · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, h1, UInt64.toNat_one]
    · omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; omega

/-- The loop condition of `reverse`, in which `i < len ∧ i < len / 2` is `i < len / 2`. -/
theorem half_iff {d : Nat} (len : UInt64) (hd : d < 2 ^ 64) :
    (UInt64.ofNat d < len ∧ UInt64.ofNat d < len / 2) ↔ d < len.toNat / 2 := by
  rw [ofNat_lt_iff _ hd, ofNat_lt_iff _ hd, UInt64.toNat_div]
  simp only [UInt64.reduceToNat]; omega

/-- A full cell is `some` of its content. -/
theorem some_getD_of_full {s : Slots α n} {k : Nat} {d : α} (h : s.isFull k = true) :
    some ((s.cell k).getD d) = s.cell k := by
  simp only [Slots.isFull] at h
  cases hc : s.cell k <;> simp_all

/-! ### `fill` -/

/-- The state after `d` iterations of `fill`, in which the cells below `min d len` hold `v` and the
others are those of `s`. -/
def FillInv (s st : Slots α n) (len : Nat) (v : α) (d : Nat) : Prop :=
  ∀ k < n, st.cell k = if k < min d len then some v else s.cell k

theorem FillInv.init (s : Slots α n) (len : Nat) (v : α) : FillInv s s len v 0 := by
  intro k _; simp

theorem FillInv.step {s st : Slots α n} {len : Nat} {v : α} {d : Nat} (h : FillInv s st len v d)
    (hd : d < len) : FillInv s (st.setCell d (some v)) len v (d + 1) := by
  intro k hk
  rw [Slots.cell_setCell, h k hk]
  grind

theorem FillInv.stop {s st : Slots α n} {len : Nat} {v : α} {d m : Nat} (h : FillInv s st len v d)
    (hd : len ≤ d) (hm : d ≤ m) : FillInv s st len v m := by
  intro k hk
  rw [h k hk]
  by_cases h2 : k < min d len <;> by_cases h3 : k < min m len <;> simp [h2, h3] <;> omega

theorem FillInv.post {s st : Slots α n} {len : Nat} {v : α} (h : FillInv s st len v n) :
    ∀ k < n, st.cell k = if k < len then some v else s.cell k := by
  intro k hk; rw [h k hk]
  by_cases h2 : k < len <;> simp [h2] <;> omega

/-! ### `copy` -/

/-- The state after `d` iterations of `copy`, in which the cells below `min d (min dl sl)` hold
those of `src`. -/
def CopyInv [Inhabited α] (dst src st : Slots α n) (dl sl : Nat) (d : Nat) : Prop :=
  ∀ k < n, st.cell k =
    if k < min d (min dl sl) then some ((src.cell k).getD default) else dst.cell k

theorem CopyInv.init [Inhabited α] (dst src : Slots α n) (dl sl : Nat) :
    CopyInv dst src dst dl sl 0 := by
  intro k _; simp

theorem CopyInv.step [Inhabited α] {dst src st : Slots α n} {dl sl d : Nat}
    (h : CopyInv dst src st dl sl d) (h1 : d < dl) (h2 : d < sl) :
    CopyInv dst src (st.setCell d (some ((src.cell d).getD default))) dl sl (d + 1) := by
  intro k hk
  rw [Slots.cell_setCell, h k hk]
  by_cases e : k = d
  · subst e; simp [hk]; omega
  · by_cases h3 : k < min d (min dl sl) <;> simp [e, h3] <;> omega

theorem CopyInv.stop [Inhabited α] {dst src st : Slots α n} {dl sl d m : Nat}
    (h : CopyInv dst src st dl sl d) (hd : dl ≤ d ∨ sl ≤ d) (hm : d ≤ m) : CopyInv dst src st dl sl m := by
  intro k hk
  rw [h k hk]
  by_cases h2 : k < min d (min dl sl) <;> by_cases h3 : k < min m (min dl sl) <;>
    simp [h2, h3] <;> omega

theorem CopyInv.post [Inhabited α] {dst src st : Slots α n} {dl sl : Nat}
    (h : CopyInv dst src st dl sl n) (hf : ∀ k < sl, src.isFull k = true) :
    ∀ k < n, st.cell k = if k < dl ∧ k < sl then src.cell k else dst.cell k := by
  intro k hk; rw [h k hk]
  by_cases h2 : k < dl ∧ k < sl
  · simp [h2, some_getD_of_full (hf k h2.2)]; omega
  · simp [h2]; omega

/-! ### `reverse` -/

/-- The state after `d` iterations of `reverse`, when `e = min d (len / 2)` swaps are done. The
first `e` and the last `e` cells below `len` hold their mirror image's content, and the others are
those of `s`. -/
def RevInv [Inhabited α] (s st : Slots α n) (len : Nat) (d : Nat) : Prop :=
  ∀ k < n, st.cell k =
    if k < min d (len / 2) ∨ (len - min d (len / 2) ≤ k ∧ k < len)
    then some ((s.cell (len - 1 - k)).getD default) else s.cell k

theorem RevInv.init [Inhabited α] (s : Slots α n) (len : Nat) : RevInv s s len 0 := by
  intro k _; simp; omega

theorem RevInv.step [Inhabited α] {s st : Slots α n} {len d : Nat} (h : RevInv s st len d)
    (hd : d < len / 2) (hl : len ≤ n) :
    RevInv s ((st.setCell d (some ((st.cell (len - 1 - d)).getD default))).setCell (len - 1 - d)
      (some ((st.cell d).getD default))) len (d + 1) := by
  have hm : min d (len / 2) = d := by omega
  have hm' : min (d + 1) (len / 2) = d + 1 := by omega
  have hj := h (len - 1 - d) (by omega)
  have hi := h d (by omega)
  rw [hm] at hj hi
  rw [ite_eq_right (by omega)] at hj hi
  intro k hk
  rw [Slots.cell_setCell, Slots.cell_setCell, h k hk, hm, hm', hj, hi]
  by_cases e1 : k = len - 1 - d
  · simp only [e1, show len - 1 - d < n by omega, and_self, ite_true]
    rw [ite_eq_left (Or.inr ⟨by omega, by omega⟩), show len - 1 - (len - 1 - d) = d by omega]
  · by_cases e2 : k = d
    · subst e2; simp [e1, hk]
    · simp only [e1, e2, false_and, ite_false]
      by_cases c : k < d ∨ len - d ≤ k ∧ k < len
      · rw [ite_eq_left c, ite_eq_left (by omega)]
      · rw [ite_eq_right c, ite_eq_right (by omega)]

theorem RevInv.stop [Inhabited α] {s st : Slots α n} {len d m : Nat} (h : RevInv s st len d)
    (hd : len / 2 ≤ d) (hm : len / 2 ≤ m) : RevInv s st len m := by
  intro k hk
  rw [h k hk, Nat.min_eq_right hd, Nat.min_eq_right hm]

/-- The result of `reverse` when every cell below the length is full, which is the mirror
image. -/
theorem RevInv.full [Inhabited α] {s st : Slots α n} {len : Nat} (h : RevInv s st len n)
    (hl : len ≤ n) (hf : ∀ k < len, s.isFull k = true) :
    ∀ k < n, st.cell k = if k < len then s.cell (len - 1 - k) else s.cell k := by
  intro k hk
  rw [h k hk, Nat.min_eq_right (by omega)]
  have hs : ∀ j < len, some ((s.cell j).getD default) = s.cell j := fun j hj => some_getD_of_full (hf j hj)
  by_cases c : k < len / 2 ∨ len - len / 2 ≤ k ∧ k < len
  · rw [ite_eq_left c, ite_eq_left (by omega), hs _ (by omega)]
  · rw [ite_eq_right c]
    by_cases hkl : k < len
    · rw [ite_eq_left hkl, show len - 1 - k = k by omega]
    · rw [ite_eq_right hkl]

/-! ### The verification conditions of the instances' loops

For a loop over `List.range m`, here with `m = n`, `vcgen` leaves a step goal per iteration in the
shape `pref ++ cur :: suff`, with `cur` the counter, for the body that continues, and one goal for
the exit. These lemmas take the goals in that shape, so each instance's proof is one line per
goal. -/

variable {m cur : Nat} {pref suff : List Nat}

theorem FillInv.yield {s st : Slots α n} {len : UInt64} {v : α} (hm : m < 2 ^ 64)
    (hr : List.range m = pref ++ cur :: suff) (ih : FillInv s st len.toNat v pref.length)
    (hc : UInt64.ofNat cur < len) :
    FillInv s (st.setCell (UInt64.ofNat cur).toNat (some v)) len.toNat v (pref ++ [cur]).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  rw [ofNat_lt_iff _ (by omega)] at hc
  simpa [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)] using ih.step hc

theorem FillInv.brk {s st : Slots α n} {len : UInt64} {v : α} (hm : m < 2 ^ 64)
    (hr : List.range m = pref ++ cur :: suff) (ih : FillInv s st len.toNat v pref.length)
    (hc : ¬UInt64.ofNat cur < len) : FillInv s st len.toNat v (List.range m).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  rw [ofNat_lt_iff _ (by omega)] at hc
  exact ih.stop (by omega) (by simp; omega)

theorem CopyInv.yield [Inhabited α] {dst src st : Slots α n} {dl sl : UInt64} (hm : m < 2 ^ 64)
    (hr : List.range m = pref ++ cur :: suff) (ih : CopyInv dst src st dl.toNat sl.toNat pref.length)
    (hc : UInt64.ofNat cur < dl ∧ UInt64.ofNat cur < sl) :
    CopyInv dst src (st.setCell (UInt64.ofNat cur).toNat
      (some ((src.cell (UInt64.ofNat cur).toNat).getD default))) dl.toNat sl.toNat
      (pref ++ [cur]).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  rw [ofNat_lt_iff _ (by omega), ofNat_lt_iff _ (by omega)] at hc
  simpa [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)] using ih.step hc.1 hc.2

theorem CopyInv.brk [Inhabited α] {dst src st : Slots α n} {dl sl : UInt64} (hm : m < 2 ^ 64)
    (hr : List.range m = pref ++ cur :: suff) (ih : CopyInv dst src st dl.toNat sl.toNat pref.length)
    (hc : ¬(UInt64.ofNat cur < dl ∧ UInt64.ofNat cur < sl)) :
    CopyInv dst src st dl.toNat sl.toNat (List.range m).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  rw [ofNat_lt_iff _ (by omega), ofNat_lt_iff _ (by omega)] at hc
  exact ih.stop (by omega) (by simp; omega)

theorem RevInv.yield [Inhabited α] {s st : Slots α n} {len : UInt64} (hm : m < 2 ^ 64)
    (hl : len.toNat ≤ n) (hr : List.range m = pref ++ cur :: suff)
    (ih : RevInv s st len.toNat pref.length)
    (hc : UInt64.ofNat cur < len ∧ UInt64.ofNat cur < len / 2) :
    RevInv s ((st.setCell (UInt64.ofNat cur).toNat
        (some ((st.cell (len - 1 - UInt64.ofNat cur).toNat).getD default))).setCell
      (len - 1 - UInt64.ofNat cur).toNat (some ((st.cell (UInt64.ofNat cur).toNat).getD default)))
      len.toNat (pref ++ [cur]).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  have hd := (half_iff len (by omega)).mp hc
  simpa [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), toNat_mirror hd] using ih.step hd hl

theorem RevInv.brk [Inhabited α] {s st : Slots α n} {len : UInt64} (hm : m < 2 ^ 64)
    (hr : List.range m = pref ++ cur :: suff)
    (ih : RevInv s st len.toNat pref.length)
    (hc : ¬(UInt64.ofNat cur < len ∧ UInt64.ofNat cur < len / 2)) :
    RevInv s st len.toNat (List.range m).length := by
  obtain ⟨rfl, hlt⟩ := range_split hr
  have hd : len.toNat / 2 ≤ pref.length :=
    Nat.not_lt.mp fun h => hc ((half_iff len (by omega)).mpr h)
  exact ih.stop hd (by simp; omega)

end Slice

/-! ## The contracts, proved once -/

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
include hn

mp prove Slice.fill.spec := by
  intro s sl v
  vcgen [Slice.fill] invariants
  · fun done _ st => Slice.FillInv s st.2.1 sl.toNat v done.length
  case vc1 => exact Slice.FillInv.init s _ v
  case vc2 _ _ _ ih k hk => exact Slice.FillInv.post (by simpa using ih) k hk
  case vc3 _ _ _ hr _ _ _ ih hc => exact Slice.FillInv.yield hn hr ih hc
  case vc4 _ _ _ hr _ _ _ ih hc => exact Slice.FillInv.brk hn hr ih hc

mp prove Slice.copy.spec := by
  intro dst dl src sl
  vcgen [Slice.copy] invariants
  · fun done _ st => Slice.CopyInv dst src st.2.1 dl.toNat sl.toNat done.length
  case vc1 => exact Slice.CopyInv.init dst src _ _
  case vc2 hp _ _ _ ih k hk => exact Slice.CopyInv.post (by simpa using ih) hp.2.2 k hk
  case vc3 _ _ _ hr _ _ _ ih hc => exact Slice.CopyInv.yield hn hr ih hc
  case vc4 _ _ _ hr _ _ _ ih hc => exact Slice.CopyInv.brk hn hr ih hc

mp prove Slice.reverse.spec := by
  intro s sl
  vcgen [Slice.reverse] invariants
  · fun done _ st => Slice.RevInv s st.2.1 sl.toNat done.length
  case vc1 => exact Slice.RevInv.init s _
  case vc2 hp _ _ _ ih k hk => exact Slice.RevInv.full (by simpa using ih) hp.1 hp.2 k hk
  case vc3 _ _ _ hr _ _ _ ih hc => exact Slice.RevInv.yield hn ‹sl.toNat ≤ n ∧ _›.1 hr ih hc
  case vc4 _ _ _ hr _ _ _ ih hc => exact Slice.RevInv.brk hn hr ih hc

end

end Millipede.Lib
