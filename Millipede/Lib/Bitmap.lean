import Millipede.Core.Place

/-!
# Occupancy bitmaps

This module holds the Lean facts behind the pool arena of `Millipede/Lib/Pool.lean`. A bitmap is
a `Vector UInt64 W` in which bit `i` is bit `i % 64` of word `i / 64`. The arena code tests, sets
and clears bits with the word operations `>>>`, `<<<`, `&&&`, `|||` and `~~~`, whose shift
amounts are taken modulo 64. This module relates those expressions, exactly as they appear in the
normal forms of the `mp def`s, to `bmBit`, and proves the counting lemmas about `cnt`, the number
of set bits below `n`, that make `live` equal to the population count.

It also states the generic pool invariant `PoolInv slots bits live`, which says that for every
`i < n` bit `i` is set exactly when cell `i` is full and that `live` is the number of set bits. It
proves that the invariant is kept by the three state changes a pool makes, which are filling a
vacant cell and setting its bit, emptying a full cell and clearing its bit, and writing a full
cell. These proofs do not depend on the element type, the capacity or the struct that holds the
three fields, and every concrete pool proves its contracts from them.
-/

namespace Millipede.Lib

/-! ## Bits of a word -/

/-- Bit `k` of a word. -/
def bitw (w : UInt64) (k : Nat) : Bool := w.toBitVec.getLsbD k

theorem bitw_eq_testBit (w : UInt64) (k : Nat) : bitw w k = w.toNat.testBit k := by
  simp only [bitw, BitVec.getLsbD]; rfl

/-- The bit test the arena code performs, where `(w >>> x) &&& 1 == 0` holds exactly when bit
`x % 64` is clear. -/
theorem test_eq_zero_iff (w x : UInt64) :
    (w >>> x &&& 1 = 0) ↔ bitw w (x.toNat % 64) = false := by
  rw [bitw_eq_testBit, ← UInt64.toNat_inj]
  simp [UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.testBit, Nat.and_one_is_mod]

theorem bitw_set (w x : UInt64) (k : Nat) (hk : k < 64) :
    bitw (w ||| 1 <<< x) k = (bitw w k || k == x.toNat % 64) := by
  simp only [bitw]; simp [hk]
  by_cases h : k = x.toNat % 64
  · simp [h]
  · by_cases h1 : k < x.toNat % 64
    · simp [h, h1]
    · have : k - x.toNat % 64 ≠ 0 := by omega
      simp [h, h1, this]

theorem bitw_clr (w x : UInt64) (k : Nat) (hk : k < 64) :
    bitw (w &&& ~~~(1 <<< x)) k = (bitw w k && k != x.toNat % 64) := by
  simp only [bitw]; simp [hk]
  by_cases h : k = x.toNat % 64
  · simp [h]
  · by_cases h1 : k < x.toNat % 64
    · simp [h, h1]
    · have : k - x.toNat % 64 ≠ 0 := by omega
      simp [h, h1, this]

@[simp] theorem bitw_zero (k : Nat) : bitw 0 k = false := by
  simp [bitw]

/-! ## Bitmaps -/

/-- Bit `i` of a bitmap, which is bit `i % 64` of word `i / 64`. A word out of range reads `0`. -/
def bmBit {W : Nat} (bits : Vector UInt64 W) (i : Nat) : Bool := bitw (vget bits (i / 64) 0) (i % 64)

theorem shr6_toNat (x : UInt64) : (x >>> 6).toNat = x.toNat / 64 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

@[simp] theorem default_uint64 : (default : UInt64) = 0 := rfl

/-- The bitmap test of the arena code. -/
theorem bm_test_iff {W : Nat} (bits : Vector UInt64 W) (x : UInt64) :
    (vget bits (x >>> 6).toNat default >>> x &&& 1 = 0) ↔ bmBit bits x.toNat = false := by
  rw [test_eq_zero_iff, shr6_toNat]; rfl

/-- The bitmap test in the form that `mp_safe` leaves it. -/
theorem bm_test_iff' {W : Nat} (bits : Vector UInt64 W) (x : UInt64) :
    (vget bits (x.toNat / 64) 0 >>> x &&& 1 = 0) ↔ bmBit bits x.toNat = false := by
  rw [test_eq_zero_iff]; rfl

/-- Setting bit `x`, as the arena code updates the bitmap. -/
def bmSet {W : Nat} (bits : Vector UInt64 W) (x : UInt64) : Vector UInt64 W :=
  vset bits (x >>> 6).toNat (vget bits (x >>> 6).toNat default ||| 1 <<< x)

/-- Clearing bit `x`, as the arena code updates the bitmap. -/
def bmClr {W : Nat} (bits : Vector UInt64 W) (x : UInt64) : Vector UInt64 W :=
  vset bits (x >>> 6).toNat (vget bits (x >>> 6).toNat default &&& ~~~(1 <<< x))

theorem bmBit_set {W : Nat} (bits : Vector UInt64 W) (x : UInt64) (j : Nat)
    (hx : x.toNat / 64 < W) : bmBit (bmSet bits x) j = (bmBit bits j || j == x.toNat) := by
  simp only [bmBit, bmSet, shr6_toNat, default_uint64]
  by_cases hw : j / 64 = x.toNat / 64
  · rw [hw, vget_vset_same _ _ _ _ hx, bitw_set _ _ _ (Nat.mod_lt _ (by decide))]
    congr 1
    apply Bool.eq_iff_iff.mpr; simp; omega
  · rw [vget_vset_ne _ _ _ _ _ (Ne.symm hw)]
    have : j ≠ x.toNat := fun h => hw (h ▸ rfl)
    simp [this]

theorem bmBit_clr {W : Nat} (bits : Vector UInt64 W) (x : UInt64) (j : Nat)
    (hx : x.toNat / 64 < W) : bmBit (bmClr bits x) j = (bmBit bits j && j != x.toNat) := by
  simp only [bmBit, bmClr, shr6_toNat, default_uint64]
  by_cases hw : j / 64 = x.toNat / 64
  · rw [hw, vget_vset_same _ _ _ _ hx, bitw_clr _ _ _ (Nat.mod_lt _ (by decide))]
    congr 1
    apply Bool.eq_iff_iff.mpr; simp; omega
  · rw [vget_vset_ne _ _ _ _ _ (Ne.symm hw)]
    have : j ≠ x.toNat := fun h => hw (h ▸ rfl)
    simp [this]

@[simp] theorem bmBit_zero {W : Nat} (j : Nat) : bmBit (Vector.replicate W (0 : UInt64)) j = false := by
  simp only [bmBit, vget]
  split <;> simp

/-! ## Counting set bits -/

/-- The number of `i < n` with `f i`, which for a bitmap is its population count below `n`. -/
def cnt (n : Nat) (f : Nat → Bool) : Nat := (List.range n).countP f

theorem cnt_le (n : Nat) (f : Nat → Bool) : cnt n f ≤ n := by
  simpa [cnt] using List.countP_le_length (l := List.range n) (p := f)

theorem cnt_succ (n : Nat) (f : Nat → Bool) :
    cnt (n + 1) f = cnt n f + (if f n then 1 else 0) := by
  simp [cnt, List.range_succ, List.countP_append]

theorem cnt_congr (n : Nat) (f g : Nat → Bool) (h : ∀ i < n, f i = g i) : cnt n f = cnt n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Turning one bit on below `n` adds one. -/
theorem cnt_flip_on (n r : Nat) (f g : Nat → Bool) (hr : r < n) (hf : f r = false)
    (hg : g r = true) (h : ∀ i < n, i ≠ r → g i = f i) : cnt n g = cnt n f + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cnt_succ, cnt_succ]
    by_cases hn : r = n
    · subst hn
      rw [cnt_congr r g f (fun i hi => h i (by omega) (by omega))]
      simp [hf, hg]
    · rw [ih (by omega) (fun i hi hne => h i (by omega) hne), h n (by omega) (Ne.symm hn)]
      omega

/-- Turning one bit off below `n` removes one. -/
theorem cnt_flip_off (n r : Nat) (f g : Nat → Bool) (hr : r < n) (hf : f r = true)
    (hg : g r = false) (h : ∀ i < n, i ≠ r → g i = f i) : cnt n g + 1 = cnt n f :=
  (cnt_flip_on n r g f hr hg hf (fun i hi hne => (h i hi hne).symm)).symm

/-- With all bits below `n` set, the count is `n`. -/
theorem cnt_all (n : Nat) (f : Nat → Bool) (h : ∀ i < n, f i = true) : cnt n f = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]; rfl

@[simp] theorem Slots.cell_empty {α : Type} (n i : Nat) : (Slots.empty n : Slots α n).cell i = none := by
  simp only [Slots.cell, Slots.empty, Slots.cells, vget]
  split <;> simp

/-! ## The generic pool invariant -/

/-- The pool invariant. For every cell `i < n`, bit `i` of the bitmap is set exactly when the cell
is full, and `live` is the number of set bits below `n`, so `live` is the number of full cells
and `live ≤ n`. -/
structure PoolInv {T : Type} {n W : Nat} (slots : Slots T n) (bits : Vector UInt64 W)
    (live : UInt64) : Prop where
  bit_iff : ∀ i < n, bmBit bits i = (slots.cell i).isSome
  live_eq : live.toNat = cnt n (bmBit bits)

namespace PoolInv
variable {T : Type} {n W : Nat} {slots : Slots T n} {bits : Vector UInt64 W} {live : UInt64}

theorem empty : PoolInv (Slots.empty n : Slots T n) (Vector.replicate W 0) 0 where
  bit_iff i _ := by simp
  live_eq := by
    simp only [UInt64.toNat_zero]
    rw [cnt_congr n _ (fun _ => false) (fun i _ => by simp)]
    simp [cnt]

/-- A clear bit below `n` is a vacant cell. -/
theorem vacant_of_clear (h : PoolInv slots bits live) (i : Nat) (hi : i < n)
    (hb : bmBit bits i = false) : slots.isVacant i = true := by
  have := h.bit_iff i hi
  rw [hb] at this
  unfold Slots.isVacant
  cases hc : slots.cell i
  · simp [hi]
  · rw [hc] at this; simp at this

/-- A full cell has its bit set. -/
theorem set_of_full (h : PoolInv slots bits live) (i : Nat) (hf : slots.isFull i = true) :
    bmBit bits i = true := by
  rw [h.bit_iff i (Slots.lt_of_isFull hf)]; exact hf

/-- A full cell is live, so the count is positive and `live - 1` does not wrap. -/
theorem live_pos (h : PoolInv slots bits live) (i : Nat) (hf : slots.isFull i = true) :
    1 ≤ live.toNat := by
  have := cnt_flip_off n i (bmBit bits) (fun j => bmBit bits j && j != i) (Slots.lt_of_isFull hf)
    (h.set_of_full i hf) (by simp) (fun j _ hne => by simp [hne])
  rw [h.live_eq]; omega

/-- A set bit below `n` is a full cell. -/
theorem full_of_set (h : PoolInv slots bits live) (i : Nat) (hi : i < n)
    (hb : bmBit bits i = true) : slots.isFull i = true := by
  rw [h.bit_iff i hi] at hb; exact hb

/-- A clear bit below `n` leaves room, since the count is below `n`. -/
theorem _root_.Millipede.Lib.cnt_lt_of_clear (n r : Nat) (f : Nat → Bool) (hr : r < n)
    (hf : f r = false) : cnt n f < n := by
  have := cnt_flip_on n r f (fun i => f i || i == r) hr hf (by simp)
    (fun i _ hne => by simp [hne])
  have := cnt_le n (fun i => f i || i == r)
  omega

/-- A clear bit below `n` leaves room, since fewer than `n` cells are live. -/
theorem live_lt (h : PoolInv slots bits live) (x : Nat) (hx : x < n) (hb : bmBit bits x = false) :
    live.toNat < n := h.live_eq ▸ cnt_lt_of_clear n x _ hx hb

/-- With a clear bit below `n < 2^64`, `live + 1` does not wrap. -/
theorem live_succ (h : PoolInv slots bits live) (x : Nat) (hx : x < n) (hb : bmBit bits x = false)
    (hn : n < 2 ^ 64) : (live + 1).toNat = live.toNat + 1 := by
  have := h.live_lt x hx hb
  rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Filling the vacant cell `x` and setting its bit adds one live cell. -/
theorem put (h : PoolInv slots bits live) (x : UInt64) (v : T) (hx : x.toNat < n)
    (hW : n ≤ 64 * W) (hb : bmBit bits x.toNat = false) (hn : n < 2 ^ 64) :
    PoolInv (slots.setCell x.toNat (some v)) (bmSet bits x) (live + 1) where
  bit_iff i hi := by
    rw [bmBit_set _ _ _ (by omega)]
    by_cases hix : i = x.toNat
    · subst hix; simp [Slots.cell_setCell_same _ _ _ hx]
    · rw [Slots.cell_setCell_ne _ _ _ _ (Ne.symm hix), h.bit_iff i hi]; simp [hix]
  live_eq := by
    have hc := cnt_flip_on n x.toNat (bmBit bits) (bmBit (bmSet bits x)) hx hb
      (by rw [bmBit_set _ _ _ (by omega)]; simp)
      (fun i _ hne => by rw [bmBit_set _ _ _ (by omega)]; simp [hne])
    have hle := cnt_le n (bmBit (bmSet bits x))
    have hl := h.live_eq
    rw [hc, ← h.live_eq, UInt64.toNat_add]
    simp only [UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- Emptying the full cell `x` and clearing its bit removes one live cell. -/
theorem take (h : PoolInv slots bits live) (x : UInt64) (hW : n ≤ 64 * W)
    (hf : slots.isFull x.toNat = true) :
    PoolInv (slots.setCell x.toNat none) (bmClr bits x) (live - 1) where
  bit_iff i hi := by
    have hx := Slots.lt_of_isFull hf
    rw [bmBit_clr _ _ _ (by omega)]
    by_cases hix : i = x.toNat
    · subst hix; simp [Slots.cell_setCell_same _ _ _ hx]
    · rw [Slots.cell_setCell_ne _ _ _ _ (Ne.symm hix), h.bit_iff i hi]; simp [hix]
  live_eq := by
    have hx := Slots.lt_of_isFull hf
    have hc := cnt_flip_off n x.toNat (bmBit bits) (bmBit (bmClr bits x)) hx
      (h.set_of_full _ hf)
      (by rw [bmBit_clr _ _ _ (by omega)]; simp)
      (fun i _ hne => by rw [bmBit_clr _ _ _ (by omega)]; simp [hne])
    have hpos : 1 ≤ live.toNat := by rw [h.live_eq]; omega
    rw [UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using hpos), h.live_eq]
    simp only [UInt64.toNat_one]
    omega

/-- Writing a full cell keeps the invariant. -/
theorem write (h : PoolInv slots bits live) (x : Nat) (v : T) (hf : slots.isFull x = true) :
    PoolInv (slots.setCell x (some v)) bits live where
  bit_iff i hi := by
    by_cases hix : i = x
    · subst hix
      rw [Slots.cell_setCell_same _ _ _ hi, h.bit_iff i hi]; simpa [Slots.isFull] using hf
    · rw [Slots.cell_setCell_ne _ _ _ _ (Ne.symm hix), h.bit_iff i hi]
  live_eq := h.live_eq

end PoolInv

end Millipede.Lib
