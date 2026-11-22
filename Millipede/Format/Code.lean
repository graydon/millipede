import Millipede.Lib.Slice
import Millipede.Format.Theorems

/-!
# Format descriptions: Millipede code for the leaves

The Millipede functions that read and write the leaves of a description over byte slices, each one
definition for every slice bound `N < 2 ^ 64`, with contracts stated against the model
(`Millipede/Format/Model.lean`). The bytes of a slice `s` are `Slots.bytes s s.len.toNat`.

- `getU s pos k big` reads an integer of `k ≤ 8` bytes at `pos`, in big-endian order when `big`;
  its contract is `decUint` of the `k` bytes at `pos`.
- `putU d pos k big v` writes the `k` low bytes of `v` at `pos`; after it the bytes at `pos` are
  `encUint k _ v` and the other cells are unchanged (`Writes`).
- `getBytes` and `putBytes` copy `n` bytes between a slice and an array.
- `parseUint`, `parseLBytes`, `writeUint`, `writeLBytes` are the leaves `uint` and `lbytes` in one
  calling convention, so that they compose: a parser takes the position by `&mut`, returns whether
  the input parsed, and its contract is `Parsed f B pos ok pos' v`, which says nothing about the
  position or the output when the input does not parse; a writer requires room for its bytes, and
  its contract is `Written f d d' pos pos' v`: it wrote `f.write v` at `pos` and left every other
  cell unchanged. `parseLBytes` also bounds the length it returns by `max`.
  `Parsed` and `Written` compose through `pair` and `union` by the lemmas of this file, so a
  record or a union is a sequence of calls whose proof cites the leaves' contracts.
-/

namespace Millipede.Format

open Millipede Std.WP

set_option experimental.vcgen true

/-- The first `len` bytes of a byte slice's cells, with 0 for an empty cell. -/
def Slots.bytes {N : Nat} (s : Slots UInt8 N) (len : Nat) : List UInt8 :=
  (List.range len).map fun i => (s.cell i).getD 0

/-- The byte order named by a flag. -/
def endian (big : Bool) : Endian := if big then .big else .little

/-- The bytes read after `d` of the `k` steps of `getU`: the first `d` in big-endian order, the
last `d` in little-endian order. -/
def win (big : Bool) (L : List UInt8) (d : Nat) : List UInt8 :=
  if big then L.take d else L.drop (L.length - d)

@[simp] theorem Slots.bytes_length {N : Nat} (s : Slots UInt8 N) (len : Nat) :
    (Slots.bytes s len).length = len := by simp [Slots.bytes]

theorem Slots.bytes_getElem {N : Nat} (s : Slots UInt8 N) (len i : Nat) (h : i < (Slots.bytes s len).length) :
    (Slots.bytes s len)[i] = (s.cell i).getD 0 := by simp [Slots.bytes]

theorem Slots.bytes_window_length {N : Nat} (s : Slots UInt8 N) {len pos k : Nat}
    (h : pos + k ≤ len) : (((Slots.bytes s len).drop pos).take k).length = k := by
  simp; omega

theorem Slots.bytes_window_getElem {N : Nat} (s : Slots UInt8 N) {len pos k : Nat} (i : Nat)
    (h : i < (((Slots.bytes s len).drop pos).take k).length) :
    (((Slots.bytes s len).drop pos).take k)[i] = (s.cell (pos + i)).getD 0 := by
  simp [Slots.bytes]

/-- The index `pos + k - 1 - c` of a little-endian read, as a number. -/
theorem toNat_idx_rev {pos k : UInt64} {c : Nat} (hc : c < k.toNat) (h : pos.toNat + k.toNat < 2 ^ 64) :
    (pos + k - 1 - UInt64.ofNat c).toNat = pos.toNat + k.toNat - 1 - c := by
  have hc' : (UInt64.ofNat c).toNat = c := UInt64.toNat_ofNat_of_lt' (show c < 2 ^ 64 by omega)
  have h1 : (pos + k).toNat = pos.toNat + k.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  have h2 : (pos + k - 1).toNat = pos.toNat + k.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1]; simp; omega), h1]; simp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hc', h2]; omega), h2, hc']

theorem win_zero (big : Bool) (L : List UInt8) : win big L 0 = [] := by
  cases big <;> simp [win]

theorem win_len (big : Bool) (L : List UInt8) : win big L L.length = L := by
  cases big <;> simp [win]

theorem decUint_win_lt (big : Bool) (L : List UInt8) (d : Nat) (hd : d ≤ L.length) :
    decUint (endian big) (win big L d) < 256 ^ d := by
  have := decUint_lt (endian big) (win big L d)
  cases big <;> simp_all [win] <;> grind

theorem decUint_win_step (big : Bool) (L : List UInt8) (d : Nat) (hd : d < L.length) :
    decUint (endian big) (win big L (d + 1)) =
      256 * decUint (endian big) (win big L d) + (if big then L[d] else L[L.length - 1 - d]).toNat := by
  cases big
  · simp only [win, endian, decUint, Bool.false_eq_true, ite_false]
    rw [List.drop_eq_getElem_cons (i := L.length - (d + 1)) (by omega),
      show L.length - d = L.length - (d + 1) + 1 by omega]
    simp only [leVal, show L.length - (d + 1) = L.length - 1 - d by omega]
    omega
  · simp only [win, endian, decUint, ite_true, List.take_add_one, List.getElem?_eq_getElem hd,
      Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append, leVal]
    omega

theorem getU_step (big : Bool) (L : List UInt8) (d : Nat) (hd : d < L.length) (hL : L.length ≤ 8)
    (b : UInt64) (hb : b.toNat = decUint (endian big) (win big L d)) (x : UInt8)
    (hx : x = if big then L[d] else L[L.length - 1 - d]) :
    (b * 256 + x.toUInt64).toNat = decUint (endian big) (win big L (d + 1)) := by
  have h1 := decUint_win_lt big L d (by omega)
  have h2 : 256 ^ d ≤ 256 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := x.toNat_lt
  rw [decUint_win_step big L d hd, ← hx, ← hb]
  have h7 : (256 : Nat) ^ 7 = 72057594037927936 := rfl
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (a := b.toNat * 256) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega
/-! ## Reading and writing integers -/

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
set_option mp.autoSpec false in
/-- The integer of `k ≤ 8` bytes at `pos`. -/
mp def getU (s : &[UInt8; N]) (pos : UInt64) (k : UInt64) (big : Bool)
    requires pos.toNat + k.toNat ≤ s.len.toNat ∧ k.toNat ≤ 8
    ensures result.toNat = decUint (endian big) (((Slots.bytes s s.len.toNat).drop pos.toNat).take k.toNat) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    if i ≥ k then break
    let j := if big then pos + i else pos + k - 1 - i
    acc := acc * 256 + s[j]!.toUInt64
  acc
end

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
mp prove getU.spec := by
  intro s sl pos k big
  vcgen [getU] invariants
  · fun done _ acc => acc.toNat = decUint (endian big)
      (win big (((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat) (min done.length k.toNat))
  all_goals obtain ⟨⟨hpk, hk8⟩, hsl, -⟩ := ‹(_ ∧ _) ∧ _›
  all_goals have hL := Slots.bytes_window_length s hpk
  all_goals clear ‹(_ ∧ _) ∧ _›
  case vc1 => cases big <;> simp [win_zero, decUint, leVal, endian]
  case vc2 ih =>
    have hw := win_len big (((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat)
    rw [hL] at hw
    rw [List.length_range, Nat.min_eq_right hk8, hw] at ih
    exact ih
  case vc3 pref cur suff hr b ih hc hbig =>
    subst hbig
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simp only [List.length_append, List.length_singleton, Nat.min_eq_left (Nat.le_of_lt hc),
      Nat.min_eq_left (show pref.length + 1 ≤ k.toNat by omega)] at ih ⊢
    refine getU_step true (((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat) pref.length (by omega) (by omega) _ ih _ ?_
    simp [Slots.bytes, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show pos.toNat + pref.length < 2 ^ 64 by omega)]
    rfl
  case vc4 pref cur suff hr b ih hc hbig =>
    simp only [Bool.not_eq_true] at hbig; subst hbig
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simp only [List.length_append, List.length_singleton, Nat.min_eq_left (Nat.le_of_lt hc),
      Nat.min_eq_left (show pref.length + 1 ≤ k.toNat by omega)] at ih ⊢
    refine getU_step false (((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat) pref.length (by omega) (by omega) _ ih _ ?_
    simp only [toNat_idx_rev (pos := pos) (k := k) hc (by omega), Bool.false_eq_true, ite_false]
    rw [Slots.bytes_window_getElem, hL]
    rw [show pos.toNat + (k.toNat - 1 - pref.length) = pos.toNat + k.toNat - 1 - pref.length by omega]
    rfl
  case vc5 pref cur suff hr b ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simpa [Nat.min_eq_right (show k.toNat ≤ pref.length by omega), Nat.min_eq_right hk8] using ih
end

/-- `d'` is `d` with the bytes `l` written at `pos`. -/
def Writes {N : Nat} (d d' : Slots UInt8 N) (pos : Nat) (l : List UInt8) : Prop :=
  ∀ j < N, d'.cell j = if pos ≤ j ∧ j < pos + l.length then l[j - pos]? else d.cell j

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
set_option mp.autoSpec false in
/-- Write the `k ≤ 8` low bytes of `v` at `pos`. -/
mp def putU (d : &mut [UInt8; N]) (pos : UInt64) (k : UInt64) (big : Bool) (v : UInt64)
    requires pos.toNat + k.toNat ≤ d.len.toNat ∧ k.toNat ≤ 8
    ensures Writes d d' pos.toNat (encUint k.toNat (endian big) v.toNat) : Unit := do
  let mut w := v
  for i in 0...8 do
    if i ≥ k then break
    let j := if big then pos + k - 1 - i else pos + i
    d[j]! := (w % 256).toUInt8
    w := w / 256
end

theorem leBytes_getElem? (k n i : Nat) (h : i < k) :
    (leBytes k n)[i]? = some (UInt8.ofNat (n / 256 ^ i % 256)) := by
  induction k generalizing n i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [leBytes]
    | succ i =>
      simp only [leBytes, List.getElem?_cons_succ, ih (n / 256) i (by omega), Nat.div_div_eq_div_mul,
        Nat.pow_succ']

/-- Byte `i` of the encoding, which `putU` writes at step `i` from the right end (big-endian) or
the left end (little-endian). -/
theorem encUint_getElem? (k n i : Nat) (big : Bool) (h : i < k) :
    (encUint k (endian big) n)[if big then k - 1 - i else i]? =
      some (UInt8.ofNat (n / 256 ^ i % 256)) := by
  cases big
  · simp [encUint, endian, leBytes_getElem? k n i h]
  · simp only [encUint, endian, ite_true, List.getElem?_reverse (by simp; omega : k - 1 - i < (leBytes k n).length),
      leBytes_length]
    rw [show k - 1 - (k - 1 - i) = i by omega, leBytes_getElem? k n i h]

theorem toUInt8_mod (w : UInt64) : (w % 256).toUInt8 = UInt8.ofNat (w.toNat % 256) := by
  apply UInt8.toNat_inj.mp; simp

/-- The cells after `dd` of the `k` steps of `putU`. -/
def PartW {N : Nat} (d st : Slots UInt8 N) (pos k : Nat) (big : Bool) (n dd : Nat) : Prop :=
  ∀ j < N, st.cell j = if (if big then pos + k - dd ≤ j ∧ j < pos + k else pos ≤ j ∧ j < pos + dd)
    then (encUint k (endian big) n)[j - pos]? else d.cell j

theorem PartW.init {N : Nat} (d : Slots UInt8 N) (pos k : Nat) (big : Bool) (n : Nat) :
    PartW d d pos k big n 0 := by
  intro j _; cases big <;> simp <;> omega

theorem PartW.step {N : Nat} {d st : Slots UInt8 N} {pos k : Nat} {big : Bool} {n dd : Nat}
    (h : PartW d st pos k big n dd) (hd : dd < k) :
    PartW d (st.setCell (if big then pos + k - 1 - dd else pos + dd) (some (UInt8.ofNat (n / 256 ^ dd % 256))))
      pos k big n (dd + 1) := by
  intro j hj
  rw [Slots.cell_setCell, h j hj]
  have he := encUint_getElem? k n dd big hd
  cases big <;> simp only [Bool.false_eq_true, ite_false, ite_true] at he ⊢
  · by_cases e : j = pos + dd
    · subst e; simp [hj, he]
    · simp only [e, false_and, ite_false]; grind
  · by_cases e : j = pos + k - 1 - dd
    · subst e; simp [hj, show pos + k - 1 - dd - pos = k - 1 - dd by omega, he]; omega
    · simp only [e, false_and, ite_false]; grind

theorem PartW.writes {N : Nat} {d st : Slots UInt8 N} {pos k : Nat} {big : Bool} {n : Nat}
    (h : PartW d st pos k big n k) : Writes d st pos (encUint k (endian big) n) := by
  intro j hj
  rw [h j hj, encUint_length]
  cases big <;> simp

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
mp prove putU.spec := by
  intro d dl pos k big v
  vcgen [putU] invariants
  · fun done _ (w, st, _) => w.toNat = v.toNat / 256 ^ (min done.length k.toNat) ∧
      PartW d st pos.toNat k.toNat big v.toNat (min done.length k.toNat)
  case vc1 => simp [PartW.init]
  case vc2 hp w st _ ih =>
    obtain ⟨-, ih⟩ := ih
    rw [List.length_range, Nat.min_eq_right hp.1.2] at ih
    exact ih.writes
  case vc3 hp pref cur suff hr w st _ ih hc hbig =>
    subst hbig
    obtain ⟨rfl, _⟩ := range_split hr
    obtain ⟨⟨hpk, hk8⟩, hsl, -⟩ := hp
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simp only [List.length_append, List.length_singleton, Nat.min_eq_left (Nat.le_of_lt hc),
      Nat.min_eq_left (show pref.length + 1 ≤ k.toNat by omega)] at ih ⊢
    obtain ⟨hw, ih⟩ := ih
    refine ⟨?_, ?_⟩
    · simp [hw, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · have := ih.step hc
      simp only [ite_true] at this
      rw [toNat_idx_rev (pos := pos) (k := k) hc (by omega)]
      simpa [hw, toUInt8_mod] using this
  case vc4 hp pref cur suff hr w st _ ih hc hbig =>
    simp only [Bool.not_eq_true] at hbig; subst hbig
    obtain ⟨rfl, _⟩ := range_split hr
    obtain ⟨⟨hpk, hk8⟩, hsl, -⟩ := hp
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simp only [List.length_append, List.length_singleton, Nat.min_eq_left (Nat.le_of_lt hc),
      Nat.min_eq_left (show pref.length + 1 ≤ k.toNat by omega)] at ih ⊢
    obtain ⟨hw, ih⟩ := ih
    refine ⟨?_, ?_⟩
    · simp [hw, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · have := ih.step hc
      simp only [Bool.false_eq_true, ite_false] at this
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show pos.toNat + pref.length < 2 ^ 64 by omega)]
      simpa [hw, toUInt8_mod] using this
  case vc5 hp pref cur suff hr w st _ ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simpa [Nat.min_eq_right (show k.toNat ≤ pref.length by omega), Nat.min_eq_right hp.1.2] using ih
end
/-! ## Copying bytes -/

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM
set_option mp.autoSpec false in
/-- Copy the `n` bytes at `pos` into the first `n` elements of `out`. -/
mp def getBytes (s : &[UInt8; N]) (pos n : UInt64) (out : &mut Arr UInt8 M)
    requires pos.toNat + n.toNat ≤ s.len.toNat ∧ n.toNat ≤ M
    ensures ∀ j < n.toNat, vget out' j 0 = (s.cell (pos.toNat + j)).getD 0 : Unit := do
  for i in 0...M do
    if i ≥ n then break
    out[i] := s[pos + i]!

set_option mp.autoSpec false in
/-- Write the first `n` elements of `src` at `pos`. -/
mp def putBytes (d : &mut [UInt8; N]) (pos : UInt64) (src : &Arr UInt8 M) (n : UInt64)
    requires pos.toNat + n.toNat ≤ d.len.toNat ∧ n.toNat ≤ M
    ensures Writes d d' pos.toNat (src.toList.take n.toNat) : Unit := do
  for i in 0...M do
    if i ≥ n then break
    d[pos + i]! := src[i]
end

theorem Writes.nil {N : Nat} (d : Slots UInt8 N) (pos : Nat) : Writes d d pos [] := by
  intro j _; rw [ite_eq_right (by simp)]

theorem Writes.snoc {N : Nat} {d st : Slots UInt8 N} {pos : Nat} {l : List UInt8} (x : UInt8)
    (h : Writes d st pos l) : Writes d (st.setCell (pos + l.length) (some x)) pos (l ++ [x]) := by
  intro j hj
  rw [Slots.cell_setCell, h j hj]
  by_cases e : j = pos + l.length
  · subst e; simp [hj]
  · simp only [e, false_and, ite_false, List.length_append, List.length_singleton]
    by_cases hr : pos ≤ j ∧ j < pos + l.length
    · rw [ite_eq_left hr, ite_eq_left (by omega), List.getElem?_append_left (by omega)]
    · rw [ite_eq_right hr, ite_eq_right (by omega)]

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM
mp prove getBytes.spec := by
  intro s sl pos n out
  vcgen [getBytes] invariants
  · fun done _ (_, o, _) => ∀ j < min done.length n.toNat, vget o j 0 = (s.cell (pos.toNat + j)).getD 0
  case vc1 => simp
  case vc2 hp _ o _ ih j hj =>
    exact ih j (by simp; omega)
  case vc3 hp pref cur suff hr _ o _ ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    obtain ⟨⟨hpk, hnM⟩, hsl, -⟩ := hp
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    rw [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), UInt64.toNat_add,
      UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show pos.toNat + pref.length < 2 ^ 64 by omega)]
    by_cases e : j = pref.length
    · subst e; rw [vget_vset_same _ _ _ _ (by omega)]; rfl
    · rw [vget_vset_ne _ _ _ _ _ (Ne.symm e)]; exact ih j (by omega)
  case vc4 hp pref cur suff hr _ o _ ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    intro j hj
    exact ih j (by simp at hj; omega)
mp prove putBytes.spec := by
  intro d dl pos src n
  vcgen [putBytes] invariants
  · fun done _ (_, st, _) => Writes d st pos.toNat (src.toList.take (min done.length n.toNat))
  case vc1 => simpa using Writes.nil d pos.toNat
  case vc2 hp _ st _ ih =>
    simpa [Nat.min_eq_right (show n.toNat ≤ M by omega)] using ih
  case vc3 hp pref cur suff hr _ st _ ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    obtain ⟨⟨hpk, hnM⟩, hsl, -⟩ := hp
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simp only [List.length_append, List.length_singleton, Nat.min_eq_left (Nat.le_of_lt hc),
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)] at ih ⊢
    have := ih.snoc (vget src pref.length 0)
    rw [List.length_take, Nat.min_eq_left (by simp; omega)] at this
    rw [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), UInt64.toNat_add,
      UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show pos.toNat + pref.length < 2 ^ 64 by omega), List.take_add_one]
    simpa [vget, show pref.length < M by omega] using this
  case vc4 hp pref cur suff hr _ st _ ih hc =>
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    simpa [Nat.min_eq_right (show n.toNat ≤ M by omega), Nat.min_eq_right (show n.toNat ≤ pref.length by omega)] using ih
end
/-! ## The calling convention of parsers and writers -/

/-- What a parser at `pos` in the bytes `B` returned, `ok`, the position `pos'` and the value `v`,
against the model (in an arm chain, for the selected tag `t`): when `f` parses the bytes from
`pos`, `ok` is true, `pos'` is the position after the value and `v` is the value; otherwise `ok` is
false. -/
def ParsedT (f : Fmt) (t : Nat) (B : List UInt8) (pos : UInt64) (ok : Bool) (pos' : UInt64)
    (v : Val) : Prop :=
  match f.parseT t (B.drop pos.toNat) with
  | none => ok = false
  | some (w, rest) => ok = true ∧ pos'.toNat + rest.length = B.length ∧ v = w

/-- `ParsedT` for a whole description. -/
abbrev Parsed (f : Fmt) := ParsedT f 0

/-- What a writer did: it wrote the bytes of `v` at `pos` and nothing else, and `pos'` is the
position after them. -/
def WrittenT {N : Nat} (f : Fmt) (t : Nat) (d d' : Slots UInt8 N) (pos pos' : UInt64) (v : Val) :
    Prop :=
  pos'.toNat = pos.toNat + (f.writeT t v).length ∧ Writes d d' pos.toNat (f.writeT t v)

/-- `WrittenT` for a whole description. -/
abbrev Written {N : Nat} (f : Fmt) := @WrittenT N f 0

/-- A byte string of at most `M` bytes: the first `len` elements of `data`. -/
structure LBytes (M : Nat) where
  len : UInt64
  data : Arr UInt8 M
deriving Data

instance {M : Nat} : Inhabited (LBytes M) := ⟨⟨0, Vector.replicate M 0⟩⟩

/-- The value of a byte string. -/
def LBytes.toVal {M : Nat} (b : LBytes M) : Val := .bytes (b.data.toList.take b.len.toNat)

/-- The bytes of a byte string. -/
def LBytes.bytes {M : Nat} (b : LBytes M) : List UInt8 := b.data.toList.take b.len.toNat

/-- Two byte strings within their bounds are equal when their lengths and their first `len` bytes
are. -/
theorem LBytes.bytes_eq_iff {M : Nat} {a b : LBytes M} (ha : a.len.toNat ≤ M) (hb : b.len.toNat ≤ M) :
    a.bytes = b.bytes ↔ a.len = b.len ∧ ∀ j < a.len.toNat, vget a.data j 0 = vget b.data j 0 := by
  simp only [LBytes.bytes]
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_take, Vector.length_toList] at hl
    have hlen : a.len = b.len := UInt64.toNat_inj.mp (by omega)
    refine ⟨hlen, fun j hj => ?_⟩
    have := congrArg (·[j]?) h
    simp only [List.getElem?_take, hj, ← hlen, ite_true] at this
    simpa [vget, show j < M by omega, Vector.getElem?_toList] using this
  · rintro ⟨hlen, h⟩
    apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    simp only [List.length_take, Vector.length_toList] at h1
    have := h j (by omega)
    simpa [vget, show j < M by omega] using this

/-- The value of a byte string is its bytes. -/
theorem LBytes.toVal_eq {M : Nat} (b : LBytes M) : b.toVal = .bytes b.bytes := rfl

/-- The bytes of a slice of the first `n` elements of an array are those elements. -/
theorem Slots.bytes_vview {N : Nat} (v : Vector UInt8 N) {n : Nat} (h : n ≤ N) :
    Slots.bytes (vview v 0 n) n = v.toList.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [Slots.bytes_length] at h1
  rw [Slots.bytes_getElem, vview_cell]
  simp [h1, show i < N by omega]

/-- Writing `w` at the start of a slice of an array, and writing the slice back, puts `w` at the
start of the array. -/
theorem vunview_take {N : Nat} {v : Vector UInt8 N} {s' : Slots UInt8 N} {w : List UInt8} {n : Nat}
    (hw : Writes (vview v 0 n) s' 0 w) (hl : w.length ≤ n) (hn : n ≤ N) :
    (vunview v 0 n s').toList.take w.length = w := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_take, Vector.length_toList] at h1
  have := hw i (by omega)
  rw [ite_eq_left ⟨by omega, by omega⟩] at this
  simp [vunview, show i < n by omega, this, List.getElem?_eq_getElem h2]

namespace ParsedT

variable {f : Fmt} {t : Nat} {B : List UInt8} {p p' : UInt64} {v : Val}

/-- The bytes left by a parse from `p` are the bytes from the position after the value. -/
theorem rest_eq {w : Val} {rest : List UInt8} (h : f.parseT t (B.drop p.toNat) = some (w, rest))
    (hp : p.toNat ≤ B.length) : rest = B.drop (B.length - rest.length) ∧
      p.toNat + rest.length ≤ B.length := by
  obtain ⟨_, pre, he, _⟩ := Fmt.parseT_sound f t _ w rest h
  have hl := congrArg List.length he
  simp only [List.length_drop, List.length_append] at hl
  refine ⟨?_, by omega⟩
  rw [show B.length - rest.length = p.toNat + pre.length by omega, ← List.drop_drop, he]
  simp

theorem ok_eq (h : ParsedT f t B p true p' v) (hp : p.toNat ≤ B.length) :
    f.parseT t (B.drop p.toNat) = some (v, B.drop p'.toNat) ∧ p.toNat ≤ p'.toNat ∧
      p'.toNat ≤ B.length := by
  unfold ParsedT at h
  split at h
  · cases h
  · rename_i w rest he
    obtain ⟨-, hl, rfl⟩ := h
    obtain ⟨hr, hle⟩ := rest_eq he hp
    refine ⟨?_, by omega, by omega⟩
    rw [he, show p'.toNat = B.length - rest.length by omega, ← hr]

theorem of_some (h : f.parseT t (B.drop p.toNat) = some (v, B.drop p'.toNat))
    (hp' : p'.toNat ≤ B.length) : ParsedT f t B p true p' v := by
  unfold ParsedT; rw [h]; simp; omega

theorem false_iff {p'' : UInt64} {v' : Val} :
    ParsedT f t B p false p' v ↔ ParsedT f t B p false p'' v' := by
  unfold ParsedT; split <;> simp

theorem of_none (h : f.parseT t (B.drop p.toNat) = none) : ParsedT f t B p false p' v := by
  unfold ParsedT; rw [h]

theorem none_of_false (h : ParsedT f t B p false p' v) : f.parseT t (B.drop p.toNat) = none := by
  unfold ParsedT at h; split at h <;> simp_all

end ParsedT

/-- A parser that returned true read a value of the description. -/
theorem ParsedT.okT {f : Fmt} {t : Nat} {B : List UInt8} {p p' : UInt64} {v : Val}
    (h : ParsedT f t B p true p' v) (hp : p.toNat ≤ B.length) : f.okT t v = true :=
  (Fmt.parseT_sound f t _ v _ (h.ok_eq hp).1).1

/-- A parser's position after a value is within the bytes. -/
theorem ParsedT.le_len {f : Fmt} {t : Nat} {N : Nat} {s : Slots UInt8 N} {len : Nat} {p p' : UInt64}
    {ok : Bool} {v : Val} (h : ParsedT f t (Slots.bytes s len) p ok p' v) (hok : ok = true)
    (hp : p.toNat ≤ len) : p'.toNat ≤ len := by
  subst hok; simpa using (h.ok_eq (by simpa using hp)).2.2

/-- The contract of a parser, with the bound on the position after the value. -/
theorem ParsedT.with_le {f : Fmt} {t : Nat} {N : Nat} {s : Slots UInt8 N} {len : Nat} {p p' : UInt64}
    {ok : Bool} {v : Val} (h : ParsedT f t (Slots.bytes s len) p ok p' v) (hp : p.toNat ≤ len) :
    ParsedT f t (Slots.bytes s len) p ok p' v ∧ (ok = true → p'.toNat ≤ len) :=
  ⟨h, fun hok => h.le_len hok hp⟩

/-- A record stops when its first field does not parse. -/
theorem Parsed.pair_stop {a b : Fmt} {B : List UInt8} {p p1 p' : UInt64} {va v : Val} {t : Nat}
    (ha : Parsed a B p false p1 va) : ParsedT (.pair a b) t B p false p' v := by
  apply ParsedT.of_none; simp [Fmt.parseT, ParsedT.none_of_false ha]

/-- A record parses as its first field, then its second from where the first ended. -/
theorem Parsed.pair_cont {a b : Fmt} {B : List UInt8} {p p1 p2 : UInt64} {va vb : Val} {ok : Bool}
    {t : Nat} (hp : p.toNat ≤ B.length) (ha : Parsed a B p true p1 va)
    (hb : Parsed b B p1 ok p2 vb) : ParsedT (.pair a b) t B p ok p2 (.pair va vb) := by
  obtain ⟨hpa, -, hp1⟩ := ha.ok_eq hp
  cases ok
  · apply ParsedT.of_none; simp [Fmt.parseT, hpa, ParsedT.none_of_false hb]
  · obtain ⟨hpb, -, hp2⟩ := hb.ok_eq hp1
    apply ParsedT.of_some _ hp2; simp [Fmt.parseT, hpa, hpb]

/-- A union stops when its tag does not parse. -/
theorem Parsed.union_stop {k : Nat} {e : Endian} {arms : Fmt} {B : List UInt8} {p p1 p' : UInt64}
    {vt v : Val} {t : Nat} (ht : Parsed (.uint k e) B p false p1 vt) :
    ParsedT (.union k e arms) t B p false p' v := by
  have h := ParsedT.none_of_false ht
  apply ParsedT.of_none
  simp only [Fmt.parseT, Option.map_eq_none_iff] at h ⊢
  rw [h]

/-- A union parses as its tag, then the arm of that tag from where the tag ended. -/
theorem Parsed.union_cont {k : Nat} {e : Endian} {arms : Fmt} {B : List UInt8} {p p1 p2 : UInt64}
    {tg : Nat} {v : Val} {ok : Bool} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num tg)) (ha : ParsedT arms tg B p1 ok p2 v) :
    ParsedT (.union k e arms) t B p ok p2 (.tag tg v) := by
  obtain ⟨hpt, -, hp1⟩ := ht.ok_eq hp
  simp only [Fmt.parseT, Option.map_eq_some_iff] at hpt
  obtain ⟨⟨n, r⟩, hr, he⟩ := hpt
  simp only [Prod.mk.injEq, Val.num.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases ok
  · apply ParsedT.of_none; simp [Fmt.parseT, hr, ParsedT.none_of_false ha]
  · obtain ⟨hpa, -, hp2⟩ := ha.ok_eq hp1
    apply ParsedT.of_some _ hp2; simp [Fmt.parseT, hr, hpa]

/-- An arm chain at tag `t` is the first arm with that tag. -/
theorem ParsedT.arm_eq {tag : Nat} {f rest : Fmt} {t : Nat} {B : List UInt8} {p p' : UInt64}
    {ok : Bool} {v : Val} : ParsedT (.arm tag f rest) t B p ok p' v =
      if t = tag then Parsed f B p ok p' v else ParsedT rest t B p ok p' v := by
  by_cases ht : t = tag <;> simp only [ParsedT, Fmt.parseT, ht, ite_true, ite_false]

/-- No arm matches. -/
theorem ParsedT.noArm {t : Nat} {B : List UInt8} {p p' : UInt64} {v : Val} :
    ParsedT .noArm t B p false p' v := ParsedT.of_none rfl

theorem Writes.append {N : Nat} {d d1 d2 : Slots UInt8 N} {p : Nat} {l1 l2 : List UInt8}
    (h1 : Writes d d1 p l1) (h2 : Writes d1 d2 (p + l1.length) l2) : Writes d d2 p (l1 ++ l2) := by
  intro j hj
  rw [h2 j hj, h1 j hj]
  simp only [List.length_append]
  by_cases a : p + l1.length ≤ j ∧ j < p + l1.length + l2.length
  · rw [ite_eq_left a, ite_eq_left (by omega), List.getElem?_append_right (by omega),
      show j - p - l1.length = j - (p + l1.length) by omega]
  · rw [ite_eq_right a]
    by_cases b : p ≤ j ∧ j < p + l1.length
    · rw [ite_eq_left b, ite_eq_left (by omega), List.getElem?_append_left (by omega)]
    · rw [ite_eq_right b, ite_eq_right (by omega)]

/-- Writing keeps the full cells full. -/
theorem Writes.isFull {N : Nat} {d d' : Slots UInt8 N} {p : Nat} {l : List UInt8} (h : Writes d d' p l)
    {j : Nat} (hj : d.isFull j = true) : d'.isFull j = true := by
  have hjN : j < N := Slots.lt_of_isFull hj
  simp only [Slots.isFull, h j hjN] at hj ⊢
  split
  · simp [List.getElem?_eq_getElem (show j - p < l.length by omega)]
  · exact hj

/-- A record writes its first field, then its second after it. -/
theorem Written.pair {N : Nat} {a b : Fmt} {d d1 d2 : Slots UInt8 N} {p p1 p2 : UInt64} {va vb : Val}
    {t : Nat} (ha : Written a d d1 p p1 va) (hb : Written b d1 d2 p1 p2 vb) :
    WrittenT (.pair a b) t d d2 p p2 (.pair va vb) := by
  obtain ⟨h1, wa⟩ := ha
  obtain ⟨h2, wb⟩ := hb
  rw [h1] at wb h2
  exact ⟨by simp [Fmt.writeT, h2]; omega, by simpa [Fmt.writeT] using wa.append wb⟩

/-- A union writes its tag, then the arm of that tag after it. -/
theorem Written.union {N : Nat} {k : Nat} {e : Endian} {arms : Fmt} {d d1 d2 : Slots UInt8 N}
    {p p1 p2 : UInt64} {tg : Nat} {v : Val} {t : Nat} (ht : Written (.uint k e) d d1 p p1 (.num tg))
    (ha : WrittenT arms tg d1 d2 p1 p2 v) : WrittenT (.union k e arms) t d d2 p p2 (.tag tg v) := by
  obtain ⟨h1, wa⟩ := ht
  obtain ⟨h2, wb⟩ := ha
  rw [h1] at wb h2
  exact ⟨by simp [Fmt.writeT, h2] at *; omega, by simpa [Fmt.writeT] using wa.append wb⟩

/-- An arm chain at tag `t` writes the first arm with that tag. -/
theorem WrittenT.arm_eq {N : Nat} {tag : Nat} {f rest : Fmt} {t : Nat} {d d' : Slots UInt8 N}
    {p p' : UInt64} {v : Val} : WrittenT (.arm tag f rest) t d d' p p' v =
      if t = tag then Written f d d' p p' v else WrittenT rest t d d' p p' v := by
  by_cases ht : t = tag <;> simp only [WrittenT, Fmt.writeT, ht, ite_true, ite_false]

/-- The empty record parses without reading. -/
theorem ParsedT.unit {t : Nat} {B : List UInt8} {p : UInt64} (hp : p.toNat ≤ B.length) :
    ParsedT .unit t B p true p .unit :=
  ParsedT.of_some (by simp [Fmt.parseT]) hp

/-- The empty record writes nothing. -/
theorem WrittenT.unit {N : Nat} {t : Nat} {d : Slots UInt8 N} {p : UInt64} {v : Val} :
    WrittenT .unit t d d p p v := ⟨by simp [Fmt.writeT], Writes.nil _ _⟩

/-- A union whose tag has no arm writes nothing after the tag. -/
theorem WrittenT.noArm {N : Nat} {t : Nat} {d : Slots UInt8 N} {p : UInt64} {v : Val} :
    WrittenT .noArm t d d p p v := ⟨by simp [Fmt.writeT], Writes.nil _ _⟩

/-- A writer's contract that holds for every bound of a byte string, at one bound. -/
theorem WrittenT.of_forall {N : Nat} {k : Nat} {e : Endian} {m t : Nat} {d d' : Slots UInt8 N}
    {p p' : UInt64} {v : Val} (h : ∀ m, WrittenT (.lbytes k e m) t d d' p p' v) :
    WrittenT (.lbytes k e m) t d d' p p' v := h m

/-- A cell below a bound under which every cell is full is full. -/
theorem isFull_of_lt {N : Nat} {d : Slots UInt8 N} {n k : Nat} (hf : ∀ j < n, d.isFull j = true)
    (hk : k < n) : d.isFull k = true := hf k hk

/-- A writer keeps a full cell full. -/
theorem WrittenT.isFull {N : Nat} {f : Fmt} {t : Nat} {d d' : Slots UInt8 N} {p p' : UInt64} {v : Val}
    {j : Nat} (hw : WrittenT f t d d' p p' v) (hf : d.isFull j = true) : d'.isFull j = true :=
  hw.2.isFull hf

/-- A byte-string writer keeps a full cell full. -/
theorem WrittenT.isFull_forall {N : Nat} {k : Nat} {e : Endian} {t : Nat} {d d' : Slots UInt8 N}
    {p p' : UInt64} {v : Val} {j : Nat} (hw : ∀ m, WrittenT (.lbytes k e m) t d d' p p' v)
    (hf : d.isFull j = true) : d'.isFull j = true := (hw 0).isFull hf

/-! ## The leaves `uint` and `lbytes` -/

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN

set_option mp.autoSpec false in
/-- Parse an integer of `k ≤ 8` bytes at `pos` into `out`. -/
mp def parseUint (s : &[UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool) (out : &mut UInt64)
    requires pos.toNat ≤ s.len.toNat ∧ k.toNat ≤ 8
    ensures Parsed (.uint k.toNat (endian big)) (Slots.bytes s s.len.toNat) pos result pos'
      (.num out'.toNat) ∧ (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < k then return false
  out := getU (&s) p k big
  pos := p + k
  true

set_option mp.autoSpec false in
/-- Write the integer `v` in `k ≤ 8` bytes at `pos`. -/
mp def writeUint (d : &mut [UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool) (v : UInt64)
    requires pos.toNat + k.toNat ≤ d.len.toNat ∧ k.toNat ≤ 8
    ensures pos'.toNat = pos.toNat + k.toNat ∧
      Written (.uint k.toNat (endian big)) d d' pos pos' (.num v.toNat) : Unit := do
  let p := pos
  let _ := putU (&mut d) p k big v
  pos := p + k

include hM

set_option mp.autoSpec false in
/-- Parse a byte string with a length of `k ≤ 8` bytes, at most `max ≤ M`, at `pos` into `out`. -/
mp def parseLBytes (s : &[UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool) (max : UInt64)
    (out : &mut LBytes M) requires pos.toNat ≤ s.len.toNat ∧ k.toNat ≤ 8 ∧ max.toNat ≤ M
    ensures Parsed (.lbytes k.toNat (endian big) max.toNat) (Slots.bytes s s.len.toNat) pos result
      pos' out'.toVal ∧ (result = true → pos'.toNat ≤ s.len.toNat ∧ out'.len.toNat ≤ max.toNat) :
      Bool := do
  let p := pos
  if s.len - p < k then return false
  let n := getU (&s) p k big
  if n > max then return false
  let q := p + k
  if s.len - q < n then return false
  out.len := n
  let _ := getBytes (&s) q n (&mut out.data)
  pos := q + n
  true

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Write the byte string `v` with a length of `k ≤ 8` bytes at `pos`. -/
mp def writeLBytes (d : &mut [UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool)
    (v : &LBytes M) requires pos.toNat + k.toNat + v.len.toNat ≤ d.len.toNat ∧ k.toNat ≤ 8 ∧
      v.len.toNat ≤ M
    ensures pos'.toNat = pos.toNat + k.toNat + v.len.toNat ∧
      ∀ max, Written (.lbytes k.toNat (endian big) max) d d' pos pos' v.toVal : Unit := do
  let p := pos
  let n := v.len
  let _ := putU (&mut d) p k big n
  let _ := putBytes (&mut d) (p + k) (&v.data) n
  pos := p + k + n
end

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM
mp prove writeLBytes.safe := by
  mp_auto [Writes.isFull]
end

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN
mp prove parseUint.spec := by
  intro s sl pos k big out
  vcgen [parseUint]
  all_goals obtain ⟨⟨hp, hk⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 =>
    refine ParsedT.with_le ?_ (by omega)
    apply ParsedT.of_none; simp [Fmt.parseT, readUint]; omega
  case vc2 => exact ⟨⟨by omega, hk⟩, hsl, hf⟩
  case vc3 =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, fun _ => by rw [hpk]; omega⟩
    apply ParsedT.of_some _ (by simp; omega)
    simp [Fmt.parseT, readUint, hpk, ‹_ = decUint _ _›]; omega
mp prove writeUint.spec := by
  intro d dl pos k big v
  vcgen [writeUint]
  case vc1 hp _ st _ hw =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact ⟨hpk, by simp [Fmt.writeT, hpk], hw⟩
end


theorem toNat_add_of_le {a b c : UInt64} (h : a.toNat + b.toNat ≤ c.toNat) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := c.toNat_lt; omega)]

theorem readUint_drop_some {k : Nat} {e : Endian} {B : List UInt8} {p : Nat} (h : p + k ≤ B.length) :
    readUint k e (B.drop p) = some (decUint e ((B.drop p).take k), B.drop (p + k)) := by
  simp [readUint, List.drop_drop]; omega

theorem readUint_drop_none {k : Nat} {e : Endian} {B : List UInt8} {p : Nat} (hp : p ≤ B.length)
    (h : B.length < p + k) :
    readUint k e (B.drop p) = none := by
  simp [readUint]; omega

/-- The first `n` elements of an array that holds the `n` bytes of a slice at `q`. -/
theorem take_toList_eq {N M : Nat} {s : Slots UInt8 N} {len q n : Nat} {a : Vector UInt8 M}
    (hv : ∀ j < n, vget a j 0 = (s.cell (q + j)).getD 0) (hn : n ≤ M) (hq : q + n ≤ len) :
    a.toList.take n = ((Slots.bytes s len).drop q).take n := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_take, Vector.length_toList] at h1
  have := hv j (by omega)
  simp only [vget, show j < M by omega, ↓reduceDIte] at this
  simp [Slots.bytes, this]

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM
mp prove parseLBytes.spec := by
  intro s sl pos k big max out
  vcgen [parseLBytes]
  case vc1 hpre hk' =>
    obtain ⟨⟨hp, -, -⟩, -, -⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk'
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp [Fmt.parseT, readUint_drop_none (show pos.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
      (show (Slots.bytes s sl.toNat).length < pos.toNat + k.toNat by simp; omega)]
  case vc2 hpre hk' =>
    obtain ⟨⟨hp, hk, -⟩, hsl, hf⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk'
    exact ⟨⟨by omega, hk⟩, hsl, hf⟩
  case vc3 hpre hk' n _ hn hmax =>
    obtain ⟨⟨hp, -, -⟩, -, -⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk' hmax
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, hrd, ← hn]
    rw [ite_eq_right (by omega)]
  case vc4 hpre hk' n _ hn hmax hroom =>
    obtain ⟨⟨hp, -, -⟩, -, -⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk' hmax hroom
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hpk] at hroom
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, hrd, ← hn]
    rw [ite_eq_right (by simp; omega)]
  case vc5 hpre hk' n _ hn hmax hroom =>
    obtain ⟨⟨hp, -, hmx⟩, hsl, hf⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk' hmax hroom
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hpk] at hroom
    rw [hpk]; exact ⟨⟨by omega, by omega⟩, hsl, hf⟩
  case vc6 hpre hk' n _ hn hmax hroom _ data _ hv =>
    obtain ⟨⟨hp, -, hmx⟩, hsl, -⟩ := hpre
    try dsimp only at *
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at hk' hmax hroom
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hpk] at hroom
    rw [hpk] at hv
    have hq : (pos + k + n).toNat = pos.toNat + k.toNat + n.toNat := by
      rw [toNat_add_of_le (a := pos + k) (b := n) (c := sl) (by rw [hpk]; omega), hpk]
    refine ⟨ParsedT.of_some ?_ (by rw [hq]; simp; omega), fun _ => ⟨by rw [hq]; omega, by omega⟩⟩
    simp only [Fmt.parseT, hrd, ← hn, LBytes.toVal]
    rw [ite_eq_left (by simp; omega), take_toList_eq (len := sl.toNat) hv (by omega) (by omega), hq, List.drop_drop]
mp prove writeLBytes.spec := by
  intro d dl pos k big v
  vcgen [writeLBytes]
  all_goals obtain ⟨⟨hp, hk, hlen⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  case vc1 => exact ⟨⟨by omega, hk⟩, hsl, hf⟩
  all_goals have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := dl) (by omega)
  case vc2 _ st _ hw => exact ⟨⟨by omega, hlen⟩, hsl, fun j hj => hw.isFull (hf j hj)⟩
  case vc3 _ st _ hw _ st' _ hw' =>
    have hq : (pos + k + v.len).toNat = pos.toNat + k.toNat + v.len.toNat := by
      rw [toNat_add_of_le (c := dl) (by omega), hpk]
    have hl : (v.data.toList.take v.len.toNat).length = v.len.toNat := by simp; omega
    rw [hpk, show pos.toNat + k.toNat = pos.toNat + (encUint k.toNat (endian big) v.len.toNat).length by simp] at hw'
    refine ⟨hq, fun m => ⟨by simp [Fmt.writeT, LBytes.toVal, hq, hl]; omega, ?_⟩⟩
    simp only [Fmt.writeT, LBytes.toVal, hl]
    exact hw.append hw'
end

/-! ## Validators

A validator at `pos` returns whether a value of the description begins there and moves the position
past it, without building the value. Its contract is `Checked f B pos ok pos'`, which is
`Fmt.checkT` as `ParsedT` is `Fmt.parseT`, and which composes through the same lemmas. -/

/-- What a validator at `pos` in the bytes `B` returned, against `Fmt.checkT` (in an arm chain,
for the selected tag `t`). -/
def CheckedT (f : Fmt) (t : Nat) (B : List UInt8) (pos : UInt64) (ok : Bool) (pos' : UInt64) :
    Prop :=
  match f.checkT t (B.drop pos.toNat) with
  | none => ok = false
  | some rest => ok = true ∧ pos'.toNat + rest.length = B.length

/-- `CheckedT` for a whole description. -/
abbrev Checked (f : Fmt) := CheckedT f 0

namespace CheckedT

variable {f : Fmt} {t : Nat} {B : List UInt8} {p p' : UInt64} {ok : Bool}

/-- A validator's contract is a parser's for some value. -/
theorem iff_parsed : CheckedT f t B p ok p' ↔ ∃ v, ParsedT f t B p ok p' v := by
  unfold CheckedT ParsedT
  rw [Fmt.checkT_eq]
  cases h : f.parseT t (B.drop p.toNat) with
  | none => exact ⟨fun h => ⟨.unit, h⟩, fun ⟨_, h⟩ => h⟩
  | some r =>
    obtain ⟨w, rest⟩ := r
    exact ⟨fun h => ⟨w, h.1, h.2, rfl⟩, fun ⟨_, h1, h2, _⟩ => ⟨h1, h2⟩⟩

theorem of_parsed {v : Val} (h : ParsedT f t B p ok p' v) : CheckedT f t B p ok p' :=
  iff_parsed.mpr ⟨v, h⟩

end CheckedT

theorem Checked.pair_stop {a b : Fmt} {B : List UInt8} {p p1 p' : UInt64} {t : Nat}
    (ha : Checked a B p false p1) : CheckedT (.pair a b) t B p false p' := by
  obtain ⟨va, ha⟩ := CheckedT.iff_parsed.mp ha
  exact CheckedT.of_parsed (Parsed.pair_stop (v := .unit) ha)

theorem Checked.pair_cont {a b : Fmt} {B : List UInt8} {p p1 p2 : UInt64} {ok : Bool} {t : Nat}
    (hp : p.toNat ≤ B.length) (ha : Checked a B p true p1) (hb : Checked b B p1 ok p2) :
    CheckedT (.pair a b) t B p ok p2 := by
  obtain ⟨va, ha⟩ := CheckedT.iff_parsed.mp ha
  obtain ⟨vb, hb⟩ := CheckedT.iff_parsed.mp hb
  exact CheckedT.of_parsed (Parsed.pair_cont hp ha hb)

theorem Checked.union_stop {k : Nat} {e : Endian} {arms : Fmt} {B : List UInt8} {p p1 p' : UInt64}
    {vt : Val} {t : Nat} (ht : Parsed (.uint k e) B p false p1 vt) :
    CheckedT (.union k e arms) t B p false p' :=
  CheckedT.of_parsed (Parsed.union_stop (v := .unit) ht)

theorem Checked.union_cont {k : Nat} {e : Endian} {arms : Fmt} {B : List UInt8} {p p1 p2 : UInt64}
    {tg : Nat} {ok : Bool} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num tg)) (ha : CheckedT arms tg B p1 ok p2) :
    CheckedT (.union k e arms) t B p ok p2 := by
  obtain ⟨v, ha⟩ := CheckedT.iff_parsed.mp ha
  exact CheckedT.of_parsed (Parsed.union_cont hp ht ha)

theorem CheckedT.arm_eq {tag : Nat} {f rest : Fmt} {t : Nat} {B : List UInt8} {p p' : UInt64}
    {ok : Bool} : CheckedT (.arm tag f rest) t B p ok p' =
      if t = tag then Checked f B p ok p' else CheckedT rest t B p ok p' := by
  by_cases ht : t = tag <;> simp only [CheckedT, Fmt.checkT, ht, ite_true, ite_false]

theorem CheckedT.noArm {t : Nat} {B : List UInt8} {p p' : UInt64} :
    CheckedT .noArm t B p false p' := rfl

theorem CheckedT.unit {t : Nat} {B : List UInt8} {p : UInt64} (hp : p.toNat ≤ B.length) :
    CheckedT .unit t B p true p := CheckedT.of_parsed (ParsedT.unit hp)

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN

set_option mp.autoSpec false in
/-- Check that an integer of `k` bytes is at `pos`, and move past it. -/
mp def checkUint (s : &[UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool)
    requires pos.toNat ≤ s.len.toNat
    ensures Checked (.uint k.toNat (endian big)) (Slots.bytes s s.len.toNat) pos result pos' ∧
      (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < k then return false
  pos := p + k
  true

set_option mp.autoSpec false in
/-- Check that a byte string with a length of `k ≤ 8` bytes, at most `max`, is at `pos`, and move
past it. -/
mp def checkLBytes (s : &[UInt8; N]) (pos : &mut UInt64) (k : UInt64) (big : Bool) (max : UInt64)
    requires pos.toNat ≤ s.len.toNat ∧ k.toNat ≤ 8
    ensures Checked (.lbytes k.toNat (endian big) max.toNat) (Slots.bytes s s.len.toNat) pos result
      pos' ∧ (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < k then return false
  let n := getU (&s) p k big
  if n > max then return false
  let q := p + k
  if s.len - q < n then return false
  pos := q + n
  true
end

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
mp prove checkUint.spec := by
  intro s sl pos k big
  vcgen [checkUint]
  all_goals obtain ⟨hp, -, -⟩ := ‹_ ∧ _›
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    simp only [CheckedT, Fmt.checkT, List.length_drop, Slots.bytes_length,
      show ¬ (k.toNat ≤ sl.toNat - pos.toNat) by omega, ite_false]
  case vc2 hk' =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    refine ⟨?_, fun _ => by rw [hpk]; omega⟩
    simp only [CheckedT, Fmt.checkT, List.length_drop, Slots.bytes_length,
      show k.toNat ≤ sl.toNat - pos.toNat by omega, ite_true, hpk]
    simp; omega
mp prove checkLBytes.spec := by
  intro s sl pos k big max
  vcgen [checkLBytes]
  all_goals obtain ⟨⟨hp, hk⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    simp only [CheckedT, Fmt.checkT, readUint_drop_none (show pos.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
      (show (Slots.bytes s sl.toNat).length < pos.toNat + k.toNat by simp; omega)]
  case vc2 hk' => exact ⟨⟨by omega, hk⟩, hsl, hf⟩
  case vc3 n _ hn hk' hmax =>
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    refine ⟨?_, by simp⟩
    simp only [CheckedT, Fmt.checkT, hrd, ← hn]
    rw [ite_eq_right (by omega)]
    trivial
  case vc4 n _ hn hk' _ hroom =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hpk] at hroom
    refine ⟨?_, by simp⟩
    simp only [CheckedT, Fmt.checkT, hrd, ← hn]
    rw [ite_eq_right (by simp; omega)]
    trivial
  case vc5 n _ hn hk' hmax hroom =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    have hrd := readUint_drop_some (e := endian big) (show pos.toNat + k.toNat ≤ (Slots.bytes s sl.toNat).length by simp; omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hpk] at hroom
    have hq : (pos + k + n).toNat = pos.toNat + k.toNat + n.toNat := by
      rw [toNat_add_of_le (a := pos + k) (b := n) (c := sl) (by rw [hpk]; omega), hpk]
    refine ⟨?_, fun _ => by rw [hq]; omega⟩
    simp only [CheckedT, Fmt.checkT, hrd, ← hn]
    rw [ite_eq_left (by simp; omega)]
    simp [hq]; omega
end
end Millipede.Format
