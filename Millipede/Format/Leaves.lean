import Millipede.Format.Code

/-!
# Format descriptions: the leaves `bytes`, `skip` and `const`

The Millipede code of the leaves that the key-value messages do not use, in the calling convention
of `Millipede/Format/Code.lean`.

- `parseBytes`, `writeBytes` and `checkBytes` read, write and check `bytes n` held in the first `n`
  elements of an array.
- `skipBytes` reads `skip n`, which it checks too, and `writeSkip` writes it as zeros, for
  `n ≤ 8`.
- `parseConst` reads and checks `const l`, and `writeConst` writes it, for a constant of at most 8
  bytes given as the big-endian number `v` of `k` bytes: `l = encUint k .big v`.
-/

namespace Millipede.Format

open Millipede Std.WP

set_option experimental.vcgen true

/-- The `k` big-endian bytes of `0` are zeros. -/
theorem encUint_zero (k : Nat) (e : Endian) : encUint k e 0 = List.replicate k 0 := by
  have : leBytes k 0 = List.replicate k 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [leBytes, ih, List.replicate_succ]
  cases e <;> simp [encUint, this]

/-- Room for `k` bytes after `pos`, against the bytes left. -/
theorem room_iff {B : List UInt8} {pos : Nat} {k : Nat} (hp : pos ≤ B.length) :
    k ≤ (B.drop pos).length ↔ pos + k ≤ B.length := by simp; omega

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM

set_option mp.autoSpec false in
/-- Parse `n ≤ M` bytes at `pos` into the first `n` elements of `out`. -/
mp def parseBytes (s : &[UInt8; N]) (pos : &mut UInt64) (n : UInt64) (out : &mut Arr UInt8 M)
    requires pos.toNat ≤ s.len.toNat ∧ n.toNat ≤ M
    ensures Parsed (.bytes n.toNat) (Slots.bytes s s.len.toNat) pos result pos'
      (.bytes (out'.toList.take n.toNat)) ∧ (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < n then return false
  let _ := getBytes (&s) p n (&mut out)
  pos := p + n
  true

set_option mp.autoSpec false in
/-- Write the first `n ≤ M` elements of `src` at `pos`. -/
mp def writeBytes (d : &mut [UInt8; N]) (pos : &mut UInt64) (n : UInt64) (src : &Arr UInt8 M)
    requires pos.toNat + n.toNat ≤ d.len.toNat ∧ n.toNat ≤ M
    ensures pos'.toNat = pos.toNat + n.toNat ∧
      Written (.bytes n.toNat) d d' pos pos' (.bytes (src.toList.take n.toNat)) : Unit := do
  let p := pos
  let _ := putBytes (&mut d) p (&src) n
  pos := p + n
end

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN

set_option mp.autoSpec false in
/-- Check that `n` bytes are at `pos`, and move past them. -/
mp def checkBytes (s : &[UInt8; N]) (pos : &mut UInt64) (n : UInt64)
    requires pos.toNat ≤ s.len.toNat
    ensures Checked (.bytes n.toNat) (Slots.bytes s s.len.toNat) pos result pos' ∧
      (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < n then return false
  pos := p + n
  true

set_option mp.autoSpec false in
/-- Read `n` ignored bytes at `pos`. -/
mp def skipBytes (s : &[UInt8; N]) (pos : &mut UInt64) (n : UInt64)
    requires pos.toNat ≤ s.len.toNat
    ensures Parsed (.skip n.toNat) (Slots.bytes s s.len.toNat) pos result pos' .unit ∧
      (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < n then return false
  pos := p + n
  true

set_option mp.autoSpec false in
/-- Write `k ≤ 8` ignored bytes, as zeros, at `pos`. -/
mp def writeSkip (d : &mut [UInt8; N]) (pos : &mut UInt64) (k : UInt64)
    requires pos.toNat + k.toNat ≤ d.len.toNat ∧ k.toNat ≤ 8
    ensures pos'.toNat = pos.toNat + k.toNat ∧ Written (.skip k.toNat) d d' pos pos' .unit :
      Unit := do
  let p := pos
  let _ := putU (&mut d) p k true 0
  pos := p + k

set_option mp.autoSpec false in
/-- Read the constant of the `k ≤ 8` big-endian bytes of `v` at `pos`. -/
mp def parseConst (s : &[UInt8; N]) (pos : &mut UInt64) (k : UInt64) (v : UInt64)
    requires pos.toNat ≤ s.len.toNat ∧ k.toNat ≤ 8 ∧ v.toNat < 256 ^ k.toNat
    ensures Parsed (.const (encUint k.toNat .big v.toNat)) (Slots.bytes s s.len.toNat) pos result
      pos' .unit ∧ (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do
  let p := pos
  if s.len - p < k then return false
  let x := getU (&s) p k true
  if x != v then return false
  pos := p + k
  true

set_option mp.autoSpec false in
/-- Write the constant of the `k ≤ 8` big-endian bytes of `v` at `pos`. -/
mp def writeConst (d : &mut [UInt8; N]) (pos : &mut UInt64) (k : UInt64) (v : UInt64)
    requires pos.toNat + k.toNat ≤ d.len.toNat ∧ k.toNat ≤ 8 ∧ v.toNat < 256 ^ k.toNat
    ensures pos'.toNat = pos.toNat + k.toNat ∧
      Written (.const (encUint k.toNat .big v.toNat)) d d' pos pos' .unit : Unit := do
  let p := pos
  let _ := putU (&mut d) p k true v
  pos := p + k
end

section
variable (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64)
include hN hM
mp prove parseBytes.spec := by
  intro s sl pos n out
  vcgen [parseBytes]
  all_goals obtain ⟨⟨hp, hn⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, List.length_drop, Slots.bytes_length]
    rw [ite_eq_right (by omega)]
  case vc2 hk' => exact ⟨⟨by omega, hn⟩, hsl, hf⟩
  case vc3 _ o _ hv hk' =>
    have hpk : (pos + n).toNat = pos.toNat + n.toNat := toNat_add_of_le (c := sl) (by omega)
    refine ⟨ParsedT.of_some ?_ (by simp; omega), fun _ => by rw [hpk]; omega⟩
    simp only [Fmt.parseT, List.length_drop, Slots.bytes_length]
    rw [ite_eq_left (by omega), take_toList_eq (len := sl.toNat) hv hn (by omega), hpk, List.drop_drop,
      Nat.add_comm]
mp prove writeBytes.spec := by
  intro d dl pos n src
  vcgen [writeBytes]
  all_goals obtain ⟨⟨hp, _hn⟩, _hsl, _hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  case vc1 _ st _ hw =>
    have hpk : (pos + n).toNat = pos.toNat + n.toNat := toNat_add_of_le (c := dl) (by omega)
    have hl : (src.toList.take n.toNat).length = n.toNat := by simp; omega
    exact ⟨hpk, by simp [Fmt.writeT, hpk, hl], by simpa [Fmt.writeT] using hw⟩
end

section
variable (N : Nat) (hN : N < 2 ^ 64)
include hN
mp prove checkBytes.spec := by
  intro s sl pos n
  vcgen [checkBytes]
  all_goals obtain ⟨hp, -, -⟩ := ‹_ ∧ _›
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    simp only [CheckedT, Fmt.checkT, List.length_drop, Slots.bytes_length,
      show ¬ (n.toNat ≤ sl.toNat - pos.toNat) by omega, ite_false]
  case vc2 hk' =>
    have hpk : (pos + n).toNat = pos.toNat + n.toNat := toNat_add_of_le (c := sl) (by omega)
    refine ⟨?_, fun _ => by rw [hpk]; omega⟩
    simp only [CheckedT, Fmt.checkT, List.length_drop, Slots.bytes_length,
      show n.toNat ≤ sl.toNat - pos.toNat by omega, ite_true, hpk]
    simp; omega
mp prove skipBytes.spec := by
  intro s sl pos n
  vcgen [skipBytes]
  all_goals obtain ⟨hp, -, -⟩ := ‹_ ∧ _›
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, List.length_drop, Slots.bytes_length]
    rw [ite_eq_right (by omega)]
  case vc2 hk' =>
    have hpk : (pos + n).toNat = pos.toNat + n.toNat := toNat_add_of_le (c := sl) (by omega)
    refine ⟨ParsedT.of_some ?_ (by simp; omega), fun _ => by rw [hpk]; omega⟩
    simp only [Fmt.parseT, List.length_drop, Slots.bytes_length]
    rw [ite_eq_left (by omega), hpk, List.drop_drop, Nat.add_comm]
mp prove writeSkip.spec := by
  intro d dl pos k
  vcgen [writeSkip]
  all_goals obtain ⟨⟨hp, _hk⟩, _hsl, _hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  case vc1 _ st _ hw =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := dl) (by omega)
    simp only [endian, ite_true, UInt64.toNat_zero, encUint_zero] at hw
    exact ⟨hpk, by simp [Fmt.writeT, hpk], by simpa [Fmt.writeT] using hw⟩
mp prove parseConst.spec := by
  intro s sl pos k v
  vcgen [parseConst]
  all_goals obtain ⟨⟨hp, hk, hv⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hp)] at *
  case vc1 hk' =>
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, encUint_length]
    rw [ite_eq_right]
    intro h
    have := congrArg List.length h
    simp at this; omega
  case vc2 hk' => exact ⟨⟨by omega, hk⟩, hsl, hf⟩
  case vc4 x _ hx hne _ =>
    refine ⟨?_, by simp⟩
    apply ParsedT.of_none
    simp only [Fmt.parseT, encUint_length]
    rw [ite_eq_right]
    intro h
    apply hne
    apply UInt64.toNat_inj.mp
    rw [hx, h]
    simpa [endian] using decUint_encUint k.toNat .big v.toNat hv
  case vc3 x _ hx hne hk' =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := sl) (by omega)
    subst hne
    refine ⟨ParsedT.of_some ?_ (by simp; omega), fun _ => by rw [hpk]; omega⟩
    have hwin := Slots.bytes_window_length s (show pos.toNat + k.toNat ≤ sl.toNat by omega)
    have he : encUint k.toNat .big x.toNat =
        ((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat := by
      rw [hx]
      simpa [endian, hwin] using encUint_decUint .big (((Slots.bytes s sl.toNat).drop pos.toNat).take k.toNat)
    simp only [Fmt.parseT, encUint_length]
    rw [ite_eq_left he.symm, hpk, List.drop_drop, Nat.add_comm]
mp prove writeConst.spec := by
  intro d dl pos k v
  vcgen [writeConst]
  all_goals obtain ⟨⟨hp, hk, _hv⟩, hsl, hf⟩ := ‹(_ ∧ _) ∧ _›
  all_goals try dsimp only at *
  case vc1 => exact ⟨⟨hp, hk⟩, hsl, hf⟩
  case vc2 _ st _ hw =>
    have hpk : (pos + k).toNat = pos.toNat + k.toNat := toNat_add_of_le (c := dl) (by omega)
    simp only [endian, ite_true] at hw
    exact ⟨hpk, by simp [Fmt.writeT, hpk], by simpa [Fmt.writeT] using hw⟩
end

end Millipede.Format
