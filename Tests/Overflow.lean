import Millipede.Meta.MpDef
import Millipede.Meta.Report

/-!
# Tests for the three forms of `+ - *` and the analyser in `mp def`

The plain operators wrap with no obligation, the `!` forms carry the obligation that the result
fits, and the `?` forms check it and return a `Result`. This suite proves that the normal forms
of the checked forms equal the Lean functions `CheckedArith.addChk` and its siblings on words
and bytes. It shows that the obligation is real, since a function whose `+!` may overflow has no
`f.safe` while the same function with `+` is total.

`mp def` tries the interval analyser first, which reads `requires` bounds as input intervals.
When the analyser certifies a function, `f.analysed` exists and `f.safe` follows from it, and
otherwise `mp_safe` is tried. The suite also checks that the automatic attempt gives up within
its kernel budget, and counts the indices that come from wrapping arithmetic.

The three forms are described in doc/design/obligations.md.
-/

namespace Millipede.Tests.Overflow

open Millipede Std.WP

set_option experimental.vcgen true

/-! ## Checked forms -/

mp def addC (x y : UInt64) : Result Unit UInt64 := x +? y
mp def subC (x y : UInt64) : Result Unit UInt64 := x -? y
mp def mulC (x y : UInt64) : Result Unit UInt64 := x *? y
mp def addC8 (x y : UInt8) : Result Unit UInt8 := x +? y
mp def subC8 (x y : UInt8) : Result Unit UInt8 := x -? y
mp def mulC8 (x y : UInt8) : Result Unit UInt8 := x *? y

/-- The check of `*?`, which says that for `x ≠ 0` the wrapped product divided by `x` is `y`
exactly when the product fits. -/
theorem mul_check (x y : Nat) (hx : 0 < x) :
    x * y % 2 ^ 64 / x = y ↔ x * y < 2 ^ 64 := by
  constructor
  · intro h
    have h1 : x * y ≤ x * y % 2 ^ 64 := by
      have := Nat.div_mul_le_self (x * y % 2 ^ 64) x
      rw [h, Nat.mul_comm] at this; exact this
    have := Nat.mod_lt (x * y) (show 0 < 2 ^ 64 by decide); omega
  · intro h; rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel_left _ hx]

theorem add_lt_iff (x y : UInt64) : x + y < x ↔ ¬ x.toNat + y.toNat < 2 ^ 64 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; have := x.toNat_lt; have := y.toNat_lt; omega

theorem addC_eq (x y : UInt64) : (addC x y).run = CheckedArith.addChk x y := by
  simp only [addC, CheckedArith.addChk, add_lt_iff]
  by_cases h : x.toNat + y.toNat < 2 ^ 64 <;> simp [h] <;> try rfl

theorem subC_eq (x y : UInt64) : (subC x y).run = CheckedArith.subChk x y := by
  simp only [subC, CheckedArith.subChk, UInt64.lt_iff_toNat_lt]
  split <;> split <;> first | rfl | (exfalso; omega)

theorem mulC_eq (x y : UInt64) : (mulC x y).run = CheckedArith.mulChk x y := by
  simp only [mulC, CheckedArith.mulChk]
  by_cases h0 : x = 0
  · subst h0; simp
  · have hx : 0 < x.toNat := by
      have : x.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
      omega
    have hc : x * y / x = y ↔ x.toNat * y.toNat < 2 ^ 64 := by
      rw [← mul_check x.toNat y.toNat hx, ← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_mul]
    by_cases h : x.toNat * y.toNat < 2 ^ 64 <;> simp [h0, hc, h] <;> try rfl

theorem add8_lt_iff (x y : UInt8) :
    255 < x.toUInt64 + y.toUInt64 ↔ ¬ x.toNat + y.toNat < 2 ^ 8 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64]
  have := x.toNat_lt; have := y.toNat_lt
  show 255 < _ ↔ _
  omega

theorem addC8_eq (x y : UInt8) : (addC8 x y).run = CheckedArith.addChk x y := by
  simp only [addC8, CheckedArith.addChk, add8_lt_iff]
  by_cases h : x.toNat + y.toNat < 2 ^ 8 <;> simp [h]

theorem subC8_eq (x y : UInt8) : (subC8 x y).run = CheckedArith.subChk x y := by
  simp only [subC8, CheckedArith.subChk, UInt8.lt_iff_toNat_lt]
  by_cases h : y.toNat ≤ x.toNat
  · have h2 : ¬ (255 : UInt64) < x.toUInt64 - y.toUInt64 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by simpa using h))]
      simp only [UInt8.toNat_toUInt64]; have := x.toNat_lt; show ¬ 255 < _; omega
    simp [h, h2, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

-- The checked forms on words and bytes, with both outcomes.
example : (addC 3 4).run = .ok 7 := rfl
example : (addC 0xFFFFFFFFFFFFFFFF 1).run = .error () := rfl
example : (subC 3 4).run = .error () := rfl
example : (subC 4 3).run = .ok 1 := rfl
example : (mulC 0x100000000 0x100000000).run = .error () := rfl
example : (mulC 0x100000000 0xFFFFFFFF).run = .ok 0xFFFFFFFF00000000 := rfl
example : (mulC 0 0xFFFFFFFFFFFFFFFF).run = .ok 0 := rfl
example : (addC8 200 55).run = .ok 255 := rfl
example : (addC8 200 56).run = .error () := rfl
example : (subC8 3 4).run = .error () := rfl
example : (mulC8 16 15).run = .ok 240 := rfl
example : (mulC8 16 16).run = .error () := rfl

-- The checked forms have no obligation.
example := @addC.safe
example := @mulC8.safe

/-! ## Wrapping and obligated forms -/

mp def addW (x y : UInt64) : UInt64 := x + y
mp def mulW8 (x y : UInt8) : UInt8 := x * y
example : (addW 0xFFFFFFFFFFFFFFFF 2).run = 1 := rfl
example : (mulW8 16 17).run = 16 := rfl
-- A wrapping operator has no obligation.
example := @addW.safe

-- `x +! y` on arbitrary words may overflow, so `mp def` cannot discharge it and `addO.safe` is
-- missing.
/-- info: the obligations of `addO` were not discharged automatically; prove them with `mp prove addO.safe := …` (the goal is `addO.SafeGoal`); left:
x : UInt64
y : UInt64
⊢ x.toNat + y.toNat < 18446744073709551616 -/
#guard_msgs in
mp def addO (x y : UInt64) : UInt64 := x +! y
/-- The obligation is exactly that the sum fits. -/
example (ω : Oracle) (w : World) (x y : UInt64) :
    addO.exp.safe ω (.cons y (.cons x .nil)) w ↔ x.toNat + y.toNat < 2 ^ 64 := by
  simp [addO.exp, Exp.safe, Prim.ok, Args.denote, Atom.denote]
-- A byte subtraction has the obligation that it does not go below zero.
/-- info: the obligations of `subO8` were not discharged automatically; prove them with `mp prove subO8.safe := …` (the goal is `subO8.SafeGoal`); left:
x : UInt8
y : UInt8
⊢ (x.toUInt64 - y.toUInt64).toNat < 256 -/
#guard_msgs in
mp def subO8 (x y : UInt8) : UInt8 := x -! y
example (ω : Oracle) (w : World) : ¬ subO8.exp.safe ω (.cons 4 (.cons 3 .nil)) w := by
  simp [subO8.exp, Exp.safe, Exp.denote, Prim.ok, Args.denote, Atom.denote, Prim.denote]

/-! ## The analyser in `mp def` -/

/-- A function the analyser certifies, so `counted.analysed` is its verdict and `counted.safe`
follows. -/
mp def counted (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    acc := acc +! (a[i] &&& 255)
  acc
example : counted.exp.safeBy [] = true := counted.analysed
example (ω : Oracle) (w : World) (a : Vector UInt64 8) : counted.exp.safe ω (.cons a .nil) w :=
  counted.safe ω w a

/-- `requires` bounds become input intervals. -/
mp def scaledReq (x : UInt64) requires x.toNat ≤ 1000 : UInt64 := x *! 1000
example := @scaledReq.analysed
example := @scaledReq.safe

/-- The analyser does not certify this function, because it does not relate the comparison of
two parameters to the index, but `mp_safe` proves the obligation from `requires`. -/
mp def viaMpSafe (a : Arr UInt64 8) (i j : UInt64) requires i.toNat < j.toNat ∧ j.toNat ≤ 8 :
    UInt64 := a[i]!
example := @viaMpSafe.safe

/-- The analyser never certifies a `Slots` cell, but it certifies the addition `k +! 1` from
`k ≤ 2`. The relaxed term, in which the addition wraps, goes to `mp_safe`, which proves the cell
full from `requires`. -/
mp def cellPlus (s : Slots UInt64 4) (k : UInt64) requires s.isFull k.toNat = true ∧ k.toNat ≤ 2 :
    UInt64 :=
  s[k]! + (k +! 1)
example := @cellPlus.relaxed
example := @cellPlus.safe
-- The relaxed term has no obligation for the addition.
example : (cellPlus.exp.relax (Analysis.AEnv.ofItvs [⟨0, 2⟩])).2 = [true] := by decide


/-- An operation with an obligation in the right operand of `&&` is evaluated only when the left
operand holds, so `i < 100` bounds `i +! 1` and the analyser certifies it. -/
mp def shortInc (i : UInt64) : Bool := i < 100 && i +! 1 < 50
example := @shortInc.analysed

/-! ## Contracts and generic definitions

A definition under `variable`s that it does not use takes none of them, so it is closed and its
`requires` bounds feed the analyser as usual. The analyser does not read a callee's `ensures`
bound, since it knows nothing of a call's result, but `mp_safe` uses it. -/

section
variable (k : Nat) (hk : k < 100)
/-- `x` in thousandths, for `x < 8`. -/
mp def Scaled.milli (x : UInt64) requires x.toNat < 8 : UInt64 := x *! 1000
end
example := @Scaled.milli.analysed

mp def dbl (x : UInt64) requires x.toNat < 8 ensures result.toNat < 16 : UInt64 := x +! x
example := @dbl.analysed

/-- The analyser does not certify this function, since it knows nothing of the result of `dbl`,
but `mp_safe` proves `y *! 4` from the contract of `dbl`. -/
mp def quad (x : UInt64) requires x.toNat < 8 : UInt64 :=
  let y := dbl x
  y *! 4
example := @quad.safe

/-- The analyser reads a bound on a `UInt64` parameter written `x < c` and certifies
`x *! 1000` from it alone. -/
mp def wordReq (x : UInt64) requires x < 100 : UInt64 := x *! 1000
example := @wordReq.analysed

mp def wordReqGe (x : UInt64) requires x ≥ 10 ∧ 20 > x : UInt64 := (x -! 10) *! (x +! 1)
example := @wordReqGe.analysed

/-! ## The automatic attempt gives up within its budget

Without the analyser, `mp_safe` finds a proof of the obligations of `fillOff` that is too
expensive for the kernel, because it unfolds the 1024-iteration loop over the 16 KiB array. The
proof is checked within `mp.autoSafe.kernelHeartbeats` and dropped. The check runs here with a
small budget, which it exceeds just as it exceeds the default one. -/

/-- info: the obligations of `fillOff` were not discharged automatically; prove them with `mp prove fillOff.safe := …` (the goal is `fillOff.SafeGoal`); left:
(the proof found is too expensive for the kernel, `mp.autoSafe.kernelHeartbeats`) -/
#guard_msgs in
set_option mp.autoSafe.kernelHeartbeats 1000 in
set_option mp.analyser false in
mp def fillOff (arena : Arr UInt8 16384) (pg : UInt64) (kib : UInt64) (v : UInt8)
    requires pg.toNat < 4 ∧ kib.toNat ≤ 4 : Arr UInt8 16384 := do
  let mut a := arena
  let base := pg *! 4096
  for k in 0...4 do
    if k ≥ kib then break
    let start := base +! k *! 1024
    for j in 0...1024 do
      a[start +! j]! := v
  a

-- A loop of 2^32 iterations has its normal form, checked by the kernel with the bound as a
-- variable (Tests/LoopBounds.lean).
set_option mp.autoSafe false in
mp def growW : UInt64 := do
  let mut acc := 0
  for i in 0...4294967296 do
    acc := acc + i
  acc
example := @growW.exp_run

/-! ## Wrapping arithmetic into an index

`Wraps.count`, which `#mp_report` prints for each function, counts the indices and slice bounds
that are the result of a wrapping `+ - *`. `nextW` indexes with `i + 1` and `nextO` with
`i +! 1`, and `maskW` masks a wrapping sum with `&&&`, which does not count. -/

set_option mp.autoSafe false in
mp def nextW (a : Arr UInt64 8) (i : UInt64) : UInt64 := let j := i + 1; a[j]!
set_option mp.autoSafe false in
mp def nextO (a : Arr UInt64 8) (i : UInt64) : UInt64 := let j := i +! 1; a[j]!
set_option mp.autoSafe false in
mp def maskW (a : Arr UInt64 8) (i : UInt64) : UInt64 := let j := (i + 1) &&& 7; a[j]!
set_option mp.autoSafe false in
mp def sliceW (b : Arr UInt8 16) (n : UInt64) : UInt64 :=
  let m := n * 2
  let r := &b[0..m]
  r.len

example : Wraps.count nextW.exp = 1 := by decide
example : Wraps.count nextO.exp = 0 := by decide
example : Wraps.count maskW.exp = 0 := by decide
example : Wraps.count sliceW.exp = 1 := by decide

end Millipede.Tests.Overflow
