import Millipede.Meta.MpDef

/-!
# Tests of the obligation analyser

The analyser is a verified interval analysis of Core terms. These tests check its transfer
functions on small cases, including those where a wrap is possible and the result is the full
interval, and division and remainder by zero. They check by kernel `decide` that it certifies the
programs it must certify, and that it does not certify a real possible overflow, an index off by
one, an accumulator that can pass `2^64` within the loop's bound, or a branch whose condition does
not imply the index bound. They also check the interval it gives a constant expression and a
loop's accumulator. `Tests/Overflow.lean` tests how `mp def` uses the analyser.

The suite was shown to catch seeded bugs in the analyser, each applied by hand, built and
reverted. A wrong upper bound in `wMul`, a `wSub` that ignores its side condition, a loop whose
candidate invariants are not checked inductive and a counter interval one short each break a
soundness proof. Dropping the widening keeps the proofs but makes the tests of `sumSmall`, `growOk`
and the bound of `sumSmall`'s value fail.
-/

namespace Millipede.Tests.Analysis

open Millipede Millipede.Analysis

/-! ## Transfer functions -/

example : wAdd ⟨1, 2⟩ ⟨3, 4⟩ = ⟨4, 6⟩ := by decide
example : wAdd ⟨0, wmax⟩ ⟨1, 1⟩ = Itv.top := by decide
example : wMul ⟨2, 3⟩ ⟨4, 5⟩ = ⟨8, 15⟩ := by decide
example : wMul ⟨0, 2 ^ 32⟩ ⟨0, 2 ^ 32⟩ = Itv.top := by decide
example : wSub true ⟨10, 20⟩ ⟨1, 5⟩ = ⟨5, 19⟩ := by decide
example : wSub false ⟨10, 20⟩ ⟨1, 5⟩ = Itv.top := by decide
example : wDiv ⟨10, 20⟩ ⟨2, 5⟩ = ⟨2, 10⟩ := by decide
-- the divisor may be `0`, and `x / 0 = 0`, so the result starts at `0`
example : wDiv ⟨10, 20⟩ ⟨0, 5⟩ = ⟨0, 20⟩ := by decide
example : wMod ⟨0, 100⟩ ⟨1, 8⟩ = ⟨0, 7⟩ := by decide
-- `x % 0 = x`
example : wMod ⟨0, 100⟩ ⟨0, 8⟩ = ⟨0, 100⟩ := by decide
example : wAnd ⟨0, wmax⟩ ⟨255, 255⟩ = ⟨0, 255⟩ := by decide
example : wShr ⟨1024, 4096⟩ ⟨10, 10⟩ = ⟨1, 4⟩ := by decide
example : wShl ⟨1, 3⟩ ⟨12, 12⟩ = ⟨4096, 12288⟩ := by decide
example : wShl ⟨1, 2 ^ 60⟩ ⟨12, 12⟩ = Itv.top := by decide
example : wTrunc8 ⟨0, 300⟩ = Itv.top8 := by decide
example : wTrunc8 ⟨3, 200⟩ = ⟨3, 200⟩ := by decide
-- the concrete products at the corners are inside the computed interval
example : ∀ x ∈ [2, 3], ∀ y ∈ [4, 5], (wMul ⟨2, 3⟩ ⟨4, 5⟩).lo ≤ x * y ∧ x * y ≤ (wMul ⟨2, 3⟩ ⟨4, 5⟩).hi := by
  decide

/-! ## Programs -/

-- the tests call the analyser directly
set_option mp.autoSafe false

/-- A sum of the counter, at most `99 · 100 / 2`, whose accumulator's bound comes from the loop
bound. -/
mp def sumSmall : UInt64 := do
  let mut acc := 0
  for i in 0...100 do
    acc := acc +! i
  acc
example : sumSmall.exp.safeBy [] = true := by decide

/-- A sum of arbitrary words, which can really overflow and is not certified. -/
mp def sumAny (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    acc := acc +! a[i]
  acc
example : sumAny.exp.safeBy [] = false := by decide

/-- Sixteen additions of values below `2^60`, which stay at most `2^64 - 16` and are certified. -/
mp def growOk (a : Arr UInt64 16) : UInt64 := do
  let mut acc := 0
  for i in 0...16 do
    acc := acc +! (a[i] &&& 1152921504606846975)
  acc
example : growOk.exp.safeBy [] = true := by decide

/-- Seventeen such additions can exceed `2^64`, so they are not certified. -/
mp def overGrow (a : Arr UInt64 17) : UInt64 := do
  let mut acc := 0
  for i in 0...17 do
    acc := acc +! (a[i] &&& 1152921504606846975)
  acc
example : overGrow.exp.safeBy [] = false := by decide

/-- A product of bounded values. -/
mp def mulBound (x y : UInt64) : UInt64 := (x &&& 65535) *! (y &&& 65535)
example : mulBound.exp.safeBy [] = true := by decide

/-- Nine iterations over an array of eight, whose last index is out of range. -/
mp def offByOne (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...9 do
    acc := acc + a[i]!
  acc
example : offByOne.exp.safeBy [] = false := by decide

mp def inRange (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    acc := acc + a[i]!
  acc
example : inRange.exp.safeBy [] = true := by decide

/-- At a branch the condition `i < 8` refines the interval and bounds the index. -/
mp def guarded (a : Arr UInt64 8) (i : UInt64) : UInt64 := if i < 8 then a[i]! else 0
example : guarded.exp.safeBy [] = true := by decide

/-- `i ≤ 8` does not. -/
mp def guardedOff (a : Arr UInt64 8) (i : UInt64) : UInt64 := if i ≤ 8 then a[i]! else 0
example : guardedOff.exp.safeBy [] = false := by decide

/-- `y ≤ x` on the path certifies `x - y`, which is not certified without it. -/
mp def subGuard (x y : UInt64) : UInt64 := if y ≤ x then x -! y else 0
example : subGuard.exp.safeBy [] = true := by decide
mp def subBad (x y : UInt64) : UInt64 := if y ≤ x + 1 then x -! y else 0
example : subBad.exp.safeBy [] = false := by decide

/-- An input interval, which is how `requires` enters the analysis, certifies `x * 1000` when
`x ≤ 1000`. -/
mp def scaled (x : UInt64) : UInt64 := x *! 1000
example : scaled.exp.safeBy [⟨0, 1000⟩] = true := by decide
example : scaled.exp.safeBy [] = false := by decide

/-- A nested loop over the pages of a buffer, in which `k * 1024 + j < 4096`. -/
mp def zeroKiB (buf : Arr UInt8 4096) (n : UInt64) : Arr UInt8 4096 := do
  let mut a := buf
  for k in 0...4 do
    if k ≥ n then break
    for j in 0...1024 do
      a[k *! 1024 +! j]! := 0
  a
example : zeroKiB.exp.safeBy [] = true := by decide

/-- In byte arithmetic the obligation is the narrowing of the word result. -/
mp def byteMask (b : UInt8) : UInt8 := (b &&& 127) +! 100
example : byteMask.exp.safeBy [] = true := by decide
mp def byteOver (b : UInt8) : UInt8 := (b &&& 127) +! 200
example : byteOver.exp.safeBy [] = false := by decide

/-! ## Values -/

/-- A constant expression is a point. -/
mp def constant : UInt64 := let x := 6; let y := x *! 7; y +! 0
example : (constant.exp.an {}).v.w = ⟨42, 42⟩ := by decide

/-- The accumulator of `sumSmall` after the loop is at most `0 + 99 · 100`. -/
example : (sumSmall.exp.an {}).v.w.hi ≤ 9900 := by decide

end Millipede.Tests.Analysis
