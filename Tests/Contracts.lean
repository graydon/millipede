import Millipede.Meta.MpDef

/-!
# Tests of contracts

A function `mp def f … requires P ensures Q` gets the triple `f.spec`, which is
`⦃P⦄ f x ⦃fun r => Q⦄` over the result `result` and the final values `p'` of its `&mut`
parameters, and `f.post`, the same fact about the value. These tests check both statements for a pure function, a function
with a `&mut` parameter and an effectful one. The contracts are proved automatically. A caller's
contract is proved through the callee's contract without unfolding the callee, and a caller's
obligations are discharged from the callee's `ensures`. A contract that needs a loop invariant is
proved with `mp prove f.spec`.

A false `ensures` is not proved and its goal is refuted, and a call that violates `requires`
leaves an obligation that is refuted too. The statement checks were shown by hand to catch two
seeded bugs, dropping `requires` from the precondition of `f.spec` and swapping `result` with a
`&mut` output. Leaving the callees' contracts out of the automatic attempt leaves `twice.safe`
unproved.
-/

namespace Millipede.Tests.Contracts

open Millipede Std.WP

set_option experimental.vcgen true

mp def inc (x : UInt64) requires x.toNat < 10 ensures result.toNat = x.toNat + 1 : UInt64 :=
  x + 1

example : ∀ x : UInt64, ⦃x.toNat < 10⦄ inc x ⦃fun r => r.1.toNat = x.toNat + 1⦄ := inc.spec
example : ∀ x : UInt64, x.toNat < 10 → (inc x).run.1.toNat = x.toNat + 1 := inc.post

/-- The `requires` of the second call, `y < 10`, follows from the `ensures` of the first call. -/
mp def twice (x : UInt64) requires x.toNat < 5 ensures result.toNat = x.toNat + 2 : UInt64 :=
  let y := inc x
  inc y

example : ∀ ω w (x : UInt64), x.toNat < 5 → twice.exp.safe ω (.cons x .nil) w := twice.safe

/-- A caller's proof through the callee's contract, in which `vcgen` does not unfold `inc`. -/
example (x : UInt64) : ⦃x.toNat < 3⦄ twice x ⦃fun r => r.1.toNat < 6⦄ := by
  vcgen [twice]
  all_goals grind

/-- A function with a `&mut` parameter `p`, whose final value is `p'`. -/
structure P where
  x : UInt64
  y : UInt64
deriving Data

mp def bump (p : &mut P) (d : UInt64) requires d.toNat < 3 ∧ p.x.toNat < 100
    ensures p'.x.toNat = p.x.toNat + d.toNat ∧ p'.y = p.y ∧ result = d : UInt64 := do
  p.x := p.x + d
  d

example : ∀ (p : P) (d : UInt64), ⦃d.toNat < 3 ∧ p.x.toNat < 100⦄ bump p d
    ⦃fun r => r.2.1.x.toNat = p.x.toNat + d.toNat ∧ r.2.1.y = p.y ∧ r.1 = d⦄ := bump.spec

/-- An effectful function, whose contract holds from every world. -/
mp extern "read" sysRead (fd : UInt64) (buf : OutByte) : UInt64

mp def rd (x : UInt64) requires x.toNat < 10 ensures result.toNat ≤ x.toNat + 1 : UInt64 :=
  let c := sysRead 0
  if c < 256 then x + 1 else x

example : ∀ ω (x : UInt64), ⦃fun _ => x.toNat < 10⦄ rd ω x ⦃fun r _ => r.1.toNat ≤ x.toNat + 1⦄ :=
  rd.spec
example : ∀ ω w (x : UInt64), x.toNat < 10 → ((rd ω x).run w).1.1.toNat ≤ x.toNat + 1 := rd.post

/-! ## A contract that needs an invariant -/

/-- info: the contract of `count4` was not proved automatically: a loop needs an invariant (a fact about the counters done, the counters left and the carried value, true before and after every iteration; the postcondition at the carried value was tried and is not one). Prove it with
  mp prove count4.spec := by
    intro x; vcgen [count4] invariants
    · fun done left acc => …
    all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind
(`range_split`: the counter is below the bound; the goal is `count4.SpecGoal`); left:
⊢ ?inv1 [] (List.range 4) 0 -/
#guard_msgs in
mp def count4 (x : UInt64) ensures result = 4 : UInt64 := do
  let mut acc := 0
  for i in 0...4 do
    acc := acc + 1
  acc

mp prove count4.spec := by
  intro x
  vcgen [count4] invariants
  · fun done _ acc => acc.toNat = done.length
  all_goals (try have := range_split ‹List.range 4 = _›); grind

example : ∀ x : UInt64, (count4 x).run = 4 := count4.post

/-! ## A false `ensures` -/

/-- info: the contract of `bad` was not proved automatically; prove it with `mp prove bad.spec := …` (the goal is `bad.SpecGoal`); left:
x : UInt64
a_3 : UInt64
a : x.toNat < 5
a_2 : a_1.toNat = x.toNat + 1
a_4 : a_3.toNat = a_1.toNat + 1
⊢ a_3.toNat = x.toNat + 3 -/
#guard_msgs in
mp def bad (x : UInt64) requires x.toNat < 5 ensures result.toNat = x.toNat + 3 : UInt64 :=
  let y := inc x
  inc y

/-- error: Unknown constant `Millipede.Tests.Contracts.bad.spec` -/
#guard_msgs in
#check @bad.spec

/-- The goal left is false. -/
example : ¬ bad.SpecGoal := fun h => by
  have := Spec.run_of_triple (h 0) (by decide)
  revert this; decide

/-! ## A call that violates `requires` -/

/-- info: the obligations of `badcall` were not discharged automatically; prove them with `mp prove badcall.safe := …` (the goal is `badcall.SafeGoal`); left:
x : UInt64
⊢ x.toNat < 10 -/
#guard_msgs in
mp def badcall (x : UInt64) : UInt64 := inc x

/-- The obligation left, for `inc 20`, is false. -/
example (ω : Oracle) : ¬ badcall.SafeGoal := fun h => by
  have := h ω World.init 20
  simp [badcall.exp, Exp.safe, inc.req, RArgs.denote, Atom.denote] at this

/-! ## Names that `ensures` binds

A parameter may not be named `result`, or `p'` when `p` is a `&mut` parameter, because `ensures`
binds these names. -/

/-- error: a function with `ensures` cannot have a parameter named `result`: in `ensures`, `result` is the value returned -/
#guard_msgs in
mp def resP (result : UInt64) ensures result = 3 : UInt64 := 3

/-- error: a function with `ensures` cannot have a parameter named `p'`: in `ensures`, `p'` is the final value of the `&mut` parameter `p` -/
#guard_msgs in
mp def primeP (p : &mut P) (p' : UInt64) ensures p'.x = p.x : Unit := ()

/-! ## An unknown closer of `mp_safe … using` is an error -/

/-- error: Unknown identifier `noSuchLemma.Safe'` -/
#guard_msgs in
example : twice.SafeGoal := by
  intro ω w x h
  mp_safe [twice.exp, inc.req] using noSuchLemma.Safe', inc.Safe' grind [inc.post]

/-! ## `mp prove` chooses what to prove by its target -/

/-- error: `mp prove` proves `f.safe`, `f.spec`, `p.inv_init` or `p.inv_step` -/
#guard_msgs in
mp prove twice.bogus := trivial

/-- error: `Millipede.Tests.Contracts.inc.spec` is already proved -/
#guard_msgs in
mp prove inc.spec := inc.spec

end Millipede.Tests.Contracts
