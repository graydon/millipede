import Millipede.Meta.MpDef

/-!
# Tests for `mp program … invariant I`

`mp program` with an invariant generates the goals `p.InvInitGoal` and `p.InvStepGoal`, which
this suite checks against their expected statements, for pure and for effectful `init` and
`step`. When the goals are proved automatically, `p.inv` and `p.safe` follow with no user proof.
An invariant the automation cannot prove is proved with `mp prove p.inv_step`, and `p.safe`
follows from it. Without an invariant, `p.safe` exists for a `step` without `requires`, and a
`step` with one gets a message.

An invariant that `step` does not keep, and one too weak for the step's `requires`, are not
proved, `p.safe` does not exist for them, and their goals are refuted. Two seeded bugs were
checked by hand. Dropping `I r → R r` from `p.InvStepGoal` makes the derivation of `cProg.safe`
fail, and stating the step goal over the initial root instead of the final one breaks the check
of the statement.

Root invariants are described in doc/design/obligations.md.
-/

namespace Millipede.Tests.ProgramInv

open Millipede Std.WP

set_option experimental.vcgen true

/-- A counter that stays below 10. -/
structure C where
  n : UInt64
  hits : UInt64
deriving Data

mp def cInit : C := { n := 0, hits := 0 }

mp def cStep (r : &mut C) requires r.n.toNat < 10 ensures r'.n.toNat < 10 : Unit := do
  let a := r.n
  let a2 := if a < 9 then a + 1 else 0
  r.n := a2
  ()

mp program cProg (root : C) init cInit step cStep invariant fun r => r.n.toNat < 10

example : cProg.InvInitGoal = ⦃True⦄ cInit ⦃fun r => r.n.toNat < 10⦄ := rfl
example : cProg.InvStepGoal = ∀ r : C,
    (r.n.toNat < 10 → r.n.toNat < 10) ∧ ⦃r.n.toNat < 10⦄ cStep r ⦃fun x => x.2.1.n.toNat < 10⦄ := rfl
example : ∀ ω n, (cProg.run ω n).1.n.toNat < 10 := cProg.inv
example : cProg.Safe := cProg.safe

/-! ## Effectful `init` and `step` -/

mp extern "write" sysWrite (fd : UInt64) (buf : Bytes) : UInt64
mp extern "read" sysRead (fd : UInt64) (buf : OutByte) : UInt64

mp def eInit : C :=
  let _w := sysWrite 1 "hi\n"
  { n := 0, hits := 0 }

/-- Counts the input bytes, saturating at 9. -/
mp def eStep (r : &mut C) requires r.n.toNat < 10 : Unit := do
  let c := sysRead 0
  if c < 256 then
    if r.n < 9 then
      r.n := r.n + 1
      ()
    else ()
  else ()

mp program eProg (root : C) init eInit step eStep invariant fun r => r.n.toNat < 10

example : eProg.InvStepGoal = ∀ ω (r : C), (r.n.toNat < 10 → r.n.toNat < 10) ∧
    ⦃fun _ => r.n.toNat < 10⦄ eStep ω r ⦃fun x _ => x.2.1.n.toNat < 10⦄ := rfl
example : ∀ ω n, (eProg.run ω n).1.n.toNat < 10 := eProg.inv
example : eProg.Safe := eProg.safe

/-! ## An invariant proved by hand: `mp prove p.inv_step` -/

/-- A predicate that the automation does not unfold here, because `twoProg` is declared under
`mp.unfoldPreds false`. -/
def Even64 (x : UInt64) : Prop := x.toNat % 2 = 0

mp def twoStep (r : &mut C) requires Even64 r.n : Unit := do
  r.n := r.n + 2
  ()

/-- info: `twoProg.inv_init` was not proved automatically; prove it with `mp prove twoProg.inv_init := …` (the goal is `Millipede.Tests.ProgramInv.twoProg.InvInitGoal`)
---
info: `twoProg.inv_step` was not proved automatically; prove it with `mp prove twoProg.inv_step := …` (the goal is `Millipede.Tests.ProgramInv.twoProg.InvStepGoal`) -/
#guard_msgs in
set_option mp.unfoldPreds false in
mp program twoProg (root : C) init cInit step twoStep invariant fun r => Even64 r.n

mp prove twoProg.inv_init := by
  vcgen [cInit]; simp [Even64]

mp prove twoProg.inv_step := fun r => ⟨id, by
  vcgen [twoStep]
  simp [Even64, UInt64.toNat_add] at *
  omega⟩

example : twoProg.Safe := twoProg.safe
example : ∀ ω n, Even64 (twoProg.run ω n).1.n := twoProg.inv

/-! ## Without an invariant -/

mp def keep (r : &mut C) : Unit := ()

mp program kProg (root : C) init cInit step keep

example : kProg.Safe := kProg.safe

/-- info: `nProg.safe` is not generated: `Millipede.Tests.ProgramInv.cStep` has a `requires`; give the program an `invariant` under which it holds -/
#guard_msgs in
mp program nProg (root : C) init cInit step cStep

/-! ## Negative: wrong invariants -/

-- `cStep` reaches 9, so `n < 5` is not kept.
/-- info: `cBad.inv_step` was not proved automatically; prove it with `mp prove cBad.inv_step := …` (the goal is `Millipede.Tests.ProgramInv.cBad.InvStepGoal`) -/
#guard_msgs in
mp program cBad (root : C) init cInit step cStep invariant fun r => r.n.toNat < 5

/--
error: Invalid field `safe`: The environment does not contain `Millipede.Program.safe`, so it is not possible to project the field `safe` from an expression
  cBad
of type `Program`
-/
#guard_msgs in
example : cBad.Safe := cBad.safe

example : ¬ cBad.InvStepGoal := fun h => by
  have := Spec.run_of_triple (h ⟨4, 0⟩).2 (by decide)
  revert this; decide

-- `True` does not give `cStep`'s `requires`.
/-- info: `cWeak.inv_step` was not proved automatically; prove it with `mp prove cWeak.inv_step := …` (the goal is `Millipede.Tests.ProgramInv.cWeak.InvStepGoal`) -/
#guard_msgs in
mp program cWeak (root : C) init cInit step cStep invariant fun _ => True

example : ¬ cWeak.InvStepGoal := fun h => absurd ((h ⟨20, 0⟩).1 trivial) (by decide)

end Millipede.Tests.ProgramInv
