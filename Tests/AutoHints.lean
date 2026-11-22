import Millipede.Meta.MpDef

/-!
# Tests for the hints after an automatic attempt that leaves obligations

A pair borrow `(a[i], a[j])` whose indices may be equal leaves the goal `False`, and the message
names the pair borrow and the obligation that the indices differ (scratch/audit/reach/Borrow.lean,
`alias4`). An attempt that runs out of its budget names `mp.autoSafe.maxHeartbeats` and splitting
the function (scratch/audit/reach/Wc.lean, whose first `wStep` held the loop of `count`); here
the budget is made small so that a short function exceeds it.
-/

namespace Millipede.Tests.AutoHints

open Millipede

structure S where
  a : Arr UInt64 8
deriving Data

mp def sw (p : &mut (UInt64 × UInt64)) : Unit := do
  p.fst := 1
  p.snd := 2

/--
info: the obligations of `swap2` were not discharged automatically; prove them with `mp prove swap2.safe := …` (the goal is `swap2.SafeGoal`); left:
⊢ False
hint: the pair borrow `(s.a[i]!, s.a[j]!)` takes two cells of one array, so its obligations include that the two indices differ; a goal `False` here usually means that they may be equal. State it in `requires` (as `i ≠ j`) or test it before the borrow
-/
#guard_msgs in
mp def swap2 (s : &mut S) (i j : UInt64) requires i.toNat < 8 ∧ j.toNat < 8 : Unit :=
  sw (&mut (s.a[i]!, s.a[j]!))

mp def swap2' (s : &mut S) (i j : UInt64) requires i.toNat < 8 ∧ j.toNat < 8 ∧ i ≠ j : Unit :=
  sw (&mut (s.a[i]!, s.a[j]!))
example := @swap2'.safe

/--
info: the obligations of `sumTo` were not discharged automatically; prove them with `mp prove sumTo.safe := …` (the goal is `sumTo.SafeGoal`); left:
(deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (1) has been reached
hint: the attempt ran out of its budget `mp.autoSafe.maxHeartbeats` (in thousands of heartbeats; Lean's `maxHeartbeats` does not apply to it). Raise it for this function with `set_option mp.autoSafe.maxHeartbeats 2000000 in mp def sumTo …`, or move a loop or a branch into an `mp def` of its own: the attempt's cost grows with the variables in scope and the reads of them
-/
#guard_msgs in
set_option mp.analyser false in
set_option mp.autoSafe.maxHeartbeats 1 in
mp def sumTo (a : Arr UInt64 8) (n : UInt64) requires n.toNat ≤ 8 : UInt64 := do
  let mut t := 0
  for i in 0...min n 8 do
    t := t +! a[i]!
  t

end Millipede.Tests.AutoHints
