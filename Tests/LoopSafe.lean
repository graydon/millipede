import Millipede.Lib.Pool
import Millipede.Lib.Bump

/-!
# Tests for loop invariants of obligations

An obligation that depends on a loop's state needs an invariant, given as
`mp prove f.safe := by mp_auto invariants · fun done left (acc, x, …, _) => …` with one `·` per
loop in source order. The state is shaped as in a contract's invariant. The same text after
`mp prove f.spec` proves the contract and then `f.safe` with it. A goal left about a loop's state
names its components after the source variables and the flags for leaving the loop and
returning, and the error for an invariant that does not say enough is reported at the invariant.

The invariants are described in doc/reference/proofs.md.
-/

namespace Millipede.Tests.LoopSafe

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## An index carried by the loop

`j` and `s` move together so that `j + s = 4`, a relation the verified analyser does not track.
The state is `(s, (j, (t, ())))`, because `s` is the variable the body ends by assigning. -/

#guard_msgs (drop info) in
mp def walk (a : Arr UInt64 4) : UInt64 := do
  let mut j := 0
  let mut s := 4
  let mut t := 0
  for _ in 0...100 do
    if s == 0 then break
    t := t + a[j]!
    j := j + 1
    s := s - 1
  t

mp prove walk.safe := by
  mp_auto invariants
  · fun _ _ (s, j, _) => j.toNat + s.toNat = 4

example := @walk.safe

-- An invariant over the state alone that does not say enough is reported at the invariant,
-- naming the component the goal is about.
#guard_msgs (drop info) in
mp def walk2 (a : Arr UInt64 4) : UInt64 := do
  let mut j := 0
  let mut s := 4
  let mut t := 0
  for _ in 0...100 do
    if s == 0 then break
    t := t + a[j]!
    j := j + 1
    s := s - 1
  t

/-- error: mp_auto: this loop invariant does not prove the obligations of its loop or is not kept by an iteration (about `j`); left:
j : UInt64
⊢ j.toNat < 4
---
error: the proof is incomplete -/
#guard_msgs in
mp prove walk2.safe := by
  mp_auto invariants
  · fun (s, _) => s.toNat ≤ 4

/-! ## An arena client

`Store.sum` allocates, reads and frees inside a loop with `continue`, `break` and `return`, and
one invariant proves both its contract and its obligations. -/

section
variable (A : Alloc UInt64) (h4 : 4 ≤ A.cap)
include h4

#guard_msgs (drop info) in
/-- Sums, through the arena, at most four nonzero values of `xs` before the first 99, and returns
7000 at once when it sees a 7. -/
mp def Store.sum (s : &mut A.S) (xs : &Arr UInt64 8) requires A.Inv s ∧ A.used s = 0
    ensures A.Inv s' : UInt64 := do
  let mut total := 0
  let mut n := 0
  for i in 0...8 do
    let x := xs[i]
    if x == 0 then continue
    if x == 99 then break
    if x == 7 then return 7000
    if n == 4 then break
    let k := A.alloc! (&mut s) x
    let y := A.get (&s) (&k)
    let v := A.free (&mut s) k
    total := total + v + y
    n := n + 1
  total

/-- info: `Store.sum.safe` was proved with the contract's loop invariants -/
#guard_msgs in
mp prove Store.sum.spec := by
  mp_auto invariants
  · fun _ _ (n, s, _) => A.Inv s ∧ A.used s ≤ n.toNat ∧ n.toNat ≤ 4

example : Store.sum.SafeGoal A h4 := Store.sum.safe A h4

#guard_msgs (drop info) in
/-- The obligations alone, with an invariant written for them that matches every component. -/
mp def Store.sum2 (s : &mut A.S) (xs : &Arr UInt64 8) requires A.Inv s ∧ A.used s = 0 : UInt64 := do
  let mut total := 0
  let mut n := 0
  for i in 0...8 do
    let x := xs[i]
    if x == 0 then continue
    if x == 99 then break
    if x == 7 then return 7000
    if n == 4 then break
    let k := A.alloc! (&mut s) x
    let v := A.free (&mut s) k
    total := total + v
    n := n + 1
  total

mp prove Store.sum2.safe := by
  mp_auto invariants
  · fun _ _ (n, s, _, _, _, _, _) => A.Inv s ∧ A.used s ≤ n.toNat ∧ n.toNat ≤ 4

#guard_msgs (drop info) in
/-- A callee whose loop has no contract, so the caller's contract is proved automatically with
the invariant `True`. It uses no variable of the section, so it is closed although the section
has `include h4`. -/
mp def Store.pick (xs : &Arr UInt64 8) : UInt64 := do
  let mut total := 0
  let mut n := 0
  for i in 0...8 do
    let x := xs[i]
    if x == 0 then continue
    if x == 99 then break
    if x == 7 then return 7000
    if n == 4 then break
    total := total + x
    n := n + 1
  total

#guard_msgs (drop info) in
mp def Store.keep (s : &mut A.S) (xs : &Arr UInt64 8) requires A.Inv s ∧ A.used s < A.cap
    ensures A.Inv s' : UInt64 :=
  let v := Store.pick (&xs)
  let k := A.alloc! (&mut s) v
  A.free (&mut s) k

example : Store.keep.SafeGoal A h4 := Store.keep.safe A h4
example := @Store.keep.spec
example : Vector UInt64 8 → Id (UInt64 × Unit) := Store.pick

end

/-! The safety of `Store.sum` at the pool and at the bump arena. -/

example : Store.sum.SafeGoal Pool8.impl (by decide) := Store.sum.safe _ _
example : Store.sum.SafeGoal Bump8.impl (by decide) := Store.sum.safe _ _

end Millipede.Tests.LoopSafe
