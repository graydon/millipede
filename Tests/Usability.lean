import Millipede.Lib.Pool
import Millipede.Lib.Units
import Millipede.Meta.Report

/-!
# Tests for the automatic proofs and messages of `mp def`

A predicate defined in the file with a `Prop` result and used in `requires`, `ensures` or
`invariant` is unfolded by the automatic attempts, so it needs no `mp_auto [P]`. With
`mp.unfoldPreds false` the same definition leaves its obligation open, which shows the test has
teeth. A callee's contract is used when its `requires` is closed at the call, and the test shows
that `grind` alone does not get there.

For a loop, the postcondition at the carried value is tried as the invariant, and when it is not
inductive the message gives the shape of the proof. A goal left about an arena's cells in use
carries a hint that names `Alloc.KeyStack`. The suite also pins the messages for a `Bytes`
parameter and for a caller of a definition that failed, and checks how `#mp_report` names the
way each proof was obtained.
-/

namespace Millipede.Tests.Usability

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## Contract predicates are unfolded -/

def Small (k : UInt64) : Prop := k ≤ 3
def Twice (k r : UInt64) : Prop := r = k + k ∧ Small k

#guard_msgs in
mp def pick (k : UInt64) requires Small k : UInt64 :=
  let t : Arr UInt64 4 := #v[1, 2, 3, 4]
  t[k]!

#guard_msgs in
mp def dbl (k : UInt64) requires Small k ensures Twice k result : UInt64 := k + k

/-- info: the obligations of `pick0` were not discharged automatically; prove them with `mp prove pick0.safe := …` (the goal is `pick0.SafeGoal`); left:
k : UInt64
h : Small k
⊢ k.toNat < 4 -/
#guard_msgs in
set_option mp.unfoldPreds false in
mp def pick0 (k : UInt64) requires Small k : UInt64 :=
  let t : Arr UInt64 4 := #v[1, 2, 3, 4]
  t[k]!

-- A root invariant given by a predicate is proved automatically for `init` and for each step.
def Bounded (r : UInt64) : Prop := r ≤ 10
mp def bInit : UInt64 := 0
mp def bStep (r : &mut UInt64) : Unit := do
  if r < 10 then
    r := r + 1
    ()
  else ()

#guard_msgs in
mp program bounded (root : UInt64) init bInit step bStep invariant Bounded
example : ∀ ω n, Bounded (bounded.run ω n).1 := bounded.inv

/-! ## A callee's `requires` that is closed at the call

`grind` instantiates `underBudget.post` only from its conclusion and never proves `1 ≤ 64`, so
`mp_inst_posts` instantiates the contract at the call's arguments first. -/

mp def underBudget (seen : Q byte) (cap : Q KiB) requires cap ≤ 64
    ensures result = true → seen.toNat < cap.toNat * 1024 : Bool :=
  seen < cap.to! byte

#guard_msgs in
mp def countIn (n : UInt64) : UInt64 := if underBudget (byte n) (KiB 1) then n +! 1 else 0
example : countIn.SafeGoal := countIn.safe

example (n : UInt64) (h : (underBudget n 1).run.fst = true) : n.toNat < 1024 := by
  mp_inst_posts [underBudget]
  grind

-- Without `mp_inst_posts`, `grind` with the contract and the word lemmas does not get there.
example (n : UInt64) (h : (underBudget n 1).run.fst = true) : n.toNat < 1024 := by
  fail_if_success grind [underBudget.post, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  mp_inst_posts [underBudget]
  grind

/-! ## Loop invariants

The postcondition is tried as the invariant, and otherwise the message says what to write. -/

#guard_msgs in
mp def firstOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let t : Arr UInt64 3 := #v[40, 91, 123]
  let mut acc := 3
  for i in 0...3 do
    acc := if acc == 3 && t[i] == c then i else acc
  acc
example : ∀ c, (firstOf c).run ≤ 3 := firstOf.post

-- `acc = 4` is not kept by the loop, so the message gives the proof's shape, which then works.
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
  intro x; vcgen [count4] invariants
  · fun done left acc => acc.toNat = done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind

/-! ## A too-weak invariant over an arena points to `Alloc.KeyStack`

An invariant that keeps no record of the keys held leaves the obligation `live < 8` of `alloc!`
open, and the message names the library's accounting. `KeyStack` needs no import beyond the
pool's. -/

structure Hold where
  pool : Pool8
  keys : Slots Pool8.Key 8
  n : UInt64
deriving Data

def WeakInv (r : Hold) : Prop := r.pool.Inv ∧ r.n.toNat ≤ 8

/-- info: the obligations of `hPush` were not discharged automatically; prove them with `mp prove hPush.safe := …` (the goal is `hPush.SafeGoal`); left:
r : Hold
h : WeakInv r ∧ r.n < 8
⊢ r.pool.live.toNat < 8
hint: a goal about an arena's cells in use usually needs the keys held in the invariant: `A.KeyStack s keys n` (a stack of keys in `Slots`, Millipede/Lib/Alloc.lean; doc/reference/surface.md, "Library") -/
#guard_msgs in
mp def hPush (r : &mut Hold) (v : UInt64) requires WeakInv r ∧ r.n < 8 : Unit := do
  let k := Pool8.alloc! (&mut r.pool) v
  let i := r.n
  let _ := r.keys.put! i k
  r.n := i +! 1
  ()

example (r : Hold) : Prop := Pool8.impl.KeyStack r.pool r.keys r.n

/-! ## Messages -/

-- A string parameter is refused.
/-- error: a string (`Bytes`) can only be passed to an extern (`mp extern … (buf : Bytes)`); an `mp def` cannot take or return one: choose the string at the extern's call, or pass a byte slice `&[U8; n]` -/
#guard_msgs in
mp def sayB (msg : Bytes) : Unit := ()

-- A caller of a definition that failed gets its own message.
/-- error: type mismatch: expected UInt64, but this has type Bool -/
#guard_msgs in
mp def broken (x : UInt64) : UInt64 := x + true
/-- error: `broken` was not defined because of the error above (at its `mp def`) -/
#guard_msgs in
mp def callsBroken (x : UInt64) : UInt64 := broken x

/-! ## Proof status in `#mp_report`

The report tells a proof by `mp_auto` apart from one written by hand. -/

set_option mp.autoSafe false in
mp def pickA (k : UInt64) requires Small k : UInt64 :=
  let t : Arr UInt64 4 := #v[1, 2, 3, 4]
  t[k]!
mp prove pickA.safe := by mp_auto

set_option mp.autoSafe false in
mp def pickH (k : UInt64) requires Small k : UInt64 :=
  let t : Arr UInt64 4 := #v[1, 2, 3, 4]
  t[k]!
mp prove pickH.safe := by
  mp_auto

/-- info: "mp_auto (mp prove … := by mp_auto) | by hand (mp prove) | automatic" -/
#guard_msgs in
#eval show Lean.CoreM String from do
  return s!"{← Meta.proofStatus ``pickA `safe} | {← Meta.proofStatus ``pickH `safe} | \
    {← Meta.proofStatus ``pick `safe}"

end Millipede.Tests.Usability
