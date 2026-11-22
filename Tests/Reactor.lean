import Millipede.Lib.Pool
import Millipede.Lib.Units
import Millipede.Top.Tally

/-!
# A reactor over a pool, proved automatically

The program `ring` keeps a pool of 8 cells, a stack of the keys it holds and a byte budget as a
quantity. Each step reads a byte, and while under budget pushes it, popping the newest key
first when 8 are held. At the end of input it pops one key per step and then exits with the
total's low byte. The program has no hand proof, because the automatic attempt of `mp def` falls
back to `mp_auto` and unfolds the invariant `RInv`, so `ring.safe` and `ring.inv` follow.

`mp_auto` does not prove two wrong programs, a push that forgets to count the key and a step
that pushes a ninth key without popping. The suite also checks that plain `vcgen` proves a
contract through a pure callee with a `&mut` argument, and that a callee without a
specification is reported by `mp_auto`.
-/

namespace Millipede.Tests.Reactor

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true
mp extern "read" rRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern noreturn "exit" rExit (code : UInt64) : UInt64

structure Ring where
  pool : Pool8
  keys : Slots Pool8.Key 8
  n : UInt64
  seen : UInt64
  sum : UInt64
deriving Data

def RInv (r : Ring) : Prop :=
  r.pool.Inv ∧ Pool8.impl.KeyStack r.pool r.keys r.n ∧ r.seen.toNat ≤ 1024

mp def underBudget (seen : Q byte) requires seen.toNat ≤ 1024
    ensures result = true → seen.toNat < 1024 : Bool := seen < (KiB 1).to! byte

mp def rInit ensures RInv result : Ring :=
  { pool := Pool8.new, keys := Slots.empty 8, n := 0, seen := 0, sum := 0 }

mp def rPush (r : &mut Ring) (c : UInt64) requires RInv r ∧ r.n.toNat < 8
    ensures RInv r' : Unit := do
  let k := Pool8.alloc! (&mut r.pool) c
  let i := r.n
  let _ := r.keys.put! i k
  r.n := i +! 1
  ()

mp def rPop (r : &mut Ring) requires RInv r ∧ 0 < r.n.toNat
    ensures RInv r' ∧ r'.n.toNat + 1 = r.n.toNat : Unit := do
  let i := r.n -! 1
  let k := r.keys.take! i
  let v := Pool8.free (&mut r.pool) k
  r.n := i
  r.sum := r.sum + v
  ()

mp def rStep (r : &mut Ring) requires RInv r ensures RInv r' : Unit := do
  let c := rRead 0
  if c < 256 && underBudget (byte r.seen) then
    r.seen := r.seen +! 1
    if r.n < 8 then rPush (&mut r) c
    else
      let _ := rPop (&mut r)
      rPush (&mut r) c
  else if r.n == 0 then
    let _x := rExit (r.sum &&& 255)
    ()
  else rPop (&mut r)

mp program ring (root : Ring) init rInit step rStep invariant RInv

example : ring.Safe := ring.safe

/-! ## Wrong programs are not proved -/

/-- A push that forgets to count the pushed key, so the stack's invariant fails. -/
mp def rPushBad (r : &mut Ring) (c : UInt64) requires RInv r ∧ r.n.toNat < 8 ensures RInv r' :
    Unit :=
  let k := Pool8.alloc! (&mut r.pool) c
  let i := r.n
  let _ := r.keys.put! i k
  ()

example : True := by
  fail_if_success (have : rPushBad.SpecGoal := by mp_auto [RInv])
  trivial

/-- A step that pushes a ninth key without popping, so the `requires` of `rPush` fails at the
call. -/
mp def rStepBad (r : &mut Ring) requires RInv r : Unit :=
  let c := rRead 0
  if c < 256 then rPush (&mut r) c else ()

example : True := by
  fail_if_success (have : rStepBad.SafeGoal := by mp_auto [RInv])
  trivial

/-! ## `vcgen` through carriers

The normal forms of `mp def` expand every carrier `t.carrier` of a type that reduces to
`⟨C, _⟩`, so the `Spec.pure` rule of `vcgen` applies under a call's `bind`. A callee without a
specification is reported by `mp_auto` with the error "No spec found" of `vcgen`. -/

open Millipede.Examples in
/-- Plain `vcgen` proves the contract of the step of `pooltally`, an effectful caller of a pure
callee with a `&mut` struct argument. -/
example : ∀ (A : Lib.Alloc UInt64) (h8 : 8 ≤ A.cap) (hr : A.reuse = true) (ω : Oracle)
    (r : TallyRoot A),
    ⦃fun _ => TallyInv A r⦄ Tally.step A h8 hr ω r ⦃fun x _ => TallyInv A x.2.1⦄ := by
  intro A h8 hr ω r
  vcgen [Tally.step]
  all_goals grind [Tally.push.post, Tally.pop.post, TallyInv, → Alloc.KeyStack.le,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]

/-- An effectful helper that has no contract and is not an `mp def`, so `mp_auto` does not
unfold it. -/
def noSpecHelper (n : UInt64) : StateM World UInt64 := pure (n + 1)

def noSpecCaller (n : UInt64) : StateM World UInt64 := do
  let a ← noSpecHelper n
  pure (a + 1)

def noSpecCaller.SpecGoal : Prop := ∀ n, ⦃fun _ => n < 10⦄ noSpecCaller n ⦃fun r _ => r = n + 2⦄

/-- error: No spec found for program noSpecHelper n✝. -/
#guard_msgs in
example : noSpecCaller.SpecGoal := by unfold noSpecCaller.SpecGoal; mp_auto

end Millipede.Tests.Reactor
