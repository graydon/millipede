import Millipede.Meta.MpDef
import Millipede.Top.Trace
import Millipede.Meta.Reach
import Millipede.Meta.Report
import Millipede.Top.Examples

/-!
# Tests of contracts about events

An effectful function's `ensures` may name `history`, the events before the call, `events`, the
events the call appends, and `exited`, whether it ends halted. `f.spec` is then a triple for every
postcondition: from a live world the contract holds, and from a halted world nothing changes
(doc/phases/ensures-events.md).

* `greet` writes the greeting. Its contract is one `write` event whose result is the oracle's
  answer given the history, and it does not exit. It is proved automatically.
* `helloE` calls `greet` and exits. Its contract is proved automatically through `greet.spec`,
  without unfolding `greet`.
* `helloP_events` is the trace of the program `helloP` for every oracle, from `helloE.post` and
  the equation `helloE.exp_denote`, without unfolding `helloE` or `greet`.
* `cnt` is a reactor whose step writes the greeting three times and then exits. The step's
  contract has a branch for each case and is proved automatically. `mp program` derives
  `cnt.reach` and `cnt.events_reach` from the contracts. `cnt_events`, its trace for every
  oracle, follows by an induction over `Program.Reach` (`cnt_reach`), without unfolding
  `cntStep`. `cntR` has a step whose contract has a `requires`; its `stepRel` is the contract
  under that `requires`, and `cntR.events_reach` is derived the same way.
* `greetUnlessZero` calls `exitIfZero`, which may exit, and then `greet`. Its contract has a
  branch for each case and is proved automatically: `greet.spec` holds from a halted world too,
  where the call changes nothing.
* `putEach` writes each byte of an array in a loop. Its contract is one write per byte, in order
  (`byteWrites`). The automatic attempt proves it with the invariant `w = ⟨history ++ byteWrites ω
  history a done.length, false⟩`, the contract's events with the loop's bound replaced by the
  iterations done; `putEach2` gives it by hand, and the invariant one write ahead fails
  (`putEach'`). `exitImported` names an imported event, which the attempt unfolds. The loop of
  `writeThenCount` makes no call, and the automatic attempt proves its contract with the contract
  as the invariant.
* Two wrong contracts, one with the events swapped and one with the wrong bytes, are not proved,
  and each is refuted under an oracle that answers `0`.
* Four more false contracts are refuted the same way: one that ignores the answer the code
  branches on, one that states a call made in one branch only, one that counts the iterations
  after a `break`, and one that counts a call after `exit`. `exitThenGreet` has the true contract
  of the last, and `greetOne` a contract that gives only the number of events.
* `cnt2` is `cnt` with its step's contract proved later by `mp prove`; `#mp_report` says that
  the trace theorem waits for it, and then names `cnt2.events_reach`.

Seeded bug, checked by hand: stating the final world of `f.spec` as `⟨evs, e⟩` instead of
`⟨w.events ++ evs, e⟩` leaves `greet` and `helloE` unproved and this file fails.
-/

namespace Millipede.Tests.EnsuresEvents
open Millipede Std.WP

set_option experimental.vcgen true

mp extern "write" sysWrite (fd : UInt64) (buf : Bytes) : UInt64
mp extern noreturn "exit" sysExit (code : UInt64) : UInt64

/-- The bytes of `hello, world\n`. -/
def msg : List UInt8 := [104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10]

/-- The call `write(1, "hello, world\n")`. -/
def writeCall : Call := ⟨"write", [1], [msg], []⟩

/-- The event of `exit(code)`. -/
def exitEvent (code : UInt64) : Event := ⟨"exit", [code], [], 0, []⟩

mp def greet ensures events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false
    : Unit :=
  let _w := sysWrite 1 "hello, world\n"
  ()

mp def helloE
    ensures events = [writeCall.event (ω.answer history writeCall), exitEvent 0] ∧ exited
    : Unit :=
  let _g := greet
  let _x := sysExit 0
  ()

/-- `helloE.post` states the events of a run from a live world with any history `h`. -/
example (ω : Oracle) (h : List Event) : ∃ evs, ((helloE ω).run ⟨h, false⟩).2.events = h ++ evs ∧
    evs = [writeCall.event (ω.answer h writeCall), exitEvent 0] ∧
    ((helloE ω).run ⟨h, false⟩).2.halted = true :=
  helloE.post ω h

mp def keep (s : Unit) : Unit := s

/-- `write(1, "hello, world\n"); exit(0)`, with `greet` as a callee. -/
def helloP : Program := ⟨Ty.unit, helloE.exp, keep.exp⟩

theorem helloP_events (ω : Oracle) (n : Nat) :
    helloP.events ω n = [writeCall.event (ω.answer [] writeCall), exitEvent 0] := by
  obtain ⟨evs, he, hevs, hx⟩ := helloE.post ω []
  have h0 : (helloP.run ω 0).2 = ((helloE ω).run World.init).2 := by
    rw [Program.run, helloP, helloE.exp_denote]
  rw [Program.events_of_init_halts _ _ (by rw [h0]; exact hx) n, h0]
  exact he.trans hevs

/-! ## A reactor -/

mp def cntInit : UInt64 := 0

mp def cntStep (c : &mut UInt64)
    ensures (c = 3 → events = [exitEvent 0] ∧ exited) ∧
      (c ≠ 3 → events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false ∧
        c' = c + 1)
    : Unit := do
  if c == 3 then
    let _x := sysExit 0
    ()
  else
    let _g := greet
    c := c + 1
    ()

mp program cnt (root : UInt64) init cntInit step cntStep

/-- The history after `k` greetings, each answered by the oracle given the history before it. -/
def greetings (ω : Oracle) : Nat → List Event
  | 0 => []
  | k + 1 => greetings ω k ++ [writeCall.event (ω.answer (greetings ω k) writeCall)]

/-- The trace of `cnt` after `n` steps: `n` greetings, and after the fourth step `exit(0)`. -/
def cntTrace (ω : Oracle) (n : Nat) : List Event :=
  if n ≤ 3 then greetings ω n else greetings ω 3 ++ [exitEvent 0]

/-- What the contracts of `cntInit` and `cntStep` say about a state after `n` steps. -/
theorem cnt_reach (ω : Oracle) (n : Nat) (s : cnt.State.carrier × World)
    (h : cnt.Reach (cnt.initRel ω) (cnt.stepRel ω) n s) :
    (n ≤ 3 → (s.1 : UInt64).toNat = n ∧ s.2 = ⟨greetings ω n, false⟩) ∧
      (3 < n → s.2 = ⟨greetings ω 3 ++ [exitEvent 0], true⟩) := by
  induction h with
  | init r evs e hi => obtain ⟨rfl, rfl, rfl⟩ := hi; simp [greetings, cntInit]
  | step n r r' h evs e _ hE ih =>
    change UInt64 at r r'
    simp only [cnt.stepRel] at hE
    have h3 : r = 3 ↔ r.toNat = 3 := by simp [← UInt64.toNat_inj]
    have h1 : (r + 1).toNat = (r.toNat + 1) % 2 ^ 64 := by simp [UInt64.toNat_add]
    grind [greetings]
  | halted n r r' w _ hw ih => grind

/-- For every oracle, the trace of `cnt` after `n` steps is `cntTrace ω n`. The proof cites
`cnt.events_reach`, which `mp program` derived from the contracts of `cntInit` and `cntStep`, and
does not unfold either. -/
theorem cnt_events (ω : Oracle) (n : Nat) : cnt.events ω n = cntTrace ω n := by
  obtain ⟨r, hr⟩ := cnt.events_reach ω n
  have := cnt_reach ω n _ hr
  unfold cntTrace; split <;> grind

/-- A step whose contract has a `requires`: `cntR.stepRel ω r h evs e r'` is
`r ≤ 3 → …`, and the trace theorem is derived as for `cnt` (`Program.reach_of_contracts_req`). -/
mp def cntStepR (c : &mut UInt64) requires c ≤ 3
    ensures c' ≤ 3 ∧ (c = 3 → events = [exitEvent 0] ∧ exited) ∧
      (c ≠ 3 → events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false ∧
        c' = c + 1)
    : Unit := do
  if c == 3 then
    let _x := sysExit 0
    ()
  else
    let _g := greet
    c := c + 1
    ()

mp program cntR (root : UInt64) init cntInit step cntStepR invariant fun c => c ≤ 3

example (ω : Oracle) (r : UInt64) (h evs : List Event) (e : Bool) (r' : UInt64) :
    cntR.stepRel ω r h evs e r' = (r ≤ 3 → r' ≤ 3 ∧ (r = 3 → evs = [exitEvent 0] ∧ e = true) ∧
      (r ≠ 3 → evs = [writeCall.event (ω.answer h writeCall)] ∧ e = false ∧ r' = r + 1)) := rfl

example := @cntR.events_reach

/-! ## A callee that may exit -/

/-- Exits with status 1 when `c` is 0, and otherwise makes no call. -/
mp def exitIfZero (c : UInt64)
    ensures (c = 0 → events = [exitEvent 1] ∧ exited) ∧ (c ≠ 0 → events = [] ∧ exited = false)
    : Unit :=
  if c == 0 then
    let _x := sysExit 1
    ()
  else ()

/-- The greeting after `exitIfZero`: after `exit` the call of `greet` changes nothing, which
`greet.spec` states for a halted world. -/
mp def greetUnlessZero (c : UInt64)
    ensures (c = 0 → events = [exitEvent 1] ∧ exited) ∧
      (c ≠ 0 → events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false)
    : Unit :=
  let _e := exitIfZero c
  let _g := greet
  ()

example := @greetUnlessZero.spec

/-! ## Loops -/

mp extern "write" sysWriteS (fd : UInt64) (buf : &[U8]) : UInt64

/-- The call `write(1, [b])`. -/
def byteCall (b : UInt8) : Call := ⟨"write", [1], [[b]], []⟩

/-- The events of writing the first `k` bytes of `a` one at a time after the history `h`, each
answered by the oracle given the history before it. -/
def byteWrites (ω : Oracle) (h : List Event) (a : Vector UInt8 4) : Nat → List Event
  | 0 => []
  | k + 1 => byteWrites ω h a k ++
      [(byteCall a[k]!).event (ω.answer (h ++ byteWrites ω h a k) (byteCall a[k]!))]

/-- The automatic attempt proves the contract with the invariant "the events so far are the
contract's events at the number of iterations done": `byteWrites ω history a 4` with `4`, the loop's
bound, replaced by `done.length`. -/
mp def putEach (a : Arr UInt8 4) ensures events = byteWrites ω history a 4 ∧ exited = false
    : Unit := do
  for i in 0...4 do
    let _w := sysWriteS 1 (&a[i..i+1])
  ()

example := @putEach.spec

-- The same invariant given by hand.
set_option mp.autoSpec false in
mp def putEach2 (a : Arr UInt8 4) ensures events = byteWrites ω history a 4 ∧ exited = false
    : Unit := do
  for i in 0...4 do
    let _w := sysWriteS 1 (&a[i..i+1])
  ()

mp prove putEach2.spec := by
  intro ω a; mp_auto invariants
  · fun done _ _ w => w = ⟨history ++ byteWrites ω history a done.length, false⟩

-- A wrong invariant, one write ahead, is not kept.
set_option mp.autoSpec false in
mp def putEach' (a : Arr UInt8 4) ensures events = byteWrites ω history a 4 ∧ exited = false
    : Unit := do
  for i in 0...4 do
    let _w := sysWriteS 1 (&a[i..i+1])
  ()

/-- error: mp_auto: a goal is left:
⊢ False
---
error: the proof is incomplete -/
#guard_msgs in
mp prove putEach'.spec := by
  intro ω a; mp_auto invariants
  · fun done _ _ w => w = ⟨history ++ byteWrites ω history a (done.length + 1), false⟩

/-- A loop that makes no call keeps the contract, which is its invariant: the automatic attempt
proves it. -/
mp def writeThenCount (a : Arr UInt8 4) ensures events.length = 1 ∧ exited = false : UInt64 := do
  let _w := sysWriteS 1 (&a[0..1])
  let mut n := 0
  for i in 0...4 do
    if a[i] == 0 then n := n + 1
  n

example := @writeThenCount.spec

/-- An oracle that answers every call with `0`. -/
def ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩

#guard_msgs (drop info) in
mp def helloSwapped
    ensures events = [exitEvent 0, writeCall.event (ω.answer history writeCall)] ∧ exited
    : Unit :=
  let _g := greet
  let _x := sysExit 0
  ()

#guard_msgs (drop info) in
mp def helloWrongBytes
    ensures events = [(⟨"write", [1], [[104]], []⟩ : Call).event (ω.answer history writeCall),
      exitEvent 0] ∧ exited
    : Unit :=
  let _g := greet
  let _x := sysExit 0
  ()

/-- The contract of `helloSwapped`, with the events in the wrong order, is false: under `ω0` the
function writes and then exits. -/
theorem helloSwapped_refuted : ¬ helloSwapped.SpecGoal := fun h => by
  obtain ⟨evs, he, hevs, -⟩ := Spec.runE_of_triple
    (fun _ h evs e => evs = [exitEvent 0, writeCall.event (ω0.answer h writeCall)] ∧ e = true)
    (h ω0) trivial []
  subst hevs; revert he; decide

/-- The contract of `helloWrongBytes`, with the wrong bytes, is false. -/
theorem helloWrongBytes_refuted : ¬ helloWrongBytes.SpecGoal := fun h => by
  obtain ⟨evs, he, hevs, -⟩ := Spec.runE_of_triple
    (fun _ h evs e => evs = [(⟨"write", [1], [[104]], []⟩ : Call).event (ω0.answer h writeCall),
      exitEvent 0] ∧ e = true)
    (h ω0) trivial []
  subst hevs; revert he; decide

/-! ## Contracts that say more than the code does

Each contract below is false, is not proved, and is refuted. `f.SpecGoal` exists only when
`f.spec` was not proved, so each refutation also checks that the contract was not proved. -/

-- The code exits when the oracle answers the write with `0`; the contract ignores the answer.
#guard_msgs (drop info) in
mp def writeExitIfZero
    ensures events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false
    : Unit :=
  let n := sysWrite 1 "hello, world\n"
  if n == 0 then
    let _x := sysExit 0
    ()
  else ()

theorem writeExitIfZero_refuted : ¬ writeExitIfZero.SpecGoal := fun h => by
  obtain ⟨evs, he, -, hx⟩ := Spec.runE_of_triple
    (fun _ h evs e => evs = [writeCall.event (ω0.answer h writeCall)] ∧ e = false)
    (h ω0) trivial []
  revert hx; decide

-- The greeting is made in one branch only; the contract states it in both.
#guard_msgs (drop info) in
mp def greetIfZero (c : UInt64)
    ensures events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false
    : Unit :=
  if c == 0 then
    let _g := greet
    ()
  else ()

theorem greetIfZero_refuted : ¬ greetIfZero.SpecGoal := fun h => by
  obtain ⟨evs, he, hevs, -⟩ := Spec.runE_of_triple
    (fun _ h evs e => evs = [writeCall.event (ω0.answer h writeCall)] ∧ e = false)
    (h ω0 1) trivial []
  subst hevs; revert he; decide

-- The loop leaves at the first zero byte; the contract counts every iteration.
#guard_msgs (drop info) in
mp def greetUntil (a : Arr UInt8 4) ensures events.length = 4 ∧ exited = false : Unit := do
  for i in 0...4 do
    if a[i] == 0 then break
    let _g := greet
  ()

theorem greetUntil_refuted : ¬ greetUntil.SpecGoal := fun h => by
  obtain ⟨evs, he, hevs, -⟩ := Spec.runE_of_triple
    (fun _ _ evs e => evs.length = 4 ∧ e = false) (h ω0 (Vector.replicate 4 0)) trivial []
  rw [List.nil_append] at he; subst he; revert hevs; decide

-- A call after `exit` appends nothing, and the contract that counts it is false.
#guard_msgs (drop info) in
mp def exitThenGreet'
    ensures events = [exitEvent 0, writeCall.event (ω.answer (history ++ [exitEvent 0]) writeCall)]
      ∧ exited
    : Unit :=
  let _x := sysExit 0
  let _g := greet
  ()

theorem exitThenGreet'_refuted : ¬ exitThenGreet'.SpecGoal := fun h => by
  obtain ⟨evs, he, hevs, -⟩ := Spec.runE_of_triple
    (fun _ h evs e => evs = [exitEvent 0, writeCall.event (ω0.answer (h ++ [exitEvent 0])
      writeCall)] ∧ e = true) (h ω0) trivial []
  subst hevs; revert he; decide

/-- The true contract of the same code: the events are the exit alone. It is proved
automatically, through `greet.spec` from a halted world. -/
mp def exitThenGreet ensures events = [exitEvent 0] ∧ exited : Unit :=
  let _x := sysExit 0
  let _g := greet
  ()

example := @exitThenGreet.spec

/-- A contract may name an imported call or event: the automatic attempt unfolds
`Examples.exitEvent`, defined in Millipede/Top/Examples.lean. -/
mp def exitImported ensures events = [Examples.exitEvent 2] ∧ exited : Unit :=
  let _x := sysExit 2
  ()

example := @exitImported.spec

/-- A contract may constrain the events without determining them. `greetOne.post` then says only
that one event is appended. -/
mp def greetOne ensures events.length = 1 ∧ exited = false : Unit :=
  let _g := greet
  ()

example (ω : Oracle) (h : List Event) : ∃ evs,
    ((greetOne ω).run ⟨h, false⟩).2.events = h ++ evs ∧ evs.length = 1 ∧
      ((greetOne ω).run ⟨h, false⟩).2.halted = false :=
  greetOne.post ω h

-- A parameter cannot be named after the events, which it would hide.
/-- error: a function with `ensures` cannot have a parameter named `exited`: in the `ensures` of a function that makes calls, `history` is the events before the call, `events` the events it appends and `exited` whether it ends by `exit` -/
#guard_msgs in
mp def exitedP (exited : Bool) ensures exited = false : Unit :=
  let _g := greet
  ()

set_option mp.autoSpec false in
/-- A program whose step's contract is not yet proved has no trace theorem yet, and
`#mp_report` says so. -/
mp def cntStep2 (c : &mut UInt64)
    ensures (c = 3 → events = [exitEvent 0] ∧ exited) ∧
      (c ≠ 3 → events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false ∧
        c' = c + 1)
    : Unit := do
  if c == 3 then
    let _x := sysExit 0
    ()
  else
    let _g := greet
    c := c + 1
    ()

mp program cnt2 (root : UInt64) init cntInit step cntStep2

/-- trace from the contracts of init and step: waits for `mp prove Millipede.Tests.EnsuresEvents.cntStep2.spec` -/
#guard_msgs (substring := true) in
#mp_report cnt2

mp prove cntStep2.spec := by mp_auto

example := @cnt2.events_reach

/-- trace from the contracts of init and step: `Millipede.Tests.EnsuresEvents.cnt2.events_reach` -/
#guard_msgs (substring := true) in
#mp_report cnt2

end Millipede.Tests.EnsuresEvents
