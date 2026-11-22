import Millipede.Top.Ledger
import Millipede.Top.Examples
import Millipede.Top.SoundA64
import Tests.Lin

/-!
# Differential tests for the whole compiler

Each program is compiled to ELF bytes for x64 or arm64 Linux, the bytes are loaded by the
target's ELF loader model, and the target's machine model runs from the loaded state by compiled
evaluation. For two oracles on both targets, the run is compared with the source in three ways.
The machine must halt with exactly the source trace, it must execute no more instructions than
the sum of the step bounds of the reactor steps run, and its stack pointer must never go more
than the program's stack bound below its start. With a cost model that charges nothing, the
instruction check fails on both targets.

The suite also checks that a program with a wide state compiles, because Core's cost charges
each word moved, and that `compile` refuses an unknown target, a building block without a
certificate of its law and a term the borrow checker rejects. The native images are run by
`scripts/mpc-check.sh`.
-/

namespace Millipede.Tests.Top

open Millipede Millipede.Tests.Core Millipede.Tests.Lower Millipede.Tests.Lin

/-- Runs the machine from `s` for at most `fuel` steps. It tracks the deepest stack `sp₀ - sp`
and, for every event, the instruction count when the event was produced. -/
def runTrack (t : Target) (ω : Oracle) (sp₀ : UInt64) :
    Nat → t.sem.State → Nat → List Nat → Option (t.sem.State × Nat × List Nat)
  | 0, s, d, ats => some (s, d, ats)
  | fuel + 1, s, d, ats =>
    if s.1.world.halted then some (s, d, ats)
    else match t.sem.step ω s with
      | none => none
      | some s' =>
        let ats' := if s'.1.world.events.length > s.1.world.events.length then ats ++ [s'.2] else ats
        runTrack t ω sp₀ fuel s' (max d (sp₀ - t.isa.sp s'.1.regs).toNat) ats'

/-- Compiles for `t`, loads and runs. It returns the final events, the instruction count,
whether the machine halted, the deepest stack and the instruction count at each event. -/
def runCompiledOn (t : Target) (ω : Oracle) (p : Program) (fuel : Nat) :
    Option (List Event × Nat × Bool × Nat × List Nat) := do
  let b ← (compile p t).toOption
  let s₀ ← t.fmt.load b.data.toList
  let (s, d, ats) ← runTrack t ω (t.isa.sp s₀.regs) fuel (s₀, 0) 0 []
  pure (s.1.world.events, s.2, s.1.world.halted, d, ats)

/-- `runCompiledOn x64Linux`. -/
def runCompiled := runCompiledOn x64Linux

/-- The first reactor step after which the source has halted (searched up to `n`). -/
def haltStep (ω : Oracle) (p : Program) : Nat → Option Nat
  | 0 => none
  | n + 1 => match haltStep ω p n with
    | some k => some k
    | none => if p.halted ω n then some n else none

/-- The sum of the static step bounds of the reactor steps `0..k`. -/
def costUpTo (κ : CostModel) (ω : Oracle) (p : Program) (k : Nat) : Nat :=
  ((List.range (k + 1)).map fun j => p.stepCost j ω κ).sum

/-- Whether every event is produced within the step bounds. When the machine produces event `j`
and it belongs to reactor step `k`, the first `k` with more than `j` source events, at most
`stepCost 0 + … + stepCost k` instructions may have run. The soundness theorem's step bound
implies this, since the mark of step `k` comes after the event. -/
def eventsInBudget (κ : CostModel) (ω : Oracle) (p : Program) (ats : List Nat) : Bool :=
  (List.range ats.length).all fun j =>
    match (List.range 21).find? (fun k => (p.events ω k).length > j), ats[j]? with
    | some k, some n => n ≤ costUpTo κ ω p k
    | _, _ => false

/-- The whole check for one program and oracle on target `t`, with the target's cost and frame
models. -/
def agreesOn (t : Target) (ω : Oracle) (p : Program) (fuel : Nat) : Bool :=
  match runCompiledOn t ω p fuel, haltStep ω p 20 with
  | some (ev, instrs, halted, depth, ats), some k =>
    halted && ev == p.events ω k && instrs ≤ costUpTo t.κ ω p k && eventsInBudget t.κ ω p ats &&
      depth ≤ p.stackBytes t.φ
  | _, _ => false

/-- `agreesOn x64Linux`. -/
def agrees := agreesOn x64Linux

/-- The programs checked, which are the first five registered examples and four reactors of
other test suites. `callProg` makes nested calls. -/
def programs : List (String × Program) :=
  (Examples.registry.take 5).map (fun e => (e.name, e.prog)) ++
    [("helloCore", Tests.Core.hello), ("counter", counter), ("resProg", resProg),
     ("callProg", callProg)]

#guard programs.all fun (_, p) => agrees ω0 p 20000
#guard programs.all fun (_, p) => agrees ωc p 20000
-- The same on arm64, with its ELF loader model, machine model, cost model and frame model.
#guard programs.all fun (_, p) => agreesOn arm64Linux ω0 p 20000
#guard programs.all fun (_, p) => agreesOn arm64Linux ωc p 20000
-- With a cost model that charges nothing, the instruction bound fails on both targets.
def κ0 : CostModel := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
#guard !agreesOn { arm64Linux with κ := κ0 } ω0 Examples.sum 20000
#guard !agreesOn { x64Linux with κ := κ0 } ω0 Examples.sum 20000

-- The exact traces of some registered examples.
#guard (runCompiled ω0 Examples.exit42 1000).map (·.1) = some [⟨"exit", [42], [], 0, []⟩]
#guard (runCompiled ω0 Examples.sum 20000).map (·.1) = some [⟨"exit", [45], [], 0, []⟩]
#guard (runCompiled ωc Examples.ticks 20000).map (fun r => r.1.length) = some 5
-- The instruction count at each event of `ticks`, which writes once per step and then exits.
#guard (runCompiled ωc Examples.ticks 20000).map (fun r => r.2.2.2.2) = some [12, 43, 74, 105, 120]

#guard (runCompiledOn arm64Linux ω0 Examples.exit42 1000).map (·.1) = some [⟨"exit", [42], [], 0, []⟩]
#guard (runCompiledOn arm64Linux ω0 Examples.sum 20000).map (·.1) = some [⟨"exit", [45], [], 0, []⟩]
#guard (runCompiledOn arm64Linux ωc Examples.ticks 20000).map (fun r => r.1.length) = some 5

-- A partial run sees a prefix of the source trace.
#guard (runCompiled ωc Examples.ticks 40).map (·.1) = some (Examples.ticks.events ωc 1)

/-! ## Refusals -/

/-- A type of width `n + 1`, made of nested `Result`s. -/
def wide : Nat → Ty
  | 0 => .u64
  | n + 1 => .result (wide n) .u64

def wideVal : (n : Nat) → (wide n).carrier
  | 0 => (0 : UInt64)
  | _ + 1 => Except.ok 0

/-- A reactor with a 41-word state, which is copied at every step because the step does not
hand back its root in place. Core's cost charges `κ.word` for each word moved, so the step's
ticks pay for the copies. -/
def wideProg : Program where
  State := wide 40
  init := .atom (.lit (wideVal 40))
  step := .atom v0

#guard (Flat.lower wideProg).toBool
#guard (compile wideProg x64Linux).toBool

/-- Whether the budget check accepts the selected code of `wideProg` under `κ`. It accepts under
`X64.κ` and refuses when the per-word weight is 0. -/
def wideBudget (κ : CostModel) : Bool :=
  match Flat.lower wideProg with
  | .error _ => false
  | .ok fp =>
    let P := Lin.linearize fp wideProg.memBytes
    X64.budgetOk 0 0 κ P

#guard wideBudget X64.κ
#guard !wideBudget { X64.κ with word := 0 }

/-- A program with a wide state that exits after one step, which agrees with the source when
compiled and run. -/
def wideExit : Program where
  State := wide 40
  init := .atom (.lit (wideVal 40))
  step := .let_ (.ext .exit (.word (.lit 7) .nil)) (.atom v1)

#guard agrees ω0 wideExit 20000

/-- A 3-word state still fits. -/
def narrowProg : Program where
  State := wide 2
  init := .atom (.lit (wideVal 2))
  step := .let_ (.ext .exit (.word (.lit 7) .nil)) (.atom v1)

#guard agrees ω0 narrowProg 20000
#guard agreesOn arm64Linux ω0 narrowProg 20000

-- A target without a registered backend has none, and `compile` refuses it.
#guard (Backend.of? { x64Linux with name := "riscv64-linux" }).isNone
#guard match compile Examples.exit42 { x64Linux with name := "riscv64-linux" } with
  | .error _ => true
  | .ok _ => false
-- Each registered target determines its backend.
#guard targets.all fun t => (Backend.of? t).map (·.target.name) == some t.name

/-! ## The soundness theorem for the registered targets -/

example : CompileSound.Statement compile x64Linux := compile_sound
example : CompileSound.Statement compile arm64Linux := compile_sound_arm64

example (b : ByteArray) (h : compile Examples.hello x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧ ∀ ω : Oracle,
      let m := Machine.run x64Linux s₀ ω
      m.NeverStuck ∧ TraceEq m.trace (Examples.hello.events ω) ∧
        m.StackWithin (Examples.hello.stackBytes x64Linux.φ) ∧
        m.StepsWithin (Examples.hello.events ω) (fun k => Examples.hello.stepCost k ω x64Linux.κ) :=
  compile_sound _ b h (Program.safe_of_total _ (by decide) (by decide))

-- The ledger names the unconditional theorem and no open claim.
#guard ((ledger "sum" "" Examples.sum 8192).splitOn "Millipede.compile_sound (no hypotheses)").length == 2
#guard ((ledger "sum" "" Examples.sum 8192).splitOn
  "== Open claims (doc/open-claims.md) ==\nnone\n").length == 2
#guard ((ledger "pooltally" "" Examples.PoolTally.prog 8192).splitOn "Millipede.compile_sound (no hypotheses)").length == 2
-- The arm64 ledger names the arm64 theorem and the arm64 models.
#guard ((ledger "sum" "" Examples.sum 8192 "" arm64Linux).splitOn "Millipede.compile_sound_arm64 (no hypotheses)").length == 2
#guard ((ledger "sum" "" Examples.sum 8192 "" arm64Linux).splitOn "Millipede.A64.linux").length == 3
#guard ((ledger "sum" "" Examples.sum 8192 "" arm64Linux).splitOn "X64").length == 1
-- Lawfulness is no premise, because the building blocks are certified and `compile` checks it.
#guard ((ledger "pooltally" "" Examples.PoolTally.prog 8192).splitOn "Program.Lawful p").length == 1
#guard ((ledger "pooltally" "" Examples.PoolTally.prog 8192).splitOn "Exp.certified").length == 3
#guard (compile Examples.PoolTally.prog x64Linux).toBool

/-! ### Uncertified building blocks

`certProg l` reads the field `l` of its root, a pair, and exits with it. With the certified
`Lens.fst` the pipeline's checks pass. With the same lens stripped of its certificate, or with
an unlawful lens whose `get` reads the second component while the lowering reads the bytes at
offset 0, the checks fail and `compile` refuses the program, which would otherwise compile to
code that disagrees with its source. -/
def certProg (l : Lens (.pair .u64 .u64) .u64) : Program where
  State := .pair .u64 .u64
  init := .mk (Ctor.pairMk .u64 .u64) (.cons (.lit 1) (.cons (.lit 2) .nil))
  step := .let_ (.read (.field (.var .here) l))
    (.let_ (.ext ExtSig.exit (.word (.var .here) .nil)) (.atom (.var (.there (.there .here)))))

/-- An unlawful lens without a certificate. -/
def badFst : Lens (.pair .u64 .u64) .u64 := ⟨"fst", 0, Prod.snd, fun p x => (x, p.2), none⟩

#guard Compile.checks (certProg (Lens.fst _ _))
#guard (compile (certProg (Lens.fst _ _)) x64Linux).toBool
#guard !Compile.checks (certProg { Lens.fst .u64 .u64 with law := none })
#guard !Compile.checks (certProg badFst)
#guard match compile (certProg badFst) x64Linux with
  | .error e => (e.splitOn "without a certificate of its law").length == 2
  | .ok _ => false

/-- An oracle that feeds the input `abc` to `read`, followed by the end of input. -/
def ωabc : Oracle :=
  ⟨fun h c => if c.sym = "read" ∧ h.length < 3 then ⟨1, [[(97 + h.length).toUInt8]]⟩ else ⟨0, []⟩⟩

/-- Runs a Lin program for at most `fuel` steps, stopping when it halts or is stuck. -/
def linRun (κ : CostModel) (P : Lin.Prog) (ω : Oracle) : Nat → Lin.State → Lin.State
  | 0, s => s
  | n + 1, s => if s.world.halted then s else match Lin.step κ P ω s with
    | some s' => linRun κ P ω n s'
    | none => s

/-- The final world of `pooltally` taken through the pipeline down to Lin. -/
def tallyLin (ω : Oracle) : Option World := Except.toOption do
  let fp ← Flat.lower Examples.PoolTally.prog
  let P := Lin.linearize fp Examples.PoolTally.prog.memBytes
  pure (linRun X64.κ P ω 200000 P.init).world

-- The Lin run halts with exactly the source trace. It reads three bytes and the end of input,
-- reads once more in each step while the three held keys are freed, and exits with
-- `(97+98+99) mod 256`.
#guard tallyLin ωabc == some ⟨Examples.PoolTally.prog.events ωabc 8, true⟩
#guard (Examples.PoolTally.prog.events ωabc 8).getLast?.map (·.args) == some [38]
#guard tallyLin ω0 == some ⟨Examples.PoolTally.prog.events ω0 5, true⟩
-- The trace differs from that of another input.
#guard tallyLin ωabc != some ⟨Examples.PoolTally.prog.events ω0 5, true⟩

/-- What is proved about the bytes of `pooltally`, the full statement with no hypotheses. -/
example (b : ByteArray)
    (hc : compile Examples.PoolTally.prog x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧ ∀ ω : Oracle,
      let m := Machine.run x64Linux s₀ ω
      m.NeverStuck ∧ TraceEq m.trace (Examples.PoolTally.prog.events ω) ∧
        m.StackWithin (Examples.PoolTally.prog.stackBytes x64Linux.φ) ∧
        m.StepsWithin (Examples.PoolTally.prog.events ω)
          (fun k => Examples.PoolTally.prog.stepCost k ω x64Linux.κ) :=
  compile_sound _ b hc Examples.PoolTally.prog.safe

/-! ## `compile` requires the borrow checker -/

/-- A program whose step drops a `Result`, which is linear, so the borrow checker rejects the
unused `let`. Lowering alone accepts the program, and `compile` refuses it. -/
def dropResult : Program :=
  ⟨Ty.u64, .atom (.lit (t := Ty.u64) 0),
    .let_ (.ok (ε := Ty.unit) (.lit (t := Ty.u64) 0)) (.atom (.var (.there .here)))⟩
#guard !dropResult.wf
#guard (Flat.lower dropResult).toBool
#guard match compile dropResult x64Linux with
  | .error e => (e.splitOn "a term the borrow checker rejects").length == 2
  | .ok _ => false
example (b : ByteArray) (h : compile dropResult x64Linux = .ok b) : False := by
  have := compile_wf h; simp [show dropResult.wf = false by decide] at this

end Millipede.Tests.Top
