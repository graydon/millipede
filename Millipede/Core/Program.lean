import Millipede.Core.Stack
import Millipede.Core.Wf
import Millipede.Core.Safe

/-!
# Programs

A program has no global variables. It owns one value, the root, of type `p.State`, which lives in
static storage. `init` runs once and produces the root, and `step` then runs again and again, each
time with `&mut root`. In the value semantics a `mut` parameter is a lens, so `step` receives the
root's value and hands back its updated value, and its type is `Exp [State] State`. Every
container the program uses is a field of the root or lives in a frame.

Each step is a bounded term, so the step is the unit of cost accounting. A program's behaviour is
its trace of extern events, given by finite prefixes: `p.events ω n` is the trace after `init` and
`n` steps. The trace stops growing once `exit` has been called, by `events_halted`. The resources of a program are `stepCost`, the bound on the steps of
one reactor step, `stackBytes φ`, the main frame and the calls, and `footprint`, the root's bytes
plus the larger footprint of `init` and `step`.
-/

namespace Millipede

/-- A reactor program, given by the root's type, `init`, and `step`, which takes `&mut root`. -/
structure Program where
  /-- the type of the root -/
  State : Ty
  /-- builds the root -/
  init : Exp [] State
  /-- one reactor step with `&mut root`, which takes the root's value and returns its updated
  value -/
  step : Exp [State] State

namespace Program

/-- The root and the world after `init` and `n` steps, under oracle `ω`. -/
def run (p : Program) (ω : Oracle) : Nat → p.State.carrier × World
  | 0 => p.init.denote ω .nil World.init
  | n + 1 =>
    let s := p.run ω n
    p.step.denote ω (.cons s.1 .nil) s.2

/-- The event trace after `init` and `n` steps. -/
def events (p : Program) (ω : Oracle) (n : Nat) : List Event := (p.run ω n).2.events

/-- Whether the program has called `exit` by the end of reactor step `n`, where step 0 is
`init`. -/
def halted (p : Program) (ω : Oracle) (n : Nat) : Bool := (p.run ω n).2.halted

/-- How the step hands back the root: in place when every tail of it is the root's variable, and
otherwise by a copy. `init` builds the root in place. -/
def stepHb (p : Program) : Hb := if p.step.tailVar 0 then .whole 0 else .copy

/-- The static step bound for reactor step `k`, where step 0 is `init`. It does not depend on
`ω`, which it takes only so that it has the shape of the other per-step statements. -/
def stepCost (p : Program) (k : Nat) (_ω : Oracle) (κ : CostModel) : Nat :=
  match k with
  | 0 => p.init.cost κ .copy
  | _ + 1 => p.step.cost κ p.stepHb

/-- The steps that reactor step `k` actually takes in the instrumented semantics, where step 0 is
`init`. -/
def stepSteps (p : Program) (ω : Oracle) (κ : CostModel) : Nat → Nat
  | 0 => (p.init.exec ω κ .copy .nil World.init).steps
  | k + 1 => (p.step.exec ω κ p.stepHb (.cons (p.run ω k).1 .nil) (p.run ω k).2).steps

/-- The root's type. -/
abbrev Root (p : Program) : Ty := p.State

/-- A program is well formed when `init` passes the checker and `step` passes it with its
parameter a `mut` binder that it hands back, so that a linear root is moved into the result
exactly once. -/
def wf (p : Program) : Bool :=
  p.init.wf && checkBody p.step.check [BS.fresh .mut p.State.linear]

/-- The program's obligations hold on every run, for every oracle. -/
def Safe (p : Program) : Prop :=
  ∀ ω : Oracle, p.init.safe ω .nil World.init ∧
    ∀ n, p.step.safe ω (.cons (p.run ω n).1 .nil) (p.run ω n).2

/-- A program without partial operations is `Safe`. -/
theorem safe_of_total (p : Program) (hi : p.init.total = true) (hs : p.step.total = true) :
    p.Safe :=
  fun ω => ⟨Exp.safe_of_total ω _ hi _ _, fun _ => Exp.safe_of_total ω _ hs _ _⟩

/-- The stack bound of a program under frame model `φ`. `init` and `step` run in one main frame,
which holds the root twice, as the current value and the next one being built, plus the slots of
the larger of the two bodies. The frames of the calls inside `init` or `step` come on top. Since
`φ` is monotone, any layout whose main frame has at most this many slots fits. -/
def stackBytes (p : Program) (φ : FrameModel) : Nat :=
  φ.frame (frameWords (2 * ctxWords [p.State] + max p.init.slotWords p.step.slotWords)) +
    max (p.init.stackBytes φ) (p.step.stackBytes φ)

/-- The static memory footprint in bytes, which is the root in static storage plus the larger
footprint of `init` and `step`. -/
def footprint (p : Program) : Nat :=
  p.State.size + max p.init.footprint p.step.footprint

/-- After `exit`, a step changes nothing. -/
theorem run_halted (p : Program) (ω : Oracle) (n : Nat) (h : p.halted ω n = true) :
    (p.run ω (n + 1)).2 = (p.run ω n).2 :=
  Exp.denote_halted ω _ _ _ h

/-- `exit` ends the trace, since once halted the program stays halted and its trace is final. -/
theorem events_halted (p : Program) (ω : Oracle) (n : Nat) (h : p.halted ω n = true) :
    ∀ k, (p.run ω (n + k)).2 = (p.run ω n).2 := by
  intro k
  induction k <;> grind [halted, run_halted]

end Program

end Millipede
