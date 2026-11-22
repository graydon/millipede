import Millipede.Core.Program
import Millipede.Target.Target

/-!
# The top-level statement

`CompileSound.Statement compile t` is the statement of `compile_sound`, parameterised by the
compiler so that it is stated independently of any one compiler. `Millipede.compile_sound` in
`Top/Sound.lean` proves it for `compile` and `x64Linux` without hypotheses.

For a program `p` that compiled to the bytes `b` and is `Safe`, there is a machine state `s₀` that
the format's loader model produces from `b`, and for every oracle `ω` the machine run `m` from `s₀`
has four properties:

1. It never gets stuck, so there is no fault, no undecodable instruction and no unsupported system
   call.
2. It has the same event trace as the source, `TraceEq m.trace (p.events ω)`, which means the same
   extern calls in the same order with the same data, whether the trace is finite or infinite.
3. It keeps its stack within `p.stackBytes t.φ` bytes.
4. It executes at most `p.stepCost k ω t.κ` instructions in reactor step `k`, with the step
   boundaries tied to the trace.

The bytes are a `ByteArray`, and the loader model reads `b.data.toList`. Traces are compared as
limits of growing prefixes, because a reactor runs forever. `Machine.Exec.StepsWithin` makes the
instructions per reactor step precise. It requires increasing machine times at which the machine's
trace is exactly the source trace after that many reactor steps, with the instruction count of
each segment bounded, so a compiler cannot move events or work between reactor steps beyond what
the bounds allow. `p.stepCost k ω κ` is Core's static bound for one step, evaluated at the
target's cost model.

The proof works with `Program.sem p ω κ`, the source semantics at the level of reactor steps, as a
`Sem` whose state `k` is the number of reactor steps done, with `init` as step 0. Its trace is
`p.events ω (k-1)` and its clock is the sum of the static step bounds. The passes' simulations
compose with `FwdSim.comp`, and `Top/Sound.lean` assembles them.
-/

namespace Millipede

/-! ## The statement -/

/-- The statement of `compile_sound` for a compiler `compile` and a target `t`. -/
def CompileSound.Statement (compile : Program → Target → Except String ByteArray)
    (t : Target) : Prop :=
  ∀ (p : Program) (b : ByteArray), compile p t = .ok b → p.Safe →
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run t s₀ ω
        m.NeverStuck ∧
        TraceEq m.trace (p.events ω) ∧
        m.StackWithin (p.stackBytes t.φ) ∧
        m.StepsWithin (p.events ω) (fun k => p.stepCost k ω t.κ)

/-! ## The reactor-level source semantics and the reduction to a simulation -/

namespace Program

/-- The source trace after `k` reactor steps, where 0 means that nothing has run yet. -/
def traceAfter (p : Program) (ω : Oracle) : Nat → List Event
  | 0 => []
  | k + 1 => p.events ω k

/-- The sum of the static bounds of reactor steps `0..k-1`. -/
def costPrefix (p : Program) (ω : Oracle) (κ : CostModel) : Nat → Nat
  | 0 => 0
  | k + 1 => costPrefix p ω κ k + p.stepCost k ω κ

/-- The reactor as a `Sem`, for a fixed oracle `ω` and cost model `κ`. Its state `k` is the number
of reactor steps done, and one step runs the next reactor step. It never gets stuck, and after
`exit` the trace no longer changes, which is the stuttering of a halted program. -/
abbrev sem (p : Program) (ω : Oracle) (κ : CostModel) : Sem where
  State := Nat
  step _ k := some (k + 1)
  events k := p.traceAfter ω k
  clock k := p.costPrefix ω κ k

theorem sem_run (p : Program) (ω : Oracle) (κ : CostModel) (ω' : Oracle) :
    ∀ (n k : Nat), (p.sem ω κ).run ω' k n = some (k + n)
  | 0, k => rfl
  | n + 1, k => by
    rw [Sem.run_succ]
    show (p.sem ω κ).run ω' (k + 1) n = some (k + (n + 1))
    rw [sem_run p ω κ ω' n (k + 1)]; congr 1; omega

theorem sem_neverStuck (p : Program) (ω : Oracle) (κ : CostModel) (ω' : Oracle) (k : Nat) :
    (p.sem ω κ).NeverStuck ω' k := by
  intro n; rw [sem_run]; rfl

theorem sem_clockAt (p : Program) (ω : Oracle) (κ : CostModel) (ω' : Oracle) (k : Nat) :
    (p.sem ω κ).clockAt ω' (0 : Nat) k = p.costPrefix ω κ k := by
  unfold Sem.clockAt; rw [sem_run, Nat.zero_add]

theorem sem_traceAt (p : Program) (ω : Oracle) (κ : CostModel) (ω' : Oracle) :
    (p.sem ω κ).traceAt ω' (0 : Nat) = p.traceAfter ω := by
  funext k
  unfold Sem.traceAt; rw [sem_run, Nat.zero_add]

theorem traceEq_traceAfter (p : Program) (ω : Oracle) :
    TraceEq (p.traceAfter ω) (p.events ω) := by
  constructor
  · intro n
    cases n with
    | zero => exact ⟨0, List.nil_prefix⟩
    | succ n => exact ⟨n, List.prefix_refl _⟩
  · intro m; exact ⟨m + 1, List.prefix_refl _⟩

end Program

end Millipede
