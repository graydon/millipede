import Millipede.Core.Stack
import Millipede.Compile.Sem
import Millipede.Object.Format

/-!
# Targets and machine runs

A `Target` bundles an ISA model, an ABI on it, an executable format, and the two resource hooks
every backend supplies. The cost model `κ` gives instructions per source construct, and the
compiler checks that its code takes at most that many, so that each reactor step runs at most
`p.stepCost k ω t.κ` instructions. The frame model `φ` gives the bytes of stack that an
activation with `w` word slots occupies, return address and alignment included, so that the
stack depth is at most `p.stackBytes t.φ`.

`Target.sem` is the machine as a `Sem`, whose state is the machine state together with the
number of instructions executed. A step fetches, decodes and executes one instruction, with
system calls answered by the oracle through `Abi.trap`. After `exit` the machine stutters,
stepping to itself and executing nothing more.

`Machine.run t s₀ ω` is the execution from `s₀`. It never gets stuck when there is never a
fault, an undecodable instruction or an unsupported system call. Its observations are the events
after `n` steps, the instructions executed in the first `n` steps, the stack bound `StackWithin`
and the bound on each reactor step `StepsWithin`. `Target.Laws t` collects the proof obligations
of a target, the laws of its ISA and of its format.
-/

namespace Millipede

/-- A compilation target. -/
structure Target where
  name : String
  isa : Isa
  abi : Abi isa
  fmt : Format isa abi
  /-- The instructions per source construct. -/
  κ : CostModel
  /-- The frame sizes. -/
  φ : FrameModel

/-- The proof obligations of a target. -/
structure Target.Laws (t : Target) : Prop where
  isa : t.isa.Laws
  fmt : t.fmt.Laws

namespace Target

variable (t : Target)

/-- The machine as a semantics, whose state is the machine state and the instruction count. A
halted machine stutters. -/
def sem : Sem where
  State := MState t.isa.Regs × Nat
  step ω s :=
    if s.1.world.halted then some s
    else (t.isa.step (t.abi.trap ω) s.1).map (fun s' => (s', s.2 + 1))
  events s := s.1.world.events
  clock s := s.2

variable {t}

/-- With the ISA laws, the machine only extends the trace and counts up. -/
theorem sem_mono (hl : t.isa.Laws) : t.sem.Mono where
  events ω s s' h := by
    simp only [sem] at h ⊢
    split at h
    · cases h; exact List.prefix_refl _
    · cases hs : t.isa.step (t.abi.trap ω) s.1 with
      | none => rw [hs] at h; cases h
      | some s₁ =>
        rw [hs] at h; cases h
        exact (t.abi.step_respects hl ω hs).2
  clock ω s s' h := by
    simp only [sem] at h ⊢
    split at h
    · cases h; exact Nat.le_refl _
    · cases hs : t.isa.step (t.abi.trap ω) s.1 with
      | none => rw [hs] at h; cases h
      | some s₁ => rw [hs] at h; cases h; exact Nat.le_succ _

end Target

/-- An execution of target `t` from machine state `s₀` under oracle `ω`. -/
structure Machine.Exec (t : Target) where
  s₀ : MState t.isa.Regs
  ω : Oracle

/-- The execution of `t` from `s₀` under `ω`, finite or infinite. -/
def Machine.run (t : Target) (s₀ : MState t.isa.Regs) (ω : Oracle) : Machine.Exec t :=
  ⟨s₀, ω⟩

namespace Machine.Exec

variable {t : Target} (m : Machine.Exec t)

/-- The `Sem` state at time `0`. -/
def start : t.sem.State := (m.s₀, 0)

/-- The machine state after `n` steps, or `none` if it is stuck by then. -/
def state (n : Nat) : Option (MState t.isa.Regs) :=
  (t.sem.run m.ω m.start n).map Prod.fst

/-- No fault, no undecodable instruction, no unsupported system call, ever. -/
def NeverStuck : Prop := t.sem.NeverStuck m.ω m.start

/-- The events observed after `n` steps. -/
def trace (n : Nat) : List Event := t.sem.traceAt m.ω m.start n

/-- The instructions executed during the first `n` steps, where steps after `exit` execute
nothing. -/
def instrs (n : Nat) : Nat := t.sem.clockAt m.ω m.start n

/-- At every time the stack pointer lies within `b` bytes below its initial value, as
`(sp₀ - sp) mod 2⁶⁴ ≤ b`. So it is never above `sp₀` either, short of wrapping past the whole
address space. -/
def StackWithin (b : Nat) : Prop :=
  ∀ n s, m.state n = some s → (t.isa.sp m.s₀.regs - t.isa.sp s.regs).toNat ≤ b

/-- Instruction bounds for each reactor step. There are monotone machine times `marks k` with
`marks 0 = 0` such that by time `marks (k+1)` the machine has produced exactly the trace `ev k`,
the source trace after reactor steps `0..k`, and at most `bound k` instructions run between
`marks k` and `marks (k+1)`. So every event of reactor step `k` happens within
`bound 0 + … + bound k` instructions, and reactor step `k` costs at most `bound k`. -/
def StepsWithin (ev : Nat → List Event) (bound : Nat → Nat) : Prop :=
  ∃ marks : Nat → Nat, marks 0 = 0 ∧ ∀ k, marks k ≤ marks (k + 1) ∧
    m.trace (marks (k + 1)) = ev k ∧ m.instrs (marks (k + 1)) - m.instrs (marks k) ≤ bound k

end Machine.Exec

end Millipede
