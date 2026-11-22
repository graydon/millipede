import Millipede.Top.Behaviour

/-!
# Acceptance checked by the kernel

The theorems of `Top/Behaviour.lean` hold for every `b` with `compile p t = .ok b`. This file
proves, by evaluation in Lean's kernel, that such a `b` exists for `exit42` and `hello`, and
drops the hypothesis: the bytes exist, they load, and the machine does what the specification
says. The kernel evaluates the whole pipeline, from the checks before lowering to the ELF
writer, so no step of it is run as compiled code.

The evaluation is of the default `compile`, register allocation included: the untrusted
allocator `RegAlloc.Alloc.allocate` uses only `for` loops, lists and the structural merge sort
`sortBy`, which the kernel evaluates. For `revchunks` the kernel does not finish in reasonable
time: the instruction budget's potential, `Sel.potential`, a fixed-point iteration over arrays, is
the slow part. Its acceptance rests on compiled evaluation (`Tests/Witness.lean` checks it with
`#guard`), recorded as `CompileAccepts.Statement`.
-/

namespace Millipede.Examples

theorem Except.exists_of_toBool {ε α : Type} {e : Except ε α} (h : e.toBool = true) :
    ∃ a, e = .ok a := by
  cases e with
  | error => simp [Except.toBool] at h
  | ok a => exact ⟨a, rfl⟩

set_option maxRecDepth 100000 in
theorem exit42_compiles_x64 : (compile exit42 x64Linux).toBool = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem exit42_compiles_arm64 : (compile exit42 arm64Linux).toBool = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hello_compiles_x64 : (compile hello x64Linux).toBool = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hello_compiles_arm64 : (compile hello arm64Linux).toBool = true := by
  decide +kernel

/-- `hello` with no hypothesis. On both targets the compiler produces bytes, they load, and for every oracle the machine never gets stuck, every trace it
shows is a prefix of `write(1, "hello, world\n")` followed by `exit(0)`, and it shows both. -/
theorem hello_runs (t : Target) (ht : t = x64Linux ∨ t = arm64Linux) :
    ∃ b s₀, compile hello t = .ok b ∧ t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, let m := Machine.run t s₀ ω
        m.NeverStuck ∧ (∀ n, m.trace n <+: Hello.spec ω) ∧ ∃ n, m.trace n = Hello.spec ω := by
  have hs := sound_compileWith {}
  rcases ht with rfl | rfl
  · obtain ⟨b, hb⟩ := Except.exists_of_toBool hello_compiles_x64
    obtain ⟨s₀, hl, h⟩ := hello_behaviour hs.1 b hb
    exact ⟨b, s₀, hb, hl, h⟩
  · obtain ⟨b, hb⟩ := Except.exists_of_toBool hello_compiles_arm64
    obtain ⟨s₀, hl, h⟩ := hello_behaviour hs.2 b hb
    exact ⟨b, s₀, hb, hl, h⟩

/-- `exit42` with no hypothesis: the bytes exist and load, and for every oracle the machine never
gets stuck and its trace is `exit(42)`. -/
theorem exit42_runs (t : Target) (ht : t = x64Linux ∨ t = arm64Linux) :
    ∃ b s₀, compile exit42 t = .ok b ∧ t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, let m := Machine.run t s₀ ω
        m.NeverStuck ∧ (∀ n, m.trace n <+: [exitEvent 42]) ∧ ∃ n, m.trace n = [exitEvent 42] := by
  have he : ∀ ω n, exit42.events ω n = [exitEvent 42] := by
    intro ω n
    have h0 : (exit42.run ω 0).2 = ⟨[exitEvent 42], true⟩ := by
      simp [exit42, Program.run, exit42Init.exp_denote, exit42Init, World.init, World.call,
        exitEvent, Call.event, fitOut]
      rfl
    rw [Program.events_of_init_halts _ _ (by rw [h0]) n, h0]
  have hs := sound_compileWith {}
  have key : ∀ {t : Target}, Sound compile t →
      (compile exit42 t).toBool = true →
      ∃ b s₀, compile exit42 t = .ok b ∧ t.fmt.load b.data.toList = some s₀ ∧
        ∀ ω : Oracle, let m := Machine.run t s₀ ω
          m.NeverStuck ∧ (∀ n, m.trace n <+: [exitEvent 42]) ∧ ∃ n, m.trace n = [exitEvent 42] := by
    intro t hcc hc
    obtain ⟨b, hb⟩ := Except.exists_of_toBool hc
    obtain ⟨s₀, hl, h⟩ := exit42.behaviour_of_events hcc exit42.safe _ he hb
    exact ⟨b, s₀, hb, hl, fun ω => ⟨(h ω).1, TraceEq.const (h ω).2⟩⟩
  rcases ht with rfl | rfl
  · exact key hs.1 exit42_compiles_x64
  · exact key hs.2 exit42_compiles_arm64

/-- That the default compiler accepts `revchunks` on both targets. It is checked by compiled
evaluation (`Tests/Witness.lean`). The kernel does not finish evaluating it, because the budget
potential `Sel.potential` takes too long. -/
def CompileAccepts.Statement : Prop :=
  ∀ t ∈ [x64Linux, arm64Linux], ∃ b, compile revProg t = .ok b

end Millipede.Examples
