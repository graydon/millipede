import Millipede.Top.Statement
import Millipede.Meta.Sem

/-!
# Lemmas about the traces of reactors

A program's behaviour is its event trace `p.events ω n`, for every oracle `ω`. This file holds
the lemmas that a proof of one program's trace uses:

* `Program.events_of_init_halts`: a program whose `init` exits has the trace of `init`;
* `Program.behaviour_of_events`, which composes a trace theorem with a compiler's soundness
  statement: if the source trace is `S ω n` for every oracle, then the loaded machine never gets
  stuck and its trace is the limit of `S ω`. For a trace that ends with `exit`,
  `TraceEq.const` reads this as: every machine trace is a prefix of the final trace, and some
  machine trace is the final trace.
-/

namespace Millipede

/-! ## A program that exits in `init` -/

namespace Program

/-- A program whose `init` exits has the trace of `init` after every number of steps. -/
theorem events_of_init_halts (p : Program) (ω : Oracle) (h : (p.run ω 0).2.halted = true)
    (n : Nat) : p.events ω n = (p.run ω 0).2.events := by
  have := events_halted p ω 0 h n
  simp only [Nat.zero_add] at this
  simp [events, this]

end Program

/-! ## Composing with the compiler's soundness -/

/-- A limit of growing prefixes that are all the same list `L` is `L`: every trace of `a` is a
prefix of `L`, and some trace of `a` is `L`. -/
theorem TraceEq.const {a : Nat → List Event} {L : List Event} (h : TraceEq a (fun _ => L)) :
    (∀ n, a n <+: L) ∧ ∃ n, a n = L := by
  refine ⟨fun n => (h.1 n).choose_spec, ?_⟩
  obtain ⟨n, hn⟩ := h.2 0
  exact ⟨n, ((h.1 n).choose_spec).eq_of_length (Nat.le_antisymm
    ((h.1 n).choose_spec).length_le hn.length_le)⟩

/-- The prefixes of a finite trace `L` have the limit `L`. -/
theorem TraceEq.take {a : Nat → List Event} {L : List Event} (h : TraceEq a (fun n => L.take n)) :
    TraceEq a (fun _ => L) :=
  h.trans ⟨fun n => ⟨0, List.take_prefix n L⟩,
    fun _ => ⟨L.length, by simp [List.take_of_length_le (Nat.le_refl _)]⟩⟩

/-- A theorem about the source trace carried to the machine. If `cc` satisfies the soundness
statement for `t`, `p` is `Safe`, and the source trace of `p` after `n` steps is `S ω n` for
every oracle, then whenever `cc p t = .ok b` the bytes `b` load, and for every oracle the
machine never gets stuck and its trace has the limit of `S ω`. -/
theorem Program.behaviour_of_events {cc : Program → Target → Except String ByteArray}
    {t : Target} (hcc : CompileSound.Statement cc t) (p : Program) (hp : p.Safe)
    (S : Oracle → Nat → List Event) (hS : ∀ ω n, p.events ω n = S ω n) {b : ByteArray}
    (hc : cc p t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, (Machine.run t s₀ ω).NeverStuck ∧ TraceEq (Machine.run t s₀ ω).trace (S ω) := by
  obtain ⟨s₀, hl, h⟩ := hcc p b hc hp
  refine ⟨s₀, hl, fun ω => ⟨(h ω).1, ?_⟩⟩
  have he : p.events ω = S ω := funext (hS ω)
  exact he ▸ (h ω).2.1

end Millipede
