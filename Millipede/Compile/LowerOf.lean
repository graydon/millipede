import Millipede.Compile.LowerProg
import Millipede.Compile.LowerRestr

/-!
# The hypotheses of the memory refinement from the checks

`compile` establishes `MemHyp`, the hypotheses of the reactor simulation, from three checks and one
premise:

* `lower` accepts the program, so its terms are in the lowered fragment, which the refinement
  covers entirely;
* the borrow checker accepts the program, which gives the block rule and the borrow discipline that
  the lowering of references to pointers rests on;
* the building blocks are lawful, because `compile` checks their certificates;
* the program is `Safe`, which is a premise of the statement.
-/

namespace Millipede.Flat

/-- The borrow checker's guarantees for a program: the block rule and the borrow discipline of
`init` and of `step`, whose parameter, the root, is a `&mut` binder. -/
theorem _root_.Millipede.Program.checked (p : Program) (h : p.wf = true) :
    p.init.Restr [] ∧ p.step.Restr [true] ∧ p.init.Frozen ∧ p.step.Frozen := by
  simp only [Program.wf, Bool.and_eq_true] at h
  obtain ⟨hi, hs⟩ := h
  obtain ⟨st, hst⟩ := checkBody_some hs
  refine ⟨?_, ?_, p.init.frozen_of_wf hi, p.step.frozen_of_check hst⟩
  · have := p.init.restr_of_wf hi; simpa [allW] using this
  · have := p.step.restr_of_check _ _ hst
    have e : wflags [BS.fresh .mut p.State.linear] = [true] := rfl
    rwa [e] at this

/-- The hypotheses of the reactor simulation hold for a program that `lower` lowers, that the
borrow checker accepts, whose building blocks are lawful, and that is `Safe`. -/
theorem MemHyp.of_checks {p : Program} {fp : Prog} (h : lower p = .ok fp) (hwf : p.wf = true)
    (hL : p.init.Lawful ∧ p.step.Lawful) (hS : p.Safe) : MemHyp p := by
  unfold lower at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hr, hr', hf, hf'⟩ := p.checked hwf
    exact MemHyp.ofMemOk hok.1.1 hok.1.2 hr hr' hf hf' hL.1 hL.2 hS
  · cases h

end Millipede.Flat
