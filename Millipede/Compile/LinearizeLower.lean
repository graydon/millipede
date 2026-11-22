import Millipede.Compile.LinearizeProof
import Millipede.Compile.LowerProg

/-!
# Lowering followed by linearization

The lowering `lower` keeps every Core value in byte memory at addresses `[0, Program.memBytes)`,
with the root at `0` and every activation's values above it, and its Lin image `linearize fp M` has
that data region. The generic simulation `linearize_sim` takes as a hypothesis that every access
lies in the region. `lowerInBounds` discharges it for a lowered program that meets `MemHyp`,
because every byte that `lower`'s code touches lies in the static memory it allocated. The memory
refinement carries this fact, since its runs are bounded, every access of a term is below
`bp + n + e.memNeed`, and the reactor's runs pass through every reachable state.

Composed with `lower`, the reactor semantics of a Core program is then simulated with factor 1 by
its Lin image with the data region `[0, p.memBytes)`, given `MemHyp p`. It follows that the Lin run
never gets stuck and has the program's trace.

See doc/design/compiler.md.
-/

namespace Millipede.Lin

theorem extMemOk_of_extAccIn {M : Nat} {f : Flat.Frame} :
    ∀ (as : List Flat.ExtArg), Flat.ExtAccIn M f as → extMemOk M f as = true
  | [], _ => rfl
  | .mem _ _ :: as, h | .outMem _ _ :: as, h => by
    simp only [extMemOk, inDataN, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1, extMemOk_of_extAccIn as h.2⟩
  | .word _ :: as, h | .bytes _ :: as, h | .out _ :: as, h => extMemOk_of_extAccIn (f := f) as h

/-- A bounded access lies in the data region. -/
theorem memIn_of_accIn {M : Nat} {s : Flat.State} (h : Flat.AccIn M s) : MemIn M s := by
  obtain ⟨cur, kont, frame, mem, world, clock⟩ := s
  cases cur with
  | load w x a off =>
    cases w <;> simpa [Flat.AccIn, MemIn, inData, Flat.Width.bytes] using h
  | store w a off b =>
    cases w <;> simpa [Flat.AccIn, MemIn, inData, Flat.Width.bytes] using h
  | ext _ _ _ args => exact extMemOk_of_extAccIn args h
  | _ => simp [MemIn]

/-- The accesses of `lower` stay in its static memory. For a program that meets the hypotheses of
the memory refinement, the Flat code of `lower` touches only addresses below `p.memBytes`, which
hold the root, the next root and the activations' regions below the watermark. -/
theorem lowerInBounds :
    ∀ (p : Program) (fp : Flat.Prog), Flat.lower p = .ok fp → Flat.MemHyp p →
      ∀ (κ : CostModel) (ω : Oracle), InBounds κ ω fp p.memBytes := by
  intro p fp h hH κ ω s hs
  unfold Flat.lower at h
  split at h
  · rename_i hok
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact memIn_of_accIn (Flat.lowerProg_accIn p ω κ hH hok.2 s hs)
  · cases h

/-! ## Composed with `lower` -/

/-- Under the hypotheses of the memory refinement, the reactor semantics of `p` is simulated with
factor 1 by the Lin semantics of `linearize fp p.memBytes`, from source state `0` to its initial
state. -/
theorem lower_linearize_sound (p : Program) (fp : Flat.Prog) (h : Flat.lower p = .ok fp)
    (hH : Flat.MemHyp p) (ω : Oracle) (κ : CostModel) :
    ∃ sim : FwdSim (p.sem ω κ) (Lin.sem κ (linearize fp p.memBytes)) ω, sim.factor = 1 ∧
      ∃ i, sim.R i (0 : Nat) (linearize fp p.memBytes).init := by
  have hB := lowerInBounds p fp h hH κ ω
  obtain ⟨sim₁, hf₁, i₁, hR₁⟩ := Flat.lower_sound p fp h hH ω κ
  refine ⟨sim₁.comp (linearize_sim fp p.memBytes ω κ hB), ?_, (measure fp.init, i₁),
    fp.init, hR₁, linearize_sim_init fp p.memBytes ω κ hB⟩
  show 1 * sim₁.factor = 1
  rw [hf₁]

/-- The Lin run of a lowered program never gets stuck, and in particular never accesses memory
outside its data region. -/
theorem lower_linearize_neverStuck (p : Program) (fp : Flat.Prog)
    (h : Flat.lower p = .ok fp) (hH : Flat.MemHyp p) (ω : Oracle) (κ : CostModel) :
    (Lin.sem κ (linearize fp p.memBytes)).NeverStuck ω (linearize fp p.memBytes).init := by
  obtain ⟨sim, _, i, hR⟩ := lower_linearize_sound p fp h hH ω κ
  exact sim.neverStuck hR (p.sem_neverStuck ω κ ω 0)

/-- The Lin run of a lowered program has the program's trace. -/
theorem lower_linearize_traceEq (p : Program) (fp : Flat.Prog)
    (h : Flat.lower p = .ok fp) (hH : Flat.MemHyp p) (ω : Oracle) (κ : CostModel) :
    TraceEq ((Lin.sem κ (linearize fp p.memBytes)).traceAt ω
      (linearize fp p.memBytes).init) (p.events ω) := by
  obtain ⟨sim, _, i, hR⟩ := lower_linearize_sound p fp h hH ω κ
  have h₁ := sim.traceEq (Lin.sem_mono κ _) hR (p.sem_neverStuck ω κ ω 0)
  rw [Program.sem_traceAt] at h₁
  exact h₁.symm.trans (p.traceEq_traceAfter ω)

end Millipede.Lin
