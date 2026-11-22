import Millipede.Compile.LowerSound

/-!
# `lower` as a forward simulation of the reactor

The root lives in static storage at address `0`, since the main activation's base pointer is `0`.
`init` builds the root in place, and each reactor step runs with the root as its parameter. A step
that hands its parameter back in place copies nothing, and any other step writes its result to a
temporary above the root, which is then copied over it.

`Flat.lowerSim p ω κ` says that for every oracle and cost model, the Flat run of `lowerProg p`
simulates the reactor-level source semantics with factor 1. After reactor step `j`, matched states
have the source world and have either halted or reached the reactor loop head with the root's bytes
at `[0, size)` representing `(p.run ω j).1`.

`Flat.lower_sound` packages this for the pipeline under the hypotheses of the memory refinement.
The program is in the lowered fragment, obeys the block rule and the borrow discipline, has lawful
building blocks and is safe; under the block rule `init` writes nothing bound outside it and `step`
writes only its root.
-/

namespace Millipede.Flat

/-- The hypotheses of the memory refinement for a program: the refinement property of `init` and
`step` for every cost model and oracle, the block rule, the borrow discipline, lawful building
blocks, and safety. On the lowered fragment `lowerM_sound` gives the refinement property. -/
structure MemHyp (p : Program) : Prop where
  initSound : ∀ κ ω, MSoundAt κ ω p.init
  stepSound : ∀ κ ω, MSoundAt κ ω p.step
  initRestr : p.init.Restr []
  stepRestr : p.step.Restr [true]
  initFrozen : p.init.Frozen
  stepFrozen : p.step.Frozen
  initLawful : p.init.Lawful
  stepLawful : p.step.Lawful
  safe : p.Safe

/-- `MemHyp` for a program in the lowered fragment. -/
theorem MemHyp.ofMemOk {p : Program} (hi : p.init.memOk = true)
    (hs : p.step.memOk = true)
    (initRestr : p.init.Restr []) (stepRestr : p.step.Restr [true])
    (initFrozen : p.init.Frozen) (stepFrozen : p.step.Frozen)
    (initLawful : p.init.Lawful) (stepLawful : p.step.Lawful) (safe : p.Safe) : MemHyp p :=
  ⟨fun κ ω => lowerM_sound κ ω _ hi, fun κ ω => lowerM_sound κ ω _ hs, initRestr, stepRestr,
    initFrozen, stepFrozen, initLawful, stepLawful, safe⟩

/-- The reactor loop of a lowered program. -/
abbrev memLoop (p : Program) : Stmt :=
  .while .skip (.imm 1) (stepCode p)

/-- One reactor step from a state whose root bytes `[0, size)` represent `v`: the code simulates the
step's `exec` and leaves the root bytes representing its value. The step runs in place when it
hands back its root. Otherwise it runs in tail mode `none` with the temporary `[size, 2·size)` above
the root as its destination, and `copyM` copies the result over the root. -/
theorem stepCode_sim (p : Program) (ω : Oracle) (κ : CostModel) (hH : MemHyp p)
    (hmem : p.memBytes < UInt64.size) (v : p.State.carrier) (w : World) (hw : w.halted = false)
    (hsafe : p.step.safe ω (.cons v .nil) w) (k : List Kont) (f : Frame) (m : Heap) (c : Nat)
    (hf : f BP = UInt64.ofNat 0) (hv : Data.reprBytes v (rd m 0 p.State.size)) :
    MSim κ ω p.memBytes ⟨stepCode p, k, f, m, w, c⟩ k
      (fun v _ h => Data.reprBytes v (rd h 0 p.State.size)) (fun _ => False)
      (p.step.exec ω κ p.stepHb (.cons v .nil) w) := by
  have hmb : p.State.size + max p.init.memNeed (p.stepTmp + p.step.memNeed) < UInt64.size := hmem
  have hms := Nat.le_max_right p.init.memNeed (p.stepTmp + p.step.memNeed)
  have henv : MEnvRel m 0 (.cons v .nil) [.own 0] [⟨0, none, none, none⟩] :=
    ⟨fun _ => VarRel.of_exact (by simpa using hv), trivial, trivial⟩
  have hvs : ∀ tm : Tl, VS [⟨0, none, none, none⟩] (p.step.VSafe · tm) :=
    fun _ i h => absurd (by cases i <;> rfl) h
  have hhole : HoleAv p.step [⟨0, none, none, none⟩] := fun i H h => by cases i <;> simp at h
  by_cases hc : p.step.Conf (.whole 0) = true
  · have ht : p.stepTmp = 0 := by simp [Program.stepTmp, hc]
    rw [show p.stepHb = .whole 0 by simp [Program.stepHb, ← Exp.conf_whole, hc]]
    rw [ht] at hms
    have hlay : Lay 0 p.State.size [p.State] [.own 0] [⟨0, none, none, none⟩] [true] :=
      ⟨⟨by simp [Loc.off, Loc.size], ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun H e => by cases e⟩,
        trivial, trivial⟩
    have hS := hH.stepSound κ ω (.whole 0) p.memBytes [true] [.own 0] [⟨0, none, none, none⟩]
      p.State.size 0 0 (.cons v .nil) k f m w c hc rfl hH.stepRestr hH.stepLawful hH.stepFrozen
      hhole hlay (by simp [Tl.dsz]) ⟨Or.inl (by simp [Tl.dsz]), Or.inl (by simp [Tl.dsz]), trivial⟩
      (by omega) hf henv hsafe hw (by unfold Program.memBytes; omega) (hvs _)
      (SlotHyp.of_none rfl fun i => by cases i <;> rfl)
    simp only [stepCode, hc, ↓reduceIte]
    exact (hS.post fun _ _ hq _ => by simpa [TQ] using hq).weaken fun _ h => h.elim
  · have ht : p.stepTmp = p.State.size := by simp [Program.stepTmp, hc]
    rw [show p.stepHb = .copy by simp [Program.stepHb, ← Exp.conf_whole, hc]]
    rw [ht] at hms
    have hlay : Lay 0 (p.State.size + p.State.size) [p.State] [.own 0] [⟨0, none, none, none⟩]
        [true] :=
      ⟨⟨by simp [Loc.off, Loc.size], ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun H e => by cases e⟩,
        trivial, trivial⟩
    have hS := hH.stepSound κ ω .none p.memBytes [true] [.own 0] [⟨0, none, none, none⟩]
      (p.State.size + p.State.size) p.State.size 0 (.cons v .nil) (.seq (copyM p.State.size 0
        p.State.size) :: k) f m w c p.step.conf_none trivial hH.stepRestr hH.stepLawful
      hH.stepFrozen hhole hlay (by simp [Tl.dsz])
      ⟨Or.inr (by simp [Loc.off, Loc.size]), by simp [SI.Out, Disj, Tl.dsz], trivial⟩
      (by omega) hf henv hsafe hw (by unfold Program.memBytes; omega) (hvs _)
      (SlotHyp.of_none rfl fun i => by cases i <;> rfl)
    simp only [stepCode, hc, Bool.false_eq_true, ↓reduceIte]
    have := (MSim.seq_intro (k := k) (Q := fun v _ h => Data.reprBytes v (rd h 0 p.State.size))
      (prot := fun _ => False) hw (MSim.bind hS (fun _ => rfl) (fun _ h => h.elim)
        (prot₂ := fun _ => False) (pf₂ := fun _ => False) (pf := fun _ => False) (r₂ := ⟨(p.step.exec ω κ .copy (.cons v .nil) w).val,
          (p.step.exec ω κ .copy (.cons v .nil) w).world, 0⟩) fun f₁ m₁ hf₁ hq _ hw₁ => by
        obtain ⟨f', hf', hr⟩ := copyB_runs (κ := κ) (ω := ω) (L := p.memBytes) (.slot BP)
          (.slot BP) (by simp) (by simp) p.State.size p.State.size 0 0 0 f₁ m₁
          (by simp [hf₁, hf]) (by simp [hf₁, hf]) (by omega) (by omega) (Or.inr (by omega))
          (by unfold Program.memBytes; omega) (by unfold Program.memBytes; omega)
        refine MSim.done hw₁ hr rfl rfl (by rw [hf' BP (by decide)]) ?_ (fun _ h => h.elim)
        have hq' : Data.reprBytes (p.step.exec ω κ .copy (.cons v .nil) w).val
            (rd m₁ p.State.size p.State.size) := by simpa [TQ] using hq
        have hB := rd_wr m₁ 0 (rd m₁ p.State.size p.State.size) (by simp; omega)
        rw [rd_length] at hB
        simpa [hB] using hq'))
    exact this.of_eq rfl rfl (by simp)

/-- The matching relation of the memory reactor simulation. -/
def MReactorRel (p : Program) (ω : Oracle) : Nat → State → Prop
  | 0, t => t = (lowerProg p).init
  | j + 1, t => t.world = (p.run ω j).2 ∧
    (t.world.halted = true ∨
      (t.cur = memLoop p ∧ t.kont = [] ∧ t.frame BP = UInt64.ofNat 0 ∧
        Data.reprBytes (p.run ω j).1 (rd t.mem 0 p.State.size)))

theorem mreactor_step (p : Program) (ω : Oracle) (κ : CostModel) (hH : MemHyp p)
    (hmem : p.memBytes < UInt64.size) (k : Nat) (t : State) (hR : MReactorRel p ω k t) :
    ∃ t', ReachL κ ω p.memBytes (next κ ω t) t' ∧ MReactorRel p ω (k + 1) t' ∧
      t'.clock ≤ t.clock + p.stepCost k ω κ := by
  have hmb : p.State.size + max p.init.memNeed (p.stepTmp + p.step.memNeed) < UInt64.size := hmem
  have hmi := Nat.le_max_left p.init.memNeed (p.stepTmp + p.step.memNeed)
  cases k with
  | zero =>
    simp only [MReactorRel] at hR
    subst hR
    have hS := hH.initSound κ ω .none p.memBytes [] [] [] p.State.size 0 0 .nil [.seq (memLoop p)]
      Frame.zero (fun _ => 0) World.init 0 (by simp) trivial hH.initRestr hH.initLawful
      hH.initFrozen (fun i H h => by simp at h) trivial (by simp [Tl.dsz]) trivial
      (by omega) rfl trivial (hH.safe ω).1 rfl (by unfold Program.memBytes; omega)
      (fun i h => absurd (by cases i <;> rfl) h) (SlotHyp.of_none rfl fun _ => rfl)
    rw [Tl.hb_none] at hS
    obtain ⟨s₁, hr₁, hw₁, hc₁, h4⟩ := hS
    have hwr : (p.init.exec ω κ .copy .nil World.init).world = (p.run ω 0).2 := Exp.exec_world _ _ _ _ _
    have hcost : (p.init.exec ω κ .copy .nil World.init).steps ≤ p.stepCost 0 ω κ :=
      Exp.exec_steps_le _ _ _ _ _
    have hr₀ : ReachL κ ω p.memBytes (next κ ω (lowerProg p).init) s₁ := by
      rw [next_run rfl]; simp only [lowerProg, Prog.init, exec1]; exact hr₁
    cases hh : (p.init.exec ω κ .copy .nil World.init).world.halted with
    | true =>
      refine ⟨s₁, hr₀, ⟨by rw [hw₁, hwr], Or.inl (by rw [hw₁, hh])⟩, ?_⟩
      simp only [Prog.init] at hc₁ ⊢; omega
    | false =>
      rcases h4 with h' | ⟨hcur, hk, hcl, hf, hv, _⟩
      · rw [hh] at h'; cases h'
      obtain ⟨cur, kont, f₁, m₁, w₁, c₁⟩ := s₁
      simp only at hcur hk hcl hf hv hw₁
      subst hcur hk hw₁ hcl
      refine ⟨⟨memLoop p, [], f₁, m₁, (p.init.exec ω κ .copy .nil World.init).world, 0 +
          (p.init.exec ω κ .copy .nil World.init).steps⟩,
        hr₀.trans (ReachL.step' hh (by simp only [exec1]; exact ReachL.refl _)),
        ⟨hwr, Or.inr ⟨rfl, rfl, hf, ?_⟩⟩, ?_⟩
      · show Data.reprBytes (p.init.denote ω .nil World.init).1 _
        rw [← Exp.exec_val ω κ]; simpa [TQ] using hv
      · simp only [Prog.init]; omega
  | succ j =>
    obtain ⟨cur, kont, f, m, w, c⟩ := t
    simp only [MReactorRel] at hR
    obtain ⟨hw, hR⟩ := hR
    subst hw
    cases hh : (p.run ω j).2.halted with
    | true =>
      refine ⟨⟨cur, kont, f, m, (p.run ω j).2, c⟩, by simp [next, hh]; exact ReachL.refl _, ?_,
        Nat.le_add_right _ _⟩
      simp only [MReactorRel]
      exact ⟨(p.run_halted ω j hh).symm, Or.inl hh⟩
    | false =>
      rcases hR with h' | ⟨hcur, hk, hf, hv⟩
      · rw [hh] at h'; cases h'
      subst hcur hk
      have hS := stepCode_sim p ω κ hH hmem (p.run ω j).1 (p.run ω j).2 hh ((hH.safe ω).2 j)
        [.seq (memLoop p)] f m c hf hv
      obtain ⟨s₁, hr₁, hw₁, hc₁, h4⟩ := hS
      have hwr : (p.step.exec ω κ p.stepHb (.cons (p.run ω j).1 .nil) (p.run ω j).2).world =
          (p.run ω (j + 1)).2 := Exp.exec_world _ _ _ _ _
      have hcost : (p.step.exec ω κ p.stepHb (.cons (p.run ω j).1 .nil) (p.run ω j).2).steps ≤
          p.stepCost (j + 1) ω κ := Exp.exec_steps_le _ _ _ _ _
      have hr₀ : ReachL κ ω p.memBytes (next κ ω ⟨memLoop p, [], f, m, (p.run ω j).2, c⟩) s₁ := by
        have h10 : ((1 : UInt64) = 0) = False := by decide
        rw [next_run hh]; simp only [exec1]
        exact ReachL.step' hh (by
          simp only [exec1, eval_imm, h10, ↓reduceIte]; exact hr₁)
      cases hh' : (p.step.exec ω κ p.stepHb (.cons (p.run ω j).1 .nil) (p.run ω j).2).world.halted with
      | true =>
        refine ⟨s₁, hr₀, ⟨by rw [hw₁, hwr], Or.inl (by rw [hw₁, hh'])⟩, ?_⟩
        simp only at hc₁ ⊢; omega
      | false =>
        rcases h4 with h' | ⟨hcur, hk, hcl, hf', hv', _⟩
        · rw [hh'] at h'; cases h'
        obtain ⟨cur, kont, f₁, m₁, w₁, c₁⟩ := s₁
        simp only at hcur hk hcl hf' hv' hw₁
        subst hcur hk hw₁ hcl
        have hfb : f₁ BP = UInt64.ofNat 0 := hf'.trans hf
        refine ⟨⟨memLoop p, [], f₁, m₁, (p.step.exec ω κ p.stepHb (.cons (p.run ω j).1 .nil) (p.run ω j).2).world,
            c + (p.step.exec ω κ p.stepHb (.cons (p.run ω j).1 .nil) (p.run ω j).2).steps⟩,
          hr₀.trans (ReachL.step' hh' (by simp only [exec1]; exact ReachL.refl _)),
          ⟨hwr, Or.inr ⟨rfl, rfl, hfb, ?_⟩⟩, by simp only; omega⟩
        show Data.reprBytes (p.step.denote ω (.cons (p.run ω j).1 .nil) (p.run ω j).2).1 _
        rw [← Exp.exec_val ω κ]
        exact hv'

/-- `lower` simulates the reactor with factor 1, for every oracle `ω` and cost model `κ`, under the
hypotheses of the memory refinement. -/
def lowerSim (p : Program) (ω : Oracle) (κ : CostModel) (hH : MemHyp p)
    (hmem : p.memBytes < UInt64.size) : FwdSim (p.sem ω κ) (Flat.sem κ) ω where
  Idx := Unit
  lt _ _ := False
  wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  R _ k t := MReactorRel p ω k t
  factor := 1
  events_eq := by
    intro _ k t hR
    cases k with
    | zero => simp only [MReactorRel] at hR; subst hR; rfl
    | succ j => simp only [MReactorRel] at hR; exact (congrArg World.events hR.1).symm
  step := by
    intro _ k t k' hR hs
    cases hs
    obtain ⟨t', ⟨n, hn, _⟩, hR', hc⟩ := mreactor_step p ω κ hH hmem k t hR
    refine ⟨(), t', n + 1, ?_, hR', Or.inl (Nat.succ_pos _), ?_⟩
    · rw [run_eq]; exact congrArg some hn
    · show t'.clock + 1 * p.costPrefix ω κ k ≤ t.clock + 1 * (p.costPrefix ω κ k + p.stepCost k ω κ)
      omega

/-- The correctness of `lower`, in the form the pipeline composes. If `lower p = .ok fp` and the
program meets the hypotheses of the memory refinement, then for every oracle and cost model there is
a forward simulation with factor 1 from the reactor semantics of `p` to the Flat run of `fp`. -/
theorem lower_sound (p : Program) (fp : Prog) (h : lower p = .ok fp) (hH : MemHyp p)
    (ω : Oracle) (κ : CostModel) :
    ∃ sim : FwdSim (p.sem ω κ) (Flat.sem κ) ω, sim.factor = 1 ∧ ∃ i, sim.R i 0 fp.init := by
  unfold lower at h
  split at h
  · rename_i hok
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨lowerSim p ω κ hH hok.2, rfl, (), rfl⟩
  · cases h

/-- The Flat run of a lowered program has the same trace as the source, for every oracle. -/
theorem lower_traceEq (p : Program) (fp : Prog) (h : lower p = .ok fp) (hH : MemHyp p)
    (ω : Oracle) (κ : CostModel) : TraceEq ((Flat.sem κ).traceAt ω fp.init) (p.events ω) := by
  obtain ⟨sim, _, i, hR⟩ := lower_sound p fp h hH ω κ
  have h₁ := sim.traceEq (sem_mono κ) hR (p.sem_neverStuck ω κ ω 0)
  rw [Program.sem_traceAt] at h₁
  exact h₁.symm.trans (p.traceEq_traceAfter ω)

/-! ## The lowered program stays in its static memory -/

/-- One transition either keeps the world or leaves the state at `skip`, since only an extern call
changes the world. -/
theorem exec1_world_or_skip (κ : CostModel) (ω : Oracle) (s : State) :
    (exec1 κ ω s).world = s.world ∨ (exec1 κ ω s).cur = .skip := by
  unfold exec1
  split <;> (try split) <;> simp

/-- A halted state reached from a start that is running or finished is at `skip`. -/
theorem nextN_halted_skip (κ : CostModel) (ω : Oracle) :
    ∀ (n : Nat) (s : State), (s.world.halted = true → s.cur = .skip) →
      ((nextN κ ω n s).world.halted = true → (nextN κ ω n s).cur = .skip)
  | 0, _, h => h
  | n + 1, s, h => by
    refine nextN_halted_skip κ ω n (next κ ω s) ?_
    cases hh : s.world.halted with
    | true => simp only [next, hh, ite_true]; exact fun _ => h hh
    | false =>
      rw [next_run hh]
      intro hh'
      rcases exec1_world_or_skip κ ω s with e | e
      · rw [e, hh] at hh'; cases hh'
      · exact e

/-- The state a matched reactor state is in makes no memory access. -/
theorem MReactorRel.accIn (p : Program) (ω : Oracle) (M : Nat) :
    ∀ (j : Nat) (t : State), MReactorRel p ω j t →
      (t.world.halted = true → t.cur = .skip) → AccIn M t
  | 0, t, hR, _ => by simp only [MReactorRel] at hR; subst hR; trivial
  | j + 1, t, hR, hsk => by
    simp only [MReactorRel] at hR
    rcases hR.2 with hh | ⟨hcur, _⟩
    · unfold AccIn; rw [hsk hh]; trivial
    · unfold AccIn; rw [hcur]; trivial

/-- Every state that the lowered program reaches accesses memory only below `p.memBytes`, under the
hypotheses of the memory refinement. The reactor simulation runs through every reachable state,
because each reactor step is at least one transition, and its runs are bounded. -/
theorem lowerProg_accIn (p : Program) (ω : Oracle) (κ : CostModel) (hH : MemHyp p)
    (hmem : p.memBytes < UInt64.size) (s : State) (hs : Reach κ ω (lowerProg p).init s) :
    AccIn p.memBytes s := by
  have hsk : ∀ m, (nextN κ ω m (lowerProg p).init).world.halted = true →
      (nextN κ ω m (lowerProg p).init).cur = .skip :=
    fun m => nextN_halted_skip κ ω m _ (by intro h; cases h)
  have key : ∀ j, ∃ N, MReactorRel p ω j (nextN κ ω N (lowerProg p).init) ∧ j ≤ N ∧
      ∀ m, m < N → AccIn p.memBytes (nextN κ ω m (lowerProg p).init) := by
    intro j
    induction j with
    | zero => exact ⟨0, rfl, Nat.le_refl _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      obtain ⟨N, hR, hjN, hacc⟩ := ih
      obtain ⟨t', ⟨n, hn, hacc'⟩, hR', _⟩ := mreactor_step p ω κ hH hmem j _ hR
      have e : nextN κ ω (N + (n + 1)) (lowerProg p).init = t' := by
        rw [nextN_add]; exact hn
      refine ⟨N + (n + 1), e ▸ hR', by omega, fun m hm => ?_⟩
      rcases Nat.lt_trichotomy m N with h | h | h
      · exact hacc m h
      · subst h; exact MReactorRel.accIn p ω _ j _ hR (hsk m)
      · have := hacc' (m - N - 1) (by omega)
        rwa [show nextN κ ω (m - N - 1) (next κ ω (nextN κ ω N (lowerProg p).init)) =
            nextN κ ω m (lowerProg p).init by
          rw [← show nextN κ ω (m - N - 1 + 1) (nextN κ ω N (lowerProg p).init) =
              nextN κ ω (m - N - 1) (next κ ω (nextN κ ω N (lowerProg p).init)) from rfl,
            ← nextN_add, show N + (m - N - 1 + 1) = m by omega]] at this
  obtain ⟨m, rfl⟩ := hs
  obtain ⟨N, _, hmN, hacc⟩ := key (m + 1)
  exact hacc m (by omega)

end Millipede.Flat
