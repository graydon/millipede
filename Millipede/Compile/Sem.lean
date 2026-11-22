import Millipede.Extern.Oracle

/-!
# The simulation framework

Every level of the compiler, from Flat and Lin to Asm and the machine, and the reactor-level view of
the source, is given as a `Sem`. A `Sem` is a deterministic small-step state machine whose step
takes the extern oracle `ω`, and each state carries the events observed so far and a work counter,
its clock. Determinism holds by construction, because `step` is a function.

There are no final states. A semantics that has stopped after `exit` steps to itself with its trace
and clock unchanged, so every run is infinite unless it gets stuck, which happens on a fault, an
undecodable instruction or an unsupported system call. Never getting stuck is therefore the whole
progress property.

The correctness of a pass is a forward simulation `FwdSim S T ω` for each oracle, in the style of
CompCert's star simulation with a well-founded index. Every source step is matched by zero or more
target steps, and when the target takes no step the index decreases. On every step the target
clock advances by at most `factor` times the source clock's advance. A pass that must relate stack
depths carries that relation as an invariant inside the simulation relation.

The main declarations are the following:

* `Sem`, with the fields `State`, `step`, `events` and `clock`, and `Sem.Mono`, which says that a
  step only extends the events and never decreases the clock;
* `S.run ω s n`, the state after `n` steps, with `NeverStuck`, `traceAt` and `clockAt`;
* `TraceEq a b`, which says that two growing chains of traces have the same limit;
* `FwdSim S T ω`, and the theorems `FwdSim.star` along a source run, `FwdSim.comp` composing two
  simulations, `FwdSim.neverStuck`, `FwdSim.traceEq` and `FwdSim.schedule`.
-/

namespace Millipede

/-- A deterministic small-step semantics with an extern oracle. `step ω s = none` means that `s`
is stuck, and a halted state steps to itself. `events s` is the trace observed so far, oldest
first, and `clock s` counts the work done, in instructions on a machine and in cost units at the
source. -/
structure Sem where
  State : Type
  step : Oracle → State → Option State
  events : State → List Event
  clock : State → Nat

namespace Sem

variable (S : Sem)

/-- Monotonicity laws of a semantics: a step only extends the trace and never decreases the
clock. -/
structure Mono : Prop where
  events : ∀ ω s s', S.step ω s = some s' → S.events s <+: S.events s'
  clock : ∀ ω s s', S.step ω s = some s' → S.clock s ≤ S.clock s'

/-- The state after `n` steps from `s`, or `none` if the run got stuck. It recurses structurally
on `n`. -/
def run (ω : Oracle) : S.State → Nat → Option S.State
  | s, 0 => some s
  | s, n + 1 => (S.step ω s).bind (fun s' => run ω s' n)

/-- The run from `s` never gets stuck. -/
def NeverStuck (ω : Oracle) (s : S.State) : Prop := ∀ n, (S.run ω s n).isSome

/-- The trace observed after `n` steps from `s`, or `[]` if the run is stuck by then. It is
meaningful only together with `NeverStuck`. -/
def traceAt (ω : Oracle) (s : S.State) (n : Nat) : List Event :=
  match S.run ω s n with
  | some s' => S.events s'
  | none => []

/-- The clock after `n` steps from `s`, or `0` if the run is stuck by then. -/
def clockAt (ω : Oracle) (s : S.State) (n : Nat) : Nat :=
  match S.run ω s n with
  | some s' => S.clock s'
  | none => 0

variable {S}

@[simp] theorem run_zero (ω : Oracle) (s : S.State) : S.run ω s 0 = some s := rfl

theorem run_succ (ω : Oracle) (s : S.State) (n : Nat) :
    S.run ω s (n + 1) = (S.step ω s).bind (fun s' => S.run ω s' n) := rfl

theorem run_one {ω : Oracle} {s s' : S.State} (h : S.step ω s = some s') :
    S.run ω s 1 = some s' := by
  simp [run_succ, h]

/-- Runs concatenate. -/
theorem run_add (ω : Oracle) (s : S.State) (n m : Nat) :
    S.run ω s (n + m) = (S.run ω s n).bind (fun s' => S.run ω s' m) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_right_comm, run_succ, run_succ]
    cases S.step ω s with
    | none => rfl
    | some s₁ => simp [ih]

theorem run_add_of {ω : Oracle} {s s' : S.State} {n : Nat} (h : S.run ω s n = some s')
    (m : Nat) : S.run ω s (n + m) = S.run ω s' m := by
  rw [run_add, h]; rfl

/-- A run that is defined at time `n` is defined at every earlier time. -/
theorem run_isSome_of_le {ω : Oracle} {s : S.State} {k n : Nat} (hk : k ≤ n)
    (h : (S.run ω s n).isSome) : (S.run ω s k).isSome := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [run_add] at h
  cases hr : S.run ω s k with
  | none => rw [hr] at h; simp at h
  | some _ => rfl

/-- Along a run, the trace only grows and the clock never decreases. -/
theorem run_mono (hS : S.Mono) {ω : Oracle} {s s' : S.State} {n : Nat}
    (h : S.run ω s n = some s') : S.events s <+: S.events s' ∧ S.clock s ≤ S.clock s' := by
  induction n generalizing s with
  | zero => cases h; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  | succ n ih =>
    rw [run_succ] at h
    cases hn : S.step ω s with
    | none => rw [hn] at h; cases h
    | some s₁ =>
      rw [hn] at h
      have h₂ := ih h
      exact ⟨(hS.events ω s s₁ hn).trans h₂.1, Nat.le_trans (hS.clock ω s s₁ hn) h₂.2⟩

/-- If the run is defined at time `n`, the trace at any earlier time is a prefix of it. -/
theorem traceAt_mono (hS : S.Mono) {ω : Oracle} {s : S.State} {k n : Nat} (hk : k ≤ n)
    (h : (S.run ω s n).isSome) : S.traceAt ω s k <+: S.traceAt ω s n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hk' := run_isSome_of_le hk h
  cases hr : S.run ω s k with
  | none => rw [hr] at hk'; simp at hk'
  | some s₁ =>
    have := run_add_of (m := d) hr
    unfold traceAt
    rw [hr, this]
    rw [this] at h
    cases hr2 : S.run ω s₁ d with
    | none => rw [hr2] at h; simp at h
    | some s₂ => exact (run_mono hS hr2).1

/-- From a never-stuck state, the next state is never stuck. -/
theorem NeverStuck.step {ω : Oracle} {s s' : S.State} (h : S.NeverStuck ω s)
    (hn : S.step ω s = some s') : S.NeverStuck ω s' := by
  intro n
  have := h (n + 1)
  rwa [run_succ, hn] at this

/-- A never-stuck state has a successor. -/
theorem NeverStuck.exists_step {ω : Oracle} {s : S.State} (h : S.NeverStuck ω s) :
    ∃ s', S.step ω s = some s' := by
  have := h 1
  cases hs : S.step ω s with
  | none => simp [run_succ, hs] at this
  | some s' => exact ⟨s', rfl⟩

end Sem

/-- Two growing chains of traces have the same limit: every element of each chain is a prefix of
some element of the other. For chains that only grow, this is equality of the limit traces,
finite or infinite. -/
def TraceEq (a b : Nat → List Event) : Prop :=
  (∀ n, ∃ m, a n <+: b m) ∧ (∀ m, ∃ n, b m <+: a n)

theorem TraceEq.symm {a b : Nat → List Event} (h : TraceEq a b) : TraceEq b a := ⟨h.2, h.1⟩

theorem TraceEq.trans {a b c : Nat → List Event} (h₁ : TraceEq a b) (h₂ : TraceEq b c) :
    TraceEq a c := by
  constructor
  · intro n
    obtain ⟨m, hm⟩ := h₁.1 n
    obtain ⟨k, hk⟩ := h₂.1 m
    exact ⟨k, hm.trans hk⟩
  · intro n
    obtain ⟨m, hm⟩ := h₂.2 n
    obtain ⟨k, hk⟩ := h₁.2 m
    exact ⟨k, hm.trans hk⟩

/-- A forward simulation of `S` by `T` under oracle `ω`, with a well-founded index for stuttering
and a linear resource clause.

* `R i s t` says that target state `t` matches source state `s` at index `i`, and related states
  have the same trace.
* `step` says that when `s` steps to `s'`, `T` runs `n ≥ 0` steps from `t` to some `t'` that
  matches `s'`, the index decreases if `n = 0`, and the target clock advances by at most `factor`
  times the source clock's advance. The clock bound is written without subtraction, as
  `clock t' + factor * clock s ≤ clock t + factor * clock s'`. -/
structure FwdSim (S T : Sem) (ω : Oracle) where
  Idx : Type
  lt : Idx → Idx → Prop
  wf : WellFounded lt
  R : Idx → S.State → T.State → Prop
  factor : Nat
  events_eq : ∀ {i s t}, R i s t → S.events s = T.events t
  step : ∀ {i s t s'}, R i s t → S.step ω s = some s' →
    ∃ i' t' n, T.run ω t n = some t' ∧ R i' s' t' ∧ (0 < n ∨ lt i' i) ∧
      T.clock t' + factor * S.clock s ≤ T.clock t + factor * S.clock s'

namespace FwdSim

variable {S T U : Sem} {ω : Oracle}

private theorem comb {α : Type} {r : α → α → Prop} {i i₁ i' : α} {m₁ m₂ : Nat}
    (h₁ : 0 < m₁ ∨ r i₁ i) (h₂ : 0 < m₂ ∨ i' = i₁ ∨ Relation.TransGen r i' i₁) :
    0 < m₁ + m₂ ∨ Relation.TransGen r i' i := by
  rcases h₁ with h₁ | h₁
  · exact Or.inl (by omega)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (by omega)
    · subst h₂; exact Or.inr (.single h₁)
    · exact Or.inr (.tail h₂ h₁)

/-- Simulation along a source run of `n` steps. The index ends equal, which happens only when
`n = 0`, or smaller in the transitive closure, unless the target moved. The clock clauses add up
along the run. -/
theorem star (sim : FwdSim S T ω) :
    ∀ (n : Nat) {i : sim.Idx} {s t s' : _}, sim.R i s t → S.run ω s n = some s' →
    ∃ i' t' m, T.run ω t m = some t' ∧ sim.R i' s' t' ∧
      (0 < m ∨ i' = i ∨ Relation.TransGen sim.lt i' i) ∧
      (0 < n → 0 < m ∨ Relation.TransGen sim.lt i' i) ∧
      T.clock t' + sim.factor * S.clock s ≤ T.clock t + sim.factor * S.clock s' := by
  intro n
  induction n with
  | zero =>
    intro i s t s' hR h
    cases h
    exact ⟨i, t, 0, rfl, hR, Or.inr (Or.inl rfl), by simp, Nat.le_refl _⟩
  | succ n ih =>
    intro i s t s' hR h
    rw [Sem.run_succ] at h
    cases hn : S.step ω s with
    | none => rw [hn] at h; cases h
    | some s₁ =>
      rw [hn] at h
      obtain ⟨i₁, t₁, m₁, hm₁, hR₁, hd₁, hc₁⟩ := sim.step hR hn
      obtain ⟨i', t', m₂, hm₂, hR', hw₂, _, hc₂⟩ := ih hR₁ h
      have hs := comb hd₁ hw₂
      refine ⟨i', t', m₁ + m₂, ?_, hR', hs.elim Or.inl (fun h => Or.inr (Or.inr h)),
        fun _ => hs, by omega⟩
      rw [Sem.run_add_of hm₁]; exact hm₂

/-- Simulations compose. The index of the composite is lexicographic, with the outer pass's index,
transitively closed, first, and the resource factors multiply. -/
def comp (s₁₂ : FwdSim S T ω) (s₂₃ : FwdSim T U ω) : FwdSim S U ω where
  Idx := s₂₃.Idx × s₁₂.Idx
  lt := Prod.Lex (Relation.TransGen s₂₃.lt) s₁₂.lt
  wf := (Prod.lex ⟨_, s₂₃.wf.transGen⟩ ⟨_, s₁₂.wf⟩).wf
  R := fun i s u => ∃ t, s₁₂.R i.2 s t ∧ s₂₃.R i.1 t u
  factor := s₂₃.factor * s₁₂.factor
  events_eq := fun ⟨_, h₁, h₂⟩ => (s₁₂.events_eq h₁).trans (s₂₃.events_eq h₂)
  step := by
    intro i s u s' hR hs
    obtain ⟨t, h₁, h₂⟩ := hR
    obtain ⟨i₁', t', n, hrun, hR₁', hd₁, hc₁⟩ := s₁₂.step h₁ hs
    obtain ⟨i₂', u', m, hrunU, hR₂', hw, hst, hc₂⟩ := s₂₃.star n h₂ hrun
    refine ⟨(i₂', i₁'), u', m, hrunU, ⟨t', hR₁', hR₂'⟩, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · have hlt : s₁₂.lt i₁' i.2 := by
            rcases hd₁ with h | h
            · omega
            · exact h
          rcases hw with h | h | h
          · omega
          · obtain ⟨a, b⟩ := i
            simp only at h; subst h; exact Or.inr (Prod.Lex.right _ hlt)
          · obtain ⟨a, b⟩ := i; exact Or.inr (Prod.Lex.left _ _ h)
        · rcases hst hn with h | h
          · omega
          · obtain ⟨a, b⟩ := i; exact Or.inr (Prod.Lex.left _ _ h)
      · exact Or.inl hm
    · have h3 := Nat.mul_le_mul_left s₂₃.factor hc₁
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc] at h3
      omega

/-- A never-stuck source drives the target arbitrarily far: from related states, for every `N`
there are related states reached after `m ≥ N` target steps. -/
theorem reach (sim : FwdSim S T ω) (N : Nat) :
    ∀ (i : sim.Idx) (s : S.State) (t : T.State), sim.R i s t → S.NeverStuck ω s →
    ∃ i' s' t' n m, S.run ω s n = some s' ∧ T.run ω t m = some t' ∧ sim.R i' s' t' ∧
      N ≤ m := by
  induction N using Nat.strongRecOn with
  | ind N ihN =>
  intro i
  refine sim.wf.induction (C := fun i => ∀ (s : S.State) (t : T.State), sim.R i s t →
    S.NeverStuck ω s → ∃ i' s' t' n m, S.run ω s n = some s' ∧ T.run ω t m = some t' ∧
      sim.R i' s' t' ∧ N ≤ m) i ?_
  intro i ihi s t hR hs
  obtain ⟨s₁, hst⟩ := hs.exists_step
  have hs₁ : S.NeverStuck ω s₁ := hs.step hst
  have hn₁ : S.run ω s 1 = some s₁ := Sem.run_one hst
  obtain ⟨i', t', k, hk, hR', hd, _⟩ := sim.step hR hst
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    have hlt : sim.lt i' i := by
      rcases hd with h | h
      · omega
      · exact h
    cases hk
    obtain ⟨i'', s'', t'', n, m, h₁, h₂, h₃, h₄⟩ := ihi i' hlt s₁ t hR' hs₁
    refine ⟨i'', s'', t'', 1 + n, m, ?_, h₂, h₃, h₄⟩
    rw [Sem.run_add_of hn₁]; exact h₁
  · by_cases hNk : N ≤ k
    · exact ⟨i', s₁, t', 1, k, hn₁, hk, hR', hNk⟩
    · obtain ⟨i'', s'', t'', n, m, h₁, h₂, h₃, h₄⟩ :=
        ihN (N - k) (by omega) i' s₁ t' hR' hs₁
      refine ⟨i'', s'', t'', 1 + n, k + m, ?_, ?_, h₃, by omega⟩
      · rw [Sem.run_add_of hn₁]; exact h₁
      · rw [Sem.run_add_of hk]; exact h₂

/-- A forward simulation from a source that never gets stuck makes the deterministic target never
stuck. -/
theorem neverStuck (sim : FwdSim S T ω) {i : sim.Idx} {s : S.State} {t : T.State}
    (hR : sim.R i s t) (hs : S.NeverStuck ω s) : T.NeverStuck ω t := by
  intro N
  obtain ⟨_, _, t', _, m, _, h₂, _, h₄⟩ := sim.reach N i s t hR hs
  exact Sem.run_isSome_of_le h₄ (by rw [h₂]; rfl)

/-- A forward simulation from a never-stuck source to a monotone target gives the same event trace,
finite or infinite. -/
theorem traceEq (sim : FwdSim S T ω) (hT : T.Mono) {i : sim.Idx} {s : S.State}
    {t : T.State} (hR : sim.R i s t) (hs : S.NeverStuck ω s) :
    TraceEq (S.traceAt ω s) (T.traceAt ω t) := by
  constructor
  · intro n
    have hn := hs n
    cases hsn : S.run ω s n with
    | none => rw [hsn] at hn; simp at hn
    | some s' =>
      obtain ⟨i', t', m, hm, hR', _⟩ := sim.star n hR hsn
      refine ⟨m, ?_⟩
      simp only [Sem.traceAt, hsn, hm, sim.events_eq hR']
      exact List.prefix_refl _
  · intro N
    obtain ⟨_, s', t', n, m, h₁, h₂, h₃, h₄⟩ := sim.reach N i s t hR hs
    refine ⟨n, ?_⟩
    have he : S.traceAt ω s n = T.events t' := by
      simp only [Sem.traceAt, h₁, sim.events_eq h₃]
    rw [he]
    have := Sem.traceAt_mono hT h₄ (by rw [h₂]; rfl)
    simp only [Sem.traceAt, h₂] at this
    exact this

/-- Along a never-stuck source run there are non-decreasing target times `marks k`, with
`marks 0 = 0`, at which the target state matches the source state after `k` steps, and between
consecutive marks the target clock advances by at most `factor` times the source clock's advance.
This is how per-step resource bounds reach the machine. -/
theorem schedule (sim : FwdSim S T ω) {i : sim.Idx} {s₀ : S.State} {t₀ : T.State}
    (hR : sim.R i s₀ t₀) (hs : S.NeverStuck ω s₀) :
    ∃ marks : Nat → Nat, marks 0 = 0 ∧ ∀ k, marks k ≤ marks (k + 1) ∧
      (∃ j s t, S.run ω s₀ k = some s ∧ T.run ω t₀ (marks k) = some t ∧ sim.R j s t) ∧
      T.clockAt ω t₀ (marks (k + 1)) + sim.factor * S.clockAt ω s₀ k ≤
        T.clockAt ω t₀ (marks k) + sim.factor * S.clockAt ω s₀ (k + 1) := by
  let P : Nat → sim.Idx × Nat → Prop := fun k x =>
    ∃ s t, S.run ω s₀ k = some s ∧ T.run ω t₀ x.2 = some t ∧ sim.R x.1 s t
  have key : ∀ k (x : sim.Idx × Nat), P k x → ∃ y : sim.Idx × Nat, x.2 ≤ y.2 ∧ P (k + 1) y ∧
      T.clockAt ω t₀ y.2 + sim.factor * S.clockAt ω s₀ k ≤
        T.clockAt ω t₀ x.2 + sim.factor * S.clockAt ω s₀ (k + 1) := by
    intro k x ⟨s, t, hs₁, ht₁, hR₁⟩
    have hsk : S.NeverStuck ω s := by
      intro n; have := hs (k + n); rwa [Sem.run_add_of hs₁] at this
    obtain ⟨s', hn⟩ := hsk.exists_step
    have hk1 : S.run ω s₀ (k + 1) = some s' := by
      rw [Sem.run_add_of hs₁]; exact Sem.run_one hn
    obtain ⟨i', t', n, hrun, hR', _, hc⟩ := sim.step hR₁ hn
    refine ⟨(i', x.2 + n), Nat.le_add_right _ _, ⟨s', t', hk1, ?_, hR'⟩, ?_⟩
    · show T.run ω t₀ (x.2 + n) = some t'
      rw [Sem.run_add_of ht₁]; exact hrun
    · simp only [Sem.clockAt, hs₁, hk1, Sem.run_add_of ht₁, hrun, ht₁]
      exact hc
  have h0 : P 0 (i, 0) := ⟨s₀, t₀, rfl, rfl, hR⟩
  let f : (k : Nat) → {x : sim.Idx × Nat // P k x} := fun k =>
    @Nat.rec (fun k => {x : sim.Idx × Nat // P k x}) ⟨(i, 0), h0⟩
      (fun k ih => ⟨Classical.choose (key k ih.1 ih.2),
        (Classical.choose_spec (key k ih.1 ih.2)).2.1⟩) k
  refine ⟨fun k => (f k).1.2, rfl, fun k => ?_⟩
  have hspec := Classical.choose_spec (key k (f k).1 (f k).2)
  obtain ⟨s, t, h₁, h₂, h₃⟩ := (f k).2
  exact ⟨hspec.1, ⟨_, s, t, h₁, h₂, h₃⟩, hspec.2.2⟩

end FwdSim

end Millipede
