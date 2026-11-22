/-!
# Parallel moves

A call sequence passes arguments into registers that may be the sources of other arguments, and a
return sequence may deliver results into registers that hold other results. Both are parallel
moves: every destination receives the value its source held before any move. This module
sequentialises a parallel move into single register moves with one temporary and proves the
sequence correct for any register type.

`seq tmp n ms` drops the moves of a register to itself, emits a move whose destination is no
other move's source while there is one, and otherwise, when the remaining moves form cycles,
copies the first move's source into `tmp` and reads it from there. It refuses (`none`) when fuel
runs out or when `tmp` is already a pending source at a cycle; neither happens for fuel
`2 * ms.length + 1`, but only the accepted sequences need to be correct. `seq_run` says that an
accepted sequence leaves every register but `tmp` as the parallel move `par` does, provided the
destinations are distinct and `tmp` is none of them.
-/

namespace Millipede.Sel.PMove

variable {R V : Type} [DecidableEq R]

/-- The register file after the single move `d ← s`. -/
def step (f : R → V) (d s : R) : R → V := fun r => if r = d then f s else f r

/-- The register file after a sequence of single moves. -/
def run (f : R → V) : List (R × R) → R → V
  | [] => f
  | (d, s) :: ms => run (step f d s) ms

/-- The source of the move into `r`, if any. -/
def src? (ms : List (R × R)) (r : R) : Option R := (ms.find? (·.1 = r)).map (·.2)

/-- The register file after the parallel move `ms`. -/
def par (f : R → V) (ms : List (R × R)) (r : R) : V :=
  match src? ms r with
  | some s => f s
  | none => f r

/-- One move of the sequence for the parallel move `ms`, which has no move of a register to
itself, and the parallel move left after it: a move whose destination is no pending source, or else
the copy of the first move's source into `tmp`, which the remaining moves then read. It refuses when
`tmp` is a pending source. -/
def pick (tmp : R) (ms : List (R × R)) : Option ((R × R) × List (R × R)) :=
  match ms.find? (fun p => !(ms.any fun q => q.2 = p.1)) with
  | some (d, s) => some ((d, s), ms.filter fun p => p.1 ≠ d)
  | none => match ms with
    | [] => none
    | (_, s₀) :: _ =>
      if ms.any (fun q => q.2 = tmp) then none
      else some ((tmp, s₀), ms.map fun p => (p.1, if p.2 = s₀ then tmp else p.2))

/-- The sequential moves of the parallel move `ms`, with temporary `tmp` and fuel `n`. -/
def seq (tmp : R) : Nat → List (R × R) → Option (List (R × R))
  | 0, ms => if ms.all (fun p => p.1 = p.2) then some [] else none
  | n + 1, ms =>
    match pick tmp (ms.filter fun p => p.1 ≠ p.2) with
    | some (mv, rest) => (mv :: ·) <$> seq tmp n rest
    | none => if ms.all (fun p => p.1 = p.2) then some [] else none

theorem run_append (f : R → V) (l₁ l₂ : List (R × R)) : run f (l₁ ++ l₂) = run (run f l₁) l₂ := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons p l ih => obtain ⟨d, s⟩ := p; exact ih _

omit [DecidableEq R] in
theorem mem_unique {ms : List (R × R)} (hnd : (ms.map (·.1)).Nodup) {r s s' : R}
    (h1 : (r, s) ∈ ms) (h2 : (r, s') ∈ ms) : s = s' := by
  induction ms with
  | nil => cases h1
  | cons p ms ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨he, rfl⟩ | h2
    · rfl
    · exact absurd ⟨_, h2, rfl⟩ hnd.1
    · subst he; exact absurd ⟨_, h1, rfl⟩ hnd.1
    · exact ih hnd.2 h1 h2

theorem par_of_mem {ms : List (R × R)} (hnd : (ms.map (·.1)).Nodup) (f : R → V) {r s : R}
    (h : (r, s) ∈ ms) : par f ms r = f s := by
  unfold par src?
  cases hs : ms.find? (·.1 = r) with
  | none =>
    simp only [List.find?_eq_none, decide_eq_true_eq] at hs
    exact absurd rfl (hs _ h)
  | some p =>
    have hm := List.mem_of_find?_eq_some hs
    have hr := List.find?_some hs
    simp only [decide_eq_true_eq] at hr
    obtain ⟨r', s'⟩ := p; simp only at hr; subst hr
    simp only [Option.map_some]
    rw [mem_unique hnd hm h]

theorem par_of_not {ms : List (R × R)} (f : R → V) {r : R} (h : ∀ s, (r, s) ∉ ms) :
    par f ms r = f r := by
  unfold par src?
  cases hs : ms.find? (·.1 = r) with
  | none => rfl
  | some p =>
    have hm := List.mem_of_find?_eq_some hs
    have hr := List.find?_some hs
    simp only [decide_eq_true_eq] at hr
    obtain ⟨r', s'⟩ := p; simp only at hr; subst hr
    exact absurd hm (h s')

omit [DecidableEq R] in
theorem nodup_filter {ms : List (R × R)} (hnd : (ms.map (·.1)).Nodup) (q : R × R → Bool) :
    ((ms.filter q).map (·.1)).Nodup :=
  hnd.sublist ((List.filter_sublist).map _)

/-- Dropping the moves of a register to itself does not change the parallel move. -/
theorem par_filter {ms : List (R × R)} (hnd : (ms.map (·.1)).Nodup) (f : R → V) (r : R) :
    par f (ms.filter fun p => p.1 ≠ p.2) r = par f ms r := by
  by_cases h : ∃ s, (r, s) ∈ ms
  · obtain ⟨s, hs⟩ := h
    rw [par_of_mem hnd f hs]
    by_cases hrs : r = s
    · subst hrs
      refine par_of_not f fun s' hs' => ?_
      simp only [List.mem_filter, decide_eq_true_eq] at hs'
      exact hs'.2 (mem_unique hnd hs'.1 hs).symm
    · exact par_of_mem (nodup_filter hnd _) f (by simp [hs, hrs])
  · simp only [not_exists] at h
    rw [par_of_not f h, par_of_not f fun s hs => h s (List.mem_filter.1 hs).1]

/-- One move of `pick` keeps the destinations distinct and not `tmp`, and the move followed by
the rest is the parallel move, except at `tmp`. -/
theorem pick_spec {tmp : R} {ms rest : List (R × R)} {mv : R × R}
    (h : pick tmp ms = some (mv, rest)) (hnd : (ms.map (·.1)).Nodup) (ht : ∀ p ∈ ms, p.1 ≠ tmp) :
    (rest.map (·.1)).Nodup ∧ (∀ p ∈ rest, p.1 ≠ tmp) ∧
      ∀ (f : R → V) r, r ≠ tmp → par (step f mv.1 mv.2) rest r = par f ms r := by
  unfold pick at h
  split at h
  · rename_i d s hf
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have hfree := List.find?_some hf
    simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq] at hfree
    refine ⟨nodup_filter hnd _, fun p hp => ht p (List.mem_filter.1 hp).1, fun f r _ => ?_⟩
    by_cases hrd : r = d
    · subst hrd
      rw [par_of_mem hnd f hm, par_of_not]
      · simp [step]
      · intro s' hs'; simp at hs'
    · by_cases hx : ∃ s', (r, s') ∈ ms
      · obtain ⟨s', hs'⟩ := hx
        rw [par_of_mem hnd f hs', par_of_mem (s := s') (nodup_filter hnd _) _ (by simp [hs', hrd])]
        simp only [step]
        rw [ite_eq_right]; intro he; subst he; exact hfree _ hs' rfl
      · simp only [not_exists] at hx
        rw [par_of_not f hx, par_of_not _ fun s' hs' => hx s' (List.mem_filter.1 hs').1]
        simp [step, hrd]
  · rename_i hf
    split at h
    · cases h
    · rename_i d₀ s₀ ms₀
      split at h
      · cases h
      · rename_i hnt
        cases h
        simp only [Bool.not_eq_true, List.any_eq_false, decide_eq_true_eq] at hnt
        have hmap : ((((d₀, s₀) :: ms₀).map fun p => (p.1, if p.2 = s₀ then tmp else p.2)).map
            (·.1)) = ((d₀, s₀) :: ms₀).map (·.1) := by simp [List.map_map, Function.comp_def]
        refine ⟨hmap ▸ hnd, fun p hp => ?_, fun f r hr => ?_⟩
        · simp only [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact ht q hq
        · by_cases hx : ∃ s', (r, s') ∈ (d₀, s₀) :: ms₀
          · obtain ⟨s', hs'⟩ := hx
            rw [par_of_mem hnd f hs', par_of_mem (hmap ▸ hnd) _ (List.mem_map_of_mem
              (f := fun p => (p.1, if p.2 = s₀ then tmp else p.2)) hs')]
            simp only [step]
            by_cases hss : s' = s₀
            · simp [hss]
            · rw [ite_eq_right hss, ite_eq_right]; intro he; exact hnt _ hs' he
          · simp only [not_exists] at hx
            rw [par_of_not f hx, par_of_not]
            · simp [step, hr]
            · intro s' hs'
              simp only [List.mem_map, Prod.mk.injEq] at hs'
              obtain ⟨q, hq, h1, -⟩ := hs'
              exact hx q.2 (h1 ▸ hq)

/-- Each move of `pick` writes `tmp` or a destination of `ms`, and so does each move left. -/
theorem pick_dst {tmp : R} {ms rest : List (R × R)} {mv : R × R}
    (h : pick tmp ms = some (mv, rest)) :
    (mv.1 = tmp ∨ ∃ q ∈ ms, q.1 = mv.1) ∧ ∀ p ∈ rest, ∃ q ∈ ms, q.1 = p.1 := by
  unfold pick at h
  split at h
  · rename_i d s hf
    cases h
    exact ⟨Or.inr ⟨_, List.mem_of_find?_eq_some hf, rfl⟩,
      fun p hp => ⟨p, (List.mem_filter.1 hp).1, rfl⟩⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        refine ⟨Or.inl rfl, fun p hp => ?_⟩
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact ⟨q, hq, rfl⟩

/-- Each move of an accepted sequence writes `tmp` or a destination of `ms`. -/
theorem seq_dst {tmp : R} : ∀ (n : Nat) {ms l : List (R × R)}, seq tmp n ms = some l →
    ∀ p ∈ l, p.1 = tmp ∨ ∃ q ∈ ms, q.1 = p.1
  | 0, ms, l, h, p, hp => by
    simp only [seq] at h
    split at h
    · cases h; cases hp
    · cases h
  | n + 1, ms, l, h, p, hp => by
    simp only [seq] at h
    split at h
    · rename_i mv rest hpk
      cases hl : seq tmp n rest with
      | none => rw [hl] at h; cases h
      | some l' =>
        rw [hl] at h; cases h
        obtain ⟨h1, h2⟩ := pick_dst hpk
        rcases List.mem_cons.1 hp with rfl | hp
        · rcases h1 with h1 | ⟨q, hq, he⟩
          · exact Or.inl h1
          · exact Or.inr ⟨q, (List.mem_filter.1 hq).1, he⟩
        · rcases seq_dst n hl p hp with h3 | ⟨q, hq, he⟩
          · exact Or.inl h3
          · obtain ⟨q', hq', he'⟩ := h2 q hq
            exact Or.inr ⟨q', (List.mem_filter.1 hq').1, he'.trans he⟩
    · split at h
      · cases h; cases hp
      · cases h

/-- The move of `pick` reads a source of `ms`, and each move left reads `tmp` or a source of `ms`. -/
theorem pick_src {tmp : R} {ms rest : List (R × R)} {mv : R × R}
    (h : pick tmp ms = some (mv, rest)) :
    (∃ q ∈ ms, q.2 = mv.2) ∧ ∀ p ∈ rest, p.2 = tmp ∨ ∃ q ∈ ms, q.2 = p.2 := by
  unfold pick at h
  split at h
  · rename_i d s hf
    cases h
    exact ⟨⟨_, List.mem_of_find?_eq_some hf, rfl⟩,
      fun p hp => Or.inr ⟨p, (List.mem_filter.1 hp).1, rfl⟩⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        refine ⟨⟨_, List.mem_cons_self, rfl⟩, fun p hp => ?_⟩
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨q, hq, rfl⟩

/-- Each move of an accepted sequence reads `tmp` or a source of `ms`. -/
theorem seq_src {tmp : R} : ∀ (n : Nat) {ms l : List (R × R)}, seq tmp n ms = some l →
    ∀ p ∈ l, p.2 = tmp ∨ ∃ q ∈ ms, q.2 = p.2
  | 0, ms, l, h, p, hp => by
    simp only [seq] at h
    split at h
    · cases h; cases hp
    · cases h
  | n + 1, ms, l, h, p, hp => by
    simp only [seq] at h
    split at h
    · rename_i mv rest hpk
      cases hl : seq tmp n rest with
      | none => rw [hl] at h; cases h
      | some l' =>
        rw [hl] at h; cases h
        obtain ⟨⟨q, hq, he⟩, h2⟩ := pick_src hpk
        rcases List.mem_cons.1 hp with rfl | hp
        · exact Or.inr ⟨q, (List.mem_filter.1 hq).1, he⟩
        · rcases seq_src n hl p hp with h3 | ⟨q, hq, he⟩
          · exact Or.inl h3
          · rcases h2 q hq with h4 | ⟨q', hq', he'⟩
            · exact Or.inl (he ▸ h4)
            · exact Or.inr ⟨q', (List.mem_filter.1 hq').1, he'.trans he⟩
    · split at h
      · cases h; cases hp
      · cases h

/-- An accepted sequence has at most as many moves as the fuel. -/
theorem seq_length {tmp : R} : ∀ (n : Nat) {ms l : List (R × R)}, seq tmp n ms = some l →
    l.length ≤ n
  | 0, ms, l, h => by
    simp only [seq] at h
    split at h
    · cases h; simp
    · cases h
  | n + 1, ms, l, h => by
    simp only [seq] at h
    split at h
    · cases hl : seq tmp n _ with
      | none => rw [hl] at h; cases h
      | some l' =>
        rw [hl] at h; cases h
        have := seq_length n hl
        simp; omega
    · split at h
      · cases h; simp
      · cases h

/-- A run depends only on the values on a set `G` that holds every source: from files that agree
on `G`, the runs agree on `G`. -/
theorem run_congr {G : R → Prop} : ∀ (l : List (R × R)) {f g : R → V}, (∀ p ∈ l, G p.2) →
    (∀ r, G r → f r = g r) → ∀ r, G r → run f l r = run g l r
  | [], _, _, _, h, r, hr => h r hr
  | (d, s) :: l, f, g, hs, h, r, hr =>
    run_congr l (fun p hp => hs p (List.mem_cons_of_mem _ hp)) (fun r hr => by
      simp only [step]; split
      · exact h s (hs _ List.mem_cons_self)
      · exact h r hr) r hr

/-- An accepted sequence leaves every register but `tmp` as the parallel move does. -/
theorem seq_run {tmp : R} : ∀ (n : Nat) {ms l : List (R × R)}, (ms.map (·.1)).Nodup →
    (∀ p ∈ ms, p.1 ≠ tmp) → seq tmp n ms = some l → ∀ (f : R → V) r, r ≠ tmp → run f l r = par f ms r
  | 0, ms, l, hnd, _, h, f, r, _ => by
    simp only [seq] at h
    split at h
    · rename_i ha
      cases h
      by_cases hx : ∃ s, (r, s) ∈ ms
      · obtain ⟨s, hs⟩ := hx
        have := List.all_eq_true.1 ha _ hs
        simp only [decide_eq_true_eq] at this
        rw [par_of_mem hnd f hs, ← this]; rfl
      · simp only [not_exists] at hx; rw [par_of_not f hx]; rfl
    · cases h
  | n + 1, ms, l, hnd, ht, h, f, r, hr => by
    simp only [seq] at h
    split at h
    · rename_i mv rest hp
      cases hl : seq tmp n rest with
      | none => rw [hl] at h; cases h
      | some l' =>
        rw [hl] at h; cases h
        obtain ⟨h1, h2, h3⟩ := pick_spec hp (nodup_filter hnd _)
          fun p hq => ht p (List.mem_filter.1 hq).1
        obtain ⟨d, s⟩ := mv
        show run (step f d s) l' r = _
        rw [seq_run n h1 h2 hl _ r hr, h3 f r hr, par_filter hnd]
    · split at h
      · rename_i ha
        cases h
        by_cases hx : ∃ s, (r, s) ∈ ms
        · obtain ⟨s, hs⟩ := hx
          have := List.all_eq_true.1 ha _ hs
          simp only [decide_eq_true_eq] at this
          rw [par_of_mem hnd f hs, ← this]; rfl
        · simp only [not_exists] at hx; rw [par_of_not f hx]; rfl
      · cases h

end Millipede.Sel.PMove
