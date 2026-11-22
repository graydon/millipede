import Millipede.Core.Effects

/-!
# The states a reactor reaches, from event contracts

`Program.Reach p Ei Es n s` says that `s`, a root and a world, is a state that the event
contracts `Ei` of `init` and `Es` of `step` allow after `n` steps. `Program.reach_of_contracts`
says that the program reaches only such states, for every oracle. It is the reactor induction
for contracts about events, proved once (doc/phases/ensures-events.md). `mp program` cites it
for `p.reach` and `p.events_reach`.
-/

namespace Millipede

/-- The states that the event contracts `Ei` of `init` and `Es` of `step` allow after `n` steps.
`Ei r evs e` relates the root `r` that `init` builds, its events and whether it exited.
`Es r h evs e r'` relates the root before a step, the history, the events the step appends,
whether it exited and the root after. After `exit` the world stays and the root is not
described. -/
inductive Program.Reach (p : Program) (Ei : p.State.carrier → List Event → Bool → Prop)
    (Es : p.State.carrier → List Event → List Event → Bool → p.State.carrier → Prop) :
    Nat → p.State.carrier × World → Prop
  | init (r : p.State.carrier) (evs : List Event) (e : Bool) :
      Ei r evs e → Program.Reach p Ei Es 0 (r, ⟨evs, e⟩)
  | step (n : Nat) (r r' : p.State.carrier) (h evs : List Event) (e : Bool) :
      Program.Reach p Ei Es n (r, ⟨h, false⟩) → Es r h evs e r' →
      Program.Reach p Ei Es (n + 1) (r', ⟨h ++ evs, e⟩)
  | halted (n : Nat) (r r' : p.State.carrier) (w : World) :
      Program.Reach p Ei Es n (r, w) → w.halted = true → Program.Reach p Ei Es (n + 1) (r', w)

/-- If `init`'s run satisfies `Ei` and every step from a live world with history `h` appends
events that satisfy `Es`, then the program reaches only states that `Program.Reach` allows. -/
theorem Program.reach_of_contracts (p : Program) (ω : Oracle)
    (Ei : p.State.carrier → List Event → Bool → Prop)
    (Es : p.State.carrier → List Event → List Event → Bool → p.State.carrier → Prop)
    (hi : Ei (p.run ω 0).1 (p.run ω 0).2.events (p.run ω 0).2.halted)
    (hs : ∀ r h, ∃ evs, (p.step.denote ω (.cons r .nil) ⟨h, false⟩).2.events = h ++ evs ∧
      Es r h evs (p.step.denote ω (.cons r .nil) ⟨h, false⟩).2.halted
        (p.step.denote ω (.cons r .nil) ⟨h, false⟩).1) :
    ∀ n, Program.Reach p Ei Es n (p.run ω n) := by
  intro n
  induction n with
  | zero => exact .init _ _ _ hi
  | succ n ih =>
    rw [show p.run ω (n + 1) = p.step.denote ω (.cons (p.run ω n).1 .nil) (p.run ω n).2 from rfl]
    generalize p.run ω n = s at ih ⊢
    obtain ⟨r, h, e⟩ := s
    cases e with
    | false =>
      obtain ⟨evs, he, hE⟩ := hs r h
      generalize p.step.denote ω (.cons r .nil) ⟨h, false⟩ = s' at he hE ⊢
      obtain ⟨r', h', e'⟩ := s'
      simp only at he hE
      subst he
      exact .step n r r' h evs e' ih hE
    | true =>
      have hw := Exp.denote_halted ω p.step (.cons r .nil) ⟨h, true⟩ rfl
      rw [show p.step.denote ω (.cons r .nil) ⟨h, true⟩ =
        ((p.step.denote ω (.cons r .nil) ⟨h, true⟩).1, ⟨h, true⟩) from Prod.ext rfl hw]
      exact .halted n r _ ⟨h, true⟩ ih rfl

/-- `Program.reach_of_contracts` for a `step` whose contract has a `requires` `R`: the relation of
a step is `R r → Es r h evs e r'`, and the step's contract is needed only from a root where `R`
holds. From another root the step still only appends to the history (`Exp.denote_syms`). -/
theorem Program.reach_of_contracts_req (p : Program) (ω : Oracle)
    (Ei : p.State.carrier → List Event → Bool → Prop) (R : p.State.carrier → Prop)
    (Es : p.State.carrier → List Event → List Event → Bool → p.State.carrier → Prop)
    (hi : Ei (p.run ω 0).1 (p.run ω 0).2.events (p.run ω 0).2.halted)
    (hs : ∀ r h, R r → ∃ evs, (p.step.denote ω (.cons r .nil) ⟨h, false⟩).2.events = h ++ evs ∧
      Es r h evs (p.step.denote ω (.cons r .nil) ⟨h, false⟩).2.halted
        (p.step.denote ω (.cons r .nil) ⟨h, false⟩).1) :
    ∀ n, Program.Reach p Ei (fun r h evs e r' => R r → Es r h evs e r') n (p.run ω n) := by
  refine Program.reach_of_contracts p ω _ _ hi fun r h => ?_
  by_cases hR : R r
  · obtain ⟨evs, he, hE⟩ := hs r h hR
    exact ⟨evs, he, fun _ => hE⟩
  · obtain ⟨evs, he, -⟩ := Exp.denote_syms ω p.step (.cons r .nil) ⟨h, false⟩
    exact ⟨evs, he, fun h' => absurd h' hR⟩

end Millipede
