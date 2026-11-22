import Millipede.Meta.Sem
import Millipede.Core.Program
import Std.Tactic.Do
import Std.WP

/-!
# Contracts and invariants on the library side

This module proves once the facts that `mp def … ensures` and `mp program … invariant` cite, and
it does not import `Lean`.
- `World.callM_spec` and `World.askM_spec` give an extern call in a normal form to `vcgen`. They
  say that the postcondition holds of the call's answer and the next world.
- `Spec.run_of_triple` and `Spec.runM_of_triple` turn a triple of a pure or effectful normal form
  into a fact about its value, which is the generated `f.post`, and `Spec.triple_of_run` turns it
  back.
- `Program.safe_of_inv` is the reactor induction. An invariant established by `init` and kept by
  `step`, under which both are safe, gives `p.Safe` and the invariant after every step.
-/

namespace Millipede

open Std.WP

set_option experimental.vcgen true

theorem World.callM_eq (ω : Oracle) (c : Call) (nr : Bool) :
    World.callM ω c nr = (modifyGet fun w => w.call ω c nr : StateM World UInt64) := rfl

/-- An extern call, whose postcondition holds of its answer and the next world. -/
@[spec] theorem World.callM_spec (ω : Oracle) (c : Call) (nr : Bool) (Q : UInt64 → World → Prop) :
    ⦃fun w => Q (w.call ω c nr).1 (w.call ω c nr).2⦄ World.callM ω c nr ⦃Q⦄ := by
  rw [World.callM_eq]; vcgen

theorem World.askM_eq (ω : Oracle) (c : Call) (nr : Bool) :
    World.askM ω c nr = (modifyGet fun w => w.ask ω c nr : StateM World Reply) := rfl

/-- An extern call writing a buffer, whose postcondition holds of the reply and the next world. -/
@[spec] theorem World.askM_spec (ω : Oracle) (c : Call) (nr : Bool) (Q : Reply → World → Prop) :
    ⦃fun w => Q (w.ask ω c nr).1 (w.ask ω c nr).2⦄ World.askM ω c nr ⦃Q⦄ := by
  rw [World.askM_eq]; vcgen

/-- A loop of the normal form over `upto n` is `Spec.forIn_list` at `List.range n`, so its
invariants and their goals are those of a loop over `List.range n`. -/
@[spec] theorem Spec.forIn_upto.{u, v, uₚ, uₑ} {β : Type u} {m : Type u → Type v}
    {Pred : Type uₚ} {EPred : Type uₑ} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] {n : Nat} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant Nat β Pred) {epost : EPred}
    (step : ∀ pref cur suff (_h : List.range n = pref ++ cur :: suff) b,
      Triple (f cur b) (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (List.range n) [] b')
        epost) :
    Triple (forIn (upto n) init f) (inv [] (List.range n) init)
      (fun b => inv (List.range n) [] b) epost :=
  Spec.forIn_list inv step

/-- A fact about the value of a pure program, as a triple. -/
theorem Spec.triple_of_run {α : Type} {P : Prop} {x : Id α} {Q : α → Prop} (h : P → Q x.run) :
    ⦃P⦄ x ⦃Q⦄ :=
  Triple.iff.mpr h

/-- A triple of a pure program, as a fact about its value. -/
theorem Spec.run_of_triple {α : Type} {P : Prop} {x : Id α} {Q : α → Prop} (h : ⦃P⦄ x ⦃Q⦄)
    (hp : P) : Q x.run :=
  Id.of_run_eq_wp rfl Q (Triple.iff.mp h hp)

/-- A triple of an effectful program whose assertions ignore the world, as a fact about its
value from any world. -/
theorem Spec.runM_of_triple {α : Type} {P : Prop} {x : StateM World α} {Q : α → Prop}
    (h : ⦃fun _ => P⦄ x ⦃fun r _ => Q r⦄) (hp : P) (w : World) : Q (x.run w).1 :=
  StateM.of_run_eq_wp rfl (fun p => Q p.1) ((Triple.iff.mp h) w hp)

/-! ## Contracts about events

An event contract of an effectful function is a relation `E r h evs e` between its result `r`
(with the final values of its `&mut` parameters), the history `h` before the call, the events
`evs` the call appends, and whether it ends halted, `e`. Its triple holds for every
postcondition `Q`: from a live world `w`, `Q` holds of the result and the world
`⟨w.events ++ evs, e⟩` for some `evs` and `e` related by `E`. -/

/-- The precondition of an event contract `E` under the `requires` `P`, for the postcondition
`Q`. `mp def` states `f.spec` with this unfolded, so that `vcgen` sees the conjunction. -/
abbrev Spec.EventPre {α : Type} (P : Prop) (E : α → List Event → List Event → Bool → Prop)
    (Q : α → World → Prop) (w : World) : Prop :=
  P ∧ w.halted = false ∧ ∀ r evs e, E r w.events evs e → Q r ⟨w.events ++ evs, e⟩

/-- The precondition of the generated `f.spec` of an event contract. From a live world it is
`Spec.EventPre`. From a halted world a run changes nothing (`Exp.denote_halted`), so `Q` must
hold of every result and the same world. A caller's `vcgen` uses the second part for the code
after a callee that may exit. -/
abbrev Spec.EventPreH {α : Type} (P : Prop) (E : α → List Event → List Event → Bool → Prop)
    (Q : α → World → Prop) (w : World) : Prop :=
  (w.halted = false → P ∧ ∀ r evs e, E r w.events evs e → Q r ⟨w.events ++ evs, e⟩) ∧
    (w.halted = true → ∀ r, Q r w)

/-- An event contract from live worlds extends to every world, for a program that changes
nothing from a halted world. -/
theorem Spec.eventSpecH {α : Type} {P : Prop} {x : StateM World α}
    (E : α → List Event → List Event → Bool → Prop)
    (hl : ∀ Q : α → World → Prop, ⦃Spec.EventPre P E Q⦄ x ⦃Q⦄)
    (hh : ∀ w : World, w.halted = true → (x.run w).2 = w)
    (Q : α → World → Prop) : ⦃Spec.EventPreH P E Q⦄ x ⦃Q⦄ := by
  refine Triple.iff.mpr fun w ⟨hlive, hhalt⟩ => ?_
  cases hw : w.halted
  · obtain ⟨hp, hq⟩ := hlive hw
    exact Triple.iff.mp (hl Q) w ⟨hp, hw, hq⟩
  · show Q (x.run w).1 (x.run w).2
    rw [hh w hw]; exact hhalt hw _

/-- An event contract from every world holds from live worlds. -/
theorem Spec.eventSpec_live {α : Type} {P : Prop} {x : StateM World α}
    (E : α → List Event → List Event → Bool → Prop)
    (hs : ∀ Q : α → World → Prop, ⦃Spec.EventPreH P E Q⦄ x ⦃Q⦄)
    (Q : α → World → Prop) : ⦃Spec.EventPre P E Q⦄ x ⦃Q⦄ :=
  Triple.iff.mpr fun w ⟨hp, hl, hq⟩ =>
    Triple.iff.mp (hs Q) w ⟨fun _ => ⟨hp, hq⟩, fun h => by simp [hl] at h⟩

/-- An event contract as a fact about the run from a live world with the history `h`: the final
world extends `h` by some events `evs`, and `E` relates them to the result. -/
theorem Spec.runE_of_triple {α : Type} {P : Prop} {x : StateM World α}
    (E : α → List Event → List Event → Bool → Prop)
    (hs : ∀ Q : α → World → Prop, ⦃Spec.EventPre P E Q⦄ x ⦃Q⦄) (hp : P) (h : List Event) :
    ∃ evs, (x.run ⟨h, false⟩).2.events = h ++ evs ∧
      E (x.run ⟨h, false⟩).1 h evs (x.run ⟨h, false⟩).2.halted :=
  StateM.of_run_eq_wp rfl (fun (p : α × World) => ∃ evs, p.2.events = h ++ evs ∧ E p.1 h evs p.2.halted)
    ((Triple.iff.mp (hs fun r w => ∃ evs, w.events = h ++ evs ∧ E r h evs w.halted))
      ⟨h, false⟩ ⟨hp, rfl, fun _ evs _ he => ⟨evs, rfl, he⟩⟩)

/-- An event contract from a triple about the run from the live world with history `h`, for every
`h`. A proof in this form has the history before the call in scope, so a loop invariant can state
the events so far, as `w = ⟨h ++ evs, false⟩`. The tactic `mp_history` applies it. -/
theorem Spec.eventSpec_of_hist {α : Type} {P : Prop} {x : StateM World α}
    (E : α → List Event → List Event → Bool → Prop)
    (hs : ∀ h, P → ⦃fun w => w = ⟨h, false⟩⦄ x
      ⦃fun r w => ∃ evs, w.events = h ++ evs ∧ E r h evs w.halted⦄)
    (Q : α → World → Prop) : ⦃Spec.EventPre P E Q⦄ x ⦃Q⦄ := by
  refine Triple.iff.mpr fun ⟨h, e⟩ ⟨hp, hl, hq⟩ => ?_
  simp only at hl; subst hl
  obtain ⟨evs, he, hE⟩ := StateM.of_run_eq_wp rfl
    (fun p : α × World => ∃ evs, p.2.events = h ++ evs ∧ E p.1 h evs p.2.halted)
    ((Triple.iff.mp (hs h hp)) ⟨h, false⟩ rfl)
  have hQ := hq _ _ _ hE
  show Q (x.run ⟨h, false⟩).1 (x.run ⟨h, false⟩).2
  revert he hQ; generalize (x.run ⟨h, false⟩).2 = w'; rcases w' with ⟨h', e'⟩
  intro he; simp only at he; subst he; exact id

/-- A triple from the one world `w₀`, from a fact about the run from it. After `mp_history` it
turns the goal into a fact about `(x.run ⟨history, false⟩)`, for a proof by a lemma about the
run. -/
theorem Spec.triple_of_run_at {α : Type} {x : StateM World α} {w₀ : World}
    {Q : α → World → Prop} (h : Q (x.run w₀).1 (x.run w₀).2) : ⦃fun w => w = w₀⦄ x ⦃Q⦄ :=
  Triple.iff.mpr fun _ hw => hw ▸ h

/-- The length `i + 1 - i` of a slice `a[i..i+1]` of one cell. -/
theorem UInt64.ofNat_add_one_sub (k : Nat) : UInt64.ofNat k + 1 - UInt64.ofNat k = 1 := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel]

/-- A slice of one cell. -/
theorem vrange_one {α : Type} {n : Nat} (a : Vector α n) (k : Nat) (hk : k < n) :
    vrange a k 1 = [a[k]] := by
  simp [vrange, List.take_one, hk]

/-- The bytes an extern delivers into its output buffer appear in a normal form as `List.headD`
unfolded to its `match`; `simp` turns that back into the simp normal form of `List.headD`, in which
lemmas about the delivered bytes are stated. -/
@[simp] theorem headD_match {α : Type} (l : List α) (d : α) :
    List.getLastD.match_1 (fun _ _ => α) l d (fun f => f) (fun a _ _ => a) = l.head?.getD d := by
  cases l <;> rfl

/-- An extern call from a live world, as `World.call` computes it. `simp` uses these on the
worlds that a proof of an event contract builds, whose `halted` field is a literal. -/
@[simp] theorem World.call_mk_live (ω : Oracle) (c : Call) (h : List Event) :
    (World.mk h false).call ω c false =
      (c.value (ω.answer h c), ⟨h ++ [c.event (ω.answer h c)], false⟩) := rfl

@[simp] theorem World.call_mk_exit (ω : Oracle) (c : Call) (h : List Event) :
    (World.mk h false).call ω c true = (0, ⟨h ++ [c.event ⟨0, []⟩], true⟩) := rfl

@[simp] theorem World.ask_mk_live (ω : Oracle) (c : Call) (h : List Event) :
    (World.mk h false).ask ω c false = (ω.answer h c, ⟨h ++ [c.event (ω.answer h c)], false⟩) := rfl

/-- The reactor induction, proved once for every program. An invariant `I` of the root that holds
after `init` and that `step` keeps, with both safe under it, gives `p.Safe` and `I` after every
step, for every oracle. -/
theorem Program.safe_of_inv (p : Program) (I : p.State.carrier → Prop)
    (hi : ∀ ω, p.init.safe ω .nil World.init ∧ I (p.init.denote ω .nil World.init).1)
    (hs : ∀ ω r w, I r →
      p.step.safe ω (.cons r .nil) w ∧ I (p.step.denote ω (.cons r .nil) w).1) :
    p.Safe ∧ ∀ ω n, I (p.run ω n).1 := by
  have inv : ∀ ω n, I (p.run ω n).1 := fun ω n => by
    induction n with
    | zero => exact (hi ω).2
    | succ n ih => exact (hs ω _ _ ih).2
  exact ⟨fun ω => ⟨(hi ω).1, fun n => (hs ω _ _ (inv ω n)).1⟩, inv⟩

end Millipede
