import Millipede.Core.Program

/-!
# The extern symbols a term can call

`Exp.syms e` lists the symbols of the extern calls written in `e`, the bodies of its callees
included, since a Core call carries its callee's body. `Exp.denote_syms` says that a run of `e`,
under any oracle and from any world, only appends events whose symbol is in that list.

`e.NoCalls S` says that no run of `e` appends an event whose symbol is in `S`, and
`Program.NoCalls p S` says the same of every trace of a program. Both follow from `syms` by
kernel evaluation, through `Exp.noCalls_of_syms` and `Program.noCalls_of`. `mp def` and
`mp program` state them for the extern symbols of the capability classes a function or program
does not hold, which is what a capability token buys.
-/

namespace Millipede

/-- The extern symbols that `e` calls, callees included, with repeats. -/
def Exp.syms : {Γ : List Ty} → {t : Ty} → Exp Γ t → List String
  | _, _, .atom _ => []
  | _, _, .let_ e₁ e₂ => e₁.syms ++ e₂.syms
  | _, _, .ite _ e₁ e₂ => e₁.syms ++ e₂.syms
  | _, _, .prim _ _ => []
  | _, _, .call _ body _ => body.syms
  | _, _, .ok _ => []
  | _, _, .err _ => []
  | _, _, .match_ _ eE eO => eE.syms ++ eO.syms
  | _, _, .ext sig _ => [sig.sym]
  | _, _, .extMut sig _ k => sig.sym :: k.syms
  | _, _, .mk _ _ => []
  | _, _, .read _ => []
  | _, _, .assign _ _ k => k.syms
  | _, _, .case _ _ eP eQ => eP.syms ++ eQ.syms
  | _, _, .put _ _ _ k => k.syms
  | _, _, .take (dflt := _) _ _ k => k.syms
  | _, _, .borrowShr _ body k => body.syms ++ k.syms
  | _, _, .borrowMut _ body k => body.syms ++ k.syms
  | _, _, .callRef _ _ body _ k => body.syms ++ k.syms
  | _, _, .guard _ => []
  | _, _, .loop _ _ _ c body k => c.syms ++ body.syms ++ k.syms

/-- The world `w'` is `w` with events appended, each of whose symbols satisfies `P`. -/
def World.Adds (P : String → Prop) (w w' : World) : Prop :=
  ∃ new, w'.events = w.events ++ new ∧ ∀ ev ∈ new, P ev.sym

theorem World.Adds.refl (P : String → Prop) (w : World) : World.Adds P w w :=
  ⟨[], by simp, by simp⟩

theorem World.Adds.trans {P : String → Prop} {w₁ w₂ w₃ : World} (h₁ : World.Adds P w₁ w₂)
    (h₂ : World.Adds P w₂ w₃) : World.Adds P w₁ w₃ := by
  obtain ⟨n₁, e₁, p₁⟩ := h₁
  obtain ⟨n₂, e₂, p₂⟩ := h₂
  exact ⟨n₁ ++ n₂, by simp [e₂, e₁], by grind⟩

theorem World.Adds.mono {P Q : String → Prop} {w w' : World} (h : World.Adds P w w')
    (hPQ : ∀ s, P s → Q s) : World.Adds Q w w' := by
  obtain ⟨n, e, p⟩ := h
  exact ⟨n, e, fun ev hm => hPQ _ (p ev hm)⟩

/-- An extern call appends at most its own event. -/
theorem World.call_adds (ω : Oracle) (c : Call) (nr : Bool) (w : World) :
    World.Adds (· = c.sym) w (w.call ω c nr).2 := by
  unfold World.call
  split
  · exact World.Adds.refl _ _
  · split <;> exact ⟨[_], rfl, by simp [Call.event]⟩

theorem loopDenote_adds {σ : Type} {P : String → Prop} (cond : UInt64 → σ → World → Bool × World)
    (body : UInt64 → σ → World → σ × World)
    (hc : ∀ i a w, World.Adds P w (cond i a w).2)
    (hb : ∀ i a w, World.Adds P w (body i a w).2) :
    ∀ n i acc w, World.Adds P w (loopDenote cond body n i acc w).2 := by
  intro n
  induction n with
  | zero => intro i acc w; exact World.Adds.refl _ _
  | succ n ih =>
    intro i acc w
    simp only [loopDenote]
    split
    · exact hc _ _ _
    · exact (hc _ _ _).trans ((hb _ _ _).trans (ih _ _ _))

/-- A run of `e` appends only events whose symbol is in `e.syms`, for every oracle. -/
theorem Exp.denote_syms (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), World.Adds (· ∈ e.syms) w (e.denote ω env w).2 := by
  have l {P Q : String → Prop} {w w' : World} (h : World.Adds P w w') (hPQ : ∀ s, P s → Q s) :=
    h.mono hPQ
  induction e <;> intro env w
  case match_ s _ _ ihE ihO =>
    cases h : (s.denote env : Except _ _) <;>
      simp only [Exp.denote, h, Except.elim_error, Except.elim_ok, Exp.syms]
    · exact l (ihE _ _) (by simp_all)
    · exact l (ihO _ _) (by simp_all)
  case case s sp _ _ ihP ihQ =>
    cases h : sp.split (s.denote env) <;>
      simp only [Exp.denote, h, Sum.elim_inl, Sum.elim_inr, Exp.syms]
    · exact l (ihP _ _) (by simp_all)
    · exact l (ihQ _ _) (by simp_all)
  case ite c _ _ ih₁ ih₂ =>
    simp only [Exp.denote, Exp.syms]
    split
    · exact l (ih₁ _ _) (by simp_all)
    · exact l (ih₂ _ _) (by simp_all)
  case ext sig args =>
    exact l (World.call_adds _ _ _ _) (by simp [ExtSig.call, Exp.syms])
  case extMut sig args k ih =>
    simp only [Exp.denote, Exp.syms]
    refine World.Adds.trans (l (P := (· = sig.sym)) ?_ (by simp_all)) (l (ih _ _) (by simp_all))
    rw [World.ask_snd]; exact World.call_adds _ _ _ _
  case loop n cs init c body k ihc ihb ihk =>
    simp only [Exp.denote, Exp.syms]
    exact World.Adds.trans
      (l (loopDenote_adds (P := (· ∈ c.syms ++ body.syms))
        _ _ (fun _ _ _ => l (ihc _ _) (by simp_all)) (fun _ _ _ => l (ihb _ _) (by simp_all))
        _ _ _ _) (by grind))
      (l (ihk _ _) (by simp_all))
  case let_ ih₁ ih₂ =>
    exact (l (ih₁ _ _) (by simp_all [Exp.syms])).trans (l (ih₂ _ _) (by simp_all [Exp.syms]))
  case call ih => exact l (ih _ _) (by simp [Exp.syms])
  case assign ih => exact l (ih _ _) (by simp [Exp.syms])
  case put ih => exact l (ih _ _) (by simp [Exp.syms])
  case take ih => exact l (ih _ _) (by simp [Exp.syms])
  case borrowShr ih₁ ih₂ =>
    exact (l (ih₁ _ _) (by simp_all [Exp.syms])).trans (l (ih₂ _ _) (by simp_all [Exp.syms]))
  case borrowMut ih₁ ih₂ =>
    exact (l (ih₁ _ _) (by simp_all [Exp.syms])).trans (l (ih₂ _ _) (by simp_all [Exp.syms]))
  case callRef ih₁ ih₂ =>
    exact (l (ih₁ _ _) (by simp_all [Exp.syms])).trans (l (ih₂ _ _) (by simp_all [Exp.syms]))
  all_goals exact World.Adds.refl _ _

/-- No run of `e`, under any oracle, from any world and environment, appends an event whose
symbol is in `S`. -/
def Exp.NoCalls {Γ : List Ty} {t : Ty} (e : Exp Γ t) (S : List String) : Prop :=
  ∀ (ω : Oracle) (env : Env Γ) (w : World), World.Adds (· ∉ S) w (e.denote ω env w).2

/-- `e.NoCalls S` when no symbol of `e` is in `S`, which the kernel decides. -/
theorem Exp.noCalls_of_syms {Γ : List Ty} {t : Ty} (e : Exp Γ t) (S : List String)
    (h : (e.syms.all fun s => !S.contains s) = true) : e.NoCalls S := by
  intro ω env w
  refine (e.denote_syms ω env w).mono fun s hs => ?_
  have := List.all_eq_true.mp h s hs
  simpa using this

/-- No trace of `p`, under any oracle and after any number of steps, has an event whose symbol
is in `S`. -/
def Program.NoCalls (p : Program) (S : List String) : Prop :=
  ∀ (ω : Oracle) (n : Nat), ∀ ev ∈ p.events ω n, ev.sym ∉ S

/-- A program calls no symbol of `S` when neither `init` nor `step` does. -/
theorem Program.noCalls_of (p : Program) (S : List String) (hi : p.init.NoCalls S)
    (hs : p.step.NoCalls S) : p.NoCalls S := by
  intro ω n
  induction n with
  | zero =>
    obtain ⟨new, he, hn⟩ := hi ω .nil World.init
    intro ev hm
    simp only [Program.events, Program.run] at hm
    rw [he] at hm
    exact hn ev (by simpa [World.init] using hm)
  | succ n ih =>
    obtain ⟨new, he, hn⟩ := hs ω (.cons (p.run ω n).1 .nil) (p.run ω n).2
    intro ev hm
    simp only [Program.events, Program.run] at hm ih
    rw [he, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih ev hm
    · exact hn ev hm

end Millipede
