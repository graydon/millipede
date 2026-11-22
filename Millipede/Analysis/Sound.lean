import Millipede.Analysis.Loop

/-!
# Soundness of the analyser

The main theorem is `Exp.an_sound`. It says that, from an abstract environment that holds of the
environment, the analysis of `e` describes its value and the components of a loop body's
hand-back tuple, and that `e.safe` holds when the analysis certifies the obligations. It assumes
`e.LoopsOk`, which says that the hand-back constructors of loop bodies are tuple constructors.
-/

namespace Millipede.Analysis

open Millipede

variable {Γ : List Ty}

/-! ## The environment of a continuation after a write and a binder -/

/-- The environment after a write to the variables `ks` and a new binder, which top describes. -/
theorem AEnv.sat_killPush {s : Ty} {ks : List Nat} {A : AEnv Γ} {env env' : Env Γ} (hA : A.sat env)
    (he : AgreeOff ks env env') (x : s.carrier) : ((A.kill ks).push {}).sat (.cons x env') :=
  AEnv.sat_push (AEnv.sat_kill hA he) (AVal.sat_top _ _)

/-- The continuation's value, described again as before the write. -/
theorem AVal.sat_forgetUnshift {s t : Ty} {ks : List Nat} {a : AVal (s :: Γ)} {env env' : Env Γ}
    (he : AgreeOff ks env env') {x : s.carrier} {v : t.carrier} (h : a.sat (.cons x env') v) :
    (a.unshift.forget ks).sat env v :=
  AVal.sat_forget (AgreeOff.symm he) (AVal.sat_unshift h)


/-- The candidates describe the state of a loop at iteration `j`. -/
def LoopInv {s : Ty} {ts : List Ty} (ca : Cand) (cc : List Cand) (j : Nat)
    (st : s.carrier × (Ty.tup ts).carrier) : Prop :=
  (ca.atJ j : AVal []).sat .nil st.1 ∧ CandsSat j cc ts st.2

/-- The chosen attempt is one of the attempts. -/
theorem loopPick_eq {s : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts) (A : AEnv Γ) (a0 : AVal Γ)
    (fc fb : AEnv (.u64 :: s :: Γ) → Res (.u64 :: s :: Γ)) :
    ∃ ca cc, loopPick n cs A a0 fc fb = loopAttempt n cs A a0 fc fb ca cc := by
  dsimp only [loopPick]
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- The invariant of a valid attempt. The candidates describe the initial state, and an iteration
that runs, with its counter below `n`, from a described state satisfies its environments, the
body's under the condition's facts, and hands back a state described at the next iteration. -/
theorem loopAttempt_inv (ω : Oracle) {s : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts)
    (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts)))
    (hc : ∀ B env' w', AEnv.sat B env' → (c.an B).v.sat env' (c.denote ω env' w').1)
    (hb : ∀ B env' w', AEnv.sat B env' →
      TupSat env' (body.an B).cs (s :: ts) (body.denote ω env' w').1)
    {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) (hn : n < 2 ^ 64) (hd : cs.distinct = true)
    {ca : Cand} {cc : List Cand}
    (hv : (loopAttempt n cs A (A.atomV init) (fun B => c.an B) (fun B => body.an B) ca
      cc).valid = true) :
    LoopInv ca cc 0 (init.denote env, cs.get env) ∧
    ∀ j st w', j < n → LoopInv ca cc j st →
      (bodyA n A cs ca cc).sat (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2))) ∧
      ((c.denote ω (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2))) w').1 = true →
        ((bodyA n A cs ca cc).assumeAll (c.an (bodyA n A cs ca cc)).v.t).sat
          (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2))) ∧
        LoopInv ca cc (j + 1) (body.denote ω (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2)))
          (c.denote ω (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2))) w').2).1) := by
  simp only [loopAttempt, Bool.and_eq_true] at hv
  obtain ⟨⟨hi, hci⟩, hok⟩ := hv
  refine ⟨⟨Cand.init_sat hi (A.atomV_sat hA init), candsInit_sat hA cs cc hci⟩,
    fun j st w' hj hP => ?_⟩
  have hB := sat_bodyA hA cs hd hj hn hP.1 hP.2
  refine ⟨hB, fun hct => ?_⟩
  have hB' := AEnv.sat_assumeAll hB ((AVal.sat_bool (hc _ _ w' hB)).1 hct)
  exact ⟨hB', candsOk_step (by omega) hok (hb _ _ _ hB')⟩

/-- The analysis of a loop is sound, given that of its condition, body and continuation. -/
theorem loopAn_sound (ω : Oracle) {s u : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts)
    (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u)
    (hc : ∀ B env' w', AEnv.sat B env' → (c.an B).v.sat env' (c.denote ω env' w').1 ∧
      ((c.an B).ok = true → c.safe ω env' w'))
    (hb : ∀ B env' w', AEnv.sat B env' →
      TupSat env' (body.an B).cs (s :: ts) (body.denote ω env' w').1 ∧
      ((body.an B).ok = true → body.safe ω env' w'))
    (hk : ∀ B env' w', AEnv.sat B env' → (k.an B).v.sat env' (k.denote ω env' w').1 ∧
      ((k.an B).ok = true → k.safe ω env' w'))
    (A : AEnv Γ) (env : Env Γ) (w : World) (hA : A.sat env) :
    (loopAn n cs (A.atomV init) (fun B => c.an B) (fun B => body.an B) (fun B => k.an B) A).v.sat
        env ((Exp.loop n cs init c body k).denote ω env w).1 ∧
      ((loopAn n cs (A.atomV init) (fun B => c.an B) (fun B => body.an B) (fun B => k.an B)
        A).ok = true → (Exp.loop n cs init c body k).safe ω env w) := by
  -- The loop's semantics.
  let cond := fun (i : UInt64) (st : s.carrier × (Ty.tup ts).carrier) (w : World) =>
    c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w
  let bodyF := fun (i : UInt64) (st : s.carrier × (Ty.tup ts).carrier) (w : World) =>
    body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w
  let r := loopDenote cond bodyF n 0 (init.denote env, cs.get env) w
  have hden : (Exp.loop n cs init c body k).denote ω env w =
      k.denote ω (.cons r.1.1 (cs.set env r.1.2)) r.2 := rfl
  have hsafe : (Exp.loop n cs init c body k).safe ω env w ↔
      loopSafe (fun i st w => c.safe ω (.cons i (.cons st.1 (cs.set env st.2))) w)
        (fun i st w => body.safe ω (.cons i (.cons st.1 (cs.set env st.2))) w) cond bodyF n 0
        (init.denote env, cs.get env) w ∧ k.safe ω (.cons r.1.1 (cs.set env r.1.2)) r.2 := Iff.rfl
  rw [hden, hsafe]
  have hagr : AgreeOff cs.idxs env (cs.set env r.1.2) := Carry.set_agree cs env r.1.2
  -- The continuation, with no information on the state.
  have htop := AEnv.sat_killPush hA hagr r.1.1
  have hdflt := AVal.sat_forgetUnshift hagr (hk _ _ r.2 htop).1
  by_cases hnd : (decide (n < 2 ^ 64) && cs.distinct) = true
  · simp only [loopAn, hnd, ↓reduceIte]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnd
    obtain ⟨hn, hd⟩ := hnd
    obtain ⟨ca, cc, hpick⟩ := loopPick_eq n cs A (A.atomV init) (fun B => c.an B)
      (fun B => body.an B)
    simp only [hpick]
    by_cases hv : (loopAttempt n cs A (A.atomV init) (fun B => c.an B) (fun B => body.an B) ca
      cc).valid = true
    · simp only [hv, ↓reduceIte, Bool.true_and]
      obtain ⟨hP0, hstep⟩ := loopAttempt_inv ω n cs init c body (fun B e w hB => (hc B e w hB).1)
        (fun B e w hB => (hb B e w hB).1) hA hn hd hv
      obtain ⟨j, hj, hPj⟩ := loopDenote_invJ (LoopInv ca cc) cond bodyF n 0 _ w hP0
        (fun j a w' _ hj hP hct => ((hstep j a w' (by omega) hP).2 hct).2)
      have hK := sat_stateA hA cs hd (j := n) (Cand.atJ_mono (by omega) hPj.1)
        (CandsSat.mono (by omega) hPj.2)
      refine ⟨AVal.sat_forgetUnshift hagr (hk _ _ _ hK).1, fun hok' => ?_⟩
      simp only [loopAttempt, Bool.and_eq_true] at hok'
      obtain ⟨⟨hokc, hokb⟩, hokk⟩ := hok'
      refine ⟨loopSafe_invJ (LoopInv ca cc) _ _ cond bodyF n 0 _ w hP0 fun j a w' _ hj hP => ?_,
        (hk _ _ _ hK).2 hokk⟩
      have hs := hstep j a w' (by omega) hP
      exact ⟨(hc _ _ w' hs.1).2 hokc, fun hct => ⟨(hb _ _ _ (hs.2 hct).1).2 hokb, (hs.2 hct).2⟩⟩
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact ⟨hdflt, fun h => by simp at h⟩
  · simp only [loopAn, hnd, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hdflt, fun h => by simp at h⟩

end Millipede.Analysis

namespace Millipede.Analysis

open Millipede

/-! ## The relaxed term -/

theorem _root_.Millipede.Prim.denote_wrap {ps : List Ty} {r : Ty} (p : Prim ps r)
    (env : Env ps) : p.wrap.denote env = p.denote env := by
  cases p <;> try rfl
  all_goals rcases env with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> rfl

/-- The relaxed term has the same denotation. -/
theorem _root_.Millipede.Exp.relax_denote (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (A : AEnv Γ) (env : Env Γ) (w : World), (e.relax A).1.denote ω env w = e.denote ω env w := by
  induction e <;> intro A env w
  case ite c e₁ e₂ ih₁ ih₂ =>
    rcases c with m | b
    · simp only [Exp.relax, Exp.anR, Exp.denote] at ih₁ ih₂ ⊢; simp only [ih₁, ih₂]
    · cases b <;> rfl
  case prim p args =>
    simp only [Exp.relax, Exp.anR]
    split
    · split <;> simp [Exp.denote, Prim.denote_wrap]
    · rfl
  case loop n cs init c body k ihc ihb ihk =>
    simp only [Exp.relax, Exp.anR] at ihc ihb ihk ⊢
    split <;> simp only [Exp.denote, ihc, ihb, ihk]
  all_goals simp_all [Exp.relax, Exp.anR, Exp.denote, keep]

/-- The obligations of a loop transfer iteration by iteration along an invariant. -/
theorem loopSafe_mono {σ : Type} (P : Nat → σ → Prop) (cS bS cS' bS' : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    ∀ (n i : Nat) (acc : σ) (w : World), P i acc →
      (∀ j a w, i ≤ j → j < i + n → P j a → (cS' (UInt64.ofNat j) a w → cS (UInt64.ofNat j) a w) ∧
        ((cond (UInt64.ofNat j) a w).1 = true →
          (bS' (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2 →
            bS (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2) ∧
          P (j + 1) (body (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2).1)) →
      loopSafe cS' bS' cond body n i acc w → loopSafe cS bS cond body n i acc w := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; trivial
  | succ n ih =>
    intro i acc w hP h hs
    have hi := h i acc w (Nat.le_refl _) (by omega) hP
    exact ⟨hi.1 hs.1, fun hc => ⟨(hi.2 hc).1 (hs.2 hc).1,
      ih _ _ _ (hi.2 hc).2 (fun j a w h1 h2 => h j a w (by omega) (by omega)) (hs.2 hc).2⟩⟩

/-- The relaxed loop's obligations imply the loop's, given that the relaxed condition's, body's
and continuation's do. -/
theorem loopRelax_safe (ω : Oracle) {s u : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts)
    (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u)
    (hc : ∀ B env' w', AEnv.sat B env' → (c.an B).v.sat env' (c.denote ω env' w').1 ∧
      ((c.relax B).1.safe ω env' w' → c.safe ω env' w'))
    (hb : ∀ B env' w', AEnv.sat B env' →
      TupSat env' (body.an B).cs (s :: ts) (body.denote ω env' w').1 ∧
      ((body.relax B).1.safe ω env' w' → body.safe ω env' w'))
    (hk : ∀ B env' w', AEnv.sat B env' → (k.relax B).1.safe ω env' w' → k.safe ω env' w')
    (A : AEnv Γ) (env : Env Γ) (w : World) (hA : A.sat env)
    (h : ((Exp.loop n cs init c body k).relax A).1.safe ω env w) :
    (Exp.loop n cs init c body k).safe ω env w := by
  let cond := fun (i : UInt64) (st : _ × (Ty.tup _).carrier) (w : World) =>
    c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w
  let bodyF := fun (i : UInt64) (st : _ × (Ty.tup _).carrier) (w : World) =>
    body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w
  let r := loopDenote cond bodyF n 0 (init.denote env, cs.get env) w
  simp only [Exp.relax, Exp.anR] at h
  split at h
  · next hnd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnd
    obtain ⟨⟨hn, hd⟩, hv⟩ := hnd
    obtain ⟨ca, cc, hpick⟩ := loopPick_eq n cs A (A.atomV init) (fun B => c.an B)
      (fun B => body.an B)
    simp only [hpick] at h hv
    simp only [Exp.safe, Exp.relax_denote] at h
    obtain ⟨hP0, hstep⟩ := loopAttempt_inv ω n cs init c body
      (fun B e w hB => (hc B e w hB).1) (fun B e w hB => (hb B e w hB).1) hA hn hd hv
    obtain ⟨j, hj, hPj⟩ := loopDenote_invJ (LoopInv ca cc) cond bodyF n 0 _ w hP0
      (fun j a w' _ hj hP hct => ((hstep j a w' (by omega) hP).2 hct).2)
    have hK := sat_stateA hA cs hd (j := n) (Cand.atJ_mono (by omega) hPj.1)
      (CandsSat.mono (by omega) hPj.2)
    refine ⟨loopSafe_mono (LoopInv ca cc) _ _ _ _ cond bodyF n 0 _ w hP0
      (fun j a w' _ hj hP => ?_) h.1, hk _ _ _ hK h.2⟩
    have hs := hstep j a w' (by omega) hP
    exact ⟨(hc _ _ _ hs.1).2, fun hct => ⟨(hb _ _ _ (hs.2 hct).1).2, (hs.2 hct).2⟩⟩
  · simp only [Exp.safe] at h
    exact ⟨h.1, hk _ _ _ (AEnv.sat_killPush hA (Carry.set_agree cs env r.1.2) _) h.2⟩

/-! ## Soundness -/

/-- What the analysis of `e` from `A` guarantees in an environment that `A` describes. The value
is described, a loop body's hand-back components are described, the certified obligations hold,
and the relaxed term's obligations imply those of `e`. -/
def SoundAt (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (A : AEnv Γ) (env : Env Γ)
    (w : World) : Prop :=
  (e.an A).v.sat env (e.denote ω env w).1 ∧
  (∀ {s : Ty} {ts : List Ty} (ht : t = .pair s (.tup ts)), e.TailsOk ht →
    TupSat env (e.an A).cs (s :: ts)
      (cast (congrArg Ty.carrier ht) (e.denote ω env w).1 : (Ty.pair s (Ty.tup ts)).carrier)) ∧
  ((e.an A).ok = true → e.safe ω env w) ∧
  ((e.relax A).1.safe ω env w → e.safe ω env w)

/-- A term that is not relaxed and whose analysis returns top, no components and `ok = false`, or
`true` with no obligation, is trivially sound. -/
theorem SoundAt.top {ω : Oracle} {Γ : List Ty} {t : Ty} {e : Exp Γ t} {A : AEnv Γ} {env : Env Γ}
    {w : World} (hv : (e.an A).v = {}) (hc : (e.an A).cs = []) (hr : (e.relax A).1 = e)
    (hs : (e.an A).ok = true → e.safe ω env w) : SoundAt ω e A env w :=
  ⟨by rw [hv]; exact AVal.sat_top _ _, fun _ _ => by rw [hc]; trivial, hs, by rw [hr]; exact id⟩

/-- Two arms whose results are joined. -/
theorem Res.join_v {Γ : List Ty} {r₁ r₂ : Res Γ} {env : Env Γ} {t : Ty} {v : t.carrier}
    (h : r₁.v.sat env v ∨ r₂.v.sat env v) : (r₁.join r₂).v.sat env v :=
  h.elim AVal.sat_join_l AVal.sat_join_r

/-- The analyser and the relaxation are sound. -/
theorem Exp.an_sound (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (A : AEnv Γ) (env : Env Γ) (w : World), e.LoopsOk → A.sat env → SoundAt ω e A env w := by
  induction e with
  | atom a =>
    intro A env w _ hA
    exact ⟨A.atomV_sat hA a, fun _ _ => trivial, fun _ => trivial, fun _ => trivial⟩
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro A env w hL hA
    have h₁ := ih₁ A env w hL.1 hA
    have h₂ := ih₂ _ _ (e₁.denote ω env w).2 hL.2 (AEnv.sat_push hA (AVal.sat_shift.mpr h₁.1))
    refine ⟨AVal.sat_unshift h₂.1, fun ht hT => TupSat.unshift (h₂.2.1 ht hT), fun hok => ?_,
      fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨h₁.2.2.1 hok.1, h₂.2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      rw [← Exp.relax, Exp.relax_denote] at hr
      exact ⟨h₁.2.2.2 hr.1, h₂.2.2.2 hr.2⟩
  | ite c e₁ e₂ ih₁ ih₂ =>
    intro A env w hL hA
    rcases c with m | b
    · have hb := AVal.sat_bool (hA.1 m)
      have h₁ := fun hc => ih₁ _ env w hL.1 (AEnv.sat_assumeAll hA (hb.1 hc))
      have h₂ := fun hc => ih₂ _ env w hL.2 (AEnv.sat_assumeAll hA (hb.2 hc))
      cases hc : (env.get m : Bool)
      · refine ⟨?_, fun ht hT => ?_, fun hok => ⟨fun h' => ?_, fun _ => (h₂ hc).2.2.1 ?_⟩,
          fun hr => ⟨fun h' => ?_, fun _ => (h₂ hc).2.2.2 ?_⟩⟩
        · simp only [Exp.an, Exp.anR, Exp.denote, Atom.denote, hc]
          exact Res.join_v (.inr (h₂ hc).1)
        · simp only [Exp.an, Exp.anR, Exp.denote, Atom.denote, hc, Res.join]
          exact TupSat.join_r ((h₂ hc).2.1 ht hT.2)
        all_goals simp_all [Atom.denote, Exp.an, Exp.relax, Exp.anR, Res.join, Exp.safe]
      · refine ⟨?_, fun ht hT => ?_, fun hok => ⟨fun _ => (h₁ hc).2.2.1 ?_, fun h' => ?_⟩,
          fun hr => ⟨fun _ => (h₁ hc).2.2.2 ?_, fun h' => ?_⟩⟩
        · simp only [Exp.an, Exp.anR, Exp.denote, Atom.denote, hc]
          exact Res.join_v (.inl (h₁ hc).1)
        · simp only [Exp.an, Exp.anR, Exp.denote, Atom.denote, hc, Res.join]
          exact TupSat.join_l ((h₁ hc).2.1 ht hT.1)
        all_goals simp_all [Atom.denote, Exp.an, Exp.relax, Exp.anR, Res.join, Exp.safe]
    · cases b
      · have h := ih₂ A env w hL.2 hA
        exact ⟨h.1, fun ht hT => h.2.1 ht hT.2,
          fun hok => ⟨fun h' => by simp [Atom.denote] at h', fun _ => h.2.2.1 hok⟩, id⟩
      · have h := ih₁ A env w hL.1 hA
        exact ⟨h.1, fun ht hT => h.2.1 ht hT.1,
          fun hok => ⟨fun _ => h.2.2.1 hok, fun h' => by simp [Atom.denote] at h'⟩, id⟩
  | prim p args =>
    intro A env w _ hA
    have h := anPrim_sound hA p args
    refine ⟨h.1, fun _ _ => trivial, h.2, fun hr => ?_⟩
    simp only [Exp.relax, Exp.anR] at hr
    split at hr
    · split at hr
      · next hc => exact h.2 hc
      · exact hr
    · exact hr
  | call _ body args ih =>
    intro A env w hL hA
    have h := ih _ (args.denote env) w hL (argsAVals_sat hA args)
    exact ⟨AVal.sat_plain h.1, fun _ _ => trivial, h.2.2.1, id⟩
  | ok a => intro A env w _ _; exact SoundAt.top rfl rfl rfl fun _ => trivial
  | err a => intro A env w _ _; exact SoundAt.top rfl rfl rfl fun _ => trivial
  | match_ s eE eO ihE ihO =>
    intro A env w hL hA
    have hE := fun e => ihE (A.push {}) (.cons e env) w hL.1 (AEnv.sat_push hA (AVal.sat_top _ _))
    have hO := fun a => ihO (A.push {}) (.cons a env) w hL.2 (AEnv.sat_push hA (AVal.sat_top _ _))
    refine ⟨?_, fun _ _ => trivial, fun hok => ?_, fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Exp.denote]
      cases hs : (s.denote env : Except _ _) with
      | error e => exact Res.join_v (.inl (AVal.sat_unshift (hE e).1))
      | ok a => exact Res.join_v (.inr (AVal.sat_unshift (hO a).1))
    · simp only [Exp.an, Exp.anR, Res.join, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨fun e _ => (hE e).2.2.1 hok.1, fun a _ => (hO a).2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      exact ⟨fun e he => (hE e).2.2.2 (hr.1 e he), fun a ha => (hO a).2.2.2 (hr.2 a ha)⟩
  | ext sig args =>
    intro A env w _ hA
    exact SoundAt.top rfl rfl rfl fun hok => EArgs.okA_sound hA args hok
  | extMut sig args k ih =>
    intro A env w hL hA
    have hag : AgreeOff (EArgs.outRoots args) env (args.fill env env
        (fitOut (sig.call args env).outCaps (w.ask ω (sig.call args env) sig.noreturn).1.bytesOut)) :=
      EArgs.fill_agree args env env _
    have h := ih _ _ (w.ask ω (sig.call args env) sig.noreturn).2 hL
      (AEnv.sat_killPush hA hag (w.ask ω (sig.call args env) sig.noreturn).1.result)
    refine ⟨AVal.sat_forgetUnshift hag h.1, fun _ _ => trivial, fun hok => ?_, fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨EArgs.okA_sound hA args hok.1, h.2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      exact ⟨hr.1, h.2.2.2 hr.2⟩
  | mk c args =>
    intro A env w _ hA
    refine ⟨AVal.sat_top _ _, fun {s ts} ht hT => ?_, fun _ => trivial, id⟩
    by_cases hk : c.kind = .tuple
    · obtain ⟨hps, hb⟩ := hT hk
      have hcs : ((Exp.mk c args).an A).cs = Exp.anR.argsAVals' A args := by
        simp [Exp.an, Exp.anR, hk]
      rw [hcs]
      have e : (cast (congrArg Ty.carrier ht) ((Exp.mk c args).denote ω env w).1 :
          (Ty.pair s (Ty.tup ts)).carrier) = Flat.tupBuild (s :: ts) (hps ▸ args.denote env) := hb _
      rw [e]
      subst hps; exact TupSat.args hA args
    · have hcs : ((Exp.mk c args).an A).cs = [] := by simp [Exp.an, Exp.anR, hk]
      rw [hcs]; trivial
  | read p =>
    intro A env w _ hA
    exact ⟨Place.readV_sat hA p, fun _ _ => trivial, fun hok => Place.okA_sound hA p hok, id⟩
  | assign p a k ih =>
    intro A env w hL hA
    have hag : AgreeOff [p.root] (p.set env (a.denote env)) env :=
      AgreeOff.symm (agree_set p env _)
    have h := ih _ _ w hL (AEnv.sat_write hA p (A.atomV_sat hA a))
    refine ⟨AVal.sat_forget hag h.1, fun ht hT => TupSat.forget hag (h.2.1 ht hT), fun hok => ?_,
      fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Bool.and_eq_true] at hok
      exact ⟨Place.okA_sound hA p hok.1, h.2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      exact ⟨hr.1, h.2.2.2 hr.2⟩
  | case s sp eP eQ ihP ihQ =>
    intro A env w hL hA
    have hP := fun x => ihP (A.push {}) (.cons x env) w hL.1 (AEnv.sat_push hA (AVal.sat_top _ _))
    have hQ := fun y => ihQ (A.push {}) (.cons y env) w hL.2 (AEnv.sat_push hA (AVal.sat_top _ _))
    refine ⟨?_, fun _ _ => trivial, fun hok => ?_, fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Exp.denote]
      cases hs : sp.split (s.denote env) with
      | inl x => exact Res.join_v (.inl (AVal.sat_unshift (hP x).1))
      | inr y => exact Res.join_v (.inr (AVal.sat_unshift (hQ y).1))
    · simp only [Exp.an, Exp.anR, Res.join, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨fun x _ => (hP x).2.2.1 hok.1, fun y _ => (hQ y).2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      exact ⟨fun x hx => (hP x).2.2.2 (hr.1 x hx), fun y hy => (hQ y).2.2.2 (hr.2 y hy)⟩
  | put p i a k ih =>
    intro A env w hL hA
    have hag : AgreeOff [p.root] env (p.set env (Slots.setCell (p.get env) (i.denote env).toNat
        (some (a.denote env)))) := agree_set p env _
    have h := ih _ _ w hL (AEnv.sat_kill hA hag)
    refine ⟨AVal.sat_forget (AgreeOff.symm hag) h.1, fun _ _ => trivial,
      fun h => by simp [Exp.an, Exp.anR] at h, fun hr => ?_⟩
    simp only [Exp.relax, Exp.anR, Exp.safe] at hr
    exact ⟨hr.1, h.2.2.2 hr.2⟩
  | take p i k ih =>
    intro A env w hL hA
    have hag : AgreeOff [p.root] env (p.set env (Slots.setCell (p.get env) (i.denote env).toNat
        none)) := agree_set p env _
    have h := ih _ _ w hL (AEnv.sat_killPush hA hag
      (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default))
    refine ⟨AVal.sat_forgetUnshift hag h.1, fun _ _ => trivial,
      fun h => by simp [Exp.an, Exp.anR] at h, fun hr => ?_⟩
    simp only [Exp.relax, Exp.anR, Exp.safe] at hr
    exact ⟨hr.1, h.2.2.2 hr.2⟩
  | borrowShr p body k ihb ihk =>
    intro A env w hL hA
    have hb := ihb _ _ w hL.1 (AEnv.sat_push hA (AVal.sat_shift.mpr (Place.readV_sat hA p)))
    have hk := ihk _ _ (body.denote ω (.cons (p.get env) env) w).2 hL.2
      (AEnv.sat_push hA (AVal.sat_shift.mpr (AVal.sat_unshift hb.1)))
    refine ⟨AVal.sat_unshift hk.1, fun _ _ => trivial, fun hok => ?_, fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨Place.okA_sound hA p hok.1.1, hb.2.2.1 hok.1.2, hk.2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      rw [← Exp.relax, Exp.relax_denote] at hr
      exact ⟨hr.1, hb.2.2.2 hr.2.1, hk.2.2.2 hr.2.2⟩
  | borrowMut p body k ihb ihk =>
    intro A env w hL hA
    have hb := ihb _ _ w hL.1 (AEnv.sat_push hA (AVal.sat_shift.mpr (Place.readV_sat hA p)))
    have hag : AgreeOff [p.root] env (p.set env (body.denote ω (.cons (p.get env) env) w).1.2) :=
      agree_set p env _
    have hk := ihk _ _ (body.denote ω (.cons (p.get env) env) w).2 hL.2
      (AEnv.sat_killPush hA hag (body.denote ω (.cons (p.get env) env) w).1.1)
    refine ⟨AVal.sat_forgetUnshift hag hk.1, fun _ _ => trivial, fun hok => ?_, fun hr => ?_⟩
    · simp only [Exp.an, Exp.anR, Res.unshift, Bool.and_eq_true] at hok
      exact ⟨Place.okA_sound hA p hok.1.1, hb.2.2.1 hok.1.2, hk.2.2.1 hok.2⟩
    · simp only [Exp.relax, Exp.anR, Exp.safe] at hr
      rw [← Exp.relax, Exp.relax_denote] at hr
      exact ⟨hr.1, hb.2.2.2 hr.2.1, hk.2.2.2 hr.2.2⟩
  | callRef _ _ body args k _ ihk =>
    intro A env w hL hA
    have hag : AgreeOff (RArgs.mutRoots args) env
        (args.writeBack env (body.denote ω (args.denote env) w).1.2) :=
      RArgs.writeBack_agree args env _
    have h := ihk _ _ (body.denote ω (args.denote env) w).2 hL
      (AEnv.sat_killPush hA hag (body.denote ω (args.denote env) w).1.1)
    refine ⟨AVal.sat_forgetUnshift hag h.1, fun _ _ => trivial,
      fun h => by simp [Exp.an, Exp.anR] at h, fun hr => ?_⟩
    simp only [Exp.relax, Exp.anR, Exp.safe] at hr
    exact ⟨hr.1, hr.2.1, hr.2.2.1, h.2.2.2 hr.2.2.2⟩
  | guard => intro A env w _ _; exact SoundAt.top rfl rfl rfl fun _ => trivial
  | loop n cs init c body k ihc ihb ihk =>
    intro A env w hL hA
    have h := loopAn_sound ω n cs init c body k
      (fun B env' w' hB => ⟨(ihc B env' w' hL.1 hB).1, (ihc B env' w' hL.1 hB).2.2.1⟩)
      (fun B env' w' hB => ⟨(ihb B env' w' hL.2.1 hB).2.1 rfl hL.2.2.1,
        (ihb B env' w' hL.2.1 hB).2.2.1⟩)
      (fun B env' w' hB => ⟨(ihk B env' w' hL.2.2.2 hB).1, (ihk B env' w' hL.2.2.2 hB).2.2.1⟩)
      A env w hA
    have hcs : ((Exp.loop n cs init c body k).an A).cs = [] := by
      simp only [Exp.an, Exp.anR]; unfold loopAn; split <;> rfl
    refine ⟨h.1, fun _ _ => by rw [hcs]; trivial, h.2, loopRelax_safe ω n cs init c body k
      (fun B env' w' hB => ⟨(ihc B env' w' hL.1 hB).1, (ihc B env' w' hL.1 hB).2.2.2⟩)
      (fun B env' w' hB => ⟨(ihb B env' w' hL.2.1 hB).2.1 rfl hL.2.2.1,
        (ihb B env' w' hL.2.1 hB).2.2.2⟩)
      (fun B env' w' hB => (ihk B env' w' hL.2.2.2 hB).2.2.2) A env w hA⟩

end Millipede.Analysis

namespace Millipede.Analysis

open Millipede

/-! ## The decision procedure -/

/-- Input descriptions, one word interval per variable by index, with missing ones top. This is
the entry point for preconditions, whose bounds on parameters become these intervals. -/
def AEnv.ofItvs {Γ : List Ty} (is : List Itv) : AEnv Γ := ⟨is.map AVal.ofW, []⟩

/-- The intervals hold of an environment's word variables. -/
def ItvsHold : {Γ : List Ty} → List Itv → Env Γ → Prop
  | _, i :: is, .cons (t := t) v env =>
    (∀ h : t = .u64, i.mem (cast (congrArg Ty.carrier h) v : UInt64).toNat) ∧ ItvsHold is env
  | _, _, _ => True

theorem ofItvs_get {Γ : List Ty} : ∀ {is : List Itv} {env : Env Γ}, ItvsHold is env →
    ∀ {t : Ty} (m : Mem t Γ) {Δ : List Ty} (e : Env Δ),
      ((is[m.idx]?.map (AVal.ofW · [])).getD {} : AVal Δ).sat e (env.get m)
  | [], _, _, _, _, _, e => by simpa using AVal.sat_top e _
  | _ :: _, .nil, _, _, m, _, _ => by cases m
  | i :: is, .cons v env, hh, _, m, _, e => by
    obtain ⟨h, hs⟩ := hh
    cases m with
    | here =>
      refine ⟨fun h' => ⟨by simpa [Mem.idx, AVal.ofW] using h h', by simp [Mem.idx, AVal.ofW]⟩,
        fun _ => by simpa [Mem.idx, AVal.ofW] using Itv.mem_top8 (UInt8.toNat_lt _),
        fun _ => by simp [Mem.idx, AVal.ofW]⟩
    | there m => simpa [Mem.idx] using ofItvs_get hs m e

theorem AEnv.sat_ofItvs {Γ : List Ty} {is : List Itv} {env : Env Γ} (h : ItvsHold is env) :
    (AEnv.ofItvs is : AEnv Γ).sat env :=
  ⟨fun m => by simpa [AEnv.get, AEnv.ofItvs] using ofItvs_get h m env, by simp [AEnv.ofItvs]⟩

/-- The analyser's decision procedure, which says that every obligation of `e` is certified from
the input intervals `is`. -/
def _root_.Millipede.Exp.safeBy {Γ : List Ty} {t : Ty} (is : List Itv) (e : Exp Γ t) : Bool :=
  (e.an (AEnv.ofItvs is)).ok

/-- If the analyser certifies `e` from input intervals that hold, the obligations of `e` hold. The
hypothesis `e.LoopsOk` says that the hand-back constructors of its loop bodies are tuple
constructors, which `rfl` proves for the terms of `mp def`. -/
theorem _root_.Millipede.Exp.safe_of_safeBy {Γ : List Ty} {t : Ty} {is : List Itv} {e : Exp Γ t}
    (hL : e.LoopsOk) (h : e.safeBy is = true) (ω : Oracle) (env : Env Γ) (w : World)
    (hI : ItvsHold is env) : e.safe ω env w :=
  (Exp.an_sound ω e _ env w hL (AEnv.sat_ofItvs hI)).2.2.1 h

/-- Partial certification. From input intervals that hold, the obligations of the relaxed term, in
which the overflow obligations the analyser certifies are dropped, imply those of the term. -/
theorem _root_.Millipede.Exp.safe_of_relax {Γ : List Ty} {t : Ty} {is : List Itv} {e e' : Exp Γ t}
    (hL : e.LoopsOk) (he : (e.relax (AEnv.ofItvs is)).1 = e') (ω : Oracle) (env : Env Γ)
    (w : World) (hI : ItvsHold is env) (h : e'.safe ω env w) : e.safe ω env w :=
  (Exp.an_sound ω e _ env w hL (AEnv.sat_ofItvs hI)).2.2.2 (he ▸ h)

end Millipede.Analysis

namespace Millipede.Analysis

open Millipede

theorem ItvsHold.nil {Γ : List Ty} (env : Env Γ) : ItvsHold [] env := by cases env <;> trivial

/-- A word parameter with an interval. -/
theorem ItvsHold.word {Γ : List Ty} {i : Itv} {is : List Itv} {v : UInt64} {env : Env Γ}
    (h : i.mem v.toNat) (hs : ItvsHold is env) : ItvsHold (i :: is) (Env.cons (t := .u64) v env) :=
  ⟨fun _ => h, hs⟩

/-- A parameter without an interval. -/
theorem ItvsHold.top {Γ : List Ty} {t : Ty} {is : List Itv} {v : t.carrier} {env : Env Γ}
    (hs : ItvsHold is env) : ItvsHold (Itv.top :: is) (Env.cons v env) :=
  ⟨fun _ => Itv.mem_top (UInt64.toNat_lt _), hs⟩

/-- Componentwise sum of counts. -/
def addC (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

local infixl:65 " ⊕ₙ " => addC

/-- The number of overflow obligations, from `…Nuw` primitives, and of other partial operations of
a term, for reports. -/
def _root_.Millipede.Exp.oblCount : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat × Nat
  | _, _, .let_ e₁ e₂ => e₁.oblCount ⊕ₙ e₂.oblCount
  | _, _, .ite _ e₁ e₂ => e₁.oblCount ⊕ₙ e₂.oblCount
  | _, _, .prim p _ => (if p.total then 0 else 1, 0)
  | _, _, .call _ body _ => body.oblCount
  | _, _, .match_ _ eE eO => eE.oblCount ⊕ₙ eO.oblCount
  | _, _, .ext _ args => (0, if args.total then 0 else 1)
  | _, _, .extMut _ _ k => k.oblCount ⊕ₙ (0, 1)
  | _, _, .read p => (0, if p.total then 0 else 1)
  | _, _, .assign p _ k => k.oblCount ⊕ₙ (0, if p.total then 0 else 1)
  | _, _, .case _ _ eP eQ => eP.oblCount ⊕ₙ eQ.oblCount
  | _, _, .put _ _ _ k => k.oblCount ⊕ₙ (0, 1)
  | _, _, .take (dflt := _) _ _ k => k.oblCount ⊕ₙ (0, 1)
  | _, _, .borrowShr p body k => body.oblCount ⊕ₙ k.oblCount ⊕ₙ (0, if p.total then 0 else 1)
  | _, _, .borrowMut p body k => body.oblCount ⊕ₙ k.oblCount ⊕ₙ (0, if p.total then 0 else 1)
  | _, _, .callRef _ _ _ _ k => k.oblCount ⊕ₙ (0, 1)
  | _, _, .loop _ _ _ c body k => c.oblCount ⊕ₙ body.oblCount ⊕ₙ k.oblCount
  | _, _, _ => (0, 0)

end Millipede.Analysis

namespace Millipede.Analysis

open Millipede

/-- Whether a term has a loop outside callee bodies. -/
def _root_.Millipede.Exp.hasLoop : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .let_ e₁ e₂ => e₁.hasLoop || e₂.hasLoop
  | _, _, .ite _ e₁ e₂ => e₁.hasLoop || e₂.hasLoop
  | _, _, .call _ body _ => body.hasLoop
  | _, _, .match_ _ eE eO => eE.hasLoop || eO.hasLoop
  | _, _, .extMut _ _ k => k.hasLoop
  | _, _, .assign _ _ k => k.hasLoop
  | _, _, .case _ _ eP eQ => eP.hasLoop || eQ.hasLoop
  | _, _, .put _ _ _ k => k.hasLoop
  | _, _, .take (dflt := _) _ _ k => k.hasLoop
  | _, _, .borrowShr _ body k => body.hasLoop || k.hasLoop
  | _, _, .borrowMut _ body k => body.hasLoop || k.hasLoop
  | _, _, .callRef _ _ _ _ k => k.hasLoop
  | _, _, .loop _ _ _ _ _ _ => true
  | _, _, _ => false

/-- A term without loops satisfies `LoopsOk`, which the kernel decides for such terms. -/
theorem _root_.Millipede.Exp.loopsOk_of_hasLoop {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (h : e.hasLoop = false) : e.LoopsOk := by
  induction e <;> simp_all [Exp.hasLoop, Exp.LoopsOk]

/-- Whether a place has a `Slots` selector, whose obligation the analyser never certifies. -/
def _root_.Millipede.Place.opaque {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .var _ => false
  | _, .field p _ => p.opaque
  | _, .index (dflt := _) p _ => p.opaque
  | _, .range p _ _ => p.opaque
  | _, .pair2 (dflt := _) p _ _ => p.opaque
  | _, _ => true

/-- Whether a term has an operation whose obligation the analyser never certifies, which is a
`put`, a `take`, a call with references or a `Slots` place. -/
def _root_.Millipede.Exp.hasOpaque : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .let_ e₁ e₂ => e₁.hasOpaque || e₂.hasOpaque
  | _, _, .ite _ e₁ e₂ => e₁.hasOpaque || e₂.hasOpaque
  | _, _, .call _ body _ => body.hasOpaque
  | _, _, .match_ _ eE eO => eE.hasOpaque || eO.hasOpaque
  | _, _, .extMut _ _ k => k.hasOpaque
  | _, _, .read p => p.opaque
  | _, _, .assign p _ k => p.opaque || k.hasOpaque
  | _, _, .case _ _ eP eQ => eP.hasOpaque || eQ.hasOpaque
  | _, _, .borrowShr p body k => p.opaque || body.hasOpaque || k.hasOpaque
  | _, _, .borrowMut p body k => p.opaque || body.hasOpaque || k.hasOpaque
  | _, _, .loop _ _ _ c body k => c.hasOpaque || body.hasOpaque || k.hasOpaque
  | _, _, .put _ _ _ _ | _, _, .take (dflt := _) _ _ _ | _, _, .callRef _ _ _ _ _ => true
  | _, _, _ => false

/-- Whether the analyser can help with a term, by a cheap syntactic test that `mp def` uses to
skip it. The term must have overflow obligations, which the analyser may certify or relax, or no
operation that it never certifies. -/
def _root_.Millipede.Exp.anWorth {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Bool :=
  e.nuwCount != 0 || !e.hasOpaque

end Millipede.Analysis
