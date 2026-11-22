import Millipede.Analysis.Transfer
import Millipede.Meta.Sem

/-!
# Soundness of the loop analysis

A loop's state at iteration `j`, which is its accumulator and carried variables, is described by
the chosen candidates at `j`. The lemmas `loopDenote_invJ` and `loopSafe_invJ` carry such an
invariant, indexed by the counter, through the loop driver. The candidates hold initially by
`Cand.init`, and each iteration keeps them by `Cand.ok`, with the counter's value used for the
growth bounds. From the candidates the environments of the body, `sat_bodyA`, and of the
continuation, `sat_stateA`, are satisfied.
-/

namespace Millipede.Analysis

open Millipede

variable {Γ : List Ty}

/-! ## Tuples -/

/-- The components of a tuple are described by `as`, where missing descriptions are top. -/
def TupSat (env : Env Γ) : List (AVal Γ) → (ts : List Ty) → (Ty.tup ts).carrier → Prop
  | a :: as, t :: ts, v => a.sat env (t := t) (v : t.carrier × (Ty.tup ts).carrier).1 ∧
    TupSat env as ts v.2
  | _, _, _ => True

theorem TupSat.head {env : Env Γ} {os : List (AVal Γ)} {t : Ty} {ts : List Ty}
    {v : (Ty.tup (t :: ts)).carrier} (h : TupSat env os (t :: ts) v) :
    (os.headD {}).sat env (t := t) (v : t.carrier × (Ty.tup ts).carrier).1 ∧
      TupSat env os.tail ts v.2 := by
  cases os with
  | nil => exact ⟨AVal.sat_top _ _, by cases ts <;> trivial⟩
  | cons o os => exact h

theorem TupSat.unshift {s : Ty} {x : s.carrier} {env : Env Γ} :
    ∀ {os : List (AVal (s :: Γ))} {ts : List Ty} {v : (Ty.tup ts).carrier},
      TupSat (.cons x env) os ts v → TupSat env (os.map AVal.unshift) ts v
  | [], _, _, _ => by simp [TupSat]
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, _, h => ⟨AVal.sat_unshift h.1, TupSat.unshift h.2⟩

theorem TupSat.join_l {env : Env Γ} : ∀ {os os' : List (AVal Γ)} {ts : List Ty}
    {v : (Ty.tup ts).carrier}, TupSat env os ts v → TupSat env (List.zipWith AVal.join os os') ts v
  | [], _, _, _, _ => by simp [TupSat]
  | _ :: _, [], _, _, _ => by simp [TupSat]
  | _ :: _, _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, h => ⟨AVal.sat_join_l h.1, TupSat.join_l h.2⟩

theorem TupSat.join_r {env : Env Γ} : ∀ {os os' : List (AVal Γ)} {ts : List Ty}
    {v : (Ty.tup ts).carrier}, TupSat env os' ts v → TupSat env (List.zipWith AVal.join os os') ts v
  | [], _, _, _, _ => by simp [TupSat]
  | _ :: _, [], _, _, _ => by simp [TupSat]
  | _ :: _, _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, h => ⟨AVal.sat_join_r h.1, TupSat.join_r h.2⟩

theorem TupSat.forget {ks : List Nat} {env env' : Env Γ} (he : AgreeOff ks env env') :
    ∀ {os : List (AVal Γ)} {ts : List Ty} {v : (Ty.tup ts).carrier},
      TupSat env os ts v → TupSat env' (os.map (AVal.forget ks)) ts v
  | [], _, _, _ => by simp [TupSat]
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, _, h => ⟨AVal.sat_forget he h.1, TupSat.forget he h.2⟩

theorem TupSat.args {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) :
    ∀ {ps : List Ty} (args : Args Γ ps),
      TupSat env (Exp.anR.argsAVals' A args) ps (Flat.tupBuild ps (args.denote env))
  | _, .nil => trivial
  | _, .cons a as => ⟨A.atomV_sat hA a, TupSat.args hA as⟩

/-! ## Candidates -/

/-- The carried components are described by the candidates at iteration `j`. -/
def CandsSat (j : Nat) : List Cand → (ts : List Ty) → (Ty.tup ts).carrier → Prop
  | c :: cc, t :: ts, v => (c.atJ j : AVal []).sat .nil (t := t)
      (v : t.carrier × (Ty.tup ts).carrier).1 ∧ CandsSat j cc ts v.2
  | _, _, _ => True

/-- A candidate's description does not depend on the context. -/
theorem Cand.atJ_ctx {Δ Δ' : List Ty} {c : Cand} {j : Nat} {e : Env Δ} {e' : Env Δ'} {t : Ty}
    {v : t.carrier} (h : (c.atJ j : AVal Δ).sat e v) : (c.atJ j : AVal Δ').sat e' v :=
  ⟨fun hh => ⟨(h.1 hh).1, by simp [Cand.atJ]⟩, h.2.1, fun _ => by simp [Cand.atJ]⟩

theorem Cand.atJ_mono {Δ : List Ty} {c : Cand} {j j' : Nat} (hj : j ≤ j') {e : Env Δ} {t : Ty}
    {v : t.carrier} (h : (c.atJ j : AVal Δ).sat e v) : (c.atJ j' : AVal Δ).sat e v := by
  refine ⟨fun hh => ⟨?_, by simp [Cand.atJ]⟩, h.2.1, fun _ => by simp [Cand.atJ]⟩
  have := (h.1 hh).1
  have := Nat.mul_le_mul_left c.d hj
  simp only [Cand.atJ, Itv.mem] at *; omega

theorem Cand.init_sat {Δ Δ' : List Ty} {c : Cand} {a : AVal Δ} (hc : c.init a = true) {e : Env Δ}
    {e' : Env Δ'} {t : Ty} {v : t.carrier} (h : a.sat e v) : (c.atJ 0 : AVal Δ').sat e' v := by
  simp only [Cand.init, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine ⟨fun hh => ⟨?_, by simp [Cand.atJ]⟩, fun hh => Itv.mem_sub hc.2 (h.2.1 hh),
    fun _ => by simp [Cand.atJ]⟩
  have := (h.1 hh).1; simp only [Cand.atJ, Itv.mem] at *; omega

/-- One iteration keeps a candidate, since the handed-back value, described by `o` in the body
whose counter is `j`, is described at `j + 1`. -/
theorem Cand.ok_step {Δ Δ' : List Ty} {c : Cand} {o : AVal (.u64 :: Δ)} (hc : c.ok o = true)
    {j : Nat} {e : Env Δ} {e' : Env Δ'} {t : Ty} {v : t.carrier}
    (hj : j < 2 ^ 64) (h : o.sat (.cons (UInt64.ofNat j) e) v) : (c.atJ (j + 1) : AVal Δ').sat e' v := by
  simp only [Cand.ok, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  obtain ⟨⟨⟨hlo, hhi⟩, hb⟩, hg⟩ := hc
  refine ⟨fun hh => ⟨?_, by simp [Cand.atJ]⟩, fun hh => Itv.mem_sub hb (h.2.1 hh),
    fun _ => by simp [Cand.atJ]⟩
  have hw := (h.1 hh).1
  simp only [Cand.atJ, Itv.mem] at hw ⊢
  have hmul : c.d * (j + 1) = c.d * j + c.d := Nat.mul_succ _ _
  rcases hg with hg | ⟨u, hu, ⟨hy, hc0⟩, hd⟩
  · have := Nat.zero_le (c.d * j); omega
  · have hub := (h.1 hh).2 u hu
    rcases u with ⟨c0, d, (y | y)⟩
    · simp only [Atom.idx0, beq_iff_eq] at hy
      obtain ⟨-, hm⟩ := Mem.eq_of_idx y Mem.here (by simpa [Mem.idx] using hy)
      cases hm
      simp only [UB.holds, Atom.denote, Env.get_here, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hj] at hub
      have := Nat.mul_le_mul_right j hd
      dsimp only at hd hc0 this
      omega
    · simp [Atom.idx0] at hy

/-! ## Carried variables -/

theorem Carry.set_agree {ts : List Ty} (cs : Carry Γ ts) :
    ∀ (env : Env Γ) (vs : (Ty.tup ts).carrier), AgreeOff cs.idxs env (cs.set env vs) := by
  induction cs with
  | nil => intro env _; exact AgreeOff.refl _ _
  | cons m cs ih => intro env vs; exact AgreeOff.trans (agree_set (.var m) env vs.1) (ih _ _)

/-- Each carried variable holds its component. -/
def CarryHolds (E : Env Γ) {ts : List Ty} : Carry Γ ts → (Ty.tup ts).carrier → Prop
  | .nil, _ => True
  | .cons m cs, vs => E.get m = vs.1 ∧ CarryHolds E cs vs.2

theorem Carry.holds_set {ts : List Ty} (cs : Carry Γ ts) (hd : cs.distinct = true) :
    ∀ (env : Env Γ) (vs : (Ty.tup ts).carrier), CarryHolds (cs.set env vs) cs vs := by
  induction cs with
  | nil => intro _ _; trivial
  | cons m cs ih =>
    intro env vs
    simp only [Carry.distinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hd
    refine ⟨?_, ih hd.2 _ _⟩
    show (cs.set (env.set m vs.1) vs.2).get m = vs.1
    rw [Carry.set_agree cs _ _ m (by simpa using hd.1), Env.get_set_same]

theorem sat_setCands {j : Nat} {E : Env Γ} {ts : List Ty} (cs : Carry Γ ts) :
    ∀ (cc : List Cand) (vs : (Ty.tup ts).carrier) (A : AEnv Γ), A.sat E → CarryHolds E cs vs →
      CandsSat j cc ts vs → (A.setCands j cs cc).sat E := by
  induction cs with
  | nil => intro cc _ A hA _ _; cases cc <;> exact hA
  | cons m cs ih =>
    intro cc vs A hA hh hc
    cases cc with
    | nil => exact hA
    | cons c cc =>
      exact ih cc vs.2 _ (AEnv.sat_setv m hA (by rw [hh.1]; exact Cand.atJ_ctx hc.1)) hh.2 hc.2

theorem candsInit_sat {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {ts : List Ty} :
    ∀ (cs : Carry Γ ts) (cc : List Cand), candsInit A cs cc = true → CandsSat 0 cc ts (cs.get env)
  | .nil, [], _ => trivial
  | .cons m cs, c :: cc, h => by
    simp only [candsInit, Bool.and_eq_true] at h
    exact ⟨Cand.init_sat h.1 (hA.1 m), candsInit_sat hA cs cc h.2⟩
  | .nil, _ :: _, h | .cons _ _, [], h => by simp [candsInit] at h

theorem CandsSat.mono {j j' : Nat} (hj : j ≤ j') : ∀ {cc : List Cand} {ts : List Ty}
    {vs : (Ty.tup ts).carrier}, CandsSat j cc ts vs → CandsSat j' cc ts vs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, _, h => ⟨Cand.atJ_mono hj h.1, CandsSat.mono hj h.2⟩

theorem candsOk_step {Δ : List Ty} {j : Nat} (hj : j < 2 ^ 64) {e : Env Δ} :
    ∀ {cc : List Cand} {ts : List Ty} {os : List (AVal (.u64 :: Δ))} {vs : (Ty.tup ts).carrier},
      candsOk cc os = true → TupSat (.cons (UInt64.ofNat j) e) os ts vs →
      CandsSat (j + 1) cc ts vs
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _ => trivial
  | c :: cc, t :: ts, os, vs, h, ht => by
    simp only [candsOk, Bool.and_eq_true] at h
    have ht' := TupSat.head ht
    exact ⟨Cand.ok_step h.1 hj ht'.1, candsOk_step hj h.2 ht'.2⟩

/-! ## The environments of the body and the continuation -/

theorem sat_stateA {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {s : Ty} {ts : List Ty}
    (cs : Carry Γ ts) (hd : cs.distinct = true) {j : Nat} {ca : Cand} {cc : List Cand}
    {st : s.carrier × (Ty.tup ts).carrier} (ha : (ca.atJ j : AVal []).sat .nil st.1)
    (hc : CandsSat j cc ts st.2) :
    (stateA A cs j ca cc).sat (.cons st.1 (cs.set env st.2)) :=
  AEnv.sat_push (sat_setCands cs cc st.2 _ (AEnv.sat_kill hA (Carry.set_agree cs env st.2))
    (Carry.holds_set cs hd env st.2) hc) (Cand.atJ_ctx ha)

/-- Set `k` by a function of its description, when the result describes every variable at `k`. -/
theorem AEnv.sat_setv' {Δ : List Ty} {A : AEnv Δ} {env : Env Δ} {k : Nat} {a : AVal Δ}
    (hA : A.sat env) (ha : ∀ {t : Ty} (m : Mem t Δ), m.idx = k → a.sat env (env.get m)) :
    (A.setv k a).sat env := by
  refine ⟨fun m' => ?_, hA.2⟩
  rw [AEnv.get_setv]
  split
  · next h => exact ha m' h.symm
  · exact hA.1 m'

/-- Adding a growth bound `≤ c0 + d · counter` to variable `pos` keeps the environment satisfied. -/
theorem sat_addUB {Δ : List Ty} {A : AEnv (.u64 :: Δ)} {E : Env (.u64 :: Δ)} (hA : A.sat E)
    {pos : Nat} {c : Cand}
    (hb : ∀ {t : Ty} (m : Mem t (.u64 :: Δ)), m.idx = pos → ∀ h : t = .u64,
      (cast (congrArg Ty.carrier h) (E.get m) : UInt64).toNat ≤
        c.c0 + c.d * (E.get .here : UInt64).toNat) :
    (A.addUB pos c).sat E := by
  refine AEnv.sat_setv' hA fun m hm => ?_
  have h0 := hA.1 m
  rw [hm] at h0
  refine ⟨fun hh => ⟨(h0.1 hh).1, fun u hu => ?_⟩, h0.2.1, h0.2.2⟩
  simp only [List.mem_cons] at hu
  rcases hu with rfl | hu
  · simpa [UB.holds, Atom.denote] using hb m hm hh
  · exact (h0.1 hh).2 u hu

/-- The bound of a value described by a candidate at iteration `j`. -/
theorem Cand.atJ_bound {Δ : List Ty} {c : Cand} {j : Nat} {e : Env Δ} {t : Ty} {v : t.carrier}
    (h : (c.atJ j : AVal Δ).sat e v) (hh : t = .u64) :
    (cast (congrArg Ty.carrier hh) v : UInt64).toNat ≤ c.c0 + c.d * j := by
  have := (h.1 hh).1; simp only [Cand.atJ, Itv.mem] at this; omega

theorem sat_addUBs {s : Ty} {E0 : Env Γ} {x : s.carrier} {j : Nat} (hj : j < 2 ^ 64)
    {ts : List Ty} (cs : Carry Γ ts) :
    ∀ (cc : List Cand) (vs : (Ty.tup ts).carrier) (A : AEnv (.u64 :: s :: Γ)),
      A.sat (.cons (UInt64.ofNat j) (.cons x E0)) → CarryHolds E0 cs vs → CandsSat j cc ts vs →
      (A.addUBs cs cc).sat (.cons (UInt64.ofNat j) (.cons x E0)) := by
  induction cs with
  | nil => intro cc _ A hA _ _; cases cc <;> exact hA
  | cons m cs ih =>
    intro cc vs A hA hh hc
    cases cc with
    | nil => exact hA
    | cons c cc =>
      refine ih cc vs.2 _ (sat_addUB hA fun m' hm' hh' => ?_) hh.2 hc.2
      rcases m' with _ | _ | m'
      · simp [Mem.idx] at hm'
      · simp [Mem.idx] at hm'
      · simp only [Mem.idx] at hm'
        obtain ⟨rfl, hm⟩ := Mem.eq_of_idx m m' (by omega)
        cases hm
        simp only [Env.get_there, Env.get_here, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hj]
        rw [hh.1]; exact Cand.atJ_bound hc.1 hh'

theorem sat_bodyA {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {s : Ty} {ts : List Ty}
    (cs : Carry Γ ts) (hd : cs.distinct = true) {n j : Nat} (hjn : j < n) (hn : n < 2 ^ 64)
    {ca : Cand} {cc : List Cand} {st : s.carrier × (Ty.tup ts).carrier}
    (ha : (ca.atJ j : AVal []).sat .nil st.1) (hc : CandsSat j cc ts st.2) :
    (bodyA n A cs ca cc).sat (.cons (UInt64.ofNat j) (.cons st.1 (cs.set env st.2))) := by
  have hj : j < 2 ^ 64 := by omega
  have h1 := sat_stateA hA cs hd (Cand.atJ_mono (j' := n - 1) (by omega) ha)
    (CandsSat.mono (j' := n - 1) (by omega) hc)
  have h2 := AEnv.sat_push (x := UInt64.ofNat j) (a := AVal.ofW ⟨0, n - 1⟩) h1
    (AVal.sat_ofW.mpr ⟨by simp only [Itv.mem, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hj]; omega,
      by simp⟩)
  refine sat_addUBs hj cs cc st.2 _ (sat_addUB h2 fun m hm hh => ?_)
    (Carry.holds_set cs hd env st.2) hc
  rcases m with _ | _ | m
  · simp [Mem.idx] at hm
  · simp only [Env.get_there, Env.get_here, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hj]
    exact Cand.atJ_bound ha hh
  · simp [Mem.idx] at hm

end Millipede.Analysis
