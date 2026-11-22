import Millipede.Analysis.Analyze

/-!
# Soundness of the transfer functions

This module proves the transfer functions for primitives, places, extern arguments and writes
sound. `anPrim_sound` says that the description of a primitive's value holds and that a certified
obligation `Prim.ok` holds. `Place.okA_sound` and `EArgs.okA_sound` say that certified place and
slice obligations hold. `AEnv.sat_write` and `sat_fill` describe the environment after a write or
after an extern fills a slice.
-/

namespace Millipede.Analysis

open Millipede

variable {Γ : List Ty}

/-! ## Words -/

theorem wAdd_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wAdd a b).mem (x + y).toNat := by
  unfold wAdd; split
  · rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp only [Itv.mem, wmax] at *; omega)]
    simp only [Itv.mem] at *; omega
  · exact Itv.mem_top (UInt64.toNat_lt _)

theorem wMul_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wMul a b).mem (x * y).toNat := by
  unfold wMul; split
  · next h =>
    simp only [Itv.mem] at ha hb
    have h1 := Nat.mul_le_mul ha.2 hb.2
    have h2 := Nat.mul_le_mul ha.1 hb.1
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simp only [wmax] at h; omega)]
    exact ⟨h2, h1⟩
  · exact Itv.mem_top (UInt64.toNat_lt _)

theorem wSub_mem {ge : Bool} {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat)
    (hge : ge = true → y.toNat ≤ x.toNat) : (wSub ge a b).mem (x - y).toNat := by
  unfold wSub; split
  · next h =>
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (hge h))]
    simp only [Itv.mem] at *; omega
  · exact Itv.mem_top (UInt64.toNat_lt _)

theorem wDiv_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wDiv a b).mem (x / y).toNat := by
  rw [UInt64.toNat_div]; unfold wDiv; simp only [Itv.mem] at *; split
  · exact ⟨Nat.le_trans (Nat.div_le_div_left hb.2 (by omega)) (Nat.div_le_div_right ha.1),
      Nat.le_trans (Nat.div_le_div_right ha.2) (Nat.div_le_div_left hb.1 (by omega))⟩
  · exact ⟨Nat.zero_le _, Nat.le_trans (Nat.div_le_self _ _) ha.2⟩

theorem wMod_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wMod a b).mem (x % y).toNat := by
  rw [UInt64.toNat_mod]; unfold wMod; simp only [Itv.mem] at *
  have := Nat.mod_le x.toNat y.toNat
  refine ⟨Nat.zero_le _, ?_⟩; split
  · have := Nat.mod_lt x.toNat (show 0 < y.toNat by omega); omega
  · omega

theorem wAnd_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wAnd a b).mem (x &&& y).toNat := by
  rw [UInt64.toNat_and]; simp only [wAnd, Itv.mem] at *
  have := @Nat.and_le_left x.toNat y.toNat; have := @Nat.and_le_right x.toNat y.toNat; omega

theorem wShr_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wShr a b).mem (x >>> y).toNat := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; unfold wShr; simp only [Itv.mem] at *
  split
  · next h =>
    rw [show y.toNat % 64 = b.hi by omega]
    exact ⟨Nat.div_le_div_right ha.1, Nat.div_le_div_right ha.2⟩
  · exact ⟨Nat.zero_le _, Nat.le_trans (Nat.div_le_self _ _) ha.2⟩

theorem wShl_mem {a b : Itv} {x y : UInt64} (ha : a.mem x.toNat) (hb : b.mem y.toNat) :
    (wShl a b).mem (x <<< y).toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; unfold wShl
  split
  · next h =>
    simp only [Itv.mem] at *
    rw [show y.toNat % 64 = b.hi by omega]
    have h1 := Nat.mul_le_mul_right (2 ^ b.hi) ha.2
    have h2 := Nat.mul_le_mul_right (2 ^ b.hi) ha.1
    rw [Nat.mod_eq_of_lt (by simp only [wmax] at h; omega)]
    exact ⟨h2, h1⟩
  · exact Itv.mem_top (Nat.mod_lt _ (by decide))

theorem wTrunc8_mem {a : Itv} {x : UInt64} (ha : a.mem x.toNat) :
    (wTrunc8 a).mem x.toUInt8.toNat := by
  rw [UInt64.toNat_toUInt8]; unfold wTrunc8; split
  · next h => rw [Nat.mod_eq_of_lt (by simp only [Itv.mem] at ha; omega)]; exact ha
  · exact Itv.mem_top8 (Nat.mod_lt _ (by decide))

theorem AEnv.geq_sound {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {x y : Atom Γ .u64}
    (h : A.geq x y = true) : (y.denote env).toNat ≤ (x.denote env).toNat := by
  simp only [AEnv.geq, Bool.or_eq_true, decide_eq_true_eq] at h
  have hx := A.atomW_mem hA x; have hy := A.atomW_mem hA y
  simp only [Itv.mem] at hx hy
  rcases h with (h | h) | h
  · omega
  · simpa [Cmp.holds, COp.eval] using A.has_holds hA h
  · have := A.has_holds hA h; simp only [Cmp.holds, COp.eval] at this; omega

theorem AEnv.addV_sat {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) (x y : Atom Γ .u64) :
    (A.addV x y).sat env (t := .u64) (x.denote env + y.denote env) := by
  have hx := A.atomW_mem hA x; have hy := A.atomW_mem hA y
  unfold AEnv.addV; split
  · next h =>
    refine AVal.sat_ofW.mpr ⟨wAdd_mem hx hy, fun u hu => ?_⟩
    simp only [Itv.mem, wmax] at hx hy h
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp only [AEnv.sumUB, List.mem_append, List.mem_map] at hu
    rcases hu with ⟨u', hu', rfl⟩ | ⟨u', hu', rfl⟩
    · have := A.atomUB_holds hA x u' hu'; simp only [UB.holds] at this ⊢; omega
    · have := A.atomUB_holds hA y u' hu'; simp only [UB.holds] at this ⊢; omega
  · exact AVal.sat_ofW.mpr ⟨Itv.mem_top (UInt64.toNat_lt _), by simp⟩

/-! ## Booleans -/

theorem sat_not {a : AVal Γ} {env : Env Γ} {v : Bool} (h : a.sat env (t := .bool) v) :
    (AVal.ofBool a.f a.t).sat env (t := .bool) (!v) := by
  have h1 := AVal.sat_bool h
  refine AVal.sat_ofBool.mpr ⟨fun hv => h1.2 (by simpa using hv), fun hv => h1.1 (by simpa using hv)⟩

theorem sat_and {a b : AVal Γ} {env : Env Γ} {v w : Bool} (ha : a.sat env (t := .bool) v)
    (hb : b.sat env (t := .bool) w) :
    (AVal.ofBool (a.t ++ b.t) []).sat env (t := .bool) (v && w) := by
  have h1 := AVal.sat_bool ha; have h2 := AVal.sat_bool hb
  refine AVal.sat_ofBool.mpr ⟨fun h c hc => ?_, fun _ c hc => by simp at hc⟩
  simp only [Bool.and_eq_true, List.mem_append] at h hc
  rcases hc with hc | hc
  · exact h1.1 h.1 c hc
  · exact h2.1 h.2 c hc

theorem sat_or {a b : AVal Γ} {env : Env Γ} {v w : Bool} (ha : a.sat env (t := .bool) v)
    (hb : b.sat env (t := .bool) w) :
    (AVal.ofBool [] (a.f ++ b.f)).sat env (t := .bool) (v || w) := by
  have h1 := AVal.sat_bool ha; have h2 := AVal.sat_bool hb
  refine AVal.sat_ofBool.mpr ⟨fun _ c hc => by simp at hc, fun h c hc => ?_⟩
  simp only [Bool.or_eq_false_iff, List.mem_append] at h hc
  rcases hc with hc | hc
  · exact h1.2 h.1 c hc
  · exact h2.2 h.2 c hc

/-! ## Primitives -/

theorem anPrim_sound {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {ps : List Ty} {r : Ty}
    (p : Prim ps r) (args : Args Γ ps) :
    (anPrim A p args).2.sat env (p.denote (args.denote env)) ∧
      ((anPrim A p args).1 = true → p.ok (args.denote env)) := by
  have hW := A.atomW_mem hA
  have hV := fun {t : Ty} (a : Atom Γ t) => A.atomV_sat hA a
  have ofW := fun {w : Itv} {v : UInt64} (h : w.mem v.toNat) =>
    (AVal.sat_ofW (Γ := Γ) (env := env) (ub := [])).mpr ⟨h, by simp⟩
  cases p <;> rcases args with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;>
    simp only [anPrim, Prim.denote, Prim.ok, Args.denote, Env.get_here, Env.get_there,
      Args.a0_cons, Args.a1_cons, imp_self, and_true]
  all_goals first
    | exact A.addV_sat hA x y
    | exact ⟨A.addV_sat hA x y, fun h => by
        have h1 := hW x; have h2 := hW y; simp only [Itv.mem] at h1 h2
        have h : _ ≤ 2 ^ 64 - 1 := of_decide_eq_true h; omega⟩
    | exact ofW (wSub_mem (hW x) (hW y) (A.geq_sound hA))
    | exact ⟨ofW (wSub_mem (hW x) (hW y) (A.geq_sound hA)), A.geq_sound hA⟩
    | exact ofW (wMul_mem (hW x) (hW y))
    | exact ⟨ofW (wMul_mem (hW x) (hW y)), fun h => by
        have h1 := hW x; have h2 := hW y; simp only [Itv.mem] at h1 h2
        have h : _ ≤ 2 ^ 64 - 1 := of_decide_eq_true h
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul h1.2 h2.2) (by omega)⟩
    | exact ofW (wDiv_mem (hW x) (hW y))
    | exact ofW (wMod_mem (hW x) (hW y))
    | exact ofW (wAnd_mem (hW x) (hW y))
    | exact ofW (wShl_mem (hW x) (hW y))
    | exact ofW (wShr_mem (hW x) (hW y))
    | exact AVal.sat_top _ _
    | exact ofW (by simpa [UInt8.toNat_toUInt64] using AVal.sat_b (hV x))
    | exact AVal.sat_ofB.mpr (wTrunc8_mem (hW x))
    | exact ⟨AVal.sat_ofB.mpr (wTrunc8_mem (hW x)), fun h => by
        have h1 := hW x; simp only [Itv.mem] at h1; have h := of_decide_eq_true h; omega⟩
    | (refine AVal.sat_ofBool.mpr ⟨fun h c hc => ?_, fun h c hc => ?_⟩ <;>
        simp only [List.mem_singleton] at hc <;> subst hc <;>
        simp only [Cmp.holds, COp.eval, decide_eq_true_eq, decide_eq_false_iff_not,
          UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ne_eq, UInt64.toNat_inj, decide_not,
          Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not] at h ⊢ <;> omega)
    | exact sat_not (hV x)
    | exact sat_and (hV x) (hV y)
    | exact sat_or (hV x) (hV y)

/-! ## Places and extern arguments -/

theorem Place.okA_sound {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {t : Ty} (p : Place Γ t)
    (h : Place.okA A p = true) : p.ok env := by
  induction p with
  | var => trivial
  | field p _ ih => exact ih h
  | index p i ih =>
    simp only [Place.okA, Bool.and_eq_true, decide_eq_true_eq] at h
    have := A.atomW_mem hA i; simp only [Itv.mem] at this
    exact ⟨ih h.1, by omega⟩
  | slot => simp [Place.okA] at h
  | range p lo len ih =>
    simp only [Place.okA, Bool.and_eq_true, decide_eq_true_eq] at h
    have := A.atomW_mem hA lo; have := A.atomW_mem hA len; simp only [Itv.mem] at *
    exact ⟨ih h.1, by omega⟩
  | pair2 p i j ih =>
    simp only [Place.okA, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    have hi := A.atomW_mem hA i; have hj := A.atomW_mem hA j; simp only [Itv.mem] at hi hj
    refine ⟨ih h.1.1.1, by omega, by omega, ?_⟩
    rcases h.2 with (h' | h') | h'
    · omega
    · omega
    · simpa [Cmp.holds, COp.eval] using A.has_holds hA h'
  | rangeS => simp [Place.okA] at h
  | pair2S => simp [Place.okA] at h

theorem Place.readV_sat {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {t : Ty} (p : Place Γ t) :
    (Place.readV A p).sat env (p.get env) := by
  cases p with
  | var m => exact hA.1 m
  | _ => exact AVal.sat_top _ _

theorem EArgs.okA_sound {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {ps : List ExtParam}
    (as : EArgs Γ ps) (h : EArgs.okA A as = true) : as.ok env := by
  induction as with
  | nil => trivial
  | word _ _ ih => exact ih h
  | bufIn b _ ih =>
    cases b with
    | const => exact ih h
    | slice a lo len =>
      simp only [EArgs.okA, Bool.and_eq_true, decide_eq_true_eq] at h
      have := A.atomW_mem hA lo; have := A.atomW_mem hA len; simp only [Itv.mem] at *
      exact ⟨⟨Place.okA_sound hA a h.1.1, by omega⟩, ih h.2⟩
  | bufOut _ ih => exact ih h
  | sliceOut a lo cap _ ih =>
    simp only [EArgs.okA, Bool.and_eq_true, decide_eq_true_eq] at h
    have := A.atomW_mem hA lo; have := A.atomW_mem hA cap; simp only [Itv.mem] at *
    exact ⟨⟨Place.okA_sound hA a h.1.1, by omega⟩, ih h.2⟩

/-! ## Writes -/

theorem AgreeOff.trans {ks ks' : List Nat} {e₁ e₂ e₃ : Env Γ} (h₁ : AgreeOff ks e₁ e₂)
    (h₂ : AgreeOff ks' e₂ e₃) : AgreeOff (ks ++ ks') e₁ e₃ := fun m hm => by
  simp only [List.mem_append, not_or] at hm
  rw [h₂ m hm.2, h₁ m hm.1]

theorem AgreeOff.refl (ks : List Nat) (env : Env Γ) : AgreeOff ks env env := fun _ _ => rfl

theorem AgreeOff.symm {ks : List Nat} {e₁ e₂ : Env Γ} (h : AgreeOff ks e₁ e₂) : AgreeOff ks e₂ e₁ :=
  fun m hm => (h m hm).symm

theorem agree_set {t : Ty} (p : Place Γ t) (env : Env Γ) (v : t.carrier) :
    AgreeOff [p.root] env (p.set env v) :=
  fun m hm => Place.get_set_ne p env v m (by simpa using hm)

theorem EArgs.fill_agree {ps : List ExtParam} (as : EArgs Γ ps) (env : Env Γ) :
    ∀ (env' : Env Γ) (bss : List (List UInt8)),
      AgreeOff (EArgs.outRoots as) env' (as.fill env env' bss) := by
  induction as with
  | nil => intro env' _; exact AgreeOff.refl _ _
  | word _ _ ih => intro env' bss; exact ih env' _
  | bufIn _ _ ih => intro env' bss; exact ih env' _
  | bufOut _ ih => intro env' bss; exact ih env' _
  | sliceOut a lo cap _ ih =>
    intro env' bss
    exact AgreeOff.trans (agree_set a env' _) (ih _ _)

theorem RArgs.writeBack_agree {ps os : List Ty} (as : RArgs Γ ps os) :
    ∀ (env : Env Γ) (vs : (Ty.tup os).carrier), AgreeOff (RArgs.mutRoots as) env (as.writeBack env vs) := by
  induction as with
  | nil => intro env _; exact AgreeOff.refl _ _
  | own _ _ ih => intro env vs; exact ih env vs
  | shr _ _ ih => intro env vs; exact ih env vs
  | «mut» p _ ih => intro env vs; exact AgreeOff.trans (agree_set p env vs.1) (ih _ _)

theorem AEnv.sat_write {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {t : Ty} (p : Place Γ t)
    {a : AVal Γ} {v : t.carrier} (ha : a.sat env v) : (A.write p a).sat (p.set env v) := by
  cases p with
  | var m =>
    have he : AgreeOff [m.idx] env (env.set m v) := agree_set (.var m) env v
    show ((A.kill [m.idx]).setv m.idx (a.forget [m.idx])).sat (env.set m v)
    refine AEnv.sat_setv m (AEnv.sat_kill hA he) ?_
    rw [Env.get_set_same]; exact AVal.sat_forget he ha
  | _ => exact AEnv.sat_kill hA (agree_set _ env v)

/-! ## Call arguments -/

theorem argsAVals_get {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {ps : List Ty}
    (args : Args Γ ps) : ∀ {Δ : List Ty} (env' : Env Δ) {t : Ty} (m : Mem t ps),
      ((argsAVals (Δ := Δ) A args)[m.idx]?.getD {}).sat env' ((args.denote env).get m) := by
  induction args with
  | nil => intro _ _ _ m; cases m
  | cons a as ih =>
    intro _ env' _ m
    cases m with
    | here => exact AVal.sat_plain (A.atomV_sat hA a)
    | there m => simpa [argsAVals, Mem.idx, Args.denote] using ih env' m

theorem argsAVals_sat {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {ps : List Ty}
    (args : Args Γ ps) : (⟨argsAVals A args, []⟩ : AEnv ps).sat (args.denote env) :=
  ⟨fun m => argsAVals_get hA args _ m, by simp⟩

end Millipede.Analysis
