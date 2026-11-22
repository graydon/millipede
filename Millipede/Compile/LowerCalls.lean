import Millipede.Compile.LowerExt
import Millipede.Compile.LowerFill

/-!
# The memory refinement of calls, constructors and `Slots`

This module proves the case lemmas for `call`, `mk`, `put` and `take` under the memory lowering.

A call copies its owned arguments into the callee's region. A one-word parameter that the callee
never takes the address of is passed instead as a word into a slot of the callee's frame. A
result that the callee computes in tail mode `Tl.word` is returned as words, and any other result
is left at the callee's destination.

A constructor copies each argument to its placements and then writes the tag byte. In a tail mode
that hands back references, it writes only the first argument, because the others are the
references themselves and are already in place. In tail mode `word`, it writes the tag word and
the arguments' words into the slots. `put` writes a cell of a `Slots` place, and `take` copies a
cell out and empties it logically.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-! ## Calls -/

/-- The run-time knowledge of owned parameters at consecutive offsets of a region at `bp'`. -/
def ownS (bp' : Nat) (offs : List Nat) : List SI := offs.map fun o => ⟨bp' + o, none, none, none⟩

/-- The parameters at offsets from `o' ≥ o + sz` are away from `[o, o + sz)`. -/
theorem Away.paramLocs (wp : Nat → Bool) {bp' o sz : Nat} :
    ∀ (ps : List Ty) (o' j : Nat), o + sz ≤ o' →
      Away bp' o sz ps (paramLocs wp ps o' j) (ownS bp' (paramOffs ps o'))
  | [], _, _, _ => trivial
  | t :: ts, o', j, ho => by
    simp only [Flat.paramLocs, paramOffs, ownS, List.map_cons]
    refine ⟨?_, ?_, Away.paramLocs wp ts (o' + t.size) (j + 1) (by omega)⟩
    · split <;> exact Or.inl (by simp [Loc.off]; omega)
    · simp only [SI.Out_mk, SI.sz_mk_none]; exact Or.inl (by omega)

/-- The callee's parameters form a layout for any choice of writable variables, with the word
parameters slot-resident and the others at consecutive offsets. -/
theorem Lay.paramLocs (wp : Nat → Bool) (bp' : Nat) : ∀ (ps : List Ty) (o j : Nat) (W : List Bool),
    Lay bp' (o + ctxSize ps) ps (paramLocs wp ps o j) (ownS bp' (paramOffs ps o)) W
  | [], _, _, _ => trivial
  | t :: ts, o, j, W => by
    have ih := Lay.paramLocs wp bp' ts (o + t.size) (j + 1) W.tail
    simp only [ctxSize, ← Nat.add_assoc] at ih ⊢
    have := Lay.pushAtL (n := o + t.size + ctxSize ts) (m := o + t.size + ctxSize ts) t
      (W.headD false) (l := if wp j then .slot o (FR + slotsIn (Flat.paramLocs wp ts (o + t.size)
        (j + 1))) 1 else .own o) (by split <;> simp) ih (Away.paramLocs wp ts _ _ (Nat.le_refl _))
      (by omega) (Nat.le_refl _)
    cases W <;> exact this

/-- Each word parameter's argument has its word in its scratch slot, counting from parameter
number `j`. -/
def _root_.Millipede.Args.Words {Γ : List Ty} (wp : Nat → Bool) (env : Env Γ) (f : Frame) :
    {ps : List Ty} → Args Γ ps → Nat → Prop
  | _, .nil, _ => True
  | _, .cons (t := t) a as, j =>
    (wp j = true → WordRel t (a.denote env) (f (REXT + j))) ∧ Args.Words wp env f as (j + 1)

theorem _root_.Millipede.Args.Words.congr {Γ : List Ty} {wp : Nat → Bool} {env : Env Γ}
    {f f' : Frame} : ∀ {ps : List Ty} {args : Args Γ ps} {j : Nat}, args.Words wp env f j →
      (∀ j', j ≤ j' → f' (REXT + j') = f (REXT + j')) → args.Words wp env f' j
  | _, .nil, _, _, _ => trivial
  | _, .cons _ _, j, h, hf => ⟨fun hw => by rw [hf j (Nat.le_refl _)]; exact h.1 hw,
      Args.Words.congr h.2 fun j' hj' => hf j' (by omega)⟩

/-- `argsPass`, starting at parameter number `j`, puts each word parameter's word into its scratch
slot `REXT + j` and copies every other argument to its offset in the callee's region at `bp + n`,
where it is represented. Only `RT`, `RP` and the scratch slots `REXT + j'` for `j' ≥ j` change in
the frame. -/
theorem argsPass_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} (wp : Nat → Bool) (hl : Lay bp n Γ ρ S W) :
    ∀ {ps : List Ty} (args : Args Γ ps) (o j : Nat) (f : Frame) (h : Heap),
      (∀ i, wp (j + i) = true → (ps.getD i .unit).wordTy = true ∧ REXT + j + i < FR) →
      bp + n + o + ctxSize ps ≤ UInt64.size → f BP = UInt64.ofNat bp → MEnvRel h bp env ρ S →
      FEnvRel f env ρ → args.NoHole S → bp + n + o + ctxSize ps ≤ L → args.NoExt S →
      ∃ f' h', Runs κ ω L (argsPass wp args ρ (n + o) j) f h f' h' ∧ f' BP = f BP ∧
        (∀ x, x ≠ RT → x ≠ RP → (∀ j', j ≤ j' → x ≠ REXT + j') → f' x = f x) ∧
        (∀ a, a < UInt64.size → ¬ (bp + n + o ≤ a ∧ a < bp + n + o + ctxSize ps) →
          h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
        MEnvRel h' (bp + n) (args.denote env) (paramLocs wp ps o j)
          (ownS (bp + n) (paramOffs ps o)) ∧
        args.Words wp env f' j
  | _, .nil, _, _, f, h, _, _, _, _, _, _, _, _ =>
    ⟨f, h, Runs.skip _ _, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, trivial, trivial⟩
  | _, .cons (t := t) a as, o, j, f, h, hwp, hb, hf, henv, hfe, hnh, hbL, hne => by
    simp only [ctxSize] at hb hbL
    have hl' := hl.length
    -- the head: a word into `REXT + j`, or a copy to its offset
    obtain ⟨f₁, h₁, hr₁, hf₁, hk₁, hm₁, hv₁, hw₁⟩ : ∃ f₁ h₁,
        Runs κ ω L (if wp j then atomWord a ρ (REXT + j) else atomTo a ρ (n + o)) f h f₁ h₁ ∧
        f₁ BP = f BP ∧ (∀ x, x ≠ RT → x ≠ RP → x ≠ REXT + j → f₁ x = f x) ∧
        (∀ a', a' < UInt64.size → ¬ (bp + n + o ≤ a' ∧ a' < bp + n + o + t.size) →
          h₁ (UInt64.ofNat a') = h (UInt64.ofNat a')) ∧
        (wp j = false → VarRel h₁ t (a.denote env) ⟨bp + n + o, none, none, none⟩) ∧
        (wp j = true → WordRel t (a.denote env) (f₁ (REXT + j))) := by
      cases hj : wp j
      · obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a
          (d := n + o) hl (hl.away (by omega)) (by omega) (by omega) hf henv hfe hnh.1 (by omega)
          (by omega) hne.1
        refine ⟨f₁, _, by simpa using hr₁, hf₁ BP (by decide) (by decide),
          fun x h1 h2 _ => hf₁ x h1 h2, fun x hx hn => wr_out (by omega) hx (by omega),
          fun _ => ?_, fun e => by cases e⟩
        have e : rd (wr h (bp + (n + o)) B) (bp + n + o) t.size = B := by
          rw [← hBl, ← Nat.add_assoc, rd_wr _ _ _ (by omega)]
        exact VarRel.of_exact (by show Data.reprBytes _ (rd _ (bp + n + o) t.size); rw [e]; exact hBr)
      · have hts := (hwp 0 (by simpa using hj)).1
        have hlt := (hwp 0 (by simpa using hj)).2
        obtain ⟨v, hv, hr⟩ := atomWord_word (κ := κ) (ω := ω) (L := L) a (REXT + j) hf henv hfe hl
          hnh.1 (by omega) (by omega) (by simpa using hts)
        refine ⟨f.set (REXT + j) v, h, ⟨(by simpa using hr), fun x hx => Frame.set_ne _ _ (by
          simp only [REXT, FR, Nat.add_zero] at hx hlt ⊢; omega)⟩, Frame.set_ne _ _ (by simp only [REXT, BP]; omega),
          fun x _ _ h3 => Frame.set_ne _ _ h3, fun _ _ _ => rfl, (fun e => by cases e),
          (fun _ => by simpa using hv)⟩
    obtain ⟨f', h', hr, hb', hk', hout, hrel, hws⟩ := argsPass_runs wp hl as (o + t.size) (j + 1) f₁ h₁
      (fun i hi => by
        have := hwp (i + 1) (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this)
      (by omega) (hf₁.trans hf)
      (henv.above hl fun x hx => hm₁ x (by omega) (by omega)) (hfe.keep hr₁.keep) hnh.2 (by omega)
      hne.2
    refine ⟨f', h', Runs.seq hr₁ (by rw [show n + o + t.size = n + (o + t.size) by omega]; exact hr),
      hb'.trans hf₁, fun x h1 h2 h3 => (hk' x h1 h2 fun j' hj' => h3 j' (by omega)).trans
        (hk₁ x h1 h2 (h3 j (Nat.le_refl _))), fun x hx hn => ?_, ⟨fun hs => ?_, ?_, hrel⟩,
      ⟨fun hw => ?_, hws⟩⟩
    · simp only [ctxSize] at hn
      rw [hout x hx (by omega)]; exact hm₁ x hx (by omega)
    · cases hj : wp j
      · have := hv₁ hj
        exact this.congr fun x hx _ => hout x (by have := this; simp [SI.In_mk, InR] at hx; omega)
          (by simp [SI.In_mk, InR] at hx; omega)
      · have hts := (hwp 0 (by simpa using hj)).1
        simp only [List.getD_cons_zero] at hts
        simp only [hj, ↓reduceIte, Loc.isSlot, Loc.slot?, Ty.wordTy_slotTy hts] at hs
        simp at hs
    · cases hj : wp j <;> simp [PtrOk]
    · rw [hk' _ (by simp only [REXT, RT]; omega) (by simp only [REXT, RP]; omega)
        fun j' hj' => by omega]; exact hw₁ hw

/-- Entering and returning from a call. The callee runs from a fresh frame holding its base
pointer and returns to the caller's frame with the words of `ret` written to `dst…`, and the
caller continues with `c₂`. -/
theorem MSim.call_step {α β : Type} {name : String} {fr : Nat} {body : Stmt} {ret : List Operand}
    {ops : List Operand} {dst : Nat} {k : List Kont} {c₂ : Stmt} {f : Frame} {h : Heap} {w : World} {cl : Nat}
    {Q₁ : α → Frame → Heap → Prop} {Q : β → Frame → Heap → Prop}
    {prot prot₁ prot₂ pf₁ pf : Nat → Prop} {r₁ : Out α} {r₂ : Out β} (hw : w.halted = false)
    (h₁ : MSim κ ω L ⟨body, .ret ret dst f :: .seq c₂ :: k, Frame.ofList (ops.map (Operand.eval f)),
      h, w, cl⟩ (.ret ret dst f :: .seq c₂ :: k) Q₁ prot₁ r₁ pf₁)
    (hhalt : r₁.world.halted = true → r₂.world = r₁.world)
    (hp : ∀ a, prot a → prot₁ a ∧ prot₂ a)
    (hbp : ∀ f₁ : Frame, (f.writes dst (ret.map (Operand.eval f₁))) BP = f BP)
    (hpf : ∀ (f₁ : Frame) x, FR ≤ x → pf x → (f.writes dst (ret.map (Operand.eval f₁))) x = f x)
    (h₂ : ∀ f₁ m₁, Q₁ r₁.val f₁ m₁ →
      (∀ a, prot₁ a → m₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) → r₁.world.halted = false →
      MSim κ ω L ⟨c₂, k, f.writes dst (ret.map (Operand.eval f₁)), m₁, r₁.world, cl + r₁.steps⟩ k
        Q prot₂ r₂ pf) :
    MSim κ ω L ⟨.seq (.call name fr body ret ops dst) c₂, k, f, h, w, cl⟩ k Q prot
      ⟨r₂.val, r₂.world, r₁.steps + r₂.steps⟩ pf := by
  have hent : ReachL κ ω L ⟨.seq (.call name fr body ret ops dst) c₂, k, f, h, w, cl⟩
      ⟨body, .ret ret dst f :: .seq c₂ :: k, Frame.ofList (ops.map (Operand.eval f)), h, w, cl⟩ :=
    ReachL.step' hw (by simp only [exec1]; exact ReachL.step' hw (by
      simp only [exec1]; exact ReachL.refl _))
  obtain ⟨s₁, hr₁, hw₁, hc₁, h4⟩ := h₁
  cases hh : r₁.world.halted with
  | true =>
    refine ⟨s₁, hent.trans hr₁, by simp only; rw [hhalt hh]; exact hw₁, by simp only at hc₁ ⊢; omega, ?_⟩
    left; simp only; rw [hhalt hh]; exact hh
  | false =>
    rcases h4 with h | ⟨hcur, hk, hcl, hf, hv, hm, -⟩
    · rw [hh] at h; cases h
    obtain ⟨cur, kont, f₁, m₁, w₁, c₁⟩ := s₁
    simp only at hcur hk hcl hf hv hm hw₁
    subst hcur hk hcl hw₁
    obtain ⟨s₂, hr₂, hw₂, hc₂, h5⟩ := h₂ f₁ m₁ hv hm hh
    have hr : ReachL κ ω L ⟨.seq (.call name fr body ret ops dst) c₂, k, f, h, w, cl⟩ s₂ :=
      (hent.trans hr₁).trans (ReachL.step' hh (by
        simp only [exec1]; exact ReachL.step' hh (by
          simp only [exec1]; exact hr₂)))
    refine ⟨s₂, hr, hw₂, by simp only at hc₂ ⊢; omega, ?_⟩
    rcases h5 with h | ⟨a, b, cl', d', e, g, g'⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, b, by simp only at cl' ⊢; omega, d'.trans (hbp f₁), e, fun x hx => ?_,
        fun x hx hp => (g' x hx hp).trans (hpf f₁ x hx hp)⟩
      exact (g x (hp x hx).2).trans (hm x (hp x hx).1)

theorem InW.ownS_ge {bp' x : Nat} : ∀ {ps : List Ty} {offs : List Nat} {W : List Bool},
    InW ps (ownS bp' offs) W x → bp' ≤ x
  | _ :: _, _ :: _, W, h => by
    rcases h with ⟨_, h⟩ | h
    · simp only [SI.In_mk, InR] at h; omega
    · exact InW.ownS_ge h
  | [], _, _, h => (h : False).elim
  | _ :: _, [], _, h => (h : False).elim

theorem HoleAv.none_of {Γ : List Ty} {t : Ty} {e : Exp Γ t} {S : List SI}
    (h : ∀ i, (S.getD i default).hole = none) : HoleAv e S :=
  fun i H hH => by rw [h i] at hH; cases hH

theorem ownS_hole (bp' : Nat) (offs : List Nat) (i : Nat) :
    ((ownS bp' offs).getD i default).hole = none := by
  unfold ownS
  induction offs generalizing i with
  | nil => rfl
  | cons o offs ih => cases i <;> simp_all

theorem ownS_ext (bp' : Nat) (offs : List Nat) (i : Nat) :
    ((ownS bp' offs).getD i default).ext = none := by
  unfold ownS
  induction offs generalizing i with
  | nil => rfl
  | cons o offs ih => cases i <;> simp_all

theorem VS.of_none {S : List SI} {P : Nat → Bool} (h : ∀ i, (S.getD i default).ext = none) :
    VS S P := fun i hi => absurd (h i) hi

/-- The callee's frame represents its word parameters. The word of parameter number `j`, held in
the caller's scratch slot `REXT + j`, is in the callee's frame slot that `paramLocs` assigns to
it. -/
theorem FEnvRel.params {Γ : List Ty} {env : Env Γ} (wp : Nat → Bool) (f G : Frame) :
    ∀ {ps : List Ty} (args : Args Γ ps) (o j : Nat),
      (∀ i, wp (j + i) = true → (ps.getD i .unit).wordTy = true) → args.Words wp env f j →
      (∀ i, i < (paramWords wp ps j).length →
        G (FR + i) = ((paramWords wp ps j).getD i (.imm 0)).eval f) →
      FEnvRel G (args.denote env) (paramLocs wp ps o j)
  | _, .nil, _, _, _, _, _ => rfl
  | _, .cons (t := t) (ts := ts) a as, o, j, hts, hw, hG => by
    simp only [Flat.paramLocs, Args.denote]
    have hts' : ∀ i, wp (j + 1 + i) = true → (ts.getD i .unit).wordTy = true := fun i hi => by
      have := hts (i + 1) (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi)
      simpa using this
    refine ⟨?_, FEnvRel.params wp f G as (o + t.size) (j + 1) hts' hw.2 fun i hi => ?_⟩
    · split
      · rename_i hj
        have := hts 0 (by simpa using hj)
        simp only [List.getD_cons_zero] at this
        refine ⟨Nat.le_add_right _ _, Ty.wordTy_slotTy this, (Ty.wordTy_slotN this).symm,
          (wordsRel_one (Ty.wordTy_slotN this)).2 ?_⟩
        rw [slotsIn_paramLocs, hG _ (by simp [paramWords, hj])]
        simpa [paramWords, hj, List.getD_eq_getElem?_getD, List.getElem?_append_right] using hw.1 hj
      · trivial
    · rw [hG i (by simp only [paramWords, List.length_append]; omega)]
      simp only [paramWords, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The callee's frame of a call: its base pointer, then the words of its word parameters at
`FR, FR + 1, …`. -/
theorem callOps_frame (wp : Nat → Bool) (ps : List Ty) (f : Frame) (i : Nat) :
    Frame.ofList ((callOps wp ps).map (Operand.eval f)) (FR + i) =
      ((paramWords wp ps 0).getD i (.imm 0)).eval f := by
  simp only [Frame.ofList, callOps, List.map_cons, List.map_append, List.map_replicate,
    List.getD_eq_getElem?_getD]
  rw [show FR + i = (FR - 1 + i) + 1 by simp [FR]; omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp [FR]), List.length_replicate, Nat.add_sub_cancel_left,
    List.getElem?_map]
  cases (paramWords wp ps 0)[i]? <;> rfl

theorem callOps_BP (wp : Nat → Bool) (ps : List Ty) (f : Frame) :
    Frame.ofList ((callOps wp ps).map (Operand.eval f)) BP = f RX := rfl

/-- A slot-resident parameter is a word parameter. -/
theorem paramLocs_slot (wp : Nat → Bool) :
    ∀ (ps : List Ty) (o j i : Nat), ((paramLocs wp ps o j).getD i default).isSlot = true →
      wp (j + i) = true
  | [], _, _, i, h => by simp [Flat.paramLocs, Loc.isSlot] at h
  | _ :: ts, o, j, 0, h => by
    simp only [Flat.paramLocs, List.getD_cons_zero] at h; split at h
    · simpa using ‹wp j = true›
    · simp at h
  | _ :: ts, o, j, i + 1, h => by
    simp only [Flat.paramLocs, List.getD_cons_succ] at h
    rw [show j + (i + 1) = j + 1 + i by omega]; exact paramLocs_slot wp ts _ _ i h

/-- The callee's tail mode for a word result is its slot `FR + q`, above the word parameters'. -/
theorem word_ok_params {ps : List Ty} (wp : Nat → Bool) :
    (Tl.word (FR + slotsIn (paramLocs wp ps 0 0))).Ok (allW ps) (paramLocs wp ps 0 0) :=
  Tl.Ok.word_top _ (SlotsOk.paramLocs wp ps 0 0)

/-- Entering a call passes the arguments, which puts the word parameters' words in slots and copies
the other arguments into the callee's region at the watermark `n`, and puts the callee's base
pointer in `RX`. The callee, run in its frame from there in tail mode `tmc`, then has its
hypotheses. -/
theorem call_entry {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r) (args : Args Γ ps)
    {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f : Frame}
    {h : Heap} {w : World} {tm : Tl} (H : MHyp ω (.call name body args) tm L W ρ S n d bp env f h w)
    (tmc : Tl) (hCc : body.Conf tmc = true)
    (hOc : tmc.Ok (allW ps) (paramLocs body.wordParam ps 0 0)) (hvc : tmc.vars = [])
    (hdc : tmc.dsz r ≤ r.size) :
    ∃ f₁ f₂ h₁, Runs κ ω L (argsPass body.wordParam args ρ n 0) f h f₁ h₁ ∧
      Runs κ ω L (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n))) f₁ h₁ f₂ h₁ ∧ f₁ BP = f BP ∧
      f₂ BP = f BP ∧ (∀ x, FR ≤ x → f₂ x = f x) ∧
      (∀ a, a < bp + n → h₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      MHyp ω body tmc L (allW ps) (paramLocs body.wordParam ps 0 0)
        (ownS (bp + n) (paramOffs ps 0)) (ctxSize ps + r.size) (ctxSize ps) (bp + n)
        (args.denote env) (Frame.ofList ((callOps body.wordParam ps).map (Operand.eval f₂))) h₁ w := by
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hwp : ∀ i, body.wordParam (0 + i) = true →
      (ps.getD i .unit).wordTy = true ∧ REXT + 0 + i < FR := fun i hi => by
    simp only [Exp.wordParam, Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨hi.1.2, by simp only [REXT, FR] at hi ⊢; omega⟩
  obtain ⟨f₁, h₁, hr₁, hb₁, hk₁, hout₁, hrel, hws⟩ := argsPass_runs (κ := κ) (ω := ω) (n := n)
    (bp := bp) (env := env) (L := L) body.wordParam H.lay args 0 0 f h hwp (by omega) H.bpOk
    H.envRel H.sl.rel (Args.noHole args fun i H' h' => H.hole i H' h') (by omega)
    (Args.noExt H.vs args fun i h => by simpa [Exp.VSafe] using h)
  simp only [Nat.add_zero] at hr₁ hout₁
  let f₂ := f₁.set RX (UInt64.ofNat (bp + n))
  have hf₂ : f₂ BP = UInt64.ofNat bp := by
    simp only [f₂, Frame.set, show (BP = RX) = False by decide, ite_false]; rw [hb₁, H.bpOk]
  have hrun₂ : Runs κ ω L (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n))) f₁ h₁ f₂ h₁ :=
    Runs.congr (Runs.bin _ _ _ _ _ _) (by
      simp only [f₂, eval_slot, eval_imm, BinOp.eval, hb₁, H.bpOk, ofNat_add_ofNat]) rfl
  have hlay0 : Lay (bp + n) (ctxSize ps) ps (paramLocs body.wordParam ps 0 0)
      (ownS (bp + n) (paramOffs ps 0)) (allW ps) := by
    have := Lay.paramLocs body.wordParam (bp + n) ps 0 0 (allW ps); simp only [Nat.zero_add] at this
    exact this
  -- the callee's frame: its base pointer and its word parameters' words
  have hws₂ : args.Words body.wordParam env f₂ 0 := hws.congr fun j' _ => by
    simp only [f₂]; exact Frame.set_ne _ _ (by simp only [REXT, RX]; omega)
  have hfe := FEnvRel.params body.wordParam f₂ (Frame.ofList ((callOps body.wordParam ps).map
    (Operand.eval f₂))) args 0 0 (fun i hi => (hwp i hi).1) hws₂ fun i _ => callOps_frame _ _ _ i
  refine ⟨f₁, f₂, h₁, hr₁, hrun₂, hb₁, hf₂.trans H.bpOk.symm, fun x hx => ?_,
    fun a ha => hout₁ a (by omega) (by omega),
    ⟨hCc, hOc, H.restr, H.lawful, H.frozen, HoleAv.none_of (ownS_hole _ _),
      hlay0.mono (Nat.le_add_right _ r.size), by omega, hlay0.away (Nat.le_refl _), by omega,
      (by rw [callOps_BP]; simp [f₂]), hrel, H.safe, H.run, by omega, VS.of_none (ownS_ext _ _),
      ⟨SlotsOk.paramLocs _ _ _ _, hfe, fun i hi =>
        ⟨by have := paramLocs_slot _ _ _ _ i hi
            simp only [Exp.wordParam, Nat.zero_add, Bool.and_eq_true] at this; exact this.2,
          by rw [hvc]; exact List.not_mem_nil⟩⟩⟩⟩
  simp only [f₂]; rw [Frame.set_ne _ _ (by simp only [RX, FR] at hx ⊢; omega)]; exact hr₁.keep x hx

/-- A call passes the arguments and runs the callee in its region at the watermark `n` in tail mode
`tmc`, which leaves the result at the callee's destination `ctxSize ps` or as a word in a slot. It
then returns the words `ret` to the caller's slots `dst…`. Back in the caller's frame, `BP` and the
slots from `FR` on are as before the call except for the returned words, and nothing below the
watermark has changed. Then `c₂` runs. -/
theorem call_sim {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r) (args : Args Γ ps)
    (ih : MSoundAt κ ω body) {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat}
    {env : Env Γ} {f : Frame} {h : Heap} {w : World}
    {tm : Tl} (H : MHyp ω (.call name body args) tm L W ρ S n d bp env f h w)
    (tmc : Tl) (hCc : body.Conf tmc = true)
    (hOc : tmc.Ok (allW ps) (paramLocs body.wordParam ps 0 0)) (hvc : tmc.vars = [])
    (hhc : tmc.hb = .copy) (hdc : tmc.dsz r ≤ r.size) (fr : Nat) (ret : List Operand) (dst : Nat) {β : Type} {c₂ : Stmt}
    {k : List Kont} {c : Nat} {Q : β → Frame → Heap → Prop} {prot pf : Nat → Prop} {r₂ : Out β}
    (hp : ∀ a, prot a → a < bp + n)
    (hhalt : (body.exec ω κ .copy (args.denote env) w).world.halted = true →
      r₂.world = (body.exec ω κ .copy (args.denote env) w).world)
    (hbp : ∀ f₂ f₁ : Frame, f₂ BP = f BP → (f₂.writes dst (ret.map (Operand.eval f₁))) BP = f BP)
    (hpf : ∀ (f₂ f₁ : Frame) x, (∀ y, FR ≤ y → f₂ y = f y) → FR ≤ x → pf x →
      (f₂.writes dst (ret.map (Operand.eval f₁))) x = f x)
    (h₂ : ∀ (f₁ f₂ : Frame) (m₁ : Heap), f₂ BP = f BP → (∀ x, FR ≤ x → f₂ x = f x) →
      TQ tmc (bp + n) (ctxSize ps) (paramLocs body.wordParam ps 0 0)
        (ownS (bp + n) (paramOffs ps 0)) r (body.exec ω κ .copy (args.denote env) w).val f₁ m₁ →
      (∀ a, a < bp + n → m₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) →
      (body.exec ω κ .copy (args.denote env) w).world.halted = false →
      MSim κ ω L ⟨c₂, k, f₂.writes dst (ret.map (Operand.eval f₁)), m₁,
        (body.exec ω κ .copy (args.denote env) w).world,
        c + (Tick.call (ctxWords ps + width r)).cost κ + (body.exec ω κ .copy (args.denote env) w).steps⟩
        k Q prot r₂ pf) :
    MSim κ ω L ⟨.seq (.tick (.call (ctxWords ps + width r))) (.seq (argsPass body.wordParam args ρ n 0)
        (.seq (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n)))
        (.seq (.call name fr (lowerM body tmc (paramLocs body.wordParam ps 0 0)
          (ctxSize ps + r.size) (ctxSize ps)) ret (callOps body.wordParam ps) dst) c₂))),
        k, f, h, w, c⟩ k Q prot
      ⟨r₂.val, r₂.world, (Tick.call (ctxWords ps + width r)).cost κ +
        ((body.exec ω κ .copy (args.denote env) w).steps + r₂.steps)⟩ pf := by
  obtain ⟨f₁, f₂, h₁, hr₁, hrun₂, hb₁, hf₂f, hk₂, hout₁, Hc⟩ :=
    call_entry (κ := κ) name body args H tmc hCc hOc hvc hdc
  have hstep := MSim.call_step (name := name) (fr := fr) (k := k) (Q := Q) (pf := pf)
    (prot := prot) (prot₂ := prot) (r₂ := r₂) H.run
    (hhc ▸ ih.app Hc (.ret ret dst f₂ :: .seq c₂ :: k) (c + (Tick.call (ctxWords ps + width r)).cost κ))
    hhalt (fun a ha => by
      refine ⟨?_, ha⟩
      have := hp a ha
      exact ⟨by omega, fun e => by unfold InR at e; omega, fun e => by
        have := InW.ownS_ge e; omega⟩)
    (fun f₁ => (hbp f₂ f₁ hf₂f).trans hf₂f.symm) (fun f₁ x hx hpx => (hpf f₂ f₁ x hk₂ hx hpx).trans
      (hk₂ x hx).symm)
    (fun f₁ m₁ hv hm hh => h₂ f₁ f₂ m₁ hf₂f hk₂ hv (fun a ha => by
        rw [hm a ⟨by omega, fun e => by unfold InR at e; omega, fun e => by
          have := InW.ownS_ge e; omega⟩]
        exact hout₁ a ha) hh)
  exact MSim.tick H.run (MSim.runs H.run hr₁ hb₁ (fun x hx => hout₁ x (hp x hx))
    (MSim.runs H.run hrun₂ (by rw [hf₂f, hb₁]) (fun _ _ => rfl) hstep))

/-- Whether a term's tails compute into slots does not depend on the slots. -/
theorem _root_.Millipede.Exp.conf_word {Γ : List Ty} {t : Ty} (e : Exp Γ t) (k k' : Nat) :
    e.Conf (.word k) = e.Conf (.word k') := by
  induction e <;> simp_all [Exp.Conf, Tl.up]

/-- The result of a call as the next code sees it, when the program has not halted. The frame
keeps `BP` and the slots from `FR` on except the `cnt` slots from `dst`, the memory below the
watermark is unchanged, and `R` holds. The continuation `c₂` then runs. -/
abbrev CallCont (κ : CostModel) (ω : Oracle) (L : Nat) {Γ ps : List Ty} {r : Ty} (body : Exp ps r)
    (args : Args Γ ps) (env : Env Γ) (w : World) (bp n c : Nat) (f : Frame) (h : Heap)
    (k : List Kont) {β : Type} (Q : β → Frame → Heap → Prop) (prot pf : Nat → Prop) (r₂ : Out β)
    (c₂ : Stmt) (dst cnt : Nat) (R : Frame → Heap → Prop) : Prop :=
  ∀ (f₂ : Frame) (m₁ : Heap), f₂ BP = f BP → (∀ x, FR ≤ x → (x < dst ∨ dst + cnt ≤ x) →
    f₂ x = f x) → R f₂ m₁ →
    (∀ a, a < bp + n → m₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) →
    (body.exec ω κ .copy (args.denote env) w).world.halted = false →
    MSim κ ω L ⟨c₂, k, f₂, m₁, (body.exec ω κ .copy (args.denote env) w).world,
      c + (Tick.call (ctxWords ps + width r)).cost κ + (body.exec ω κ .copy (args.denote env) w).steps⟩
      k Q prot r₂ pf

theorem Frame.writes_out : ∀ (f : Frame) (d : Nat) (vs : List UInt64) (x : Nat),
    (x < d ∨ d + vs.length ≤ x) → f.writes d vs x = f x
  | _, _, [], _, _ => rfl
  | f, d, v :: vs, x, h => by
    simp only [Frame.writes, List.length_cons] at h ⊢
    rw [Frame.writes_out _ _ _ _ (by omega), Frame.set_ne _ _ (by omega)]

theorem Frame.writes_at : ∀ (f : Frame) (d : Nat) (vs : List UInt64) (j : Nat),
    j < vs.length → f.writes d vs (d + j) = vs.getD j 0
  | f, d, v :: vs, 0, _ => by
    simp only [Frame.writes, Nat.add_zero]
    rw [Frame.writes_out _ _ _ _ (by omega)]; simp
  | f, d, v :: vs, j + 1, h => by
    simp only [Frame.writes]
    rw [show d + (j + 1) = d + 1 + j by omega, Frame.writes_at _ _ _ j (by simpa using h)]; simp

theorem retSlots_eval (f : Frame) (k n : Nat) :
    ((retSlots k n).map (Operand.eval f)).length = n ∧
      ∀ j, j < n → ((retSlots k n).map (Operand.eval f)).getD j 0 = f (k + j) := by
  simp [retSlots, List.getD_eq_getElem?_getD]
  intro j hj; simp [hj]

/-- A result returned as words, from the callee's slots from `FR + q` when the callee is lowered in
`Tl.word`, into the slots from `dst`, which are above `BP` and include no protected slot. -/
theorem call_ret_word {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r)
    (args : Args Γ ps) (ih : MSoundAt κ ω body) {W : List Bool} {ρ : List Loc} {S : List SI}
    {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World} {tm : Tl}
    (H : MHyp ω (.call name body args) tm L W ρ S n d bp env f h w)
    (hwc : body.Conf (.word (FR + slotsIn (paramLocs body.wordParam ps 0 0))) = true) (dst : Nat)
    (hdst : BP < dst) {β : Type} {c₂ : Stmt} {k : List Kont} {c : Nat}
    {Q : β → Frame → Heap → Prop} {prot pf : Nat → Prop} {r₂ : Out β} (hp : ∀ a, prot a → a < bp + n)
    (hhalt : (body.exec ω κ .copy (args.denote env) w).world.halted = true →
      r₂.world = (body.exec ω κ .copy (args.denote env) w).world)
    (hpf : ∀ x, FR ≤ x → pf x → x < dst ∨ dst + r.slotN ≤ x)
    (h₂ : CallCont κ ω L body args env w bp n c f h k Q prot pf r₂ c₂ dst r.slotN fun f₂ _ =>
      WordsRel r (body.exec ω κ .copy (args.denote env) w).val f₂ dst) :
    MSim κ ω L ⟨.seq (.tick (.call (ctxWords ps + width r))) (.seq (argsPass body.wordParam args ρ n 0)
        (.seq (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n)))
        (.seq (.call name (FR + slotsIn (paramLocs body.wordParam ps 0 0) + max r.slotN body.slotNeed)
          (lowerM body (.word (FR + slotsIn (paramLocs body.wordParam ps 0 0)))
            (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps))
          (retSlots (FR + slotsIn (paramLocs body.wordParam ps 0 0)) r.slotN)
          (callOps body.wordParam ps) dst) c₂))), k, f, h, w, c⟩ k Q prot
      ⟨r₂.val, r₂.world, (Tick.call (ctxWords ps + width r)).cost κ +
        ((body.exec ω κ .copy (args.denote env) w).steps + r₂.steps)⟩ pf := by
  have hout : ∀ (f₂ f₁ : Frame) x, (x < dst ∨ dst + r.slotN ≤ x) →
      (f₂.writes dst ((retSlots (FR + slotsIn (paramLocs body.wordParam ps 0 0)) r.slotN).map
        (Operand.eval f₁))) x = f₂ x := fun f₂ f₁ x hx =>
    Frame.writes_out _ _ _ _ (by rw [(retSlots_eval f₁ _ _).1]; exact hx)
  exact call_sim (κ := κ) name body args ih H (.word _) hwc (word_ok_params _) rfl rfl
    (by simp [Tl.dsz]) _ _ dst hp hhalt (fun f₂ f₁ hf => (hout f₂ f₁ BP (Or.inl hdst)).trans hf)
    (fun f₂ f₁ x hk hx hpx => (hout f₂ f₁ x (hpf x hx hpx)).trans (hk x hx))
    fun f₁ f₂ m₁ hf₂ hk₂ hv hm hh => h₂ _ m₁ ((hout f₂ f₁ BP (Or.inl hdst)).trans hf₂)
      (fun x hx hxd => (hout f₂ f₁ x hxd).trans (hk₂ x hx)) (by
        obtain ⟨B, hB, hW⟩ := hv
        refine ⟨B, hB, wordsAt_iff.2 fun j hj => ?_⟩
        rw [Frame.writes_at _ _ _ _ (by rw [(retSlots_eval f₁ _ _).1]; exact hj),
          (retSlots_eval f₁ _ _).2 j hj]
        exact wordsAt_iff.1 hW j hj) hm hh

/-- A result left at the callee's destination, when the callee is lowered in mode `none`, is seen
by the next code as bytes at `bp + n + ctxSize ps`. -/
theorem call_ret_mem {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r)
    (args : Args Γ ps) (ih : MSoundAt κ ω body) {W : List Bool} {ρ : List Loc} {S : List SI}
    {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World} {tm : Tl}
    (H : MHyp ω (.call name body args) tm L W ρ S n d bp env f h w) {β : Type} {c₂ : Stmt}
    {k : List Kont} {c : Nat} {Q : β → Frame → Heap → Prop} {prot pf : Nat → Prop} {r₂ : Out β}
    (hp : ∀ a, prot a → a < bp + n)
    (hhalt : (body.exec ω κ .copy (args.denote env) w).world.halted = true →
      r₂.world = (body.exec ω κ .copy (args.denote env) w).world)
    (h₂ : CallCont κ ω L body args env w bp n c f h k Q prot pf r₂ c₂ BP 0 fun _ m₁ =>
      Data.reprBytes (body.exec ω κ .copy (args.denote env) w).val (rd m₁ (bp + (n + ctxSize ps)) r.size)) :
    MSim κ ω L ⟨.seq (.tick (.call (ctxWords ps + width r))) (.seq (argsPass body.wordParam args ρ n 0)
        (.seq (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n)))
        (.seq (.call name (FR + slotsIn (paramLocs body.wordParam ps 0 0) + body.slotNeed)
          (lowerM body .none (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps))
          [] (callOps body.wordParam ps) 0) c₂))), k, f, h, w, c⟩ k Q prot
      ⟨r₂.val, r₂.world, (Tick.call (ctxWords ps + width r)).cost κ +
        ((body.exec ω κ .copy (args.denote env) w).steps + r₂.steps)⟩ pf :=
  call_sim (κ := κ) name body args ih H .none (by simp) trivial rfl rfl (by simp [Tl.dsz]) _ [] 0 hp hhalt
    (fun _ _ h => by simpa [Frame.writes] using h) (fun _ _ x hk hx _ => by simpa [Frame.writes] using hk x hx)
    fun _ f₂ m₁ hf₂ hk₂ hv hm hh => h₂ f₂ m₁ hf₂ (fun x hx _ => hk₂ x hx)
      (by simpa [TQ, Nat.add_assoc] using hv) hm hh

/-- The case of a call. The arguments are copied into the callee's region at the watermark and the
callee runs there. A result that the callee computes into its slots is returned as words, into the
destination slots or through the scratch slots from `REXT`, and any other result is copied from
the callee's destination. -/
theorem msound_call {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r) (args : Args Γ ps)
    (ih : MSoundAt κ ω body) : MSoundAt κ ω (.call name body args) := by
  refine .leafW (fun L W ρ S n d bp env k f h w c H => ?_) fun K L W ρ S n d bp env k f h w c H => ?_
  all_goals
    have hb := H.size; have hbL := H.room
    simp only [Exp.memNeed] at hb hbL
    simp only [lowerM]
  · have hdn := H.dn0
    split
    · -- the words returned to the scratch slots from `REXT`, then stored
      rename_i hwc
      have hts := body.slotTy_of_word hwc
      have hcap := Ty.slotN_le hts
      refine (call_ret_word (κ := κ) name body args ih H hwc REXT (by decide)
        (c₂ := stSlots (scalarWidth r.size) (.slot BP) d REXT r.slotN)
        (Q := TQ .none bp d ρ S r) (r₂ := (⟨(body.exec ω κ .copy (args.denote env) w).val,
          (body.exec ω κ .copy (args.denote env) w).world, 0⟩ : Out r.carrier)) (fun a ha => ha.1) (fun _ => rfl)
        (fun x hx _ => by simp only [REXT, FR, SLOT_CAP] at hx hcap ⊢; omega)
        fun f₂ m₁ hf₂ _ hv _ hh => ?_).of_eq (by simp [Exp.exec]) (by simp [Exp.exec])
          (by simp [Exp.exec, Tick.cost])
      have hf₃ : f₂ BP = UInt64.ofNat bp := hf₂.trans H.bpOk
      obtain ⟨B, hBl, hBr, hrun⟩ := stSlots_words (κ := κ) (ω := ω) (L := L) (o := d) hts hf₃ hv
        (by omega) (by omega)
      refine MSim.done (h' := wr m₁ (bp + d) B) hh hrun rfl rfl rfl ?_ fun x hx => ?_
      · show Data.reprBytes _ (rd _ _ r.size); rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr
      · obtain ⟨h1, h2, _⟩ := hx
        exact wr_out (by omega) (by omega) (by unfold InR at h2; omega)
    · -- the result copied from the callee's destination
      refine (call_ret_mem (κ := κ) name body args ih H (c₂ := copyM (n + ctxSize ps) d r.size)
        (Q := TQ .none bp d ρ S r) (r₂ := (⟨(body.exec ω κ .copy (args.denote env) w).val,
          (body.exec ω κ .copy (args.denote env) w).world, 0⟩ : Out r.carrier)) (fun a ha => ha.1) (fun _ => rfl)
        fun f₂ m₁ hf₂ _ hv _ hh => ?_).of_eq (by simp [Exp.exec]) (by simp [Exp.exec])
          (by simp [Exp.exec, Tick.cost])
      have hf₂' : f₂ BP = UInt64.ofNat bp := hf₂.trans H.bpOk
      obtain ⟨f₃, hf₃, hr₃⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot BP)
        (by decide) (by decide) r.size (n + ctxSize ps) d bp bp f₂ m₁ hf₂' hf₂' (by omega)
        (by omega) (Or.inr (by omega)) (by omega) (by omega)
      refine MSim.done hh hr₃ rfl rfl (hf₃ BP (by decide)) ?_ ?_
      · show Data.reprBytes _ (rd _ _ r.size)
        have := rd_wr m₁ (bp + d) (rd m₁ (bp + (n + ctxSize ps)) r.size) (by simp; omega)
        rw [rd_length] at this; rw [this]; exact hv
      · intro x hx; obtain ⟨h1, h2, h3⟩ := hx
        rw [wr_out (by simp; omega) (by omega) (by simp; unfold InR at h2; omega)]
  · have hK := H.tmOk.1
    have hts : r.slotTy = true := by simpa [Exp.Conf] using H.conf
    split
    · -- the words returned straight into the destination slots
      rename_i hwc
      exact (call_ret_word (κ := κ) name body args ih H hwc K
        (by simp only [FR, BP] at hK ⊢; omega) (c₂ := .skip) (Q := TQ (.word K) bp d ρ S r)
        (r₂ := (⟨(body.exec ω κ .copy (args.denote env) w).val,
          (body.exec ω κ .copy (args.denote env) w).world, 0⟩ : Out r.carrier)) (fun a ha => ha.1) (fun _ => rfl)
        (fun x _ hp => Or.inl (SProt.lt_word H.tmOk hp))
        fun f₂ m₁ _ _ hv _ hh => MSim.reaches_done hh (Runs.skip _ _).run rfl rfl rfl
          hv (fun _ _ => rfl) fun _ _ _ => rfl).of_eq
        (by simp [Exp.exec]) (by simp [Exp.exec]) (by simp [Exp.exec, Tick.cost])
    · -- the result loaded from the callee's destination into the slots
      refine (call_ret_mem (κ := κ) name body args ih H
        (c₂ := ldSlots (scalarWidth r.size) K (.slot BP) (n + ctxSize ps) r.slotN)
        (Q := TQ (.word K) bp d ρ S r) (r₂ := (⟨(body.exec ω κ .copy (args.denote env) w).val,
          (body.exec ω κ .copy (args.denote env) w).world, 0⟩ : Out r.carrier)) (fun a ha => ha.1) (fun _ => rfl)
        fun f₂ m₁ hf₂ hk₂ hv _ hh => ?_).of_eq (by simp [Exp.exec]) (by simp [Exp.exec])
          (by simp [Exp.exec, Tick.cost])
      obtain ⟨f', hld, hfb, hlo, hwv⟩ := load_words (κ := κ) (ω := ω) (L := L) (K := K)
        (o := n + ctxSize ps) hts (hf₂.trans H.bpOk) (by decide) hK (by simpa [Nat.add_assoc] using hv)
        (by omega) (by omega)
      exact MSim.reaches_done hh hld rfl rfl hfb hwv (fun _ _ => rfl)
        fun x _ hp => hlo x (SProt.lt_word H.tmOk hp)

/-! ## Constructors -/

/-- `x` lies in one of the placements, whose offsets are relative to `A`. -/
def InPl (A : Nat) (L : List (Nat × Nat)) (x : Nat) : Prop := ∃ q ∈ L, A + q.1 ≤ x ∧ x < A + q.1 + q.2

/-- Copying an atom to several disjoint offsets inside the destination. -/
theorem copies_runs {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n d Sz bp : Nat} {env : Env Γ} (hl : Lay bp n Γ ρ S W)
    (hd : Away bp d Sz Γ ρ S) (hdS : d + Sz ≤ n) (hbn : bp + n ≤ UInt64.size) (hnL : bp + n ≤ L)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none) :
    ∀ (os : List Nat) (f : Frame) (h : Heap), f BP = UInt64.ofNat bp → MEnvRel h bp env ρ S →
      FEnvRel f env ρ → (∀ o ∈ os, o + t.size ≤ Sz) →
      (os.map fun o => (o, t.size)).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) →
      ∃ f' h', Runs κ ω L (os.foldr (fun o c => .seq (atomTo a ρ (d + o)) c) .skip) f h f' h' ∧
        f' BP = f BP ∧ MEnvRel h' bp env ρ S ∧
        (∀ x, x < UInt64.size → ¬ InPl (bp + d) (os.map fun o => (o, t.size)) x →
          h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
        ∀ o ∈ os, Data.reprBytes (a.denote env) (rd h' (bp + d + o) t.size)
  | [], f, h, _, henv, _, _, _ => ⟨f, h, Runs.skip _ _, rfl, henv, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | o :: os, f, h, hf, henv, hfe, hin, hpw => by
    have ho := hin o (by simp)
    obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := d + o) hl
      (hd.sub (by omega) (by omega)) (by omega) hbn hf henv hfe hnh (by omega) hnL hne
    have henv₁ := henv.wr_away (d := d + o) hl hbn B (by rw [hBl]; exact hd.sub (by omega) (by omega))
      (by rw [hBl]; omega)
    rw [List.map_cons, List.pairwise_cons] at hpw
    obtain ⟨f', h', hr, hb', henv', hout, hrep⟩ := copies_runs a hl hd hdS hbn hnL hnh hne os f₁ _
      ((hf₁ BP (by decide) (by decide)).trans hf) henv₁ (hfe.keep hr₁.keep)
      (fun o' h' => hin o' (by simp [h'])) hpw.2
    refine ⟨f', h', Runs.seq hr₁ hr, hb'.trans (hf₁ BP (by decide) (by decide)), henv',
      fun x hx hn => ?_, ?_⟩
    · rw [hout x hx fun ⟨q, hq, h1, h2⟩ => hn ⟨q, by simp [hq], h1, h2⟩]
      exact wr_out (by omega) hx fun ⟨h1, h2⟩ => hn ⟨(o, t.size), by simp, by omega, by omega⟩
    · intro o' ho'
      rcases List.mem_cons.mp ho' with rfl | ho'
      · have e1 : rd h' (bp + d + o') t.size = rd (wr h (bp + (d + o')) B) (bp + d + o') t.size :=
          rd_congr fun i hi => hout _ (by omega) (by
            rintro ⟨q, hq, h1, h2⟩
            obtain ⟨o'', ho'', rfl⟩ := List.mem_map.mp hq
            have := hpw.1 _ (List.mem_map_of_mem ho'')
            simp only [Disj] at this h1 h2; omega)
        have e2 : rd (wr h (bp + (d + o')) B) (bp + d + o') t.size = B := by
          rw [← hBl, show bp + d + o' = bp + (d + o') by omega, rd_wr _ _ _ (by omega)]
        rw [e1, e2]; exact hBr
      · exact hrep o' ho'

theorem argsTo_nil {Γ : List Ty} (ρ : List Loc) (d : Nat) :
    ∀ {ps : List Ty} (args : Args Γ ps), argsTo args [] ρ d = .skip
  | _, .nil => rfl
  | _, .cons _ as => argsTo_nil ρ d as

/-- The arguments that a plan copies, those with offsets, read no variable with an extent. -/
def _root_.Millipede.Args.NoExtFor {Γ : List Ty} (S : List SI) :
    {ps : List Ty} → Args Γ ps → List (List Nat) → Prop
  | _, .cons a as, _ :: oss =>
    (∀ m, a = .var m → (S.getD m.idx default).ext = none) ∧ Args.NoExtFor S as oss
  | _, _, _ => True

theorem _root_.Millipede.Args.NoExt.noExtFor {Γ : List Ty} {S : List SI} :
    {ps : List Ty} → {as : Args Γ ps} → as.NoExt S → ∀ oss, as.NoExtFor S oss
  | _, .nil, _, oss => by cases oss <;> trivial
  | _, .cons _ as, h, [] => trivial
  | _, .cons _ as, h, _ :: oss => ⟨h.1, Args.NoExt.noExtFor (as := as) h.2 oss⟩

/-- Copying constructor arguments to their placements. -/
theorem argsTo_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    {n d Sz bp : Nat} {env : Env Γ}
    (hl : Lay bp n Γ ρ S W) (hd : Away bp d Sz Γ ρ S) (hdS : d + Sz ≤ n)
    (hbn : bp + n ≤ UInt64.size) (hnL : bp + n ≤ L) :
    ∀ {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat)) (f : Frame) (h : Heap),
      f BP = UInt64.ofNat bp → MEnvRel h bp env ρ S → FEnvRel f env ρ → args.NoHole S →
      args.NoExtFor S oss →
      (∀ q ∈ placements ps oss, q.1 + q.2 ≤ Sz) →
      (placements ps oss).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) →
      ∃ f' h', Runs κ ω L (argsTo args oss ρ d) f h f' h' ∧ f' BP = f BP ∧
        (∀ x, x < UInt64.size → ¬ InPl (bp + d) (placements ps oss) x →
          h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
        ArgsAt oss (args.denote env) (rd h' (bp + d) Sz)
  | _, .nil, oss, f, h, _, _, _, _, _, _, _ =>
    ⟨f, h, by cases oss <;> exact Runs.skip _ _, rfl, fun _ _ _ => rfl, by cases oss <;> trivial⟩
  | _, .cons a as, [], f, h, _, _, _, _, _, _, _ =>
    ⟨f, h, by rw [argsTo_nil]; exact Runs.skip _ _, rfl, fun _ _ _ => rfl, trivial⟩
  | _, .cons (t := t) (ts := ts) a as, os :: oss, f, h, hf, henv, hfe, hnh, hne, hin, hpw => by
    simp only [placements] at hin hpw
    rw [List.pairwise_append] at hpw
    obtain ⟨f₁, h₁, hr₁, hb₁, henv₁, hout₁, hrep₁⟩ := copies_runs (κ := κ) (ω := ω) a hl hd hdS hbn
      hnL hnh.1 hne.1 os f h hf henv hfe
      (fun o ho => hin (o, t.size) (List.mem_append_left _ (List.mem_map_of_mem ho))) hpw.1
    obtain ⟨f', h', hr, hb', hout, hargs⟩ := argsTo_runs hl hd hdS hbn hnL as oss f₁ h₁
      ((hb₁).trans hf) henv₁ (hfe.keep hr₁.keep) hnh.2 hne.2
      (fun q hq => hin q (List.mem_append_right _ hq)) hpw.2.1
    refine ⟨f', h', Runs.seq hr₁ hr, hb'.trans hb₁, fun x hx hn => ?_, ⟨fun o ho => ?_, hargs⟩⟩
    · have m2 : ∀ q, q ∈ placements ts oss → q ∈ placements (t :: ts) (os :: oss) := fun q hq => by
        simp only [placements]; exact List.mem_append_right _ hq
      have m1 : ∀ q, q ∈ os.map (fun o => (o, t.size)) → q ∈ placements (t :: ts) (os :: oss) :=
        fun q hq => by simp only [placements]; exact List.mem_append_left _ hq
      rw [hout x hx fun ⟨q, hq, h1, h2⟩ => hn ⟨q, m2 q hq, h1, h2⟩]
      exact hout₁ x hx fun ⟨q, hq, h1, h2⟩ => hn ⟨q, m1 q hq, h1, h2⟩
    · have hoS := hin (o, t.size) (List.mem_append_left _ (List.mem_map_of_mem ho))
      rw [← rd_slice _ _ _ _ _ hoS]
      have e : rd h' (bp + d + o) t.size = rd h₁ (bp + d + o) t.size := rd_congr fun i hi =>
        hout _ (by omega) fun ⟨q, hq, h1, h2⟩ => by
          have := hpw.2.2 (o, t.size) (List.mem_map_of_mem ho) q hq
          simp only [Disj] at this; omega
      rw [e]; exact hrep₁ o ho

/-! ## Patching bytes -/

/-- Splice segments into a byte list, in order. -/
def patchAll (bs : List UInt8) : List (Nat × List UInt8) → List UInt8
  | [] => bs
  | q :: l => patchAll (splice bs q.1 q.2) l

theorem patchAll_length : ∀ (bs : List UInt8) (l : List (Nat × List UInt8)),
    (∀ q ∈ l, q.1 + q.2.length ≤ bs.length) → (patchAll bs l).length = bs.length
  | _, [], _ => rfl
  | bs, q :: l, h => by
    have hq := h q (by simp)
    have hs := splice_length bs q.1 q.2 hq
    rw [patchAll, patchAll_length _ l fun q' hq' => by rw [hs]; exact h q' (by simp [hq']), hs]

theorem patchAll_other : ∀ (bs : List UInt8) (l : List (Nat × List UInt8)) (o m : Nat),
    (∀ q ∈ l, q.1 + q.2.length ≤ bs.length) → (∀ q ∈ l, Disj o m q.1 q.2.length) →
    slice (patchAll bs l) o m = slice bs o m
  | _, [], _, _, _, _ => rfl
  | bs, q :: l, o, m, h, hd => by
    have hq := h q (by simp)
    have hs := splice_length bs q.1 q.2 hq
    rw [patchAll, patchAll_other _ l o m (fun q' hq' => by rw [hs]; exact h q' (by simp [hq']))
      fun q' hq' => hd q' (by simp [hq'])]
    rcases hd q (by simp) with e | e
    · exact slice_splice_of_le _ _ _ _ _ e (by omega)
    · exact slice_splice_of_ge _ _ _ _ _ e (by omega)

theorem patchAll_slice : ∀ (bs : List UInt8) (l : List (Nat × List UInt8)),
    (∀ q ∈ l, q.1 + q.2.length ≤ bs.length) →
    (l.map fun q => (q.1, q.2.length)).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) →
    ∀ q ∈ l, slice (patchAll bs l) q.1 q.2.length = q.2
  | _, [], _, _, _, h => by cases h
  | bs, q :: l, h, hp, q', hq' => by
    have hq := h q (by simp)
    have hs := splice_length bs q.1 q.2 hq
    rw [List.map_cons, List.pairwise_cons] at hp
    rcases List.mem_cons.mp hq' with rfl | hq'
    · rw [patchAll, patchAll_other _ l _ _ (fun q'' h'' => by rw [hs]; exact h q'' (by simp [h'']))
        fun q'' h'' => hp.1 _ (List.mem_map_of_mem h''), slice_splice_same _ _ _ hq]
    · exact patchAll_slice _ l (fun q'' h'' => by rw [hs]; exact h q'' (by simp [h''])) hp.2 q' hq'

/-! ## Constructors in a tail mode -/

theorem _root_.Millipede.Mem.ofIdx : ∀ (Γ : List Ty) (i : Nat), i < Γ.length →
    ∃ (T : Ty) (m : Mem T Γ), m.idx = i
  | [], _, h => by simp at h
  | s :: _, 0, _ => ⟨s, .here, rfl⟩
  | _ :: Γ, i + 1, h => by
    obtain ⟨T, m, hm⟩ := Mem.ofIdx Γ i (by simp at h; omega)
    exact ⟨T, .there m, by simp [Mem.idx, hm]⟩

theorem placements_cs : ∀ {ps : List Ty} (cs : List (Nat × Nat × Nat)),
    tySizes ps = cs.map (·.2.2) →
    placements ps (cs.map fun c => [c.2.1]) = cs.map fun c => (c.2.1, c.2.2)
  | [], [], _ => rfl
  | t :: ts, c :: cs, h => by
    simp only [tySizes, List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, placements, List.map_nil, List.singleton_append, h.1]
    rw [placements_cs cs (by simpa [tySizes] using h.2)]
  | [], _ :: _, h => by simp [tySizes] at h
  | _ :: _, [], h => by simp [tySizes] at h

/-- The in-place arguments of a tail constructor are represented by bytes that agree with each
variable's location, which is its storage or the word in its frame slot. -/
theorem argsAt_vars {Γ : List Ty} {env : Env Γ} {h : Heap} {f : Frame} {bp : Nat} {ρ : List Loc}
    {S : List SI} (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ) :
    ∀ {ps : List Ty} (rest : Args Γ ps) (cs : List (Nat × Nat × Nat)),
      rest.areVars (cs.map (·.1)) = true → tySizes ps = cs.map (·.2.2) →
      (∀ c ∈ cs, (S.getD c.1 default).hole = none) →
      ∃ Ls : List ((Nat × Nat × Nat) × List UInt8), Ls.map Prod.fst = cs ∧
        (∀ q ∈ Ls, q.2.length = q.1.2.2 ∧ ∀ bs, slice bs q.1.2.1 q.1.2.2 = q.2 →
          CompAt bs f h (ρ.getD q.1.1 default) (S.getD q.1.1 default) q.1.2.1 q.1.2.2) ∧
        ∀ bs, (∀ q ∈ Ls, slice bs q.1.2.1 q.1.2.2 = q.2) →
          ArgsAt (cs.map fun c => [c.2.1]) (rest.denote env) bs
  | [], .nil, [], _, _, _ => ⟨[], rfl, fun _ hq => absurd hq List.not_mem_nil, fun _ _ => trivial⟩
  | t :: ts, .cons (.var m) rest, c :: cs, hv, hs, hnh => by
    simp only [List.map_cons, Args.areVars, Bool.and_eq_true, beq_iff_eq] at hv
    simp only [tySizes, List.map_cons, List.cons.injEq] at hs
    obtain ⟨Ls, hLs, hq, ha⟩ := argsAt_vars henv hfe rest cs hv.2 (by simpa [tySizes] using hs.2)
      (fun c' h' => hnh c' (by simp [h']))
    have hcs : c.2.2 = t.size := hs.1.symm
    -- the component's bytes: its memory representation, or the word in its slot
    obtain ⟨B, hB, hc⟩ : ∃ B : List UInt8, Data.reprBytes (env.get m) B ∧ ∀ bs,
        slice bs c.2.1 c.2.2 = B → CompAt bs f h (ρ.getD c.1 default) (S.getD c.1 default) c.2.1 c.2.2 := by
      rw [← hv.1]
      cases hk : (ρ.getD m.idx default).slot? with
      | some k =>
        obtain ⟨_, hn, B, hB, hw⟩ := hfe.get m hk
        exact ⟨B, hB, fun bs e => by simp only [CompAt, hk]; rw [e, hn]; exact hw⟩
      | none =>
        obtain ⟨B, hB, hm, _⟩ := (henv.get m (by unfold Loc.isSlot; rw [hk]; rfl)).1
        have hnoh : (S.getD m.idx default).hole = none := by rw [hv.1]; exact hnh c (by simp)
        have hBl := Data.reprBytes_length hB
        refine ⟨B, hB, fun bs e => (CompAt.mem hk).2 ?_⟩
        have hlim := (S.getD m.idx default).lim_le t.size
        rw [hcs] at e ⊢
        rw [show slice bs c.2.1 ((S.getD m.idx default).lim t.size) =
          slice (slice bs c.2.1 t.size) 0 ((S.getD m.idx default).lim t.size) by
            rw [slice_slice _ _ _ _ _ (by omega), Nat.add_zero], e]
        refine (rdS_of_getD (by rw [slice_length_of_le (by rw [hBl]; simpa using hlim)])
          fun i hi => ?_).symm
        rw [hm i (by simpa [SI.sz] using hi) (by unfold SI.inHole; rw [hnoh]; exact id)]
        simp only [slice, List.drop_zero, List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [ite_eq_left_iff.mpr (fun h => absurd (by simpa using hi) h)]
    refine ⟨(c, B) :: Ls, by simp [hLs], fun q hq' => ?_, fun bs hbs => ⟨fun o ho => ?_, ha bs fun q hq' =>
      hbs q (by simp [hq'])⟩⟩
    · rcases List.mem_cons.mp hq' with rfl | hq'
      · exact ⟨by rw [Data.reprBytes_length hB, hcs], hc⟩
      · exact hq q hq'
    · simp only [List.mem_singleton] at ho; subst ho
      have e := hbs (c, B) (by simp)
      simp only at e
      rw [← hs.1] at e
      rw [e]; exact hB
  | _, .cons (.lit _) _, _ :: _, hv, _, _ => by simp [Args.areVars] at hv
  | _, .nil, _ :: _, hv, _, _ => by simp [Args.areVars] at hv
  | _, .cons _ _, [], hv, _, _ => by simp [Args.areVars] at hv

/-- What `bigVar?` found: a variable in memory whose placement splits the others' into `A` and
`B`, and which, written at its placement, completes the arguments that `argsTo` writes when its
offsets are left out. -/
theorem bigVar?_spec {Γ : List Ty} {ρ : List Loc} :
    ∀ {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat)) {j o o1 sz : Nat},
      bigVar? args oss ρ = some (j, o, o1, sz) →
      ∃ (e : Ty) (m : Mem e Γ), e.size = sz ∧ ρ.getD m.idx default = .own o ∧ sz % 8 = 0 ∧
        sz < UInt64.size ∧
        (∃ A B, placements ps oss = A ++ (o1, sz) :: B ∧ placements ps (oss.set j []) = A ++ B) ∧
        (∀ S, args.NoHole S → (S.getD m.idx default).hole = none) ∧
        (∀ S, args.NoExtFor S oss →
          (S.getD m.idx default).ext = none ∧ args.NoExtFor S (oss.set j [])) ∧
        ∀ (env : Env Γ) (bs : List UInt8), ArgsAt (oss.set j []) (args.denote env) bs →
          Data.reprBytes (env.get m) (slice bs o1 sz) → ArgsAt oss (args.denote env) bs
  | _, .nil, _, _, _, _, _, h => by simp [bigVar?] at h
  | _, .cons _ _, [], _, _, _, _, h => by simp [bigVar?] at h
  | _, .cons (t := e) (ts := ts) a as, os :: oss, j, o, o1, sz, h => by
    simp only [bigVar?] at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h; subst h
      split at hr
      · rename_i m o1' 
        split at hr
        · rename_i o' hρ
          split at hr
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
            refine ⟨e, m, rfl, hρ, hc.1, hc.2.2, ⟨[], placements ts oss, by simp [placements], by
              simp [placements]⟩, fun S hn => hn.1 m rfl, fun S hn => ⟨hn.1 m rfl, hn⟩,
              fun env bs ha hv => ⟨fun o ho => ?_, ha.2⟩⟩
            simp only [List.mem_singleton] at ho; subst ho; exact hv
          · simp at hr
        · simp at hr
      · simp at hr
    · obtain ⟨⟨j', o', o1', sz'⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨e', m, hsz, hρ, h8, hU, ⟨A, B, h1, h2⟩, hnh, hne, hargs⟩ := bigVar?_spec as oss hr
      refine ⟨e', m, hsz, hρ, h8, hU, ⟨os.map (fun o => (o, e.size)) ++ A, B, ?_, ?_⟩,
        fun S hn => hnh S hn.2, fun S hn => ⟨(hne S hn.2).1, hn.1, (hne S hn.2).2⟩,
        fun env bs ha hv => ⟨ha.1, hargs env bs ha.2 hv⟩⟩
      · simp [placements, h1]
      · simp [placements, h2]

/-- The case of a constructor, which copies the arguments to their placements and then writes the
tag byte. In a tail mode it writes only the first argument, because the others are the in-place
references. -/
theorem msound_mk {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) :
    MSoundAt κ ω (.mk c args) := by
  refine .intro fun tm L W ρ S n d bp env k f h w cl H => ?_
  have hC := H.conf; have hdn := H.dn; have hd := H.away; have hb := H.nU; have hbL := H.nL
  obtain ⟨hpl, hpw, htag1, hbuild⟩ := H.lawful
  have hnh := Args.noHole args fun i H' h' => H.hole i H' h'
  cases tm with
  | none =>
    simp only [Tl.dsz] at hdn hd ⊢
    cases hfc : fillCode? c args d (Tl.none.hb.mkW ps t) with
    | some code =>
      -- a fill: the store loop writes the element repeated
      obtain ⟨k, w, P, T, rfl, hkw, htg, hsz, hk8, hargs⟩ := fillCode?_spec hfc
      have hcode : lowerM (.mk c args) .none ρ n d = .seq (.tick (.ctor (Tl.none.hb.mkW ps t - k * w)))
          (.seq (fillLoop d k P w) (writeB (.slot BP) (d + 8 * k) T)) := by
        simp only [lowerM, mkCode?, hfc]
      rw [hcode]
      have hX : rd (wr h (bp + d) (reps k (natBytes 8 P.toNat) ++ T)) (bp + d) t.size =
          reps k (natBytes 8 P.toNat) ++ T := by
        have := rd_wr h (bp + d) (reps k (natBytes 8 P.toNat) ++ T) (by simp; omega)
        simpa [hsz, Nat.mul_comm 8] using this
      refine fillCode_msim H.run H.bpOk hkw hk8 (by omega) (by omega) rfl
        (by simp [Exp.exec, Tick.cost]) (fun f' _ _ => ?_) (fun x hx => ?_)
      · exact hbuild _ _ (rd_length _ _ _) (by rw [htg]; trivial) (by rw [hX]; exact hargs env)
      · unfold Prot InR at hx
        exact wr_out (by simp; omega) (by omega) (by simp; omega)
    | none =>
    cases hcc : copyCode? c args ρ d (Tl.none.hb.mkW ps t) with
    | some code =>
      -- a large first argument in memory, copied by a loop
      have hcode : lowerM (.mk c args) .none ρ n d = code := by simp only [lowerM, mkCode?, hfc, hcc]
      rw [hcode]
      have hne := (Args.noExt H.vs args fun i h => by
        cases args <;> simpa [Exp.VSafe] using h).noExtFor c.plan.1
      simp only [copyCode?] at hcc
      split at hcc
      · rename_i oss hpl'
        split at hcc
        · rename_i j o o1 sz hbv
          split at hcc
          · rename_i hkW
            simp only [Option.some.injEq] at hcc; subst hcc
            obtain ⟨e, m, rfl, hρ, h8, hsU, ⟨A, B, hP, hP'⟩, hnhm, hnem, hargsAt⟩ :=
              bigVar?_spec args oss hbv
            rw [hpl'] at hne hpl hpw
            obtain ⟨hnem1, hne'⟩ := hnem S hne
            have hl := H.lay
            have hsing := hl.var m
            have hsn := hsing.snd_none hnem1
            have hlen := hl.length
            have hA : (S.getD m.idx default).A = bp + o := by
              have := hsing.2.1; rw [hρ] at this; exact this.1
            have hs : o + e.size ≤ n := by have := hsing.slotLe; rw [hρ] at this; exact this
            have hv := (H.envRel.get m (by rw [hρ]; rfl)).1.exact (hnhm S hnh) hnem1 hsn
            rw [hA] at hv
            have hq0 : o1 + e.size ≤ t.size := (hpl (o1, e.size) (by rw [hP]; simp)).1
            have hd1 : Away bp (d + o1) e.size Γ ρ S := hd.sub (by omega) (by omega)
            have hdj := Away.var m hd1 hlen.1 hlen.2
            rw [SI.Out_none hsn] at hdj
            have hdj1 : Disj (d + o1) e.size o e.size := by
              have := hdj.1; rw [hρ] at this; simpa only [Loc.off, Loc.size] using this
            have hk8 : 8 * (e.size / 8) = e.size := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)
            rw [hP] at hpw
            have hpw' : (A ++ B).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) :=
              hpw.sublist (List.Sublist.append_left (List.sublist_cons_self _ B) A)
            have hsep : ∀ q ∈ A ++ B, Disj o1 e.size q.1 q.2 := by
              intro q hq
              rcases List.mem_append.mp hq with hq | hq
              · have := (List.pairwise_append.mp hpw).2.2 q hq (o1, e.size) (by simp)
                unfold Disj at this ⊢; omega
              · exact List.rel_of_pairwise_cons (List.pairwise_append.mp hpw).2.1 hq
            refine tickLoop_msim (h₁ := wr h (bp + (d + o1)) (rd h (bp + o) (8 * (e.size / 8))))
              H.run hkW rfl (by simp [Exp.exec, Tick.cost])
              (fun c' => copyLoop_reach o (d + o1) (e.size / 8) 1 bp (by rw [hk8]; omega)
                (by rw [hk8]; omega) (by rw [hk8]; omega) (by unfold Disj at hdj1; omega)
                (by rw [hk8]; omega) (by rw [hk8]; omega) _ k w H.run f h c' H.bpOk)
              (fun f₁ hB₁ hk => ?_)
            rw [hk8]
            have henv₁ := H.envRel.wr_away hl hb (rd h (bp + o) e.size)
              (by rw [rd_length]; exact hd1) (by rw [rd_length]; omega)
            rw [← Nat.add_assoc] at henv₁ ⊢
            obtain ⟨f₂, h₂, hr₂, hb₂, hout₂, hargs₂⟩ := argsTo_runs (κ := κ) (ω := ω) (L := L)
              (Sz := t.size) hl hd hdn hb hbL args (oss.set j []) f₁ _ (hB₁.trans H.bpOk) henv₁
              (H.sl.rel.keep hk) hnh hne'
              (fun q hq => (hpl q (by
                rw [hP]; rw [hP'] at hq
                rcases List.mem_append.mp hq with hq | hq <;> simp [hq])).1)
              (by rw [hP']; exact hpw')
            have hfirst : rd h₂ (bp + d + o1) e.size = rd h (bp + o) e.size := by
              rw [rd_congr (h' := h₂) (fun i hi => hout₂ _ (by omega) fun ⟨q, hq, h1, h2⟩ => by
                rw [hP'] at hq
                have := hsep q hq
                unfold Disj at this; omega)]
              have := rd_wr h (bp + d + o1) (rd h (bp + o) e.size) (by rw [rd_length]; omega)
              rwa [rd_length] at this
            refine ⟨f₂, h₂, hr₂, hb₂, ?_, fun x hx => ?_⟩
            · refine hbuild _ _ (rd_length _ _ _) (by rw [hpl']; trivial) ?_
              rw [hpl']
              exact hargsAt env _ hargs₂ (by rw [← rd_slice _ _ _ _ _ hq0, hfirst]; exact hv)
            · unfold Prot InR at hx
              rw [hout₂ x (by omega) fun ⟨q, hq, h1, h2⟩ => by
                have := (hpl q (by
                  rw [hP]; rw [hP'] at hq
                  rcases List.mem_append.mp hq with hq | hq <;> simp [hq])).1; omega]
              exact wr_out (by rw [rd_length]; omega) (by omega) (by rw [rd_length]; omega)
          · simp at hcc
        · simp at hcc
      · simp at hcc
    | none =>
    obtain ⟨f₁, h₁, hr₁, hb₁, hout₁, hargs⟩ := argsTo_runs (κ := κ) (ω := ω) (L := L) (Sz := t.size)
      H.lay hd hdn (by omega) (by omega) args c.plan.1 f h H.bpOk H.envRel H.sl.rel hnh
      ((Args.noExt H.vs args fun i h => by
        cases args <;> simpa [Exp.VSafe] using h).noExtFor _) (fun q hq => (hpl q hq).1) hpw
    have hprot₁ : ∀ x, Prot bp n d t.size Γ S W x → h₁ (UInt64.ofNat x) = h (UInt64.ofNat x) :=
      fun x hx => hout₁ x (by unfold Prot at hx; omega) fun ⟨q, hq, h1, h2⟩ => by
        have := (hpl q hq).1; unfold Prot InR at hx; omega
    cases htg : c.plan.2 with
    | none =>
      have hcode : lowerM (.mk c args) .none ρ n d =
          .seq (.tick (.ctor (Tl.none.hb.mkW ps t))) (.seq (argsTo args c.plan.1 ρ d) .skip) := by
        simp only [lowerM, mkCode?, htg, hfc, hcc]
      rw [hcode]
      refine MSim.tick_done H.run (Runs.seq hr₁ (Runs.skip _ _)) rfl (by simp [Exp.exec, Tick.cost])
        hb₁ ?_ hprot₁
      exact hbuild _ _ (rd_length _ _ _) (by rw [htg]; trivial) hargs
    | some i =>
      have hcode : lowerM (.mk c args) .none ρ n d =
          .seq (.tick (.ctor (Tl.none.hb.mkW ps t))) (.seq (argsTo args c.plan.1 ρ d)
            (.store .w8 (.slot BP) (UInt64.ofNat d) (.imm (UInt64.ofNat i)))) := by
        simp only [lowerM, mkCode?, htg, hfc, hcc]
      rw [hcode]
      have h1t := htag1 (by rw [htg]; rfl)
      let b : UInt8 := (UInt64.ofNat i).toUInt8
      have hst : Runs κ ω L (.store .w8 (.slot BP) (UInt64.ofNat d) (.imm (UInt64.ofNat i))) f₁ h₁ f₁
          (wr h₁ (bp + d) [b]) :=
        Runs.congr (Runs.store _ _ _ _ _ _
          (acc_off (b := 1) (by omega) (by omega) (hb₁.trans H.bpOk))) rfl (by
          simp only [eval_slot, eval_imm, hb₁, H.bpOk, ofNat_add_ofNat]; rfl)
      refine MSim.tick_done H.run (Runs.seq hr₁ hst) rfl (by simp [Exp.exec, Tick.cost])
        hb₁ ?_ (fun x hx => ?_)
      · refine hbuild _ _ (rd_length _ _ _) ?_ (hargs.congr _ _ fun q hq => ?_)
        · rw [htg]; show (rd _ (bp + d) t.size).head? = some b
          cases ht : t.size with
          | zero => omega
          | succ m => simp [rd, wr, Heap.store8, b]
        · have hq1 := (hpl q hq).2 (by rw [htg]; rfl)
          have hq2 := (hpl q hq).1
          rw [← rd_slice _ _ _ _ _ hq2, ← rd_slice _ _ _ _ _ hq2]
          exact rd_congr fun j hj => wr_out (by simp; omega) (by omega) (by simp; omega)
      · unfold Prot InR at hx
        rw [wr_out (by simp; omega) (by omega) (by simp; omega)]
        exact hprot₁ x ⟨hx.1, hx.2.1, hx.2.2⟩
  | whole x => simp [Exp.Conf] at hC
  | word K =>
    -- a constructor computed into the slots from `K`
    have hok : c.slotOk = true := hC
    have hcode : lowerM (.mk c args) (.word K) ρ n d =
        .seq (.tick (.ctor ((Tl.word K).hb.mkW ps t))) (ctorCode args c.plan ρ K t.slotN) := by
      simp only [lowerM, hok, ↓reduceIte]
    simp only [Ctor.slotOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hts, hfit⟩, hsz⟩ := hok
    obtain ⟨f', hr, hfb, hout, B, hBl, hBt, hBa, hW⟩ := ctorCode_reach (κ := κ) (ω := ω) (L := L)
      args c.plan K t.slotN t.size (Ty.slotN_pos hts) (Ty.slotN_le hts) H.tmOk.1 H.bpOk H.envRel
      H.sl.rel H.lay H.nL H.nU (fun i k hk => (H.sl.ok.range i k hk).1) hfit
      (by rcases Ty.slotTy_cases hts with ⟨h1, h2, _⟩ | ⟨h1, _, _⟩
          · right; refine ⟨h1, h2, ?_⟩; rw [h1] at hsz; simpa using hsz
          · left; exact h1)
      (fun q hq => (hpl q hq).1) hnh
      ((Args.noExt H.vs args fun i h => by cases args <;> simpa [Exp.VSafe] using h))
    rw [hcode]
    exact MSim.tick_word H.run hr rfl (by simp [Exp.exec, Tick.cost]) hfb
      (fun y hy hy' => hout y hy (Or.inl hy'))
      ⟨B, hbuild _ B hBl hBt hBa, hW⟩ fun x hx => SProt.lt_word H.tmOk hx
  | split f0 cs =>
    simp only [Tl.dsz] at hdn hd ⊢
    cases args with
    | nil => simp [Exp.Conf] at hC
    | @cons p0 ps' a rest =>
      simp only [Exp.Conf, Bool.and_eq_true, decide_eq_true_eq] at hC
      obtain ⟨⟨⟨⟨hnone, hf0⟩, hplan⟩, hvars⟩, hsizes⟩ := hC
      have htake : c.plan.1.take 1 = [[0]] := by rw [hplan]; rfl
      have hcode : lowerM (.mk c (.cons a rest)) (.split f0 cs) ρ n d =
          .seq (.tick (.ctor ((Tl.split f0 cs).hb.mkW (p0 :: ps') t))) (.seq (argsTo (.cons a rest) [[0]] ρ d) .skip) := by
        simp only [lowerM, htake, hnone]
      rw [hcode]
      have hpl0 : placements (p0 :: ps') [[0]] = [(0, p0.size)] := by
        simp [placements]
      obtain ⟨f₁, h₁, hr₁, hb₁, hout₁, hargs⟩ := argsTo_runs (κ := κ) (ω := ω) (L := L) (Sz := f0)
        H.lay hd hdn (by omega) (by omega) (.cons a rest) [[0]] f h H.bpOk H.envRel H.sl.rel hnh
        ⟨H.vs.atom a fun i h => by simpa [Exp.VSafe] using h, by cases rest <;> trivial⟩
        (fun q hq => by rw [hpl0] at hq; simp at hq; subst hq; simp; omega)
        (by rw [hpl0]; simp)
      have hout₁' : ∀ x, x < UInt64.size → ¬ InR (bp + d) f0 x → h₁ (UInt64.ofNat x) = h (UInt64.ofNat x) :=
        fun x hx hn => hout₁ x hx fun ⟨q, hq, h1, h2⟩ => by
          rw [hpl0] at hq; simp at hq; subst hq; exact hn ⟨by omega, by simp at h2; omega⟩
      have henv₁ : MEnvRel h₁ bp env ρ S := H.envRel.congr fun x hx => hout₁' x
        (by have := H.lay.vis_lt hx; omega) fun hin => hd.not_vis hin hx
      -- the in-place components have no hole: they are writable
      have hcnh : ∀ c' ∈ cs, (S.getD c'.1 default).hole = none := by
        intro c' hc'
        have hw' := H.tmOk c' hc'
        have hlen := H.lay.length
        by_cases hlt : c'.1 < Γ.length
        · obtain ⟨T, m, hm⟩ := Mem.ofIdx Γ c'.1 hlt
          rw [← hm] at hw' ⊢
          exact (H.lay.var m).2.2.1 hw'
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show S.length ≤ c'.1 by omega)]
          rfl
      -- the bytes representing the value: the first argument and the in-place components
      obtain ⟨Ls, hLs, hLq, hLa⟩ := argsAt_vars henv₁ (H.sl.rel.keep hr₁.keep) rest cs hvars
        hsizes hcnh
      let segs : List (Nat × List UInt8) := (0, rd h₁ (bp + d) f0) ::
        Ls.map fun q => (q.1.2.1, q.2)
      have hsegs : segs.map (fun q => (q.1, q.2.length)) = placements (p0 :: ps') c.plan.1 := by
        rw [hplan]
        simp only [segs, List.map_cons, List.map_map, rd_length, placements, List.map_nil,
          List.singleton_append, hf0]
        rw [placements_cs cs hsizes, ← hLs]
        congr 1
        simp only [List.map_map]
        apply List.map_congr_left; intro q hq; simp [(hLq q hq).1]
      let bs := patchAll (List.replicate t.size 0) segs
      have hin : ∀ q ∈ segs, q.1 + q.2.length ≤ (List.replicate t.size (0 : UInt8)).length := by
        intro q hq
        have := (hpl (q.1, q.2.length) (by rw [← hsegs]; exact List.mem_map_of_mem hq)).1
        simpa using this
      have hbl : bs.length = t.size := by rw [patchAll_length _ _ hin]; simp
      have hsl := patchAll_slice _ _ hin (by rw [hsegs]; exact hpw)
      have hs0 : slice bs 0 f0 = rd h₁ (bp + d) f0 := by
        have := hsl (0, rd h₁ (bp + d) f0) (by simp [segs]); rwa [rd_length] at this
      have hsq : ∀ q ∈ Ls, slice bs q.1.2.1 q.1.2.2 = q.2 := by
        intro q hq
        have := hsl (q.1.2.1, q.2) (by
          simp only [segs, List.mem_cons, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩)
        rwa [(hLq q hq).1] at this
      have hsc : ∀ c' ∈ cs, CompAt bs f₁ h₁ (ρ.getD c'.1 default) (S.getD c'.1 default) c'.2.1
          c'.2.2 := by
        intro c' hc'
        rw [← hLs] at hc'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc'
        exact (hLq q hq).2 bs (hsq q hq)
      refine MSim.tick_done H.run (Runs.seq hr₁ (Runs.skip _ _)) rfl (by simp [Exp.exec, Tick.cost])
        hb₁ ⟨bs, ?_, hs0, hsc⟩
        (fun x hx => hout₁' x (by unfold Prot at hx; omega) hx.2.1)
      refine hbuild _ _ hbl (by rw [hnone]; trivial) ?_
      rw [hplan]
      refine ⟨fun o ho => ?_, hLa bs hsq⟩
      simp only [List.mem_singleton] at ho; subst ho
      rw [hf0, hs0]
      have := hargs.1 0 (by simp)
      rw [← hf0, slice_full _ _ (rd_length _ _ _)] at this
      rw [← hf0]; exact this

/-! ## `Slots` -/

/-- Writing cell `j` puts bytes representing `v` over that cell and nowhere else in the `Slots`. -/
theorem slots_write_repr {τ : Ty} {n' j : Nat} (sv : Slots τ.carrier n') {v : τ.carrier}
    {h h' : Heap} {X : Nat}
    (hj : j < n') (hX : X + n' * τ.size ≤ UInt64.size)
    (hr : Data.reprBytes (α := Slots τ.carrier n') sv (rd h X (n' * τ.size)))
    (hout : ∀ a, a < UInt64.size → ¬ (X + j * τ.size ≤ a ∧ a < X + j * τ.size + τ.size) →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hv : Data.reprBytes v (rd h' (X + j * τ.size) τ.size)) :
    Data.reprBytes (α := Slots τ.carrier n') (Slots.setCell sv j (some v)) (rd h' X (n' * τ.size)) := by
  refine ⟨rd_length _ _ _, fun k hk => ?_⟩
  show Slots.cellRepr _ (slice (rd h' X (n' * τ.size)) (k * τ.size) τ.size)
  have hkb : k * τ.size + τ.size ≤ n' * τ.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have hjb : j * τ.size + τ.size ≤ n' * τ.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  rw [← rd_slice _ _ _ _ _ hkb]
  simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
  erw [Vector.getElem_set hj hk]
  split
  · rename_i hjk; subst hjk; exact hv
  · rename_i hjk
    have hk' : k ≠ j := fun e => hjk e.symm
    have e1 : rd h' (X + k * τ.size) τ.size = rd h (X + k * τ.size) τ.size := rd_congr fun x hx => by
      refine hout _ (by omega) ?_
      rintro ⟨h1, h2⟩
      have := elem_disj_of_ne (A := 0) (sz := τ.size) hk'; unfold Disj at this; omega
    rw [e1, rd_slice _ _ (n' * τ.size) _ _ hkb]
    exact hr.2 k hk

/-- Emptying a cell keeps the bytes, because an empty cell's bytes are arbitrary. -/
theorem slots_clear_repr {τ : Ty} {n' : Nat} (sv : Slots τ.carrier n') (j : Nat) (bs : List UInt8)
    (hr : Data.reprBytes (α := Slots τ.carrier n') sv bs) :
    Data.reprBytes (α := Slots τ.carrier n') (Slots.setCell sv j none) bs := by
  refine ⟨hr.1, fun k hk => ?_⟩
  by_cases hj : j < n'
  · simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
    erw [Vector.getElem_set hj hk]
    split
    · trivial
    · exact hr.2 k hk
  · simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
    exact hr.2 k hk

theorem slots_cell_repr {τ : Ty} {n' : Nat} (sv : Slots τ.carrier n') {j : Nat} {x : τ.carrier}
    {h : Heap} {X : Nat} (hc : Slots.cell sv j = some x)
    (hr : Data.reprBytes (α := Slots τ.carrier n') sv (rd h X (n' * τ.size))) :
    j < n' ∧ Data.reprBytes x (rd h (X + j * τ.size) τ.size) := by
  have hj : j < n' := by
    rcases Nat.lt_or_ge j n' with hj | hj
    · exact hj
    · simp [Slots.cell, vget, Nat.not_lt.mpr hj] at hc
  refine ⟨hj, ?_⟩
  have hjb : j * τ.size + τ.size ≤ n' * τ.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have := hr.2 j hj
  simp only [Slots.cell, vget, hj, ↓reduceDIte] at hc
  have hc' : sv.cells[j] = some x := hc
  simp only [Slots.cells] at hc'
  rw [hc'] at this
  rw [rd_slice _ _ (n' * τ.size) _ _ hjb]; exact this

theorem conf_k {Γ : List Ty} {t u : Ty} {e : Exp Γ t} {k : Exp Γ u} {tm : Tl}
    (hk : ∀ tm', tm' ≠ .none → e.Conf tm' = k.Conf tm') (hC : e.Conf tm = true) : k.Conf tm = true := by
  cases tm with
  | none => exact k.conf_none
  | whole _ | split _ _ => rw [← hk _ (fun h => by cases h)]; exact hC
  | word k => rw [← hk _ (fun h => by cases h)]; exact hC

/-- The case of `s.put! i a; k`. -/
theorem msound_put {Γ : List Ty} {t : Ty} {n' : Nat} {u : Ty} (p : Place Γ (.slots t n'))
    (i : Atom Γ .u64) (a : Atom Γ t) (k : Exp Γ u) (hc : p.contig = true) (ih : MSoundAt κ ω k) :
    MSoundAt κ ω (.put p i a k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hCk : k.Conf tm = true := conf_k (fun tm' h' => by cases tm' <;> first | rfl | exact absurd rfl h') H.conf
  obtain ⟨⟨hok, hvac⟩, hsk⟩ := H.safe
  have hmt := Nat.le_max_left t.size k.memNeed
  have hmk := Nat.le_max_right t.size k.memNeed
  have hnhp := p.nh_of .write fun i' H' h' => (H.hole i' H' h').2.2.1
  generalize hjj : (i.denote env).toNat = j at hvac hsk
  have hj : j < n' := by simp [Slots.isVacant] at hvac; exact hvac.1
  have hpv : p.ExtOk S := VS.place p H.vs fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact Place.VSafe_isVarAt h.1.1.1
  obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := n) H.lay
    (H.lay.away (Nat.le_refl _)) (by omega) (by omega) H.bpOk H.envRel H.sl.rel
    (a.noHole fun i' H' h' => (H.hole i' H' h').2.1)
    (by omega) (by omega) (H.vs.atom a fun i h => by
      simp only [Exp.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.2)
  have henv₁ : MEnvRel (wr h (bp + n) B) bp env ρ S :=
    H.envRel.above H.lay fun x hx => wr_out (by omega) (by omega) (by omega)
  have hfb₁ : f₁ BP = UInt64.ofNat bp := (hf₁ BP (by decide) (by decide)).trans H.bpOk
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc hfb₁ henv₁
    (H.sl.rel.keep hr₁.keep) H.lay hnhp.1 H.lawful.1 (hpv.notPair H.lay) (by omega) (by omega)
  obtain ⟨f₃, hr₃, hb₃, ha₃, _⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) i t.size _
    (hb₂.trans hfb₁) ha₂ henv₁ (H.sl.rel.keep fun x hx => (hr₂.keep x hx).trans (hr₁.keep x hx))
    H.lay (i.noHole fun i' H' h' => (H.hole i' H' h').1) (by omega) (by omega)
  rw [hjj] at ha₃
  have hg := place_get p hc H.lawful.1 hok henv₁ H.lay hnhp.2 hpv hns
  have hsz : (Ty.slots t n').size = n' * t.size := rfl
  have hjb : j * t.size + t.size ≤ n' * t.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  obtain ⟨f₄, hf₄, hr₄, hH'', hHout⟩ := stash_copy (κ := κ) (ω := ω) (L := L) (h := h) (n := n)
    (hb₃.trans (hb₂.trans hfb₁)) ha₃ hBl (by omega) (by omega) (by omega)
  generalize hH' : wr (wr h (bp + n) B) ((placeA p S env) + j * t.size) B = H₁ at hr₄ hH'' hHout
  have hrepS := slots_write_repr (τ := t) (v := a.denote env) (p.get env) hj (by omega) hg.2 hHout
    (by
      rw [← hH']
      have e := rd_wr (wr h (bp + n) B) (placeA p S env + j * t.size) B (by rw [hBl]; omega)
      rw [hBl] at e; rw [e]; exact hBr)
  have henv₂ := place_set p hc H.lawful.1 hok henv₁ H.lay H.restr.1 (by omega) hpv hns H₁ _ (fun x hx hn =>
    hHout x (by omega) (by
      intro ⟨h1, h2⟩; apply hn; unfold InR; constructor <;> omega)) hrepS
  have hK := ih.app (H.cont hCk H.restr.2 H.lawful.2 H.frozen (H.hole.sub fun _ _ h => h.2.2.2)
    (hf₄.trans (hb₃.trans (hb₂.trans hfb₁))) henv₂
    ((H.sl.rel.keep fun x hx => (hr₄.keep x hx).trans ((hr₃.keep x hx).trans ((hr₂.keep x hx).trans
      (hr₁.keep x hx)))).place_set p hns _) (by rw [← hjj] at hsk ⊢; exact hsk)
    (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)) kk
    (c + (Tick.mem (p.depth + 1) (width t)).cost κ)
  have hlen := H.lay.length
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run
    (MSim.runs H.run hr₁
    (hf₁ BP (by decide) (by decide)) (fun x hx => wr_out (by omega) (by unfold Prot at hx; omega)
      (by unfold Prot at hx; omega))
    (MSim.runs H.run hr₂ hb₂ (fun _ _ => rfl) (MSim.runs H.run hr₃ hb₃ (fun _ _ => rfl)
      (MSim.runs H.run hr₄ hf₄ (fun x hx => ?_) ?_))))).of_eq rfl rfl
    (by simp [Exp.exec, Tick.cost, hjj])
  · obtain ⟨hx1, hx2, hx3⟩ := hx
    refine hHout x (by omega) fun ⟨h1, h2⟩ => hx3 (InW.place p H.restr.1 ?_ hlen.2)
    exact place_in p hc H.lawful.1 hok henv₁ H.lay hpv (by unfold InR; omega)
  · simp only [hjj] at hK ⊢
    exact hK

/-- The case of `let x := s.take! i; k`. -/
theorem msound_take {Γ : List Ty} {t : Ty} {n' : Nat} {u : Ty} [Inhabited t.carrier]
    (p : Place Γ (.slots t n')) (i : Atom Γ .u64) (k : Exp (t :: Γ) u) (hc : p.contig = true)
    (ih : MSoundAt κ ω k) : MSoundAt κ ω (.take p i k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hCk : k.Conf tm.up = true := by
    cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using H.conf
  obtain ⟨⟨hok, hfull⟩, hsk⟩ := H.safe
  have hnhp := p.nh_of .write fun i' H' h' => (H.hole i' H' h').2.1
  generalize hjj : (i.denote env).toNat = j at hfull hsk
  obtain ⟨x, hx⟩ : ∃ x, Slots.cell (p.get env) j = some x := by
    simp only [Slots.isFull] at hfull; exact Option.isSome_iff_exists.mp hfull
  have hpv : p.ExtOk S := VS.place p H.vs fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact Place.VSafe_isVarAt h.1.1
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc H.bpOk H.envRel
    H.sl.rel H.lay hnhp.1 H.lawful.1 (hpv.notPair H.lay) (by omega) (by omega)
  obtain ⟨f₃, hr₃, hb₃, ha₃, _⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) i t.size _
    (hb₂.trans H.bpOk) ha₂ H.envRel (H.sl.rel.keep hr₂.keep) H.lay
    (i.noHole fun i' H' h' => (H.hole i' H' h').1) (by omega) (by omega)
  rw [hjj] at ha₃
  have hg := place_get p hc H.lawful.1 hok H.envRel H.lay hnhp.2 hpv hns
  have hsz : (Ty.slots t n').size = n' * t.size := rfl
  obtain ⟨hj, hxr⟩ := slots_cell_repr (τ := t) (p.get env) hx hg.2
  have hjb : j * t.size + t.size ≤ n' * t.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have henvC := place_set p hc H.lawful.1 hok H.envRel H.lay H.restr.1 (by omega) hpv hns h _
    (fun _ _ _ => rfl)
    (slots_clear_repr (τ := t) _ j _ hg.2)
  have hval : ((Slots.cell (p.get env) j).getD default : t.carrier) = x := by rw [hx]; rfl
  have hfe₃ := (H.sl.rel.keep fun x hx => (hr₃.keep x hx).trans (hr₂.keep x hx)).place_set p hns
    (Slots.setCell (p.get env) j none)
  have hf₃ : f₃ BP = UInt64.ofNat bp := hb₃.trans (hb₂.trans H.bpOk)
  have hdn := H.dn
  have hV := H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2
  -- the cell: loaded into the binder's frame slot, or copied to the binder's memory at `n`
  have hrest : MSim κ ω L ⟨if k.slotBind then
        .seq (ldSlots (scalarWidth t.size) (FR + slotsIn ρ) (.slot RA) 0 t.slotN)
          (lowerM k tm.up (.slot n (FR + slotsIn ρ) t.slotN :: ρ) (n + t.size) d)
      else .seq (copyB (.slot RA) 0 (.slot BP) n t.size) (lowerM k tm.up (.own n :: ρ) (n + t.size) d),
      kk, f₃, h, w, c + (Tick.mem (p.depth + 1) (width t)).cost κ⟩ kk (TQ tm bp d ρ S u)
      (Prot bp n d (tm.dsz u) Γ S W)
      (k.exec ω κ tm.up.hb (.cons ((Slots.cell (p.get env) j).getD default)
        (p.set env (Slots.setCell (p.get env) j none))) w) (SProt ρ W) := by
    split
    · rename_i hsb
      obtain ⟨f', hld, -, hlo, hword⟩ := load_words (κ := κ) (ω := ω) (L := L)
        (K := FR + slotsIn ρ) (o := 0) (Ty.slotTy_of_bind hsb) ha₃ (by decide)
        (Nat.le_add_right _ _) (by simpa using hxr) (by omega) (by omega)
      exact slot_step k ih H _ hld hlo hsb (by rw [hval]; exact hword) hCk H.restr.2 H.lawful.2
        H.frozen (H.hole.push _ rfl fun _ _ h => h.2.2) (Nat.le_refl _) (by omega) hf₃ henvC hfe₃
        hsk (by omega) hV fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2
    · obtain ⟨f₄, hf₄, hr₄⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot RA) (.slot BP)
        (by decide) (by decide) t.size 0 n ((placeA p S env) + j * t.size) bp f₃ h ha₃ hf₃
        (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
      simp only [Nat.add_zero] at hr₄
      have hv : Data.reprBytes ((Slots.cell (p.get env) j).getD default)
          (rd (wr h (bp + n) (rd h ((placeA p S env) + j * t.size) t.size)) (bp + n) t.size) := by
        have := rd_wr h (bp + n) (rd h ((placeA p S env) + j * t.size) t.size) (by simp; omega)
        rw [rd_length] at this; rw [this, hval]; exact hxr
      exact MSim.runs H.run hr₄ (hf₄ BP (by decide))
        (fun y hy => wr_out (by simp; omega) (by unfold Prot at hy; omega)
          (by unfold Prot at hy; simp; omega))
        (.unpush (Nat.le_refl _) (ih.app (H.push _ (Nat.le_refl _) hCk H.restr.2 H.lawful.2
          H.frozen (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega) (by omega)
          ((hf₄ BP (by decide)).trans hf₃)
          (henvC.above H.lay fun y hy => wr_out (by simp; omega) (by omega) (by simp; omega))
          (hfe₃.keep hr₄.keep) hv hsk hV H.run) kk _))
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run
    (MSim.runs H.run hr₂ hb₂ (fun _ _ => rfl) (MSim.runs H.run hr₃ hb₃ (fun _ _ => rfl)
      hrest))).of_eq ?_ ?_ ?_ <;>
    simp [Exp.exec, Tick.cost, hjj, Tl.hb_up]

end

end Millipede.Flat
