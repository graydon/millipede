import Millipede.Compile.LowerLet

/-!
# The memory refinement of enum `case`

A `case s sp eP eQ`, one step of a match on a derived enum, is lowered to a tag test. The code
loads the scrutinee's tag byte and compares it with `sp.tag`. On a hit it copies the payload to the
arm's variable, and otherwise it builds the rest and runs the other arm. The rest is the other
payload, a renumbered smaller sum or the whole value, as `RestMode` selects, and `Split.Lawful`
relates its bytes to `sp.split`.

A slot-resident scrutinee is taken apart in its frame slots. Its tag is the low byte of its first
word, the payload and a `payload` rest are in the words after it, and a `whole` rest is its words.
The tag test needs no bound on the number of variants, because `Split.Lawful` states what the tag
byte means. `Exp.memOk` still bounds the variants by 256, because the lowering writes one tag byte.

See doc/design/compiler.md.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem rd_headD {h : Heap} {A S : Nat} (hS : 1 ≤ S) : (rd h A S).headD 0 = h (UInt64.ofNat A) := by
  cases S with
  | zero => omega
  | succ S => rfl

theorem rd_head? {h : Heap} {A S : Nat} (hS : 1 ≤ S) : (rd h A S).head? = some (h (UInt64.ofNat A)) := by
  cases S with
  | zero => omega
  | succ S => rfl

/-- The code of a `case`'s rest builds bytes satisfying `RestOk` at `n'` and changes nothing below
`bp + n'`. -/
theorem restCode_runs (mode : RestMode) (tag ls po n' qsize S bp : Nat) {f : Frame} {h : Heap}
    (hf : f BP = UInt64.ofNat bp) (hS : 1 ≤ S) (hls : ls + S ≤ n')
    (hb : bp + n' + qsize ≤ UInt64.size)
    (hmode : match mode with
      | .payload => po + qsize ≤ S
      | .whole => qsize = S
      | .retag po' m => 1 ≤ po' ∧ po' + m ≤ qsize ∧ po + m ≤ S)
    (hbL : bp + n' + qsize ≤ L) :
    ∃ f' h', f' BP = f BP ∧ Runs κ ω L (restCode mode tag ls po n' qsize) f h f' h' ∧
      (∀ y, y < bp + n' → h' (UInt64.ofNat y) = h (UInt64.ofNat y)) ∧
      RestOk mode tag po qsize (rd h (bp + ls) S) (rd h' (bp + n') qsize) := by
  cases mode with
  | payload =>
    simp only at hmode
    obtain ⟨f', hf', hr⟩ := payload_copy (κ := κ) (ω := ω) (L := L) (ls := ls) (po := po)
      (sz := qsize) (S := S) (n' := n') (h := h) hf hmode hls hb hbL
    refine ⟨f', _, hf', hr, fun y hy => wr_out (by simp; omega) (by omega) (by omega), ?_⟩
    simp only [RestOk]
    have := rd_wr h (bp + n') (rd h (bp + ls + po) qsize) (by simp; omega)
    rw [rd_length] at this
    rw [this, rd_slice _ (bp + ls) S _ _ hmode]
  | whole =>
    simp only at hmode
    subst hmode
    obtain ⟨f', hf', hr⟩ := payload_copy (κ := κ) (ω := ω) (L := L) (ls := ls) (po := 0)
      (sz := qsize) (S := qsize) (n' := n') (h := h) hf (by omega) hls hb hbL
    refine ⟨f', _, hf', hr, fun y hy => wr_out (by simp; omega) (by omega) (by omega), ?_⟩
    simp only [RestOk]
    have := rd_wr h (bp + n') (rd h (bp + ls + 0) qsize) (by simp; omega)
    rw [rd_length] at this
    rw [this]; rfl
  | retag po' m =>
    obtain ⟨h1, h2, h3⟩ := hmode
    let b := h (UInt64.ofNat (bp + ls))
    let v : UInt64 := b.toUInt64 - (if UInt64.ofNat tag < b.toUInt64 then 1 else 0)
    let f₁ := f.set RT (h.load .w8 ((Operand.slot BP).eval f + UInt64.ofNat ls))
    have hf₁ : f₁ BP = UInt64.ofNat bp := by
      simp only [f₁]; rw [Frame.set_ne _ _ (by decide)]; exact hf
    have hRT : f₁ RT = b.toUInt64 := by
      simp only [f₁, Frame.set, ↓reduceIte, eval_slot, hf, ofNat_add_ofNat, Heap.load, b]
    let f₂ := f₁.set RX (BinOp.ult.eval ((Operand.imm (UInt64.ofNat tag)).eval f₁)
      ((Operand.slot RT).eval f₁))
    let f₃ := f₂.set RT (BinOp.sub.eval ((Operand.slot RT).eval f₂) ((Operand.slot RX).eval f₂))
    have hf₃ : f₃ BP = UInt64.ofNat bp := by
      simp only [f₃, f₂]; rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide)]; exact hf₁
    have hv : f₃ RT = v := by
      simp only [f₃, f₂, Frame.set_same, eval_slot, eval_imm, BinOp.eval, v]
      rw [Frame.set_ne _ _ (by decide)]; simp only [hRT]
    let h₄ := h.store .w8 ((Operand.slot BP).eval f₃ + UInt64.ofNat n') ((Operand.slot RT).eval f₃)
    have hh₄ : h₄ = h.store8 (UInt64.ofNat (bp + n')) v.toUInt8 := by
      simp only [h₄, eval_slot, hf₃, hv, ofNat_add_ofNat, Heap.store]
    obtain ⟨f₅, hf₅, hr₅⟩ := payload_copy (κ := κ) (ω := ω) (L := L) (ls := ls) (po := po) (sz := m)
      (S := S) (n' := n' + po') (h := h₄) hf₃ h3 (by omega) (by omega) (by omega)
    have hr : Runs κ ω L (restCode (.retag po' m) tag ls po n' qsize) f h f₅
        (wr h₄ (bp + (n' + po')) (rd h₄ (bp + ls + po) m)) :=
      Runs.seq (Runs.load .w8 RT (.slot BP) (UInt64.ofNat ls) f h
        (acc_off (b := 1) (by omega) (by omega) hf)) (Runs.seq (Runs.bin _ _ _ _ _ _)
        (Runs.seq (Runs.bin _ _ _ _ _ _) (Runs.seq (Runs.store .w8 (.slot BP) (UInt64.ofNat n')
          (.slot RT) f₃ h (acc_off (b := 1) (by omega) (by omega) hf₃)) hr₅)))
    have h₄lo : ∀ y, y < UInt64.size → y ≠ bp + n' → h₄ (UInt64.ofNat y) = h (UInt64.ofNat y) := by
      intro y hy hne
      rw [hh₄]; simp only [Heap.store8]
      rw [ite_eq_right (ofNat_ne hy (by omega) hne)]
    have hrd₄ : rd h₄ (bp + ls + po) m = rd h (bp + ls + po) m :=
      rd_congr fun i hi => h₄lo _ (by omega) (by omega)
    refine ⟨f₅, _, hf₅.trans (hf₃.trans hf.symm), hr, fun y hy => ?_, ?_⟩
    · rw [wr_out (by simp; omega) (by omega) (by simp; omega)]
      exact h₄lo y (by omega) (by omega)
    · simp only [RestOk]
      refine ⟨?_, ?_⟩
      · rw [rd_head? (by omega), wr_out (by simp; omega) (by omega) (by simp; omega), hh₄,
          rd_headD hS]
        simp [Heap.store8, v, b]
      · rw [← rd_slice _ (bp + n') qsize _ _ h2, ← rd_slice _ (bp + ls) S _ _ h3, ← Nat.add_assoc]
        have := rd_wr h₄ (bp + (n' + po')) (rd h₄ (bp + ls + po) m) (by simp; omega)
        rw [rd_length] at this
        rw [← Nat.add_assoc] at this
        rw [this, hrd₄]

/-- One arm of a `case`, which is a prelude that builds the arm's variable at `n' ≥ n` followed by
the arm. -/
theorem case_arm {Γ : List Ty} {a u : Ty} (eA : Exp (a :: Γ) u) (ihA : MSoundAt κ ω eA)
    {e₀ : Exp Γ u} {pre : Stmt} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI}
    {n n' d bp : Nat} {env : Env Γ} {x : a.carrier} {f₀ : Frame} {h₀ : Heap}
    {k : List Kont} {f₁ f₂ : Frame} {h₁ h₂ : Heap} {w : World} {c : Nat}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w)
    (hC : eA.Conf tm.up = true) (hR : eA.Restr (true :: W)) (hL : eA.Lawful)
    (hF : eA.Frozen) (hH : HoleAv eA (⟨bp + n', none, none, none⟩ :: S)) (hnn : n ≤ n')
    (hb : bp + n' + (a.size + eA.memNeed) ≤ UInt64.size) (hf₁ : f₁ BP = UInt64.ofNat bp)
    (hr : Runs κ ω L pre f₁ h₁ f₂ h₂) (hf₂ : f₂ BP = f₁ BP)
    (hm : ∀ y, y < bp + n' → h₂ (UInt64.ofNat y) = h₁ (UInt64.ofNat y))
    (hx : Data.reprBytes x (rd h₂ (bp + n') a.size)) (henv : MEnvRel h₁ bp env ρ S)
    (hfe : FEnvRel f₁ env ρ) (hs : eA.safe ω (.cons x env) w)
    (hbL : bp + n' + (a.size + eA.memNeed) ≤ L) (hV : VS S fun i => eA.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → eA.noAddr (i + 1) = true) :
    MSim κ ω L ⟨.seq pre (lowerM eA tm.up (.own n' :: ρ) (n' + a.size) d), k, f₁, h₁, w, c⟩ k
      (TQ tm bp d ρ S u) (Prot bp n d (tm.dsz u) Γ S W) (eA.exec ω κ tm.up.hb (.cons x env) w) (SProt ρ W) :=
  MSim.runs H.run hr hf₂ (fun y hy => hm y (by unfold Prot at hy; omega))
    (arm_step eA ihA H x hC hR hL hF hH hnn (by omega) (hf₂.trans hf₁)
      (henv.above H.lay fun y hy => hm y (by omega)) (hfe.keep hr.keep) hx hs (by omega) hV hna)

theorem conf_case {Γ : List Ty} {t p q u : Ty} {s : Atom Γ t} {sp : Split t p q}
    {eP : Exp (p :: Γ) u} {eQ : Exp (q :: Γ) u} {tm : Tl}
    (h : (Exp.case s sp eP eQ).Conf tm = true) : eP.Conf tm.up = true ∧ eQ.Conf tm.up = true := by
  cases tm with
  | none => exact ⟨eP.conf_none, eQ.conf_none⟩
  | whole _ | split _ _ => simpa [Exp.Conf] using h
  | word k => simpa [Exp.Conf] using h

/-- A `case` on a slot-resident scrutinee in the slots from `K`. The tag is the low byte of its
first word, the tested payload is in the words after it, and the rest is either the other payload,
also after the tag's word, or the scrutinee's own words. -/
theorem case_slot {Γ : List Ty} {t p q u : Ty} (s : Atom Γ t) (sp : Split t p q)
    (eP : Exp (p :: Γ) u) (eQ : Exp (q :: Γ) u) (ihP : MSoundAt κ ω eP) (ihQ : MSoundAt κ ω eQ)
    {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ}
    {kk : List Kont} {f : Frame} {h : Heap} {w : World} {c K : Nat}
    (H : MHyp ω (.case s sp eP eQ) tm L W ρ S n d bp env f h w) (hso : s.slotOf ρ = some K) :
    MSim κ ω L ⟨lowerM (.case s sp eP eQ) tm ρ n d, kk, f, h, w, c⟩ kk (TQ tm bp d ρ S u)
      (Prot bp n d (tm.dsz u) Γ S W) ((Exp.case s sp eP eQ).exec ω κ tm.hb env w) (SProt ρ W) := by
  obtain ⟨m, rfl, hk⟩ : ∃ m, s = .var m ∧ (ρ.getD m.idx default).slot? = some K := by
    cases s with
    | var m => exact ⟨m, rfl, hso⟩
    | lit v => simp [Atom.slotOf] at hso
  simp only [lowerM, hso]
  have hb := H.size; have hbL := H.room; have hs := H.safe; have hC := conf_case H.conf
  simp only [Exp.memNeed] at hb hbL; simp only [Exp.safe] at hs
  obtain ⟨hLp, hLs, hLm, hLx⟩ := H.lawful.1
  have hmP := Nat.le_max_left (p.size + eP.memNeed) (q.size + eQ.memNeed)
  have hmQ := Nat.le_max_right (p.size + eP.memNeed) (q.size + eQ.memNeed)
  have hok : sp.slotOk = true := by
    have := (H.sl.na m.idx (Loc.isSlot_iff.2 ⟨K, hk⟩)).1
    simp only [Exp.noAddr, Atom.isVar, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_self_eq_true] at this
    simpa using this.1.1
  obtain ⟨B, hB, hwB, hnw, hts, hRT⟩ := slot_tag H.sl.rel hk
  have hran := H.sl.ok.range m.idx K hk
  rw [hnw] at hran
  have hFRK := hran.1
  have hBl : B.length = t.size := Data.reprBytes_length hB
  have hx := hLx _ _ hB
  let f₁ := f.set RT (f K &&& 0xFF)
  let f₂ := f₁.set RX (BinOp.eq.eval ((Operand.slot RT).eval f₁)
    ((Operand.imm (UInt64.ofNat sp.tag)).eval f₁))
  have hr₁ : Runs κ ω L (.bin .band RT (.slot K) (.imm 0xFF)) f h f₁ h := Runs.bin _ _ _ _ _ _
  have hr₂ : Runs κ ω L (.bin .eq RX (.slot RT) (.imm (UInt64.ofNat sp.tag))) f₁ h f₂ h :=
    Runs.bin _ _ _ _ _ _
  have hf₂ : f₂ BP = UInt64.ofNat bp := by
    simp only [f₂, f₁]; rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide)]
    exact H.bpOk
  have hfe₂ := (H.sl.rel.keep hr₁.keep).keep hr₂.keep
  have hf₁ : f₁ BP = UInt64.ofNat bp := by
    simp only [f₁]; rw [Frame.set_ne _ _ (by decide)]; exact H.bpOk
  have hRX : (Operand.slot RX).eval f₂ =
      if (B.headD 0).toUInt64 = UInt64.ofNat sp.tag then 1 else 0 := by
    simp only [f₂, f₁, eval_slot, Frame.set_same, eval_imm, BinOp.eval]; rw [hRT]
  have hw₂ : ∀ (p : Ty) (v : p.carrier) (j : Nat), K ≤ j → (p.slotTy = true → WordsRel p v f j) →
      p.slotTy = true → WordsRel p v f₂ j := fun p v j hj hw hts =>
    (hw hts).congr fun x hx _ => by
      simp only [f₂, f₁]
      rw [Frame.set_ne _ _ (by simp only [FR, RX] at hFRK ⊢; omega),
        Frame.set_ne _ _ (by simp only [FR, RT] at hFRK ⊢; omega)]
  simp only [Split.slotOk, Ty.wordPay, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨-, hpP⟩, h8P⟩, hmode⟩ := hok
  cases hsv : sp.split ((Atom.var m).denote env) with
  | inl x =>
    obtain ⟨htag, hpx⟩ := hx.1 x hsv
    obtain ⟨hv0, hw, hn⟩ := slot_payload hts hBl hwB hpP hLp h8P hpx
    have hA := arm_slot (L := L) (k := kk) (c := c + (Tick.match_ (width t)).cost κ)
      (sz := t.size) (src := K + 1) (cnt := (Atom.var m).slotNw ρ - 1) eP ihP H x
      (hpP.imp_right And.left) (by omega) (by simp only [Atom.slotNw, hnw]; omega) (by omega)
      hf₂ H.envRel hfe₂ hv0 (hw₂ _ _ _ (by omega) hw) hC.1 H.restr.1 H.lawful.2.1 H.frozen.1
      (H.hole.push _ rfl fun _ _ h => h.2.1) (by omega) (hs.1 x hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
    exact (MSim.tick H.run (MSim.runs H.run hr₁ (by rw [hf₁, H.bpOk]) (fun _ _ => rfl)
      (MSim.runs H.run hr₂ (by rw [hf₂, hf₁]) (fun _ _ => rfl) (MSim.ite_t H.run
        (by rw [hRX, ite_eq_left_of_eq_true _ _ (eq_true htag)]; decide) hA)))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, Tl.hb_up])
  | inr y =>
    obtain ⟨htag, hqy⟩ := hx.2 y hsv
    -- the rest: the other payload after the tag's word, or the scrutinee's own words
    obtain ⟨hpay, hsrc, hmin, hv0, hw, hqs⟩ : (q.size = 0 ∨ q.slotTy = true) ∧
        K + sp.restOff + q.slotN ≤ FR + slotsIn ρ ∧
        min q.slotN ((Atom.var m).slotNw ρ - sp.restOff) = q.slotN ∧
        (q.size = 0 → Data.reprBytes y []) ∧
        (q.slotTy = true → WordsRel q y f (K + sp.restOff)) ∧ q.size ≤ t.size := by
      unfold Split.restOff
      cases hmd : sp.mode with
      | payload =>
        simp only [hmd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmode hLm; rw [hmd] at hqy
        obtain ⟨hv0, hw, hn⟩ := slot_payload hts hBl hwB hmode.1 hLm hmode.2
          (hqy _ (slice_length_of_le (by omega)) rfl)
        simp only [reduceCtorEq, ↓reduceIte, Atom.slotNw, hnw]
        exact ⟨hmode.1.imp_right And.left, by omega, by omega, hv0, hw, by omega⟩
      | whole =>
        simp only [hmd] at hmode hLm; rw [hmd] at hqy
        have hn : q.slotN = t.slotN := by unfold Ty.slotN; rw [hLm]
        simp only [↓reduceIte, Atom.slotNw, hnw, Nat.add_zero, Nat.sub_zero]
        exact ⟨Or.inr hmode, by omega, by omega, fun h0 => by omega,
          fun _ => ⟨B, hqy B (by rw [hBl, hLm]) rfl, by rw [hn]; exact hwB⟩, by omega⟩
      | retag => simp [hmd] at hmode
    have hA := arm_slot (L := L) (k := kk) (c := c + (Tick.match_ (width t)).cost κ)
      (sz := t.size) (src := K + sp.restOff) (cnt := (Atom.var m).slotNw ρ - sp.restOff) eQ ihQ
      H y hpay hsrc hmin hqs
      hf₂ H.envRel hfe₂ hv0 (hw₂ _ _ _ (by omega) hw) hC.2 H.restr.2 H.lawful.2.2 H.frozen.2
      (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega) (hs.2 y hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)
    exact (MSim.tick H.run (MSim.runs H.run hr₁ (by rw [hf₁, H.bpOk]) (fun _ _ => rfl)
      (MSim.runs H.run hr₂ (by rw [hf₂, hf₁]) (fun _ _ => rfl) (MSim.ite_e H.run
        (by rw [hRX, ite_eq_right_of_eq_false _ _ (eq_false htag)]) hA)))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, Tl.hb_up])

/-- The case of `case` on an enum, which tests the tag byte, then copies the payload or builds the
rest, and runs the arm. -/
theorem msound_case {Γ : List Ty} {t p q u : Ty} (s : Atom Γ t) (sp : Split t p q)
    (eP : Exp (p :: Γ) u) (eQ : Exp (q :: Γ) u) (ihP : MSoundAt κ ω eP) (ihQ : MSoundAt κ ω eQ) :
    MSoundAt κ ω (.case s sp eP eQ) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  cases hso : s.slotOf ρ with
  | some K => exact case_slot s sp eP eQ ihP ihQ H hso
  | none =>
  simp only [lowerM, hso]
  have hb := H.size; have hbL := H.room; have hs := H.safe; have hC := conf_case H.conf
  simp only [Exp.memNeed] at hb hbL; simp only [Exp.safe] at hs
  obtain ⟨hLp, hLs, hLm, hLx⟩ := H.lawful.1
  have hmP := Nat.le_max_left (p.size + eP.memNeed) (q.size + eQ.memNeed)
  have hmQ := Nat.le_max_right (p.size + eP.memNeed) (q.size + eQ.memNeed)
  obtain ⟨f₁, h₁, hf₁, hfk₁, hRT, hm₁, hls, hrep, hpre⟩ := scrut_load (κ := κ) (ω := ω) (L := L) s
    H.lay (by omega) H.bpOk H.envRel H.sl.rel (s.noHole fun i H' h' => (H.hole i H' h').1) (by omega)
    (H.vs.atom s fun i h => by
      simp only [Exp.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.1)
    (fun m e => by subst e; unfold Loc.isSlot; simp only [Atom.slotOf] at hso; rw [hso]; rfl)
    H.run hLs
  have hfe₂ : ∀ v, FEnvRel (f₁.set RX v) env ρ := fun v =>
    H.sl.rel.keep fun x hx => (Frame.set_keep f₁ v (by decide) x hx).trans (hfk₁ x hx)
  have henv₁ := H.envRel.above H.lay hm₁
  have hx := hLx _ _ hrep
  rw [rd_headD hLs] at hx
  have hRX : ∀ v : UInt64, (Operand.slot RX).eval (f₁.set RX (BinOp.eq.eval ((Operand.slot RT).eval f₁)
      ((Operand.imm v).eval f₁))) = if (h₁ (UInt64.ofNat (bp + scrutLoc s ρ n))).toUInt64 = v then 1 else 0 := by
    intro v; simp only [eval_slot, Frame.set_same, eval_imm, BinOp.eval, hRT]
  have hp : ∀ x, Prot bp n d (tm.dsz u) Γ S W x → x < bp + n := fun x hx => hx.1
  have hf₂ : ∀ v, (f₁.set RX v) BP = UInt64.ofNat bp := fun v =>
    (Frame.set_ne f₁ (x := RX) (y := BP) v (by decide)).trans hf₁
  have hf₂' := hf₂ (BinOp.eq.eval ((Operand.slot RT).eval f₁) ((Operand.imm (UInt64.ofNat sp.tag)).eval f₁))
  cases hsv : sp.split (s.denote env) with
  | inl x =>
    obtain ⟨htag, hpx⟩ := hx.1 x hsv
    have hA := arm_in (L := L) (k := k) (c := c + (Tick.match_ (width t)).cost κ) eP ihP H x hLp hls
      hf₂' henv₁ (hfe₂ _) (by rw [rd_slice _ _ _ _ _ hLp]; exact hpx) hC.1 H.restr.1 H.lawful.2.1
      H.frozen.1 (H.hole.push _ rfl fun _ _ h => h.2.1) (by omega) (hs.1 x hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
    exact (MSim.tick H.run (hpre hp (MSim.runs H.run (Runs.bin _ _ _ _ _ _) (hf₂'.trans hf₁.symm)
      (fun _ _ => rfl) (MSim.ite_t H.run (by rw [hRX, ite_eq_left_of_eq_true _ _ (eq_true htag)]; decide) hA)))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, width, Ty.words, Tl.hb_up])
  | inr y =>
    obtain ⟨htag, hqy⟩ := hx.2 y hsv
    obtain ⟨f₃, h₃, hf₃, hr₃, hm₃, hok⟩ := restCode_runs (κ := κ) (ω := ω) (L := L) sp.mode sp.tag
      (scrutLoc s ρ n) (payloadOff t.data.shape) (n + t.size) q.size t.size bp (h := h₁) hf₂' hLs (by omega) (by omega)
      (by revert hLm; cases sp.mode <;> simp only <;> omega) (by omega)
    have hA := case_arm (k := k) (c := c + (Tick.match_ (width t)).cost κ) eQ ihQ H hC.2 H.restr.2
      H.lawful.2.2 H.frozen.2 (H.hole.push _ rfl fun _ _ h => h.2.2) (Nat.le_add_right n t.size)
      (by omega) hf₂' hr₃ hf₃ hm₃ (hqy _ (rd_length _ _ _) hok) henv₁ (hfe₂ _) (hs.2 y hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)
    exact (MSim.tick H.run (hpre hp (MSim.runs H.run (Runs.bin _ _ _ _ _ _) (hf₂'.trans hf₁.symm)
      (fun _ _ => rfl) (MSim.ite_e H.run (by rw [hRX, ite_eq_right_of_eq_false _ _ (eq_false htag)]) hA)))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, width, Ty.words, Tl.hb_up])

end

end Millipede.Flat
