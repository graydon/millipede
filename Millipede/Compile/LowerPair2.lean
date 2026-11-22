import Millipede.Compile.LowerGuard

/-!
# Reading and writing the two elements `p[i], p[j]`

The lowered code reads a two-element place element by element. `RA` and `RB` both start at the
array's address, each is advanced to its element by `i * size` or `j * size`, and the two elements
are copied to the two fields of the destination pair. Each element is the one that the index place
`p[i]!` denotes, so the layout of the pair finishes the proof.

To write `p[i], p[j]`, the code computes both element addresses before either element is written,
because an index variable may live inside the array's root variable, and then copies the two
components to the two elements. The two writes do not overlap because of the obligation `i ≠ j`,
so the array's bytes afterwards represent `vset (vset a i x) j y`.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem fieldOffset_zero (fs : List Shape) : Shape.fieldOffset fs 0 = 0 := by
  cases fs with
  | nil => rfl
  | cons s ss => simp [Shape.fieldOffset, Shape.prodOffsets, alignUp_zero]

/-- The components of a represented pair. -/
theorem pair_repr {u t : Ty} (x : (Ty.pair u t).carrier) (bs : List UInt8)
    (h : Data.reprBytes x bs) :
    Data.reprBytes x.1 (slice bs 0 u.size) ∧ Data.reprBytes x.2 (slice bs (sndOff u t) t.size) := by
  obtain ⟨_, hr⟩ := h
  have h0 := Fields.reprAt_field [⟨Prod.fst⟩, ⟨Prod.snd⟩] x bs hr 0 (by simp)
  have h1 := Fields.reprAt_field [⟨Prod.fst⟩, ⟨Prod.snd⟩] x bs hr 1 (by simp)
  refine ⟨?_, h1⟩
  rw [fieldOffset_zero] at h0; exact h0

theorem fst_le (u t : Ty) : u.size ≤ (Ty.pair u t).size := by
  have := Shape.fieldOffset_add_size_le [Data.shape u.carrier, Data.shape t.carrier] 0 (by simp)
  rw [fieldOffset_zero, Nat.zero_add] at this; exact this

/-- Advance the address register `R` to element `i` by `R += i * sz`, then run `rest`. -/
theorem elemStep_runs {Γ : List Ty} (i : Atom Γ .u64) {ρ : List Loc} {S : List SI}
    {W : List Bool} {bp nn : Nat} {env : Env Γ}
    {f : Frame} {h : Heap} (R sz A : Nat) (hRX : R ≠ RX) (hRB : R ≠ BP)
    (hf : f BP = UInt64.ofNat bp) (hA : f R = UInt64.ofNat A) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ)
    (hl : Lay bp nn Γ ρ S W) (hnh : ∀ m, i = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + nn ≤ L) (hnU : bp + nn ≤ UInt64.size) (hRF : R < FR)
    {rest : Stmt} {P : Frame → Heap → Prop}
    (k : ∀ f₃, f₃ BP = f BP → f₃ R = UInt64.ofNat (A + (i.denote env).toNat * sz) →
      (∀ x, x ≠ R → x ≠ RX → f₃ x = f x) → FEnvRel f₃ env ρ →
      ∃ f' h', Runs κ ω L rest f₃ h f' h' ∧ P f' h') :
    ∃ f' h', Runs κ ω L (.seq (atomWord i ρ RX) (.seq (.bin .mul RX (.slot RX)
        (.imm (UInt64.ofNat sz))) (.seq (.bin .add R (.slot R) (.slot RX)) rest))) f h f' h' ∧
      P f' h' := by
  have hr₁ := atomWord_u64 (κ := κ) (ω := ω) i RX hf henv hfe hl hnh hnL hnU
  let f₁ := f.set RX (i.denote env)
  have hr₂ := Runs.bin (κ := κ) (ω := ω) (L := L) .mul RX (.slot RX) (.imm (UInt64.ofNat sz)) f₁ h
  let f₂ := f₁.set RX (BinOp.mul.eval ((Operand.slot RX).eval f₁) ((Operand.imm (UInt64.ofNat sz)).eval f₁))
  have hr₃ := Runs.bin (κ := κ) (ω := ω) (L := L) .add R (.slot R) (.slot RX) f₂ h hRF
  let f₃ := f₂.set R (BinOp.add.eval ((Operand.slot R).eval f₂) ((Operand.slot RX).eval f₂))
  obtain ⟨f', h', hr, hP⟩ := k f₃ (by simp [f₃, f₂, f₁, Frame.set, Ne.symm hRB])
    (by
      simp only [f₃, f₂, f₁, Frame.set_same, eval_slot, eval_imm, BinOp.eval]
      rw [Frame.set_ne _ _ hRX, Frame.set_ne _ _ hRX, hA, ofNat_toNat_mul, ofNat_add_ofNat])
    (fun x h1 h2 => by simp [f₃, f₂, f₁, Frame.set, h1, h2])
    (hfe.keep (Runs.seq hr₁ (Runs.seq hr₂ hr₃)).keep)
  exact ⟨f', h', Runs.seq hr₁ (Runs.seq hr₂ (Runs.seq hr₃ hr)), hP⟩

/-- The code that reads `p[i], p[j]` to a destination `d` away from the variables writes only the
destination, with bytes that represent the pair of elements. -/
theorem placeRead_pair2_runs {Γ : List Ty} {t : Ty} {n : Nat} [Inhabited t.carrier]
    (p : Place Γ (.arr t n)) (i j : Atom Γ .u64) {ρ : List Loc} {S : List SI} {W : List Bool}
    {n' d bp : Nat} {env : Env Γ}
    {f : Frame} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hs : (Place.pair2 p i j).ok env) (hnh : (Place.pair2 p i j).NH S) (hl : Lay bp n' Γ ρ S W)
    (hd : Away bp d (Ty.pair t t).size Γ ρ S)
    (hdn : d + (Ty.pair t t).size ≤ n') (hb : bp + n' ≤ UInt64.size)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hns : (ρ.getD p.root default).isSlot = false) (hbL : bp + n' ≤ L) :
    ∃ f' h', Runs κ ω L (placeRead (.pair2 p i j) ρ d) f h f' h' ∧ f' BP = f BP ∧
      (∀ a, a < UInt64.size → ¬ (bp + d ≤ a ∧ a < bp + d + (Ty.pair t t).size) →
        h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      Data.reprBytes ((Place.pair2 p i j).get env) (rd h' (bp + d) (Ty.pair t t).size) := by
  simp only [Place.ok] at hs
  obtain ⟨hok, hi, hj, _⟩ := hs
  have hso : sndOff t t + t.size ≤ (Ty.pair t t).size := sndOff_add_le t t
  have hfo := fst_le t t
  have hsz : t.size ≤ sndOff t t := by
    show t.size ≤ alignUp (alignUp 0 (Data.shape t.carrier).align + t.size)
      (Data.shape t.carrier).align
    rw [alignUp_zero, Nat.zero_add]; exact le_alignUp _ _ (Shape.align_pos _)
  let PS := (Ty.pair t t).size
  let qi : Place Γ t := .index p i
  let qj : Place Γ t := .index p j
  have hgi := place_get qi hc hL ⟨hok, hi⟩ henv hl hnh.2 (Or.inr rfl) hns
  have hgj := place_get qj hc hL ⟨hok, hj⟩ henv hl hnh.2 (Or.inr rfl) hns
  have hAi : placeA qi S env = placeA p S env + (i.denote env).toNat * t.size := by
    simp only [placeA, qi]
  have hAj : placeA qj S env = placeA p S env + (j.denote env).toNat * t.size := by
    simp only [placeA, qj]
  -- the elements lie away from the destination
  have hdi := disj_of_pt2 fun x h1 h2 =>
    Away.place qi hd hl henv hc hL ⟨hok, hi⟩ (Or.inr rfl) h1 h2
  have hdj := disj_of_pt2 fun x h1 h2 =>
    Away.place qj hd hl henv hc hL ⟨hok, hj⟩ (Or.inr rfl) h1 h2
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc hf henv hfe hl
    hnh.1.1 hL (p.notPair_of_ty hl (arr_not_prod t n)) hbL hb
  have hgi2 := hgi.2
  have hgj2 := hgj.2
  have hgi1 := hgi.1
  have hgj1 := hgj.1
  clear hgi hgj
  generalize placeA qi S env = Ai at *
  generalize placeA qj S env = Aj at *
  have hr₂ := Runs.mov (κ := κ) (ω := ω) (L := L) RB (.slot RA) f₁ h
  let f₂ := f₁.set RB ((Operand.slot RA).eval f₁)
  have hb₂ : f₂ BP = UInt64.ofNat bp := by simp [f₂, Frame.set, hb₁, hf]
  have ha₂ : f₂ RA = UInt64.ofNat (placeA p S env) := by simp [f₂, Frame.set, ha₁]
  have hB₂ : f₂ RB = UInt64.ofNat (placeA p S env) := by simp [f₂, ha₁]
  let H₄ := wr h (bp + d) (rd h (Ai) t.size)
  let H₆ := wr H₄ (bp + (d + sndOff t t)) (rd H₄ (Aj) t.size)
  have hH₄ : ∀ x, x < UInt64.size → ¬ (bp + d ≤ x ∧ x < bp + d + t.size) →
      H₄ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx hn =>
    wr_out (by simp; omega) hx (by simp; omega)
  have hrdj : rd H₄ (Aj) t.size = rd h (Aj) t.size :=
    rd_congr fun x hx => hH₄ _ (by omega) (by omega)
  obtain ⟨f₆, h₆, hr, hf₆, hh₆⟩ := elemStep_runs (κ := κ) (ω := ω) (P := fun f' h' =>
      f' BP = UInt64.ofNat bp ∧ h' = H₆) i RA t.size (placeA p S env) (by decide) (by decide)
      hb₂ ha₂ henv (hfe.keep (Runs.seq hr₁ hr₂).keep) hl hnh.1.2.1 hbL hb (by decide)
      (fun f₃ hb₃ ha₃ hx₃ hfe₃ => by
    rw [← hAi] at ha₃
    have hB₃ : f₃ RB = UInt64.ofNat (placeA p S env) := (hx₃ RB (by decide) (by decide)).trans hB₂
    obtain ⟨f₄, hf₄, hr₄⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot RA) (.slot BP) (by decide)
      (by decide) t.size 0 d (Ai) bp f₃ h ha₃ (hb₃.trans hb₂) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [Nat.add_zero] at hr₄
    have hb₄ : f₄ BP = UInt64.ofNat bp := (hf₄ BP (by decide)).trans (hb₃.trans hb₂)
    have hB₄ : f₄ RB = UInt64.ofNat (placeA p S env) := (hf₄ RB (by decide)).trans hB₃
    obtain ⟨f₆, h₆, hr₆, hP⟩ := elemStep_runs (κ := κ) (ω := ω) (h := H₄) (P := fun f' h' =>
        f' BP = UInt64.ofNat bp ∧ h' = H₆) j RB t.size (placeA p S env) (by decide)
        (by decide) hb₄ hB₄ (henv.wr_away hl (by omega) _
          (hd.sub (Nat.le_refl _) (by rw [rd_length]; omega)) (by rw [rd_length]; omega))
        (hfe₃.keep hr₄.keep) hl hnh.1.2.2 hbL hb (by decide) (fun f₅ hb₅ hB₅ _ _ => by
      rw [← hAj] at hB₅
      obtain ⟨f₆, hf₆, hr₆⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot RB) (.slot BP) (by decide)
        (by decide) t.size 0 (d + sndOff t t) (Aj) bp f₅ H₄ hB₅ (hb₅.trans hb₄)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [Nat.add_zero] at hr₆
      exact ⟨f₆, H₆, hr₆, (hf₆ BP (by decide)).trans (hb₅.trans hb₄), rfl⟩)
    exact ⟨f₆, h₆, Runs.seq hr₄ hr₆, hP⟩)
  subst hh₆
  have hrun : Runs κ ω L (placeRead (.pair2 p i j) ρ d) f h f₆ H₆ :=
    Runs.seq hr₁ (Runs.seq hr₂ hr)
  refine ⟨f₆, H₆, hrun, hf₆.trans hf.symm, ?_, ?_⟩
  · intro x hx hn
    show wr H₄ _ _ _ = _
    rw [wr_out (by simp; omega) hx (by simp; omega)]
    exact hH₄ x hx (by omega)
  · show Data.reprBytes _ (rd H₆ (bp + d) PS)
    refine pair_of_slices _ _ _ (rd_length _ _ _) ?_ ?_
    · rw [← rd_slice _ (bp + d) PS 0 t.size (by omega), Nat.add_zero]
      have e1 : rd H₆ (bp + d) t.size = rd H₄ (bp + d) t.size :=
        rd_congr fun x hx => show wr H₄ _ _ _ = _ from
          wr_out (by simp; omega) (by omega) (by simp; omega)
      have e2 := rd_wr h (bp + d) (rd h (Ai) t.size) (by simp; omega)
      rw [rd_length] at e2
      have e2' : rd H₄ (bp + d) t.size = rd h Ai t.size := e2
      rw [e1, e2']; exact hgi2
    · rw [← rd_slice _ (bp + d) PS _ t.size hso]
      have e2 : rd H₆ (bp + d + sndOff t t) t.size = rd H₄ Aj t.size := by
        have := rd_wr H₄ (bp + (d + sndOff t t)) (rd H₄ Aj t.size) (by simp; omega)
        rw [rd_length] at this
        rw [Nat.add_assoc]; exact this
      rw [e2, hrdj]; exact hgj2

/-- Reading `p[i], p[j]`. -/
theorem msound_read_pair2 {Γ : List Ty} {t : Ty} {n : Nat} [Inhabited t.carrier]
    (p : Place Γ (.arr t n)) (i j : Atom Γ .u64) (hc : p.contig = true) :
    MSoundAt κ ω (.read (.pair2 p i j)) := by
  refine .leaf fun L W ρ S n' d bp env k f h w c H => ?_
  have hdn := H.dn0; have hd := H.away0; have hb := H.nU; have hbL := H.nL
  obtain ⟨f', h', hr, hf', hout, hv⟩ :=
    placeRead_pair2_runs (κ := κ) (ω := ω) (L := L) p i j hc H.lawful H.safe
      ((Place.pair2 p i j).nh_of .read fun i' H' h' => H.hole i' H' h') H.lay hd hdn (by omega) H.bpOk H.envRel
      H.sl.rel (H.sl.ns_of_addr (by simp [Exp.noAddr, Place.root, Place.wordField])) (by omega)
  refine MSim.tick_done H.run hr rfl (by simp [Exp.exec, Tick.cost]) hf' hv ?_
  intro x hx; unfold Prot InR at hx
  exact hout x (by omega) (by omega)

theorem vset_getElem {α : Type} {N : Nat} (w : Vector α N) (a k : Nat) (x : α) (ha : a < N)
    (hk : k < N) : (vset w a x)[k] = if a = k then x else w[k] := by
  simp only [vset, ha, dite_true]; exact Vector.getElem_set ha hk

theorem elem_bound {k N sz : Nat} (hk : k < N) : k * sz + sz ≤ N * sz := by
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk

/-- Writing `p[i], p[j]`: bytes that represent the two components, written over the two elements
and nowhere else, represent the environment in which the place holds the pair. -/
theorem place_set_pair2 {Γ : List Ty} {t : Ty} {N : Nat} [Inhabited t.carrier]
    (p : Place Γ (.arr t N)) (i j : Atom Γ .u64) {ρ : List Loc} {S : List SI} {W : List Bool}
    {n bp : Nat} {env : Env Γ}
    {h : Heap} (hc : p.contig = true) (hL : p.Lawful) (hok : (Place.pair2 p i j).ok env)
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hW : W.getD p.root false = true)
    (hns : (ρ.getD p.root default).isSlot = false)
    (hbn : bp + n ≤ UInt64.size) (h' : Heap)
    (v : (Ty.pair t t).carrier)
    (hout : ∀ a, a < bp + n →
      ¬ (placeA p S env + (i.denote env).toNat * t.size ≤ a ∧
        a < placeA p S env + (i.denote env).toNat * t.size + t.size) →
      ¬ (placeA p S env + (j.denote env).toNat * t.size ≤ a ∧
        a < placeA p S env + (j.denote env).toNat * t.size + t.size) →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hvi : Data.reprBytes v.1 (rd h' (placeA p S env + (i.denote env).toNat * t.size) t.size))
    (hvj : Data.reprBytes v.2 (rd h' (placeA p S env + (j.denote env).toNat * t.size) t.size)) :
    MEnvRel h' bp ((Place.pair2 p i j).set env v) ρ S := by
  simp only [Place.ok] at hok
  obtain ⟨hok, hi, hj, hij⟩ := hok
  have hg := place_get p hc hL hok henv hl (fun H hH => by
    rw [(hl.root p).2.2.1 hW] at hH; cases hH) (extOk_parent_arr p henv hl) hns
  show MEnvRel h' bp (p.set env (vset (vset (p.get env) (i.denote env).toNat v.1)
    (j.denote env).toNat v.2)) ρ S
  generalize (i.denote env).toNat = a at *
  generalize (j.denote env).toNat = b at *
  have hsz : (Ty.arr t N).size = N * t.size := rfl
  have hab := elem_bound (sz := t.size) hi
  have hbb := elem_bound (sz := t.size) hj
  refine place_set p hc hL hok henv hl hW hbn (extOk_parent_arr p henv hl) hns h' _ (fun x hx hn => hout x (by omega) (by
      unfold InR at hn; omega) (by unfold InR at hn; omega))
    ⟨rd_length _ _ _, fun k hk => ?_⟩
  show Data.reprBytes _ (slice (rd h' (placeA p S env) (N * t.size)) (k * t.size) t.size)
  have hkb := elem_bound (sz := t.size) hk
  rw [← rd_slice _ _ _ _ _ hkb, vset_getElem _ _ _ _ hj hk, vset_getElem _ _ _ _ hi hk]
  split
  · rename_i e; subst e; exact hvj
  split
  · rename_i _ e; subst e; exact hvi
  rename_i hbk hak
  have e1 : rd h' (placeA p S env + k * t.size) t.size =
      rd h (placeA p S env + k * t.size) t.size := rd_congr fun x hx => by
    refine hout _ (by omega) ?_ ?_
    · have := elem_disj (sz := t.size) (x := k * t.size + x) (Ne.symm hak) (by omega) (by omega)
      omega
    · have := elem_disj (sz := t.size) (x := k * t.size + x) (Ne.symm hbk) (by omega) (by omega)
      omega
  rw [e1, rd_slice _ _ (N * t.size) _ _ hkb]
  exact hg.2.2 k hk

/-- The code that writes `p[i], p[j]` from a source above the watermark changes only the two
elements, and the result represents the environment in which the place holds the source's pair. -/
theorem placeWrite_pair2_runs {Γ : List Ty} {t : Ty} {N : Nat} [Inhabited t.carrier]
    (p : Place Γ (.arr t N)) (i j : Atom Γ .u64) {ρ : List Loc} {S : List SI} {W : List Bool}
    {n src bp : Nat}
    {env : Env Γ} {f : Frame} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : (Place.pair2 p i j).ok env) (hnh : (Place.pair2 p i j).NH S) (hl : Lay bp n Γ ρ S W)
    (hW : W.getD p.root false = true) (hsrc : n ≤ src)
    (hb : bp + src + (Ty.pair t t).size ≤ UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hns : (ρ.getD p.root default).isSlot = false) (v : (Ty.pair t t).carrier)
    (hv : Data.reprBytes v (rd h (bp + src) (Ty.pair t t).size))
    (hbL : bp + src + (Ty.pair t t).size ≤ L) :
    ∃ f' h', Runs κ ω L (placeWrite (.pair2 p i j) ρ src) f h f' h' ∧ f' BP = f BP ∧
      (∀ a, a < UInt64.size → ¬ (S.getD p.root default).In p.rootTy a →
        h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      MEnvRel h' bp ((Place.pair2 p i j).set env v) ρ S := by
  have hok' := hok
  simp only [Place.ok] at hok'
  obtain ⟨hokp, hi, hj, hij⟩ := hok'
  have hso : sndOff t t + t.size ≤ (Ty.pair t t).size := sndOff_add_le t t
  have hfo := fst_le t t
  have hsz : t.size ≤ sndOff t t := by
    show t.size ≤ alignUp (alignUp 0 (Data.shape t.carrier).align + t.size)
      (Data.shape t.carrier).align
    rw [alignUp_zero, Nat.zero_add]; exact le_alignUp _ _ (Shape.align_pos _)
  obtain ⟨hv1, hv2⟩ := pair_repr v _ hv
  rw [← rd_slice _ _ _ _ _ (by omega), Nat.add_zero] at hv1
  rw [← rd_slice _ _ _ _ _ hso] at hv2
  have hg := place_get p hc hL hokp henv hl (fun H hH => by
    rw [(hl.root p).2.2.1 hW] at hH; cases hH) (extOk_parent_arr p henv hl) hns
  have hsz' : (Ty.arr t N).size = N * t.size := rfl
  have hab := elem_bound (sz := t.size) hi
  have hbb := elem_bound (sz := t.size) hj
  have hset := place_set_pair2 p i j hc hL hok henv hl hW hns (by omega)
  have hregion : ∀ x, x < UInt64.size → ¬ (S.getD p.root default).In p.rootTy x →
      ¬ (placeA p S env ≤ x ∧ x < placeA p S env + N * t.size) := by
    intro x _ hn ⟨h1, h2⟩
    exact hn (place_in p hc hL hokp henv hl (extOk_parent_arr p henv hl) ⟨h1, h2⟩)
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc hf henv hfe hl
    hnh.1.1 hL (p.notPair_of_ty hl (arr_not_prod t N)) (by omega) (by omega)
  have hr₂ := Runs.mov (κ := κ) (ω := ω) (L := L) RB (.slot RA) f₁ h
  let f₂ := f₁.set RB ((Operand.slot RA).eval f₁)
  have hb₂ : f₂ BP = UInt64.ofNat bp := by simp [f₂, Frame.set, hb₁, hf]
  have ha₂ : f₂ RA = UInt64.ofNat (placeA p S env) := by simp [f₂, Frame.set, ha₁]
  have hB₂ : f₂ RB = UInt64.ofNat (placeA p S env) := by simp [f₂, ha₁]
  generalize hAi : placeA p S env + (i.denote env).toNat * t.size = Ai at hset
  generalize hAj : placeA p S env + (j.denote env).toNat * t.size = Aj at hset
  have hdisj : ∀ x, Ai ≤ x → x < Ai + t.size → ¬ (Aj ≤ x ∧ x < Aj + t.size) := by
    intro x h1 h2
    have := elem_disj (sz := t.size) (x := x - placeA p S env) hij (by omega) (by omega)
    omega
  let H₄ := wr h Ai (rd h (bp + src) t.size)
  let H₆ := wr H₄ Aj (rd H₄ (bp + (src + sndOff t t)) t.size)
  have hH₄ : ∀ x, x < UInt64.size → ¬ (Ai ≤ x ∧ x < Ai + t.size) →
      H₄ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx hn =>
    wr_out (by simp; omega) hx (by simp; omega)
  have hH₆ : ∀ x, x < UInt64.size → ¬ (Aj ≤ x ∧ x < Aj + t.size) →
      H₆ (UInt64.ofNat x) = H₄ (UInt64.ofNat x) := fun x hx hn =>
    wr_out (by simp; omega) hx (by simp; omega)
  have hrdj : rd H₄ (bp + (src + sndOff t t)) t.size = rd h (bp + (src + sndOff t t)) t.size :=
    rd_congr fun x hx => hH₄ _ (by omega) (by omega)
  obtain ⟨f₆, h₆, hr, hf₆, hh₆⟩ := elemStep_runs (κ := κ) (ω := ω) (L := L) (P := fun f' h' =>
      f' BP = UInt64.ofNat bp ∧ h' = H₆) i RA t.size (placeA p S env) (by decide) (by decide)
      hb₂ ha₂ henv (hfe.keep (Runs.seq hr₁ hr₂).keep) hl hnh.1.2.1 (by omega) (by omega) (by decide)
      (fun f₃ hb₃ ha₃ hx₃ hfe₃ => by
    rw [hAi] at ha₃
    have hB₃ : f₃ RB = UInt64.ofNat (placeA p S env) :=
      (hx₃ RB (by decide) (by decide)).trans hB₂
    obtain ⟨f₆, h₆, hr₆, hP⟩ := elemStep_runs (κ := κ) (ω := ω) (L := L) (P := fun f' h' =>
        f' BP = UInt64.ofNat bp ∧ h' = H₆) j RB t.size (placeA p S env) (by decide)
        (by decide) (hb₃.trans hb₂) hB₃ henv hfe₃ hl hnh.1.2.2 (by omega) (by omega) (by decide)
        (fun f₅ hb₅ hB₅ hx₅ _ => by
      rw [hAj] at hB₅
      have ha₅ : f₅ RA = UInt64.ofNat Ai := (hx₅ RA (by decide) (by decide)).trans ha₃
      have hb₅' : f₅ BP = UInt64.ofNat bp := hb₅.trans (hb₃.trans hb₂)
      obtain ⟨f₄, hf₄, hr₄⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot RA) (by decide)
        (by decide) t.size src 0 bp Ai f₅ h hb₅' ha₅ (by omega) (by omega) (Or.inr (by omega))
        (by omega) (by omega)
      rw [Nat.add_zero] at hr₄
      have hb₄ : f₄ BP = UInt64.ofNat bp := (hf₄ BP (by decide)).trans hb₅'
      have hB₄ : f₄ RB = UInt64.ofNat Aj := (hf₄ RB (by decide)).trans hB₅
      obtain ⟨f₆, hf₆, hr₆⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot RB) (by decide)
        (by decide) t.size (src + sndOff t t) 0 bp Aj f₄ H₄ hb₄ hB₄
        (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
      rw [Nat.add_zero] at hr₆
      exact ⟨f₆, H₆, Runs.seq hr₄ hr₆, (hf₆ BP (by decide)).trans hb₄, rfl⟩)
    exact ⟨f₆, h₆, hr₆, hP⟩)
  subst hh₆
  have hrun : Runs κ ω L (placeWrite (.pair2 p i j) ρ src) f h f₆ H₆ :=
    Runs.seq hr₁ (Runs.seq hr₂ hr)
  refine ⟨f₆, H₆, hrun, hf₆.trans hf.symm, ?_, ?_⟩
  · intro x hx hn
    have := hregion x hx hn
    rw [hH₆ x hx (by omega), hH₄ x hx (by omega)]
  · refine hset H₆ v (fun x hx h1 h2 => by rw [hH₆ x (by omega) h2, hH₄ x (by omega) h1]) ?_ ?_
    · have e : rd H₆ Ai t.size = rd H₄ Ai t.size :=
        rd_congr fun x hx => hH₆ _ (by omega) (hdisj _ (by omega) (by omega))
      have e2 := rd_wr h Ai (rd h (bp + src) t.size) (by simp; omega)
      rw [rd_length] at e2
      rw [e, e2]; exact hv1
    · have e2 := rd_wr H₄ Aj (rd H₄ (bp + (src + sndOff t t)) t.size) (by simp; omega)
      rw [rd_length] at e2
      rw [e2, hrdj, ← Nat.add_assoc]; exact hv2

/-- `p[i], p[j] := a; k` writes the pair to a temporary, copies its two components over the two
elements and continues. -/
theorem msound_assign_pair2 {Γ : List Ty} {t : Ty} {N : Nat} {u : Ty} [Inhabited t.carrier]
    (p : Place Γ (.arr t N)) (i j : Atom Γ .u64) (a : Atom Γ (.pair t t)) (k : Exp Γ u)
    (hc : p.contig = true) (ih : MSoundAt κ ω k) : MSoundAt κ ω (.assign (.pair2 p i j) a k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hCk : k.Conf tm = true := by have := H.conf; cases tm <;> simp_all [Exp.Conf]
  have hmt := Nat.le_max_left (Ty.pair t t).size k.memNeed
  have hmk := Nat.le_max_right (Ty.pair t t).size k.memNeed
  have hnh := (Place.pair2 p i j).nh_of .write fun i' H' h' => (H.hole i' H' h').2.1
  have hns : (ρ.getD p.root default).isSlot = false :=
    H.sl.ns_of_addr (by simp [Exp.noAddr, Place.root, Place.isVarAt, Place.wordField])
  obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := n) H.lay
    (H.lay.away (Nat.le_refl _)) (by omega) (by omega) H.bpOk H.envRel H.sl.rel
    (a.noHole fun i' H' h' => (H.hole i' H' h').1)
    (by omega) (by omega) (H.vs.atom a fun i h => by
      simp only [Exp.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.2)
  have hbB : bp + n + B.length ≤ UInt64.size := by omega
  have henv₁ : MEnvRel (wr h (bp + n) B) bp env ρ S :=
    H.envRel.above H.lay fun x hx => wr_out (by omega) (by omega) (by omega)
  have hfb₁ : f₁ BP = UInt64.ofNat bp := (hf₁ BP (by decide) (by decide)).trans H.bpOk
  have hB : rd (wr h (bp + n) B) (bp + n) (Ty.pair t t).size = B := by
    have := rd_wr h (bp + n) B (by omega); rwa [hBl] at this
  obtain ⟨f₂, H₂, hr₂, hb₂, hout₂, henv₂⟩ := placeWrite_pair2_runs (κ := κ) (ω := ω) (L := L) p i j
    hc H.lawful.1 H.safe.1 hnh H.lay H.restr.1 (Nat.le_refl _) (by omega) hfb₁ henv₁
    (H.sl.rel.keep hr₁.keep) hns (a.denote env) (by rw [hB]; exact hBr) (by omega)
  have hK := ih.app (H.cont hCk H.restr.2 H.lawful.2 H.frozen (H.hole.sub fun _ _ h => h.2.2)
    (hb₂.trans hfb₁) henv₂ ((H.sl.rel.keep fun x hx => (hr₂.keep x hx).trans (hr₁.keep x hx)).place_set
      (.pair2 p i j) hns _) H.safe.2
    (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)) kk
    (c + (Tick.mem (Place.pair2 p i j).depth (width (.pair t t))).cost κ)
  have hlen := H.lay.length
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run (MSim.runs H.run hr₁
    (hf₁ BP (by decide) (by decide)) (fun x hx => wr_out (by omega) (by unfold Prot at hx; omega)
      (by unfold Prot at hx; omega))
    (MSim.runs H.run hr₂ hb₂ (fun x hx => ?_) hK))).of_eq rfl rfl (by simp [Exp.exec, Tick.cost])
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hxn : x < bp + n := hx1
  exact hout₂ x (by omega) fun hin => hx3 (InW.place p H.restr.1 hin hlen.2)

end

end Millipede.Flat
