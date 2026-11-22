import Millipede.Compile.LowerCallRef

/-!
# Slices as a pointer and a length

A borrow of a slice, `&q[lo..lo+len]` or `&mut q[lo..lo+len]`, stores the address of element `lo`
and the length `len` in a 16-byte slot at the watermark, so a slice is a pointer and a length. The
view binder, of type `Ty.view T N`, is a reference binder whose storage is its extent: the first
`len · size` bytes from its address, which are the viewed run of the array. Nothing is copied when
the borrow begins or ends, and the proof rests on four facts:

* the binder's value `vview arr lo len` is represented by the array's bytes from element `lo` on,
  since its cells `0 … len-1` are the elements `lo … lo+len-1` and the others are empty;
* its elements are reached as cells `r[i]!`, whose obligation that the cell is full puts them
  inside the extent;
* a `&mut` slice is a hole of its lender that covers exactly the viewed elements, with the path
  `q.path ++ [dyn]`, and a place of the lender whose path does not overlap it does not overlap the
  array place `q` either, so it lies outside the hole;
* when the borrow ends, the bytes of the viewed elements are the handed-back view's cells, all of
  which are full by the hand-back condition `Exp.HB`, so the memory represents the write-back
  `vunview arr lo len v`.

The design of slices is described in doc/design/memory.md.
-/

namespace Millipede.Flat

/-! ## A slice place

`SliceAt p … len A Hl` collects what a borrow of a slice place `p` needs in a given state. The place
is `q[lo..lo+len]` of an array or of a view variable. Its address code computes the address `A` of
its first element, and its `len` elements lie inside one piece of its root's storage, below the
watermark, and represent its view. `Hl` is the hole that a `&mut` borrow of the place makes in its
root, a region that contains the elements and that every place the body may use avoids. Writing
back a view whose first `len` cells are full gives the write-back. The proofs for borrows are stated
once over `SliceAt`. -/

/-- The facts about a slice place, described above. -/
structure SliceAt {Γ : List Ty} {T : Ty} {N : Nat} (p : Place Γ (.view T N)) (len : Atom Γ .u64)
    (ρ : List Loc) (S : List SI) (W : List Bool) (n bp : Nat) (env : Env Γ) (h : Heap) (A : Nat)
    (Hl : Hole) : Prop where
  code : ∀ (κ : CostModel) (ω : Oracle) (L : Nat) (f : Frame), f BP = UInt64.ofNat bp →
    FEnvRel f env ρ → bp + n ≤ L → bp + n ≤ UInt64.size →
    ∃ f', Runs κ ω L (placeAddr p ρ) f h f' h ∧ f' BP = f BP ∧ f' RA = UInt64.ofNat A
  store : ∀ d, refStore p ρ d = sliceStore len ρ d
  lenNH : ∀ m, len = .var m → (S.getD m.idx default).hole = none
  hle : (len.denote env).toNat ≤ N
  bound : A + (len.denote env).toNat * T.size ≤ bp + n
  holds : (S.getD p.root default).Holds p.rootTy A ((len.denote env).toNat * T.size)
  rep : ∀ m : Heap, (∀ x, x < bp + n → m (UInt64.ofNat x) = h (UInt64.ofNat x)) →
    Data.reprBytes (α := Slots T.carrier N) (p.get env) (rd m A (N * T.size))
  vok : ViewOK (.slots T N) (p.get env) ((len.denote env).toNat * T.size)
  full : ∀ k, k < (len.denote env).toNat → (p.get env : Slots T.carrier N).isFull k = true
  holePath : Hl.path = p.path
  holeIn : ∀ x, InR Hl.a Hl.len x → (S.getD p.root default).In p.rootTy x
  holeOK : HoleOK (S.getD p.root default) p.rootTy Hl
  elemsIn : ∀ x, InR A ((len.denote env).toNat * T.size) x → InR Hl.a Hl.len x
  back : W.getD p.root false = true → bp + n ≤ UInt64.size → ∀ (m : Heap) (v : Slots T.carrier N),
    (∀ x, x < bp + n → ¬ InR A ((len.denote env).toNat * T.size) x →
      m (UInt64.ofNat x) = h (UInt64.ofNat x)) →
    (∀ k, k < (len.denote env).toNat → v.isFull k = true) → ∀ V : List UInt8,
    Data.reprBytes (α := Slots T.carrier N) v V →
    slice V 0 ((len.denote env).toNat * T.size) = rd m A ((len.denote env).toNat * T.size) →
    MEnvRel m bp (p.set env v) ρ S

section
variable {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ}
  {h : Heap}

/-- The slice `q[lo..lo+len]` of an array place, whose hole is the viewed elements. -/
theorem range_at (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (q : Place Γ (.arr T N)) (lo len : Atom Γ .u64) (hc : q.contig = true) (hL : q.Lawful)
    (hok : (Place.range q lo len).ok env) (hnh : (Place.range q lo len).NH S)
    (hns : (ρ.getD q.root default).isSlot = false) :
    SliceAt (.range q lo len) len ρ S W n bp env h (placeA q S env + (lo.denote env).toNat * T.size)
      ⟨placeA q S env + (lo.denote env).toNat * T.size, (len.denote env).toNat * T.size,
        q.path ++ [.dyn]⟩ := by
  obtain ⟨hokq, hfit⟩ := hok
  have hnhq := hnh.range
  have hpv := extOk_parent_arr q henv hl
  have hsz : (Ty.arr T N).size = N * T.size := rfl
  have hg := place_get q hc hL hokq henv hl hnhq.2 hpv hns
  obtain ⟨-, -, hat, hhold⟩ := place_at q hc hL hokq henv hl hpv
  have hinq := fun x (hx : InR (placeA q S env) (Ty.arr T N).size x) =>
    place_in q hc hL hokq henv hl hpv hx
  rw [hsz] at hg hhold hinq
  have hfit' : (lo.denote env).toNat * T.size + (len.denote env).toNat * T.size ≤ N * T.size := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hfit
  refine ⟨fun κ ω L f hf hfe hnL hnU => ?_, fun _ => rfl, hnh.1.2.2, by omega, by omega,
    hhold.sub (by omega) (by omega),
    fun m hm => vview_repr _ (by rw [rd_congr fun j hj => hm _ (by omega)]; exact hg.2) hfit,
    viewOK_of_slots (by omega) (vview_cells _ _ _ hfit),
    fun k hk => by simp [Place.get, vview_isFull]; omega, rfl,
    fun x hx => hinq x (by simp only [InR] at hx ⊢; omega),
    holeOK_range q env _ _ _ _ hc hL hokq (hl.root q).ok hat hfit, fun _ h => h,
    fun hW hbn m v hm hfull V hV hVm => ?_⟩
  · obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) q hc hf henv hfe hl
      hnhq.1 hL (q.notPair_of_ty hl (arr_not_prod T N)) hnL hnU
    obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) lo T.size _
      (hb₁.trans hf) ha₁ henv (hfe.keep hr₁.keep) hl hnh.1.2.1 hnL hnU
    exact ⟨f₂, Runs.seq hr₁ hr₂, hb₂.trans hb₁, ha₂⟩
  · have hrep := vunview_repr (q.get env) v (h := h) (m := m) hfit hg.2 hfull V hV hVm
      (fun i hi hn => hm _ (by omega) (fun hin => hn (by unfold InR at hin ⊢; omega)))
    exact place_set q hc hL hokq henv hl hW hbn hpv hns m _
      (fun x hx hn => hm x hx fun hin => hn (by rw [hsz]; unfold InR at hin ⊢; omega)) hrep

/-- The sub-slice `s[lo..lo+len]` of a view variable, whose hole is its elements. The hole's
guarantee holds trivially, because the path `[dyn]` overlaps every place of the variable. -/
theorem rangeS_at (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    (m : Mem (.slots T N) Γ) (lo len : Atom Γ .u64)
    (hok : (Place.rangeS m lo len).ok env) (hnh : (Place.rangeS m lo len).NH S) :
    SliceAt (.rangeS m lo len) len ρ S W n bp env h
      ((S.getD m.idx default).A + (lo.denote env).toNat * T.size)
      ⟨(S.getD m.idx default).A + (lo.denote env).toNat * T.size, (len.denote env).toNat * T.size,
        [.dyn]⟩ := by
  have hH := hole_none_of_dyn (p := Place.rangeS m lo len) rfl hnh.2
  obtain ⟨hle, hb, hhold, -, hvok⟩ := rangeS_facts hl henv m lo len hok hH
  refine ⟨fun κ ω L f hf hfe hnL hnU => ?_, fun _ => rfl, hnh.1.2, hle, hb, hhold,
    fun m' hm => (rangeS_facts hl (henv.above hl hm) m lo len hok hH).2.2.2.1, hvok,
    fun k hk => sview_full _ hok.1 hok.2 hk, rfl, fun x hx => hhold.In hx, ?_, fun _ h => h,
    fun hW hbn m' v hm hfull V hV hVm => rangeS_set_rel hl henv hbn m lo len hok hH hW m' v hfull V
      hV hVm hm⟩
  · obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) (.var m) rfl hf henv
      hfe hl trivial trivial ((Place.var m).notPair_of_ty hl (slots_not_prod T N)) hnL hnU
    obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) lo T.size _
      (hb₁.trans hf) ha₁ henv (hfe.keep hr₁.keep) hl hnh.1.1 hnL hnU
    exact ⟨f₂, Runs.seq hr₁ hr₂, hb₂.trans hb₁, ha₂⟩
  · intro _ _ q _ _ _ _ _ hov
    rw [Sel.overlap_dyn_left] at hov; cases hov

end

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- The code of a slice reference computes the address of the first element and then stores the
address and the length in the 16-byte slot. No byte below the watermark changes, and the slot's
first word is the address. -/
theorem slice_ref_runs {Γ : List Ty} {t₀ : Ty} {e₀ : Exp Γ t₀} {tm : Tl} {W : List Bool}
    {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World}
    {T : Ty} {N : Nat} {p : Place Γ (.view T N)} {len : Atom Γ .u64} {A : Nat} {Hl : Hole}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f h w) (hP : SliceAt p len ρ S W n bp env h A Hl)
    (hL : bp + n + 16 ≤ L) (hU : bp + n + 16 ≤ UInt64.size) :
    ∃ f₁ f₂ H₂, Runs κ ω L (placeAddr p ρ) f h f₁ h ∧ f₁ BP = f BP ∧
      Runs κ ω L (refStore p ρ n) f₁ h f₂ H₂ ∧ f₂ BP = f BP ∧
      (∀ x, x < bp + n → H₂ (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      decodeLE (rd H₂ (bp + n) 8) = UInt64.ofNat A := by
  obtain ⟨f₁, hr₁, hb₁, ha₁⟩ := hP.code κ ω L f H.bpOk H.sl.rel (by omega) (by omega)
  have hfb₁ : f₁ BP = UInt64.ofNat bp := hb₁.trans H.bpOk
  have hst := store_ptr (κ := κ) (ω := ω) (L := L) (h := h) (n := n) hfb₁ ha₁ (by omega) (by omega)
  generalize hH₁ : wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat) = H₁ at hst
  have hH₁o : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx => by
    rw [← hH₁]; exact wr_out (by simp; omega) (by omega) (by simp; omega)
  have hlw := atomWord_u64 (κ := κ) (ω := ω) (L := L) len RX hfb₁ (H.envRel.above H.lay hH₁o)
    (H.sl.rel.keep hr₁.keep) H.lay hP.lenNH (by omega) (by omega)
  have hfb₂ : (f₁.set RX (len.denote env)) BP = UInt64.ofNat bp := by
    rw [Frame.set_ne _ _ (by decide)]; exact hfb₁
  have hst2 := store_word (κ := κ) (ω := ω) (L := L) (h := H₁) (m := n + 8) RX (len.denote env)
    hfb₂ (by simp) (by omega) (by omega)
  have hH₂₁ : ∀ x, x < bp + (n + 8) →
      wr H₁ (bp + (n + 8)) (natBytes 8 (len.denote env).toNat) (UInt64.ofNat x) = H₁ (UInt64.ofNat x) :=
    fun x hx => wr_out (by simp; omega) (by omega) (by simp; omega)
  refine ⟨f₁, _, _, hr₁, hb₁, by rw [hP.store n]; exact Runs.seq hst (Runs.seq hlw hst2),
    hfb₂.trans H.bpOk.symm, fun x hx => (hH₂₁ x (by omega)).trans (hH₁o x hx), ?_⟩
  rw [rd_congr fun j hj => hH₂₁ _ (by omega), ← hH₁]; exact ptr_bytes h bp n A (by omega)

/-- `let x := { let r = &p; body }; k` for a slice place `p`. The binder's 16-byte slot holds the
address of the first element and the length, and its storage is the viewed run of elements. -/
theorem msound_borrowShr_slice {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (p : Place Γ (.view T N)) (len : Atom Γ .u64) (body : Exp (Ty.view T N :: Γ) u)
    (k : Exp (u :: Γ) v) (hW16 : p.slotW = 16) (hloc : ∀ o, p.refLoc o = .ref o)
    (hVb : body.VSafe 0 .none = true)
    (hP : ∀ {W ρ S n bp env h}, Lay bp n Γ ρ S W → MEnvRel h bp env ρ S → p.ok env → p.NH S →
      p.Lawful → (ρ.getD p.root default).isSlot = false → ∃ A Hl, SliceAt p len ρ S W n bp env h A Hl)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr p body k) := by
  refine msound_borrowShr_of p body k hW16 hloc (fun o => .inl (hloc o ▸ rfl))
    (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, hW16] at hb hbL
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨A, Hl, hP⟩ := hP H.lay H.envRel H.safe.1
    (p.nh_of .read fun i H' h' => (H.hole i H' h').1) H.lawful.1 hns
  obtain ⟨f₁, f₂, H₂, hr₁, hb₁, hst, hb₂, hH₂o, hptr⟩ := slice_ref_runs (κ := κ) (ω := ω) (L := L)
    H hP (by omega) (by omega)
  have hle := hP.hle; have hbd := hP.bound; have hhold := hP.holds; have hvok := hP.vok
  generalize (len.denote env).toNat = len' at hle hbd hhold hvok
  refine ⟨f₂, H₂, ⟨A, none, some (len' * T.size), none⟩, ⟨⟨f₁, hr₁, hb₁, hst, hb₂⟩, hH₂o,
    Lay.pushRefE (Ty.view T N) false (some (len' * T.size)) H.lay.noW (Nat.le_refl _) (by omega)
      (by rw [sz_view hle]; exact hbd)
      (by rw [sz_view hle]; exact H.lay.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hhold))
      (fun e => by cases e), rfl,
    ⟨fun _ => VarRel.of_exact' (hP.rep _ hH₂o) (fun e' he' => by cases he'; exact hvok) rfl, hptr,
      H.envRel.above H.lay hH₂o⟩⟩, .inr hVb⟩

/-- `let x := { let r = &mut p; body }; k` for a slice place `p`. The binder holds the address of
the first element and the length, and the body writes the viewed elements in place, as a hole of
the lender, and hands the view back in place. When the borrow ends, all the view's cells are full
by the hand-back condition, so the memory represents the write-back. -/
theorem msound_borrowMut_slice {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (p : Place Γ (.view T N)) (len : Atom Γ .u64)
    (body : Exp (Ty.view T N :: Γ) (.pair u (Ty.view T N))) (k : Exp (u :: Γ) v)
    (hW16 : p.slotW = 16) (hloc : ∀ o, p.refLoc o = .ref o)
    (hCb : body.Conf (borrowTl u (Ty.view T N)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.view T N)) = true) (hHB : body.HB 0 = true)
    (hP : ∀ {W ρ S n bp env h}, Lay bp n Γ ρ S W → MEnvRel h bp env ρ S → p.ok env → p.NH S →
      p.Lawful → (ρ.getD p.root default).isSlot = false → ∃ A Hl, SliceAt p len ρ S W n bp env h A Hl)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut p body k) := by
  refine msound_borrowMut_of p body k hW16 hloc (fun o => .inl (hloc o ▸ rfl)) hCb
    (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, hW16] at hb hbL
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨A, Hl, hP⟩ := hP H.lay H.envRel H.safe.1
    (p.nh_of .write fun i H' h' => (H.hole i H' h').1) H.lawful.1 hns
  have hback : ∀ j, j < (len.denote env).toNat →
      (body.exec ω κ .split (.cons (p.get env) env) w).val.2.isFull j = true := by
    rw [Exp.exec_val]; exact hb_backOk ω body hHB _ _ hP.full env w
  obtain ⟨f₁, f₂, H₂, hr₁, hb₁, hst, hb₂, hH₂o, hptr⟩ := slice_ref_runs (κ := κ) (ω := ω) (L := L)
    H hP (by omega) (by omega)
  have hle := hP.hle; have hbd := hP.bound; have hhold := hP.holds; have hvok := hP.vok
  have hel := hP.elemsIn; have hpb := hP.back
  generalize (len.denote env).toNat = len' at hle hbd hhold hvok hel hpb hback
  have hrA : RefsAway bp A (len' * T.size) Γ ρ :=
    H.lay.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hhold)
  obtain ⟨hlh, hvis⟩ := H.lay.lend p Hl hP.holeIn hP.holeOK H.restr.1 _ (fun x hx => hhold.In hx)
    hel (fun x hx => hrA.not_refSlot hx)
  refine ⟨f₂, H₂, ⟨A, none, some (len' * T.size), none⟩, Hl, ⟨⟨f₁, hr₁, hb₁, hst, hb₂⟩, hH₂o,
    Lay.pushRefE (Ty.view T N) true (some (len' * T.size)) hlh (Nat.le_refl _) (by omega)
      (by rw [sz_view hle]; exact hbd) (by rw [sz_view hle]; exact hrA)
      (fun _ => by rw [sz_view hle]; exact hvis), rfl,
    ⟨fun _ => VarRel.of_exact' (hP.rep _ hH₂o) (fun e' he' => by cases he'; exact hvok) rfl, hptr,
      (H.envRel.above H.lay hH₂o).setHole _ _ ((H.lay.root p).2.2.1 H.restr.1)⟩⟩,
    hP.holePath, .inr hVb,
    fun x hx => InW.place p H.restr.1 (hhold.In (by rw [SI.In_mk, sz_view hle] at hx; exact hx))
      H.lay.length.2, fun m bs hm hv hsc => ?_⟩
  rw [rdS_none (s := ⟨A, none, some (len' * T.size), none⟩) rfl,
    show (SI.mk A none (some (len' * T.size)) none).lim (Ty.view T N).size = len' * T.size from
      sz_view hle] at hsc
  have hlN : 0 + len' * T.size ≤ (Ty.view T N).size := by
    rw [Nat.zero_add]; exact Nat.mul_le_mul_right T.size hle
  exact hpb H.restr.1 (by omega) m _ (fun x hx hn => hm x hx (by rw [SI.In_mk, sz_view hle]; exact hn))
    hback _ hv (by rw [slice_slice _ _ _ _ _ hlN, Nat.add_zero]; exact hsc)

/-- `let x := { let r = &q[lo..lo+len]; body }; k`. -/
theorem msound_borrowShr_range {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (q : Place Γ (.arr T N)) (lo len : Atom Γ .u64) (body : Exp (Ty.view T N :: Γ) u)
    (k : Exp (u :: Γ) v) (hc : q.contig = true) (hVb : body.VSafe 0 .none = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr (.range q lo len) body k) :=
  msound_borrowShr_slice _ len body k rfl (fun _ => rfl) hVb
    (fun hl henv hok hnh hL hns => ⟨_, _, range_at hl henv q lo len hc hL hok hnh hns⟩) ihb ihk

/-- `let x := { let r = &mut q[lo..lo+len]; body }; k`. The hole of the lender covers exactly the
viewed elements, and when the borrow ends the memory represents `vunview`. -/
theorem msound_borrowMut_range {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (q : Place Γ (.arr T N)) (lo len : Atom Γ .u64) (body : Exp (Ty.view T N :: Γ) (.pair u (Ty.view T N)))
    (k : Exp (u :: Γ) v) (hc : q.contig = true) (hCb : body.Conf (borrowTl u (Ty.view T N)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.view T N)) = true) (hHB : body.HB 0 = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut (.range q lo len) body k) :=
  msound_borrowMut_slice _ len body k rfl (fun _ => rfl) hCb hVb hHB
    (fun hl henv hok hnh hL hns => ⟨_, _, range_at hl henv q lo len hc hL hok hnh hns⟩) ihb ihk

/-- `let x := { let r = &s[lo..lo+len]; body }; k` for a view variable `s`. The binder holds `s`'s
address plus `lo · size` and the length, and nothing is copied. -/
theorem msound_borrowShr_rangeS {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (m : Mem (.slots T N) Γ) (lo len : Atom Γ .u64) (body : Exp (Ty.view T N :: Γ) u)
    (k : Exp (u :: Γ) v) (hVb : body.VSafe 0 .none = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr (.rangeS m lo len) body k) :=
  msound_borrowShr_slice _ len body k rfl (fun _ => rfl) hVb
    (fun hl henv hok hnh _ _ => ⟨_, _, rangeS_at hl henv m lo len hok hnh⟩) ihb ihk

/-- `let x := { let r = &mut s[lo..lo+len]; body }; k` for a view variable `s`. The body writes the
sub-slice's elements in place, and when the borrow ends the memory represents `sunview`. -/
theorem msound_borrowMut_rangeS {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty}
    (m : Mem (.slots T N) Γ) (lo len : Atom Γ .u64)
    (body : Exp (Ty.view T N :: Γ) (.pair u (Ty.view T N))) (k : Exp (u :: Γ) v)
    (hCb : body.Conf (borrowTl u (Ty.view T N)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.view T N)) = true) (hHB : body.HB 0 = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut (.rangeS m lo len) body k) :=
  msound_borrowMut_slice _ len body k rfl (fun _ => rfl) hCb hVb hHB
    (fun hl henv hok hnh _ _ => ⟨_, _, rangeS_at hl henv m lo len hok hnh⟩) ihb ihk

end

end Millipede.Flat
