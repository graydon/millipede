import Millipede.Compile.LowerView

/-!
# References to the pair `p[i], p[j]`

A borrow `&p[i], p[j]` or `&mut p[i], p[j]` is a reference to two elements of one array at once.
Its binder or parameter lives at two addresses, one per element: its 16-byte slot holds the address
of element `i` and, 8 bytes on, the address of element `j`. Its run-time knowledge is a storage of
two pieces, the first component being element `i`'s bytes and the second element `j`'s. Nothing is
copied when the borrow begins or ends, because the body reads and writes the two elements in place
through `r.fst` and `r.snd`, and such a binder is used only through its fields.

The lender lends the whole array place `p`, since the borrow checker freezes every element, so its
hole is all of `p`'s bytes. The elements other than `i` and `j` are not the binder's storage and
the body cannot change them. When the borrow ends, the memory represents the write-back of the
pair.

The design of references is described in doc/design/memory.md.
-/

namespace Millipede.Flat

/-! ## The two-piece knowledge -/

theorem pair_ty_shape (T : Ty) : (Ty.pair T T).data.shape = .prod [T.data.shape, T.data.shape] :=
  rfl

theorem pair_ty_size (T : Ty) : (Ty.pair T T).size = 2 * T.size := by
  show (Ty.pair T T).data.shape.size = _; rw [pair_ty_shape]; exact (pairShape _).2

theorem sndOff_pair (T : Ty) : sndOff T T = T.size := by
  show Shape.fieldOffset [T.data.shape, T.data.shape] 1 = _; exact (pairShape _).1

/-- The run-time knowledge of a reference to the elements at `Ai` and `Aj`. -/
def pairSI (T : Ty) (Ai Aj : Nat) : SI := ⟨Ai, none, some (Ty.pair T T).size, some (T.size, Aj)⟩

theorem pairSI_pair {T : Ty} {Ai Aj : Nat} (hd : Disj Ai T.size Aj T.size) :
    PairSI (Ty.pair T T) (pairSI T Ai Aj) :=
  ⟨T.data.shape, Aj, pair_ty_shape T, rfl, rfl, hd⟩

theorem pairSI_sz (T : Ty) (Ai Aj : Nat) : (pairSI T Ai Aj).sz (Ty.pair T T) = 2 * T.size := by
  simp [pairSI, SI.sz, SI.lim, pair_ty_size]

theorem pairSI_at_lt {T : Ty} {Ai Aj k : Nat} (hk : k < T.size) : (pairSI T Ai Aj).at k = Ai + k := by
  simp [pairSI, SI.at, hk]

theorem pairSI_at_ge {T : Ty} {Ai Aj k : Nat} (hk : T.size ≤ k) :
    (pairSI T Ai Aj).at k = Aj + (k - T.size) := by
  simp [pairSI, SI.at, Nat.not_lt.mpr hk]

/-- The storage of a pair reference: its two elements. -/
theorem pairSI_In {T : Ty} {Ai Aj x : Nat} :
    (pairSI T Ai Aj).In (Ty.pair T T) x ↔ InR Ai T.size x ∨ InR Aj T.size x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [pairSI_sz] at hk
    by_cases h : k < T.size
    · left; rw [pairSI_at_lt h]; unfold InR; omega
    · right; rw [pairSI_at_ge (by omega)]; unfold InR; omega
  · rintro (h | h) <;> unfold InR at h
    · exact ⟨x - Ai, by rw [pairSI_sz]; omega, by rw [pairSI_at_lt (by omega)]; omega⟩
    · exact ⟨T.size + (x - Aj), by rw [pairSI_sz]; omega, by rw [pairSI_at_ge (by omega)]; omega⟩

theorem pairSI_Out {T : Ty} {Ai Aj a len : Nat} :
    (pairSI T Ai Aj).Out (Ty.pair T T) a len ↔ Disj a len Ai T.size ∧ Disj a len Aj T.size := by
  simp only [SI.Out, pairSI, pairSI_sz]
  rw [show (SI.mk Ai none (some (Ty.pair T T).size) (some (T.size, Aj))).sz (Ty.pair T T) =
    2 * T.size from pairSI_sz T Ai Aj]
  rw [show 2 * T.size - T.size = T.size by omega]

/-- The bytes of a pair reference's storage are its two elements' bytes. -/
theorem pairSI_rdS (h : Heap) (T : Ty) (Ai Aj : Nat) :
    rdS h (pairSI T Ai Aj) (2 * T.size) = rd h Ai T.size ++ rd h Aj T.size := by
  apply rdS_of_getD (by simp; omega)
  intro k hk
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : k < T.size
  · rw [pairSI_at_lt h1, List.getElem?_append_left (by simpa using h1), ← List.getD_eq_getElem?_getD,
      rd_getD _ _ _ _ h1]
  · rw [pairSI_at_ge (by omega), List.getElem?_append_right (by simp; omega), ← List.getD_eq_getElem?_getD,
      rd_length, rd_getD _ _ _ _ (by omega)]

theorem pairSI_Below {T : Ty} {Ai Aj L : Nat} (hi : Ai + T.size ≤ L) (hj : Aj + T.size ≤ L) :
    (pairSI T Ai Aj).Below (Ty.pair T T) L := by
  simp only [SI.Below, pairSI]
  rw [show (SI.mk Ai none (some (Ty.pair T T).size) (some (T.size, Aj))).sz (Ty.pair T T) =
    2 * T.size from pairSI_sz T Ai Aj]
  omega

/-! ## Pushing a pair reference binder -/

/-- A pair reference binder for the disjoint elements at `Ai` and `Aj` below the watermark, with its
16-byte slot at `o ≥ n`. The layout extends when every pointer slot is away from both elements and,
if the binder is writable, neither element is any variable's visible storage. -/
theorem Lay.pushRef2 {bp n : Nat} (T : Ty) (b : Bool) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} {o m Ai Aj : Nat} (hl : Lay bp n Γ ρ S (Flat.noW W)) (ho : n ≤ o)
    (hom : o + 16 ≤ m) (hd : Disj Ai T.size Aj T.size)
    (hAi : Ai + T.size ≤ bp + n) (hAj : Aj + T.size ≤ bp + n)
    (hri : RefsAway bp Ai T.size Γ ρ) (hrj : RefsAway bp Aj T.size Γ ρ)
    (hw : b = true → ∀ x, (InR Ai T.size x ∨ InR Aj T.size x) → ¬ Vis bp Γ ρ S x) :
    Lay bp m (Ty.pair T T :: Γ) (.ref2 o :: ρ) (pairSI T Ai Aj :: S) (b :: Flat.noW W) := by
  refine ⟨⟨by simp [Loc.off, Loc.size]; omega, ⟨pairSI_pair hd, pairSI_Below (by omega) (by omega),
    pairSI_Out.2 ⟨by unfold Disj; omega, by unfold Disj; omega⟩⟩, fun _ => rfl,
    fun H h => by cases h⟩, ?_, hl.mono (by omega)⟩
  show CompatAll bp (Ty.pair T T) (.ref2 o) (pairSI T Ai Aj) b Γ ρ S (Flat.noW W)
  induction Γ generalizing ρ S W with
  | nil => trivial
  | cons t ts ih =>
    cases ρ with
    | nil => trivial
    | cons l ρ =>
      cases S with
      | nil => trivial
      | cons s' S =>
        have h1 := hl.1.slotLe
        have h2 := hl.1.below
        have hrest := hl.2.2
        rw [noW_tail] at hrest
        refine ⟨⟨Or.inr (show l.off + l.size t ≤ o by omega), (fun o' w e => ?_),
          (fun o' w e => pairSI_Out.2 ⟨hri.1 o' w e, hrj.1 o' w e⟩),
          (fun hb x hx hx' => ?_), (fun hb x hx hx' => ?_)⟩, ?_⟩
        · simp only [Loc.ptr, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact h2.out (by omega)
        · exact Classical.byContradiction fun hc =>
            hw hb x (pairSI_In.1 hx) (Or.inl ⟨hx', hc⟩)
        · rw [noW_headD] at hb; cases hb
        · rw [noW_tail]
          exact ih hrest hri.2 hrj.2 (fun hb x hx hv => hw hb x hx (Or.inr (Or.inr hv)))

/-! ## Passing the reference: two addresses -/

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- The address code of two elements `q[i], q[j]` of a contiguous place `q`, an array or a `Slots`
variable, puts element `i`'s address into `RA` and element `j`'s into `RB`. -/
theorem pairAddr_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} (hl : Lay bp n Γ ρ S W) {t' : Ty} (T : Ty) (q : Place Γ t') (i j : Atom Γ .u64)
    (f : Frame) (h : Heap) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ) (hc : q.contig = true) (hL : q.Lawful) (hnp : q.NotPair S) (hnq : q.IdxNH S)
    (hni : ∀ m, i = .var m → (S.getD m.idx default).hole = none)
    (hnj : ∀ m, j = .var m → (S.getD m.idx default).hole = none) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) :
    ∃ f', Runs κ ω L (pairAddrCode (placeAddr q ρ) i j ρ T.size) f h f' h ∧ f' BP = f BP ∧
      f' RA = UInt64.ofNat (placeA q S env + (i.denote env).toNat * T.size) ∧
      f' RB = UInt64.ofNat (placeA q S env + (j.denote env).toNat * T.size) := by
  obtain ⟨f₁, hr₁, hb₁, ha₁, -⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) q hc hf henv hfe hl hnq
    hL hnp hnL hnU
  have hr₂ := Runs.mov (κ := κ) (ω := ω) (L := L) RB (.slot RA) f₁ h
  let f₂ := f₁.set RB ((Operand.slot RA).eval f₁)
  have hb₂ : f₂ BP = UInt64.ofNat bp := by simp [f₂, Frame.set, hb₁, hf]
  have ha₂ : f₂ RA = UInt64.ofNat (placeA q S env) := by simp [f₂, Frame.set, ha₁]
  have hB₂ : f₂ RB = UInt64.ofNat (placeA q S env) := by simp [f₂, ha₁]
  obtain ⟨f₃, hr₃, hb₃, ha₃, hx₃⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) i T.size _ hb₂ ha₂
    henv (hfe.keep (Runs.seq hr₁ hr₂).keep) hl hni hnL hnU
  have hB₃ : f₃ RB = UInt64.ofNat (placeA q S env) := (hx₃ RB (by decide) (by decide)).trans hB₂
  have hfb₃ : f₃ BP = UInt64.ofNat bp := hb₃.trans hb₂
  have hr₄ := atomWord_u64 (κ := κ) (ω := ω) (L := L) j RX hfb₃ henv
    (hfe.keep (Runs.seq hr₁ (Runs.seq hr₂ hr₃)).keep) hl hnj hnL hnU
  let f₄ := f₃.set RX (j.denote env)
  have hr₅ := Runs.bin (κ := κ) (ω := ω) (L := L) .mul RX (.slot RX) (.imm (UInt64.ofNat T.size)) f₄ h
  let f₅ := f₄.set RX (BinOp.mul.eval ((Operand.slot RX).eval f₄) ((Operand.imm (UInt64.ofNat T.size)).eval f₄))
  have hr₆ := Runs.bin (κ := κ) (ω := ω) (L := L) .add RB (.slot RB) (.slot RX) f₅ h
  let f₆ := f₅.set RB (BinOp.add.eval ((Operand.slot RB).eval f₅) ((Operand.slot RX).eval f₅))
  refine ⟨f₆, Runs.seq hr₁ (Runs.seq hr₂ (Runs.seq hr₃ (Runs.seq hr₄ (Runs.seq hr₅ hr₆)))),
    by simp [f₆, f₅, f₄, Frame.set, hfb₃, hf], ?_, ?_⟩
  · simp only [f₆, f₅, f₄]
    rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), ha₃]
  · simp only [f₆, f₅, f₄, Frame.set_same, eval_slot, eval_imm, BinOp.eval]
    rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), hB₃, ofNat_toNat_mul,
      ofNat_add_ofNat]

/-- Storing the two addresses from `RA` and `RB` at `bp + d` and `bp + d + 8`. -/
theorem pairStore_runs {d bp Ai Aj : Nat} {f : Frame} {h : Heap}
    (hf : f BP = UInt64.ofNat bp) (ha : f RA = UInt64.ofNat Ai) (hb : f RB = UInt64.ofNat Aj)
    (hU : bp + d + 16 ≤ UInt64.size) (hLd : bp + d + 16 ≤ L) :
    ∃ h', Runs κ ω L (pairStore d) f h f h' ∧
      (∀ a, a < UInt64.size → ¬ InR (bp + d) 16 a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      decodeLE (rd h' (bp + d) 8) = UInt64.ofNat Ai ∧ decodeLE (rd h' (bp + d + 8) 8) = UInt64.ofNat Aj := by
  have hst₁ := store_word (κ := κ) (ω := ω) (L := L) (m := d) (h := h) RA _ hf ha (by omega) (by omega)
  have hst₂ := store_word (κ := κ) (ω := ω) (L := L) (m := d + 8)
    (h := wr h (bp + d) (natBytes 8 (UInt64.ofNat Ai).toNat)) RB _ hf hb (by omega) (by omega)
  refine ⟨_, Runs.seq hst₁ hst₂, fun a ha hn => ?_, ?_, ?_⟩
  · unfold InR at hn
    rw [wr_out (by simp; omega) ha (by simp; omega), wr_out (by simp; omega) ha (by simp; omega)]
  · rw [rd_congr fun k hk => wr_out (by simp; omega) (by omega) (by simp; omega)]
    exact ptr_bytes h bp d _ (by omega)
  · rw [show bp + d + 8 = bp + (d + 8) by omega]
    exact ptr_bytes _ bp (d + 8) _ (by omega)

end

/-- The value of a pair reference is represented by its two elements' bytes. -/
theorem pair_varRel {h : Heap} {T : Ty} {Ai Aj : Nat} {x y : T.carrier}
    (hx : Data.reprBytes x (rd h Ai T.size)) (hy : Data.reprBytes y (rd h Aj T.size)) :
    VarRel h (Ty.pair T T) (x, y) (pairSI T Ai Aj) := by
  refine ⟨rd h Ai T.size ++ rd h Aj T.size, ?_, fun k hk _ => ?_, fun e _ hs => by cases hs⟩
  · refine pair_of_slices (a := T) (b := T) x y _ (by simp [pair_ty_size]; omega) ?_ ?_
    · show Data.reprBytes x _
      rw [show slice (rd h Ai T.size ++ rd h Aj T.size) 0 T.size = rd h Ai T.size by
        simp [slice]]
      exact hx
    · show Data.reprBytes y (slice _ (sndOff T T) T.size)
      rw [sndOff_pair, show slice (rd h Ai T.size ++ rd h Aj T.size) T.size T.size = rd h Aj T.size by
        simp [slice, List.take_of_length_le]]
      exact hy
  · rw [pairSI_sz] at hk
    rw [← pairSI_rdS h T Ai Aj, rdS_getD _ _ _ _ hk]

/-! ## A place of two elements

`PairAt p … Ai Aj H` collects what a reference to a two-element place `p` needs in a given state.
The place is `q[i], q[j]` of an array or of a view variable. Its address code computes the
addresses `Ai` and `Aj` of the two elements, which are disjoint, inside one piece of the root's
storage, below the watermark, and represent the pair. `H` is the hole that a `&mut` borrow of the
place makes in its root, a region that contains both elements and that every place the body may
use avoids. Writing the two elements back gives the write-back of the pair. The proofs for borrows
and arguments are stated once over `PairAt`. -/

/-- The facts about a two-element place, described above. -/
structure PairAt {Γ : List Ty} {T : Ty} (p : Place Γ (.pair T T)) (ρ : List Loc) (S : List SI)
    (W : List Bool) (n bp : Nat) (env : Env Γ) (h : Heap) (Ai Aj : Nat) (H : Hole) : Prop where
  code : ∀ (κ : CostModel) (ω : Oracle) (L : Nat) (f : Frame), f BP = UInt64.ofNat bp →
    FEnvRel f env ρ → bp + n ≤ L → bp + n ≤ UInt64.size →
    ∃ f', Runs κ ω L (placeAddr p ρ) f h f' h ∧ f' BP = f BP ∧ f' RA = UInt64.ofNat Ai ∧
      f' RB = UInt64.ofNat Aj
  store : ∀ d, refStore p ρ d = pairStore d
  disj : Disj Ai T.size Aj T.size
  bi : Ai + T.size ≤ bp + n
  bj : Aj + T.size ≤ bp + n
  hi : (S.getD p.root default).Holds p.rootTy Ai T.size
  hj : (S.getD p.root default).Holds p.rootTy Aj T.size
  gi : Data.reprBytes (p.get env).1 (rd h Ai T.size)
  gj : Data.reprBytes (p.get env).2 (rd h Aj T.size)
  holePath : H.path = p.path
  holeIn : ∀ x, InR H.a H.len x → (S.getD p.root default).In p.rootTy x
  holeOK : HoleOK (S.getD p.root default) p.rootTy H
  elemsIn : ∀ x, (InR Ai T.size x ∨ InR Aj T.size x) → InR H.a H.len x
  back : W.getD p.root false = true → bp + n ≤ UInt64.size → ∀ (m : Heap) (v : (Ty.pair T T).carrier),
    (∀ x, x < bp + n → ¬ InR Ai T.size x → ¬ InR Aj T.size x → m (UInt64.ofNat x) = h (UInt64.ofNat x)) →
    Data.reprBytes v.1 (rd m Ai T.size) → Data.reprBytes v.2 (rd m Aj T.size) →
    MEnvRel m bp (p.set env v) ρ S

/-- The pair `q[i], q[j]` of an array place, whose hole is the whole array. -/
theorem pair2_at {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} {h : Heap} (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) {T : Ty} {N : Nat}
    [Inhabited T.carrier] (q : Place Γ (.arr T N)) (i j : Atom Γ .u64) (hc : q.contig = true)
    (hL : q.Lawful) (hok : (Place.pair2 q i j).ok env) (hnh : (Place.pair2 q i j).NH S)
    (hns : (ρ.getD q.root default).isSlot = false) :
    PairAt (.pair2 q i j) ρ S W n bp env h
      (placeA q S env + (i.denote env).toNat * T.size) (placeA q S env + (j.denote env).toNat * T.size)
      ⟨placeA q S env, N * T.size, q.path ++ [.dyn]⟩ := by
  have hok' := hok
  obtain ⟨hokq, hi, hj, hij⟩ := hok'
  have hpv := extOk_parent_arr q henv hl
  obtain ⟨-, -, hat, hhold⟩ := place_at q hc hL hokq henv hl hpv
  have hsz : (Ty.arr T N).size = N * T.size := rfl
  rw [hsz] at hhold
  have hbi := elem_bound (sz := T.size) hi
  have hbj := elem_bound (sz := T.size) hj
  have hgi := place_get (.index q i) hc hL ⟨hokq, hi⟩ henv hl hnh.2 (Or.inr rfl) hns
  have hgj := place_get (.index q j) hc hL ⟨hokq, hj⟩ henv hl hnh.2 (Or.inr rfl) hns
  refine ⟨fun κ ω L f hf hfe hnL hnU => pairAddr_runs hl T q i j f h hf henv hfe hc hL
      (q.notPair_of_ty hl (arr_not_prod T N)) hnh.1.1 hnh.1.2.1 hnh.1.2.2 hnL hnU, fun _ => rfl,
    ?_, hgi.1, hgj.1, hhold.sub (by omega) (by omega), hhold.sub (by omega) (by omega), hgi.2, hgj.2,
    rfl, fun x hx => place_in q hc hL hokq henv hl hpv (by rw [hsz]; exact hx), ?_, ?_,
    fun hW hbn m v hm hv1 hv2 => place_set_pair2 q i j hc hL hok henv hl hW hns hbn m v hm hv1 hv2⟩
  · exact elem_disj_of_ne hij
  · have h0 : HoleOK (S.getD q.root default) q.rootTy
        ⟨placeA q S env + 0 * T.size, N * T.size, q.path ++ [.dyn]⟩ :=
      holeOK_range q env _ (placeA q S env) 0 N hc hL hokq (hl.root q).ok hat (by omega)
    rw [Nat.zero_mul, Nat.add_zero] at h0; exact @h0
  · show ∀ x, _ → InR (placeA q S env) (N * T.size) x
    rintro x (h | h) <;> unfold InR at h ⊢ <;> omega

section
variable {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ}
  {h : Heap} {T : Ty} {p : Place Γ (.pair T T)} {Ai Aj : Nat} {Hl : Hole}

/-- Every pointer slot is away from the two elements. -/
theorem PairAt.refsAway (hP : PairAt p ρ S W n bp env h Ai Aj Hl) (hl : Lay bp n Γ ρ S W) :
    RefsAway bp Ai T.size Γ ρ ∧ RefsAway bp Aj T.size Γ ρ :=
  ⟨hl.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hP.hi),
    hl.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hP.hj)⟩

/-- The binder's value is represented by the two elements. -/
theorem PairAt.varRel (hP : PairAt p ρ S W n bp env h Ai Aj Hl) {H₁ : Heap}
    (hH₁ : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x)) :
    VarRel H₁ (Ty.pair T T) (p.get env) (pairSI T Ai Aj) := by
  have e : p.get env = ((p.get env).1, (p.get env).2) := rfl
  rw [e]
  refine pair_varRel ?_ ?_
  · rw [rd_congr fun j hj => hH₁ _ (by have := hP.bi; omega)]; exact hP.gi
  · rw [rd_congr fun j hj => hH₁ _ (by have := hP.bj; omega)]; exact hP.gj

end


/-! ## Borrows of a two-element place -/

/-- The handed-back value of a pair reference whose two pieces hold its bytes: each component is
represented at its element. -/
theorem pair_back_repr {T : Ty} {Ai Aj : Nat} {h' : Heap} (v : (Ty.pair T T).carrier)
    (V : List UInt8) (hV : Data.reprBytes v V)
    (hVm : slice V 0 ((pairSI T Ai Aj).sz (Ty.pair T T)) =
      rdS h' (pairSI T Ai Aj) ((pairSI T Ai Aj).sz (Ty.pair T T))) :
    Data.reprBytes v.1 (rd h' Ai T.size) ∧ Data.reprBytes v.2 (rd h' Aj T.size) := by
  rw [pairSI_sz, pairSI_rdS] at hVm
  have hVl : V.length = 2 * T.size := (Data.reprBytes_length hV).trans (pair_ty_size T)
  rw [slice_full V _ hVl] at hVm
  obtain ⟨hv1, hv2⟩ := pair_repr v V hV
  rw [hVm, show slice (rd h' Ai T.size ++ rd h' Aj T.size) 0 T.size = rd h' Ai T.size by
    simp [slice]] at hv1
  rw [hVm, sndOff_pair, show slice (rd h' Ai T.size ++ rd h' Aj T.size) T.size T.size =
    rd h' Aj T.size by simp [slice, List.take_of_length_le]] at hv2
  exact ⟨hv1, hv2⟩


section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- `let x := { let r = &p; body }; k` for a two-element place `p`. The binder's slot holds the
two elements' addresses, and the body reads them in place. -/
theorem msound_borrowShr_pairG {Γ : List Ty} {T : Ty} {u v : Ty} (p : Place Γ (.pair T T))
    (body : Exp (Ty.pair T T :: Γ) u) (k : Exp (u :: Γ) v) (hW16 : p.slotW = 16)
    (hloc : ∀ o, p.refLoc o = .ref2 o) (hVb : body.VSafe 0 .none = true)
    (hP : ∀ {W ρ S n bp env h}, Lay bp n Γ ρ S W → MEnvRel h bp env ρ S → p.ok env → p.NH S →
      p.Lawful → (ρ.getD p.root default).isSlot = false → ∃ Ai Aj Hl, PairAt p ρ S W n bp env h Ai Aj Hl)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr p body k) := by
  refine msound_borrowShr_of p body k hW16 hloc (fun o => .inr (hloc o ▸ rfl))
    (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, hW16] at hb hbL
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨Ai, Aj, Hl, hP⟩ := hP H.lay H.envRel H.safe.1
    (p.nh_of .read fun i H' h' => (H.hole i H' h').1) H.lawful.1 hns
  obtain ⟨hri, hrj⟩ := hP.refsAway H.lay
  obtain ⟨f₁, hr₁, hb₁, ha₁, hB₁⟩ := hP.code κ ω L f H.bpOk H.sl.rel (by omega) (by omega)
  obtain ⟨H₁, hst, hH₁out, hp1, hp2⟩ := pairStore_runs (κ := κ) (ω := ω) (L := L) (d := n)
    (hb₁.trans H.bpOk) ha₁ hB₁ (by omega) (by omega)
  have hH₁o : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx =>
    hH₁out x (by omega) (by unfold InR; omega)
  refine ⟨_, H₁, pairSI T Ai Aj, ⟨⟨f₁, hr₁, hb₁, by rw [hP.store n]; exact hst, hb₁⟩, hH₁o,
    Lay.pushRef2 T false H.lay.noW (Nat.le_refl _) (Nat.le_refl _) hP.disj hP.bi hP.bj hri hrj
      (fun e => by cases e), rfl,
    ⟨fun _ => hP.varRel hH₁o, ⟨hp1, fun f' A2 e => ?_⟩, H.envRel.above H.lay hH₁o⟩⟩, .inr hVb⟩
  simp only [pairSI, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact hp2

/-- `let x := { let r = &mut p; body }; k` for a two-element place `p`. The binder's slot holds the
two elements' addresses, the body updates them in place and hands the binder back in place, and
the lender's hole is the place's region. When the borrow ends, the memory represents the write-back
of the pair. -/
theorem msound_borrowMut_pairG {Γ : List Ty} {T : Ty} {u v : Ty} (p : Place Γ (.pair T T))
    (body : Exp (Ty.pair T T :: Γ) (.pair u (Ty.pair T T))) (k : Exp (u :: Γ) v)
    (hW16 : p.slotW = 16) (hloc : ∀ o, p.refLoc o = .ref2 o)
    (hCb : body.Conf (borrowTl u (Ty.pair T T)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.pair T T)) = true)
    (hP : ∀ {W ρ S n bp env h}, Lay bp n Γ ρ S W → MEnvRel h bp env ρ S → p.ok env → p.NH S →
      p.Lawful → (ρ.getD p.root default).isSlot = false → ∃ Ai Aj Hl, PairAt p ρ S W n bp env h Ai Aj Hl)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut p body k) := by
  refine msound_borrowMut_of p body k hW16 hloc (fun o => .inr (hloc o ▸ rfl)) hCb
    (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, hW16] at hb hbL
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨Ai, Aj, Hl, hP⟩ := hP H.lay H.envRel H.safe.1
    (p.nh_of .write fun i H' h' => (H.hole i H' h').1) H.lawful.1 hns
  obtain ⟨hri, hrj⟩ := hP.refsAway H.lay
  obtain ⟨f₁, hr₁, hb₁, ha₁, hB₁⟩ := hP.code κ ω L f H.bpOk H.sl.rel (by omega) (by omega)
  obtain ⟨H₁, hst, hH₁out, hp1, hp2⟩ := pairStore_runs (κ := κ) (ω := ω) (L := L) (d := n)
    (hb₁.trans H.bpOk) ha₁ hB₁ (by omega) (by omega)
  have hH₁o : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx =>
    hH₁out x (by omega) (by unfold InR; omega)
  -- the two elements are in the lender's hole, visible to no variable
  obtain ⟨hlh, hvis⟩ := H.lay.lend p Hl hP.holeIn hP.holeOK H.restr.1 _
    (fun x hx => hx.elim (fun h => hP.hi.In h) (fun h => hP.hj.In h)) hP.elemsIn
    (fun x hx => hx.elim (fun h => hri.not_refSlot h) (fun h => hrj.not_refSlot h))
  refine ⟨_, H₁, pairSI T Ai Aj, Hl, ⟨⟨f₁, hr₁, hb₁, by rw [hP.store n]; exact hst, hb₁⟩, hH₁o,
    Lay.pushRef2 T true hlh (Nat.le_refl _) (Nat.le_refl _) hP.disj hP.bi hP.bj hri hrj
      (fun _ => hvis), rfl,
    ⟨fun _ => hP.varRel hH₁o, ⟨hp1, fun f' A2 e => ?_⟩,
      (H.envRel.above H.lay hH₁o).setHole _ _ ((H.lay.root p).2.2.1 H.restr.1)⟩⟩,
    hP.holePath, .inr hVb, fun x hx => InW.place p H.restr.1
      ((pairSI_In.1 hx).elim (fun h => hP.hi.In h) (fun h => hP.hj.In h)) H.lay.length.2,
    fun m bs hm hv hsc => ?_⟩
  · simp only [pairSI, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact hp2
  · rw [show (pairSI T Ai Aj).lim (Ty.pair T T).size = (pairSI T Ai Aj).sz (Ty.pair T T) from rfl]
      at hsc
    have hlen2 := Data.reprBytes_length hv
    obtain ⟨hw1, hw2⟩ := pair_back_repr (Ai := Ai) (Aj := Aj) _ _ hv (by
      rw [slice_full _ _ (by rw [pairSI_sz, ← pair_ty_size T]; exact hlen2)]
      rw [pairSI_sz, ← pair_ty_size] at hsc ⊢; exact hsc)
    exact hP.back H.restr.1 (by omega) m _ (fun x hx hn1 hn2 => hm x hx fun h5 =>
      (pairSI_In.1 h5).elim hn1 hn2) hw1 hw2

/-- `let x := { let r = &(q[i], q[j]); body }; k`. -/
theorem msound_borrowShr_pair2 {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty} [Inhabited T.carrier]
    (q : Place Γ (.arr T N)) (i j : Atom Γ .u64) (body : Exp (Ty.pair T T :: Γ) u)
    (k : Exp (u :: Γ) v) (hc : q.contig = true) (hVb : body.VSafe 0 .none = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr (.pair2 q i j) body k) :=
  msound_borrowShr_pairG _ body k rfl (fun _ => rfl) hVb
    (fun hl henv hok hnh hL hns => ⟨_, _, _, pair2_at hl henv q i j hc hL hok hnh hns⟩) ihb ihk

/-- `let x := { let r = &mut (q[i], q[j]); body }; k`. The lender's hole is the whole array, and
when the borrow ends the memory represents the write-back of the pair. -/
theorem msound_borrowMut_pair2 {Γ : List Ty} {T : Ty} {N : Nat} {u v : Ty} [Inhabited T.carrier]
    (q : Place Γ (.arr T N)) (i j : Atom Γ .u64) (body : Exp (Ty.pair T T :: Γ) (.pair u (Ty.pair T T)))
    (k : Exp (u :: Γ) v) (hc : q.contig = true) (hCb : body.Conf (borrowTl u (Ty.pair T T)) = true)
    (hVb : body.VSafe 0 (borrowTl u (Ty.pair T T)) = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut (.pair2 q i j) body k) :=
  msound_borrowMut_pairG _ body k rfl (fun _ => rfl) hCb hVb
    (fun hl henv hok hnh hL hns => ⟨_, _, _, pair2_at hl henv q i j hc hL hok hnh hns⟩) ihb ihk

end

end Millipede.Flat
