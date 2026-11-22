import Millipede.Compile.LowerInv

/-!
# The simulation predicate of the memory refinement

`MSim κ ω L s k Q prot r` says that running Flat from `s` matches the instrumented Core result `r`.
The run reaches the same world, and so the same events, with the clock advanced by exactly
`r.steps`, and it returns to the continuation `k` with the base pointer unchanged. Its final frame
and memory satisfy `Q` for `r.val`, and every protected address in `prot` keeps its byte. When the
program calls `exit`, the Flat run instead stops in the same halted world, having spent at most
`r.steps`. Every state of the run accesses memory only below `L`.

`MSoundAt κ ω e` is the refinement property of one term: in every tail mode the term conforms to,
and for every `L` above the term's memory, its lowered code satisfies `MSim`. This module also
holds the composition lemmas `MSim.pre`, `MSim.bind` and `MSim.done`, and the lemmas about the
layout and the frame relation that the cases of the proof use. The method is described in
doc/design/compiler.md.
-/

namespace Millipede.Flat

/-- The simulation predicate, described in the module doc. `pf` marks the frame slots from `FR` on,
which hold the slot-resident variables, that the run must not change. -/
def MSim (κ : CostModel) (ω : Oracle) (L : Nat) {α : Type} (s : State) (k : List Kont)
    (Q : α → Frame → Heap → Prop) (prot : Nat → Prop) (r : Out α) (pf : Nat → Prop := fun _ => False) :
    Prop :=
  ∃ s', ReachL κ ω L s s' ∧ s'.world = r.world ∧ s'.clock ≤ s.clock + r.steps ∧
    (r.world.halted = true ∨
      (s'.cur = .skip ∧ s'.kont = k ∧ s'.clock = s.clock + r.steps ∧ s'.frame BP = s.frame BP ∧
        Q r.val s'.frame s'.mem ∧
        (∀ a, prot a → s'.mem (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) ∧
        ∀ x, FR ≤ x → pf x → s'.frame x = s.frame x))

theorem rd_getD (h : Heap) : ∀ (A n i : Nat), i < n → (rd h A n).getD i 0 = h (UInt64.ofNat (A + i))
  | A, n + 1, 0, _ => by simp [rd]
  | A, n + 1, i + 1, hi => by
    simp only [rd, List.getD_cons_succ]
    rw [rd_getD h (A + 1) n i (by omega)]; congr 2; omega

theorem rd_of_getD {h : Heap} {A : Nat} : ∀ {n : Nat} {B : List UInt8}, B.length = n →
    (∀ i, i < n → h (UInt64.ofNat (A + i)) = B.getD i 0) → rd h A n = B
  | 0, [], _, _ => rfl
  | n + 1, b :: B, hl, hB => by
    simp only [rd]
    have h0 := hB 0 (by omega); simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, @rd_of_getD h (A + 1) n B (by simpa using hl) fun i hi => by
      have := hB (i + 1) (by omega)
      simp only [List.getD_cons_succ] at this
      rw [← this]; congr 2; omega]
  | 0, _ :: _, hl, _ => by simp at hl
  | _ + 1, [], hl, _ => by simp at hl

/-- The first `n` bytes of a variable's value, wherever they live. -/
def rdS (h : Heap) (s : SI) : Nat → List UInt8
  | 0 => []
  | n + 1 => rdS h s n ++ [h (UInt64.ofNat (s.at n))]

@[simp] theorem rdS_length (h : Heap) (s : SI) (n : Nat) : (rdS h s n).length = n := by
  induction n <;> simp_all [rdS]

theorem rdS_getD (h : Heap) (s : SI) : ∀ (n i : Nat), i < n →
    (rdS h s n).getD i 0 = h (UInt64.ofNat (s.at i))
  | n + 1, i, hi => by
    simp only [rdS, List.getD_eq_getElem?_getD]
    by_cases hin : i < n
    · rw [List.getElem?_append_left (by simpa using hin)]
      have := rdS_getD h s n i hin
      simpa [List.getD_eq_getElem?_getD] using this
    · have : i = n := by omega
      subst this
      rw [List.getElem?_append_right (by simp)]
      simp

theorem rdS_of_getD {h : Heap} {s : SI} {n : Nat} {B : List UInt8} (hl : B.length = n)
    (hB : ∀ i, i < n → h (UInt64.ofNat (s.at i)) = B.getD i 0) : rdS h s n = B := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have e1 := rdS_getD h s n i (by simpa using h1)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at e1
  simp only [Option.getD_some] at e1
  rw [e1, hB i (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

theorem rdS_congr {h h' : Heap} {s : SI} {n : Nat}
    (hm : ∀ i, i < n → h' (UInt64.ofNat (s.at i)) = h (UInt64.ofNat (s.at i))) :
    rdS h' s n = rdS h s n :=
  rdS_of_getD (by simp) fun i hi => by rw [hm i hi, rdS_getD h s n i hi]

/-- The bytes of a variable without a second piece are read at its address. -/
theorem rdS_none {s : SI} (hs : s.snd = none) (h : Heap) (n : Nat) : rdS h s n = rd h s.A n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have e1 := rdS_getD h s n i (by simpa using h1)
  have e2 := rd_getD h s.A n i (by simpa using h1)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at e2
  simp only [Option.getD_some] at e1 e2
  rw [e1, e2, SI.at_none hs]

/-- An in-place component of a tail mode, the bytes `off .. off + sz` of the handed-back value
`bs`, held by a variable at location `l`. In memory, the variable's bytes are the component's. In
the frame slots from `k`, the slots hold the chunks of the component's bytes. -/
def CompAt (bs : List UInt8) (f : Frame) (h : Heap) (l : Loc) (s : SI) (off sz : Nat) : Prop :=
  match l.slot? with
  | some k => WordsAt f k (slice bs off sz) l.nw
  | none => slice bs off (s.lim sz) = rdS h s (s.lim sz)

/-- What a term in tail mode `tm` leaves in memory and in the frame. For `none` its value's bytes
are at the destination, and for `whole x` variable `x`'s bytes represent it. For `split`, some bytes
`bs` that represent it hold its first component at the destination and each in-place component where
that variable lives. For `word k` the frame slots from `k` hold it. -/
def TQ (tm : Tl) (bp d : Nat) (ρ : List Loc) (S : List SI) (t : Ty) :
    t.carrier → Frame → Heap → Prop :=
  match tm with
  | .none => fun v _ h => Data.reprBytes v (rd h (bp + d) t.size)
  | .whole x => fun v _ h => Data.reprBytes v (rd h (S.getD x default).A t.size)
  | .split f0 cs => fun v f h => ∃ bs : List UInt8, Data.reprBytes v bs ∧
      slice bs 0 f0 = rd h (bp + d) f0 ∧
      ∀ c ∈ cs, CompAt bs f h (ρ.getD c.1 default) (S.getD c.1 default) c.2.1 c.2.2
  | .word k => fun v f _ => WordsRel t v f k

/-- A component in memory. -/
theorem CompAt.mem {bs : List UInt8} {f : Frame} {h : Heap} {l : Loc} {s : SI} {off sz : Nat}
    (hl : l.slot? = none) :
    CompAt bs f h l s off sz ↔ slice bs off (s.lim sz) = rdS h s (s.lim sz) := by
  simp only [CompAt, hl]

/-- A tail mode fits the context. Its in-place variables are writable, so they have no hole. A word
destination `k` is a frame slot from `FR` on and at most the next free one, and every slot-resident
variable lies wholly below `k`, or wholly from `k` on and is then writable. Such a variable is a
slot-resident binder of the term itself, dead once the value is written. -/
def Tl.Ok (tm : Tl) (W : List Bool) (ρ : List Loc) : Prop :=
  match tm with
  | .none => True
  | .whole x => W.getD x false = true
  | .split _ cs => ∀ c ∈ cs, W.getD c.1 false = true
  | .word k => FR ≤ k ∧ k ≤ FR + slotsIn ρ ∧ ∀ i k', (ρ.getD i default).slot? = some k' →
      k' + (ρ.getD i default).nw ≤ k ∨ (k ≤ k' ∧ W.getD i false = true)

/-- Every variable with an extent, which is a slice view, satisfies `P`. -/
def VS (S : List SI) (P : Nat → Bool) : Prop :=
  ∀ i, (S.getD i default).ext ≠ none → P i = true

theorem VS.mono {S : List SI} {P Q : Nat → Bool} (h : VS S P) (hq : ∀ i, P i = true → Q i = true) :
    VS S Q := fun i hi => hq i (h i hi)

/-- Under a binder without an extent. -/
theorem VS.push {S : List SI} {P : Nat → Bool} (si : SI) (hsi : si.ext = none)
    (h : VS S fun i => P (i + 1)) : VS (si :: S) P := by
  intro i hi
  cases i with
  | zero => exact absurd hsi hi
  | succ i => exact h i (by simpa using hi)

/-- A view variable at the head: its own fact, and the others'. -/
theorem VS.push_view {S : List SI} {P : Nat → Bool} (si : SI) (h0 : P 0 = true)
    (h : VS S fun i => P (i + 1)) : VS (si :: S) P := by
  intro i hi
  cases i with
  | zero => exact h0
  | succ i => exact h i (by simpa using hi)

/-- Under two binders without an extent. -/
theorem VS.push2 {S : List SI} {P : Nat → Bool} (si sj : SI) (hsi : si.ext = none)
    (hsj : sj.ext = none) (h : VS S fun i => P (i + 2)) : VS (si :: sj :: S) P := by
  intro i hi
  match i, hi with
  | 0, hi => exact absurd hsi hi
  | 1, hi => exact absurd hsj hi
  | i + 2, hi => exact h i (by simpa using hi)

/-- An atom that no view-variable test rejects reads no variable with an extent. -/
theorem VS.atom {Γ : List Ty} {t : Ty} {S : List SI} {P : Nat → Bool} (a : Atom Γ t)
    (h : VS S P) (ha : ∀ i, P i = true → a.isVar i = false) :
    ∀ m, a = .var m → (S.getD m.idx default).ext = none := by
  intro m e
  subst e
  cases he : (S.getD m.idx default).ext with
  | none => rfl
  | some x =>
    have := ha _ (h m.idx (by rw [he]; nofun))
    simp [Atom.isVar] at this

/-- The facts about slot-resident variables: they are numbered from `FR` in binding order,
represented by the frame, never addressed by the term, and not handed back in place by its tail
mode. -/
structure SlotHyp {Γ : List Ty} {t : Ty} (e : Exp Γ t) (tm : Tl) (ρ : List Loc) (env : Env Γ)
    (f : Frame) : Prop where
  ok : SlotsOk ρ
  rel : FEnvRel f env ρ
  na : ∀ i, (ρ.getD i default).isSlot = true → e.noAddr i = true ∧ i ∉ tm.vars

/-- The refinement property of a term under the memory lowering, in every tail mode it conforms to.
From any state whose frame holds the base pointer and whose memory represents the environment,
under the hypotheses on layout, restraint, lawfulness, borrows, safety and the address space, and
with every slice view used only through its elements, the lowered code simulates `exec`. -/
def MSoundAt (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Prop :=
  ∀ (tm : Tl) (L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI) (n d bp : Nat) (env : Env Γ)
    (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
    e.Conf tm = true → tm.Ok W ρ → e.Restr W → e.Lawful → e.Frozen → HoleAv e S →
    Lay bp n Γ ρ S W → d + tm.dsz t ≤ n → Away bp d (tm.dsz t) Γ ρ S →
    bp + n + e.memNeed ≤ UInt64.size → f BP = UInt64.ofNat bp → MEnvRel h bp env ρ S →
    e.safe ω env w → w.halted = false → bp + n + e.memNeed ≤ L →
    VS S (e.VSafe · tm) → SlotHyp e tm ρ env f →
    MSim κ ω L ⟨lowerM e tm ρ n d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.hb env w) (SProt ρ W)

/-- The hypotheses of `MSoundAt` for `e`, as named fields. -/
structure MHyp (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (tm : Tl) (L : Nat)
    (W : List Bool) (ρ : List Loc) (S : List SI) (n d bp : Nat) (env : Env Γ) (f : Frame)
    (h : Heap) (w : World) : Prop where
  conf : e.Conf tm = true
  tmOk : tm.Ok W ρ
  restr : e.Restr W
  lawful : e.Lawful
  frozen : e.Frozen
  hole : HoleAv e S
  lay : Lay bp n Γ ρ S W
  dn : d + tm.dsz t ≤ n
  away : Away bp d (tm.dsz t) Γ ρ S
  size : bp + n + e.memNeed ≤ UInt64.size
  bpOk : f BP = UInt64.ofNat bp
  envRel : MEnvRel h bp env ρ S
  safe : e.safe ω env w
  run : w.halted = false
  room : bp + n + e.memNeed ≤ L
  vs : VS S (e.VSafe · tm)
  sl : SlotHyp e tm ρ env f

theorem msoundAt_iff {κ : CostModel} {ω : Oracle} {Γ : List Ty} {t : Ty} {e : Exp Γ t} :
    MSoundAt κ ω e ↔ ∀ (tm : Tl) (L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI)
      (n d bp : Nat) (env : Env Γ) (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
      MHyp ω e tm L W ρ S n d bp env f h w →
      MSim κ ω L ⟨lowerM e tm ρ n d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
        (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.hb env w) (SProt ρ W) :=
  ⟨fun H _ _ _ _ _ _ _ _ _ _ _ _ _ _ x =>
    H _ _ _ _ _ _ _ _ _ _ _ _ _ _ x.1 x.2 x.3 x.4 x.5 x.6 x.7 x.8 x.9 x.10 x.11 x.12 x.13 x.14 x.15 x.16
      x.17,
   fun H _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 =>
    H _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17⟩⟩

/-- Prove `MSoundAt` from the bundled hypotheses. -/
theorem MSoundAt.intro {κ : CostModel} {ω : Oracle} {Γ : List Ty} {t : Ty} {e : Exp Γ t}
    (H : ∀ (tm : Tl) (L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI)
      (n d bp : Nat) (env : Env Γ) (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
      MHyp ω e tm L W ρ S n d bp env f h w →
      MSim κ ω L ⟨lowerM e tm ρ n d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
        (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.hb env w) (SProt ρ W)) : MSoundAt κ ω e :=
  msoundAt_iff.2 H

/-- Use `MSoundAt` on one bundle of hypotheses. -/
theorem MSoundAt.app {κ : CostModel} {ω : Oracle} {Γ : List Ty} {t : Ty} {e : Exp Γ t}
    (ih : MSoundAt κ ω e) {tm : Tl} {L : Nat} {W : List Bool} {ρ : List Loc} {S : List SI}
    {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World}
    (H : MHyp ω e tm L W ρ S n d bp env f h w) (k : List Kont) (c : Nat) :
    MSim κ ω L ⟨lowerM e tm ρ n d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.hb env w) (SProt ρ W) :=
  msoundAt_iff.1 ih _ _ _ _ _ _ _ _ _ k _ _ _ c H

section
variable {ω : Oracle} {Γ : List Ty} {t : Ty} {e : Exp Γ t} {tm : Tl} {L : Nat} {W : List Bool}
  {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World}

theorem MHyp.nU (H : MHyp ω e tm L W ρ S n d bp env f h w) : bp + n ≤ UInt64.size := by
  have := H.size; omega

theorem MHyp.nL (H : MHyp ω e tm L W ρ S n d bp env f h w) : bp + n ≤ L := by
  have := H.room; omega

theorem MHyp.dn0 (H : MHyp ω e .none L W ρ S n d bp env f h w) : d + t.size ≤ n := H.dn

theorem MHyp.away0 (H : MHyp ω e .none L W ρ S n d bp env f h w) : Away bp d t.size Γ ρ S :=
  H.away

end

/-- One chunk: the word of the first eight bytes, or fewer. -/
theorem wordsAt_one {f : Frame} {k : Nat} {B : List UInt8} (hB : B.length ≤ 8) :
    WordsAt f k B 1 ↔ f k = decodeLE B := by
  simp [WordsAt, List.take_of_length_le hB]

/-- The slot of a one-word value: `WordsRel` is `WordRel` of the slot. -/
theorem wordsRel_one {t : Ty} {v : t.carrier} {f : Frame} {k : Nat} (h1 : t.slotN = 1) :
    WordsRel t v f k ↔ WordRel t v (f k) := by
  have hle : t.size ≤ 8 := by unfold Ty.slotN at h1; omega
  constructor
  · rintro ⟨B, hB, hw⟩
    rw [h1, wordsAt_one (by rw [Data.reprBytes_length hB]; exact hle)] at hw
    exact ⟨B, hB, hw.symm⟩
  · rintro ⟨B, hB, hw⟩
    exact ⟨B, hB, by rw [h1, wordsAt_one (by rw [Data.reprBytes_length hB]; exact hle)]; exact hw.symm⟩

section
variable {κ : CostModel} {ω : Oracle} {L : Nat} {α β : Type} {pf : Nat → Prop}

theorem MSim.of_eq {s : State} {k : List Kont} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop}
    {r r' : Out α} (h : MSim κ ω L s k Q prot r pf) (hv : r'.val = r.val) (hw : r'.world = r.world)
    (hs : r'.steps = r.steps) : MSim κ ω L s k Q prot r' pf := by
  obtain ⟨s', h1, h2, h3, h4⟩ := h
  refine ⟨s', h1, hw ▸ h2, hs ▸ h3, ?_⟩
  rw [hw, hs, hv]; exact h4

theorem MSim.weaken {s : State} {k : List Kont} {Q : α → Frame → Heap → Prop} {prot prot' : Nat → Prop}
    {pf' : Nat → Prop} {r : Out α} (h : MSim κ ω L s k Q prot r pf) (hp : ∀ a, prot' a → prot a)
    (hpf : ∀ x, pf' x → pf x := by first | exact fun _ h => h | exact fun _ h => h.elim) :
    MSim κ ω L s k Q prot' r pf' := by
  obtain ⟨s', h1, h2, h3, h4⟩ := h
  refine ⟨s', h1, h2, h3, ?_⟩
  rcases h4 with h | ⟨a, b, c, d, e, g, g'⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, c, d, e, fun x hx => g x (hp x hx), fun x hx hp => g' x hx (hpf x hp)⟩

theorem MSim.post {s : State} {k : List Kont} {Q Q' : α → Frame → Heap → Prop} {prot : Nat → Prop}
    {r : Out α} (h : MSim κ ω L s k Q prot r pf)
    (hq : ∀ f m, Q r.val f m → (∀ a, prot a → m (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) →
      Q' r.val f m) :
    MSim κ ω L s k Q' prot r pf := by
  obtain ⟨s', h1, h2, h3, h4⟩ := h
  refine ⟨s', h1, h2, h3, ?_⟩
  rcases h4 with h | ⟨a, b, c, d, e, g, g'⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, c, d, hq _ _ e g, g, g'⟩

/-- A prefix that reaches `s₀`, charging `δ`, keeping the base pointer and the protected slots, and
changing no protected address. -/
theorem MSim.pre {s s₀ : State} {δ : Nat} {k : List Kont} {Q : α → Frame → Heap → Prop}
    {prot : Nat → Prop} {r : Out α} (hr : ReachL κ ω L s s₀) (hc : s₀.clock = s.clock + δ)
    (hf : s₀.frame BP = s.frame BP)
    (hm : ∀ a, prot a → s₀.mem (UInt64.ofNat a) = s.mem (UInt64.ofNat a))
    (hfk : ∀ x, FR ≤ x → pf x → s₀.frame x = s.frame x)
    (h : MSim κ ω L s₀ k Q prot r pf) : MSim κ ω L s k Q prot ⟨r.val, r.world, δ + r.steps⟩ pf := by
  obtain ⟨s', h1, h2, h3, h4⟩ := h
  refine ⟨s', hr.trans h1, h2, by simp only; omega, ?_⟩
  rcases h4 with h | ⟨a, b, cl, d', e, g, g'⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, by simp only; omega, d'.trans hf, e, fun x hx => (g x hx).trans (hm x hx),
      fun x hx hp => (g' x hx hp).trans (hfk x hx hp)⟩

/-- Sequencing into an arbitrary continuation: run `s` until it is back at `.seq c₂ :: K`, then
run `c₂` from `K` to the final continuation `k`. `c₂` starts in a frame whose protected slots `pf₁`
are the original ones. -/
theorem MSim.bindKF {s : State} {K k : List Kont} {c₂ : Stmt} {Q₁ : α → Frame → Heap → Prop}
    {Q : β → Frame → Heap → Prop} {prot prot₁ prot₂ : Nat → Prop} {pf₁ pf₂ : Nat → Prop} {r₁ : Out α}
    {r₂ : Out β}
    (h₁ : MSim κ ω L s (.seq c₂ :: K) Q₁ prot₁ r₁ pf₁)
    (hhalt : r₁.world.halted = true → r₂.world = r₁.world)
    (hp : ∀ a, prot a → prot₁ a ∧ prot₂ a)
    (hpf : ∀ x, pf x → pf₁ x ∧ pf₂ x)
    (h₂ : ∀ f₁ m₁, f₁ BP = s.frame BP → (∀ x, FR ≤ x → pf₁ x → f₁ x = s.frame x) →
      Q₁ r₁.val f₁ m₁ →
      (∀ a, prot₁ a → m₁ (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) →
      r₁.world.halted = false →
      MSim κ ω L ⟨c₂, K, f₁, m₁, r₁.world, s.clock + r₁.steps⟩ k Q prot₂ r₂ pf₂) :
    MSim κ ω L s k Q prot ⟨r₂.val, r₂.world, r₁.steps + r₂.steps⟩ pf := by
  obtain ⟨s₁, hr₁, hw₁, hc₁, h4⟩ := h₁
  cases hh : r₁.world.halted with
  | true =>
    refine ⟨s₁, hr₁, by simp only; rw [hhalt hh]; exact hw₁, by simp only; omega, ?_⟩
    left; simp only; rw [hhalt hh]; exact hh
  | false =>
    rcases h4 with h | ⟨hcur, hk, hcl, hf, hv, hm, hfk⟩
    · rw [hh] at h; cases h
    obtain ⟨cur, kont, f₁, m₁, w₁, c₁⟩ := s₁
    simp only at hcur hk hcl hf hv hm hw₁ hfk
    subst hcur hk hcl hw₁
    obtain ⟨s₂, hr₂, hw₂, hc₂, h5⟩ := h₂ f₁ m₁ hf hfk hv hm hh
    have hr : ReachL κ ω L s s₂ := hr₁.trans (ReachL.step' hh (by simp only [exec1]; exact hr₂))
    refine ⟨s₂, hr, hw₂, by simp only at hc₂ ⊢; omega, ?_⟩
    rcases h5 with h | ⟨a, b, cl, d', e, g, g'⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, b, by simp only at cl ⊢; omega, d'.trans hf, e, fun x hx => ?_,
        fun x hx hp => ?_⟩
      · exact (g x (hp x hx).2).trans (hm x (hp x hx).1)
      · exact (g' x hx (hpf x hp).2).trans (hfk x hx (hpf x hp).1)

/-- Sequencing into an arbitrary continuation, where the second part needs no frame facts. -/
theorem MSim.bindK {s : State} {K k : List Kont} {c₂ : Stmt} {Q₁ : α → Frame → Heap → Prop}
    {Q : β → Frame → Heap → Prop} {prot prot₁ prot₂ : Nat → Prop} {pf₁ pf₂ : Nat → Prop} {r₁ : Out α}
    {r₂ : Out β}
    (h₁ : MSim κ ω L s (.seq c₂ :: K) Q₁ prot₁ r₁ pf₁)
    (hhalt : r₁.world.halted = true → r₂.world = r₁.world)
    (hp : ∀ a, prot a → prot₁ a ∧ prot₂ a)
    (h₂ : ∀ f₁ m₁, f₁ BP = s.frame BP → Q₁ r₁.val f₁ m₁ →
      (∀ a, prot₁ a → m₁ (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) →
      r₁.world.halted = false →
      MSim κ ω L ⟨c₂, K, f₁, m₁, r₁.world, s.clock + r₁.steps⟩ k Q prot₂ r₂ pf₂)
    (hpf : ∀ x, pf x → pf₁ x ∧ pf₂ x := by
      first | exact fun _ h => h.elim | exact fun _ h => ⟨h, h⟩) :
    MSim κ ω L s k Q prot ⟨r₂.val, r₂.world, r₁.steps + r₂.steps⟩ pf :=
  MSim.bindKF h₁ hhalt hp hpf fun f₁ m₁ hf _ => h₂ f₁ m₁ hf

/-- Sequencing: run `s` until it is back at `.seq c₂ :: k`, then run `c₂`. -/
theorem MSim.bind {s : State} {k : List Kont} {c₂ : Stmt} {Q₁ : α → Frame → Heap → Prop}
    {Q : β → Frame → Heap → Prop} {prot prot₁ prot₂ : Nat → Prop} {pf₁ pf₂ : Nat → Prop} {r₁ : Out α}
    {r₂ : Out β}
    (h₁ : MSim κ ω L s (.seq c₂ :: k) Q₁ prot₁ r₁ pf₁)
    (hhalt : r₁.world.halted = true → r₂.world = r₁.world)
    (hp : ∀ a, prot a → prot₁ a ∧ prot₂ a)
    (h₂ : ∀ f₁ m₁, f₁ BP = s.frame BP → Q₁ r₁.val f₁ m₁ →
      (∀ a, prot₁ a → m₁ (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) →
      r₁.world.halted = false →
      MSim κ ω L ⟨c₂, k, f₁, m₁, r₁.world, s.clock + r₁.steps⟩ k Q prot₂ r₂ pf₂)
    (hpf : ∀ x, pf x → pf₁ x ∧ pf₂ x := by
      first | exact fun _ h => h.elim | exact fun _ h => ⟨h, h⟩) :
    MSim κ ω L s k Q prot ⟨r₂.val, r₂.world, r₁.steps + r₂.steps⟩ pf :=
  MSim.bindK h₁ hhalt hp h₂ hpf

/-- Sequencing, with the second part starting in a frame whose protected slots are the original
ones. -/
theorem MSim.bindF {s : State} {k : List Kont} {c₂ : Stmt} {Q₁ : α → Frame → Heap → Prop}
    {Q : β → Frame → Heap → Prop} {prot prot₁ prot₂ : Nat → Prop} {pf₁ pf₂ : Nat → Prop} {r₁ : Out α}
    {r₂ : Out β}
    (h₁ : MSim κ ω L s (.seq c₂ :: k) Q₁ prot₁ r₁ pf₁)
    (hhalt : r₁.world.halted = true → r₂.world = r₁.world)
    (hp : ∀ a, prot a → prot₁ a ∧ prot₂ a)
    (hpf : ∀ x, pf x → pf₁ x ∧ pf₂ x)
    (h₂ : ∀ f₁ m₁, f₁ BP = s.frame BP → (∀ x, FR ≤ x → pf₁ x → f₁ x = s.frame x) →
      Q₁ r₁.val f₁ m₁ →
      (∀ a, prot₁ a → m₁ (UInt64.ofNat a) = s.mem (UInt64.ofNat a)) →
      r₁.world.halted = false →
      MSim κ ω L ⟨c₂, k, f₁, m₁, r₁.world, s.clock + r₁.steps⟩ k Q prot₂ r₂ pf₂) :
    MSim κ ω L s k Q prot ⟨r₂.val, r₂.world, r₁.steps + r₂.steps⟩ pf :=
  MSim.bindKF h₁ hhalt hp hpf h₂

/-- Code with no subterm runs, and the Core step charges nothing more. -/
theorem MSim.done {st : Stmt} {k : List Kont} {f f' : Frame} {h h' : Heap} {w : World} {c : Nat}
    {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α} (hw : w.halted = false)
    (hr : Runs κ ω L st f h f' h')
    (hrw : r.world = w) (hrs : r.steps = 0) (hf : f' BP = f BP) (hv : Q r.val f' h')
    (hm : ∀ a, prot a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MSim κ ω L ⟨st, k, f, h, w, c⟩ k Q prot r pf :=
  ⟨⟨.skip, k, f', h', w, c⟩, hr.run k w c hw, hrw.symm, by simp [hrs],
    Or.inr ⟨rfl, rfl, by simp [hrs], hf, hv, hm, fun x hx _ => hr.keep x hx⟩⟩

/-- A tick, then `rest`. -/
theorem MSim.tick {t : Tick} {rest : Stmt} {k : List Kont} {f : Frame} {h : Heap} {w : World}
    {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α} (hw : w.halted = false)
    (hrest : MSim κ ω L ⟨rest, k, f, h, w, c + t.cost κ⟩ k Q prot r pf) :
    MSim κ ω L ⟨.seq (.tick t) rest, k, f, h, w, c⟩ k Q prot ⟨r.val, r.world, t.cost κ + r.steps⟩ pf :=
  MSim.pre (s₀ := ⟨rest, k, f, h, w, c + t.cost κ⟩)
    (ReachL.step' hw (by simp only [exec1]; exact ReachL.step' hw (by
      simp only [exec1]; exact ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _))))
    rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl) hrest

/-- A tick-free prefix `a` that reaches `f₁` and `h₁` and changes no protected slot, then `b`. -/
theorem MSim.reach {a b : Stmt} {k : List Kont} {f f₁ : Frame} {h h₁ : Heap} {w : World}
    {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α} (hw : w.halted = false)
    (ha : Reaches κ ω L a f h f₁ h₁) (hf : f₁ BP = f BP)
    (hm : ∀ x, prot x → h₁ (UInt64.ofNat x) = h (UInt64.ofNat x))
    (hk : ∀ x, FR ≤ x → pf x → f₁ x = f x)
    (hb : MSim κ ω L ⟨b, k, f₁, h₁, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.seq a b, k, f, h, w, c⟩ k Q prot r pf := by
  have hr : ReachL κ ω L ⟨.seq a b, k, f, h, w, c⟩ ⟨b, k, f₁, h₁, w, c⟩ :=
    ReachL.step' hw (by
      simp only [exec1]
      exact (ha (.seq b :: k) w c hw).trans
        (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)))
  have := MSim.pre (δ := 0) hr rfl hf hm hk hb
  exact this.of_eq rfl rfl (by simp)

/-- A tick-free prefix `a` that `Runs`, then `b`. -/
theorem MSim.runs {a b : Stmt} {k : List Kont} {f f₁ : Frame} {h h₁ : Heap} {w : World}
    {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α} (hw : w.halted = false)
    (ha : Runs κ ω L a f h f₁ h₁) (hf : f₁ BP = f BP)
    (hm : ∀ x, prot x → h₁ (UInt64.ofNat x) = h (UInt64.ofNat x))
    (hb : MSim κ ω L ⟨b, k, f₁, h₁, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.seq a b, k, f, h, w, c⟩ k Q prot r pf :=
  MSim.reach hw ha.run hf hm (fun x hx _ => ha.keep x hx) hb

theorem MSim.seq_intro {c₁ c₂ : Stmt} {k : List Kont} {f : Frame} {h : Heap}
    {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α}
    (hw : w.halted = false)
    (h₁ : MSim κ ω L ⟨c₁, .seq c₂ :: k, f, h, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.seq c₁ c₂, k, f, h, w, c⟩ k Q prot r pf :=
  (MSim.pre (s := ⟨.seq c₁ c₂, k, f, h, w, c⟩) (s₀ := ⟨c₁, .seq c₂ :: k, f, h, w, c⟩) (δ := 0)
    (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)) rfl rfl
    (fun _ _ => rfl) (fun _ _ _ => rfl) h₁).of_eq rfl rfl (by simp)

theorem MSim.ite {o : Operand} {t e : Stmt} {k : List Kont} {f : Frame}
    {h : Heap} {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α}
    (hw : w.halted = false)
    (hb : MSim κ ω L ⟨if o.eval f = 0 then e else t, k, f, h, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.ite o t e, k, f, h, w, c⟩ k Q prot r pf :=
  (MSim.pre (s := ⟨.ite o t e, k, f, h, w, c⟩)
    (s₀ := ⟨if o.eval f = 0 then e else t, k, f, h, w, c⟩) (δ := 0)
    (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)) rfl rfl
    (fun _ _ => rfl) (fun _ _ _ => rfl) hb).of_eq rfl rfl (by simp)

/-- The `then` arm of a Flat `ite`. -/
theorem MSim.ite_t {o : Operand} {t e : Stmt} {k : List Kont} {f : Frame}
    {h : Heap} {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α}
    (hw : w.halted = false) (ho : o.eval f ≠ 0) (hb : MSim κ ω L ⟨t, k, f, h, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.ite o t e, k, f, h, w, c⟩ k Q prot r pf :=
  MSim.ite hw (by simpa [ho] using hb)

/-- The `else` arm of a Flat `ite`. -/
theorem MSim.ite_e {o : Operand} {t e : Stmt} {k : List Kont} {f : Frame}
    {h : Heap} {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α}
    (hw : w.halted = false) (ho : o.eval f = 0) (hb : MSim κ ω L ⟨e, k, f, h, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.ite o t e, k, f, h, w, c⟩ k Q prot r pf :=
  MSim.ite hw (by simpa [ho] using hb)

/-- Code with no subterm that reaches `f'` and `h'`, writing no protected frame slot. -/
theorem MSim.reaches_done {st : Stmt} {k : List Kont} {f f' : Frame} {h h' : Heap} {w : World}
    {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α} (hw : w.halted = false)
    (hr : Reaches κ ω L st f h f' h') (hrw : r.world = w) (hrs : r.steps = 0) (hf : f' BP = f BP)
    (hv : Q r.val f' h') (hm : ∀ a, prot a → h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hk : ∀ x, FR ≤ x → pf x → f' x = f x) :
    MSim κ ω L ⟨st, k, f, h, w, c⟩ k Q prot r pf :=
  ⟨⟨.skip, k, f', h', w, c⟩, hr k w c hw, hrw.symm, by simp [hrs],
    Or.inr ⟨rfl, rfl, by simp [hrs], hf, hv, hm, hk⟩⟩

/-- A tick, then code that computes a value into the slots from `K`, as in tail mode `word K`. It
reaches a frame `f'` that holds the value from `K` and keeps the slots from `FR` up to `K`, which are
those of the protected variables, and the memory is unchanged. -/
theorem MSim.tick_word {t : Tick} {X : Stmt} {k : List Kont} {f f' : Frame} {h : Heap} {w : World}
    {c K : Nat} {T : Ty} {r : Out T.carrier} {bp d : Nat} {ρ : List Loc}
    {S : List SI} {prot : Nat → Prop} (hw : w.halted = false)
    (hX : Reaches κ ω L X f h f' h) (hrw : r.world = w) (hrs : r.steps = t.cost κ)
    (hf : f' BP = f BP) (hfk : ∀ x, FR ≤ x → x < K → f' x = f x) (hv : WordsRel T r.val f' K)
    (hpf : ∀ x, pf x → x < K) :
    MSim κ ω L ⟨.seq (.tick t) X, k, f, h, w, c⟩ k (TQ (.word K) bp d ρ S T) prot r pf :=
  (MSim.tick (r := ⟨r.val, r.world, 0⟩) hw (MSim.reaches_done hw hX (by rw [hrw]) rfl hf hv
    (fun _ _ => rfl) (fun x hx hp => hfk x hx (hpf x hp)))).of_eq rfl rfl (by simp [hrs])

/-- A tick, then tick-free code producing the result. -/
theorem MSim.tick_done {t : Tick} {rest : Stmt} {k : List Kont} {f f' : Frame}
    {h h' : Heap} {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out α}
    (hw : w.halted = false)
    (hr : Runs κ ω L rest f h f' h') (hrw : r.world = w) (hrs : r.steps = t.cost κ)
    (hf : f' BP = f BP) (hv : Q r.val f' h')
    (hm : ∀ a, prot a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MSim κ ω L ⟨.seq (.tick t) rest, k, f, h, w, c⟩ k Q prot r pf :=
  (MSim.tick (r := ⟨r.val, r.world, 0⟩) hw (MSim.done hw hr (by rw [hrw]) rfl hf hv hm)).of_eq
    rfl rfl (by simp [hrs])

end

/-! ## Lists of variables -/

theorem headD_eq_getD (W : List Bool) : W.headD false = W.getD 0 false := by cases W <;> rfl

theorem tail_getD (W : List Bool) (i : Nat) : W.tail.getD i false = W.getD (i + 1) false := by
  cases W <;> simp

theorem noW_headD (W : List Bool) : (noW W).headD false = false := by
  rw [headD_eq_getD]; exact noW_getD W 0

theorem noW_tail (W : List Bool) : (noW W).tail = noW W.tail := by cases W <;> rfl

/-! ## Layout lemmas -/

section Layout
variable {bp n : Nat}

theorem Compat.symm {t t' : Ty} {l l' : Loc} {s s' : SI} {w w' : Bool}
    (h : Compat bp t l s w t' l' s' w') : Compat bp t' l' s' w' t l s w :=
  ⟨by rcases h.1 with e | e <;> unfold Disj <;> omega, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem CompatAll.get {t : Ty} {l : Loc} {s : SI} {w : Bool} {t' : Ty} :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} (m : Mem t' ts),
    CompatAll bp t l s w ts ρ S W → ρ.length = ts.length → S.length = ts.length →
    Compat bp t l s w t' (ρ.getD m.idx default) (S.getD m.idx default) (W.getD m.idx false)
  | _ :: _, _ :: _, _ :: _, W, .here, h, _, _ => by
    show Compat _ _ _ _ _ _ _ _ (W.getD 0 false); rw [← headD_eq_getD]; exact h.1
  | _ :: _, _ :: _, _ :: _, W, .there m, h, hρ, hS => by
    have := CompatAll.get m h.2 (by simpa using hρ) (by simpa using hS)
    show Compat _ _ _ _ _ _ _ _ (W.getD (m.idx + 1) false); rw [← tail_getD]; exact this
  | _ :: _, [], _, _, _, _, hρ, _ => by simp at hρ
  | _ :: _, _ :: _, [], _, _, _, _, hS => by simp at hS

theorem Lay.length : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    Lay bp n Γ ρ S W → ρ.length = Γ.length ∧ S.length = Γ.length
  | [], [], [], _, _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, _, hl => by
    have := Lay.length hl.2.2; simp [this.1, this.2]
  | [], _ :: _, _, _, hl => hl.elim
  | [], [], _ :: _, _, hl => hl.elim
  | _ :: _, [], _, _, hl => hl.elim
  | _ :: _, _ :: _, [], _, hl => hl.elim

/-- The facts about variable `m`. -/
theorem Lay.var : ∀ {t : Ty} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    (m : Mem t Γ), Lay bp n Γ ρ S W →
    Single bp n t (ρ.getD m.idx default) (S.getD m.idx default) (W.getD m.idx false)
  | _, _ :: _, _ :: _, _ :: _, W, .here, hl => by
    show Single _ _ _ _ _ (W.getD 0 false); rw [← headD_eq_getD]; exact hl.1
  | _, _ :: _, _ :: _, _ :: _, W, .there m, hl => by
    have := Lay.var m hl.2.2
    show Single _ _ _ _ _ (W.getD (m.idx + 1) false); rw [← tail_getD]; exact this
  | _, _ :: _, [], _, _, _, hl => hl.elim
  | _, _ :: _, _ :: _, [], _, _, hl => hl.elim

/-- The facts about two distinct variables. -/
theorem Lay.pair : ∀ {t t' : Ty} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    (m : Mem t Γ) (m' : Mem t' Γ), m.idx ≠ m'.idx → Lay bp n Γ ρ S W →
    Compat bp t (ρ.getD m.idx default) (S.getD m.idx default) (W.getD m.idx false)
      t' (ρ.getD m'.idx default) (S.getD m'.idx default) (W.getD m'.idx false)
  | _, _, _ :: _, _ :: _, _ :: _, W, .here, .here, hne, _ => absurd rfl hne
  | _, _, _ :: _, _ :: _, _ :: _, W, .here, .there m', _, hl => by
    have hlen := Lay.length hl.2.2
    have := CompatAll.get m' hl.2.1 hlen.1 hlen.2
    show Compat _ _ _ _ (W.getD 0 false) _ _ _ (W.getD (m'.idx + 1) false)
    rw [← headD_eq_getD, ← tail_getD]; exact this
  | _, _, _ :: _, _ :: _, _ :: _, W, .there m, .here, _, hl => by
    have hlen := Lay.length hl.2.2
    have := (CompatAll.get m hl.2.1 hlen.1 hlen.2).symm
    show Compat _ _ _ _ (W.getD (m.idx + 1) false) _ _ _ (W.getD 0 false)
    rw [← headD_eq_getD, ← tail_getD]; exact this
  | _, _, _ :: _, _ :: _, _ :: _, W, .there m, .there m', hne, hl => by
    have := Lay.pair m m' (fun e => hne (by simp [Mem.idx, e])) hl.2.2
    show Compat _ _ _ _ (W.getD (m.idx + 1) false) _ _ _ (W.getD (m'.idx + 1) false)
    rw [← tail_getD, ← tail_getD]; exact this
  | _, _, _ :: _, [], _, _, _, _, _, hl => hl.elim
  | _, _, _ :: _, _ :: _, [], _, _, _, _, hl => hl.elim

/-- A variable without an extent has no second piece, since only a pair reference has one and a
pair reference has an extent. -/
theorem Single.snd_none {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w)
    (he : s.ext = none) : s.snd = none := by
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | own o => exact h2.2.2
  | slot o _ _ => exact h2.2.2
  | ref o => exact h2.1
  | ref2 o =>
    obtain ⟨_, _, _, _, he', _⟩ := h2.1
    rw [he] at he'; cases he'

/-- A variable with an extent or a second piece, that is a view or a pair reference, is in memory. -/
theorem Single.ns_of_ext {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w)
    (he : s.ext ≠ none ∨ s.snd ≠ none) : l.isSlot = false := by
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | slot o k _ =>
    exfalso; rcases he with he | he
    · exact he h2.2.1
    · exact he h2.2.2
  | _ => rfl

/-- A variable without a second piece is not at a two-address location. -/
theorem Single.not_ref2 {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w)
    (hs : s.snd = none) (o : Nat) : l ≠ .ref2 o := by
  rintro rfl
  obtain ⟨_, _, _, h2, _⟩ := h.2.1.1
  rw [hs] at h2; cases h2

/-- A variable whose type is not a pair has no second piece. -/
theorem Single.snd_none_of_ty {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w)
    (ht : ∀ fs, t.data.shape ≠ .prod fs) : s.snd = none := by
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | own o => exact h2.2.2
  | slot o _ _ => exact h2.2.2
  | ref o => exact h2.1
  | ref2 o =>
    obtain ⟨_, _, hsh, _⟩ := h2.1
    exact absurd hsh (ht _)

/-- A variable whose type is neither a `Slots`, the type of a view, nor a pair has no extent. -/
theorem VarRel.ext_none {h : Heap} {t : Ty} {v : t.carrier} {s : SI} (hv : VarRel h t v s)
    (hsnd : s.snd = none) (ht : ∀ cnt sh, t.data.shape ≠ .slots cnt sh) : s.ext = none := by
  obtain ⟨_, _, _, hx⟩ := hv
  cases he : s.ext with
  | none => rfl
  | some e =>
    obtain ⟨cnt, _, sh, hs, _⟩ := hx e he hsnd
    exact absurd hs (ht cnt sh)

/-- A variable's run-time knowledge is well formed for its type. -/
theorem Single.ok {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) : s.Ok t := by
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | own o => exact Or.inl h2.2.2
  | slot o _ _ => exact Or.inl h2.2.2
  | ref o => exact Or.inl h2.1
  | ref2 o => exact Or.inr h2.1

/-- A variable's storage lies below the watermark. -/
theorem Single.below {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) :
    s.Below t (bp + n) := by
  obtain ⟨h1, h2, _⟩ := h
  cases l with
  | own o =>
    simp only [Loc.off, Loc.size] at h1 h2
    have := s.sz_le t
    simp only [SI.Below, h2.2.2]; omega
  | slot o _ _ =>
    simp only [Loc.off, Loc.size] at h1 h2
    have := s.sz_le t
    simp only [SI.Below, h2.2.2]; omega
  | ref o => simp only [SI.Below, h2.1]; exact h2.2.1
  | ref2 o => exact h2.2.1

/-- A variable's storage lies below the watermark, stated pointwise. -/
theorem Single.lt {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) {x : Nat}
    (hx : s.In t x) : x < bp + n := h.below.lt hx

/-- The storage of a variable without a second piece lies below the watermark. -/
theorem Single.dataLe {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w)
    (hs : s.snd = none) : s.A + s.sz t ≤ bp + n := by
  have := h.below; simp only [SI.Below, hs] at this; exact this

/-- A variable's storage is away from its own pointer slot. -/
theorem Single.ptrOut {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) :
    ∀ o w', l.ptr = some (o, w') → s.Out t (bp + o) w' := by
  intro o w' e
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | own o => cases e
  | slot o _ _ => cases e
  | ref o' =>
    simp only [Loc.ptr, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    rw [SI.Out_none h2.1]; exact h2.2.2
  | ref2 o' =>
    simp only [Loc.ptr, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    exact h2.2.2

theorem Single.slotLe {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) :
    l.off + l.size t ≤ n := h.1

theorem Single.mono {t : Ty} {l : Loc} {s : SI} {w : Bool} {m : Nat} (h : Single bp n t l s w)
    (hm : n ≤ m) : Single bp m t l s w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, ?_, h3, h4⟩
  cases l with
  | own o => exact h2
  | slot o _ _ => exact h2
  | ref o => exact ⟨h2.1, by have := h2.2.1; omega, h2.2.2⟩
  | ref2 o => exact ⟨h2.1, h2.2.1.mono (by omega), h2.2.2⟩

theorem Single.noW {t : Ty} {l : Loc} {s : SI} {w : Bool} (h : Single bp n t l s w) :
    Single bp n t l s false :=
  ⟨h.1, h.2.1, (fun e => by cases e), h.2.2.2⟩

theorem Compat.noW {t t' : Ty} {l l' : Loc} {s s' : SI} {w w' : Bool}
    (h : Compat bp t l s w t' l' s' w') : Compat bp t l s false t' l' s' false :=
  ⟨h.1, h.2.1, h.2.2.1, (fun e => by cases e), (fun e => by cases e)⟩

theorem CompatAll.mono_noW {t : Ty} {l : Loc} {s : SI} {w : Bool} :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    CompatAll bp t l s w ts ρ S W → CompatAll bp t l s false ts ρ S (noW W)
  | _ :: _, _ :: _, _ :: _, W, h => by
    refine ⟨by rw [noW_headD]; exact h.1.noW, ?_⟩
    rw [noW_tail]; exact CompatAll.mono_noW h.2
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _ => trivial

/-- Fewer writable variables keep the layout. -/
theorem Lay.noW : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    Lay bp n Γ ρ S W → Lay bp n Γ ρ S (noW W)
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, W, hl => by
    refine ⟨by rw [noW_headD]; exact hl.1.noW, by rw [noW_headD, noW_tail]; exact hl.2.1.mono_noW,
      by rw [noW_tail]; exact Lay.noW hl.2.2⟩
  | [], _ :: _, _, _, hl => hl.elim
  | [], [], _ :: _, _, hl => hl.elim
  | _ :: _, [], _, _, hl => hl.elim
  | _ :: _, _ :: _, [], _, hl => hl.elim

theorem CompatAll.congrW {t : Ty} {l : Loc} {s : SI} {w : Bool} :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W W' : List Bool},
    (∀ i, W.getD i false = W'.getD i false) →
    CompatAll bp t l s w ts ρ S W → CompatAll bp t l s w ts ρ S W'
  | _ :: _, _ :: _, _ :: _, W, W', hW, h => by
    refine ⟨by rw [headD_eq_getD, ← hW 0, ← headD_eq_getD]; exact h.1, ?_⟩
    exact CompatAll.congrW (fun i => by rw [tail_getD, tail_getD, hW]) h.2
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _, _ => trivial

theorem Lay.mono {m : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    Lay bp n Γ ρ S W → n ≤ m → Lay bp m Γ ρ S W
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, hl, hm => ⟨hl.1.mono hm, hl.2.1, Lay.mono hl.2.2 hm⟩
  | [], _ :: _, _, _, hl, _ => hl.elim
  | [], [], _ :: _, _, hl, _ => hl.elim
  | _ :: _, [], _, _, hl, _ => hl.elim
  | _ :: _, _ :: _, [], _, hl, _ => hl.elim

/-- Every slot and every value lie below the watermark. -/
theorem Lay.away {o sz : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    Lay bp n Γ ρ S W → n ≤ o → Away bp o sz Γ ρ S
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, hl, ho => by
    have h1 := hl.1.slotLe
    exact ⟨Or.inr (by omega), hl.1.below.out (by omega), Lay.away hl.2.2 ho⟩
  | [], _ :: _, _, _, hl, _ => hl.elim
  | [], [], _ :: _, _, hl, _ => hl.elim
  | _ :: _, [], _, _, hl, _ => hl.elim
  | _ :: _, _ :: _, [], _, hl, _ => hl.elim

theorem SI.Out.sub {s : SI} {t : Ty} {a len a' len' : Nat} (h : s.Out t a len) (h1 : a ≤ a')
    (h2 : a' + len' ≤ a + len) : s.Out t a' len' := by
  unfold SI.Out Disj at *
  cases hs : s.snd with
  | none => simp only [hs] at h ⊢; omega
  | some p => obtain ⟨f, A2⟩ := p; simp only [hs] at h ⊢; omega

theorem Away.sub {o sz o' sz' : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI},
    Away bp o sz Γ ρ S → o ≤ o' → o' + sz' ≤ o + sz → Away bp o' sz' Γ ρ S
  | _ :: _, _ :: _, _ :: _, ha, h1, h2 =>
    ⟨by rcases ha.1 with e | e <;> unfold Disj <;> omega,
     ha.2.1.sub (by omega) (by omega), Away.sub ha.2.2 h1 h2⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _ => trivial

/-- A destination away from all variables is away from variable `m`. -/
theorem Away.var {o sz : Nat} : ∀ {t : Ty} {Γ : List Ty} {ρ : List Loc} {S : List SI}
    (m : Mem t Γ), Away bp o sz Γ ρ S → ρ.length = Γ.length → S.length = Γ.length →
    Disj o sz (ρ.getD m.idx default).off ((ρ.getD m.idx default).size t) ∧
      (S.getD m.idx default).Out t (bp + o) sz
  | _, _ :: _, _ :: _, _ :: _, .here, ha, _, _ => ⟨ha.1, ha.2.1⟩
  | _, _ :: _, _ :: _, _ :: _, .there m, ha, hρ, hS => by
    simpa [Mem.idx] using Away.var m ha.2.2 (by simpa using hρ) (by simpa using hS)
  | _, _ :: _, [], _, _, _, hρ, _ => by simp at hρ
  | _, _ :: _, _ :: _, [], _, _, _, hS => by simp at hS

/-- A fresh variable at an offset `o` away from every variable: owned, or slot-resident with its
reserved bytes at `o`. -/
theorem Lay.pushAtL (s : Ty) (b : Bool) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} {o m : Nat} {l : Loc} (hlo : l = .own o ∨ ∃ K w, l = .slot o K w)
    (hl : Lay bp n Γ ρ S W) (ha : Away bp o s.size Γ ρ S)
    (ho : o + s.size ≤ m) (hn : n ≤ m) :
    Lay bp m (s :: Γ) (l :: ρ) (⟨bp + o, none, none, none⟩ :: S) (b :: W) := by
  have hoff : l.off = o ∧ l.size s = s.size ∧ l.ptr = none := by
    rcases hlo with rfl | ⟨K, w, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  refine ⟨⟨by rw [hoff.1, hoff.2.1]; omega, by rcases hlo with rfl | ⟨K, w, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩,
    fun _ => rfl, fun H h => by cases h⟩, ?_, hl.mono hn⟩
  show CompatAll bp s l ⟨bp + o, none, none, none⟩ b Γ ρ S W
  induction Γ generalizing ρ S W with
  | nil => trivial
  | cons t ts ih =>
    cases ρ with
    | nil => trivial
    | cons l' ρ =>
      cases S with
      | nil => trivial
      | cons s' S =>
        obtain ⟨ha1, ha2, ha3⟩ := ha
        refine ⟨⟨by rw [hoff.1, hoff.2.1]; exact ha1, (fun o' w e => by rw [hoff.2.2] at e; cases e),
          (fun o' w e => ?_), (fun _ x hx hx' => ?_), (fun _ x hx hx' => ?_)⟩, ih hl.2.2 ha3⟩
        · obtain ⟨e1, e2⟩ := Loc.ptr_size e t
          rw [e1, e2] at ha1
          show Disj (bp + o') w (bp + o) ((SI.mk (bp + o) none none none).sz s)
          rw [SI.sz_mk_none]; unfold Disj at ha1 ⊢; omega
        · exfalso; rw [SI.In_mk, SI.sz_mk_none] at hx; exact ha2.not_In hx hx'
        · exfalso; rw [SI.In_mk, SI.sz_mk_none] at hx'; exact ha2.not_In hx' hx

/-- A fresh owned variable at an offset `o` away from every variable. -/
theorem Lay.pushAt (s : Ty) (b : Bool) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} {o m : Nat} (hl : Lay bp n Γ ρ S W) (ha : Away bp o s.size Γ ρ S)
    (ho : o + s.size ≤ m) (hn : n ≤ m) :
    Lay bp m (s :: Γ) (.own o :: ρ) (⟨bp + o, none, none, none⟩ :: S) (b :: W) :=
  Lay.pushAtL s b (Or.inl rfl) hl ha ho hn

/-- A fresh owned variable at the watermark. -/
theorem Lay.push (s : Ty) (b : Bool) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} (hl : Lay bp n Γ ρ S W) :
    Lay bp (n + s.size) (s :: Γ) (.own n :: ρ) (⟨bp + n, none, none, none⟩ :: S) (b :: W) :=
  Lay.pushAt s b hl (hl.away (Nat.le_refl _)) (Nat.le_refl _) (by omega)

/-- A fresh slot-resident variable with its reserved bytes at the watermark. -/
theorem Lay.pushSlot (s : Ty) (b : Bool) (K w : Nat) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} (hl : Lay bp n Γ ρ S W) :
    Lay bp (n + s.size) (s :: Γ) (.slot n K w :: ρ) (⟨bp + n, none, none, none⟩ :: S) (b :: W) :=
  Lay.pushAtL s b (Or.inr ⟨K, w, rfl⟩) hl (hl.away (Nat.le_refl _)) (Nat.le_refl _) (by omega)

/-- A destination below the watermark is away from a fresh variable at the watermark, owned or
slot-resident. -/
theorem Away.pushL {o sz : Nat} (s : Ty) {Γ : List Ty} {ρ : List Loc} {S : List SI} {l : Loc}
    (hl : l.off = n ∧ l.size s = s.size)
    (ha : Away bp o sz Γ ρ S) (ho : o + sz ≤ n) :
    Away bp o sz (s :: Γ) (l :: ρ) (⟨bp + n, none, none, none⟩ :: S) :=
  ⟨by rw [hl.1, hl.2]; exact Or.inl ho, Or.inl (by show bp + o + sz ≤ bp + n; omega), ha⟩

theorem Away.push {o sz : Nat} (s : Ty) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    (ha : Away bp o sz Γ ρ S) (ho : o + sz ≤ n) :
    Away bp o sz (s :: Γ) (.own n :: ρ) (⟨bp + n, none, none, none⟩ :: S) :=
  Away.pushL s ⟨rfl, rfl⟩ ha ho

end Layout

/-! ## Representation lemmas -/

/-- Without a hole, an extent or a second piece, a variable's value is represented by its bytes. -/
theorem VarRel.exact {h : Heap} {t : Ty} {v : t.carrier} {s : SI} (hv : VarRel h t v s)
    (hs : s.hole = none) (he : s.ext = none := by rfl) (hsn : s.snd = none := by rfl) :
    Data.reprBytes v (rd h s.A t.size) := by
  obtain ⟨B, hB, hm, _⟩ := hv
  rw [rd_of_getD (Data.reprBytes_length hB) fun i hi => by
    have := hm i (by rw [SI.sz_none he]; exact hi) (by simp [SI.inHole, hs])
    rwa [SI.at_none hsn] at this]
  exact hB

theorem VarRel.of_exact {h : Heap} {t : Ty} {v : t.carrier} {s : SI}
    (hv : Data.reprBytes v (rd h s.A t.size)) (he : s.ext = none := by rfl)
    (hsn : s.snd = none := by rfl) : VarRel h t v s :=
  ⟨_, hv, fun i hi _ => by
    rw [SI.at_none hsn]; exact (rd_getD h s.A t.size i (by have := s.sz_le t; omega)).symm,
    fun e h' => by rw [he] at h'; cases h'⟩

theorem VarRel.congr {h h' : Heap} {t : Ty} {v : t.carrier} {s : SI} (hv : VarRel h t v s)
    (hm : ∀ x, s.In t x → ¬ s.inHole x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) :
    VarRel h' t v s := by
  obtain ⟨B, hB, hb, hx⟩ := hv
  exact ⟨B, hB, fun i hi hn => (hm _ (SI.In_at hi) hn).trans (hb i hi hn), hx⟩

theorem PtrOk.congr {h h' : Heap} {bp : Nat} {l : Loc} {s : SI} (hp : PtrOk h bp l s)
    (hm : ∀ o w, l.ptr = some (o, w) → ∀ x, InR (bp + o) w x →
      h' (UInt64.ofNat x) = h (UInt64.ofNat x)) :
    PtrOk h' bp l s := by
  cases l with
  | own o => trivial
  | slot o _ _ => trivial
  | ref o =>
    show decodeLE (rd h' (bp + o) 8) = _
    rw [rd_congr fun i hi => hm o 8 rfl _ ⟨by omega, by omega⟩]; exact hp
  | ref2 o =>
    refine ⟨?_, fun f A2 e => ?_⟩
    · show decodeLE (rd h' (bp + o) 8) = _
      rw [rd_congr fun i hi => hm o 16 rfl _ ⟨by omega, by omega⟩]; exact hp.1
    · rw [rd_congr fun i hi => hm o 16 rfl _ ⟨by omega, by omega⟩]; exact hp.2 f A2 e

/-- `x` is in some variable's visible storage or in some pointer slot. -/
def Vis (bp : Nat) : List Ty → List Loc → List SI → Nat → Prop
  | t :: ts, l :: ρ, s :: S, x =>
    (s.In t x ∧ ¬ s.inHole x) ∨ (∃ o w, l.ptr = some (o, w) ∧ InR (bp + o) w x) ∨
      Vis bp ts ρ S x
  | _, _, _, _ => False

/-- The representation of the environment only depends on the visible bytes. -/
theorem MEnvRel.congr {h h' : Heap} {bp : Nat} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    {S : List SI}, MEnvRel h bp env ρ S →
    (∀ x, Vis bp Γ ρ S x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) → MEnvRel h' bp env ρ S
  | _, .nil, _, _, _, _ => trivial
  | _, .cons _ _, l :: ρ, s :: S, hr, hm =>
    ⟨fun hs => (hr.1 hs).congr fun x h1 h2 => hm x (Or.inl ⟨h1, h2⟩),
     hr.2.1.congr fun o w e x hx => hm x (Or.inr (Or.inl ⟨o, w, e, hx⟩)),
     MEnvRel.congr hr.2.2 fun x hx => hm x (Or.inr (Or.inr hx))⟩
  | _, .cons _ _, [], _, hr, _ => hr.elim
  | _, .cons _ _, _ :: _, [], hr, _ => hr.elim

theorem Lay.vis_lt {bp n : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    {x : Nat}, Lay bp n Γ ρ S W → Vis bp Γ ρ S x → x < bp + n
  | t :: _, _ :: _, _ :: _, _, x, hl, hv => by
    rcases hv with ⟨h1, _⟩ | ⟨o, w, e, h1⟩ | hv
    · exact hl.1.lt h1
    · have := hl.1.slotLe; obtain ⟨e1, e2⟩ := Loc.ptr_size e t
      unfold InR at h1; omega
    · exact Lay.vis_lt hl.2.2 hv
  | [], _, _, _, _, _, hv => hv.elim
  | _ :: _, [], _, _, _, _, hv => hv.elim
  | _ :: _, _ :: _, [], _, _, _, hv => hv.elim

theorem Away.not_vis {bp o sz : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {x : Nat},
    Away bp o sz Γ ρ S → InR (bp + o) sz x → ¬ Vis bp Γ ρ S x
  | t :: _, l :: _, _ :: _, x, ha, hx, hv => by
    rcases hv with ⟨h1, _⟩ | ⟨o', w, e, h1⟩ | hv
    · exact ha.2.1.not_In hx h1
    · obtain ⟨e1, e2⟩ := Loc.ptr_size e t
      have := ha.1; rw [e1, e2] at this
      rcases this with e | e <;> unfold InR at hx h1 <;> omega
    · exact Away.not_vis ha.2.2 hx hv
  | [], _, _, _, _, _, hv => hv
  | _ :: _, [], _, _, _, _, hv => hv
  | _ :: _, _ :: _, [], _, _, _, hv => hv

/-- Writes at or above the watermark keep the environment. -/
theorem MEnvRel.above {h h' : Heap} {bp n : Nat} {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    {S : List SI} {W : List Bool} (hr : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hm : ∀ a, a < bp + n → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) : MEnvRel h' bp env ρ S :=
  hr.congr fun x hx => hm x (hl.vis_lt hx)

/-- A write away from every variable keeps the environment. -/
theorem MEnvRel.wr_away {h : Heap} {bp n d : Nat} {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    {S : List SI} {W : List Bool} (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hbn : bp + n ≤ UInt64.size) (B : List UInt8) (ha : Away bp d B.length Γ ρ S)
    (hb : bp + d + B.length ≤ UInt64.size) : MEnvRel (wr h (bp + d) B) bp env ρ S :=
  henv.congr fun x hx => by
    have := hl.vis_lt hx
    exact wr_other h (bp + d) B x (by omega) hb (by
      by_cases h1 : x < bp + d
      · exact Or.inl h1
      · exact Or.inr (Nat.le_of_not_lt fun h2 => ha.not_vis ⟨by omega, by omega⟩ hx))

/-- With no writable variable, a visible address is in no writable storage. -/
theorem InW.noW : ∀ {Γ : List Ty} {S : List SI} {W : List Bool} {x : Nat}, ¬ InW Γ S (noW W) x
  | _ :: _, _ :: _, W, x, h => by
    rcases h with ⟨h, _⟩ | h
    · rw [noW_headD] at h; cases h
    · rw [noW_tail] at h; exact InW.noW h
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h

/-- When no variable is writable, memory unchanged on the protected addresses is unchanged on the
variables. -/
theorem MEnvRel.of_prot {h h' : Heap} {bp n d sz : Nat} {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} {W W' : List Bool} (hr : MEnvRel h bp env ρ S)
    (hl : Lay bp n Γ ρ S W') (ha : Away bp d sz Γ ρ S)
    (hm : ∀ a, Prot bp n d sz Γ S (noW W) a → h' (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MEnvRel h' bp env ρ S :=
  hr.congr fun x hx => hm _ ⟨hl.vis_lt hx, fun h1 => ha.not_vis h1 hx, InW.noW⟩

/-- What the relation says of variable `m`: the representation of its value when it is in memory,
and its reference slot. -/
theorem MEnvRel.get' {h : Heap} {bp : Nat} {t : Ty} : ∀ {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} (m : Mem t Γ), MEnvRel h bp env ρ S →
    ((ρ.getD m.idx default).isSlot = false ∨ t.slotTy = false →
      VarRel h t (env.get m) (S.getD m.idx default)) ∧
      PtrOk h bp (ρ.getD m.idx default) (S.getD m.idx default)
  | _, .cons _ _, _ :: _, _ :: _, .here, hr => ⟨hr.1, hr.2.1⟩
  | _, .cons _ _, _ :: _, _ :: _, .there m, hr => by
    simpa [Mem.idx] using MEnvRel.get' m hr.2.2
  | _, .cons _ _, [], _, _, hr => hr.elim
  | _, .cons _ _, _ :: _, [], _, hr => hr.elim

/-- The value of a variable in memory. -/
theorem MEnvRel.get {h : Heap} {bp : Nat} {t : Ty} {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} (m : Mem t Γ) (hr : MEnvRel h bp env ρ S)
    (hns : (ρ.getD m.idx default).isSlot = false) :
    VarRel h t (env.get m) (S.getD m.idx default) ∧
      PtrOk h bp (ρ.getD m.idx default) (S.getD m.idx default) :=
  ⟨(hr.get' m).1 (Or.inl hns), (hr.get' m).2⟩

/-- The value of a variable of a type that is never slot-resident. -/
theorem MEnvRel.get_ty {h : Heap} {bp : Nat} {t : Ty} {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} (m : Mem t Γ) (hr : MEnvRel h bp env ρ S)
    (ht : t.slotTy = false) :
    VarRel h t (env.get m) (S.getD m.idx default) ∧
      PtrOk h bp (ρ.getD m.idx default) (S.getD m.idx default) :=
  ⟨(hr.get' m).1 (Or.inr ht), (hr.get' m).2⟩

/-- Changing a slot-resident variable's value keeps the memory relation. -/
theorem MEnvRel.set_slot {h : Heap} {bp : Nat} {t : Ty} : ∀ {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} (m : Mem t Γ) (v : t.carrier),
    t.slotTy = true → (ρ.getD m.idx default).isSlot = true → MEnvRel h bp env ρ S →
    MEnvRel h bp (env.set m v) ρ S
  | _, .cons _ _, _ :: _, _ :: _, .here, _, ht, hs, hr =>
    ⟨(fun h' => by simp [Mem.idx] at hs; rw [hs, ht] at h'; simp at h'), hr.2.1, hr.2.2⟩
  | _, .cons _ _, _ :: _, _ :: _, .there m, v, ht, hs, hr =>
    ⟨hr.1, hr.2.1, MEnvRel.set_slot m v ht (by simpa [Mem.idx] using hs) hr.2.2⟩
  | _, .cons _ _, [], _, _, _, _, _, hr => hr.elim
  | _, .cons _ _, _ :: _, [], _, _, _, _, hr => hr.elim

/-! ## Holes and atoms -/

/-- An atom that respects every hole's loan reads no variable with a hole. -/
theorem _root_.Millipede.Atom.noHole {Γ : List Ty} {t : Ty} {S : List SI} (a : Atom Γ t)
    (ha : ∀ i H, (S.getD i default).hole = some H → a.Avoids i ⟨true, H.path⟩) :
    ∀ m, a = .var m → (S.getD m.idx default).hole = none := by
  intro m e; subst e
  cases hh : (S.getD m.idx default).hole with
  | none => rfl
  | some H =>
    have := ha m.idx H hh rfl
    simp [Loan.blocks, Sel.overlap_nil_right] at this

/-- `HoleAv` passes to a subterm in the same context. -/
theorem HoleAv.sub {Γ : List Ty} {t u : Ty} {e : Exp Γ t} {e' : Exp Γ u} {S : List SI}
    (h : HoleAv e S) (he : ∀ i l, e.Avoids i l → e'.Avoids i l) : HoleAv e' S :=
  fun i H hH => he _ _ (h i H hH)

/-- `HoleAv` passes to a subterm under a binder without a hole. -/
theorem HoleAv.push {Γ : List Ty} {t u s : Ty} {e : Exp Γ t} {e' : Exp (s :: Γ) u} {S : List SI}
    (si : SI) (hsi : si.hole = none) (h : HoleAv e S)
    (he : ∀ i l, e.Avoids i l → e'.Avoids (i + 1) l) : HoleAv e' (si :: S) := by
  intro i H hH
  cases i with
  | zero => simp [hsi] at hH
  | succ i => exact he _ _ (h i H (by simpa using hH))

/-- `HoleAv` passes to a subterm under two binders without a hole. -/
theorem HoleAv.push2 {Γ : List Ty} {t u s₁ s₂ : Ty} {e : Exp Γ t} {e' : Exp (s₁ :: s₂ :: Γ) u}
    {S : List SI} (si sj : SI) (hsi : si.hole = none) (hsj : sj.hole = none) (h : HoleAv e S)
    (he : ∀ i l, e.Avoids i l → e'.Avoids (i + 2) l) : HoleAv e' (si :: sj :: S) := by
  intro i H hH
  match i, hH with
  | 0, hH => simp [hsi] at hH
  | 1, hH => simp [hsj] at hH
  | i + 2, hH => exact he _ _ (h i H (by simpa using hH))

/-! ## Slot-resident variables

The frame relation `FEnvRel` says that the slots of each slot-resident variable hold the words of its
value. The slots are numbered from `FR` in binding order, so distinct variables have disjoint slots
and a new binder's slots are none of the old ones. Scratch code keeps every slot from `FR` on, and a
subterm keeps the slots of the variables it may not write. -/

section Slots

/-! ### Words of chunks -/

theorem WordsAt.congr {f f' : Frame} : ∀ {k : Nat} {B : List UInt8} {n : Nat},
    WordsAt f k B n → (∀ x, k ≤ x → x < k + n → f' x = f x) → WordsAt f' k B n
  | _, _, 0, _, _ => trivial
  | k, _, n + 1, h, hm => ⟨by rw [hm k (Nat.le_refl _) (by omega)]; exact h.1,
      WordsAt.congr h.2 fun x h1 h2 => hm x (by omega) (by omega)⟩

theorem WordsRel.congr {f f' : Frame} {t : Ty} {v : t.carrier} {k : Nat} (h : WordsRel t v f k)
    (hm : ∀ x, k ≤ x → x < k + t.slotN → f' x = f x) : WordsRel t v f' k :=
  let ⟨B, hB, hw⟩ := h; ⟨B, hB, hw.congr hm⟩

/-! ### The frame relation -/

theorem FEnvRel.get {f : Frame} {t : Ty} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    (m : Mem t Γ), FEnvRel f env ρ → ∀ {k : Nat}, (ρ.getD m.idx default).slot? = some k →
    t.slotTy = true ∧ (ρ.getD m.idx default).nw = t.slotN ∧ WordsRel t (env.get m) f k
  | _, .cons _ _, l :: _, .here, hr, k, hk => by
    cases l with
    | slot o k' n =>
      simp only [Mem.idx, List.getD_cons_zero, Loc.slot?_slot, Option.some.injEq] at hk
      subst hk; exact ⟨hr.1.2.1, hr.1.2.2.1, hr.1.2.2.2⟩
    | _ => simp [Mem.idx] at hk
  | _, .cons _ _, _ :: _, .there m, hr, _, hk => FEnvRel.get m hr.2 (by simpa [Mem.idx] using hk)
  | _, .cons _ _, [], _, hr, _, _ => hr.elim

theorem FEnvRel.congr {f f' : Frame} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc},
    FEnvRel f env ρ → (∀ i x, (ρ.getD i default).holds x = true → f' x = f x) →
    FEnvRel f' env ρ
  | _, .nil, _, hr, _ => hr
  | _, .cons _ _, l :: _, hr, hm => by
    refine ⟨?_, FEnvRel.congr hr.2 fun i x hx => hm (i + 1) x (by simpa using hx)⟩
    have h1 := hr.1
    cases l with
    | slot o k n =>
      obtain ⟨h1, h2, h3, hw⟩ := h1
      exact ⟨h1, h2, h3, hw.congr fun x hx1 hx2 => hm 0 x (by simp; omega)⟩
    | _ => trivial
  | _, .cons _ _, [], hr, _ => hr.elim

/-- A context without slot-resident variables: any frame represents them. -/
theorem FEnvRel.of_none {f : Frame} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc},
    ρ.length = Γ.length → (∀ i, (ρ.getD i default).slot? = none) → FEnvRel f env ρ
  | _, .nil, _, hl, _ => List.eq_nil_of_length_eq_zero hl
  | _, .cons _ _, l :: _, hl, hn => by
    refine ⟨?_, FEnvRel.of_none (by simpa using hl) fun i => by simpa using hn (i + 1)⟩
    have := hn 0
    cases l <;> simp_all [SlotRel]
  | _, .cons _ _, [], hl, _ => by simp at hl

theorem SlotsOk.holds {ρ : List Loc} (h : SlotsOk ρ) (i x : Nat)
    (hx : (ρ.getD i default).holds x = true) : FR ≤ x ∧ x < FR + slotsIn ρ := by
  obtain ⟨k, hk, h1, h2⟩ := Loc.holds_iff.1 hx
  have := h.range i k hk; omega

/-- Distinct variables hold distinct slots. -/
theorem SlotsOk.inj : ∀ {ρ : List Loc}, SlotsOk ρ → ∀ {i j x : Nat},
    (ρ.getD i default).holds x = true → (ρ.getD j default).holds x = true → i = j
  | [], _, i, _, _, hi, _ => by simp at hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: _, h, 0, j + 1, x, hi, hj => by
    obtain ⟨k, hk, h1, _⟩ := Loc.holds_iff.1 hi
    have e := h.1 k (by simpa using hk)
    have := h.2.holds j x (by simpa using hj); omega
  | _ :: _, h, i + 1, 0, x, hi, hj => by
    obtain ⟨k, hk, h1, _⟩ := Loc.holds_iff.1 hj
    have e := h.1 k (by simpa using hk)
    have := h.2.holds i x (by simpa using hi); omega
  | _ :: ρ, h, i + 1, j + 1, x, hi, hj => by
    rw [SlotsOk.inj h.2 (i := i) (j := j) (x := x) (by simpa using hi) (by simpa using hj)]

/-- The slots `FR … FR + slotsIn ρ - 1` are all held by variables. -/
theorem SlotsOk.cover : ∀ {ρ : List Loc}, SlotsOk ρ → ∀ x, FR ≤ x → x < FR + slotsIn ρ →
    ∃ i, (ρ.getD i default).holds x = true
  | [], _, _, h1, hx => by simp only [slotsIn, Nat.add_zero] at hx; omega
  | l :: ρ, h, x, h1, h2 => by
    by_cases hx : x < FR + slotsIn ρ
    · obtain ⟨i, hi⟩ := SlotsOk.cover h.2 x h1 hx
      exact ⟨i + 1, by simpa using hi⟩
    · refine ⟨0, ?_⟩
      simp only [slotsIn_cons] at h2
      cases l with
      | slot o k n =>
        have e := h.1 k rfl
        simp only [List.getD_cons_zero, Loc.holds_slot, Loc.nw_slot] at h2 ⊢
        simp; omega
      | _ => simp at h2; omega

/-- A variable's slots from `k` start at or above another's first slot `x`, or lie wholly below it. -/
theorem SlotsOk.ov {ρ : List Loc} (hok : SlotsOk ρ) {i j x k : Nat}
    (hi : (ρ.getD i default).slot? = some x) (hni : 1 ≤ (ρ.getD i default).nw)
    (hj : (ρ.getD j default).slot? = some k) : x ≤ k ∨ k + (ρ.getD j default).nw ≤ x := by
  refine Classical.byContradiction fun hc => ?_
  have e := hok.inj (i := i) (j := j) (x := x) (Loc.holds_iff.2 ⟨x, hi, Nat.le_refl _, by omega⟩)
    (Loc.holds_iff.2 ⟨k, hj, by omega, by omega⟩)
  subst e; rw [hi] at hj; cases hj; omega

/-- Slot-resident variables' slots are from `FR` on. -/
theorem FEnvRel.ge {f : Frame} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc}, FEnvRel f env ρ →
    ∀ i x, (ρ.getD i default).holds x = true → FR ≤ x
  | _, .nil, [], _, i, x, hx => by simp at hx
  | _, .nil, _ :: _, hr, _, _, _ => by cases hr
  | _, .cons _ _, l :: _, hr, 0, x, hx => by
    cases l with
    | slot o k n => simp at hx; exact Nat.le_trans hr.1.1 hx.1
    | _ => simp at hx
  | _, .cons _ _, _ :: _, hr, i + 1, x, hx => FEnvRel.ge hr.2 i x (by simpa using hx)
  | _, .cons _ _, [], hr, _, _, _ => hr.elim

/-- The frame represents the slot-resident variables after scratch code, which keeps every slot
from `FR` on. -/
theorem FEnvRel.keep {f f' : Frame} {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    (hr : FEnvRel f env ρ) (hk : ∀ x, FR ≤ x → f' x = f x) : FEnvRel f' env ρ :=
  hr.congr fun i x h => hk x (hr.ge i x h)

/-- The frame relation depends only on the slot-resident variables' values. -/
theorem FEnvRel.env_congr {f : Frame} : ∀ {Γ : List Ty} {env env' : Env Γ} {ρ : List Loc},
    FEnvRel f env ρ → (∀ {s : Ty} (m : Mem s Γ), (ρ.getD m.idx default).isSlot = true →
      env'.get m = env.get m) → FEnvRel f env' ρ
  | _, .nil, .nil, _, hr, _ => hr
  | _, .cons v env, .cons v' env', l :: ρ, hr, h => by
    refine ⟨?_, FEnvRel.env_congr hr.2 fun m hm => h (.there m) (by simpa [Mem.idx] using hm)⟩
    have h1 := hr.1
    cases l with
    | slot o k n =>
      have e : v' = v := h .here (by simp [Mem.idx])
      rw [e]; exact h1
    | _ => trivial
  | _, .cons _ _, .cons _ _, [], hr, _ => hr.elim

/-- Writing a place rooted at a variable in memory keeps the frame relation. -/
theorem FEnvRel.place_set {f : Frame} {Γ : List Ty} {t : Ty} {env : Env Γ} {ρ : List Loc}
    (hr : FEnvRel f env ρ) (p : Place Γ t) (hns : (ρ.getD p.root default).isSlot = false)
    (v : t.carrier) : FEnvRel f (p.set env v) ρ :=
  hr.env_congr fun m hm => Place.get_set_ne p env v m fun e => by rw [e, hns] at hm; cases hm

/-- Writing a slot-resident variable's slots with its new value, which changes no other variable's
slot. -/
theorem FEnvRel.set_slots {f f' : Frame} {t : Ty} : ∀ {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} (m : Mem t Γ) (v : t.carrier) {k : Nat}, SlotsOk ρ →
    (ρ.getD m.idx default).slot? = some k → WordsRel t v f' k →
    (∀ x, FR ≤ x → (ρ.getD m.idx default).holds x = false → f' x = f x) → FEnvRel f env ρ →
    FEnvRel f' (env.set m v) ρ
  | _, .cons _ env, l :: ρ, .here, v, k, hok, hk, hw, hout, hr => by
    cases l with
    | slot o k' n =>
      simp only [Mem.idx, List.getD_cons_zero, Loc.slot?_slot, Option.some.injEq] at hk; subst hk
      refine ⟨⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, hw⟩, hr.2.congr fun i x hx =>
        hout x (hok.2.holds i x hx).1 ?_⟩
      have := hok.2.holds i x hx
      have e := hok.1 k' rfl
      simp only [Mem.idx, List.getD_cons_zero, Loc.holds_slot]; simp; omega
    | _ => simp [Mem.idx] at hk
  | _, .cons x env, l :: ρ, .there m, v, k, hok, hk, hw, hout, hr => by
    have hk' : (ρ.getD m.idx default).slot? = some k := by simpa [Mem.idx] using hk
    refine ⟨?_, FEnvRel.set_slots m v hok.2 hk' hw
      (fun y hy1 hy => hout y hy1 (by simpa [Mem.idx] using hy)) hr.2⟩
    have h1 := hr.1
    cases l with
    | slot o k' n' =>
      obtain ⟨h1, h2, h3, hw'⟩ := h1
      have e := hok.1 k' rfl
      refine ⟨h1, h2, h3, hw'.congr fun y hy1 hy2 => hout y (by omega) ?_⟩
      have := hok.2.range m.idx k hk'
      cases hh : (ρ.getD m.idx default).holds y with
      | false => simpa [Mem.idx] using hh
      | true => have := hok.2.holds m.idx y hh; subst h3; omega
    | _ => trivial
  | _, .cons _ _, [], _, _, _, _, _, _, _, hr => hr.elim

/-- The frame relation holds after a subterm that may write none of the slot-resident variables. -/
theorem FEnvRel.prot {f f' : Frame} {Γ : List Ty} {env : Env Γ} {ρ : List Loc} {W : List Bool}
    (hr : FEnvRel f env ρ)
    (hk : ∀ x, FR ≤ x → SProt ρ (noW W) x → f' x = f x) : FEnvRel f' env ρ :=
  hr.congr fun i x h => hk x (hr.ge i x h) ⟨i, h, noW_getD W i⟩

/-- The frame relation holds after code that writes only scratch slots and slots from
`FR + slotsIn ρ` on, which belong to a new binder. -/
theorem FEnvRel.below {f f' : Frame} {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    (hr : FEnvRel f env ρ) (hok : SlotsOk ρ) (hk : ∀ x, FR ≤ x → x < FR + slotsIn ρ → f' x = f x) :
    FEnvRel f' env ρ :=
  hr.congr fun i x h => hk x (hok.holds i x h).1 (hok.holds i x h).2

theorem SProt.push {ρ : List Loc} {W : List Bool} {x : Nat} (l : Loc) (b : Bool)
    (h : SProt ρ W x) : SProt (l :: ρ) (b :: W) x :=
  let ⟨i, h1, h2⟩ := h; ⟨i + 1, by simpa using h1, by simpa using h2⟩

/-- A protected slot belongs to a slot-resident variable, so it is below `FR + slotsIn ρ`. -/
theorem SProt.lt {ρ : List Loc} {W : List Bool} {x : Nat} (hok : SlotsOk ρ) (h : SProt ρ W x) :
    x < FR + slotsIn ρ :=
  let ⟨i, h1, _⟩ := h; (hok.holds i x h1).2

theorem SlotsOk.of_none : ∀ {ρ : List Loc}, (∀ i, (ρ.getD i default).slot? = none) → SlotsOk ρ
  | [], _ => trivial
  | _ :: _, h => ⟨(fun k hk => by have := h 0; simp at this; rw [this] at hk; cases hk),
      SlotsOk.of_none fun i => by simpa using h (i + 1)⟩

/-- A context without slot-resident variables, such as a callee's parameters. -/
theorem SlotHyp.of_none {Γ : List Ty} {t : Ty} {e : Exp Γ t} {tm : Tl} {ρ : List Loc}
    {env : Env Γ} {f : Frame} (hρ : ρ.length = Γ.length)
    (h : ∀ i, (ρ.getD i default).slot? = none) : SlotHyp e tm ρ env f :=
  ⟨SlotsOk.of_none h, FEnvRel.of_none hρ h, fun i hi => by
    obtain ⟨k, hk⟩ := Loc.isSlot_iff.1 hi; rw [h i] at hk; cases hk⟩

/-- A variable the term addresses is in memory. -/
theorem SlotHyp.ns_of_addr {Γ : List Ty} {t : Ty} {e : Exp Γ t} {tm : Tl} {ρ : List Loc}
    {env : Env Γ} {f : Frame} (H : SlotHyp e tm ρ env f) {i : Nat} (h : e.noAddr i = false) :
    (ρ.getD i default).isSlot = false := by
  cases hs : (ρ.getD i default).isSlot
  · rfl
  · rw [(H.na i hs).1] at h; cases h

/-- A variable the tail mode hands back in place is in memory. -/
theorem SlotHyp.ns_of_tm {Γ : List Ty} {t : Ty} {e : Exp Γ t} {tm : Tl} {ρ : List Loc}
    {env : Env Γ} {f : Frame} (H : SlotHyp e tm ρ env f) {i : Nat} (h : i ∈ tm.vars) :
    (ρ.getD i default).isSlot = false := by
  cases hs : (ρ.getD i default).isSlot
  · rfl
  · exact absurd h (H.na i hs).2

/-- The slot-resident variables' facts pass to a term in the same context. -/
theorem SlotHyp.sub {Γ : List Ty} {t t' : Ty} {e : Exp Γ t} {e' : Exp Γ t'} {tm tm' : Tl}
    {ρ : List Loc} {env env' : Env Γ} {f f' : Frame} (H : SlotHyp e tm ρ env f)
    (hrel : FEnvRel f' env' ρ)
    (hna : ∀ i, e.noAddr i = true → i ∉ tm.vars → e'.noAddr i = true ∧ i ∉ tm'.vars) :
    SlotHyp e' tm' ρ env' f' :=
  ⟨H.ok, hrel, fun i hi => hna i (H.na i hi).1 (H.na i hi).2⟩

/-- The slot-resident variables' facts pass to a term under one more binder at location `l`. The
binder is slot-resident only in the next slots, and then not addressed by the term, and the tail
mode `tm'` hands back in place only the binder or variables that `tm` hands back. -/
theorem SlotHyp.pushT {Γ : List Ty} {s t t' : Ty} {e : Exp Γ t} {e' : Exp (s :: Γ) t'} {tm : Tl}
    {ρ : List Loc} {env : Env Γ} {f : Frame} (H : SlotHyp e tm ρ env f) (l : Loc)
    (hl : ∀ k, l.slot? = some k → k = FR + slotsIn ρ) {tm' : Tl} {v : s.carrier} {env' : Env Γ}
    {f' : Frame} (hrel : FEnvRel f' (.cons v env') (l :: ρ))
    (h0 : l.isSlot = true → e'.noAddr 0 = true ∧ 0 ∉ tm'.vars)
    (hna : ∀ i, e.noAddr i = true → e'.noAddr (i + 1) = true)
    (htm : ∀ i, i + 1 ∈ tm'.vars → i ∈ tm.vars) :
    SlotHyp e' tm' (l :: ρ) (.cons v env') f' := by
  refine ⟨⟨hl, H.ok⟩, hrel, fun i hi => ?_⟩
  cases i with
  | zero => exact h0 (by simpa using hi)
  | succ i =>
    have := H.na i (by simpa using hi)
    exact ⟨hna i this.1, fun h => this.2 (htm i h)⟩

/-- `SlotHyp.pushT` in the tail mode `tm.up`. -/
theorem SlotHyp.push {Γ : List Ty} {s t t' : Ty} {e : Exp Γ t} {e' : Exp (s :: Γ) t'} {tm : Tl}
    {ρ : List Loc} {env : Env Γ} {f : Frame} (H : SlotHyp e tm ρ env f) (l : Loc)
    (hl : ∀ k, l.slot? = some k → k = FR + slotsIn ρ) {v : s.carrier} {env' : Env Γ} {f' : Frame}
    (hrel : FEnvRel f' (.cons v env') (l :: ρ)) (h0 : l.isSlot = true → e'.noAddr 0 = true)
    (hna : ∀ i, e.noAddr i = true → e'.noAddr (i + 1) = true) :
    SlotHyp e' tm.up (l :: ρ) (.cons v env') f' :=
  H.pushT l hl hrel (fun h => ⟨h0 h, Tl.zero_not_mem_up tm⟩) hna fun _ h => Tl.succ_mem_up.1 h

/-- A slot protected from a term is protected from a term that may write nothing. -/
theorem SProt.noW {ρ : List Loc} {W W' : List Bool} {x : Nat} (h : SProt ρ W x) :
    SProt ρ (noW W') x :=
  let ⟨i, h1, _⟩ := h; ⟨i, h1, noW_getD W' i⟩

/-- A slot protected from a term is protected from one that may write less. -/
theorem SProt.wle {ρ : List Loc} {W W' : List Bool} {x : Nat} (h : SProt ρ W x)
    (hW : ∀ i, W'.getD i false = true → W.getD i false = true) : SProt ρ W' x := by
  obtain ⟨i, h1, h2⟩ := h
  refine ⟨i, h1, ?_⟩
  cases e : W'.getD i false
  · rfl
  · rw [hW i e] at h2; cases h2

/-- The protected slots are below a word destination. -/
theorem SProt.lt_word {ρ : List Loc} {W : List Bool} {k x : Nat} (hk : (Tl.word k).Ok W ρ)
    (h : SProt ρ W x) : x < k := by
  obtain ⟨i, hi, hw⟩ := h
  obtain ⟨k', hk', h1, h2⟩ := Loc.holds_iff.1 hi
  rcases hk.2.2 i k' hk' with h3 | ⟨_, h3⟩
  · omega
  · rw [h3] at hw; cases hw

/-- A word destination at the next free slot `FR + slotsIn ρ`: every slot-resident variable is below
it. -/
theorem Tl.Ok.word_top {ρ : List Loc} (W : List Bool) (hok : SlotsOk ρ) :
    (Tl.word (FR + slotsIn ρ)).Ok W ρ :=
  ⟨Nat.le_add_right _ _, Nat.le_refl _, fun i k' hk => Or.inl (hok.range i k' hk).2⟩

end Slots

end Millipede.Flat
