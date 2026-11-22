import Millipede.Compile.LowerSim

/-!
# The memory refinement of atoms, scalars and control

This module proves that the memory lowering of atoms, primitives, `if`, `let`, `Result`
constructors and `match` simulates the evaluation of the term. There is one lemma for each
primitive load or store and one case lemma for each construct, which takes the refinement property
of its subterms as hypotheses, so that `LowerSound.lean` can assemble the cases by induction on
the term.

An atom reads its variable at the variable's own offset in the frame, or through the reference
slot when the variable is a reference. A variable read as an atom has no hole, because the borrow
checker forbids using a lender while an exclusive loan of it is live.
-/

namespace Millipede.Flat

/-! ## Tail modes under binders -/

@[simp] theorem Tl.up_dsz (tm : Tl) (t : Ty) : tm.up.dsz t = tm.dsz t := by
  cases tm <;> rfl

/-- The tail mode under a binder at location `l` is well formed when it was well formed outside.
The binder is writable when it is slot-resident, and then it sits at the next free slot. -/
theorem Tl.Ok.up {tm : Tl} {W : List Bool} {ρ : List Loc} (b : Bool) (l : Loc)
    (hb : l.isSlot = true → b = true) (hl : ∀ k, l.slot? = some k → k = FR + slotsIn ρ)
    (h : tm.Ok W ρ) : tm.up.Ok (b :: W) (l :: ρ) := by
  cases tm with
  | none => trivial
  | whole x => exact h
  | split f0 cs =>
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact h c' hc'
  | word k =>
    refine ⟨h.1, by simp only [slotsIn_cons]; have := h.2.1; omega, fun i k' hi => ?_⟩
    cases i with
    | zero =>
      have e := hl k' (by simpa using hi)
      exact Or.inr ⟨by have := h.2.1; omega, hb (Loc.isSlot_iff.2 ⟨k', by simpa using hi⟩)⟩
    | succ i => simpa using h.2.2 i k' (by simpa using hi)

theorem Tl.Ok.none (W : List Bool) (ρ : List Loc) : Tl.none.Ok W ρ := trivial

theorem TQ.up {tm : Tl} {bp d : Nat} {ρ : List Loc} {S : List SI} {t : Ty} (l : Loc) (si : SI)
    (v : t.carrier) (f : Frame) (h : Heap) :
    TQ tm.up bp d (l :: ρ) (si :: S) t v f h ↔ TQ tm bp d ρ S t v f h := by
  cases tm with
  | none => exact Iff.rfl
  | whole x => exact Iff.rfl
  | word k => exact Iff.rfl
  | split f0 cs =>
    simp only [TQ, Tl.up, List.mem_map]
    constructor
    · rintro ⟨bs, h1, h2, h3⟩
      exact ⟨bs, h1, h2, fun c hc => by simpa using h3 (c.1 + 1, c.2) ⟨c, hc, rfl⟩⟩
    · rintro ⟨bs, h1, h2, h3⟩
      exact ⟨bs, h1, h2, fun c ⟨c', hc', e⟩ => by subst e; simpa using h3 c' hc'⟩

@[simp] theorem _root_.Millipede.Exp.conf_none {Γ : List Ty} {t : Ty} (e : Exp Γ t) : e.Conf .none = true := by
  cases e <;> rfl

/-- Protection below `n` implies protection for code that binds a fresh writable variable at
`n' ≥ n`. -/
theorem Prot.push {bp n n' d sz : Nat} {Γ : List Ty} {S : List SI} {W : List Bool} (s : Ty)
    (m : Nat) (hn : n ≤ n') {a : Nat} (ha : Prot bp n d sz Γ S W a) :
    Prot bp (n' + m) d sz (s :: Γ) (⟨bp + n', none, none, none⟩ :: S) (true :: W) a := by
  obtain ⟨h1, h2, h3⟩ := ha
  refine ⟨by omega, h2, ?_⟩
  rintro (⟨_, h5⟩ | h5)
  · rw [SI.In_mk] at h5; simp only [InR] at h5; omega
  · exact h3 h5

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-! ## Atoms -/

/-- Writing `B` at `A` leaves every address outside `[A, A + |B|)`. -/
theorem wr_out {h : Heap} {A : Nat} {B : List UInt8} (hb : A + B.length ≤ UInt64.size) {a : Nat}
    (ha : a < UInt64.size) (hout : ¬ (A ≤ a ∧ a < A + B.length)) :
    wr h A B (UInt64.ofNat a) = h (UInt64.ofNat a) :=
  wr_other h A B a ha hb (by omega)

/-- An access at `bp + o`, for a static offset `o`, lies below `L`. -/
theorem acc_off {o bp b : Nat} (hL : bp + o + b ≤ L) (hU : bp + o < UInt64.size) {f : Frame}
    (hf : f BP = UInt64.ofNat bp) : ((Operand.slot BP).eval f + UInt64.ofNat o).toNat + b ≤ L := by
  rw [eval_slot, hf, ofNat_add_ofNat]; exact acc_ofNat hL hU

/-- Loading a reference slot gives the address of its value. -/
theorem ptr_load {Γ : List Ty} {t : Ty} (m : Mem t Γ) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp o : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) (hρ : ρ.getD m.idx default = .ref o)
    (hf : f BP = UInt64.ofNat bp) (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size)
    (hx : x < FR := by decide) :
    Runs κ ω L (.load .w64 x (.slot BP) (UInt64.ofNat o)) f h
      (f.set x (UInt64.ofNat (S.getD m.idx default).A)) h := by
  have hs : o + 8 ≤ n := by have := (hl.var m).slotLe; rw [hρ] at this; exact this
  refine Runs.congr (Runs.load _ _ _ _ _ _ (acc_off (b := 8) (by omega)
    (by omega) hf) hx) ?_ rfl
  have hp := (henv.get' m).2
  rw [hρ] at hp
  simp only [eval_slot, hf, ofNat_add_ofNat, load64_eq]
  rw [show decodeLE (rd h (bp + o) 8) = _ from hp]

/-- Storing a one-word scalar's word at the scalar's width writes bytes representing its value. -/
theorem store_wordRel {t : Ty} {v : t.carrier} {w : UInt64} (ht : t.wordTy = true)
    (hw : WordRel t v w) (h : Heap) (A : Nat) :
    ∃ B : List UInt8, B.length = t.size ∧ Data.reprBytes v B ∧
      h.store (scalarWidth t.size) (UInt64.ofNat A) w = wr h A B := by
  obtain ⟨B, hB, rfl⟩ := hw
  have hl : B.length = t.size := Data.reprBytes_length hB
  refine ⟨B, hl, hB, ?_⟩
  rcases Ty.wordTy_size ht with ⟨h8, hw8⟩ | ⟨h1, hw1⟩
  · have hB8 : B.length = 8 := hl.trans h8
    rw [hw8, store64_eq, decodeLE_toNat B (by omega)]
    have := natBytes_natOfBytes B
    rw [hB8] at this
    rw [this]
  · have hB1 : B.length = 1 := hl.trans h1
    obtain ⟨b, rfl⟩ : ∃ b, B = [b] := by
      match B, hB1 with
      | [b], _ => exact ⟨b, rfl⟩
    rw [hw1, show decodeLE [b] = b.toUInt64 by simp [decodeLE], store8_eq]; rfl

/-! ## Chunks of slot-resident values -/

/-- `WordsAt`, pointwise: slot `k + j` holds the word of bytes `8j … 8j + 7`. -/
theorem wordsAt_iff {f : Frame} : ∀ {n k : Nat} {B : List UInt8},
    WordsAt f k B n ↔ ∀ j, j < n → f (k + j) = decodeLE ((B.drop (8 * j)).take 8)
  | 0, _, _ => by simp [WordsAt]
  | n + 1, k, B => by
    simp only [WordsAt]
    rw [wordsAt_iff]
    constructor
    · rintro ⟨h0, h1⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j =>
        rw [show k + (j + 1) = k + 1 + j by omega, h1 j (by omega), List.drop_drop]
        congr 3; omega
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun j hj => ?_⟩
      rw [show k + 1 + j = k + (j + 1) by omega, h (j + 1) (by omega), List.drop_drop]
      congr 3; omega

theorem chunks_getD : ∀ (B : List UInt8) (n j : Nat), j < n →
    (chunks B n).getD j 0 = decodeLE ((B.drop (8 * j)).take 8)
  | _, n + 1, 0, _ => by simp [chunks]
  | B, n + 1, j + 1, hj => by
    simp only [chunks, List.getD_cons_succ]
    rw [chunks_getD (B.drop 8) n j (by omega), List.drop_drop]; congr 3; omega

/-- The chunks of `8n` bytes read from memory. -/
theorem rd_chunk (h : Heap) (A n j : Nat) (hj : j < n) :
    ((rd h A (8 * n)).drop (8 * j)).take 8 = rd h (A + 8 * j) 8 := by
  have e := rd_slice h A (8 * n) (8 * j) 8 (by omega)
  simpa [slice] using e.symm

/-- Loading `n` chunks of width `w` from `b + o, b + o + 8, …` into the slots from `K`, where the
base slot `b` is below `K`. -/
theorem ldSlots_reach {κ : CostModel} {ω : Oracle} {L : Nat} (w : Width) :
    ∀ (n : Nat) {K b o A : Nat} {f : Frame} {h : Heap}, f b = UInt64.ofNat A → b < K →
    (∀ j, j < n → A + o + 8 * j + w.bytes ≤ L ∧ A + o + 8 * j < UInt64.size) →
    ∃ f', Reaches κ ω L (ldSlots w K (.slot b) o n) f h f' h ∧
      (∀ x, (x < K ∨ K + n ≤ x) → f' x = f x) ∧
      ∀ j, j < n → f' (K + j) = h.load w (UInt64.ofNat (A + o + 8 * j))
  | 0, _, _, _, _, f, _, _, _, _ => ⟨f, (Runs.skip f _).run, fun _ _ => rfl, fun _ h => by omega⟩
  | n + 1, K, b, o, A, f, h, hf, hb, hj => by
    have ha : ((Operand.slot b).eval f + UInt64.ofNat o) = UInt64.ofNat (A + o) := by
      rw [eval_slot, hf, ofNat_add_ofNat]
    have hr₁ := Reaches.load (κ := κ) (ω := ω) (L := L) w K (.slot b) (UInt64.ofNat o) f h
      (by rw [ha]; exact acc_ofNat (by have := hj 0 (by omega); omega) (hj 0 (by omega)).2)
    rw [ha] at hr₁
    obtain ⟨f', hr, hout, hval⟩ := ldSlots_reach (κ := κ) (ω := ω) (L := L) w n (K := K + 1) (b := b)
      (o := o + 8) (A := A) (f := f.set K (h.load w (UInt64.ofNat (A + o)))) (h := h)
      (by rw [Frame.set_ne _ _ (by omega)]; exact hf) (by omega)
      (fun j hj' => by have := hj (j + 1) (by omega); omega)
    refine ⟨f', Reaches.seq hr₁ hr, fun x hx => ?_, fun j hj' => ?_⟩
    · rw [hout x (by omega), Frame.set_ne _ _ (by omega)]
    · cases j with
      | zero => simp only [Nat.add_zero, Nat.mul_zero]; rw [hout K (by omega)]; simp
      | succ j =>
        rw [show K + (j + 1) = K + 1 + j by omega, hval j (by omega),
          show A + o + 8 * (j + 1) = A + (o + 8) + 8 * j by omega]

/-- Loading the chunks of a slot-resident value from bytes representing it at `b + o`, where the
base slot `b` is below `K`, leaves the slots from `K` holding the value. -/
theorem ldSlots_words {κ : CostModel} {ω : Oracle} {L : Nat} {t : Ty} (ht : t.slotTy = true)
    {v : t.carrier} {K b o A : Nat} {f : Frame} {h : Heap} (hf : f b = UInt64.ofNat A)
    (hbK : b < K) (hv : Data.reprBytes v (rd h (A + o) t.size)) (hL : A + o + t.size ≤ L)
    (hU : A + o + t.size ≤ UInt64.size) :
    ∃ f', Reaches κ ω L (ldSlots (scalarWidth t.size) K (.slot b) o t.slotN) f h f' h ∧
      (∀ x, (x < K ∨ K + t.slotN ≤ x) → f' x = f x) ∧ WordsRel t v f' K := by
  rcases Ty.slotTy_cases ht with ⟨h1, hn, hw⟩ | ⟨h8, hn, hw⟩
  · rw [hn, hw]
    obtain ⟨f', hr, hout, hval⟩ := ldSlots_reach (κ := κ) (ω := ω) (L := L) .w8 1 (K := K) (o := o) (h := h) hf hbK
      (fun j hj => by simp only [Width.bytes]; omega)
    refine ⟨f', hr, hout, _, hv, ?_⟩
    rw [hn, wordsAt_one (by rw [rd_length]; omega), h1]
    have := hval 0 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at this
    rw [this, load8_eq]
  · rw [hw]
    obtain ⟨f', hr, hout, hval⟩ := ldSlots_reach (κ := κ) (ω := ω) (L := L) .w64 t.slotN (K := K) (o := o) (h := h) hf hbK
      (fun j hj => by simp only [Width.bytes]; omega)
    refine ⟨f', hr, hout, _, hv, wordsAt_iff.2 fun j hj => ?_⟩
    rw [hval j hj, h8, rd_chunk h _ _ _ hj, load64_eq]

/-- Storing `n` whole-word chunks at `b + o, …` writes `B` when the slots from `K` hold the words
of `B`. -/
theorem stSlots64 {κ : CostModel} {ω : Oracle} {L : Nat} {b : Nat} :
    ∀ (n : Nat) {K o A : Nat} {B : List UInt8} {f : Frame} {h : Heap}, f b = UInt64.ofNat A →
    B.length = 8 * n → WordsAt f K B n → A + o + 8 * n ≤ L → A + o + 8 * n ≤ UInt64.size →
    Runs κ ω L (stSlots .w64 (.slot b) o K n) f h f (wr h (A + o) B)
  | 0, _, _, _, B, f, h, _, hB, _, _, _ => by
    obtain rfl : B = [] := List.eq_nil_of_length_eq_zero (by simpa using hB)
    exact Runs.skip f h
  | n + 1, K, o, A, B, f, h, hf, hB, hw, hL, hU => by
    have ha : ((Operand.slot b).eval f + UInt64.ofNat o) = UInt64.ofNat (A + o) := by
      rw [eval_slot, hf, ofNat_add_ofNat]
    have h8 : (B.take 8).length = 8 := by simp; omega
    have hst : h.store .w64 (UInt64.ofNat (A + o)) (f K) = wr h (A + o) (B.take 8) := by
      rw [hw.1, store64_eq, decodeLE_toNat _ (by omega)]
      have := natBytes_natOfBytes (B.take 8)
      rw [h8] at this; rw [this]
    have hr₁ := Runs.store (κ := κ) (ω := ω) (L := L) .w64 (.slot b) (UInt64.ofNat o) (.slot K) f h
      (by rw [ha]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega))
    rw [ha, eval_slot, hst] at hr₁
    have hr₂ := stSlots64 (κ := κ) (ω := ω) (L := L) (b := b) n (K := K + 1) (o := o + 8) (A := A)
      (B := B.drop 8) (f := f) (h := wr h (A + o) (B.take 8)) hf (by simp; omega) hw.2
      (by omega) (by omega)
    have e : wr (wr h (A + o) (B.take 8)) (A + (o + 8)) (B.drop 8) = wr h (A + o) B := by
      rw [← List.take_append_drop 8 B, wr_append, h8, List.take_append_drop,
        show A + o + 8 = A + (o + 8) by omega]
    exact Runs.seq hr₁ (by rw [e] at hr₂; exact hr₂)

/-- Storing the chunks of a slot-resident value from the slots from `K` that hold it at `b + o`
writes bytes representing it. -/
theorem stSlots_words {κ : CostModel} {ω : Oracle} {L : Nat} {t : Ty} (ht : t.slotTy = true)
    {v : t.carrier} {K b o A : Nat} {f : Frame} {h : Heap} (hf : f b = UInt64.ofNat A)
    (hv : WordsRel t v f K) (hL : A + o + t.size ≤ L) (hU : A + o + t.size ≤ UInt64.size) :
    ∃ B, B.length = t.size ∧ Data.reprBytes v B ∧
      Runs κ ω L (stSlots (scalarWidth t.size) (.slot b) o K t.slotN) f h f (wr h (A + o) B) := by
  obtain ⟨B, hB, hw⟩ := hv
  have hl : B.length = t.size := Data.reprBytes_length hB
  refine ⟨B, hl, hB, ?_⟩
  have ha : ((Operand.slot b).eval f + UInt64.ofNat o) = UInt64.ofNat (A + o) := by
    rw [eval_slot, hf, ofNat_add_ofNat]
  rcases Ty.slotTy_cases ht with ⟨h1, hn, hwd⟩ | ⟨h8, hn, hwd⟩
  · rw [hn, hwd]
    rw [hn, wordsAt_one (by omega)] at hw
    obtain ⟨c, rfl⟩ : ∃ c, B = [c] := by
      match B, (show B.length = 1 by omega) with
      | [c], _ => exact ⟨c, rfl⟩
    have hr₁ := Runs.store (κ := κ) (ω := ω) (L := L) .w8 (.slot b) (UInt64.ofNat o) (.slot K) f h
      (by rw [ha]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega))
    rw [ha, eval_slot, hw, show decodeLE [c] = c.toUInt64 by simp [decodeLE], store8_eq] at hr₁
    exact Runs.seq hr₁ (Runs.skip _ _)
  · rw [hwd]
    exact stSlots64 t.slotN hf (by omega) hw (by omega) (by omega)

/-- Copying `n` slots from `k` to `x` in increasing order, which is correct when the source starts
at or above the destination or lies wholly below it. -/
theorem movSlots_reach {κ : CostModel} {ω : Oracle} {L : Nat} :
    ∀ (n : Nat) {x k : Nat} {f : Frame} {h : Heap}, (x ≤ k ∨ k + n ≤ x) →
    ∃ f', Reaches κ ω L (movSlots x k n) f h f' h ∧ (∀ y, (y < x ∨ x + n ≤ y) → f' y = f y) ∧
      ∀ j, j < n → f' (x + j) = f (k + j)
  | 0, _, _, f, h, _ => ⟨f, (Runs.skip f h).run, fun _ _ => rfl, fun _ h => by omega⟩
  | n + 1, x, k, f, h, hov => by
    obtain ⟨f', hr, hout, hval⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) n (x := x + 1)
      (k := k + 1) (f := f.set x (f k)) (h := h) (by omega)
    refine ⟨f', Reaches.seq (Reaches.mov x (.slot k) f h) hr, fun y hy => ?_, fun j hj => ?_⟩
    · rw [hout y (by omega), Frame.set_ne _ _ (by omega)]
    · cases j with
      | zero => simp only [Nat.add_zero]; rw [hout x (by omega)]; simp
      | succ j =>
        rw [show x + (j + 1) = x + 1 + j by omega, hval j (by omega),
          Frame.set_ne _ _ (by omega)]
        congr 1; omega

/-- Writing constant words to the slots from `x`. -/
theorem immSlots_reach {κ : CostModel} {ω : Oracle} {L : Nat} :
    ∀ (vs : List UInt64) {x : Nat} {f : Frame} {h : Heap},
    ∃ f', Reaches κ ω L (immSlots x vs) f h f' h ∧ (∀ y, (y < x ∨ x + vs.length ≤ y) → f' y = f y) ∧
      ∀ j, j < vs.length → f' (x + j) = vs.getD j 0
  | [], _, f, h => ⟨f, (Runs.skip f h).run, fun _ _ => rfl, fun _ h => by simp at h⟩
  | v :: vs, x, f, h => by
    obtain ⟨f', hr, hout, hval⟩ := immSlots_reach (κ := κ) (ω := ω) (L := L) vs (x := x + 1)
      (f := f.set x v) (h := h)
    refine ⟨f', Reaches.seq (Reaches.mov x (.imm v) f h) hr, fun y hy => ?_, fun j hj => ?_⟩
    · simp only [List.length_cons] at hy
      rw [hout y (by omega), Frame.set_ne _ _ (by omega)]
    · cases j with
      | zero => simp only [Nat.add_zero]; rw [hout x (by omega)]; simp
      | succ j =>
        rw [show x + (j + 1) = x + 1 + j by omega, hval j (by simpa using hj)]
        simp

/-! ## The bytes of frame words -/

/-- The little-endian bytes of `n` frame words from slot `K`. -/
def wordsBytes (f : Frame) : Nat → Nat → List UInt8
  | _, 0 => []
  | K, n + 1 => natBytes 8 (f K).toNat ++ wordsBytes f (K + 1) n

@[simp] theorem wordsBytes_length (f : Frame) : ∀ (K n : Nat), (wordsBytes f K n).length = 8 * n
  | _, 0 => rfl
  | K, n + 1 => by simp [wordsBytes, wordsBytes_length f (K + 1) n]; omega

theorem wordsAt_wordsBytes (f : Frame) : ∀ (K n : Nat), WordsAt f K (wordsBytes f K n) n
  | _, 0 => trivial
  | K, n + 1 => by
    refine ⟨?_, ?_⟩
    · simp only [wordsBytes]
      rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
        decodeLE_natBytes8]
    · simp only [wordsBytes]
      rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp),
        List.nil_append]
      exact wordsAt_wordsBytes f (K + 1) n

/-- Whole-word bytes held by the frame are its words' bytes. -/
theorem wordsBytes_eq {f : Frame} : ∀ {K n : Nat} {B : List UInt8}, B.length = 8 * n →
    WordsAt f K B n → wordsBytes f K n = B
  | _, 0, B, hl, _ => (List.eq_nil_of_length_eq_zero (by simpa using hl)).symm
  | K, n + 1, B, hl, hw => by
    have h8 : (B.take 8).length = 8 := by simp; omega
    simp only [wordsBytes]
    rw [wordsBytes_eq (B := B.drop 8) (by simp; omega) hw.2, hw.1,
      decodeLE_toNat _ (by omega)]
    have := natBytes_natOfBytes (B.take 8)
    rw [h8] at this; rw [this, List.take_append_drop]

theorem wordsBytes_add (f : Frame) : ∀ (K a b : Nat),
    wordsBytes f K (a + b) = wordsBytes f K a ++ wordsBytes f (K + a) b
  | _, 0, b => by simp [wordsBytes]
  | K, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [wordsBytes, List.append_assoc]
    rw [wordsBytes_add f (K + 1) a b, show K + 1 + a = K + (a + 1) by omega]

/-- The words of a slice of whole words. -/
theorem wordsBytes_slice (f : Frame) (K i j m : Nat) (h : i + j ≤ m) :
    slice (wordsBytes f K m) (8 * i) (8 * j) = wordsBytes f (K + i) j := by
  rw [show m = i + (j + (m - i - j)) by omega, wordsBytes_add, wordsBytes_add]
  simp [slice]

theorem wordsBytes_congr {f f' : Frame} : ∀ {K n : Nat},
    (∀ j, j < n → f' (K + j) = f (K + j)) → wordsBytes f' K n = wordsBytes f K n
  | _, 0, _ => rfl
  | K, n + 1, h => by
    simp only [wordsBytes]
    rw [show f' K = f K from h 0 (by omega), wordsBytes_congr (f := f) fun j hj => by
      rw [show K + 1 + j = K + (j + 1) by omega]; exact h (j + 1) (by omega)]

/-- The low byte of a little-endian word is its first byte. -/
theorem decodeLE_low (b : UInt8) (bs : List UInt8) (hl : bs.length ≤ 7) :
    decodeLE (b :: bs) &&& 255 = b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, decodeLE_toNat _ (by simp; omega)]
  simp only [natOfBytes, UInt8.toNat_toUInt64]
  have := b.toNat_lt; omega

/-- The word of a slot holding a `U64`. -/
theorem word_u64 {v : UInt64} {w : UInt64} (hw : WordRel .u64 v w) : w = v := by
  obtain ⟨B, ⟨_, hB⟩, rfl⟩ := hw
  have hB' : B = natBytes 8 v.toNat := hB
  rw [hB', decodeLE_natBytes8]

/-- The word of a boolean: `1` or `0`. -/
abbrev bword (b : Bool) : UInt64 := if b then 1 else 0

theorem decode_bool (b : Bool) : decodeLE (natBytes 1 (if b then 1 else 0)) = bword b := by
  cases b <;> rfl

theorem word_bool {v : Bool} {w : UInt64} (hw : WordRel .bool v w) : w = bword v := by
  obtain ⟨B, ⟨_, hB⟩, rfl⟩ := hw
  have hB' : B = natBytes 1 (if v then 1 else 0) := hB
  rw [hB', decode_bool]

theorem decode_u8 (b : UInt8) : decodeLE (natBytes 1 b.toNat) = b.toUInt64 := by
  simp [natBytes, decodeLE, UInt8.ofNat_toNat]

theorem word_u8 {v : UInt8} {w : UInt64} (hw : WordRel .u8 v w) : w = v.toUInt64 := by
  obtain ⟨B, ⟨_, hB⟩, rfl⟩ := hw
  have hB' : B = natBytes 1 v.toNat := hB
  rw [hB', decode_u8]

/-- `atomTo a ρ d` writes bytes representing the atom's value at `bp + d`, and only `RT` and `RP`
change in the frame. -/
theorem atomTo_runs {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    (hl : Lay bp n Γ ρ S W) (hd : Away bp d t.size Γ ρ S)
    (hbd : bp + d + t.size ≤ UInt64.size) (hbn : bp + n ≤ UInt64.size)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none) (hdL : bp + d + t.size ≤ L)
    (hnL : bp + n ≤ L) (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none) :
    ∃ f' B, (∀ x, x ≠ RT → x ≠ RP → f' x = f x) ∧ B.length = t.size ∧
      Data.reprBytes (a.denote env) B ∧ Runs κ ω L (atomTo a ρ d) f h f' (wr h (bp + d) B) := by
  cases a with
  | var m =>
    have hsing := hl.var m
    have hsn := hsing.snd_none (hne m rfl)
    have hdl := hsing.dataLe hsn
    have hlen := hl.length
    have hdj := Away.var m hd hlen.1 hlen.2
    rw [SI.Out_none hsn] at hdj
    rw [SI.sz_none (hne m rfl)] at hdl hdj
    simp only [atomTo]
    split
    · rename_i o hρ
      have hv := (henv.get m (by rw [hρ]; rfl)).1.exact (hnh m rfl) (hne m rfl) hsn
      have hA : (S.getD m.idx default).A = bp + o := by have := hsing.2.1; rw [hρ] at this; exact this.1
      have hs : o + t.size ≤ n := by have := hsing.slotLe; rw [hρ] at this; exact this
      have hdj1 : Disj d t.size o t.size := by have := hdj.1; rw [hρ] at this; exact this
      obtain ⟨f', hf', hr⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot BP) (by decide)
        (by decide) t.size o d bp bp f h hf hf (by omega) (by omega)
        (by unfold Disj at hdj1; omega) (by omega) (by omega)
      refine ⟨f', _, fun x h1 _ => hf' x h1, rd_length _ _ _, ?_, hr⟩
      rw [← hA]; exact hv
    · rename_i o hρ
      have hv := (henv.get m (by rw [hρ]; rfl)).1.exact (hnh m rfl) (hne m rfl) hsn
      have hr₁ := ptr_load (κ := κ) (ω := ω) (L := L) m RP hl henv hρ hf hnL hbn
      have hdj2 := hdj.2
      have hfP : (f.set RP (UInt64.ofNat (S.getD m.idx default).A)) BP = UInt64.ofNat bp := by
        rw [Frame.set_ne _ _ (by decide)]; exact hf
      obtain ⟨f', hf', hr⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot RP) (.slot BP)
        (by decide) (by decide) t.size 0 d (S.getD m.idx default).A bp
        (f.set RP (UInt64.ofNat (S.getD m.idx default).A)) h (by simp) hfP
        (by omega) (by omega) (by unfold Disj at hdj2; omega) (by omega) (by omega)
      refine ⟨f', _, fun x h1 h2 => (hf' x h1).trans (Frame.set_ne _ _ h2), rd_length _ _ _, ?_,
        Runs.seq hr₁ (by simpa using hr)⟩
      exact hv
    · rename_i o hρ; exact absurd hρ (hsing.not_ref2 hsn o)
    · rename_i o k w hρ
      obtain ⟨hty, hnw, hw⟩ := hfe.get m (k := k) (by rw [hρ]; rfl)
      rw [hρ] at hnw; simp only [Loc.nw_slot] at hnw; subst hnw
      obtain ⟨B, hBl, hBr, hr⟩ := stSlots_words (κ := κ) (ω := ω) (L := L) (o := d) hty hf hw
        (by omega) (by omega)
      exact ⟨f, B, fun _ _ _ => rfl, hBl, hBr, hr⟩
  | lit v =>
    exact ⟨f, _, fun _ _ _ => rfl, Data.encodeBytes_length v, Data.reprBytes_encode v,
      writeB_runs (.slot BP) _ d bp f h hf (by rw [Data.encodeBytes_length]; omega)
        (by rw [Data.encodeBytes_length]; omega)⟩

/-- Loading an atom of a one-word scalar type into any slot `x` gives a word holding its value.
The word is the decoding of the bytes for a variable in memory, the variable's slot for a
slot-resident one, and the `encode` bytes for a literal. -/
theorem atomWord_word {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W) (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hts : t.wordTy = true) :
    ∃ v, WordRel t (a.denote env) v ∧ Reaches κ ω L (atomWord a ρ x) f h (f.set x v) h := by
  have hw := Ty.wordTy_size hts
  have hsz : ∀ fs, t.data.shape ≠ .prod fs := by
    unfold Ty.wordTy at hts; intro fs he; rw [he] at hts; cases hts
  have hss : ∀ cnt sh, t.data.shape ≠ .slots cnt sh := by
    unfold Ty.wordTy at hts; intro cnt sh he; rw [he] at hts; cases hts
  cases a with
  | var m =>
    have hsing := hl.var m
    have hsn := hsing.snd_none_of_ty hsz
    have hdl := hsing.dataLe hsn
    simp only [atomWord]
    split
    · rename_i o hρ
      have hvr := (henv.get m (by rw [hρ]; rfl)).1
      have hne := hvr.ext_none hsn hss
      rw [SI.sz_none hne] at hdl
      have hv := hvr.exact (hnh m rfl) hne hsn
      have hA : (S.getD m.idx default).A = bp + o := by have := hsing.2.1; rw [hρ] at this; exact this.1
      refine ⟨_, ⟨_, hv, rfl⟩, Reaches.congr (Reaches.load _ _ _ _ _ _ (acc_off
        (b := (scalarWidth t.size).bytes) (by rw [Ty.wordTy_bytes hts]; omega)
        (by rcases hw with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega) hf)) ?_ rfl⟩
      simp only [Operand.eval, hf, ofNat_add_ofNat]
      rw [← hA]
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, load64_eq, h1]
      · rw [h2, load8_eq, h1]
    · rename_i o hρ
      have hvr := (henv.get m (by rw [hρ]; rfl)).1
      have hne := hvr.ext_none hsn hss
      rw [SI.sz_none hne] at hdl
      have hv := hvr.exact (hnh m rfl) hne hsn
      have hs : o + 8 ≤ n := by have := hsing.slotLe; rw [hρ] at this; exact this
      have hp := (henv.get' m).2
      rw [hρ] at hp
      refine ⟨_, ⟨_, hv, rfl⟩, Reaches.congr (Reaches.seq (Reaches.load _ _ _ _ _ _
        (acc_off (b := 8) (by omega) (by omega) hf)) (Reaches.load _ _ _ _ _ _ ?_)) ?_ rfl⟩
      · simp only [eval_slot, Frame.set_same, UInt64.add_zero, hf, ofNat_add_ofNat, load64_eq]
        rw [show decodeLE (rd h (bp + o) 8) = _ from hp]
        exact acc_ofNat (by rw [Ty.wordTy_bytes hts]; omega) (by omega)
      · funext y
        simp only [Frame.set, eval_slot, ↓reduceIte, UInt64.add_zero, hf, ofNat_add_ofNat,
          load64_eq]
        rw [show decodeLE (rd h (bp + o) 8) = _ from hp]
        split
        · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h2, load64_eq, h1]
          · rw [h2, load8_eq, h1]
        · rfl
    · rename_i o hρ; exact absurd hρ (hsing.not_ref2 hsn o)
    · rename_i o k w hρ
      obtain ⟨_, _, hwr⟩ := hfe.get m (k := k) (by rw [hρ]; rfl)
      exact ⟨_, (wordsRel_one (Ty.wordTy_slotN hts)).1 hwr, Reaches.mov _ _ _ _⟩
  | lit v =>
    exact ⟨_, ⟨_, Data.reprBytes_encode v, rfl⟩, Reaches.mov _ _ _ _⟩

/-- `atomWord` into a scratch slot changes only scratch slots. -/
theorem atomWord_runs {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W) (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hts : t.wordTy = true)
    (wd : t.carrier → UInt64) (hwd : ∀ v w, WordRel t v w → w = wd v) (hx : x < FR) :
    Runs κ ω L (atomWord a ρ x) f h (f.set x (wd (a.denote env))) h := by
  obtain ⟨v, hv, hr⟩ := atomWord_word (κ := κ) (ω := ω) (L := L) a x hf henv hfe hl hnh hnL hnU
    hts
  rw [← hwd _ _ hv]
  exact ⟨hr, Frame.set_keep f _ hx⟩

/-- The atom's word: a `U64` atom loads its value. -/
theorem atomWord_u64 {Γ : List Ty} (a : Atom Γ .u64) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) (hx : x < FR := by decide) :
    Runs κ ω L (atomWord a ρ x) f h (f.set x (a.denote env)) h :=
  atomWord_runs a x hf henv hfe hl hnh hnL hnU rfl id (fun _ _ hw => word_u64 hw) hx

/-- The atom's word: a `Bool` atom loads `1` or `0`. -/
theorem atomWord_bool {Γ : List Ty} (a : Atom Γ .bool) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) (hx : x < FR := by decide) :
    Runs κ ω L (atomWord a ρ x) f h (f.set x (bword (a.denote env))) h :=
  atomWord_runs a x hf henv hfe hl hnh hnL hnU rfl bword (fun _ _ hw => word_bool hw) hx

/-- The atom's word: a `U8` atom loads its byte zero-extended. -/
theorem atomWord_u8 {Γ : List Ty} (a : Atom Γ .u8) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) (hx : x < FR := by decide) :
    Runs κ ω L (atomWord a ρ x) f h (f.set x (a.denote env : UInt8).toUInt64) h :=
  atomWord_runs a x hf henv hfe hl hnh hnL hnU rfl (fun v : UInt8 => v.toUInt64)
    (fun _ _ hw => word_u8 hw) hx

theorem rp_lt {x : Nat} (h : FR ≤ x) : RP < x := by simp only [FR, RP] at h ⊢; omega

/-- A slot-resident variable lies wholly below a word destination or starts at or above it. -/
theorem Tl.Ok.word_ov {Γ : List Ty} {t : Ty} {K : Nat} {W : List Bool} {ρ : List Loc}
    {env : Env Γ} {f : Frame} (hk : (Tl.word K).Ok W ρ) (hfe : FEnvRel f env ρ) (m : Mem t Γ)
    {k : Nat} (h : (ρ.getD m.idx default).slot? = some k) : K ≤ k ∨ k + t.slotN ≤ K := by
  obtain ⟨_, hn, _⟩ := hfe.get m h
  rcases hk.2.2 m.idx k h with h1 | ⟨h1, _⟩
  · right; omega
  · left; exact h1

/-- A form of `atomSlots_reach` that needs only the source variable's words instead of the whole
frame relation, and keeps every slot outside the destination except `RP`. -/
theorem atomSlots_reach' {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hts : t.slotTy = true) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : ∀ m k, a = .var m → (ρ.getD m.idx default).slot? = some k →
      t.slotTy = true ∧ (ρ.getD m.idx default).nw = t.slotN ∧ WordsRel t (env.get m) f k)
    (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hx : RP < x)
    (hov : ∀ m k, a = .var m → (ρ.getD m.idx default).slot? = some k → x ≤ k ∨ k + t.slotN ≤ x) :
    ∃ f', Reaches κ ω L (atomSlots a ρ x t.slotN) f h f' h ∧ f' BP = f BP ∧
      (∀ y, y ≠ RP → (y < x ∨ x + t.slotN ≤ y) → f' y = f y) ∧ WordsRel t (a.denote env) f' x := by
  cases a with
  | var m =>
    have hsing := hl.var m
    have hsn := hsing.snd_none (hne m rfl)
    have hdl := hsing.dataLe hsn
    rw [SI.sz_none (hne m rfl)] at hdl
    simp only [atomSlots]
    split
    · rename_i o hρ
      have hv := (henv.get m (by rw [hρ]; rfl)).1.exact (hnh m rfl) (hne m rfl) hsn
      have hA : (S.getD m.idx default).A = bp + o := by have := hsing.2.1; rw [hρ] at this; exact this.1
      rw [hA] at hv hdl
      obtain ⟨f', hr, hout, hw⟩ := ldSlots_words (κ := κ) (ω := ω) (L := L) (K := x) (b := BP)
        hts hf (by simp only [RP, BP] at hx ⊢; omega) hv (by omega) (by omega)
      exact ⟨f', hr, hout BP (Or.inl (by simp only [RP, BP] at hx ⊢; omega)),
        fun y _ hy => hout y hy, hw⟩
    · rename_i o hρ
      have hv := (henv.get m (by rw [hρ]; rfl)).1.exact (hnh m rfl) (hne m rfl) hsn
      have hr₁ := ptr_load (κ := κ) (ω := ω) (L := L) m RP hl henv hρ hf hnL hnU
      obtain ⟨f', hr, hout, hw⟩ := ldSlots_words (κ := κ) (ω := ω) (L := L) (K := x) (b := RP)
        (o := 0) (A := (S.getD m.idx default).A)
        (f := f.set RP (UInt64.ofNat (S.getD m.idx default).A)) hts (Frame.set_same _ _ _)
        (by simp only [RP] at hx ⊢; omega) (by rw [Nat.add_zero]; exact hv) (by omega)
        (by omega)
      refine ⟨f', Reaches.seq hr₁.run hr, ?_, fun y hy hy' => ?_, hw⟩
      · rw [hout BP (Or.inl (by simp only [RP, BP] at hx ⊢; omega)), Frame.set_ne _ _ (by decide)]
      · rw [hout y hy', Frame.set_ne _ _ hy]
    · rename_i o hρ; exact absurd hρ (hsing.not_ref2 hsn o)
    · rename_i o k w hρ
      obtain ⟨_, hnw, B, hB, hw⟩ := hfe m k rfl (by rw [hρ]; rfl)
      rw [hρ] at hnw; simp only [Loc.nw_slot] at hnw; subst hnw
      rw [Nat.min_self]
      obtain ⟨f', hr, hout, hval⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) t.slotN
        (x := x) (k := k) (f := f) (h := h) (by have := hov m k rfl (by rw [hρ]; rfl); omega)
      refine ⟨f', hr, hout BP (Or.inl (by simp only [RP, BP] at hx ⊢; omega)),
        fun y _ hy => hout y hy, B, hB, wordsAt_iff.2 fun j hj => ?_⟩
      rw [hval j hj]; exact wordsAt_iff.1 hw j hj
  | lit v =>
    obtain ⟨f', hr, hout, hval⟩ := immSlots_reach (κ := κ) (ω := ω) (L := L)
      (chunks (Data.encodeBytes v) t.slotN) (x := x) (f := f) (h := h)
    rw [chunks_length] at hout hval
    refine ⟨f', hr, hout BP (Or.inl (by simp only [RP, BP] at hx ⊢; omega)),
      fun y _ hy => hout y hy, _, Data.reprBytes_encode v, wordsAt_iff.2 fun j hj => ?_⟩
    rw [hval j hj, chunks_getD _ _ _ hj]

/-- Loading the words of an atom of a slot-resident type into the slots from `x ≥ FR` makes those
slots hold its value and leaves every other slot from `FR` on unchanged. A source variable's slots
must start at or above `x` or lie wholly below it. -/
theorem atomSlots_reach {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hts : t.slotTy = true) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ) (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hx : RP < x)
    (hov : ∀ m k, a = .var m → (ρ.getD m.idx default).slot? = some k → x ≤ k ∨ k + t.slotN ≤ x) :
    ∃ f', Reaches κ ω L (atomSlots a ρ x t.slotN) f h f' h ∧ f' BP = f BP ∧
      (∀ y, FR ≤ y → (y < x ∨ x + t.slotN ≤ y) → f' y = f y) ∧ WordsRel t (a.denote env) f' x :=
  have ⟨f', hr, hb, hout, hw⟩ := atomSlots_reach' a x hts hf henv (fun m _ _ hk => hfe.get m hk)
    hl hnh hne hnL hnU hx hov
  ⟨f', hr, hb, fun y hy => hout y (by simp only [FR, RP] at hy ⊢; omega), hw⟩

/-- `atomSlotsS` copies an atom through the scratch slots, for a source that straddles the
destination. The slots from `x` then hold the atom's value and the other slots from `FR` on are
unchanged. -/
theorem atomSlotsS_reach {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (x : Nat)
    (hts : t.slotTy = true) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ) (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hx : FR ≤ x) :
    ∃ f', Reaches κ ω L (atomSlotsS a ρ x t.slotN) f h f' h ∧ f' BP = f BP ∧
      (∀ y, FR ≤ y → (y < x ∨ x + t.slotN ≤ y) → f' y = f y) ∧ WordsRel t (a.denote env) f' x := by
  have hcap := Ty.slotN_le hts
  unfold atomSlotsS
  cases ho : a.slotOf ρ with
  | none =>
    simp only
    exact atomSlots_reach a x hts hf henv hfe hl hnh hne hnL hnU (rp_lt hx) fun m k e hk => by
      subst e; simp only [Atom.slotOf] at ho; rw [ho] at hk; cases hk
  | some k =>
    have hk : ∀ m k', a = .var m → (ρ.getD m.idx default).slot? = some k' → k' = k := by
      intro m k' e hk'; subst e; simp only [Atom.slotOf] at ho; rw [ho] at hk'; cases hk'; rfl
    have hFRk : FR ≤ k := by
      cases a with
      | var m =>
        simp only [Atom.slotOf] at ho
        obtain ⟨_, hn, _⟩ := hfe.get m ho
        exact hfe.ge m.idx k (Loc.holds_iff.2 ⟨k, ho, Nat.le_refl _, by
          rw [hn]; have := Ty.slotN_pos hts; omega⟩)
      | lit v => simp [Atom.slotOf] at ho
    simp only
    split
    · rename_i hc
      exact atomSlots_reach a x hts hf henv hfe hl hnh hne hnL hnU (rp_lt hx)
        fun m k' e hk' => by rw [hk m k' e hk']; exact hc
    · obtain ⟨f₁, hr₁, hb₁, hout₁, hw₁⟩ := atomSlots_reach a REXT hts hf henv hfe hl hnh hne hnL hnU
        (by decide) fun m k' e hk' => by rw [hk m k' e hk']; left; simp only [FR, REXT] at hFRk ⊢; omega
      obtain ⟨f₂, hr₂, hout₂, hval₂⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) t.slotN
        (x := x) (k := REXT) (f := f₁) (h := h)
        (by right; simp only [FR, REXT, SLOT_CAP] at hx hcap ⊢; omega)
      have hBx : BP < x := by simp only [FR, BP] at hx ⊢; omega
      have hRy : ∀ y, FR ≤ y → REXT + t.slotN ≤ y := fun y hy => by
        simp only [FR, REXT, SLOT_CAP] at hy hcap ⊢; omega
      refine ⟨f₂, Reaches.seq hr₁ hr₂, by rw [hout₂ BP (Or.inl hBx), hb₁],
        fun y hy hy' => by rw [hout₂ y hy', hout₁ y hy (Or.inr (hRy y hy))], ?_⟩
      obtain ⟨B, hB, hw⟩ := hw₁
      exact ⟨B, hB, wordsAt_iff.2 fun j hj => by rw [hval₂ j hj]; exact wordsAt_iff.1 hw j hj⟩

/-! ## Cases -/

/-- An atom conforms to tail mode `whole x` only when it is the variable `x`. The proof unfolds
`Exp.Conf`, because `simp` over its equations is slow. -/
theorem _root_.Millipede.Exp.conf_atom_whole {Γ : List Ty} {t : Ty} {a : Atom Γ t} {x : Nat}
    (h : (Exp.atom a).Conf (.whole x) = true) : ∃ m, a = .var m ∧ m.idx = x := by
  cases a with
  | var m => exact ⟨m, rfl, beq_iff_eq.mp h⟩
  | lit v => exact absurd h Bool.false_ne_true

/-- A slot-resident binder has a slot-resident type. -/
theorem _root_.Millipede.Ty.slotTy_of_bind {Γ : List Ty} {s t : Ty} {e : Exp (s :: Γ) t}
    (h : e.slotBind = true) : s.slotTy = true := by
  simp only [Exp.slotBind, Bool.and_eq_true] at h; exact h.1.1

/-- An atom is copied to the destination, or in tail mode `whole x` it is the variable `x` itself,
which is already in place. -/
theorem msound_atom {Γ : List Ty} {t : Ty} (a : Atom Γ t) : MSoundAt κ ω (.atom a) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  have hb := H.size; have hbL := H.room; have hdn := H.dn; have hd := H.away
  simp only [Exp.memNeed] at hb hbL
  have hne := H.vs.atom a fun i h => by simpa [Exp.VSafe] using h
  cases tm with
  | none =>
    simp only [Tl.dsz] at hdn hd ⊢
    obtain ⟨f', B, hf', hBl, hBr, hr⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a H.lay hd
      (by omega) (by omega) H.bpOk H.envRel H.sl.rel (a.noHole H.hole) (by omega) (by omega) hne
    refine MSim.tick_done H.run hr rfl rfl (hf' BP (by decide) (by decide))
      (by show Data.reprBytes _ (rd _ _ t.size); rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr)
      (fun x hx => wr_out (by omega) (by unfold Prot InR at hx; omega)
        (by unfold Prot InR at hx; omega))
  | whole x =>
    obtain ⟨m, rfl, rfl⟩ := Exp.conf_atom_whole H.conf
    refine MSim.tick_done H.run (Runs.skip f h) rfl rfl rfl ?_
      (fun _ _ => rfl)
    exact (H.envRel.get m (H.sl.ns_of_tm (by simp [Tl.vars]))).1.exact
      ((H.lay.var m).2.2.1 H.tmOk) (hne m rfl) ((H.lay.var m).snd_none (hne m rfl))
  | split f0 cs => exact absurd H.conf (by cases a <;> exact Bool.false_ne_true)
  | word K =>
    have hts : t.slotTy = true := H.conf
    obtain ⟨f', hr, hfb, hout, hv⟩ := atomSlots_reach (κ := κ) (ω := ω) (L := L) a K hts H.bpOk
      H.envRel H.sl.rel H.lay (a.noHole H.hole) hne H.nL H.nU (rp_lt H.tmOk.1)
      fun m k e hk => by subst e; exact H.tmOk.word_ov H.sl.rel m hk
    simp only [lowerM]
    exact MSim.tick_word H.run hr rfl rfl hfb
      (fun y hy hy' => hout y hy (Or.inl hy')) hv
      fun x hx => SProt.lt_word H.tmOk hx

/-! ## Tail modes of the constructs -/

theorem conf_leaf {Γ : List Ty} {t : Ty} {e : Exp Γ t} {tm : Tl} (hC : e.Conf tm = true)
    (hl : ∀ tm', tm' ≠ Tl.none → e.Conf tm' = false) : tm = .none := by
  cases tm with
  | none => rfl
  | whole _ | split _ _ => rw [hl _ (fun h => by cases h)] at hC; cases hC
  | word k => rw [hl _ (fun h => by cases h)] at hC; cases hC

/-- A leaf construct that computes a one-word scalar conforms to the tail mode `none`, and to
`word K`, in which it writes its word straight into slot `K`. -/
theorem MSoundAt.leafW {Γ : List Ty} {t : Ty} {e : Exp Γ t}
    (H : ∀ (L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI) (n d bp : Nat) (env : Env Γ)
      (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
      MHyp ω e .none L W ρ S n d bp env f h w →
      MSim κ ω L ⟨lowerM e .none ρ n d, k, f, h, w, c⟩ k (TQ .none bp d ρ S t)
        (Prot bp n d t.size Γ S W) (e.exec ω κ .copy env w) (SProt ρ W))
    (HW : ∀ (K L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI) (n d bp : Nat) (env : Env Γ)
      (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
      MHyp ω e (.word K) L W ρ S n d bp env f h w →
      MSim κ ω L ⟨lowerM e (.word K) ρ n d, k, f, h, w, c⟩ k (TQ (.word K) bp d ρ S t)
        (Prot bp n d 0 Γ S W) (e.exec ω κ .copy env w) (SProt ρ W))
    (hleaf : ∀ x f0 cs, e.Conf (.whole x) = false ∧ e.Conf (.split f0 cs) = false := by
      intro x f0 cs; exact ⟨rfl, rfl⟩) : MSoundAt κ ω e :=
  .intro fun tm L W ρ S n d bp env k f h w c Hm => by
    cases tm with
    | none => exact H L W ρ S n d bp env k f h w c Hm
    | word K => exact HW K L W ρ S n d bp env k f h w c Hm
    | whole x => have := Hm.conf; rw [(hleaf x 0 []).1] at this; cases this
    | split f0 cs => have := Hm.conf; rw [(hleaf 0 f0 cs).2] at this; cases this

/-- A leaf construct conforms only to tail mode `none`. -/
theorem MSoundAt.leaf {Γ : List Ty} {t : Ty} {e : Exp Γ t}
    (H : ∀ (L : Nat) (W : List Bool) (ρ : List Loc) (S : List SI) (n d bp : Nat) (env : Env Γ)
      (k : List Kont) (f : Frame) (h : Heap) (w : World) (c : Nat),
      MHyp ω e .none L W ρ S n d bp env f h w →
      MSim κ ω L ⟨lowerM e .none ρ n d, k, f, h, w, c⟩ k (TQ .none bp d ρ S t)
        (Prot bp n d t.size Γ S W) (e.exec ω κ .copy env w) (SProt ρ W))
    (hleaf : ∀ tm', tm' ≠ Tl.none → e.Conf tm' = false := by
      intro tm' h'; cases tm' <;> first | rfl | exact absurd rfl h') : MSoundAt κ ω e :=
  .intro fun tm L W ρ S n d bp env k f h w c Hm => by
    obtain rfl := conf_leaf Hm.conf hleaf; exact H L W ρ S n d bp env k f h w c Hm

section
variable {Γ : List Ty} {u : Ty} {e₀ : Exp Γ u} {tm : Tl} {W : List Bool}
  {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}

/-- The hypotheses pass to a continuation `k` in the same context, with environment `env'`, frame
`f` and heap `h`, given the facts that depend on the term. -/
theorem MHyp.cont (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w) {k : Exp Γ u} {env' : Env Γ}
    {f : Frame} {h : Heap} (hC : k.Conf tm = true) (hR : k.Restr W) (hL : k.Lawful)
    (hF : k.Frozen) (hH : HoleAv k S) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env' ρ S) (hfe : FEnvRel f env' ρ) (hs : k.safe ω env' w)
    (hV : VS S (k.VSafe · tm))
    (hm : k.memNeed ≤ e₀.memNeed := by simp only [Exp.memNeed]; omega)
    (hna : ∀ i, e₀.noAddr i = true → k.noAddr i = true := by
      intro i h; simp only [Exp.noAddr, Bool.and_eq_true] at h; simp_all) :
    MHyp ω k tm L W ρ S n d bp env' f h w :=
  have := H.size; have := H.room
  ⟨hC, H.tmOk, hR, hL, hF, hH, H.lay, H.dn, H.away, by omega, hf, henv, hs, H.run, by omega, hV,
    H.sl.sub hfe fun i h ht => ⟨hna i h, ht⟩⟩

/-- The hypotheses pass to a term `k` under one more binder, a fresh writable variable at
`n' ≥ n` holding `v`. -/
theorem MHyp.push (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w) {s : Ty} {k : Exp (s :: Γ) u}
    {n' : Nat} {env' : Env Γ} {f : Frame} {h : Heap} {w' : World} (v : s.carrier) (hnn : n ≤ n') (hC : k.Conf tm.up = true)
    (hR : k.Restr (true :: W)) (hL : k.Lawful) (hF : k.Frozen)
    (hH : HoleAv k (⟨bp + n', none, none, none⟩ :: S))
    (hb : bp + n' + s.size + k.memNeed ≤ UInt64.size) (hbL : bp + n' + s.size + k.memNeed ≤ L)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env' ρ S) (hfe : FEnvRel f env' ρ)
    (hv : Data.reprBytes v (rd h (bp + n') s.size)) (hs : k.safe ω (.cons v env') w')
    (hV : VS S fun i => k.VSafe (i + 1) tm.up) (hw : w'.halted = false)
    (hna : ∀ i, e₀.noAddr i = true → k.noAddr (i + 1) = true := by
      intro i h; simp only [Exp.noAddr, Bool.and_eq_true] at h; simp_all) :
    MHyp ω k tm.up L (true :: W) (.own n' :: ρ) (⟨bp + n', none, none, none⟩ :: S) (n' + s.size) d bp
      (.cons v env') f h w' :=
  have := H.dn
  ⟨hC, H.tmOk.up true _ (fun _ => rfl) (by simp), hR, hL, hF, hH, (H.lay.mono hnn).push s true,
    by simp only [Tl.up_dsz]; omega, by simp only [Tl.up_dsz]; exact H.away.push s (by omega),
    by omega, hf, ⟨(fun _ => VarRel.of_exact hv), trivial, henv⟩, hs, hw, by omega, VS.push _ rfl hV,
    H.sl.push (.own n') (by simp) ⟨trivial, hfe⟩ (by simp) hna⟩

/-- The hypotheses pass to a term under a slot-resident binder: its value `v` in the frame
slots from `FR + slotsIn ρ`, its reserved bytes at `n' ≥ n`. -/
theorem MHyp.pushSlot (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w) {s : Ty}
    {k : Exp (s :: Γ) u} {n' : Nat} {env' : Env Γ} {f : Frame} {h : Heap} {w' : World}
    (v : s.carrier) (hnn : n ≤ n')
    (hC : k.Conf tm.up = true) (hR : k.Restr (true :: W)) (hL : k.Lawful) (hF : k.Frozen)
    (hH : HoleAv k (⟨bp + n', none, none, none⟩ :: S))
    (hb : bp + n' + s.size + k.memNeed ≤ UInt64.size) (hbL : bp + n' + s.size + k.memNeed ≤ L)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env' ρ S) (hfe : FEnvRel f env' ρ)
    (hts : s.slotTy = true) (hv : WordsRel s v f (FR + slotsIn ρ)) (hs : k.safe ω (.cons v env') w')
    (hV : VS S fun i => k.VSafe (i + 1) tm.up) (hw : w'.halted = false)
    (hna0 : k.noAddr 0 = true) (hna : ∀ i, e₀.noAddr i = true → k.noAddr (i + 1) = true) :
    MHyp ω k tm.up L (true :: W) (.slot n' (FR + slotsIn ρ) s.slotN :: ρ)
      (⟨bp + n', none, none, none⟩ :: S) (n' + s.size) d bp (.cons v env') f h w' :=
  have := H.dn
  ⟨hC, H.tmOk.up true _ (fun _ => rfl) (by simp), hR, hL, hF, hH,
    (H.lay.mono hnn).pushSlot s true _ _,
    by simp only [Tl.up_dsz]; omega, by simp only [Tl.up_dsz]; exact H.away.pushL s ⟨rfl, rfl⟩ (by omega),
    by omega, hf, ⟨(fun h => by rw [hts] at h; simp at h), trivial, henv⟩, hs, hw, by omega, VS.push _ rfl hV,
    H.sl.push _ (by simp) ⟨⟨Nat.le_add_right _ _, hts, rfl, hv⟩, hfe⟩ (fun _ => hna0) hna⟩

/-- A simulation under one more binder, as set up by `MHyp.push` or `MHyp.pushSlot`, is a
simulation for the enclosing term. -/
theorem MSim.unpush {s : State} {k : List Kont} {r : Out u.carrier} {s' : Ty}
    {n' : Nat} {l : Loc} (hnn : n ≤ n')
    (h : MSim κ ω L s k (TQ tm.up bp d (l :: ρ) (⟨bp + n', none, none, none⟩ :: S) u)
      (Prot bp (n' + s'.size) d (tm.up.dsz u) (s' :: Γ) (⟨bp + n', none, none, none⟩ :: S) (true :: W)) r
      (SProt (l :: ρ) (true :: W))) :
    MSim κ ω L s k (TQ tm bp d ρ S u) (Prot bp n d (tm.dsz u) Γ S W) r (SProt ρ W) :=
  (h.post fun _ _ hq _ => (TQ.up _ _ _ _ _).mp hq).weaken (fun a ha => by
    rw [Tl.up_dsz]; exact Prot.push s' _ hnn ha) fun x hx => hx.push l true

end

theorem conf_let {Γ : List Ty} {s t : Ty} {e₁ : Exp Γ s} {e₂ : Exp (s :: Γ) t} {tm : Tl}
    (h : (Exp.let_ e₁ e₂).Conf tm = true) : e₂.Conf tm.up = true := by
  cases tm with
  | none => exact e₂.conf_none
  | _ => exact h

theorem conf_ite {Γ : List Ty} {t : Ty} {c : Atom Γ .bool} {e₁ e₂ : Exp Γ t} {tm : Tl}
    (h : (Exp.ite c e₁ e₂).Conf tm = true) : e₁.Conf tm = true ∧ e₂.Conf tm = true := by
  cases tm with
  | none => exact ⟨e₁.conf_none, e₂.conf_none⟩
  | _ => exact Bool.and_eq_true_iff.mp h

theorem conf_match {Γ : List Ty} {ε α t : Ty} {s : Atom Γ (.result ε α)} {eE : Exp (ε :: Γ) t}
    {eO : Exp (α :: Γ) t} {tm : Tl} (h : (Exp.match_ s eE eO).Conf tm = true) :
    eE.Conf tm.up = true ∧ eO.Conf tm.up = true := by
  cases tm with
  | none => exact ⟨eE.conf_none, eO.conf_none⟩
  | _ => exact Bool.and_eq_true_iff.mp h

/-- The hypotheses pass to the branch that an `if` takes, in a frame that keeps `BP` and the slots
from `FR` on. -/
theorem MHyp.ite {Γ : List Ty} {t : Ty} {cnd : Atom Γ .bool} {e₁ e₂ : Exp Γ t} {tm : Tl}
    {L : Nat} {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ}
    {f fc : Frame} {h : Heap} {w : World}
    (H : MHyp ω (.ite cnd e₁ e₂) tm L W ρ S n d bp env f h w) (hfc : fc BP = UInt64.ofNat bp)
    (hfk : ∀ x, FR ≤ x → fc x = f x) :
    MHyp ω (bif cnd.denote env then e₁ else e₂) tm L W ρ S n d bp env fc h w := by
  have hC := conf_ite H.conf
  have hs := H.safe; have hb := H.size; have hbL := H.room
  simp only [Exp.safe] at hs; simp only [Exp.memNeed] at hb hbL
  have := Nat.le_max_left e₁.memNeed e₂.memNeed
  have := Nat.le_max_right e₁.memNeed e₂.memNeed
  have hfe := H.sl.rel.keep hfk
  cases hc : cnd.denote env <;> simp only [Bool.cond_false, Bool.cond_true]
  · exact ⟨hC.2, H.tmOk, H.restr.2, H.lawful.2, H.frozen.2, H.hole.sub fun _ _ h => h.2.2, H.lay,
      H.dn, H.away, by omega, hfc, H.envRel, hs.2 hc, H.run, by omega,
      H.vs.mono (fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2),
      H.sl.sub hfe fun i h ht => ⟨by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2, ht⟩⟩
  · exact ⟨hC.1, H.tmOk, H.restr.1, H.lawful.1, H.frozen.1, H.hole.sub fun _ _ h => h.2.1, H.lay,
      H.dn, H.away, by omega, hfc, H.envRel, hs.1 hc, H.run, by omega,
      H.vs.mono (fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2),
      H.sl.sub hfe fun i h ht => ⟨by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1, ht⟩⟩

/-- An `if` loads its condition into `RT` and then runs the branch it selects. -/
theorem msound_ite {Γ : List Ty} {t : Ty} (cnd : Atom Γ .bool) (e₁ e₂ : Exp Γ t)
    (ih₁ : MSoundAt κ ω e₁) (ih₂ : MSoundAt κ ω e₂) : MSoundAt κ ω (.ite cnd e₁ e₂) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  have hr := atomWord_bool (κ := κ) (ω := ω) (L := L) cnd RT H.bpOk H.envRel H.sl.rel H.lay
    (cnd.noHole fun i H' h' => (H.hole i H' h').1) H.nL H.nU
  have hfc : (f.set RT (bword (cnd.denote env))) BP = UInt64.ofNat bp := by
    rw [Frame.set_ne _ _ (by decide)]; exact H.bpOk
  have hA := (show MSoundAt κ ω (bif cnd.denote env then e₁ else e₂) by
    cases cnd.denote env <;> assumption).app (H.ite hfc hr.keep) k
      (c + Tick.ite.cost κ)
  revert hA hr hfc; cases hc : cnd.denote env <;> intro hr hfc hA <;>
  exact (MSim.tick H.run (MSim.runs H.run hr (by rw [hfc, H.bpOk]) (fun _ _ => rfl)
    (MSim.ite H.run (by simpa [Operand.eval, Frame.set, bword] using hA)))).of_eq
      (by simp [Exp.exec, hc]) (by simp [Exp.exec, hc]) (by simp [Exp.exec, hc, Tick.cost])

/-! ## Scalar results -/

theorem wordRel_u64 (x : UInt64) : WordRel .u64 x x :=
  ⟨natBytes 8 x.toNat, ⟨natBytes_length _ _, rfl⟩, decodeLE_natBytes8 x⟩

theorem wordRel_bool (b : Bool) : WordRel .bool b (bword b) :=
  ⟨natBytes 1 (if b then 1 else 0), ⟨natBytes_length _ _, rfl⟩, decode_bool b⟩

theorem wordRel_u8 (b : UInt8) : WordRel .u8 b b.toUInt64 :=
  ⟨natBytes 1 b.toNat, ⟨natBytes_length _ _, rfl⟩, decode_u8 b⟩

/-- Storing a `U64` writes its eight bytes. -/
theorem storeOk_u64 (x : UInt64) (h : Heap) (A : Nat) :
    ∃ B : List UInt8, B.length = Ty.u64.size ∧ Data.reprBytes x B ∧
      h.store (scalarWidth Ty.u64.size) (UInt64.ofNat A) x = wr h A B :=
  store_wordRel rfl (wordRel_u64 x) h A

theorem bword_decide (P : Prop) [Decidable P] : (if P then (1 : UInt64) else 0) = bword (decide P) := by
  by_cases h : P <;> simp [h, bword]

theorem bword_ne (P : Prop) [Decidable P] : (if P then (0 : UInt64) else 1) = bword (decide ¬ P) := by
  by_cases h : P <;> simp [h, bword]

/-- The arguments of a term read no variable with a hole. -/
def _root_.Millipede.Args.NoHole {Γ : List Ty} (S : List SI) : {ps : List Ty} → Args Γ ps → Prop
  | _, .nil => True
  | _, .cons a as => (∀ m, a = .var m → (S.getD m.idx default).hole = none) ∧ Args.NoHole S as

theorem _root_.Millipede.Args.noHole {Γ : List Ty} {S : List SI} : {ps : List Ty} → (as : Args Γ ps) →
    (∀ i H, (S.getD i default).hole = some H → as.Avoids i ⟨true, H.path⟩) → as.NoHole S
  | _, .nil, _ => trivial
  | _, .cons a as, h => ⟨a.noHole fun i H h' => (h i H h').1,
      Args.noHole as fun i H h' => (h i H h').2⟩

/-- The arguments of a term read no variable with an extent, that is, no slice view. -/
def _root_.Millipede.Args.NoExt {Γ : List Ty} (S : List SI) : {ps : List Ty} → Args Γ ps → Prop
  | _, .nil => True
  | _, .cons a as => (∀ m, a = .var m → (S.getD m.idx default).ext = none) ∧ Args.NoExt S as

theorem _root_.Millipede.Args.noExt {Γ : List Ty} {S : List SI} {P : Nat → Bool} (hV : VS S P) :
    {ps : List Ty} → (as : Args Γ ps) → (∀ i, P i = true → as.mentions i = false) → as.NoExt S
  | _, .nil, _ => trivial
  | _, .cons a as, h => ⟨hV.atom a fun i hi => by
      have := h i hi; simp only [Args.mentions, Bool.or_eq_false_iff] at this; exact this.1,
      Args.noExt hV as fun i hi => by
        have := h i hi; simp only [Args.mentions, Bool.or_eq_false_iff] at this; exact this.2⟩

/-- The loads, the operation and the cost of a primitive, after which the operation's word holds
the primitive's value. -/
theorem prim_spec {Γ ps : List Ty} {r : Ty} (p : Prim ps r) (args : Args Γ ps) {ρ : List Loc}
    {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W)
    (hnh : args.NoHole S) (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) :
    ∃ f', Runs κ ω L (primLoad args ρ) f h f' h ∧ f' BP = f BP ∧
      (primCode p [.slot RX, .slot RY]).1.cost κ = p.cost κ ∧
      WordRel r (p.denote (args.denote env)) ((primCode p [.slot RX, .slot RY]).2.1.eval
        ((primCode p [.slot RX, .slot RY]).2.2.1.eval f')
        ((primCode p [.slot RX, .slot RY]).2.2.2.eval f')) := by
  have hfx : ∀ v : UInt64, (f.set RX v) BP = UInt64.ofNat bp := fun v => by
    rw [Frame.set_ne _ _ (by decide)]; exact hf
  have hfex : ∀ v : UInt64, FEnvRel (f.set RX v) env ρ := fun v =>
    hfe.keep (Frame.set_keep f v (by decide))
  have hn : (0xFFFFFFFFFFFFFFFF : UInt64) = -1 := by decide
  cases p <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  all_goals first
    | (refine ⟨_, Runs.seq (atomWord_u64 a RX hf henv hfe hl hnh.1 hnL hnU)
          (atomWord_u64 b RY (hfx _) henv (hfex _) hl hnh.2.1 hnL hnU),
        by simp [Frame.set], by simp [primCode, Tick.cost, Prim.cost], ?_⟩)
    | (refine ⟨_, Runs.seq (atomWord_bool a RX hf henv hfe hl hnh.1 hnL hnU)
          (atomWord_bool b RY (hfx _) henv (hfex _) hl hnh.2.1 hnL hnU),
        by simp [Frame.set], by simp [primCode, Tick.cost, Prim.cost], ?_⟩)
    | (refine ⟨_, atomWord_u64 a RX hf henv hfe hl hnh.1 hnL hnU, by simp [Frame.set],
        by simp [primCode, Tick.cost, Prim.cost], ?_⟩)
    | (refine ⟨_, atomWord_bool a RX hf henv hfe hl hnh.1 hnL hnU, by simp [Frame.set],
        by simp [primCode, Tick.cost, Prim.cost], ?_⟩)
    | (refine ⟨_, atomWord_u8 a RX hf henv hfe hl hnh.1 hnL hnU, by simp [Frame.set],
        by simp [primCode, Tick.cost, Prim.cost], ?_⟩)
  all_goals simp only [primCode, Operand.eval, Frame.set, BinOp.eval, Prim.denote, Args.denote,
    List.getD_cons_zero, List.getD_cons_succ,
    show RX = RY ↔ False by decide, ↓reduceIte, hn,
    UInt64.xor_neg_one, UInt64.or_zero]
  all_goals first
    | exact wordRel_u64 _
    | (rw [word_and_255]; exact wordRel_u8 _)
    | (rw [bword_decide]; exact wordRel_bool _)
    | (rw [bword_ne]; exact wordRel_bool _)
    | (generalize a.denote env = x; cases x <;> exact wordRel_bool _)
    | (generalize a.denote env = x; generalize b.denote env = y; cases x <;> cases y <;>
        exact wordRel_bool _)
    | skip

/-- The case of a primitive. -/
theorem msound_prim {Γ ps : List Ty} {r : Ty} (p : Prim ps r) (args : Args Γ ps) :
    MSoundAt κ ω (.prim p args) := by
  refine .leafW (fun L W ρ S n d bp env k f h w c H => ?_) fun K L W ρ S n d bp env k f h w c H => ?_
  rotate_left
  · obtain ⟨f', hr, hf', hcost, hst⟩ := prim_spec (κ := κ) (ω := ω) (L := L) p args (ρ := ρ) H.bpOk
      H.envRel H.sl.rel H.lay (Args.noHole args H.hole) H.nL H.nU
    simp only [lowerM]
    have hK := H.tmOk.1
    exact MSim.tick_word H.run (Reaches.seq hr.run (Reaches.bin _ _ _ _ _ _)) rfl
      (by simp [Exp.exec, hcost]) (by rw [Frame.set_ne _ _ (by simp only [FR, BP] at hK ⊢; omega)]; exact hf')
      (fun x hx hlt => by rw [Frame.set_ne _ _ (by omega)]; exact hr.keep x hx)
      ((wordsRel_one (Ty.wordTy_slotN p.wordTy)).2 (by rw [Frame.set_same]; exact hst))
      fun x hx => SProt.lt_word H.tmOk hx
  have hdn := H.dn0; have hb := H.nU; have hbL := H.nL; have hf := H.bpOk
  obtain ⟨f', hr, hf', hcost, hst⟩ := prim_spec (κ := κ) (ω := ω) (L := L) p args (ρ := ρ) hf H.envRel
    H.sl.rel H.lay (Args.noHole args H.hole) hbL hb
  have hwr : (scalarWidth r.size).bytes ≤ r.size := by cases p <;> decide
  have hw1 : 1 ≤ (scalarWidth r.size).bytes := by
    cases (scalarWidth r.size) <;> decide
  generalize hv : (primCode p [.slot RX, .slot RY]).2.1.eval
    ((primCode p [.slot RX, .slot RY]).2.2.1.eval f')
    ((primCode p [.slot RX, .slot RY]).2.2.2.eval f') = v at hst
  obtain ⟨B, hBl, hBr, hBs⟩ := store_wordRel p.wordTy hst h (bp + d)
  have hrun : Runs κ ω L (.seq (primLoad args ρ) (.seq (.bin (primCode p [.slot RX, .slot RY]).2.1 RT
      (primCode p [.slot RX, .slot RY]).2.2.1 (primCode p [.slot RX, .slot RY]).2.2.2)
      (.store (scalarWidth r.size) (.slot BP) (UInt64.ofNat d) (.slot RT)))) f h
      (f'.set RT v) (wr h (bp + d) B) := by
    have e1 : (Operand.slot BP).eval (f'.set RT v) = UInt64.ofNat bp := by
      simp only [eval_slot]; rw [Frame.set_ne _ _ (by decide), hf', hf]
    refine Runs.seq hr (Runs.seq (Runs.congr (Runs.bin _ _ _ _ _ _) (by rw [hv]) rfl) ?_)
    refine Runs.congr (Runs.store _ _ _ _ _ _ (by
      rw [e1, ofNat_add_ofNat]; exact acc_ofNat (by omega) (by omega))) rfl ?_
    have e2 : (Operand.slot RT).eval (f'.set RT v) = v := by simp [Frame.set]
    rw [e1, e2, ofNat_add_ofNat, hBs]
  refine MSim.tick_done H.run hrun rfl (by simp [Exp.exec, hcost])
    (by rw [Frame.set_ne _ _ (by decide), hf']) ?_ ?_
  · show Data.reprBytes _ (rd _ _ r.size); rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr
  · intro x hx
    exact wr_out (by omega) (by unfold Prot at hx; omega) (by unfold Prot InR at hx; omega)

/-! ## `let` -/

/-- Loading the chunks of a slot-resident value into the slots from `K ≥ FR`, from bytes
representing it at offset `o` from the address in the scratch slot `b`, makes those slots hold the
value and leaves the slots below `K` unchanged. -/
theorem load_words {s : Ty} (hts : s.slotTy = true) {v : s.carrier} {A o K b : Nat} {f : Frame}
    {h : Heap} (hf : f b = UInt64.ofNat A) (hb : b < FR) (hK : FR ≤ K)
    (hv : Data.reprBytes v (rd h (A + o) s.size))
    (hbL : A + o + s.size ≤ L) (hbU : A + o + s.size ≤ UInt64.size) :
    ∃ f', Reaches κ ω L (ldSlots (scalarWidth s.size) K (.slot b) o s.slotN) f h f' h ∧
      f' BP = f BP ∧ (∀ x, x < K → f' x = f x) ∧ WordsRel s v f' K := by
  obtain ⟨f', hr, hout, hw⟩ := ldSlots_words (κ := κ) (ω := ω) (L := L) (K := K) hts hf (by omega)
    hv hbL hbU
  exact ⟨f', hr, hout BP (Or.inl (by simp only [FR, BP] at hK ⊢; omega)),
    fun x hx => hout x (Or.inl hx), hw⟩

/-! ## `Result` -/

/-- A `Result` has a one-byte tag. -/
theorem except_tagBytes (ε α : Ty) : Shape.tagBytes [Data.shape ε.carrier, Data.shape α.carrier] = 1 := rfl

theorem rpo_eq (ε α : Ty) : rpo ε α = Shape.payloadOffset [Data.shape ε.carrier, Data.shape α.carrier] := rfl

theorem rpo_ge (ε α : Ty) : 1 ≤ rpo ε α := by
  have := Shape.tagBytes_le_payloadOffset [Data.shape ε.carrier, Data.shape α.carrier]
  rw [except_tagBytes] at this; rw [rpo_eq]; exact this

theorem rpo_ok (ε α : Ty) : rpo ε α + α.size ≤ (Ty.result ε α).size := by
  rw [rpo_eq]; exact Shape.payload_add_size_le _ _ (by simp)

theorem rpo_err (ε α : Ty) : rpo ε α + ε.size ≤ (Ty.result ε α).size := by
  rw [rpo_eq]; exact Shape.payload_add_size_le _ _ (by simp)

theorem result_repr_ok {ε α : Ty} (v : α.carrier) (bs : List UInt8)
    (hl : bs.length = (Ty.result ε α).size) (ht : slice bs 0 1 = [1])
    (hp : Data.reprBytes v (slice bs (rpo ε α) α.size)) :
    @Data.reprBytes (Ty.result ε α).carrier _ (Except.ok v) bs :=
  ⟨hl, ht, hp⟩

theorem result_repr_err {ε α : Ty} (v : ε.carrier) (bs : List UInt8)
    (hl : bs.length = (Ty.result ε α).size) (ht : slice bs 0 1 = [0])
    (hp : Data.reprBytes v (slice bs (rpo ε α) ε.size)) :
    @Data.reprBytes (Ty.result ε α).carrier _ (Except.error v) bs :=
  ⟨hl, ht, hp⟩

/-- The tag byte and the payload of a represented `Result`. -/
theorem result_repr_inv {ε α : Ty} (r : (Ty.result ε α).carrier) (bs : List UInt8)
    (h : Data.reprBytes r bs) :
    (∀ v, r = .ok v → slice bs 0 1 = [1] ∧ Data.reprBytes v (slice bs (rpo ε α) α.size)) ∧
    (∀ v, r = .error v → slice bs 0 1 = [0] ∧ Data.reprBytes v (slice bs (rpo ε α) ε.size)) := by
  obtain ⟨_, hr⟩ := h
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;> subst hv <;> exact hr

/-- A tag byte `v` at `d`, then an atom at the payload offset: the bytes of a `Result`. -/
theorem tagged_runs {Γ : List Ty} {ε α p : Ty} (a : Atom Γ p) (v : UInt64) {ρ : List Loc}
    {S : List SI} {W : List Bool} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    (hp : rpo ε α + p.size ≤ (Ty.result ε α).size) (hl : Lay bp n Γ ρ S W)
    (hdn : d + (Ty.result ε α).size ≤ n) (hd : Away bp d (Ty.result ε α).size Γ ρ S)
    (hb : bp + n ≤ UInt64.size) (hbL : bp + n ≤ L) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hnh : ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, a = .var m → (S.getD m.idx default).ext = none) :
    ∃ f' h', Runs κ ω L (.seq (.store .w8 (.slot BP) (UInt64.ofNat d) (.imm v))
        (atomTo a ρ (d + rpo ε α))) f h f' h' ∧ f' BP = f BP ∧
      slice (rd h' (bp + d) (Ty.result ε α).size) 0 1 = [v.toUInt8] ∧
      Data.reprBytes (a.denote env) (slice (rd h' (bp + d) (Ty.result ε α).size) (rpo ε α) p.size) ∧
      ∀ x, Prot bp n d (Ty.result ε α).size Γ S W x → h' (UInt64.ofNat x) = h (UInt64.ofNat x) := by
  have hp1 := rpo_ge ε α
  have hst : Runs κ ω L (.store .w8 (.slot BP) (UInt64.ofNat d) (.imm v)) f h f
      (wr h (bp + d) [v.toUInt8]) :=
    Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega) (by omega) hf))
      rfl (by simp only [eval_slot, eval_imm, hf, ofNat_add_ofNat]; rfl)
  obtain ⟨f', B, hf', hBl, hBr, hr⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := d + rpo ε α)
    (h := wr h (bp + d) [v.toUInt8]) hl (hd.sub (by omega) (by omega)) (by omega) (by omega) hf
    (henv.wr_away hl (by omega) [_] (hd.sub (by omega) (by simp; omega)) (by simp; omega))
    hfe hnh (by omega) (by omega) hne
  refine ⟨f', _, Runs.seq hst hr, hf' BP (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [← rd_slice _ (bp + d) (Ty.result ε α).size 0 1 (by omega)]
    simp only [Nat.add_zero, rd]
    rw [wr_out (by omega) (by omega) (by omega)]
    simp [wr, Heap.store8]
  · rw [← rd_slice _ (bp + d) (Ty.result ε α).size _ _ (by omega), ← hBl, ← Nat.add_assoc,
      rd_wr _ _ _ (by omega)]
    exact hBr
  · intro x hx; unfold Prot InR at hx
    rw [wr_out (by omega) (by omega) (by omega)]
    exact wr_out (B := [_]) (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)

/-- A whole-word payload type has `8 · slotN` bytes. -/
theorem wordPay_size {p : Ty} (h8 : p.size % 8 = 0) : p.size = 8 * p.slotN := by
  unfold Ty.slotN; omega

/-! ## Constructors into frame slots -/

/-- The first `p.size` bytes of the words of a slot-resident value are its bytes. -/
theorem wordsBytes_take {p : Ty} (hts : p.slotTy = true) {f : Frame} {K : Nat} {B : List UInt8}
    (hB : B.length = p.size) (hw : WordsAt f K B p.slotN) :
    (wordsBytes f K p.slotN).take p.size = B := by
  rcases Ty.slotTy_cases hts with ⟨h1, hn, _⟩ | ⟨h8, -, _⟩
  · rw [hn, h1]; rw [hn, wordsAt_one (by omega)] at hw
    match B, (show B.length = 1 by omega), hw with
    | [b], _, hw => simp [wordsBytes, hw, decodeLE, natBytes, Nat.mod_eq_of_lt b.toNat_lt]
  · rw [wordsBytes_eq (by omega) hw, List.take_of_length_le (by omega)]

/-- A value's bytes at a multiple of 8 inside whole words are the first bytes of its words. -/
theorem slice_wordsBytes (f : Frame) {x N o s m : Nat} (ho : o % 8 = 0) (hm : o / 8 + m ≤ N)
    (hs : s ≤ 8 * m) : slice (wordsBytes f x N) o s = (wordsBytes f (x + o / 8) m).take s := by
  rw [← wordsBytes_slice f x (o / 8) m N hm, show o = 8 * (o / 8) by omega]
  simp only [slice, List.take_take, Nat.min_eq_left hs, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]

/-- An empty value is represented by no bytes. -/
theorem reprBytes_empty {p : Ty} (v : p.carrier) (h0 : p.size = 0) : Data.reprBytes v [] := by
  have := Data.reprBytes_encode v
  rwa [List.eq_nil_of_length_eq_zero (show (Data.encodeBytes v).length = 0 by simpa using h0)] at this

/-- The arguments' words are in the slots from `x`, each non-empty argument's at word `o / 8` for
its placement `[o]`. -/
def ArgsW (f : Frame) (x : Nat) : {ps : List Ty} → List (List Nat) → Env ps → Prop
  | _, os :: oss, .cons (t := p) v env =>
    (p.size = 0 ∨ WordsRel p v f (x + os.headD 0 / 8)) ∧ ArgsW f x oss env
  | _, _, _ => True

/-- The arguments' words, when the arguments fit in order, give their bytes in the words. -/
theorem argsAt_of_words {f : Frame} {x N : Nat} : ∀ {ps : List Ty} (oss : List (List Nat))
    (env : Env ps) (lo : Nat), wordsFit ps oss lo N = true → ArgsW f x oss env →
    ArgsAt oss env (wordsBytes f x N)
  | _, [], .nil, _, _, _ => trivial
  | _, os :: oss, .cons (t := p) v env, lo, hfit, hh => by
    obtain ⟨hv, hw⟩ := hh
    obtain ⟨o, rfl⟩ : ∃ o, os = [o] := by
      match os, hfit with
      | [o], _ => exact ⟨o, rfl⟩
      | [], h => simp [wordsFit] at h
      | _ :: _ :: _, h => simp [wordsFit] at h
    simp only [wordsFit] at hfit
    simp only [List.headD_cons] at hv
    refine ⟨fun o' ho' => ?_, ?_⟩
    · rw [List.mem_singleton] at ho'; rw [ho']
      split at hfit
      · rename_i h0; rw [h0, show slice _ o 0 = [] by simp [slice]]; exact reprBytes_empty v h0
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
        obtain ⟨⟨⟨⟨hts, ho8⟩, -⟩, hle⟩, -⟩ := hfit
        obtain ⟨B, hB, hwB⟩ := hv.resolve_left ‹_›
        have := Ty.slotTy_cases hts
        rw [slice_wordsBytes f ho8 hle (by omega)]
        rw [wordsBytes_take hts (Data.reprBytes_length hB) hwB]; exact hB
    · split at hfit
      · exact argsAt_of_words oss env lo hfit hw
      · simp only [Bool.and_eq_true] at hfit; exact argsAt_of_words oss env _ hfit.2 hw
  | _, [], .cons _ _, _, h, _ => by simp [wordsFit] at h
  | _, _ :: _, .nil, _, h, _ => by simp [wordsFit] at h

/-- `argsSlots` puts each argument's words at its place in the slots from `x`, provided each
argument variable's slots are away from the slots written so far, which start at `x + lo`. Only the
slots from `x + lo` below `x + N`, and `RP`, are written. -/
theorem argsSlots_reach {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} {h : Heap} (x N : Nat) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hx : RP < x)
    (hge : ∀ i k, (ρ.getD i default).slot? = some k → RP < k) :
    ∀ {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat)) (lo : Nat) (f : Frame),
    f BP = UInt64.ofNat bp → wordsFit ps oss lo N = true → args.slotsAway ρ x N oss = true →
    args.NoHole S → args.NoExt S →
    (∀ {t : Ty} (m : Mem t Γ) k, args.mentions m.idx = true →
      (ρ.getD m.idx default).slot? = some k → (x + lo ≤ k ∨ k + (ρ.getD m.idx default).nw ≤ x) →
      t.slotTy = true ∧ (ρ.getD m.idx default).nw = t.slotN ∧ WordsRel t (env.get m) f k) →
    ∃ f', Reaches κ ω L (argsSlots ρ x N args oss) f h f' h ∧ f' BP = f BP ∧
      (∀ y, y ≠ RP → (y < x + lo ∨ x + N ≤ y) → f' y = f y) ∧ ArgsW f' x oss (args.denote env)
  | _, .nil, oss, _, f, _, _, _, _, _, _ => by
    refine ⟨f, ?_, rfl, fun _ _ _ => rfl, ?_⟩
    · cases oss <;> exact (Runs.skip f h).run
    · cases oss <;> trivial
  | _, .cons (t := p) a as, [], _, f, _, hfit, _, _, _, _ => by simp [wordsFit] at hfit
  | _, .cons (t := p) a as, os :: oss, lo, f, hf, hfit, haw, hnh, hnx, hsrc => by
    obtain ⟨o, rfl⟩ : ∃ o, os = [o] := by
      match os, hfit with
      | [o], _ => exact ⟨o, rfl⟩
      | [], h => simp [wordsFit] at h
      | _ :: _ :: _, h => simp [wordsFit] at h
    simp only [Args.slotsAway, Bool.and_eq_true, List.headD_cons] at haw
    have hment : ∀ i, as.mentions i = true → (Args.cons a as).mentions i = true := fun i h => by
      simp [Args.mentions, h]
    simp only [wordsFit] at hfit
    simp only [argsSlots, List.headD_cons]
    split at hfit
    · -- an empty argument: nothing
      rename_i h0
      have hts : p.slotTy = false := by
        cases e : p.slotTy
        · rfl
        · have := Ty.slotN_pos e; unfold Ty.slotN at this; omega
      obtain ⟨f', hr, hb, hout, hw⟩ := argsSlots_reach x N henv hl hnL hnU hx hge as oss lo f hf
        hfit haw.2 hnh.2 hnx.2 fun m k hm hk hc => hsrc m k (hment _ hm) hk hc
      refine ⟨f', ?_, hb, hout, Or.inl h0, hw⟩
      simp only [hts, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact Reaches.seq (Runs.skip f h).run hr
    · rename_i h0
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
      obtain ⟨⟨⟨⟨hts, ho8⟩, hlo⟩, hle⟩, hfit⟩ := hfit
      have hmin : min p.slotN (N - o / 8) = p.slotN := by omega
      -- the argument's words at `x + o / 8`
      obtain ⟨f₁, hr₁, hb₁, hout₁, hw₁⟩ : ∃ f₁, Reaches κ ω L (if p.slotTy && a.slotOf ρ !=
            some (x + o / 8) then atomSlots a ρ (x + o / 8) (min p.slotN (N - o / 8)) else .skip)
            f h f₁ h ∧ f₁ BP = f BP ∧
          (∀ y, y ≠ RP → (y < x + o / 8 ∨ x + o / 8 + p.slotN ≤ y) → f₁ y = f y) ∧
          WordsRel p (a.denote env) f₁ (x + o / 8) := by
        rw [hmin, hts, Bool.true_and]
        split
        · rename_i hne
          -- the source's slots are away from the destination; an argument already in place is skipped
          have hA : ∀ m k, a = .var m → (ρ.getD m.idx default).slot? = some k →
              x + N ≤ k ∨ k + (ρ.getD m.idx default).nw ≤ x := fun m k e hk => by
            subst e
            have h1 := haw.1
            simp only [Atom.slotOf, hk, Atom.slotNw, Bool.or_eq_true, beq_iff_eq] at h1 hne
            simp only [bne_iff_ne, ne_eq, Option.some.injEq] at hne
            rcases h1 with (h | h) | h
            · exact absurd h hne
            · exact Or.inl (of_decide_eq_true h)
            · exact Or.inr (of_decide_eq_true h)
          refine atomSlots_reach' a _ hts hf henv (fun m k e hk => hsrc m k (by subst e; simp
            [Args.mentions, Atom.isVar]) hk ?_) hl hnh.1 hnx.1 hnL hnU (by omega)
            fun m k e hk => ?_
          · have := hA m k e hk; omega
          · have := hA m k e hk
            obtain ⟨_, hn, _⟩ := hsrc m k (by subst e; simp [Args.mentions, Atom.isVar]) hk
              (by omega)
            omega
        · rename_i heq
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
          obtain ⟨m, rfl, hk⟩ : ∃ m, a = .var m ∧ (ρ.getD m.idx default).slot? = some (x + o / 8) := by
            cases a with
            | var m => exact ⟨m, rfl, heq⟩
            | lit v => simp [Atom.slotOf] at heq
          obtain ⟨-, -, hw⟩ := hsrc m _ (by simp [Args.mentions, Atom.isVar]) hk (Or.inl (by omega))
          exact ⟨f, (Runs.skip f h).run, rfl, fun _ _ _ => rfl, hw⟩
      obtain ⟨f', hr, hb, hout, hw⟩ := argsSlots_reach x N henv hl hnL hnU hx hge as oss
        (o / 8 + p.slotN) f₁ (by rw [hb₁, hf]) hfit haw.2 hnh.2 hnx.2
        fun m k hm hk hc => by
          obtain ⟨h1, h2, hw⟩ := hsrc m k (hment _ hm) hk (by omega)
          refine ⟨h1, h2, hw.congr fun y hy hy' => hout₁ y ?_ ?_⟩
          · have := hge _ _ hk; omega
          · omega
      refine ⟨f', Reaches.seq hr₁ hr, by rw [hb, hb₁], fun y hy hy' => by
        rw [hout y hy (by omega), hout₁ y hy (by omega)], Or.inr ?_, hw⟩
      exact hw₁.congr fun y hy hy' => hout y (by omega) (by omega)

theorem ArgsAt.congr {bs bs' : List UInt8} : ∀ {ps : List Ty} (oss : List (List Nat)) (env : Env ps),
    ArgsAt oss env bs → (∀ q ∈ placements ps oss, slice bs' q.1 q.2 = slice bs q.1 q.2) →
    ArgsAt oss env bs'
  | _, [], _, _, _ => by cases ‹Env _› <;> trivial
  | _, _ :: _, .nil, _, _ => trivial
  | _, os :: oss, .cons (t := t) (Γ := ts) v env, hh, he => by
    obtain ⟨h1, h2⟩ := hh
    refine ⟨fun o ho => ?_, ArgsAt.congr oss env h2 fun q hq => he q ?_⟩
    · have hm : (o, t.size) ∈ placements (t :: ts) (os :: oss) := by
        simp only [placements]; exact List.mem_append_left _ (List.mem_map_of_mem ho)
      rw [he (o, t.size) hm]; exact h1 o ho
    · simp only [placements]; exact List.mem_append_right _ hq

/-- No argument variable's slots meet the scratch slots from `REXT`, because every slot-resident
variable is from `FR` on. -/
theorem slotsAway_scratch {Γ : List Ty} {ρ : List Loc} {N : Nat} (hN : N ≤ SLOT_CAP)
    (hge : ∀ i k, (ρ.getD i default).slot? = some k → FR ≤ k) :
    ∀ {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat)), args.slotsAway ρ REXT N oss = true
  | _, .nil, _ => by simp [Args.slotsAway]
  | _, .cons _ _, [] => by simp [Args.slotsAway]
  | _, .cons a as, os :: oss => by
    simp only [Args.slotsAway, slotsAway_scratch hN hge as oss, Bool.and_true]
    cases a with
    | lit _ => rfl
    | var m =>
      simp only [Atom.slotOf]
      cases hk : (ρ.getD m.idx default).slot? with
      | none => rfl
      | some k =>
        have := hge _ _ hk
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        left; right; simp only [FR, REXT, SLOT_CAP] at this hN ⊢; omega

/-- The only argument of a one-byte value is one byte at word 0, which leaves its byte
zero-extended in the word. -/
theorem argsW_one_byte {f : Frame} {x : Nat} : ∀ {ps : List Ty} {oss : List (List Nat)}
    {env : Env ps}, tySizes ps = [1] → wordsFit ps oss 0 1 = true → ArgsW f x oss env →
    (f x).toNat < 256
  | [p], [o] :: oss', .cons v .nil, h1, hfit, hw => by
    simp only [tySizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [wordsFit, h1, Nat.one_ne_zero, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hfit
    obtain ⟨⟨⟨⟨hts, -⟩, -⟩, hle⟩, -⟩ := hfit
    obtain ⟨B, hB, hwB⟩ := hw.1.resolve_left (by omega)
    have hBl : B.length = 1 := (Data.reprBytes_length hB).trans h1
    have hn : p.slotN = 1 := by unfold Ty.slotN; omega
    rw [hn, wordsAt_one (by omega), show x + [o].headD 0 / 8 = x by simp; omega] at hwB
    match B, hBl with
    | [c], _ => rw [hwB]; simp [decodeLE]; exact c.toNat_lt
  | [], _, _, h1, _, _ => by simp [tySizes] at h1
  | _ :: _ :: _, _, _, h1, _, _ => by simp [tySizes] at h1
  | [_], [], _, _, h, _ => by simp [wordsFit] at h
  | [_], [] :: _, _, _, h, _ => by simp [wordsFit] at h
  | [_], (_ :: _ :: _) :: _, _, _, h, _ => by simp [wordsFit] at h

/-- The bytes of a constructor's words, as written by `ctorSlots`, are the tag byte and the
arguments' bytes at their placements inside `sz`. -/
theorem ctor_words {f : Frame} {x : Nat} {ps : List Ty} {oss : List (List Nat)} {env : Env ps}
    {tag : Option Nat} {N sz : Nat} (hN1 : 1 ≤ N)
    (hfit : wordsFit ps oss (if tag.isSome then 1 else 0) N = true)
    (hsz : sz = 8 * N ∨ (sz = 1 ∧ N = 1 ∧ (tag.isSome ∨ tySizes ps = [1])))
    (hin : ∀ q ∈ placements ps oss, q.1 + q.2 ≤ sz) (hw : ArgsW f x oss env)
    (htag : ∀ i, tag = some i → f x = UInt64.ofNat (i % 256)) :
    ∃ B : List UInt8, B.length = sz ∧ TagAt tag B ∧ ArgsAt oss env B ∧ WordsAt f x B N := by
  have hargs := argsAt_of_words oss env _ hfit hw
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hW : wordsBytes f x (N' + 1) = natBytes 8 (f x).toNat ++ wordsBytes f (x + 1) N' := rfl
  have hhead : ∀ i, tag = some i → (f x).toUInt8 = (UInt64.ofNat i).toUInt8 := fun i hi => by
    rw [htag i hi]; apply UInt8.toNat_inj.mp; simp
  rcases hsz with rfl | ⟨rfl, hN, h1⟩
  · refine ⟨wordsBytes f x (N' + 1), by simp, ?_, hargs, wordsAt_wordsBytes _ _ _⟩
    cases tag with
    | none => trivial
    | some i =>
      show (wordsBytes f x (N' + 1)).head? = some _
      rw [hW, natBytes8_eq]; simp [hhead i rfl]
  · obtain rfl : N' = 0 := by omega
    -- the word is the zero-extended byte
    have hlt : (f x).toNat < 256 := by
      cases ht : tag.isSome
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, false_or] at hfit h1
        exact argsW_one_byte h1 hfit hw
      · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp ht
        rw [htag i hi]; simp [UInt64.toNat_ofNat']; omega
    have hb : decodeLE [(f x).toUInt8] = f x := by
      apply UInt64.toNat_inj.mp; simp [decodeLE]; omega
    refine ⟨[(f x).toUInt8], rfl, ?_, ArgsAt.congr oss env hargs fun q hq => ?_, ?_⟩
    · cases tag with
      | none => trivial
      | some i => show [(f x).toUInt8].head? = some _; simp [hhead i rfl]
    · have := hin q hq
      rw [hW, natBytes8_eq]
      rcases (show q.2 = 0 ∨ (q.1 = 0 ∧ q.2 = 1) by omega) with h0 | ⟨h0, h1⟩
      · simp [slice, h0]
      · simp [slice, h0, h1]
    · rw [wordsAt_one (by simp), hb]

/-- `ctorSlots` into the `N` slots from `x`, where `x` is above the scratch slot `RP`, writes the
tag word and then the arguments' words. Only the slots from `x` below `x + N`, and `RP`, are
written. -/
theorem ctorSlots_reach {Γ ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame}
    {h : Heap} (x N : Nat) (hN1 : 1 ≤ N) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ) (hl : Lay bp n Γ ρ S W)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) (hx : RP < x)
    (hge : ∀ i k, (ρ.getD i default).slot? = some k → RP < k)
    (hfit : wordsFit ps plan.1 (if plan.2.isSome then 1 else 0) N = true)
    (haw : args.slotsAway ρ x N plan.1 = true)
    (hnh : args.NoHole S) (hne : args.NoExt S) :
    ∃ f', Reaches κ ω L (ctorSlots args plan ρ x N) f h f' h ∧ f' BP = f BP ∧
      (∀ y, y ≠ RP → (y < x ∨ x + N ≤ y) → f' y = f y) ∧ ArgsW f' x plan.1 (args.denote env) ∧
      ∀ i, plan.2 = some i → f' x = UInt64.ofNat (i % 256) := by
  obtain ⟨os, tag⟩ := plan
  simp only at hfit haw ⊢
  -- the tag word
  obtain ⟨f₁, hr₁, hb₁, hout₁, ht₁, lo, hlo, hlo1, hfit'⟩ : ∃ f₁, Reaches κ ω L
      (match tag with | some i => .mov x (.imm (UInt64.ofNat (i % 256))) | none => .skip) f h f₁ h ∧
      f₁ BP = f BP ∧ (∀ y, (y < x ∨ x + (if tag.isSome then 1 else 0) ≤ y) → f₁ y = f y) ∧
      (∀ i, tag = some i → f₁ x = UInt64.ofNat (i % 256)) ∧
      ∃ lo, lo ≤ 1 ∧ lo = (if tag.isSome then 1 else 0) ∧ wordsFit ps os lo N = true := by
    cases tag with
    | none => exact ⟨f, (Runs.skip f h).run, rfl, fun _ _ => rfl, nofun, 0, by omega, rfl, hfit⟩
    | some i =>
      refine ⟨_, Reaches.mov x _ f h, by rw [Frame.set_ne _ _ (by simp only [RP, BP] at hx ⊢; omega)],
        fun y hy => Frame.set_ne _ _ (by simp at hy; omega), fun i' hi => ?_, 1, Nat.le_refl _, rfl,
        hfit⟩
      cases hi; simp
  obtain ⟨f', hr, hb, hout, hw⟩ := argsSlots_reach x N henv hl hnL hnU hx hge args os lo f₁
    (by rw [hb₁, hf]) hfit' haw hnh hne fun m k _ hk hc => by
      obtain ⟨h1, h2, hw⟩ := hfe.get m hk
      exact ⟨h1, h2, hw.congr fun y hy hy' => hout₁ y (by omega)⟩
  refine ⟨f', Reaches.seq hr₁ hr, by rw [hb, hb₁], fun y hy hy' => ?_, hw, fun i hi => ?_⟩
  · rw [hout y hy (by omega), hout₁ y (by omega)]
  · subst hi
    simp only [Option.isSome_some, ↓reduceIte] at hlo1
    rw [hout x (by simp only [RP] at hx ⊢; omega) (by omega)]; exact ht₁ i rfl

/-- `ctorCode` builds a constructor in the `N` slots from `k ≥ FR`, either directly or through the
scratch slots from `REXT` followed by a move. The slots from `k` then hold `sz` bytes with the tag
byte and the arguments at their placements, and the other slots from `FR` on are unchanged. -/
theorem ctorCode_reach {Γ ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame}
    {h : Heap} (k N sz : Nat) (hN1 : 1 ≤ N) (hN : N ≤ SLOT_CAP) (hK : FR ≤ k)
    (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ) (hl : Lay bp n Γ ρ S W)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size)
    (hge : ∀ i k, (ρ.getD i default).slot? = some k → FR ≤ k)
    (hfit : wordsFit ps plan.1 (if plan.2.isSome then 1 else 0) N = true)
    (hsz : sz = 8 * N ∨ (sz = 1 ∧ N = 1 ∧ (plan.2.isSome ∨ tySizes ps = [1])))
    (hin : ∀ q ∈ placements ps plan.1, q.1 + q.2 ≤ sz)
    (hnh : args.NoHole S) (hne : args.NoExt S) :
    ∃ f', Reaches κ ω L (ctorCode args plan ρ k N) f h f' h ∧ f' BP = f BP ∧
      (∀ y, FR ≤ y → (y < k ∨ k + N ≤ y) → f' y = f y) ∧
      ∃ B : List UInt8, B.length = sz ∧ TagAt plan.2 B ∧ ArgsAt plan.1 (args.denote env) B ∧
        WordsAt f' k B N := by
  have hge' : ∀ i k, (ρ.getD i default).slot? = some k → RP < k := fun i k hk => by
    have := hge i k hk; simp only [FR, RP] at this ⊢; omega
  have hFR : ∀ y, FR ≤ y → y ≠ RP := fun y hy => by simp only [FR, RP] at hy ⊢; omega
  unfold ctorCode; split
  · rename_i haw
    obtain ⟨f', hr, hb, hout, hw, ht⟩ := ctorSlots_reach args plan k N hN1 hf henv hfe hl hnL hnU
      (by simp only [FR, RP] at hK ⊢; omega) hge' hfit haw hnh hne
    exact ⟨f', hr, hb, fun y hy hy' => hout y (hFR y hy) hy',
      ctor_words hN1 hfit hsz hin hw ht⟩
  · obtain ⟨f₁, hr₁, hb₁, hout₁, hw, ht⟩ := ctorSlots_reach args plan REXT N hN1 hf henv hfe hl
      hnL hnU (by decide) hge' hfit (slotsAway_scratch hN hge args plan.1) hnh hne
    obtain ⟨B, hBl, hBt, hBa, hBw⟩ := ctor_words hN1 hfit hsz hin hw ht
    obtain ⟨f₂, hr₂, hout₂, hval₂⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) N (x := k)
      (k := REXT) (f := f₁) (h := h) (by right; simp only [FR, REXT, SLOT_CAP] at hK hN ⊢; omega)
    have hRy : ∀ y, FR ≤ y → REXT + N ≤ y := fun y hy => by
      simp only [FR, REXT, SLOT_CAP] at hy hN ⊢; omega
    refine ⟨f₂, Reaches.seq hr₁ hr₂, by
        rw [hout₂ BP (Or.inl (by simp only [FR, BP] at hK ⊢; omega)), hb₁],
      fun y hy hy' => by rw [hout₂ y hy', hout₁ y (hFR y hy) (Or.inr (hRy y hy))],
      B, hBl, hBt, hBa, wordsAt_iff.2 fun j hj => by rw [hval₂ j hj]; exact wordsAt_iff.1 hBw j hj⟩

/-- The case of `ok` and `err`, which `resultCode` lowers by writing the tag byte and the payload
atom `a` at offset `rpo` to the destination. When the result is slot-resident, it is instead built
as a constructor in the slots from `K`. -/
theorem msound_result {Γ : List Ty} {ε α p : Ty} {e : Exp Γ (.result ε α)} (a : Atom Γ p)
    (tag : Nat) (v : Env Γ → (Ty.result ε α).carrier)
    (hcode : ∀ tm ρ n d, lowerM e tm ρ n d =
      .seq (.tick (.ctor (width (.result ε α)))) (resultCode ε α a tag tm ρ d))
    (hexec : ∀ env w, e.exec ω κ .copy env w = ⟨v env, w, (Tick.ctor (width (.result ε α))).cost κ⟩)
    (hconf : ∀ K, e.Conf (.word K) = Ty.slotSum ε α)
    (hle : rpo ε α + p.size ≤ (Ty.result ε α).size)
    (hpay : Ty.slotSum ε α = true →
      (rpo ε α = 8 ∨ p.size = 0) ∧ (p.size = 0 ∨ (p.slotTy = true ∧ p.size % 8 = 0)))
    (hrepr : ∀ env B, B.length = (Ty.result ε α).size → slice B 0 1 = [(UInt64.ofNat tag).toUInt8] →
      Data.reprBytes (a.denote env) (slice B (rpo ε α) p.size) → Data.reprBytes (v env) B)
    (hhole : ∀ S, HoleAv e S → ∀ m, a = .var m → (S.getD m.idx default).hole = none)
    (hvs : ∀ i tm, e.VSafe i tm = true → a.isVar i = false)
    (hleaf : ∀ x f0 cs, e.Conf (.whole x) = false ∧ e.Conf (.split f0 cs) = false) :
    MSoundAt κ ω e := by
  refine .leafW (fun L W ρ S n d bp env k f h w c H => ?_)
    (fun K L W ρ S n d bp env k f h w c H => ?_) hleaf
  · obtain ⟨f', h', hr, hf', h1, h2, hm⟩ := tagged_runs (κ := κ) (ω := ω) (L := L) a
      (UInt64.ofNat tag) hle H.lay H.dn H.away H.nU H.nL H.bpOk H.envRel H.sl.rel (hhole S H.hole)
      (H.vs.atom a fun i h => hvs i _ h)
    rw [hcode]
    exact MSim.tick_done H.run hr (by rw [hexec]) (by simp [hexec, Tick.cost]) hf'
      (by rw [hexec]; exact hrepr env _ (rd_length _ _ _) h1 h2) hm
  · have hs : Ty.slotSum ε α = true := by rw [← hconf K]; exact H.conf
    obtain ⟨hres, -⟩ := slotSum_facts hs
    obtain ⟨hpo, hpay⟩ := hpay hs
    have hN1 := Ty.slotN_pos hres
    have hfit : wordsFit [p] [[rpo ε α]] 1 (Ty.result ε α).slotN = true := by
      simp only [wordsFit]
      split
      · rfl
      · rename_i h0
        obtain ⟨hts, hp8⟩ := hpay.resolve_left h0
        have h8 := hpo.resolve_right h0
        have := wordPay_size hp8
        rcases Ty.slotTy_cases hres with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
        · omega
        · have hle' : 8 + p.size ≤ (Ty.result ε α).size := h8 ▸ hle
          simp only [hts, h8, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          refine ⟨⟨⟨⟨trivial, trivial⟩, by decide⟩, ?_⟩, trivial⟩; unfold Ty.slotN at *; omega
    obtain ⟨f'', hr, hb, hlo, B, hBl, hBt, hBa, hw⟩ := ctorCode_reach (κ := κ) (ω := ω) (L := L)
      (.cons a .nil) ([[rpo ε α]], some tag) K _ (Ty.result ε α).size hN1 (Ty.slotN_le hres)
      H.tmOk.1 H.bpOk H.envRel H.sl.rel H.lay H.nL H.nU (fun i k hk => H.sl.ok.range i k hk |>.1)
      hfit (by rcases Ty.slotTy_cases hres with ⟨h1, h2, _⟩ | ⟨h1, _, _⟩ <;> simp_all)
      (by simp [placements]; omega) ⟨hhole S H.hole, trivial⟩
      ⟨H.vs.atom a fun i h => hvs i _ h, trivial⟩
    rw [hcode]
    simp only [resultCode, hs, ↓reduceIte]
    have hB0 : slice B 0 1 = [(UInt64.ofNat tag).toUInt8] := by
      cases B with
      | nil => simp [TagAt] at hBt
      | cons b _ => simp only [TagAt, List.head?_cons, Option.some.injEq] at hBt; simp [slice, hBt]
    exact MSim.tick_word H.run hr (by rw [hexec]) (by simp [hexec, Tick.cost]) hb
      (fun y hy hy' => hlo y hy (Or.inl hy'))
      ⟨B, by rw [hexec]; exact hrepr env B hBl hB0 (hBa.1 _ (List.mem_singleton_self _)), hw⟩
      fun x hx => SProt.lt_word H.tmOk hx

theorem msound_ok {Γ : List Ty} {ε α : Ty} (a : Atom Γ α) :
    MSoundAt κ ω (Exp.ok (ε := ε) a) :=
  msound_result a 1 (fun env => .ok (a.denote env)) (fun _ _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (rpo_ok ε α)
    (fun h => ⟨((slotSum_facts h).2.1).imp_right fun h => h.2, (slotSum_facts h).2.2.2⟩)
    (fun _ B hl ht hp => result_repr_ok _ B hl ht hp) (fun _ H => a.noHole H)
    (fun i _ h => by simpa [Exp.VSafe] using h) fun _ _ _ => ⟨rfl, rfl⟩

theorem msound_err {Γ : List Ty} {ε α : Ty} (a : Atom Γ ε) :
    MSoundAt κ ω (Exp.err (α := α) a) :=
  msound_result a 0 (fun env => .error (a.denote env)) (fun _ _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (rpo_err ε α)
    (fun h => ⟨((slotSum_facts h).2.1).imp_right fun h => h.1, (slotSum_facts h).2.2.1⟩)
    (fun _ B hl ht hp => result_repr_err _ B hl ht hp) (fun _ H => a.noHole H)
    (fun i _ h => by simpa [Exp.VSafe] using h) fun _ _ _ => ⟨rfl, rfl⟩

/-! ## Scrutinees and arms -/

/-- A scrutinee's bytes are those of its owned variable, or, for a literal or a reference, a copy
at the watermark. -/
theorem scrut_spec {Γ : List Ty} {t : Ty} (s : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (hl : Lay bp n Γ ρ S W)
    (hbn : bp + n + t.size ≤ UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hnh : ∀ m, s = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + n + t.size ≤ L) (hne : ∀ m, s = .var m → (S.getD m.idx default).ext = none)
    (hns : ∀ m, s = .var m → (ρ.getD m.idx default).isSlot = false) :
    ∃ f₁ h₁, Runs κ ω L (scrutPre s ρ n) f h f₁ h₁ ∧ f₁ BP = f BP ∧
      (∀ a, a < bp + n → h₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧
      scrutLoc s ρ n ≤ n ∧
      Data.reprBytes (s.denote env) (rd h₁ (bp + scrutLoc s ρ n) t.size) := by
  cases s with
  | var m =>
    have hsing := hl.var m
    simp only [scrutPre, scrutLoc]
    split
    · rename_i o hρ
      have hA : (S.getD m.idx default).A = bp + o := by have := hsing.2.1; rw [hρ] at this; exact this.1
      have hs : o + t.size ≤ n := by have := hsing.slotLe; rw [hρ] at this; exact this
      refine ⟨f, h, Runs.skip _ _, rfl, fun _ _ => rfl, by omega, ?_⟩
      rw [← hA]; exact (henv.get m (hns m rfl)).1.exact (hnh m rfl) (hne m rfl)
        (hsing.snd_none (hne m rfl))
    · rename_i o k hρ; have := hns m rfl; rw [hρ] at this; cases this
    · rename_i o hρ
      obtain ⟨f', B, hf', hBl, hBr, hr⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) (.var m) (d := n)
        hl (hl.away (Nat.le_refl _)) (by omega) (by omega) hf henv hfe hnh (by omega) (by omega) hne
      refine ⟨f', _, by simpa [atomTo, hρ] using hr, hf' BP (by decide) (by decide),
        fun a ha => wr_out (by omega) (by omega) (by omega), Nat.le_refl _, ?_⟩
      rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr
    · rename_i o hρ; exact absurd hρ (hsing.not_ref2 (hsing.snd_none (hne m rfl)) o)
  | lit v =>
    refine ⟨f, _, writeB_runs (.slot BP) _ n bp f h hf (by rw [Data.encodeBytes_length]; omega)
      (by rw [Data.encodeBytes_length]; omega), rfl, fun a ha =>
      wr_out (by simp; omega) (by omega) (by omega), Nat.le_refl _, ?_⟩
    have e := rd_wr h (bp + n) (Data.encodeBytes v) (by simp; omega)
    rw [Data.encodeBytes_length] at e
    show Data.reprBytes v (rd _ (bp + n) t.size)
    rw [e]; exact Data.reprBytes_encode v

theorem rd_head {h : Heap} {A S : Nat} {b : UInt8} (hS : 1 ≤ S) (e : slice (rd h A S) 0 1 = [b]) :
    h (UInt64.ofNat A) = b := by
  cases S with
  | zero => omega
  | succ S => simpa [rd, slice] using e

/-- Copying a payload from inside the scrutinee's region `[ls, ls + S)`, where `ls + S ≤ n'`, to a
fresh variable at `n'`. -/
theorem payload_copy {ls po sz S n' bp : Nat} {f : Frame} {h : Heap} (hf : f BP = UInt64.ofNat bp)
    (hpo : po + sz ≤ S) (hls : ls + S ≤ n') (hb : bp + n' + sz ≤ UInt64.size)
    (hbL : bp + n' + sz ≤ L) :
    ∃ f', f' BP = f BP ∧ Runs κ ω L (copyM (ls + po) n' sz) f h f'
      (wr h (bp + n') (rd h (bp + ls + po) sz)) := by
  obtain ⟨f', hf', hr⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot BP) (by decide)
    (by decide) sz (ls + po) n' bp bp f h hf hf (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
  exact ⟨f', hf' BP (by decide), by rw [← Nat.add_assoc] at hr; exact hr⟩

/-- Placing the scrutinee's bytes, then loading its tag byte into `RT`, then running `rest`. -/
theorem scrut_load {Γ : List Ty} {t : Ty} (s : Atom Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} {w : World}
    (hl : Lay bp n Γ ρ S W) (hbn : bp + n + t.size ≤ UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hnh : ∀ m, s = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + n + t.size ≤ L) (hne : ∀ m, s = .var m → (S.getD m.idx default).ext = none)
    (hns : ∀ m, s = .var m → (ρ.getD m.idx default).isSlot = false)
    (hw : w.halted = false) (ht : 1 ≤ t.size) :
    ∃ f₁ h₁, f₁ BP = UInt64.ofNat bp ∧ (∀ x, FR ≤ x → f₁ x = f x) ∧
      f₁ RT = (h₁ (UInt64.ofNat (bp + scrutLoc s ρ n))).toUInt64 ∧
      (∀ a, a < bp + n → h₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) ∧ scrutLoc s ρ n ≤ n ∧
      Data.reprBytes (s.denote env) (rd h₁ (bp + scrutLoc s ρ n) t.size) ∧
      ∀ {α : Type} {rest : Stmt} {k : List Kont} {c : Nat} {Q : α → Frame → Heap → Prop}
        {prot pf : Nat → Prop} {r : Out α}, (∀ x, prot x → x < bp + n) →
        MSim κ ω L ⟨rest, k, f₁, h₁, w, c⟩ k Q prot r pf →
        MSim κ ω L ⟨.seq (scrutPre s ρ n) (.seq (.load .w8 RT (.slot BP)
          (UInt64.ofNat (scrutLoc s ρ n))) rest), k, f, h, w, c⟩ k Q prot r pf := by
  obtain ⟨f₀, h₁, hr₁, hfb₀, hm₁, hls, hrep⟩ := scrut_spec (κ := κ) (ω := ω) (L := L) s hl hbn hf
    henv hfe hnh hnL hne hns
  have hf₀ : f₀ BP = UInt64.ofNat bp := hfb₀.trans hf
  refine ⟨_, h₁, by rw [Frame.set_ne _ _ (by decide)]; exact hf₀,
    fun x hx => (Frame.set_keep f₀ _ (by decide) x hx).trans (hr₁.keep x hx),
    by simp only [Frame.set, ↓reduceIte, eval_slot, hf₀, ofNat_add_ofNat, Heap.load], hm₁, hls, hrep,
    fun hp hm => MSim.runs hw hr₁ hfb₀ (fun x hx => hm₁ x (hp x hx))
      (MSim.runs hw (Runs.load .w8 RT (.slot BP) _ f₀ h₁ (acc_off (b := 1) (by omega) (by omega) hf₀))
        (by rw [Frame.set_ne _ _ (by decide)]) (fun _ _ => rfl) hm)⟩

/-- An arm binds a fresh variable at `n'` holding the payload and runs the arm's code under one
more binder, in the context given by the enclosing term's hypotheses `H`. -/
theorem arm_step {Γ : List Ty} {p t : Ty} (e : Exp (p :: Γ) t) (ih : MSoundAt κ ω e)
    {e₀ : Exp Γ t} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n n' d bp : Nat}
    {env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w)
    {k : List Kont} {f : Frame} {h : Heap} {c : Nat} (v : p.carrier)
    (hC : e.Conf tm.up = true) (hR : e.Restr (true :: W)) (hL : e.Lawful)
    (hF : e.Frozen) (hH : HoleAv e (⟨bp + n', none, none, none⟩ :: S)) (hnn : n ≤ n')
    (hb : bp + n' + p.size + e.memNeed ≤ UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hv : Data.reprBytes v (rd h (bp + n') p.size))
    (hs : e.safe ω (.cons v env) w) (hbL : bp + n' + p.size + e.memNeed ≤ L)
    (hV : VS S fun i => e.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → e.noAddr (i + 1) = true) :
    MSim κ ω L ⟨lowerM e tm.up (.own n' :: ρ) (n' + p.size) d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.up.hb (.cons v env) w) (SProt ρ W) :=
  .unpush hnn (ih.app (H.push v hnn hC hR hL hF hH hb hbL hf henv hfe hv hs hV H.run hna) k c)

/-- A continuation under a slot-resident binder runs after code `X`, which puts the binder's value
in the slots from `FR + slotsIn ρ` and keeps the slots below. -/
theorem slot_step {Γ : List Ty} {p t : Ty} (e : Exp (p :: Γ) t) (ih : MSoundAt κ ω e)
    {e₀ : Exp Γ t} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n n' d bp : Nat}
    {env₀ env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}
    (H : MHyp ω e₀ tm L W ρ S n d bp env₀ f₀ h₀ w)
    {k : List Kont} {X : Stmt} {f f' : Frame} {h : Heap} {c : Nat} (v : p.carrier)
    (hX : Reaches κ ω L X f h f' h) (hlo : ∀ y, y < FR + slotsIn ρ → f' y = f y)
    (hsb : e.slotBind = true) (hword : WordsRel p v f' (FR + slotsIn ρ))
    (hC : e.Conf tm.up = true) (hR : e.Restr (true :: W)) (hL : e.Lawful)
    (hF : e.Frozen) (hH : HoleAv e (⟨bp + n', none, none, none⟩ :: S)) (hnn : n ≤ n')
    (hb : bp + n' + p.size + e.memNeed ≤ UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hs : e.safe ω (.cons v env) w) (hbL : bp + n' + p.size + e.memNeed ≤ L)
    (hV : VS S fun i => e.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → e.noAddr (i + 1) = true) :
    MSim κ ω L ⟨.seq X (lowerM e tm.up (.slot n' (FR + slotsIn ρ) p.slotN :: ρ) (n' + p.size) d),
        k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.up.hb (.cons v env) w) (SProt ρ W) := by
  simp only [Exp.slotBind, Bool.and_eq_true] at hsb
  have hfb : f' BP = f BP := hlo BP (by simp only [FR, BP]; omega)
  exact MSim.reach H.run hX hfb (fun _ _ => rfl) (fun x _ hp => hlo x (SProt.lt H.sl.ok hp))
    (.unpush hnn (ih.app (H.pushSlot v hnn hC hR hL hF hH hb hbL (hfb.trans hf) henv
      (hfe.below H.sl.ok fun x _ hx => hlo x hx) hsb.1.1 hword hs hV H.run hsb.1.2 hna) k c))

/-- An arm whose variable is a copy, at `n + sz`, of the payload at `ls + po`, which lies inside
the scrutinee's `sz` bytes at `ls ≤ n`. -/
theorem copy_arm {Γ : List Ty} {p t : Ty} (e : Exp (p :: Γ) t) (ih : MSoundAt κ ω e)
    {e₀ : Exp Γ t} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat}
    {env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w)
    {k : List Kont} {f : Frame} {h : Heap} {c ls po sz : Nat} (v : p.carrier)
    (hpo : po + p.size ≤ sz) (hls : ls ≤ n) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hv : Data.reprBytes v (rd h (bp + ls + po) p.size))
    (hC : e.Conf tm.up = true) (hR : e.Restr (true :: W)) (hL : e.Lawful)
    (hF : e.Frozen) (hH : HoleAv e (⟨bp + (n + sz), none, none, none⟩ :: S))
    (hb : bp + (n + sz) + p.size + e.memNeed ≤ UInt64.size)
    (hs : e.safe ω (.cons v env) w) (hbL : bp + (n + sz) + p.size + e.memNeed ≤ L)
    (hV : VS S fun i => e.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → e.noAddr (i + 1) = true) :
    MSim κ ω L ⟨.seq (copyM (ls + po) (n + sz) p.size)
        (lowerM e tm.up (.own (n + sz) :: ρ) (n + sz + p.size) d), k, f, h, w, c⟩ k
      (TQ tm bp d ρ S t) (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.up.hb (.cons v env) w) (SProt ρ W) := by
  obtain ⟨f₂, hf₂, hr₂⟩ := payload_copy (κ := κ) (ω := ω) (L := L) (ls := ls) (po := po)
    (sz := p.size) (S := sz) (n' := n + sz) (h := h) hf hpo (by omega) (by omega) (by omega)
  have hh₂ := rd_wr h (bp + (n + sz)) (rd h (bp + ls + po) p.size) (by simp; omega)
  rw [rd_length] at hh₂
  refine MSim.runs H.run hr₂ hf₂ (fun x hx => wr_out (by simp; omega) (by unfold Prot at hx; omega)
    (by unfold Prot at hx; simp; omega)) ?_
  exact arm_step e ih H v hC hR hL hF hH (by omega) hb (hf₂.trans hf)
    (henv.above H.lay fun a ha => wr_out (by simp; omega) (by omega) (by simp; omega))
    (hfe.keep hr₂.keep) (by rw [hh₂]; exact hv) hs hbL hV hna

/-- An arm whose variable is the payload at `ls + po`, inside the scrutinee's `sz` bytes at
`ls ≤ n`. The payload is loaded into the binder's frame slots when the binder is slot-resident, and
otherwise copied to `n + sz`. -/
theorem arm_in {Γ : List Ty} {p t : Ty} (e : Exp (p :: Γ) t) (ih : MSoundAt κ ω e)
    {e₀ : Exp Γ t} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat}
    {env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w)
    {k : List Kont} {f : Frame} {h : Heap} {c ls po sz : Nat} (v : p.carrier)
    (hpo : po + p.size ≤ sz) (hls : ls ≤ n) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hv : Data.reprBytes v (rd h (bp + ls + po) p.size))
    (hC : e.Conf tm.up = true) (hR : e.Restr (true :: W)) (hL : e.Lawful)
    (hF : e.Frozen) (hH : HoleAv e (⟨bp + (n + sz), none, none, none⟩ :: S))
    (hb : bp + (n + sz) + p.size + e.memNeed ≤ UInt64.size)
    (hs : e.safe ω (.cons v env) w) (hbL : bp + (n + sz) + p.size + e.memNeed ≤ L)
    (hV : VS S fun i => e.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → e.noAddr (i + 1) = true) :
    MSim κ ω L ⟨memArm e.slotBind p (FR + slotsIn ρ) BP (ls + po) (n + sz)
        fun l => lowerM e tm.up (l :: ρ) (n + sz + p.size) d, k, f, h, w, c⟩ k
      (TQ tm bp d ρ S t) (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.up.hb (.cons v env) w) (SProt ρ W) := by
  unfold memArm; split
  · rename_i hsb
    obtain ⟨f', hld, -, hlo, hword⟩ := load_words (κ := κ) (ω := ω) (L := L)
      (K := FR + slotsIn ρ) (o := ls + po) (Ty.slotTy_of_bind hsb) hf (by decide)
      (Nat.le_add_right _ _) (by rw [← Nat.add_assoc]; exact hv) (by omega) (by omega)
    exact slot_step e ih H v hld hlo hsb hword hC hR hL hF hH (by omega) hb hf henv hfe hs hbL hV hna
  · exact copy_arm e ih H v hpo hls hf henv hfe hv hC hR hL hF hH hb hs hbL hV hna

/-- An arm whose payload is in the frame slots from `src`, as for a slot-resident scrutinee. The
payload is moved into the binder's slots when the binder is slot-resident, and otherwise stored to
its memory at `n + sz`, where `sz` is at least the payload's size. -/
theorem arm_slot {Γ : List Ty} {p t : Ty} (e : Exp (p :: Γ) t) (ih : MSoundAt κ ω e)
    {e₀ : Exp Γ t} {tm : Tl} {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat}
    {env : Env Γ} {f₀ : Frame} {h₀ : Heap} {w : World}
    (H : MHyp ω e₀ tm L W ρ S n d bp env f₀ h₀ w)
    {k : List Kont} {f : Frame} {h : Heap} {c src cnt sz : Nat} (v : p.carrier)
    (hpay : p.size = 0 ∨ p.slotTy = true)
    (hsrc : src + p.slotN ≤ FR + slotsIn ρ) (hmin : min p.slotN cnt = p.slotN)
    (hsz : p.size ≤ sz)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hv0 : p.size = 0 → Data.reprBytes v []) (hw : p.slotTy = true → WordsRel p v f src)
    (hC : e.Conf tm.up = true) (hR : e.Restr (true :: W)) (hL : e.Lawful)
    (hF : e.Frozen) (hH : HoleAv e (⟨bp + (n + sz), none, none, none⟩ :: S))
    (hb : bp + (n + sz) + p.size + e.memNeed ≤ UInt64.size)
    (hs : e.safe ω (.cons v env) w) (hbL : bp + (n + sz) + p.size + e.memNeed ≤ L)
    (hV : VS S fun i => e.VSafe (i + 1) tm.up)
    (hna : ∀ i, e₀.noAddr i = true → e.noAddr (i + 1) = true) :
    MSim κ ω L ⟨slotArm e.slotBind p (FR + slotsIn ρ) src cnt (n + sz)
        fun l => lowerM e tm.up (l :: ρ) (n + sz + p.size) d, k, f, h, w, c⟩ k
      (TQ tm bp d ρ S t) (Prot bp n d (tm.dsz t) Γ S W) (e.exec ω κ tm.up.hb (.cons v env) w) (SProt ρ W) := by
  have hdn := H.dn
  unfold slotArm; rw [hmin]; split
  · rename_i hsb
    obtain ⟨f', hr, hout, hval⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) p.slotN
      (x := FR + slotsIn ρ) (k := src) (f := f) (h := h) (Or.inr hsrc)
    obtain ⟨B, hB, hwB⟩ := hw (Ty.slotTy_of_bind hsb)
    exact slot_step e ih H v hr (fun y hy => hout y (Or.inl hy)) hsb
      ⟨B, hB, wordsAt_iff.2 fun j hj => by rw [hval j hj]; exact wordsAt_iff.1 hwB j hj⟩ hC hR hL hF
      hH (by omega) hb hf henv hfe hs hbL hV hna
  · -- the payload's bytes stored to the binder's memory
    obtain ⟨B, hBl, hBr, hrun⟩ : ∃ B : List UInt8, B.length = p.size ∧ Data.reprBytes v B ∧
        Runs κ ω L (stSlots (scalarWidth p.size) (.slot BP) (n + sz) src p.slotN) f h f
          (wr h (bp + (n + sz)) B) := by
      rcases hpay with h0 | hts
      · have hn0 : p.slotN = 0 := by unfold Ty.slotN; omega
        refine ⟨[], by simp [h0], hv0 h0, ?_⟩
        rw [hn0]; exact Runs.skip f h
      · exact stSlots_words (κ := κ) (ω := ω) (L := L) (o := n + sz) hts hf (hw hts)
          (by omega) (by omega)
    have hh₂ := rd_wr h (bp + (n + sz)) B (by omega)
    rw [hBl] at hh₂
    refine MSim.runs H.run hrun rfl (fun x hx => wr_out (by omega) (by unfold Prot at hx; omega)
      (by unfold Prot at hx; omega)) ?_
    exact arm_step e ih H v hC hR hL hF hH (by omega) hb hf
      (henv.above H.lay fun a ha => wr_out (by omega) (by omega) (by omega))
      hfe (by rw [hh₂]; exact hBr) hs hbL hV hna

/-- The payload of a slot-resident sum with bytes `B` in the slots from `K` is in the words after
the tag's, at `po = 8`, or it is empty. -/
theorem slot_payload {t p : Ty} {po : Nat} {v : p.carrier} {B : List UInt8} {f : Frame} {K : Nat}
    (hres : t.slotTy = true) (hBl : B.length = t.size) (hwB : WordsAt f K B t.slotN)
    (hpay : p.size = 0 ∨ (p.slotTy = true ∧ p.size % 8 = 0))
    (hle : po + p.size ≤ t.size) (h8 : p.size = 0 ∨ po = 8)
    (hrep : Data.reprBytes v (slice B po p.size)) :
    (p.size = 0 → Data.reprBytes v []) ∧ (p.slotTy = true → WordsRel p v f (K + 1)) ∧
      p.slotN + 1 ≤ t.slotN := by
  refine ⟨fun h0 => by rwa [h0, show slice B po 0 = [] by simp [slice]] at hrep,
    fun hts => ?_, ?_⟩
  · have hp8 : p.size % 8 = 0 := by
      rcases hpay with h0 | h1
      · have := Ty.slotN_pos hts; unfold Ty.slotN at this; omega
      · exact h1.2
    have hp0 : p.size ≠ 0 := by have := Ty.slotN_pos hts; unfold Ty.slotN at this; omega
    have hr8 := h8.resolve_left hp0
    rcases Ty.slotTy_cases hres with ⟨h1, _, _⟩ | ⟨hsz8, _, _⟩
    · omega
    · refine ⟨_, hrep, ?_⟩
      rw [← wordsBytes_eq (by rw [hBl]; exact hsz8) hwB, hr8, wordPay_size hp8,
        show 8 = 8 * 1 by rfl, wordsBytes_slice _ _ _ _ _ (by have := wordPay_size hp8; omega)]
      exact wordsAt_wordsBytes _ _ _
  · rcases hpay with h0 | ⟨hts, hp8⟩
    · have : p.slotN = 0 := by unfold Ty.slotN; omega
      rw [this]; exact Ty.slotN_pos hres
    · have hp0 : p.size ≠ 0 := by have := Ty.slotN_pos hts; unfold Ty.slotN at this; omega
      have hr8 := h8.resolve_left hp0
      rcases Ty.slotTy_cases hres with ⟨h1, _, _⟩ | ⟨hsz8, _, _⟩
      · omega
      · have := wordPay_size hp8; omega

/-- The tag of a slot-resident sum held by variable `m` in the slots from `K` is the low byte of
its first word, which is the first byte of its bytes `B`. -/
theorem slot_tag {Γ : List Ty} {t : Ty} {env : Env Γ} {ρ : List Loc} {f : Frame} {K : Nat}
    {m : Mem t Γ} (hfe : FEnvRel f env ρ) (hk : (ρ.getD m.idx default).slot? = some K) :
    ∃ B : List UInt8, Data.reprBytes (env.get m) B ∧ WordsAt f K B t.slotN ∧
      (ρ.getD m.idx default).nw = t.slotN ∧ t.slotTy = true ∧
      f K &&& 0xFF = (B.headD 0).toUInt64 := by
  obtain ⟨hts, hnw, B, hB, hwB⟩ := hfe.get m hk
  have hBl : B.length = t.size := Data.reprBytes_length hB
  have hn1 := Ty.slotN_pos hts
  obtain ⟨b0, rest, rfl⟩ : ∃ b0 rest, B = b0 :: rest := by
    cases B with
    | nil => have := Ty.slotN_pos hts; unfold Ty.slotN at this; simp at hBl; omega
    | cons b0 rest => exact ⟨b0, rest, rfl⟩
  refine ⟨_, hB, hwB, hnw, hts, ?_⟩
  obtain ⟨m', hm'⟩ : ∃ m', t.slotN = m' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn1).symm⟩
  have hK0 : f K = decodeLE (b0 :: rest.take 7) := by
    have := hwB; rw [hm'] at this; rw [this.1]; rfl
  rw [hK0]; exact decodeLE_low b0 _ (by simp; omega)

/-- A `match` on a slot-resident scrutinee in the slots from `K` reads the tag from the low byte
of its first word and the payload from its next words. -/
theorem match_slot {Γ : List Ty} {ε α t : Ty} (s : Atom Γ (.result ε α)) (eE : Exp (ε :: Γ) t)
    (eO : Exp (α :: Γ) t) (ihE : MSoundAt κ ω eE) (ihO : MSoundAt κ ω eO) {tm : Tl} {L : Nat}
    {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {kk : List Kont}
    {f : Frame} {h : Heap} {w : World} {c K : Nat}
    (H : MHyp ω (.match_ s eE eO) tm L W ρ S n d bp env f h w) (hso : s.slotOf ρ = some K) :
    MSim κ ω L ⟨lowerM (.match_ s eE eO) tm ρ n d, kk, f, h, w, c⟩ kk (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) ((Exp.match_ s eE eO).exec ω κ tm.hb env w) (SProt ρ W) := by
  obtain ⟨m, rfl, hk⟩ : ∃ m, s = .var m ∧ (ρ.getD m.idx default).slot? = some K := by
    cases s with
    | var m => exact ⟨m, rfl, hso⟩
    | lit v => simp [Atom.slotOf] at hso
  simp only [lowerM, hso]
  have hb := H.size; have hbL := H.room; have hs := H.safe; have hC := conf_match H.conf
  simp only [Exp.memNeed] at hb hbL; simp only [Exp.safe] at hs
  have hmE := Nat.le_max_left (ε.size + eE.memNeed) (α.size + eO.memNeed)
  have hmO := Nat.le_max_right (ε.size + eE.memNeed) (α.size + eO.memNeed)
  have hS1 := rpo_ok ε α; have hS2 := rpo_err ε α
  have hsum : Ty.slotSum ε α = true := by
    have := (H.sl.na m.idx (Loc.isSlot_iff.2 ⟨K, hk⟩)).1
    simp only [Exp.noAddr, Atom.isVar, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_self_eq_true] at this
    simpa using this.1.1
  obtain ⟨hres, hpo, hpE, hpA⟩ := slotSum_facts hsum
  obtain ⟨B, hB, hwB, hnw, -, hRT⟩ := slot_tag H.sl.rel hk
  have hran := H.sl.ok.range m.idx K hk
  rw [hnw] at hran
  have hFRK := hran.1
  have hBl : B.length = (Ty.result ε α).size := Data.reprBytes_length hB
  have hinv := result_repr_inv _ _ hB
  let f₁ := f.set RT (f K &&& 0xFF)
  have hr₁ : Runs κ ω L (.bin .band RT (.slot K) (.imm 0xFF)) f h f₁ h := Runs.bin _ _ _ _ _ _
  have hf₁ : f₁ BP = UInt64.ofNat bp := by
    simp only [f₁]; rw [Frame.set_ne _ _ (by decide)]; exact H.bpOk
  have hfe₁ := H.sl.rel.keep hr₁.keep
  have hRT₁ : f₁ RT = (B.headD 0).toUInt64 := by simp only [f₁, Frame.set_same]; exact hRT
  have hw₁ : ∀ (p : Ty) (v : p.carrier), (p.slotTy = true → WordsRel p v f (K + 1)) →
      p.slotTy = true → WordsRel p v f₁ (K + 1) := fun p v hw hts =>
    (hw hts).congr fun x hx _ => by
      simp only [f₁]; rw [Frame.set_ne _ _ (by simp only [FR, RT] at hFRK ⊢; omega)]
  have hhd : ∀ b, slice B 0 1 = [b] → B.headD 0 = b := fun b hb => by
    cases B with
    | nil => simp [slice] at hb
    | cons b0 _ => simpa [slice] using hb
  cases hsv : (env.get m : Except ε.carrier α.carrier) with
  | error e =>
    obtain ⟨ht, hpe⟩ := hinv.2 e hsv
    obtain ⟨hv0, hw, hn⟩ := slot_payload hres hBl hwB hpE hS2
      (hpo.symm.imp And.left id) hpe
    have hA := arm_slot (L := L) (k := kk) (c := c + (Tick.match_ (width (.result ε α))).cost κ) (sz :=
      (Ty.result ε α).size) (src := K + 1) (cnt := (Atom.var m).slotNw ρ - 1) eE ihE H e
      (hpE.imp_right And.left) (by omega)
      (by simp only [Atom.slotNw, hnw]; omega) (by omega) hf₁ H.envRel hfe₁ hv0 (hw₁ _ _ hw) hC.1
      H.restr.1 H.lawful.1 H.frozen.1 (H.hole.push _ rfl fun _ _ h => h.2.1) (by omega)
      (hs.1 e (by simpa [Atom.denote] using hsv)) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
    exact (MSim.tick H.run (MSim.runs H.run hr₁ (by rw [hf₁, H.bpOk]) (fun _ _ => rfl)
      (MSim.ite_e H.run (by rw [eval_slot, hRT₁, hhd 0 ht]; rfl) hA))).of_eq
      (by simp [Exp.exec, Atom.denote, hsv, Tl.hb_up]) (by simp [Exp.exec, Atom.denote, hsv, Tl.hb_up])
      (by simp [Exp.exec, Atom.denote, hsv, Tick.cost, Tl.hb_up])
  | ok v =>
    obtain ⟨ht, hpv⟩ := hinv.1 v hsv
    obtain ⟨hv0, hw, hn⟩ := slot_payload hres hBl hwB hpA hS1
      (hpo.symm.imp And.right id) hpv
    have hA := arm_slot (L := L) (k := kk) (c := c + (Tick.match_ (width (.result ε α))).cost κ) (sz :=
      (Ty.result ε α).size) (src := K + 1) (cnt := (Atom.var m).slotNw ρ - 1) eO ihO H v
      (hpA.imp_right And.left) (by omega)
      (by simp only [Atom.slotNw, hnw]; omega) (by omega) hf₁ H.envRel hfe₁ hv0 (hw₁ _ _ hw) hC.2
      H.restr.2 H.lawful.2 H.frozen.2 (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega)
      (hs.2 v (by simpa [Atom.denote] using hsv)) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)
    exact (MSim.tick H.run (MSim.runs H.run hr₁ (by rw [hf₁, H.bpOk]) (fun _ _ => rfl)
      (MSim.ite_t H.run (by rw [eval_slot, hRT₁, hhd 1 ht]; decide) hA))).of_eq
      (by simp [Exp.exec, Atom.denote, hsv, Tl.hb_up]) (by simp [Exp.exec, Atom.denote, hsv, Tl.hb_up])
      (by simp [Exp.exec, Atom.denote, hsv, Tick.cost, Tl.hb_up])

/-- A `match` on a `Result` tests the tag byte, copies the payload and runs the arm. A
slot-resident scrutinee is tested and taken apart in its frame slots. -/
theorem msound_match {Γ : List Ty} {ε α t : Ty} (s : Atom Γ (.result ε α)) (eE : Exp (ε :: Γ) t)
    (eO : Exp (α :: Γ) t) (ihE : MSoundAt κ ω eE) (ihO : MSoundAt κ ω eO) :
    MSoundAt κ ω (.match_ s eE eO) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  cases hso : s.slotOf ρ with
  | some K => exact match_slot s eE eO ihE ihO H hso
  | none =>
  simp only [lowerM, hso]
  have hb := H.size; have hbL := H.room; have hs := H.safe; have hC := conf_match H.conf
  simp only [Exp.memNeed] at hb hbL; simp only [Exp.safe] at hs
  have hmE := Nat.le_max_left (ε.size + eE.memNeed) (α.size + eO.memNeed)
  have hmO := Nat.le_max_right (ε.size + eE.memNeed) (α.size + eO.memNeed)
  have hS1 := rpo_ok ε α; have hS2 := rpo_err ε α
  have hS0 : 1 ≤ (Ty.result ε α).size := by have := rpo_ge ε α; omega
  obtain ⟨f₁, h₁, hf₁, hfk₁, hRT, hm₁, hls, hrep, hpre⟩ := scrut_load (κ := κ) (ω := ω) (L := L) s
    H.lay (by omega) H.bpOk H.envRel H.sl.rel (s.noHole fun i H' h' => (H.hole i H' h').1) (by omega)
    (H.vs.atom s fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; simpa using h.1.1)
    (fun m e => by subst e; unfold Loc.isSlot; simp only [Atom.slotOf] at hso; rw [hso]; rfl)
    H.run hS0
  have hfe₁ := H.sl.rel.keep hfk₁
  have hinv := result_repr_inv _ _ hrep
  have henv₁ := H.envRel.above H.lay hm₁
  have hp : ∀ x, Prot bp n d (tm.dsz t) Γ S W x → x < bp + n := fun x hx => hx.1
  cases hsv : (s.denote env : Except ε.carrier α.carrier) with
  | error e =>
    obtain ⟨ht, hpe⟩ := hinv.2 e hsv
    have hA := arm_in (L := L) (k := k) (c := c + (Tick.match_ (width (.result ε α))).cost κ) eE ihE H e hS2
      hls hf₁ henv₁ hfe₁ (by rw [rd_slice _ _ _ _ _ (by omega)]; exact hpe) hC.1 H.restr.1 H.lawful.1
      H.frozen.1 (H.hole.push _ rfl fun _ _ h => h.2.1) (by omega) (hs.1 e hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
    exact (MSim.tick H.run (hpre hp (MSim.ite_e H.run
      (by rw [eval_slot, hRT, rd_head hS0 ht]; rfl) hA))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, Tl.hb_up])
  | ok v =>
    obtain ⟨ht, hpv⟩ := hinv.1 v hsv
    have hA := arm_in (L := L) (k := k) (c := c + (Tick.match_ (width (.result ε α))).cost κ) eO ihO H v hS1
      hls hf₁ henv₁ hfe₁ (by rw [rd_slice _ _ _ _ _ (by omega)]; exact hpv) hC.2 H.restr.2 H.lawful.2
      H.frozen.2 (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega) (hs.2 v hsv) (by omega)
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)
    exact (MSim.tick H.run (hpre hp (MSim.ite_t H.run
      (by rw [eval_slot, hRT, rd_head hS0 ht]; decide) hA))).of_eq
      (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tl.hb_up]) (by simp [Exp.exec, hsv, Tick.cost, Tl.hb_up])

end

end Millipede.Flat
