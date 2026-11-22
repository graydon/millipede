import Millipede.Compile.LowerSim

/-!
# Loops of large constructors

A constructor of at least `fillMin` bytes is written by a word loop (`wordLoop`) rather than by
one store per word: a fill with a literal element, such as `Vector.replicate n 0`, by a loop of
8-byte stores (`fillCode?`), and a constructor whose argument is a large variable in memory by a
loop of 8-byte loads and stores (`copyCode?`). Each iteration charges the tick `words w` for the
words it writes, and the constructor's own tick charges the rest, so the clock still advances by
exactly the constructor's cost and every iteration pays for its instructions in the budget check.

`wordWhile_reach` runs a word loop given what its body does to the heap in one iteration;
`fillLoop_reach` and `copyLoop_reach` are its two instances, and `tickLoop_msim` turns the
constructor's tick, the loop and the code after it into the memory simulation. What the lowering
checked is `fillCode?_spec` (LowerFacts.lean) and `bigVar?_spec` (LowerCalls.lean).
-/

namespace Millipede.Flat

/-! ## Word loops -/

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- A word loop with `m` iterations left, from byte offset `8 j`, whose body `B` takes the heap
from `H j` to `H (j + 1)` when `RB` holds `bp + 8 j`, changing only `RT`: it reaches `H k`, charges
`m` ticks, and changes only `RA`, `RB`, `RX` and `RT` in the frame. -/
theorem wordWhile_reach (k w bp : Nat) (B : Stmt) (H : Nat → Heap) (hk8 : 8 * k < UInt64.size)
    (hB : ∀ j, j < k → ∀ f : Frame, f BP = UInt64.ofNat bp → f RB = UInt64.ofNat (bp + 8 * j) →
      ∃ f', (∀ x, x ≠ RT → f' x = f x) ∧ Reaches κ ω L B f (H j) f' (H (j + 1)))
    (K : List Kont) (wo : World) (hw : wo.halted = false) :
    ∀ (m j : Nat) (f : Frame) (c : Nat), j + m = k → f BP = UInt64.ofNat bp →
      f RA = UInt64.ofNat (8 * j) →
      ∃ f', (∀ x, x ≠ RA → x ≠ RB → x ≠ RX → x ≠ RT → f' x = f x) ∧
        ReachL κ ω L ⟨wordWhile k w B, K, f, H j, wo, c⟩
          ⟨.skip, K, f', H k, wo, c + m * (Tick.words w).cost κ⟩
  | 0, j, f, c, hj, _, hA => by
    refine ⟨f.set RX 0, fun x _ _ hx' _ => Frame.set_ne _ _ hx', ?_⟩
    have hlt : ¬ (UInt64.ofNat (8 * j) < UInt64.ofNat (8 * k)) := by
      rw [ofNat_lt_ofNat (by omega) (by omega)]; omega
    have e : BinOp.eval .ult (Operand.eval f (.slot RA)) (Operand.eval f (.imm (UInt64.ofNat (8 * k))))
        = 0 := by simp only [BinOp.eval, eval_slot, eval_imm, hA, hlt, ↓reduceIte]
    rw [show j = k by omega, Nat.zero_mul, Nat.add_zero]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1, e]
    refine ReachL.step' hw ?_
    simp only [exec1, Frame.set_same, eval_slot, ↓reduceIte]
    exact ReachL.refl _
  | m + 1, j, f, c, hj, hBP, hA => by
    have hlt : UInt64.ofNat (8 * j) < UInt64.ofNat (8 * k) := by
      rw [ofNat_lt_ofNat (by omega) (by omega)]; omega
    let f₁ := f.set RX 1
    let f₂ := f₁.set RB (UInt64.ofNat (bp + 8 * j))
    have hBP₁ : f₁ BP = UInt64.ofNat bp := by
      simp only [f₁]; rw [Frame.set_ne _ _ (by decide)]; exact hBP
    have hRA₁ : f₁ RA = UInt64.ofNat (8 * j) := by
      simp only [f₁]; rw [Frame.set_ne _ _ (by decide)]; exact hA
    obtain ⟨f₂', hf₂', hr₂⟩ := hB j (by omega) f₂
      (by simp only [f₂]; rw [Frame.set_ne _ _ (by decide)]; exact hBP₁) (Frame.set_same _ _ _)
    have hRA₂ : f₂' RA = UInt64.ofNat (8 * j) := by
      rw [hf₂' RA (by decide)]; simp only [f₂]; rw [Frame.set_ne _ _ (by decide)]; exact hRA₁
    let f₃ := f₂'.set RA (UInt64.ofNat (8 * (j + 1)))
    obtain ⟨f', hf', hr⟩ := wordWhile_reach k w bp B H hk8 hB K wo hw m (j + 1) f₃
      (c + (Tick.words w).cost κ) (by omega)
      (by simp only [f₃]; rw [Frame.set_ne _ _ (by decide), hf₂' BP (by decide)]
          simp only [f₂]; rw [Frame.set_ne _ _ (by decide)]; exact hBP₁)
      (Frame.set_same _ _ _)
    refine ⟨f', fun x h1 h2 h3 h4 => ?_, ?_⟩
    · rw [hf' x h1 h2 h3 h4]; simp only [f₃]
      rw [Frame.set_ne _ _ h1, hf₂' x h4]; simp only [f₂, f₁]
      rw [Frame.set_ne _ _ h2, Frame.set_ne _ _ h3]
    have e₁ : BinOp.eval .ult (Operand.eval f (.slot RA)) (Operand.eval f (.imm (UInt64.ofNat (8 * k))))
        = 1 := by simp only [BinOp.eval, eval_slot, eval_imm, hA, hlt, ↓reduceIte]
    have e₂ : BinOp.eval .add (Operand.eval f₁ (.slot BP)) (Operand.eval f₁ (.slot RA)) =
        UInt64.ofNat (bp + 8 * j) := by
      simp only [BinOp.eval, eval_slot, hRA₁, hBP₁, ofNat_add_ofNat]
    have e₃ : BinOp.eval .add (Operand.eval f₂' (.slot RA)) (Operand.eval f₂' (.imm 8)) =
        UInt64.ofNat (8 * (j + 1)) := by
      simp only [BinOp.eval, eval_slot, eval_imm]
      rw [hRA₂, show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_add_ofNat, Nat.mul_succ]
    rw [show c + (m + 1) * (Tick.words w).cost κ = c + (Tick.words w).cost κ +
      m * (Tick.words w).cost κ by rw [Nat.succ_mul]; omega]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1, e₁]
    refine ReachL.step' hw ?_
    simp only [exec1, Frame.set_same, eval_slot]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1]
    rw [show f.set RX 1 = f₁ from rfl, e₂]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine (hr₂ _ wo _ hw).trans ?_
    refine ReachL.step' hw ?_
    simp only [exec1]
    refine ReachL.step' hw ?_
    simp only [exec1, e₃]
    refine ReachL.step' hw ?_
    simp only [exec1]
    exact hr

/-- The whole word loop, followed by `b`. -/
theorem wordLoop_reach (k w bp : Nat) (B : Stmt) (H : Nat → Heap) (hk8 : 8 * k < UInt64.size)
    (hB : ∀ j, j < k → ∀ f : Frame, f BP = UInt64.ofNat bp → f RB = UInt64.ofNat (bp + 8 * j) →
      ∃ f', (∀ x, x ≠ RT → f' x = f x) ∧ Reaches κ ω L B f (H j) f' (H (j + 1)))
    (b : Stmt) (K : List Kont) (wo : World) (hw : wo.halted = false) (f : Frame) (c : Nat)
    (hBP : f BP = UInt64.ofNat bp) :
    ∃ f', (∀ x, x ≠ RA → x ≠ RB → x ≠ RX → x ≠ RT → f' x = f x) ∧
      ReachL κ ω L ⟨.seq (wordLoop k w B) b, K, f, H 0, wo, c⟩
        ⟨b, K, f', H k, wo, c + k * (Tick.words w).cost κ⟩ := by
  obtain ⟨f', hf', hr⟩ := wordWhile_reach (κ := κ) (ω := ω) (L := L) k w bp B H hk8 hB
    (.seq b :: K) wo hw k 0 (f.set RA 0) c (by omega)
    (by rw [Frame.set_ne _ _ (by decide)]; exact hBP) (by simp)
  refine ⟨f', fun x h1 h2 h3 h4 => by rw [hf' x h1 h2 h3 h4, Frame.set_ne _ _ h1], ?_⟩
  refine ReachL.step' hw ?_
  simp only [exec1]
  refine ReachL.step' hw ?_
  simp only [exec1]
  refine ReachL.step' hw ?_
  simp only [exec1]
  refine ReachL.step' hw ?_
  simp only [exec1]
  exact hr.trans (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _))

/-- The fill loop: it writes the word `P` `k` times from `bp + d`. -/
theorem fillLoop_reach (d k : Nat) (P : UInt64) (w bp : Nat) (hk8 : 8 * k < UInt64.size)
    (hk : bp + d + 8 * k ≤ UInt64.size)
    (hL : bp + d + 8 * k ≤ L) (b : Stmt) (K : List Kont) (wo : World) (hw : wo.halted = false)
    (f : Frame) (h : Heap) (c : Nat) (hB : f BP = UInt64.ofNat bp) :
    ∃ f', (∀ x, x ≠ RA → x ≠ RB → x ≠ RX → x ≠ RT → f' x = f x) ∧
      ReachL κ ω L ⟨.seq (fillLoop d k P w) b, K, f, h, wo, c⟩
        ⟨b, K, f', wr h (bp + d) (reps k (natBytes 8 P.toNat)), wo, c + k * (Tick.words w).cost κ⟩ :=
  wordLoop_reach k w bp _ (fun j => wr h (bp + d) (reps j (natBytes 8 P.toNat))) hk8
    (fun j hj g hg hgB => by
      refine ⟨g, fun _ _ => rfl, fun K' w' c' hw' => ?_⟩
      have hacc : AccIn L ⟨.store .w64 (.slot RB) (UInt64.ofNat d) (.imm P), K', g,
          wr h (bp + d) (reps j (natBytes 8 P.toNat)), w', c'⟩ := by
        simp only [AccIn, eval_slot, hgB, ofNat_add_ofNat, Width.bytes]
        exact acc_ofNat (by omega) (by omega)
      refine ReachL.step' hw' ?_ hacc
      simp only [exec1, eval_slot, eval_imm, hgB, ofNat_add_ofNat]
      rw [store64_eq, reps_succ', wr_append]
      simp only [reps_length, natBytes_length]
      rw [show bp + 8 * j + d = bp + d + j * 8 by omega]
      exact ReachL.refl _)
    b K wo hw f c hB

/-- The copy loop: it copies `k` words from `bp + so` to `bp + dd`, two disjoint ranges. -/
theorem copyLoop_reach (so dd k w bp : Nat) (hk8 : 8 * k < UInt64.size)
    (hs : bp + so + 8 * k ≤ UInt64.size) (hd : bp + dd + 8 * k ≤ UInt64.size)
    (hdisj : so + 8 * k ≤ dd ∨ dd + 8 * k ≤ so) (hsL : bp + so + 8 * k ≤ L)
    (hdL : bp + dd + 8 * k ≤ L) (b : Stmt) (K : List Kont) (wo : World)
    (hw : wo.halted = false) (f : Frame) (h : Heap) (c : Nat) (hB : f BP = UInt64.ofNat bp) :
    ∃ f', (∀ x, x ≠ RA → x ≠ RB → x ≠ RX → x ≠ RT → f' x = f x) ∧
      ReachL κ ω L ⟨.seq (copyLoop so dd k w) b, K, f, h, wo, c⟩
        ⟨b, K, f', wr h (bp + dd) (rd h (bp + so) (8 * k)), wo, c + k * (Tick.words w).cost κ⟩ :=
  wordLoop_reach k w bp _ (fun j => wr h (bp + dd) (rd h (bp + so) (8 * j))) hk8
    (fun j hj g hg hgB => by
      let H := wr h (bp + dd) (rd h (bp + so) (8 * j))
      let B := rd h (bp + so + 8 * j) 8
      have hsrc : rd H (bp + so + 8 * j) 8 = B := rd_congr fun i hi =>
        wr_other _ _ _ _ (by omega) (by simp; omega) (by simp; omega)
      refine ⟨(g.set RT (decodeLE B)), fun x hx => Frame.set_ne _ _ hx, fun K' w' c' hw' => ?_⟩
      have hacc₁ : AccIn L ⟨.load .w64 RT (.slot RB) (UInt64.ofNat so),
          .seq (.store .w64 (.slot RB) (UInt64.ofNat dd) (.slot RT)) :: K', g, H, w', c'⟩ := by
        simp only [AccIn, eval_slot, hgB, ofNat_add_ofNat, Width.bytes]
        exact acc_ofNat (by omega) (by omega)
      have hacc₂ : AccIn L ⟨.store .w64 (.slot RB) (UInt64.ofNat dd) (.slot RT), K',
          g.set RT (decodeLE B), H, w', c'⟩ := by
        simp only [AccIn, eval_slot, Width.bytes]
        rw [Frame.set_ne _ _ (by decide), hgB, ofNat_add_ofNat]
        exact acc_ofNat (by omega) (by omega)
      have hld : H.load .w64 (UInt64.ofNat (bp + 8 * j + so)) = decodeLE B := by
        rw [load64_eq, show bp + 8 * j + so = bp + so + 8 * j by omega, hsrc]
      have hst : H.store .w64 (UInt64.ofNat (bp + 8 * j + dd)) (decodeLE B) =
          wr h (bp + dd) (rd h (bp + so) (8 * (j + 1))) := by
        have hB8 : natBytes 8 (decodeLE B).toNat = B := by
          rw [decodeLE_toNat B (by simp [B])]
          have := natBytes_natOfBytes B; simp only [B, rd_length] at this; exact this
        rw [store64_eq, hB8, Nat.mul_succ, rd_add, wr_append]
        simp only [rd_length, H, B]
        rw [show bp + 8 * j + dd = bp + dd + 8 * j by omega]
      simp only [H] at hld hst hacc₁ hacc₂
      refine ReachL.step' hw' ?_
      simp only [exec1]
      refine ReachL.step' hw' ?_ hacc₁
      simp only [exec1, eval_slot, hgB, ofNat_add_ofNat]
      rw [hld]
      refine ReachL.step' hw' ?_
      simp only [exec1]
      refine ReachL.step' hw' ?_ hacc₂
      simp only [exec1, eval_slot, Frame.set_same]
      rw [Frame.set_ne _ _ (by decide), hgB, ofNat_add_ofNat, hst]
      exact ReachL.refl _)
    b K wo hw f c hB

/-- A constructor's tick for the part `W - k w` of its charge, a word loop of `k` iterations of
`words w`, then tick-free code `b`: the clock advances by exactly the constructor's charge `W`. -/
theorem tickLoop_msim {α : Type} {k w W : Nat} {B b : Stmt} {K : List Kont} {f : Frame}
    {h h₁ : Heap} {wo : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot pf : Nat → Prop}
    {r : Out α} (hw : wo.halted = false) (hkw : k * w ≤ W) (hrw : r.world = wo)
    (hrs : r.steps = (Tick.ctor W).cost κ)
    (hloop : ∀ c', ∃ f₁, (∀ x, x ≠ RA → x ≠ RB → x ≠ RX → x ≠ RT → f₁ x = f x) ∧
      ReachL κ ω L ⟨.seq (wordLoop k w B) b, K, f, h, wo, c'⟩
        ⟨b, K, f₁, h₁, wo, c' + k * (Tick.words w).cost κ⟩)
    (hrest : ∀ f₁ : Frame, f₁ BP = f BP → (∀ x, FR ≤ x → f₁ x = f x) →
      ∃ f₂ h₂, Runs κ ω L b f₁ h₁ f₂ h₂ ∧ f₂ BP = f₁ BP ∧ Q r.val f₂ h₂ ∧
        ∀ a, prot a → h₂ (UInt64.ofNat a) = h (UInt64.ofNat a)) :
    MSim κ ω L ⟨.seq (.tick (.ctor (W - k * w))) (.seq (wordLoop k w B) b), K, f, h, wo, c⟩
      K Q prot r pf := by
  let c₁ := c + (Tick.ctor (W - k * w)).cost κ
  obtain ⟨f₁, hf₁, hr₁⟩ := hloop c₁
  have hB₁ : f₁ BP = f BP := hf₁ BP (by decide) (by decide) (by decide) (by decide)
  have hkeep : ∀ x, FR ≤ x → f₁ x = f x := fun x hx =>
    hf₁ x (by simp only [FR, RA] at *; omega) (by simp only [FR, RB] at *; omega)
      (by simp only [FR, RX] at *; omega) (by simp only [FR, RT] at *; omega)
  obtain ⟨f₂, h₂, hr₂, hB₂, hq, hm⟩ := hrest f₁ hB₁ hkeep
  have hcl : c₁ + k * (Tick.words w).cost κ = c + r.steps := by
    simp only [c₁, hrs, Tick.cost]
    rw [← Nat.mul_assoc, Nat.add_assoc c, Nat.add_assoc κ.ctor, ← Nat.add_mul,
      Nat.sub_add_cancel hkw]
  refine ⟨⟨.skip, K, f₂, h₂, wo, c₁ + k * (Tick.words w).cost κ⟩, ?_, hrw.symm, by simp [hcl],
    Or.inr ⟨rfl, rfl, hcl, hB₂.trans hB₁, hq, hm,
      fun x hx _ => (hr₂.keep x hx).trans (hkeep x hx)⟩⟩
  refine ReachL.step' hw ?_
  simp only [exec1]
  refine ReachL.step' hw ?_
  simp only [exec1]
  refine ReachL.step' hw ?_
  simp only [exec1]
  exact hr₁.trans (hr₂.run K wo _ hw)

/-- The code of a fill: the constructor's tick for the part of `W` the loop does not pay, the loop
of `k` stores of `P`, and the tail `T`. It writes those bytes in place and advances the clock by
exactly the constructor's charge `W`. -/
theorem fillCode_msim {α : Type} {d k w W bp : Nat} {P : UInt64} {T : List UInt8} {K : List Kont}
    {f : Frame} {h : Heap} {wo : World} {c : Nat} {Q : α → Frame → Heap → Prop}
    {prot pf : Nat → Prop} {r : Out α} (hw : wo.halted = false) (hB : f BP = UInt64.ofNat bp)
    (hkw : k * w ≤ W) (hk8 : 8 * k < UInt64.size) (hU : bp + d + 8 * k + T.length ≤ UInt64.size)
    (hL : bp + d + 8 * k + T.length ≤ L) (hrw : r.world = wo) (hrs : r.steps = (Tick.ctor W).cost κ)
    (hv : ∀ f', f' BP = f BP → (∀ x, FR ≤ x → f' x = f x) →
      Q r.val f' (wr h (bp + d) (reps k (natBytes 8 P.toNat) ++ T)))
    (hm : ∀ a, prot a → wr h (bp + d) (reps k (natBytes 8 P.toNat) ++ T) (UInt64.ofNat a) =
      h (UInt64.ofNat a)) :
    MSim κ ω L ⟨.seq (.tick (.ctor (W - k * w))) (.seq (fillLoop d k P w)
      (writeB (.slot BP) (d + 8 * k) T)), K, f, h, wo, c⟩ K Q prot r pf := by
  refine tickLoop_msim hw hkw hrw hrs (fun c' => fillLoop_reach d k P w bp hk8 (by omega)
    (by omega) _ K wo hw f h c' hB) fun f₁ hB₁ hk => ?_
  have hW := writeB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) T (d + 8 * k) bp f₁
    (wr h (bp + d) (reps k (natBytes 8 P.toNat))) (by rw [eval_slot, hB₁, hB]) (by omega) (by omega)
  have hh : wr (wr h (bp + d) (reps k (natBytes 8 P.toNat))) (bp + (d + 8 * k)) T =
      wr h (bp + d) (reps k (natBytes 8 P.toNat) ++ T) := by
    rw [wr_append]; simp only [reps_length, natBytes_length]; congr 1; omega
  rw [hh] at hW
  exact ⟨f₁, _, hW, rfl, hv f₁ hB₁ hk, hm⟩

end

end Millipede.Flat
