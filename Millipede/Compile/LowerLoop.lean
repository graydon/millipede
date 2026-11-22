import Millipede.Compile.LowerSlice
import Millipede.Compile.LowerRestr

/-!
# The memory refinement of bounded loops

A lowered loop keeps its accumulator at the watermark `n`, where the continuation finds it as its
variable, and its counter in an 8-byte cell above it at `a = n + s.size`. At the start of each
iteration the counter is copied into the counter variable's cell at `a + 8`, so that a body that
writes that variable does not change the loop. The condition is evaluated into the byte at
`a + 16`, the body into `a + 17`, and the body's new accumulator is then copied to the accumulator.

Either loop variable may instead live in frame slots. A counter variable that the body does not
write is a frame slot that is the counter itself, so it needs no cell and no copy. An accumulator
of slot-resident type lives in frame slots, receives the initial atom's words directly, and is not
copied at the exit. A body that carries no variable and whose tails compute into slots runs into
the slots after the loop variables', from which `accNext` moves the value to the accumulator. A
condition whose tails compute into slots is likewise computed into a slot. `LoopG` is stated over
the locations of the loop variables and the condition's tail mode, so one proof covers every
combination.

The tick of an iteration is charged at the start of the body when the condition holds and right
after the condition when it fails, so every path of the linearized code into the body passes it.
The clock then falls short of `exec`'s count only when the condition halts.

A loop may also write carried variables, which are variables bound outside it. They are updated in
place, because the body is lowered in tail mode `loopTl` and hands them back where they live, so
nothing is copied for them at entry, at exit or per iteration. A carried variable of slot-resident
type that nothing addresses is kept in its slots, which the body assigns.

`LoopG.head` proves the invariant at the loop head by induction on the number of remaining
iterations. `loopG_of_loop` instantiates it for `Exp.loop`: at the loop head the memory and the
frame represent the environment with the current carried values and hold the accumulator and the
counter. After an iteration, `carry_rel` shows that each carried variable holds its component of
the handed-back value and that nothing else below the watermark changed.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- After the condition, load the flag into `RX`, and charge the iteration here if the condition
failed. If it held, the body charges the iteration. -/
abbrev loopTestM (s : Ty) (n : Nat) (tmc : Tl) : Stmt :=
  .seq (flagLoad tmc n) (.ite (.slot RX) .skip (.tick (.iter (width s))))

/-- The first part of a lowered loop iteration: the counter test, the counter variable, the
condition into `a + 16` or a frame slot, and its test. -/
abbrev loopPreM {Γ : List Ty} {s : Ty} (N a : Nat) (lc : Loc) (c : Exp (.u64 :: s :: Γ) .bool)
    (tmc : Tl) (ρ' : List Loc) (m : Nat) : Stmt :=
  .seq (cntTest lc a N)
    (.ite (.slot RX) (.seq (cntEnter lc a) (.seq (lowerM c tmc ρ' m (a + 16)) (loopTestM s a tmc)))
      .skip)

/-- After the body, move its new accumulator to the accumulator and increment the counter. -/
abbrev loopNextM (s : Ty) (a : Nat) (lc la : Loc) (tmb : Tl) : Stmt :=
  .seq (accNext la (bodyLoc tmb a s.slotN) s.size) (cntNext lc a)

/-- The body part of a lowered loop iteration: the iteration's tick, the body in tail mode `tmb`
into `a + 17`, then `loopNextM`. -/
abbrev loopBodyCM {Γ : List Ty} {t : Ty} (s : Ty) (a : Nat) (lc la : Loc)
    (body : Exp (.u64 :: s :: Γ) t) (tmb : Tl) (ρ' : List Loc) (m : Nat) : Stmt :=
  .seq (.tick (.iter (width s))) (.seq (lowerM body tmb ρ' m (a + 17)) (loopNextM s a lc la tmb))

theorem ReachL.seq_reach {a b : Stmt} {K : List Kont} {f f' : Frame} {h h' : Heap} {w : World}
    {c : Nat} (hw : w.halted = false) (ha : Reaches κ ω L a f h f' h') :
    ReachL κ ω L ⟨.seq a b, K, f, h, w, c⟩ ⟨b, K, f', h', w, c⟩ :=
  ReachL.step' hw (by
    simp only [exec1]
    exact (ha (.seq b :: K) w c hw).trans
      (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)))

/-- Code that charges no tick at the head of a continuation `seq b`, followed by `b`. -/
theorem MSim.reach_k {α : Type} {a b : Stmt} {k : List Kont} {f f₁ : Frame} {h h₁ : Heap}
    {w : World} {c : Nat} {Q : α → Frame → Heap → Prop} {prot pf : Nat → Prop} {r : Out α}
    (hw : w.halted = false) (ha : Reaches κ ω L a f h f₁ h₁) (hf : f₁ BP = f BP)
    (hm : ∀ x, prot x → h₁ (UInt64.ofNat x) = h (UInt64.ofNat x))
    (hk : ∀ x, FR ≤ x → pf x → f₁ x = f x)
    (hb : MSim κ ω L ⟨b, k, f₁, h₁, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨a, .seq b :: k, f, h, w, c⟩ k Q prot r pf :=
  (MSim.pre (s := ⟨a, .seq b :: k, f, h, w, c⟩) (δ := 0)
    ((ha _ w c hw).trans (ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _))) rfl hf hm
    hk hb).of_eq rfl rfl (by simp)

theorem ReachL.while_exit {pre body : Stmt} {o : Operand} {k : List Kont} {f f' : Frame}
    {h h' : Heap} {w : World} {c : Nat} (hw : w.halted = false) (hp : Reaches κ ω L pre f h f' h')
    (ho : o.eval f' = 0) :
    ReachL κ ω L ⟨.while pre o body, k, f, h, w, c⟩ ⟨.skip, k, f', h', w, c⟩ :=
  ReachL.step' hw (by
    simp only [exec1]
    exact (hp _ w c hw).trans
      (ReachL.step' hw (by simp only [exec1, ho, ↓reduceIte]; exact ReachL.refl _)))

/-! ## The counter and the accumulator

Each loop variable is in memory or in frame slots. A slot-resident counter variable is the counter
itself, so the test reads the slot, the increment adds to it, and nothing is copied per iteration,
which is sound because the body does not write it. A slot-resident accumulator receives the initial
atom's words and, after each iteration, the body's new accumulator; nothing is copied at the exit.
-/

/-- A loop variable's location: its bytes at offset `o`, or for a slot-resident type its slots from
`K`. The counter's location is a `U64` at `a + 8`. -/
def AccLoc (s : Ty) (la : Loc) (n K : Nat) : Prop :=
  la = .own n ∨ (s.slotTy = true ∧ la = .slot n K s.slotN)

/-- The location of the loop counter's variable. -/
abbrev CntLoc (lc : Loc) (a K : Nat) : Prop := AccLoc .u64 lc (a + 8) K

/-- The counter holds `i`, in its slot or in the memory cell at `a`. -/
def CntAt (lc : Loc) (bp a : Nat) (f : Frame) (h : Heap) (i : Nat) : Prop :=
  match lc with
  | .slot _ k _ => f k = UInt64.ofNat i
  | _ => rd h (bp + a) 8 = natBytes 8 (UInt64.ofNat i).toNat

/-- The accumulator holds `v`, as words in its slots or as bytes that represent it at its offset. -/
def AccAt (s : Ty) (la : Loc) (bp : Nat) (f : Frame) (h : Heap) (v : s.carrier) : Prop :=
  match la with
  | .slot _ k w => w = s.slotN ∧ WordsRel s v f k
  | l => Data.reprBytes v (rd h (bp + l.off) s.size)

theorem CntAt.congr {lc : Loc} {bp a i : Nat} {f f' : Frame} {h h' : Heap}
    (hc : CntAt lc bp a f h i)
    (hh : ∀ j, j < 8 → h' (UInt64.ofNat (bp + a + j)) = h (UInt64.ofNat (bp + a + j)))
    (hf : ∀ k, lc.slot? = some k → f' k = f k) : CntAt lc bp a f' h' i := by
  cases lc with
  | slot o k _ => simp only [CntAt] at hc ⊢; rw [hf k rfl]; exact hc
  | _ => simp only [CntAt] at hc ⊢; rw [← hc]; exact rd_congr hh

theorem AccAt.congr {s : Ty} {la : Loc} {bp : Nat} {v : s.carrier} {f f' : Frame} {h h' : Heap}
    (hc : AccAt s la bp f h v)
    (hh : ∀ j, j < s.size → h' (UInt64.ofNat (bp + la.off + j)) =
      h (UInt64.ofNat (bp + la.off + j)))
    (hf : ∀ x, la.holds x = true → f' x = f x) : AccAt s la bp f' h' v := by
  cases la with
  | slot o k n =>
    simp only [AccAt] at hc ⊢
    obtain ⟨rfl, hc⟩ := hc
    exact ⟨rfl, hc.congr fun x h1 h2 => hf x (by simp; omega)⟩
  | _ => simp only [AccAt] at hc ⊢; rw [rd_congr hh]; exact hc

/-- The counter test: `RX := counter < N`. -/
theorem cnt_test {lc : Loc} {bp a i N K : Nat} {f : Frame} {hh : Heap} (hlc : CntLoc lc a K)
    (hf : f BP = UInt64.ofNat bp) (hc : CntAt lc bp a f hh i) (hN : N < UInt64.size) (hi : i ≤ N)
    (hbL : bp + a + 8 ≤ L) (hbU : bp + a + 8 ≤ UInt64.size) :
    Runs κ ω L (cntTest lc a N) f hh (f.set RX (if i < N then 1 else 0)) hh := by
  have hlt : (UInt64.ofNat i < UInt64.ofNat N) ↔ i < N := ofNat_lt_ofNat hN hi
  rcases hlc with rfl | ⟨-, rfl⟩
  · simp only [CntAt] at hc
    refine Runs.congr (Runs.seq (Runs.load _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega)
      (by omega) hf)) (Runs.bin _ _ _ _ _ _)) ?_ rfl
    funext x
    simp only [Frame.set, eval_slot, eval_imm, hf, ofNat_add_ofNat, BinOp.eval, ↓reduceIte]
    rw [load64_eq, hc, decodeLE_natBytes8]
    by_cases h : i < N <;> by_cases hx : x = RX <;> simp [h, hlt, hx]
  · simp only [CntAt] at hc
    refine Runs.congr (Runs.bin _ _ _ _ _ _) ?_ rfl
    simp only [eval_slot, eval_imm, hc, BinOp.eval]
    by_cases h : i < N <;> simp [h, hlt]

/-- Entering an iteration makes the counter variable hold the counter. Only the counter variable's
8 bytes in memory change. -/
theorem cnt_enter {lc : Loc} {bp a i K : Nat} {f : Frame} {h : Heap} (hlc : CntLoc lc a K)
    (hf : f BP = UInt64.ofNat bp) (hc : CntAt lc bp a f h i) (hbL : bp + a + 16 ≤ L)
    (hbU : bp + a + 16 ≤ UInt64.size) :
    ∃ f' h', Runs κ ω L (cntEnter lc a) f h f' h' ∧ f' BP = f BP ∧
      (∀ x, x < UInt64.size → ¬ InR (bp + (a + 8)) 8 x →
        h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      CntAt lc bp a f' h' i ∧
      (lc = .own (a + 8) → Data.reprBytes (UInt64.ofNat i) (rd h' (bp + (a + 8)) 8)) := by
  rcases hlc with rfl | ⟨-, rfl⟩
  · simp only [CntAt] at hc ⊢
    have hf₃ : (f.set RT (UInt64.ofNat i)) BP = UInt64.ofNat bp := by
      rw [Frame.set_ne _ _ (by decide)]; exact hf
    have hout : ∀ x, x < UInt64.size → ¬ InR (bp + (a + 8)) 8 x →
        wr h (bp + (a + 8)) (natBytes 8 (UInt64.ofNat i).toNat) (UInt64.ofNat x) =
          h (UInt64.ofNat x) :=
      fun x hx hn => wr_out (by simp; omega) hx (by simp; unfold InR at hn; omega)
    refine ⟨f.set RT (UInt64.ofNat i), wr h (bp + (a + 8)) (natBytes 8 (UInt64.ofNat i).toNat),
      Runs.seq (f₁ := f.set RT (UInt64.ofNat i)) (h₁ := h)
        (Runs.congr (Runs.load _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega) (by omega)
          hf)) (by simp only [eval_slot, hf, ofNat_add_ofNat]; rw [load64_eq, hc, decodeLE_natBytes8])
          rfl)
        (Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega) (by omega)
          hf₃)) rfl (by
          simp only [eval_slot, Frame.set, ↓reduceIte, show (BP = RT) = False by decide, hf,
            ofNat_add_ofNat]
          rw [store64_eq])), hf₃.trans hf.symm, hout, ?_, fun _ => ?_⟩
    · exact (rd_congr fun j hj => hout _ (by omega) (by unfold InR; omega)).trans hc
    · have := rd_wr h (bp + (a + 8)) (natBytes 8 (UInt64.ofNat i).toNat) (by simp; omega)
      rw [natBytes_length] at this; rw [this]; exact ⟨natBytes_length _ _, rfl⟩
  · exact ⟨f, h, Runs.skip f h, rfl, fun _ _ _ => rfl, hc, fun e => by cases e⟩

/-- Incrementing the counter changes only the counter, which is its slot or the 8 bytes at `a`. -/
theorem cnt_next {lc : Loc} {bp a i K : Nat} {f : Frame} {h : Heap} (hlc : CntLoc lc a K)
    (hK : FR ≤ K) (hf : f BP = UInt64.ofNat bp) (hc : CntAt lc bp a f h i) (hbL : bp + a + 8 ≤ L)
    (hbU : bp + a + 8 ≤ UInt64.size) :
    ∃ f' h', Reaches κ ω L (cntNext lc a) f h f' h' ∧ f' BP = f BP ∧
      (∀ x, FR ≤ x → lc.slot? ≠ some x → f' x = f x) ∧
      (∀ x, x < UInt64.size → ¬ InR (bp + a) 8 x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      CntAt lc bp a f' h' (i + 1) := by
  have hKBP : BP ≠ K := by simp only [FR, BP] at hK ⊢; omega
  rcases hlc with rfl | ⟨-, rfl⟩
  · simp only [CntAt] at hc ⊢
    let f₈ := (f.set RT (UInt64.ofNat i)).set RT (UInt64.ofNat i + 1)
    have hf₈ : f₈ BP = UInt64.ofNat bp := by
      simp only [f₈, Frame.set, show (BP = RT) = False by decide, ite_false]; exact hf
    have hout : ∀ x, x < UInt64.size → ¬ InR (bp + a) 8 x →
        wr h (bp + a) (natBytes 8 (UInt64.ofNat (i + 1)).toNat) (UInt64.ofNat x) =
          h (UInt64.ofNat x) :=
      fun x hx hn => wr_out (by simp; omega) hx (by simp; unfold InR at hn; omega)
    have hr : Runs κ ω L (cntNext (.own (a + 8)) a) f h f₈
        (wr h (bp + a) (natBytes 8 (UInt64.ofNat (i + 1)).toNat)) :=
      Runs.seq (f₁ := f.set RT (UInt64.ofNat i)) (h₁ := h)
        (Runs.congr (Runs.load _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega)
          (by omega) hf)) (by simp only [eval_slot, hf, ofNat_add_ofNat]; rw [load64_eq, hc,
            decodeLE_natBytes8]) rfl)
        (Runs.seq (f₁ := f₈) (h₁ := h)
          (Runs.congr (Runs.bin _ _ _ _ (f.set RT (UInt64.ofNat i)) h) (by
            simp only [f₈, eval_slot, eval_imm, BinOp.eval, Frame.set, ↓reduceIte]) rfl)
          (Runs.congr (Runs.store _ _ _ _ f₈ h (acc_off (by simp only [Width.bytes]; omega)
            (by omega) hf₈)) rfl (by
            simp only [f₈, eval_slot, Frame.set, ↓reduceIte, show (BP = RT) = False by decide,
              hf, ofNat_add_ofNat]
            rw [store64_eq, show UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) by
              rw [UInt64.ofNat_add]; rfl])))
    refine ⟨f₈, _, hr.run, hf₈.trans hf.symm, fun x hx _ => hr.keep x hx, hout, ?_⟩
    have := rd_wr h (bp + a) (natBytes 8 (UInt64.ofNat (i + 1)).toNat) (by simp; omega)
    rwa [natBytes_length] at this
  · simp only [CntAt] at hc ⊢
    refine ⟨f.set K (UInt64.ofNat i + 1), h, Reaches.congr (Reaches.bin _ _ _ _ _ _) ?_ rfl,
      Frame.set_ne _ _ hKBP, fun x _ hx => Frame.set_ne _ _ (fun e => hx (by rw [e]; rfl)),
      fun _ _ _ => rfl, ?_⟩
    · simp only [eval_slot, eval_imm, hc, BinOp.eval]
    · simp only [Frame.set, ↓reduceIte]; rw [UInt64.ofNat_add]; rfl

/-- Where a loop body leaves the new accumulator: its destination `a + 17`, or for a slot-resident
accumulator the slots from `T`, after the accumulator's. -/
def BodyLoc (s : Ty) (la lb : Loc) (a : Nat) : Prop :=
  lb = .own (a + 17) ∨ ∃ K T, la.slot? = some K ∧ lb = .slot (a + 17) T s.slotN ∧ K + s.slotN ≤ T

/-- Moving the new accumulator from where the body left it changes only the accumulator, which is
its slots or its bytes at `n`. -/
theorem acc_next {s : Ty} {la lb : Loc} {bp n a K : Nat} {v : s.carrier} {f : Frame} {h : Heap}
    (hla : AccLoc s la n K) (hlb : BodyLoc s la lb a) (hK : FR ≤ K) (ha : a = n + s.size)
    (hf : f BP = UInt64.ofNat bp) (hv : AccAt s lb bp f h v) (hbL : bp + (a + 17 + s.size) ≤ L)
    (hbU : bp + (a + 17 + s.size) ≤ UInt64.size) :
    ∃ f' h', Reaches κ ω L (accNext la lb s.size) f h f' h' ∧ f' BP = f BP ∧
      (∀ x, FR ≤ x → la.holds x = false → f' x = f x) ∧
      (∀ x, x < UInt64.size → ¬ InR (bp + n) s.size x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      AccAt s la bp f' h' v := by
  have hKBP : BP ≠ K := by simp only [FR, BP] at hK ⊢; omega
  rcases hlb with rfl | ⟨K', T, hK', rfl, hKT⟩
  · replace hv : Data.reprBytes v (rd h (bp + (a + 17)) s.size) := hv
    rcases hla with rfl | ⟨hts, rfl⟩
    · obtain ⟨f₇, hf₇, hr₇⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot BP)
        (by decide) (by decide) s.size (a + 17) n bp bp f h hf hf (by omega) (by omega)
        (Or.inr (by omega)) (by omega) (by omega)
      refine ⟨f₇, _, hr₇.run, hf₇ BP (by decide), fun x hx _ => hr₇.keep x hx,
        fun x hx hn => wr_out (by simp; omega) hx (by simp; unfold InR at hn; omega), ?_⟩
      show Data.reprBytes v (rd (wr h (bp + n) (rd h (bp + (a + 17)) s.size)) (bp + n) s.size)
      have := rd_wr h (bp + n) (rd h (bp + (a + 17)) s.size) (by simp; omega)
      rw [rd_length] at this; rw [this]; exact hv
    · obtain ⟨f', hr, hout, hw⟩ := ldSlots_words (κ := κ) (ω := ω) (L := L) (K := K) (b := BP)
        (o := a + 17) hts hf (by simp only [FR, BP] at hK ⊢; omega) hv (by omega) (by omega)
      exact ⟨f', h, hr, hout BP (Or.inl (by simp only [FR, BP] at hK ⊢; omega)),
        fun x _ hx => hout x (by
          have := Loc.holds_false (l := .slot n K s.slotN) rfl hx; simpa using this),
        fun _ _ _ => rfl, rfl, hw⟩
  · rcases hla with rfl | ⟨hts, rfl⟩
    · simp [Loc.slot?] at hK'
    · have hKT' : K + s.slotN ≤ T := by simp only [Loc.slot?, Option.some.injEq] at hK'; omega
      obtain ⟨-, B, hB, hW⟩ := hv
      obtain ⟨f', hr, hout, hval⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) s.slotN (x := K)
        (k := T) (f := f) (h := h) (Or.inl (by omega))
      refine ⟨f', h, hr, hout BP (Or.inl (by simp only [FR, BP] at hK ⊢; omega)),
        fun x _ hx => hout x (by
          have := Loc.holds_false (l := .slot n K s.slotN) rfl hx; simpa using this),
        fun _ _ _ => rfl, rfl, B, hB, ?_⟩
      exact wordsAt_iff.2 fun j hj => by rw [hval j hj]; exact wordsAt_iff.1 hW j hj

/-- The condition failed: charge the iteration and leave the loop. -/
theorem ReachL.loopTest_false {s : Ty} {a : Nat} {tmc : Tl} {pre body : Stmt} {K : List Kont} {f f' : Frame}
    {h : Heap} {w : World} {clk : Nat} (hw : w.halted = false)
    (hl : Runs κ ω L (flagLoad tmc a) f h f' h) (hx : f' RX = 0) :
    ReachL κ ω L ⟨loopTestM s a tmc, .loop pre (.slot RX) body :: K, f, h, w, clk⟩
      ⟨.skip, K, f', h, w, clk + (Tick.iter (width s)).cost κ⟩ :=
  (ReachL.seq_reach hw hl.run).trans (ReachL.step' hw (by
    simp only [exec1, eval_slot, hx, ↓reduceIte]; exact ReachL.step' hw (by
      simp only [exec1]; exact ReachL.step' hw (by
        simp only [exec1, eval_slot, hx, ↓reduceIte]; exact ReachL.refl _))))

/-- The condition held: enter the body, which charges the iteration. -/
theorem ReachL.loopTest_true {s : Ty} {a : Nat} {tmc : Tl} {pre b rest : Stmt} {K : List Kont}
    {f f' : Frame} {h : Heap} {w : World} {clk : Nat} (hw : w.halted = false)
    (hl : Runs κ ω L (flagLoad tmc a) f h f' h) (hx : f' RX ≠ 0) :
    ReachL κ ω L ⟨loopTestM s a tmc,
        .loop pre (.slot RX) (.seq (.tick (.iter (width s))) (.seq b rest)) :: K, f, h, w, clk⟩
      ⟨b, .seq rest :: .seq (.while pre (.slot RX) (.seq (.tick (.iter (width s))) (.seq b rest)))
        :: K, f', h, w, clk + (Tick.iter (width s)).cost κ⟩ :=
  (ReachL.seq_reach hw hl.run).trans (ReachL.step' hw (by
    simp only [exec1, eval_slot, hx, ↓reduceIte]; exact ReachL.step' hw (by
      simp only [exec1, eval_slot, hx, ↓reduceIte]; exact ReachL.step' hw (by
        simp only [exec1]; exact ReachL.step' hw (by
          simp only [exec1]; exact ReachL.step' hw (by
            simp only [exec1]; exact ReachL.step' hw (by
              simp only [exec1]; exact ReachL.refl _)))))))

/-! ## The generic loop invariant

A loop lowers to a fixed skeleton: the counter, the counter's variable at `a + 8`, the condition at
`a + 16`, the body's value at `a + 17`, and the accumulator. `LoopG` states the invariant over a
loop state `st`, the body's value, which gives the accumulator `fst st` and the environment
`E st`. For `Exp.loop` the state holds the accumulator and the carried variables' values.
`LoopG.head` is the invariant at the loop head, by induction on the number of remaining iterations.
-/

/-- The loop's two variables, the counter's and the accumulator. -/
abbrev loopρ (lc la : Loc) (ρ : List Loc) : List Loc := lc :: la :: ρ

abbrev loopS (bp a n : Nat) (S : List SI) : List SI :=
  ⟨bp + (a + 8), none, none, none⟩ :: ⟨bp + n, none, none, none⟩ :: S

/-- The environment of the condition and the body, with counter `i` and loop state `st`. -/
abbrev loopEnv {Γ : List Ty} {s t : Ty} (fst : t.carrier → s.carrier) (E : t.carrier → Env Γ)
    (i : UInt64) (st : t.carrier) : Env (.u64 :: s :: Γ) :=
  .cons i (.cons (fst st) (E st))

abbrev loopPreG {Γ : List Ty} {s : Ty} (N a : Nat) (lc la : Loc) (c : Exp (.u64 :: s :: Γ) .bool)
    (tmc : Tl) (ρ : List Loc) : Stmt :=
  loopPreM N a lc c tmc (loopρ lc la ρ) (a + 17 + s.size)

abbrev loopBodyG {Γ : List Ty} {s t : Ty} (a : Nat) (lc la : Loc) (body : Exp (.u64 :: s :: Γ) t)
    (tmb : Tl) (ρ : List Loc) : Stmt :=
  loopBodyCM s a lc la body tmb (loopρ lc la ρ) (a + 17 + s.size)

theorem AccLoc.loc {s : Ty} {la : Loc} {n K : Nat} (h : AccLoc s la n K) :
    la = .own n ∨ ∃ K' w, la = .slot n K' w := by
  rcases h with rfl | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨K, _, rfl⟩

/-- The layout inside the loop. -/
theorem loop_lay {bp n a m : Nat} {Γ : List Ty} {s : Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} {lc la : Loc} {Kc Ka : Nat} (hl : Lay bp n Γ ρ S W) (hlc : CntLoc lc a Kc)
    (hla : AccLoc s la n Ka) (ha : a = n + s.size) (b₁ b₂ : Bool) (hm : a + 16 ≤ m) :
    Lay bp m (.u64 :: s :: Γ) (loopρ lc la ρ) (loopS bp a n S) (b₁ :: b₂ :: W) :=
  have hlA : Lay bp (a + 8) (s :: Γ) (la :: ρ) (⟨bp + n, none, none, none⟩ :: S) (b₂ :: W) :=
    Lay.pushAtL s b₂ hla.loc hl (hl.away (Nat.le_refl _)) (by omega) (by omega)
  Lay.pushAtL Ty.u64 b₁ hlc.loc hlA (hlA.away (Nat.le_refl _)) (by show a + 8 + 8 ≤ _; omega)
    (by omega)

/-- Writable storage lies below the watermark. -/
theorem InW.lt {bp n x : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W W' : List Bool},
    Lay bp n Γ ρ S W' → InW Γ S W x → x < bp + n
  | _ :: _, _ :: _, _ :: _, _, _, hl, h => h.elim (fun h => hl.1.lt h.2) (InW.lt hl.2.2)
  | [], _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, hl, _ => hl.elim
  | _ :: _, _ :: _, [], _, _, _, h => h.elim

/-- An address below the counter's variable, outside the accumulator's bytes and the writable
storage, is protected from the condition and the body. -/
theorem loop_prot {bp a n m o sz x : Nat} {Γ : List Ty} {s : Ty} {S : List SI} {W : List Bool}
    (b₁ b₂ : Bool) (hx : x < bp + (a + 8)) (hd : ¬ InR (bp + n) s.size x) (hW : ¬ InW Γ S W x)
    (hm : x < bp + m) (ho : a + 8 ≤ o) :
    Prot bp m o sz (.u64 :: s :: Γ) (loopS bp a n S) (b₁ :: b₂ :: W) x :=
  ⟨hm, by unfold InR; omega, by
    rintro (⟨_, h3⟩ | ⟨_, h3⟩ | h2)
    · simp only [SI.In_mk, InR, show Ty.u64.size = 8 from rfl, SI.sz_mk_none] at h3; omega
    · exact hd (by simpa using h3)
    · exact hW h2⟩

/-- What the loop invariant needs of a lowered loop: the layout, the locations of the two loop
variables, the simulations of the condition and the body from any iteration's environment, and how
the body's value gives the next loop state. The body may write the counter variable only when it
is in memory. The condition's value is in its byte or in a frame slot. -/
structure LoopG (κ : CostModel) (ω : Oracle) (L : Nat) {Γ : List Ty} {s t : Ty} (N : Nat)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) t)
    (fst : t.carrier → s.carrier) (E : t.carrier → Env Γ) (tmc tmb : Tl) (lc la : Loc) (wc : Bool)
    (bp n a : Nat) (ρ : List Loc) (S : List SI) (W Wb : List Bool) : Prop where
  lay : Lay bp n Γ ρ S W
  na : a = n + s.size
  room : bp + (a + 17 + s.size) ≤ L
  size : bp + (a + 17 + s.size) ≤ UInt64.size
  hN : N < UInt64.size
  /-- The slot-resident variables, none of which is carried, keep their slots. -/
  slots : SlotsOk ρ
  laOk : AccLoc s la n (FR + slotsIn ρ)
  lcOk : CntLoc lc a (FR + slotsIn (la :: ρ))
  wcOk : lc.isSlot = true → wc = false
  /-- The condition's value is its byte at `a + 16` or a frame slot. -/
  tmcOk : tmc = .none ∨ ∃ T, tmc = .word T
  /-- The body's new accumulator is at `a + 17`, or in slots after a slot-resident accumulator's. -/
  lbOk : BodyLoc s la (bodyLoc tmb a s.slotN) a
  condS : ∀ (i : UInt64) (st : t.carrier) (f : Frame) (h : Heap) (w : World) (K : List Kont)
    (clk : Nat), f BP = UInt64.ofNat bp → FEnvRel f (loopEnv fst E i st) (loopρ lc la ρ) →
    MEnvRel h bp (loopEnv fst E i st) (loopρ lc la ρ) (loopS bp a n S) →
    c.safe ω (loopEnv fst E i st) w → w.halted = false →
    MSim κ ω L ⟨lowerM c tmc (loopρ lc la ρ) (a + 17 + s.size) (a + 16), K, f, h, w, clk⟩ K
      (TQ tmc bp (a + 16) (loopρ lc la ρ) (loopS bp a n S) .bool)
      (Prot bp (a + 17 + s.size) (a + 16) (Tl.dsz .bool tmc) (.u64 :: s :: Γ) (loopS bp a n S)
        (false :: false :: noW W)) (c.exec ω κ .copy (loopEnv fst E i st) w)
      (SProt (loopρ lc la ρ) (false :: false :: noW W))
  bodyS : ∀ (i : UInt64) (st : t.carrier) (f : Frame) (h : Heap) (w : World) (K : List Kont)
    (clk : Nat), f BP = UInt64.ofNat bp → FEnvRel f (loopEnv fst E i st) (loopρ lc la ρ) →
    MEnvRel h bp (loopEnv fst E i st) (loopρ lc la ρ) (loopS bp a n S) →
    body.safe ω (loopEnv fst E i st) w → w.halted = false →
    MSim κ ω L ⟨lowerM body tmb (loopρ lc la ρ) (a + 17 + s.size) (a + 17), K, f, h, w, clk⟩ K
      (TQ tmb bp (a + 17) (loopρ lc la ρ) (loopS bp a n S) t)
      (Prot bp (a + 17 + s.size) (a + 17) (tmb.dsz t) (.u64 :: s :: Γ) (loopS bp a n S)
        (wc :: true :: Wb)) (body.exec ω κ tmb.hb (loopEnv fst E i st) w)
      (SProt (loopρ lc la ρ) (wc :: true :: Wb))
  step : ∀ (i : UInt64) (st : t.carrier) (w : World) (f f' : Frame) (h h' : Heap),
    MEnvRel h bp (E st) ρ S → FEnvRel f (E st) ρ → body.safe ω (loopEnv fst E i st) w →
    TQ tmb bp (a + 17) (loopρ lc la ρ) (loopS bp a n S) t
      (body.exec ω κ tmb.hb (loopEnv fst E i st) w).val f' h' →
    (∀ x, Prot bp (a + 17 + s.size) (a + 17) (tmb.dsz t) (.u64 :: s :: Γ) (loopS bp a n S)
        (wc :: true :: Wb) x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) →
    (∀ x, FR ≤ x → SProt (loopρ lc la ρ) (wc :: true :: Wb) x → f' x = f x) →
    AccAt s (bodyLoc tmb a s.slotN) bp f' h' (fst (body.exec ω κ tmb.hb (loopEnv fst E i st) w).val) ∧
      MEnvRel h' bp (E (body.exec ω κ tmb.hb (loopEnv fst E i st) w).val) ρ S ∧
      FEnvRel f' (E (body.exec ω κ tmb.hb (loopEnv fst E i st) w).val) ρ

/-- What the loop leaves: the accumulator holds the final state's, and the memory and the frame
represent the final state's environment. -/
abbrev LoopPost {Γ : List Ty} (s : Ty) (la : Loc) (bp : Nat) (ρ : List Loc) (S : List SI) {t : Ty}
    (fst : t.carrier → s.carrier) (E : t.carrier → Env Γ) : t.carrier → Frame → Heap → Prop :=
  fun r f' h' => AccAt s la bp f' h' (fst r) ∧ MEnvRel h' bp (E r) ρ S ∧ FEnvRel f' (E r) ρ

/-- The loop invariant at the loop head, with `mm` iterations left from counter `i`: the memory and
the frame represent the environment `E st`, and they hold the counter and the accumulator. -/
def LoopAt (κ : CostModel) (ω : Oracle) (L : Nat) (κi : CostModel) {Γ : List Ty} {s t : Ty}
    (N : Nat) (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) t)
    (fst : t.carrier → s.carrier) (E : t.carrier → Env Γ) (tmc tmb : Tl) (lc la : Loc)
    (bp n a : Nat) (ρ : List Loc) (S : List SI) (Wb : List Bool) (K : List Kont) (mm i : Nat) :
    Prop :=
  ∀ (st : t.carrier) (f : Frame) (h : Heap) (w : World) (clk : Nat),
    f BP = UInt64.ofNat bp → FEnvRel f (E st) ρ → MEnvRel h bp (E st) ρ S →
    CntAt lc bp a f h i → AccAt s la bp f h (fst st) → w.halted = false →
    loopSafe (fun i st w => c.safe ω (loopEnv fst E i st) w)
      (fun i st w => body.safe ω (loopEnv fst E i st) w)
      (fun i st w => c.denote ω (loopEnv fst E i st) w)
      (fun i st w => body.denote ω (loopEnv fst E i st) w) mm i st w →
    MSim κ ω L ⟨.while (loopPreG N a lc la c tmc ρ) (.slot RX) (loopBodyG a lc la body tmb ρ), K, f, h,
        w, clk⟩
      K (LoopPost s la bp ρ S fst E)
      (Prot bp n n s.size Γ S Wb)
      (loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
        (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm i st w) (SProt ρ Wb)

namespace LoopG
variable {Γ : List Ty} {s t : Ty} {N : Nat} {c : Exp (.u64 :: s :: Γ) .bool}
  {body : Exp (.u64 :: s :: Γ) t} {fst : t.carrier → s.carrier} {E : t.carrier → Env Γ} {tmc tmb : Tl}
  {lc la : Loc} {wc : Bool} {bp n a : Nat} {ρ : List Loc} {S : List SI} {W Wb : List Bool}

/-- The slots of the enclosing variables are not those of the two loop variables. -/
theorem slot_ne (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {i x : Nat}
    (hx : (ρ.getD i default).holds x = true) : la.holds x = false ∧ lc.slot? ≠ some x := by
  have := G.slots.holds i x hx
  constructor
  · rcases G.laOk with e' | ⟨_, e'⟩ <;> rw [e'] <;> simp; omega
  · intro e
    rcases G.lcOk with e' | ⟨-, e'⟩ <;> rw [e'] at e <;> simp at e
    rcases G.laOk with e' | ⟨_, e'⟩ <;> rw [e'] at e <;> simp at e <;> omega

theorem off_le (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) :
    la.off = n := by
  rcases G.laOk with e | ⟨_, e⟩ <;> rw [e] <;> rfl

theorem lc_ge (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {k : Nat}
    (hk : lc.slot? = some k) : FR ≤ k := by
  rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e] at hk <;> simp [Loc.slot?] at hk; omega

theorem la_ge (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {x : Nat}
    (hk : la.holds x = true) : FR ≤ x := by
  rcases G.laOk with e | ⟨_, e⟩ <;> rw [e] at hk <;> simp at hk; omega

/-- The counter's slot is held by the counter variable. -/
theorem lc_holds (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {k : Nat}
    (hk : lc.slot? = some k) : lc.holds k = true := by
  rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e] at hk ⊢ <;> simp [show Ty.u64.slotN = 1 from rfl] at hk ⊢; omega

/-- The counter's slot is not the accumulator's. -/
theorem lc_ne_la (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {k : Nat}
    (hk : lc.slot? = some k) : la.holds k = false := by
  rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e] at hk <;> simp at hk
  rcases G.laOk with e' | ⟨_, e'⟩ <;> rw [e'] <;> simp [e', Loc.nw] at hk ⊢; omega

theorem la_ne_lc (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {x : Nat}
    (hx : la.holds x = true) : lc.slot? ≠ some x := fun e => by
  rw [G.lc_ne_la e] at hx; cases hx

/-- Once the counter variable holds the counter, the frame and the memory relate both loop
variables. -/
theorem rels (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {i : Nat}
    {st : t.carrier} {f : Frame} {h : Heap} (hfe : FEnvRel f (E st) ρ) (henv : MEnvRel h bp (E st) ρ S)
    (hcnt : CntAt lc bp a f h i) (hacc : AccAt s la bp f h (fst st))
    (hcv : lc = .own (a + 8) → Data.reprBytes (UInt64.ofNat i) (rd h (bp + (a + 8)) 8)) :
    FEnvRel f (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) ∧
      MEnvRel h bp (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) (loopS bp a n S) := by
  have hp1 : PtrOk h bp lc ⟨bp + (a + 8), none, none, none⟩ := by
    rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e] <;> trivial
  have hp2 : PtrOk h bp la ⟨bp + n, none, none, none⟩ := by
    rcases G.laOk with e | ⟨_, e⟩ <;> rw [e] <;> trivial
  refine ⟨⟨?_, ?_, hfe⟩, ⟨fun hc => ?_, hp1, fun ha => ?_, hp2, henv⟩⟩
  · rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e]
    · trivial
    · exact ⟨by simp only [slotsIn_cons]; omega, rfl, rfl, (wordsRel_one rfl).2 (by
        simp only [CntAt, e] at hcnt; rw [hcnt]; exact wordRel_u64 _)⟩
  · rcases G.laOk with e | ⟨hts, e⟩ <;> rw [e]
    · trivial
    · rw [e] at hacc; exact ⟨by omega, hts, rfl, hacc.2⟩
  · rcases G.lcOk with e | ⟨-, e⟩
    · exact VarRel.of_exact (hcv e)
    · rw [e] at hc; exfalso; rcases hc with hc | hc
      · simp at hc
      · exact absurd hc (by decide)
  · rcases G.laOk with e | ⟨hts, e⟩
    · rw [e] at hacc; exact VarRel.of_exact hacc
    · rw [e] at ha; simp [Loc.isSlot, hts] at ha

/-- From the loop head with counter `i < N` to the condition: the counter variable holds the
counter, and the memory and the frame represent the iteration's environment. -/
theorem enter (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {i : Nat}
    {st : t.carrier} {f : Frame} {h : Heap} {w : World} {clk : Nat} {K : List Kont}
    (hw : w.halted = false) (hf : f BP = UInt64.ofNat bp) (hfe : FEnvRel f (E st) ρ)
    (henv : MEnvRel h bp (E st) ρ S) (hcnt : CntAt lc bp a f h i)
    (hacc : AccAt s la bp f h (fst st)) (hi : i < N) :
    ∃ f₃ h₃, f₃ BP = f BP ∧ (∀ x, FR ≤ x → f₃ x = f x) ∧
      (∀ x, x < bp + (a + 8) → h₃ (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      CntAt lc bp a f₃ h₃ i ∧ AccAt s la bp f₃ h₃ (fst st) ∧
      FEnvRel f₃ (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) ∧
      MEnvRel h₃ bp (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) (loopS bp a n S) ∧
      ReachL κ ω L ⟨.while (loopPreG N a lc la c tmc ρ) (.slot RX) (loopBodyG a lc la body tmb ρ), K,
          f, h, w, clk⟩
        ⟨lowerM c tmc (loopρ lc la ρ) (a + 17 + s.size) (a + 16),
          .seq (loopTestM s a tmc) :: .loop (loopPreG N a lc la c tmc ρ) (.slot RX)
            (loopBodyG a lc la body tmb ρ) :: K, f₃, h₃, w, clk⟩ := by
  have := G.room; have := G.size; have := G.na
  have hH := G.off_le
  have hr₁ := cnt_test (κ := κ) (ω := ω) (L := L) G.lcOk hf hcnt G.hN (by omega) (by omega)
    (by omega)
  have hx1 : (f.set RX (if i < N then 1 else 0)) RX = 1 := by simp [Frame.set, hi]
  have hfx : (f.set RX (if i < N then 1 else 0)) BP = UInt64.ofNat bp := by
    rw [Frame.set_ne _ _ (by decide)]; exact hf
  have hkx : ∀ x, FR ≤ x → (f.set RX (if i < N then 1 else 0)) x = f x :=
    Frame.set_keep f _ (by decide)
  obtain ⟨f₃, h₃, hr₂, hf₃, hout, hcnt₃, hcv⟩ := cnt_enter (κ := κ) (ω := ω) (L := L) G.lcOk hfx
    (hcnt.congr (fun _ _ => rfl) fun k hk => hkx k (G.lc_ge hk)) (by omega) (by omega)
  have hk₃ : ∀ x, FR ≤ x → f₃ x = f x := fun x hx => (hr₂.keep x hx).trans (hkx x hx)
  have hacc₃ : AccAt s la bp f₃ h₃ (fst st) :=
    hacc.congr (fun j hj => hout _ (by omega) (by unfold InR; omega)) fun x hx => hk₃ x (G.la_ge hx)
  have henv₃ : MEnvRel h₃ bp (E st) ρ S := henv.above G.lay fun x hx => hout x (by omega)
    (by unfold InR; omega)
  obtain ⟨hfe₃, hme₃⟩ := G.rels (hfe.keep hk₃) henv₃ hcnt₃ hacc₃ hcv
  refine ⟨f₃, h₃, hf₃.trans (Frame.set_ne _ _ (by decide)), hk₃,
    fun x hx => hout x (by omega) (by unfold InR; omega), hcnt₃, hacc₃, hfe₃, hme₃, ?_⟩
  apply ReachL.step' hw; simp only [exec1]
  refine (ReachL.seq_reach hw hr₁.run).trans ?_
  apply ReachL.step' hw
  simp only [exec1, eval_slot, hx1, show ((1 : UInt64) = 0) = False by decide, ite_false]
  refine (ReachL.seq_reach hw hr₂.run).trans ?_
  apply ReachL.step' hw; simp only [exec1]; exact ReachL.refl _

/-- One iteration after the condition held: the body, the new accumulator and the increment, and
then the loop head with the next counter. -/
theorem iter (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {κi : CostModel}
    {K : List Kont} {mm i : Nat}
    (ih : LoopAt κ ω L κi N c body fst E tmc tmb lc la bp n a ρ S Wb K mm (i + 1)) {st : t.carrier}
    {f : Frame} {h : Heap} {w : World} {clk : Nat} (hw : w.halted = false)
    (hf : f BP = UInt64.ofNat bp)
    (hfe : FEnvRel f (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ))
    (henv : MEnvRel h bp (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) (loopS bp a n S))
    (hcnt : CntAt lc bp a f h i)
    (hsb : body.safe ω (loopEnv fst E (UInt64.ofNat i) st) w)
    (hsr : loopSafe (fun i st w => c.safe ω (loopEnv fst E i st) w)
      (fun i st w => body.safe ω (loopEnv fst E i st) w)
      (fun i st w => c.denote ω (loopEnv fst E i st) w)
      (fun i st w => body.denote ω (loopEnv fst E i st) w) mm (i + 1)
      (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
      (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world) :
    MSim κ ω L ⟨lowerM body tmb (loopρ lc la ρ) (a + 17 + s.size) (a + 17),
        .seq (loopNextM s a lc la tmb) :: .seq (.while (loopPreG N a lc la c tmc ρ) (.slot RX)
          (loopBodyG a lc la body tmb ρ)) :: K, f, h, w, clk⟩ K
      (LoopPost s la bp ρ S fst E)
      (Prot bp n n s.size Γ S Wb)
      ⟨(loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
          (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).val,
        (loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
          (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).world,
        (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).steps +
        (loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
          (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
          (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).steps⟩ (SProt ρ Wb) := by
  have := G.room; have := G.size; have := G.na; have hH := G.off_le
  refine MSim.bindKF (G.bodyS _ st f h w _ clk hf hfe henv hsb hw)
    (fun hh' => loopExec_halted κi _ _ (fun _ _ _ h => exec_halted ω κ c _ _ h)
      (fun _ _ _ h => exec_halted ω κ body _ _ h) _ _ _ _ hh')
    (fun x hx => ⟨loop_prot wc true (by have := hx.1; omega) hx.2.1 hx.2.2
      (by have := hx.1; omega) (by omega), hx⟩) (fun x hx => ⟨(hx.push _ _).push _ _, hx⟩)
    fun f₆ m₆ hf₆ hfk₆ hv₆ hm₆ hh₆ => ?_
  simp only at hf₆ hm₆ hfk₆
  obtain ⟨hacc₆, henv₆, hfe₆⟩ := G.step _ st w f f₆ h m₆ henv.2.2.2.2 hfe.2.2 hsb hv₆ hm₆ hfk₆
  have hcnt₆ : CntAt lc bp a f₆ m₆ i := hcnt.congr
    (fun j hj => hm₆ _ (loop_prot wc true (by omega) (by unfold InR; omega)
      (fun h2 => by have := InW.lt G.lay h2; omega) (by omega) (by omega)))
    fun k hk => hfk₆ k (G.lc_ge hk) ⟨0, G.lc_holds hk, by
      rcases G.lcOk with e | ⟨-, e⟩ <;> rw [e] at hk <;> simp [Loc.slot?] at hk
      simp [G.wcOk (by rw [e]; rfl)]⟩
  obtain ⟨f₇, m₇, hr₇, hf₇, hk₇, hm₇, hacc₇⟩ := acc_next (κ := κ) (ω := ω) (L := L)
    (v := fst (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val) G.laOk G.lbOk (by omega) G.na
    (hf₆.trans hf) hacc₆ G.room G.size
  have hcnt₇ : CntAt lc bp a f₇ m₇ i := hcnt₆.congr
    (fun j hj => hm₇ _ (by omega) (by unfold InR; omega))
    fun k hk => hk₇ k (G.lc_ge hk) (G.lc_ne_la hk)
  obtain ⟨f₈, m₈, hr₈, hf₈, hk₈, hm₈, hcnt₈⟩ := cnt_next (κ := κ) (ω := ω) (L := L) G.lcOk
    (by simp only [slotsIn_cons]; omega) (hf₇.trans (hf₆.trans hf)) hcnt₇ (by omega) (by omega)
  have hacc₈ := hacc₇.congr (fun j hj => hm₈ _ (by omega) (by unfold InR; omega))
    fun x hx => hk₈ x (G.la_ge hx) (G.la_ne_lc hx)
  have hfρ₈ : ∀ i' x, (ρ.getD i' default).holds x = true → f₈ x = f₆ x := fun i' x hx => by
    have hne := G.slot_ne hx
    have hge := (G.slots.holds i' x hx).1
    rw [hk₈ x hge hne.2, hk₇ x hge hne.1]
  have hm₈₆ : ∀ x, x < bp + n → ¬ InR (bp + n) s.size x →
      m₈ (UInt64.ofNat x) = m₆ (UInt64.ofNat x) := fun x hx hn => by
    rw [hm₈ x (by omega) (by unfold InR; omega), hm₇ x (by omega) hn]
  exact MSim.reach_k hh₆ (Reaches.seq hr₇ hr₈) (hf₈.trans hf₇)
    (fun x hx => hm₈₆ x hx.1 hx.2.1)
    (fun x hx hp => by
      have hp' := (hp.push la true).push lc wc
      obtain ⟨i', hi', _⟩ := hp
      rw [hfρ₈ i' x hi', hfk₆ x hx hp'])
    (ih _ f₈ m₈ _ _ (hf₈.trans (hf₇.trans (hf₆.trans hf))) (hfe₆.congr hfρ₈)
      (henv₆.congr fun x hx => hm₈₆ x (by have := G.lay.vis_lt hx; omega)
        fun h1 => (G.lay.away (o := n) (sz := s.size) (Nat.le_refl _)).not_vis h1 hx)
      hcnt₈ hacc₈ hh₆ hsr)

/-- After the condition, with its value `b` in its byte, either leave the loop or run the body. -/
theorem test (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {κi : CostModel}
    {K : List Kont} {mm i : Nat}
    (ih : LoopAt κ ω L κi N c body fst E tmc tmb lc la bp n a ρ S Wb K mm (i + 1)) {st : t.carrier}
    {b : Bool} {f : Frame} {h : Heap} {w : World} {clk : Nat} (hw : w.halted = false)
    (hf : f BP = UInt64.ofNat bp)
    (hfe : FEnvRel f (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ))
    (hv : TQ tmc bp (a + 16) (loopρ lc la ρ) (loopS bp a n S) .bool b f h)
    (henv : MEnvRel h bp (loopEnv fst E (UInt64.ofNat i) st) (loopρ lc la ρ) (loopS bp a n S))
    (hcnt : CntAt lc bp a f h i) (hacc : AccAt s la bp f h (fst st))
    (hsafe : b = true → body.safe ω (loopEnv fst E (UInt64.ofNat i) st) w ∧
      loopSafe (fun i st w => c.safe ω (loopEnv fst E i st) w)
        (fun i st w => body.safe ω (loopEnv fst E i st) w)
        (fun i st w => c.denote ω (loopEnv fst E i st) w)
        (fun i st w => body.denote ω (loopEnv fst E i st) w) mm (i + 1)
        (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
        (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world) :
    MSim κ ω L ⟨loopTestM s a tmc, .loop (loopPreG N a lc la c tmc ρ) (.slot RX)
        (loopBodyG a lc la body tmb ρ) :: K, f, h, w, clk⟩ K
      (LoopPost s la bp ρ S fst E)
      (Prot bp n n s.size Γ S Wb)
      (if b then
        ⟨(loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
            (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).val,
          (loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
            (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).world,
          (Tick.iter (width s)).cost κ + (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).steps +
          (loopExec κi (fun i st w => c.exec ω κ .copy (loopEnv fst E i st) w)
            (fun i st w => body.exec ω κ tmb.hb (loopEnv fst E i st) w) mm (i + 1)
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).val
            (body.exec ω κ tmb.hb (loopEnv fst E (UInt64.ofNat i) st) w).world).steps⟩
      else ⟨st, w, (Tick.iter (width s)).cost κ⟩) (SProt ρ Wb) := by
  have := G.room; have := G.size; have := G.na
  have hf₅ : (f.set RX (bword b)) BP = UInt64.ofNat bp := by
    simp only [Frame.set, show (BP = RX) = False by decide, ite_false]; exact hf
  have hk₅ := Frame.set_keep f (bword b) (show RX < FR by decide)
  have hl8 : Runs κ ω L (flagLoad tmc a) f h (f.set RX (bword b)) h := by
    rcases G.tmcOk with rfl | ⟨T, rfl⟩
    · have hcb : h (UInt64.ofNat (bp + (a + 16))) = UInt8.ofNat ((if b then 1 else 0) % 256) := by
        obtain ⟨_, hv⟩ := hv
        have hv' : rd h (bp + (a + 16)) 1 = natBytes 1 (if b then 1 else 0) := hv
        simpa [rd, natBytes] using hv'
      exact Runs.congr (Runs.load _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega) (by omega)
        hf)) (by simp only [eval_slot, hf, ofNat_add_ofNat, Heap.load, hcb]; cases b <;> rfl) rfl
    · exact Runs.congr (Runs.mov _ _ _ _) (by
        rw [eval_slot, word_bool ((wordsRel_one rfl).1 hv)]) rfl
  cases b with
  | false =>
    have hx0 : (f.set RX (bword false)) RX = 0 := by simp [bword]
    exact ⟨⟨.skip, K, f.set RX (bword false), h, w, clk + (Tick.iter (width s)).cost κ⟩,
      ReachL.loopTest_false hw hl8 hx0, rfl, by simp, Or.inr ⟨rfl, rfl, by simp, hf₅.trans hf.symm,
        ⟨hacc.congr (fun _ _ => rfl) fun x hx => hk₅ x (G.la_ge hx), henv.2.2.2.2,
          hfe.2.2.keep hk₅⟩, fun _ _ => rfl, fun x hx _ => hk₅ x hx⟩⟩
  | true =>
    have hx1 : (f.set RX (bword true)) RX ≠ 0 := by simp [bword]
    obtain ⟨hsb, hsr⟩ := hsafe rfl
    exact (MSim.pre (ReachL.loopTest_true hw hl8 hx1) rfl (hf₅.trans hf.symm) (fun _ _ => rfl)
      (fun x hx _ => hk₅ x hx)
      (G.iter ih hw hf₅ (hfe.keep hk₅) henv
        (hcnt.congr (fun _ _ => rfl) fun k hk => hk₅ k (G.lc_ge hk)) hsb hsr)).of_eq rfl rfl
      (by simp; omega)

/-- One more iteration at the loop head. -/
theorem succ (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) {κi : CostModel}
    (hκi : κi.iter = κ.iter + width s * κ.word) {K : List Kont} {mm i : Nat} (hi : i < N)
    (ih : LoopAt κ ω L κi N c body fst E tmc tmb lc la bp n a ρ S Wb K mm (i + 1)) :
    LoopAt κ ω L κi N c body fst E tmc tmb lc la bp n a ρ S Wb K (mm + 1) i := by
  intro st f hh wd clk hf hfe henv hcnt hacc hwd hsafe
  have := G.room; have := G.size; have := G.na; have hH := G.off_le
  obtain ⟨f₃, h₃, hf₃, hk₃, hout, hcnt₃, hacc₃, hfe₃, henv₃, hhead⟩ :=
    G.enter (K := K) (clk := clk) hwd hf hfe henv hcnt hacc hi
  have hC := G.condS _ st f₃ h₃ wd (.seq (loopTestM s a tmc) :: .loop (loopPreG N a lc la c tmc ρ) (.slot RX)
    (loopBodyG a lc la body tmb ρ) :: K) clk (hf₃.trans hf) hfe₃ henv₃ hsafe.1 hwd
  generalize hCV : c.exec ω κ .copy (loopEnv fst E (UInt64.ofNat i) st) wd = rc at hC
  have hsafe₂ := hsafe.2
  simp only [← Exp.exec_val ω κ (hb := .copy) c, ← Exp.exec_world ω κ (hb := .copy) c, hCV,
    ← Exp.exec_val ω κ (hb := tmb.hb) body, ← Exp.exec_world ω κ (hb := tmb.hb) body] at hsafe₂
  have hds : Tl.dsz .bool tmc ≤ 1 := by
    rcases G.tmcOk with rfl | ⟨T, rfl⟩
    · exact Nat.le_of_eq (show Ty.bool.size = 1 from rfl)
    · exact Nat.zero_le _
  have hW0 : ∀ j, (false :: false :: noW W).getD j false = false := fun j => by
    match j with
    | 0 | 1 => rfl
    | j + 2 => simp only [List.getD_cons_succ, noW_getD]
  refine (MSim.pre (δ := 0) hhead rfl hf₃ (fun x hx => hout x (by have := hx.1; omega))
    (fun x hx _ => hk₃ x hx)
    (MSim.bindKF hC ?_ (fun x hx => ⟨loop_prot false false (by have := hx.1; omega) hx.2.1 InW.noW
      (by have := hx.1; omega) (by omega), hx⟩) (fun x hx => ⟨(hx.noW.push _ _).push _ _, hx⟩)
      fun f₄ m₄ hf₄ hfk₄ hv₄ hm₄ hh₄ => by
      have hk₄ : ∀ i' x, ((loopρ lc la ρ).getD i' default).holds x = true → f₄ x = f₃ x :=
        fun i' x hx => hfk₄ x (hfe₃.ge i' x hx) ⟨i', hx, hW0 i'⟩
      have hm₄' : ∀ x, x < bp + (a + 16) → m₄ (UInt64.ofNat x) = h₃ (UInt64.ofNat x) :=
        fun x hx => hm₄ x ⟨by omega, by unfold InR; omega, InW.noW (W := true :: true :: W)⟩
      exact G.test ih hh₄ (hf₄.trans (hf₃.trans hf)) (hfe₃.congr hk₄) hv₄
        (henv₃.of_prot (W := true :: true :: W) (loop_lay G.lay G.lcOk G.laOk G.na false false
          (m := a + 17 + s.size) (by omega))
          ((loop_lay G.lay G.lcOk G.laOk G.na false false (Nat.le_refl _)).away (Nat.le_refl _)) hm₄)
        (hcnt₃.congr (fun j hj => hm₄' _ (by omega)) fun k hk => hk₄ 0 k (G.lc_holds hk))
        (hacc₃.congr (fun j hj => hm₄ _ ⟨by omega, by
          unfold InR; omega,
          InW.noW (W := true :: true :: W)⟩) fun x hx => hk₄ 1 x hx)
        hsafe₂)).of_eq ?_ ?_ ?_
  · intro hh'; split
    · have hb' := exec_halted ω κ (hb := tmb.hb) body (loopEnv fst E (UInt64.ofNat i) st) _ hh'
      rw [loopExec_halted κi _ _ (fun _ _ _ h => exec_halted ω κ c _ _ h)
        (fun _ _ _ h => exec_halted ω κ body _ _ h) _ _ _ _ (by rw [hb']; exact hh'), hb']
    · rfl
  all_goals cases hcv : rc.val <;> simp [loopExec, hcv, hCV, Tick.cost, hκi] <;> omega

/-- The loop invariant at the loop head, by induction on the remaining iterations. -/
theorem head (G : LoopG κ ω L N c body fst E tmc tmb lc la wc bp n a ρ S W Wb) (κi : CostModel)
    (hκi : κi.iter = κ.iter + width s * κ.word) (K : List Kont) :
    ∀ mm i, i + mm = N → LoopAt κ ω L κi N c body fst E tmc tmb lc la bp n a ρ S Wb K mm i := by
  intro mm
  induction mm with
  | zero =>
    intro i hi st f hh wd clk hf hfe henv hcnt hacc hwd _
    have := G.room; have := G.size; have := G.na
    have hr₁ := cnt_test (κ := κ) (ω := ω) (L := L) G.lcOk hf hcnt G.hN (by omega) (by omega)
      (by omega)
    have hx0 : (f.set RX (if i < N then 1 else 0)) RX = 0 := by simp [Frame.set]; omega
    have hpre := Runs.seq hr₁ (Runs.ite_false (c := .slot RX) (e := .skip)
      (t := .seq (cntEnter lc a) (.seq (lowerM c tmc (loopρ lc la ρ) (a + 17 + s.size) (a + 16))
        (loopTestM s a tmc)))
      (by simpa using hx0) (Runs.skip _ _))
    exact ⟨⟨.skip, K, _, hh, wd, clk⟩, ReachL.while_exit hwd hpre.run (by simpa using hx0),
      rfl, by simp [loopExec], Or.inr ⟨rfl, rfl, by simp [loopExec],
        by simp only; exact Frame.set_ne _ _ (by decide),
        by simp only [loopExec]; exact ⟨hacc.congr (fun _ _ => rfl) fun x hx =>
          hpre.keep x (G.la_ge hx), henv, hfe.keep hpre.keep⟩, fun _ _ => rfl,
        fun x hx _ => hpre.keep x hx⟩⟩
  | succ mm ih => exact fun i hi => G.succ hκi (by omega) (ih (i + 1) (by omega))

end LoopG

end

/-! ## Positions and the carried storage -/

/-- `a` is in the storage of the variable at position `j`. -/
def InAt : List Ty → List SI → Nat → Nat → Prop
  | t :: _, s :: _, 0, a => s.In t a
  | _ :: ts, _ :: S, j + 1, a => InAt ts S j a
  | _, _, _, _ => False

theorem InAt.mem {a : Nat} : ∀ {t : Ty} {Γ : List Ty} {S : List SI} (m : Mem t Γ),
    S.length = Γ.length →
    (InAt Γ S m.idx a ↔ (S.getD m.idx default).In t a)
  | _, _ :: _, _ :: _, .here, _ => Iff.rfl
  | _, _ :: _, _ :: _, .there m, h => by
    simpa [InAt, Mem.idx] using InAt.mem m (by simpa using h)
  | _, _ :: _, [], _, h => by simp at h

theorem InW.iff {a : Nat} : ∀ {Γ : List Ty} {S : List SI} {W : List Bool},
    InW Γ S W a ↔ ∃ j, W.getD j false = true ∧ InAt Γ S j a
  | [], _, _ => ⟨fun h => h.elim, fun ⟨j, _, h⟩ => by cases j <;> exact h.elim⟩
  | _ :: _, [], _ => ⟨fun h => h.elim, fun ⟨j, _, h⟩ => by cases j <;> exact h.elim⟩
  | t :: ts, s :: S, W => by
    simp only [InW]
    rw [InW.iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨j, h1, h2⟩)
      · exact ⟨0, by rwa [← headD_eq_getD], h2⟩
      · exact ⟨j + 1, by rwa [← tail_getD], h2⟩
    · rintro ⟨j, h1, h2⟩
      cases j with
      | zero => exact Or.inl ⟨by rwa [headD_eq_getD], h2⟩
      | succ j => exact Or.inr ⟨j, by rwa [tail_getD], h2⟩

/-- `a` is in the storage of one of the variables `xs`. -/
def CIn (Γ : List Ty) (S : List SI) (xs : List Nat) (a : Nat) : Prop := ∃ j ∈ xs, InAt Γ S j a

theorem InW.selW {Γ : List Ty} {S : List SI} {W : List Bool} {xs : List Nat} {a : Nat}
    (h : InW Γ S (selW xs 0 W) a) : InW Γ S W a ∧ CIn Γ S xs a := by
  obtain ⟨j, hj, ha⟩ := InW.iff.1 h
  rw [getD_selW, Nat.zero_add] at hj
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hj
  exact ⟨InW.iff.2 ⟨j, hj.1, ha⟩, j, hj.2, ha⟩

/-! ## Fewer writable variables keep the layout -/

section Layout
variable {bp n : Nat}

theorem Single.wle {t : Ty} {l : Loc} {s : SI} {w w' : Bool} (h : Single bp n t l s w)
    (hw : w' = true → w = true) : Single bp n t l s w' :=
  ⟨h.1, h.2.1, fun e => h.2.2.1 (hw e), h.2.2.2⟩

theorem Compat.wle {t t' : Ty} {l l' : Loc} {s s' : SI} {w w' v v' : Bool}
    (h : Compat bp t l s w t' l' s' w') (hv : v = true → w = true) (hv' : v' = true → w' = true) :
    Compat bp t l s v t' l' s' v' :=
  ⟨h.1, h.2.1, h.2.2.1, fun e => h.2.2.2.1 (hv e), fun e => h.2.2.2.2 (hv' e)⟩

theorem CompatAll.wle {t : Ty} {l : Loc} {s : SI} {w v : Bool} (hv : v = true → w = true) :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W W' : List Bool},
    (∀ i, W'.getD i false = true → W.getD i false = true) →
    CompatAll bp t l s w ts ρ S W → CompatAll bp t l s v ts ρ S W'
  | _ :: _, _ :: _, _ :: _, W, W', hW, h => by
    refine ⟨h.1.wle hv (fun e => ?_), CompatAll.wle hv (fun i hi => ?_) h.2⟩
    · rw [headD_eq_getD] at e ⊢; exact hW 0 e
    · rw [tail_getD] at hi ⊢; exact hW _ hi
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _, _ => trivial

/-- Fewer writable variables keep the layout. -/
theorem Lay.wle : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {W W' : List Bool},
    (∀ i, W'.getD i false = true → W.getD i false = true) →
    Lay bp n Γ ρ S W → Lay bp n Γ ρ S W'
  | [], [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, W, W', hW, hl => by
    have h0 : W'.headD false = true → W.headD false = true := fun e => by
      rw [headD_eq_getD] at e ⊢; exact hW 0 e
    have ht : ∀ i, W'.tail.getD i false = true → W.tail.getD i false = true := fun i hi => by
      rw [tail_getD] at hi ⊢; exact hW _ hi
    exact ⟨hl.1.wle h0, hl.2.1.wle h0 ht, Lay.wle ht hl.2.2⟩
  | [], _ :: _, _, _, _, _, hl => hl.elim
  | [], [], _ :: _, _, _, _, hl => hl.elim
  | _ :: _, [], _, _, _, _, hl => hl.elim
  | _ :: _, _ :: _, [], _, _, _, hl => hl.elim

end Layout

/-! ## The memory after an iteration -/

theorem slice_getD_lt (bs : List UInt8) (o l l' i : Nat) (h : i < l) (h' : l ≤ l') :
    (slice bs o l).getD i 0 = (slice bs o l').getD i 0 := by
  simp [slice, List.getD_eq_getElem?_getD, h, show i < l' by omega]

section
variable {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}

/-- After a loop body, the memory and the frame represent the carried variables' handed-back
values. Each carried variable holds its component of the handed-back value, the tuple at offset `b`
of the bytes `BS`, in its storage or its frame slots. Nothing else below the watermark changes, and
no other variable's slot. A carried slice view keeps its occupancy, so it is still a view of its
extent. -/
theorem carry_rel (hl : Lay bp n Γ ρ S W) (hbn : bp + n ≤ UInt64.size) (hok : SlotsOk ρ)
    (m : Heap) (f' : Frame) (BS : List UInt8) :
    ∀ {ts : List Ty} (cs : Carry Γ ts) (b : Nat) (env : Env Γ) (h : Heap) (f : Frame)
      (vs : (Ty.tup ts).carrier),
      cs.distinct = true → (∀ x ∈ cs.idxs, W.getD x false = true) →
      MEnvRel h bp env ρ S → FEnvRel f env ρ →
      Data.reprBytes vs (slice BS b (Ty.tup ts).size) →
      (∀ c ∈ cs.idxs.zip ((tupOffs ts b).zip (ts.map Ty.size)),
        CompAt BS f' m (ρ.getD c.1 default) (S.getD c.1 default) c.2.1 c.2.2) →
      (∀ x ∈ cs.idxs, (S.getD x default).ext ≠ none → (cs.set env vs).occsAt x = env.occsAt x) →
      (∀ a, a < bp + n → ¬ CIn Γ S cs.idxs a → m (UInt64.ofNat a) = h (UInt64.ofNat a)) →
      (∀ i y, (ρ.getD i default).holds y = true → i ∉ cs.idxs → f' y = f y) →
      MEnvRel m bp (cs.set env vs) ρ S ∧ FEnvRel f' (cs.set env vs) ρ
  | _, .nil, _, env, h, f, _, _, _, henv, hfe, _, _, _, hm, hfr =>
    ⟨henv.congr fun x hx => hm x (hl.vis_lt hx) (fun ⟨_, hj, _⟩ => by simp [Carry.idxs] at hj),
      hfe.congr fun i y hy => hfr i y hy (by simp [Carry.idxs])⟩
  | _, .cons (t := t) (ts := ts') x cs, b, env, h, f, vs, hd, hW, henv, hfe, hvs, hc, hx, hm,
      hfr => by
    obtain ⟨v, vs'⟩ := vs
    simp only [Carry.distinct, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hd
    have hlen := Lay.length hl
    -- the components
    have hp := pair_repr (u := t) (t := Ty.tup ts') (v, vs') _ hvs
    rw [slice_slice _ _ _ _ _ (by rw [Nat.zero_add]; exact fst_le t (Ty.tup ts')), Nat.add_zero] at hp
    rw [slice_slice BS b (Ty.tup (t :: ts')).size _ _ (sndOff_add_le t (Ty.tup ts'))] at hp
    simp only [Carry.idxs, tupOffs, List.map_cons, List.zip_cons_cons, List.mem_cons,
      forall_eq_or_imp] at hc
    have hc1 : CompAt BS f' m (ρ.getD x.idx default) (S.getD x.idx default) b t.size := by
      have := hc.1; simp only [List.getD_eq_getElem?_getD] at this ⊢; exact this
    -- the memory with only `x` updated
    let m₁ : Heap := fun y => if (S.getD x.idx default).In t y.toNat then m y else h y
    have hm₁ : ∀ a, a < UInt64.size → m₁ (UInt64.ofNat a) =
        if (S.getD x.idx default).In t a then m (UInt64.ofNat a) else h (UInt64.ofNat a) :=
      fun a ha => by simp only [m₁, UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha]
    have hout : ∀ a, a < bp + n → ¬ (S.getD x.idx default).In t a →
        m₁ (UInt64.ofNat a) = h (UInt64.ofNat a) := fun a ha hn => by
      rw [hm₁ a (by omega), ite_eq_right hn]
    -- `x` is in memory and its storage holds `v`, or in a frame slot that holds `v`'s word
    obtain ⟨f₁, henv₁, hfe₁, hfr₁⟩ : ∃ f₁ : Frame, MEnvRel m₁ bp (env.set x v) ρ S ∧
        FEnvRel f₁ (env.set x v) ρ ∧ ∀ i y, (ρ.getD i default).holds y = true → i ∉ cs.idxs →
          f' y = f₁ y := by
      cases hk : (ρ.getD x.idx default).slot? with
      | none =>
        replace hc1 := (CompAt.mem hk).1 hc1
        have hvr : VarRel m₁ t v (S.getD x.idx default) := by
          refine ⟨slice BS b t.size, hp.1, fun i hi _ => ?_, fun e he hsn => ?_⟩
          · have hi' : i < (S.getD x.idx default).lim t.size := hi
            have hin : (S.getD x.idx default).In t ((S.getD x.idx default).at i) := SI.In_at hi
            have hlt := (hl.var x).lt hin
            rw [hm₁ _ (by omega), ite_eq_left hin, ← rdS_getD m _ _ i hi', ← hc1]
            exact slice_getD_lt _ _ _ _ _ hi (SI.lim_le _ _)
          · have hocc := hx x.idx (by simp [Carry.idxs]) (by rw [he]; nofun)
            simp only [Carry.set] at hocc
            rw [Carry.set_occsAt_ne cs hd.1, Env.occsAt_set_same, Env.occsAt_get] at hocc
            obtain ⟨_, _, _, hvx⟩ :=
              (henv.get x ((hl.var x).ns_of_ext (Or.inl (by rw [he]; nofun)))).1
            exact ViewOK.of_occs (hvx e he hsn) hocc
        refine ⟨f, henv.set_var' x v hl (hW x.idx (by simp [Carry.idxs])) hbn hout fun _ => hvr,
          hfe.env_congr fun m' hm' => Env.get_set_ne env x m' v fun e => ?_,
          fun i k hk' hi => hfr i k hk' ?_⟩
        · rw [e, Loc.isSlot, hk] at hm'; cases hm'
        · intro hm'
          simp only [Carry.idxs, List.mem_cons] at hm'
          rcases hm' with e | e
          · rw [e, Loc.holds_of_isSlot (by unfold Loc.isSlot; rw [hk]; rfl)] at hk'; cases hk'
          · exact hi e
      | some k =>
        obtain ⟨hts, hnw, -⟩ := hfe.get x hk
        let f₁ : Frame := fun y => if (ρ.getD x.idx default).holds y then f' y else f y
        have hw : WordsRel t v f₁ k := ⟨_, hp.1, by
          unfold CompAt at hc1; rw [hk, hnw] at hc1
          exact hc1.congr fun y h1 h2 => by
            simp only [f₁, Loc.holds_iff.2 ⟨k, hk, h1, by rw [hnw]; exact h2⟩, ↓reduceIte]⟩
        refine ⟨f₁, henv.set_var' x v hl (hW x.idx (by simp [Carry.idxs])) hbn hout
          fun h' => ?_, FEnvRel.set_slots x v hok hk hw (fun y _ hy => by simp only [f₁, hy]; rfl)
            hfe, fun i y hy hi => ?_⟩
        · unfold Loc.isSlot at h'; rw [hk, hts] at h'; simp at h'
        · by_cases hix : i = x.idx
          · subst hix; simp only [f₁, hy, ↓reduceIte]
          · have hxy : (ρ.getD x.idx default).holds y = false := by
              cases e : (ρ.getD x.idx default).holds y
              · rfl
              · exact absurd (hok.inj hy e) hix
            simp only [f₁, hxy]
            exact hfr i y hy (by simp [Carry.idxs, hi, hix])
    have := carry_rel hl hbn hok m f' BS cs
      (b + fieldOff (Data.shape (t.carrier × (Ty.tup ts').carrier)) 1) (env.set x v) m₁ f₁ vs' hd.2
      (fun y hy => hW y (by simp [Carry.idxs, hy])) henv₁ hfe₁ hp.2 hc.2
      (fun y hy hy' => by
        have := hx y (by simp [Carry.idxs, hy]) hy'
        simp only [Carry.set] at this
        rw [this]
        exact (Env.occsAt_set_ne env x v y (fun e => hd.1 (e ▸ hy))).symm)
      (fun a ha hn => by
        rw [hm₁ a (by omega)]
        split
        · rfl
        · rename_i hin
          refine hm a ha fun ⟨j, hj, hja⟩ => ?_
          simp only [Carry.idxs, List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact hin ((InAt.mem x hlen.2).1 hja)
          · exact hn ⟨j, hj, hja⟩)
      hfr₁
    simpa only [Carry.set] using this

end

/-! ## The loop -/

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- The facts about slot-resident variables inside a loop's condition, or inside its body in a tail
mode that hands back nothing whole. The counter's variable and the accumulator are slot-resident
only where the term does not address them. -/
theorem SlotHyp.loop {Γ ts : List Ty} {s u t' : Ty} {N : Nat} {cs : Carry Γ ts} {init : Atom Γ s}
    {c : Exp (.u64 :: s :: Γ) .bool} {body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))}
    {k : Exp (s :: Γ) u} {tm : Tl} {ρ : List Loc} {env : Env Γ} {f₀ : Frame}
    (H : SlotHyp (.loop N cs init c body k) tm ρ env f₀) {e' : Exp (.u64 :: s :: Γ) t'} {tm' : Tl}
    (htm : tm'.vars = [])
    (hna : ∀ i, (Exp.loop N cs init c body k).noAddr i = true → e'.noAddr (i + 2) = true)
    {lc la : Loc} (hla : ∀ k, la.slot? = some k → k = FR + slotsIn ρ)
    (hlc : ∀ k, lc.slot? = some k → k = FR + slotsIn (la :: ρ))
    (h0 : lc.isSlot = true → e'.noAddr 0 = true) (h1 : la.isSlot = true → e'.noAddr 1 = true)
    {f : Frame} {env₂ : Env (.u64 :: s :: Γ)} (hfe : FEnvRel f env₂ (lc :: la :: ρ)) :
    SlotHyp e' tm' (lc :: la :: ρ) env₂ f := by
  refine ⟨⟨hlc, hla, H.ok⟩, hfe, fun i hi => ⟨?_, by rw [htm]; exact List.not_mem_nil⟩⟩
  match i, hi with
  | 0, hi => exact h0 (by simpa using hi)
  | 1, hi => exact h1 (by simpa using hi)
  | i + 2, hi => exact hna i (H.na i (by simpa using hi)).1

theorem loopTl_ok {Γ ts : List Ty} {s : Ty} (cs : Carry Γ ts) {W : List Bool}
    (hW : ∀ x ∈ cs.idxs, W.getD x false = true) (b₁ b₂ : Bool) (ρ : List Loc) :
    (loopTl s cs).Ok (b₁ :: b₂ :: selW cs.idxs 0 W) ρ := by
  intro c hc
  obtain ⟨x, hx, e⟩ := List.mem_map.1 (List.of_mem_zip hc).1
  rw [← e, List.getD_cons_succ, List.getD_cons_succ, getD_selW, Nat.zero_add]
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq]; exact ⟨hW x hx, hx⟩

theorem accLoc_ok {Γ : List Ty} {s t u : Ty} {c : Exp (.u64 :: s :: Γ) .bool}
    {body : Exp (.u64 :: s :: Γ) t} {k : Exp (s :: Γ) u} (ρ : List Loc) (n : Nat) :
    AccLoc s (accLoc (Exp.accSlot c body k) ρ n s.slotN) n (FR + slotsIn ρ) := by
  unfold accLoc; split
  · rename_i h; simp only [Exp.accSlot, Bool.and_eq_true] at h; exact Or.inr ⟨h.1.1.1, rfl⟩
  · exact Or.inl rfl

theorem cntLoc_ok (b : Bool) (ρ : List Loc) (a : Nat) : CntLoc (cntLoc b ρ a) a (FR + slotsIn ρ) := by
  unfold cntLoc; split
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl

/-- Zeroing the counter. -/
theorem cnt_init {lc : Loc} {bp a K : Nat} {f : Frame} {h : Heap} (hlc : CntLoc lc a K)
    (hK : FR ≤ K) (hf : f BP = UInt64.ofNat bp) (hbL : bp + a + 8 ≤ L)
    (hbU : bp + a + 8 ≤ UInt64.size) :
    ∃ f' h', Reaches κ ω L (cntInit lc a) f h f' h' ∧ f' BP = f BP ∧
      (∀ x, FR ≤ x → lc.slot? ≠ some x → f' x = f x) ∧
      (∀ x, x < UInt64.size → ¬ InR (bp + a) 8 x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      CntAt lc bp a f' h' 0 := by
  have hKBP : BP ≠ K := by simp only [FR, BP] at hK ⊢; omega
  rcases hlc with rfl | ⟨-, rfl⟩
  · have hst : Runs κ ω L (.store .w64 (.slot BP) (UInt64.ofNat a) (.imm 0)) f h f
        (wr h (bp + a) (natBytes 8 (UInt64.ofNat 0).toNat)) :=
      Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (by simp only [Width.bytes]; omega) (by omega) hf))
        rfl (by simp only [eval_slot, eval_imm, hf, ofNat_add_ofNat]; rw [store64_eq]; rfl)
    refine ⟨f, _, hst.run, rfl, fun _ _ _ => rfl,
      fun x hx hn => wr_out (by simp; omega) hx (by simp; unfold InR at hn; omega), ?_⟩
    show rd _ (bp + a) 8 = _
    have := rd_wr h (bp + a) (natBytes 8 (UInt64.ofNat 0).toNat) (by simp; omega)
    rwa [natBytes_length] at this
  · exact ⟨f.set K 0, h, Reaches.congr (Reaches.mov _ _ _ _) rfl rfl, Frame.set_ne _ _ hKBP,
      fun x _ hx => Frame.set_ne _ _ (fun e => hx (by rw [e]; rfl)), fun _ _ _ => rfl,
      by simp [CntAt, Frame.set]⟩

/-- The initial accumulator: the atom's bytes at the accumulator's offset `n`, or its words in the
accumulator's slots. Only the accumulator and the scratch slots change. -/
theorem acc_init {Γ : List Ty} {s : Ty} (init : Atom Γ s) {la : Loc} {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp K : Nat} {env : Env Γ} {f : Frame} {h : Heap} (hla : AccLoc s la n K)
    (hK : FR + slotsIn ρ ≤ K) (hok : SlotsOk ρ) (hl : Lay bp n Γ ρ S W) (hbn : bp + n + s.size ≤ UInt64.size)
    (hbL : bp + n + s.size ≤ L) (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ) (hnh : ∀ m, init = .var m → (S.getD m.idx default).hole = none)
    (hne : ∀ m, init = .var m → (S.getD m.idx default).ext = none) :
    ∃ f' h', Reaches κ ω L (accInit la init ρ) f h f' h' ∧ f' BP = f BP ∧
      (∀ x, FR ≤ x → la.holds x = false → f' x = f x) ∧
      (∀ x, x < UInt64.size → ¬ InR (bp + n) s.size x → h' (UInt64.ofNat x) = h (UInt64.ofNat x)) ∧
      AccAt s la bp f' h' (init.denote env) := by
  have hKBP : BP ≠ K := by simp only [FR, BP] at hK ⊢; omega
  rcases hla with rfl | ⟨hts, rfl⟩
  · obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) init (d := n) hl
      (hl.away (Nat.le_refl _)) (by omega) (by omega) hf henv hfe hnh (by omega) (by omega) hne
    refine ⟨f₁, _, hr₁.run, hf₁ BP (by decide) (by decide), fun x hx _ => hr₁.keep x hx,
      fun x hx hn => wr_out (by omega) hx (by rw [hBl]; unfold InR at hn; omega), ?_⟩
    show Data.reprBytes _ (rd (wr h (bp + n) B) (bp + n) s.size)
    have := rd_wr h (bp + n) B (by omega)
    rw [hBl] at this; rw [this]; exact hBr
  · obtain ⟨f', hr, hfb, hout, hw⟩ := atomSlots_reach (κ := κ) (ω := ω) (L := L) init K hts hf
      henv hfe hl hnh hne (by omega) (by omega) (by simp only [FR, RP] at hK ⊢; omega) fun m k' _ hk' => Or.inr (by
        have := hok.range m.idx k' hk'
        obtain ⟨_, hn, _⟩ := hfe.get m hk'
        omega)
    exact ⟨f', h, hr, hfb, fun x hx hx' => hout x hx (by
        have := Loc.holds_false (l := .slot n K s.slotN) rfl hx'; simpa using this),
      fun _ _ _ => rfl, rfl, hw⟩

/-- The tail mode of a loop condition: a slot `T` after the loop variables', or its byte. -/
theorem flagTl_ok {Γ : List Ty} {s : Ty} (c : Exp (.u64 :: s :: Γ) .bool) {ρ' : List Loc}
    {W : List Bool} {S : List SI} (hok : SlotsOk ρ')
    (hV : ∀ i, (S.getD i default).ext ≠ none → c.VSafe (i + 2) .none = true) :
    c.Conf (flagTl c (FR + slotsIn ρ')) = true ∧ (flagTl c (FR + slotsIn ρ')).Ok W ρ' ∧
      (flagTl c (FR + slotsIn ρ')).vars = [] ∧ Tl.dsz .bool (flagTl c (FR + slotsIn ρ')) ≤ 1 ∧
      ∀ i, (S.getD i default).ext ≠ none → c.VSafe (i + 2) (flagTl c (FR + slotsIn ρ')) = true := by
  unfold flagTl; split
  · rename_i hw
    exact ⟨by rw [c.conf_word _ FR]; exact hw, Tl.Ok.word_top _ hok, rfl, Nat.zero_le _,
      fun i hi => by rw [Exp.VSafe_word]; exact hV i hi⟩
  · exact ⟨c.conf_none, trivial, rfl, Nat.le_of_eq rfl, hV⟩

/-- The tail mode of a loop body: into the slots from `T` after the loop variables', or with the
carried variables in place. -/
theorem bodyTl_ok {Γ ts : List Ty} {s u : Ty} (cs : Carry Γ ts) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) {ρ' : List Loc}
    {W : List Bool} {S : List SI} (hS : S.length = Γ.length) (hok : SlotsOk ρ')
    (hCb : body.Conf (loopTl s cs) = true)
    (hW : (loopTl s cs).Ok W ρ')
    (hV : ∀ i, (S.getD i default).ext ≠ none → body.VSafe (i + 2) (loopTl s cs) = true) :
    body.Conf (bodyTl cs c body k (FR + slotsIn ρ')) = true ∧
      (bodyTl cs c body k (FR + slotsIn ρ')).Ok W ρ' ∧
      (bodyTl cs c body k (FR + slotsIn ρ')).vars = [] ∧
      Tl.dsz (.pair s (.tup ts)) (bodyTl cs c body k (FR + slotsIn ρ')) ≤ s.size ∧
      ∀ i, (S.getD i default).ext ≠ none →
        body.VSafe (i + 2) (bodyTl cs c body k (FR + slotsIn ρ')) = true := by
  unfold bodyTl; split
  · rename_i hw
    have hwc : body.Conf (.word (FR + slotsIn ρ')) = true := by
      rw [body.conf_word _ FR]; simp only [Exp.bodyW, Bool.and_eq_true] at hw; exact hw.1.2
    refine ⟨hwc, Tl.Ok.word_top _ hok, rfl, Nat.zero_le _, fun i hi => ?_⟩
    have hi' : i < Γ.length := by
      rw [← hS]; refine Nat.lt_of_not_le fun hge => hi ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    simp only [Exp.bodyW, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true'] at hw
    rw [Exp.VSafe_word]
    obtain ⟨⟨⟨⟨-, hts⟩, -⟩, -⟩, hall⟩ := hw
    simp only [List.isEmpty_iff] at hts; subst hts
    have hcs : loopTl s cs = .split s.size [] := by cases cs; rfl
    exact (hall i hi').resolve_left (by rw [← hcs, hV i hi]; decide)
  · exact ⟨hCb, hW, rfl, Nat.le_refl _, hV⟩

/-- A loop body's value in its tail mode: the new accumulator where `bodyLoc` says, and bytes `bs`
whose tuple at `b` holds the carried variables' handed-back values, each where that variable lives. -/
theorem body_value {Γ ts : List Ty} {s u : Ty} (cs : Carry Γ ts) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) {ρ : List Loc}
    {S : List SI} {bp a n : Nat} {lc la : Loc} {v : (Ty.pair s (.tup ts)).carrier} {f' : Frame}
    {h' : Heap}
    (hv : TQ (bodyTl cs c body k (FR + slotsIn (loopρ lc la ρ))) bp (a + 17) (loopρ lc la ρ)
      (loopS bp a n S) _ v f' h') :
    ∃ (bs : List UInt8) (b : Nat),
      AccAt s (bodyLoc (bodyTl cs c body k (FR + slotsIn (loopρ lc la ρ))) a s.slotN) bp f' h' v.1 ∧ Data.reprBytes v.2 (slice bs b (Ty.tup ts).size) ∧
      ∀ c ∈ cs.idxs.zip ((tupOffs ts b).zip (ts.map Ty.size)),
        CompAt bs f' h' (ρ.getD c.1 default) (S.getD c.1 default) c.2.1 c.2.2 := by
  unfold bodyTl at hv ⊢
  cases hw : Exp.bodyW c body k <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at hv ⊢
  rotate_left
  · -- computed into the slots: no carried variable, the accumulator's words
    simp only [Exp.bodyW, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨⟨-, rfl⟩, hsz⟩, -⟩, -⟩ := hw
    obtain ⟨B, hB, hW⟩ := hv
    have hpr := pair_repr _ B hB
    have hBl := Data.reprBytes_length hB
    have hN : (Ty.pair s (.tup [])).slotN = s.slotN := by unfold Ty.slotN; rw [hsz]
    refine ⟨B, _, ⟨rfl, B, ?_, hN ▸ hW⟩, hpr.2, by simp⟩
    rw [← slice_full B s.size (hBl.trans hsz)]; exact hpr.1
  · -- in memory: the accumulator at `a + 17`, the carried variables in place
    obtain ⟨bs, hbs, hbs0, hbsc⟩ := hv
    have hpr := pair_repr _ bs hbs
    exact ⟨bs, _, show Data.reprBytes _ (rd h' (bp + (a + 17)) s.size) by
      rw [← hbs0]; exact hpr.1, hpr.2, fun c hc => by
      have := hbsc (c.1 + 2, c.2) (by
        simp only [Carry.comps, List.zip_map_left, List.mem_map]; exact ⟨c, hc, rfl⟩)
      simpa only [List.getD_cons_succ] using this⟩

/-- A loop with carried variables is a generic loop `LoopG`. Its state is the accumulator and the
carried variables' values, and its environment has the carried variables set. The body either hands
the carried variables back in place or, carrying none, computes into frame slots, and it writes
only them and the counter variable when that is in memory. -/
theorem loopG_of_loop {Γ ts : List Ty} {s u : Ty} {N : Nat} {cs : Carry Γ ts} {init : Atom Γ s}
    {c : Exp (.u64 :: s :: Γ) .bool} {body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))}
    {k : Exp (s :: Γ) u} (ihc : MSoundAt κ ω c) (ihb : MSoundAt κ ω body) {tm : Tl}
    {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f₀ : Frame}
    {h₀ : Heap} {w₀ : World}
    (H : MHyp ω (.loop N cs init c body k) tm L W ρ S n d bp env f₀ h₀ w₀)
    (hN : N < UInt64.size) (hd : cs.distinct = true) (hCb : body.Conf (loopTl s cs) = true)
    {la lc : Loc} (hla : accLoc (Exp.accSlot c body k) ρ n s.slotN = la)
    (hlc : cntLoc (Exp.cntSlot c body) (la :: ρ) (n + s.size) = lc) :
    LoopG κ ω L N c body Prod.fst (fun st => cs.set env st.2) (flagTl c (FR + slotsIn (lc :: la :: ρ)))
      (bodyTl cs c body k (FR + slotsIn (lc :: la :: ρ))) lc la (!Exp.cntSlot c body) bp n
      (n + s.size) ρ S W (selW cs.idxs 0 W) := by
  have hmc := Nat.le_max_left c.memNeed body.memNeed
  have hmb := Nat.le_max_right c.memNeed body.memNeed
  have hmk := Nat.le_max_left (17 + s.size + max c.memNeed body.memNeed) k.memNeed
  have hl := H.lay; have hR := H.restr
  have hb := H.size; have hbL := H.room; simp only [Exp.memNeed] at hb hbL
  have hV : ∀ i, (S.getD i default).ext ≠ none →
      c.VSafe (i + 2) .none = true ∧ body.VSafe (i + 2) (loopTl s cs) = true ∧
        (cs.idxs.contains i = true → body.HBx (i + 2) ((cs.after i).map (· + 2)) = true) :=
    fun i hi => by
      have := H.vs i hi
      simp only [Exp.VSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
      exact ⟨this.1.1.1.2, this.1.1.2, fun h => this.1.2.resolve_left (by simpa using h)⟩
  have hWc : ∀ i, (noW W).getD i false = true → W.getD i false = true := fun i h => by
    simp only [noW, List.getD_eq_getElem?_getD, List.getElem?_map] at h
    cases hw : W[i]? <;> simp [hw] at h
  have hWb : ∀ i, (selW cs.idxs 0 W).getD i false = true → W.getD i false = true := fun i h => by
    rw [getD_selW] at h; simp only [Bool.and_eq_true] at h; exact h.1
  have hlaOk : AccLoc s la n (FR + slotsIn ρ) := hla ▸ accLoc_ok (c := c) (body := body) (k := k) ρ n
  have hlcOk : CntLoc lc (n + s.size) (FR + slotsIn (la :: ρ)) := hlc ▸ cntLoc_ok _ _ _
  have hlay := fun {W' : List Bool} (hW' : ∀ i, W'.getD i false = true → W.getD i false = true) b₁ b₂ m
    (hm : n + s.size + 16 ≤ m) => loop_lay (hl.wle hW') hlcOk hlaOk rfl b₁ b₂ hm
  have hna : ∀ i, (Exp.loop N cs init c body k).noAddr i = true →
      c.noAddr (i + 2) = true ∧ body.noAddr (i + 2) = true := by
    intro i h
    simp only [Exp.noAddr, Bool.and_eq_true] at h
    exact h.1
  have hla' : ∀ k', la.slot? = some k' → k' = FR + slotsIn ρ :=
    fun k' hk => by rcases hlaOk with e | ⟨_, e⟩ <;> rw [e] at hk <;> simp [Loc.slot?] at hk; exact hk.symm
  have hlc' : ∀ k', lc.slot? = some k' → k' = FR + slotsIn (la :: ρ) :=
    fun k' hk => by rcases hlcOk with e | ⟨-, e⟩ <;> rw [e] at hk <;> simp [Loc.slot?] at hk; exact hk.symm
  have hok' : SlotsOk (lc :: la :: ρ) := ⟨hlc', hla', H.sl.ok⟩
  -- the loop variables are slot-resident only where the condition and the body do not address them
  have hcs : lc.isSlot = true → Exp.cntSlot c body = true := fun h => by
    subst hlc; unfold cntLoc at h; split at h
    · assumption
    · simp [Loc.isSlot] at h
  have has : la.isSlot = true → Exp.accSlot c body k = true := fun h => by
    subst hla; unfold accLoc at h; split at h
    · assumption
    · simp [Loc.isSlot] at h
  have hcs' := fun h => by have := hcs h; simp only [Exp.cntSlot, Bool.and_eq_true] at this; exact this
  have has' := fun h => by have := has h; simp only [Exp.accSlot, Bool.and_eq_true] at this; exact this
  -- the counter variable is read-only in the body when it is slot-resident
  have hRb : body.Restr ((!Exp.cntSlot c body) :: true :: selW cs.idxs 0 W) := by
    cases e : Exp.cntSlot c body
    · exact hR.2.2.1
    · simp only [Exp.cntSlot, Bool.and_eq_true] at e
      exact body.restr_clr (fun j hj hw => by
        match j, hj with
        | j + 1, _ => simpa using hw) e.1.2 e.2 hR.2.2.1
  -- the tail modes of the condition and the body: into the slots after the loop variables', or memory
  have hcT := flagTl_ok c (W := false :: false :: noW W) hok' fun i hi => (hV i hi).1
  have hbT := bodyTl_ok cs c body k (W := (!Exp.cntSlot c body) :: true :: selW cs.idxs 0 W)
    H.lay.length.2 hok' hCb
    (loopTl_ok cs hR.1 _ _ _) fun i hi => (hV i hi).2.1
  refine ⟨hl, rfl, by omega, by omega, hN, H.sl.ok, hlaOk, hlcOk, fun h => by simp [hcs h], ?_, ?_,
    fun i st f h w K clk hf hfe henv hs hw => flagTl_hb c _ ▸ ihc.app (W := false :: false :: noW W)
      (n := n + s.size + 17 + s.size) (d := n + s.size + 16) ⟨hcT.1, hcT.2.1, hR.2.1,
      H.lawful.1, H.frozen.1, HoleAv.push2 _ _ rfl rfl H.hole fun _ _ h => h.2.2.1,
      hlay hWc false false _ (by omega), by have := hcT.2.2.2.1; omega,
      (hlay hWc false false _ (Nat.le_refl _)).away (Nat.le_refl _), by omega, hf, henv, hs, hw,
      by omega, VS.push2 _ _ rfl rfl hcT.2.2.2.2,
      H.sl.loop hcT.2.2.1 (fun i h => (hna i h).1) hla' hlc' (fun h => (hcs' h).1.1)
        (fun h => (has' h).1.1.2) hfe⟩ K clk,
    fun i st f h w K clk hf hfe henv hs hw => ihb.app
      (W := (!Exp.cntSlot c body) :: true :: selW cs.idxs 0 W) (n := n + s.size + 17 + s.size)
      (d := n + s.size + 17) ⟨hbT.1, hbT.2.1, hRb, H.lawful.2.1, H.frozen.2.1,
      HoleAv.push2 _ _ rfl rfl H.hole fun _ _ h => h.2.2.2.1, hlay hWb _ true _ (by omega),
      by have := hbT.2.2.2.1; omega, (hlay hWc false false _ (Nat.le_refl _)).away (by omega),
      by omega, hf, henv, hs, hw, by omega, VS.push2 _ _ rfl rfl hbT.2.2.2.2,
      H.sl.loop hbT.2.2.1 (fun i h => (hna i h).2) hla' hlc' (fun h => (hcs' h).1.2)
        (fun h => (has' h).1.2) hfe⟩ K clk,
    fun i st w f f' h h' henv hfe hsb hv hm hfk => ?_⟩
  · unfold flagTl; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · unfold bodyTl; split
    · rename_i hw
      have hA : Exp.accSlot c body k = true := by
        simp only [Exp.bodyW, Bool.and_eq_true] at hw; exact hw.1.1.1.1
      rw [← hla]; simp only [accLoc, hA, ↓reduceIte]
      refine Or.inr ⟨FR + slotsIn ρ, _, rfl, rfl, ?_⟩
      simp only [slotsIn_cons, Loc.nw]; omega
    · exact Or.inl rfl
  -- the body's value: the new accumulator, and the carried variables' handed-back values
  obtain ⟨bs, b, hacc, hvs, hbsc⟩ := body_value cs c body k hv
  refine ⟨hacc, ?_⟩
  rw [← Carry.set_set cs hd env st.2]
  exact carry_rel hl (by omega) H.sl.ok h' f' bs cs b (cs.set env st.2) h f _ hd hR.1 henv hfe hvs
    hbsc
    (fun x hx hxe => cs.exact_step hd hx _ i st.1 _ (by
      rw [Exp.exec_val]
      exact Exp.hbx_exact ω body (x + 2) _ ((hV x hxe).2.2 (by simp [hx])) _ _ hsb))
    (fun x hx hn => hm x (loop_prot _ true (by omega) (by unfold InR; omega)
      (fun h2 => hn (InW.selW h2).2) (by omega) (by omega)))
    fun j k' hk hj => hfk k' (H.sl.ok.holds j k' hk).1 ⟨j + 2, by simpa using hk, by
      rw [List.getD_cons_succ, List.getD_cons_succ, getD_selW, Nat.zero_add]; simp [hj]⟩

theorem conf_loop {Γ ts : List Ty} {s u : Ty} {N : Nat} {cs : Carry Γ ts} {init : Atom Γ s}
    {c : Exp (.u64 :: s :: Γ) .bool} {body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))}
    {k : Exp (s :: Γ) u} {tm : Tl} (h : (Exp.loop N cs init c body k).Conf tm = true) :
    k.Conf tm.up = true := by
  cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using h

/-- A loop that writes carried variables: the initial accumulator in its bytes or its slots, the
counter zeroed, the loop, in which the body updates the carried variables in place, and then the
continuation. -/
theorem msound_loop {Γ ts : List Ty} {s u : Ty} (N : Nat) (cs : Carry Γ ts) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts)))
    (k : Exp (s :: Γ) u) (hN : N < UInt64.size) (hd : cs.distinct = true)
    (hCb : body.Conf (loopTl s cs) = true) (ihc : MSoundAt κ ω c) (ihb : MSoundAt κ ω body)
    (ihk : MSoundAt κ ω k) : MSoundAt κ ω (.loop N cs init c body k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w clk H => ?_
  have hl := H.lay
  have hb := H.size; have hbL := H.room; simp only [Exp.memNeed] at hb hbL
  have hmk := Nat.le_max_right (17 + s.size + max c.memNeed body.memNeed) k.memNeed
  have hVk := H.vs.mono fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2
  simp only [lowerM]
  generalize hla : accLoc (Exp.accSlot c body k) ρ n s.slotN = la
  generalize hlc : cntLoc (Exp.cntSlot c body) (la :: ρ) (n + s.size) = lc
  have G := loopG_of_loop (κ := κ) ihc ihb H hN hd hCb hla hlc
  have hH := G.off_le
  -- the initial accumulator
  obtain ⟨f₂, H₁, hr₂, hf₂, hk₂, hm₂, hacc₁⟩ := acc_init (κ := κ) (ω := ω) (L := L) init G.laOk
    (Nat.le_refl _) H.sl.ok hl
    (by omega) (by omega) H.bpOk H.envRel H.sl.rel (init.noHole fun i H' h' => (H.hole i H' h').1)
    (H.vs.atom init fun i h => by
      simp only [Exp.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.1.1.1)
  have hH₁o : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x) := fun x hx =>
    hm₂ x (by omega) (by unfold InR; omega)
  -- the counter
  obtain ⟨f₃, H₃, hr₃, hf₃, hk₃, hm₃, hcnt⟩ := cnt_init (κ := κ) (ω := ω) (L := L) G.lcOk
    (by simp only [slotsIn_cons]; omega) (hf₂.trans H.bpOk) (by omega) (by omega)
  have hacc : AccAt s la bp f₃ H₃ (init.denote env) :=
    hacc₁.congr (fun j hj => hm₃ _ (by omega) (by unfold InR; omega))
      fun x hx => hk₃ x (G.la_ge hx) (G.la_ne_lc hx)
  have hfρ₃ : ∀ i x, (ρ.getD i default).holds x = true → f₃ x = f x := fun i x hx => by
    have hne := G.slot_ne hx
    have hge := (H.sl.ok.holds i x hx).1
    rw [hk₃ x hge hne.2, hk₂ x hge hne.1]
  have henv₂ : MEnvRel H₃ bp (cs.set env (cs.get env)) ρ S := by
    rw [Carry.set_get]
    exact H.envRel.above hl fun x hx => by rw [hm₃ _ (by omega) (by unfold InR; omega), hH₁o _ hx]
  have hs := H.safe
  simp only [Exp.safe] at hs
  let κi : CostModel := { κ with iter := κ.iter + s.words * κ.word }
  have hfe₁ : FEnvRel f₃ (cs.set env (cs.get env)) ρ := by
    rw [Carry.set_get]; exact H.sl.rel.congr hfρ₃
  have hHL := G.head κi rfl
    (.seq (lowerM k tm.up (la :: ρ) (n + s.size) d) :: kk)
    N 0 (by omega) (init.denote env, cs.get env) f₃ H₃ w (clk + (Tick.loop (width s)).cost κ)
    (hf₃.trans (hf₂.trans H.bpOk)) hfe₁ henv₂ hcnt hacc H.run hs.1
  -- the loop agrees with the value semantics
  rw [bodyTl_hb] at hHL
  have hls := loopExec_sound κi (fun i st w => c.exec ω κ .copy (.cons i (.cons st.1 (cs.set env st.2))) w)
    (fun i st w => body.exec ω κ (Hb.of !ts.isEmpty) (.cons i (.cons st.1 (cs.set env st.2))) w)
    (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
    (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) (c.cost κ .copy)
    (body.cost κ (Hb.of !ts.isEmpty))
    (fun i a w => c.exec_sound ω κ .copy _ w) (fun i a w => body.exec_sound ω κ _ _ w) N 0
    (init.denote env, cs.get env) w
  generalize hR₁ : loopExec κi (fun i st w => c.exec ω κ .copy (.cons i (.cons st.1 (cs.set env st.2))) w)
    (fun i st w => body.exec ω κ (Hb.of !ts.isEmpty) (.cons i (.cons st.1 (cs.set env st.2))) w) N 0
    (init.denote env, cs.get env) w = r₁ at hHL hls
  have hWb : ∀ i, (selW cs.idxs 0 W).getD i false = true → W.getD i false = true := fun i h => by
    rw [getD_selW] at h; simp only [Bool.and_eq_true] at h; exact h.1
  have hbind := MSim.bindF (pf := SProt ρ W) (Q := TQ tm bp d ρ S u) (prot₂ := Prot bp n d (tm.dsz u) Γ S W)
    (r₂ := k.exec ω κ tm.up.hb (.cons r₁.val.1 (cs.set env r₁.val.2)) r₁.world) hHL
    (fun hh => exec_halted ω κ k _ _ hh)
    (fun x hx => ⟨⟨hx.1, by have := hx.1; unfold InR; omega, fun e => hx.2.2 (InW.selW e).1⟩, hx⟩)
    (fun x hx => ⟨hx.wle hWb, hx⟩)
    (fun f₅ m₄ hf₅ _ hv _ hh => by
      obtain ⟨hacc₅, henv₅, hfeK⟩ := hv
      have hsk : k.safe ω (.cons r₁.val.1 (cs.set env r₁.val.2)) r₁.world := by
        rw [hls.1, hls.2.1]; exact hs.2
      rcases G.laOk with e | ⟨hts, e⟩
      · subst e
        exact .unpush (Nat.le_refl _) (ihk.app (H.push r₁.val.1 (Nat.le_refl _)
          (conf_loop H.conf) H.restr.2.2.2 H.lawful.2.2 H.frozen.2.2
          (H.hole.push _ rfl fun _ _ h => h.2.2.2.2) (by omega) (by omega)
          (hf₅.trans (hf₃.trans (hf₂.trans H.bpOk))) henv₅ hfeK hacc₅ hsk hVk hh) kk _)
      · subst e
        have hna0 : k.noAddr 0 = true := by
          unfold accLoc at hla
          split at hla
          · rename_i hs'; simp only [Exp.accSlot, Bool.and_eq_true] at hs'; exact hs'.2
          · cases hla
        exact .unpush (Nat.le_refl _) (ihk.app (H.pushSlot r₁.val.1 (Nat.le_refl _)
          (conf_loop H.conf) H.restr.2.2.2 H.lawful.2.2 H.frozen.2.2
          (H.hole.push _ rfl fun _ _ h => h.2.2.2.2) (by omega) (by omega)
          (hf₅.trans (hf₃.trans (hf₂.trans H.bpOk))) henv₅ hfeK hts
          hacc₅.2 hsk hVk hh hna0
          (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)) kk _))
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run
    (MSim.reach H.run hr₂ hf₂
      (fun x hx => hm₂ x (by unfold Prot at hx; omega) (by unfold Prot at hx; unfold InR; omega))
      (fun x hx hp => by
        obtain ⟨i, hi, _⟩ := hp
        rw [hk₂ x hx (G.slot_ne hi).1])
    (MSim.reach H.run hr₃ hf₃ (fun x hx => by
        rw [hm₃ _ (by unfold Prot at hx; omega) (by unfold InR; unfold Prot at hx; omega)])
      (fun x hx hp => by obtain ⟨i, hi, _⟩ := hp; rw [hk₃ x hx (G.slot_ne hi).2])
      (MSim.seq_intro H.run hbind)))).of_eq ?_ ?_ ?_
  · simp only [Exp.exec, Tl.hb_up]; rw [hR₁]
  · simp only [Exp.exec, Tl.hb_up]; rw [hR₁]
  · simp only [Exp.exec, Tick.cost, Tl.hb_up]; rw [hR₁]; simp only [width, Ty.words]; omega

end

end Millipede.Flat
