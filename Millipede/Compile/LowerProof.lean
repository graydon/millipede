import Millipede.Compile.LowerFacts

/-!
# Memory primitives of the refinement of `lower`

This module holds the byte-level facts that the memory refinement uses:

* `rd h a n` reads `n` bytes at address `a` and `wr h a bs` writes them, where `a` is a `Nat` and
  the heap is indexed by `UInt64.ofNat a`, with laws for reading back, slicing and splicing below
  `2^64`;
* `ReachL κ ω L s s'` says that `s'` is reachable from `s` and that every state on the way accesses
  memory only below `L`;
* `Runs L st f h f' h'` says that the statement `st`, which touches neither the clock nor the world,
  runs from frame `f` and heap `h` to `f'` and `h'` in any continuation, accessing memory only below
  `L`, and such runs compose with `Runs.seq`;
* the copy primitives `copyB` and `writeB`, the scalar loads and stores, and the decoding of
  little-endian words.
-/

namespace Millipede.Flat

/-! ## Facts about `exec` -/

theorem exec_halted (ω : Oracle) (κ : CostModel) {Γ : List Ty} {t : Ty} {hb : Hb} (e : Exp Γ t)
    (env : Env Γ) (w : World) (h : w.halted = true) : (e.exec ω κ hb env w).world = w := by
  rw [Exp.exec_world]; exact Exp.denote_halted ω e env w h

theorem loopExec_halted {σ : Type} (κ : CostModel) (cond : UInt64 → σ → World → Out Bool)
    (body : UInt64 → σ → World → Out σ)
    (hc : ∀ i a w, w.halted = true → (cond i a w).world = w)
    (hb : ∀ i a w, w.halted = true → (body i a w).world = w) :
    ∀ m i acc w, w.halted = true → (loopExec κ cond body m i acc w).world = w
  | 0, _, _, _, _ => rfl
  | m + 1, i, acc, w, h => by
    simp only [loopExec]
    have h1 := hc (UInt64.ofNat i) acc w h
    split
    · exact h1
    · simp only
      rw [loopExec_halted κ cond body hc hb m _ _ _ (by rw [hb _ _ _ (by rw [h1]; exact h), h1]; exact h),
        hb _ _ _ (by rw [h1]; exact h), h1]

theorem ofNat_lt_ofNat {i N : Nat} (hN : N < UInt64.size) (hi : i ≤ N) :
    (UInt64.ofNat i < UInt64.ofNat N) ↔ i < N := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [UInt64.size] at hN
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## Reading and writing byte ranges -/

/-- The `n` bytes at address `a`. -/
def rd (h : Heap) (a : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => h (UInt64.ofNat a) :: rd h (a + 1) n

/-- Write bytes at address `a`, in order. -/
def wr (h : Heap) (a : Nat) : List UInt8 → Heap
  | [] => h
  | b :: bs => wr (h.store8 (UInt64.ofNat a) b) (a + 1) bs

/-- An extern's output write at a word address is `wr`. -/
theorem writeBytes_eq_wr : ∀ (h : Heap) (a : Nat) (bs : List UInt8),
    h.writeBytes (UInt64.ofNat a) bs = wr h a bs
  | _, _, [] => rfl
  | h, a, b :: bs => by
    simp only [Heap.writeBytes, wr]
    rw [show UInt64.ofNat a + 1 = UInt64.ofNat (a + 1) from (UInt64.ofNat_add a 1).symm]
    exact writeBytes_eq_wr _ _ bs

@[simp] theorem rd_length (h : Heap) (a n : Nat) : (rd h a n).length = n := by
  induction n generalizing a <;> simp [rd, *]

theorem ofNat_inj {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size)
    (h : UInt64.ofNat a = UInt64.ofNat b) : a = b := by
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat'] at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem ofNat_ne {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size) (h : a ≠ b) :
    UInt64.ofNat a ≠ UInt64.ofNat b := fun e => h (ofNat_inj ha hb e)

/-- Writing elsewhere leaves an address unchanged. -/
theorem wr_other (h : Heap) (a : Nat) (bs : List UInt8) (x : Nat) (hx : x < UInt64.size)
    (hb : a + bs.length ≤ UInt64.size) (hout : x < a ∨ a + bs.length ≤ x) :
    wr h a bs (UInt64.ofNat x) = h (UInt64.ofNat x) := by
  induction bs generalizing h a with
  | nil => rfl
  | cons b bs ih =>
    simp only [wr]
    rw [ih _ _ (by simp at hb; omega) (by simp at hout; omega)]
    simp only [Heap.store8]
    rw [ite_eq_right (ofNat_ne hx (by simp at hb; omega) (by simp at hout; omega))]

/-- Reading back what was written. -/
theorem rd_wr (h : Heap) (a : Nat) (bs : List UInt8) (hb : a + bs.length ≤ UInt64.size) :
    rd (wr h a bs) a bs.length = bs := by
  induction bs generalizing h a with
  | nil => rfl
  | cons b bs ih =>
    simp only [wr, List.length_cons, rd]
    rw [ih _ _ (by simp at hb; omega), wr_other _ _ _ _ (by simp at hb; omega)
      (by simp at hb; omega) (Or.inl (Nat.lt_succ_self _))]
    simp [Heap.store8]

/-- Reads depend only on the bytes read. -/
theorem rd_congr {h h' : Heap} {a n : Nat}
    (heq : ∀ i, i < n → h' (UInt64.ofNat (a + i)) = h (UInt64.ofNat (a + i))) :
    rd h' a n = rd h a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [rd]
    rw [show a = a + 0 by rfl, heq 0 (by omega), ih (fun i hi => by
      have := heq (i + 1) (by omega); rw [show a + 0 + 1 + i = a + (i + 1) by omega]; exact this)]

theorem rd_add (h : Heap) (a m n : Nat) : rd h a (m + n) = rd h a m ++ rd h (a + m) n := by
  induction m generalizing a with
  | zero => simp [rd]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [rd, ih, List.cons_append]
    rw [show a + 1 + m = a + (m + 1) by omega]

/-- A sub-range is a slice of the range. -/
theorem rd_slice (h : Heap) (a n o m : Nat) (hle : o + m ≤ n) :
    rd h (a + o) m = slice (rd h a n) o m := by
  rw [show n = o + (m + (n - o - m)) by omega, rd_add, rd_add]
  simp [slice]

/-- A range whose middle part changed is the old range spliced with the new middle. -/
theorem rd_splice {h h' : Heap} {a n o m : Nat} (hle : o + m ≤ n)
    (heq : ∀ i, i < n → (i < o ∨ o + m ≤ i) → h' (UInt64.ofNat (a + i)) = h (UInt64.ofNat (a + i))) :
    rd h' a n = splice (rd h a n) o (rd h' (a + o) m) := by
  rw [show n = o + (m + (n - o - m)) by omega, rd_add, rd_add, rd_add h, rd_add h]
  simp only [splice, rd_length]
  have e1 : rd h' a o = rd h a o := rd_congr fun i hi => heq i (by omega) (Or.inl hi)
  have e2 : rd h' (a + o + m) (n - o - m) = rd h (a + o + m) (n - o - m) :=
    rd_congr fun i hi => by
      have := heq (o + m + i) (by omega) (Or.inr (by omega))
      rw [show a + o + m + i = a + (o + m + i) by omega]; exact this
  rw [e1, e2]
  simp [List.drop_append]

/-! ## Bounded runs -/

/-- The memory buffers of an extern call lie below address `L`. -/
def ExtAccIn (L : Nat) (f : Frame) : List ExtArg → Prop
  | [] => True
  | .mem a n :: as => (a.eval f).toNat + (n.eval f).toNat ≤ L ∧ ExtAccIn L f as
  | .outMem a n :: as => (a.eval f).toNat + (n.eval f).toNat ≤ L ∧ ExtAccIn L f as
  | _ :: as => ExtAccIn L f as

/-- The memory access that the state `s` is about to make, if any, lies below address `L`. -/
def AccIn (L : Nat) (s : State) : Prop :=
  match s.cur with
  | .load w _ a off => (a.eval s.frame + off).toNat + w.bytes ≤ L
  | .store w a off _ => (a.eval s.frame + off).toNat + w.bytes ≤ L
  | .ext _ _ _ args => ExtAccIn L s.frame args
  | _ => True

/-- `s'` is reachable from `s`, and every state of the run before `s'` accesses memory only below
`L`. -/
def ReachL (κ : CostModel) (ω : Oracle) (L : Nat) (s s' : State) : Prop :=
  ∃ n, nextN κ ω n s = s' ∧ ∀ m, m < n → AccIn L (nextN κ ω m s)

section ReachL
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem ReachL.refl (s : State) : ReachL κ ω L s s := ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ReachL.trans {s₁ s₂ s₃ : State} (h₁ : ReachL κ ω L s₁ s₂) (h₂ : ReachL κ ω L s₂ s₃) :
    ReachL κ ω L s₁ s₃ := by
  obtain ⟨m, rfl, hm⟩ := h₁; obtain ⟨n, rfl, hn⟩ := h₂
  refine ⟨m + n, nextN_add κ ω m n s₁, fun i hi => ?_⟩
  by_cases hi' : i < m
  · exact hm i hi'
  · have := hn (i - m) (by omega)
    rw [← nextN_add] at this
    rwa [show m + (i - m) = i by omega] at this

theorem ReachL.head {s s₁ s' : State} (h₁ : next κ ω s = s₁) (ha : AccIn L s)
    (h₂ : ReachL κ ω L s₁ s') : ReachL κ ω L s s' := by
  obtain ⟨n, rfl, hn⟩ := h₂
  refine ⟨n + 1, by simp [nextN, h₁], fun m hm => ?_⟩
  cases m with
  | zero => exact ha
  | succ m => simp only [nextN, h₁]; exact hn m (by omega)

/-- One transition of a running state, whose access, if any, is below `L`. -/
theorem ReachL.step' {s s' : State} (hw : s.world.halted = false)
    (h : ReachL κ ω L (exec1 κ ω s) s') (ha : AccIn L s := by trivial) : ReachL κ ω L s s' :=
  ReachL.head (next_run hw) ha h

theorem ExtAccIn.mono {L L' : Nat} {f : Frame} (hL : L ≤ L') :
    ∀ (as : List ExtArg), ExtAccIn L f as → ExtAccIn L' f as
  | [], _ => trivial
  | .mem _ _ :: as, h | .outMem _ _ :: as, h => ⟨by have := h.1; omega, ExtAccIn.mono hL as h.2⟩
  | .word _ :: as, h | .bytes _ :: as, h | .out _ :: as, h => ExtAccIn.mono (f := f) hL as h

theorem ReachL.mono {L' : Nat} {s s' : State} (h : ReachL κ ω L s s') (hL : L ≤ L') :
    ReachL κ ω L' s s' := by
  obtain ⟨n, h1, h2⟩ := h
  refine ⟨n, h1, fun m hm => ?_⟩
  have := h2 m hm
  unfold AccIn at this ⊢
  split <;> simp_all
  all_goals first | omega | exact ExtAccIn.mono hL _ this

/-- The address `A` of an access, as a word, is below `L`. -/
theorem acc_ofNat {A b : Nat} (h1 : A + b ≤ L) (h2 : A < UInt64.size) :
    (UInt64.ofNat A).toNat + b ≤ L := by
  simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h2]; exact h1

end ReachL

/-! ## Tick-free, world-free code -/

/-- `st` runs from frame `f` and heap `h` to `f'` and `h'` in every continuation, touching neither
the world nor the clock and accessing memory only below `L`. -/
def Reaches (κ : CostModel) (ω : Oracle) (L : Nat) (st : Stmt) (f : Frame) (h : Heap) (f' : Frame)
    (h' : Heap) : Prop :=
  ∀ (k : List Kont) (w : World) (c : Nat), w.halted = false →
    ReachL κ ω L ⟨st, k, f, h, w, c⟩ ⟨.skip, k, f', h', w, c⟩

/-- Scratch code runs: it reaches `f'` and `h'` and keeps every frame slot from `FR` on, where the
slot-resident variables live. -/
structure Runs (κ : CostModel) (ω : Oracle) (L : Nat) (st : Stmt) (f : Frame) (h : Heap) (f' : Frame)
    (h' : Heap) : Prop where
  run : Reaches κ ω L st f h f' h'
  /-- The slots from `FR` on are unchanged. -/
  keep : ∀ x, FR ≤ x → f' x = f x

section Runs
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem Runs.skip (f : Frame) (h : Heap) : Runs κ ω L .skip f h f h :=
  ⟨fun _ _ _ _ => ReachL.refl _, fun _ _ => rfl⟩

theorem Runs.seq {a b : Stmt} {f f₁ f₂ : Frame} {h h₁ h₂ : Heap}
    (ha : Runs κ ω L a f h f₁ h₁) (hb : Runs κ ω L b f₁ h₁ f₂ h₂) :
    Runs κ ω L (.seq a b) f h f₂ h₂ := by
  refine ⟨fun k w c hw => ?_, fun x hx => (hb.keep x hx).trans (ha.keep x hx)⟩
  refine ReachL.step' hw ?_
  simp only [exec1]
  exact (ha.run _ w c hw).trans (ReachL.step' hw (by simp only [exec1]; exact hb.run k w c hw))

theorem Frame.set_keep (f : Frame) {x : Nat} (v : UInt64) (hx : x < FR) :
    ∀ y, FR ≤ y → f.set x v y = f y :=
  fun _ hy => Frame.set_ne _ _ (by omega)

theorem Reaches.mov (x : Nat) (o : Operand) (f : Frame) (h : Heap) :
    Reaches κ ω L (.mov x o) f h (f.set x (o.eval f)) h :=
  fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)

theorem Reaches.bin (op : BinOp) (x : Nat) (a b : Operand) (f : Frame) (h : Heap) :
    Reaches κ ω L (.bin op x a b) f h (f.set x (op.eval (a.eval f) (b.eval f))) h :=
  fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _)

theorem Reaches.load (w : Width) (x : Nat) (a : Operand) (off : UInt64) (f : Frame) (h : Heap)
    (ha : (a.eval f + off).toNat + w.bytes ≤ L) :
    Reaches κ ω L (.load w x a off) f h (f.set x (h.load w (a.eval f + off))) h :=
  fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _) ha

theorem Reaches.seq {a b : Stmt} {f f₁ f₂ : Frame} {h h₁ h₂ : Heap}
    (ha : Reaches κ ω L a f h f₁ h₁) (hb : Reaches κ ω L b f₁ h₁ f₂ h₂) :
    Reaches κ ω L (.seq a b) f h f₂ h₂ := fun k w c hw =>
  ReachL.step' hw (by
    simp only [exec1]
    exact (ha _ w c hw).trans (ReachL.step' hw (by simp only [exec1]; exact hb k w c hw)))

theorem Reaches.congr {st : Stmt} {f f₁ f' : Frame} {h h₁ h' : Heap}
    (hr : Reaches κ ω L st f h f₁ h₁) (hf : f₁ = f') (hh : h₁ = h') :
    Reaches κ ω L st f h f' h' := hf ▸ hh ▸ hr

theorem Runs.mov (x : Nat) (o : Operand) (f : Frame) (h : Heap) (hx : x < FR := by decide) :
    Runs κ ω L (.mov x o) f h (f.set x (o.eval f)) h :=
  ⟨Reaches.mov x o f h, Frame.set_keep f _ hx⟩

theorem Runs.bin (op : BinOp) (x : Nat) (a b : Operand) (f : Frame) (h : Heap)
    (hx : x < FR := by decide) :
    Runs κ ω L (.bin op x a b) f h (f.set x (op.eval (a.eval f) (b.eval f))) h :=
  ⟨fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _),
    Frame.set_keep f _ hx⟩

theorem Runs.load (w : Width) (x : Nat) (a : Operand) (off : UInt64) (f : Frame) (h : Heap)
    (ha : (a.eval f + off).toNat + w.bytes ≤ L) (hx : x < FR := by decide) :
    Runs κ ω L (.load w x a off) f h (f.set x (h.load w (a.eval f + off))) h :=
  ⟨fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _) ha,
    Frame.set_keep f _ hx⟩

theorem Runs.store (w : Width) (a : Operand) (off : UInt64) (b : Operand) (f : Frame) (h : Heap)
    (ha : (a.eval f + off).toNat + w.bytes ≤ L) :
    Runs κ ω L (.store w a off b) f h f (h.store w (a.eval f + off) (b.eval f)) :=
  ⟨fun _ _ _ hw => ReachL.step' hw (by simp only [exec1]; exact ReachL.refl _) ha,
    fun _ _ => rfl⟩

theorem Runs.ite_false {c : Operand} {t e : Stmt} {f f' : Frame} {h h' : Heap}
    (hc : c.eval f = 0) (he : Runs κ ω L e f h f' h') : Runs κ ω L (.ite c t e) f h f' h' :=
  ⟨fun k w cl hw => ReachL.step' hw (by simp only [exec1, hc, ↓reduceIte]; exact he.run k w cl hw),
    he.keep⟩

theorem Runs.congr {st : Stmt} {f f₁ f' : Frame} {h h₁ h' : Heap} (hr : Runs κ ω L st f h f₁ h₁)
    (hf : f₁ = f') (hh : h₁ = h') : Runs κ ω L st f h f' h' := hf ▸ hh ▸ hr

end Runs

/-! ## Address arithmetic -/

theorem ofNat_add_ofNat (a b : Nat) : UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  (UInt64.ofNat_add a b).symm

/-! ## Byte copies -/

theorem store8_eq (h : Heap) (a : UInt64) (b : UInt8) :
    h.store .w8 a b.toUInt64 = h.store8 a b := by
  simp [Heap.store]

/-! ## Little-endian words -/

/-- A 64-bit load reads the little-endian word of the 8 bytes. -/
theorem load64_eq (h : Heap) (A : Nat) : h.load .w64 (UInt64.ofNat A) = decodeLE (rd h A 8) := by
  simp only [Heap.load, rd, decodeLE, List.range, List.range.loop, List.foldr, ofNat_add_ofNat,
    Nat.add_zero]

/-- A byte load reads the byte. -/
theorem load8_eq (h : Heap) (A : Nat) : h.load .w8 (UInt64.ofNat A) = decodeLE (rd h A 1) := by
  simp [Heap.load, rd, decodeLE]

/-- Storing a 64-bit word writes its 8 little-endian bytes. -/
theorem store64_eq (h : Heap) (A : Nat) (v : UInt64) :
    h.store .w64 (UInt64.ofNat A) v = wr h A (natBytes 8 v.toNat) := by
  rw [natBytes8_eq]
  simp only [Heap.store, List.range, List.range.loop, List.foldl, wr, ofNat_add_ofNat]
  have e : ∀ i : Nat, (8 * UInt64.ofNat i) = UInt64.ofNat (8 * i) := fun i => by
    rw [UInt64.ofNat_mul]; rfl
  simp only [e]
  rfl

/-- Writing a concatenation writes its parts in turn. -/
theorem wr_append : ∀ (h : Heap) (a : Nat) (xs ys : List UInt8),
    wr h a (xs ++ ys) = wr (wr h a xs) (a + xs.length) ys
  | _, _, [], _ => rfl
  | h, a, x :: xs, ys => by
    simp only [List.cons_append, wr, List.length_cons]
    rw [wr_append _ _ xs ys, show a + 1 + xs.length = a + (xs.length + 1) by omega]

/-- `writeB1` writes constant bytes and leaves the frame unchanged. -/
theorem writeB1_runs {κ : CostModel} {ω : Oracle} {L : Nat} (db : Operand) :
    ∀ (bs : List UInt8) (d D : Nat) (f : Frame) (h : Heap), db.eval f = UInt64.ofNat D →
      D + d + bs.length ≤ L → D + d + bs.length ≤ UInt64.size →
      Runs κ ω L (writeB1 db d bs) f h f (wr h (D + d) bs)
  | [], _, _, f, h, _, _, _ => Runs.skip _ _
  | b :: bs, d, D, f, h, hD, hL, hU => by
    simp only [List.length_cons] at hL hU
    refine Runs.seq (Runs.congr (Runs.store _ _ _ _ _ _ (by
      rw [hD, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega)))
      rfl rfl) ?_
    have := writeB1_runs (κ := κ) (ω := ω) (L := L) db bs (d + 1) D f
      (h.store .w8 (db.eval f + UInt64.ofNat d) (Operand.eval f (.imm b.toUInt64))) hD
      (by omega) (by omega)
    refine Runs.congr this rfl ?_
    rw [hD]
    simp only [eval_imm, store8_eq, ofNat_add_ofNat, wr]
    rw [show D + (d + 1) = D + d + 1 by omega]

/-- `writeB` writes constant bytes and leaves the frame unchanged. -/
theorem writeB_runs {κ : CostModel} {ω : Oracle} {L : Nat} (db : Operand) :
    ∀ (bs : List UInt8) (d D : Nat) (f : Frame) (h : Heap), db.eval f = UInt64.ofNat D →
      D + d + bs.length ≤ L → D + d + bs.length ≤ UInt64.size →
      Runs κ ω L (writeB db d bs) f h f (wr h (D + d) bs)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, d, D, f, h, hD, hL, hU => by
    simp only [List.length_cons] at hL hU
    let w := [b0, b1, b2, b3, b4, b5, b6, b7]
    have hw : natBytes 8 (decodeLE w).toNat = w := by
      rw [decodeLE_toNat w (by simp [w])]; exact natBytes_natOfBytes w
    have hs : h.store .w64 (db.eval f + UInt64.ofNat d) (Operand.eval f (.imm (decodeLE w))) =
        wr h (D + d) w := by
      rw [hD, eval_imm, ofNat_add_ofNat, store64_eq, hw]
    simp only [writeB]
    refine Runs.seq (Runs.congr (Runs.store _ _ _ _ _ _ (by
      rw [hD, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega)))
      rfl rfl) ?_
    rw [hs]
    have := writeB_runs (κ := κ) (ω := ω) (L := L) db bs (d + 8) D f (wr h (D + d) w) hD
      (by omega) (by omega)
    refine Runs.congr this rfl ?_
    rw [show (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) = w ++ bs from rfl, wr_append]
    simp only [w, List.length_cons, List.length_nil]
    rw [show D + (d + 8) = D + d + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) by omega]
  | [], _, _, f, h, _, _, _ => Runs.skip _ _
  | [_], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _, _, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _, _, _, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _, _, _, _, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU
  | [_, _, _, _, _, _, _], d, D, f, h, hD, hL, hU => writeB1_runs db _ d D f h hD hL hU

/-- `copyB` copies `len` bytes between disjoint ranges, and changes only `RT` in the frame. -/
theorem copyB_runs {κ : CostModel} {ω : Oracle} {L : Nat} (sb db : Operand) (hsb : sb ≠ .slot RT)
    (hdb : db ≠ .slot RT) :
    ∀ (len so d S D : Nat) (f : Frame) (h : Heap),
      sb.eval f = UInt64.ofNat S → db.eval f = UInt64.ofNat D →
      S + so + len ≤ UInt64.size → D + d + len ≤ UInt64.size →
      (S + so + len ≤ D + d ∨ D + d + len ≤ S + so) →
      S + so + len ≤ L → D + d + len ≤ L →
      ∃ f', (∀ x, x ≠ RT → f' x = f x) ∧
        Runs κ ω L (copyB sb so db d len) f h f' (wr h (D + d) (rd h (S + so) len)) := by
  intro len so d
  induction so, d, len using copyB.induct with
  | case1 => intro _ _ f h _ _ _ _ _ _ _; exact ⟨f, fun _ _ => rfl, Runs.skip _ _⟩
  | case2 so d len ih =>
    intro S D f h hS hD hs hd hdisj hSL hDL
    rw [copyB.eq_2]
    have hevS : ∀ g : Frame, (∀ x, x ≠ RT → g x = f x) → sb.eval g = UInt64.ofNat S := by
      intro g hg; cases sb with
      | imm w => exact hS
      | slot y => simp only [Operand.eval] at hS ⊢; rw [hg y (fun e => hsb (by rw [e]))]; exact hS
    have hevD : ∀ g : Frame, (∀ x, x ≠ RT → g x = f x) → db.eval g = UInt64.ofNat D := by
      intro g hg; cases db with
      | imm w => exact hD
      | slot y => simp only [Operand.eval] at hD ⊢; rw [hg y (fun e => hdb (by rw [e]))]; exact hD
    let B := rd h (S + so) 8
    let f₁ := f.set RT (decodeLE B)
    let h₁ := wr h (D + d) B
    have hf₁ : ∀ x, x ≠ RT → f₁ x = f x := fun x hx => Frame.set_ne _ _ hx
    obtain ⟨f', hf', hr⟩ := ih S D f₁ h₁
      (hevS f₁ hf₁) (hevD f₁ hf₁) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨f', fun x hx => (hf' x hx).trans (hf₁ x hx), ?_⟩
    have hrd : rd h₁ (S + (so + 8)) len = rd h (S + so + 8) len := by
      rw [show S + (so + 8) = S + so + 8 by omega]
      exact rd_congr fun i hi => wr_other _ _ _ _ (by omega) (by simp [B]; omega)
        (by simp [B]; omega)
    have hfinal : wr h₁ (D + (d + 8)) (rd h₁ (S + (so + 8)) len) =
        wr h (D + d) (rd h (S + so) (len + 8)) := by
      rw [hrd, Nat.add_comm len 8, rd_add, wr_append]
      simp [h₁, B]; rw [show D + (d + 8) = D + d + 8 by omega]
    rw [← hfinal]
    have hB : natBytes 8 (decodeLE B).toNat = B := by
      rw [decodeLE_toNat _ (by simp [B])]
      have := natBytes_natOfBytes B; simp only [B, rd_length] at this; exact this
    refine Runs.seq (f₁ := f₁) (h₁ := h) (Runs.congr (Runs.load _ _ _ _ _ _ (by
      rw [hS, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega)))
      (by simp only [f₁, B, hS, ofNat_add_ofNat, load64_eq]) rfl) (Runs.seq ?_ hr)
    refine Runs.congr (Runs.store _ _ _ _ _ _ (by
      rw [hevD _ hf₁, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega)
        (by omega))) rfl ?_
    have e1 : Operand.eval f₁ (.slot RT) = decodeLE B := by simp [f₁, Operand.eval]
    rw [e1, hevD _ hf₁, ofNat_add_ofNat, store64_eq, hB]
  | case3 so d len hne ih =>
    intro S D f h hS hD hs hd hdisj hSL hDL
    rw [copyB.eq_3 _ _ _ _ _ hne]
    have hevS : ∀ g : Frame, (∀ x, x ≠ RT → g x = f x) → sb.eval g = UInt64.ofNat S := by
      intro g hg; cases sb with
      | imm w => exact hS
      | slot y => simp only [Operand.eval] at hS ⊢; rw [hg y (fun e => hsb (by rw [e]))]; exact hS
    have hevD : ∀ g : Frame, (∀ x, x ≠ RT → g x = f x) → db.eval g = UInt64.ofNat D := by
      intro g hg; cases db with
      | imm w => exact hD
      | slot y => simp only [Operand.eval] at hD ⊢; rw [hg y (fun e => hdb (by rw [e]))]; exact hD
    let b := h (UInt64.ofNat (S + so))
    let f₁ := f.set RT b.toUInt64
    let h₁ := h.store8 (UInt64.ofNat (D + d)) b
    have hf₁ : ∀ x, x ≠ RT → f₁ x = f x := fun x hx => Frame.set_ne _ _ hx
    obtain ⟨f', hf', hr⟩ := ih S D f₁ h₁
      (hevS f₁ hf₁) (hevD f₁ hf₁) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨f', fun x hx => (hf' x hx).trans (hf₁ x hx), ?_⟩
    have hrd : rd h₁ (S + (so + 1)) len = rd h (S + so + 1) len := by
      rw [show S + (so + 1) = S + so + 1 by omega]
      refine rd_congr fun i hi => ?_
      simp only [h₁, Heap.store8]
      rw [ite_eq_right (ofNat_ne (by omega) (by omega) (by omega))]
    have hfinal : wr h₁ (D + (d + 1)) (rd h₁ (S + (so + 1)) len) =
        wr h (D + d) (rd h (S + so) (len + 1)) := by
      rw [hrd]; simp only [rd, wr, h₁, b]; rw [show D + (d + 1) = D + d + 1 by omega]
    rw [← hfinal]
    have hl : f.set RT (h.load .w8 (sb.eval f + UInt64.ofNat so)) = f₁ := by
      simp only [f₁, b, hS, ofNat_add_ofNat, Heap.load]
    refine Runs.seq (Runs.congr (Runs.load _ _ _ _ _ _ (by
      rw [hS, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega))) hl rfl)
      (Runs.seq ?_ hr)
    refine Runs.congr (Runs.store _ _ _ _ _ _ (by
      rw [hevD _ hf₁, ofNat_add_ofNat]; exact acc_ofNat (by simp only [Width.bytes]; omega)
        (by omega))) rfl ?_
    have e1 : Operand.eval f₁ (.slot RT) = b.toUInt64 := by simp [f₁, Operand.eval]
    rw [e1, hevD _ hf₁, ofNat_add_ofNat, store8_eq]


end Millipede.Flat
