import Millipede.Compile.LowerPlace

/-!
# The memory refinement of extern calls with slices

An extern call loads its word arguments into `REXT…` and passes each slice `a[lo..lo+len]` of a
byte array as two words, the address of element `lo` and the length. The bytes of a byte array are
its elements, so the `len` bytes from that address are the viewed elements, and the call record
that Flat builds is the one that Core builds.

There are two case lemmas. `msound_ext` covers a call that only reads its slices, such as
`write(fd, &a[lo..lo+n])`, and leaves the result word at the destination. `msound_extMut` covers a
call that writes one mutable slice, such as `read(fd, &mut a[lo..lo+cap])`. The machine writes at
most `cap` bytes of the reply from the slice's address, which is the array place written with
`vwrite`, and the result word goes to the continuation's variable.

See doc/design/world.md.
-/

namespace Millipede.Flat

/-! ## Byte arrays -/

theorem u8_encodeBytes (x : UInt8) : Data.encodeBytes x = [x] := by
  show natBytes 1 x.toNat = [x]
  simp [natBytes]

/-- The bytes of a byte array are its elements. -/
theorem bytes_repr_iff {N : Nat} (v : Vector UInt8 N) (B : List UInt8) :
    Data.reprBytes v B ↔ B = v.toList := by
  have e : Data.encodeBytes v = v.toList := by
    show v.toList.flatMap Data.encodeBytes = v.toList
    rw [show (Data.encodeBytes : UInt8 → List UInt8) = fun x => [x] from funext u8_encodeBytes]
    simp
  constructor
  · intro h; rw [Data.reprBytes_canon h, e]
  · intro h; subst h; rw [← e]; exact Data.reprBytes_encode v

theorem arr_u8_size (N : Nat) : (Ty.arr .u8 N).size = N := by
  simp [Ty.size]

/-- `vwrite` within the vector splices the list. -/
theorem vwrite_toList {N : Nat} : ∀ (v : Vector UInt8 N) (lo : Nat) (bs : List UInt8),
    lo + bs.length ≤ N → (vwrite v lo bs).toList = splice v.toList lo bs
  | v, lo, [], _ => by simp [vwrite, splice]
  | v, lo, b :: bs, h => by
    simp only [List.length_cons] at h
    simp only [vwrite]
    rw [vwrite_toList _ _ bs (by omega)]
    simp only [vset, show lo < N by omega, ↓reduceDIte, Vector.toList_set, splice]
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.length_append, List.length_take, List.length_set, Vector.length_toList,
        List.length_cons, List.length_drop] at h1 h2
      simp only [List.getElem_append, List.getElem_take, List.getElem_set, List.getElem_cons,
        List.getElem_drop, List.length_take, List.length_set, Vector.length_toList,
        List.length_append, List.length_cons]
      grind

/-! ## What the lowering of the arguments needs -/

/-- An atom reads no variable with a hole. -/
abbrev NoHoleAt {Γ : List Ty} {t : Ty} (S : List SI) (a : Atom Γ t) : Prop :=
  ∀ m, a = .var m → (S.getD m.idx default).hole = none

/-- A slice argument that the lowering handles. Its array place is contiguous, lawful and valid,
is accessed respecting every hole, and is not a view as a whole. The slice fits the array, and its
atoms read no variable with a hole. -/
structure SliceOk {Γ : List Ty} (ρ : List Loc) (S : List SI) (env : Env Γ) {N : Nat}
    (a : Place Γ (.arr .u8 N)) (lo len : Atom Γ .u64) : Prop where
  contig : a.contig = true
  lawful : a.Lawful
  ok : a.ok env
  fit : (lo.denote env).toNat + (len.denote env).toNat ≤ N
  nh : a.NH S
  ext : a.ExtOk S
  lo : NoHoleAt S lo
  len : NoHoleAt S len
  /-- The array is in memory, not in frame slots. -/
  ns : (ρ.getD a.root default).isSlot = false

/-- The arguments of an extern call satisfy what the lowering needs, which is `SliceOk` for each
slice. -/
def _root_.Millipede.EArgs.MOk {Γ : List Ty} (ρ : List Loc) (S : List SI) (env : Env Γ) :
    {ps : List ExtParam} → EArgs Γ ps → Prop
  | _, .nil => True
  | _, .word a as => NoHoleAt S a ∧ as.MOk ρ S env
  | _, .bufIn (.const _) as => as.MOk ρ S env
  | _, .bufIn (.slice a lo len) as => SliceOk ρ S env a lo len ∧ as.MOk ρ S env
  | _, .bufOut as => as.MOk ρ S env
  | _, .sliceOut a lo cap as => SliceOk ρ S env a lo cap ∧ as.MOk ρ S env

/-- The facts the term-level hypotheses give about an extern call's arguments. -/
theorem _root_.Millipede.EArgs.mOk_of {Γ : List Ty} {ρ : List Loc} {S : List SI} {env : Env Γ}
    {P : Nat → Bool} {ps : List ExtParam} (as : EArgs Γ ps)
    (hA : ∀ i H, (S.getD i default).hole = some H → as.Avoids i ⟨true, H.path⟩)
    (hL : as.Lawful) (hok : as.ok env) (hm : as.memOk = true) (hV : VS S P)
    (hP : ∀ i, P i = true → as.VSafe i = true)
    (hna : ∀ i, (ρ.getD i default).isSlot = true → as.noAddr i = true) : as.MOk ρ S env := by
  induction as with
  | nil => trivial
  | word a as ih =>
    exact ⟨a.noHole fun i H h => (hA i H h).1, ih (fun i H h => (hA i H h).2) hL hok hm
      (fun i h => by have := hP i h; simp only [EArgs.VSafe, Bool.and_eq_true] at this; exact this.2)
      fun i h => by simpa [EArgs.noAddr] using hna i h⟩
  | bufIn b as ih =>
    cases b with
    | const => exact ih hA hL hok hm hP fun i h => by simpa [EArgs.noAddr] using hna i h
    | slice a lo len =>
      simp only [EArgs.memOk, Bool.and_eq_true] at hm
      refine ⟨⟨hm.1, hL.1, hok.1.1, hok.1.2, a.nh_of .read fun i H h => (hA i H h).2.2.1,
        VS.place a hV fun i h => Place.VSafe_isVarAt (by
          have := hP i h; simp only [EArgs.VSafe, Bool.and_eq_true] at this; exact this.1.1.1),
        lo.noHole fun i H h => (hA i H h).1, len.noHole fun i H h => (hA i H h).2.1, ?_⟩,
        ih (fun i H h => (hA i H h).2.2.2) hL.2 hok.2 hm.2 (fun i h => by
          have := hP i h; simp only [EArgs.VSafe, Bool.and_eq_true] at this; exact this.2)
          fun i h => by have := hna i h; simp only [EArgs.noAddr, Bool.and_eq_true] at this; exact this.2⟩
      cases h : (ρ.getD a.root default).isSlot
      · rfl
      · have := hna _ h; simp [EArgs.noAddr] at this
  | bufOut as ih => exact ih hA hL hok hm hP fun i h => by simpa [EArgs.noAddr] using hna i h
  | sliceOut a lo cap as ih =>
    simp only [EArgs.memOk, Bool.and_eq_true] at hm
    refine ⟨⟨hm.1, hL.1, hok.1.1, hok.1.2, a.nh_of .write fun i H h => (hA i H h).2.2.1,
      VS.place a hV fun i h => Place.VSafe_isVarAt (by
        have := hP i h; simp only [EArgs.VSafe, Bool.and_eq_true] at this; exact this.1.1.1),
      lo.noHole fun i H h => (hA i H h).1, cap.noHole fun i H h => (hA i H h).2.1, ?_⟩,
      ih (fun i H h => (hA i H h).2.2.2) hL.2 hok.2 hm.2 (fun i h => by
        have := hP i h; simp only [EArgs.VSafe, Bool.and_eq_true] at this; exact this.2)
        fun i h => by have := hna i h; simp only [EArgs.noAddr, Bool.and_eq_true] at this; exact this.2⟩
    cases h : (ρ.getD a.root default).isSlot
    · rfl
    · have := hna _ h; simp [EArgs.noAddr] at this

/-- The address of the first mutable slice of an extern call, which is element `lo` of its array
place. -/
def _root_.Millipede.EArgs.outAddr {Γ : List Ty} (S : List SI) (env : Env Γ) :
    {ps : List ExtParam} → EArgs Γ ps → Option Nat
  | _, .nil => none
  | _, .word _ as => as.outAddr S env
  | _, .bufIn _ as => as.outAddr S env
  | _, .bufOut as => as.outAddr S env
  | _, .sliceOut a lo _ _ => some (placeA a S env + (lo.denote env).toNat)

/-! ## The one mutable slice of `extMut` -/

theorem _root_.Millipede.EArgs.fill_noOut {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps)
    (h1 : as.noOut = true) (h2 : as.noBufOut = true) (env : Env Γ) :
    ∀ (env' : Env Γ) (bss : List (List UInt8)), as.fill env env' bss = env' := by
  induction as with
  | nil => intros; rfl
  | word _ _ ih | bufIn _ _ ih => exact ih h1 h2
  | bufOut => simp [EArgs.noBufOut] at h2
  | sliceOut => simp [EArgs.noOut] at h1

theorem _root_.Millipede.EArgs.outCaps_noOut {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps)
    (h1 : as.noOut = true) (h2 : as.noBufOut = true) (env : Env Γ) : as.outCaps env = [] := by
  induction as with
  | nil => rfl
  | word _ _ ih | bufIn _ _ ih => exact ih h1 h2
  | bufOut => simp [EArgs.noBufOut] at h2
  | sliceOut => simp [EArgs.noOut] at h1

/-- The facts about the one mutable slice of an extern call whose only output buffer is a mutable
slice. They give its address, its capacity, and what writing the reply does to the environment. -/
theorem _root_.Millipede.EArgs.oneOut_spec {Γ : List Ty} {ρ : List Loc} {S : List SI} {env : Env Γ}
    {W : List Bool} {ps : List ExtParam} (as : EArgs Γ ps) (h1 : as.oneOut = true)
    (hM : as.MOk ρ S env) (hW : as.outW W) :
    ∃ (N : Nat) (a : Place Γ (.arr .u8 N)) (lo cap : Atom Γ .u64), SliceOk ρ S env a lo cap ∧
      W.getD a.root false = true ∧
      as.outAddr S env = some (placeA a S env + (lo.denote env).toNat) ∧
      as.outCaps env = [(cap.denote env).toNat] ∧
      ∀ bss, as.fill env env bss = a.set env (vwrite (a.get env) (lo.denote env).toNat (bss.headD [])) := by
  induction as with
  | nil => simp [EArgs.oneOut] at h1
  | word _ _ ih => exact ih h1 hM.2 hW
  | bufIn b _ ih => cases b <;> first | exact ih h1 hM hW | exact ih h1 hM.2 hW
  | bufOut => simp [EArgs.oneOut] at h1
  | sliceOut a lo cap as _ =>
    simp only [EArgs.oneOut, Bool.and_eq_true] at h1
    refine ⟨_, a, lo, cap, hM.1, hW.1, rfl, ?_, fun bss => ?_⟩
    · simp [EArgs.outCaps, as.outCaps_noOut h1.1 h1.2]
    · simp only [EArgs.fill]; exact as.fill_noOut h1.1 h1.2 _ _ _

/-! ## Running the argument code -/

/-- The bytes an extern reads from memory are `rd`. -/
theorem heap_read_eq (h : Heap) : ∀ (A n : Nat), h.read (UInt64.ofNat A) n = rd h A n
  | _, 0 => rfl
  | A, n + 1 => by
    simp only [rd]
    rw [← heap_read_eq h (A + 1) n]
    simp only [Heap.read, List.range_succ_eq_map, List.map_cons, List.map_map, ofNat_add_ofNat,
      Nat.add_zero, List.cons.injEq, true_and]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [show A + (i + 1) = A + 1 + i by omega]

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- A slice argument puts the address of element `lo` in slot `x` and the length in `x + 1`, and
only `RA`, `RX` and those two slots change. -/
theorem sliceArg_runs {Γ : List Ty} {N : Nat} (a : Place Γ (.arr .u8 N)) (lo len : Atom Γ .u64)
    {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    {x : Nat} (hx : RX < x) (hxF : x + 1 < FR) (hf : f BP = UInt64.ofNat bp)
    (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W) (hs : SliceOk ρ S env a lo len) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) :
    ∃ f', Runs κ ω L (extArgs.sliceArg a lo len ρ x) f h f' h ∧
      (∀ y, y < x → y ≠ RA → y ≠ RX → f' y = f y) ∧
      f' x = UInt64.ofNat (placeA a S env + (lo.denote env).toNat) ∧
      f' (x + 1) = len.denote env ∧ placeA a S env + N ≤ bp + n ∧
      rd h (placeA a S env) N = (a.get env).toList := by
  obtain ⟨f₁, hr₁, hb₁, ha₁, hx₁⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) a hs.contig hf henv
    hfe hl hs.nh.1 hs.lawful (hs.ext.notPair hl) hnL hnU
  obtain ⟨f₂, hr₂, hb₂, ha₂, hx₂⟩ := elemAddr_runs (κ := κ) (ω := ω) (L := L) lo Ty.u8.size _
    (hb₁.trans hf) ha₁ henv (hfe.keep hr₁.keep) hl hs.lo hnL hnU
  have hg := place_get a hs.contig hs.lawful hs.ok henv hl hs.nh.2 hs.ext hs.ns
  rw [arr_u8_size] at hg
  have hx0 : BP ≠ x := by unfold BP RX at *; omega
  have hxa : RA ≠ x := by unfold RA RX at *; omega
  have hbf : (f₂.set x (f₂ RA)) BP = UInt64.ofNat bp := by
    rw [Frame.set_ne _ _ hx0, hb₂, hb₁, hf]
  refine ⟨_, Runs.seq (Runs.seq hr₁ hr₂) (Runs.seq (Runs.mov _ _ _ _ (by omega))
      (atomWord_u64 len (x + 1) hbf henv (hfe.keep fun y hy => by
        rw [Frame.set_ne _ _ (by omega)]; exact (hr₂.keep y hy).trans (hr₁.keep y hy))
        hl hs.len hnL hnU hxF)), fun y hy h1 h2 => ?_, ?_, ?_, hg.1,
    (bytes_repr_iff _ _).1 hg.2⟩
  · simp only [eval_slot]
    rw [Frame.set_ne _ _ (by omega), Frame.set_ne _ _ (by omega), hx₂ y h1 h2, hx₁ y h1 h2]
  · simp only [eval_slot]
    rw [Frame.set_ne _ _ (by omega), Frame.set_same, ha₂]
    simp [Ty.size]
  · simp [Frame.set_same]

/-- The argument code of an extern call loads the words and the slices' addresses and lengths into
slots from `x`. The Flat call record it builds is the Core one, its memory buffers lie below `L`,
and its first output buffer in memory is at the first mutable slice's address. -/
theorem extArgs_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat}
    {env : Env Γ} {h : Heap} (hl : Lay bp n Γ ρ S W) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) {ps : List ExtParam} (args : EArgs Γ ps) :
    ∀ (x : Nat) (f : Frame), RX < x → x + args.wordCount ≤ FR → f BP = UInt64.ofNat bp →
      MEnvRel h bp env ρ S → FEnvRel f env ρ → args.MOk ρ S env →
      ∃ f', Runs κ ω L (extArgs args ρ x).1 f h f' h ∧
        (∀ y, y < x → y ≠ RA → y ≠ RX → f' y = f y) ∧
        extWords f' (extArgs args ρ x).2 = args.words env ∧
        extBytes h f' (extArgs args ρ x).2 = args.bytesIn env ∧
        extCaps f' (extArgs args ρ x).2 = args.outCaps env ∧
        ExtAccIn L f' (extArgs args ρ x).2 ∧
        ∀ o c, extOutArg (extArgs args ρ x).2 = some (o, c) →
          ∃ A, args.outAddr S env = some A ∧ o.eval f' = UInt64.ofNat A := by
  induction args with
  | nil =>
    intro x f _ _ _ _ _ _
    exact ⟨f, Runs.skip _ _, fun _ _ _ _ => rfl, rfl, rfl, rfl, trivial, fun _ _ h => by
      simp [extArgs, extOutArg] at h⟩
  | word a as ih =>
    intro x f hx hxF hf henv hfe hm
    have hx0 : BP ≠ x := by unfold BP RX at *; omega
    simp only [EArgs.wordCount] at hxF
    obtain ⟨f', hr, hlt, hw, hb, hc, hacc, hout⟩ := ih (x + 1) (f.set x (a.denote env))
      (by omega) (by omega) (by rw [Frame.set_ne _ _ hx0]; exact hf) henv
      (hfe.keep (Frame.set_keep f _ (by omega))) hm.2
    have hfx : f' x = a.denote env := by
      rw [hlt x (by omega) (by unfold RA RX at *; omega) (by unfold RX at *; omega)]
      simp [Frame.set]
    refine ⟨f', Runs.seq (atomWord_u64 a x hf henv hfe hl hm.1 hnL hnU (by omega)) hr,
      fun y hy h1 h2 => by
      rw [hlt y (by omega) h1 h2, Frame.set_ne _ _ (by omega)], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [extArgs, extWords, eval_slot, EArgs.words, hw, hfx]
    · simpa [extArgs, extBytes, EArgs.bytesIn] using hb
    · simpa [extArgs, extCaps, EArgs.outCaps] using hc
    · simpa [extArgs, ExtAccIn] using hacc
    · intro o c ho
      simp only [extArgs, extOutArg] at ho
      simpa [EArgs.outAddr] using hout o c ho
  | bufIn b as ih =>
    cases b with
    | const bs =>
      intro x f hx hxF hf henv hfe hm
      obtain ⟨f', hr, hlt, hw, hb, hc, hacc, hout⟩ := ih x f hx (by simpa [EArgs.wordCount] using hxF)
        hf henv hfe hm
      refine ⟨f', hr, hlt, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [extArgs, extWords, EArgs.words] using hw
      · simp [extArgs, extBytes, EArgs.bytesIn, Buf.denote, hb]
      · simpa [extArgs, extCaps, EArgs.outCaps] using hc
      · simpa [extArgs, ExtAccIn] using hacc
      · intro o c ho
        simp only [extArgs, extOutArg] at ho
        simpa [EArgs.outAddr] using hout o c ho
    | slice a lo len =>
      intro x f hx hxF hf henv hfe hm
      simp only [EArgs.wordCount] at hxF
      obtain ⟨f₁, hr₁, hlt₁, hx₁, hx₁', hA, hrd⟩ := sliceArg_runs (κ := κ) (ω := ω) (L := L) a lo len
        hx (by omega) hf henv hfe hl hm.1 hnL hnU
      have hbf : f₁ BP = UInt64.ofNat bp := by
        rw [hlt₁ BP (by unfold BP RX at *; omega) (by decide) (by decide), hf]
      obtain ⟨f', hr, hlt, hw, hb, hc, hacc, hout⟩ := ih (x + 2) f₁ (by omega) (by omega) hbf henv
        (hfe.keep hr₁.keep) hm.2
      have e1 : f' x = f₁ x := hlt x (by omega) (by unfold RA RX at *; omega)
        (by unfold RX at *; omega)
      have e2 : f' (x + 1) = f₁ (x + 1) := hlt (x + 1) (by omega) (by unfold RA RX at *; omega)
        (by unfold RX at *; omega)
      have hfit := hm.1.fit
      refine ⟨f', Runs.seq hr₁ hr, fun y hy h1 h2 => by
        rw [hlt y (by omega) h1 h2, hlt₁ y (by omega) h1 h2], ?_, ?_, ?_, ?_, ?_⟩
      · simpa [extArgs, extWords, EArgs.words] using hw
      · simp only [extArgs, extBytes, EArgs.bytesIn, Buf.denote, eval_slot, e1, e2, hx₁, hx₁',
          heap_read_eq, hb]
        rw [rd_slice h _ _ _ _ hfit, hrd]; rfl
      · simpa [extArgs, extCaps, EArgs.outCaps] using hc
      · simp only [extArgs, ExtAccIn, eval_slot, e1, e2, hx₁, hx₁']
        refine ⟨?_, hacc⟩
        have := Nat.mod_le (placeA a S env + (lo.denote env).toNat) UInt64.size
        rw [UInt64.toNat_ofNat']; omega
      · intro o c ho
        simp only [extArgs, extOutArg] at ho
        simpa [EArgs.outAddr] using hout o c ho
  | bufOut as ih =>
    intro x f hx hxF hf henv hfe hm
    obtain ⟨f', hr, hlt, hw, hb, hc, hacc, hout⟩ := ih x f hx (by simpa [EArgs.wordCount] using hxF)
      hf henv hfe hm
    refine ⟨f', hr, hlt, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [extArgs, extWords, EArgs.words] using hw
    · simpa [extArgs, extBytes, EArgs.bytesIn] using hb
    · simp [extArgs, extCaps, EArgs.outCaps, hc]
    · simpa [extArgs, ExtAccIn] using hacc
    · intro o c ho
      simp only [extArgs, extOutArg] at ho
      simpa [EArgs.outAddr] using hout o c ho
  | sliceOut a lo cap as ih =>
    intro x f hx hxF hf henv hfe hm
    simp only [EArgs.wordCount] at hxF
    obtain ⟨f₁, hr₁, hlt₁, hx₁, hx₁', hA, hrd⟩ := sliceArg_runs (κ := κ) (ω := ω) (L := L) a lo cap
      hx (by omega) hf henv hfe hl hm.1 hnL hnU
    have hbf : f₁ BP = UInt64.ofNat bp := by
      rw [hlt₁ BP (by unfold BP RX at *; omega) (by decide) (by decide), hf]
    obtain ⟨f', hr, hlt, hw, hb, hc, hacc, -⟩ := ih (x + 2) f₁ (by omega) (by omega) hbf henv
      (hfe.keep hr₁.keep) hm.2
    have e1 : f' x = f₁ x := hlt x (by omega) (by unfold RA RX at *; omega)
      (by unfold RX at *; omega)
    have e2 : f' (x + 1) = f₁ (x + 1) := hlt (x + 1) (by omega) (by unfold RA RX at *; omega)
      (by unfold RX at *; omega)
    have hfit := hm.1.fit
    refine ⟨f', Runs.seq hr₁ hr, fun y hy h1 h2 => by
      rw [hlt y (by omega) h1 h2, hlt₁ y (by omega) h1 h2], ?_, ?_, ?_, ?_, ?_⟩
    · simpa [extArgs, extWords, EArgs.words] using hw
    · simpa [extArgs, extBytes, EArgs.bytesIn] using hb
    · simp [extArgs, extCaps, EArgs.outCaps, hc, e2, hx₁']
    · simp only [extArgs, ExtAccIn, eval_slot, e1, e2, hx₁, hx₁']
      refine ⟨?_, hacc⟩
      have := Nat.mod_le (placeA a S env + (lo.denote env).toNat) UInt64.size
      rw [UInt64.toNat_ofNat']; omega
    · intro o c ho
      simp only [extArgs, extOutArg, Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      exact ⟨_, rfl, by rw [eval_slot, e1, hx₁]⟩

/-- Without a mutable slice, the lowered arguments have no output buffer in memory. -/
theorem extArgs_noOut {Γ : List Ty} {ρ : List Loc} {ps : List ExtParam} (args : EArgs Γ ps)
    (h : args.noOut = true) : ∀ x, extOutArg (extArgs args ρ x).2 = none := by
  induction args with
  | nil => intro; rfl
  | word _ _ ih | bufOut _ ih => intro x; simpa [extArgs, extOutArg] using ih h _
  | bufIn b _ ih => cases b <;> intro x <;> simpa [extArgs, extOutArg] using ih h _
  | sliceOut => simp [EArgs.noOut] at h

/-- The extern's write into a mutable slice. The bytes `bs`, at most the capacity, written from the
address of element `lo` represent the environment where the array holds `vwrite` of them, and
nothing outside the array's storage changes. -/
theorem out_write_rel {Γ : List Ty} {N : Nat} (a : Place Γ (.arr .u8 N)) (lo cap : Atom Γ .u64)
    {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap}
    (hs : SliceOk ρ S env a lo cap) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hW : W.getD a.root false = true) (hbn : bp + n ≤ UInt64.size) (bs : List UInt8)
    (hbs : bs.length ≤ (cap.denote env).toNat) :
    MEnvRel (wr h (placeA a S env + (lo.denote env).toNat) bs) bp
        (a.set env (vwrite (a.get env) (lo.denote env).toNat bs)) ρ S ∧
      ∀ x, x < UInt64.size → ¬ InR (placeA a S env) N x →
        wr h (placeA a S env + (lo.denote env).toNat) bs (UInt64.ofNat x) = h (UInt64.ofNat x) := by
  have hg := place_get a hs.contig hs.lawful hs.ok henv hl hs.nh.2 hs.ext hs.ns
  rw [arr_u8_size] at hg
  have hfit := hs.fit
  have hrd := (bytes_repr_iff _ _).1 hg.2
  have hout : ∀ x, x < UInt64.size → ¬ InR (placeA a S env) N x →
      wr h (placeA a S env + (lo.denote env).toNat) bs (UInt64.ofNat x) = h (UInt64.ofNat x) :=
    fun x hx hn => wr_other _ _ _ _ hx (by omega) (by unfold InR at hn; omega)
  refine ⟨place_set a hs.contig hs.lawful hs.ok henv hl hW hbn hs.ext hs.ns _ _
    (fun x hx hn => hout x (by omega) (by rwa [arr_u8_size] at hn)) ?_, hout⟩
  rw [arr_u8_size, bytes_repr_iff, vwrite_toList _ _ _ (by omega), ← hrd,
    rd_splice (o := (lo.denote env).toNat) (m := bs.length) (by omega) fun i hi hio =>
      wr_other _ _ _ _ (by omega) (by omega) (by omega), rd_wr _ _ _ (by omega)]

/-- With a mutable slice, the lowered arguments have an output buffer in memory. -/
theorem extArgs_out {Γ : List Ty} {ρ : List Loc} {ps : List ExtParam} (args : EArgs Γ ps)
    (h : args.noOut = false) : ∀ x, ∃ o c, extOutArg (extArgs args ρ x).2 = some (o, c) := by
  induction args with
  | nil => simp [EArgs.noOut] at h
  | word _ _ ih | bufOut _ ih => intro x; simpa [extArgs, extOutArg] using ih h _
  | bufIn b _ ih => cases b <;> intro x <;> simpa [extArgs, extOutArg] using ih h _
  | sliceOut => intro x; exact ⟨_, _, rfl⟩

theorem _root_.Millipede.EArgs.noOut_of_oneOut {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps)
    (h : as.oneOut = true) : as.noOut = false := by
  induction as with
  | nil | bufOut => simp [EArgs.oneOut] at h
  | word _ _ ih | bufIn _ _ ih => exact ih h
  | sliceOut => rfl

/-- The tick of an extern call pays `exec`'s charge. -/
theorem tick_ext_cost {Γ : List Ty} {ps : List ExtParam} (args : EArgs Γ ps) :
    (Tick.ext args.depth args.slices).cost κ = κ.ext + args.cost κ := by
  simp [Tick.cost, EArgs.cost, Nat.add_assoc]

/-- An extern call without an output buffer, with its word into slot `x`, loads the arguments into
`REXT…` and makes the call. The frame from `FR` on is unchanged except `x`, and the memory is
unchanged. -/
theorem ext_reach {Γ : List Ty} (sig : ExtSig) (args : EArgs Γ sig.params)
    (hno : args.noOut = true) (hm : args.memOk = true) (hwc : args.wordCount ≤ FR - REXT)
    {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    {w : World} {tm : Tl} (H : MHyp ω (.ext sig args) tm L W ρ S n d bp env f h w) (x : Nat)
    (rest : Stmt) (K : List Kont) (c : Nat) :
    ∃ f₁ : Frame, f₁ BP = f BP ∧ (∀ y, FR ≤ y → f₁ y = f y) ∧
      ReachL κ ω L ⟨.seq (.tick (.ext args.depth args.slices)) (.seq (extArgs args ρ REXT).1
          (.seq (.ext sig.sym sig.noreturn x (extArgs args ρ REXT).2) rest)), K, f, h, w, c⟩
        ⟨.skip, .seq rest :: K, f₁.set x (Exp.exec ω κ .copy (.ext sig args) env w).val, h,
          (Exp.exec ω κ .copy (.ext sig args) env w).world, c + (Exp.exec ω κ .copy (.ext sig args) env w).steps⟩ := by
  have hb := H.nU; have hbL := H.nL
  have hM : args.MOk ρ S env := args.mOk_of (fun i H' h' => H.hole i H' h') H.lawful H.safe hm H.vs
    (fun i h => by simpa [Exp.VSafe] using h) fun i h => by simpa [Exp.noAddr] using (H.sl.na i h).1
  obtain ⟨f₁, hr₁, hlt, hws, hbs, hcs, hacc, -⟩ := extArgs_runs (κ := κ) (ω := ω) H.lay (L := L)
    (by omega) (by omega) args REXT f (by decide) (by simp only [REXT, FR] at hwc ⊢; omega)
    H.bpOk H.envRel H.sl.rel hM
  have hcall : (⟨sig.sym, extWords f₁ (extArgs args ρ REXT).2, extBytes h f₁ (extArgs args ρ REXT).2,
      extCaps f₁ (extArgs args ρ REXT).2⟩ : Call) = sig.call args env := by
    simp only [ExtSig.call, hws, hbs, hcs]
  refine ⟨f₁, hlt BP (by decide) (by decide) (by decide), hr₁.keep, ?_⟩
  simp only [Exp.exec]
  refine ReachL.step' H.run (by simp only [exec1]; exact ReachL.step' H.run (by
    simp only [exec1]; exact ReachL.step' H.run (by
    simp only [exec1, tick_ext_cost]; exact ReachL.step' H.run (by
    simp only [exec1]; exact (hr₁.run _ w _ H.run).trans (ReachL.step' H.run (by
    simp only [exec1]; exact ReachL.step' H.run (by
    simp only [exec1]; exact ReachL.step' H.run (by
    simp only [exec1, extRun_none (extArgs_noOut args hno REXT)]; rw [hcall]
    exact ReachL.refl _) hacc)))))))

/-- The case of an extern call without an output buffer, whose word goes through `RX` to the
destination. -/
theorem msound_ext {Γ : List Ty} (sig : ExtSig) (args : EArgs Γ sig.params)
    (hno : args.noOut = true) (hm : args.memOk = true) (hwc : args.wordCount ≤ FR - REXT) :
    MSoundAt κ ω (.ext sig args) := by
  refine .leafW (fun L W ρ S n d bp env k f h w c H => ?_) fun K L W ρ S n d bp env k f h w c H => ?_
  rotate_left
  · obtain ⟨f₁, hf₁, hk₁, hreach⟩ := ext_reach (κ := κ) sig args hno hm hwc H K .skip k c
    simp only [lowerM]
    generalize Exp.exec ω κ .copy (.ext sig args) env w = r at hreach ⊢
    cases hh : r.world.halted with
    | true => exact ⟨_, hreach, rfl, Nat.le_refl _, Or.inl hh⟩
    | false =>
      have hK := H.tmOk.1
      refine ⟨⟨.skip, k, f₁.set K r.val, h, r.world, c + r.steps⟩,
        hreach.trans (ReachL.step' hh (by simp only [exec1]; exact ReachL.refl _)), rfl,
        Nat.le_refl _, Or.inr ⟨rfl, rfl, rfl, ?_, ?_, fun _ _ => rfl, fun x hx hp => ?_⟩⟩
      · simp only; rw [Frame.set_ne _ _ (by simp only [FR, BP] at hK ⊢; omega)]; exact hf₁
      · exact (wordsRel_one (by decide)).2 (by show WordRel _ _ ((f₁.set K r.val) K); rw [Frame.set_same]; exact wordRel_u64 _)
      · simp only; rw [Frame.set_ne _ _ (Nat.ne_of_lt (SProt.lt_word H.tmOk hp))]; exact hk₁ x hx
  have hdn := H.dn0; have hd := H.away0; have hb := H.nU; have hbL := H.nL
  obtain ⟨f₁, hf₁, hk₁, hreach⟩ := ext_reach (κ := κ) sig args hno hm hwc H RX
    (.store .w64 (.slot BP) (UInt64.ofNat d) (.slot RX)) k c
  have hf₁' : f₁ BP = UInt64.ofNat bp := hf₁.trans H.bpOk
  generalize Exp.exec ω κ .copy (.ext sig args) env w = r at hreach ⊢
  cases hh : r.world.halted with
  | true => exact ⟨_, hreach, rfl, Nat.le_refl _, Or.inl hh⟩
  | false =>
    obtain ⟨B, hBl, hBr, hBs⟩ := storeOk_u64 r.val h (bp + d)
    rw [show scalarWidth Ty.u64.size = .w64 by decide] at hBs
    refine ⟨⟨.skip, k, f₁.set RX r.val, wr h (bp + d) B, r.world, c + r.steps⟩,
      hreach.trans (ReachL.step' hh (by simp only [exec1]; exact ReachL.step' hh (by
        simp only [exec1, eval_slot, Frame.set, ↓reduceIte, show (BP = RX) = False by decide,
          hf₁', ofNat_add_ofNat, hBs]; exact ReachL.refl _) (by
        show ((Operand.slot BP).eval (f₁.set RX r.val) + UInt64.ofNat d).toNat + Width.bytes .w64 ≤ L
        rw [eval_slot, Frame.set_ne _ _ (by decide), hf₁', ofNat_add_ofNat]
        exact acc_ofNat (by simp only [Width.bytes]; have : Ty.u64.size = 8 := rfl; omega)
          (by have : Ty.u64.size = 8 := rfl; omega)))), rfl, Nat.le_refl _,
      Or.inr ⟨rfl, rfl, rfl, by simp [Frame.set, hf₁', H.bpOk], ?_, ?_,
        fun x hx _ => (Frame.set_keep f₁ _ (by decide) x hx).trans (hk₁ x hx)⟩⟩
    · show Data.reprBytes _ (rd _ _ Ty.u64.size)
      rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr
    · intro x hx; unfold Prot InR at hx
      exact wr_out (by omega) (by omega) (by omega)

/-- The case of an extern call writing a mutable slice, as in `read(fd, &mut a[lo..lo+cap])`. The
machine writes at most `cap` bytes of the reply from the address of element `lo`, which represents
the array written with `vwrite`, and the result word is stored as the continuation's variable. -/
theorem msound_extMut {Γ : List Ty} {u : Ty} (sig : ExtSig) (args : EArgs Γ sig.params)
    (k : Exp (.u64 :: Γ) u) (h1 : args.oneOut = true) (hm : args.memOk = true)
    (hwc : args.wordCount ≤ FR - REXT) (ih : MSoundAt κ ω k) : MSoundAt κ ω (.extMut sig args k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed] at hb hbL
  have hCk : k.Conf tm.up = true := by
    cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using H.conf
  obtain ⟨hok, hsk⟩ := H.safe
  have hM : args.MOk ρ S env := args.mOk_of (fun i H' h' => (H.hole i H' h').1) H.lawful.1 hok hm
    H.vs (fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1) fun i h => by
      have := (H.sl.na i h).1; simp only [Exp.noAddr, Bool.and_eq_true] at this; exact this.1
  obtain ⟨N, a, lo, cap, hs, hW, hoa, hcaps, hfill⟩ := args.oneOut_spec h1 hM H.restr.1
  obtain ⟨f₁, hr₁, hlt, hws, hbs, hcs, hacc, hout⟩ := extArgs_runs (κ := κ) (ω := ω) H.lay (L := L)
    (by omega) (by omega) args REXT f (by decide) (by simp only [REXT, FR] at hwc ⊢; omega)
    H.bpOk H.envRel H.sl.rel hM
  have hf₁ : f₁ BP = UInt64.ofNat bp := (hlt BP (by decide) (by decide) (by decide)).trans H.bpOk
  obtain ⟨o, c', hoc⟩ := extArgs_out (ρ := ρ) args (args.noOut_of_oneOut h1) REXT
  obtain ⟨A, hA, hoe⟩ := hout o c' hoc
  rw [hoa] at hA; cases hA
  have hcall : (⟨sig.sym, extWords f₁ (extArgs args ρ REXT).2, extBytes h f₁ (extArgs args ρ REXT).2,
      extCaps f₁ (extArgs args ρ REXT).2⟩ : Call) = sig.call args env := by
    simp only [ExtSig.call, hws, hbs, hcs]
  generalize hq : w.ask ω (sig.call args env) sig.noreturn = q
  generalize hbs' : (fitOut (sig.call args env).outCaps q.1.bytesOut).headD [] = bs
  have hbsl : bs.length ≤ (cap.denote env).toNat := by
    rw [← hbs']; simp only [ExtSig.call, hcaps]; exact fitOut_one_le _ _
  have hrun : extRun ω sig.sym sig.noreturn (extArgs args ρ REXT).2 f₁ h w =
      (q.1.result, wr h (placeA a S env + (lo.denote env).toNat) bs, q.2) := by
    rw [← hbs']; simp only [extRun, hoc, hoe, writeBytes_eq_wr]; rw [hcall, hq, hcs]; rfl
  obtain ⟨henv₁, hout₁⟩ := out_write_rel a lo cap hs H.envRel H.lay hW (by omega) bs hbsl
  have hdenv : args.fill env env (fitOut (sig.call args env).outCaps q.1.bytesOut) =
      a.set env (vwrite (a.get env) (lo.denote env).toNat bs) := by rw [hfill, hbs']
  -- the call, from the tick to the state after the extern, with its word in slot `x`
  have hreach : ∀ (x : Nat) (rest : Stmt), ReachL κ ω L ⟨.seq (.tick (.ext args.depth args.slices))
        (.seq (extArgs args ρ REXT).1 (.seq (.ext sig.sym sig.noreturn x (extArgs args ρ REXT).2)
          rest)), kk, f, h, w, c⟩
      ⟨.skip, .seq rest :: kk, f₁.set x q.1.result, wr h (placeA a S env + (lo.denote env).toNat) bs,
        q.2, c + (κ.ext + args.cost κ)⟩ := by
    intro x rest
    refine ReachL.step' H.run (by simp only [exec1]; exact ReachL.step' H.run (by
      simp only [exec1]; exact ReachL.step' H.run (by
      simp only [exec1, tick_ext_cost]; exact ReachL.step' H.run (by
      simp only [exec1]; exact (hr₁.run _ w _ H.run).trans (ReachL.step' H.run (by
      simp only [exec1]; exact ReachL.step' H.run (by
      simp only [exec1]; exact ReachL.step' H.run (by
      simp only [exec1, hrun]; exact ReachL.refl _) hacc)))))))
  rw [hq, hdenv] at hsk
  have hexec : Exp.exec ω κ tm.hb (.extMut sig args k) env w =
      ⟨(k.exec ω κ tm.up.hb (.cons q.1.result (a.set env (vwrite (a.get env) (lo.denote env).toNat bs))) q.2).val,
       (k.exec ω κ tm.up.hb (.cons q.1.result (a.set env (vwrite (a.get env) (lo.denote env).toNat bs))) q.2).world,
       κ.ext + args.cost κ +
        (k.exec ω κ tm.up.hb (.cons q.1.result (a.set env (vwrite (a.get env) (lo.denote env).toNat bs))) q.2).steps⟩ := by
    simp only [Exp.exec, hq, hdenv, Tl.hb_up]
  rw [hexec]
  -- the bytes of the slice's array lie in a writable root, so they are not protected
  have hprot : ∀ x, Prot bp n d (tm.dsz u) Γ S W x → ¬ InR (placeA a S env) N x := fun x hx hin =>
    hx.2.2 (InW.place a hW (place_in a hs.contig hs.lawful hs.ok H.envRel H.lay hs.ext
      (by rwa [arr_u8_size])) H.lay.length.2)
  simp only [lowerM]
  cases hh : q.2.halted with
  | true =>
    split <;>
    · refine ⟨_, hreach _ _, (exec_halted ω κ k _ _ hh).symm, by simp only; omega, Or.inl ?_⟩
      rw [exec_halted ω κ k _ _ hh]; exact hh
  | false =>
  have hfk₁ : ∀ x, FR ≤ x → f₁ x = f x := hr₁.keep
  have hV := H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2
  split
  · -- a slot-resident result: the extern's word straight into the binder's slot
    rename_i hsb
    simp only [Exp.slotBind, Bool.and_eq_true] at hsb
    have h8 : Ty.u64.size = 8 := rfl
    have hfK : (f₁.set (FR + slotsIn ρ) q.1.result) BP = UInt64.ofNat bp := by
      rw [Frame.set_slot_BP, hf₁]
    have hK := ih.app (H.pushSlot q.1.result (Nat.le_refl _) hCk H.restr.2 H.lawful.2 H.frozen
      (H.hole.push _ rfl fun _ _ h => h.2) (by omega) (by omega) hfK henv₁
      (((H.sl.rel.keep hfk₁).place_set a hs.ns _).below H.sl.ok fun x _ hx =>
        Frame.set_ne _ _ (by omega)) rfl
      ((wordsRel_one (by decide)).2 (by rw [Frame.set_same]; exact wordRel_u64 _)) hsk hV hh hsb.1.2
      (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2)) kk
      (c + (κ.ext + args.cost κ))
    refine (MSim.pre ((hreach _ _).trans (ReachL.step' hh (by simp only [exec1]; exact ReachL.refl _)))
      rfl (hfK.trans H.bpOk.symm) (fun x hx => hout₁ x (by have := hx.1; omega) (hprot x hx))
      (fun x hx hp => by
        show (f₁.set _ _) x = f x
        rw [Frame.set_ne _ _ (by have := SProt.lt H.sl.ok hp; omega)]; exact hfk₁ x hx)
      (.unpush (Nat.le_refl _) hK)).of_eq rfl rfl rfl
  · have h8 : Ty.u64.size = 8 := rfl
    obtain ⟨B, hBl, hBr, hBs⟩ := storeOk_u64 q.1.result (wr h (placeA a S env + (lo.denote env).toNat) bs)
      (bp + n)
    rw [show scalarWidth Ty.u64.size = .w64 by decide] at hBs
    have hf₂ : (f₁.set RX q.1.result) BP = UInt64.ofNat bp := by
      rw [Frame.set_ne _ _ (by decide), hf₁]
    have hv : Data.reprBytes q.1.result
        (rd (wr (wr h (placeA a S env + (lo.denote env).toNat) bs) (bp + n) B) (bp + n) Ty.u64.size) := by
      rw [← hBl, rd_wr _ _ _ (by have : Ty.u64.size = 8 := rfl; omega)]; exact hBr
    have hfk₂ : ∀ x, FR ≤ x → (f₁.set RX q.1.result) x = f x := fun x hx =>
      (Frame.set_keep f₁ _ (by decide) x hx).trans (hr₁.keep x hx)
    have hK := ih.app (H.push q.1.result (Nat.le_refl _) hCk H.restr.2 H.lawful.2 H.frozen
      (H.hole.push _ rfl fun _ _ h => h.2) (by omega) (by omega) hf₂
      (henv₁.above H.lay fun y hy => wr_out (by have : Ty.u64.size = 8 := rfl; omega) (by omega)
        (by have : Ty.u64.size = 8 := rfl; omega))
      ((H.sl.rel.keep hfk₂).place_set a hs.ns _) hv hsk
      (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2) hh) kk
      (c + (κ.ext + args.cost κ))
    have hreach₂ : ReachL κ ω L ⟨.skip, .seq (.seq (.store .w64 (.slot BP) (UInt64.ofNat n) (.slot RX))
          (lowerM k tm.up (.own n :: ρ) (n + 8) d)) :: kk,
        f₁.set RX q.1.result, wr h (placeA a S env + (lo.denote env).toNat) bs, q.2,
        c + (κ.ext + args.cost κ)⟩
        ⟨lowerM k tm.up (.own n :: ρ) (n + 8) d, kk, f₁.set RX q.1.result,
          wr (wr h (placeA a S env + (lo.denote env).toNat) bs) (bp + n) B, q.2,
          c + (κ.ext + args.cost κ)⟩ :=
      ReachL.step' hh (by simp only [exec1]; exact ReachL.step' hh (by
        simp only [exec1]; exact ReachL.step' hh (by
        simp only [exec1, eval_slot, hf₂, ofNat_add_ofNat, Frame.set_same, hBs]
        exact ReachL.step' hh (by simp only [exec1]; exact ReachL.refl _)) (by
          show ((Operand.slot BP).eval (f₁.set RX q.1.result) + UInt64.ofNat n).toNat +
            Width.bytes .w64 ≤ L
          rw [eval_slot, hf₂, ofNat_add_ofNat]
          exact acc_ofNat (by simp only [Width.bytes]; omega) (by omega))))
    refine (MSim.pre ((hreach _ _).trans hreach₂) rfl (hf₂.trans H.bpOk.symm) (fun x hx => ?_)
      (fun x hx _ => hfk₂ x hx) (.unpush (Nat.le_refl _) hK)).of_eq rfl rfl rfl
    have hx1 := hx.1
    show wr (wr h _ bs) (bp + n) B (UInt64.ofNat x) = h (UInt64.ofNat x)
    rw [wr_out (by have : Ty.u64.size = 8 := rfl; omega) (by omega) (by omega),
      hout₁ x (by omega) (hprot x hx)]

end

end Millipede.Flat
