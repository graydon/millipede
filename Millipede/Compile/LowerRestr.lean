import Millipede.Compile.LowerInv

/-!
# The checker implies the block rule

`Exp.check` tracks, for each binder, whether it may be written in the current block and its mode,
and a `shr` binder, an `&` reference, is never written. The memory refinement relies on the block
rule `Exp.Restr e W`, which is stated with a list of writable flags `W`. This module proves, as
`Exp.restr_of_check`, that a term the checker accepts from a state `st` obeys the block rule for
the flags of `st`, which are the binders writable in the block and not `&`.

The proof is one induction over the term. It rests on three facts. The checker never makes a binder
more writable, because the uses keep each binder's flag and mode, entering a block clears the
flags, leaving it restores the outer ones, and the inner binder is dropped when it goes out of
scope. A write access succeeds only on a binder that is writable and not `&`. And `Exp.Restr` is
monotone in its flags.
-/

namespace Millipede.Flat

/-- The writable flags of a checker state: binders that are writable in the current block and
not `&` references. -/
def wflags (st : List BS) : List Bool := st.map fun b => b.wr && b.mode != .shr

/-! ## Flags order -/

/-- Every variable writable under `W` is writable under `W'`. -/
def WLe (W W' : List Bool) : Prop := ∀ k, W.getD k false = true → W'.getD k false = true

theorem WLe.refl (W : List Bool) : WLe W W := fun _ h => h

theorem WLe.trans {W₁ W₂ W₃ : List Bool} (h₁ : WLe W₁ W₂) (h₂ : WLe W₂ W₃) : WLe W₁ W₃ :=
  fun k h => h₂ k (h₁ k h)

theorem WLe.cons {b b' : Bool} {W W' : List Bool} (hb : b = true → b' = true) (h : WLe W W') :
    WLe (b :: W) (b' :: W') := by
  intro k hk
  cases k with
  | zero => simpa using hb (by simpa using hk)
  | succ k => simpa using h k (by simpa using hk)

theorem WLe.tail {b b' : Bool} {W W' : List Bool} (h : WLe (b :: W) (b' :: W')) : WLe W W' :=
  fun k hk => by simpa using h (k + 1) (by simpa using hk)

theorem WLe.of_eq {W W' : List Bool} (h : W = W') : WLe W W' := h ▸ WLe.refl _

theorem WLe.nil (W : List Bool) : WLe [] W := fun k h => by simp at h

theorem WLe.of_noW (W W' : List Bool) : WLe (noW W) W' := fun k h => by
  rw [noW_getD] at h; cases h

/-! ## Monotonicity of the block rule -/

theorem _root_.Millipede.RArgs.mutW_mono {Γ : List Ty} {W W' : List Bool} (hW : WLe W W') :
    {ps os : List Ty} → (as : RArgs Γ ps os) → as.mutW W → as.mutW W'
  | _, _, .nil, _ => trivial
  | _, _, .own _ as, h => as.mutW_mono hW h
  | _, _, .shr _ as, h => as.mutW_mono hW h
  | _, _, .mut _ as, h => ⟨hW _ h.1, as.mutW_mono hW h.2⟩

theorem _root_.Millipede.EArgs.outW_mono {Γ : List Ty} {W W' : List Bool} (hW : WLe W W')
    {ps : List ExtParam} (as : EArgs Γ ps) (h : as.outW W) : as.outW W' := by
  induction as with
  | nil => trivial
  | word _ _ ih | bufIn _ _ ih | bufOut _ ih => exact ih h
  | sliceOut _ _ _ _ ih => exact ⟨hW _ h.1, ih h.2⟩

theorem WLe.selW (xs : List Nat) (k : Nat) {W W' : List Bool} (h : WLe W W') :
    WLe (selW xs k W) (selW xs k W') := fun j hj => by
  rw [getD_selW] at hj ⊢
  simp only [Bool.and_eq_true] at hj ⊢
  exact ⟨h j hj.1, hj.2⟩

/-- The block rule is monotone in the writable flags. -/
theorem _root_.Millipede.Exp.restr_mono {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {W W' : List Bool}, WLe W W' → e.Restr W → e.Restr W' := by
  induction e <;> intro W W' hW h
  case loop ihc ihb ihk =>
    exact ⟨fun x hx => hW _ (h.1 x hx), ihc (WLe.cons id (WLe.cons id (WLe.of_noW _ _))) h.2.1,
      ihb (WLe.cons id (WLe.cons id (WLe.selW _ _ hW))) h.2.2.1, ihk (WLe.cons id hW) h.2.2.2⟩
  all_goals grind [Exp.Restr, WLe.cons, WLe.of_noW, RArgs.mutW_mono, EArgs.outW_mono, WLe]

/-- Every variable other than `i` writable under `W` is writable under `W'`. -/
def WLeX (i : Nat) (W W' : List Bool) : Prop :=
  ∀ k, k ≠ i → W.getD k false = true → W'.getD k false = true

theorem WLeX.cons {i : Nat} {b b' : Bool} {W W' : List Bool} (hb : b = true → b' = true)
    (h : WLeX i W W') : WLeX (i + 1) (b :: W) (b' :: W') := by
  intro k hk hw
  cases k with
  | zero => simpa using hb (by simpa using hw)
  | succ k => simpa using h k (by omega) (by simpa using hw)

theorem WLeX.noW {i : Nat} {W W' : List Bool} : WLeX i (noW W) W' := fun k _ hk => by
  rw [noW_getD] at hk; cases hk

theorem WLeX.selW (xs : List Nat) {i : Nat} {W W' : List Bool} (h : WLeX i W W') :
    WLeX i (selW xs 0 W) (selW xs 0 W') := fun j hj hw => by
  rw [getD_selW] at hw ⊢
  simp only [Bool.and_eq_true] at hw ⊢
  exact ⟨h j hj hw.1, hw.2⟩

theorem _root_.Millipede.RArgs.mutW_clr {Γ : List Ty} {W W' : List Bool} {i : Nat}
    (hW : WLeX i W W') : {ps os : List Ty} → (as : RArgs Γ ps os) → as.noAddr i = true →
      as.mutW W → as.mutW W'
  | _, _, .nil, _, _ => trivial
  | _, _, .own _ as, hn, h => as.mutW_clr hW hn h
  | _, _, .shr _ as, hn, h => as.mutW_clr hW (by simp_all [RArgs.noAddr]) h
  | _, _, .mut _ as, hn, h => by
    simp only [RArgs.noAddr, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    exact ⟨hW _ hn.1 h.1, as.mutW_clr hW hn.2 h.2⟩

theorem _root_.Millipede.EArgs.outW_clr {Γ : List Ty} {W W' : List Bool} {i : Nat}
    (hW : WLeX i W W') {ps : List ExtParam} (as : EArgs Γ ps) (hn : as.noAddr i = true)
    (h : as.outW W) : as.outW W' := by
  induction as with
  | nil => trivial
  | word _ _ ih | bufOut _ ih => exact ih hn h
  | bufIn b _ ih => cases b <;> simp_all [EArgs.noAddr, EArgs.outW]
  | sliceOut _ _ _ _ ih =>
    simp only [EArgs.noAddr, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    exact ⟨hW _ hn.1 h.1, ih hn.2 h.2⟩

/-- A term that never writes variable `i` obeys the block rule with `i` read-only. A loop's
slot-resident counter variable is such a variable. -/
theorem _root_.Millipede.Exp.restr_clr {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {W W' : List Bool} {i : Nat}, WLeX i W W' → e.noAddr i = true → e.noAsg i = true →
      e.Restr W → e.Restr W' := by
  induction e <;> intro W W' i hW hn ha h <;>
    simp only [Exp.noAddr, Exp.noAsg, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hn ha
  case let_ ih₁ ih₂ => exact ⟨ih₁ WLeX.noW hn.1 ha.1 h.1, ih₂ (WLeX.cons id hW) hn.2 ha.2 h.2⟩
  case ite ih₁ ih₂ => exact ⟨ih₁ hW hn.1 ha.1 h.1, ih₂ hW hn.2 ha.2 h.2⟩
  case match_ ih₁ ih₂ =>
    exact ⟨ih₁ (WLeX.cons id hW) hn.1.2 ha.1 h.1, ih₂ (WLeX.cons id hW) hn.2 ha.2 h.2⟩
  case case ih₁ ih₂ =>
    exact ⟨ih₁ (WLeX.cons id hW) hn.1.2 ha.1 h.1, ih₂ (WLeX.cons id hW) hn.2 ha.2 h.2⟩
  case extMut ih => exact ⟨EArgs.outW_clr hW _ hn.1 h.1, ih (WLeX.cons id hW) hn.2 ha h.2⟩
  case assign p _ _ ih =>
    refine ⟨hW _ (fun e => ?_) h.1, ih hW hn.2 ha.2 h.2⟩
    rcases hn.1 with (h1 | h1) | h1
    · exact h1 e
    · simp_all
    · simp_all
  case put ih => exact ⟨hW _ hn.1 h.1, ih hW hn.2 ha h.2⟩
  case take ih => exact ⟨hW _ hn.1 h.1, ih (WLeX.cons id hW) hn.2 ha h.2⟩
  case borrowShr ihb ihk =>
    exact ⟨ihb (WLeX.cons id WLeX.noW) hn.1.2 ha.1 h.1, ihk (WLeX.cons id hW) hn.2 ha.2 h.2⟩
  case borrowMut ihb ihk =>
    exact ⟨hW _ hn.1.1 h.1, ihb (WLeX.cons id WLeX.noW) hn.1.2 ha.1 h.2.1,
      ihk (WLeX.cons id hW) hn.2 ha.2 h.2.2⟩
  case callRef ihb ihk =>
    exact ⟨RArgs.mutW_clr hW _ hn.1 h.1, h.2.1, ihk (WLeX.cons id hW) hn.2 ha h.2.2⟩
  case loop ihc ihb ihk =>
    exact ⟨fun x hx => hW _ (fun e => ha.1.1.1 (e ▸ hx)) (h.1 x hx),
      ihc (WLeX.cons id (WLeX.cons id WLeX.noW)) hn.1.1 ha.1.1.2 h.2.1,
      ihb (WLeX.cons id (WLeX.cons id (WLeX.selW _ hW))) hn.1.2 ha.1.2 h.2.2.1,
      ihk (WLeX.cons id hW) hn.2 ha.2 h.2.2.2⟩
  all_goals exact h

/-! ## The checker keeps or lowers the flags -/

theorem BS.access_flags {b b' : BS} {path : List Sel} {a : Acc} (h : b.access path a = some b') :
    b'.wr = b.wr ∧ b'.mode = b.mode := by
  unfold BS.access at h; split at h <;> grind

theorem ctxAccess_flags : ∀ {st st' : List BS} {k : Nat} {path : List Sel} {a : Acc},
    ctxAccess st k path a = some st' → wflags st' = wflags st
  | [], _, _, _, _, h => by simp [ctxAccess] at h
  | b :: bs, st', 0, path, a, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    obtain ⟨h1, h2⟩ := BS.access_flags hb
    simp [wflags, h1, h2]
  | b :: bs, st', k + 1, path, a, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨bs', hb, rfl⟩ := h
    have := ctxAccess_flags hb
    simp only [wflags, List.map_cons] at this ⊢
    rw [this]

/-- A write access succeeds only on a binder writable in the block and not `&`. -/
theorem ctxAccess_write : ∀ {st st' : List BS} {k : Nat} {path : List Sel},
    ctxAccess st k path .write = some st' → (wflags st).getD k false = true
  | [], _, _, _, h => by simp [ctxAccess] at h
  | b :: bs, st', 0, path, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, _⟩ := h
    grind [BS.access, wflags]
  | b :: bs, st', k + 1, path, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨bs', hb, _⟩ := h
    simpa [wflags] using ctxAccess_write hb

theorem addLoan_flags : ∀ (st : List BS) (k : Nat) (l : Loan), wflags (addLoan st k l) = wflags st
  | [], _, _ => rfl
  | b :: bs, 0, l => by simp [addLoan, wflags]
  | b :: bs, k + 1, l => by
    have := addLoan_flags bs k l
    simp only [addLoan, wflags, List.map_cons] at this ⊢
    rw [this]

theorem _root_.Millipede.Atom.use_flags {Γ : List Ty} {t : Ty} {st st' : List BS} (a : Atom Γ t)
    (h : a.use st = some st') : wflags st' = wflags st := by
  cases a with
  | var m => exact ctxAccess_flags h
  | lit v => simp only [Atom.use, Option.some.injEq] at h; rw [h]

theorem _root_.Millipede.Args.use_flags {Γ : List Ty} :
    {ps : List Ty} → (st st' : List BS) → (as : Args Γ ps) → Args.use st as = some st' →
      wflags st' = wflags st
  | _, st, st', .nil, h => by simp only [Args.use, Option.some.injEq] at h; rw [h]
  | _, st, st', .cons a as, h => by
    simp only [Args.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    rw [Args.use_flags _ _ as h₂, a.use_flags h₁]

theorem _root_.Millipede.Place.useIdx_flags {Γ : List Ty} {t : Ty} (p : Place Γ t) :
    ∀ {st st' : List BS}, p.useIdx st = some st' → wflags st' = wflags st := by
  induction p <;> intro st st' h <;> useIdx_step at h
  all_goals first
    | grind [Atom.use_flags]
    | (obtain ⟨_, h1, h2⟩ := h; rw [Atom.use_flags _ h2, Atom.use_flags _ h1])

theorem _root_.Millipede.Place.access_flags {Γ : List Ty} {t : Ty} (p : Place Γ t)
    {st st' : List BS} {a : Acc} (h : p.access st a = some st') : wflags st' = wflags st := by
  simp only [Place.access, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  rw [ctxAccess_flags h₂, p.useIdx_flags h₁]

/-- A write access to a place succeeds only if its root is writable. -/
theorem _root_.Millipede.Place.access_write {Γ : List Ty} {t : Ty} (p : Place Γ t)
    {st st' : List BS} (h : p.access st .write = some st') :
    (wflags st).getD p.root false = true := by
  simp only [Place.access, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  rw [← p.useIdx_flags h₁]; exact ctxAccess_write h₂

theorem _root_.Millipede.EArgs.use_flags {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps) :
    ∀ (st st' : List BS), EArgs.use st as = some st' →
      wflags st' = wflags st ∧ as.outW (wflags st) := by
  induction as with
  | bufIn b as ih => cases b <;> intro st st' h <;> simp only [EArgs.use, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h <;> grind [EArgs.outW, Atom.use_flags, Place.access_flags]
  | _ => intro st st' h; simp only [EArgs.use, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h; grind [EArgs.outW, Atom.use_flags, Place.access_flags,
        Place.access_write]

theorem _root_.Millipede.RArgs.use_flags {Γ : List Ty} {ps os : List Ty} (st st' : List BS)
    (as : RArgs Γ ps os) (h : RArgs.use st as = some st') :
    wflags st' = wflags st ∧ as.mutW (wflags st) := by
  induction as generalizing st st' <;> simp only [RArgs.use, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.mutW, Atom.use_flags, Place.access_flags, Place.access_write, addLoan_flags]

theorem _root_.Millipede.Guard.use_flags {Γ : List Ty} {st st' : List BS} (g : Guard Γ)
    (h : g.use st = some st') : wflags st' = wflags st := by
  cases g with
  | valid p _ => exact p.access_flags h

theorem _root_.Millipede.Carry.use_flags {Γ : List Ty} :
    {ts : List Ty} → (st st' : List BS) → (cs : Carry Γ ts) → cs.use st = some st' →
      wflags st' = wflags st ∧ ∀ x ∈ cs.idxs, (wflags st).getD x false = true
  | _, st, st', .nil, h => by
    simp only [Carry.use, Option.some.injEq] at h; rw [h]; exact ⟨rfl, by simp [Carry.idxs]⟩
  | _, st, st', .cons m cs, h => by
    simp only [Carry.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    obtain ⟨e, hm⟩ := Carry.use_flags _ _ cs h₂
    rw [ctxAccess_flags h₁] at e hm
    exact ⟨e, by
      simp only [Carry.idxs, List.mem_cons, forall_eq_or_imp]; exact ⟨ctxAccess_write h₁, hm⟩⟩

theorem wflags_carryIn (xs : List Nat) :
    ∀ (k : Nat) (st : List BS), wflags (carryIn xs k st) = selW xs k (wflags st)
  | _, [] => rfl
  | k, b :: bs => by
    have ih := wflags_carryIn xs (k + 1) bs
    simp only [wflags] at ih
    simp only [carryIn, wflags, List.map_cons, Flat.selW, ih, List.cons.injEq, and_true]
    cases b.wr <;> cases xs.contains k <;> simp

theorem WLe.fresh {m : Mode} {lin : Bool} {s : List BS} {W : List Bool} (h : WLe (wflags s) W) :
    WLe (wflags (BS.fresh m lin :: s)) (true :: W) := by
  simp only [wflags, List.map_cons]; exact WLe.cons (fun _ => rfl) h

theorem getD_wflags_enterBlock (st : List BS) (k : Nat) :
    (wflags (enterBlock st)).getD k false = false := by
  simp only [wflags, enterBlock, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[k]? <;> rfl

theorem WLe.of_enterBlock (st : List BS) (W : List Bool) : WLe (wflags (enterBlock st)) W :=
  fun k h => by rw [getD_wflags_enterBlock] at h; cases h

theorem WLe.exitBlock : ∀ (st s : List BS), WLe (wflags (Millipede.exitBlock st s)) (wflags st)
  | o :: os, a :: as => by
    simp only [Millipede.exitBlock, wflags, List.map_cons]
    exact WLe.cons id (WLe.exitBlock os as)
  | [], _ => by simp only [Millipede.exitBlock]; exact WLe.nil _
  | _ :: _, [] => by simp only [Millipede.exitBlock]; exact WLe.nil _

theorem WLe.popDone {s s' : List BS} {W : List Bool} (h : Millipede.popDone s = some s')
    (hs : WLe (wflags s) (true :: W)) : WLe (wflags s') W := by
  cases s <;> grind [Millipede.popDone, wflags, WLe.tail]

/-- The flags after a binder introduced over `s` and popped. -/
theorem WLe.bind {s s₂ st' : List BS} {W : List Bool} {m : Mode} {lin : Bool}
    (h₂ : WLe (wflags s₂) (wflags (BS.fresh m lin :: s))) (hs : WLe (wflags s) W)
    (h₃ : Millipede.popDone s₂ = some st') : WLe (wflags st') W :=
  WLe.popDone h₃ (h₂.trans (WLe.fresh hs))

theorem wflags_initCtx (ps : List Ty) : wflags (initCtx ps) = allW ps := by
  simp [wflags, initCtx, BS.fresh, allW]

theorem _root_.Millipede.RArgs.binders_le {Γ : List Ty} :
    (st : List BS) → {ps os : List Ty} → (as : RArgs Γ ps os) →
      WLe (wflags (as.binders st)) as.modeW
  | _, _, _, .nil => WLe.nil _
  | st, _, _, .own _ as => by
    simp only [RArgs.binders, wflags, List.map_cons, RArgs.modeW]
    exact WLe.cons (fun _ => rfl) (as.binders_le st)
  | st, _, _, .shr _ as => by
    simp only [RArgs.binders, wflags, List.map_cons, RArgs.modeW]
    exact WLe.cons (fun h => by simp [BS.fresh] at h) (as.binders_le st)
  | st, _, _, .mut _ as => by
    simp only [RArgs.binders, wflags, List.map_cons, RArgs.modeW]
    exact WLe.cons (fun _ => rfl) (as.binders_le st)

theorem checkBody_some {check : List BS → Option (List BS)} {bs : List BS}
    (h : checkBody check bs = true) : ∃ st, check bs = some st := by
  unfold checkBody at h
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

/-! ## The bridge -/

/-- The checker implies the block rule, with the invariant that the checker never makes a binder
more writable. -/
theorem _root_.Millipede.Exp.restr_check {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (st st' : List BS), e.check st = some st' →
      e.Restr (wflags st) ∧ WLe (wflags st') (wflags st) := by
  induction e <;> intro st st' h <;> check_step at h
  case let_ ih₁ ih₂ =>
    obtain ⟨s₁, h₁, s₂, h₂, h₃⟩ := h
    have hW := WLe.exitBlock st s₁
    exact ⟨⟨Exp.restr_mono _ (WLe.of_enterBlock _ _) (ih₁ _ _ h₁).1,
      Exp.restr_mono _ (WLe.fresh hW) (ih₂ _ _ h₂).1⟩, (ih₂ _ _ h₂).2.bind hW h₃⟩
  case borrowShr p _ _ ihb ihk =>
    obtain ⟨s₀, h₀, sb, hb, sb', -, sk, hk, h₃⟩ := h
    have hS : WLe (wflags (exitBlock s₀ sb')) (wflags st) :=
      p.access_flags h₀ ▸ WLe.exitBlock s₀ sb'
    exact ⟨⟨Exp.restr_mono _ (WLe.cons (fun h => by simp [BS.fresh] at h) (WLe.of_enterBlock _ _))
      (ihb _ _ hb).1, Exp.restr_mono _ (WLe.fresh hS) (ihk _ _ hk).1⟩, (ihk _ _ hk).2.bind hS h₃⟩
  case borrowMut p _ _ ihb ihk =>
    obtain ⟨s₀, h₀, sb, hb, sb', -, sk, hk, h₃⟩ := h
    have hS : WLe (wflags (exitBlock s₀ sb')) (wflags st) :=
      p.access_flags h₀ ▸ WLe.exitBlock s₀ sb'
    exact ⟨⟨p.access_write h₀, Exp.restr_mono _ (WLe.cons (fun _ => rfl) (WLe.of_enterBlock _ _))
      (ihb _ _ hb).1, Exp.restr_mono _ (WLe.fresh hS) (ihk _ _ hk).1⟩, (ihk _ _ hk).2.bind hS h₃⟩
  case callRef args _ ihb ihk =>
    obtain ⟨s₁, h₁, hb, sk, hk, h₃⟩ := h
    obtain ⟨sb, hsb⟩ := checkBody_some hb
    have hW := WLe.exitBlock st s₁
    exact ⟨⟨(RArgs.use_flags _ _ args h₁).2,
      Exp.restr_mono _ (args.binders_le st) (ihb _ _ hsb).1,
      Exp.restr_mono _ (WLe.fresh hW) (ihk _ _ hk).1⟩, (ihk _ _ hk).2.bind hW h₃⟩
  case extMut args _ ihk =>
    obtain ⟨s₁, h₁, sk, hk, h₃⟩ := h
    obtain ⟨e, hm⟩ := args.use_flags _ _ h₁
    exact ⟨⟨hm, Exp.restr_mono _ (WLe.fresh (.of_eq e)) (ihk _ _ hk).1⟩,
      (ihk _ _ hk).2.bind (.of_eq e) h₃⟩
  case ext args => exact ⟨trivial, .of_eq (args.use_flags _ _ h.2).1⟩
  case loop cs init _ _ _ ihc ihb ihk =>
    obtain ⟨-, s₀, h₀, s₁, h₁, sc, hc, sb, hb, -, sk, hk, h₃⟩ := h
    obtain ⟨e₁, hcw⟩ := Carry.use_flags _ _ cs h₁
    have e₀ := init.use_flags h₀
    have hS : WLe (wflags s₁) (wflags st) := .of_eq (e₁.trans e₀)
    refine ⟨⟨fun x hx => by rw [← e₀]; exact hcw x hx,
      Exp.restr_mono _ (WLe.cons id (WLe.cons id (WLe.of_enterBlock _ _))) (ihc _ _ hc).1,
      Exp.restr_mono _ ?_ (ihb _ _ hb).1, Exp.restr_mono _ (WLe.fresh hS) (ihk _ _ hk).1⟩,
      (ihk _ _ hk).2.bind hS h₃⟩
    simp only [wflags, List.map_cons]
    refine WLe.cons (fun _ => rfl) (WLe.cons (fun _ => rfl) ?_)
    have := wflags_carryIn cs.idxs 0 s₁
    simp only [wflags] at this
    rw [this]; exact WLe.selW _ _ hS
  all_goals grind [Exp.Restr, → Atom.use_flags, → Args.use_flags,
    → Guard.use_flags, → Place.access_flags, → Place.access_write, WLe.refl, WLe.trans,
    WLe.popDone, WLe.fresh, Exp.restr_mono, checkBody_some, wflags_initCtx, → RArgs.use_flags]

/-- The checker implies the block rule: a term that `Exp.check` accepts from state `st` writes only
the binders that `st` marks writable. -/
theorem _root_.Millipede.Exp.restr_of_check {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (st st' : List BS) (h : e.check st = some st') : e.Restr (wflags st) :=
  (e.restr_check st st' h).1

/-- Well-formedness implies the block rule for the whole context, with every binder writable, so
`compile` need not check `Exp.restrB` separately. -/
theorem _root_.Millipede.Exp.restr_of_wf {Γ : List Ty} {t : Ty} (e : Exp Γ t) (h : e.wf = true) :
    e.Restr (allW Γ) := by
  unfold Exp.wf at h
  cases hc : e.check (initCtx Γ) with
  | none => rw [hc] at h; cases h
  | some st' =>
    have := e.restr_of_check _ _ hc
    rwa [wflags_initCtx] at this

end Millipede.Flat
