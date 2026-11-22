import Millipede.Compile.LinearizeProof
import Millipede.Compile.LowerFacts

/-!
# The stack bound of the pipeline

`lower` keeps every Core value in the static data region, except small values that are never
addressed, which it keeps in frame slots. Each activation, the main code or a call, has the
`Flat.FR = 16` scratch slots, and above them `Exp.slotNeed` slots for its slot-resident binders.
Core's stack measure charges every activation `frameWords w = scratchWords + w` slots, with
`FR = scratchWords`, and a term needs no more slots for its binders than its slot words. The
static Lin stack bound of a lowered program is therefore within the source bound, for every frame
model `φ`. The main theorems are the following:

* `lowerM_callBytes`: the Flat call measure of `lowerM e` is at most `e.stackBytes φ`;
* `linearize_stackBytes_le`: `(linearize (lowerProg p) M).stackBytes φ ≤ p.stackBytes φ`;
* `lower_linearize_stackBytes_le`: the same for `lower`'s output, which is what `compile` links,
  so no stack check runs on the program.

The module also proves that lowered code stays within its frame slots, by the decidable
`Lin.withinB`, so that its linearization is well formed. The stack measure is described in
doc/design/resources.md.
-/

namespace Millipede.Flat

open Lin (Stmt.callBytes)

variable (φ : FrameModel)

/-! ## Straight-line helpers make no calls -/

@[simp] theorem copyB_cb (sb : Operand) (so : Nat) (db : Operand) (d len : Nat) :
    Stmt.callBytes φ (copyB sb so db d len) = 0 := by
  induction so, d, len using copyB.induct <;>
    simp_all [copyB.eq_2, copyB.eq_3, copyB, Stmt.callBytes]

@[simp] theorem writeB1_cb (db : Operand) (d : Nat) (bs : List UInt8) :
    Stmt.callBytes φ (writeB1 db d bs) = 0 := by
  induction bs generalizing d <;> simp_all [writeB1, Stmt.callBytes]

@[simp] theorem writeB_cb (db : Operand) (d : Nat) (bs : List UInt8) :
    Stmt.callBytes φ (writeB db d bs) = 0 := by
  induction d, bs using writeB.induct <;> simp_all [writeB, Stmt.callBytes]

@[simp] theorem varAddr_cb (l : Loc) (x : Nat) : Stmt.callBytes φ (varAddr l x) = 0 := by
  cases l <;> rfl

@[simp] theorem cntTest_cb (lc : Loc) (a N : Nat) : Stmt.callBytes φ (cntTest lc a N) = 0 := by
  cases lc <;> rfl

@[simp] theorem cntEnter_cb (lc : Loc) (a : Nat) : Stmt.callBytes φ (cntEnter lc a) = 0 := by
  cases lc <;> rfl

@[simp] theorem cntNext_cb (lc : Loc) (a : Nat) : Stmt.callBytes φ (cntNext lc a) = 0 := by
  cases lc <;> rfl

@[simp] theorem cntInit_cb (lc : Loc) (a : Nat) : Stmt.callBytes φ (cntInit lc a) = 0 := by
  cases lc <;> rfl

@[simp] theorem ldSlots_cb (w : Width) (k : Nat) (b : Operand) (o n : Nat) :
    Stmt.callBytes φ (ldSlots w k b o n) = 0 := by
  induction n generalizing k o <;> simp_all [ldSlots, Stmt.callBytes]

@[simp] theorem stSlots_cb (w : Width) (b : Operand) (o k n : Nat) :
    Stmt.callBytes φ (stSlots w b o k n) = 0 := by
  induction n generalizing k o <;> simp_all [stSlots, Stmt.callBytes]

@[simp] theorem movSlots_cb (k k' n : Nat) : Stmt.callBytes φ (movSlots k k' n) = 0 := by
  induction n generalizing k k' <;> simp_all [movSlots, Stmt.callBytes]

@[simp] theorem immSlots_cb (k : Nat) (vs : List UInt64) : Stmt.callBytes φ (immSlots k vs) = 0 := by
  induction vs generalizing k <;> simp_all [immSlots, Stmt.callBytes]

@[simp] theorem accNext_cb (la lb : Loc) (sz : Nat) : Stmt.callBytes φ (accNext la lb sz) = 0 := by
  cases la <;> cases lb <;> simp [accNext]

@[simp] theorem flagLoad_cb (tmc : Tl) (a : Nat) : Stmt.callBytes φ (flagLoad tmc a) = 0 := by
  cases tmc <;> rfl

@[simp] theorem atomTo_cb {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (d : Nat) :
    Stmt.callBytes φ (atomTo a ρ d) = 0 := by
  cases a <;> simp only [atomTo] <;> try split
  all_goals simp [Stmt.callBytes]

@[simp] theorem atomWord_cb {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (x : Nat) :
    Stmt.callBytes φ (atomWord a ρ x) = 0 := by
  cases a <;> simp only [atomWord] <;> try split
  all_goals simp [Stmt.callBytes]

@[simp] theorem atomSlots_cb {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (x cnt : Nat) :
    Stmt.callBytes φ (atomSlots a ρ x cnt) = 0 := by
  cases a <;> simp only [atomSlots] <;> try split
  all_goals simp [Stmt.callBytes]

@[simp] theorem atomSlotsS_cb {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (x cnt : Nat) :
    Stmt.callBytes φ (atomSlotsS a ρ x cnt) = 0 := by
  unfold atomSlotsS; split
  · split <;> simp [Stmt.callBytes]
  · simp

@[simp] theorem argsSlots_cb {Γ : List Ty} (ρ : List Loc) (x n : Nat) : ∀ {ps : List Ty}
    (args : Args Γ ps) (oss : List (List Nat)), Stmt.callBytes φ (argsSlots ρ x n args oss) = 0
  | _, .nil, _ => by cases ‹List (List Nat)› <;> rfl
  | _, .cons _ _, [] => rfl
  | _, .cons _ as, _ :: oss => by
    simp only [argsSlots, Stmt.callBytes, argsSlots_cb ρ x n as oss]; split <;> simp [Stmt.callBytes]

@[simp] theorem ctorCode_cb {Γ ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    (ρ : List Loc) (k n : Nat) : Stmt.callBytes φ (ctorCode args plan ρ k n) = 0 := by
  unfold ctorCode ctorSlots; split <;> (try split) <;> simp [Stmt.callBytes]

@[simp] theorem resultCode_cb {Γ : List Ty} {p : Ty} (ε α : Ty) (a : Atom Γ p) (tag : Nat)
    (tm : Tl) (ρ : List Loc) (d : Nat) : Stmt.callBytes φ (resultCode ε α a tag tm ρ d) = 0 := by
  unfold resultCode; split <;> try split
  all_goals simp [Stmt.callBytes]

@[simp] theorem accInit_cb {Γ : List Ty} {s : Ty} (la : Loc) (init : Atom Γ s) (ρ : List Loc) :
    Stmt.callBytes φ (accInit la init ρ) = 0 := by
  cases la <;> simp [accInit]

@[simp] theorem elemAddr_cb {Γ : List Ty} (i : Atom Γ .u64) (ρ : List Loc) (size : Nat) :
    Stmt.callBytes φ (elemAddr i ρ size) = 0 := by
  simp [elemAddr, Stmt.callBytes]

@[simp] theorem placeAddr_cb {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) :
    Stmt.callBytes φ (placeAddr p ρ) = 0 := by
  induction p with
  | field p l ih => simp only [placeAddr]; split <;> simp_all [Stmt.callBytes]
  | _ => simp_all [placeAddr, pairAddrCode, Stmt.callBytes]

@[simp] theorem refStore_cb {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (n : Nat) :
    Stmt.callBytes φ (refStore p ρ n) = 0 := by
  cases p <;> simp [refStore, sliceStore, pairStore, Stmt.callBytes]

@[simp] theorem placeRead_cb {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (d : Nat) :
    Stmt.callBytes φ (placeRead p ρ d) = 0 := by
  cases p <;> simp [placeRead, Stmt.callBytes]

@[simp] theorem placeWrite_cb {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (d : Nat) :
    Stmt.callBytes φ (placeWrite p ρ d) = 0 := by
  cases p <;> simp [placeWrite, Stmt.callBytes]

theorem placeCheck_cb {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) :
    ∀ c, placeCheck p ρ = some c → Stmt.callBytes φ c = 0 := by
  induction p <;> intro c hc <;> simp only [placeCheck] at hc
  all_goals first
    | (simp only [Option.some.injEq] at hc; subst hc; rfl)
    | cases hc
    | (split at hc
       · obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hc
         simp_all [Stmt.callBytes]
       · cases hc)
    | simp_all

@[simp] theorem guardCode_cb {Γ : List Ty} (g : Guard Γ) (ρ : List Loc) (d : Nat) :
    Stmt.callBytes φ (guardCode g ρ d) = 0 := by
  cases g with
  | valid p _ =>
    cases h : placeCheck p ρ with
    | none => simp [guardCode, h, Stmt.callBytes]
    | some c => simp [guardCode, h, Stmt.callBytes, placeCheck_cb φ p ρ c h]

@[simp] theorem primLoad_cb {Γ : List Ty} {ps : List Ty} (args : Args Γ ps) (ρ : List Loc) :
    Stmt.callBytes φ (primLoad args ρ) = 0 := by
  rcases args with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp [primLoad, Stmt.callBytes]

@[simp] theorem scrutPre_cb {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (n : Nat) :
    Stmt.callBytes φ (scrutPre a ρ n) = 0 := by
  cases a <;> simp only [scrutPre] <;> try split
  all_goals simp [Stmt.callBytes]

@[simp] theorem restCode_cb (mode : RestMode) (tag ls po n' qsize : Nat) :
    Stmt.callBytes φ (restCode mode tag ls po n' qsize) = 0 := by
  cases mode <;> simp [restCode, Stmt.callBytes]

@[simp] theorem extArgs_cb {Γ : List Ty} {ps : List ExtParam} (args : EArgs Γ ps) (ρ : List Loc)
    (x : Nat) : Stmt.callBytes φ (extArgs args ρ x).1 = 0 := by
  induction args generalizing x
  case bufIn b _ ih => cases b <;> simp_all [extArgs, extArgs.sliceArg, Stmt.callBytes]
  all_goals simp_all [extArgs, extArgs.sliceArg, Stmt.callBytes]

@[simp] theorem argsTo_cb {Γ : List Ty} {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat))
    (ρ : List Loc) (d : Nat) : Stmt.callBytes φ (argsTo args oss ρ d) = 0 := by
  induction args generalizing oss with
  | nil => rfl
  | cons a _ ih =>
    cases oss with
    | nil => simp [argsTo, ih]
    | cons os oss =>
      have : ∀ os : List Nat, Stmt.callBytes φ
          (os.foldr (fun o c => .seq (atomTo a ρ (d + o)) c) .skip) = 0 := by
        intro os; induction os <;> simp_all [Stmt.callBytes]
      simp [argsTo, Stmt.callBytes, this, ih]

@[simp] theorem argsPass_cb {Γ : List Ty} {ps : List Ty} (wp : Nat → Bool) (args : Args Γ ps)
    (ρ : List Loc) (d j : Nat) : Stmt.callBytes φ (argsPass wp args ρ d j) = 0 := by
  induction args generalizing d j <;> simp only [argsPass, Stmt.callBytes] <;> try split
  all_goals simp_all

@[simp] theorem rargsPass_cb {Γ : List Ty} {ps os : List Ty} (args : RArgs Γ ps os)
    (ρ : List Loc) (d : Nat) : Stmt.callBytes φ (rargsPass args ρ d) = 0 := by
  induction args generalizing d <;> simp_all [rargsPass, Stmt.callBytes]

/-! ## Terms -/

/-- The frame slots of a slot-resident type are within its words, which `Ty.slotTy` checks. -/
theorem slotN_le_words {t : Ty} (h : t.slotTy = true) : t.slotN ≤ t.data.shape.words := by
  unfold Ty.slotTy at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem slotTy_words {t : Ty} (h : t.slotTy = true) : 1 ≤ t.data.shape.words :=
  Nat.le_trans (Ty.slotN_pos h) (slotN_le_words h)

/-- A slot-resident binder's slots are within its words. -/
theorem slotBind_words {Γ : List Ty} {s t : Ty} {e : Exp (s :: Γ) t} :
    (if e.slotBind then e.slotNeed + s.slotN else e.slotNeed) ≤ s.data.shape.words + e.slotNeed := by
  split
  · rename_i h
    have := slotN_le_words (t := s) (by simp only [Exp.slotBind, Bool.and_eq_true] at h; exact h.1.1)
    omega
  · omega

/-- A term's slot words include its type's words. -/
theorem _root_.Millipede.Exp.words_le_slotWords {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    t.data.shape.words ≤ e.slotWords := by
  cases e <;> simp only [Exp.slotWords, Ty.words] <;>
    first | omega | (have : (Data.shape UInt64).words = 1 := rfl; omega)

/-- A term of a type of at least one word has at least one slot word. -/
theorem _root_.Millipede.Exp.one_le_slotWords {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (ht : 1 ≤ t.data.shape.words) : 1 ≤ e.slotWords := by
  cases e <;> simp only [Exp.slotWords, Ty.words] at ht ⊢ <;> omega

/-- A term's slot-resident binders need no more frame slots than its slot words. -/
theorem _root_.Millipede.Exp.slotNeed_le_slotWords {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    e.slotNeed ≤ e.slotWords := by
  induction e
  case let_ s _ e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.slotNeed, Exp.slotWords]
    split
    · rename_i h
      have := slotN_le_words (t := s) (by simp only [Exp.slotBind, Bool.and_eq_true] at h; exact h.1.1)
      have := e₁.words_le_slotWords
      exact Nat.max_le.2 ⟨by omega, by omega⟩
    · omega
  case loop s _ _ _ _ c body k ihc ihb ihk =>
    have hc1 : 1 ≤ c.slotWords := c.one_le_slotWords (by decide)
    have hbA : Exp.bodyW c body k = true → Exp.accSlot c body k = true := fun h => by
      simp only [Exp.bodyW, Bool.and_eq_true] at h; exact h.1.1.1.1
    have hsw : Exp.accSlot c body k = true → s.slotN ≤ s.data.shape.words := fun hA =>
      slotN_le_words (by simp only [Exp.accSlot, Bool.and_eq_true] at hA; exact hA.1.1.1)
    simp only [Exp.slotNeed, Exp.slotWords, Ty.words]
    cases hA : Exp.accSlot c body k <;> cases hB : Exp.bodyW c body k <;>
      cases Exp.cntSlot c body <;> cases c.Conf (.word FR) <;> simp_all <;> omega
  case match_ ε α _ _ eE eO ihE ihO =>
    have := slotBind_words (e := eE); have := slotBind_words (e := eO)
    simp only [Exp.slotNeed, Exp.slotWords]; omega
  case case t p q _ _ _ eP eQ ihP ihQ =>
    have := slotBind_words (e := eP); have := slotBind_words (e := eQ)
    simp only [Exp.slotNeed, Exp.slotWords, Ty.words] at *; omega
  case take t _ _ _ _ _ k ih =>
    have := slotBind_words (e := k)
    simp only [Exp.slotNeed, Exp.slotWords, Ty.words] at *; omega
  case extMut u sig _ k ih =>
    simp only [Exp.slotNeed, Exp.slotWords]; split <;> omega
  all_goals simp only [Exp.slotNeed, Exp.slotWords]; omega

/-- A callee's frame, `FR` scratch slots and then its slot-resident binders, is within the slots
that Core charges its activation. -/
theorem callee_frame_le {ps : List Ty} {t : Ty} (body : Exp ps t) :
    φ.frame (FR + body.slotNeed) ≤ φ.frame (frameWords (ctxWords ps + body.slotWords)) :=
  φ.mono (by have := body.slotNeed_le_slotWords; simp only [frameWords, FR, scratchWords]; omega)

/-- A callee's word parameters take at most its parameters' words. -/
theorem slotsIn_paramLocs_le (wp : Nat → Bool) :
    ∀ (ps : List Ty) (o j : Nat), (∀ i, wp (j + i) = true → (ps.getD i .unit).wordTy = true) →
      slotsIn (paramLocs wp ps o j) ≤ ctxWords ps
  | [], _, _, _ => by simp [paramLocs, slotsIn]
  | t :: ts, o, j, h => by
    have ih := slotsIn_paramLocs_le wp ts (o + t.size) (j + 1) fun i hi => by
      have := h (i + 1) (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi)
      simpa using this
    simp only [paramLocs, slotsIn_cons, ctxWords]
    split
    · rename_i hj
      have := slotTy_words (t := t) (Ty.wordTy_slotTy (by simpa using h 0 (by simpa using hj)))
      simp; omega
    · simp; omega

theorem wordParams_le {ps : List Ty} {t : Ty} (body : Exp ps t) :
    slotsIn (paramLocs body.wordParam ps 0 0) ≤ ctxWords ps :=
  slotsIn_paramLocs_le _ ps 0 0 fun i hi => by
    simp only [Exp.wordParam, Nat.zero_add, Bool.and_eq_true] at hi; exact hi.1.2

/-- A callee's frame, `FR` scratch slots, its word parameters and then its slot-resident binders, is
within the slots that Core charges its activation. -/
theorem callee_frame_le' {ps : List Ty} {t : Ty} (body : Exp ps t) :
    φ.frame (FR + slotsIn (paramLocs body.wordParam ps 0 0) + body.slotNeed) ≤
      φ.frame (frameWords (ctxWords ps + body.slotWords)) :=
  φ.mono (by
    have := body.slotNeed_le_slotWords; have := wordParams_le body
    simp only [frameWords, FR, scratchWords]; omega)

/-- A callee whose body returns words in tail mode `word` declares its result's slots, and stays
within the slots that Core charges, which include its result's words. -/
theorem callee_frame_le_word {ps : List Ty} {t : Ty} (body : Exp ps t) {k : Nat}
    (hw : body.Conf (.word k) = true) :
    φ.frame (FR + slotsIn (paramLocs body.wordParam ps 0 0) + max t.slotN body.slotNeed) ≤
      φ.frame (frameWords (ctxWords ps + body.slotWords)) :=
  φ.mono (by
    have := body.slotNeed_le_slotWords; have := wordParams_le body
    have := slotN_le_words (body.slotTy_of_word hw); have := body.words_le_slotWords
    simp only [frameWords, FR, scratchWords, Ty.words] at *; omega)

/-- The loop code of a large constructor makes no call. -/
theorem mkCode?_callBytes {Γ ps : List Ty} {t : Ty} {c : Ctor ps t} {args : Args Γ ps}
    {ρ : List Loc} {d W : Nat} {code : Stmt} (h : mkCode? c args ρ d W = some code) :
    Stmt.callBytes φ code = 0 := by
  unfold mkCode? at h
  split at h
  · rename_i hfc
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨k, w, P, T, rfl, -⟩ := fillCode?_spec hfc
    simp [Stmt.callBytes, fillLoop]
  · unfold copyCode? at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          simp [Stmt.callBytes, copyLoop]
        · simp at h
      · simp at h
    · simp at h

/-- The Flat call measure of lowered code is within Core's stack measure. Every lowered call
declares the scratch frame `FR` and its body's slot-resident binders, which `Exp.stackBytes`
charges at least. -/
theorem lowerM_callBytes {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (tm : Tl) (ρ : List Loc) (n d : Nat), Stmt.callBytes φ (lowerM e tm ρ n d) ≤ e.stackBytes φ := by
  induction e <;> intro tm ρ n d
  case call ps r _ body _ ih =>
    have := callee_frame_le' φ body
    have := ih .none (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps)
    have := ih (.word (FR + slotsIn (paramLocs body.wordParam ps 0 0)))
      (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps)
    simp only [lowerM, Exp.stackBytes]; split
    · rename_i hw
      have := callee_frame_le_word φ body hw
      cases tm <;> simp [Stmt.callBytes] <;> omega
    · cases tm <;> simp [Stmt.callBytes] <;> omega
  case let_ s _ e₁ e₂ ih₁ ih₂ =>
    have h1 := ih₁ .none ρ (n + s.size) n
    have h1' := ih₁ (.word (FR + slotsIn ρ)) ρ (n + s.size) n
    simp only [lowerM, Exp.stackBytes]
    split
    · have h2 := ih₂ tm.up (.slot n (FR + slotsIn ρ) s.slotN :: ρ) (n + s.size) d
      split <;> simp only [Stmt.callBytes, ldSlots_cb] <;> omega
    · have := ih₂ tm.up (.own n :: ρ) (n + s.size) d
      simp only [Stmt.callBytes]; omega
  case callRef ps os r u _ _ body args k ihb ihk =>
    have := callee_frame_le φ body
    have := ihb (callTl r args) (args.locs 0) (args.frame + r.size) args.frame
    have := ihk tm.up (.own (n + args.frame) :: ρ) (n + args.frame + r.size) d
    simp [lowerM, Stmt.callBytes, Exp.stackBytes]
    omega
  case mk c args =>
    simp only [lowerM]
    split
    · rename_i hfc
      rw [mkCode?_callBytes φ hfc]; omega
    · (repeat' split) <;> simp [Stmt.callBytes]
  all_goals (try simp [lowerM, memArm, slotArm, Stmt.callBytes, Exp.stackBytes])
  all_goals first | grind | (repeat' split) <;> simp [Stmt.callBytes] <;> grind

/-- The Flat call measure of a lowered program is within the larger of `init`'s and
`step`'s Core stack measures. -/
theorem lowerProg_callBytes (p : Program) :
    Stmt.callBytes φ (lowerProg p).main ≤ max (p.init.stackBytes φ) (p.step.stackBytes φ) := by
  have := lowerM_callBytes φ p.init .none [] p.State.size 0
  have := lowerM_callBytes φ p.step (.whole 0) [.own 0] p.State.size 0
  have := lowerM_callBytes φ p.step .none [.own 0] (p.State.size + p.State.size) p.State.size
  simp only [lowerProg, stepCode, Stmt.callBytes]
  split <;> simp [Stmt.callBytes] <;> omega

end Millipede.Flat

namespace Millipede.Lin

/-- The stack bound of the pipeline, for every frame model `φ`: the static Lin stack bound of a
lowered and linearized program is within the source bound `Program.stackBytes`. The main
activation and every call have the scratch frame `Flat.FR` and their slot-resident binders'
slots, which Core charges at least. -/
theorem linearize_stackBytes_le (φ : FrameModel) (p : Program) (M : Nat) :
    (linearize (Flat.lowerProg p) M).stackBytes φ ≤ p.stackBytes φ := by
  rw [linearize_stackBytes]
  have h₁ := Flat.lowerProg_callBytes φ p
  have h₂ : φ.frame (Flat.lowerProg p).frame ≤
      φ.frame (frameWords (2 * ctxWords [p.State] + max p.init.slotWords p.step.slotWords)) := by
    have := p.init.slotNeed_le_slotWords; have := p.step.slotNeed_le_slotWords
    exact φ.mono (by simp only [Flat.lowerProg, frameWords, Flat.FR, scratchWords]; omega)
  simp only [Program.stackBytes]
  exact Nat.add_le_add h₂ h₁

/-- The pipeline up to Lin, which `compile` selects and links, has its stack bound within
`p.stackBytes φ`. -/
theorem lower_linearize_stackBytes_le (φ : FrameModel) {p : Program} {fp : Flat.Prog}
    (hl : Flat.lower p = .ok fp) (M : Nat) :
    (linearize fp M).stackBytes φ ≤ p.stackBytes φ := by
  unfold Flat.lower at hl
  split at hl
  · cases hl; exact linearize_stackBytes_le φ p _
  · cases hl

end Millipede.Lin

/-! ## Frames: lowered code stays within its scratch frame -/

namespace Millipede.Flat

open Lin (withinB opsBelowB)

/-- The scratch registers lie in the frame. -/
theorem regs_lt_FR : BP < FR ∧ RA < FR ∧ RB < FR ∧ RT < FR ∧ RX < FR ∧ RY < FR ∧ RP < FR := by
  decide

/-- An extern argument's operands are slots below `m`. -/
def extArgBelow (m : Nat) : ExtArg → Bool
  | .word o => opsBelowB [o] m
  | .bytes _ => true
  | .mem a l => opsBelowB [a, l] m
  | .out _ => true
  | .outMem a l => opsBelowB [a, l] m

theorem copyB_within (x so y d len : Nat) (hx : x < FR) (hy : y < FR) :
    withinB (copyB (.slot x) so (.slot y) d len) FR = true := by
  induction so, d, len using copyB.induct <;>
    simp_all [copyB.eq_2, copyB.eq_3, copyB, withinB, opsBelowB, regs_lt_FR]

theorem writeB1_within (y d : Nat) (bs : List UInt8) (hy : y < FR) :
    withinB (writeB1 (.slot y) d bs) FR = true := by
  induction bs generalizing d <;> simp_all [writeB1, withinB, opsBelowB]

theorem writeB_within (y d : Nat) (bs : List UInt8) (hy : y < FR) :
    withinB (writeB (.slot y) d bs) FR = true := by
  induction d, bs using writeB.induct <;> simp_all [writeB, withinB, opsBelowB, writeB1_within]

theorem varAddr_within (l : Loc) (x : Nat) (hx : x < FR) : withinB (varAddr l x) FR = true := by
  cases l <;> simp [varAddr, withinB, opsBelowB, hx]

theorem restCode_within (mode : RestMode) (tag ls po n' qsize : Nat) :
    withinB (restCode mode tag ls po n' qsize) FR = true := by
  cases mode <;> simp [restCode, withinB, opsBelowB, copyB_within, regs_lt_FR]

theorem opsBelowB_mono {ops : List Operand} {n n' : Nat} (h : opsBelowB ops n = true) (hn : n ≤ n') :
    opsBelowB ops n' = true :=
  List.all_eq_true.2 fun o ho => by
    have := List.all_eq_true.1 h o ho
    cases o <;> simp_all; omega

/-- A statement within `n` slots is within any larger frame. -/
theorem withinB_mono : ∀ {s : Stmt} {n n' : Nat}, withinB s n = true → n ≤ n' → withinB s n' = true
  | .skip, _, _, _, _ => rfl
  | .seq a b, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true] at h ⊢; exact ⟨withinB_mono h.1 hn, withinB_mono h.2 hn⟩
  | .mov _ _, _, _, h, hn | .load _ _ _ _, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by omega, opsBelowB_mono h.2 hn⟩
  | .bin _ _ _ _, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by omega, opsBelowB_mono h.2 hn⟩
  | .store _ _ _ _, _, _, h, hn => opsBelowB_mono h hn
  | .ite _ _ _, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨opsBelowB_mono h.1.1 hn, withinB_mono h.1.2 hn⟩, withinB_mono h.2 hn⟩
  | .while _ _ _, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨withinB_mono h.1.1 hn, opsBelowB_mono h.1.2 hn⟩, withinB_mono h.2 hn⟩
  | .call _ _ _ _ _ _, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1.1, opsBelowB_mono h.1.2 hn⟩, by omega⟩
  | .ext _ _ _ args, _, _, h, hn => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨by omega, List.all_eq_true.2 fun a ha => ?_⟩
    have := List.all_eq_true.1 h.2 a ha
    cases a <;> simp_all [opsBelowB_mono _ hn] <;> exact opsBelowB_mono this hn
  | .tick _, _, _, _, _ => rfl

theorem copyB_within' {m : Nat} (hm : FR ≤ m) (x so y d len : Nat) (hx : x < FR) (hy : y < FR) :
    withinB (copyB (.slot x) so (.slot y) d len) m = true :=
  withinB_mono (copyB_within x so y d len hx hy) hm

theorem writeB_within' {m : Nat} (hm : FR ≤ m) (y d : Nat) (bs : List UInt8) (hy : y < FR) :
    withinB (writeB (.slot y) d bs) m = true :=
  withinB_mono (writeB_within y d bs hy) hm

/-- The frame slots of a context's slot-resident variables are below `m`: each starts below `m`
and ends at most at `m`. -/
def SlotsBelow (ρ : List Loc) (m : Nat) : Prop :=
  ∀ i k, (ρ.getD i default).slot? = some k → k < m ∧ k + (ρ.getD i default).nw ≤ m

theorem SlotsBelow.cons {ρ : List Loc} {m : Nat} {l : Loc} (h : SlotsBelow ρ m)
    (hl : ∀ k, l.slot? = some k → k < m ∧ k + l.nw ≤ m) : SlotsBelow (l :: ρ) m
  | 0, k, hk => hl k (by simpa using hk)
  | i + 1, k, hk => by simpa using h i k (by simpa using hk)

theorem SlotsBelow.of_none {ρ : List Loc} {m : Nat} (h : ∀ i, (ρ.getD i default).slot? = none) :
    SlotsBelow ρ m := fun i k hk => by rw [h i] at hk; cases hk

/-- A slot-resident variable's slots are all below `m`. -/
theorem SlotsBelow.slots {ρ : List Loc} {m : Nat} (h : SlotsBelow ρ m) {i k n o : Nat}
    (hk : ρ.getD i default = .slot o k n) : ∀ j, j < n → k + j < m := fun j hj => by
  have := h i k (by rw [hk]; rfl); rw [hk] at this; simp only [Loc.nw_slot] at this; omega

/-- A callee's parameters have their slots below `FR` plus its word parameters' slots. -/
theorem SlotsBelow.paramLocs (wp : Nat → Bool) (ps : List Ty) {m : Nat}
    (hm : FR + slotsIn (paramLocs wp ps 0 0) ≤ m) : SlotsBelow (paramLocs wp ps 0 0) m :=
  fun i k hk => by
    have := (SlotsOk.paramLocs wp ps 0 0).range i k hk
    have h1 := paramLocs_nw wp ps 0 0 i hk
    exact ⟨by omega, by omega⟩

theorem ldSlots_within (w : Width) (b : Nat) (o : Nat) {m : Nat} (hb : b < m) :
    ∀ (n k : Nat), (∀ j, j < n → k + j < m) → withinB (ldSlots w k (.slot b) o n) m = true
  | 0, _, _ => rfl
  | n + 1, k, h => by
    have := h 0 (by omega)
    simp only [ldSlots, withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
      List.all_nil, Bool.and_true]
    refine ⟨⟨by omega, by simpa using hb⟩, ldSlots_within w b (o + 8) hb n (k + 1) fun j hj => ?_⟩
    have := h (j + 1) (by omega); omega

theorem stSlots_within (w : Width) (b : Nat) (o : Nat) {m : Nat} (hb : b < m) :
    ∀ (n k : Nat), (∀ j, j < n → k + j < m) → withinB (stSlots w (.slot b) o k n) m = true
  | 0, _, _ => rfl
  | n + 1, k, h => by
    have := h 0 (by omega)
    simp only [stSlots, withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
      List.all_nil, Bool.and_true]
    refine ⟨⟨by simpa using hb, by simpa using this⟩, stSlots_within w b (o + 8) hb n (k + 1)
      fun j hj => ?_⟩
    have := h (j + 1) (by omega); omega

theorem movSlots_within {m : Nat} : ∀ (n k k' : Nat), (∀ j, j < n → k + j < m) →
    (∀ j, j < n → k' + j < m) → withinB (movSlots k k' n) m = true
  | 0, _, _, _, _ => rfl
  | n + 1, k, k', h, h' => by
    have := h 0 (by omega); have := h' 0 (by omega)
    simp only [movSlots, withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
      List.all_nil, Bool.and_true]
    refine ⟨⟨by omega, by simpa using this⟩, movSlots_within n (k + 1) (k' + 1)
      (fun j hj => by have := h (j + 1) (by omega); omega)
      (fun j hj => by have := h' (j + 1) (by omega); omega)⟩

theorem immSlots_within {m : Nat} : ∀ (vs : List UInt64) (k : Nat),
    (∀ j, j < vs.length → k + j < m) → withinB (immSlots k vs) m = true
  | [], _, _ => rfl
  | v :: vs, k, h => by
    simp only [immSlots, withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
      List.all_nil, Bool.and_true]
    exact ⟨by have := h 0 (by simp); omega, immSlots_within vs (k + 1) fun j hj => by
      have := h (j + 1) (by simp; omega); omega⟩

theorem paramWords_below (wp : Nat → Bool) :
    ∀ (ps : List Ty) (j : Nat), (∀ i, wp (j + i) = true → REXT + j + i < FR) →
      ∀ x, Operand.slot x ∈ paramWords wp ps j → x < FR
  | [], _, _, _, hx => by simp [paramWords] at hx
  | _ :: ts, j, h, x, hx => by
    simp only [paramWords, List.mem_append] at hx
    rcases hx with hx | hx
    · exact paramWords_below wp ts (j + 1) (fun i hi => by
        have := h (i + 1) (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi); omega) x hx
    · split at hx
      · have := h 0 (by simpa using ‹wp j = true›); simp at hx; omega
      · simp at hx

theorem callOps_length (wp : Nat → Bool) (ps : List Ty) :
    (callOps wp ps).length = FR + slotsIn (paramLocs wp ps 0 0) := by
  simp [callOps, slotsIn_paramLocs, FR]; omega

section
variable {m : Nat} (hm : FR ≤ m)
include hm

theorem regs_lt : BP < m ∧ RA < m ∧ RB < m ∧ RT < m ∧ RX < m ∧ RY < m ∧ RP < m := by
  simp only [FR, BP, RA, RB, RT, RX, RY, RP] at *; omega

theorem atomTo_within {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (d : Nat) : withinB (atomTo a ρ d) m = true := by
  have hr := regs_lt hm
  have hc := fun x y so d len (hx : x < FR) (hy : y < FR) =>
    withinB_mono (copyB_within x so y d len hx hy) hm
  cases a with
  | var x =>
    simp only [atomTo]; split
    · exact hc _ _ _ _ _ (by decide) (by decide)
    · simp [withinB, opsBelowB, hr, hc _ _ _ _ _ (by decide : RP < FR) (by decide : BP < FR)]
    · simp [withinB, opsBelowB, hr, hc _ _ _ _ _ (by decide : RP < FR) (by decide : BP < FR)]
    · rename_i k w heq
      exact stSlots_within _ BP d hr.1 w k (hρ.slots heq)
  | lit v => exact withinB_mono (writeB_within _ _ _ (by decide)) hm

theorem atomWord_within {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (x : Nat) (hx : x < m) : withinB (atomWord a ρ x) m = true := by
  have hr := regs_lt hm
  cases a with
  | var y =>
    simp only [atomWord]; split
    all_goals try simp [withinB, opsBelowB, hr, hx]
    rename_i k w heq
    exact (hρ y.idx k (by rw [heq]; rfl)).1
  | lit v => simp [atomWord, withinB, opsBelowB, hx]

theorem atomSlots_within {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) (x cnt : Nat) (hx : ∀ j, j < cnt → x + j < m) :
    withinB (atomSlots a ρ x cnt) m = true := by
  have hr := regs_lt hm
  cases a with
  | var y =>
    simp only [atomSlots]; split
    · exact ldSlots_within _ BP _ hr.1 cnt x hx
    · simp only [withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
        List.all_nil, Bool.and_true]
      exact ⟨⟨hr.2.2.2.2.2.2, by simpa using hr.1⟩, ldSlots_within _ RP _ hr.2.2.2.2.2.2 cnt x hx⟩
    · simp only [withinB, opsBelowB, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
        List.all_nil, Bool.and_true]
      exact ⟨⟨hr.2.2.2.2.2.2, by simpa using hr.1⟩, ldSlots_within _ RP _ hr.2.2.2.2.2.2 cnt x hx⟩
    · rename_i k w heq
      exact movSlots_within _ x k (fun j hj => hx j (by have := Nat.min_le_right w cnt; omega))
        fun j hj =>
        hρ.slots heq j (by have := Nat.min_le_left w cnt; omega)
  | lit v => exact immSlots_within _ x fun j hj => hx j (by rw [chunks_length] at hj; exact hj)

theorem atomSlotsS_within {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) (x cnt : Nat) (hx : ∀ j, j < cnt → x + j < m) (hc : REXT + cnt ≤ FR) :
    withinB (atomSlotsS a ρ x cnt) m = true := by
  unfold atomSlotsS; split
  · split
    · exact atomSlots_within hm a hρ x cnt hx
    · simp only [withinB, Bool.and_eq_true]
      exact ⟨atomSlots_within hm a hρ REXT cnt (fun j hj => by omega),
        movSlots_within _ _ _ hx fun j hj => by omega⟩
  · exact atomSlots_within hm a hρ x cnt hx

theorem elemAddr_within {Γ : List Ty} (i : Atom Γ .u64) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (size : Nat) : withinB (elemAddr i ρ size) m = true := by
  have hr := regs_lt hm
  simp [elemAddr, withinB, opsBelowB, atomWord_within hm i hρ, hr]

theorem placeAddr_within {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) : withinB (placeAddr p ρ) m = true := by
  have hr := regs_lt hm
  have hv := fun l => withinB_mono (varAddr_within l RA (by decide)) hm
  induction p with
  | field p l ih =>
    simp only [placeAddr]; split <;> simp_all [withinB, opsBelowB]
  | _ => simp_all [placeAddr, pairAddrCode, withinB, opsBelowB, elemAddr_within hm _ hρ,
    atomWord_within hm _ hρ]

theorem refStore_within {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (n : Nat) : withinB (refStore p ρ n) m = true := by
  have hr := regs_lt hm
  cases p <;> simp [refStore, sliceStore, pairStore, withinB, opsBelowB, atomWord_within hm _ hρ, hr]

theorem placeRead_within {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) (d : Nat) : withinB (placeRead p ρ d) m = true := by
  have hr := regs_lt hm
  have hc := fun x y so d len (hx : x < FR) (hy : y < FR) =>
    withinB_mono (copyB_within x so y d len hx hy) hm
  cases p <;> simp [placeRead, withinB, opsBelowB, placeAddr_within hm _ hρ, hc, hr, regs_lt_FR,
    atomWord_within hm _ hρ RX hr.2.2.2.2.1]

theorem placeWrite_within {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) (d : Nat) : withinB (placeWrite p ρ d) m = true := by
  have hr := regs_lt hm
  have hc := fun x y so d len (hx : x < FR) (hy : y < FR) =>
    withinB_mono (copyB_within x so y d len hx hy) hm
  cases p <;> simp [placeWrite, withinB, opsBelowB, placeAddr_within hm _ hρ, hc, hr, regs_lt_FR,
    atomWord_within hm _ hρ RX hr.2.2.2.2.1]

theorem placeCheck_within {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) : ∀ c, placeCheck p ρ = some c → withinB c m = true := by
  have hr := regs_lt hm
  induction p <;> intro c hc <;> simp only [placeCheck] at hc
  all_goals first
    | (simp only [Option.some.injEq] at hc; subst hc; simp [withinB, opsBelowB, hr])
    | cases hc
    | (split at hc
       · obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hc
         simp_all [withinB, opsBelowB, atomWord_within hm _ hρ RX hr.2.2.2.2.1,
           atomWord_within hm _ hρ RT hr.2.2.2.1]
       · cases hc)
    | simp_all

theorem guardCode_within {Γ : List Ty} (g : Guard Γ) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (d : Nat) : withinB (guardCode g ρ d) m = true := by
  have hr := regs_lt hm
  cases g with
  | valid p _ =>
    cases h : placeCheck p ρ with
    | none => simp [guardCode, h, withinB, opsBelowB, hr]
    | some c => simp [guardCode, h, withinB, opsBelowB, hr, placeCheck_within hm p hρ c h]

theorem primLoad_within {Γ : List Ty} {ps : List Ty} (args : Args Γ ps) {ρ : List Loc}
    (hρ : SlotsBelow ρ m) : withinB (primLoad args ρ) m = true := by
  have hr := regs_lt hm
  rcases args with _ | ⟨a, _ | ⟨b, _⟩⟩ <;>
    simp [primLoad, withinB, atomWord_within hm _ hρ, hr]

theorem scrutPre_within {Γ : List Ty} {t : Ty} (a : Atom Γ t) {ρ : List Loc} (hρ : SlotsBelow ρ m)
    (n : Nat) : withinB (scrutPre a ρ n) m = true := by
  cases a <;> simp only [scrutPre] <;> try split
  all_goals simp [withinB, atomTo_within hm _ hρ, withinB_mono (writeB_within BP _ _ (by decide)) hm]

theorem argsTo_within {Γ : List Ty} {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat))
    {ρ : List Loc} (hρ : SlotsBelow ρ m) (d : Nat) : withinB (argsTo args oss ρ d) m = true := by
  induction args generalizing oss with
  | nil => rfl
  | cons a _ ih =>
    cases oss with
    | nil => simp [argsTo, ih]
    | cons os oss =>
      have : ∀ os : List Nat,
          withinB (os.foldr (fun o c => .seq (atomTo a ρ (d + o)) c) .skip) m = true := by
        intro os; induction os <;> simp_all [withinB, atomTo_within hm _ hρ]
      simp [argsTo, withinB, this, ih]

theorem argsPass_within {Γ : List Ty} {ps : List Ty} (wp : Nat → Bool) (args : Args Γ ps)
    {ρ : List Loc} (hρ : SlotsBelow ρ m) (d j : Nat)
    (hwp : ∀ i, wp (j + i) = true → REXT + j + i < FR) :
    withinB (argsPass wp args ρ d j) m = true := by
  induction args generalizing d j with
  | nil => rfl
  | cons a as ih =>
    simp only [argsPass, withinB, Bool.and_eq_true]
    refine ⟨?_, ih _ _ fun i hi => by
      have := hwp (i + 1) (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi); omega⟩
    split
    · exact atomWord_within hm _ hρ _ (by have := hwp 0 (by simpa using ‹wp j = true›); omega)
    · exact atomTo_within hm _ hρ _

theorem rargsPass_within {Γ : List Ty} {ps os : List Ty} (args : RArgs Γ ps os)
    {ρ : List Loc} (hρ : SlotsBelow ρ m) (d : Nat) : withinB (rargsPass args ρ d) m = true := by
  induction args generalizing d <;>
    simp_all [rargsPass, withinB, atomTo_within hm _ hρ, placeAddr_within hm _ hρ,
      refStore_within hm _ hρ]

end

/-- The extern argument code stays in the frame, and the argument operands are slots below `FR`,
when the argument slots `x … x + wordCount - 1` are. -/
theorem extArgs_within {Γ : List Ty} {ps : List ExtParam} (args : EArgs Γ ps) {ρ : List Loc}
    {m : Nat} (hm : FR ≤ m) (hρ : SlotsBelow ρ m) (x : Nat) (h : x + args.wordCount ≤ FR) :
    withinB (extArgs args ρ x).1 m = true ∧ ∀ a ∈ (extArgs args ρ x).2, extArgBelow FR a = true := by
  have hr := regs_lt hm
  induction args generalizing x
  case bufIn b _ ih =>
    cases b with
    | const =>
      obtain ⟨h1, h2⟩ := ih x (by simpa only [EArgs.wordCount] using h)
      simp only [extArgs, List.mem_cons, forall_eq_or_imp]; exact ⟨h1, rfl, h2⟩
    | slice a lo len =>
      simp only [EArgs.wordCount] at h
      have := ih (x + 2) (by omega)
      have := atomWord_within hm len hρ (x + 1) (by omega)
      simp_all [extArgs, extArgs.sliceArg, withinB, opsBelowB, extArgBelow,
        placeAddr_within hm _ hρ]
      omega
  case sliceOut a lo len _ ih =>
    simp only [EArgs.wordCount] at h
    have := ih (x + 2) (by omega)
    have := atomWord_within hm len hρ (x + 1) (by omega)
    simp_all [extArgs, extArgs.sliceArg, withinB, opsBelowB, extArgBelow, placeAddr_within hm _ hρ]
    omega
  case word a _ ih =>
    simp only [EArgs.wordCount] at h
    have := ih (x + 1) (by omega)
    have := atomWord_within hm a hρ x (by omega)
    simp_all [extArgs, withinB, opsBelowB, extArgBelow]
    omega
  case bufOut _ ih =>
    obtain ⟨h1, h2⟩ := ih x (by simpa only [EArgs.wordCount] using h)
    simp only [extArgs, List.mem_cons, forall_eq_or_imp]; exact ⟨h1, rfl, h2⟩
  case nil => simp [extArgs, withinB]

theorem getD_below {l : List Operand} {n : Nat} (h : OpsBelow l n) (i : Nat) :
    OpsBelow [l.getD i (.imm 0)] n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => intro x hx; simp at hx
  | some o => intro x hx; simp at hx; subst hx; exact h x (List.mem_of_getElem? hi)

theorem primCode_below {ps : List Ty} {r : Ty} (p : Prim ps r) {as : List Operand} {n : Nat}
    (h : OpsBelow as n) :
    OpsBelow [(primCode p as).2.2.1, (primCode p as).2.2.2] n := by
  have h0 := getD_below h 0
  have h1 := getD_below h 1
  have himm : ∀ w, OpsBelow [Operand.imm w] n := fun w x hx => by simp at hx
  have pair : ∀ a b : Operand, OpsBelow [a] n → OpsBelow [b] n → OpsBelow [a, b] n :=
    fun a b ha hb => by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact ha x (by simp [hx])
      · exact hb x (by simp [hx])
  cases p <;> simp only [primCode] <;> first
    | exact pair _ _ h0 h1 | exact pair _ _ h1 h0 | exact pair _ _ h0 (himm _)

theorem opsBelowB_of {ops : List Operand} {n : Nat} (h : OpsBelow ops n) :
    opsBelowB ops n = true :=
  List.all_eq_true.2 fun o ho => by
    cases o with
    | slot x => simp [h x ho]
    | imm _ => rfl

theorem withinB_seq (a b : Stmt) (n : Nat) : withinB (.seq a b) n = (withinB a n && withinB b n) :=
  rfl

/-- An extern call with the arguments that `extArgs` builds stays in the frame. -/
theorem ext_within {Γ : List Ty} {ps : List ExtParam} (args : EArgs Γ ps) {ρ : List Loc}
    {m : Nat} (hm : FR ≤ m) (hρ : SlotsBelow ρ m)
    (sym : String) (nr : Bool) (h : REXT + args.wordCount ≤ FR) (x : Nat) (hx : x < m) :
    withinB (extArgs args ρ REXT).1 m = true ∧
    withinB (.ext sym nr x (extArgs args ρ REXT).2) m = true := by
  obtain ⟨h1, h2⟩ := extArgs_within args hm hρ REXT h
  refine ⟨h1, ?_⟩
  simp only [withinB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hx, fun a ha => ?_⟩
  have := h2 a ha
  cases a <;> simp_all [extArgBelow] <;> exact opsBelowB_mono this hm

theorem _root_.Millipede.Place.refLoc_nw {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat) :
    (p.refLoc o).nw = 0 := by
  unfold Place.refLoc; split <;> rfl

@[simp] theorem slotsIn_locs {Γ : List Ty} {ps os : List Ty} (as : RArgs Γ ps os) (o : Nat) :
    slotsIn (as.locs o) = 0 := by
  induction as generalizing o <;> simp_all [RArgs.locs, slotsIn, Place.refLoc_nw]

/-- The slot bound of a tail mode for a value of type `t`, which needs `k + t.slotN` slots for its
slots from `k`. -/
def Tl.wk (t : Ty) : Tl → Nat
  | .word k => k + t.slotN
  | _ => 0

@[simp] theorem Tl.wk_up (t : Ty) (tm : Tl) : tm.up.wk t = tm.wk t := by cases tm <;> rfl
@[simp] theorem Tl.wk_none (t : Ty) : Tl.none.wk t = 0 := rfl
@[simp] theorem Tl.wk_split (t : Ty) (f0 : Nat) (cs : List (Nat × Nat × Nat)) :
    (Tl.split f0 cs).wk t = 0 := rfl

/-- The frame bound of a term: its code stays within `m` frame slots when its context's slots and
`Exp.slotNeed` more are within `m`, and so is its word destination. -/
abbrev WithinAll {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Prop :=
  ∀ (tm : Tl) (ρ : List Loc) (n d m : Nat), FR + slotsIn ρ + e.slotNeed ≤ m → SlotsBelow ρ m →
    tm.wk t ≤ m → withinB (lowerM e tm ρ n d) m = true

/-- The frame bound for a term under more binders in memory. -/
theorem within_push {Γ : List Ty} {t s : Ty} {e : Exp (s :: Γ) t} (ih : WithinAll e)
    {ρ : List Loc} {m : Nat} (hm : FR + slotsIn ρ + e.slotNeed ≤ m) (hρ : SlotsBelow ρ m) :
    ∀ (l : Loc), l.slot? = none → ∀ tm n d, tm.wk t ≤ m → withinB (lowerM e tm (l :: ρ) n d) m = true :=
  fun l hl tm n d hw => ih tm _ n d m (by
    have : l.nw = 0 := by cases l <;> simp_all
    simp [this]; omega) (hρ.cons fun k hk => by rw [hl] at hk; cases hk) hw

/-- A slot-resident binder's type has at least one slot. -/
theorem _root_.Millipede.Exp.slotBind_pos {Γ : List Ty} {s t : Ty} {e : Exp (s :: Γ) t}
    (h : e.slotBind = true) : 1 ≤ s.slotN :=
  Ty.slotN_pos (by simp only [Exp.slotBind, Bool.and_eq_true] at h; exact h.1.1)

/-- An arm or continuation under a fresh binder at `n'`, which is slot-resident in the slots from
`FR + slotsIn ρ` after the code `P` that gives it its value, or in memory after `X`. -/
theorem slotArm_within {Γ : List Ty} {s t : Ty} {e : Exp (s :: Γ) t} (ih : WithinAll e)
    {ρ : List Loc} {m : Nat}
    (hm : FR + slotsIn ρ + (if e.slotBind then e.slotNeed + s.slotN else e.slotNeed) ≤ m)
    (hρ : SlotsBelow ρ m) (tm : Tl) (hw : tm.wk t ≤ m) (P X : Stmt) (n' n'' d : Nat)
    (hP : FR + slotsIn ρ + s.slotN ≤ m → withinB P m = true) (hX : withinB X m = true) :
    withinB (if e.slotBind then .seq P (lowerM e tm (.slot n' (FR + slotsIn ρ) s.slotN :: ρ) n'' d)
      else .seq X (lowerM e tm (.own n' :: ρ) n'' d)) m = true := by
  split
  · rename_i hb; simp only [hb, ↓reduceIte] at hm
    have := Exp.slotBind_pos hb
    rw [withinB_seq, hP (by omega), ih tm _ n'' d m (by simp; omega)
      (hρ.cons fun k hk => by simp at hk ⊢; omega) hw]; rfl
  · rename_i hb; simp only [hb, Bool.false_eq_true, ↓reduceIte] at hm
    rw [withinB_seq, hX, ih tm _ n'' d m (by simp; omega) (hρ.cons fun k hk => by simp at hk) hw]
    rfl

/-! ### The frame bound, construct by construct -/

section
variable {Γ : List Ty} {ρ : List Loc} {n d m : Nat}

theorem within_atom {t : Ty} (a : Atom Γ t) : WithinAll (.atom a) := by
  intro tm ρ n d m hm hρ hw
  have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
  simp only [lowerM]; split
  · simp [withinB]
  · simp only [Tl.wk] at hw
    simp [withinB]; exact atomSlots_within hm' _ hρ _ _ fun j hj => by omega
  · simp [withinB, atomTo_within hm' _ hρ]

theorem within_ext {sig : ExtSig} (args : EArgs Γ sig.params)
    (h : (Exp.ext sig args).memOk = true) : WithinAll (.ext sig args) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.memOk, Bool.and_eq_true, decide_eq_true_eq, Exp.slotNeed] at h hm
  have hm' : FR ≤ m := by omega
  have hx := fun x (hx : x < m) => Flat.ext_within args hm' hρ sig.sym sig.noreturn
    (by simp only [REXT, FR] at h ⊢; omega) x hx
  simp only [lowerM]; split
  · rename_i k
    simp only [Tl.wk, show Ty.u64.slotN = 1 from rfl] at hw
    rw [withinB_seq, withinB_seq, withinB_seq, (hx k (by omega)).1, (hx k (by omega)).2]; rfl
  · rw [withinB_seq, withinB_seq, withinB_seq, (hx RX (regs_lt hm').2.2.2.2.1).1,
      (hx RX (regs_lt hm').2.2.2.2.1).2]
    simp [withinB, opsBelowB, regs_lt hm']

theorem within_extMut {sig : ExtSig} {u : Ty} (args : EArgs Γ sig.params) (k : Exp (.u64 :: Γ) u)
    (h : (Exp.extMut sig args k).memOk = true) (ih : WithinAll k) :
    WithinAll (.extMut sig args k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.memOk, Bool.and_eq_true, decide_eq_true_eq, Exp.slotNeed] at h hm
  have hm' : FR ≤ m := by split at hm <;> omega
  have hx := fun x (hx : x < m) => Flat.ext_within args hm' hρ sig.sym sig.noreturn
    (by simp only [REXT, FR] at h ⊢; omega) x hx
  simp only [lowerM]; split
  · rename_i hb; simp only [hb, ↓reduceIte] at hm
    rw [withinB_seq, withinB_seq, withinB_seq, (hx RX (regs_lt hm').2.2.2.2.1).1,
      (hx _ (by omega)).2, ih tm.up _ _ d m (by simp; omega)
        (hρ.cons fun k hk => by simp at hk ⊢; omega) (by simpa using hw)]; rfl
  · rename_i hb; simp only [hb, Bool.false_eq_true, ↓reduceIte] at hm
    rw [withinB_seq, withinB_seq, withinB_seq, withinB_seq, (hx RX (regs_lt hm').2.2.2.2.1).1,
      (hx RX (regs_lt hm').2.2.2.2.1).2, ih tm.up (.own n :: ρ) _ d m (by simp; omega)
        (hρ.cons fun k hk => by simp at hk) (by simpa using hw)]
    simp [withinB, opsBelowB, regs_lt hm']

theorem within_prim {ps : List Ty} {r : Ty} (p : Prim ps r) (args : Args Γ ps) :
    WithinAll (.prim p args) := by
  intro tm ρ n d m hm hρ hw
  have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
  have hb := opsBelowB_of (primCode_below p (as := [.slot RX, .slot RY]) (n := m)
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> simp [regs_lt hm']))
  simp only [opsBelowB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hb
  simp only [lowerM]; split
  · simp [withinB, opsBelowB, hb, primLoad_within hm' _ hρ]
    simp [Tl.wk, Ty.wordTy_slotN p.wordTy] at hw; omega
  · simp [withinB, opsBelowB, hb, primLoad_within hm' _ hρ, regs_lt hm']

theorem within_read {t : Ty} (p : Place Γ t) : WithinAll (.read p) := by
  intro tm ρ n d m hm hρ hw
  have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
  simp only [lowerM]; split
  · rename_i K nw hsf
    obtain ⟨s, y, l, o, k, nn, rfl, hρy, -, -, -, rfl, rfl⟩ := Place.slotField_some hsf
    have hs := hρ.slots hρy
    have hc := Nat.min_le_right t.slotN (nn - lensOff l / 8)
    have hc' := Nat.min_le_left t.slotN (nn - lensOff l / 8)
    split
    · simp only [Tl.wk] at hw
      simp only [withinB, Bool.true_and]
      exact movSlots_within _ _ _ (fun j hj => by omega)
        fun j hj => by have := hs (lensOff l / 8 + j) (by omega); omega
    · simp only [withinB, Bool.true_and]
      exact stSlots_within _ BP _ (regs_lt hm').1 _ _ fun j hj => by
        have := hs (lensOff l / 8 + j) (by omega); omega
  · split
    · rename_i k
      simp only [Tl.wk] at hw
      simp [withinB, placeAddr_within hm' p hρ]
      exact ldSlots_within _ RA 0 (regs_lt hm').2.1 _ k fun j hj => by omega
    · simp [withinB, placeRead_within hm' _ hρ]

theorem within_let {s t : Ty} (e₁ : Exp Γ s) (e₂ : Exp (s :: Γ) t) (ih₁ : WithinAll e₁)
    (ih₂ : WithinAll e₂) : WithinAll (.let_ e₁ e₂) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by split at hm <;> omega
  simp only [lowerM]
  split
  · rename_i hsb
    simp only [hsb, ↓reduceIte] at hm
    have hpos := Exp.slotBind_pos hsb
    have hmx := Nat.le_max_left e₁.slotNeed (e₂.slotNeed + s.slotN)
    have hmy := Nat.le_max_right e₁.slotNeed (e₂.slotNeed + s.slotN)
    have hρ' : SlotsBelow (.slot n (FR + slotsIn ρ) s.slotN :: ρ) m :=
      hρ.cons fun k hk => by simp at hk ⊢; omega
    have hi : withinB (if e₁.Conf (.word (FR + slotsIn ρ)) then
        lowerM e₁ (.word (FR + slotsIn ρ)) ρ (n + s.size) n
      else .seq (lowerM e₁ .none ρ (n + s.size) n)
        (ldSlots (scalarWidth s.size) (FR + slotsIn ρ) (.slot BP) n s.slotN)) m = true := by
      split
      · exact ih₁ _ _ _ _ _ (by omega) hρ (by simp only [Tl.wk]; omega)
      · rw [withinB_seq, ih₁ .none ρ (n + s.size) n m (by omega) hρ (by simp),
          ldSlots_within _ BP _ (regs_lt hm').1 _ _ fun j hj => by omega]; rfl
    rw [withinB_seq, withinB_seq, hi, ih₂ tm.up _ (n + s.size) d m (by simp; omega) hρ'
      (by simpa using hw)]; rfl
  · rename_i hsb
    simp only [hsb, Bool.false_eq_true, ↓reduceIte] at hm
    simp [withinB, ih₁ .none ρ (n + s.size) n m (by omega) hρ (by simp),
      ih₂ tm.up (.own n :: ρ) (n + s.size) d m (by simp; omega)
        (hρ.cons fun k hk => by simp at hk) (by simpa using hw)]

theorem within_call {ps : List Ty} {r : Ty} (name : String) (body : Exp ps r) (args : Args Γ ps)
    (ih : WithinAll body) : WithinAll (.call name body args) := by
  intro tm ρ n d m hm hρ hw
  have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
  have hwp : ∀ i, body.wordParam (0 + i) = true → REXT + 0 + i < FR := fun i hi => by
    simp only [Exp.wordParam, Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hi
    simp only [REXT, FR] at hi ⊢; omega
  have hops : opsBelowB (callOps body.wordParam ps) m = true := by
    simp only [opsBelowB, callOps, List.all_cons, List.all_append, Bool.and_eq_true,
      List.all_eq_true]
    refine ⟨by simp [regs_lt hm'], fun o ho => by rw [List.eq_of_mem_replicate ho], fun o ho => ?_⟩
    cases o with
    | slot x => have := paramWords_below _ _ _ hwp x ho; simp; omega
    | imm _ => rfl
  have hlen := callOps_length body.wordParam ps
  have hq := wordParams_le body
  have := ih .none (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps)
    (FR + slotsIn (paramLocs body.wordParam ps 0 0) + body.slotNeed) (by omega)
    (SlotsBelow.paramLocs _ _ (by omega)) (by simp)
  have := regs_lt hm'
  have hA := argsPass_within hm' body.wordParam args hρ n 0 hwp
  simp only [lowerM]
  split
  · rename_i hwc
    have hts := body.slotTy_of_word hwc
    have hcap := Ty.slotN_le hts
    have hW := ih (.word (FR + slotsIn (paramLocs body.wordParam ps 0 0)))
      (paramLocs body.wordParam ps 0 0) (ctxSize ps + r.size) (ctxSize ps)
      (FR + slotsIn (paramLocs body.wordParam ps 0 0) + max r.slotN body.slotNeed) (by omega)
      (SlotsBelow.paramLocs _ _ (by omega)) (by simp [Tl.wk]; omega)
    have hrb : opsBelowB (retSlots (FR + slotsIn (paramLocs body.wordParam ps 0 0)) r.slotN)
        (FR + slotsIn (paramLocs body.wordParam ps 0 0) + max r.slotN body.slotNeed) = true := by
      simp only [opsBelowB, retSlots, List.all_map, List.all_eq_true, List.mem_range]
      intro j hj; simp only [Function.comp, decide_eq_true_eq]; omega
    have hrl : (retSlots (FR + slotsIn (paramLocs body.wordParam ps 0 0)) r.slotN).length =
        r.slotN := by simp [retSlots]
    split <;> simp only [withinB, Bool.and_eq_true, decide_eq_true_eq, hrl] <;> and_intros
    all_goals first
      | rfl | exact hW | exact hops | exact hA | exact this | exact hrb | omega
      | (simp only [Tl.wk] at hw; omega)
      | (exact stSlots_within _ BP _ (regs_lt hm').1 _ _ fun j hj => by
          simp only [REXT, FR, SLOT_CAP] at *; omega)
      | trivial
      | (simp only [REXT]; simp only [FR, SLOT_CAP] at hm' hcap; omega)
      | (simp [opsBelowB, regs_lt hm'] <;> omega)
  · split <;> simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] <;> and_intros
    all_goals first
      | rfl | exact hops | exact hA | exact this | omega
      | exact copyB_within' hm' _ _ _ _ _ (by decide) (by decide)
      | (simp [opsBelowB, regs_lt hm'] <;> omega)
      | (rename_i k; simp only [Tl.wk] at hw
         exact ldSlots_within _ BP _ (regs_lt hm').1 _ k fun j hj => by omega)

theorem within_callRef {ps os : List Ty} {r u : Ty} (name : String) (req : Env ps → Prop)
    (body : Exp ps (.tup (r :: os))) (args : RArgs Γ ps os) (k : Exp (r :: Γ) u)
    (ihb : WithinAll body) (ihk : WithinAll k) : WithinAll (.callRef name req body args k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by omega
  have := ihb (callTl r args) (args.locs 0) (args.frame + r.size) args.frame
    (FR + body.slotNeed) (by simp) (SlotsBelow.of_none (args.locs_slot? 0)) (by simp)
  have h1 : 1 ≤ FR + body.slotNeed := by simp only [FR]; omega
  simp [lowerM, withinB, opsBelowB, rargsPass_within hm' _ hρ, regs_lt hm',
    ihk tm.up (.own (n + args.frame) :: ρ) (n + args.frame + r.size) d m (by simp; omega)
      (hρ.cons fun k hk => by simp at hk) (by simpa using hw)]
  exact ⟨this, h1⟩

theorem within_ite {t : Ty} (c : Atom Γ .bool) (e₁ e₂ : Exp Γ t) (ih₁ : WithinAll e₁)
    (ih₂ : WithinAll e₂) : WithinAll (.ite c e₁ e₂) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by omega
  have := Nat.le_max_left e₁.slotNeed e₂.slotNeed; have := Nat.le_max_right e₁.slotNeed e₂.slotNeed
  simp [lowerM, withinB, opsBelowB, regs_lt hm', atomWord_within hm' _ hρ RT (regs_lt hm').2.2.2.1,
    ih₁ tm ρ n d m (by omega) hρ hw, ih₂ tm ρ n d m (by omega) hρ hw]

/-- One arm of a `match` or `case` on a slot-resident scrutinee, which moves the slots from `src`
into the binder's slots or to memory. At most `cnt` slots are moved, which keeps the bound
syntactic. -/
theorem matchArm_within {p t : Ty} {e : Exp (p :: Γ) t} (ih : WithinAll e) {src cnt : Nat}
    (hk : src + cnt ≤ m) (hm' : FR ≤ m)
    (hm : FR + slotsIn ρ + (if e.slotBind then e.slotNeed + p.slotN else e.slotNeed) ≤ m)
    (hρ : SlotsBelow ρ m) (tm : Tl) (hw : tm.wk t ≤ m) (n' d : Nat) :
    withinB (slotArm e.slotBind p (FR + slotsIn ρ) src cnt n'
      fun l => lowerM e tm (l :: ρ) (n' + p.size) d) m = true := by
  have h1 := Nat.min_le_left p.slotN cnt; have h2 := Nat.min_le_right p.slotN cnt
  exact slotArm_within ih hm hρ tm hw _ _ n' _ d
    (fun hK => movSlots_within _ _ _ (fun j hj => by omega) fun j hj => by omega)
    (stSlots_within _ BP _ (regs_lt hm').1 _ _ fun j hj => by omega)

/-- One arm of a `match`, `case` or `take` whose payload is in memory at `b + lp`, where `b` is a
scratch slot. -/
theorem memArm_within {p t : Ty} {e : Exp (p :: Γ) t} (ih : WithinAll e) (hm' : FR ≤ m)
    (hm : FR + slotsIn ρ + (if e.slotBind then e.slotNeed + p.slotN else e.slotNeed) ≤ m)
    (hρ : SlotsBelow ρ m) (tm : Tl) (hw : tm.wk t ≤ m) {b : Nat} (hb : b < FR) (lp n' d : Nat) :
    withinB (memArm e.slotBind p (FR + slotsIn ρ) b lp n'
      fun l => lowerM e tm (l :: ρ) (n' + p.size) d) m = true :=
  slotArm_within ih hm hρ tm hw _ _ n' _ d
    (fun hK => ldSlots_within _ b _ (by omega) _ _ fun j hj => by omega)
    (copyB_within' hm' _ _ _ _ _ hb (by decide))

theorem within_match {ε α t : Ty} (sc : Atom Γ (.result ε α)) (eE : Exp (ε :: Γ) t)
    (eO : Exp (α :: Γ) t) (ihE : WithinAll eE) (ihO : WithinAll eO) :
    WithinAll (.match_ sc eE eO) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have := Nat.le_max_left (if eE.slotBind then eE.slotNeed + ε.slotN else eE.slotNeed)
    (if eO.slotBind then eO.slotNeed + α.slotN else eO.slotNeed)
  have := Nat.le_max_right (if eE.slotBind then eE.slotNeed + ε.slotN else eE.slotNeed)
    (if eO.slotBind then eO.slotNeed + α.slotN else eO.slotNeed)
  have hm' : FR ≤ m := by omega
  have hw' : tm.up.wk t ≤ m := by simpa using hw
  simp only [lowerM]
  split
  · rename_i k hk
    obtain ⟨y, rfl, hy⟩ : ∃ y, sc = .var y ∧ (ρ.getD y.idx default).slot? = some k := by
      cases sc with
      | var y => exact ⟨y, rfl, hk⟩
      | lit v => simp [Atom.slotOf] at hk
    have hkm := hρ y.idx k hy
    have hk' : k + 1 + ((Atom.var y).slotNw ρ - 1) ≤ m := by have := hkm.2; simp only [Atom.slotNw] at *; omega
    have hO := matchArm_within ihO hk' hm' (by omega) hρ _ hw' (n + (Ty.result ε α).size) d
    have hE := matchArm_within ihE hk' hm' (by omega) hρ _ hw' (n + (Ty.result ε α).size) d
    simp only [withinB, hO, hE]
    simp [opsBelowB, regs_lt hm', hkm.1]
  · have hO := memArm_within ihO hm' (by omega) hρ _ hw' (b := BP) (by decide)
      (scrutLoc sc ρ n + payloadOff (Data.shape (Except ε.carrier α.carrier)))
      (n + (Ty.result ε α).size) d
    have hE := memArm_within ihE hm' (by omega) hρ _ hw' (b := BP) (by decide)
      (scrutLoc sc ρ n + payloadOff (Data.shape (Except ε.carrier α.carrier)))
      (n + (Ty.result ε α).size) d
    simp only [withinB, hO, hE]
    simp [opsBelowB, regs_lt hm', scrutPre_within hm' _ hρ]

/-- The arguments' words into the `N` slots from `x`. -/
theorem argsSlots_within {x N : Nat} (hm' : FR ≤ m) (hρ : SlotsBelow ρ m) (hx : x + N ≤ m) :
    ∀ {ps : List Ty} (args : Args Γ ps) (oss : List (List Nat)),
    withinB (argsSlots ρ x N args oss) m = true
  | _, .nil, oss => by cases oss <;> rfl
  | _, .cons _ _, [] => rfl
  | _, .cons a as, os :: oss => by
    simp only [argsSlots, withinB_seq, argsSlots_within hm' hρ hx as oss, Bool.and_true]
    split
    · exact atomSlots_within hm' a hρ _ _ fun j hj => by
        have := Nat.min_le_right (Ty.slotN ‹_›) (N - os.headD 0 / 8); omega
    · rfl

/-- A constructor into the `N` slots from `x`, at most `SLOT_CAP` of them. -/
theorem ctorCode_within {ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    {x N : Nat} (hm' : FR ≤ m) (hρ : SlotsBelow ρ m) (hN1 : 1 ≤ N) (hN : N ≤ SLOT_CAP)
    (hx : x + N ≤ m) : withinB (ctorCode args plan ρ x N) m = true := by
  have hS : withinB (ctorSlots args plan ρ REXT N) m = true := by
    unfold ctorSlots
    rw [withinB_seq, argsSlots_within hm' hρ (by simp only [REXT, FR, SLOT_CAP] at *; omega)]
    split <;> simp [withinB, opsBelowB] <;> simp only [REXT, FR] at *; omega
  unfold ctorCode; split
  · unfold ctorSlots
    rw [withinB_seq, argsSlots_within hm' hρ hx]
    split <;> simp [withinB, opsBelowB]; omega
  · rw [withinB_seq, hS, movSlots_within _ _ _ (fun j hj => by omega)
      (fun j hj => by simp only [REXT, FR, SLOT_CAP] at *; omega)]; rfl

/-- An `ok` or `err` constructor. -/
theorem resultCode_within {p : Ty} (ε α : Ty) (a : Atom Γ p) (tag : Nat)
    (tm : Tl) (hρ : SlotsBelow ρ m) (hm' : FR ≤ m) (hw : tm.wk (.result ε α) ≤ m) :
    withinB (resultCode ε α a tag tm ρ d) m = true := by
  unfold resultCode; split
  · simp only [Tl.wk] at hw
    split
    · rename_i hs
      have hres := (slotSum_facts hs).1
      exact ctorCode_within _ _ hm' hρ (Ty.slotN_pos hres) (Ty.slotN_le hres) hw
    · rfl
  all_goals simp [withinB, opsBelowB, regs_lt hm', atomTo_within hm' _ hρ]

theorem within_ok {ε α : Ty} (a : Atom Γ α) : WithinAll (Exp.ok (ε := ε) a) := by
  intro tm ρ n d m hm hρ hw
  simp only [lowerM, withinB, Bool.true_and]
  exact resultCode_within ε α a 1 tm hρ (by simp only [Exp.slotNeed] at hm; omega) hw

theorem within_err {ε α : Ty} (a : Atom Γ ε) : WithinAll (Exp.err (α := α) a) := by
  intro tm ρ n d m hm hρ hw
  simp only [lowerM, withinB, Bool.true_and]
  exact resultCode_within ε α a 0 tm hρ (by simp only [Exp.slotNeed] at hm; omega) hw

/-- The loop code of a large constructor uses only scratch slots and slots of `ρ`. -/
theorem mkCode?_within {ps : List Ty} {t : Ty} {c : Ctor ps t} {args : Args Γ ps}
    {ρ : List Loc} {d W m : Nat} {code : Stmt} (hm : FR ≤ m) (hρ : SlotsBelow ρ m)
    (h : mkCode? c args ρ d W = some code) : withinB code m = true := by
  unfold mkCode? at h
  split at h
  · rename_i hfc
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨k, w, P, T, rfl, -⟩ := fillCode?_spec hfc
    simp [withinB, opsBelowB, fillLoop, regs_lt hm, writeB_within' hm]
  · unfold copyCode? at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          simp [withinB, opsBelowB, copyLoop, regs_lt hm, argsTo_within hm _ _ hρ]
        · simp at h
      · simp at h
    · simp at h

theorem within_mk {ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) :
    WithinAll (.mk c args) := by
  intro tm ρ n d m hm hρ hw
  have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
  cases tm
  case word k =>
    simp only [Tl.wk] at hw
    simp only [lowerM, withinB, Bool.true_and]
    split
    · rename_i hok
      have hts : t.slotTy = true := by simp only [Ctor.slotOk, Bool.and_eq_true] at hok; exact hok.1.1
      exact ctorCode_within _ _ hm' hρ (Ty.slotN_pos hts) (Ty.slotN_le hts) hw
    · rfl
  case none =>
    simp only [lowerM]
    split
    · rename_i hfc
      exact mkCode?_within hm' hρ hfc
    · split <;> simp [withinB, opsBelowB, regs_lt hm', argsTo_within hm' _ _ hρ]
  all_goals simp only [lowerM]; split <;> simp [withinB, opsBelowB, regs_lt hm', argsTo_within hm' _ _ hρ]

theorem within_assign {t u : Ty} (p : Place Γ t) (a : Atom Γ t) (k : Exp Γ u) (ih : WithinAll k) :
    WithinAll (.assign p a k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by omega
  simp only [lowerM]; split
  · rename_i x hx
    obtain ⟨y, rfl, hy⟩ := Place.slotOf_some hx
    have := hρ _ _ hy
    simp [withinB, ih tm ρ n d m hm hρ hw]
    have h2 := this.2
    exact atomSlots_within hm' _ hρ x _ fun j hj => by
      simp [List.getD_eq_getElem?_getD, Place.root] at hj h2 ⊢; omega
  · split
    · rename_i K nw hsf
      obtain ⟨s, y, l, o, k, nn, rfl, hρy, -, -, hts, rfl, rfl⟩ := Place.slotField_some hsf
      have hs := hρ.slots hρy
      have hcap := Ty.slotN_le hts
      simp [withinB, ih tm ρ n d m hm hρ hw]
      exact atomSlotsS_within hm' _ hρ _ _ (fun j hj => by
        have := Nat.lt_min.mp hj
        have := hs (lensOff l / 8 + j) (by omega); omega)
        (Nat.le_trans (Nat.add_le_add_left (Nat.min_le_left _ _) _)
          (by simp only [REXT, FR, SLOT_CAP] at *; omega))
    · simp [withinB, atomTo_within hm' _ hρ, placeWrite_within hm' _ hρ, ih tm ρ n d m hm hρ hw]

theorem within_case {t p q u : Ty} (sc : Atom Γ t) (sp : Split t p q) (eP : Exp (p :: Γ) u)
    (eQ : Exp (q :: Γ) u) (ihP : WithinAll eP) (ihQ : WithinAll eQ) :
    WithinAll (.case sc sp eP eQ) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have := Nat.le_max_left (if eP.slotBind then eP.slotNeed + p.slotN else eP.slotNeed)
    (if eQ.slotBind then eQ.slotNeed + q.slotN else eQ.slotNeed)
  have := Nat.le_max_right (if eP.slotBind then eP.slotNeed + p.slotN else eP.slotNeed)
    (if eQ.slotBind then eQ.slotNeed + q.slotN else eQ.slotNeed)
  have hm' : FR ≤ m := by omega
  have hw' : tm.up.wk u ≤ m := by simpa using hw
  simp only [lowerM]
  split
  · rename_i k hk
    obtain ⟨y, rfl, hy⟩ : ∃ y, sc = .var y ∧ (ρ.getD y.idx default).slot? = some k := by
      cases sc with
      | var y => exact ⟨y, rfl, hk⟩
      | lit v => simp [Atom.slotOf] at hk
    have hkm := hρ y.idx k hy
    have hr : sp.restOff ≤ 1 := by unfold Split.restOff; split <;> omega
    have hP := matchArm_within ihP (src := k + 1) (cnt := (Atom.var y).slotNw ρ - 1)
      (by have := hkm.2; simp only [Atom.slotNw] at *; omega) hm' (by omega) hρ _ hw' (n + t.size) d
    have hQ := matchArm_within ihQ (src := k + sp.restOff)
      (cnt := (Atom.var y).slotNw ρ - sp.restOff)
      (by have := hkm.2; simp only [Atom.slotNw] at *; omega) hm' (by omega) hρ _ hw' (n + t.size) d
    simp only [withinB, hP, hQ]
    simp [opsBelowB, regs_lt hm', hkm.1]
  have hP := memArm_within ihP hm' (by omega) hρ tm.up hw' (b := BP) (by decide)
    (scrutLoc sc ρ n + payloadOff t.data.shape) (n + t.size) d
  simp only [withinB, hP]
  simp [opsBelowB, regs_lt hm', scrutPre_within hm' _ hρ,
    withinB_mono (restCode_within _ _ _ _ _ _) hm']
  have : eQ.slotNeed ≤ if eQ.slotBind then eQ.slotNeed + q.slotN else eQ.slotNeed := by
    split <;> omega
  exact within_push ihQ (by omega) hρ (.own _) rfl _ _ _ (by simpa using hw)

theorem within_take {t u : Ty} {N : Nat} {dflt : Inhabited t.carrier} (p : Place Γ (.slots t N))
    (i : Atom Γ .u64) (k : Exp (t :: Γ) u) (ih : WithinAll k) :
    WithinAll (Exp.take (dflt := dflt) p i k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by split at hm <;> omega
  have hk := memArm_within ih hm' hm hρ tm.up (by simpa using hw) (b := RA) (by decide) 0 n d
  simp only [lowerM]
  simp only [withinB_seq, hk]
  simp [withinB, placeAddr_within hm' _ hρ, elemAddr_within hm' _ hρ]

theorem within_put {t u : Ty} {N : Nat} (p : Place Γ (.slots t N))
    (i : Atom Γ .u64) (a : Atom Γ t) (k : Exp Γ u) (ih : WithinAll k) :
    WithinAll (.put p i a k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  have hm' : FR ≤ m := by omega
  simp [lowerM, withinB, atomTo_within hm' _ hρ, placeAddr_within hm' _ hρ,
    elemAddr_within hm' _ hρ, copyB_within' hm', regs_lt_FR, ih tm ρ n d m hm hρ hw]

/-- A borrow `&p` or `&mut p`: the body under the reference's location, and the continuation under
its result's. -/
theorem within_borrow {t u v : Ty} (p : Place Γ t) {body : Exp (t :: Γ) u'} {k : Exp (u :: Γ) v}
    {tmb : Tl} (ihb : WithinAll body) (ihk : WithinAll k) (hb : tmb.wk u' = 0)
    (hm : FR + slotsIn ρ + max body.slotNeed k.slotNeed ≤ m) (hρ : SlotsBelow ρ m) (tm : Tl)
    (hw : tm.wk v ≤ m) (n d : Nat) :
    withinB (.seq (.tick (.ref p.depth)) (.seq (placeAddr p ρ)
      (.seq (refStore p ρ n)
      (.seq (lowerM body tmb (p.refLoc n :: ρ) (n + p.slotW + u.size) (n + p.slotW))
        (lowerM k tm.up (.own (n + p.slotW) :: ρ) (n + p.slotW + u.size) d))))) m = true := by
  have := Nat.le_max_left body.slotNeed k.slotNeed; have := Nat.le_max_right body.slotNeed k.slotNeed
  have hm' : FR ≤ m := by omega
  simp [withinB, placeAddr_within hm' _ hρ, refStore_within hm' _ hρ,
    within_push ihb (by omega) hρ _ (Place.refLoc_slot? _ _) tmb _ _ (by omega)]
  exact within_push ihk (by omega) hρ (.own _) rfl _ _ _ (by simpa using hw)

/-- The parts of a loop's frame bound. -/
theorem loop_bound {B A C X Y K m : Nat} (h : B + max (A + C + max X Y) (A + K) ≤ m) :
    B + A + C + X ≤ m ∧ B + A + C + Y ≤ m ∧ B + A + K ≤ m := by
  have := Nat.le_max_left (A + C + max X Y) (A + K); have := Nat.le_max_right (A + C + max X Y) (A + K)
  have := Nat.le_max_left X Y; have := Nat.le_max_right X Y
  omega

theorem within_loop {ts : List Ty} {s u : Ty} (N : Nat) (cs : Carry Γ ts) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts)))
    (k : Exp (s :: Γ) u) (ihc : WithinAll c) (ihb : WithinAll body) (ihk : WithinAll k) :
    WithinAll (.loop N cs init c body k) := by
  intro tm ρ n d m hm hρ hw
  simp only [Exp.slotNeed] at hm
  obtain ⟨hm₁, hm₂, hm₃⟩ := loop_bound hm
  have := Nat.le_max_left 1 c.slotNeed; have := Nat.le_max_right 1 c.slotNeed
  have := Nat.le_max_left s.slotN body.slotNeed; have := Nat.le_max_right s.slotN body.slotNeed
  have hm' : FR ≤ m := by omega
  have hr := regs_lt hm'
  have hwu := (Tl.wk_up _ tm) ▸ hw
  have hbA : Exp.bodyW c body k = true → Exp.accSlot c body k = true := fun h => by
    simp only [Exp.bodyW, Bool.and_eq_true] at h; exact h.1.1.1.1
  have hN : Exp.bodyW c body k = true → (Ty.pair s (.tup ts)).slotN = s.slotN := fun h => by
    simp only [Exp.bodyW, Bool.and_eq_true, decide_eq_true_eq] at h; unfold Ty.slotN; rw [h.1.1.2]
  have hpos : Exp.accSlot c body k = true → 1 ≤ s.slotN := fun hA =>
    Ty.slotN_pos (by simp only [Exp.accSlot, Bool.and_eq_true] at hA; exact hA.1.1.1)
  cases hA : Exp.accSlot c body k <;> cases hC : Exp.cntSlot c body <;>
    cases hB : Exp.bodyW c body k <;> cases hW : c.Conf (.word FR)
  all_goals try (have h' := hbA hB; rw [hA] at h'; cases h')
  all_goals try have := hpos hA
  all_goals
    simp only [hA, hC, hB, hW, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hm₁ hm₂ hm₃
    simp only [lowerM, hA, hC, hB, hW, accLoc, cntLoc, bodyTl, flagTl, bodyLoc,
      Bool.false_eq_true, ↓reduceIte]
    simp [withinB, opsBelowB, cntTest, cntEnter, cntNext, cntInit, accNext, accInit, flagLoad,
      hr, atomTo_within hm' _ hρ, copyB_within' hm', Loc.off]
  all_goals and_intros
  all_goals first
    | omega
    | exact atomSlots_within hm' _ hρ _ _ fun j hj => by omega
    | exact ldSlots_within _ BP _ hr.1 _ _ fun j hj => by omega
    | exact movSlots_within _ _ _ (fun j hj => by omega) fun j hj => by omega
    | refine ihc _ _ _ _ _ ?_ ?_ (by simp [Tl.wk, show Ty.bool.slotN = 1 from rfl] <;> omega)
    | refine ihb _ _ _ _ _ ?_ ?_ (by
        first | (simp [Tl.wk]; done) | (simp only [Tl.wk, hN hB]; omega))
    | refine ihk _ _ _ _ _ ?_ ?_ hwu
  all_goals first
    | (simp; omega)
    | (refine SlotsBelow.cons (SlotsBelow.cons hρ ?_) ?_ <;> intro k hk <;>
        simp [Loc.slot?] at hk ⊢ <;> omega)
    | (refine SlotsBelow.cons hρ ?_; intro k hk; simp [Loc.slot?] at hk ⊢ <;> omega)

end

/-- Lowered code stays within its frame: the scratch slots `FR`, the slots of the slot-resident
variables in context, and `Exp.slotNeed` more for its own slot-resident binders. Every call
declares `FR` and its body's `slotNeed`, and its body stays within them. This holds for every term
in the lowered fragment, where extern calls take at most `FR - REXT` argument words. -/
theorem lowerM_within {Γ : List Ty} {t : Ty} (e : Exp Γ t) (h : e.memOk = true) : WithinAll e := by
  induction e <;> simp only [Exp.memOk, Bool.and_eq_true] at h
  case atom a => exact within_atom a
  case let_ e₁ e₂ ih₁ ih₂ => exact within_let e₁ e₂ (ih₁ h.1) (ih₂ h.2)
  case ite c e₁ e₂ ih₁ ih₂ => exact within_ite c e₁ e₂ (ih₁ h.1) (ih₂ h.2)
  case prim p args => exact within_prim p args
  case call name body args ih => exact within_call name body args (ih h)
  case ok a => exact within_ok a
  case err a => exact within_err a
  case match_ sc eE eO ihE ihO => exact within_match sc eE eO (ihE h.1) (ihO h.2)
  case ext sig args => exact within_ext args (by simp [Exp.memOk, h])
  case extMut sig args k ih => exact within_extMut args k (by simp [Exp.memOk, h]) (ih h.2)
  case mk c args => exact within_mk c args
  case read p => exact within_read p
  case assign p a k ih => exact within_assign p a k (ih h.2)
  case case sc sp eP eQ ihP ihQ => exact within_case sc sp eP eQ (ihP h.1.2) (ihQ h.2)
  case put p i a k ih => exact within_put p i a k (ih h.2)
  case take _ _ _ dflt p i k ih => exact within_take (dflt := dflt) p i k (ih h.2)
  case borrowShr p body k ihb ihk =>
    intro tm ρ n d m hm hρ hw
    exact within_borrow p (ihb h.1.2) (ihk h.2) rfl hm hρ tm hw n d
  case borrowMut p body k ihb ihk =>
    intro tm ρ n d m hm hρ hw
    exact within_borrow p (ihb h.1.2) (ihk h.2) rfl hm hρ tm hw n d
  case callRef name req body args k ihb ihk => exact within_callRef name req body args k (ihb h.1.2) (ihk h.2)
  case guard g =>
    intro tm ρ n d m hm hρ hw
    have hm' : FR ≤ m := by simp only [Exp.slotNeed] at hm; omega
    simp [lowerM, withinB, guardCode_within hm' _ hρ]
  case loop N cs init c body k ihc ihb ihk =>
    exact within_loop N cs init c body k (ihc h.1.1.2) (ihb h.1.2) (ihk h.2)

end Millipede.Flat

namespace Millipede.Lin

/-- The main statement of a lowered program stays within its scratch frame. -/
theorem lowerProg_within (p : Program) (hi : p.init.memOk = true) (hs : p.step.memOk = true) :
    withinB (Flat.lowerProg p).main (Flat.lowerProg p).frame = true := by
  have hm : Flat.FR ≤ Flat.FR + max p.init.slotNeed p.step.slotNeed := Nat.le_add_right _ _
  have hρ : Flat.SlotsBelow [.own 0] (Flat.FR + max p.init.slotNeed p.step.slotNeed) :=
    Flat.SlotsBelow.of_none fun i => by cases i <;> rfl
  have := Nat.le_max_left p.init.slotNeed p.step.slotNeed
  have := Nat.le_max_right p.init.slotNeed p.step.slotNeed
  have h1 := Flat.lowerM_within _ hi .none [] p.State.size 0
    (Flat.FR + max p.init.slotNeed p.step.slotNeed) (by simp [Flat.slotsIn]; omega)
    (Flat.SlotsBelow.of_none fun _ => rfl) (by simp)
  have h2 := Flat.lowerM_within _ hs (.whole 0) [.own 0] p.State.size 0
    (Flat.FR + max p.init.slotNeed p.step.slotNeed) (by simp [Flat.slotsIn]; omega) hρ
    (by simp [Flat.Tl.wk])
  have h3 := Flat.lowerM_within _ hs .none [.own 0] (p.State.size + p.State.size) p.State.size
    (Flat.FR + max p.init.slotNeed p.step.slotNeed) (by simp [Flat.slotsIn]; omega) hρ (by simp)
  simp only [Flat.lowerProg, Flat.stepCode]
  split <;> simp [withinB, opsBelowB, h1, h2, h3, Flat.copyB_within' hm]

/-- Lowered code stays within its frames, so its linearization is well formed, as `select`
assumes. -/
theorem lower_linearize_wf {p : Program} {fp : Flat.Prog} (hl : Flat.lower p = .ok fp)
    (M : Nat) : (linearize fp M).Wf := by
  unfold Flat.lower at hl
  split at hl
  · rename_i hok
    cases hl
    simp only [Bool.and_eq_true] at hok
    exact linearize_wf _ M (withinB_spec _ _ (lowerProg_within p hok.1.1 hok.1.2))
  · cases hl

end Millipede.Lin
