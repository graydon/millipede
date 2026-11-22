import Millipede.Core.Wf
import Millipede.Core.Denote

/-!
# What the borrow checker guarantees

In the value semantics an exclusive borrow reads the place when the borrow begins and writes the
body's handed-back value back when it ends, and a call with `&mut` arguments writes the callee's
handed-back values into the argument places one after the other. The machine instead passes
addresses, so a borrow body and a callee update the lender's storage in place. The two agree
because, while a borrow is live, nothing else touches the lent place. This file states that
guarantee as a property of the term and proves that every term the checker accepts has it.

A loan on a binder blocks an access when the loan's path and the access's path overlap and either
the loan is exclusive or the access is not a read. `Exp.Avoids k l e` says that no access in `e`
to binder `k` is blocked by loan `l`. Accesses are read off the syntax, so the property covers
every evaluation path at once. `Exp.Frozen e` says that at every borrow in `e` the body avoids
the loan the borrow creates, and that the reference arguments of every call are separated:
after an `&mut p` argument the later arguments do not touch anything overlapping `p`, and after
an `&p` argument they do not write or move anything overlapping it.

`Exp.frozen_of_wf` proves that every term with `e.wf = true` is frozen. The proof follows the
checker, which returns the loans it was given and checks every access against a state that
still holds them. `RArgs.writeBack_idx` draws the consequence for calls: under separation, the
sequential write-backs of the value semantics store to the places as they were passed at the
call, which are the addresses the machine computed.

The design is described in doc/design/memory.md.
-/

namespace Millipede

/-! ## The access discipline -/

/-- Whether loan `l` blocks an access of kind `a` to `path`, which is the test that `BS.access`
makes. -/
def Loan.blocks (l : Loan) (path : List Sel) (a : Acc) : Bool :=
  Sel.overlap l.path path && (l.excl || a != .read)

/-- The access an atom of type `t` makes to its variable, which is a move when `t` is linear and a
read otherwise, as in `Atom.use`. -/
def atomAcc (t : Ty) : Acc := if t.linear then .move else .read

/-- The atom does not access binder `k` in a way that loan `l` blocks. -/
def Atom.Avoids {Γ : List Ty} {t : Ty} (k : Nat) (l : Loan) : Atom Γ t → Prop
  | .var m => m.idx = k → l.blocks [] (atomAcc t) = false
  | .lit _ => True

/-- The argument atoms do not access binder `k` in a way that loan `l` blocks. -/
def Args.Avoids {Γ : List Ty} (k : Nat) (l : Loan) : {ps : List Ty} → Args Γ ps → Prop
  | _, .nil => True
  | _, .cons a as => a.Avoids k l ∧ as.Avoids k l


/-- The index atoms of a place avoid binder `k` under loan `l`. -/
def Place.IdxAvoids {Γ : List Ty} (k : Nat) (l : Loan) : {t : Ty} → Place Γ t → Prop
  | _, .var _ => True
  | _, .field p _ => p.IdxAvoids k l
  | _, .index (dflt := _) p i => p.IdxAvoids k l ∧ i.Avoids k l
  | _, .slot (dflt := _) p i => p.IdxAvoids k l ∧ i.Avoids k l
  | _, .range p lo len => p.IdxAvoids k l ∧ lo.Avoids k l ∧ len.Avoids k l
  | _, .pair2 (dflt := _) p i j => p.IdxAvoids k l ∧ i.Avoids k l ∧ j.Avoids k l
  | _, .rangeS _ lo len => lo.Avoids k l ∧ len.Avoids k l
  | _, .pair2S (dflt := _) _ i j => i.Avoids k l ∧ j.Avoids k l

/-- An access of kind `a` to place `p` is not blocked by loan `l` on binder `k`, neither through
the index atoms nor, when `p` is rooted at `k`, through its path. -/
def Place.Avoids {Γ : List Ty} {t : Ty} (k : Nat) (l : Loan) (p : Place Γ t) (a : Acc) : Prop :=
  p.IdxAvoids k l ∧ (p.root = k → l.blocks p.path a = false)

/-- Extern arguments avoid binder `k` under loan `l`. Their word atoms and the atoms of their
slices count, and a shared slice reads its array place while a mutable slice writes it. -/
def EArgs.Avoids {Γ : List Ty} (k : Nat) (l : Loan) : {ps : List ExtParam} → EArgs Γ ps → Prop
  | _, .nil => True
  | _, .word a as => a.Avoids k l ∧ as.Avoids k l
  | _, .bufIn (.const _) as => as.Avoids k l
  | _, .bufIn (.slice a lo len) as =>
    lo.Avoids k l ∧ len.Avoids k l ∧ a.Avoids k l .read ∧ as.Avoids k l
  | _, .bufOut as => as.Avoids k l
  | _, .sliceOut a lo cap as =>
    lo.Avoids k l ∧ cap.Avoids k l ∧ a.Avoids k l .write ∧ as.Avoids k l

/-- Call arguments avoid binder `k` under loan `l`. An owned argument uses its atom, `&p` reads
`p` and `&mut p` writes it. -/
def RArgs.Avoids {Γ : List Ty} (k : Nat) (l : Loan) : {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own a as => a.Avoids k l ∧ as.Avoids k l
  | _, _, .shr p as => p.Avoids k l .read ∧ as.Avoids k l
  | _, _, .mut p as => p.Avoids k l .write ∧ as.Avoids k l

/-- The writes a loop makes to its carried variables avoid binder `k` under loan `l`. Each one
writes a whole binder. -/
def Carry.Avoids {Γ : List Ty} (k : Nat) (l : Loan) : {ts : List Ty} → Carry Γ ts → Prop
  | _, .nil => True
  | _, .cons m cs => (m.idx = k → l.blocks [] .write = false) ∧ cs.Avoids k l

/-- The places a guard reads avoid binder `k` under loan `l`. -/
def Guard.Avoids {Γ : List Ty} (k : Nat) (l : Loan) : Guard Γ → Prop
  | .valid p _ => p.Avoids k l .read

/-- No access in `e` to binder `k` is blocked by loan `l`. The index `k` is shifted under
binders, and callee bodies are closed terms, so they are not entered. -/
def Exp.Avoids : {Γ : List Ty} → {t : Ty} → Nat → Loan → Exp Γ t → Prop
  | _, _, k, l, .atom a => a.Avoids k l
  | _, _, k, l, .let_ e₁ e₂ => e₁.Avoids k l ∧ e₂.Avoids (k + 1) l
  | _, _, k, l, .ite c e₁ e₂ => c.Avoids k l ∧ e₁.Avoids k l ∧ e₂.Avoids k l
  | _, _, k, l, .prim _ args => args.Avoids k l
  | _, _, k, l, .call _ _ args => args.Avoids k l
  | _, _, k, l, .ok a => a.Avoids k l
  | _, _, k, l, .err a => a.Avoids k l
  | _, _, k, l, .match_ s eE eO => s.Avoids k l ∧ eE.Avoids (k + 1) l ∧ eO.Avoids (k + 1) l
  | _, _, k, l, .ext _ args => args.Avoids k l
  | _, _, k, l, .extMut _ args e => args.Avoids k l ∧ e.Avoids (k + 1) l
  | _, _, k, l, .mk _ args => args.Avoids k l
  | _, _, k, l, .read p => p.Avoids k l .read
  | _, _, k, l, .assign p a e => a.Avoids k l ∧ p.Avoids k l .write ∧ e.Avoids k l
  | _, _, k, l, .case s _ eP eQ => s.Avoids k l ∧ eP.Avoids (k + 1) l ∧ eQ.Avoids (k + 1) l
  | _, _, k, l, .put p i a e => i.Avoids k l ∧ a.Avoids k l ∧ p.Avoids k l .write ∧ e.Avoids k l
  | _, _, k, l, .take (dflt := _) p i e => i.Avoids k l ∧ p.Avoids k l .write ∧ e.Avoids (k + 1) l
  | _, _, k, l, .borrowShr p body e =>
    p.Avoids k l .read ∧ body.Avoids (k + 1) l ∧ e.Avoids (k + 1) l
  | _, _, k, l, .borrowMut p body e =>
    p.Avoids k l .write ∧ body.Avoids (k + 1) l ∧ e.Avoids (k + 1) l
  | _, _, k, l, .callRef _ _ _ args e => args.Avoids k l ∧ e.Avoids (k + 1) l
  | _, _, k, l, .guard g => g.Avoids k l
  | _, _, k, l, .loop _ cs init c body e =>
    init.Avoids k l ∧ cs.Avoids k l ∧ c.Avoids (k + 2) l ∧ body.Avoids (k + 2) l ∧
      e.Avoids (k + 1) l

/-- The reference arguments of a call are separated. After `&mut p`, the later arguments do not
read, write, move or index with anything overlapping `p`, and after `&p` they do not write or
move anything overlapping `p`. -/
def RArgs.Sep {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Prop
  | _, _, .nil => True
  | _, _, .own _ as => as.Sep
  | _, _, .shr p as => as.Avoids p.root ⟨false, p.path⟩ ∧ as.Sep
  | _, _, .mut p as => as.Avoids p.root ⟨true, p.path⟩ ∧ as.Sep

/-- The borrow discipline that the pointer lowering relies on. At every borrow inside `e`,
callee bodies included, the body avoids the borrow's loan on the lender, and at every call with
reference arguments the arguments are separated. -/
def Exp.Frozen : {Γ : List Ty} → {t : Ty} → Exp Γ t → Prop
  | _, _, .atom _ => True
  | _, _, .let_ e₁ e₂ => e₁.Frozen ∧ e₂.Frozen
  | _, _, .ite _ e₁ e₂ => e₁.Frozen ∧ e₂.Frozen
  | _, _, .prim _ _ => True
  | _, _, .call _ body _ => body.Frozen
  | _, _, .ok _ => True
  | _, _, .err _ => True
  | _, _, .match_ _ eE eO => eE.Frozen ∧ eO.Frozen
  | _, _, .ext _ _ => True
  | _, _, .extMut _ _ e => e.Frozen
  | _, _, .mk _ _ => True
  | _, _, .read _ => True
  | _, _, .assign _ _ e => e.Frozen
  | _, _, .case _ _ eP eQ => eP.Frozen ∧ eQ.Frozen
  | _, _, .put _ _ _ e => e.Frozen
  | _, _, .take (dflt := _) _ _ e => e.Frozen
  | _, _, .borrowShr p body e =>
    body.Avoids (p.root + 1) ⟨false, p.path⟩ ∧ body.Frozen ∧ e.Frozen
  | _, _, .borrowMut p body e =>
    body.Avoids (p.root + 1) ⟨true, p.path⟩ ∧ body.Frozen ∧ e.Frozen
  | _, _, .callRef _ _ body args e => args.Sep ∧ body.Frozen ∧ e.Frozen
  | _, _, .guard _ => True
  | _, _, .loop _ _ _ c body e => c.Frozen ∧ body.Frozen ∧ e.Frozen

/-! ## Loans in checker states -/

/-- The loans of every binder of a checker state. -/
abbrev loansOf (st : List BS) : List (List Loan) := st.map BS.loans

/-- Binder `k` of `st` carries loan `l`. -/
def HasLoan (st : List BS) (k : Nat) (l : Loan) : Prop :=
  ∃ ls, (loansOf st)[k]? = some ls ∧ l ∈ ls

theorem HasLoan.of_loans {st st' : List BS} {k : Nat} {l : Loan}
    (e : loansOf st' = loansOf st) (h : HasLoan st k l) : HasLoan st' k l := by
  unfold HasLoan at *; rw [e]; exact h

/-- `HasLoan` depends only on the loans, in a form `grind` can use. -/
theorem HasLoan.congr {st st' : List BS} (e : loansOf st' = loansOf st) (k : Nat) (l : Loan) :
    HasLoan st' k l = HasLoan st k l := by
  simp only [HasLoan, e]

@[simp] theorem hasLoan_cons_succ (b : BS) (st : List BS) (k : Nat) (l : Loan) :
    HasLoan (b :: st) (k + 1) l ↔ HasLoan st k l := by
  simp [HasLoan]

theorem HasLoan.cons {st : List BS} {k : Nat} {l : Loan} (h : HasLoan st k l) (b : BS) :
    HasLoan (b :: st) (k + 1) l :=
  (hasLoan_cons_succ b st k l).2 h

theorem loansOf_length {st st' : List BS} (e : loansOf st' = loansOf st) :
    st'.length = st.length := by
  have := congrArg List.length e; simpa using this

theorem BS.access_loans {b b' : BS} {path : List Sel} {a : Acc} (h : b.access path a = some b') :
    b'.loans = b.loans := by
  unfold BS.access at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem BS.access_blocks {b b' : BS} {path : List Sel} {a : Acc} (h : b.access path a = some b')
    {l : Loan} (hl : l ∈ b.loans) : l.blocks path a = false := by
  unfold BS.access at h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i hany
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
    exact hany l hl

theorem ctxAccess_loans : ∀ {st st' : List BS} {k : Nat} {path : List Sel} {a : Acc},
    ctxAccess st k path a = some st' → loansOf st' = loansOf st
  | [], _, _, _, _, h => by simp [ctxAccess] at h
  | b :: bs, st', 0, path, a, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp [BS.access_loans hb]
  | b :: bs, st', k + 1, path, a, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨bs', hb, rfl⟩ := h
    simp only [loansOf, List.map_cons] at ⊢
    have := ctxAccess_loans hb
    simp only [loansOf] at this
    rw [this]

theorem ctxAccess_lt : ∀ {st st' : List BS} {k : Nat} {path : List Sel} {a : Acc},
    ctxAccess st k path a = some st' → k < st.length
  | [], _, _, _, _, h => by simp [ctxAccess] at h
  | b :: bs, st', 0, path, a, h => by simp
  | b :: bs, st', k + 1, path, a, h => by
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨bs', hb, rfl⟩ := h
    simpa using ctxAccess_lt hb

theorem ctxAccess_blocks : ∀ {st st' : List BS} {k : Nat} {path : List Sel} {a : Acc},
    ctxAccess st k path a = some st' → ∀ {l : Loan}, HasLoan st k l → l.blocks path a = false
  | [], _, _, _, _, h => by simp [ctxAccess] at h
  | b :: bs, st', 0, path, a, h => by
    intro hl
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    obtain ⟨ls, hls, hm⟩ := hl
    simp only [loansOf, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hls
    subst hls
    exact BS.access_blocks hb hm
  | b :: bs, st', k + 1, path, a, h => by
    intro hl
    simp only [ctxAccess, Option.map_eq_some_iff] at h
    obtain ⟨bs', hb, rfl⟩ := h
    exact ctxAccess_blocks hb ((hasLoan_cons_succ _ _ _ _).mp hl)

theorem Atom.use_loans {Γ : List Ty} {t : Ty} {st st' : List BS} (a : Atom Γ t)
    (h : a.use st = some st') : loansOf st' = loansOf st := by
  cases a with
  | var m => exact ctxAccess_loans h
  | lit v => simp only [Atom.use, Option.some.injEq] at h; rw [h]

theorem Atom.use_avoids {Γ : List Ty} {t : Ty} {st st' : List BS} (a : Atom Γ t)
    (h : a.use st = some st') {k : Nat} {l : Loan} (hl : HasLoan st k l) : a.Avoids k l := by
  cases a with
  | var m =>
    intro hk
    subst hk
    have := ctxAccess_blocks h hl
    simpa [atomAcc] using this
  | lit v => trivial

theorem Args.use_loans {Γ : List Ty} :
    {ps : List Ty} → (st st' : List BS) → (as : Args Γ ps) → Args.use st as = some st' →
      loansOf st' = loansOf st
  | _, st, st', .nil, h => by simp only [Args.use, Option.some.injEq] at h; rw [h]
  | _, st, st', .cons a as, h => by
    simp only [Args.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    rw [Args.use_loans _ _ as h₂, a.use_loans h₁]

theorem Args.use_avoids {Γ : List Ty} :
    {ps : List Ty} → (st st' : List BS) → (as : Args Γ ps) → Args.use st as = some st' →
      ∀ {k : Nat} {l : Loan}, HasLoan st k l → as.Avoids k l
  | _, st, st', .nil, _ => fun _ => trivial
  | _, st, st', .cons a as, h => by
    intro hl
    simp only [Args.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ⟨a.use_avoids h₁ hl, Args.use_avoids _ _ as h₂ (hl.of_loans (a.use_loans h₁))⟩

/-- Split a successful `Place.useIdx` step in hypothesis `h`. -/
macro "useIdx_step" " at " h:ident : tactic => `(tactic|
  simp only [Place.useIdx, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
    at $h:ident)

theorem Place.useIdx_loans {Γ : List Ty} {t : Ty} (p : Place Γ t) :
    ∀ {st st' : List BS}, p.useIdx st = some st' → loansOf st' = loansOf st := by
  induction p <;> intro st st' h <;> useIdx_step at h
  all_goals first
    | grind [Atom.use_loans]
    | (obtain ⟨_, h1, h2⟩ := h; rw [Atom.use_loans _ h2, Atom.use_loans _ h1])

theorem Place.useIdx_avoids {Γ : List Ty} {t : Ty} (p : Place Γ t) :
    ∀ {st st' : List BS}, p.useIdx st = some st' →
      ∀ {k : Nat} {l : Loan}, HasLoan st k l → p.IdxAvoids k l := by
  induction p <;> intro st st' h k l hl <;> useIdx_step at h
  all_goals grind [Place.IdxAvoids, Atom.use_avoids, HasLoan.of_loans, → Atom.use_loans,
    → Place.useIdx_loans]

theorem Place.access_loans {Γ : List Ty} {t : Ty} (p : Place Γ t) {st st' : List BS} {a : Acc}
    (h : p.access st a = some st') : loansOf st' = loansOf st := by
  simp only [Place.access, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  rw [ctxAccess_loans h₂, p.useIdx_loans h₁]

theorem Place.access_avoids {Γ : List Ty} {t : Ty} (p : Place Γ t) {st st' : List BS} {a : Acc}
    (h : p.access st a = some st') {k : Nat} {l : Loan} (hl : HasLoan st k l) :
    p.Avoids k l a := by
  simp only [Place.access, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  refine ⟨p.useIdx_avoids h₁ hl, fun hk => ?_⟩
  subst hk
  exact ctxAccess_blocks h₂ (hl.of_loans (p.useIdx_loans h₁))

theorem Place.access_lt {Γ : List Ty} {t : Ty} (p : Place Γ t) {st st' : List BS} {a : Acc}
    (h : p.access st a = some st') : p.root < st.length := by
  simp only [Place.access, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  have := ctxAccess_lt h₂
  rwa [loansOf_length (p.useIdx_loans h₁)] at this

/-! ### Adding, entering and leaving -/

theorem EArgs.use_loans {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps) :
    ∀ (st st' : List BS), EArgs.use st as = some st' → loansOf st' = loansOf st := by
  induction as with
  | bufIn b as ih => cases b <;> intro st st' h <;> simp only [EArgs.use, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h <;>
      grind [Atom.use_loans, Place.access_loans]
  | _ => intro st st' h; simp only [EArgs.use, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h; grind [Atom.use_loans, Place.access_loans]

theorem EArgs.use_avoids {Γ : List Ty} {ps : List ExtParam} (as : EArgs Γ ps) :
    ∀ (st st' : List BS), EArgs.use st as = some st' →
      ∀ {k : Nat} {l : Loan}, HasLoan st k l → as.Avoids k l := by
  induction as with
  | bufIn b as ih => cases b <;> intro st st' h k l hl <;> simp only [EArgs.use,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
      grind [EArgs.Avoids, Atom.use_avoids, Place.access_avoids, HasLoan.of_loans,
        → Atom.use_loans, → Place.access_loans]
  | _ => intro st st' h k l hl; simp only [EArgs.use, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h; grind [EArgs.Avoids, Atom.use_avoids, Place.access_avoids,
        HasLoan.of_loans, → Atom.use_loans, → Place.access_loans]

theorem addLoan_length : ∀ (st : List BS) (k : Nat) (l : Loan), (addLoan st k l).length = st.length
  | [], _, _ => rfl
  | b :: bs, 0, l => by simp [addLoan]
  | b :: bs, k + 1, l => by simp [addLoan, addLoan_length bs k l]

/-- Adding a loan keeps the loans already there. -/
theorem HasLoan.addLoan : ∀ {st : List BS} {k : Nat} {l : Loan} (j : Nat) (l' : Loan),
    HasLoan st k l → HasLoan (Millipede.addLoan st j l') k l
  | [], _, _, _, _, h => by obtain ⟨ls, hls, _⟩ := h; simp at hls
  | b :: bs, 0, l, 0, l', h => by
    obtain ⟨ls, hls, hm⟩ := h
    simp only [loansOf, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hls
    subst hls
    exact ⟨l' :: b.loans, by simp [Millipede.addLoan], List.mem_cons_of_mem _ hm⟩
  | b :: bs, k + 1, l, 0, l', h => by
    simp only [Millipede.addLoan, hasLoan_cons_succ] at h ⊢; exact h
  | b :: bs, 0, l, j + 1, l', h => by
    obtain ⟨ls, hls, hm⟩ := h
    exact ⟨ls, by simpa [Millipede.addLoan] using hls, hm⟩
  | b :: bs, k + 1, l, j + 1, l', h => by
    simp only [Millipede.addLoan, hasLoan_cons_succ] at h ⊢; exact HasLoan.addLoan j l' h

/-- The loan just added. -/
theorem hasLoan_addLoan : ∀ {st : List BS} {k : Nat} (l : Loan), k < st.length →
    HasLoan (addLoan st k l) k l
  | [], _, _, h => by simp at h
  | b :: bs, 0, l, _ => ⟨l :: b.loans, by simp [addLoan], List.mem_cons_self⟩
  | b :: bs, k + 1, l, h => by
    simp only [addLoan, hasLoan_cons_succ]
    exact hasLoan_addLoan l (by simpa using h)

@[simp] theorem loansOf_enterBlock (st : List BS) : loansOf (enterBlock st) = loansOf st := by
  simp [enterBlock]

@[simp] theorem hasLoan_enterBlock (st : List BS) (k : Nat) (l : Loan) :
    HasLoan (enterBlock st) k l ↔ HasLoan st k l := by
  simp [HasLoan]

@[simp] theorem loansOf_carryIn (xs : List Nat) :
    ∀ (k : Nat) (st : List BS), loansOf (carryIn xs k st) = loansOf st
  | _, [] => rfl
  | k, b :: bs => by simp [carryIn, loansOf_carryIn xs (k + 1) bs]

@[simp] theorem loansOf_carryOut (xs : List Nat) :
    ∀ (k : Nat) (st : List BS), loansOf (carryOut xs k st) = loansOf st
  | _, [] => rfl
  | k, b :: bs => by simp [carryOut, loansOf_carryOut xs (k + 1) bs]

@[simp] theorem hasLoan_carryIn (xs : List Nat) (j : Nat) (st : List BS) (k : Nat) (l : Loan) :
    HasLoan (carryIn xs j st) k l ↔ HasLoan st k l := by
  simp only [HasLoan, loansOf_carryIn]

theorem Carry.use_loans {Γ : List Ty} :
    ∀ {ts : List Ty} {st st' : List BS} (cs : Carry Γ ts), cs.use st = some st' →
      loansOf st' = loansOf st
  | _, _, _, .nil, h => by simp only [Carry.use, Option.some.injEq] at h; rw [h]
  | _, _, _, .cons m cs, h => by
    simp only [Carry.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    rw [Carry.use_loans cs h₂, ctxAccess_loans h₁]

theorem Carry.use_avoids {Γ : List Ty} :
    ∀ {ts : List Ty} {st st' : List BS} (cs : Carry Γ ts), cs.use st = some st' →
      ∀ {k : Nat} {l : Loan}, HasLoan st k l → cs.Avoids k l
  | _, _, _, .nil, _, _, _, _ => trivial
  | _, _, _, .cons m cs, h, k, l, hl => by
    simp only [Carry.use, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ⟨fun hk => by subst hk; exact ctxAccess_blocks h₁ hl,
      Carry.use_avoids cs h₂ (hl.of_loans (ctxAccess_loans h₁))⟩

theorem loansOf_exitBlock : ∀ (o a : List BS), a.length = o.length →
    loansOf (exitBlock o a) = loansOf o
  | [], [], _ => rfl
  | o :: os, a :: as, h => by
    simp only [exitBlock, loansOf, List.map_cons] at *
    have := loansOf_exitBlock os as (by simpa using h)
    simp only [loansOf] at this
    rw [this]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem loansOf_popDone {s s' : List BS} (h : popDone s = some s') :
    ∃ b, s = b :: s' := by
  cases s with
  | nil => simp [popDone] at h
  | cons b bs =>
    simp only [popDone] at h
    split at h
    · cases h; exact ⟨b, rfl⟩
    · cases h

theorem loansOf_popDone' {s s' : List BS} (h : popDone s = some s') :
    loansOf s' = (loansOf s).tail := by
  obtain ⟨b, rfl⟩ := loansOf_popDone h; rfl

theorem RArgs.use_length {Γ : List Ty} {ps os : List Ty} (st st' : List BS) (as : RArgs Γ ps os)
    (h : RArgs.use st as = some st') : st'.length = st.length := by
  induction as generalizing st st' <;> simp only [RArgs.use, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [loansOf_length, Atom.use_loans, Place.access_loans, addLoan_length]

/-- The loan a borrow adds after accessing its place. -/
theorem Place.hasLoan_access {Γ : List Ty} {t : Ty} (p : Place Γ t) {st s : List BS} {a : Acc}
    (h : p.access st a = some s) (l : Loan) : HasLoan (addLoan s p.root l) p.root l :=
  hasLoan_addLoan _ (by rw [loansOf_length (p.access_loans h)]; exact p.access_lt h)

theorem RArgs.use_avoids {Γ : List Ty} {ps os : List Ty} (st st' : List BS) (as : RArgs Γ ps os)
    (h : RArgs.use st as = some st') {k : Nat} {l : Loan} (hl : HasLoan st k l) : as.Avoids k l := by
  induction as generalizing st st' <;> simp only [RArgs.use, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.Avoids, Atom.use_avoids, Place.access_avoids, HasLoan.of_loans, HasLoan.addLoan,
      → Atom.use_loans, → Place.access_loans]

/-- Reference arguments that the checker accepts are separated. -/
theorem RArgs.use_sep {Γ : List Ty} {ps os : List Ty} (st st' : List BS) (as : RArgs Γ ps os)
    (h : RArgs.use st as = some st') : as.Sep := by
  induction as generalizing st st' <;> simp only [RArgs.use, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.Sep, RArgs.use_avoids, Place.hasLoan_access]

theorem Guard.use_loans {Γ : List Ty} {st st' : List BS} (g : Guard Γ)
    (h : g.use st = some st') : loansOf st' = loansOf st := by
  cases g with
  | valid p _ => exact p.access_loans h

theorem Guard.use_avoids {Γ : List Ty} {st st' : List BS} (g : Guard Γ)
    (h : g.use st = some st') {k : Nat} {l : Loan} (hl : HasLoan st k l) : g.Avoids k l := by
  cases g with
  | valid p _ => exact p.access_avoids h hl

/-! ## The checker keeps the loans it is given -/

/-- Split a successful `Exp.check` step in hypothesis `h` into its successful sub-checks. -/
macro "check_step" " at " h:ident : tactic => `(tactic|
  simp only [Exp.check, Option.bind_eq_bind, Option.bind_none, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some, Option.bind_eq_some_iff, Option.some.injEq] at $h:ident)

/-- The checker returns the loans it was given on every binder, so in particular the state keeps
its length. -/
theorem Exp.check_loans {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {st st' : List BS}, e.check st = some st' → loansOf st' = loansOf st := by
  induction e <;> intro st st' h <;> check_step at h
  all_goals grind [Atom.use_loans, Args.use_loans, EArgs.use_loans, Guard.use_loans,
    Carry.use_loans, Place.access_loans, loansOf_popDone', loansOf_exitBlock, loansOf_length, loansOf_enterBlock,
    addLoan_length, RArgs.use_length]

/-! ## Every access is checked against a state that still has the loan -/

section
-- These patterns let `grind` follow `HasLoan` facts through the checker states.
local grind_pattern HasLoan.congr => loansOf st', HasLoan st k l
local grind_pattern HasLoan.cons => b :: st, HasLoan st k l

/-- A loan present when the checker starts on `e` blocks no access in `e`, because every access
is checked against a state that still holds the loan. -/
theorem Exp.check_avoids {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {st st' : List BS}, e.check st = some st' →
      ∀ {k : Nat} {l : Loan}, HasLoan st k l → e.Avoids k l := by
  induction e <;> intro st st' h k l hl <;> check_step at h
  case loop init _ _ _ ihc ihb ihk =>
    obtain ⟨-, s₀, h₀, s₁, h₁, sc, hc, sb, hb, -, sk, hk, hp⟩ := h
    have e₀ := init.use_loans h₀
    have e₁ := Carry.use_loans _ h₁
    have hl₁ : HasLoan s₁ k l := (hl.of_loans e₀).of_loans e₁
    exact ⟨init.use_avoids h₀ hl, Carry.use_avoids _ h₁ (hl.of_loans e₀),
      ihc hc (((hasLoan_enterBlock _ _ _).2 hl₁).cons _ |>.cons _),
      ihb hb (((hasLoan_carryIn _ _ _ _ _).2 hl₁).cons _ |>.cons _), ihk hk (hl₁.cons _)⟩
  all_goals grind [Exp.Avoids, Atom.use_avoids, Args.use_avoids, EArgs.use_avoids,
    Guard.use_avoids, Place.access_avoids, RArgs.use_avoids, HasLoan.addLoan, hasLoan_cons_succ,
    hasLoan_enterBlock, hasLoan_carryIn, Carry.use_avoids, → Carry.use_loans,
    → Exp.check_loans, → Atom.use_loans, → Args.use_loans, → EArgs.use_loans,
    → Guard.use_loans, → Place.access_loans, → loansOf_popDone', loansOf_exitBlock,
    loansOf_length, loansOf_enterBlock, addLoan_length, RArgs.use_length]

end

/-! ## The checker establishes the discipline -/

theorem checkBody_some' {check : List BS → Option (List BS)} {bs : List BS}
    (h : checkBody check bs = true) : ∃ st, check bs = some st := by
  unfold checkBody at h
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

/-- Every term that the checker accepts is frozen. At each `&mut` borrow the body touches the lent
place only through the binder, at each `&` borrow nothing overlapping is written, and the
reference arguments of each call are separated. -/
theorem Exp.frozen_of_check {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {st st' : List BS}, e.check st = some st' → e.Frozen := by
  induction e <;> intro st st' h <;> check_step at h
  all_goals grind [Exp.Frozen, checkBody_some', RArgs.use_sep, Exp.check_avoids,
    hasLoan_cons_succ, hasLoan_enterBlock, Place.hasLoan_access]

/-- A well-formed term keeps the borrow discipline that the pointer lowering relies on. -/
theorem Exp.frozen_of_wf {Γ : List Ty} {t : Ty} (e : Exp Γ t) (h : e.wf = true) : e.Frozen := by
  unfold Exp.wf at h
  cases hc : e.check (initCtx Γ) with
  | none => rw [hc] at h; cases h
  | some st' => exact e.frozen_of_check hc


/-! ## Write-back addresses are fixed at the call -/

theorem Sel.overlap_nil_right (π : List Sel) : Sel.overlap π [] = true := by
  cases π <;> rfl

theorem Env.get_set_ne {t s : Ty} {Γ : List Ty} (env : Env Γ) (m : Mem t Γ) (m' : Mem s Γ)
    (v : t.carrier) (h : m'.idx ≠ m.idx) : (env.set m v).get m' = env.get m' := by
  induction env with
  | nil => cases m
  | cons x env ih =>
    cases m with
    | here =>
      cases m' with
      | here => exact absurd rfl h
      | there m' => rfl
    | there m =>
      cases m' with
      | here => rfl
      | there m' => exact ih m m' (fun e => h (by simp [Mem.idx, e]))

/-- Writing a place changes only its root variable. -/
theorem Place.get_set_ne {Γ : List Ty} {t s : Ty} (p : Place Γ t) (env : Env Γ) (v : t.carrier)
    (m : Mem s Γ) (h : m.idx ≠ p.root) : (p.set env v).get m = env.get m := by
  induction p with
  | var m' => exact Env.get_set_ne env m' m v h
  | field p l ih => exact ih _ h
  | index p i ih => exact ih _ h
  | slot p i ih => exact ih _ h
  | range p lo len ih => exact ih _ h
  | pair2 p i j ih => exact ih _ h
  | rangeS m' => exact Env.get_set_ne env m' m _ h
  | pair2S m' => exact Env.get_set_ne env m' m _ h

/-- Two environments agree on every variable except binder `k`. -/
def EqExcept {Γ : List Ty} (k : Nat) (env env' : Env Γ) : Prop :=
  ∀ {s : Ty} (m : Mem s Γ), m.idx ≠ k → env.get m = env'.get m

/-- Reads a place with its index atoms evaluated in `envI` and its root's value taken from `env`,
so that `Place.getAt env p env = p.get env`. -/
def Place.getAt {Γ : List Ty} (envI : Env Γ) : {t : Ty} → Place Γ t → Env Γ → t.carrier
  | _, .var m, env => env.get m
  | _, .field p l, env => l.get (p.getAt envI env)
  | _, .index (dflt := _) p i, env => vget (p.getAt envI env) (i.denote envI).toNat default
  | _, .slot (dflt := _) p i, env =>
    ((p.getAt envI env : Slots _ _).cell (i.denote envI).toNat).getD default
  | _, .range p lo len, env =>
    vview (p.getAt envI env) (lo.denote envI).toNat (len.denote envI).toNat
  | _, .pair2 (dflt := _) p i j, env =>
    (vget (p.getAt envI env) (i.denote envI).toNat default,
      vget (p.getAt envI env) (j.denote envI).toNat default)
  | _, .rangeS m lo len, env => sview (env.get m) (lo.denote envI).toNat (len.denote envI).toNat
  | _, .pair2S (dflt := _) m i j, env =>
    (((env.get m : Slots _ _).cell (i.denote envI).toNat).getD default,
      ((env.get m : Slots _ _).cell (j.denote envI).toNat).getD default)

/-- Writes a place with its index atoms evaluated in `envI`, so that
`Place.setAt env p env = p.set env`. -/
def Place.setAt {Γ : List Ty} (envI : Env Γ) : {t : Ty} → Place Γ t → Env Γ → t.carrier → Env Γ
  | _, .var m, env, v => env.set m v
  | _, .field p l, env, v => p.setAt envI env (l.set (p.getAt envI env) v)
  | _, .index (dflt := _) p i, env, v =>
    p.setAt envI env (vset (p.getAt envI env) (i.denote envI).toNat v)
  | _, .slot (dflt := _) p i, env, v =>
    p.setAt envI env (Slots.setCell (p.getAt envI env) (i.denote envI).toNat (some v))
  | _, .range p lo len, env, v =>
    p.setAt envI env (vunview (p.getAt envI env) (lo.denote envI).toNat (len.denote envI).toNat v)
  | _, .pair2 (dflt := _) p i j, env, v =>
    p.setAt envI env
      (vset (vset (p.getAt envI env) (i.denote envI).toNat v.1) (j.denote envI).toNat v.2)
  | _, .rangeS m lo len, env, v =>
    env.set m (sunview (env.get m) (lo.denote envI).toNat (len.denote envI).toNat v)
  | _, .pair2S (dflt := _) m i j, env, v =>
    env.set m (((env.get m : Slots _ _).setCell (i.denote envI).toNat (some v.1)).setCell
      (j.denote envI).toNat (some v.2))

theorem Place.getAt_self {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) :
    p.getAt env env = p.get env := by
  induction p with
  | var => rfl
  | field p l ih => simp [Place.getAt, Place.get, ih]
  | index p i ih => simp [Place.getAt, Place.get, ih]
  | slot p i ih => simp [Place.getAt, Place.get, ih]
  | range p lo len ih => simp [Place.getAt, Place.get, ih]
  | pair2 p i j ih => simp [Place.getAt, Place.get, ih]
  | rangeS => rfl
  | pair2S => rfl

theorem Place.setAt_self {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) (v : t.carrier) :
    p.setAt env env v = p.set env v := by
  induction p with
  | var => rfl
  | field p l ih => simp [Place.setAt, Place.set, ih, Place.getAt_self]
  | index p i ih => simp [Place.setAt, Place.set, ih, Place.getAt_self]
  | slot p i ih => simp [Place.setAt, Place.set, ih, Place.getAt_self]
  | range p lo len ih => simp [Place.setAt, Place.set, ih, Place.getAt_self]
  | pair2 p i j ih => simp [Place.setAt, Place.set, ih, Place.getAt_self]
  | rangeS => rfl
  | pair2S => rfl

theorem Atom.denote_eqExcept {Γ : List Ty} {t : Ty} {k : Nat} {π : List Sel} (a : Atom Γ t)
    (ha : a.Avoids k ⟨true, π⟩) {env env' : Env Γ} (he : EqExcept k env env') :
    a.denote env = a.denote env' := by
  cases a with
  | var m =>
    refine he m fun hk => ?_
    have := ha hk
    simp [Loan.blocks, Sel.overlap_nil_right] at this
  | lit => rfl

/-- The index environment matters only through the index atoms. -/
theorem Place.getAt_setAt_congr {Γ : List Ty} {t : Ty} {k : Nat} {π : List Sel} (p : Place Γ t)
    (hp : p.IdxAvoids k ⟨true, π⟩) {envI envI' : Env Γ} (he : EqExcept k envI envI') :
    (∀ env, p.getAt envI env = p.getAt envI' env) ∧
      (∀ env v, p.setAt envI env v = p.setAt envI' env v) := by
  induction p <;> simp only [Place.IdxAvoids] at hp
  all_goals grind [Place.getAt, Place.setAt, Atom.denote_eqExcept]

/-- The write-backs of a call with every argument place's index atoms evaluated in `envI`, the
environment at the call. This is what the machine does when it stores through the addresses it
computed when it passed the arguments. -/
def RArgs.writeBackAt {Γ : List Ty} (envI : Env Γ) :
    {ps os : List Ty} → RArgs Γ ps os → Env Γ → (Ty.tup os).carrier → Env Γ
  | _, _, .nil, env, _ => env
  | _, _, .own _ as, env, vs => as.writeBackAt envI env vs
  | _, _, .shr _ as, env, vs => as.writeBackAt envI env vs
  | _, _, .mut p as, env, vs => as.writeBackAt envI (p.setAt envI env vs.1) vs.2

theorem RArgs.writeBackAt_congr {Γ : List Ty} {k : Nat} {π : List Sel} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → as.Avoids k ⟨true, π⟩ →
      ∀ {envI envI' : Env Γ}, EqExcept k envI envI' →
      ∀ env vs, as.writeBackAt envI env vs = as.writeBackAt envI' env vs
  | _, _, .nil, _, _, _, _, _, _ => rfl
  | _, _, .own _ as, h, _, _, he, env, vs => as.writeBackAt_congr h.2 he env vs
  | _, _, .shr _ as, h, _, _, he, env, vs => as.writeBackAt_congr h.2 he env vs
  | _, _, .mut p as, h, envI, envI', he, env, vs => by
    simp only [RArgs.writeBackAt]
    rw [((p.getAt_setAt_congr h.1.1 he).2 env vs.1)]
    exact as.writeBackAt_congr h.2 he _ _

/-- Under the separation that the checker guarantees, the sequential write-backs of a call store
through the argument places as they were passed. Each argument place's index atoms evaluate, at
the moment of its write-back, to their values at the call, so the write-backs go to the
addresses that the machine computed once at the call. -/
theorem RArgs.writeBack_idx {Γ : List Ty} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → as.Sep →
      ∀ (env : Env Γ) (vs : (Ty.tup os).carrier), as.writeBack env vs = as.writeBackAt env env vs
  | _, _, .nil, _, _, _ => rfl
  | _, _, .own _ as, h, env, vs => RArgs.writeBack_idx as h env vs
  | _, _, .shr _ as, h, env, vs => RArgs.writeBack_idx as h.2 env vs
  | _, _, .mut p as, h, env, vs => by
    simp only [RArgs.writeBack, RArgs.writeBackAt]
    rw [RArgs.writeBack_idx as h.2, Place.setAt_self]
    refine as.writeBackAt_congr h.1 (k := p.root) (fun m hm => ?_) _ _
    exact Place.get_set_ne p env vs.1 m hm

end Millipede
