import Millipede.Core.Exp

/-!
# The checker

`Exp.check e st` runs over a term in evaluation order with an abstract state `st`, which holds one
`BS` per binder of the context, index 0 first. A binder's state records its mode, whether its
type is linear, whether it has been moved, whether it may be written in the current block, and
the loans currently taken of places rooted at it. The checker returns the state after `e`, or
`none` when a rule is violated. `Exp.wf e` is a `Bool`, so a closed term is checked by `decide`.

The linearity rules are the following. An atom of linear type moves its variable, after which the
variable cannot be used again, and an atom of any other type copies it. An owned or `mut` binder
of linear type must be moved exactly once on every path before it goes out of scope, so an unused
`let` of a `Result` is rejected. Both arms of an `if`, `match` or `case` end in the same state. A
loop's condition changes nothing, and its body moves no binder from outside the loop.

A place is a root binder and a path of selectors, each a field number or `dyn`, which stands for
any element, `Slots` cell or slice. Two paths overlap when one extends the other, with fields
compared by number and any two elements treated as possibly equal. While `&mut p` is live, which
is during the body of a borrow or a call that takes `&mut p`, no place overlapping `p` is used.
While `&p` is live, overlapping places may be read but not written, moved or mutably borrowed. A
shared reference binder is never written or moved. Only non-linear values are copied out of a
place or overwritten in one, while `take` and `put` move values out of and into `Slots` cells.

Borrowing a slice, passing it by reference, or borrowing a view binder whole makes a view binder,
which at the machine is a pointer and a length. Its elements are reached as cells `r[i]!`. A view
place is never assigned whole or the target of `put` or `take`, since those could fill a cell
past the length, where there is no storage. Reading a view, or handing it back from a borrow,
copies its first `len` cells into a `Slots` value.

Assignment changes a place for its continuation, so writes are allowed only to binders of the
current block. Inside a `let`'s bound term, a borrow body, or a loop's condition or body, the
binders from outside are read-only, although moving them still counts, and with this rule the
continuation semantics is the imperative one. A loop with carried variables is the exception. It
makes a write access to each carried binder, which must be writable, not a shared reference, not
moved and not lent, and its body may write exactly those binders and must hand back the linear
ones.

`Exp.wf e` checks `e` with the binders of its context owned and unconstrained at the end.
`Fn.wf` also requires the function's linear parameters to be consumed.
-/

namespace Millipede

/-- A selector in a place path. -/
inductive Sel where
  /-- the struct field with this number, `Lens.index` -/
  | field (k : Nat)
  /-- some element, which is an array index, a `Slots` cell or a slice -/
  | dyn
deriving DecidableEq, Repr

/-- Whether two paths from the same root may denote overlapping storage. -/
def Sel.overlap : List Sel → List Sel → Bool
  | [], _ => true
  | _, [] => true
  | .field a :: p, .field b :: q => a == b && Sel.overlap p q
  | _ :: p, _ :: q => Sel.overlap p q

/-- A live borrow of the place at `path`, which is a `&mut` borrow when `excl` holds. -/
structure Loan where
  excl : Bool
  path : List Sel
deriving DecidableEq, Repr

/-- The checker's state of one binder. -/
structure BS where
  mode : Mode
  lin : Bool
  moved : Bool
  /-- may be written, by assignment or a mutable borrow, in the current block -/
  wr : Bool
  loans : List Loan
  /-- a slice view binder, which is a pointer and a length at the machine -/
  view : Bool := false
deriving DecidableEq, Repr

/-- A fresh binder. A `shr` binder is never writable. -/
def BS.fresh (m : Mode) (lin : Bool) : BS :=
  { mode := m, lin := lin, moved := false, wr := m != .shr, loans := [] }

/-- A binder may go out of scope when it is a reference, not linear, or already moved. -/
def BS.done (b : BS) : Bool := b.mode == .shr || !b.lin || b.moved

/-- The kinds of access to a place. -/
inductive Acc where
  | read
  | write
  | move
deriving DecidableEq, Repr

/-- Accesses `path` under binder `b`. -/
def BS.access (b : BS) (path : List Sel) (a : Acc) : Option BS :=
  if b.moved then none
  else if b.loans.any (fun l => Sel.overlap l.path path && (l.excl || a != .read)) then none
  else match a with
    | .read => some b
    | .write => if b.wr && b.mode != .shr then some b else none
    | .move => if b.mode != .shr && path.isEmpty then some { b with moved := true } else none

/-- Accesses `path` under binder number `k`. -/
def ctxAccess : List BS → Nat → List Sel → Acc → Option (List BS)
  | [], _, _, _ => none
  | b :: bs, 0, p, a => (b.access p a).map (· :: bs)
  | b :: bs, k + 1, p, a => (ctxAccess bs k p a).map (b :: ·)

/-- Adds a loan to binder number `k`. -/
def addLoan : List BS → Nat → Loan → List BS
  | [], _, _ => []
  | b :: bs, 0, l => { b with loans := l :: b.loans } :: bs
  | b :: bs, k + 1, l => b :: addLoan bs k l

/-- Makes every binder read-only, on entering a block. -/
def enterBlock (st : List BS) : List BS := st.map fun b => { b with wr := false }

/-- The state after leaving a block or a call, which is `orig` except for which binders were
moved. -/
def exitBlock : List BS → List BS → List BS
  | o :: os, a :: as => { o with moved := a.moved } :: exitBlock os as
  | _, _ => []

/-- Pops a binder going out of scope, which must be `done`. -/
def popDone : List BS → Option (List BS)
  | b :: bs => if b.done then some bs else none
  | [] => none

/-- The initial state of a context, in which every binder is owned. -/
def initCtx (Γ : List Ty) : List BS := Γ.map fun t => BS.fresh .own t.linear

/-- Whether binder number `k` is a slice view binder. -/
def isView (st : List BS) (k : Nat) : Bool := (st[k]?).any (·.view)

/-- Uses an atom, which moves a linear variable and copies any other. -/
def Atom.use {Γ : List Ty} {t : Ty} (st : List BS) : Atom Γ t → Option (List BS)
  | .var m => ctxAccess st m.idx [] (if t.linear then .move else .read)
  | .lit _ => some st

/-- Uses argument atoms, left to right. -/
def Args.use {Γ : List Ty} : {ps : List Ty} → List BS → Args Γ ps → Option (List BS)
  | _, st, .nil => some st
  | _, st, .cons a as => do let st ← a.use st; Args.use st as


namespace Place
variable {Γ : List Ty}

/-- The root binder of a place. -/
def root : {t : Ty} → Place Γ t → Nat
  | _, .var m => m.idx
  | _, .field p _ => p.root
  | _, .index (dflt := _) p _ => p.root
  | _, .slot (dflt := _) p _ => p.root
  | _, .range p _ _ => p.root
  | _, .pair2 (dflt := _) p _ _ => p.root
  | _, .rangeS m _ _ => m.idx
  | _, .pair2S (dflt := _) m _ _ => m.idx

/-- The selectors from the root, outermost first. -/
def path : {t : Ty} → Place Γ t → List Sel
  | _, .var _ => []
  | _, .field p l => p.path ++ [.field l.index]
  | _, .index (dflt := _) p _ => p.path ++ [.dyn]
  | _, .slot (dflt := _) p _ => p.path ++ [.dyn]
  | _, .range p _ _ => p.path ++ [.dyn]
  | _, .pair2 (dflt := _) p _ _ => p.path ++ [.dyn]
  | _, .rangeS _ _ _ => [.dyn]
  | _, .pair2S (dflt := _) _ _ _ => [.dyn]

/-- Reads the index atoms of a place. -/
def useIdx : {t : Ty} → List BS → Place Γ t → Option (List BS)
  | _, st, .var _ => some st
  | _, st, .field p _ => p.useIdx st
  | _, st, .index (dflt := _) p i => do let st ← p.useIdx st; i.use st
  | _, st, .slot (dflt := _) p i => do let st ← p.useIdx st; i.use st
  | _, st, .range p lo len => do let st ← p.useIdx st; let st ← lo.use st; len.use st
  | _, st, .pair2 (dflt := _) p i j => do let st ← p.useIdx st; let st ← i.use st; j.use st
  | _, st, .rangeS _ lo len => do let st ← lo.use st; len.use st
  | _, st, .pair2S (dflt := _) _ i j => do let st ← i.use st; j.use st

/-- A view place, which is a slice or a view binder itself. Borrowing one or passing it by
reference makes a view binder, and it is never assigned whole, `put` into or `take`n from. -/
def wholeView : {t : Ty} → List BS → Place Γ t → Bool
  | _, st, .var m => isView st m.idx
  | _, _, .range _ _ _ => true
  | _, _, .rangeS _ _ _ => true
  | _, _, _ => false

/-- Accesses a place by reading its index atoms and then accessing its root along its path. -/
def access {t : Ty} (st : List BS) (p : Place Γ t) (a : Acc) : Option (List BS) := do
  let st ← p.useIdx st
  ctxAccess st p.root p.path a

end Place

/-- Uses extern argument atoms and places, where a shared slice reads its array place and a
mutable slice writes it. The extern reads its input buffers before it writes its output buffers,
so a call may take overlapping slices and needs no loan. -/
def EArgs.use {Γ : List Ty} : {ps : List ExtParam} → List BS → EArgs Γ ps → Option (List BS)
  | _, st, .nil => some st
  | _, st, .word a as => do let st ← a.use st; EArgs.use st as
  | _, st, .bufIn (.const _) as => EArgs.use st as
  | _, st, .bufIn (.slice a lo len) as => do
    let st ← lo.use st; let st ← len.use st; let st ← a.access st .read; EArgs.use st as
  | _, st, .bufOut as => EArgs.use st as
  | _, st, .sliceOut a lo cap as => do
    let st ← lo.use st; let st ← cap.use st; let st ← a.access st .write; EArgs.use st as

/-- The accesses of call arguments, left to right. Each `&` or `&mut` argument stays borrowed for
the rest of the call, so overlapping arguments are rejected. -/
def RArgs.use {Γ : List Ty} : {ps os : List Ty} → List BS → RArgs Γ ps os → Option (List BS)
  | _, _, st, .nil => some st
  | _, _, st, .own a as => do let st ← a.use st; RArgs.use st as
  | _, _, st, .shr p as => do
    let st ← p.access st .read
    RArgs.use (addLoan st p.root ⟨false, p.path⟩) as
  | _, _, st, .mut p as => do
    let st ← p.access st .write
    RArgs.use (addLoan st p.root ⟨true, p.path⟩) as

/-- The callee's binders for the argument modes. An argument that is a view place in the caller's
state `st` makes a view binder. -/
def RArgs.binders {Γ : List Ty} (st : List BS) : {ps os : List Ty} → RArgs Γ ps os → List BS
  | _, _, .nil => []
  | _, _, .own (t := t) _ as => BS.fresh .own t.linear :: as.binders st
  | _, _, .shr (t := t) p as =>
    { BS.fresh .shr t.linear with view := p.wholeView st } :: as.binders st
  | _, _, .mut (t := t) p as =>
    { BS.fresh .mut t.linear with view := p.wholeView st } :: as.binders st

/-- A loop writes each of its carried variables. This is a write access to the whole binder, so
each must be writable in the current block, not a shared reference, not moved and not lent. -/
def Carry.use {Γ : List Ty} : {ts : List Ty} → List BS → Carry Γ ts → Option (List BS)
  | _, st, .nil => some st
  | _, st, .cons m cs => do let st ← ctxAccess st m.idx [] .write; Carry.use st cs

/-- The binders, numbered from `k`, inside a loop body that carries the variables `xs`. They are
read-only except for the carried ones. -/
def carryIn (xs : List Nat) : Nat → List BS → List BS
  | _, [] => []
  | k, b :: bs => { b with wr := b.wr && xs.contains k } :: carryIn xs (k + 1) bs

/-- What a loop body must leave of the binders that `carryIn` gives it. Nothing is moved except
the linear carried variables, which the body hands back. -/
def carryOut (xs : List Nat) : Nat → List BS → List BS
  | _, [] => []
  | k, b :: bs =>
    { b with wr := b.wr && xs.contains k, moved := b.moved || (xs.contains k && b.lin) } ::
      carryOut xs (k + 1) bs

/-- Reads the places of a guard. -/
def Guard.use {Γ : List Ty} (st : List BS) : Guard Γ → Option (List BS)
  | .valid p _ => p.access st .read

/-- A function body leaves every parameter `done`. -/
def checkBody (check : List BS → Option (List BS)) (bs : List BS) : Bool :=
  match check bs with
  | some st => st.all BS.done
  | none => false

/-- The checker, which returns the state after `e`, or `none` on a violation. -/
def Exp.check : {Γ : List Ty} → {t : Ty} → Exp Γ t → List BS → Option (List BS)
  | _, _, .atom a, st => a.use st
  | _, _, @Exp.let_ _ s _ e₁ e₂, st => do
    let s₁ ← e₁.check (enterBlock st)
    let s₂ ← e₂.check (BS.fresh .own s.linear :: exitBlock st s₁)
    popDone s₂
  | _, _, .ite c e₁ e₂, st => do
    let st ← c.use st
    let s₁ ← e₁.check st
    let s₂ ← e₂.check st
    if s₁ == s₂ then some s₁ else none
  | _, _, .prim _ args, st => args.use st
  | _, _, @Exp.call _ ps _ _ body args, st => do
    let st ← args.use st
    if checkBody body.check (initCtx ps) then some st else none
  | _, _, .ok a, st => a.use st
  | _, _, .err a, st => a.use st
  | _, _, @Exp.match_ _ ε α _ s eE eO, st => do
    let st ← s.use st
    let sE ← eE.check (BS.fresh .own ε.linear :: st)
    let sO ← eO.check (BS.fresh .own α.linear :: st)
    let sE ← popDone sE
    let sO ← popDone sO
    if sE == sO then some sE else none
  | _, _, .ext _ args, st => if args.noOut then args.use st else none
  | _, _, .extMut _ args k, st => do
    let st ← args.use st
    let sk ← k.check (BS.fresh .own false :: st)
    popDone sk
  | _, _, .mk _ args, st => args.use st
  | _, _, .read (t := t) p, st => if t.linear then none else p.access st .read
  | _, _, .assign (t := t) p a k, st => do
    if t.linear || p.wholeView st then none
    let st ← a.use st
    let st ← p.access st .write
    k.check st
  | _, _, @Exp.case _ _ pt qt _ s _ eP eQ, st => do
    let st ← s.use st
    let sP ← eP.check (BS.fresh .own pt.linear :: st)
    let sQ ← eQ.check (BS.fresh .own qt.linear :: st)
    let sP ← popDone sP
    let sQ ← popDone sQ
    if sP == sQ then some sP else none
  | _, _, .put p i a k, st => do
    if p.wholeView st then none
    let st ← i.use st
    let st ← a.use st
    let st ← p.access st .write
    k.check st
  | _, _, .take (t := t) (dflt := _) p i k, st => do
    if p.wholeView st then none
    let st ← i.use st
    let st ← p.access st .write
    let sk ← k.check (BS.fresh .own t.linear :: st)
    popDone sk
  | _, _, .borrowShr (t := t) (u := u) p body k, st => do
    let st₀ ← p.access st .read
    let sb ← body.check ({ BS.fresh .shr t.linear with view := p.wholeView st } ::
      enterBlock (addLoan st₀ p.root ⟨false, p.path⟩))
    let sb ← popDone sb
    let sk ← k.check (BS.fresh .own u.linear :: exitBlock st₀ sb)
    popDone sk
  | _, _, .borrowMut (t := t) (u := u) p body k, st => do
    let st₀ ← p.access st .write
    let sb ← body.check ({ BS.fresh .mut t.linear with view := p.wholeView st } ::
      enterBlock (addLoan st₀ p.root ⟨true, p.path⟩))
    let sb ← popDone sb
    let sk ← k.check (BS.fresh .own u.linear :: exitBlock st₀ sb)
    popDone sk
  | _, _, .callRef (r := r) _ _ body args k, st => do
    let st₁ ← args.use st
    if checkBody body.check (args.binders st) then
      let sk ← k.check (BS.fresh .own r.linear :: exitBlock st st₁)
      popDone sk
    else none
  | _, _, .guard g, st => g.use st
  | _, _, @Exp.loop _ _ s _ _ cs init c body k, st => do
    if !cs.distinct then none
    let st ← init.use st
    let st ← cs.use st
    let ci := { BS.fresh .own false with wr := false } ::
      { BS.fresh .own s.linear with wr := false } :: enterBlock st
    let sc ← c.check ci
    let bi := BS.fresh .own false :: BS.fresh .own s.linear :: carryIn cs.idxs 0 st
    let sb ← body.check bi
    if sc == ci && sb.drop 2 == carryOut cs.idxs 0 st && (sb.drop 1).head?.all BS.done then
      let sk ← k.check (BS.fresh .own s.linear :: st)
      popDone sk
    else none

/-- The checker on a term, with the binders of its context owned and unconstrained at the end.
Callers and `Fn.wf` constrain them. -/
def Exp.wf {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Bool := (e.check (initCtx Γ)).isSome

/-- A function is well formed when its body passes the checker and consumes each linear
parameter. -/
def Fn.wf {ps : List Ty} {r : Ty} (f : Fn ps r) : Bool :=
  checkBody f.body.check (initCtx ps)

/-- A function with reference parameters is well formed for the argument modes `ms`, one per
parameter. -/
def FnRef.wf {ps os : List Ty} {r : Ty} (f : FnRef ps os r) (ms : List Mode) : Bool :=
  checkBody f.body.check
    ((ps.zip ms).map fun (t, m) => BS.fresh m t.linear)

end Millipede
