import Lean
import Millipede.Meta.Basic

/-!
# Named A-normal form and the source-level checkers of `mp def`

The elaborator first turns the body of an `mp def` into `AExp`, a named mirror of `Exp` in which
variables are names instead of de Bruijn indices, each use carrying its syntax for error
positions. Two checkers run on it before any term is emitted.

1. The linearity checker `AExp.uses` and `checkOnce` makes sure that a linear binder is used
   exactly once on every path and never from inside a loop. Its errors point at the binder when
   it is unused or used twice, and otherwise at the use.
2. The borrow checker `AExp.check` mirrors `Exp.check` line by line on names, with the same state
   per binder: mode, linearity, whether it was moved, whether it is writable in this block, and
   its live loans. Its errors say which rule failed and where, such as a use after a move, a
   place used while it is borrowed with `&mut`, a write or move while it is borrowed with `&`, a
   write through `&`, a write to a binder of an enclosing block, or a linear value copied or
   overwritten in a place.

The kernel checks every accepted term again through `f.wf`, by `decide`, so these checkers only
give the errors their positions and wording.
-/

namespace Millipede.Meta

open Lean

/-- An atom of the named ANF, which is a variable, by name and with the syntax of the use, or a
literal, with its surface type and its value as a Lean term. -/
inductive SAtom where
  | var (n : Name) (ref : Syntax)
  | lit (ty : STy) (val : Expr)
deriving Inhabited

/-- The syntax of an atom, for errors. -/
def SAtom.ref : SAtom → Syntax
  | .var _ r => r
  | .lit _ _ => .missing

/-- A primitive, with its `Prim` constructor, its operand types in `Prim` order and its result
type. -/
structure PrimInfo where
  con : Name
  ins : List STy
  out : STy
deriving Inhabited

/-- A place, the root variable and its selectors, mirroring `Place`. A field carries its lens, a
`Lens s t` term, its field number and its type. -/
inductive SPlace where
  | var (n : Name) (ref : Syntax)
  | field (p : SPlace) (lens : Expr) (idx : Nat) (t : STy) (ref : Syntax)
  | index (p : SPlace) (i : SAtom) (ref : Syntax)
  | slot (p : SPlace) (i : SAtom) (ref : Syntax)
  | range (p : SPlace) (lo len : SAtom) (ref : Syntax)
  | elem (p : SPlace) (i : SAtom) (ref : Syntax)
  | pair2 (p : SPlace) (i j : SAtom) (ref : Syntax)
deriving Inhabited

/-- An extern argument. It is a word atom, constant bytes, a one-byte output buffer that has no
argument in the source, or a slice `a[lo:hi]` of a byte array, a `.range` place that the callee
reads with `slice` or writes with `sliceOut`. -/
inductive EArg where
  | word (a : SAtom)
  | bytes (bs : List UInt8)
  | outByte
  | slice (p : SPlace)
  | sliceOut (p : SPlace)
deriving Inhabited

/-- The syntax of a place. -/
def SPlace.ref : SPlace → Syntax
  | .var _ r | .field _ _ _ _ r | .index _ _ r | .slot _ _ r | .range _ _ _ r | .elem _ _ r
  | .pair2 _ _ _ r => r

/-- The root variable of a place. -/
def SPlace.root : SPlace → Name
  | .var n _ => n
  | .field p .. | .index p .. | .slot p .. | .range p .. | .elem p .. | .pair2 p .. => p.root

/-- The index atoms of a place, innermost selector first, in the order of `Place.useIdx`. -/
def SPlace.atoms : SPlace → List SAtom
  | .var _ _ => []
  | .field p .. => p.atoms
  | .index p i _ | .slot p i _ | .elem p i _ => p.atoms ++ [i]
  | .range p lo len _ => p.atoms ++ [lo, len]
  | .pair2 p i j _ => p.atoms ++ [i, j]

/-- Whether a place has no `Slots` cell, a slice element being one. It mirrors
`Place.checkable`. -/
def SPlace.checkable : SPlace → Bool
  | .var _ _ => true
  | .field p .. | .index p .. | .range p .. | .pair2 p .. => p.checkable
  | .slot .. | .elem .. => false

/-- A call argument with its mode. -/
inductive RArg where
  | own (a : SAtom)
  | shr (p : SPlace)
  | mut (p : SPlace)
deriving Inhabited

/-- A run-time test, mirroring `Guard`. -/
inductive SGuard where
  | valid (p : SPlace)
deriving Inhabited

/-- Named A-normal form, the elaborator's intermediate representation, which mirrors `Exp`. -/
inductive AExp where
  | atom (a : SAtom)
  | let_ (x : Name) (ref : Syntax) (s : STy) (e₁ e₂ : AExp)
  | ite (ref : Syntax) (c : SAtom) (e₁ e₂ : AExp)
  | prim (p : PrimInfo) (args : List SAtom)
  | call (f : FnInfo) (args : List SAtom)
  | ok (ε α : STy) (a : SAtom)
  | err (ε α : STy) (a : SAtom)
  | match_ (ref : Syntax) (ε α : STy) (s : SAtom) (e : Name) (eE : AExp) (a : Name) (eO : AExp)
  | ext (x : ExtInfo) (args : List EArg)
  /-- `let y := x(args); k` for an extern writing a mutable slice, as `Exp.extMut`. -/
  | extMut (ref : Syntax) (x : ExtInfo) (args : List EArg) (y : Name) (k : AExp)
  /-- Build a value with a `Ctor ins out` term. -/
  | mk (ctor : Expr) (ins : List STy) (out : STy) (args : List SAtom)
  | read (ref : Syntax) (p : SPlace) (t : STy)
  | assign (ref : Syntax) (p : SPlace) (t : STy) (a : SAtom) (k : AExp)
  /-- One step of an enum match with a `Split t pt qt` term. -/
  | case (ref : Syntax) (s : SAtom) (split : Expr) (t pt qt : STy) (x : Name) (xRef : Syntax)
      (eP : AExp) (y : Name) (eQ : AExp)
  | put (ref : Syntax) (p : SPlace) (i a : SAtom) (k : AExp)
  | take (ref : Syntax) (p : SPlace) (i : SAtom) (x : Name) (xRef : Syntax) (t : STy) (k : AExp)
  /-- `let x := { let r = &p / &mut p; body }; k`. When `excl` is set the borrow is `&mut`, and
  `body` returns the pair of its result and the final `r`. -/
  | borrow (ref : Syntax) (excl : Bool) (p : SPlace) (t : STy) (r : Name) (rRef : Syntax)
      (body : AExp) (u : STy) (x : Name) (k : AExp)
  | callRef (ref : Syntax) (f : FnInfo) (args : List RArg) (x : Name) (k : AExp)
  | guard (ref : Syntax) (g : SGuard)
  /-- `let x := (for i in 0...n do if !c then break; acc := body); k`, writing the loop-carried
  variables `carried` as `Exp.loop` does. `body` returns the tuple of its new accumulator and
  their values. -/
  | loop (ref : Syntax) (n : Expr) (s : STy) (init : SAtom) (i acc : Name)
      (carried : List (Name × STy)) (c body : AExp) (x : Name) (k : AExp)
deriving Inhabited

/-- Whether an `AExp` calls an extern, directly or through an impure callee. -/
def AExp.isPure : AExp → Bool
  | .atom _ | .prim _ _ | .ok _ _ _ | .err _ _ _ | .mk .. | .read .. | .guard .. => true
  | .let_ _ _ _ e₁ e₂ | .ite _ _ e₁ e₂ | .match_ _ _ _ _ _ e₁ _ e₂
  | .case _ _ _ _ _ _ _ _ e₁ _ e₂ | .borrow _ _ _ _ _ _ e₁ _ _ e₂ => e₁.isPure && e₂.isPure
  | .call f _ => f.isPure
  | .callRef _ f _ _ k => f.isPure && k.isPure
  | .loop _ _ _ _ _ _ _ c b _ k => c.isPure && b.isPure && k.isPure
  | .assign _ _ _ _ k | .put _ _ _ _ k | .take _ _ _ _ _ _ k => k.isPure
  | .ext _ _ | .extMut .. => false

/-- The registered functions an `AExp` calls directly. -/
def AExp.callees : AExp → List FnInfo
  | .atom _ | .prim _ _ | .ok _ _ _ | .err _ _ _ | .ext _ _ | .mk .. | .read .. | .guard .. => []
  | .let_ _ _ _ e₁ e₂ | .ite _ _ e₁ e₂ | .match_ _ _ _ _ _ e₁ _ e₂
  | .case _ _ _ _ _ _ _ _ e₁ _ e₂ | .borrow _ _ _ _ _ _ e₁ _ _ e₂ => e₁.callees ++ e₂.callees
  | .call f _ => [f]
  | .callRef _ f _ _ k => f :: k.callees
  | .loop _ _ _ _ _ _ _ c b _ k => c.callees ++ b.callees ++ k.callees
  | .assign _ _ _ _ k | .put _ _ _ _ k | .take _ _ _ _ _ _ k | .extMut _ _ _ _ k => k.callees

/-- The extern signature constants an `AExp` uses. -/
def AExp.externs : AExp → List Name
  | .ext x _ => [x.declName]
  | .extMut _ x _ _ k => x.declName :: k.externs
  | .let_ _ _ _ e₁ e₂ | .ite _ _ e₁ e₂ | .match_ _ _ _ _ _ e₁ _ e₂
  | .case _ _ _ _ _ _ _ _ e₁ _ e₂ | .borrow _ _ _ _ _ _ e₁ _ _ e₂ => e₁.externs ++ e₂.externs
  | .callRef _ _ _ _ k | .assign _ _ _ _ k | .put _ _ _ _ k | .take _ _ _ _ _ _ k => k.externs
  | .loop _ _ _ _ _ _ _ c b _ k => c.externs ++ b.externs ++ k.externs
  | _ => []

/-- The lens, constructor and split terms an `AExp` mentions, whose constants the normal form
unfolds. -/
partial def AExp.dataTerms : AExp → List Expr
  | .mk c _ _ _ => [c]
  | .read _ p _ => place p
  | .assign _ p _ _ k | .put _ p _ _ k | .take _ p _ _ _ _ k => place p ++ k.dataTerms
  | .case _ _ sp _ _ _ _ _ e₁ _ e₂ => sp :: e₁.dataTerms ++ e₂.dataTerms
  | .borrow _ _ p _ _ _ e₁ _ _ e₂ => place p ++ e₁.dataTerms ++ e₂.dataTerms
  | .let_ _ _ _ e₁ e₂ | .ite _ _ e₁ e₂ | .match_ _ _ _ _ _ e₁ _ e₂ =>
    e₁.dataTerms ++ e₂.dataTerms
  | .callRef _ _ args _ k =>
    (args.flatMap fun | .own _ => [] | .shr p | .mut p => place p) ++ k.dataTerms
  | .guard _ (.valid p) => place p
  | .ext _ args => args.flatMap slices
  | .extMut _ _ args _ k => args.flatMap slices ++ k.dataTerms
  | .loop _ _ _ _ _ _ _ c b _ k => c.dataTerms ++ b.dataTerms ++ k.dataTerms
  | _ => []
where
  slices : EArg → List Expr
    | .slice p | .sliceOut p => place p
    | _ => []
  place : SPlace → List Expr
    | .field p l _ _ _ => l :: place p
    | .var _ _ => []
    | .index p .. | .slot p .. | .range p .. | .elem p .. | .pair2 p .. => place p

/-- The number of nodes of an `AExp`, and whether it branches with an `ite`, `match`, `case` or
`loop`. -/
partial def AExp.size : AExp → Nat × Bool
  | .let_ _ _ _ e₁ e₂ | .borrow _ _ _ _ _ _ e₁ _ _ e₂ => add (e₁.size) (e₂.size) false
  | .ite _ _ e₁ e₂ | .match_ _ _ _ _ _ e₁ _ e₂ | .case _ _ _ _ _ _ _ _ e₁ _ e₂ =>
    add (e₁.size) (e₂.size) true
  | .loop _ _ _ _ _ _ _ c b _ k => add (add c.size b.size true) k.size true
  | .assign _ _ _ _ k | .put _ _ _ _ k | .take _ _ _ _ _ _ k | .extMut _ _ _ _ k
  | .callRef _ _ _ _ k => let (n, b) := k.size; (n + 1, b)
  | _ => (1, false)
where
  add (a b : Nat × Bool) (br : Bool) : Nat × Bool := (a.1 + b.1 + 1, a.2 || b.2 || br)

/-- The variables bound outside `e` that `e` writes, with repetitions. A variable is written when
`e` assigns it, `put`s or `take`s into it, borrows it or passes it with `&mut`, reads an extern's
output into it, or carries it through a loop. A loop carries exactly the outer variables its body
writes. -/
partial def AExp.writes : AExp → List Name
  | .let_ y _ _ e₁ e₂ => e₁.writes ++ e₂.writes.filter (· != y)
  | .ite _ _ e₁ e₂ => e₁.writes ++ e₂.writes
  | .loop _ _ _ _ i acc cr c b y k =>
    cr.map (·.1) ++ (c.writes ++ b.writes).filter (fun z => z != i && z != acc) ++
      k.writes.filter (· != y)
  | .match_ _ _ _ _ e eE a eO => eE.writes.filter (· != e) ++ eO.writes.filter (· != a)
  | .case _ _ _ _ _ _ y _ eP z eQ => eP.writes.filter (· != y) ++ eQ.writes.filter (· != z)
  | .extMut _ _ args y k =>
    args.filterMap (fun | .sliceOut p => some p.root | _ => none) ++ k.writes.filter (· != y)
  | .assign _ p _ _ k | .put _ p _ _ k => p.root :: k.writes
  | .take _ p _ y _ _ k => p.root :: k.writes.filter (· != y)
  | .borrow _ excl p _ r _ body _ y k =>
    (if excl then [p.root] else []) ++ body.writes.filter (· != r) ++ k.writes.filter (· != y)
  | .callRef _ _ args y k =>
    args.filterMap (fun | .mut p => some p.root | _ => none) ++ k.writes.filter (· != y)
  | _ => []

/-! ## Linearity, mirroring the moves of `Exp.check` with source positions -/

/-- A use count that is the same on every path, or the reason it is not. -/
inductive UseR where
  | n (k : Nat)
  | bad (ref : Syntax) (msg : String)
deriving Inhabited

/-- Sequential composition of use counts. -/
def UseR.add : UseR → UseR → UseR
  | .n a, .n b => .n (a + b)
  | .bad r m, _ => .bad r m
  | _, .bad r m => .bad r m

/-- Uses of `x` in an atom. -/
def SAtom.uses (x : Name) : SAtom → Nat
  | .var n _ => if n == x then 1 else 0
  | .lit _ _ => 0

/-- Uses of `x` in a list of atoms. -/
def atomsUses (x : Name) (as : List SAtom) : Nat :=
  as.foldl (fun k a => k + a.uses x) 0

/-- The syntax of the first use of `x` in `e`, respecting shadowing. -/
partial def AExp.firstUse (x : Name) : AExp → Option Syntax
  | .atom a => atomRef a
  | .let_ y _ _ e₁ e₂ => e₁.firstUse x <|> (if y == x then none else e₂.firstUse x)
  | .ite _ c e₁ e₂ => atomRef c <|> e₁.firstUse x <|> e₂.firstUse x
  | .prim _ as | .call _ as | .mk _ _ _ as => as.findSome? atomRef
  | .ok _ _ a | .err _ _ a => atomRef a
  | .match_ _ _ _ s e eE a eO =>
    atomRef s <|> (if e == x then none else eE.firstUse x) <|> (if a == x then none else eO.firstUse x)
  | .case _ s _ _ _ _ y _ eP z eQ =>
    atomRef s <|> (if y == x then none else eP.firstUse x) <|> (if z == x then none else eQ.firstUse x)
  | .ext _ args => args.findSome? eargRef
  | .extMut _ _ args y k => args.findSome? eargRef <|> (if y == x then none else k.firstUse x)
  | .read _ p _ | .guard _ (.valid p) => placeRef p
  | .assign _ p _ a k => atomRef a <|> placeRef p <|> k.firstUse x
  | .put _ p i a k => atomRef i <|> atomRef a <|> placeRef p <|> k.firstUse x
  | .take _ p i y _ _ k => atomRef i <|> placeRef p <|> (if y == x then none else k.firstUse x)
  | .borrow _ _ p _ r _ body _ y k =>
    placeRef p <|> (if r == x then none else body.firstUse x) <|> (if y == x then none else k.firstUse x)
  | .callRef _ _ args y k =>
    args.findSome? (fun | .own a => atomRef a | .shr p | .mut p => placeRef p) <|>
      (if y == x then none else k.firstUse x)
  | .loop _ _ _ init i acc _ c b y k =>
    atomRef init <|> (if x == i || x == acc then none else c.firstUse x <|> b.firstUse x) <|>
      (if y == x then none else k.firstUse x)
where
  atomRef : SAtom → Option Syntax
    | .var n r => if n == x then some r else none
    | .lit _ _ => none
  placeRef (p : SPlace) : Option Syntax :=
    if p.root == x then some p.ref else p.atoms.findSome? atomRef
  eargRef : EArg → Option Syntax
    | .word a => atomRef a
    | .slice p | .sliceOut p => placeRef p
    | _ => none

/-- Moves of `x` by extern arguments. Word atoms move, while a slice's atoms are words and its
place is not moved. -/
def eargsUses (x : Name) (as : List EArg) : Nat :=
  as.foldl (fun k a => match a with
    | .word a => k + a.uses x
    | .slice p | .sliceOut p => k + atomsUses x p.atoms
    | _ => k) 0

/-- The two arms of a branch must use `x` equally often. -/
def UseR.same (x : Name) (ref : Syntax) (l₁ l₂ : String) : UseR → UseR → UseR
  | .n a, .n b =>
    if a == b then .n a
    else .bad ref s!"linear variable `{x}` is used {a} time(s) in the {l₁} but {b} time(s) in \
      the {l₂}; a linear value must be used the same number of times on every path"
  | .bad r m, _ => .bad r m
  | _, .bad r m => .bad r m

/-- The number of moves of `x` in `e`, the same on every path, or why it is not. Atoms of linear
type move their variable and places do not. A use of `x` inside a loop's condition or body, when
`x` is bound outside the loop, is rejected, as in `Exp.check`. -/
partial def AExp.uses (x : Name) : AExp → UseR
  | .atom a => .n (a.uses x)
  | .let_ y _ _ e₁ e₂ => (e₁.uses x).add (if y == x then .n 0 else e₂.uses x)
  | .ite ref c e₁ e₂ =>
    (UseR.n (c.uses x)).add
      (UseR.same x ref "then-branch" "else-branch" (e₁.uses x) (e₂.uses x))
  | .prim _ as | .call _ as | .mk _ _ _ as => .n (atomsUses x as)
  | .ok _ _ a | .err _ _ a => .n (a.uses x)
  | .ext _ args => .n (eargsUses x args)
  | .extMut _ _ args y k => (UseR.n (eargsUses x args)).add (if y == x then .n 0 else k.uses x)
  | .match_ ref _ _ s e eE a eO =>
    (UseR.n (s.uses x)).add
      (UseR.same x ref "`err` arm" "`ok` arm"
        (if e == x then .n 0 else eE.uses x) (if a == x then .n 0 else eO.uses x))
  | .case ref s _ _ _ _ y _ eP z eQ =>
    (UseR.n (s.uses x)).add
      (UseR.same x ref "first arm" "other arms"
        (if y == x then .n 0 else eP.uses x) (if z == x then .n 0 else eQ.uses x))
  | .read .. | .guard .. => .n 0
  | .assign _ _ _ a k => (UseR.n (a.uses x)).add (k.uses x)
  | .put _ _ i a k => (UseR.n (i.uses x + a.uses x)).add (k.uses x)
  | .take _ _ i y _ _ k => (UseR.n (i.uses x)).add (if y == x then .n 0 else k.uses x)
  | .borrow _ _ _ _ r _ body _ y k =>
    (if r == x then .n 0 else body.uses x).add (if y == x then .n 0 else k.uses x)
  | .callRef _ _ args y k =>
    (UseR.n (atomsUses x (args.filterMap fun | .own a => some a | _ => none))).add
      (if y == x then .n 0 else k.uses x)
  | .loop ref _ _ init i acc carried c b y k =>
    -- A carried variable is handed back by the body once per iteration and restored for the next
    -- iteration and the continuation, so the loop does not consume it.
    let inner : UseR :=
      if x == i || x == acc then .n 0 else
      match (c.uses x), (b.uses x) with
      | .bad r m, _ => .bad r m
      | _, .bad r m => .bad r m
      | .n 0, .n 0 => .n 0
      | .n 0, .n 1 => if carried.any (·.1 == x) then .n 0 else
        .bad ((b.firstUse x).getD ref) s!"linear variable `{x}` is bound outside this loop and \
          used inside it; a loop may run any number of times"
      | _, _ =>
        let r := (c.firstUse x <|> b.firstUse x).getD ref
        .bad r s!"linear variable `{x}` is bound outside this loop and used inside it; a loop \
          may run any number of times"
    (UseR.n (init.uses x)).add (inner.add (if y == x then .n 0 else k.uses x))

/-- Check that the linear binder `x`, bound at `ref`, is used exactly once in `body`. -/
def checkOnce (x : Name) (ty : STy) (ref : Syntax) (kind : String) (body : AExp) :
    CoreM Unit := do
  unless ty.linear do return
  match body.uses x with
  | .n 1 => pure ()
  | .n 0 =>
    let how := if (match ty with | .adt n .. => n.toString.endsWith "Key" | _ => false) then "an arena key: free it with the arena's \
        `free`, or store it, e.g. in `Slots` with `put!`" else "consume it with `match`"
    throwErrorAt ref "unused linear {kind} `{x}` of type {ty}: a linear value must be used \
      exactly once ({how})"
  | .n k =>
    throwErrorAt ref "linear {kind} `{x}` of type {ty} is used {k} times; it must be used \
      exactly once"
  | .bad r m => throwErrorAt r m

/-! ## Borrowing by place, mirroring `Exp.check` with source positions -/

/-- A selector of a place path, mirroring `Sel`. -/
inductive NSel where
  | field (k : Nat)
  | dyn
deriving BEq

/-- Whether two paths may overlap, as `Sel.overlap` decides. -/
def NSel.overlap : List NSel → List NSel → Bool
  | [], _ => true
  | _, [] => true
  | .field a :: p, .field b :: q => a == b && NSel.overlap p q
  | _ :: p, _ :: q => NSel.overlap p q

/-- The selector path of a place, from the root. -/
def SPlace.path : SPlace → List NSel
  | .var _ _ => []
  | .field p _ k _ _ => p.path ++ [.field k]
  | .index p .. | .slot p .. | .range p .. | .elem p .. | .pair2 p .. => p.path ++ [.dyn]

/-- A live borrow with where it was taken, mirroring `Loan`. -/
structure NLoan where
  excl : Bool
  path : List NSel
  ref : Syntax
  /-- The reference that holds the loan, for a scoped borrow `let r := &mut p`, used in
  messages. -/
  holder : Option Name := none

/-- The checker's state of one binder, by name, mirroring `BS`. -/
structure NB where
  name : Name
  mode : PMode
  lin : Bool
  moved : Bool := false
  wr : Bool
  loans : List NLoan := []
  /-- The binder's type, for messages. -/
  ty : STy
  /-- Whether this is a slice view binder, as `BS.view`. -/
  view : Bool := false

/-- A fresh binder, as `BS.fresh`. -/
def NB.fresh (n : Name) (m : PMode) (t : STy) : NB :=
  { name := n, mode := m, lin := t.linear, wr := m != .shr, ty := t }

/-- Whether a place is a whole view, which is a slice or a view binder itself, as
`Place.wholeView` decides. -/
def SPlace.wholeView (st : List NB) : SPlace → Bool
  | .var n _ => (st.find? (·.name == n)).any (·.view)
  | .range .. => true
  | _ => false

/-- Reject a whole-view place as the target of an assignment, `put` or `take`, as the view rule
of `Exp.check` does. -/
def NB.noWholeView (st : List NB) (p : SPlace) (what : String) : Except (Syntax × String) Unit :=
  if p.wholeView st then
    throw (p.ref, s!"a slice view is not {what} whole: a view only gives access to its \
      elements `r[i]!` (filling a cell past its length has no storage behind it)")
  else pure ()

/-- Whether the binder may go out of scope, as `BS.done` decides. -/
def NB.done (b : NB) : Bool := b.mode == .shr || !b.lin || b.moved

/-- The parts of the state that `Exp.check` compares with `==` on `BS`. -/
def NB.same (a b : NB) : Bool :=
  a.mode == b.mode && a.lin == b.lin && a.moved == b.moved && a.wr == b.wr && a.view == b.view &&
    a.loans.length == b.loans.length &&
    (a.loans.zip b.loans).all fun (l, m) => l.excl == m.excl && l.path == m.path

/-- Whether two states are equal, as `==` on `List BS` decides. -/
def sameSt (a b : List NB) : Bool := a.length == b.length && (a.zip b).all fun (x, y) => x.same y

/-- The checker's errors, each with where and why. -/
abbrev ChkM := Except (Syntax × String)

/-- Kinds of access, mirroring `Acc`. -/
inductive NAcc where
  | read
  | write
  | move
deriving BEq

/-- Access `path` under a binder, as `BS.access` does. -/
def NB.access (b : NB) (path : List NSel) (a : NAcc) (ref : Syntax) : ChkM NB := do
  if b.moved then
    throw (ref, s!"use of `{b.name}` after it was moved (a linear value is used once)")
  if let some l := b.loans.find? (fun l => NSel.overlap l.path path && (l.excl || a != .read)) then
    if l.excl then
      throw (ref, match l.holder with
        | some r => s!"`{b.name}` is used here while an overlapping place is borrowed with \
            `&mut` by `{r}`; while `{r}` is live, no overlapping place may be used except \
            through `{r}`"
        | none => s!"`{b.name}` is used here while an overlapping place is borrowed with \
            `&mut` for a call's argument; no overlapping place may be used except through \
            that reference")
    else
      throw (ref, s!"`{b.name}` is {if a == .write then "written" else "moved"} here while an \
        overlapping place is borrowed with `&`; a shared borrow only allows reads")
  match a with
  | .read => return b
  | .write =>
    if b.mode == .shr then
      throw (ref, s!"cannot write through the shared reference `{b.name}`")
    if !b.wr then
      throw (ref, s!"cannot write `{b.name}` here: it is bound outside the current block (the \
        value of a `let`, a borrow body, a loop), so the update would not be visible after the \
        block; write it at statement level")
    return b
  | .move =>
    if b.mode == .shr then
      throw (ref, s!"cannot move the linear value out of the shared reference `{b.name}`")
    if !path.isEmpty then
      throw (ref, s!"cannot move a linear value out of a place of `{b.name}`; only whole \
        variables are moved")
    return { b with moved := true }

/-- Access `path` under the innermost binder named `n`, as `ctxAccess` does. -/
def stAccess : List NB → Name → List NSel → NAcc → Syntax → ChkM (List NB)
  | [], n, _, _, ref => throw (ref, s!"internal error: unbound `{n}`")
  | b :: bs, n, p, a, ref =>
    if b.name == n then return (← b.access p a ref) :: bs
    else return b :: (← stAccess bs n p a ref)

/-- Add a loan to the innermost binder named `n`, as `addLoan` does. -/
def stAddLoan : List NB → Name → NLoan → List NB
  | [], _, _ => []
  | b :: bs, n, l => if b.name == n then { b with loans := l :: b.loans } :: bs
    else b :: stAddLoan bs n l

/-- Enter a block, making every binder read-only, as `enterBlock` does. -/
def stEnter (st : List NB) : List NB := st.map fun b => { b with wr := false }

/-- Leave a block, returning to `orig` except for the moves, as `exitBlock` does. -/
def stExit : List NB → List NB → List NB
  | o :: os, a :: as => { o with moved := a.moved } :: stExit os as
  | _, _ => []

/-- The binders inside a loop body that writes the carried variables `xs`, as `carryIn` or, with
`out`, `carryOut` gives them. All are read-only except the innermost binder of each carried name,
and with `out` the linear carried ones are moved, since they are handed back. -/
def stCarry (xs : List Name) (out : Bool) : List NB → List NB
  | [] => []
  | b :: bs =>
    let c := xs.contains b.name
    { b with wr := b.wr && c, moved := b.moved || (out && c && b.lin) } ::
      stCarry (xs.filter (· != b.name)) out bs

/-- Pop a binder going out of scope, as `popDone` does. -/
def stPop (ref : Syntax) : List NB → ChkM (List NB)
  | b :: bs =>
    if b.done then return bs
    else throw (ref, s!"the linear value `{b.name}` of type {b.ty} is not consumed on every path")
  | [] => throw (ref, "internal error: empty state")

/-- Use an atom, moving a linear variable and reading any other, as `Atom.use` does. -/
def stUseAtom (st : List NB) : SAtom → ChkM (List NB)
  | .var n ref =>
    match st.find? (·.name == n) with
    | some b => stAccess st n [] (if b.lin then .move else .read) ref
    | none => throw (ref, s!"internal error: unbound `{n}`")
  | .lit _ _ => return st

/-- Use atoms, left to right. -/
def stUseAtoms (st : List NB) (as : List SAtom) : ChkM (List NB) :=
  as.foldlM stUseAtom st

/-- Access a place, first its index atoms and then its root along its path, as `Place.access`
does. -/
def stPlace (st : List NB) (p : SPlace) (a : NAcc) : ChkM (List NB) := do
  let st ← stUseAtoms st p.atoms
  stAccess st p.root p.path a p.ref

/-- Use call arguments in the callee's context order, as `RArgs.use` does. -/
def stRArgs (st : List NB) : List RArg → ChkM (List NB)
  | [] => return st
  | .own a :: as => do stRArgs (← stUseAtom st a) as
  | .shr p :: as => do
    let st ← stPlace st p .read
    stRArgs (stAddLoan st p.root ⟨false, p.path, p.ref, none⟩) as
  | .mut p :: as => do
    let st ← stPlace st p .write
    stRArgs (stAddLoan st p.root ⟨true, p.path, p.ref, none⟩) as

/-- Use extern arguments as `EArgs.use` does. Word atoms are used, and a slice `a[lo:hi]` reads
its atoms and reads or writes the array place, for `slice` and `sliceOut` respectively. -/
def stEArgs (st : List NB) : List EArg → ChkM (List NB)
  | [] => return st
  | .word a :: as => do stEArgs (← stUseAtom st a) as
  | .slice (.range q lo len _) :: as => do
    let st ← stUseAtoms st [lo, len]
    stEArgs (← stPlace st q .read) as
  | .sliceOut (.range q lo len _) :: as => do
    let st ← stUseAtoms st [lo, len]
    stEArgs (← stPlace st q .write) as
  | .slice p :: _ | .sliceOut p :: _ => throw (p.ref, "an extern's slice argument is `a[lo:hi]`")
  | _ :: as => stEArgs st as

/-- The borrow checker on named ANF, mirroring `Exp.check`. -/
partial def AExp.check : AExp → List NB → ChkM (List NB)
  | .atom a, st => stUseAtom st a
  | .let_ x ref s e₁ e₂, st => do
    let s₁ ← e₁.check (stEnter st)
    let s₂ ← e₂.check (NB.fresh x .own s :: stExit st s₁)
    stPop ref s₂
  | .ite ref c e₁ e₂, st => do
    let st ← stUseAtom st c
    let s₁ ← e₁.check st
    let s₂ ← e₂.check st
    if sameSt s₁ s₂ then return s₁
    throw (ref, "the two branches leave their variables in different states")
  | .prim _ as, st | .call _ as, st | .mk _ _ _ as, st => stUseAtoms st as
  | .ok _ _ a, st | .err _ _ a, st => stUseAtom st a
  | .match_ ref ε α s e eE a eO, st => do
    let st ← stUseAtom st s
    let sE ← stPop ref (← eE.check (NB.fresh e .own ε :: st))
    let sO ← stPop ref (← eO.check (NB.fresh a .own α :: st))
    if sameSt sE sO then return sE
    throw (ref, "the arms leave their variables in different states")
  | .ext _ args, st => stEArgs st args
  | .extMut ref _ args x k, st => do
    let st ← stEArgs st args
    stPop ref (← k.check (NB.fresh x .own .u64 :: st))
  | .read ref p t, st => do
    if t.linear then
      throw (ref, s!"cannot copy the linear value of type {t} out of a place; move the whole \
        variable instead")
    stPlace st p .read
  | .assign ref p t a k, st => do
    if t.linear then
      throw (ref, s!"cannot assign a linear value of type {t} to a place (the old value would \
        be dropped)")
    NB.noWholeView st p "assigned"
    let st ← stUseAtom st a
    let st ← stPlace st p .write
    k.check st
  | .case ref s _ _ pt qt x _ eP y eQ, st => do
    let st ← stUseAtom st s
    let sP ← stPop ref (← eP.check (NB.fresh x .own pt :: st))
    let sQ ← stPop ref (← eQ.check (NB.fresh y .own qt :: st))
    if sameSt sP sQ then return sP
    throw (ref, "the arms leave their variables in different states")
  | .put _ p i a k, st => do
    NB.noWholeView st p "the target of `put!`"
    let st ← stUseAtom st i
    let st ← stUseAtom st a
    let st ← stPlace st p .write
    k.check st
  | .take ref p i x _ t k, st => do
    NB.noWholeView st p "the target of `take!`"
    let st ← stUseAtom st i
    let st ← stPlace st p .write
    stPop ref (← k.check (NB.fresh x .own t :: st))
  | .borrow ref excl p t r _ body u x k, st => do
    let st₀ ← stPlace st p (if excl then .write else .read)
    let sb ← body.check ({ NB.fresh r (if excl then .mut else .shr) t with
      view := p.wholeView st } :: stEnter (stAddLoan st₀ p.root ⟨excl, p.path, p.ref, some r⟩))
    let sb ← stPop ref sb
    stPop ref (← k.check (NB.fresh x .own u :: stExit st₀ sb))
  | .callRef ref f args x k, st => do
    let st₁ ← stRArgs st args.reverse
    stPop ref (← k.check (NB.fresh x .own f.ret :: stExit st st₁))
  | .guard _ (.valid p), st => stPlace st p .read
  | .loop ref _ s init i acc carried c body x k, st => do
    let st ← stUseAtom st init
    let st ← carried.foldlM (fun st (y, _) => stAccess st y [] .write ref) st
    let ci := { NB.fresh i .own .u64 with wr := false } :: { NB.fresh acc .own s with wr := false } ::
      stEnter st
    let sc ← c.check ci
    unless sameSt sc ci do throw (ref, "the loop condition must not move or borrow anything")
    let names := carried.map (·.1)
    let bi := NB.fresh i .own .u64 :: NB.fresh acc .own s :: stCarry names false st
    let sb ← body.check bi
    unless sameSt (sb.drop 2) (stCarry names true st) do
      throw (ref, if carried.isEmpty then "the loop body must not move a variable bound outside the loop"
        else "the loop body must not move a variable bound outside the loop (except handing back \
          the variables it writes)")
    unless (sb.drop 1).head?.all NB.done do
      throw (ref, s!"the loop body must consume the linear accumulator `{acc}`")
    stPop ref (← k.check (NB.fresh x .own s :: st))

end Millipede.Meta
