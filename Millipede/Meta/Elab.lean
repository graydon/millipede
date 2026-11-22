import Lean
import Millipede.Meta.ANF
import Millipede.Meta.Syntax
import Millipede.Meta.Derive
import Millipede.Meta.Units
import Millipede.Meta.Overflow
import Millipede.Meta.Analyse
import Millipede.Meta.Cap

/-!
# The `mp def` elaborator

The command `mp def f (x : UInt64) (r : &mut Pt) requires P : T := body` turns a function written
in the surface language into a Core term and a set of declarations about it, in four stages.

1. The body is elaborated into the named A-normal form `AExp` of `Millipede.Meta.ANF`, in which
   every operand of an operation is an atom and each compound operand is bound to a fresh
   temporary. Types are checked on the way, and an error is reported at the subterm that causes
   it.
2. Linearity is checked by `AExp.uses` and borrowing by `AExp.check`, which mirrors `Exp.check` on
   names, so that errors point at source positions.
3. `emit` turns the ANF term into the typed de Bruijn term `f.exp`, resolving variables by name.
   The last parameter is index 0.
4. Declarations about `f.exp` are generated, each checked by the kernel.

The first stage accepts places such as `x`, `p.f`, `a[i]`, `a[i]!` and slices `a[lo..hi]`, the
statements of `do` notation, structure literals and updates, enum constructors and `match`,
borrows such as `let r := &mut p`, and calls that pass `&p` or `&mut p`. A Lean constant of type
`Ctor ps t` is applied like a function, which is how a library adds constructors beyond the
derived ones. A structure whose Lean constructor is private to another module is sealed, so
outside that module it cannot be built and its fields cannot be written. A statement such as an
assignment, a call with `&mut` arguments or a borrow takes the rest of its block as its
continuation, so it is spliced in front of that rest instead of being nested inside a `let`.

A slice parameter `(s : &[T; n])` is followed by a hidden `UInt64` parameter `s.len`, which
callers fill in from the slice they pass. The function's precondition then says that `s.len` is
at most `n` and that every cell below it is full, so an access `s[i]` is safe wherever `i < s.len`
is evident. A loop bound is a size expression over literals, `Nat` constants and `s.len`, with
`Nat` meaning.

The fourth stage generates the following declarations.
- `f.exp`, the term. A function with reference parameters or a `requires` clause is a reference
  function, whose result type `T × (M₁ × … × Unit)` adds the final values of its `&mut`
  parameters, last parameter first, and which also gets `f.req` and `f.fnRef`. Any other function
  gets `f.fn`.
- `f`, the simp-normal form of the meaning of `f.exp`, which is an ordinary Lean function. It
  lives in `Id` when no extern call is reached and in `StateM World` with an oracle argument
  otherwise, and its `&mut` parameters are extra results.
- `f.exp_run` or `f.exp_denoteM`, and `f.exp_denote`, the equations between the meaning of
  `f.exp` and `f`.
- `f.wf`, proved by `decide`.
- `f.safe`, which says that the term's obligations hold under the precondition, and `f.Safe`, the
  form that callers cite. The verified analyser of `Millipede.Meta.Analyse` is tried first and the
  tactic `mp_safe` after it, and when both fail the goal is left as `f.SafeGoal` for `mp prove`.

`mp program` builds a `Program` from an `init` and a `step` function. Its safety and invariant are
handled in `Millipede.Meta.Program`, and contracts in `Millipede.Meta.Contracts`.

The option `mp.normalForm false` skips `f` and its equations, and then no caller can have them
either, so a caller is declared under the same option. `mp def` waits for the kernel's check of
each theorem it generates (`addThmChecked`), so a rejected one stops the `mp def` before the
function is registered. The option `mp.autoSafe false` skips the attempt at the obligations, though `f.SafeGoal`
is still defined, and `mp.autoSafe.maxHeartbeats` bounds the attempt so that a failing one gives
up early.

The normal form is computed by `simp` with the fixed lemma set of `Millipede.Meta.Sem`. Because
`simp` does not rewrite instance arguments, the `Decidable` instances of `if`s are then
synthesised again and a second pass proves the two forms equal. Finally the carriers of tuple
types are expanded to nested products, so that `vcgen` and `simp` can use a callee's specification
at its declared type. The normal form is computed with every loop bound and callee abstracted
(`normalFormOfExp`), so that the kernel's check of the equation does not evaluate a loop.

An owned or `&mut` parameter of linear type is used exactly once, while a `&` parameter of linear
type is never moved and so is not counted.

The design is described in doc/design/embedding.md.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta

/-- The `mp def`s of this file whose elaboration failed, so that a caller's error can say that
`f` was not defined because of an earlier error. -/
initialize failedDefs : IO.Ref NameSet ← IO.mkRef {}

/-! ## Contexts -/

/-- How a local may be used: as an immutable `let` or parameter, a `let mut` or loop accumulator,
a `&` reference or a `&mut` reference. -/
inductive LKind where
  | own
  | ownMut
  | shr
  | mut
deriving BEq, Inhabited

/-- A local variable of the elaborator. -/
structure Local where
  /-- The name of the variable in the ANF term. -/
  name : Name
  /-- The source name, when it differs from `name`. A binder that shadows a variable in scope is
  renamed, so that a continuation elaborated outside its scope cannot be captured by it. -/
  src : Name := .anonymous
  ty : STy
  kind : LKind := .own
  /-- For a loop counter, the loop bound, which the counter stays below. -/
  bound : Option Expr := none
  /-- For a slice parameter or slice borrow, its length `r.len`. That is the hidden parameter
  `s.len` of a slice parameter, or the length atom of the borrowed slice. -/
  len? : Option SAtom := none
deriving Inhabited

/-- A typing context, innermost (de Bruijn index 0) first. -/
abbrev Ctx := List Local

/-- The source name of a local. -/
def Local.srcName (l : Local) : Name := if l.src.isAnonymous then l.name else l.src

/-- Look up a local variable by its source name. -/
def lookupLocal (ctx : Ctx) (n : Name) : Option Local := ctx.find? (·.srcName == n)

/-- Look up a local variable by its name in the ANF term. -/
def lookupVar (ctx : Ctx) (n : Name) : Option Local := ctx.find? (·.name == n)

/-- The length of a slice place, which is the length atom of `a[lo..hi]` or the length of a view
binder. -/
def placeLen? (ctx : Ctx) : SPlace → Option SAtom
  | .range _ _ len _ => some len
  | .var v _ => (lookupVar ctx v).bind (·.len?)
  | _ => none

/-- The length `r.len` of a slice view `r` in scope. -/
def viewLen? (ctx : Ctx) (n : Name) : Option SAtom :=
  match n with
  | .str v "len" => (lookupLocal ctx v).bind (·.len?)
  | _ => none

/-- The hidden length parameter of a slice parameter `s` is named `s.len`. -/
def lenParamName (s : Name) : Name := .str s "len"

/-- Whether parameter `k` is the hidden length of the slice parameter before it. -/
def isLenParam (ps : Array (Name × STy × PMode)) (k : Nat) : Bool :=
  match k with
  | 0 => false
  | k + 1 => match ps[k]?, ps[k + 1]? with
    | some (s, .slice _ _, m), some (l, .u64, .own) => m != .own && l == lenParamName s
    | _, _ => false

/-- The elaboration monad: a counter for fresh temporaries. -/
abbrev M := StateRefT Nat TermElabM

/-- A fresh temporary name; it cannot clash with source names. -/
def fresh : M Name := modifyGet fun n => (Name.mkNum `_mp_tmp n, n + 1)

/-- A bug seeded into the translation of `do` notation. Only the differential self-test sets it,
to show that the bug is caught. -/
register_option mp.selftest.badProof : String := {
  defValue := ""
  descr := "test only: give the generated theorems of this last name component, such as \
    `exp_run`, a proof that the kernel rejects"
}

register_option mp.selftest.doMutant : String := {
  defValue := ""
  descr := "test only: seed a bug in the `do` translation: break-ignored, \
    continue-falls-through, return-lost, return-falls-through, incl-off-by-one, lo-ignored, join-lost, \
    jump-join-lost, bind-name, neg-cond, acc-lost, inner-break-outer"
}

/-- Whether the seeded bug `m` is on. The option is refused outside the module of the self-test,
and `scripts/audit.sh` checks the sources for it too. -/
def doMutant (m : String) : M Bool := do
  let v := mp.selftest.doMutant.get (← getOptions)
  if v.isEmpty then return false
  unless (← getMainModule) == `Tests.Differential.DoFuncs do
    throwError "`mp.selftest.doMutant` seeds a bug into the translation of `mp def`: it is \
      allowed only in Tests/Differential/DoFuncs.lean"
  return v == m

/-- The ANF name of a new binder with source name `x`, which is `x` itself, or a fresh variant of
it when `x` is already in scope. -/
def bindName (ctx : Ctx) (x : Name) : M Name := do
  if ((lookupLocal ctx x).isSome || (lookupVar ctx x).isSome) && !(← doMutant "bind-name") then
    modifyGet fun n => (Name.mkNum x n, n + 1)
  else pure x

/-- The context entry of a new binder with ANF name `x'` and source name `x`. -/
def mkLocal (x x' : Name) (t : STy) (kind : LKind := .own) : Local :=
  { name := x', src := if x == x' then .anonymous else x, ty := t, kind := kind }

/-- Whether a name is a temporary. -/
def isTemp : Name → Bool
  | .num `_mp_tmp _ => true
  | _ => false

/-! ## Names of loop states -/

/-- The roles of the flags a loop carries, by their temporaries: "left the loop" for `break`, and
"returned" and "returned value" for `return`. `elabFor` sets it for the `mp def` being
elaborated. -/
initialize flagRolesRef : IO.Ref (NameMap String) ← IO.mkRef {}

/-- The display names of each loop's state components, the accumulator followed by the carried
variables and flags. Loops are listed in pre-order of the Core term, so a loop comes before its
body's loops and those before its continuation's. `emit` fills it. -/
initialize loopNamesRef : IO.Ref (Array (Array String)) ← IO.mkRef #[]

/-- The loop state names of each `mp def`, saved when it is emitted. `mp_safe` names a loop's
state components after them and takes its loop invariants in this order. -/
initialize loopNamesExt : SimplePersistentEnvExtension (Name × Array (Array String))
    (NameMap (Array (Array String))) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, a) => m.insert n a
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (n, v) => m.insert n v) m) {}
  }

/-- The display name of a variable of a loop state: its source name, or the flag's role. -/
def loopVarName (z : Name) : IO String := do
  if isTemp z then return ((← flagRolesRef.get).find? z).getD "_"
  return (match z with | .num p _ => p | _ => z).toString

/-- Let-bindings produced by ANF conversion, in evaluation order. -/
abbrev Binds := Array (Name × STy × AExp)

/-- Whether evaluating a term has no obligations and no effects, as for an atom, a primitive
other than `+! -! *!`, a constructor, or a `let` of these. The right operand of `&&` or `||` may
then be evaluated strictly. -/
def AExp.isInert : AExp → Bool
  | .atom _ | .mk _ _ _ _ => true
  | .prim p _ =>
    ![``Prim.addNuw, ``Prim.subNuw, ``Prim.mulNuw, ``Prim.trunc8Nuw].contains p.con
  | .let_ _ _ _ e₁ e₂ => e₁.isInert && e₂.isInert
  | _ => false

/-- Whether `a` ends, after temporary `let`s, in a statement-like term, which is a call or borrow
returning its result, an assignment, a `put` or a `take`. Only such terms are spliced. -/
partial def needsSplice : AExp → Bool
  | .callRef _ _ _ y (.atom (.var z _)) | .borrow _ _ _ _ _ _ _ _ y (.atom (.var z _))
  | .take _ _ _ y _ _ (.atom (.var z _)) | .extMut _ _ _ y (.atom (.var z _))
  | .loop _ _ _ _ _ _ _ _ _ y (.atom (.var z _)) => y == z
  | .assign .. | .put .. => true
  | .let_ y _ _ _ e₂ => isTemp y && needsSplice e₂
  | _ => false

/-- `let x := a; rest`, with the statement-like terms of `a` spliced in front of `rest`. A call or
borrow whose continuation just returns its result binds `x` directly, and assignments, `put` and
temporary `let`s float out. `Exp.wf` makes the enclosing binders read-only inside a `let`'s bound
term, so splicing keeps these statements at block level, with the same value. -/
partial def splice (a : AExp) (x : Name) (s : STy) (rest : AExp) : AExp :=
  let dflt := AExp.let_ x .missing s a rest
  if !needsSplice a then dflt else
  match a with
  | .callRef ref f args y (.atom (.var z _)) =>
    if y == z then .callRef ref f args x rest else dflt
  | .extMut ref f args y (.atom (.var z _)) =>
    if y == z then .extMut ref f args x rest else dflt
  | .borrow ref ex p t r rr body u y (.atom (.var z _)) =>
    if y == z then .borrow ref ex p t r rr body u x rest else dflt
  | .take ref p i y yr t (.atom (.var z _)) =>
    if y == z then .take ref p i x yr t rest else dflt
  | .loop ref n s' init i acc cr c b y (.atom (.var z _)) =>
    if y == z then .loop ref n s' init i acc cr c b x rest else dflt
  | .let_ y r t e₁ e₂ => if isTemp y then .let_ y r t e₁ (splice e₂ x s rest) else dflt
  | .assign ref p t a k => .assign ref p t a (splice k x s rest)
  | .put ref p i a k => .put ref p i a (splice k x s rest)
  | _ => dflt

/-- Wrap `e` in the let-bindings `bs`. -/
def wrap (bs : Binds) (e : AExp) : AExp :=
  bs.foldr (fun (x, s, a) e => splice a x s e) e

/-- Strip parentheses. -/
partial def unparen (stx : Syntax) : Syntax :=
  if stx.getKind == ``Lean.Parser.Term.paren then unparen stx[1] else stx

/-- Fail with a type mismatch at `stx` unless `t` is the expected type. -/
def expect (stx : Syntax) (exp? : Option STy) (t : STy) : M Unit := do
  if let some e := exp? then
    unless e == t do
      throwErrorAt stx "type mismatch: expected {e}, but this has type {t}{qtyHint e t}"

/-- A binder must not shadow a reference, because the write-back of a `&mut` reads it by name. -/
def checkShadow (ctx : Ctx) (x : Name) (ref : Syntax) : M Unit := do
  if let some l := lookupLocal ctx x then
    if l.kind == .mut || l.kind == .shr then
      throwErrorAt ref "`{x}` shadows the reference `{x}`; choose another name"

/-- Replace the tail values of `e`, of type `ty`, by `k a`. It is used to hand back the final
values of `&mut` references with the result. -/
partial def mapTail (e : AExp) (ty : STy) (k : SAtom → M AExp) : M AExp := do
  match e with
  | .atom a => k a
  | .let_ x r s e₁ e₂ => return .let_ x r s e₁ (← mapTail e₂ ty k)
  | .ite r c e₁ e₂ => return .ite r c (← mapTail e₁ ty k) (← mapTail e₂ ty k)
  | .match_ r ε α s x eE y eO => return .match_ r ε α s x (← mapTail eE ty k) y (← mapTail eO ty k)
  | .case r s sp t pt qt x xr eP y eQ =>
    return .case r s sp t pt qt x xr (← mapTail eP ty k) y (← mapTail eQ ty k)
  | .assign r p t a k' => return .assign r p t a (← mapTail k' ty k)
  | .put r p i a k' => return .put r p i a (← mapTail k' ty k)
  | .take r p i x xr t k' => return .take r p i x xr t (← mapTail k' ty k)
  | .borrow r ex p t rr rref body u x k' => return .borrow r ex p t rr rref body u x (← mapTail k' ty k)
  | .callRef r f args x k' => return .callRef r f args x (← mapTail k' ty k)
  | .extMut r f args x k' => return .extMut r f args x (← mapTail k' ty k)
  | .loop r n s init i acc cr c b x k' => return .loop r n s init i acc cr c b x (← mapTail k' ty k)
  | e => do
    let x ← fresh
    return .let_ x .missing ty e (← k (.var x .missing))

/-- The pair `(a, b)`. -/
def mkPairE (a b : STy) (x y : SAtom) : AExp :=
  .mk (mkApp2 (mkConst ``Ctor.pairMk) a.toTy b.toTy) [a, b] (.pair a b) [x, y]

/-- `Ty.tup ts` expanded to pairs `pair t₁ (pair t₂ … unit)`. The body of a function with `&mut`
parameters is built with these, and its normal form and obligations are computed from it, while
its declared type and the lemmas callers use keep `Ty.tup` folded as `Exp.callRef` does. -/
def tupX : List STy → STy
  | [] => .unit
  | t :: ts => .pair t (tupX ts)

/-- `(a, (m₁, (m₂, … ())))`, the result with the final values of the references `ms`, built by
the one tuple constructor `Ctor.tupMk`. The handed-back references are then the references
themselves, which the memory lowering keeps in place. -/
def tupleE (resTy : STy) (a : SAtom) (ms : List (Name × STy)) (folded := false) : M AExp := do
  let tys := ms.map (·.2)
  -- With `folded`, the type is `pair resTy (Ty.tup tys)`, as for the body of `Exp.loop`.
  let out : STy := .pair resTy (if folded then .tup tys else tupX tys)
  -- `Ctor.tupMk resTy tys`, typed with the tuple expanded like the rest of the body. The two
  -- types agree by unfolding `Ty.tup`.
  let law ← mkAppM ``PLift.up #[mkApp2 (mkConst ``Flat.CtorLaw.tuple) resTy.toTy (tyList tys)]
  let law ← mkAppOptM ``Option.some #[none, some law]
  let occs ← mkAppM ``PLift.up #[mkApp (mkConst ``Flat.tupBuild_occs) (tyList (resTy :: tys))]
  let occs ← mkAppOptM ``Option.some #[none, some occs]
  let c ← mkAppOptM ``Ctor.mk #[some (tyList (resTy :: tys)), some out.toTy, some (toExpr "tuple"),
    some (mkConst ``CtorKind.tuple), some (mkApp (mkConst ``Flat.tupBuild) (tyList (resTy :: tys))),
    some law, some occs]
  return .mk c (resTy :: tys) out (a :: ms.map fun (m, _) => .var m .missing)

/-! ## Types -/

/-- Parse a surface type. -/
partial def elabTy (stx : Syntax) : M STy := do
  match stx with
  | `(($t)) => elabTy t
  | `(UInt64) | `(U64) => return .u64
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | `(Result $e $a) | `(Except $e $a) => return .result (← elabTy e) (← elabTy a)
  | `(Bytes) => throwErrorAt stx "a string (`Bytes`) can only be passed to an extern \
      (`mp extern … (buf : Bytes)`); an `mp def` cannot take or return one: choose the string \
      at the extern's call, or pass a byte slice `&[U8; n]`"
  | `(Arr $t $n:num) | `(Vector $t $n:num) => return .arr (← elabTy t) (toExpr n.getNat)
  | `(Slots $t $n:num) => return .slots (← elabTy t) (toExpr n.getNat)
  | `(Slice $t $n:num) => return .slice (← elabTy t) (toExpr n.getNat)
  | `($a × $b) => return .pair (← elabTy a) (← elabTy b)
  | `([$_]) =>
    throwErrorAt stx "a slice type needs the length of the arrays it views: `[T; n]` (the view \
      of `a[lo..hi]` for an array `a : Arr T n`; its own length is `s.len`)"
  | _ =>
    if stx.getKind == ``mpSliceTy then
      let n ← match stx[3].isNatLit? with
        | some n => pure (toExpr n)
        | none =>
          -- A size term under `variable` binders, in a generic definition.
          let e ← Term.elabTermEnsuringType stx[3] (mkConst ``Nat)
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          unless e.hasFVar && !e.hasMVar do
            throwErrorAt stx[3] "the bound of a slice type `[T; n]` must be a numeric literal or \
              a size variable"
          pure e
      return .slice (← elabTy stx[1]) n
    if stx.getKind == ``mpRefMut || stx.getKind == ``mpRefShr then
      throwErrorAt stx "a reference type `&T` / `&mut T` is only allowed as a parameter type"
    let e ← try Term.elabType stx catch _ =>
      throwErrorAt stx "unsupported type: expected UInt64, Bool, Unit, Result ε α, Arr T n, \
        Slots T n, a type with `deriving Data`, or another type with a `Data` instance"
    Term.synthesizeSyntheticMVarsNoPostponing
    match ← exprToSTy (← instantiateMVars e) with
    | some t => return t
    | none => throwErrorAt stx "unsupported type `{e}`: it has no `Data` instance"

/-- Parse a parameter type with its mode (`&T`, `&mut T` or `T`). -/
def elabParamTy (stx : Syntax) : M (STy × PMode) := do
  if stx.getKind == ``mpRefMut then return (← elabTy stx[1], .mut)
  if stx.getKind == ``mpRefShr then return (← elabTy stx[1], .shr)
  return (← elabTy stx, .own)

/-! ## Names -/

/-- Resolve a global name to a registered `mp def` or `mp extern`. -/
def resolveEntry (id : Syntax) : M (Option Entry) := do
  let env ← getEnv
  -- `A.op`, for a variable `A : I args` of an interface whose operation `I.op` is registered by
  -- `mp interface_op`, is `I.op` at `args` and `A`.
  if let .str (.str .anonymous a) op := id.getId then
    if let some d := (← getLCtx).findFromUserName? (Name.mkSimple a) then
      let ty ← whnfR (← instantiateMVars d.type)
      if let .const I _ := ty.getAppFn then
        if let some (.fn i) := lookupEntry env (I ++ Name.mkSimple op) then
          if i.nGen == ty.getAppNumArgs + 1 then
            let r := i.instantiate (ty.getAppArgs.push d.toExpr)
            let ps ← r.params.mapM fun (x, t, m) => return (x, ← t.refresh, m)
            return some (.fn { r with params := ps, ret := ← r.ret.refresh })
  let cands ← resolveGlobalName id.getId
  for (n, fields) in cands do
    if fields.isEmpty then
      if let some e := lookupEntry env n then
        if let .adt _ := e then continue
        return some e
  -- A function declared under `mp.normalForm false` has no constant `f`, so it is found through
  -- its term `f.exp`.
  for (n, fields) in ← resolveGlobalName (id.getId ++ `exp) do
    if fields.isEmpty then
      if let some e@(.fn _) := lookupEntry env n.getPrefix then return some e
  -- `X.f`, for an abbreviation `X := C a…` of a type such as `abbrev Pool8 := Pool UInt64 8 1`,
  -- is the function `C.f`, since Lean's dot notation looks through the abbreviation. A generic
  -- `C.f` is instantiated at the call.
  if let .str p f := id.getId then
    if !p.isAnonymous then
      for (n, fields) in ← resolveGlobalName p do
        unless fields.isEmpty do continue
        let some (.defnInfo dv) := env.find? n | continue
        let some C := dv.value.getAppFn.constName? | continue
        if let some e@(.fn _) := lookupEntry env (C ++ Name.mkSimple f) then return some e
  return none

/-- Resolve a global name to a constructor of a derived type: the type and constructor. -/
def resolveCtor (id : Name) : M (Option (AdtInfo × Name)) := do
  let env ← getEnv
  let cands ← try resolveGlobalName id catch _ => pure []
  for (n, fields) in cands do
    if fields.isEmpty then
      if let some (.ctorInfo cv) := env.find? n then
        if let some i := lookupAdt env cv.induct then return some (i, n)
  return none

/-- The surface type of a `Ty` term. -/
partial def tyExprToSTy (t : Expr) : MetaM (Option STy) := do
  -- `⟨C, inst⟩` gives the carrier as written, because an open `A.S` must not become a kernel
  -- projection.
  if t.isAppOfArity ``Ty.mk 2 && t.hasFVar then return ← exprToSTy t.appFn!.appArg!
  -- `Ty.result ε α` and `Ty.pair a b` over open types give their parts as written.
  if t.hasFVar then
    if t.isAppOfArity ``Ty.result 2 then
      let some e ← tyExprToSTy t.appFn!.appArg! | return none
      let some a ← tyExprToSTy t.appArg! | return none
      return some (.result e a)
    if t.isAppOfArity ``Ty.pair 2 then
      let some a ← tyExprToSTy t.appFn!.appArg! | return none
      let some b ← tyExprToSTy t.appArg! | return none
      return some (.pair a b)
  exprToSTy (← whnf (mkApp (mkConst ``Ty.carrier) t))

/-- The elements of a `List Ty` term. -/
partial def tyListElems (l : Expr) : MetaM (Option (List Expr)) := do
  let l ← whnf l
  if l.isAppOfArity ``List.nil 1 then return some []
  if l.isAppOfArity ``List.cons 3 then
    let some rest ← tyListElems l.appArg! | return none
    return some (l.appFn!.appArg! :: rest)
  return none

/-- Resolve a global name to a `Ctor` constant, which is a Lean constant of type `Ctor ps t`,
with its parameter and result types. `mp def` applies such a constant like a function, so that
`c a b` is `Exp.mk c [a, b]`. This is how a library supplies constructors beyond the derived
ones, such as the private `Key.mint` and `Key.burn` of `Millipede/Lib/Pool.lean`. -/
def resolveCtorConst (id : Name) : M (Option (Name × List STy × STy × Nat)) := do
  let env ← getEnv
  let cands ← try resolveGlobalName id catch _ => pure []
  for (n, fields) in cands do
    if fields.isEmpty then
      if let some ci := env.find? n then
        unless ci.levelParams.isEmpty do continue
        -- A `Ctor` constant, or a function of Lean parameters returning one such as a generic
        -- type's constructor: the number of its explicit parameters.
        let r ← forallTelescope ci.type fun xs ty => do
          let ty ← whnfR ty
          unless ty.isAppOfArity ``Ctor 2 do return none
          let nExp ← xs.foldlM (fun k x => do
            return if (← x.fvarId!.getDecl).binderInfo.isExplicit then k + 1 else k) 0
          if !xs.isEmpty then return some ([], STy.unit, nExp)
          let some ps ← tyListElems ty.appFn!.appArg! | return none
          let ins ← ps.mapM fun p => (tyExprToSTy p : MetaM _)
          let some out ← (tyExprToSTy ty.appArg! : MetaM _) | return none
          if ins.all Option.isSome then return some (ins.filterMap fun x => x, out, 0)
          return none
        if let some (ins, out, k) := r then return some (n, ins, out, k)
  return none

/-- The binary operators, each with its source spelling, operand type, `Prim` and result type. -/
def binOps : List (String × PrimInfo) :=
  let w (c : Name) : PrimInfo := ⟨c, [.u64, .u64], .u64⟩
  let cmp (c : Name) : PrimInfo := ⟨c, [.u64, .u64], .bool⟩
  let b (c : Name) : PrimInfo := ⟨c, [.bool, .bool], .bool⟩
  arithOps.map (fun (o, c) => (o, w c)) ++  -- `+ - *` wrap around, `+! -! *!` carry an obligation
  [("/", w ``Prim.udiv), ("%", w ``Prim.umod), ("&&&", w ``Prim.band), ("|||", w ``Prim.bor),
   ("^^^", w ``Prim.bxor), ("<<<", w ``Prim.shl), (">>>", w ``Prim.shr),
   ("<", cmp ``Prim.ult), ("≤", cmp ``Prim.ule), ("<=", cmp ``Prim.ule),
   (">", cmp ``Prim.ugt), ("≥", cmp ``Prim.uge), (">=", cmp ``Prim.uge),
   ("&&", b ``Prim.and), ("||", b ``Prim.or)]  -- `elabE` handles `&&` and `||` before this table

/-- The UTF-8 bytes of a string literal. -/
def strBytes (s : String) : List UInt8 := s.toUTF8.toList

/-! ## Places -/

/-- The type of a place's selector target: its element type, its length and the selector that
applies. -/
def selOf (t : STy) : Option (STy × Expr × Name) :=
  match t with
  | .arr e n => some (e, n, `index)
  | .slots e n => some (e, n, `slot)
  | .slice e n => some (e, n, `slot)
  | _ => none

/-- The fields of a struct at the arguments `is` of its instance. A parameterised struct's field
types are stored with its parameters abstracted. -/
def fieldsAt (fs : Array FieldInfo) (is : Array Expr) : MetaM (Array FieldInfo) :=
  if is.isEmpty then pure fs else fs.mapM fun fi => do
    return { fi with ty := ← (fi.ty.mapExpr (·.instantiateRev is)).refresh }

/-- Field `f` of a place of type `t`. -/
def fieldOf (p : SPlace) (t : STy) (f : Name) (ref : Syntax) : M (SPlace × STy) := do
  match t with
  | .adt S _ _ is =>
    match lookupAdt (← getEnv) S with
    | some { kind := .struct fs _, .. } =>
      match (← fieldsAt fs is).find? (·.name == f) with
      | some fi => return (.field p (mkAppN (mkConst fi.lens) is) fi.idx fi.ty ref, fi.ty)
      | none => throwErrorAt ref "`{S}` has no field `{f}`"
    | _ => throwErrorAt ref "`{S}` is not a struct: it has no field `{f}`"
  | .pair a b =>
    if f == `fst || f == Name.mkSimple "1" then
      return (.field p (mkApp2 (mkConst ``Lens.fst) a.toTy b.toTy) 0 a ref, a)
    if f == `snd || f == Name.mkSimple "2" then
      return (.field p (mkApp2 (mkConst ``Lens.snd) a.toTy b.toTy) 1 b ref, b)
    throwErrorAt ref "a pair has the fields `fst` and `snd`, not `{f}`"
  | _ => throwErrorAt ref "type {t} has no field `{f}`"

/-- The place named by a dotted identifier, which is a local followed by fields. -/
def placeOfIdent (ctx : Ctx) (x : Syntax) : M (SPlace × STy) := do
  let comps := x.getId.components
  let some h := comps.head? | throwErrorAt x "expected a place"
  let some l := lookupLocal ctx h | throwErrorAt x "unknown variable `{h}`"
  let mut p := SPlace.var l.name x
  let mut t := l.ty
  for f in comps.tail do
    (p, t) ← fieldOf p t f x
  return (p, t)

/-- Whether `S` is a sealed struct, one whose Lean constructor is `private` to another module, as
in `structure S where private mk :: …`. Outside that module an `mp def` cannot build a value of
`S` or write its fields, so its values are unforgeable there, as the arena keys of
`Millipede/Lib/Pool.lean` are. -/
def sealedStruct (S : Name) : M Bool := do
  let env ← getEnv
  unless isStructure env S do return false
  isInaccessiblePrivateName (getStructureCtor env S).name

/-- Fail if `S` is sealed. -/
def requireUnsealed (ref : Syntax) (S : Name) (what : String) : M Unit := do
  if ← sealedStruct S then
    throwErrorAt ref "`{S}` is sealed (its constructor is private to its module): it cannot \
      {what} here"

/-- The struct that a derived field lens `S.f.lens` belongs to. -/
def lensStruct? (lens : Expr) : Option Name :=
  -- A parameterised struct's lens is applied to the struct's arguments.
  match lens.getAppFn with
  | .const n _ => match n with
    | .str (.str S _) "lens" => some S
    | _ => none
  | _ => none

/-- No field selector of `p` belongs to a sealed struct, since writing one would forge a value. -/
partial def requireUnsealedPath (p : SPlace) : M Unit := do
  match p with
  | .var _ _ => pure ()
  | .field q lens _ _ ref =>
    if let some S := lensStruct? lens then requireUnsealed ref S "have its fields written"
    requireUnsealedPath q
  | .index q _ _ | .slot q _ _ | .range q _ _ _ | .elem q _ _ | .pair2 q _ _ _ =>
    requireUnsealedPath q

/-- The root local of a place may be written, being a `let mut`, a `&mut` reference or a loop
accumulator, and no field on the path belongs to a sealed struct. -/
def requireMutable (ctx : Ctx) (p : SPlace) (what : String) : M Unit := do
  requireUnsealedPath p
  let some l := lookupVar ctx p.root | throwErrorAt p.ref "unknown variable `{p.root}`"
  match l.kind with
  | .ownMut | .mut => pure ()
  | .shr => throwErrorAt p.ref "cannot {what} through the shared reference `{l.srcName}`"
  | .own => throwErrorAt p.ref "`{l.srcName}` is not mutable: declare it with `let mut` (or take \
      it as `&mut`) to {what} it"

/-- Whether a surface type is `UInt8`. A byte is computed on and compared through the conversions
`Prim.zext8` and `Prim.trunc8`. -/
def STy.isU8 : STy → Bool
  | .other _ c _ _ => c.isConstOf ``UInt8
  | _ => false

/-- The surface type `UInt8`. -/
def u8STy : M STy := do
  let some t ← (exprToSTy (mkConst ``UInt8) : MetaM _) | throwError "internal: no `Data UInt8`"
  return t

/-- The primitive `zext8 : [U8] → U64` at the surface. -/
def zext8Info (u8 : STy) : PrimInfo := ⟨``Prim.zext8, [u8], .u64⟩
/-- The primitive `trunc8 : [U64] → U8` at the surface. -/
def trunc8Info (u8 : STy) : PrimInfo := ⟨``Prim.trunc8, [.u64], u8⟩

/-- Reads a loop bound written as a size expression, which is a numeric literal, a Lean constant
of type `Nat`, the length `s.len` of a slice view `s : [T; N]`, or `+ - * / %` of those, where `/`
and `%` take a positive literal. The expression has `Nat` meaning, so `-` truncates at 0.

The result is a static bound on the loop's iteration count, whether the expression depends on
run-time lengths, and the expression `e` to evaluate at run time as a `UInt64`, so that the loop
runs `bound` iterations with the condition `i < e`. In `e` every static subexpression is replaced
by its numeral and a dynamic `a - b` becomes `if b ≤ a then a - b else 0`. Every subexpression's
static bound is below `2 ^ 64`, so no `UInt64` operation of `e` wraps. -/
partial def sizeBound (ctx : Ctx) (stx : Term) : M (Option (Expr × Bool × Term)) := do
  go stx
where
  ok (n : Nat) (dyn : Bool) (e : Term) : M (Option (Expr × Bool × Term)) :=
    return if n < 2 ^ 64 then some (toExpr n, dyn, if dyn then e else Syntax.mkNumLit (toString n))
      else none
  /-- An open bound of a generic definition, such as `n` or `2 * n` over size variables. It has
  no run-time length in it. -/
  sym (e : Expr) (stx : Term) : M (Option (Expr × Bool × Term)) := return some (e, false, stx)
  go (stx : Term) : M (Option (Expr × Bool × Term)) := do
  match stx with
  | `(($e)) => go e
  | `($n:num) => ok n.getNat false stx
  | `($x:ident) =>
    match x.getId, viewLen? ctx x.getId with
    | .str v _, some _ => match (lookupLocal ctx v).map (·.ty) with
      | some (STy.slice _ m) => match STy.natOf? m with
        | some m => ok m true stx
        -- For a slice of a generic length, the length variable is the static cap.
        | none => return some (m, true, stx)
      | _ => return none
    | _, _ =>
      if (lookupLocal ctx x.getId).isSome then return none
      -- A size variable of a generic definition, declared as `variable (n : Nat)`.
      if let some d := (← getLCtx).findFromUserName? x.getId then
        if (← instantiateMVars d.type) == Lean.mkConst ``Nat then return ← sym d.toExpr stx
        return none
      -- A size parameter, which is a Lean constant of type `Nat` that evaluates to a numeral.
      let some cn ← (try some <$> resolveGlobalConstNoOverload x catch _ => pure none)
        | return none
      let some c := (← getEnv).find? cn | return none
      unless c.type == Lean.mkConst ``Nat do return none
      let e ← (Meta.reduce (Lean.mkConst cn) : MetaM _)
      let some v ← (Meta.evalNat e).run | return none
      ok v false stx
  | `($a + $b) => do
    let (some (x, p, a'), some (y, q, b')) := (← go a, ← go b) | return none
    match STy.natOf? x, STy.natOf? y with
    | some x, some y => ok (x + y) (p || q) (← `(($a' + $b')))
    | _, _ => if p || q then return none else sym (← mkAppM ``HAdd.hAdd #[x, y]) stx
  | `($a * $b) => do
    let (some (x, p, a'), some (y, q, b')) := (← go a, ← go b) | return none
    match STy.natOf? x, STy.natOf? y with
    | some x, some y => ok (x * y) (p || q) (← `(($a' * $b')))
    | _, _ => if p || q then return none else sym (← mkAppM ``HMul.hMul #[x, y]) stx
  | `($a - $b) => do
    let (some (x, p, a'), some (y, q, b')) := (← go a, ← go b) | return none
    match STy.natOf? x, STy.natOf? y with
    | some x, some y =>
      -- A dynamic difference is at most `x`, since it truncates; a static one is the `Nat`
      -- difference.
      ok (if p || q then x else x - y) (p || q) (← `((if $b' ≤ $a' then $a' - $b' else 0)))
    | _, _ => if p || q then return none else sym (← mkAppM ``HSub.hSub #[x, y]) stx
  | `($a / $b) => match b.raw.isNatLit? with
    | some k => if k == 0 then return none else do
        let some (x, p, a') ← go a | return none
        match STy.natOf? x with
        | some x => ok (x / k) p (← `(($a' / $b)))
        | none => if p then return none else sym (← mkAppM ``HDiv.hDiv #[x, toExpr k]) stx
    | none => return none
  | `($a % $b) => match b.raw.isNatLit? with
    | some k => if k == 0 then return none else do
        let some (x, p, a') ← go a | return none
        match STy.natOf? x with
        | some x => ok (if p then min x (k - 1) else x % k) p (← `(($a' % $b)))
        | none => if p then return none else sym (← mkAppM ``HMod.hMod #[x, toExpr k]) stx
    | none => return none
  | _ => return none

/-! ## Helpers of the translation of `do` statements -/


/-- A size term over the variables of a generic definition, as in `Slots.empty n` or
`Vector.replicate W v`, taken as the `Nat` term written. -/
def sizeTerm (stx : Syntax) : M Expr := do
  let e ← Term.elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  unless e.hasFVar && !e.hasMVar do
    throwErrorAt stx "the length must be a numeral or a size variable"
  return e

/-- The unit value. -/
def unitAtom : SAtom := .lit .unit (mkConst ``Unit.unit)

/-- The innermost loop around a statement. `acc : accTy` is Core's accumulator, and `user` says
whether it is a variable of the program, whose assignment at the end of an iteration is the
iteration's value. `brk?` is the loop's `break` flag, present when a `break` other than the
leading `if c then break` sets one. -/
structure LoopJ where
  acc : Name
  accTy : STy
  user : Bool := false
  brk? : Option Name := none

/-- Where the jumps of a statement go. `ret?` is the function's result type, present where
`return` is allowed, which is in the body of an `mp def` but not in a nested `do` term.
`retVars?` holds the flag and value of a `return` inside a loop, and `loop?` the innermost
loop. -/
structure DoJ where
  ret? : Option STy := none
  retVars? : Option (Name × Name) := none
  loop? : Option LoopJ := none
  /-- Inside a statement that `joinStmt` joins and that jumps, a jump ends the statement with
  `true`, after setting `rv` to the value of a `return` outside a loop. The end of a branch that
  continues is `false`, and the join tests the flag. -/
  join? : Option (Option Name) := none
  /-- The loop enclosing the innermost one, used only by the seeded bug `inner-break-outer`. -/
  outer? : Option LoopJ := none

/-- The end of an iteration of the loop `l`: its accumulator's value. -/
def endOf (l : LoopJ) : AExp := .atom (if l.accTy == .unit then unitAtom else .var l.acc .missing)

/-- The literal `b`. -/
def boolAtom (b : Bool) : SAtom := .lit .bool (toExpr b)

/-- The end of a jump, which is `true` inside a joined statement and otherwise the end of the
innermost loop's iteration. -/
def jumpEnd (j : DoJ) : AExp × STy :=
  if j.join?.isSome then (.atom (boolAtom true), .bool) else match j.loop? with
    | some l => (endOf l, l.accTy)
    | none => (.atom unitAtom, .unit)

/-- The variable a jump writes, such as a flag or the result of a `return`, as the context names
it. A joined statement writes copies, which keep the original's name as their source name. -/
def ctxVar (ctx : Ctx) (z : Name) : Name := ((lookupLocal ctx z).map (·.name)).getD z

/-- The elements of a `doSeq`, indented or bracketed. -/
def doSeqItems (seq : Syntax) : List Syntax :=
  let items := if seq.getKind == ``Lean.Parser.Term.doSeqBracketed then seq[1] else seq[0]
  items.getArgs.toList.map (·[0])

/-- The arms `if c then s (else if c then s)*` and the `else` block of a `doIf`. -/
def doIfParts (stx : Syntax) : M (List (Syntax × Syntax) × Option Syntax) := do
  let cond (c : Syntax) : M Syntax := do
    unless c.getKind == ``Lean.Parser.Term.doIfProp && c[0].isNone do
      throwErrorAt c "`if let` and `if h : c` are not supported in `mp def`"
    return c[1]
  let mut arms := [(← cond stx[1], stx[3])]
  for g in stx[4].getArgs do
    arms := arms ++ [(← cond g[1], g[3])]
  return (arms, if stx[5].isNone then none else some stx[5][1])

/-- The negation of a loop's exit test `c`, where `if c then break` leads the body. The negation
of `!d` is `d` and that of a comparison is the opposite comparison, so `if i ≥ n then break` gives
the loop condition `i < n` itself. Anything else becomes `!(c)`. -/
partial def negCond (c : Syntax) : M Syntax := do
  if ← doMutant "neg-cond" then return c
  match c with
  | `(($d)) => negCond d
  | `(!$d) => pure d
  | `($a == $b) => `($a != $b)
  | `($a != $b) => `($a == $b)
  | `($a ≠ $b) => `($a == $b)
  | `($a < $b) => `($a ≥ $b)
  | `($a ≤ $b) => `($a > $b)
  | `($a > $b) => `($a ≤ $b)
  | `($a ≥ $b) => `($a < $b)
  | _ => `(!($(⟨c⟩)))

/-- Whether `stx` contains a jump of kind `k` for the loop around it. A jump inside a nested `do`
term does not count, nor, when `intoLoops` is false, one inside an inner loop. -/
partial def hasJump (k : Name) (intoLoops : Bool) (stx : Syntax) : Bool :=
  if stx.getKind == k then true
  else if stx.getKind == ``Lean.Parser.Term.do then false
  else if !intoLoops && stx.getKind == ``Lean.Parser.Term.doFor then false
  else stx.getArgs.any (hasJump k intoLoops)

/-- Whether a statement leaves its block by a `break`, `continue` or `return` on some path. -/
def jumps (stx : Syntax) : Bool :=
  hasJump ``Lean.Parser.Term.doBreak false stx || hasJump ``Lean.Parser.Term.doContinue false stx ||
    hasJump ``Lean.Parser.Term.doReturn true stx

/-- Whether the statements `items` end on every path by assigning the variable `x` or by a jump.
Then `x` can be the loop's accumulator, since the assignment ending an iteration is its value. -/
partial def endsAssigning (x : Name) (items : List Syntax) : Bool :=
  match items.getLast? with
  | none => false
  | some it =>
    match it.getKind with
    | ``Lean.Parser.Term.doReassign =>
      it[0].getKind == ``Lean.Parser.Term.letIdDeclNoBinders && it[0][0][0].getId == x
    | ``Lean.Parser.Term.doBreak | ``Lean.Parser.Term.doContinue | ``Lean.Parser.Term.doReturn =>
      true
    | ``Lean.Parser.Term.doIf =>
      -- A missing `else` keeps `x`, so `if c then x := e` ends an accumulating iteration.
      endsAssigning x (doSeqItems it[3]) &&
        it[4].getArgs.all (fun g => endsAssigning x (doSeqItems g[3])) &&
        (it[5].isNone || endsAssigning x (doSeqItems it[5][1]))
    | ``Lean.Parser.Term.doMatch =>
      it[6][0].getArgs.all fun alt => endsAssigning x (doSeqItems alt[3])
    | ``Lean.Parser.Term.doNested => endsAssigning x (doSeqItems it[1])
    | _ => false

/-- The root names of the places that the statements of `stx` assign, as in `x := e`, `x.f := e`
or `x[i] := e`, outside any nested `do` term. -/
partial def assignedRoots (stx : Syntax) : List Name :=
  if stx.getKind == ``Lean.Parser.Term.do then [] else
  if stx.getKind == ``Lean.Parser.Term.doReassign then
    let d := stx[0]
    let lhs := if d.getKind == ``Lean.Parser.Term.letIdDeclNoBinders then d[0][0] else d[0]
    root lhs :: assignedRoots d[4]
  else stx.getArgs.toList.flatMap assignedRoots
where
  root (s : Syntax) : Name :=
    if s.isIdent then s.getId.getRoot else if s.getNumArgs > 0 then root s[0] else .anonymous

/-- Whether the statements `items` leave their block by a jump on every path. -/
partial def alwaysJumps (items : List Syntax) : Bool :=
  match items.getLast? with
  | none => false
  | some it =>
    match it.getKind with
    | ``Lean.Parser.Term.doBreak | ``Lean.Parser.Term.doContinue | ``Lean.Parser.Term.doReturn =>
      true
    | ``Lean.Parser.Term.doIf =>
      alwaysJumps (doSeqItems it[3]) && it[4].getArgs.all (fun g => alwaysJumps (doSeqItems g[3])) &&
        !it[5].isNone && alwaysJumps (doSeqItems it[5][1])
    | ``Lean.Parser.Term.doMatch => it[6][0].getArgs.all fun alt => alwaysJumps (doSeqItems alt[3])
    | ``Lean.Parser.Term.doNested => alwaysJumps (doSeqItems it[1])
    | _ => false

/-- How many copies of the rest of the block a statement `if` or `match` would hold if the rest
were put at the end of each branch. That is one per branch that does not always jump, and a
missing `else` is such a branch. A `match` over three or more constructors counts one more,
because `elabEnumMatch` elaborates its last arm into two `case` branches. -/
def contArms (it : Syntax) : Nat :=
  let n (seq : Syntax) : Nat := if alwaysJumps (doSeqItems seq) then 0 else 1
  if it.getKind == ``Lean.Parser.Term.doIf then
    n it[3] + (it[4].getArgs.map (fun g => n g[3])).sum + (if it[5].isNone then 1 else n it[5][1])
  else
    let alts := it[6][0].getArgs
    let c := (alts.map fun alt => n alt[3]).sum
    if alts.size ≥ 3 && c > 0 then c + 1 else c

/-- Whether `stx` is `()`. -/
def isUnitLit (stx : Syntax) : Bool :=
  match stx with
  | `(()) => true
  | _ => false

/-- The initial value of the result of a `return` inside a loop, which is read only after the
`return` has set it. -/
def defaultAtom (ref : Syntax) (t : STy) : M SAtom := do
  match t with
  | .u64 => return .lit .u64 (toExpr (0 : UInt64))
  | .bool => return .lit .bool (toExpr false)
  | .unit => return unitAtom
  | _ =>
    if t.linear then
      throwErrorAt ref "a `return` inside a loop needs a result type that is not linear: the \
        result is kept in a variable until the loop ends (here {t})"
    let some inst ← synthInstance? (mkApp (mkConst ``Inhabited [1]) t.carrier)
      | throwErrorAt ref "a `return` inside a loop needs an `Inhabited` result type (the result \
          is kept in a variable until the loop ends); {t} has none"
    return .lit t (mkApp2 (mkConst ``Inhabited.default [1]) t.carrier inst)

/-- The largest continuation, counted in `AExp` nodes and with no branch, that a statement `if` or
`match` copies into each branch instead of joining after it. -/
def joinCopyLimit : Nat := 8

/-- The place `y.2.2…2.1` of component `j` of `y : (h, (t₀, (t₁, … ())))`. -/
def tupCompPlace (y : Name) (h : STy) (tys : List STy) (j : Nat) : SPlace :=
  let t := tupX tys
  let p0 := SPlace.field (.var y .missing) (mkApp2 (mkConst ``Lens.snd) h.toTy t.toTy) 1 t
    .missing
  go p0 tys j
where
  go (p : SPlace) : List STy → Nat → SPlace
    | [], _ => p
    | t :: ts, 0 => .field p (mkApp2 (mkConst ``Lens.fst) t.toTy (tupX ts).toTy) 0 t .missing
    | t :: ts, j + 1 => go (.field p (mkApp2 (mkConst ``Lens.snd) t.toTy (tupX ts).toTy) 1
        (tupX ts) .missing) ts j

/-- A type whose values take one word. A join copies the variables of such types. -/
def STy.slotSized : STy → Bool
  | .u64 | .bool | .unit | .qty .. => true
  | t => t.isU8

/-- The size budget of a statement `if` or `match` with the rest of its block, in `AExp` nodes. -/
def stmtBudget : Nat := 100000

/-- Refuse a statement whose translation exceeds `stmtBudget`. -/
def checkBudget (ref : Syntax) (r : AExp × STy) : M (AExp × STy) := do
  let n := r.1.size.1
  if n > stmtBudget then
    throwErrorAt ref "this statement and the rest of its block translate to {n} nodes, more than \
      the limit of {stmtBudget}: split the function into smaller ones"
  return r

/-- A statement `if` or `match` followed by the rest of its block `next`. `stmt j c false` builds
the statement in the context `c` with `next` at the end of each branch, and `stmt j c true` puts
the end of a joined branch there, which is `()`, or `false` when the statement jumps.

A continuation that branches or is larger than `joinCopyLimit` is elaborated once, after a join
`let y := (let z' := z; …; stmt; (v, (z', …))); z := y.2.1; …; next`, where `z, …` are the outer
variables the statement writes. The value of a `let` writes nothing bound outside it, so the
statement writes the copies `z'` and hands their final values back in a tuple, and they are
assigned to `z, …` before the rest. A statement that jumps is joined the same way. Inside it a
jump sets its flags and ends the statement with `v = true`, a branch that continues ends with
`v = false`, and after the join `if y.1 then e else next` takes the jump. Here `e` is the end of
the loop's iteration, the variable `rv` that a `return` outside a loop sets before the join, or
`true` in an enclosing joined statement. A small continuation, or a statement that writes a
reference or a linear variable or moves a linear variable, is copied into each branch instead. -/
def joinStmt (j : DoJ) (ctx : Ctx) (ref : Syntax) (jumping : Bool)
    (stmt : DoJ → Ctx → Bool → M (AExp × STy)) (next : M (AExp × STy)) : M (AExp × STy) := do
  let n0 ← get
  let s0 ← Term.saveState
  let copy : M (AExp × STy) := do set n0; s0.restore; checkBudget ref (← stmt j ctx false)
  -- For a statement that jumps, where its jumps go and the variable of a `return` outside a loop.
  let (jj, rv?) ← if !jumping || j.join?.isSome then pure (j, none) else
    if j.loop?.isSome then pure ({ j with join? := some none }, none) else do
      let some rt := j.ret? | return ← copy
      let d? ← try some <$> defaultAtom ref rt catch _ => pure none
      let some d := d? | return ← copy
      let rv ← fresh
      pure ({ j with join? := some (some rv) }, some (rv, rt, d))
  let ctxS := match rv? with
    | some (rv, rt, _) => { name := rv, ty := rt, kind := .ownMut : Local } :: ctx
    | none => ctx
  -- The outer variables the statement writes.
  let s1 ← Term.saveState
  -- A statement that can only be copied may fail to elaborate as a joined one.
  let some (sa, _) ← try some <$> stmt jj ctxS true catch _ => pure none
    | return ← copy
  s1.restore
  let names := sa.writes.foldl (fun l z =>
    if l.contains z || (lookupVar ctxS z).isNone then l else l ++ [z]) []
  let outer ← names.mapM fun z => do
    let some l := lookupVar ctxS z | throwErrorAt ref "internal error: unbound `{z}`"
    pure l
  if outer.any (fun l => l.ty.linear || l.kind != .ownMut) ||
      ctx.any (fun l => l.ty.linear && !(sa.uses l.name matches .n 0)) then
    return ← copy
  let (ka, kt) ← next
  let (sz, br) := ka.size
  if !br && sz ≤ joinCopyLimit then return ← copy
  -- One variable larger than a word is written in place, through a `&mut` borrow `r` of it
  -- around the statement, and the others are copied.
  let big : Option Local := match outer.filter (fun l => !l.ty.slotSized) with
    | [b] => some b
    | _ => none
  let outer : List Local := match big with
    | some b => outer.filter (fun l => l.name != b.name)
    | none => outer
  let rb? ← big.mapM fun b => do
    pure ({ name := ← fresh, src := b.srcName, ty := b.ty, kind := .mut,
            len? := placeLen? ctxS (.var b.name .missing) } : Local)
  -- The statement again, writing the copies.
  let copies ← outer.mapM fun l => do pure (l, { l with name := ← fresh, src := l.srcName })
  let ctx' := rb?.toList ++ copies.map (·.2) ++ ctxS
  let (sa, _) ← stmt jj ctx' true
  let carried := copies.map fun (_, c) => (c.name, c.ty)
  let h : STy := if jumping then .bool else .unit
  let sa ← mapTail sa h fun a => tupleE h a carried
  let sa := copies.foldr (fun (l, c) e => .let_ c.name .missing c.ty (.atom (.var l.name .missing)) e) sa
  let y ← fresh
  let tys := carried.map (·.2)
  -- After the join, the jump or the rest.
  let ka ← if !jumping || (← doMutant "jump-join-lost") then pure ka else do
    let tail : AExp := match j.join?, j.loop?, rv? with
      | some _, _, _ => .atom (boolAtom true)
      | none, some l, _ => endOf l
      | none, none, some (rv, _, _) => .atom (.var rv .missing)
      | none, none, none => ka
    let f ← fresh
    let fp := SPlace.field (.var y .missing) (mkApp2 (mkConst ``Lens.fst) h.toTy (tupX tys).toTy) 0
      h .missing
    pure (.let_ f .missing .bool (.read ref fp .bool) (.ite ref (.var f .missing) tail ka))
  let back ← if ← doMutant "join-lost" then pure ka else
    (outer.zipIdx).foldrM (init := ka) fun (l, j) k => do
      let v ← fresh
      return .let_ v .missing l.ty (.read ref (tupCompPlace y h tys j) l.ty)
        (.assign ref (.var l.name .missing) l.ty (.var v .missing) k)
  let u := STy.pair h (tupX tys)
  let e ← match big, rb? with
    | some b, some rb =>
      let body ← mapTail sa u fun a => pure (mkPairE u b.ty a (.var rb.name .missing))
      pure (AExp.borrow ref true (.var b.name .missing) b.ty rb.name ref body u y back)
    | _, _ => pure (AExp.let_ y ref u sa back)
  let e := match rv? with
    | some (rv, rt, d) => .let_ rv .missing rt (.atom d) e
    | none => e
  checkBudget ref (e, kt)

/-! ## Elaboration from syntax -/

set_option maxHeartbeats 4000000 in
mutual

/-- Elaborate an operand to an atom, let-binding it to a fresh temporary if it is compound. -/
partial def elabAtom (ctx : Ctx) (stx : Syntax) (exp? : Option STy) : M (Binds × SAtom × STy) := do
  match stx with
  | `(($e)) => elabAtom ctx e exp?
  | `($n:num) =>
    let v := n.getNat
    -- A byte literal where a `UInt8` is expected, as for the elements of a byte buffer.
    if let some t@(.other _ c _ _) := exp? then
      if c.isConstOf ``UInt8 then
        unless v < 256 do throwErrorAt stx "literal {v} does not fit in UInt8"
        return (#[], .lit t (toExpr (UInt8.ofNat v)), t)
    unless v < 2 ^ 64 do throwErrorAt stx "literal {v} does not fit in UInt64"
    expect stx exp? .u64
    return (#[], .lit .u64 (toExpr (UInt64.ofNat v)), .u64)
  | `(()) =>
    expect stx exp? .unit
    return (#[], .lit .unit (mkConst ``Unit.unit), .unit)
  | `($x:ident) =>
    if let some l := lookupLocal ctx x.getId then
      expect stx exp? l.ty
      return (#[], .var l.name stx, l.ty)
    if let some a := viewLen? ctx x.getId then
      expect stx exp? .u64
      return (#[], (match a with | .var n _ => .var n stx | a => a), .u64)
    if x.getId == `true || x.getId == `false then
      expect stx exp? .bool
      return (#[], .lit .bool (toExpr (x.getId == `true)), .bool)
    -- A size variable of a generic definition, as a word.
    if let some d := (← getLCtx).findFromUserName? x.getId then
      if (← instantiateMVars d.type) == Lean.mkConst ``Nat then
        expect stx exp? .u64
        return (#[], .lit .u64 (mkApp (Lean.mkConst ``UInt64.ofNat) d.toExpr), .u64)
    bindCompound
  | _ => bindCompound
where
  bindCompound : M (Binds × SAtom × STy) := do
    -- `KiB e` and `q.val` are atoms, which are erased and need no temporary.
    if let some (bs, .atom a, t) ← elabQty? ctx stx then
      expect stx exp? t
      return (bs, a, t)
    let (a, t) ← elabE ctx stx exp?
    let x ← fresh
    return (#[(x, t, a)], .var x stx, t)

/-- Elaborate a list of operands, left to right, with the given expected types. -/
partial def elabAtoms (ctx : Ctx) (stxs : List Syntax) (tys : List (Option STy)) :
    M (Binds × List (SAtom × STy)) := do
  let mut bs : Binds := #[]
  let mut out := #[]
  for s in stxs, t in tys do
    let (b, a, ty) ← elabAtom ctx s t
    bs := bs ++ b
    out := out.push (a, ty)
  return (bs, out.toList)

/-- An index atom that the elaborator can prove in range, which is a literal below `n` or the
counter of an enclosing loop whose bound is at most `n`. -/
partial def staticIndex (ctx : Ctx) (i : Syntax) (n : Expr) : M (Binds × SAtom) := do
  let (bs, a, _) ← elabAtom ctx i (some .u64)
  let ok : Bool := match i.isNatLit?, STy.natOf? n with
    | some k, some n => decide (k < n)
    | some _, none => false
    | none, _ => match a with
      | .var x _ => (lookupVar ctx x).any fun l => l.bound.any fun b =>
        -- A loop `for i in 0...n` over a size variable indexes `Arr T n`.
        match STy.natOf? b, STy.natOf? n with
        | some b, some n => decide (b ≤ n)
        | _, _ => b == n
      | .lit _ _ => false
  unless ok do
    throwErrorAt i "cannot show that this index is below {n}: use a literal below {n} or the \
      counter of a loop `for i in 0...N` with N ≤ {n}; otherwise write `a[i]!` (an obligation of \
      `f.safe`) or `a[i]?` (checked, a Result)"
  return (bs, a)

/-- Elaborate a place. -/
partial def elabPlace (ctx : Ctx) (stx : Syntax) : M (Binds × SPlace × STy) := do
  match stx with
  | `(($e)) => elabPlace ctx e
  | `($x:ident) => let (p, t) ← placeOfIdent ctx x; return (#[], p, t)
  | `($e.$f:ident) =>
    let (bs, p, t) ← elabPlace ctx e
    let (p, t) ← fieldOf p t f.getId f
    return (bs, p, t)
  | `($e.$i:fieldIdx) =>
    let (bs, p, t) ← elabPlace ctx e
    let (p, t) ← fieldOf p t (Name.mkSimple (toString (i.raw.isFieldIdx?.getD 0))) i
    return (bs, p, t)
  | `($a[$i]) =>
    let (bs, p, t) ← elabPlace ctx a
    match t with
    | .arr e n =>
      let (bi, ia) ← staticIndex ctx i n
      return (bs ++ bi, .index p ia stx, e)
    | .slots _ _ => throwErrorAt stx "a `Slots` cell is accessed with `s[i]!` (the cell must be \
        full: an obligation), or tested with `s.full? i`"
    | .slice e _ =>
      -- A slice element `s[i]` is the same cell as `s[i]!`. Its obligation is that the cell is
      -- full, which follows from `i < s.len` because the view of `a[lo..hi]` holds `len` elements.
      let (bi, ia, _) ← elabAtom ctx i (some .u64)
      return (bs ++ bi, .slot p ia stx, e)
    | _ => throwErrorAt a "`[…]` needs an array, `Slots` or slice, but this has type {t}"
  | `($a[$i]!) =>
    let (bs, p, t) ← elabPlace ctx a
    let some (e, _, sel) := selOf t
      | throwErrorAt a "`[…]!` needs an array, `Slots` or slice, but this has type {t}"
    let (bi, ia, _) ← elabAtom ctx i (some .u64)
    let p := if sel == `index then SPlace.index p ia stx
      else if sel == `slot then .slot p ia stx else .elem p ia stx
    return (bs ++ bi, p, e)
  | `($f:ident $i $j) =>
    if f.getId.components.getLast? == some `pair! then
      let (p, t) ← placeOfIdent ctx (mkIdentFrom f (f.getId.components.dropLast.foldl (· ++ ·) .anonymous))
      let e ← match t with
        | .arr e _ | .slice e _ => pure e
        | _ => throwErrorAt f "`pair!` needs an array or a slice, but this has type {t}"
      let (b, as) ← elabAtoms ctx [i, j] [some .u64, some .u64]
      return (b, .pair2 p as[0]!.1 as[1]!.1 stx, .pair e e)
    throwErrorAt stx "expected a place: a variable, `p.f`, `a[i]`, `a[i]!`, `s[i]!`, `a[lo:hi]` \
      or `a.pair! i j`"
  | `(($x, $y)) =>
    -- The pair borrow `(a[i], a[j])`, or `a.pair! i j`, takes two elements of one array together.
    let elemOf (z : Syntax) : M (Syntax × Syntax) := match z with
      | `($b[$k]) | `($b[$k]!) => pure (b, k)
      | _ => throwErrorAt z "a pair of places `(a[i], a[j])` needs two elements of one array"
    let (b₁, i) ← elemOf (unparen x)
    let (b₂, j) ← elemOf (unparen y)
    unless b₁.prettyPrint.pretty == b₂.prettyPrint.pretty do
      throwErrorAt y "a pair of places `(a[i], a[j])` needs two elements of the same array"
    let (bs, p, t) ← elabPlace ctx b₁
    -- Two cells of a slice view, `Place.pair2S`. The view must be a variable.
    let e ← match t, p with
      | .arr e _, _ => pure e
      | .slice e _, .var .. => pure e
      | .slice _ _, _ => throwErrorAt b₁ "a pair of two elements of a slice needs the slice \
          itself (a slice parameter or binder), not a place inside another value"
      | _, _ => throwErrorAt b₁ "a pair `(a[i], a[j])` needs an array or a slice, but this has \
          type {t}"
    let (b, as) ← elabAtoms ctx [i, j] [some .u64, some .u64]
    return (bs ++ b, .pair2 p as[0]!.1 as[1]!.1 stx, .pair e e)
  | _ => elabPlaceRange ctx stx

/-- The places that `elabPlace` does not match by a quotation pattern, which are the slices
`a[lo:hi]` and `a[lo..hi]`. -/
partial def elabPlaceRange (ctx : Ctx) (stx : Syntax) : M (Binds × SPlace × STy) := do
  if stx.getKind == `Array.«term__[_:_]» || stx.getKind == ``mpRange then
    let a := stx[0]; let lo := stx[2]; let hi := stx[4]
    let (bs, p, t) ← elabPlace ctx a
    -- A sub-slice of a slice view, `Place.rangeS`, whose view must be a variable. Its obligation
    -- is that the cells below `hi` are full, which is `hi ≤ s.len`.
    let (e, n) ← match t, p with
      | .arr e n, _ => pure (e, n)
      | .slice e n, .var .. => pure (e, n)
      | .slice _ _, _ => throwErrorAt a "a sub-slice needs the slice itself (a slice parameter \
          or binder), not a place inside another value"
      | _, _ => throwErrorAt a "a slice `a[lo..hi]` needs an array or a slice, but this has \
          type {t}"
    let (b₁, loA, _) ← elabAtom ctx lo (some .u64)
    match lo.isNatLit?, hi.isNatLit? with
    | some l, some h =>
      unless l ≤ h do throwErrorAt stx "empty or reversed range"
      return (bs ++ b₁, .range p loA (.lit .u64 (toExpr (UInt64.ofNat (h - l)))) stx, .slice e n)
    | _, _ =>
      let (b₂, hiA, _) ← elabAtom ctx hi (some .u64)
      let len ← fresh
      let lenE := AExp.prim ⟨``Prim.sub, [.u64, .u64], .u64⟩ [hiA, loA]
      return (bs ++ b₁ ++ b₂ ++ #[(len, .u64, lenE)], .range p loA (.var len .missing) stx,
        .slice e n)
  throwErrorAt stx "expected a place: a variable, `p.f`, `a[i]`, `a[i]!`, `s[i]!`, \
    `a[lo:hi]` or `a.pair! i j`"

/-- A slice `a[lo:hi]` of a byte array `Arr U8 n`, used as an extern's buffer. -/
partial def elabByteSlice (ctx : Ctx) (stx : Syntax) : M (Binds × SPlace × Expr) := do
  let (bs, p, t) ← elabPlace ctx stx
  if let .slice _ _ := t then
    unless p matches .range .. do
      throwErrorAt stx "a slice view (a slice parameter or borrow) is not an extern buffer yet: \
        Core's extern buffer `Buf.slice` is a slice `a[lo..hi]` of a byte array place"
  let .range q .. := p | throwErrorAt stx "an extern buffer is a slice `a[lo:hi]` of a byte array"
  if let some (STy.slice _ _) := (lookupVar ctx q.root).map (·.ty) then
    if q matches .var .. then
      throwErrorAt stx "a sub-slice of a slice view is not an extern buffer yet: Core's extern \
        buffer `Buf.slice` is a slice `a[lo..hi]` of a byte array place"
  let .slice e n := t | throwErrorAt stx "an extern buffer is a slice `a[lo:hi]` of a byte array"
  unless (match e with | .other _ c _ _ => c.isConstOf ``UInt8 | _ => false) do
    throwErrorAt stx "an extern buffer is a slice of a byte array (`Arr U8 n`), but its \
      elements have type {e}"
  return (bs, p, n)

/-- Read a place, copying its value. -/
partial def readPlace (ctx : Ctx) (stx : Syntax) (exp? : Option STy) : M (AExp × STy) := do
  let (bs, p, t) ← elabPlace ctx stx
  expect stx exp? t
  if t.linear then
    throwErrorAt stx "cannot copy the linear value of type {t} out of a place (it would be used \
      twice); move a whole variable, or `take!` it out of a `Slots`"
  return (wrap bs (.read stx p t), t)

/-- Elaborate a term of the surface language to named ANF, checking it against `exp?`. -/
partial def elabE (ctx : Ctx) (stx : Syntax) (exp? : Option STy) : M (AExp × STy) := do
  if let some (bs, e, t) ← elabQty? ctx stx then
    expect stx exp? t
    return (wrap bs e, t)
  match stx with
  | `(($e)) => elabE ctx e exp?
  | `(($e : $ty)) =>
    let t ← elabTy ty
    expect stx exp? t
    elabE ctx e (some t)
  | `($_:num) | `(()) =>
    let (_, a, t) ← elabAtom ctx stx exp?
    return (.atom a, t)
  | `($x:ident) => elabIdent ctx stx x exp?
  | `(let $x:ident := $v; $b) => elabLet ctx x none v (elabE · b exp?) .own
  | `(let $x:ident : $ty := $v; $b) => elabLet ctx x (some ty) v (elabE · b exp?) .own
  | `(let _ := $v; $b) =>
    let x ← fresh
    elabLet ctx (mkIdentFrom v x) none v (elabE · b exp?) .own
  | `(if $c then $t else $e) =>
    let (bs, ca, _) ← elabAtom ctx c (some .bool)
    let (ta, tt) ← elabE ctx t exp?
    let (ea, _) ← elabE ctx e (some tt)
    return (wrap bs (.ite stx ca ta ea), tt)
  | `($a[$i]?) =>
    let (bs, p, t) ← elabPlace ctx (← `($a[$i]!))
    unless p.checkable do
      throwErrorAt stx "`[…]?` has no checked form on a `Slots` cell or a slice element: occupancy \
        is not observable at run time (doc/design/arenas.md (Slots)); write `[…]!` and prove the obligation"
    expect stx exp? (.result .unit t)
    if t.linear then throwErrorAt stx "cannot copy the linear value of type {t} out of a place"
    let g ← fresh; let e ← fresh; let o ← fresh; let v ← fresh
    let rt := STy.result .unit .unit
    return (wrap bs (.let_ g .missing rt (.guard stx (.valid p))
      (.match_ stx .unit .unit (.var g .missing) e (.err .unit t (.lit .unit (mkConst ``Unit.unit)))
        o (.let_ v .missing t (.read stx p t) (.ok .unit t (.var v .missing))))), .result .unit t)
  | `($e.$f:ident) =>
    -- `e.toUInt64`, also after fields, where `e.g.toUInt8.toUInt64` is `e` with the identifier
    -- `g.toUInt8.toUInt64`.
    match f.getId.components.reverse with
    | c :: rest =>
      if c == `toUInt64 || c == `toUInt8 then
        let base ← if rest.isEmpty then pure e.raw
          else `($e.$(mkIdentFrom f (rest.reverse.foldl (· ++ ·) .anonymous)):ident)
        elabConv ctx stx base c exp?
      else readPlace ctx stx exp?
    | [] => readPlace ctx stx exp?
  | `($_[$_]) | `($_[$_]!) | `($_.$_:fieldIdx) =>
    readPlace ctx stx exp?
  | `($f:ident $args*) => elabApp ctx stx f args exp?
  | `(match $s:term with $alts:matchAlt*) => elabMatch ctx stx s alts exp? (elabE · · ·)
  | `(!$c) =>
    let (bs, as) ← elabAtoms ctx [c] [some .bool]
    expect stx exp? .bool
    return (wrap bs (.prim ⟨``Prim.not, [.bool], .bool⟩ (as.map (·.1))), .bool)
  | `(~~~$c) =>
    let (bs, as) ← elabAtoms ctx [c] [some .u64]
    expect stx exp? .u64
    return (wrap bs (.prim ⟨``Prim.bnot, [.u64], .u64⟩ (as.map (·.1))), .u64)
  | `(⟨$args,*⟩) =>
    let some t := exp? | throwErrorAt stx "cannot infer the type of `⟨…⟩`; add a type ascription"
    elabPositional ctx stx t args.getElems
  | `(#v[$args,*]) =>
    let args := args.getElems
    let et? := match exp? with | some (.arr e _) => some e | _ => none
    let (bs, as) ← elabAtoms ctx (args.toList.map (·.raw)) (args.toList.map fun _ => et?)
    let e := (as.head?.map (·.2)).getD (et?.getD .u64)
    for (_, t) in as, s in args do unless t == e do
      throwErrorAt s "type mismatch: expected {e}, but this has type {t}"
    let t := STy.arr e (toExpr args.size)
    expect stx exp? t
    return (wrap bs (.mk (mkApp2 (mkConst ``Ctor.vec) e.toTy (toExpr args.size))
      (List.replicate args.size e) t (as.map (·.1))), t)
  | _ => elabEOther ctx stx exp?

/-- The forms that `elabE` does not match by a quotation pattern: loops, `let mut`, assignment,
references, structure instances, `.c` constructors and binary operators. They are a function of
their own because a quotation `match` copies its fallback branch into every failure path, which
makes the compiled code of one large function very large. -/
partial def elabEOther (ctx : Ctx) (stx : Syntax) (exp? : Option STy) : M (AExp × STy) := do
  match stx.getKind with
  | `Array.«term__[_:_]» | ``mpRange => readPlace ctx stx exp?
  -- A nested block `(do …)`, in which `return` is not supported.
  | ``Lean.Parser.Term.do => elabSeq {} ctx (doSeqItems stx[1]) none exp?
  | ``mpRefMut | ``mpRefShr =>
    throwErrorAt stx "a reference `&p` / `&mut p` can only be passed to a function or bound by \
      `let r := &mut p; …`"
  | ``Lean.Parser.Term.structInst => elabStructInst ctx stx exp?
  | ``Lean.Parser.Term.dotIdent => elabDotCtor ctx stx stx[1] #[] exp?
  | ``Lean.Parser.Term.app =>
    if stx[0].getKind == ``Lean.Parser.Term.dotIdent then
      elabDotCtor ctx stx stx[0][1] stx[1].getArgs exp?
    else throwErrorAt stx "unsupported syntax in `mp def`"
  | _ =>
  if stx.isStrLit?.isSome then
    throwErrorAt stx "a string literal can only be passed to a `Bytes` parameter of an extern"
  -- Binary operators `a op b`.
  if stx.getNumArgs == 3 && stx[1].isAtom then
    let op := stx[1].getAtomVal
    -- `a && b` and `a || b` short-circuit as in Lean, so `b` is evaluated, and its obligations
    -- such as those of `s[i]` must hold, only when `a` does not decide the result. A right
    -- operand whose evaluation has no obligations and no effects keeps the strict primitive.
    if op == "&&" || op == "||" then
      let (bs₁, a, _) ← elabAtom ctx stx[0] (some .bool)
      let (bs₂, b, _) ← elabAtom ctx stx[2] (some .bool)
      expect stx exp? .bool
      if bs₂.all (·.2.2.isInert) then
        let p : PrimInfo := ⟨if op == "&&" then ``Prim.and else ``Prim.or, [.bool, .bool], .bool⟩
        return (wrap (bs₁ ++ bs₂) (.prim p [a, b]), .bool)
      let rhs := wrap bs₂ (.atom b)
      let lit (v : Bool) : AExp := .atom (.lit .bool (toExpr v))
      return (wrap bs₁ (if op == "&&" then .ite stx a rhs (lit false) else .ite stx a (lit true) rhs),
        .bool)
    -- The checked forms, such as `a +? b`.
    if (checkedOps.lookup op).isSome then
      let (bs, a, b, t, _) ← elabOperands ctx stx[0] stx[2] (op := op) fun s t => do
        unless t == .u64 || t.isU8 do
          throwErrorAt s "`{op}` needs UInt64 or UInt8 operands, but this has type {t}"
      expect stx exp? (.result .unit t)
      let some e ← checkedAExp fresh op t (if t.isU8 then some (zext8Info t, trunc8Info t) else none)
        a b | throwErrorAt stx "internal error: checked operator {op}"
      return (wrap bs e, .result .unit t)
    if let some p := binOps.lookup op then
      unless p.ins == [.u64, .u64] do
        let (bs, as) ← elabAtoms ctx [stx[0], stx[2]] (p.ins.map some)
        expect stx exp? p.out
        return (wrap bs (.prim p (as.map (·.1))), p.out)
      let (bs, a, b, t, tb) ← elabOperands ctx stx[0] stx[2] (op := op) fun s t => do
        unless t == .u64 || t.isU8 || t.isQty do
          throwErrorAt s "`{op}` needs UInt64 or UInt8 operands, but this has type {t}"
      if t.isQty || tb.isQty then
        let out ← ofExceptAt stx (qtyBinOp op t tb)
        expect stx exp? out
        return (wrap bs (.prim p [a, b]), out)
      if t == .u64 then
        expect stx exp? p.out
        return (wrap bs (.prim p [a, b]), p.out)
      -- For bytes, both operands are widened with `zext8`, the operation is done on words, and an
      -- arithmetic result is narrowed to its low byte with `trunc8`, which is the byte
      -- operation's result. `+ - *` wrap modulo 2^8 because 2^8 divides 2^64, and `/ %` and the
      -- bitwise operations of bytes below 2^8 stay below 2^8.
      if op == "<<<" || op == ">>>" then
        throwErrorAt stx "shifts of UInt8 are not in the language (a UInt8 shift takes its \
          amount mod 8): widen with `.toUInt64`, shift, and narrow with `.toUInt8`"
      let (zb, x, y) ← widen8 t a b
      -- For `+ - *` of bytes the word operation wraps and the narrowing carries the obligation.
      let (p, nuw) := bytePrim p
      let e := AExp.prim p [x, y]
      if p.out == .bool then
        expect stx exp? .bool
        return (wrap (bs ++ zb) e, .bool)
      expect stx exp? t
      let z ← fresh
      let narrow : PrimInfo := if nuw then { trunc8Info t with con := ``Prim.trunc8Nuw } else trunc8Info t
      return (wrap (bs ++ zb ++ #[(z, .u64, e)]) (.prim narrow [.var z .missing]), t)
    if op == "==" || op == "!=" || op == "≠" then
      let (bs, a, b, t, tb) ← elabOperands ctx stx[0] stx[2] (op := op) fun _ _ => pure ()
      expect stx exp? .bool
      if t.isQty || tb.isQty then
        discard <| ofExceptAt stx (qtyBinOp op t tb)
        let p := if op == "==" then ``Prim.eq else ``Prim.ne
        return (wrap bs (.prim ⟨p, [.u64, .u64], .bool⟩ [a, b]), .bool)
      if t.isU8 then
        let (zb, x, y) ← widen8 t a b
        let p := if op == "==" then ``Prim.eq else ``Prim.ne
        return (wrap (bs ++ zb) (.prim ⟨p, [.u64, .u64], .bool⟩ [x, y]), .bool)
      let p : PrimInfo ← match t with
        | .u64 => pure ⟨``Prim.eq, [.u64, .u64], .bool⟩
        | .bool => pure ⟨``Prim.beq, [.bool, .bool], .bool⟩
        | _ => throwErrorAt stx "equality is only available on UInt64, UInt8 and Bool, not {t}"
      let e := AExp.prim p [a, b]
      if op == "==" then return (wrap bs e, .bool)
      if t == .u64 then
        return (wrap bs (.prim ⟨``Prim.ne, [.u64, .u64], .bool⟩ [a, b]), .bool)
      let x ← fresh
      return (wrap bs (.let_ x .missing .bool e
        (.prim ⟨``Prim.not, [.bool], .bool⟩ [.var x .missing])), .bool)
  throwErrorAt stx "unsupported syntax in `mp def`"

/-- The two operands of a binary operator `op`, which have one type, and their types. The type is
inferred from the operand that is not a numeric literal, so `32 == s[i]` compares bytes. With a
quantity the types may differ, as in `q * 3`, `n * q` or a unit mismatch that `qtyBinOp`
reports, and a numeral next to a quantity is a `UInt64`. -/
partial def elabOperands (ctx : Ctx) (l r : Syntax) (check : Syntax → STy → M Unit)
    (op := "") : M (Binds × SAtom × SAtom × STy × STy) := do
  let isLit (s : Syntax) := (unparen s).isNatLit?.isSome
  let other (t : STy) (s : Syntax) : Option STy :=
    if t.isQty then (if isLit s then some .u64 else none)
    else if t == .u64 && (op == "*" || op == "*!") && !isLit s then none else some t
  let same (t tb : STy) (s : Syntax) : M Unit := do
    unless t.isQty || tb.isQty do expect s (some t) tb
  if isLit l && !isLit r then
    let (bs₂, b, t) ← elabAtom ctx r none
    check r t
    let (bs₁, a, ta) ← elabAtom ctx l (other t l)
    return (bs₁ ++ bs₂, a, b, ta, t)
  let (bs₁, a, t) ← elabAtom ctx l none
  check l t
  let (bs₂, b, tb) ← elabAtom ctx r (other t r)
  same t tb r
  return (bs₁ ++ bs₂, a, b, t, tb)

/-- The quantity forms, which are erased to `UInt64`. They are a count `U e` of a unit `U`, the
count `q.val`, and the conversions `q.to V`, `q.to? V`, `q.toFloor V` and `q.toCeil V`. Any other
syntax gives `none`. -/
partial def elabQty? (ctx : Ctx) (stx : Syntax) : M (Option (Binds × AExp × STy)) := do
  -- The receiver and method of `q.m args` or `(e).m args`.
  let recv? (f : Syntax) : Option (Syntax × Name) :=
    if f.isIdent then
      let cs := f.getId.components
      if cs.length ≥ 2 && (lookupLocal ctx cs.head!).isSome then
        some (mkIdentFrom f (cs.dropLast.foldl (· ++ ·) .anonymous), cs.getLast!)
      else none
    else if f.getKind == ``Lean.Parser.Term.proj && f[2].isIdent then some (f[0], f[2].getId)
    else none
  let (f, args) :=
    if stx.getKind == ``Lean.Parser.Term.app then (stx[0], stx[1].getArgs) else (stx, #[])
  match recv? f with
  | some (q, `val) =>
    unless args.isEmpty do return none
    let (bs, a, t) ← elabAtom ctx q none
    unless t.isQty do return none
    return some (bs, .atom a, .u64)
  | some (q, meth) =>
    unless qtyMethods.contains meth && args.size == 1 do return none
    let (bs, a, t) ← elabAtom ctx q none
    unless t.isQty do
      throwErrorAt q "`.{meth}` converts quantities, but this has type {t}"
    let some tgt ← unitSTy? args[0]!
      | throwErrorAt args[0]! "`.{meth}` needs a unit (declared by `mp unit`)"
    let c ← ofExceptAt stx (qtyConv meth t tgt)
    return some (bs, ← qtyConvE fresh c a tgt, qtyConvTy meth tgt)
  | none =>
    unless f.isIdent && args.size == 1 && (lookupLocal ctx f.getId).isNone do return none
    let some t ← unitSTy? f | return none
    let (bs, a, _) ← elabAtom ctx args[0]! (some .u64)
    return some (bs, .atom a, t)

/-- Widen two byte atoms to words with `zext8`, binding each to a fresh temporary. -/
partial def widen8 (u8 : STy) (a b : SAtom) : M (Binds × SAtom × SAtom) := do
  let x ← fresh; let y ← fresh
  return (#[(x, .u64, .prim (zext8Info u8) [a]), (y, .u64, .prim (zext8Info u8) [b])],
    .var x .missing, .var y .missing)

/-- The conversions `e.toUInt64`, which widens a `UInt8` with `Prim.zext8` and is the identity on
`UInt64`, and `e.toUInt8`, which takes the low byte of a `UInt64` with `Prim.trunc8` and is the
identity on `UInt8`. On any other type `e.toUInt64` is read as a field of a place. -/
partial def elabConv (ctx : Ctx) (stx base : Syntax) (conv : Name) (exp? : Option STy) :
    M (AExp × STy) := do
  let (bs, a, t) ← elabAtom ctx base none
  if conv == `toUInt64 then
    if t == .u64 then expect stx exp? .u64; return (wrap bs (.atom a), .u64)
    if t.isU8 then expect stx exp? .u64; return (wrap bs (.prim (zext8Info t) [a]), .u64)
  else
    if t.isU8 then expect stx exp? t; return (wrap bs (.atom a), t)
    if t == .u64 then
      let u8 ← u8STy
      expect stx exp? u8
      return (wrap bs (.prim (trunc8Info u8) [a]), u8)
  match t with
  | .adt .. | .pair .. => readPlace ctx stx exp?
  | _ => throwErrorAt stx "`.{conv}` converts between UInt8 and UInt64, not from {t}"

/-- An identifier, which is a local, a field path of a local that is read, `true` or `false`, a
constructor without a field, or a call of a function without parameters. -/
partial def elabIdent (ctx : Ctx) (stx : Syntax) (x : TSyntax `ident) (exp? : Option STy) :
    M (AExp × STy) := do
  let n := x.getId
  if (lookupLocal ctx n).isSome || (viewLen? ctx n).isSome || n == `true || n == `false then
    let (_, a, t) ← elabAtom ctx stx exp?
    return (.atom a, t)
  if let some h := n.components.head? then
    if n.components.length ≥ 2 && (lookupLocal ctx h).isSome then
      if let some c := n.components.getLast? then
        if c == `toUInt64 || c == `toUInt8 then
          let base := mkIdentFrom x (n.components.dropLast.foldl (· ++ ·) .anonymous)
          return ← elabConv ctx stx base c exp?
      return ← readPlace ctx stx exp?
  if let some (adt, c) ← resolveCtor n then
    return ← elabCtorApp ctx stx adt c #[] exp?
  if let some r ← elabCtorConst ctx stx x #[] exp? then return r
  if (← resolveEntry x).isNone then
    -- A size variable `n` of a generic definition, as the word `UInt64.ofNat n`.
    if let some d := (← getLCtx).findFromUserName? n then
      if (← instantiateMVars d.type) == Lean.mkConst ``Nat then
        expect stx exp? .u64
        return (.atom (.lit .u64 (mkApp (Lean.mkConst ``UInt64.ofNat) d.toExpr)), .u64)
    throwErrorAt x "unknown variable `{n}`"
  elabApp ctx stx x #[] exp?

/-- `let x := v; b`, with an optional type and `kind` either `let` or `let mut`, and the scoped
borrows `let r := &mut p; b` and `let r := &p; b`. -/
partial def elabLet (ctx : Ctx) (x : TSyntax `ident) (ty? : Option Syntax) (v : Syntax)
    (body : Ctx → M (AExp × STy)) (kind : LKind) : M (AExp × STy) := do
  checkShadow ctx x.getId x
  let v := unparen v
  if v.getKind == ``mpRefMut || v.getKind == ``mpRefShr then
    if ty?.isSome then throwErrorAt v "a borrow takes no type ascription"
    return ← elabBorrow ctx x (v.getKind == ``mpRefMut) v v[1] body
  let vt? ← ty?.mapM elabTy
  let (va, vt) ← elabE ctx v vt?
  let x' ← bindName ctx x.getId
  let (ba, bt) ← body (mkLocal x.getId x' vt kind :: ctx)
  checkOnce x' vt x "let" ba
  return (splice va x' vt ba, bt)

/-- `let r := &mut p; b` or `let r := &p; b`, where the borrow lasts for `b`, the rest of the
block. -/
partial def elabBorrow (ctx : Ctx) (r : TSyntax `ident) (excl : Bool) (ref pStx : Syntax)
    (k : Ctx → M (AExp × STy)) : M (AExp × STy) := do
  let (bs, p, t) ← elabPlace ctx pStx
  if excl then requireMutable ctx p "borrow mutably"
  let r' ← bindName ctx r.getId
  let ctx' := { mkLocal r.getId r' t (if excl then .mut else .shr) with len? := placeLen? ctx p }
    :: ctx
  let (ba, u) ← k ctx'
  let body ← if excl then
      mapTail ba u fun a => pure (mkPairE u t a (.var r' .missing))
    else pure ba
  if excl then checkOnce r' t r "reference" body
  let y ← fresh
  return (wrap bs (.borrow ref excl p t r' r body u y (.atom (.var y .missing))), u)

/-- A constructor application `E.c a` or `S.mk a b`, or a constructor without a field. -/
partial def elabCtorApp (ctx : Ctx) (stx : Syntax) (adt : AdtInfo) (c : Name)
    (args : Array Syntax) (exp? : Option STy) : M (AExp × STy) := do
  -- A parameterised type is taken at the expected type's arguments.
  let t ← if adt.params.isEmpty then pure (STy.adt adt.name adt.lin #[] #[]) else
    match exp? with
    | some t@(.adt n _ _ _) => if n == adt.name then pure t else
        throwErrorAt stx "expected {t}, but `{c}` builds a `{adt.name}`"
    | _ => throwErrorAt stx "the arguments of the parameterised type `{adt.name}` are not known \
        here: give the expected type (`let x : {adt.name} … := …`)"
  let is := match t with | .adt _ _ _ is => is | _ => #[]
  expect stx exp? t
  match adt.kind with
  | .enum vs _ =>
    let some v := vs.find? (·.ctor == c) | throwErrorAt stx "internal error: constructor {c}"
    let mkC := mkAppN (mkConst v.mkC) is
    if v.hasField then
      unless args.size == 1 do throwErrorAt stx "`{c}` takes one argument"
      let pay ← (v.payload.mapExpr (·.instantiateRev is)).refresh
      let (bs, a, _) ← elabAtom ctx args[0]! (some pay)
      return (wrap bs (.mk mkC [pay] t [a]), t)
    unless args.isEmpty do throwErrorAt stx "`{c}` takes no argument"
    return (.mk mkC [.unit] t [.lit .unit (mkConst ``Unit.unit)], t)
  | .struct _ _ => elabPositional ctx stx t args

/-- A struct or pair from its fields in order, as in `S.mk a b` or `⟨a, b⟩`. -/
partial def elabPositional (ctx : Ctx) (stx : Syntax) (t : STy) (args : Array Syntax) :
    M (AExp × STy) := do
  match t with
  | .pair a b =>
    unless args.size == 2 do throwErrorAt stx "a pair has two components"
    let (bs, as) ← elabAtoms ctx args.toList [some a, some b]
    return (wrap bs (mkPairE a b as[0]!.1 as[1]!.1), t)
  | .adt S _ _ is =>
    let some { kind := .struct fs ctorC, .. } := lookupAdt (← getEnv) S
      | throwErrorAt stx "`{S}` is not a struct"
    let fs ← fieldsAt fs is
    let some cc := ctorC
      | throwErrorAt stx "`{S}` has proof fields: it cannot be built in `mp def`"
    requireUnsealed stx S "be built"
    unless args.size == fs.size do
      throwErrorAt stx "`{S}` has {fs.size} field(s), got {args.size}"
    let (bs, as) ← elabAtoms ctx args.toList (fs.toList.map (some ·.ty))
    return (wrap bs (.mk (mkAppN (mkConst cc) is) (fs.toList.map (·.ty)) t (as.map (·.1))), t)
  | _ => throwErrorAt stx "`⟨…⟩` builds a struct or a pair, but the expected type is {t}"

/-- The structure instances `{ x := a, y := b }`, `{ x := a : S }` and `{ p with x := v }`. -/
partial def elabStructInst (ctx : Ctx) (stx : Syntax) (exp? : Option STy) : M (AExp × STy) := do
  let t ← if stx[4].getNumArgs == 2 then elabTy stx[4][1] else
    match exp? with
    | some t => pure t
    | none => throwErrorAt stx "cannot infer the struct type; write `\{ x := a : S }`"
  expect stx exp? t
  let .adt S _ _ is := t | throwErrorAt stx "a struct literal needs a struct type, not {t}"
  let some { kind := .struct fs ctorC, .. } := lookupAdt (← getEnv) S
    | throwErrorAt stx "`{S}` is not a struct"
  let fs ← fieldsAt fs is
  let some cc := ctorC | throwErrorAt stx "`{S}` has proof fields: it cannot be built in `mp def`"
  requireUnsealed stx S "be built"
  -- the given fields
  let mut given : Array (Name × Syntax × Syntax) := #[]
  for f in stx[2][0].getSepArgs do
    let lv := f[0][0]
    let some defn := f[1].getArgs.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
      | throwErrorAt f "expected `field := value`"
    unless fs.any (·.name == lv.getId) do throwErrorAt lv "`{S}` has no field `{lv.getId}`"
    if given.any (·.1 == lv.getId) then throwErrorAt lv "field `{lv.getId}` given twice"
    given := given.push (lv.getId, lv, defn[2])
  let src? := if stx[1].getNumArgs == 2 then some stx[1][0][0] else none
  let mut bs : Binds := #[]
  let mut atoms : Array SAtom := #[]
  for fi in fs do
    match given.find? (·.1 == fi.name) with
    | some (_, _, v) =>
      let (b, a, _) ← elabAtom ctx v (some fi.ty)
      bs := bs ++ b; atoms := atoms.push a
    | none =>
      let some src := src? | throwErrorAt stx "missing field `{fi.name}`"
      let (b, p, st) ← elabPlace ctx src
      unless st == t do throwErrorAt src "type mismatch: expected {t}, but this has type {st}"
      if fi.ty.linear then
        throwErrorAt src "field `{fi.name}` is linear: it cannot be copied from `{src}`"
      let x ← fresh
      bs := bs ++ b ++ #[(x, fi.ty, .read src (.field p (mkAppN (mkConst fi.lens) is) fi.idx fi.ty
        src) fi.ty)]
      atoms := atoms.push (.var x .missing)
  return (wrap bs (.mk (mkAppN (mkConst cc) is) (fs.toList.map (·.ty)) t atoms.toList), t)

/-- `.c a`, a constructor of the expected enum type. -/
partial def elabDotCtor (ctx : Ctx) (stx c : Syntax) (args : Array Syntax) (exp? : Option STy) :
    M (AExp × STy) := do
  let some (.adt E _ _ _) := exp?
    | throwErrorAt stx "cannot infer the type of `.{c.getId}`; write `E.{c.getId}`"
  let some adt := lookupAdt (← getEnv) E | throwErrorAt stx "internal error: {E}"
  elabCtorApp ctx stx adt (E ++ c.getId) args exp?

/-- An application `f a b`. It is `ok` or `err`, an operation on a place such as `s.put! i v`,
`s.take! i`, `s.vacant? i` or `s.full? i`, a constructor, `Vector.replicate`, `Slots.empty`, a
call of an earlier `mp def`, or an extern call. -/
partial def elabApp (ctx : Ctx) (stx : Syntax) (f : TSyntax `ident) (args : Array Syntax)
    (exp? : Option STy) : M (AExp × STy) := do
  let fname := f.getId
  if fname == `ok || fname == `err then
    if let some t := exp? then
      if !(t matches .result _ _) then
        throwErrorAt stx "type mismatch: expected {t}, but `{fname} …` is a Result"
    let some (.result ε α) := exp?
      | throwErrorAt stx "cannot infer the Result type of `{fname}`; add a type ascription \
          `(… : Result ε α)`"
    unless args.size == 1 do throwErrorAt stx "`{fname}` takes one argument"
    let (bs, a, _) ← elabAtom ctx args[0]! (some (if fname == `ok then α else ε))
    return (wrap bs (if fname == `ok then .ok ε α a else .err ε α a), .result ε α)
  if (lookupLocal ctx fname).isSome then
    throwErrorAt f "`{fname}` is a variable, not a function"
  -- Operations on places.
  let comps := fname.components
  if comps.length ≥ 2 && (lookupLocal ctx comps.head!).isSome then
    let meth := comps.getLast!
    let pid := mkIdentFrom f (comps.dropLast.foldl (· ++ ·) .anonymous)
    let (p, pt) ← placeOfIdent ctx pid
    let .slots t _ := pt
      | throwErrorAt f "`{meth}` is an operation on `Slots`, but `{pid.getId}` has type {pt}"
    let arity := if meth == `put! then 2 else 1
    unless args.size == arity do throwErrorAt stx "`{meth}` takes {arity} argument(s)"
    let (bi, ia, _) ← elabAtom ctx args[0]! (some .u64)
    match meth.toString with
    | "put!" =>
      requireMutable ctx p "write"
      let (bv, va, _) ← elabAtom ctx args[1]! (some t)
      expect stx exp? .unit
      return (wrap (bi ++ bv) (.put stx p ia va (.atom (.lit .unit (mkConst ``Unit.unit)))), .unit)
    | "take!" =>
      requireMutable ctx p "write"
      expect stx exp? t
      let x ← fresh
      return (wrap bi (.take stx p ia x stx t (.atom (.var x .missing))), t)
    | "vacant?" | "full?" =>
      throwErrorAt f "`Slots` have no checked forms (doc/design/arenas.md (Slots): cells have no tags, \
        occupancy is known only to proofs); use `put!`/`take!`/`s[i]!` with their obligations, or \
        an arena's checked operations"
    | _ => throwErrorAt f "unknown operation `{meth}` on `Slots` (`put!`, `take!`)"
  -- Constructors and container builders.
  if let some (adt, c) ← resolveCtor fname then
    return ← elabCtorApp ctx stx adt c args exp?
  if fname == `Vector.replicate || fname == `Arr.replicate then
    unless args.size == 2 do throwErrorAt stx "`{fname}` takes a length and a value"
    let n ← match args[0]!.isNatLit? with
      | some n => pure (toExpr n)
      | none => sizeTerm args[0]!
    let et? := match exp? with | some (.arr e _) => some e | _ => none
    let (bs, a, e) ← elabAtom ctx args[1]! et?
    let t := STy.arr e n
    expect stx exp? t
    return (wrap bs (.mk (mkApp2 (mkConst ``Ctor.fill) e.toTy n) [e] t [a]), t)
  if fname == `Slots.empty then
    unless args.size == 1 do throwErrorAt stx "`Slots.empty` takes the number of cells"
    let some (.slots e m) := exp?
      | throwErrorAt stx "cannot infer the cell type of `Slots.empty`; add a type ascription"
    let n ← match args[0]!.isNatLit? with
      | some n => pure (toExpr n)
      | none => sizeTerm args[0]!
    unless m == n do throwErrorAt stx "type mismatch: expected {exp?.get!}, but this has {fmtN n} cells"
    return (.mk (mkApp2 (mkConst ``Ctor.slotsEmpty) e.toTy n) [] (.slots e n) [], .slots e n)
  if let some r ← elabCtorConst ctx stx f args exp? then return r
  match ← resolveEntry f with
  | some (.fn info) =>
    -- A generic callee's variables may be given by name, as in `f (A := impl) x`.
    let named := args.filter (·.getKind == ``Lean.Parser.Term.namedArgument)
    let args := args.filter (·.getKind != ``Lean.Parser.Term.namedArgument)
    if !named.isEmpty && (info.nGen == 0 || !info.genArgs.isEmpty) then
      throwErrorAt named[0]! "`{fname}` takes no named argument here"
    let info ← if info.nGen > 0 && info.genArgs.isEmpty then inferGen ctx stx info args exp? named
      else pure info
    let nVis := (List.range info.params.size).countP fun k => !isLenParam info.params k
    unless args.size == nVis do
      throwErrorAt stx "`{fname}` expects {nVis} argument(s), got {args.size}"
    expect stx exp? info.ret
    if !info.isRef then
      for a in args do
        let a := unparen a
        if a.getKind == ``mpRefMut || a.getKind == ``mpRefShr then
          throwErrorAt a "`{fname}` takes its arguments by value; drop the `&`"
      let (bs, as) ← elabAtoms ctx args.toList (info.params.toList.map (some ·.2.1))
      return (wrap bs (.call info (as.map (·.1))), info.ret)
    let mut bs : Binds := #[]
    let mut rargs : Array RArg := #[]
    let mut lastLen : Option SAtom := none
    let mut ai := 0
    for k in [0:info.params.size] do
      let (pn, pt, m) := info.params[k]!
      if isLenParam info.params k then
        -- The hidden length of the slice argument before it, which is the callee's `s.len`.
        let some l := lastLen | throwErrorAt stx "internal error: no slice length"
        rargs := rargs.push (.own l)
        continue
      let a := unparen args[ai]!
      ai := ai + 1
      match m with
      | .own =>
        if a.getKind == ``mpRefMut || a.getKind == ``mpRefShr then
          throwErrorAt a "parameter `{pn}` of `{fname}` is passed by value; drop the `&`"
        let (b, atm, _) ← elabAtom ctx a (some pt)
        bs := bs ++ b; rargs := rargs.push (.own atm)
      | .shr | .mut =>
        let want := if m == .mut then ``mpRefMut else ``mpRefShr
        unless a.getKind == want do
          throwErrorAt a "parameter `{pn}` of `{fname}` is `{m.fmt pt}`: pass \
            `{if m == .mut then "&mut" else "&"} p` for a place `p`"
        let (b, p, t) ← elabPlace ctx a[1]
        unless t == pt do
          if let (.slice _ n, .slice _ n') := (pt, t) then
            throwErrorAt a[1] "parameter `{pn}` of `{fname}` is a slice of an array of {n} \
              elements (`[T; {n}]`), but this is a slice of an array of {n'} elements"
          throwErrorAt a[1] "type mismatch: expected {pt}, but this has type {t}"
        if let .slice _ _ := pt then
          lastLen := placeLen? ctx p
          if lastLen.isNone then
            throwErrorAt a[1] "internal error: the length of this slice is unknown"
        if m == .mut then requireMutable ctx p "borrow mutably"
        bs := bs ++ b; rargs := rargs.push (if m == .mut then .mut p else .shr p)
    let x ← fresh
    return (wrap bs (.callRef stx info rargs.toList x (.atom (.var x .missing))), info.ret)
  | some (.ext info) =>
    let ins := info.params.filter fun (_, k) => k != .outByte
    unless args.size == info.caps.size + ins.size do
      throwErrorAt stx "extern `{fname}` expects {info.caps.size + ins.size} argument(s), got \
        {args.size}"
    -- The leading token arguments are not passed to the extern. Each is borrowed around the
    -- call, so that the borrow checker rejects a token that was moved.
    let mut toks : Array (Binds × SPlace × STy × Syntax) := #[]
    for (pn, cls) in info.caps, a in args do
      let a := unparen a
      let bad : MessageData := m!"the parameter `{pn}` of `{fname}` is a token: pass `&t` for a \
        token `t` of the capability `{cls}`"
      unless a.getKind == ``mpRefShr do throwErrorAt a bad
      let (tb, p, t) ← elabPlace ctx a[1]
      unless (← capClassOf? t) == some cls do throwErrorAt a bad
      toks := toks.push (tb, p, t, a)
    let holdToks (e : AExp) : M AExp := toks.foldrM (init := e) fun (tb, p, t, a) e => do
      let r ← fresh
      let y ← fresh
      return wrap tb (.borrow a false p t r a e .u64 y (.atom (.var y .missing)))
    let args := args.extract info.caps.size args.size
    let mut bs : Binds := #[]
    let mut eas := #[]
    let mut i := 0
    for (pn, k) in info.params do
      match k with
      | .word =>
        let a := args[i]!
        i := i + 1
        let (b, wa, _) ← elabAtom ctx a (some .u64)
        bs := bs ++ b
        eas := eas.push (EArg.word wa)
      | .bytes =>
        let a := args[i]!
        i := i + 1
        if let some s := a.isStrLit? then
          eas := eas.push (EArg.bytes (strBytes s))
        else
          let a := unparen a
          unless a.getKind == ``mpRefShr do
            throwErrorAt a "the buffer `{pn}` of `{fname}` is a string literal or a shared slice \
              `&a[lo:hi]` of a byte array"
          let (b, p, _) ← elabByteSlice ctx a[1]
          bs := bs ++ b
          eas := eas.push (EArg.slice p)
      | .sliceOut =>
        let a := unparen args[i]!
        i := i + 1
        unless a.getKind == ``mpRefMut do
          throwErrorAt a "the buffer `{pn}` of `{fname}` is a mutable slice `&mut a[lo:hi]` of a \
            byte array"
        let (b, p, _) ← elabByteSlice ctx a[1]
        requireMutable ctx p "pass as a mutable slice"
        bs := bs ++ b
        eas := eas.push (EArg.sliceOut p)
      | .outByte => eas := eas.push EArg.outByte
    expect stx exp? .u64
    if info.params.any (·.2 == .sliceOut) then
      let x ← fresh
      return (wrap bs (← holdToks (.extMut stx info eas.toList x (.atom (.var x .missing)))), .u64)
    return (wrap bs (← holdToks (.ext info eas.toList)), .u64)
  | _ =>
    let failed ← failedDefs.get
    let ns ← getCurrNamespace
    if failed.contains (ns ++ fname) || failed.contains fname then
      throwErrorAt f "`{fname}` was not defined because of the error above (at its `mp def`)"
    throwErrorAt f "unknown function `{fname}` (not an earlier `mp def` or `mp extern`)"

/-- The arguments of a generic callee at a call. The callee's variables become metavariables,
those given by name as `(x := e)` are elaborated, and the result's type is unified with the
expected type. Each visible argument whose parameter type still has a variable is then
elaborated in a throw-away state and its type unified with the parameter's. After that the
`Data` and other instances are synthesised, each hypothesis such as `hn : n < 2 ^ 64` is found in
the context or proved by `decide`, and a variable still open is the one free variable of its type
in the context, such as a section's `A : Alloc UInt64`. The callee is instantiated at the
result. -/
partial def inferGen (ctx : Ctx) (stx : Syntax) (info : FnInfo) (args : Array Syntax)
    (exp? : Option STy) (named : Array Syntax := #[]) : M FnInfo := do
  let some ci := (← getEnv).find? (info.declName ++ `exp)
    | throwErrorAt stx "internal error: no `{info.declName}.exp`"
  let (ms, _, _) ← forallMetaBoundedTelescope ci.type info.nGen
  -- The variables given by name, elaborated against their binder types.
  let names ← forallBoundedTelescope ci.type info.nGen fun xs _ =>
    xs.mapM fun x => return (← x.fvarId!.getDecl).userName
  for na in named do
    let some k := names.findIdx? (· == na[1].getId)
      | throwErrorAt na[1] "`{info.declName}` has no variable `{na[1].getId}`"
    let ty ← instantiateMVars (← inferType ms[k]!)
    let v ← Term.elabTermEnsuringType na[3] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq ms[k]! (← instantiateMVars v) do
      throwErrorAt na[3] "type mismatch for the variable `{na[1].getId}` of `{info.declName}`"
  let gi := info.instantiate ms
  let s ← (saveState : TermElabM _)
  let n ← get
  -- First the expected type, from a struct literal's field or an ascription, then each argument
  -- whose parameter type still has a variable.
  if let some e := exp? then discard <| isDefEq gi.ret.toTy e.toTy
  let mut ai := 0
  for k in [0:gi.params.size] do
    if isLenParam gi.params k then continue
    let (_, pt, m) := gi.params[k]!
    let a := unparen args[ai]!
    ai := ai + 1
    unless (← instantiateMVars pt.toTy).hasMVar do continue
    let aty? ← try
        match m with
        | .own => some <$> (do let (_, _, t) ← elabAtom ctx a none; pure t)
        | _ => some <$> (do let (_, _, t) ← elabPlace ctx a[1]; pure t)
      catch _ => pure none
    if let some aty := aty? then
      discard <| isDefEq pt.toTy aty.toTy
  let assigned ← ms.mapM fun mv => instantiateMVars mv
  (s.restore : TermElabM Unit)
  set n
  -- What unification found, then instances, then hypotheses, in binder order.
  for k in [0:ms.size] do
    if !assigned[k]!.hasMVar then ms[k]!.mvarId!.assign assigned[k]!
  let cannot (k : Nat) (ty : Expr) : M Unit := do
    let x := names[k]!
    throwErrorAt stx "cannot infer the variable `{x}` of the generic `{info.declName}` from the \
      arguments' types, the expected type or the context; give it by name, as the argument \
      `({x} := …)`, of type{indentExpr ty}"
  for k in [0:ms.size] do
    let mv := ms[k]!
    if ← mv.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType mv)
    if ty.hasMVar then cannot k ty
    if (← isClass? ty).isSome then
      let some inst ← synthInstance? ty
        | throwErrorAt stx "cannot instantiate `{info.declName}`: no instance{indentExpr ty}"
      mv.mvarId!.assign inst; continue
    if ← isProp ty then
      let hyp? ← (← getLCtx).foldlM (init := none) fun acc d => do
        if acc.isSome || d.isImplementationDetail then return acc
        if ← isDefEq d.type ty then return some d.toExpr else return none
      if let some h := hyp? then mv.mvarId!.assign h; continue
      if !ty.hasFVar then
        let r ← withAtLeastTransparency .default <| whnf (← mkDecide ty)
        if r.isConstOf ``Bool.true then
          mv.mvarId!.assign (mkApp3 (mkConst ``of_decide_eq_true) ty
            (← synthInstance (mkApp (mkConst ``Decidable) ty))
            (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))
          continue
      throwErrorAt stx "cannot instantiate `{info.declName}`: its hypothesis{indentExpr ty}\
        \nis neither in the context nor decided"
    -- A variable of the caller's section is the one free variable of this type in the context.
    let cands ← (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail || d.isLet then return acc
      if ← isDefEq d.type ty then return acc.push d.toExpr else return acc
    if cands.size == 1 then mv.mvarId!.assign cands[0]!; continue
    cannot k ty
  let out ← ms.mapM instantiateMVars
  let r := info.instantiate out
  let ps ← r.params.mapM fun (x, t, m) => return (x, ← t.refresh, m)
  return { r with params := ps, ret := ← r.ret.refresh }

/-- `c a b` for a `Ctor` constant `c`. A constructor whose result is a sealed struct may only be
applied where the struct is not sealed, or when the constant itself is `private`, declared next
to the struct. -/
partial def elabCtorConst (ctx : Ctx) (stx : Syntax) (f : Syntax) (args : Array Syntax)
    (exp? : Option STy) : M (Option (AExp × STy)) := do
  let some (cn, ins, out, k) ← resolveCtorConst f.getId | return none
  -- For a function of Lean parameters, its first `k` arguments are Lean terms.
  let (ctorE, ins, out, args) ← if k == 0 then pure (Lean.mkConst cn, ins, out, args) else do
    unless args.size ≥ k do
      throwErrorAt stx "`{f.getId}` takes {k} parameter(s) before its arguments"
    let c ← Term.elabTerm (← `($(⟨f⟩) $(args.extract 0 k |>.map (⟨·⟩))*)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let c ← instantiateMVars c
    let ty ← whnfR (← inferType c)
    let some ps ← tyListElems ty.appFn!.appArg! | throwErrorAt stx "internal error: `{cn}`"
    let ins ← ps.mapM fun p => do
      let some t ← (tyExprToSTy p : MetaM _) | throwErrorAt stx "internal error: `{cn}`"
      pure t
    let some out ← (tyExprToSTy ty.appArg! : MetaM _) | throwErrorAt stx "internal error: `{cn}`"
    pure (c, ins, out, args.extract k args.size)
  if let .adt S _ _ _ := out then
    -- `Cap.mint c` is accepted only in the `init` wrapper of `mp program`, for a class it grants.
    let granted ← if cn == ``Millipede.Lib.Cap.mint then do
        pure ((← capClassOf? out).any (← grantRef.get).contains)
      else pure false
    unless isPrivateName cn || granted do requireUnsealed stx S "be built"
  unless args.size == ins.length do
    throwErrorAt stx "`{f.getId}` takes {ins.length} argument(s), got {args.size}"
  expect stx exp? out
  let (bs, as) ← elabAtoms ctx args.toList (ins.map some)
  return some (wrap bs (.mk ctorE ins out (as.map (·.1))), out)

/-- `match s with …` on a `Result`, with the arms `ok a` and `err e` in either order, or on a
derived enum, with one arm per constructor. -/
partial def elabMatch (ctx : Ctx) (stx s : Syntax) (alts : Array (TSyntax ``Parser.Term.matchAlt))
    (exp? : Option STy) (arm : Ctx → Syntax → Option STy → M (AExp × STy)) : M (AExp × STy) := do
  let (bs, sa, st) ← elabAtom ctx s none
  if let .adt E _ _ _ := st then
    return ← elabEnumMatch ctx stx bs sa E st alts exp? arm
  let .result ε α := st
    | throwErrorAt s "`match` needs a Result or an enum, but this has type {st}"
  unless alts.size == 2 do
    throwErrorAt stx "`match` on a Result needs exactly two arms, `ok a` and `err e`"
  let mut okArm : Option (Name × Syntax × Syntax) := none
  let mut errArm : Option (Name × Syntax × Syntax) := none
  for alt in alts do
    let pats := alt.raw[1].getSepArgs
    unless pats.size == 1 && pats[0]!.getSepArgs.size == 1 do
      throwErrorAt alt "expected a single pattern `ok a` or `err e`"
    let pat := pats[0]!.getSepArgs[0]!
    let (ctor, v) ← match pat with
      | `($c:ident $v:ident) => pure (c.getId, v)
      | `($c:ident _) => pure (c.getId, mkIdentFrom pat (← fresh))
      | _ => throwErrorAt pat "expected a pattern `ok a` or `err e`"
    if ctor == `ok && okArm.isNone then okArm := some (v.getId, v, alt.raw[3])
    else if ctor == `err && errArm.isNone then errArm := some (v.getId, v, alt.raw[3])
    else throwErrorAt pat "expected a pattern `ok a` or `err e` (each once)"
  let some (a, aRef, aRhs) := okArm | throwErrorAt stx "missing arm `ok a`"
  let some (e, eRef, eRhs) := errArm | throwErrorAt stx "missing arm `err e`"
  checkShadow ctx a aRef
  checkShadow ctx e eRef
  let a' ← bindName ctx a
  let e' ← bindName ctx e
  -- Elaborate the arms in source order, so that the first fixes the result type.
  let okFirst := alts[0]!.raw[3] == aRhs
  let (ea, eo, t) ← if okFirst then do
      let (eo, t) ← arm (mkLocal a a' α :: ctx) aRhs exp?
      let (ea, _) ← arm (mkLocal e e' ε :: ctx) eRhs (some t)
      pure (ea, eo, t)
    else do
      let (ea, t) ← arm (mkLocal e e' ε :: ctx) eRhs exp?
      let (eo, _) ← arm (mkLocal a a' α :: ctx) aRhs (some t)
      pure (ea, eo, t)
  checkOnce e' ε eRef "match payload" ea
  checkOnce a' α aRef "match payload" eo
  return (wrap bs (.match_ stx ε α sa e' ea a' eo), t)

/-- `match s with | E.c₀ x => … | .c₁ => …`, with one arm per constructor in any order,
elaborated to the chain of `Exp.case`s over `E.split₀ …`. -/
partial def elabEnumMatch (ctx : Ctx) (stx : Syntax) (bs : Binds) (sa : SAtom) (E : Name)
    (eTy : STy) (alts : Array (TSyntax ``Parser.Term.matchAlt)) (exp? : Option STy)
    (arm : Ctx → Syntax → Option STy → M (AExp × STy)) : M (AExp × STy) := do
  let some { kind := .enum vs splits, .. } := lookupAdt (← getEnv) E
    | throwErrorAt stx "`{E}` is not an enum"
  -- A parameterised enum's payloads and splits are taken at the scrutinee type's arguments.
  let is := match eTy with | .adt _ _ _ is => is | _ => #[]
  let vs ← vs.mapM fun v => do
    return { v with payload := ← (v.payload.mapExpr (·.instantiateRev is)).refresh }
  let splits := splits.map fun sp => mkAppN (mkConst sp) is
  let mut arms : Array (Option (Name × Syntax × Syntax)) := Array.replicate vs.size none
  -- For each constructor, the index of its arm.
  let mut armOf : Array Nat := Array.replicate vs.size 0
  for h : altIdx in [0:alts.size] do
    let alt := alts[altIdx]
    let pats := alt.raw[1].getSepArgs
    unless pats.size == 1 && pats[0]!.getSepArgs.size == 1 do
      throwErrorAt alt "expected a single constructor pattern"
    let pat := pats[0]!.getSepArgs[0]!
    let (cStx, v?) ← match pat with
      | `($c:ident $v:ident) => pure (c.raw, some v.raw)
      | `($c:ident _) => pure (c.raw, none)
      | `($c:ident) => pure (c.raw, none)
      | _ =>
        if pat.getKind == ``Lean.Parser.Term.dotIdent then pure (pat[1], none)
        else if pat.getKind == ``Lean.Parser.Term.app && pat[0].getKind == ``Lean.Parser.Term.dotIdent
            && pat[1].getNumArgs == 1 then
          pure (pat[0][1], if pat[1][0].isIdent then some pat[1][0] else none)
        else throwErrorAt pat "expected a constructor pattern `E.c x`, `.c x` or `.c`"
    let cName := cStx.getId
    let some j := vs.findIdx? fun v => v.ctor == cName || cName.isSuffixOf v.ctor
      | throwErrorAt cStx "`{cName}` is not a constructor of `{E}`"
    if arms[j]!.isSome then throwErrorAt pat "duplicate arm for `{vs[j]!.ctor}`"
    if v?.isSome && !vs[j]!.hasField then throwErrorAt pat "`{vs[j]!.ctor}` has no field"
    let x ← match v? with | some v => pure v.getId | none => fresh
    arms := arms.set! j (some (x, v?.getD pat, alt.raw[3]))
    -- The binder is renamed below if it shadows a variable in scope.
    armOf := armOf.set! j altIdx
  for j in [0:vs.size] do
    if arms[j]!.isNone then throwErrorAt stx "missing arm for `{vs[j]!.ctor}`"
  -- Elaborate the arms in source order, so that the first fixes the type.
  let mut resTy := exp?
  let mut elabd : Array (Option AExp) := Array.replicate vs.size none
  for altIdx in [0:alts.size] do
    let some j := armOf.findIdx? (· == altIdx) | continue
    let some (x, xRef, rhs) := arms[j]! | continue
    checkShadow ctx x xRef
    let x' ← bindName ctx x
    arms := arms.set! j (some (x', xRef, rhs))
    let (e, t) ← arm (mkLocal x x' vs[j]!.payload :: ctx) rhs resTy
    checkOnce x' vs[j]!.payload xRef "match payload" e
    resTy := some t
    elabd := elabd.set! j (some e)
  let some t := resTy | throwErrorAt stx "internal error: no arm"
  let k := vs.size
  -- With two variants there is one `case` over `E.split₀ : Split E P₀ P₁`. With three or more
  -- there are `case`s over `E.splitᵢ : Split E Pᵢ E`, whose rest is the value itself, and a last
  -- one over `E.split_{k-1} : Split E P_{k-1} Unit`. Its rest is unreachable, since every other
  -- constructor was taken before, and runs the last arm on the payload's `default`, which is why
  -- `deriving Data` requires an `Inhabited` payload there.
  let rec chain (i : Nat) (scrut : SAtom) (fuel : Nat) : M AExp := do
    let (x, xRef, _) := arms[i]!.get!
    if k == 2 then
      let (y, _, _) := arms[1]!.get!
      return .case stx scrut splits[0]! eTy vs[0]!.payload vs[1]!.payload x xRef
        elabd[0]!.get! y elabd[1]!.get!
    if i + 1 == k || fuel == 0 then
      let pt := vs[i]!.payload
      let some inst ← synthInstance? (mkApp (mkConst ``Inhabited [1]) pt.carrier)
        | throwErrorAt stx "the payload of `{vs[i]!.ctor}` needs an `Inhabited` instance"
      let dflt := mkApp2 (mkConst ``Inhabited.default [1]) pt.carrier inst
      let u ← fresh
      return .case stx scrut splits[i]! eTy pt .unit x xRef elabd[i]!.get! u
        (.let_ x xRef pt (.atom (.lit pt dflt)) elabd[i]!.get!)
    let y ← fresh
    return .case stx scrut splits[i]! eTy vs[i]!.payload eTy x xRef elabd[i]!.get! y
      (← chain (i + 1) (.var y .missing) (fuel - 1))
  return (wrap bs (← chain 0 sa k), t)

/- ### Statements

The body of an `mp def` is parsed by Lean's own `do` parser, and its elements are translated here
into the ANF of Core without Lean's `do` elaborator. `elabSeq` takes the rest of the enclosing
block as a continuation `k?`, elaborated in the context where the sequence started, so that the
binders of a branch are out of scope there. An `if` or `match` statement puts the continuation at
the end of each branch and a jump does not, so the statements a jump skips are not on its path.
When `k?` is `none` the sequence is in value position, and its last element is its value. -/

/-- Elaborate the statement sequence `items` of `doElem`s. When `iterEnd` is set, `k?` is the end
of an iteration of a loop, which is `()`, so a last unit statement is its value.

The node kinds of Lean's `do` grammar that `mp def` accepts are matched here and in `elabFor`,
`doSeqItems` and `doIfParts`, so a toolchain upgrade that changes them must be followed here.
They are `doLet` with `letIdDecl`, `doReassign` with `letIdDeclNoBinders` or `letPatDecl`,
`doExpr`, `doIf` with `doIfProp` and `elseIf`, `doMatch`, `doFor` with `doForDecl` and the ranges
`Std.«term_..._»` and `Std.«term_...=_»`, `doBreak`, `doContinue`, `doReturn` and `doNested`.
Every other kind is refused with a message. -/
partial def elabSeq (j : DoJ) (ctx : Ctx) (items : List Syntax) (k? : Option (M (AExp × STy)))
    (exp? : Option STy) (iterEnd : Bool := false) : M (AExp × STy) := do
  match items with
  | [] => match k? with
    | some k => k
    | none => expect (← getRef) exp? .unit; return (.atom unitAtom, .unit)
  | it :: rest =>
  withRef it do
  let last := rest.isEmpty
  let valuePos := last && k?.isNone
  -- The rest of the block after `it`, elaborated in `ctx`.
  let next : Option (M (AExp × STy)) :=
    if last then k? else some (elabSeq j ctx rest k? exp? iterEnd)
  let nextEnd := last && iterEnd
  let noRest : M Unit := do
    if let some r := rest.head? then
      throwErrorAt r "unreachable: a statement after `{it[0].getAtomVal}` in the same block"
  let unitEnd := last && iterEnd && (j.loop?.all (·.accTy == .unit))
  -- A statement `if` or `match` followed by the rest `k` is copied into each branch that
  -- continues when at most one does and the statement jumps, and is otherwise joined.
  let joinOrCopy (stmt : DoJ → Ctx → Option (M (AExp × STy)) → Bool → M (AExp × STy))
      (k : M (AExp × STy)) : M (AExp × STy) :=
    if jumps it && contArms it ≤ 1 then do checkBudget it (← stmt j ctx next nextEnd)
    else joinStmt j ctx it (jumps it) (fun j' c join =>
      if join then stmt j' c (some (pure (.atom (if jumps it then boolAtom false else unitAtom),
        if jumps it then .bool else .unit))) false
      else stmt j' c next nextEnd) k
  match it.getKind with
  | ``Lean.Parser.Term.doLet =>
    let d := it[3][0]
    unless d.getKind == ``Lean.Parser.Term.letIdDecl && d[1].getNumArgs == 0 do
      throwErrorAt d "`let` in `mp def` binds one name: `let x := e` or `let x : T := e`"
    let ty? := if d[2].getNumArgs == 0 then none else some d[2][0][1]
    let x : TSyntax `ident ← if d[0][0].isIdent then pure ⟨d[0][0]⟩ else pure (mkIdentFrom d (← fresh))
    let isMut := !it[1].isNone
    -- For `let mut x := v` right before a loop that assigns `x` and whose counter is not `x`, `v`
    -- is the initial value of the loop's accumulator when `x` is a word.
    if isMut then
      if let some f := rest.head? then
        if f.getKind == ``Lean.Parser.Term.doFor && f[1].getSepArgs.size == 1 &&
            f[1].getSepArgs[0]![1].getId != x.getId &&
            (assignedRoots f[5]).contains x.getId then
          return ← elabFor j ctx f (some (x, ty?, d[4])) rest.tail! k? exp? iterEnd
    elabLet ctx x ty? d[4] (fun ctx' => elabSeq j ctx' rest k? exp? iterEnd)
      (if isMut then .ownMut else .own)
  | ``Lean.Parser.Term.doReassign =>
    let d := it[0]
    let lhs := if d.getKind == ``Lean.Parser.Term.letIdDeclNoBinders then d[0][0] else d[0]
    unless d[2].getNumArgs == 0 do throwErrorAt d[2] "an assignment takes no type ascription"
    let v := d[4]
    -- The last assignment of the loop's accumulator is the iteration's value.
    if last && iterEnd && lhs.isIdent then
      if let some l := j.loop? then
        if let some x := lookupLocal ctx lhs.getId then
          if l.user && x.name == l.acc then return ← elabE ctx v (some x.ty)
    let (bp, p, t) ← elabPlace ctx lhs
    requireMutable ctx p "assign"
    if t.linear then
      -- For a linear variable whose old value is consumed, by `v` or before, `v` is bound to the
      -- variable's own ANF name, so the rest of the block and every continuation see the new
      -- value. The variable's binder checks that the old value is used once, and outside a loop
      -- this checks the new one too, while in a loop the iteration hands it back.
      let .var x _ := p
        | throwErrorAt lhs "cannot assign a linear value of type {t} to a part of a place (the \
            old value would be dropped)"
      let (va, _) ← elabE ctx v (some t)
      let (ka, kt) ← elabSeq j ctx rest k? exp? iterEnd
      if j.loop?.isNone then checkOnce x t lhs "variable" ka
      return (wrap bp (splice va x t ka), kt)
    let s0 ← Term.saveState
    let (bv, a, _) ← elabAtom ctx v (some t)
    -- When a value writes a place within a term that is not spliced, as in `n + f (&mut a)`, the
    -- assignment and the rest of the block go at the term's tail, which has no branch.
    if bv.any (fun (_, _, e) => !e.writes.isEmpty && !needsSplice e) then
      s0.restore
      let (va, _) ← elabE ctx v (some t)
      if !va.size.2 then
        let (ka, kt) ← elabSeq j ctx rest k? exp? iterEnd
        return (wrap bp (← mapTail va t fun a => pure (.assign it p t a ka)), kt)
      s0.restore
      let (bv, a, _) ← elabAtom ctx v (some t)
      let (ka, kt) ← elabSeq j ctx rest k? exp? iterEnd
      return (wrap (bp ++ bv) (.assign it p t a ka), kt)
    let (ka, kt) ← elabSeq j ctx rest k? exp? iterEnd
    return (wrap (bp ++ bv) (.assign it p t a ka), kt)
  | ``Lean.Parser.Term.doExpr =>
    let e := it[0]
    if valuePos then return ← elabE ctx e exp?
    if unitEnd then return ← elabE ctx e (some .unit)
    if isUnitLit (unparen e) then return ← elabSeq j ctx rest k? exp? iterEnd
    let x ← fresh
    let (va, vt) ← elabE ctx e none
    unless vt == .unit do
      throwErrorAt e "the value of this statement (of type {vt}) would be discarded: bind it \
        with `let _ := …`, or make it the last element of the block"
    let (ka, kt) ← elabSeq j ctx rest k? exp? iterEnd
    return (splice va x .unit ka, kt)
  | ``Lean.Parser.Term.doIf =>
    let (arms, els?) ← doIfParts it
    let stmt (j : DoJ) (ctx : Ctx) (next : Option (M (AExp × STy))) (nextEnd : Bool) :
        M (AExp × STy) :=
      let branch (seq : Syntax) (e? : Option STy) : M (AExp × STy) :=
        if valuePos then elabSeq j ctx (doSeqItems seq) none e?
        else elabSeq j ctx (doSeqItems seq) next exp? nextEnd
      let rec chain : List (Syntax × Syntax) → Option STy → M (AExp × STy)
        | [], e? => match els? with
          | some seq => branch seq e?
          | none => match next with
            | some k => k
            | none => do expect it e? .unit; return (.atom unitAtom, .unit)
        | (c, seq) :: more, e? => do
          let (cb, ca, _) ← elabAtom ctx c (some .bool)
          let (ta, tt) ← branch seq e?
          let (ea, _) ← chain more (some tt)
          return (wrap cb (.ite it ca ta ea), tt)
      chain arms exp?
    match next with
    | some k => if valuePos then stmt j ctx next nextEnd else joinOrCopy stmt k
    | none => stmt j ctx next nextEnd
  | ``Lean.Parser.Term.doMatch =>
    unless it[1].isNone && it[2].isNone && it[3].isNone && it[4].getSepArgs.size == 1 do
      throwErrorAt it "`match` in `mp def` has one scrutinee and no options: `match e with …`"
    let d := it[4].getSepArgs[0]!
    unless d[0].isNone do throwErrorAt d "`match h : e` is not supported in `mp def`"
    let alts : Array (TSyntax ``Parser.Term.matchAlt) := it[6][0].getArgs.map (⟨·⟩)
    let stmt (j : DoJ) (ctx : Ctx) (next : Option (M (AExp × STy))) (nextEnd : Bool) :
        M (AExp × STy) :=
      elabMatch ctx it d[1] alts exp? fun ctx' rhs e? =>
        if valuePos then elabSeq j ctx' (doSeqItems rhs) none e?
        else elabSeq j ctx' (doSeqItems rhs) next exp? nextEnd
    match next with
    | some k => if valuePos then stmt j ctx next nextEnd else joinOrCopy stmt k
    | none => stmt j ctx next nextEnd
  | ``Lean.Parser.Term.doFor => elabFor j ctx it none rest k? exp? iterEnd
  | ``Lean.Parser.Term.doNested =>
    if valuePos then elabSeq j ctx (doSeqItems it[1]) none exp?
    else elabSeq j ctx (doSeqItems it[1]) next exp? nextEnd
  | ``Lean.Parser.Term.doBreak | ``Lean.Parser.Term.doContinue =>
    noRest
    let some l := j.loop? | throwErrorAt it "`{it[0].getAtomVal}` outside a `for` loop"
    if it.getKind == ``Lean.Parser.Term.doContinue then
      if ← doMutant "continue-falls-through" then if let some k := k? then return ← k
      return jumpEnd j
    if ← doMutant "break-ignored" then return jumpEnd j
    let some b := l.brk? | throwErrorAt it "internal error: no `break` flag"
    let (e, t) := jumpEnd j
    -- The seeded bug, in which an inner loop's `break` also leaves the loop around it.
    let e ← match j.outer?.bind (·.brk?) with
      | some ob => if ← doMutant "inner-break-outer" then
          pure (.assign it (.var (ctxVar ctx ob) it) .bool (boolAtom true) e) else pure e
      | none => pure e
    return (.assign it (.var (ctxVar ctx b) it) .bool (boolAtom true) e, t)
  | ``Lean.Parser.Term.doReturn =>
    noRest
    let some rt := j.ret? | throwErrorAt it "`return` is only supported in the body of an \
      `mp def`, not in a nested `do` term"
    let v : Syntax ← if it[1].isNone then pure (← `(())).raw else pure it[1][0]
    match j.retVars?, j.loop?, j.join? with
    | some (f, r), some _, _ =>
      let (bv, a, _) ← elabAtom ctx v (some rt)
      let (e, t) := jumpEnd j
      let setF := AExp.assign it (.var (ctxVar ctx f) it) .bool (boolAtom true) e
      if ← doMutant "return-lost" then return (setF, t)
      return (wrap bv (.assign it (.var (ctxVar ctx r) it) rt a setF), t)
    | _, _, some (some rv) =>
      let (bv, a, _) ← elabAtom ctx v (some rt)
      return (wrap bv (.assign it (.var (ctxVar ctx rv) it) rt a (.atom (boolAtom true))), .bool)
    | _, _, _ => elabE ctx v (some rt)
  | ``Lean.Parser.Term.doWhile | ``Lean.Parser.Term.doRepeat | ``Lean.Parser.Term.doRepeatUntil =>
    throwErrorAt it "unbounded loops (`while`, `repeat`) are not supported in `mp def`: write a \
      bounded loop `for i in lo...hi do` and leave it with `if c then break`"
  | ``Lean.Parser.Term.doTry =>
    throwErrorAt it "`try`/`catch`/`finally` is not supported in `mp def`: errors are `Result` \
      values (`match r with | ok a => … | err e => …`)"
  | ``Lean.Parser.Term.doLetArrow | ``Lean.Parser.Term.doReassignArrow =>
    throwErrorAt it "`←` is not supported in `mp def`: a call is written directly, `let x := f a`"
  | ``Lean.Parser.Term.doUnless =>
    throwErrorAt it "`unless` is not supported in `mp def`: write `if !c then …`"
  | k => throwErrorAt it "`{k.componentsRev.head!}` is not supported in `mp def`"

/-- `for i in lo...hi do body` or `for i in lo...=hi do body`, elaborated to Core's loop
`Exp.loop`, which has a static iteration count, a condition checked before each iteration, an
accumulator, and the carried variables, which are those bound outside the loop that the body
writes.

The bound `hi` is a size expression or `min e N` with a size expression `N` as a static cap. A
static `hi` and `lo` give the count `hi - lo`, plus one for `...=`, and no loop when `lo > hi`. A
run-time `hi` gives the count `cap - lo` and the condition `i < hi`, or `i ≤ hi`. A run-time `lo`
is evaluated once before the loop and gives the condition `i < hi`. For a non-zero `lo` Core's
counter `k` runs from 0, and the body and the condition start with `let i := k + lo`, which does
not wrap because `i` stays below the cap.

An `if c then break` as the first statement is the condition `¬c` itself. A `break` elsewhere
sets a carried flag that the condition tests, and `continue` ends the iteration, so the
statements after it are not on its path. A `return v` in a loop sets a carried flag and a carried
result, declared before the outermost such loop, so that the loops stop on the flag, and after
the loop `if flag then result else rest` follows.

Core's accumulator is the word variable, not linear, declared last among those that the body ends
by assigning on every path, excluding one of the enclosing loop's state, which stays carried in
place. Without such a variable the accumulator is `()`. The loop's state is the accumulator with
the carried variables. When the loop follows `let mut x := v` and `x` is the accumulator, `v` is
its initial value and the loop's result is bound to `x`, and otherwise `x` is declared before the
loop. An assignment `x := e` of the accumulator that ends an iteration is the iteration's value.

A counter that shadows a variable the body assigns is refused, as Lean's `do` refuses it, and one
that shadows any other variable is renamed. -/
partial def elabFor (j : DoJ) (ctx : Ctx) (stx : Syntax)
    (fuse? : Option (TSyntax `ident × Option Syntax × Syntax)) (rest : List Syntax)
    (k? : Option (M (AExp × STy))) (exp? : Option STy) (iterEnd : Bool) :
    M (AExp × STy) := withRef stx do
  let decls := stx[1].getSepArgs
  unless decls.size == 1 do
    throwErrorAt stx[1] "a `for` loop in `mp def` has one counter: `for i in lo...hi do`"
  unless stx[2].isNone && stx[3].isNone do
    throwErrorAt stx "`invariant` / `decreasing` clauses are not supported in `mp def` (a loop \
      invariant belongs to the proof: `vcgen … invariants`)"
  let d := decls[0]!
  unless d[0].isNone do throwErrorAt d "`for h : …` is not supported in `mp def`"
  let iStx := d[1]
  let iSrc ← if iStx.isIdent then pure iStx.getId
    else if iStx.getKind == ``Lean.Parser.Term.hole then fresh
    else throwErrorAt iStx "the counter of a `for` loop is a name"
  let range := d[3]
  let incl ← match range.getKind with
    | `Std.«term_..._» => pure false
    | `Std.«term_...=_» => pure true
    | _ => throwErrorAt range "a `for` loop in `mp def` runs over a range of words `lo...hi` \
        (upper bound excluded) or `lo...=hi` (included)"
  let incl := incl && !(← doMutant "incl-off-by-one")
  let loStx := range[0]
  let hiStx := range[2]
  checkShadow ctx iSrc iStx
  if let some l := lookupLocal ctx iSrc then
    if (assignedRoots stx[5]).contains iSrc then
      throwErrorAt iStx "the counter `{iSrc}` shadows the variable `{l.srcName}`, which the loop \
        body assigns: rename the counter"
  let mut pre : Binds := #[]
  let mut ctx := ctx
  -- The lower bound, which is a static `L` or an atom evaluated before the loop.
  let (lo?, loA) ← do
    match ← sizeBound ctx ⟨loStx⟩ with
    | some (l, false, _) =>
      match STy.natOf? l with
      | some l => pure (some l, SAtom.lit .u64 (toExpr (UInt64.ofNat l)))
      | none => throwErrorAt loStx "the lower bound of a loop is a word or a numeral, not a \
          size variable"
    | _ =>
      let (la, _) ← elabE ctx loStx (some .u64)
      let t ← fresh
      pre := pre.push (t, .u64, la)
      ctx := { name := t, ty := .u64 } :: ctx
      pure (none, SAtom.var t .missing)
  -- A symbolic size `c` over size variables, as a word evaluated before the loop.
  let wordOf (c : Expr) : M (Name × AExp) := do
    return (← fresh, .atom (.lit .u64 (mkApp (mkConst ``UInt64.ofNat) c)))
  -- The upper bound, which is a static cap `hc` and, at run time, the expression `hiE`.
  let (hc, hdyn, hiE) ← do
    if let some r ← sizeBound ctx ⟨hiStx⟩ then pure r else
    match hiStx with
    | `(min $a $b) =>
      let (cap, other) ← match ← sizeBound ctx a, ← sizeBound ctx b with
        | some r, _ => pure (r, b)
        | none, some r => pure (r, a)
        | none, none => throwErrorAt hiStx "`min a b` as a loop bound needs a size expression \
            as one of its operands (the static cap)"
      let (c, _, capE) := cap
      let capE ← if (STy.natOf? c).isSome then pure capE else do
        let (t, e) ← wordOf c
        pre := pre.push (t, .u64, e)
        ctx := { name := t, ty := .u64 } :: ctx
        pure (mkIdentFrom capE t)
      -- The other operand is evaluated once, before the loop.
      let (oa, _) ← elabE ctx other (some .u64)
      let t ← fresh
      pre := pre.push (t, .u64, oa)
      ctx := { name := t, ty := .u64 } :: ctx
      let tI := mkIdentFrom other t
      pure (c, true, ← `(if $tI ≤ $capE then $tI else $capE))
    | _ => throwErrorAt hiStx "the upper bound of a loop must be a size expression (a numeric \
        literal, a `Nat` constant or variable, the length `s.len` of a slice, or `+ - * / %` of \
        those, `/` and `%` by a positive literal), or `min e N` with a size expression `N`: a \
        loop needs a static bound on its number of iterations"
  -- The cap, a `Nat`, which is a numeral or, in a generic definition, a term over size variables
  -- that `compile` checks at each instance.
  let cap : Expr ← match STy.natOf? hc with
    | some h =>
      let cap := h + if incl then 1 else 0
      unless cap < 2 ^ 64 do
        throwErrorAt hiStx "an inclusive upper bound must be below 2^64 - 1 (the counter would \
          wrap around); this one may be {h}"
      pure (toExpr cap)
    | none => if incl then mkAppM ``HAdd.hAdd #[hc, toExpr (1 : Nat)] else pure hc
  let n : Expr ← match lo?, STy.natOf? cap with
    | some l, some c => pure (toExpr (c - l))
    | some 0, none | none, _ => pure cap
    | some l, none => mkAppM ``HSub.hSub #[cap, toExpr l]
  let iI := mkIdentFrom iStx iSrc
  -- A symbolic bound tested at run time, when `lo` is a run-time value, as a word.
  let hiE ← if !hdyn && lo?.isNone && (STy.natOf? hc).isNone then do
      let (t, e) ← wordOf hc
      pre := pre.push (t, .u64, e)
      ctx := { name := t, ty := .u64 } :: ctx
      pure (⟨(mkIdentFrom hiStx t).raw⟩ : Term)
    else pure hiE
  let condBound : Option Syntax ← if hdyn || lo?.isNone then
      some <$> (if incl then `($iI ≤ $hiE) else `($iI < $hiE))
    else pure none
  -- An `if c then break` as the first statement gives the condition `¬c`.
  let mut body := doSeqItems stx[5]
  let mut userCond : Option Syntax := none
  if let some f := body.head? then
    if f.getKind == ``Lean.Parser.Term.doIf then
      let (arms, els?) ← doIfParts f
      if let [(c, seq)] := arms then
        if els?.isNone && (doSeqItems seq).map (·.getKind) == [``Lean.Parser.Term.doBreak] then
          userCond := some (← withRef c (negCond c))
          body := body.tail!
  -- Flags.
  let hasBreak := body.any (hasJump ``Lean.Parser.Term.doBreak false)
  let hasReturn := body.any (hasJump ``Lean.Parser.Term.doReturn true)
  let mut flagLets : Binds := #[]
  let mut retVars? := j.retVars?
  let ownRet := hasReturn && j.retVars?.isNone
  if ownRet then
    let some rt := j.ret? | throwErrorAt stx "`return` is only supported in the body of an \
      `mp def`, not in a nested `do` term"
    let f ← fresh; let r ← fresh
    flagRolesRef.modify fun m => (m.insert f "returned").insert r "returned value"
    flagLets := flagLets.push (f, .bool, .atom (.lit .bool (toExpr false)))
    flagLets := flagLets.push (r, rt, .atom (← defaultAtom stx rt))
    ctx := { name := r, ty := rt, kind := .ownMut } :: { name := f, ty := .bool, kind := .ownMut } :: ctx
    retVars? := some (f, r)
  -- A `let mut x := v` right before the loop is absorbed when `x` is a word, and declared here
  -- otherwise.
  let mut absorbed : Option (Name × Name × STy × SAtom) := none
  if let some (x, ty?, v) := fuse? then
    checkShadow ctx x.getId x
    let (bs, ia, s) ← elabAtom ctx v (← ty?.mapM elabTy)
    let x' ← bindName ctx x.getId
    if s.slotSized && !s.linear && endsAssigning x.getId body then
      pre := pre ++ bs
      absorbed := some (x.getId, x', s, ia)
    else
      -- Declared here, bound to the last binding of `v` itself, as by a `let mut` statement.
      pre := match bs.back?, ia with
        | some (t, _, e), .var t' _ => if t == t' then pre ++ bs.pop.push (x', s, e)
            else (pre ++ bs).push (x', s, .atom ia)
        | _, _ => (pre ++ bs).push (x', s, .atom ia)
      ctx := mkLocal x.getId x' s .ownMut :: ctx
  -- Core's accumulator is the word variable declared last in the enclosing loop's body that the
  -- body ends by assigning on every path, or else `()`. A variable of the enclosing loop's state
  -- stays carried in place, since as the inner accumulator it would be copied in and assigned
  -- back.
  let outerAt := (j.loop?.bind fun o => ctx.findIdx? (·.name == o.acc)).getD ctx.length
  let userAcc? : Option Local := if absorbed.isSome then none else
    let pos (l : Local) : Nat := (ctx.findIdx? (·.name == l.name)).getD ctx.length
    let cands := ((assignedRoots stx[5]).filterMap (lookupLocal ctx)).filter fun l =>
      l.kind == .ownMut && !isTemp l.srcName && l.ty.slotSized && !l.ty.linear &&
        l.srcName != iSrc && pos l < outerAt && endsAssigning l.srcName body
    cands.foldl (fun b l => match b with
      | some b => if pos l < pos b then some l else some b
      | none => some l) none
  let user := absorbed.isSome || userAcc?.isSome
  let brk? ← if hasBreak then some <$> fresh else pure none
  if let some b := brk? then flagRolesRef.modify (·.insert b "left the loop")
  if let some b := brk? then
    flagLets := flagLets.push (b, .bool, .atom (boolAtom false))
    ctx := { name := b, ty := .bool, kind := .ownMut } :: ctx
  let (acc, accSrc, accTy, accInit) : Name × Name × STy × SAtom ← match absorbed, userAcc? with
    | some (x, x', s, ia), _ => pure (x', x, s, ia)
    | none, some l => pure (l.name, l.srcName, l.ty, .var l.name .missing)
    | none, none => do let a ← fresh; pure (a, a, .unit, unitAtom)
  -- The counter is the user's `i` when `lo` is 0, and otherwise a fresh `k` with `let i := k + lo`.
  let zeroLo := lo? == some 0
  let i' ← bindName ctx iSrc
  let kc ← if zeroLo then pure i' else fresh
  let ctxL := (if zeroLo then { mkLocal iSrc i' .u64 with bound := some cap }
    else { name := kc, ty := .u64 : Local }) ::
      { mkLocal accSrc acc accTy (if accTy == .unit then .own else .ownMut) with } :: ctx
  let ctxI := if zeroLo then ctxL else { mkLocal iSrc i' .u64 with bound := some cap } :: ctxL
  let loA := if ← doMutant "lo-ignored" then SAtom.lit .u64 (toExpr (0 : UInt64)) else loA
  let withI (e : AExp) : AExp := if zeroLo then e else
    .let_ i' .missing .u64 (.prim ⟨``Prim.add, [.u64, .u64], .u64⟩ [.var kc .missing, loA]) e
  -- The condition tests the flags first, then the run-time bound, then the user's condition.
  let flagConds ← ((retVars?.filter (fun _ => hasReturn) |>.map (·.1)).toList ++ brk?.toList)
    |>.mapM fun z => do pure (← `(!$(mkIdentFrom stx z))).raw
  let userConds ← userCond.toList.mapM fun c => do pure (← `(($(⟨c⟩)))).raw
  let parts : List Syntax := flagConds ++ condBound.toList ++ userConds
  let (ca, _) ← match parts.getLast?, parts.dropLast with
    | none, _ => pure (AExp.atom (.lit .bool (toExpr true)), STy.bool)
    | some p, ps => do
      let c ← ps.foldrM (fun q acc => `($(⟨q⟩) && $acc)) (⟨p⟩ : Term)
      let (ca, t) ← elabE ctxI c (some .bool)
      pure (withI ca, t)
  -- The body.
  let lj : LoopJ := { acc, accTy, user, brk? }
  let j' : DoJ := { j with loop? := some lj, retVars?, join? := none, outer? := j.loop? }
  let (ba, _) ← elabSeq j' ctxI body (some (pure (endOf lj, accTy))) none true
  let ba := withI ba
  for l in ctx do
    if l.ty.linear && !(ca.uses l.name matches .n 0) then
      throwErrorAt ((ca.firstUse l.name).getD stx)
        "the loop condition must not use the linear variable `{l.srcName}`"
  let loopA ← loopOf ctx stx n accTy accInit kc acc ca ba
  -- In the rest of the block an absorbed variable is the loop's result, and another accumulating
  -- variable is assigned it.
  let res ← if absorbed.isSome then pure acc else fresh
  let ctxR := if absorbed.isSome then mkLocal accSrc acc accTy .ownMut :: ctx else ctx
  let unitOuter := j.loop?.all (·.accTy == .unit)
  let (ka, kt) ← if !user && rest.isEmpty && (k?.isNone || (iterEnd && unitOuter)) then
      -- A loop that ends a unit block is the block's value.
      pure (.atom (if accTy == .unit then .var res .missing else unitAtom), STy.unit)
    else elabSeq j ctxR rest k? exp? iterEnd
  let ka := if userAcc?.isSome && !(← doMutant "acc-lost") then
      AExp.assign stx (.var acc .missing) accTy (.var res .missing) ka
    else ka
  if !user && rest.isEmpty && k?.isNone then expect stx exp? .unit
  -- After a loop that may have returned comes the result, or the end of the enclosing iteration.
  let ka ← if hasReturn && !(← doMutant "return-falls-through") then
      let some (f, r) := retVars? | throwErrorAt stx "internal error: return flag"
      -- A loop inside the outermost loop with `return` ends that loop's iteration.
      let out := match j.loop?, j.join? with
        | some _, _ => (jumpEnd j).1
        | none, some (some rv) =>
          .assign stx (.var (ctxVar ctx rv) .missing) (j.ret?.getD .unit) (.var r .missing)
            (.atom (boolAtom true))
        | none, _ => .atom (.var r .missing)
      pure (AExp.ite stx (.var f .missing) out ka)
    else pure ka
  return (wrap (pre ++ flagLets) (splice loopA res accTy ka), kt)

/-- The loop with body `ba`, built with `Exp.loop`. It carries the variables bound outside it that
the body writes, or moves when they are linear, since the body moves the old value of a linear
variable it assigns. The body hands back its accumulator with their values through one tuple
constructor naming them, so that the memory lowering keeps them in place, and the loop's result
is bound for the rest of the block. The loop's state is `(acc, (x₁, (x₂, … ())))`, which is the
accumulator, a word variable or `()`, followed by the carried variables of the program in the
order they are declared, and then the flag and value of `return`. -/
partial def loopOf (ctx : Ctx) (stx : Syntax) (n : Expr) (s : STy) (ia : SAtom) (i acc : Name)
    (ca ba : AExp) : M AExp := do
  let moved := ctx.filter (fun l => l.ty.linear && l.kind == .ownMut && !(ba.uses l.name matches .n 0))
  let ws := (ba.writes ++ ca.writes ++ moved.map (·.name)).filter fun z => z != i && z != acc
  let names := ws.foldl (fun l z => if l.contains z then l else l ++ [z]) []
  -- Declaration order, since the context is innermost first, with the flags last.
  let pos (z : Name) : Nat := ctx.length - (ctx.findIdx? (·.name == z)).getD 0
  let flag (z : Name) : Bool := isTemp ((lookupVar ctx z).map (·.srcName) |>.getD z)
  let names := names.toArray.qsort (fun a b =>
    if flag a != flag b then !flag a else pos a < pos b) |>.toList
  let carried ← names.mapM fun z => do
    let some l := lookupVar ctx z | throwErrorAt stx "internal error: unbound `{z}`"
    pure (z, l.ty)
  let body ← mapTail ba s fun a => tupleE s a carried (folded := true)
  let y ← fresh
  return .loop stx n s ia i acc carried ca body y (.atom (.var y .missing))

end

/-! ## Emission of the de Bruijn term -/

/-- `Mem t Γ` for position `k` of `ctx`. -/
def memExpr : List STy → Nat → Expr
  | t :: rest, 0 => mkApp2 (mkConst ``Mem.here) t.toTy (tyList rest)
  | s :: rest, k + 1 =>
    match rest[k]? with
    | some t => mkApp4 (mkConst ``Mem.there) t.toTy s.toTy (tyList rest) (memExpr rest k)
    | none => default
  | [], _ => default

/-- The types of a context. -/
def Ctx.tys (ctx : Ctx) : List STy := ctx.map (·.ty)

/-- The `Atom Γ t` term for a named atom. -/
def atomExpr (ctx : Ctx) (a : SAtom) : MetaM (Expr × STy) := do
  let Γ := tyList ctx.tys
  match a with
  | .lit t v => return (mkApp3 (mkConst ``Atom.lit) Γ t.toTy v, t)
  | .var n _ =>
    let some k := ctx.findIdx? (·.name == n) | throwError "internal error: unbound {n}"
    let t := ctx[k]!.ty
    return (mkApp3 (mkConst ``Atom.var) Γ t.toTy (memExpr ctx.tys k), t)

/-- The `Args Γ ps` term for atoms, in the order of `ps`. -/
def argsExpr (ctx : Ctx) : List SAtom → MetaM (Expr × List STy)
  | [] => return (mkApp (mkConst ``Args.nil) (tyList ctx.tys), [])
  | a :: as => do
    let (ae, t) ← atomExpr ctx a
    let (re, ts) ← argsExpr ctx as
    return (mkApp5 (mkConst ``Args.cons) (tyList ctx.tys) t.toTy (tyList ts) ae re, t :: ts)

/-- The `Args Γ ps` term for atoms, with the parameter types `ps` given. They may differ from the
atoms' types up to unfolding, as `Ty.tup []` differs from `Ty.unit`. -/
def argsExprT (ctx : Ctx) : List SAtom → List STy → MetaM Expr
  | a :: as, t :: ts => do
    let (ae, _) ← atomExpr ctx a
    let re ← argsExprT ctx as ts
    return mkApp5 (mkConst ``Args.cons) (tyList ctx.tys) t.toTy (tyList ts) ae re
  | _, _ => return mkApp (mkConst ``Args.nil) (tyList ctx.tys)

/-- An `Inhabited t.carrier` instance, which gives the default of a partial selector. -/
def inhabitedExpr (t : STy) : MetaM Expr := do
  match ← synthInstance? (mkApp (mkConst ``Inhabited [1]) t.carrier) with
  | some i => return i
  | none => throwError "the type {t} needs an `Inhabited` instance (the value read by a `!` \
      access when its obligation fails)"

/-- The `Place Γ t` term for a named place. -/
partial def placeExpr (ctx : Ctx) (p : SPlace) : MetaM (Expr × STy) := do
  let Γ := tyList ctx.tys
  match p with
  | .var n _ =>
    let some k := ctx.findIdx? (·.name == n) | throwError "internal error: unbound {n}"
    let t := ctx[k]!.ty
    return (mkApp3 (mkConst ``Place.var) Γ t.toTy (memExpr ctx.tys k), t)
  | .field q l _ t _ =>
    let (qe, s) ← placeExpr ctx q
    return (mkApp5 (mkConst ``Place.field) Γ s.toTy t.toTy qe l, t)
  | .index q i _ | .slot q i _ | .elem q i _ =>
    let (qe, s) ← placeExpr ctx q
    let some (e, n, _) := selOf s | throwError "internal error: selector on {s}"
    let (ie, _) ← atomExpr ctx i
    let c := match p with | .index .. => ``Place.index | _ => ``Place.slot
    return (mkAppN (mkConst c) #[Γ, e.toTy, n, ← inhabitedExpr e, qe, ie], e)
  | .range q lo len _ =>
    let (qe, s) ← placeExpr ctx q
    let (le, _) ← atomExpr ctx lo
    let (ne, _) ← atomExpr ctx len
    match s, q with
    | .arr e n, _ =>
      return (mkAppN (mkConst ``Place.range) #[Γ, e.toTy, n, qe, le, ne], .slice e n)
    | .slice e n, .var x _ =>
      -- A sub-slice of a view variable.
      let some k := ctx.findIdx? (·.name == x) | throwError "internal error: unbound {x}"
      return (mkAppN (mkConst ``Place.rangeS) #[Γ, e.toTy, n, memExpr ctx.tys k, le, ne],
        .slice e n)
    | _, _ => throwError "internal error: range on {s}"
  | .pair2 q i j _ =>
    let (qe, s) ← placeExpr ctx q
    let (ie, _) ← atomExpr ctx i
    let (je, _) ← atomExpr ctx j
    match s, q with
    | .arr e n, _ =>
      return (mkAppN (mkConst ``Place.pair2) #[Γ, e.toTy, n, ← inhabitedExpr e, qe, ie, je],
        .pair e e)
    | .slice e n, .var x _ =>
      -- Two cells of a view variable.
      let some k := ctx.findIdx? (·.name == x) | throwError "internal error: unbound {x}"
      return (mkAppN (mkConst ``Place.pair2S)
        #[Γ, e.toTy, n, ← inhabitedExpr e, memExpr ctx.tys k, ie, je], .pair e e)
    | _, _ => throwError "internal error: pair2 on {s}"

/-- The `List ExtParam` term. -/
def extParamsExpr (ps : List EPTy) : Expr :=
  ps.foldr (fun p acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``ExtParam)
      (match p with
        | .word => mkConst ``ExtParam.word
        | .bytes => mkConst ``ExtParam.bufIn
        | .outByte => mkApp (mkConst ``ExtParam.bufOut) (toExpr (1 : Nat))
        | .sliceOut => mkConst ``ExtParam.sliceOut) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``ExtParam))

/-- The `EArgs Γ ps` term. -/
def eargsExpr (ctx : Ctx) : List EArg → List EPTy → MetaM Expr
  | [], _ => return mkApp (mkConst ``EArgs.nil) (tyList ctx.tys)
  | .word a :: as, _ :: ps => do
    let (ae, _) ← atomExpr ctx a
    return mkApp4 (mkConst ``EArgs.word) (tyList ctx.tys) (extParamsExpr ps) ae
      (← eargsExpr ctx as ps)
  | .bytes bs :: as, _ :: ps => do
    let Γ := tyList ctx.tys
    return mkApp4 (mkConst ``EArgs.bufIn) Γ (extParamsExpr ps)
      (mkApp2 (mkConst ``Buf.const) Γ (toExpr bs)) (← eargsExpr ctx as ps)
  | .outByte :: as, _ :: ps => do
    return mkApp4 (mkConst ``EArgs.bufOut) (tyList ctx.tys) (extParamsExpr ps) (toExpr (1 : Nat))
      (← eargsExpr ctx as ps)
  | .slice (.range q lo len _) :: as, _ :: ps => do
    let Γ := tyList ctx.tys
    let (qe, qt) ← placeExpr ctx q
    let .arr _ n := qt | throwError "internal error: slice of {qt}"
    let (le, _) ← atomExpr ctx lo
    let (ne, _) ← atomExpr ctx len
    return mkApp4 (mkConst ``EArgs.bufIn) Γ (extParamsExpr ps)
      (mkAppN (mkConst ``Buf.slice) #[Γ, n, qe, le, ne]) (← eargsExpr ctx as ps)
  | .sliceOut (.range q lo len _) :: as, _ :: ps => do
    let Γ := tyList ctx.tys
    let (qe, qt) ← placeExpr ctx q
    let .arr _ n := qt | throwError "internal error: slice of {qt}"
    let (le, _) ← atomExpr ctx lo
    let (ne, _) ← atomExpr ctx len
    return mkAppN (mkConst ``EArgs.sliceOut)
      #[Γ, extParamsExpr ps, n, qe, le, ne, ← eargsExpr ctx as ps]
  | _ :: _, _ :: _ => throwError "internal error: an extern's slice argument is not a slice"
  | _, [] => throwError "internal error: extern arity"

/-- The `RArgs Γ ps os` term, with the arguments in the callee's context order. -/
def rargsExpr (ctx : Ctx) : List (RArg × STy) → MetaM (Expr × List STy × List STy)
  | [] => return (mkApp (mkConst ``RArgs.nil) (tyList ctx.tys), [], [])
  | (a, t) :: as => do
    let (re, ps, os) ← rargsExpr ctx as
    let Γ := tyList ctx.tys
    match a with
    | .own x =>
      let (xe, _) ← atomExpr ctx x
      return (mkAppN (mkConst ``RArgs.own) #[Γ, t.toTy, tyList ps, tyList os, xe, re], t :: ps, os)
    | .shr p =>
      let (pe, _) ← placeExpr ctx p
      return (mkAppN (mkConst ``RArgs.shr) #[Γ, t.toTy, tyList ps, tyList os, pe, re], t :: ps, os)
    | .mut p =>
      let (pe, _) ← placeExpr ctx p
      return (mkAppN (mkConst ``RArgs.mut) #[Γ, t.toTy, tyList ps, tyList os, pe, re], t :: ps,
        t :: os)

/-- The callee's context, which is its parameters with the last first, and the types of its `mut`
parameters in the same order. -/
def FnInfo.psOs (f : FnInfo) : List STy × List STy :=
  let ps := f.params.toList.reverse
  (ps.map (·.2.1), ps.filterMap fun (_, t, m) => if m == .mut then some t else none)

/-- The type of the Core term, which is the result, or for a reference function the result with
the final values of the `mut` parameters. -/
def FnInfo.expTy (f : FnInfo) : STy :=
  if f.isRef then .pair f.ret (.tup f.psOs.2) else f.ret

/-- The `Ty` term of the Core term's type, with `Ty.tup` folded as in the signature of
`Exp.callRef`, so that the rewrite lemmas of `Sem.lean` match it syntactically. -/
def FnInfo.expTyExpr (f : FnInfo) : Expr := f.expTy.toTy

/-- The type of the Core term with the tuple expanded, which is the type of the emitted body. -/
def FnInfo.expTyX (f : FnInfo) : STy :=
  if f.isRef then .pair f.ret (tupX f.psOs.2) else f.ret

/-- The `Exp Γ t` term for a named ANF term in context `ctx`. -/
partial def emit (ctx : Ctx) (e : AExp) : MetaM (Expr × STy) := do
  let Γ := tyList ctx.tys
  let bind (x : Name) (t : STy) : Ctx := { name := x, ty := t } :: ctx
  match e with
  | .atom a =>
    let (ae, t) ← atomExpr ctx a
    return (mkApp3 (mkConst ``Exp.atom) Γ t.toTy ae, t)
  | .let_ x _ s e₁ e₂ =>
    let (e₁', _) ← emit ctx e₁
    let (e₂', t) ← emit (bind x s) e₂
    return (mkApp5 (mkConst ``Exp.let_) Γ s.toTy t.toTy e₁' e₂', t)
  | .ite _ c e₁ e₂ =>
    let (ce, _) ← atomExpr ctx c
    let (e₁', t) ← emit ctx e₁
    let (e₂', _) ← emit ctx e₂
    return (mkApp5 (mkConst ``Exp.ite) Γ t.toTy ce e₁' e₂', t)
  | .prim p args =>
    let (ae, _) ← argsExpr ctx args
    return (mkApp5 (mkConst ``Exp.prim) Γ (tyList p.ins) p.out.toTy (mkConst p.con) ae, p.out)
  | .loop _ n s init i acc carried c b x k =>
    let accName ← if s == .unit then pure "_" else loopVarName acc
    let names := #[accName] ++ (← carried.toArray.mapM fun (z, _) => loopVarName z)
    loopNamesRef.modify (·.push names)
    let (ie, _) ← atomExpr ctx init
    let ctx' := { name := i, ty := .u64 : Local } :: { name := acc, ty := s : Local } :: ctx
    let (ce, _) ← emit ctx' c
    let (be, _) ← emit ctx' b
    let (ke, u) ← emit (bind x s) k
    let ts := carried.map (·.2)
    let cse ← carried.foldrM (fun (z, t) (rest : Expr × List STy) => do
        let some j := ctx.findIdx? (·.name == z) | throwError "internal error: unbound {z}"
        return (mkAppN (mkConst ``Carry.cons) #[Γ, t.toTy, tyList rest.2, memExpr ctx.tys j, rest.1],
          t :: rest.2))
      (mkApp (mkConst ``Carry.nil) Γ, [])
    return (mkAppN (mkConst ``Exp.loop)
      #[Γ, tyList ts, s.toTy, u.toTy, n, cse.1, ie, ce, be, ke], u)
  | .call f args =>
    let (ae, _) ← argsExpr ctx args.reverse
    let ps := f.params.toList.reverse.map (·.2.1)
    return (mkAppN (mkConst ``Exp.call)
      #[Γ, tyList ps, f.ret.toTy, toExpr f.declName.toString, f.const `exp, ae],
      f.ret)
  | .ok ε α a =>
    let (ae, _) ← atomExpr ctx a
    return (mkApp4 (mkConst ``Exp.ok) Γ ε.toTy α.toTy ae, .result ε α)
  | .err ε α a =>
    let (ae, _) ← atomExpr ctx a
    return (mkApp4 (mkConst ``Exp.err) Γ ε.toTy α.toTy ae, .result ε α)
  | .match_ _ ε α s x eE y eO =>
    let (se, _) ← atomExpr ctx s
    let (eE', t) ← emit (bind x ε) eE
    let (eO', _) ← emit (bind y α) eO
    return (mkAppN (mkConst ``Exp.match_) #[Γ, ε.toTy, α.toTy, t.toTy, se, eE', eO'], t)
  | .ext x args =>
    let ae ← eargsExpr ctx args (x.params.toList.map (·.2))
    return (mkApp3 (mkConst ``Exp.ext) Γ (mkConst x.declName) ae, .u64)
  | .extMut _ x args y k =>
    let ae ← eargsExpr ctx args (x.params.toList.map (·.2))
    let (ke, u) ← emit (bind y .u64) k
    return (mkAppN (mkConst ``Exp.extMut) #[Γ, u.toTy, mkConst x.declName, ae, ke], u)
  | .mk c ins out args =>
    let ae ← argsExprT ctx args ins
    return (mkAppN (mkConst ``Exp.mk) #[Γ, tyList ins, out.toTy, c, ae], out)
  | .read _ p _ =>
    let (pe, t) ← placeExpr ctx p
    return (mkApp3 (mkConst ``Exp.read) Γ t.toTy pe, t)
  | .assign _ p _ a k =>
    let (pe, t) ← placeExpr ctx p
    let (ae, _) ← atomExpr ctx a
    let (ke, u) ← emit ctx k
    return (mkAppN (mkConst ``Exp.assign) #[Γ, t.toTy, u.toTy, pe, ae, ke], u)
  | .case _ s sp t pt qt x _ eP y eQ =>
    let (se, _) ← atomExpr ctx s
    let (pE, u) ← emit (bind x pt) eP
    let (qE, _) ← emit (bind y qt) eQ
    return (mkAppN (mkConst ``Exp.case) #[Γ, t.toTy, pt.toTy, qt.toTy, u.toTy, se, sp, pE, qE], u)
  | .put _ p i a k =>
    let (pe, st) ← placeExpr ctx p
    let .slots t n := st | throwError "internal error: put on {st}"
    let (ie, _) ← atomExpr ctx i
    let (ae, _) ← atomExpr ctx a
    let (ke, u) ← emit ctx k
    return (mkAppN (mkConst ``Exp.put) #[Γ, t.toTy, n, u.toTy, pe, ie, ae, ke], u)
  | .take _ p i x _ t k =>
    let (pe, st) ← placeExpr ctx p
    let .slots _ n := st | throwError "internal error: take on {st}"
    let (ie, _) ← atomExpr ctx i
    let (ke, u) ← emit (bind x t) k
    return (mkAppN (mkConst ``Exp.take)
      #[Γ, t.toTy, n, u.toTy, ← inhabitedExpr t, pe, ie, ke], u)
  | .borrow _ excl p t r _ body u x k =>
    let (pe, _) ← placeExpr ctx p
    let (be, _) ← emit (bind r t) body
    let (ke, v) ← emit (bind x u) k
    let c := if excl then ``Exp.borrowMut else ``Exp.borrowShr
    return (mkAppN (mkConst c) #[Γ, t.toTy, u.toTy, v.toTy, pe, be, ke], v)
  | .callRef _ f args x k =>
    let (ps, os) := f.psOs
    let (re, _, _) ← rargsExpr ctx (args.reverse.zip ps)
    let (ke, u) ← emit (bind x f.ret) k
    return (mkAppN (mkConst ``Exp.callRef) #[Γ, tyList ps, tyList os, f.ret.toTy, u.toTy,
      toExpr f.declName.toString, f.const `req, f.const `exp, re,
      ke], u)
  | .guard _ g =>
    let ge ← match g with
      | .valid p => do
        let (pe, t) ← placeExpr ctx p
        -- `p.checkable = true` holds by `rfl`, since the elaborator builds guards only on
        -- checkable places.
        pure (mkApp4 (mkConst ``Guard.valid) Γ t.toTy pe
          (mkApp2 (mkConst ``rfl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))
    return (mkApp2 (mkConst ``Exp.guard) Γ ge, .result .unit .unit)

/-! ## The simp-normal form -/

/-- Lemmas of the normal-form simp set common to both views. -/
def commonLemmas : List Name :=
  [``Env.get_here, ``Env.get_there, ``Env.set_here, ``Env.set_there, ``pure_bind, ``bind_assoc,
   ``decide_eq_true_eq, ``decide_not, ``Bool.not_eq_true', ``Bool.and_eq_true, ``Bool.or_eq_true,
   ``beq_iff_eq, ``Bool.not_eq_eq_eq_not, ``Bool.not_true, ``Bool.not_false, ``ite_not,
   ``decide_eq_false_iff_not, ``beq_true, ``beq_false, ``Bool.not_not, ``bne_iff_ne, ``ne_eq,
   ``eq_self_iff_true, ``ite_true, ``ite_false, ``Bool.false_eq_true, ``Bool.true_and,
   ``Bool.and_true, ``Flat.tupBuild_cons, ``Flat.tupBuild_nil,
   -- The accumulator of a loop carrying nothing, projected at the body's tails.
   ``map_bind, ``LawfulApplicative.map_pure, ``map_ite,
   -- Bytes computed through words with `zext8` and `trunc8` read back as byte operations.
   ``UInt8.toUInt8_toUInt64, ``UInt64.toUInt8_add, ``UInt64.toUInt8_sub, ``UInt64.toUInt8_mul,
   ``UInt64.toUInt8_and, ``UInt64.toUInt8_or, ``UInt64.toUInt8_xor, ``trunc8_div, ``trunc8_mod,
   ``UInt8.toUInt64_inj, ``UInt8.toUInt64_lt, ``UInt8.toUInt64_le]

/-- Definitions the normal-form simp set unfolds. -/
def commonUnfolds : List Name :=
  [``Atom.denote, ``Args.denote, ``Prim.denote, ``ExtSig.call, ``EArgs.words, ``EArgs.bytesIn, ``EArgs.outCaps,
   ``EArgs.fill, ``List.headD, ``List.tail,
   ``Buf.denote, ``Place.get, ``Place.set, ``Place.check, ``RArgs.denote, ``RArgs.writeBack,
   ``Guard.denote, ``Lens.fst, ``Lens.snd, ``Ctor.pairMk, ``Ctor.tupMk, ``Ctor.vec, ``Ctor.fill,
   ``Ctor.slotsEmpty, ``Env.elems, ``Carry.get, ``Carry.set]

/-- Lemmas for the `Id` view, `Exp.run`. -/
def runLemmas : List Name :=
  [``Exp.run_atom, ``Exp.run_let, ``Exp.run_ite, ``Exp.run_prim, ``Exp.run_call,
   ``Exp.run_ok, ``Exp.run_err, ``Exp.run_match, ``Exp.run_mk, ``Exp.run_read, ``Exp.run_assign,
   ``Exp.run_case, ``Exp.run_put, ``Exp.run_take, ``Exp.run_borrowShr, ``Exp.run_borrowMut,
   ``Exp.run_callRef, ``Exp.run_guard, ``Exp.run_loop, ``Exp.run_loop_nil]

/-- Lemmas for the `StateM World` view, `Exp.denoteM`. -/
def denoteMLemmas : List Name :=
  [``Exp.denoteM_atom, ``Exp.denoteM_let, ``Exp.denoteM_ite, ``Exp.denoteM_prim,
   ``Exp.denoteM_call, ``Exp.denoteM_ok, ``Exp.denoteM_err,
   ``Exp.denoteM_match, ``Exp.denoteM_ext, ``Exp.denoteM_extMut, ``Exp.denoteM_mk, ``Exp.denoteM_read,
   ``Exp.denoteM_assign, ``Exp.denoteM_case, ``Exp.denoteM_put, ``Exp.denoteM_take,
   ``Exp.denoteM_borrowShr, ``Exp.denoteM_borrowMut, ``Exp.denoteM_callRef,
   ``Exp.denoteM_guard, ``Exp.denoteM_loop, ``Exp.denoteM_loop_nil]

/-- Run `simp` with the given lemmas, the local hypotheses `hyps`, the definitions to unfold and
the default simprocs. -/
def simpWith (e : Expr) (lemmas unfolds : List Name) (hyps : Array Expr := #[]) :
    MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for h in hyps do thms ← thms.add (.fvar h.fvarId!) #[] h
  -- A loop carrying nothing gets its own lemma, `forIn` over the accumulator alone.
  for n in lemmas do
    thms ← thms.addConst n (prio := if n == ``Exp.run_loop_nil || n == ``Exp.denoteM_loop_nil
      then 2000 else eval_prio default)
  for n in unfolds do thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx (simprocs := #[← Simp.getSimprocs])
  return r

/-- Synthesise the `Decidable` instance of every `if` and `dite` again. Simp does not rewrite
instance arguments, so after a condition is rewritten its instance can be an awkward cast. -/
def resynthDecidable (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
      let args := e.getAppArgs
      if let some inst ← synthInstance? (mkApp (mkConst ``Decidable) args[1]!) then
        return .done (mkAppN e.getAppFn (args.set! 2 inst))
    return .done e)

/-- Whether `e` mentions a constant of the Core language, which means the normal form was not
reached. -/
def mentionsCore (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => n == ``Exp.run || n == ``Exp.denoteM || n == ``Exp.denote || n == ``Exp.eval
    | _ => false).isSome

/-- Replace every carrier `t.carrier` whose type `t` reduces reducibly to a literal `⟨C, _⟩` by
`C`, and every carrier of a tuple type `(Ty.tup ts).carrier` by the nested product it unfolds to,
such as `A × (B × Unit)`. The two forms are definitionally equal, but the folded form, which
`Exp.run_callRef` leaves in the type arguments of a call's `bind`, keeps `simp` and `vcgen` from
matching lemmas about the callee. `vcgen`'s matcher is structural and does not reduce a
projection of a structure literal, so `Spec.pure` fails on a `bind` at a folded carrier over a
`pure` at the reduced one. -/
def expandTupCarriers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Ty.carrier 1 then
      if e.appArg!.isAppOfArity ``Ty.tup 1 then
        return .visit (← withTransparency .default <| whnf e)
      -- Any type that reduces reducibly to a literal `⟨C, _⟩`, such as `Ty.u64`, `Ty.pair a b`,
      -- `Ty.view T n`, `Ty.slots T n` or a struct's type, gives its carrier `C`, expanded further.
      match (← whnfR e.appArg!).getAppFnArgs with
      | (``Ty.mk, #[c, _]) => return .visit c
      | _ => pure ()
    return .done e)

/-- Simp-normalise `lhs`, a monadic view of a term, and return the normal form and a proof of
`lhs = nf`. There are two passes with the `Decidable` instances synthesised again in between, and
then the tuple carriers are expanded, which is a definitional change. -/
def normalForm (lhs : Expr) (lemmas unfolds : List Name) (hyps : Array Expr := #[]) :
    MetaM (Expr × Expr) := do
  let (nf, p) ← go
  return (← expandTupCarriers nf, p)
where
  go : MetaM (Expr × Expr) := do
    let r ← simpWith lhs lemmas unfolds hyps
    let nf₁ ← instantiateMVars r.expr
    let p₁ ← r.getProof
    let nf₂ ← resynthDecidable nf₁
    if nf₂ == nf₁ then return (nf₁, p₁)
    -- The second pass: `nf₁` and `nf₂` differ only in `Decidable` instances, which are
    -- subsingletons.
    let goal ← mkFreshExprMVar (← mkEq nf₁ nf₂)
    let gs ← try goal.mvarId!.congrN catch _ => pure [goal.mvarId!]
    if gs.isEmpty then
      return (nf₂, ← mkEqTrans p₁ (← instantiateMVars goal))
    return (nf₁, p₁)

/-- `e` with the bound of every loop `Exp.loop b …` whose `b` is among `bs` replaced by the
corresponding local of `ns`. -/
partial def abstractLoopBounds (bs ns : Array Expr) (e : Expr) : Expr :=
  e.replace fun e => do
    guard (e.isAppOfArity ``Exp.loop 10)
    let args := e.getAppArgs
    let j ← bs.idxOf? args[4]!
    some (mkAppN e.getAppFn ((args.map (abstractLoopBounds bs ns)).set! 4 ns[j]!))

/-- A callee of a function, as its normal form is computed: the callee's Core term `g.exp` and
its normal form `g`, both at the generic arguments of the call, and the equation between their
views (`g.exp_run` or `g.exp_denoteM`) at the same arguments. -/
structure CalleeEq where
  exp : Expr
  fn : Expr
  eq : Expr

/-- The normal form of the view `lhsOf e` of a Core term `e`, rewritten by `post`, and a proof
that the view `stmtOf e`, definitionally equal to `lhsOf e`, equals it.

Both are computed with every loop bound of `e` replaced by a local `n : Nat`, and every callee by
locals for its term, its normal form and the equation between them, which `simp` uses in place of
the callee's lemma. The proof is a function of these locals applied to the bounds and the callees.
The kernel checks its body, including the definitional steps that `simp`, `post` and `stmtOf`
leave, with the locals opaque: `forIn (upto n)` does not reduce and a callee does not unfold, so
the cost of the check does not depend on the bound of any loop, the function's own or a callee's.
With the literal bound and the callee's definition, the kernel can evaluate the loop symbolically
whenever it compares two terms that differ by unfolding around it, at a cost that grows with the
bound. -/
def normalFormOfExp (e : Expr) (callees : Array CalleeEq) (lhsOf stmtOf : Expr → Expr)
    (lemmas unfolds : List Name) (post : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let found ← IO.mkRef (#[] : Array Expr)
  e.forEach fun s => do
    if s.isAppOfArity ``Exp.loop 10 then
      let b := s.getArg! 4
      unless b.hasLooseBVars || b.isFVar || (← found.get).contains b do
        found.modify (·.push b)
  let bs ← found.get
  -- A callee called twice, at the same generic arguments, is abstracted once.
  let callees := callees.foldl (fun acc c => if acc.any (·.exp == c.exp) then acc else acc.push c)
    #[]
  let mut cDecls : Array (Name × Expr) := #[]
  for c in callees do
    cDecls := cDecls.push (`gExp, ← inferType c.exp)
  withLocalDeclsDND (bs.mapIdx fun i _ => (Name.mkSimple s!"n{i}", mkConst ``Nat)) fun ns =>
  withLocalDeclsDND cDecls fun gEs => do
  let fnDecls ← callees.mapM fun c => return (`g, ← inferType c.fn)
  withLocalDeclsDND fnDecls fun gFs => do
  let olds := callees.map (·.exp) ++ callees.map (·.fn)
  let news := gEs ++ gFs
  let abs (t : Expr) : Expr := t.replace fun s => (olds.idxOf? s).map (news[·]!)
  let hDecls ← callees.mapM fun c => return (`gEq, abs (← instantiateMVars (← inferType c.eq)))
  withLocalDeclsDND hDecls fun gHs => do
    let e' := abs (abstractLoopBounds bs ns e)
    let (nf, prf) ← normalForm (lhsOf e') lemmas unfolds gHs
    let nf ← post nf
    -- The statement over the locals, so that the kernel compares the proof's type with it while
    -- the bounds and callees are still opaque.
    let prf ← mkExpectedTypeHint (← instantiateMVars prf) (← mkEq (stmtOf e') nf)
    let nf := nf.replaceFVars (ns ++ news) (bs ++ olds)
    return (nf, mkAppN (← mkLambdaFVars (ns ++ news ++ gHs) prf)
      (bs ++ olds ++ callees.map (·.eq)))

/-! ## Declarations -/

/-- Add a definition checked by the kernel, enable realizations for it, and compile it. -/
def addDef (n : Name) (type value : Expr) (compile := true) : TermElabM Unit := do
  -- A generic definition is abstracted over its variables.
  let gvs ← genVarsRef.get
  let type ← instantiateMVars (← mkForallFVars gvs type (usedOnly := false))
  let value ← instantiateMVars (← mkLambdaFVars gvs value (usedOnly := false))
  -- The height is the one Lean's own `def` gives: one more than the constants in the value. The
  -- kernel unfolds the higher of two definitions first, so `f x` against its own unfolded body
  -- unfolds `f`, not the loops inside the body.
  let decl := Declaration.defnDecl
    { name := n, levelParams := [], type := type, value := value,
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
  addDecl decl
  enableRealizationsForConst n
  if compile then
    try compileDecl decl (logErrors := false)
    catch _ => pure ()

/-- Add a theorem checked by the kernel, with `addThmChecked`, so that a theorem the kernel
rejects is an error of the command that generates it, which then stops before it registers the
function. -/
def addThm (n : Name) (type value : Expr) : TermElabM Unit := do
  let gvs ← genVarsRef.get
  let type ← instantiateMVars (← mkForallFVars gvs type (usedOnly := false))
  let value ← instantiateMVars (← mkLambdaFVars gvs value (usedOnly := false))
  let value := if n.componentsRev.head? == some (.mkSimple (mp.selftest.badProof.get
      (← getOptions))) then mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    else value
  addThmChecked n type value

/-- Add a theorem found by an automatic attempt, checked by the kernel now within `budget`
thousands of heartbeats. It returns `false` and adds nothing if the kernel gives up. A proof that
is cheap to find can be very expensive to check, for example when the kernel unfolds a long loop
over a large array, so an automatic attempt must not hand it unbounded to the asynchronous
check. -/
def addThmBudget (n : Name) (type value : Expr) (budget : Nat) : TermElabM Bool := do
  let s ← saveState
  try
    withOptions (fun o => maxHeartbeats.set (Elab.async.set o false) budget) do
      addThm n type value
    return true
  catch _ =>
    s.restore
    return false

/-- The environment `Env.cons xₙ (… (Env.cons x₁ Env.nil))` for the parameters `x₁ … xₙ`, in which
the last parameter is index 0. -/
def envExpr (params : List (Expr × STy)) : Expr :=
  let rec go : List (Expr × STy) → Expr × List STy
    | [] => (mkConst ``Env.nil, [])
    | (x, t) :: rest =>
      let (e, ts) := go rest
      (mkApp4 (mkConst ``Env.cons) t.toTy (tyList ts) x e, t :: ts)
  (go params.reverse).1

/-- The statement `b = true` and its proof by kernel evaluation with `decide`, not yet checked. -/
def decideProof (b : Expr) : MetaM (Expr × Expr) := do
  let prop ← mkEq b (mkConst ``Bool.true)
  return (prop, mkApp3 (mkConst ``of_decide_eq_true) prop
    (mkApp2 (mkConst ``instDecidableEqBool) b (mkConst ``Bool.true))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))

/-- The borrow checker of a generic definition. `Exp.wf` reads a type only through its
linearity, so every `Data T` variable whose `T` is copyable, with `[Data.Copy T]`, is replaced by
`Data.copyInst T`, the same instance with `linear := false`, which reduces. The kernel decides the
result, `prf` being the `decide` proof at the replaced proposition, and `Data.copyInst_eq` carries
it back. The result is `none` when a type variable's linearity is unknown because it has no
`Data.Copy`, and then `wf` is decided per instance when `compile` checks it. -/
def genericWf (prop prf : Expr) (gvs : Array Expr) : MetaM (Option Expr) := do
  -- The `Data` instance variables of copyable types, each with its `Data.Copy` variable.
  let mut insts : Array (Expr × Expr × Expr) := #[]
  -- An implementation parameter such as `A : Alloc V` makes its callees' bodies opaque, so there is
  -- no generic `wf`.
  for v in gvs do
    let ty ← whnfR (← instantiateMVars (← inferType v))
    unless ty.isSort || ty.isConstOf ``Nat || ty.isAppOfArity ``Data 1 ||
        ty.isAppOfArity ``Data.Copy 2 || ty.isAppOfArity ``Inhabited 1 || (← isProp ty) do
      return none
  for v in gvs do
    let ty ← whnfR (← inferType v)
    if ty.isAppOfArity ``Data 1 then
      let α := ty.appArg!
      let deps ← gvs.filterM fun u => do
        return u != v && (← instantiateMVars (← inferType u)).containsFVar v.fvarId!
      let [c] := deps.toList | return none
      unless (← instantiateMVars (← inferType c)).isAppOfArity ``Data.Copy 2 do return none
      insts := insts.push (v, α, c)
  let cpy (α : Expr) := mkApp2 (mkConst ``Data.copyInst) α
  let at_ (k : Nat) (e : Expr) : Expr :=
    -- The instances from `k` on, replaced by their copies, with the copy's `Data.Copy` by `rfl`.
    let rest := insts.extract k insts.size
    e.replaceFVars (rest.flatMap fun (v, α, c) => #[v, c])
      (rest.flatMap fun (v, α, _) => #[cpy α v, mkApp3 (mkConst ``Data.Copy.mk) α (cpy α v)
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))])
  -- The `decide` proof at the fully replaced proposition.
  let mut p := at_ 0 prf
  -- Carry the proof back one instance at a time, through
  -- `(fun d => ∀ c : Data.Copy α d, P d c)` from the copy to `v`.
  for k in [0:insts.size] do
    let (v, α, c) := insts[k]!
    let next := at_ (k + 1) prop
    let motive ← withLocalDeclD `d (mkApp (mkConst ``Data) α) fun d =>
      withLocalDeclD `c (mkApp2 (mkConst ``Data.Copy) α d) fun c' => do
        mkLambdaFVars #[d] (← mkForallFVars #[c'] ((next.replaceFVar c c').replaceFVar v d))
    let atCopy ← withLocalDeclD `c (mkApp2 (mkConst ``Data.Copy) α (cpy α v)) fun c' => do
      mkLambdaFVars #[c'] p
    let h := mkApp3 (mkConst ``Data.copyInst_eq) α v c
    p := mkApp (← mkEqNDRec motive atCopy h) c
  return some p

/-- A proof of `b = true` by kernel evaluation, after checking it with `whnf`. -/
def decideTrue (b : Expr) : MetaM (Option (Expr × Expr)) := do
  let v ← withTransparency .all <| whnf b
  unless v.isConstOf ``Bool.true do return none
  decideProof b

/-- The `Slots` components of a loop state of type `ty`, which is nested pairs, as projections. -/
partial def slotsComps (ty : Expr) (proj : Expr → MetaM Expr) (fuel : Nat := 16) :
    MetaM (List (Expr → MetaM Expr)) := do
  if fuel == 0 then return []
  let ty0 := mkSort Level.one
  let A ← mkFreshExprMVar ty0; let B ← mkFreshExprMVar ty0
  if ← isDefEq ty (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) A B) then
    let l ← slotsComps (← instantiateMVars A) (fun e => do mkAppM ``Prod.fst #[← proj e]) (fuel - 1)
    let r ← slotsComps (← instantiateMVars B) (fun e => do mkAppM ``Prod.snd #[← proj e]) (fuel - 1)
    return l ++ r
  let α ← mkFreshExprMVar ty0; let n ← mkFreshExprMVar (mkConst ``Nat)
  if ← isDefEq ty (mkApp2 (mkConst ``Slots) α n) then return [proj]
  return []

/-- Split the obligations of a loop whose state has `Slots` components, which are carried slice
views, with `loopSafe_of_inv_cond` and the invariant that each such component has the same full
cells as at the loop's start. A slice view is written only through its cells, which stay full, so
the obligation of an element `s[i]` that cell `i` is full follows from the function's `requires`.
It fails on a state without such a component. -/
def loopInvSlots (g : MVarId) : MetaM (Option (List MVarId)) := do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  unless tgt.isAppOfArity ``loopSafe 9 do return none
  let σ := tgt.getArg! 0
  let acc := tgt.getArg! 7
  let comps ← slotsComps σ pure
  if comps.isEmpty then return none
  let P ← withLocalDeclD `st σ fun st => do
    let conjs ← comps.mapM fun pr => do
      let a ← pr st; let b ← pr acc
      withLocalDeclD `k (mkConst ``Nat) fun k => do
        mkForallFVars #[k] (← mkEq (← mkAppM ``Slots.isFull #[a, k]) (← mkAppM ``Slots.isFull #[b, k]))
    let body := conjs.dropLast.foldr (fun c acc => mkApp2 (mkConst ``And) c acc) conjs.getLast!
    mkLambdaFVars #[st] body
  let thm ← mkAppOptM ``loopSafe_of_inv_cond #[some σ, some P]
  return some (← g.apply thm)

elab "mp_loop_inv" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some gs ← loopInvSlots g | throwError "mp_loop_inv: not the obligations of a loop with a \
    slice view in its state"
  Lean.Elab.Tactic.replaceMainGoal gs

/-! ## Loop invariants for obligations

`mp_safe … invariants · I₁ · I₂`, and `mp_auto invariants …` on obligations, give the `k`-th
invariant to the `k`-th loop in the order of the loops in the source. An invariant is
`fun done left st => …` over the counters done and left, which are lists as in a contract's
invariant so that one text serves both, and the loop state `st`, or it is `fun st => …`. The
state `st` is `(acc, (x₁, (x₂, … ())))`, and a pattern `fun _ _ (acc, x, y, _) => …` names its
parts. Each loop's obligations are split with its invariant, or without one when none is given,
and its state is taken apart into components named after the source variables and the flags
«left the loop», «returned» and «returned value». -/

/-- The loop invariants given to `mp_safe`, one `·` alternative each. The companion references
hold the state names of the function's loops, the index of the next loop, and the loops given an
invariant with their component names, for the message when one fails. -/
initialize safeInvsRef : IO.Ref (Array Syntax) ← IO.mkRef #[]
initialize safeNamesRef : IO.Ref (Array (Array String)) ← IO.mkRef #[]
initialize safeLoopIdxRef : IO.Ref Nat ← IO.mkRef 0
initialize safeInvUsedRef : IO.Ref (Array (Nat × Array String)) ← IO.mkRef #[]
/-- An invariant that did not elaborate, with the error, which `mp_auto` reports. -/
initialize safeInvErrRef : IO.Ref (Option (Syntax × MessageData)) ← IO.mkRef none

/-- The terms of an `invariants · t₁ · t₂ …` clause, which are its `·` alternatives in order. -/
def invariantTerms (alts : Syntax) : Array Syntax :=
  if alts.isMissing || alts.getNumArgs < 2 then #[] else alts[1].getArgs.map (·[1])

/-- `mp_safe_setup [invariants · t …]` starts the loop splitting of `mp_safe` for the obligations
of the `mp def` in the goal, with the invariants given. -/
syntax (name := mpSafeSetup) "mp_safe_setup" (ppSpace Lean.Parser.Tactic.invariantAlts)? : tactic

/-- Unfold a goal `f.SafeGoal …` or `f.SpecGoal …`, as stated for example at a generic
definition's variables, and introduce its binders. -/
def unfoldGoalDef : Lean.Elab.Tactic.TacticM Unit := Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some c := (← instantiateMVars (← g.getType)).getAppFn.constName? | return
  unless c.components.getLast? matches some `SafeGoal | some `SpecGoal do return
  let g ← g.deltaTarget (· == c)
  let (_, g) ← g.intros
  Lean.Elab.Tactic.replaceMainGoal [g]

@[tactic mpSafeSetup] def evalMpSafeSetup : Lean.Elab.Tactic.Tactic := fun stx => do
  unfoldGoalDef
  Lean.Elab.Tactic.withMainContext do
  let tgt ← instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let fn? := (tgt.find? (·.isAppOf ``Exp.safe)).bind fun se => (se.getArg! 3).getAppFn.constName?
  let st := loopNamesExt.getState (← getEnv)
  let names := (fn?.bind fun tn => st.find? tn.getPrefix).getD #[]
  safeNamesRef.set names
  safeLoopIdxRef.set 0
  -- The parameters, which `intros` introduced, by their names, for the invariants' terms.
  let g ← Lean.Elab.Tactic.getMainGoal
  let g ← (← getLCtx).foldlM (init := g) fun g d =>
    if !d.isImplementationDetail && d.userName.hasMacroScopes then
      g.rename d.fvarId d.userName.eraseMacroScopes else pure g
  Lean.Elab.Tactic.replaceMainGoal [g]
  -- The term `f.exp …` is unfolded, because the goal states its obligations at the unfolded form
  -- of the result type and `simp` cannot work on the folded constant.
  if let some tn := fn? then
    if tn.components.getLast? matches some `exp | some `expR then
      let g ← Lean.Elab.Tactic.getMainGoal
      Lean.Elab.Tactic.replaceMainGoal [← g.deltaTarget (· == tn)]
  safeInvUsedRef.set #[]
  safeInvErrRef.set none
  safeInvsRef.set (if stx[1].isNone then #[] else invariantTerms stx[1][0])

/-- The type `ty` with its nested pairs and their components unfolded, so `(Ty.tup ts).carrier`
becomes `A × (B × …)` and `Ty.u64.carrier` becomes `UInt64`. -/
partial def unfoldProd (ty : Expr) (fuel : Nat := 32) : MetaM Expr := do
  if fuel == 0 then return ty
  let r ← whnfR ty
  if r.isAppOfArity ``Prod 2 then
    return mkApp2 r.getAppFn (← unfoldProd (r.getArg! 0) (fuel - 1))
      (← unfoldProd (r.getArg! 1) (fuel - 1))
  let x? := if ty.isAppOfArity ``Ty.carrier 1 then some ty.appArg!
    else if let .proj ``Ty 0 x := ty then some x else none
  if let some x := x? then
    let x ← whnf x
    if x.isAppOfArity ``Ty.mk 2 then return ← unfoldProd (x.getArg! 0) (fuel - 1)
  return ty

/-- A loop invariant `t` for a loop of `n` iterations with state type `σ`, as the predicate
`fun j st => t (List.range j) ((List.range n).drop j) st` on the counter and the state, or as
`fun _ st => t st`. -/
def elabLoopInv (t : Syntax) (σ n : Expr) : Lean.Elab.Tactic.TacticM Expr := do
  let lN ← mkAppM ``List #[mkConst ``Nat]
  let ty3 ← mkArrow lN (← mkArrow lN (← mkArrow σ (mkSort .zero)))
  let elabAt (ty : Expr) : Lean.Elab.Tactic.TacticM Expr := do
    let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType t ty
    instantiateMVars e
  let s ← saveState
  let (inv, three) ← try pure (← elabAt ty3, true)
    catch e3 =>
      s.restore
      try pure (← elabAt (← mkArrow σ (mkSort .zero)), false)
      catch _ => s.restore; throw e3
  withLocalDeclD `j (mkConst ``Nat) fun j => withLocalDeclD `st σ fun st => do
    let body ← if three then do
        let done ← mkAppM ``List.range #[j]
        let left ← mkAppM ``List.drop #[j, ← mkAppM ``List.range #[n]]
        pure (mkApp3 inv done left st).headBeta
      else pure (mkApp inv st).headBeta
    mkLambdaFVars #[j, st] body

/-- Take the loop state `st` apart into components named `names`, which are the accumulator, the
carried variables and the flags. The last component is `()`. -/
def destructState (st : Name) (names : Array String) :
    Lean.Elab.Tactic.TacticM (Array String) := Lean.Elab.Tactic.withMainContext do
  if names.isEmpty then return names
  -- A component named like a parameter, which is the current value of a `&mut` parameter, is
  -- primed.
  let lctx ← getLCtx
  let names := names.map fun x =>
    if x != "_" && lctx.any (fun d => !d.isImplementationDetail &&
      d.userName == Name.mkSimple x) then x ++ "'" else x
  let pats : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo) ← (names.push "_").mapM fun x => do
    if x == "_" then `(Lean.Parser.Tactic.rcasesPatLo| _) else
      `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent (Name.mkSimple x)):ident)
  Lean.Elab.Tactic.evalTactic (← `(tactic| obtain ⟨$pats,*⟩ := $(mkIdent st)))
  return names

/-- Split the obligations of the next loop and take its state apart by name. The split uses the
loop's invariant if one was given, otherwise the invariant that its slice views' cells stay full
when it carries one, and otherwise covers every state. -/
elab "mp_loop_split" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  unless tgt.isAppOfArity ``loopSafe 9 do throwError "mp_loop_split: not a loop's obligations"
  let k ← safeLoopIdxRef.get
  let names := (← safeNamesRef.get)[k]?.getD #[]
  let σ := tgt.getArg! 0
  let σ' ← unfoldProd σ
  let n := tgt.getArg! 5
  let stN ← mkFreshUserName `st
  let named (gs : List MVarId) (nIntro : Nat) (stPos : Nat) :
      Lean.Elab.Tactic.TacticM (Array String) := do
    let step := gs.getLast!
    let ns ← (List.range nIntro).mapM fun _ => mkFreshUserName `h
    let (fvs, step) ← step.introN nIntro ns
    let step ← step.replaceLocalDeclDefEq fvs[stPos]! σ'
    let step ← step.rename fvs[stPos]! stN
    let others := (← Lean.Elab.Tactic.getGoals).drop 1
    Lean.Elab.Tactic.setGoals [step]
    let names ← destructState stN names
    let rest ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals (gs.dropLast ++ rest ++ others)
    return names
  match (← safeInvsRef.get)[k]? with
  | some t =>
    let P ← try withRef t (elabLoopInv t σ' n)
      catch e =>
        safeInvErrRef.set (some (t, e.toMessageData))
        throw e
    safeLoopIdxRef.set (k + 1)
    let gs ← g.apply (← mkAppOptM ``loopSafe_invJ #[some σ, some P])
    -- The start, then one iteration, `∀ j a w, i ≤ j → j < i + n → P j a → …`.
    let names ← named gs 6 1
    safeInvUsedRef.modify (·.push (k, names))
  | none =>
    safeLoopIdxRef.set (k + 1)
    if let some gs ← loopInvSlots g then
      Lean.Elab.Tactic.replaceMainGoal gs
    else
      let gs ← g.apply (mkConst ``loopSafe_of_forall_cond)
      -- The form `∀ j, i ≤ j → j < i + n → ∀ a w, …`.
      discard <| named gs 5 3

/-- For a goal about the final state of an inner loop, `… (loopDenote cond body n i acc w).1 …`,
abstract that state and apply `loopDenote_inv_cond`. This leaves the goal for the start state
`acc` and the goal that one iteration of the inner loop keeps it. Such a goal is the invariant of
`mp_loop_inv` for an outer loop whose body runs an inner loop over a carried slice view. The
tactic fails if the goal has no such term outside binders. -/
elab "mp_loop_lift" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some t := tgt.find? fun e =>
      e.isAppOfArity ``Prod.fst 3 && e.appArg!.isAppOfArity ``loopDenote 7 && !e.hasLooseBVars
    | throwError "mp_loop_lift: no loop result in the goal"
  let σ := t.appArg!.getArg! 0
  let abst ← kabstract tgt t
  let P := Expr.lam `st σ abst .default
  unless ← isTypeCorrect P do throwError "mp_loop_lift: the goal does not abstract over the loop"
  let ld := t.appArg!
  let thm := mkAppN (mkConst ``loopDenote_inv_cond) #[σ, P, ld.getArg! 1, ld.getArg! 2, ld.getArg! 3,
    ld.getArg! 4, ld.getArg! 5, ld.getArg! 6]
  let gs ← g.apply thm
  let gs ← gs.mapM fun g' => g'.withContext do
    g'.change (← Core.betaReduce (← instantiateMVars (← g'.getType))) (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal gs

/-- `mp_check_terms t, …` elaborates each term and fails on an error such as an unknown
identifier, leaving the goal unchanged. `mp_safe … using` runs it first, because its closers are
tried under `first` and a misspelt one would otherwise be skipped silently. -/
elab "mp_check_terms " ts:term,+ : tactic => Lean.Elab.Tactic.withMainContext do
  for t in ts.getElems do
    let _ ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm t none

/-- The automatic discharge of obligations. It unfolds the term and its obligations, splits every
loop by its counter and every conjunction, and closes the pieces with `simp`, `omega`, `grind`
and `decide`, using the hypotheses in context such as the `requires` clause. Only `∧` is split,
so a structure such as an invariant `p.Inv` stays whole and can match a hypothesis or a callee's
contract. In `mp_safe [simp lemmas] using closers grind [lemmas]` the `grind` lemmas are the
callees' contracts `g.post`. -/
syntax (name := mpSafeTac) "mp_safe" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" using " term,+)? (" grind " "[" Lean.Parser.Tactic.grindParam,* "]")?
  (ppSpace Lean.Parser.Tactic.invariantAlts)? : tactic

macro_rules
  | `(tactic| mp_safe $[[$ls,*]]? $[using $cs,*]? $[grind [$gs,*]]? $[$inv:invariantAlts]?) => do
    let ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := (ls.map (·.getElems)).getD #[]
    let cs : Array Term := (cs.map (·.getElems)).getD #[]
    -- The callees' contracts `g.post`, for `grind`.
    let gs : Array (TSyntax ``Lean.Parser.Tactic.grindParam) := (gs.map (·.getElems)).getD #[]
    -- The callees' safety theorems close their obligations, taking their `requires` from context.
    let close ← cs.foldrM (fun c acc => `(tactic| first | (apply $c <;> assumption) | $acc:tactic))
      (← `(tactic| fail))
    let check ← if cs.isEmpty then `(tactic| skip) else `(tactic| mp_check_terms $cs,*)
    let setup ← match inv with
      | some i => `(tactic| mp_safe_setup $i)
      | none => `(tactic| mp_safe_setup)
    `(tactic| set_option maxRecDepth 8192 in (
      $check:tactic
      $setup:tactic
      set_option linter.unusedSimpArgs false in
      simp only [Millipede.Exp.safe, Millipede.Exp.denote, Millipede.Place.ok, Millipede.Place.get,
        Millipede.Place.set, Millipede.Atom.denote, Millipede.Env.get_here, Millipede.Env.get_there,
        Millipede.Env.set_here, Millipede.Env.set_there, Millipede.Args.denote,
        Millipede.RArgs.ok, Millipede.RArgs.denote, Millipede.RArgs.writeBack,
        Millipede.EArgs.ok, Millipede.EArgs.fill, Millipede.ExtSig.call, Millipede.EArgs.outCaps,
        Millipede.Guard.denote, Millipede.Place.check, Millipede.Prim.denote, Millipede.Prim.ok, Millipede.vrange,
        Millipede.Ctor.pairMk_build, Millipede.vview_isFull, Millipede.Slots.isFull_setCell,
        Millipede.sview_isFull, Millipede.sunview_isFull,
        Millipede.Carry.get, Millipede.Carry.set, Millipede.Flat.tupBuild_cons, Millipede.Flat.tupBuild_nil,
        Millipede.Ctor.tupMk,
        true_and, and_true, $ls,*] at *
      repeat' (first
        | exact trivial
        | $close:tactic
        | mp_loop_split
        | apply And.intro
        | intro _)
      all_goals (try (set_option linter.unusedSimpArgs false in
        simp_all [UInt64.toNat_ofNat', Nat.mod_eq_of_lt, $ls,*]))
      all_goals (try omega)
      all_goals (try grind [$gs,*])
      -- For the invariant's goal of a loop body that writes a carried slice view, an inner loop's
      -- final state is generalised, since each inner iteration keeps the invariant, and the
      -- body's nested `match` and `if` are split.
      all_goals (try ((repeat' (first | mp_loop_lift | intro _)) <;> (repeat' split) <;>
        (set_option linter.unusedSimpArgs false in
          simp_all [UInt64.toNat_ofNat', Nat.mod_eq_of_lt, $ls,*]) <;> grind [$gs,*]))
      all_goals (try decide)))

/-- The `mp_safe` call of an automatic attempt at the obligations of `term`, which is `f.exp` or
the relaxed `f.expR`, when it calls `callees`. It passes the callees' `Safe'` as simp lemmas and
closers and their `req`, and for those with a contract their `exp_denote`, so that their results
appear in the goal as normal forms, and their `post` for `grind`. With `contracts := false` the
calls are left as they are, so that `mp_safe` sees the callees' terms instead of contracts that
may say less than the term, as `ensures True` does. -/
def safeCall (callees : Array FnInfo) (term : Name)
    (extraSimp : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[])
    (extraGrind : Array (TSyntax ``Lean.Parser.Tactic.grindParam) := #[])
    (invs : Option (TSyntax ``Lean.Parser.Tactic.invariantAlts) := none) (contracts := true) :
    TermElabM Syntax := do
  let env ← getEnv
  let simpLemma (n : Name) := `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  -- A `post` that concludes with `∃`, as that of a contract about events does, has no pattern
  -- that `grind` can use, and `grind` rejects it.
  let withPost := callees.filter fun g => contracts && match env.find? (g.declName ++ `post) with
    | some ci => !ci.type.getForallBody.isAppOf ``Exists
    | none => false
  let mut lemmas := #[← simpLemma term] ++ extraSimp
  for g in callees do
    if g.hasSafe then lemmas := lemmas.push (← simpLemma (g.declName ++ `Safe'))
    if g.isRef then lemmas := lemmas.push (← simpLemma (g.declName ++ `req))
  for g in withPost do lemmas := lemmas.push (← simpLemma (g.declName ++ `exp_denote))
  let closers : Array Term := callees.filterMap fun g =>
    if g.hasSafe then some (mkCIdent (g.declName ++ `Safe')) else none
  let posts := (← withPost.mapM fun g =>
    `(Lean.Parser.Tactic.grindParam| $(mkCIdent (g.declName ++ `post)):ident)) ++ extraGrind
  if closers.isEmpty then `(tactic| (intros; mp_safe [$lemmas,*] grind [$posts,*] $[$invs]?))
  else `(tactic| (intros; mp_safe [$lemmas,*] using $closers,* grind [$posts,*] $[$invs]?))

/-- The tactic `mp_auto` without arguments, built by its syntax kind, because it is defined later,
in Millipede/Meta/Auto.lean. -/
def mpAutoSyntax : Syntax :=
  Syntax.node .none `Millipede.Meta.mpAutoTac #[Syntax.atom .none "mp_auto", mkNullNode, mkNullNode]

/-- Elaborate the parameters, `requires` clause, result type and body of `mp def`, run the
source-level checkers, and hand back the final values of the `&mut` parameters. -/
def elabHeaderBody (stx : Syntax) :
    M (Array (Name × STy × PMode × Syntax) × STy × AExp × Option Syntax) := do
  let mut params : Array (Name × STy × PMode × Syntax) := #[]
  for b in stx[4].getArgs do
    let (t, m) ← elabParamTy b[3]
    for x in b[1].getArgs do
      unless x.getId.isAtomic do
        throwErrorAt x "a parameter name is a simple identifier"
      if params.any (·.1 == x.getId) then
        throwErrorAt x "duplicate parameter `{x.getId}`"
      params := params.push (x.getId, t, m, x)
      -- A slice parameter carries its length in the hidden parameter `x.len` after it.
      if let .slice _ _ := t then
        if m != .own then params := params.push (lenParamName x.getId, .u64, .own, x)
  let req? := if stx[5].getNumArgs == 2 then some stx[5][1] else none
  let ret ← elabTy stx[7]
  let kindOf : PMode → LKind | .own => .own | .shr => .shr | .mut => .mut
  let ctx : Ctx := params.toList.reverse.map fun (x, t, m, _) =>
    { name := x, ty := t, kind := kindOf m,
      len? := if m != .own && t matches .slice _ _ then some (.var (lenParamName x) .missing)
        else none }
  let (body, _) ← if stx[9].getKind == ``Lean.Parser.Term.do then
      elabSeq { ret? := some ret } ctx (doSeqItems stx[9][1]) none (some ret)
    else elabE ctx stx[9] (some ret)
  let isRef := params.any (·.2.2.1 != .own) || req?.isSome
  let muts := params.toList.reverse.filterMap fun (x, t, m, _) =>
    if m == .mut then some (x, t) else none
  let body ← if isRef then mapTail body ret fun a => tupleE ret a muts else pure body
  for (x, t, m, ref) in params do
    -- A shared reference is never moved, since `BS.done` holds for `shr` binders.
    unless m == .shr do
      checkOnce x t ref (if m == .mut then "`&mut` parameter" else "parameter") body
  -- Borrowing by place. A slice parameter is a view binder, since every caller passes a view
  -- place for it.
  let st : List NB := params.toList.reverse.map fun (x, t, m, _) =>
    { NB.fresh x m t with view := m != .own && t matches .slice _ _ }
  match body.check st with
  | .error (r, msg) => throwErrorAt (if r.getPos?.isSome then r else stx[3]) msg
  | .ok st =>
    if let some b := st.find? (!·.done) then
      throwErrorAt stx[3] "the linear parameter `{b.name}` is not consumed"
  return (params, ret, body, req?)

/-! ## Options of `mp def`

Most of the time of `mp def` goes to the normal form and to the automatic attempt at the
obligations, so code that does not use them can turn them off. The callers of a function without
a normal form have none either. -/

register_option mp.normalForm : Bool := {
  defValue := true
  descr := "`mp def` defines the normal form `f` and proves `f.exp_run` / `f.exp_denoteM` / \
    `f.exp_denote` (callers with a normal form need it)"
}

register_option mp.autoSafe : Bool := {
  defValue := true
  descr := "`mp def` tries to discharge the obligations (`f.safe`) with `mp_safe`; when false \
    only `f.SafeGoal` is defined (a term without partial operations still gets `f.safe`)"
}

register_option mp.autoSafe.kernelHeartbeats : Nat := {
  defValue := 10000
  descr := "heartbeat budget (in thousands) of the kernel's check of a proof found by `mp def`'s \
    automatic attempt (obligations or contract); a proof over it is dropped, the goal left to \
    `mp prove`"
}

register_option mp.autoSafe.maxHeartbeats : Nat := {
  defValue := 200000
  descr := "heartbeat budget (in thousands, like `maxHeartbeats`) of the automatic `mp_safe` \
    attempt of `mp def`; a failing attempt gives up after it (`mp prove` is not limited)"
}

/-- The identifiers of a syntax tree. -/
partial def identsOf (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.flatMap identsOf
  | _ => #[]

/-- Run a command under the section's `variable`s. If the command mentions one of them, or
`force` is set, every section variable is in scope while it is elaborated, and `mp def` then
narrows them to those the definition takes. Otherwise the definition is closed. -/
def withGenVars {α : Type} (stx : Syntax) (k : TermElabM α) (force := false) :
    CommandElabM α := do
  let sc ← getScope
  if sc.varDecls.isEmpty then return ← liftTermElabM k
  -- A command that mentions no variable is elaborated outside them, so it is closed.
  let ids := identsOf stx
  let names ← runTermElabM fun vars => vars.mapM fun v => return (← v.fvarId!.getDecl).userName
  unless force || sc.includedVars.length > 0 ||
      ids.any (fun i => names.any fun n => i == n || i.getRoot == n) do
    return ← liftTermElabM k
  runTermElabM fun vars => do
    let used ← vars.anyM fun v => do
      let n := (← v.fvarId!.getDecl).userName
      return ids.any fun i => i == n || i.getRoot == n
    let inc := (vars.zip sc.varUIds).filterMap fun (v, u) =>
      if sc.includedVars.contains u then some v else none
    genVarsRef.set (if used || force || !inc.isEmpty then vars else #[])
    genIncludedRef.set inc
    try k finally genVarsRef.set #[]; genIncludedRef.set #[]

/-- Run `k` with the section variables `drop` and their instances removed from the local context,
because the attempts at a definition's obligations and contract, and its theorems, cannot use a
variable the definition does not take. -/
def withoutVars {α : Type} (drop : Array Expr) (k : TermElabM α) : TermElabM α := do
  if drop.isEmpty then return ← k
  let ids := drop.map (·.fvarId!)
  let lctx := ids.foldl (fun l i => l.erase i) (← getLCtx)
  let insts := (← getLocalInstances).filter fun li => !ids.contains li.fvar.fvarId!
  withLCtx lctx insts k

/-- Run `k` with the section variables narrowed to those the generic function `info` takes, for a
command about an existing function such as `mp prove` or `ensures`. -/
def withFnGenVars {α : Type} (info : FnInfo) (k : TermElabM α) : TermElabM α := do
  let all ← genVarsRef.get
  let sel := info.genIdx.filterMap (all[·]?)
  unless sel.size == info.nGen do
    throwError "`{info.declName}` takes {info.nGen} variables of its section, not in scope here"
  genVarsRef.set sel
  try withoutVars (all.filter (!sel.contains ·)) k finally genVarsRef.set all

/-- The variables a generic definition takes, by Lean's inclusion rule for `variable`s with
`include` read as for a definition's theorems. They are the variables it mentions in `ids`, the
identifiers of the command, or whose free variables occur in `es`, its Core term and types, which
can hold a generic callee's hypothesis found in context. To these are added the variables their
types mention, and the instance binders and `include`d variables whose types mention only taken
variables. An `include`d variable whose type mentions no variable is always taken. The result is
in section order. A definition that uses no variable of an `include`d hypothesis such as
`h4 : 4 ≤ A.cap` is not generic over it, so its callers need not supply `A`. -/
def includedGenVars (ids : Array Name) (es : Array Expr) : TermElabM (Array Expr) := do
  let vars ← genVarsRef.get
  let occ := es.foldl (fun s e => collectFVars s e) {}
  let inc0 ← genIncludedRef.get
  let mut inc : Array Expr ← vars.filterM fun v => do
    let n := (← v.fvarId!.getDecl).userName
    let closedInc := inc0.contains v &&
      !(← instantiateMVars (← inferType v)).hasAnyFVar (fun f => vars.any (·.fvarId! == f))
    return ids.any (fun i => i == n || i.getRoot == n) || occ.fvarSet.contains v.fvarId! ||
      closedInc
  let mut changed := true
  while changed do
    changed := false
    for v in vars do
      if inc.contains v then continue
      let d ← v.fvarId!.getDecl
      let ty ← instantiateMVars d.type
      let dep ← inc.anyM fun w => return (← instantiateMVars (← inferType w)).containsFVar v.fvarId!
      let tyF := (collectFVars {} ty).fvarIds
      let inst := (d.binderInfo.isInstImplicit || inc0.contains v) && !tyF.isEmpty &&
        tyF.all fun f => inc.any (·.fvarId! == f)
      if dep || inst then
        inc := inc.push v; changed := true
  return vars.filter inc.contains

/-- A registered function as seen from its own section, so a generic one is taken at the
section's variables it takes and a closed one as it is. -/
def FnInfo.inScope (f : FnInfo) : TermElabM FnInfo := do
  if f.nGen == 0 || !f.genArgs.isEmpty then return f
  let all ← genVarsRef.get
  let sel := f.genIdx.filterMap (all[·]?)
  unless sel.size == f.nGen do
    throwError "`{f.declName}` is generic over variables not in scope here"
  return f.instantiate sel

/-- The `ensures` clause of the `mp def … ensures` being elaborated, from which the automatic
attempt at the obligations takes loop invariants. -/
initialize ensuresStxRef : IO.Ref (Option Syntax) ← IO.mkRef none

/-- Loop invariants for the automatic attempt at the obligations of a function whose loops have
the states `loops`. They are the `requires` clause, the `ensures` clause unless it mentions
`result`, and both together, each stated at every loop's state as `fun _ _ (acc, x, …, _) => …`
with the components named after the variables. A `&mut` parameter `p` among `muts` is read as
`p'`. -/
def invCandidates (loops : Array (Array String)) (muts : Array String) (req? ens? : Option Syntax) :
    TermElabM (Array Syntax) := do
  if loops.isEmpty then return #[]
  let flags := ["returned", "returned value", "left the loop", "_"]
  let pat (ns : Array String) (prime : Bool) : TermElabM Term := do
    let ps : Array Term ← (ns.push "_").mapM fun x =>
      if flags.contains x then `(_) else
        pure (mkIdent (Name.mkSimple (if prime && muts.contains x then x ++ "'" else x)))
    `(($(ps[0]!), $(ps.extract 1 ps.size),*))
  let alts (body : Syntax) (prime : Bool) : TermElabM Syntax := do
    let ts ← loops.mapM fun ns => do
      let p ← pat ns prime
      `(Lean.Parser.Tactic.invariantDotAlt| · fun _ _ $p => $(⟨body⟩))
    `(Lean.Parser.Tactic.invariantAlts| invariants $ts*)
  let ens? := ens?.filter fun e => (e.find? (·.getId == `result)).isNone
  let mut out := #[]
  if let some r := req? then out := out.push (← alts r false)
  if let some e := ens? then out := out.push (← alts e true)
  if let (some r, some e) := (req?, ens?) then
    -- `requires` at the state, where each `&mut` parameter `p` is read as the component `p'`.
    let r' ← muts.foldrM (fun x (acc : Term) => do
      let p := mkIdent (Name.mkSimple x)
      `(let $p := $(mkIdent (Name.mkSimple (x ++ "'"))); $acc)) ⟨r⟩
    out := out.push (← alts (← `(($r' ∧ $(⟨e⟩)))) true)
  return out

/-- `f.exp_denoteM` and `f.exp_denote` of a function that calls no extern. They are derived from
its normal-form equation `runEq : f.exp.run env = f xs` at the parameters `xs` and from
`isPurePrf : f.exp.isPure = true`, and state `f.exp.denoteM ω env = pure (f xs).run`, for
effectful callers, and `f.exp.denote ω env w = ((f xs).run, w)`. `expC` is the Core term at the
variables over which the theorems are abstracted. Both `mp def` and `mp interface` use it. -/
def addPureDenotes (declName : Name) (short : String) (expC isPurePrf runEq : Expr)
    (xs : Array Expr) : TermElabM Unit := do
  let gvs ← genVarsRef.get
  let some (_, lhs, fApp) := (← instantiateMVars (← inferType runEq)).eq?
    | throwError "internal error: the normal-form equation of `{short}`"
  let ty ← whnfR (← inferType expC)
  let (Γ, expT, env) := (ty.appFn!.appArg!, ty.appArg!, lhs.appArg!)
  -- The result's carrier, expanded, as the normal form states it.
  let resTy ← instantiateMVars (← inferType fApp)
  let retCarrier := resTy.appArg!
  withLocalDeclD `ω (mkConst ``Oracle) fun ω => do
    let lhsM := mkApp5 (mkConst ``Exp.denoteM) ω Γ expT expC env
    let stId := mkApp2 (mkConst ``StateT [0, 0]) (mkConst ``World) (mkConst ``Id [0])
    let pureFn := mkApp3 (mkConst ``Pure.pure [0, 0]) stId
      (← synthInstance (mkApp (mkConst ``Pure [0, 0]) stId)) retCarrier
    let runF := mkApp2 (mkConst ``Id.run [0]) retCarrier fApp
    let p₁ := mkAppN (mkConst ``Exp.denoteM_of_isPure) #[ω, Γ, expT, expC, isPurePrf, env]
    let motive ← withLocalDeclD `v resTy fun v =>
      mkLambdaFVars #[v] (mkApp pureFn (mkApp2 (mkConst ``Id.run [0]) retCarrier v))
    let prfM ← mkEqTrans p₁ (← mkCongrArg motive runEq)
    let nameM := declName ++ `exp_denoteM
    addThm nameM (← mkForallFVars (#[ω] ++ xs) (← mkEq lhsM (mkApp pureFn runF)))
      (← mkLambdaFVars (#[ω] ++ xs) prfM)
    addDocStringCore nameM s!"`{short}` viewed in `StateM World` (for effectful callers)."
    withLocalDeclD `w (mkConst ``World) fun w => do
      let den := mkAppN (mkConst ``Exp.denote) #[ω, Γ, expT, expC, env, w]
      let rhsD ← mkAppM ``Prod.mk #[runF, w]
      let prfD ← mkCongrFun (mkAppN (mkAppN (mkConst nameM) gvs) (#[ω] ++ xs)) w
      let dName := declName ++ `exp_denote
      addThm dName (← mkForallFVars (#[ω, w] ++ xs) (← mkEq den rhsD))
        (← mkLambdaFVars (#[ω, w] ++ xs) prfD)
      addDocStringCore dName s!"The denotation of `{short}.exp` is `{short}`; \
        the world is unchanged."

/-- Add `f.Safe'`, the form that callers' `mp_safe` uses as a simp lemma, which states
`∀ ω env w, f.req env → f.exp.safe ω env w`, without the hypothesis when `req?` is `none`. It is
proved by `safeOf ω env w h`. Both `mp def` and `mp interface` use it. -/
def addSafeSimp (declName : Name) (expC : Expr) (req? : Option Expr)
    (safeOf : Expr → Expr → Expr → Expr → Expr) : TermElabM Unit := do
  let ty ← whnfR (← inferType expC)
  let (Γ, expT) := (ty.appFn!.appArg!, ty.appArg!)
  withLocalDeclD `ω (mkConst ``Oracle) fun ω =>
  withLocalDeclD `env (mkApp (mkConst ``Env) Γ) fun env =>
  withLocalDeclD `w (mkConst ``World) fun w => do
    let body := mkAppN (mkConst ``Exp.safe) #[ω, Γ, expT, expC, env, w]
    match req? with
    | some req =>
      withLocalDeclD `h (mkApp req env) fun h => do
        addThm (declName ++ `Safe') (← mkForallFVars #[ω, env, w] (← mkArrow (mkApp req env) body))
          (← mkLambdaFVars #[ω, env, w, h] (safeOf ω env w h))
    | none =>
      addThm (declName ++ `Safe') (← mkForallFVars #[ω, env, w] body)
        (← mkLambdaFVars #[ω, env, w] (safeOf ω env w (mkConst ``True.intro)))

/-- The pair borrows `(a[i], a[j])` and `a.pair! i j` in `stx`, as source text. -/
partial def pairBorrows (stx : Syntax) : Array String :=
  let isElem (z : Syntax) : Bool := match z with
    | `($_[$_]) | `($_[$_]!) => true
    | _ => false
  let here : Array String := match stx with
    | `(($x, $y)) => if isElem x && isElem y then #[stx.prettyPrint.pretty] else #[]
    | `($f:ident $_ $_) =>
      if f.getId.components.getLast? == some `pair! then #[stx.prettyPrint.pretty] else #[]
    | _ => #[]
  here ++ stx.getArgs.flatMap pairBorrows

/-- A hint after obligations left unproved in a function with pair borrows, whose obligations
include that the two indices differ. A goal `False` is what is left of that obligation when the
indices may be equal. -/
def pairHint (stx : Syntax) (left : String) : String :=
  let pairs := pairBorrows stx
  let target := (left.splitOn "⊢ ").getLast!
  if pairs.isEmpty || !((target.splitOn "False").length > 1 || (target.splitOn "≠").length > 1)
  then ""
  else s!"\nhint: the pair borrow {", ".intercalate (pairs.toList.map (s!"`{·}`"))} takes two \
    cells of one array, so its obligations include that the two indices differ; a goal `False` \
    here usually means that they may be equal. State it in `requires` (as `i ≠ j`) or test it \
    before the borrow"

/-- Elaborate `mp def`. -/
def elabMpDefCore (stx : Syntax) : TermElabM Unit := do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let nameStx := stx[3]
  let ns ← getCurrNamespace
  let declName := ns ++ nameStx.getId
  let short := nameStx.getId
  if (← getEnv).contains declName then
    throwErrorAt nameStx "`{declName}` is already declared"
  flagRolesRef.set {}
  let (params, ret, body, req?) ← (elabHeaderBody stx).run' 0
  let ctx0 : Ctx := params.toList.reverse.map fun (x, t, _, _) => { name := x, ty := t }
  -- A generic definition takes the variables it uses.
  let allVars ← genVarsRef.get
  if !allVars.isEmpty then
    let (e0, _) ← emit ctx0 body
    let tys := params.map (·.2.1.toTy) |>.push ret.toTy
    genVarsRef.set (← includedGenVars (identsOf stx) (tys.push e0))
  let gvs ← genVarsRef.get
  withoutVars (allVars.filter (!gvs.contains ·)) do
  let gIdx := gvs.filterMap allVars.idxOf?
  let gcn (n : Name) : Expr := mkAppN (mkConst n) gvs
  let opts ← getOptions
  let doNf := mp.normalForm.get opts
  if doNf then
    if let some g := body.callees.find? (!·.hasNf) then
      throwErrorAt nameStx "`{g.declName}` has no normal form (declared under \
        `set_option mp.normalForm false`), so `{short}` cannot have one: set the option for \
        `{short}` too"
  let isPure := body.isPure
  let isRef := params.any (·.2.2.1 != .own) || req?.isSome
  let ctx : Ctx := params.toList.reverse.map fun (x, t, _, _) => { name := x, ty := t }
  let Γ := tyList ctx.tys
  let info0 : FnInfo :=
    { declName, params := params.map (fun (x, t, m, _) => (x, t, m)), ret, isPure, isRef,
      hasSafe := false, hasNf := doNf, nGen := gvs.size, genArgs := gvs, genIdx := gIdx }
  let expSTy := info0.expTy
  loopNamesRef.set #[]
  let (expVal, _) ← emit ctx body
  modifyEnv (loopNamesExt.addEntry · (declName, ← loopNamesRef.get))
  let expName := declName ++ `exp
  let expTy := mkApp2 (mkConst ``Exp) Γ info0.expTyExpr
  addDef expName expTy expVal
  addDocStringCore expName s!"The core term of `{short}` (generated by `mp def`)."
  -- The capability classes that `short` does not hold, whose externs it must not reach.
  if gvs.isEmpty then
    let held := (← params.toList.mapM fun (_, t, _, _) => tokenClasses t).flatten ++
      (← grantRef.get)
    if let some (ty, prf) ← noCallsProof m!"`{short}`" nameStx Γ info0.expTyExpr
        (mkConst expName) held then
      addThm (declName ++ `noCalls) ty prf
      addDocStringCore (declName ++ `noCalls) s!"No run of `{short}` calls an extern symbol of a \
        capability class it holds no token of (generated by `mp def`)."
  let paramDecls := params.toList.map fun (x, t, _, _) => (x, t.carrier)
  -- `requires`, as a predicate on the parameters and on environments.
  let envTy := mkApp (mkConst ``Env) Γ
  let pms := params.map fun (x, t, m, _) => (x, t, m)
  let viewIdx := (List.range params.size).filter fun k => isLenParam pms (k + 1)
  -- `requires`, followed by what every caller guarantees of a slice argument `a[lo..hi]`, which
  -- is that its length is at most the array's and that the cells below `s.len` are full.
  let hasReq := req?.isSome || !viewIdx.isEmpty
  let reqOf (xs : Array Expr) : TermElabM Expr := do
    let user ← match req? with
      | none => pure none
      | some r => do
        let p ← Term.elabTermEnsuringType r (mkSort .zero)
        Term.synthesizeSyntheticMVarsNoPostponing
        pure (some (← instantiateMVars p))
    let views ← viewIdx.mapM fun k => do
      let sv := xs[k]!; let lv := xs[k + 1]!
      let .slice _ n := params[k]!.2.1 | throwError "internal error: slice parameter"
      let lenN := mkApp (mkConst ``UInt64.toNat) lv
      let bound ← mkAppM ``LE.le #[lenN, n]
      let full ← withLocalDeclD `k (mkConst ``Nat) fun kv => do
        let lt ← mkAppM ``LT.lt #[kv, lenN]
        let isF ← mkEq (← mkAppM ``Slots.isFull #[sv, kv]) (mkConst ``Bool.true)
        mkForallFVars #[kv] (← mkArrow lt isF)
      mkAppM ``And #[bound, full]
    let all := user.toList ++ views
    match all.reverse with
    | [] => return mkConst ``True
    | last :: rest => rest.foldlM (fun acc p => mkAppM ``And #[p, acc]) last
  let reqFun ← withLocalDeclsDND paramDecls.toArray fun xs => do
    let p ← reqOf xs
    let lam ← mkLambdaFVars xs p
    withLocalDeclD `env envTy fun env => do
      let n := params.size
      let gets := (List.range n).map fun i =>
        -- Parameter `i` in source order is at de Bruijn index `n - 1 - i`.
        mkApp4 (mkConst ``Env.get) ctx[n - 1 - i]!.ty.toTy Γ env (memExpr ctx.tys (n - 1 - i))
      mkLambdaFVars #[env] (lam.beta gets.toArray).headBeta
  -- The bundle and linearity.
  let modes := params.toList.reverse.map (·.2.2.1)
  let (bundleName, wfLhs) ← if isRef then do
      let reqName := declName ++ `req
      addDef reqName (← mkArrow envTy (mkSort .zero)) reqFun
      addDocStringCore reqName s!"The `requires` of `{short}`, on environments."
      let (_, os) := info0.psOs
      let fnRefName := declName ++ `fnRef
      addDef fnRefName (mkApp3 (mkConst ``FnRef) Γ (tyList os) ret.toTy)
        (mkAppN (mkConst ``FnRef.mk) #[Γ, tyList os, ret.toTy, toExpr declName.toString,
          gcn expName, gcn reqName])
      addDocStringCore fnRefName s!"The function bundle of `{short}` (reference parameters), \
        for callers and proofs."
      let msE := modes.foldr (fun m acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Mode)
        m.toExpr acc) (mkApp (mkConst ``List.nil [0]) (mkConst ``Mode))
      pure (fnRefName, mkApp5 (mkConst ``FnRef.wf) Γ (tyList os) ret.toTy (gcn fnRefName) msE)
    else do
      let fnName := declName ++ `fn
      addDef fnName (mkApp2 (mkConst ``Fn) Γ ret.toTy)
        (mkApp5 (mkConst ``Fn.mk) Γ ret.toTy (toExpr short.toString) (gcn expName)
          (mkLambda `_ .default envTy (mkConst ``True)))
      addDocStringCore fnName s!"The function bundle of `{short}`, for callers and the compiler."
      pure (fnName, mkApp3 (mkConst ``Fn.wf) Γ ret.toTy (gcn fnName))
  -- Checked only by the kernel, in the background, since theorems are checked asynchronously.
  -- The elaborator's own checks make a rejection an internal error, so a `whnf` pre-check would
  -- only add the cost of a second evaluation.
  let (wfProp, wfPrf) ← decideProof wfLhs
  let wfName := declName ++ `wf
  if gvs.isEmpty then addThm wfName wfProp wfPrf
  else if let some prf ← genericWf wfProp wfPrf gvs then addThm wfName wfProp prf
  addDocStringCore wfName s!"`{short}` passes the linearity and borrow checker (kernel `decide`)."
  -- The simp-normal form.
  let calleeLemmas := body.callees.map fun (g : FnInfo) =>
    if isPure then g.declName ++ `exp_run else g.declName ++ `exp_denoteM
  let dataConsts := body.dataTerms.filterMap fun e => e.getAppFn.constName?
  -- The split chain of a `match` on an enum folds into `E.mpMatch`, which stays folded and is
  -- then delta-expanded to a `match`.
  let env0 ← getEnv
  let isSplit (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "split" && (lookupAdt env0 n.getPrefix).isSome
    | _ => false
  let enums := (dataConsts.filter isSplit).map (·.getPrefix) |>.eraseDups
  let lemmas := commonLemmas ++ (if isPure then runLemmas else denoteMLemmas) ++ calleeLemmas ++
    enums.map (· ++ `mpMatch_eq)
  let unfolds := commonUnfolds ++ [expName] ++ body.externs ++ dataConsts.filter (!isSplit ·)
  let retCarrier := expSTy.carrier
  let stateM (α : Expr) := mkApp2 (mkConst ``StateM [0]) (mkConst ``World) α
  let resTy := if isPure then mkApp (mkConst ``Id [0]) retCarrier else stateM retCarrier
  let expT := info0.expTyExpr
  let expX := info0.expTyX.toTy
  -- `f` and `f.exp_run` or `f.exp_denoteM`.
  let ωs : List (Name × Expr) := if isPure then [] else [(`ω, mkConst ``Oracle)]
  if doNf then withLocalDeclsDND (ωs ++ paramDecls).toArray fun xs => do
    let ωv? := if isPure then none else some xs[0]!
    let pxs := if isPure then xs else xs.extract 1 xs.size
    let env := envExpr (pxs.toList.zip (params.toList.map (·.2.1)))
    let lhsOf (t e : Expr) := match ωv? with
      | none => mkApp4 (mkConst ``Exp.run) Γ t e env
      | some ω => mkApp5 (mkConst ``Exp.denoteM) ω Γ t e env
    let lhs := lhsOf expT (gcn expName)
    let env1 ← getEnv
    let callees := body.callees.toArray.filterMap fun (g : FnInfo) =>
      let eqN := if isPure then `exp_run else `exp_denoteM
      if env1.contains (g.declName ++ eqN) && env1.contains g.declName then
        some { exp := g.const `exp, fn := g.const .anonymous, eq := g.const eqN : CalleeEq }
      else none
    let (nf, prf) ← normalFormOfExp (← instantiateMVars expVal) callees (lhsOf expX) (lhsOf expT)
      (lemmas.filter fun n => !callees.any (·.eq.getAppFn.constName? == some n)) unfolds fun nf => do if enums.isEmpty then pure nf else
        Core.betaReduce (← deltaExpand nf fun n => enums.any (· ++ `mpMatch == n))
    if mentionsCore nf then
      throwErrorAt nameStx "internal error: the denotation of `{short}` did not reach a \
        normal form:{indentExpr nf}"
    let fTy ← mkForallFVars xs resTy
    let fVal ← mkLambdaFVars xs nf
    addDef declName fTy fVal
    Term.addTermInfo' nameStx (gcn declName) (isBinder := true)
    addDocString' declName Syntax.missing doc?
    let fApp := mkAppN (gcn declName) xs
    let eqName := declName ++ (if isPure then `exp_run else `exp_denoteM)
    let eqTy ← mkForallFVars xs (← mkEq lhs fApp)
    addThm eqName eqTy (← mkLambdaFVars xs prf)
    addDocStringCore eqName s!"The monadic view of `{short}.exp` is `{short}`."
    if isPure then
      -- `f.exp_denoteM` for effectful callers, `pure (f x y).run`, and `f.exp_denote`.
      do
        let isPureEq ← mkEq (mkApp3 (mkConst ``Exp.isPure) Γ expT (gcn expName))
          (mkConst ``Bool.true)
        let pureNow ← withTransparency .all <|
          whnf (mkApp3 (mkConst ``Exp.isPure) Γ expT (gcn expName))
        let isPurePrf ← if gvs.isEmpty || pureNow.isConstOf ``Bool.true then
            mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool)
              (mkConst ``Bool.true)) isPureEq
          else do
            -- Generic over an implementation, a callee's body is opaque, so its `g.isPure` lemma
            -- from the interface is used and the other terms are unfolded. Then `f.isPure` is
            -- added for callers.
            let env ← getEnv
            let ds := (#[expName] ++ (body.callees.filter fun (g : FnInfo) =>
                !env.contains (g.declName ++ `isPure)).map (·.declName ++ `exp)).map mkCIdent
            let ls ← (body.callees.filter fun (g : FnInfo) =>
                env.contains (g.declName ++ `isPure)).mapM fun g =>
              `(Lean.Parser.Tactic.simpLemma| $(mkCIdent (g.declName ++ `isPure)):ident)
            let cl ← (body.callees.filter fun (g : FnInfo) =>
                env.contains (g.declName ++ `isPure)).foldrM (fun g acc =>
                `(tactic| first | apply $(mkCIdent (g.declName ++ `isPure)) | $acc:tactic))
              (← `(tactic| fail))
            let dls ← ds.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $d:ident)
            let tac ← `(tactic| (simp (config := { decide := true })
              [$dls,*, Millipede.Exp.isPure, $(ls.toArray),*] <;> (repeat' apply And.intro) <;> $cl))
            match ← tryProveE isPureEq tac with
            | .ok p =>
              addThm (declName ++ `isPure) isPureEq p
              pure (gcn (declName ++ `isPure))
            | .error m => throwErrorAt nameStx "`{short}` is not shown pure generically:\n{m}"

        addPureDenotes declName short.toString (gcn expName) isPurePrf (mkAppN (gcn eqName) xs) xs
    else
      let ω := xs[0]!
      withLocalDeclD `w (mkConst ``World) fun w => do
        let den := mkAppN (mkConst ``Exp.denote) #[ω, Γ, expT, gcn expName, env, w]
        let rhsD := mkAppN (mkConst ``StateT.run [0, 0])
          #[mkConst ``World, mkConst ``Id [0], retCarrier, fApp, w]
        let prfD := mkAppN (mkConst ``Exp.denote_of_denoteM_eq)
          #[ω, Γ, expT, gcn expName, env, fApp, mkAppN (gcn eqName) xs, w]
        let dName := declName ++ `exp_denote
        addThm dName (← mkForallFVars (#[ω, w] ++ pxs) (← mkEq den rhsD))
          (← mkLambdaFVars (#[ω, w] ++ pxs) prfD)
        addDocStringCore dName s!"The denotation of `{short}.exp` is `{short}`."
  -- The obligations, as `f.SafeGoal`, `f.safe` and `f.Safe`.
  let goalTy ← withLocalDeclD `ω (mkConst ``Oracle) fun ω =>
    withLocalDeclD `w (mkConst ``World) fun w =>
    withLocalDeclsDND paramDecls.toArray fun xs => do
      let env := envExpr (xs.toList.zip (params.toList.map (·.2.1)))
      let safe := mkAppN (mkConst ``Exp.safe) #[ω, Γ, expX, gcn expName, env, w]
      match hasReq with
      | false => mkForallFVars (#[ω, w] ++ xs) safe
      | true => do
        let p ← reqOf xs
        withLocalDeclD `h p fun h => mkForallFVars (#[ω, w] ++ xs ++ #[h]) safe
  let goalName := declName ++ `SafeGoal
  addDef goalName (mkSort .zero) goalTy (compile := false)
  addDocStringCore goalName s!"The obligations of `{short}` (doc/design/obligations.md), under its \
    `requires`."
  let totalPrf? ← do
    match ← decideTrue (mkApp3 (mkConst ``Exp.total) Γ expX (gcn expName)) with
    | none => pure none
    | some (_, tp) =>
      some <$> forallTelescope goalTy fun ys _ => do
        let ω := ys[0]!; let w := ys[1]!
        let pxs := ys.extract 2 (2 + params.size)
        let env := envExpr (pxs.toList.zip (params.toList.map (·.2.1)))
        mkLambdaFVars ys (mkAppN (mkConst ``Exp.safe_of_total) #[ω, Γ, expX, gcn expName, tp,
          env, w])
  let autoSafe := mp.autoSafe.get opts
  -- The verified analyser runs first, and `mp_safe` gets what it leaves. The analyser evaluates
  -- a closed term, so it does not run on a generic definition.
  let an ← if totalPrf?.isNone && autoSafe && gvs.isEmpty then
      Analyse.analyse declName goalTy Γ expX expName params.size hasReq
    else pure .none
  let totalPrf? := totalPrf? <|> an.full?
  let (mpGoal, mpExp) := an.mpGoal goalTy expName
  let (prfE, viaTactic) ← match totalPrf? with
    | some p => pure (Except.ok p, false)
    | none => if !autoSafe then pure (.error "", false) else (·, true) <$> do
      -- The contract's predicates, as in `requires BrInv r`, are unfolded.
      let preds ← (← contractPreds goalTy).mapM fun n =>
        `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
      let tac ← safeCall body.callees.toArray mpExp (extraGrind := preds)
      -- The attempt has a budget of its own, so that a failing attempt gives up early.
      let budget := mp.autoSafe.maxHeartbeats.get opts * 1000
      let attempt (tac : Syntax) := (·.map an.convert) <$> (withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
          tryProveE mpGoal tac)
      -- When a callee has a contract, the attempt cites it, and if that fails, the attempt is
      -- repeated with the callees' terms, since a contract may say less than the term.
      let viaTerms ← if body.callees.any (fun g => (env0.contains (g.declName ++ `post))) then
          pure (some (← safeCall body.callees.toArray mpExp (extraGrind := preds)
            (contracts := false)))
        else pure none
      let first ← attempt tac
      let first ← match first, viaTerms with
        | .error _, some t => do
          match ← attempt t with
          | .ok p => pure (.ok p)
          | .error _ => pure first
        | _, _ => pure first
      match first with
      | .ok p => pure (.ok p)
      | .error left =>
        -- Then `mp_auto` runs with the libraries' `@[mp_auto]` facts. It is elaborated by name
        -- because it is defined later, and the message shows the first attempt's goal.
        match ← attempt mpAutoSyntax with
        | .ok p => pure (.ok p)
        | .error _ =>
          -- Then loop invariants from the contract are tried at each loop's state: `requires`,
          -- `ensures` with `p'` the current value of a `&mut` parameter `p`, and both.
          let loops := ((loopNamesExt.getState (← getEnv)).find? declName).getD #[]
          let muts := params.filterMap fun (x, _, m, _) => if m == .mut then some x.toString else none
          let ens? ← ensuresStxRef.get
          let mut r := .error left
          for alts in ← invCandidates loops muts req? ens? do
            if let .ok p ← attempt (Syntax.node .none `Millipede.Meta.mpAutoTac
                #[Syntax.atom .none "mp_auto", mkNullNode, mkNullNode #[alts]]) then
              r := .ok p; break
          pure r
  -- A proof found by `mp_safe` is checked by the kernel now, within its budget. What follows
  -- gets a fresh heartbeat count, since the attempts may have used most of the command's budget.
  let checked ← match prfE, viaTactic with
    | .ok prf, true => withCurrHeartbeats (addThmBudget (declName ++ `safe) goalTy prf
        (mp.autoSafe.kernelHeartbeats.get opts))
    | _, _ => pure false
  let prfE := if viaTactic && !checked && prfE matches .ok _ then
    .error "(the proof found is too expensive for the kernel, `mp.autoSafe.kernelHeartbeats`)"
    else prfE
  let prf? := match prfE with | .ok p => some p | .error _ => none
  let info := { info0 with hasSafe := prf?.isSome }
  match prf? with
  | some prf =>
    withCurrHeartbeats <| addSafeDecls declName short info goalTy prf (added := checked)
  | none =>
    if autoSafe then
      let left := match prfE with | .error m => if m.isEmpty then "" else s!"; left:\n{m}" | _ => ""
      -- Lean's advice to raise `maxHeartbeats` does not apply to the attempt's own budget, which
      -- `budgetHint` names.
      let left := (left.replace "\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit." "").replace
        "\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command." ""
      let loops := ((loopNamesExt.getState (← getEnv)).find? declName).getD #[]
      let flags := ["returned", "returned value", "left the loop"]
      let pat (ns : Array String) : String :=
        "(" ++ ", ".intercalate ((ns.push "_").toList.map fun x => if flags.contains x then "_" else x) ++ ")"
      -- Only when the goal left is about a loop's state.
      let aboutLoop := loops.any fun ns => ns.any fun x => !flags.contains x && x != "_" &&
        ((left.splitOn s!"\n{x} :").length > 1 || (left.splitOn s!"\n{x}' :").length > 1)
      let invHint := if !aboutLoop then "" else
        s!"\n(if they depend on the state of a loop, give an invariant per loop, in source order: \
        `mp prove {short}.safe := by mp_auto invariants" ++
        String.join (loops.toList.map fun ns => s!" · fun _ _ {pat ns} => …") ++ "`)"
      logInfoAt nameStx m!"the obligations of `{short}` were not discharged automatically; prove \
      them with `mp prove {short}.safe := …` (the goal is `{short}.SafeGoal`){left}\
      {keyStackHint left}{budgetHint short left}{pairHint stx[9] left}{invHint}"
  -- A generic function is registered with its variables abstracted, and instantiated at a use.
  let info := info.abstractGen gvs
  modifyEnv (registry.addEntry · (.fn info))
where
  /-- Add `f.safe`, `f.Safe` and the simp form `f.Safe'` used by callers. -/
  addSafeDecls (declName short : Name) (info : FnInfo) (goalTy prf : Expr) (added := false) :
      TermElabM Unit := do
    let safeName := declName ++ `safe
    unless added do addThm safeName goalTy prf
    addDocStringCore safeName s!"The obligations of `{short}` hold (under its `requires`)."
    -- `f.Safe : f.fn.Safe` or `f.fnRef.Safe`, by matching the environment.
    let gvs ← genVarsRef.get
    let gcn (n : Name) : Expr := mkAppN (mkConst n) gvs
    let bundle := if info.isRef then declName ++ `fnRef else declName ++ `fn
    let safeTy ← if info.isRef then do
        let (_, os) := info.psOs
        pure (mkApp4 (mkConst ``FnRef.Safe) (tyList info.psOs.1) (tyList os) info.ret.toTy
          (gcn bundle))
      else pure (mkApp3 (mkConst ``Fn.Safe) (tyList info.psOs.1) info.ret.toTy (gcn bundle))
    let n := info.params.size
    let names : List (TSyntax `term) :=
      (List.range n).map fun i => ⟨(mkIdent (Name.mkSimple s!"x{i}")).raw⟩
    -- The pattern `.cons xₙ₋₁ (… (.cons x₀ .nil))`.
    let pat ← names.foldlM (fun acc x => `(Millipede.Env.cons $x $acc)) (← `(Millipede.Env.nil))
    let args : Array (TSyntax `term) := names.toArray
    let safeS ← exprToSyntax (gcn safeName)
    let call ← `($safeS ω w $args* h)
    let callNoH ← `($safeS ω w $args*)
    let tac ← `(tactic| (intro ω env w h; match env with | $pat:term => first | exact $call | exact $callNoH))
    match ← tryProveE safeTy tac with
    | .ok p =>
      addThm (declName ++ `Safe) safeTy p
      addDocStringCore (declName ++ `Safe) s!"`{short}`'s bundle is safe under its `requires` \
        (cited by callers)."
      -- The form that callers' `mp_safe` uses as a simp lemma.
      addSafeSimp declName (gcn (declName ++ `exp))
        (if info.isRef then some (gcn (declName ++ `req)) else none)
        fun ω env w h => mkAppN (gcn (declName ++ `Safe)) #[ω, env, w, h]
    | .error m => throwError "internal error: could not derive `{short}.Safe` from \
      `{short}.safe`:\n{m}"

@[command_elab mpDef] def elabMpDef : CommandElab := fun stx => do
  try withGenVars stx (elabMpDefCore stx)
  catch e =>
    failedDefs.modify (·.insert ((← getCurrNamespace) ++ stx[3].getId))
    throw e

/-- Elaborate `mp prove f.safe := proof`. The dispatcher of `mp prove` is `elabMpProveCmd` in
`Millipede.Meta.Prove`. -/
def elabMpProveSafe (stx : Syntax) : CommandElabM Unit := do
  let target := stx[3].getId
  let fId := mkIdentFrom stx[3] target.getPrefix
  let some (.fn info0) ← withGenVars stx ((resolveEntry fId).run' 0) (force := true)
    | throwErrorAt stx[3] "`{target.getPrefix}` is not an `mp def`"
  -- A generic function is proved under the same `variable`s.
  withGenVars stx (force := info0.nGen > 0) do
  withFnGenVars info0 do
  let some (.fn info) ← (resolveEntry fId).run' 0
    | throwErrorAt stx[3] "`{target.getPrefix}` is not an `mp def`"
  if info.hasSafe then throwErrorAt stx[3] "`{info.declName}.safe` is already proved"
  let some ci := (← getEnv).find? (info.declName ++ `SafeGoal) | throwError "no SafeGoal"
  let some goalTy := ci.value? | throwError "no SafeGoal"
  let gvs ← genVarsRef.get
  let info := if info.nGen > 0 then info.instantiate gvs else info
  let goalTy := goalTy.beta gvs
  let prf ← Term.elabTermEnsuringType stx[5] goalTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let prf ← instantiateMVars prf
  if prf.hasMVar || prf.hasSorry then throwErrorAt stx[5] "the proof is incomplete"
  let info := { info with hasSafe := true }
  elabMpDefCore.addSafeDecls info.declName info.declName info goalTy prf
  modifyEnv (registry.addEntry · (.fn (info.abstractGen gvs)))

/-- Whether a type is that of a byte slice parameter, `[U8]` or `[UInt8]`. -/
def isByteSliceTy (t : Syntax) : Bool :=
  match t with
  | `([U8]) | `([UInt8]) => true
  | _ => false

/-- Elaborate `mp extern`. -/
def elabMpExternCore (stx : Syntax) : TermElabM Unit := do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let noreturn := stx[3].getNumArgs == 1
  let some sym := stx[4].isStrLit? | throwErrorAt stx[4] "expected the symbol as a string"
  let nameStx := stx[5]
  let declName := (← getCurrNamespace) ++ nameStx.getId
  let mut params : Array (Name × EPTy) := #[]
  let mut caps : Array (Name × String) := #[]
  for b in stx[6].getArgs do
    -- A leading parameter `(c : &C)` of a token type `C` makes the extern require a token.
    if params.isEmpty && b[3].getKind == ``mpRefShr then
      let some t ← (exprToSTy (← Term.elabType b[3][1]) : MetaM _)
        | throwErrorAt b[3] "unknown parameter type"
      if let some cls ← capClassOf? t then
        for x in b[1].getArgs do caps := caps.push (x.getId, cls)
        continue
    let k ← match b[3] with
      | `(UInt64) | `(U64) => pure EPTy.word
      | `(Bytes) => pure EPTy.bytes
      | `(OutByte) => pure EPTy.outByte
      | t =>
        if t.getKind == ``mpRefShr && isByteSliceTy t[1] then pure EPTy.bytes
        else if t.getKind == ``mpRefMut && isByteSliceTy t[1] then pure EPTy.sliceOut
        else throwErrorAt t "extern parameters are `UInt64` words, `Bytes` or `&[U8]` input \
          buffers, an `OutByte` buffer or a `&mut [U8]` output buffer"
    for x in b[1].getArgs do params := params.push (x.getId, k)
  match stx[8] with
  | `(UInt64) | `(U64) => pure ()
  | t => throwErrorAt t "phase-1 externs return one `UInt64` word"
  let val := mkApp3 (mkConst ``ExtSig.mk) (toExpr sym) (extParamsExpr (params.toList.map (·.2)))
    (toExpr noreturn)
  addDef declName (mkConst ``ExtSig) val
  Term.addTermInfo' nameStx (mkConst declName) (isBinder := true)
  addDocString' declName Syntax.missing doc?
  for (_, cls) in caps do
    let some c := (capClasses (← getEnv)).find? (·.cls == cls)
      | throwErrorAt nameStx "the token class `{cls}` is not declared with `mp capability`"
    unless c.syms.contains sym do
      throwErrorAt nameStx "the extern symbol \"{sym}\" does not belong to the capability \
        `{c.declName}`, whose symbols are {c.syms}"
  modifyEnv (registry.addEntry · (.ext ⟨declName, sym, params, noreturn, caps⟩))

@[command_elab mpExtern] def elabMpExtern : CommandElab := fun stx => do
  liftTermElabM (elabMpExternCore stx)

/-! ## `mp program` -/

/-- The error for an `init` or `step` that is not a registered `mp def`, which names an earlier
failure of its `mp def`, such as a generated theorem that the kernel rejected. -/
def throwNotMpDef {α : Type} (id : Syntax) : TermElabM α := do
  let n := id.getId
  let failed ← failedDefs.get
  if failed.contains ((← getCurrNamespace) ++ n) || failed.contains n then
    throwErrorAt id "`{n}` was not defined because of the error at its `mp def`"
  throwErrorAt id "`{n}` is not an `mp def`"

/-- Define the program `name` of `mp program name (root : T) init f step g` and its `wf_eq`, and
return the program's name and the `FnInfo`s of `f` and `g`, which `mp program … invariant` in
`Millipede.Meta.Program` also uses. -/
def mpProgramBase (stx : Syntax) : TermElabM (Name × FnInfo × FnInfo) := do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let nameStx := stx[3]
  let declName := (← getCurrNamespace) ++ nameStx.getId
  let T ← (elabTy stx[7]).run' 0
  let some (.fn fi) ← (resolveEntry stx[10]).run' 0 | throwNotMpDef stx[10]
  -- An `init` that takes tokens is called by the generated `p.init`, which mints them.
  let (fi, granted) ← if fi.params.isEmpty then pure (fi, []) else do
    let cls ← fi.params.toList.mapM fun (x, t, m) => do
      let some c ← capClassOf? t
        | throwErrorAt stx[10] "`init` must take no parameter, or only tokens of capability \
            classes, and return the root type {T}: its parameter `{x}` is not a token"
      unless m == .own do
        throwErrorAt stx[10] "`init` takes its tokens by value: `{x}` is a reference"
      pure c
    let wrapId := mkIdentFrom nameStx (nameStx.getId ++ `init)
    let fId : Ident := ⟨stx[10]⟩
    let mints ← cls.toArray.mapM fun c => `(($(mkIdent ``Millipede.Lib.Cap.mint) $(quote c)))
    let cmd ← `(command| mp def $wrapId : $(⟨stx[7]⟩) := $fId $mints*)
    grantRef.set cls
    try elabMpDefCore cmd finally grantRef.set []
    let some (.fn w) ← (resolveEntry wrapId).run' 0
      | throwErrorAt stx[10] "internal error: the `init` wrapper `{wrapId.getId}`"
    pure (w, cls)
  let some (.fn fs) ← (resolveEntry stx[12]).run' 0 | throwNotMpDef stx[12]
  -- A generic `init` or `step` of this section is taken at its variables, and the program takes
  -- theirs.
  let fi ← fi.inScope
  let fs ← fs.inScope
  if !(← genVarsRef.get).isEmpty then
    let inv := if stx[13].getNumArgs == 0 then #[] else #[stx[13][1]]
    genVarsRef.set (← includedGenVars (identsOf stx[7] ++ inv.flatMap identsOf)
      (fi.genArgs ++ fs.genArgs))
  unless fi.params.isEmpty && fi.ret == T do
    throwErrorAt stx[10] "`init` must take no parameter and return the root type {T}"
  unless fs.params.size == 1 && fs.params[0]!.2 == (T, .mut) && fs.ret == .unit do
    throwErrorAt stx[12] "`step` must take one parameter `&mut {T.fmtArg}` and return Unit"
  let nil := mkApp (mkConst ``List.nil [1]) (mkConst ``Ty)
  let one := tyList [T]
  let initE := if fi.isRef then
      mkAppN (mkConst ``Exp.callRef) #[nil, nil, nil, T.toTy, T.toTy, toExpr fi.declName.toString,
        fi.const `req, fi.const `exp, mkApp (mkConst ``RArgs.nil) nil,
        mkApp3 (mkConst ``Exp.atom) one T.toTy (mkApp3 (mkConst ``Atom.var) one T.toTy (memExpr [T] 0))]
    else fi.const `exp
  let ctx2 := [STy.unit, T]
  let stepE := mkAppN (mkConst ``Exp.callRef) #[one, one, one, STy.unit.toTy, T.toTy,
    toExpr fs.declName.toString, fs.const `req, fs.const `exp,
    mkAppN (mkConst ``RArgs.mut) #[one, T.toTy, nil, nil,
      mkApp3 (mkConst ``Place.var) one T.toTy (memExpr [T] 0), mkApp (mkConst ``RArgs.nil) one],
    mkApp3 (mkConst ``Exp.atom) (tyList ctx2) T.toTy
      (mkApp3 (mkConst ``Atom.var) (tyList ctx2) T.toTy (memExpr ctx2 1))]
  addDef declName (mkConst ``Program) (mkApp3 (mkConst ``Program.mk) T.toTy initE stepE)
  Term.addTermInfo' nameStx (mkConst declName) (isBinder := true)
  addDocString' declName Syntax.missing doc?
  -- For a generic program `Program.wf` is decided at each instance, when `compile` checks it.
  unless (← genVarsRef.get).isEmpty do return (declName, fi, fs)
  let some (wfProp, wfPrf) ← decideTrue (mkApp (mkConst ``Program.wf) (mkConst declName))
    | throwErrorAt nameStx "the program does not pass the checker (`Program.wf`)"
  addThm (declName ++ `wf_eq) wfProp wfPrf
  addDocStringCore (declName ++ `wf_eq) "The program passes the checker (kernel `decide`)."
  -- The capability classes that `init` is not granted, whose externs no trace contains.
  let what := m!"the program `{nameStx.getId}`"
  if let some (tyI, hi) ← noCallsProof what nameStx nil T.toTy initE granted then
    let some (_, hs) ← noCallsProof what nameStx one T.toTy stepE granted
      | throwError "internal error: capability classes"
    let S := tyI.appArg!
    let P := Lean.mkConst declName
    addThm (declName ++ `noCalls) (mkApp2 (mkConst ``Program.NoCalls) P S)
      (mkApp4 (mkConst ``Program.noCalls_of) P S hi hs)
    addDocStringCore (declName ++ `noCalls) "No trace of the program contains a call of an extern \
      symbol of a capability class that its `init` does not take (generated by `mp program`)."
  return (declName, fi, fs)

/-! ## `#mp_cost` -/

/-- The `exp` constants of all registered functions reachable from the function `n` through
callees, transitively. -/
partial def reachableExps (env : Environment) (n : Name) (acc : NameSet := {}) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  let some ci := env.find? n | return acc
  let some v := ci.value? | return acc
  for c in v.getUsedConstants do
    if c.isStr && c.getString! == "exp" then
      if let some (.fn _) := lookupEntry env c.getPrefix then
        acc := reachableExps env c acc
  return acc

@[command_elab mpCost] def elabMpCost : CommandElab := fun stx => liftTermElabM do
  let fStx := stx[1]
  let some (.fn info) ← (resolveEntry fStx).run' 0
    | throwErrorAt fStx "`{fStx.getId}` is not an `mp def`"
  let expName := info.declName ++ `exp
  let Γ := tyList info.psOs.1
  let expT := info.expTyExpr
  let exps := (reachableExps (← getEnv) expName).toList
  -- the mode in which callers charge the body: `split` when it hands back `&mut` parameters
  let hb := Lean.mkConst (if info.isRef && !info.psOs.2.isEmpty then ``Hb.split else ``Hb.copy)
  if stx[2].getNumArgs == 2 then
    let κ ← Term.elabTermEnsuringType stx[2][1] (mkConst ``CostModel)
    Term.synthesizeSyntheticMVarsNoPostponing
    let κ ← instantiateMVars κ
    let c := mkApp5 (mkConst ``Exp.cost) κ Γ expT hb (mkConst expName)
    let v ← withTransparency .all <| reduce c
    logInfo m!"cost {fStx.getId} ≤ {v}"
  else
    withLocalDeclD `κ (mkConst ``CostModel) fun κ => do
      let c := mkApp5 (mkConst ``Exp.cost) κ Γ expT hb (mkConst expName)
      let mut thms : SimpTheorems := {}
      for n in [``Exp.cost, ``Prim.cost, ``EArgs.cost, ``EArgs.depth, ``EArgs.slices, ``Hb.up,
          ``Hb.of, ``Hb.atomW, ``Hb.mkW] ++ exps do
        thms ← thms.addDeclToUnfold n
      for n in [``Nat.max_self, ``Nat.add_zero, ``Nat.zero_add, ``Nat.mul_one, ``Nat.one_mul,
          ``Nat.zero_mul, ``Nat.mul_zero, ``Ty.words_u64, ``Ty.words_bool, ``Ty.words_unit, ``Ty.words_result,
          ``ctxWords_nil, ``ctxWords_cons, ``List.isEmpty_nil, ``List.isEmpty_cons, ``Bool.not_true,
          ``Bool.not_false, ``Bool.false_eq_true, ``Hb.up_copy, ``Hb.up_split, ``Hb.up_whole] do
        thms ← thms.addConst n
      let sctx ← Simp.mkContext (config := { arith := true }) (simpTheorems := #[thms])
        (congrTheorems := ← getSimpCongrTheorems)
      let (r, _) ← simp c sctx (simprocs := #[← Simp.getSimprocs])
      -- Closed widths and place depths are numerals.
      let e ← Meta.transform r.expr (post := fun e => do
        if (e.isAppOfArity ``Ty.words 1 || e.isAppOfArity ``Place.depth 3) && !e.hasFVar then
          let v ← withTransparency .all <| reduce e
          if v.isRawNatLit || v.nat?.isSome then return .done v
        return .continue)
      let (r, _) ← simp e sctx (simprocs := #[← Simp.getSimprocs])
      logInfo m!"cost {fStx.getId} ≤ {r.expr}"

/-- Outside `mp def` and its parameter types, a reference is an error. -/
@[term_elab mpRefMut] def elabMpRefMutTerm : TermElab := fun stx _ =>
  throwErrorAt stx "`&mut p` is only available inside `mp def`"

@[term_elab mpRefShr] def elabMpRefShrTerm : TermElab := fun stx _ =>
  throwErrorAt stx "`&p` is only available inside `mp def`"

end Millipede.Meta
