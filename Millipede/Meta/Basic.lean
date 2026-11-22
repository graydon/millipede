import Lean
import Millipede.Meta.Sem
import Millipede.Core.Quantity

/-!
# Surface types and the registries of functions, externs and data types

For every earlier `mp def` and `mp extern` the elaborator needs the parameters with their types
and modes, the result type and the `requires` clause. For every type declared with
`deriving Data` it needs the fields or variants and the generated lenses, constructors and splits.
This module keeps them in persistent environment extensions, so that any later file that imports
the declaring one can use them.

`STy` is the elaborator's description of an object type. It covers `UInt64`, `Bool`, `Unit` and
`Result ε α`, arrays, `Slots`, slices, pairs, derived structs and enums, quantities, and any other
Lean type with a `Data` instance, which carries its `Ty` term. `STy.toTy` maps a surface type to
its `Ty` term and `STy.carrier` to its Lean carrier type.
-/

namespace Millipede

/-- A copyable type, whose values are not linear. Under a binder `variable (T : Type) [Data T]` the
linearity of `T` is unknown, because `Data.linear T` does not reduce, so `mp def` treats `T` as
linear. An instance `[Data.Copy T]` says that it is not, so a generic function may copy a `T` out
of a place with `a[i]!`. Instances for closed types are found by `decide`. -/
class Data.Copy (α : Type) [Data α] : Prop where
  linear_false : Data.linear α = false

/-- The instance `inst` with `linear := false`, which `Data.Copy` says it equals. The kernel
evaluates the borrow checker `Exp.wf` of a generic definition at it, since its linearity
reduces. -/
@[reducible] def Data.copyInst (α : Type) [inst : Data α] : Data α := { inst with linear := false }

theorem Data.copyInst_eq (α : Type) [inst : Data α] [h : Data.Copy α] : Data.copyInst α = inst := by
  obtain ⟨hl⟩ := h; cases inst; simp only at hl; subst hl; rfl

instance : Data.Copy UInt64 := ⟨rfl⟩
instance : Data.Copy UInt8 := ⟨rfl⟩
instance : Data.Copy Bool := ⟨rfl⟩
instance : Data.Copy Unit := ⟨rfl⟩

end Millipede

namespace Millipede.Meta

open Lean Meta

/-- The command keyword `mp`. It is not reserved, so `mp` stays an ordinary identifier elsewhere,
and it is tried at identifiers in command position. -/
def mpKw : Lean.ParserDescr := Lean.ParserDescr.nonReservedSymbol "mp" true

/-- Surface object types. -/
inductive STy where
  | u64
  | bool
  | unit
  | result (ε α : STy)
  /-- `Arr T n`, whose carrier is `Vector T n`. The size is a Lean `Nat` term, which is a numeral
  for a closed type, or an open term such as a size variable `n` or `2 * n` under `variable`
  binders. -/
  | arr (t : STy) (n : Expr)
  /-- `Slots T n`. -/
  | slots (t : STy) (n : Expr)
  /-- `Slice T n`, a slice view. It is second-class, a view binder only and never a value. In Core
  it is `Ty.view T n`, whose carrier is `Slots T n` with the viewed elements in the full cells. -/
  | slice (t : STy) (n : Expr)
  /-- `A × B`. -/
  | pair (a b : STy)
  /-- A struct or enum with `deriving Data`, whose instance is `n.instData`. A parameterised
  struct is applied to its parameters, where `cargs` are the carrier's arguments, as in `S T n`,
  and `iargs` the instance's, as in `S.instData T inst n`, with the `Data` instance after each
  type parameter. Both are empty for a closed type. -/
  | adt (n : Name) (lin : Bool) (cargs : Array Expr) (iargs : Array Expr)
  /-- Any other type with `Data`, with its `Ty` term, its carrier, its linearity and its
  spelling. -/
  | other (ty carrier : Expr) (lin : Bool) (fmt : String)
  /-- `Ty.tup ts`, kept folded. It is the type of the values that a function with `&mut`
  parameters hands back, as in the signature of `Exp.callRef`. -/
  | tup (ts : List STy)
  /-- `Q u`, a count of the unit `u`, named by its constant, of dimension `dim` with scale
  `scale`. It is erased, so its Core type is `Ty.u64`. -/
  | qty (u : Name) (dim : String) (scale : Nat)
deriving BEq, Inhabited

/-- Map every Lean term in a surface type, such as sizes, carriers and instances. It abstracts the
`variable`s of a generic definition before it is stored in the registry, and instantiates them at
a use. -/
partial def STy.mapExpr (f : Expr → Expr) : STy → STy
  | .result e a => .result (e.mapExpr f) (a.mapExpr f)
  | .arr t n => .arr (t.mapExpr f) (f n)
  | .slots t n => .slots (t.mapExpr f) (f n)
  | .slice t n => .slice (t.mapExpr f) (f n)
  | .pair a b => .pair (a.mapExpr f) (b.mapExpr f)
  | .adt n l cs is => .adt n l (cs.map f) (is.map f)
  | .other ty c l s => .other (f ty) (f c) l s
  | .tup ts => .tup (ts.map (·.mapExpr f))
  | t => t

/-- Whether a type is linear, so that its values must be used exactly once. It mirrors
`Data.linear`. -/
partial def STy.linear : STy → Bool
  | .result _ _ => true
  | .arr t _ | .slots t _ | .slice t _ => t.linear
  | .pair a b => a.linear || b.linear
  | .adt _ l _ _ | .other _ _ l _ => l
  | .tup ts => ts.any STy.linear
  | _ => false

/-- The spelling of a size term, which is its numeral, the name of a size variable, or `_`. -/
def fmtN (n : Expr) : String :=
  match n.nat? <|> n.rawNatLit? with
  | some k => toString k
  | none => match n with
    | .fvar _ | .const .. => toString n
    | _ => "_"

/-- The spelling of a parameterised type's arguments, for messages. Numerals and constants are
written as they are, and anything else as `_`. -/
def fmtArgs (cs : Array Expr) : String :=
  cs.foldl (fun acc c => acc ++ " " ++ match c.nat? <|> c.rawNatLit? with
    | some k => toString k
    | none => match c.getAppFn with
      | .const m _ => if c.getAppNumArgs == 0 then toString m.componentsRev.head! else "_"
      | _ => "_") ""

/-- The value of a size term, if it is a numeral, as in a closed type. -/
def STy.natOf? (n : Expr) : Option Nat := n.nat? <|> n.rawNatLit?

mutual
/-- Source spelling of a surface type, for messages. -/
partial def STy.fmt : STy → String
  | .u64 => "UInt64"
  | .bool => "Bool"
  | .unit => "Unit"
  | .result e a => s!"Result {e.fmtArg} {a.fmtArg}"
  | .arr t n => s!"Arr {t.fmtArg} {fmtN n}"
  | .slots t n => s!"Slots {t.fmtArg} {fmtN n}"
  | .slice t n => s!"Slice {t.fmtArg} {fmtN n}"
  | .pair a b => s!"{a.fmtArg} × {b.fmtArg}"
  | .adt n _ cs _ => n.toString ++ fmtArgs cs
  | .other _ _ _ s => s
  | .tup ts => "(" ++ ", ".intercalate (ts.map STy.fmt) ++ ")"
  | .qty u _ _ => s!"Q {u.componentsRev.head!}"

/-- The spelling of a type as an argument, parenthesised if compound. -/
partial def STy.fmtArg : STy → String
  | .result e a => s!"(Result {e.fmtArg} {a.fmtArg})"
  | .arr t n => s!"(Arr {t.fmtArg} {fmtN n})"
  | .slots t n => s!"(Slots {t.fmtArg} {fmtN n})"
  | .slice t n => s!"(Slice {t.fmtArg} {fmtN n})"
  | .pair a b => s!"({a.fmtArg} × {b.fmtArg})"
  | .other _ _ _ s => if s.any (· == ' ') then s!"({s})" else s
  | .u64 => "UInt64"
  | .bool => "Bool"
  | .unit => "Unit"
  | .adt n _ cs _ => if cs.isEmpty then n.toString else s!"({n}{fmtArgs cs})"
  | .tup ts => "(" ++ ", ".intercalate (ts.map STy.fmt) ++ ")"
  | .qty u _ _ => s!"(Q {u.componentsRev.head!})"
end

instance : ToString STy := ⟨STy.fmt⟩

/-- The `Ty` term denoted by a surface type. -/
partial def STy.toTy : STy → Expr
  | .u64 => mkConst ``Ty.u64
  | .bool => mkConst ``Ty.bool
  | .unit => mkConst ``Ty.unit
  | .result e a => mkApp2 (mkConst ``Ty.result) e.toTy a.toTy
  | .arr t n => mkApp2 (mkConst ``Ty.arr) t.toTy n
  | .slots t n => mkApp2 (mkConst ``Ty.slots) t.toTy n
  | .slice t n => mkApp2 (mkConst ``Ty.view) t.toTy n
  | .pair a b => mkApp2 (mkConst ``Ty.pair) a.toTy b.toTy
  | .adt n _ cs is => mkApp2 (mkConst ``Ty.mk) (mkAppN (mkConst n) cs)
      (mkAppN (mkConst (n ++ `instData)) is)
  | .other ty _ _ _ => ty
  | .tup ts => mkApp (mkConst ``Ty.tup) (ts.foldr (fun t acc =>
      mkApp3 (mkConst ``List.cons [1]) (mkConst ``Ty) t.toTy acc)
      (mkApp (mkConst ``List.nil [1]) (mkConst ``Ty)))
  | .qty .. => mkConst ``Ty.u64

/-- The Lean carrier type of a surface type, such as `UInt64`, `Bool`, `Unit`, `Except ε α` or
`Vector T n`. -/
partial def STy.carrier : STy → Expr
  | .u64 => mkConst ``UInt64
  | .bool => mkConst ``Bool
  | .unit => mkConst ``Unit
  | .result e a => mkApp2 (mkConst ``Except [0, 0]) e.carrier a.carrier
  | .arr t n => mkApp2 (mkConst ``Vector [0]) t.carrier n
  | .slots t n => mkApp2 (mkConst ``Slots) t.carrier n
  | .slice t n => mkApp2 (mkConst ``Slots) t.carrier n
  | .pair a b => mkApp2 (mkConst ``Prod [0, 0]) a.carrier b.carrier
  | .adt n _ cs _ => mkAppN (mkConst n) cs
  | .other _ c _ _ => c
  | .tup ts => ts.foldr (fun t acc => mkApp2 (mkConst ``Prod [0, 0]) t.carrier acc) (mkConst ``Unit)
  | .qty .. => mkConst ``UInt64

/-- The `List Ty` term for a list of surface types. -/
def tyList (ts : List STy) : Expr :=
  ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [1]) (mkConst ``Ty) t.toTy acc)
    (mkApp (mkConst ``List.nil [1]) (mkConst ``Ty))

/-- Kinds of extern parameter at the surface. A word is passed as it is. A byte buffer the callee
reads, `Bytes` or `&[U8]`, is a string literal or a shared slice `&a[lo:hi]` of a byte array. A
one-byte buffer the callee writes, `OutByte`, takes no argument at call sites, and the call's
value is the byte read or `2^64 - 1`. A mutable byte slice the callee writes, `&mut [U8]`, takes
the argument `&mut a[lo:hi]`, and the call's value is the raw result word. -/
inductive EPTy where
  | word
  | bytes
  | outByte
  | sliceOut
deriving BEq, Repr, Inhabited

/-- Parameter modes at the surface, which are owned, `&T` and `&mut T`. -/
inductive PMode where
  | own
  | shr
  | mut
deriving BEq, Repr, Inhabited

/-- The `Mode` constant for a surface mode. -/
def PMode.toExpr : PMode → Expr
  | .own => mkConst ``Mode.own
  | .shr => mkConst ``Mode.shr
  | .mut => mkConst ``Mode.mut

/-- Source spelling of a parameter type with its mode. -/
def PMode.fmt (m : PMode) (t : STy) : String :=
  match m with
  | .own => t.fmt
  | .shr => s!"&{t.fmtArg}"
  | .mut => s!"&mut {t.fmtArg}"

/-- A declared `mp def`, with its Lean name, its parameters in source order with their types and
modes, its result type, and whether it is pure, which means it calls no extern, transitively.

A function with a `&` or `&mut` parameter or a `requires` clause is a reference function,
`isRef`. Its Core term returns its result together with the final values of its `mut`
parameters, callers use `Exp.callRef`, which carries `requires`, and its `requires` is the
constant `f.req`. Other functions are `Fn`s called with `Exp.call`. -/
structure FnInfo where
  declName : Name
  params : Array (Name × STy × PMode)
  ret : STy
  isPure : Bool
  isRef : Bool
  /-- Whether the generated `f.Safe` theorem exists, which means the obligations were proved. -/
  hasSafe : Bool := true
  /-- Whether the normal form `f` and its equations `f.exp_run` or `f.exp_denoteM` exist, which
  they do unless `mp.normalForm` is off. -/
  hasNf : Bool := true
  /-- For a generic definition, the number of `variable`s that every generated declaration takes
  first, as in `f.exp T n`, `f T n` or `f.safe T n`. In the registry the surface types are stored
  with these abstracted as loose bound variables, and at a use they are instantiated with
  `genArgs`. -/
  nGen : Nat := 0
  /-- The arguments of the generated declarations at this use, empty in the registry. -/
  genArgs : Array Expr := #[]
  /-- The positions, among the section's `variable`s, of those the generated declarations take,
  in order. Positions are used because instance binders have no stable names. -/
  genIdx : Array Nat := #[]
deriving Inhabited

/-- The variables of the generic definition being elaborated, which are the `variable`s in scope
that `mp def` abstracts every generated declaration over. It is empty for a closed definition,
and `mp def` sets it for the extent of one command. -/
initialize genVarsRef : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- The section variables named by Lean's `include` command, for the command being elaborated. A
generic definition takes them whether or not it mentions them. -/
initialize genIncludedRef : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- A generated constant applied to the variables of the generic definition being elaborated, or
`mkConst n` for a closed one. -/
def gc (n : Name) : IO Expr := return mkAppN (mkConst n) (← genVarsRef.get)

/-- `f.x` applied to the generic arguments at this use, or `mkConst` for a closed function. -/
def FnInfo.const (f : FnInfo) (x : Name) : Expr := mkAppN (mkConst (f.declName ++ x)) f.genArgs

/-- The registry form of a generic function's info, with its variables `gvs` abstracted. -/
def FnInfo.abstractGen (f : FnInfo) (gvs : Array Expr) : FnInfo :=
  if gvs.isEmpty then f else
  let g := fun (e : Expr) => e.abstract gvs
  let ps := f.params.map fun (x, t, m) => (x, t.mapExpr g, m)
  { f with params := ps, ret := f.ret.mapExpr g, genArgs := #[] }

/-- A generic function's registry info at a use, with the variables of its surface types
instantiated by `args`. -/
def FnInfo.instantiate (f : FnInfo) (args : Array Expr) : FnInfo :=
  let g := fun (e : Expr) => e.instantiateRev args
  let ps := f.params.map fun (x, t, m) => (x, t.mapExpr g, m)
  { f with params := ps, ret := f.ret.mapExpr g, genArgs := args }

/-- The types of the `mut` parameters of a function, in source order. -/
def FnInfo.muts (f : FnInfo) : List STy :=
  f.params.toList.filterMap fun (_, t, m) => if m == .mut then some t else none

/-- A declared `mp extern`, with the name of its `ExtSig` constant, its symbol, its parameters,
whether it is `noreturn`, and its leading token parameters with their capability classes, which
a call must pass and which the `ExtSig` does not have. -/
structure ExtInfo where
  declName : Name
  sym : String
  params : Array (Name × EPTy)
  noreturn : Bool
  caps : Array (Name × String) := #[]
deriving Repr, Inhabited

/-- A field of a derived struct, with its name, surface type, number `Lens.index` and lens
constant `S.f.lens`. -/
structure FieldInfo where
  name : Name
  ty : STy
  idx : Nat
  lens : Name
deriving Inhabited

/-- A variant of a derived enum, with its Lean constructor, whether it has a single field, its
payload type, which is `Unit` without a field, and its `Ctor` constant `E.c.ctor`. -/
structure VariantInfo where
  ctor : Name
  hasField : Bool
  payload : STy
  mkC : Name
deriving Inhabited

/-- What `deriving Data` recorded about a type. -/
inductive AdtKind where
  /-- A struct, with its fields and its constructor `S.ctor`, which is absent when a field is a
  proof. -/
  | struct (fields : Array FieldInfo) (ctorC : Option Name)
  /-- An enum of at least two constructors, with its variants and its split chain `E.split₀ …`,
  which has one split for two variants and one per variant for three or more. -/
  | enum (variants : Array VariantInfo) (splits : Array Name)
deriving Inhabited

/-- A type with `deriving Data`. -/
structure AdtInfo where
  name : Name
  lin : Bool
  kind : AdtKind
  /-- The binders of `S.instData` and of every generated lens and constructor, with `true` for
  the `Data` instance that follows each type parameter. It is empty for a closed type. The field
  types are stored with these binders abstracted as loose bound variables, and are instantiated
  at a use by the instance's arguments. -/
  params : Array Bool := #[]
deriving Inhabited

/-- An entry of the registry. -/
inductive Entry where
  | fn (i : FnInfo)
  | ext (i : ExtInfo)
  | adt (i : AdtInfo)
deriving Inhabited

/-- The name of the declaration an entry describes. -/
def Entry.declName : Entry → Name
  | .fn i => i.declName
  | .ext i => i.declName
  | .adt i => i.name

/-- The registry of `mp def`s, `mp extern`s and derived data types, persistent across files. -/
initialize registry : SimplePersistentEnvExtension Entry (NameMap Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.declName e
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m e => m.insert e.declName e) m) {}
  }

/-- Look up a registered declaration. -/
def lookupEntry (env : Environment) (n : Name) : Option Entry :=
  (registry.getState env).find? n

/-- Look up a derived data type. -/
def lookupAdt (env : Environment) (n : Name) : Option AdtInfo :=
  match lookupEntry env n with
  | some (.adt i) => some i
  | _ => none

/-- The surface type of a Lean carrier type `e`, if it has a `Data` instance. -/
partial def exprToSTy (e : Expr) : MetaM (Option STy) := do
  let e0 ← instantiateMVars e
  let e ← whnfR e0
  -- An open type, such as `A.S` for an implementation variable `A`, is kept as written, because
  -- `whnfR` turns a projection function into a kernel projection that `vcgen` and `grind` do not
  -- take.
  let e := if e0.hasFVar && !e.getAppFn.isConst then e0 else e
  match e.getAppFn, e.getAppArgs with
  | .const ``UInt64 _, #[] => return some .u64
  | .const ``Bool _, #[] => return some .bool
  | .const ``Unit _, #[] | .const ``PUnit _, #[_] => return some .unit
  | .const ``Except _, #[ε, α] =>
    let some ε ← exprToSTy ε | return none
    let some α ← exprToSTy α | return none
    return some (.result ε α)
  | .const ``Vector _, #[t, n] => withN n fun n => do
    let some t ← exprToSTy t | return none
    return some (.arr t n)
  | .const ``Slots _, #[t, n] => withN n fun n => do
    let some t ← exprToSTy t | return none
    return some (.slots t n)
  | .const ``Prod _, #[a, b] =>
    let some a ← exprToSTy a | return none
    let some b ← exprToSTy b | return none
    return some (.pair a b)
  | .const ``Q _, #[u] => qtyOf? u
  | .const n _, #[] =>
    if let some i := lookupAdt (← getEnv) n then return some (.adt n i.lin #[] #[])
    other e
  | .const n _, cargs =>
    -- A parameterised struct applied to its parameters.
    if let some i := lookupAdt (← getEnv) n then
      if i.params.isEmpty then return none
      let mut iargs : Array Expr := #[]
      let mut k := 0
      for isInst in i.params do
        if isInst then
          let some inst ← synthInstance? (mkApp (mkConst ``Data) cargs[k - 1]!) | return none
          iargs := iargs.push inst
        else
          iargs := iargs.push cargs[k]!
          k := k + 1
      let lin ← withTransparency .all <| whnf (mkApp2 (mkConst ``Data.linear) e
        (mkAppN (mkConst (n ++ `instData)) iargs))
      -- A type parameter's linearity is unknown, so it is linear unless the parameters are
      -- copyable.
      let lin := !lin.isConstOf ``Bool.false
      return some (.adt n lin cargs iargs)
    other e
  | _, _ => other e
where
  withN (n : Expr) (k : Expr → MetaM (Option STy)) : MetaM (Option STy) := do
    let n ← instantiateMVars n
    match n.nat? <|> n.rawNatLit? with
    | some v => k (toExpr v)
    | none =>
      if n.hasFVar then k n  -- a size variable or expression of a generic definition
      else match ← (evalNat n).run with
      | some v => k (toExpr v)
      | none => return none
  /-- `Q u` for a unit constant `u` declared with `mp unit`, with its dimension and scale found by
  reduction. -/
  qtyOf? (u : Expr) : MetaM (Option STy) := do
    let .const un _ := u | return none
    let some scale ← evalNat (← whnf (mkApp (mkConst ``QUnit.scale) u)) |>.run | return none
    let .lit (.strVal dim) ← whnf (mkApp (mkConst ``Dim.name) (mkApp (mkConst ``QUnit.dim) u))
      | return none
    return some (.qty un dim scale)
  other (e : Expr) : MetaM (Option STy) := do
    if e.hasMVar then return none
    let some inst ← synthInstance? (mkApp (mkConst ``Data) e) | return none
    let ty := mkApp2 (mkConst ``Ty.mk) e inst
    let lin ← withTransparency .all <| whnf (mkApp2 (mkConst ``Data.linear) e inst)
    -- An open type such as a type variable `T` is linear unless `[Data.Copy T]` is in scope.
    let lin ← if lin.isConstOf ``Bool.true then pure true
      else if lin.isConstOf ``Bool.false then pure false
      else return some (.other ty e
        (← synthInstance? (mkApp2 (mkConst ``Data.Copy) e inst)).isNone (toString (← ppExpr e)))
    let fmt := toString (← ppExpr e)
    return some (.other ty e lin fmt)

/-- Recompute the linearity of the open types in a surface type at a use under `variable`s, whose
`[Data.Copy T]` instances may differ from those where it was stored. A parameterised struct's
field types are stored where the linearity of `T` is unknown. -/
partial def STy.refresh (t : STy) : MetaM STy := do
  match t with
  | .other _ c _ _ => return (← exprToSTy c).getD t
  | .result e a => return .result (← e.refresh) (← a.refresh)
  | .arr e n => return .arr (← e.refresh) n
  | .slots e n => return .slots (← e.refresh) n
  | .slice e n => return .slice (← e.refresh) n
  | .pair a b => return .pair (← a.refresh) (← b.refresh)
  | .adt _ _ cs _ => if cs.isEmpty then pure t else return (← exprToSTy t.carrier).getD t
  | .tup ts => return .tup (← ts.mapM (·.refresh))
  | _ => return t

/-- `@[mp_auto]` marks a lemma that `mp_auto` passes to `grind`, such as a fact of a library's
interface, or a predicate that it unfolds wherever it occurs. -/
register_label_attr mp_auto

/-- `@[mp_auto_fwd]` marks a lemma that `mp_auto` passes to `grind` for forward reasoning, as
`grind [→ l]`, so that it is instantiated from its hypotheses. An example is
`Alloc.KeyStack.used`, instantiated from a `KeyStack` fact. -/
register_label_attr mp_auto_fwd

register_option mp.unfoldPreds : Bool := {
  defValue := true
  descr := "the automatic attempts and `mp_auto` unfold the predicates of a contract (`requires`, \
    `ensures`, `invariant`) defined in the current file or tagged `@[mp_auto]` (`contractPreds`)"
}

/-- Whether `n` is a name that `mp def`, `mp program` or `mp interface` generates for a statement,
as opposed to a user predicate. -/
def generatedPred (n : Name) : Bool :=
  match n with
  | .str _ s => s ∈ ["SafeGoal", "SpecGoal", "InvInitGoal", "InvStepGoal", "req", "invariant"]
  | _ => false

/-- The predicates of a contract, which the automatic attempts and `mp_auto` unfold by passing
them to `grind`. They are the definitions that occur in `e`, or in the body of one found, that are
not recursive, not reducible and have a `Prop` result, and that are defined in the current file
or tagged `@[mp_auto]`. A predicate of an imported library such as `Alloc.KeyStack` stays folded,
because its lemmas are about the folded form. The option `mp.unfoldPreds false` turns this
off. -/
def contractPreds (e : Expr) : MetaM (Array Name) := do
  unless mp.unfoldPreds.get (← getOptions) do return #[]
  let env ← getEnv
  let tagged ← try labelled `mp_auto catch _ => pure #[]
  let isPred (n : Name) : MetaM Bool := do
    let some (.defnInfo v) := env.find? n | return false
    unless (env.getModuleIdxFor? n).isNone || tagged.contains n do return false
    if n.isInternal || generatedPred n || isMatcherCore env n then return false
    -- An `abbrev` is unfolded by `grind` and `simp` anyway.
    if (← getReducibilityStatus n) == .reducible then return false
    if v.value.getUsedConstants.any (fun c => c == n ||
        (c.isStr && (c.getString! == "brecOn" || c.getString! == "fix"))) then return false
    forallTelescopeReducing v.type fun _ b => return b.isProp
  let mut out : Array Name := #[]
  let mut seen : NameSet := {}
  let mut todo := e.getUsedConstants.toList
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let c :: rest := todo | break
    todo := rest
    if seen.contains c then continue
    seen := seen.insert c
    if ← isPred c then
      out := out.push c
      if let some v := (env.find? c).bind (·.value?) then todo := todo ++ v.getUsedConstants.toList
  return out

/-- Add a theorem and wait for the kernel's check of it, which runs in the background with its own
heartbeats, and throw an error if the kernel rejected it. Lean reports the kernel's error and still
keeps the name, as a constant that depends on itself, so without the wait a later command could
cite it. The `mp` commands add their generated theorems with it, so that a rejected one stops the
command that generates it. -/
def addThmChecked (n : Name) (type value : Expr) : CoreM Unit := do
  addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  unless ((← getEnv).toKernelEnv.find? n).any (·.isTheorem) do
    throwError "the kernel rejected the generated theorem `{n}`; its error follows"

/-- A hint after a goal left about an arena's count of cells in use, `live` or `used`. The usual
missing piece is the accounting of the keys the program holds, `Alloc.KeyStack`. -/
def keyStackHint (left0 : String) : String :=
  -- The target only, without the hypotheses shown above it.
  let left := (left0.splitOn "⊢ ").getLast!
  if (left.splitOn ".live").length > 1 || (left.splitOn ".used").length > 1 ||
      (left.splitOn "used ").length > 1 then
    "\nhint: a goal about an arena's cells in use usually needs the keys held in the invariant: \
      `A.KeyStack s keys n` (a stack of keys in `Slots`, Millipede/Lib/Alloc.lean; \
      doc/reference/surface.md, \"Library\")"
  else ""

/-- A hint after an automatic attempt at the obligations of `f` that ran out of its budget. The
attempt's `simp` over the Core term costs more with each variable in scope and each read of one,
so a long function with a loop and several branches can exceed the default budget, which is
`mp.autoSafe.maxHeartbeats`, not Lean's `maxHeartbeats`. -/
def budgetHint (f : Name) (left : String) : String :=
  if (left.splitOn "maximum number of heartbeats").length > 1 then
    s!"\nhint: the attempt ran out of its budget `mp.autoSafe.maxHeartbeats` (in thousands of \
      heartbeats; Lean's `maxHeartbeats` does not apply to it). Raise it for this function with \
      `set_option mp.autoSafe.maxHeartbeats 2000000 in mp def {f} …`, or move a loop or a branch \
      into an `mp def` of its own: the attempt's cost grows with the variables in scope and the \
      reads of them"
  else ""

/-- Reduce the projections of constructor applications in a goal shown in a message, so that
`(a, b, ()).snd.fst` becomes `b`. -/
def reduceCtorProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const f _ := e.getAppFn | return .continue
    let some pi ← getProjectionFnInfo? f | return .continue
    let args := e.getAppArgs
    if pi.fromClass || args.size ≤ pi.numParams then return .continue
    let s := args[pi.numParams]!
    let .const c _ := s.getAppFn | return .continue
    let some (.ctorInfo ci) := (← getEnv).find? c | return .continue
    let fs := s.getAppArgs
    unless fs.size == ci.numParams + ci.numFields && pi.i < ci.numFields do return .continue
    return .visit (mkAppN fs[ci.numParams + pi.i]! (args.extract (pi.numParams + 1) args.size)))

/-- A goal left by an automatic attempt, for its message. It shows the variables and at most six
hypotheses that mention a variable of the target, with readable names whose macro scopes are
erased and whose clashes are numbered, followed by the target trimmed to four lines. -/
def goalSummary (g : MVarId) : MetaM String := g.withContext do
  let decl ← g.getDecl
  let tgt ← reduceCtorProjs (← instantiateMVars decl.type)
  let mut lctx := decl.lctx
  let mut used : NameSet := {}
  for d in decl.lctx do
    if d.isImplementationDetail then continue
    let base := d.userName.eraseMacroScopes
    let mut n := base
    let mut i := 1
    while used.contains n do
      n := base.appendIndexAfter i
      i := i + 1
    used := used.insert n
    lctx := lctx.setUserName d.fvarId n
  withLCtx lctx (← getLocalInstances) do
    let inTgt := (collectFVars {} tgt).fvarSet
    let clip (l : String) := if l.length > 160 then (l.take 157).toString ++ "…" else l
    let mut vars : Array String := #[]
    let mut hyps : Array String := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← reduceCtorProjs (← instantiateMVars d.type)
      if ← isProp ty then
        let fv := (collectFVars {} ty).fvarSet
        if hyps.size < 6 && fv.toList.any inTgt.contains then
          hyps := hyps.push (clip s!"{d.userName} : {← ppExpr ty}")
      else if inTgt.contains d.fvarId then
        vars := vars.push (clip s!"{d.userName} : {← ppExpr ty}")
    let t := toString (Std.Format.nest 4 (f!"⊢ " ++ (← ppExpr tgt)))
    let ls := t.splitOn "\n"
    let ls := if ls.length > 4 then ls.take 4 ++ ["  …"] else ls
    return "\n".intercalate ((vars ++ hyps).toList ++ ls.map clip)

/-- Try to prove `goal` with a tactic block, returning the proof, or else a summary of the first
goal it leaves or the error it raises. A runtime exception such as the recursion limit or the
heartbeat budget is a failure too, and the goal is then left to `mp prove`. Every automatic
attempt uses it: `mp def`'s obligations and contract, the analyser's side goals, generic
contracts and invariants. -/
def tryProveE (goal : Expr) (tac : Syntax) : Elab.TermElabM (Except String Expr) := do
  let s ← saveState
  let attempt : Elab.TermElabM (Except String Expr) := do
    let mv ← mkFreshExprMVar goal
    let remaining ← Elab.Term.withoutErrToSorry <|
      Elab.Tactic.run mv.mvarId! (Elab.Tactic.evalTactic tac)
    let prf ← instantiateMVars mv
    -- The first goal that is a proposition, skipping for example an invariant left to choose.
    let props ← remaining.filterM fun g => g.withContext do Meta.isProp (← g.getType)
    if let some g := props.head? <|> remaining.head? then
      let msg ← goalSummary g
      s.restore
      return .error msg
    if prf.hasMVar || prf.hasSorry then
      s.restore
      return .error "(the proof is incomplete)"
    return .ok prf
  tryCatchRuntimeEx attempt fun e => do
    let msg ← (← addMessageContext e.toMessageData).toString
    s.restore
    let ls := msg.splitOn "\n"
    return .error ("\n".intercalate (ls.take 6))

/-- `tryProveE`, returning the proof only. -/
def tryProve (goal : Expr) (tac : Syntax) : Elab.TermElabM (Option Expr) := do
  return match ← tryProveE goal tac with
    | .ok p => some p
    | .error _ => none

end Millipede.Meta
