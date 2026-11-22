import Lean
import Millipede.Meta.Basic
import Millipede.Lib.Cap
import Millipede.Core.Effects

/-!
# Capability classes and the authority of a function

`mp capability Fs for "write", "read"` declares a capability class. It defines the token type
`Fs := Cap "<full name of Fs>"` and the list `Fs.syms` of the extern symbols the class governs,
and records the class.

A function holds a class when the type of one of its parameters contains a token of the class,
directly, behind a reference, or inside a struct, enum, pair, result, array or `Slots`. After
`mp def f`, the elaborator collects the symbols of every recorded class that `f` does not hold
and proves `f.noCalls : f.exp.NoCalls S` by kernel evaluation of `Exp.syms`, so that no run of `f`
calls those symbols. When the body reaches one of them, the definition is rejected with a
message that names the symbol and its class. `mp program` does the same for the classes its
`init` does not take, through `Program.NoCalls`.

Tokens are minted only by the `init` wrapper that `mp program` generates. While it is being
elaborated, `grantRef` holds the classes it grants, and `Cap.mint` is accepted only for them.
-/

namespace Millipede.Meta

open Lean Elab Command Meta

/-- A recorded capability class: the declaration that names its token type, its class string
and its extern symbols. -/
structure CapInfo where
  declName : Name
  cls : String
  syms : List String
deriving Inhabited, Repr

/-- The recorded capability classes, persistent across files. -/
initialize capRegistry : SimplePersistentEnvExtension CapInfo (Array CapInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a e => a.push e
    addImportedFn := fun as => as.foldl (fun acc a => acc ++ a) #[]
  }

/-- The recorded capability classes. -/
def capClasses (env : Environment) : Array CapInfo := capRegistry.getState env

/-- The classes that the `init` wrapper of `mp program` may mint while it is elaborated, empty
everywhere else. -/
initialize grantRef : IO.Ref (List String) ← IO.mkRef []

/-- The class of a token type `Cap c` with a literal `c`. -/
def capClassOf? (t : STy) : MetaM (Option String) := do
  let .adt n _ cargs _ := t | return none
  unless n == ``Millipede.Lib.Cap && cargs.size == 1 do return none
  match ← whnf cargs[0]! with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- The classes of the tokens that a value of type `t` contains, looking through structs, enums,
pairs, results, arrays and `Slots`, down to `fuel` levels. -/
partial def tokenClasses (t : STy) (fuel : Nat := 16) : MetaM (List String) := do
  if fuel == 0 then return []
  if let some c ← capClassOf? t then return [c]
  match t with
  | .result e a => return (← tokenClasses e (fuel - 1)) ++ (← tokenClasses a (fuel - 1))
  | .pair a b => return (← tokenClasses a (fuel - 1)) ++ (← tokenClasses b (fuel - 1))
  | .arr e _ | .slots e _ | .slice e _ => tokenClasses e (fuel - 1)
  | .tup ts => return (← ts.mapM (tokenClasses · (fuel - 1))).flatten
  | .adt n _ _ iargs =>
    let some i := lookupAdt (← getEnv) n | return []
    let tys : Array STy := match i.kind with
      | .struct fs _ => fs.map (·.ty)
      | .enum vs _ => vs.map (·.payload)
    let tys := tys.map (·.mapExpr (·.instantiateRev iargs))
    return (← tys.toList.mapM (tokenClasses · (fuel - 1))).flatten
  | _ => return []

/-- The symbols of the recorded classes outside `held`, as the list term
`C₁.syms ++ … ++ Cₙ.syms` and its value, or `none` when there are none. -/
def forbiddenSyms (held : List String) : MetaM (Option (Expr × List String)) := do
  let out := (capClasses (← getEnv)).filter fun (c : CapInfo) => !held.contains c.cls
  if out.isEmpty then return none
  let terms := out.map fun (c : CapInfo) => mkConst (c.declName ++ `syms)
  let mut e := terms[0]!
  for t in terms[1:] do e ← mkAppM ``HAppend.hAppend #[e, t]
  return some (e, (out.map (·.syms)).toList.flatten)

/-- The extern symbols of a closed Core term, by reduction, in order without repeats. -/
def expSyms (Γ t e : Expr) : MetaM (List String) := do
  let v ← withTransparency .all <| reduce (mkApp3 (mkConst ``Exp.syms) Γ t e)
  let rec go (v : Expr) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if v.isAppOfArity ``List.cons 3 then
        match v.appFn!.appArg! with
        | .lit (.strVal s) => s :: go v.appArg! fuel
        | _ => go v.appArg! fuel
      else []
  return (go v 100000).eraseDups

/-- The class that governs the symbol `s`, among those outside `held`. -/
def classOfSym (held : List String) (s : String) : MetaM (Option CapInfo) := do
  return (capClasses (← getEnv)).find? fun c => !held.contains c.cls && c.syms.contains s

/-- The statement `e.NoCalls S` and its proof by `Exp.noCalls_of_syms` and kernel evaluation, for
the symbols `S` of the classes outside `held`. It is `none` when every recorded class is held,
and it throws, naming the first symbol and its class, when `e` reaches one of them. `what` names
the function or program in the message. -/
def noCallsProof (what : MessageData) (ref : Syntax) (Γ t e : Expr) (held : List String) :
    MetaM (Option (Expr × Expr)) := do
  let some (S, Sv) ← forbiddenSyms held | return none
  let notIn ← withLocalDeclD `s (mkConst ``String) fun s => do
    mkLambdaFVars #[s] (mkApp (mkConst ``not) (← mkAppM ``List.contains #[S, s]))
  let b := mkApp3 (mkConst ``List.all [0]) (mkConst ``String) (mkApp3 (mkConst ``Exp.syms) Γ t e)
    notIn
  let v ← withTransparency .all <| whnf b
  unless v.isConstOf ``Bool.true do
    let syms ← expSyms Γ t e
    let bad := syms.filter Sv.contains
    let s := bad.headD "?"
    let some c ← classOfSym held s | throwErrorAt ref "{what} calls `{s}` without its capability"
    throwErrorAt ref "{what} calls the extern symbol \"{s}\", which needs the capability \
      `{c.declName}`, but holds no `{c.declName}` token: take one as a parameter, such as \
      `(c : &{c.declName})`"
  let prop ← mkEq b (mkConst ``Bool.true)
  let h := mkApp3 (mkConst ``of_decide_eq_true) prop
    (mkApp2 (mkConst ``instDecidableEqBool) b (mkConst ``Bool.true))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  return some (mkApp4 (mkConst ``Exp.NoCalls) Γ t e S,
    mkApp5 (mkConst ``Exp.noCalls_of_syms) Γ t e S h)

/-- `mp capability C for "sym", …` declares the capability class `C`, whose tokens have type
`C := Cap "<full name of C>"` and whose extern symbols are `C.syms`. A function may call one of
these symbols only while it holds a `C` token. -/
syntax (name := mpCapability) (docComment)? mpKw &"capability " ident &" for " str,+ : command

@[command_elab mpCapability] def elabMpCapability : CommandElab := fun stx => liftTermElabM do
  let nameStx := stx[3]
  let declName := (← getCurrNamespace) ++ nameStx.getId
  if (← getEnv).contains declName then throwErrorAt nameStx "`{declName}` is already declared"
  let syms ← stx[5].getSepArgs.toList.mapM fun s => do
    let some v := s.isStrLit? | throwErrorAt s "expected an extern symbol as a string"
    pure v
  let cls := declName.toString
  for c in capClasses (← getEnv) do
    for s in syms do
      if c.syms.contains s then
        throwErrorAt nameStx "the symbol \"{s}\" already belongs to the capability `{c.declName}`"
  let tyVal := mkApp (mkConst ``Millipede.Lib.Cap) (toExpr cls)
  addDecl (.defnDecl (mkDefinitionValEx declName [] (mkSort Level.one) tyVal .abbrev .safe []))
  setReducibleAttribute declName
  addDecl (.defnDecl (mkDefinitionValEx (declName ++ `syms) []
    (mkApp (mkConst ``List [0]) (mkConst ``String)) (toExpr syms) .abbrev .safe []))
  Term.addTermInfo' nameStx (mkConst declName) (isBinder := true)
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  if doc?.isSome then addDocString' declName Syntax.missing doc?
  else addDocStringCore declName s!"The token type of the capability class `{nameStx.getId}`."
  addDocStringCore (declName ++ `syms) s!"The extern symbols of the capability class \
    `{nameStx.getId}`."
  modifyEnv (capRegistry.addEntry · { declName, cls, syms })

end Millipede.Meta
