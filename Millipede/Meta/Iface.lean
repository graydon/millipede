import Lean
import Millipede.Meta.Elab
import Millipede.Meta.Contracts

/-!
# Interfaces as Lean structures

`mp interface I (params) where items` declares the structure `I`, which is an interface. An item
is either a field `x : T` or an operation. A field is an abstract type `S : Type`, which also gets
the field `[S_data : Data S]`, or a part of the model such as `Inv : S → Prop` or `cap : Nat`. An
operation is written with the header of an `mp def`, as in the following item.

    op alloc! (s : &mut S) (v : V) requires Inv s ∧ used s < cap ensures Inv s' ∧ … : K

An operation stands for the fields that an implementation gives for it. They are its Core
function `alloc!F`, which is a `FnRef ps os r`, or a `Fn ps r` for an operation without
`requires` or references, its normal form `alloc!`, the link `alloc!_run` between the two,
`alloc!_req`, which says that the stated `requires` implies the implementation's, its safety
`alloc!_safe`, its purity `alloc!_pure`, and its contract `alloc!_spec` when it has an `ensures`
clause. As in `mp def`, `result` and `s'` name the result and the final value of `&mut s`.

For each operation the command also adds the declarations that `mp def` generates for a function,
over the structure's parameters and an implementation `A : I params`, and it registers `I.op` as
a callee. In an `mp def` under `variable (A : I params)`, `A.op args` is then a Core call of the
body of `A.opF`, and the client's Core term, normal form, obligations and contract are Lean terms
over `A`.

`mp implementation name : I args where items` defines the reducible implementation
`name : I args`. An item `op x := f a…` names an application of an `mp def` for the operation `x`.
It stands for the six fields `xF`, `x`, `x_run`, `x_req`, `x_safe` and `x_pure`, taken from the
declarations generated for `f`, with `x_req` proved by `simp_all` unless it is given. When the
operation has a contract it also stands for `x_spec`, which is `f.spec` unless given. Any other
item `field := term` is given as it is.

The design is described in doc/design/modules.md.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta

/-- An item of `mp interface` that is a field `x : T`. -/
syntax mpIfaceField := ident " : " term
/-- An item of `mp interface` that is an operation, written with the header of an `mp def`. -/
syntax mpIfaceOp := &"op " ident (ppSpace mpBinder)* (&" requires " term)? (&" ensures " term)?
  " : " term
/-- An item of `mp interface`. -/
syntax mpIfaceItem := mpIfaceOp <|> mpIfaceField

/-- `mp interface I (params) where items` declares an interface, as the module doc describes. -/
syntax (name := mpInterface) (docComment)? mpKw &"interface " ident (ppSpace bracketedBinder)*
  " where" manyIndent(ppLine mpIfaceItem) : command

/-- An item of `mp implementation` that gives an operation by an application of an `mp def`. -/
syntax mpImplOp := &"op " ident " := " term
/-- An item of `mp implementation` that gives a field, with binders when it is a function, as in
`Owns b x := …`. -/
syntax mpImplField := ident (ppSpace binderIdent)* " := " term
/-- An item of `mp implementation`. -/
syntax mpImplItem := mpImplOp <|> mpImplField

/-- `mp implementation name : I args where items` defines an implementation, as the module doc
describes. -/
syntax (name := mpImplementation) (docComment)? mpKw &"implementation " ident " : " term
  " where" manyIndent(ppLine mpImplItem) : command

/-- A parameter's mode and type, from `&mut T`, `&T` or `T`. -/
def ifaceMode (t : Syntax) : PMode × Term :=
  if t.getKind == ``mpRefMut then (.mut, ⟨t[1]⟩)
  else if t.getKind == ``mpRefShr then (.shr, ⟨t[1]⟩)
  else (.own, ⟨t⟩)

/-- The `Ty` term of a surface type. `Result`, `Arr`, `Slots`, products and the word types are
built as `mp def` builds them, and any other type `T` is `Ty.mk T`. -/
partial def tyStx (t : Term) : CommandElabM Term := do
  match t with
  | `(($u)) => tyStx u
  | `(Result $e $a) => `(Millipede.Ty.result $(← tyStx e) $(← tyStx a))
  | `(Arr $e $n) => `(Millipede.Ty.arr $(← tyStx e) $n)
  | `(Slots $e $n) => `(Millipede.Ty.slots $(← tyStx e) $n)
  | `($a × $b) => `(Millipede.Ty.pair $(← tyStx a) $(← tyStx b))
  | `(UInt64) => `(Millipede.Ty.u64)
  | `(Bool) => `(Millipede.Ty.bool)
  | `(Unit) => `(Millipede.Ty.unit)
  | _ => `(Millipede.Ty.mk $t)

/-- The carrier of a surface type, so that `Result E A` is `Except E A`. -/
partial def carStx (t : Term) : CommandElabM Term := do
  match t with
  | `(($u)) => carStx u
  | `(Result $e $a) => `(Except $(← carStx e) $(← carStx a))
  | `($a × $b) => `($(← carStx a) × $(← carStx b))
  | _ => pure t

/-- An operation of an interface, read off its syntax. -/
structure IfaceOp where
  stx : Syntax
  name : Name
  params : Array (Ident × PMode × Term)
  req? : Option Term
  ens? : Option Term
  ret : Term
  isRef : Bool

/-- The operation of an `mpIfaceOp` item. -/
def IfaceOp.ofStx (it : Syntax) : IfaceOp :=
  let params := it[2].getArgs.flatMap fun b =>
    let (m, t) := ifaceMode b[3]
    b[1].getArgs.map fun x => (⟨x⟩, m, t)
  let req? := if it[3].isNone then none else some ⟨it[3][1]⟩
  let ens? := if it[4].isNone then none else some ⟨it[4][1]⟩
  { stx := it, name := it[1].getId, params, req?, ens?, ret := ⟨it[6]⟩,
    isRef := req?.isSome || params.any (·.2.1 != .own) }

open Std.WP in
/-- `⦃P⦄ prog ⦃Q⦄`, which elaborates without `open Std.WP` at the use. -/
def tripleStx (P prog Q : Term) : CommandElabM Term := `(open Std.WP in ⦃$P⦄ $prog ⦃$Q⦄)

/-- The structure fields of an operation. The generated binders `env` and `r` are hygienic, so an
operation parameter of that name is not captured, and `result` and `s'` are bound for
`ensures`. -/
def IfaceOp.fields (op : IfaceOp) : CommandElabM (Array Syntax) := withRef op.stx do
  let fid (s : String) : Ident := mkIdentFrom op.stx[1] (Name.mkSimple (op.name.toString ++ s))
  let (xF, x) := (fid "F", fid "")
  let ps := op.params.toList
  let ctx := ps.reverse
  let psT ← ctx.toArray.mapM (tyStx ·.2.2)
  let osT ← (ctx.filter (·.2.1 == .mut)).toArray.mapM (tyStx ·.2.2)
  let rT ← tyStx op.ret
  let all (body : Term) : CommandElabM Term :=
    ps.foldrM (fun (n, _, t) acc => do `(∀ ($n : $(← carStx t)), $acc)) body
  let call : Term := Syntax.mkApp x (op.params.map (·.1))
  let env ← ctx.foldrM (fun (n, _, _) acc => `(Millipede.Env.cons $n $acc)) (← `(Millipede.Env.nil))
  let tupC ← (← (ctx.filter (·.2.1 == .mut)).mapM (carStx ·.2.2)).foldrM
    (fun c acc => `($c × $acc)) (← `(Unit))
  let resC ← if op.isRef then `($(← carStx op.ret) × $tupC) else carStx op.ret
  let req ← op.req?.getDM `(True)
  let (fnTy, body, reqFn, safe) ← if op.isRef then
      pure (← `(Millipede.FnRef [$psT,*] [$osT,*] $rT), ← `(Millipede.FnRef.body $xF),
        ← `(Millipede.FnRef.requires $xF), ← `(Millipede.FnRef.Safe $xF))
    else pure (← `(Millipede.Fn [$psT,*] $rT), ← `(Millipede.Fn.body $xF),
        ← `(Millipede.Fn.requires $xF), ← `(Millipede.Fn.Safe $xF))
  -- The `requires` over the environment, whose entries are the parameters, last one first.
  let (reqEnv, _) ← ctx.foldlM (fun (acc, mem) (n, _, _) => do
      pure ((← `(let $n := Millipede.Env.get env $mem; $acc)), ← `(Millipede.Mem.there $mem)))
    (req, ← `(Millipede.Mem.here))
  let mut out : Array Syntax := #[
    ← `(Lean.Parser.Command.structSimpleBinder| $xF:ident : $fnTy),
    ← `(Lean.Parser.Command.structSimpleBinder| $x:ident : $(← all (← `(Id $resC)))),
    ← `(Lean.Parser.Command.structSimpleBinder| $(fid "_run"):ident :
      $(← all (← `(Millipede.Exp.run $body $env = $call)))),
    ← `(Lean.Parser.Command.structSimpleBinder| $(fid "_req"):ident :
      ∀ env, $reqEnv → $reqFn env),
    ← `(Lean.Parser.Command.structSimpleBinder| $(fid "_safe"):ident : $safe),
    ← `(Lean.Parser.Command.structSimpleBinder| $(fid "_pure"):ident :
      Millipede.Exp.isPure $body = true)]
  if let some ens := op.ens? then
    -- For a function with references, `r = (result, (pₖ', … (p₁', ())))`.
    let res ← if op.isRef then `(r.1) else `(r)
    let (post, _) ← (ctx.filter (·.2.1 == .mut)).foldlM (fun (acc, path) (n, _, _) => do
        let n' := mkIdentFrom n (n.getId.appendAfter "'")
        pure ((← `(let $n' := ($path).1; $acc)), ← `(($path).2)))
      (ens, ← `(r.2))
    let post ← `(fun (r : $resC) => let $(mkIdentFrom ens `result) := $res; $post)
    out := out.push (← `(Lean.Parser.Command.structSimpleBinder| $(fid "_spec"):ident :
      $(← all (← tripleStx req call post))))
  return out

/-- The per-operation declarations of `mp def`, over the interface's parameters `ps` and an
implementation `A`, and the registry entry of `I.op`. -/
def IfaceOp.declare (I : Name) (op : IfaceOp) : TermElabM Unit := do
  let env ← getEnv
  let some ci := env.find? I | throwError "no structure {I}"
  let x := op.name
  let opN := I ++ x
  let fld (s : String) : Name := I ++ Name.mkSimple (x.toString ++ s)
  forallTelescope ci.type fun ps _ => do
  withLocalDeclD `A (mkAppN (mkConst I) ps) fun A => do
  -- Every declaration is over the parameters and `A`, since `addThm` abstracts `genVarsRef`.
  let xs := ps.push A
  let gOld ← genVarsRef.get
  genVarsRef.set xs
  try
    let proj (f : Name) : Expr := mkApp (mkAppN (mkConst f) ps) A
    let fnE := proj (fld "F")
    let body ← mkAppM (if op.isRef then ``FnRef.body else ``Fn.body) #[fnE]
    let defn (n : Name) (v : Expr) (doc : String) : TermElabM Unit := do
      let v ← instantiateMVars (← mkLambdaFVars xs v)
      let t ← instantiateMVars (← inferType v)
      let d : DefinitionVal :=
        { name := n, levelParams := [], type := t, value := v, hints := .abbrev, safety := .safe }
      addDecl (.defnDecl d)
      try compileDecl (.defnDecl d) (logErrors := false) catch _ => pure ()
      setReducibilityStatus n .reducible
      enableRealizationsForConst n
      addDocStringCore n doc
    let thm (n : Name) (t v : Expr) (doc : String) : TermElabM Unit := do
      addThm n t v; addDocStringCore n doc
    defn (opN ++ `exp) body s!"The Core term of the operation `{x}` of an implementation."
    let expC := mkAppN (mkConst (opN ++ `exp)) xs
    let fold (e : Expr) : Expr := e.replace fun s => if s == body then some expC else none
    let runField := proj (fld "_run")
    thm (opN ++ `exp_run) (fold (← inferType runField)) runField
      s!"The Core term of `{x}` runs as its normal form."
    let reqField := proj (fld "_req")
    if op.isRef then
      let reqV ← forallBoundedTelescope (← inferType reqField) (some 1) fun es imp => do
        mkLambdaFVars es (← zetaReduce imp.bindingDomain!)
      defn (opN ++ `req) reqV s!"The `requires` of the operation `{x}`."
    let pureField := proj (fld "_pure")
    thm (opN ++ `isPure) (fold (← inferType pureField)) pureField
      s!"The operation `{x}` calls no extern."
    -- `exp_denoteM`, `exp_denote` and `Safe'`, as `mp def` adds them.
    forallTelescope (← inferType runField) fun vs _ =>
      addPureDenotes opN x.toString expC (mkAppN (mkConst (opN ++ `isPure)) xs)
        (mkAppN (mkAppN (mkConst (opN ++ `exp_run)) xs) vs) vs
    addSafeSimp opN expC (if op.isRef then some (mkAppN (mkConst (opN ++ `req)) xs) else none)
      fun ω env w h => mkAppN (proj (fld "_safe")) #[ω, env, w, mkApp2 reqField env h]
    addDocStringCore (opN ++ `Safe') s!"The obligations of `{x}` hold under its `requires`."
    -- The registry entry, with the parameters from the Core context, last one first.
    let some ts ← tyListElems (← inferType body).appFn!.appArg!
      | throwError "internal: the context of `{x}`"
    let mut params : Array (Name × STy × PMode) := #[]
    for (t, (n, m, _)) in ts.reverse.zip op.params.toList do
      let some st ← tyExprToSTy t | throwError "parameter `{n}` of `{x}`: no surface type"
      params := params.push (n.getId, st, m)
    let bt ← inferType body
    let r := if op.isRef then bt.appArg!.appFn!.appArg! else bt.appArg!
    let some ret ← tyExprToSTy r | throwError "the result of `{x}`: no surface type"
    let info : FnInfo :=
      { declName := opN, params := params, ret := ret, isPure := true, isRef := op.isRef,
        hasSafe := true, hasNf := true, nGen := xs.size, genArgs := xs }
    -- `spec` and `post`, as for `mp def … ensures`.
    if op.ens?.isSome then
      let specField := proj (fld "_spec")
      addContractDecls info (← zetaReduce (← instantiateMVars (← inferType specField))) specField
    modifyEnv (registry.addEntry · (.fn (info.abstractGen xs)))
  finally genVarsRef.set gOld

@[command_elab mpInterface] def elabMpInterface : CommandElab := fun stx => do
  let I : Ident := ⟨stx[3]⟩
  let declName := (← getCurrNamespace) ++ I.getId
  let binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := stx[4].getArgs.map (⟨·⟩)
  let mut fields : Array Syntax := #[]
  let mut ops : Array IfaceOp := #[]
  for it0 in stx[6].getArgs do
    let it := it0[0]
    if it.getKind == ``mpIfaceOp then
      let op := IfaceOp.ofStx it
      ops := ops.push op
      fields := fields ++ (← op.fields)
    else
      let (x, t) : Ident × Term := (⟨it[0]⟩, ⟨it[2]⟩)
      fields := fields.push (← `(Lean.Parser.Command.structSimpleBinder| $x:ident : $t))
      if t.raw.isOfKind ``Lean.Parser.Term.type then
        let xd := mkIdentFrom x (x.getId.appendAfter "_data")
        fields := fields.push (← `(Lean.Parser.Command.structInstBinder|
          [$xd:ident : Millipede.Data $x]))
  let doc? : Option (TSyntax ``Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let fs : TSyntax ``Lean.Parser.Command.structFields :=
    ⟨mkNode ``Lean.Parser.Command.structFields #[mkNullNode fields]⟩
  let cmd ← `(set_option linter.unusedVariables false in
    $[$doc?:docComment]? structure $I $binders* where $fs:structFields)
  let errs0 := (← get).messages.toList.countP (·.severity == .error)
  withRef stx do elabCommand cmd
  -- An error in an item has been reported at its source, so nothing more is declared.
  if (← get).messages.toList.countP (·.severity == .error) > errs0 then return
  -- The abstract types' `Data` instances, and any other field that is a class.
  let env ← getEnv
  for f in getStructureFields env declName do
    let some p := getProjFnForField? env declName f | continue
    let some ci := env.find? p | continue
    let isCls ← liftTermElabM <| forallTelescope ci.type fun _ b => return (← isClass? b).isSome
    if isCls then
      elabCommand (← `(attribute [instance] $(mkCIdent p)))
  liftTermElabM do
    for op in ops do
      IfaceOp.declare declName op
  for op in ops do
    if op.ens?.isSome then
      elabCommand (← `(attribute [spec] $(mkCIdent (declName ++ op.name ++ `spec))))

/-- The fields of an operation given by an `mp def` application `f a…`. -/
def implOpFields (x : Name) (isRef : Bool) (f : Term) :
    CommandElabM (Array (Name × Term)) := withRef f do
  let (hd, args) ← match f with
    | `($h:ident $args*) => pure (h, args)
    | `($h:ident) => pure (h, #[])
    | _ => throwErrorAt f "an operation is given by an `mp def` applied to its variables: `f a b`"
  let c (s : Name) : Term := Syntax.mkApp (mkIdentFrom hd (hd.getId ++ s)) args
  let (fnRef, req) := (mkIdentFrom hd (hd.getId ++ `fnRef), mkIdentFrom hd (hd.getId ++ `req))
  let fld (s : String) := Name.mkSimple (x.toString ++ s)
  return #[(fld "F", c (if isRef then `fnRef else `fn)), (fld "", c .anonymous),
    (fld "_run", c `exp_run), (fld "_safe", c `Safe), (fld "_pure", ← `(rfl)),
    (fld "_req", ← `(fun _ h => by
      first
      | exact h
      | simp only [$fnRef:ident, $req:ident] at *
        first | exact h | exact h.2 | exact h.1 | simp_all | grind
      | simp_all))]

@[command_elab mpImplementation] def elabMpImplementation : CommandElab := fun stx => do
  let n := stx[3]
  let ty := stx[5]
  let I ← runTermElabM fun _ => do
    let t ← elabType ty
    let some I := (← whnfR t).getAppFn.constName? | throwErrorAt ty "not an interface"
    return I
  let env ← getEnv
  let mut fields : Array (TSyntax ``Lean.Parser.Term.structInstField) := #[]
  let given := stx[7].getArgs.filterMap fun it0 =>
    if it0[0].getKind == ``mpImplField then some it0[0][0].getId else none
  for it0 in stx[7].getArgs do
    let it := it0[0]
    if it.getKind == ``mpImplOp then
      let x := it[1].getId
      let some ci := env.find? (I ++ Name.mkSimple (x.toString ++ "F"))
        | throwErrorAt it[1] "`{I}` has no operation `{x}`"
      let isRef := ci.type.getForallBody.isAppOf ``FnRef
      for (f, v) in ← implOpFields x isRef ⟨it[3]⟩ do
        if given.contains f then continue
        fields := fields.push (← withRef it[3] `(Lean.Parser.Term.structInstField|
          $(mkIdentFrom it[1] f):ident := $v))
      -- The operation's contract, when not given, is the `mp def`'s own `f.spec a…`.
      let specF := Name.mkSimple (x.toString ++ "_spec")
      if env.contains (I ++ specF) && !given.contains specF then
        if let some (hd, args) := match (⟨it[3]⟩ : Term) with
            | `($h:ident $args*) => some (h, args) | `($h:ident) => some (h, #[]) | _ => none then
          let fn? ← try some <$> liftTermElabM (realizeGlobalConstNoOverload hd) catch _ => pure none
          if let some fn := fn? then
            if env.contains (fn ++ `spec) then
              let v := Syntax.mkApp (mkCIdentFrom hd (fn ++ `spec)) args
              fields := fields.push (← withRef it[3] `(Lean.Parser.Term.structInstField|
                $(mkIdentFrom it[1] specF):ident := $v))
    else
      let x : Ident := ⟨it[0]⟩
      let bs : Array (TSyntax ``Lean.Parser.Term.funBinder) := it[1].getArgs.map (⟨·[0]⟩)
      let v : Term := ⟨it[3]⟩
      let v ← if bs.isEmpty then pure v else `(fun $bs* => $v)
      fields := fields.push (← `(Lean.Parser.Term.structInstField| $x:ident := $v))
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let val ← `(Lean.Parser.Term.structInst| { $fields,* })
  let cmd ← `($[$doc?:docComment]? @[reducible] def $(⟨n⟩):ident : $(⟨ty⟩) := $(⟨val.raw⟩))
  withRef stx do elabCommand cmd

end Millipede.Meta
