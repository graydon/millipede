import Lean
import Millipede.Meta.Basic
import Millipede.Meta.GenericLaws

/-!
# `deriving Data`

`structure S … deriving Data` and `inductive E … deriving Data` generate the object-level view of
a Lean type, and the kernel checks every declaration generated.

A structure may have fields of any type with a `Data` instance, and a field whose type is a
`Prop` is a ghost proof field. The handler generates the following declarations for it.
- `S.instData : Data S`, which lays the fields out as C does, in declaration order. The type is
  linear when a field is.
- `S.f.lens : Lens ⟨S⟩ ⟨T⟩` for each field `f : T`, with its name, its field number, which is its
  position, its projection, its update and the certificate of its law, together with the `rfl`
  simp lemmas `S.f.lens_get` and `S.f.lens_set`.
- `S.ctor : Ctor [T₁, …] ⟨S⟩` of kind `struct`, which takes its arguments in field order, with
  `S.ctor_build`. It is not generated when a field is a proof, since building such a struct needs
  the proof.

An inductive type needs at least two constructors, each with at most one field, its payload. A
constructor without a field has the payload `Unit`. The handler generates the following
declarations for it.
- `E.instData : Data E`, whose tag is the constructor index, laid out as the C type
  `struct { tag; union { payloads } }`. The type is linear when a payload is.
- `E.c.ctor : Ctor [P] ⟨E⟩` of kind `variant i` for each constructor `c`. A constructor without a
  field takes the unit literal.
- The exhaustive chain of splits. For two constructors it is `E.split0 : Split ⟨E⟩ ⟨P₀⟩ ⟨P₁⟩`.
  For `k ≥ 3` constructors it is `E.split₀ … E.split_{k-1}`, where `E.splitᵢ : Split ⟨E⟩ ⟨Pᵢ⟩ ⟨E⟩`
  for `i < k - 1` tests constructor `i` and otherwise hands back the value itself, and the last
  split, `Split ⟨E⟩ ⟨P_{k-1}⟩ Unit`, tests the last constructor. Every split is lawful for every
  value, and `rfl` simp lemmas `E.splitᵢ.c` give each split on each constructor.
- `E.mpMatch s f₀ … f_{k-1}`, a `match` on `s` that applies `fᵢ` to the payload, and
  `E.mpMatch_eq`, which says that the `Sum.elim` chain over the splits equals it. `mp def` folds
  the meaning of a `match` into `E.mpMatch` and unfolds that, so the normal form of `f` is a Lean
  `match`.

A `match` with one arm per constructor is the chain of `Exp.case`s over the splits, so it is
exhaustive by construction. The rest of the last split is unreachable, and `mp def` runs the last
arm there on the payload's `default`, so the last payload needs an `Inhabited` instance.

Every lens, constructor and split carries a certificate of its law, proved by `certify` from the
generic lemmas of `Millipede/Core/Lawful.lean`. Where the proof does not go through, as for an
enum with more than `2^8` constructors, the certificate is `none`, and `compile` refuses a
program that uses the building block. The handler also records the type in the registry, so
that `mp def` can use its fields, literals, constructors and `match`.

A type with parameters, such as `structure Bump (T : Type) (n : Nat) … deriving Data`, gets every
declaration above once, abstracted over the parameters with `[Data T]` after each type
parameter, as in `Bump.instData : (T : Type) → [Data T] → (n : Nat) → Data (Bump T n)`. The
certificates are proved by the same terms, which evaluate nothing of the layout, and for such a
type a certificate that does not go through is an error. The registry entry records the
binders, the field types are stored with them abstracted, and `mp def` instantiates them at a
use.

The handler rejects with a message a type with indices or universe parameters, a constructor
with more than one field, whose fields belong in a structure, a recursive type, which has no
`Data` instance for its field, and an inductive with a single constructor that is not a
`structure`.
-/

namespace Millipede.Meta.Derive

open Lean Elab Command Term Meta

/-- Add a definition abstracted over `bs`, checked by the kernel, enable realizations for it and
compile it. With `inst` it is a global instance. -/
def addDefnOver (bs : Array Expr) (n : Name) (type value : Expr) (doc : String)
    (inst := false) : TermElabM Unit := do
  let type ← instantiateMVars (← mkForallFVars bs type)
  let value ← instantiateMVars (← mkLambdaFVars bs value)
  let decl := Declaration.defnDecl
    { name := n, levelParams := [], type := type, value := value,
      hints := if inst then .regular 0 else .abbrev, safety := .safe }
  addDecl decl
  if inst then setReducibilityStatus n .implicitReducible
  enableRealizationsForConst n
  try compileDecl decl (logErrors := false) catch _ => pure ()
  addDocStringCore n doc
  if inst then addInstance n .global (eval_prio default)

/-- Add an `rfl` theorem with the `simp` attribute. -/
def addRflSimp (n : Name) (stmt : Expr) : TermElabM Unit := do
  let prf ← forallTelescope stmt fun xs body => do
    let some (_, l, _) := body.eq? | throwError "internal: not an equation"
    mkLambdaFVars xs (← mkEqRefl l)
  addDecl (.thmDecl { name := n, levelParams := [], type := stmt, value := prf })
  addSimpTheorem simpExtension n (post := true) (inv := false) .global (eval_prio default)

/-- `Ctor.mk` applied to its first six fields, with no hand-back certificate in `Ctor.occs`,
since a derived constructor does not hand back a reference. -/
def ctorMk (args : Array Expr) : TermElabM Expr := do
  let f := mkAppN (mkConst ``Ctor.mk) args
  match ← whnf (← inferType f) with
  | .forallE _ d _ _ => return mkApp f (← mkAppOptM ``Option.none #[some (← whnf d).appArg!])
  | _ => throwError "deriving Data: unexpected type of Ctor.mk"

/-- The certificate of a building block's law, `Lens.law`, `Ctor.law` or `Split.law`. It is
`some ⟨proof⟩`, with the proof elaborated from `prf`, a term over the generic lemmas of
`Millipede/Core/Lawful.lean`, against `law`, or `none` when that does not go through. The memory
pipeline of `compile` then refuses programs that use the building block. -/
def certify (law : Expr) (prf : String) : TermElabM Expr := do
  let pl := mkApp (mkConst ``PLift [0]) law
  let noneE := mkApp (mkConst ``Option.none [0]) pl
  let s ← saveState
  let errsBefore := (← getThe Core.State).messages.toList.filter (·.severity == .error) |>.length
  try
    let stx ← match Parser.runParserCategory (← getEnv) `term prf with
      | .ok stx => pure stx
      | .error e => throwError "internal: certificate syntax: {e}"
    let p ← Term.withoutErrToSorry do
      let e ← Term.elabTermEnsuringType stx (some law)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let errsAfter := (← getThe Core.State).messages.toList.filter (·.severity == .error) |>.length
    if p.hasMVar || p.hasSyntheticSorry || errsAfter != errsBefore then
      s.restore
      return noneE
    unless ← isDefEq (← inferType p) law do
      s.restore
      return noneE
    return mkApp2 (mkConst ``Option.some [0]) pl (mkApp2 (mkConst ``PLift.up [0]) law p)
  catch _ =>
    s.restore
    return noneE

/-- `Mem tᵢ ts` for position `i` of the `Ty` list `ts`. -/
def memAt : List Expr → Nat → Expr
  | t :: rest, 0 => mkApp2 (mkConst ``Mem.here) t (listTy rest)
  | s :: rest, k + 1 =>
    match rest[k]? with
    | some t => mkApp4 (mkConst ``Mem.there) t s (listTy rest) (memAt rest k)
    | none => default
  | [], _ => default
where
  listTy (ts : List Expr) : Expr :=
    ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [1]) (mkConst ``Ty) t acc)
      (mkApp (mkConst ``List.nil [1]) (mkConst ``Ty))

/-- `env.get m` for position `i` of the `Ty` list `ts`. -/
def envGet (ts : List Expr) (env : Expr) (i : Nat) : Expr :=
  mkApp4 (mkConst ``Env.get) ts[i]! (memAt.listTy ts) env (memAt ts i)

/-- The short name of a constant, its last component, for messages and `Lens.name`. -/
def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The surface type of a field or payload type, or an error. -/
def fieldSTy (what : String) (t : Expr) : TermElabM STy := do
  match ← exprToSTy t with
  | some s => return s
  | none => throwError "deriving Data: {what} has type{indentExpr t}\nwhich has no `Data` \
      instance (recursive types are not supported; use indices into an arena)"


/-- The binders of a type's instance, which are its parameters with `[Data T]` after each type
parameter, marked `true`. A closed type has none. -/
partial def withInstBinders {α : Type} (ps : List Expr) (acc : Array Expr) (marks : Array Bool)
    (k : Array Expr → Array Bool → TermElabM α) : TermElabM α := do
  match ps with
  | [] => k acc marks
  | p :: rest =>
    let ty ← whnf (← inferType p)
    if ty.isType then
      withLocalDecl `inst .instImplicit (mkApp (mkConst ``Data) p) fun i =>
        withInstBinders rest (acc ++ #[p, i]) (marks ++ #[false, true]) k
    else withInstBinders rest (acc.push p) (marks.push false) k

/-- A certificate, or an error for a type with parameters, where the certificate should always
go through. -/
def certifyOr (closed : Bool) (law : Expr) (prf what : String) : TermElabM Expr := do
  let cert ← certify law prf
  if cert.isAppOf ``Option.none && !closed then
    throwError "deriving Data: the law of {what} was not proved generically"
  return cert

/-- `deriving Data` for a structure. -/
def deriveStruct (S : Name) (ind : InductiveVal) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let fields := getStructureFields env S
  let ctorVal := (getStructureCtor env S).name
  forallBoundedTelescope ind.type ind.numParams fun ps _ =>
  withInstBinders ps.toList #[] #[] fun bs marks => do
    let carrier := mkAppN (mkConst S) ps
    let infos ← fields.mapM fun f => do
      let some proj := getProjFnForField? env S f
        | throwError "deriving Data: no projection for field `{f}`"
      let pty ← instantiateForall (← inferType (mkConst proj)) ps
      forallTelescope pty fun xs body => do
        let isProp ← isProp body
        if !isProp && xs.any (fun x => body.containsFVar x.fvarId!) then
          throwError "deriving Data: the type of field `{f}` depends on another field"
        return (f, proj, isProp, body)
    -- Every data field has a `Data` instance, checked before the instance is generated.
    for (f, _, isProp, fty) in infos do
      unless isProp do discard <| fieldSTy s!"field `{f}`" fty
    -- The instance.
    let fieldStx ← infos.mapM fun (_, proj, isProp, _) =>
      if isProp then `(Millipede.Field.ghost _) else `(⟨$(mkCIdent proj)⟩)
    let instTy := mkApp (mkConst ``Data) carrier
    let instVal ← elabTermEnsuringType (← `(Millipede.Data.struct [$fieldStx,*])) instTy
    synthesizeSyntheticMVarsNoPostponing
    let instName := S ++ `instData
    addDefnOver bs instName instTy (← instantiateMVars instVal)
      "The `Data` instance (C layout of the fields), generated by `deriving Data`." (inst := true)
    let instE := mkAppN (mkConst instName) bs
    let sTy := mkApp2 (mkConst ``Ty.mk) carrier instE
    let lin ← withTransparency .all <| whnf (mkApp2 (mkConst ``Data.linear) carrier instE)
    let closed := bs.isEmpty
    let mut finfos : Array FieldInfo := #[]
    let mut idx := 0
    let anyProp := infos.any (·.2.2.1)
    for (f, proj, isProp, fty) in infos do
      if isProp || anyProp then
        -- Proof fields have no lens, and in a struct with proof fields no field has one, since
        -- an update could break the proof.
        idx := idx + 1
        continue
      let fs ← fieldSTy s!"field `{f}`" fty
      let lensName := S ++ f ++ `lens
      let lensTy := mkApp2 (mkConst ``Lens) sTy fs.toTy
      let projE := mkAppN (mkConst proj) ps
      -- The update `fun s v => S.mk s.f₁ … v … s.fₙ`.
      let setFn ← withLocalDeclD `s carrier fun s => withLocalDeclD `v fty fun v => do
        let args := infos.map fun (g, proj', _, _) =>
          if g == f then v else mkApp (mkAppN (mkConst proj') ps) s
        mkLambdaFVars #[s, v] (mkAppN (mkAppN (mkConst ctorVal) ps) args)
      let law := mkAppN (mkConst ``Flat.LensLaw) #[sTy, fs.toTy, toExpr idx, projE, setFn]
      let cert ← certifyOr closed law s!"Millipede.Flat.LensLaw.field _ rfl _ _ {idx} (by simp) rfl \
        (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ => by \
        simp [Millipede.Flat.Fields.SameExcept, Millipede.Flat.Fields.SameAll]) \
        rfl (fun _ => rfl) (fun _ _ => rfl)" s!"the lens of `{f}`"
      addDefnOver bs lensName lensTy (mkAppN (mkConst ``Lens.mk) #[sTy, fs.toTy,
        toExpr (shortName f), toExpr idx, projE, setFn, cert])
        s!"The lens of field `{f}` (generated by `deriving Data`)."
      -- The `rfl` simp lemmas.
      let getStmt ← withLocalDeclD `s carrier fun s => do
        mkForallFVars (bs.push s) (← mkEq
          (mkApp4 (mkConst ``Lens.get) sTy fs.toTy (mkAppN (mkConst lensName) bs) s)
          (mkApp projE s))
      addRflSimp (S ++ f ++ `lens_get) getStmt
      let setStmt ← withLocalDeclD `s carrier fun s => withLocalDeclD `v fty fun v => do
        mkForallFVars (bs ++ #[s, v]) (← mkEq
          (mkApp5 (mkConst ``Lens.set) sTy fs.toTy (mkAppN (mkConst lensName) bs) s v)
          (← whnfCore (mkApp2 setFn s v)))
      addRflSimp (S ++ f ++ `lens_set) setStmt
      finfos := finfos.push { name := f, ty := fs, idx := idx, lens := lensName }
      idx := idx + 1
    -- The constructor, only without proof fields, with its law by `CtorLaw.structPlan`.
    let mut ctorC : Option Name := none
    unless anyProp do
      let ts := finfos.toList.map (·.ty.toTy)
      let envTy := mkApp (mkConst ``Env) (memAt.listTy ts)
      let build ← withLocalDeclD `env envTy fun e => do
        mkLambdaFVars #[e] (mkAppN (mkAppN (mkConst ctorVal) ps)
          ((List.range ts.length).map (envGet ts e)).toArray)
      let cName := S ++ `ctor
      let law := mkAppN (mkConst ``Flat.CtorLaw) #[memAt.listTy ts, sTy,
        mkConst ``CtorKind.struct, build]
      let n := ts.length
      let pat := (List.range n).foldr (fun j acc => s!"(.cons a{j} {acc})") ".nil"
      let hs := ", ".intercalate ((List.range n).map (s!"h{·}") ++ ["_"])
      let body := ", ".intercalate ((List.range n).map (s!"h{·} _ (List.mem_singleton_self _)") ++
        ["trivial"])
      let cert ← certifyOr closed law s!"Millipede.Flat.CtorLaw.struct _ rfl _ \
        (Millipede.Flat.CtorLaw.structPlan _ rfl _ rfl) (by \
        intro env bs ha; match env, ha with | {pat}, ⟨{hs}⟩ => exact ⟨{body}⟩)"
        s!"the constructor of `{S}`"
      addDefnOver bs cName (mkApp2 (mkConst ``Ctor) (memAt.listTy ts) sTy) (← ctorMk
        #[memAt.listTy ts, sTy, toExpr (shortName S), mkConst ``CtorKind.struct, build, cert])
        s!"The constructor `{S}.mk` as a core `Ctor` (generated by `deriving Data`)."
      ctorC := some cName
    let stored := finfos.map fun fi => { fi with ty := fi.ty.mapExpr (·.abstract bs) }
    let info : AdtInfo :=
      { name := S, lin := !lin.isConstOf ``Bool.false, kind := .struct stored ctorC, params := marks }
    modifyEnv (registry.addEntry · (.adt info))

/-- `deriving Data` for an inductive type with at least two constructors. -/
def deriveEnum (E : Name) (ind : InductiveVal) : CommandElabM Unit := do
  let env ← getEnv
  let k := ind.ctors.length
  let splitsInfo : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) ×
      Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) × Array Ident × Array Term × Term ←
    liftTermElabM <| forallBoundedTelescope ind.type ind.numParams fun ps _ =>
  withInstBinders ps.toList #[] #[] fun bs marks => do
    let carrier := mkAppN (mkConst E) ps
    let closed := bs.isEmpty
    -- The constructors and their fields, at most one each, at the parameters.
    let ctors ← ind.ctors.toArray.mapM fun c => do
      let some (.ctorInfo cv) := env.find? c | throwError "no constructor {c}"
      unless cv.numFields ≤ 1 do
        throwError "deriving Data: constructor `{c}` has {cv.numFields} fields; an enum \
          constructor has at most one (wrap several fields in a structure)"
      let cty ← instantiateForall cv.type ps
      let fty? ← forallTelescope cty fun xs _ => do
        if h : 0 < xs.size then
          let t ← inferType xs[0]
          if t.hasLooseBVars || (← isProp t) then
            throwError "deriving Data: the field of `{c}` must be data, not a proof"
          return some t
        return none
      return (c, fty?)
    -- The payload types, checked before the instance is generated.
    let pays ← ctors.mapM fun (c, fty?) => do
      match fty? with
      | none => pure (STy.unit, Lean.mkConst ``Unit)
      | some t => do pure (← fieldSTy s!"the field of `{c}`" t, t)
    -- The instance.
    let variantStx ← ctors.mapM fun (c, fty?) =>
      match fty? with
      | none => `(⟨fun x => match x with | $(mkCIdent c) => some () | _ => none⟩)
      | some _ => `(⟨fun x => match x with | $(mkCIdent c) y => some y | _ => none⟩)
    let instTy := mkApp (mkConst ``Data) carrier
    let instVal ← elabTermEnsuringType
      (← `(Millipede.Data.sum [$variantStx,*] (fun x => by cases x <;> simp))) instTy
    synthesizeSyntheticMVarsNoPostponing
    let instName := E ++ `instData
    addDefnOver bs instName instTy (← instantiateMVars instVal)
      "The `Data` instance (tag and payload union), generated by `deriving Data`." (inst := true)
    let instE := mkAppN (mkConst instName) bs
    let sTy := mkApp2 (mkConst ``Ty.mk) carrier instE
    let lin ← withTransparency .all <| whnf (mkApp2 (mkConst ``Data.linear) carrier instE)
    let ctorE (c : Name) : Expr := mkAppN (mkConst c) ps
    -- The constructors.
    let mut vinfos : Array VariantInfo := #[]
    for i in [0:k] do
      let (c, fty?) := ctors[i]!
      let (pSTy, _) := pays[i]!
      let ts := [pSTy.toTy]
      let envTy := mkApp (mkConst ``Env) (memAt.listTy ts)
      let build ← withLocalDeclD `env envTy fun e => do
        mkLambdaFVars #[e] (if fty?.isSome then mkApp (ctorE c) (envGet ts e 0) else ctorE c)
      let cName := c ++ `ctor
      let kindE := mkApp (mkConst ``CtorKind.variant) (toExpr i)
      let law := mkAppN (mkConst ``Flat.CtorLaw) #[memAt.listTy ts, sTy, kindE, build]
      let cert ← certifyOr closed law s!"Millipede.Flat.CtorLaw.variantAt _ _ rfl \
        (Nat.le_of_ble_eq_true rfl) {i} _ rfl _ (fun _ => rfl) (fun _ => rfl)"
        s!"the constructor `{c}`"
      addDefnOver bs cName (mkApp2 (mkConst ``Ctor) (memAt.listTy ts) sTy)
        (← ctorMk #[memAt.listTy ts, sTy, toExpr (shortName E ++ "." ++ shortName c), kindE,
          build, cert])
        s!"The constructor `{c}` as a core `Ctor` (generated by `deriving Data`)."
      vinfos := vinfos.push
        { ctor := c, hasField := fty?.isSome, payload := pSTy.mapExpr (·.abstract bs), mkC := cName }
    -- The split chain. Two variants have one split `Split E P₀ P₁`. Three or more have
    -- `Split E Pᵢ E` for `i < k - 1`, whose rest is the value itself, and `Split E P_{k-1} Unit`
    -- last.
    let nSplits := if k == 2 then 1 else k
    if k > 2 then
      let pCar := pays[k - 1]!.2
      if (← synthInstance? (mkApp (mkConst ``Inhabited [1]) pCar)).isNone then
        throwError "deriving Data: the payload of the last constructor `{ctors[k - 1]!.1}` needs \
          an `Inhabited` instance"
    let mut splits : Array Name := #[]
    for i in [0:nSplits] do
      let pair := k == 2
      let last := k > 2 && i == k - 1
      let (pS, pCar) := pays[i]!
      let (qS, qCar) := if pair then pays[1]! else if last then (STy.unit, mkConst ``Unit)
        else (STy.other sTy carrier true "", carrier)
      let qTy := qS.toTy
      let sumTy := mkApp2 (mkConst ``Sum [0, 0]) pCar qCar
      let splitFn ← withLocalDeclD `e carrier fun e => do
        let motive ← withLocalDeclD `_x carrier fun x => mkLambdaFVars #[x] sumTy
        let mut alts : Array Expr := #[]
        for j in [0:k] do
          let (_, fty?) := ctors[j]!
          let mk (x? : Option Expr) : Expr :=
            let payload := x?.getD (mkConst ``Unit.unit)
            if j == i then mkApp3 (mkConst ``Sum.inl [0, 0]) pCar qCar payload
            else if pair then mkApp3 (mkConst ``Sum.inr [0, 0]) pCar qCar payload
            else if last then mkApp3 (mkConst ``Sum.inr [0, 0]) pCar qCar (mkConst ``Unit.unit)
            else mkApp3 (mkConst ``Sum.inr [0, 0]) pCar qCar e
          match fty? with
          | some t => alts := alts.push (← withLocalDeclD `x t fun x => do mkLambdaFVars #[x] (mk (some x)))
          | none => alts := alts.push (mk none)
        mkLambdaFVars #[e] (mkAppN (mkConst (E ++ `casesOn) [1]) (ps ++ #[motive, e] ++ alts))
      let law := mkAppN (mkConst ``Flat.SplitLaw) #[sTy, pS.toTy, qTy, toExpr i, splitFn]
      let inl := "(by intro x a h; cases x <;> cases h <;> first | rfl | exact ⟨rfl, rfl⟩)"
      let inr := "(by intro x b h; cases x <;> cases h <;> first | rfl | exact ⟨rfl, rfl⟩)"
      let le := "(Nat.le_of_ble_eq_true rfl)"
      let prf :=
        if pair then s!"Millipede.Flat.SplitLaw.pairAt _ _ rfl rfl _ _ rfl rfl _ {inl} {inr}"
        else if last then s!"Millipede.Flat.SplitLaw.unitAt _ _ rfl {le} {i} _ rfl _ {inl} {inr}"
        else s!"Millipede.Flat.SplitLaw.wholeAt _ _ rfl {le} {le} {i} _ rfl _ {inl} {inr}"
      let cert ← certifyOr closed law prf s!"split {i} of `{E}`"
      let sName := E ++ Name.mkSimple s!"split{i}"
      addDefnOver bs sName (mkApp3 (mkConst ``Split) sTy pS.toTy qTy) (mkAppN (mkConst ``Split.mk)
        #[sTy, pS.toTy, qTy, toExpr (shortName E), toExpr i, splitFn, cert])
        s!"Step {i} of the exhaustive match on `{E}` (generated by `deriving Data`)."
      -- Simp lemmas giving the split on each constructor.
      let sE := mkAppN (mkConst sName) bs
      for j in [0:k] do
        let (c, fty?) := ctors[j]!
        let split (v : Expr) := mkApp5 (mkConst ``Split.split) sTy pS.toTy qTy sE v
        let stmt ← match fty? with
          | some t => withLocalDeclD `x t fun x => do
              let lhs := split (mkApp (ctorE c) x)
              mkForallFVars (bs.push x) (← mkEq lhs (← whnf lhs))
          | none => do mkForallFVars bs (← mkEq (split (ctorE c)) (← whnf (split (ctorE c))))
        addRflSimp (sName ++ Name.mkSimple (shortName c)) stmt
      splits := splits.push sName
    let info : AdtInfo :=
      { name := E, lin := !lin.isConstOf ``Bool.false, kind := .enum vinfos splits, params := marks }
    modifyEnv (registry.addEntry · (.adt info))
    -- The parameters' binders and payload types, for the eliminator.
    let pbs ← ps.mapM fun p => do
      let d ← p.fvarId!.getDecl
      `(Lean.Parser.Term.bracketedBinderF| {$(mkIdent d.userName):ident : $(← PrettyPrinter.delab d.type)})
    -- With `[Data T]` after each type parameter, since the splits take them.
    let pbsI ← (ps.zip pbs).flatMapM fun (p, b) => do
      if (← whnf (← inferType p)).isType then
        let x := mkIdent (← p.fvarId!.getDecl).userName
        return #[b, ← `(Lean.Parser.Term.bracketedBinderF| [Millipede.Data $x])]
      return #[b]
    let pNames ← ps.mapM fun p => return mkIdent (← p.fvarId!.getDecl).userName
    let payTys : Array Term ← ctors.mapM fun (_, fty?) => do
      match fty? with
      | some t => PrettyPrinter.delab t
      | none => `(Unit)
    let eTy : Term ← if closed then pure (mkCIdent E) else PrettyPrinter.delab carrier
    return (pbs, pbsI, pNames, payTys, eTy)
  let (pbs, pbsI, pNames, payTys, eTy) := splitsInfo
  -- The eliminator and the lemma folding the split chain into it, which give the normal form of
  -- a `match`.
  let fs : Array Ident := (Array.range k).map fun i => mkIdent (Name.mkSimple s!"f{i}")
  let binders ← (fs.zip payTys).mapM fun (f, t) =>
    `(Lean.Parser.Term.bracketedBinderF| ($f : $t → β))
  let alts ← ((ind.ctors.toArray.zip payTys).zip fs).mapM fun ((c, _), f) => do
    let some (.ctorInfo cv) := env.find? c | throwError "no constructor {c}"
    if cv.numFields == 1 then `(Lean.Parser.Term.matchAltExpr| | $(mkCIdent c) x => $f x)
    else `(Lean.Parser.Term.matchAltExpr| | $(mkCIdent c) => $f ())
  let sId := mkIdent `s
  let nSplits := if k == 2 then 1 else k
  let splitIds ← (Array.range nSplits).mapM fun i => do
    let c := mkCIdent (E ++ Name.mkSimple s!"split{i}")
    let nargs ← pNames.mapM fun x => `(Lean.Parser.Term.namedArgument| ($x:ident := $x))
    if nargs.isEmpty then return (c : Term)
    return (⟨mkNode ``Lean.Parser.Term.app #[c, mkNullNode (nargs.map (·.raw))]⟩ : Term)
  -- For two variants this is `Sum.elim f₀ f₁ (split₀.split s)`, and for three or more
  -- `Sum.elim f₀ (fun y => … Sum.elim f_{k-1} (fun _ => f_{k-1} default) (split_{k-1}.split y))
  --   (split₀.split s)`, built from the last split outwards.
  let yId := mkIdent `y
  let mut lhs : Term ← if k == 2 then
      `(Sum.elim $(fs[0]!) $(fs[1]!) (Millipede.Split.split $(splitIds[0]!) $sId))
    else
      `(Sum.elim $(fs[k - 1]!) (fun (_ : Unit) => $(fs[k - 1]!) default)
        (Millipede.Split.split $(splitIds[k - 1]!) $yId))
  if k > 2 then
    for j in [0:k - 1] do
      let i := k - 2 - j
      let scrut := if i == 0 then sId else yId
      lhs ← `(Sum.elim $(fs[i]!) (fun ($yId : $eTy) => $lhs)
        (Millipede.Split.split $(splitIds[i]!) $scrut))
  let mId := mkIdent (`_root_ ++ E ++ `mpMatch)
  let eqId := mkIdent (`_root_ ++ E ++ `mpMatch_eq)
  elabCommand (← `(command|
    /-- `match s with | c₀ … => f₀ … | …`: the eliminator the normal form of a `match` on this
    enum folds into (generated by `deriving Data`). -/
    def $mId:ident $pbs* {β : Sort _} ($sId : $eTy) $binders* : β :=
      match $sId:ident with $alts:matchAlt*))
  elabCommand (← `(command|
    /-- The chain of splits is the eliminator (generated by `deriving Data`). -/
    theorem $eqId:ident $pbsI* {β : Sort _} ($sId : $eTy) $binders* :
        $lhs = $(mkCIdent (E ++ `mpMatch)) $sId $fs* := by
      cases $sId:ident <;> rfl))

/-- The handler of `deriving Data`. -/
def mkDataHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    let some (.inductInfo ind) := (← getEnv).find? n | return false
    unless ind.numIndices == 0 && ind.levelParams.isEmpty do
      throwError "deriving Data: `{n}` has indices or universe parameters; object types are \
        `Type`s with parameters"
    if isStructure (← getEnv) n then deriveStruct n ind
    else if ind.ctors.length ≥ 2 then deriveEnum n ind
    else throwError "deriving Data: `{n}` has a single constructor; declare it as a `structure`"
  return true

initialize registerDerivingHandler ``Millipede.Data mkDataHandler

end Millipede.Meta.Derive
