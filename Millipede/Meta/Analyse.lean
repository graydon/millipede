import Lean
import Millipede.Analysis.Sound
import Millipede.Meta.Basic

/-!
# The analyser in `mp def`

The automatic attempt of `mp def` at the obligations `f.safe` tries the verified analyser first.
It skips a term that the analyser cannot help, which is one with no overflow obligation and an
operation the analyser never certifies. Otherwise `analyse` takes the following steps.

1. It reads bounds on word parameters from the conjuncts of the function's `requires`, such as
   `x.toNat < c`, `c ≤ x.toNat` or `x < c` with numerals, and uses them as input intervals. The
   generated `s.len.toNat ≤ n` of a slice parameter is such a bound, and so is a bound in base
   units `u.inBase x < c` on a quantity. It proves the intervals from `requires` by `omega`.
2. It proves `f.exp.LoopsOk`, which says that the hand-back constructors of loop bodies are tuples,
   by the kernel for a term without loops and otherwise by `rfl` per constructor.
3. If the kernel evaluates `f.exp.safeBy is` to `true`, it declares `f.analysed` and proves
   `f.safe` by `Exp.safe_of_safeBy`, and `mp_safe` does not run.
4. Otherwise, if the kernel finds that the analyser certifies some overflow obligations, it
   declares the relaxed term `f.expR`, in which those primitives wrap, together with
   `f.relaxed`, which says that `f.expR` is `(f.exp.relax …).1`. `mp_safe` then works on the goal
   of `f.expR`, and `Exp.safe_of_relax` turns its proof into `f.safe`.

`#mp_analyse f` reports what the analyser certified for `f`. The option `mp.analyser false` skips
the analyser, and `mp.analyser.trace true` logs its verdict at each `mp def`.
-/

namespace Millipede.Meta.Analyse

open Lean Meta Elab Millipede Millipede.Analysis

register_option mp.analyser : Bool := {
  defValue := true
  descr := "`mp def` tries the verified analyser (`Exp.safeBy`) on the obligations before `mp_safe`"
}

register_option mp.analyser.trace : Bool := {
  defValue := false
  descr := "`mp def` logs what the analyser certified"
}

/-- A numeral, which is a `Nat` or `UInt64` literal or `Nat` arithmetic on literals. -/
def numeral? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let .lit (.natVal n) := e.appFn!.appArg! then return some n
  evalNat e |>.run

/-- Bounds on free variables read off the conjuncts of a proposition, `(x, true, c)` for `x ≤ c`
and `(x, false, c)` for `c ≤ x`, with strict comparisons adjusted. -/
partial def bounds (p : Expr) : MetaM (List (FVarId × Bool × Nat)) := do
  let p ← instantiateMVars p
  -- A comparison is read as written, since on `UInt64` `whnfR` would unfold `x < c` to a
  -- `BitVec` comparison. Anything else, such as a user's `def … : Prop`, is unfolded once.
  let rel (p : Expr) : Option (Bool × Expr × Expr) :=
    if p.isAppOfArity ``LT.lt 4 then some (true, p.appFn!.appArg!, p.appArg!)
    else if p.isAppOfArity ``LE.le 4 then some (false, p.appFn!.appArg!, p.appArg!)
    else if p.isAppOfArity ``GT.gt 4 then some (true, p.appArg!, p.appFn!.appArg!)
    else if p.isAppOfArity ``GE.ge 4 then some (false, p.appArg!, p.appFn!.appArg!)
    else none
  let p ← if p.isAppOfArity ``And 2 || (rel p).isSome then pure p else whnfR p
  if p.isAppOfArity ``And 2 then
    return (← bounds p.appFn!.appArg!) ++ (← bounds p.appArg!)
  let some (strict, lhs, rhs) := rel p | return []
  -- The variable and the scale of `x`, `x.toNat`, or a quantity in base units `u.inBase x`,
  -- which is `x.toNat * u.scale`.
  let var? (e : Expr) : MetaM (Option (FVarId × Nat)) := do
    if e.isAppOfArity ``UInt64.toNat 1 && e.appArg!.isFVar then return some (e.appArg!.fvarId!, 1)
    if e.isFVar then return some (e.fvarId!, 1)
    if e.isAppOfArity `Millipede.QUnit.inBase 2 && e.appArg!.isFVar then
      let some s ← numeral? (← whnf (mkApp (mkConst `Millipede.QUnit.scale) e.appFn!.appArg!))
        | return none
      if s == 0 then return none
      return some (e.appArg!.fvarId!, s)
    return none
  if let some (x, s) ← var? lhs then
    let some c ← numeral? rhs | return []
    -- `x * s < c` iff `x ≤ (c - 1) / s`; `x * s ≤ c` iff `x ≤ c / s`
    if strict then return if c == 0 then [] else [(x, true, (c - 1) / s)]
    return [(x, true, c / s)]
  if let some (x, s) ← var? rhs then
    let some c ← numeral? lhs | return []
    -- `c ≤ x * s` iff `⌈c / s⌉ ≤ x`
    let c := if strict then c + 1 else c
    return [(x, false, (c + s - 1) / s)]
  return []

/-- The units `u` whose base-unit amounts `u.inBase x` occur in `p`, given by the `scale_eq`
lemmas that `mp unit` generates, for `memTac`. -/
def unitLemmas (p : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for e in (← instantiateMVars p).foldConsts #[] (fun c acc => acc.push c) do
    if env.contains (e ++ `scale_eq) && !out.contains (e ++ `scale_eq) then
      out := out.push (e ++ `scale_eq)
  return out

/-- A tactic proving `x ∈ [0, hi]` for a word parameter from the hypotheses in context, which hold
`requires`. `units` are the `scale_eq` lemmas of the units whose `inBase` the hypotheses
mention. -/
def memTac (units : Array Name := #[]) : MetaM Syntax := do
  -- `QUnit.inBase` is named, since Millipede/Core/Quantity.lean is not imported here.
  let us : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← (units.push `Millipede.QUnit.inBase).mapM
    fun u => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent u):ident)
  if units.isEmpty then
    `(tactic| (intro _; simp only [Millipede.Analysis.Itv.mem, Nat.zero_le, true_and,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat',
      UInt64.reduceToNat] at *; omega))
  else
    `(tactic| (intro _; simp only [Millipede.Analysis.Itv.mem, Nat.zero_le, true_and,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.reduceToNat,
      $us,*] at *; omega))

/-- A tactic proving `f.exp.LoopsOk`, which unfolds the term and shows that every hand-back
constructor is a tuple by `rfl`. -/
def loopsOkTac (expName : Name) : MetaM Syntax := do
  let e := mkCIdent expName
  `(tactic| (simp only [$e:ident, Millipede.Exp.LoopsOk, Millipede.Exp.TailsOk, and_true, true_and,
              reduceCtorEq, false_implies, imp_self, forall_const, implies_true]
             repeat' (first | trivial | exact ⟨rfl, fun _ => rfl⟩ | (intro _) | constructor)))

/-- The counts of overflow obligations and of other partial operations of a term, from
`Exp.oblCount` reduced, for reports. -/
def oblCounts (Γ expT e : Expr) : MetaM (Nat × Nat) := do
  let r ← withTransparency .all <| reduce (mkApp3 (mkConst ``Exp.oblCount) Γ expT e)
  if r.isAppOfArity ``Prod.mk 4 then
    if let (some a, some b) := (r.appFn!.appArg!.nat?, r.appArg!.nat?) then return (a, b)
    if let (.lit (.natVal a), .lit (.natVal b)) := (r.appFn!.appArg!, r.appArg!) then return (a, b)
  return (0, 0)

/-- The list of intervals, where `none` is the whole range. -/
def itvList (items : List (Option (Nat × Nat × Expr))) : Expr :=
  let itvTy := mkConst ``Itv
  items.foldr (fun it acc =>
    let itv := match it with
      | some (lo, hi, _) => mkApp2 (mkConst ``Itv.mk) (mkNatLit lo) (mkNatLit hi)
      | none => mkConst ``Itv.top
    mkApp3 (mkConst ``List.cons [0]) itvTy itv acc) (mkApp (mkConst ``List.nil [0]) itvTy)

/-- The proof of `ItvsHold (itvList items) env`, parameter by parameter. -/
partial def holdsPrf (items : List (Option (Nat × Nat × Expr))) (env : Expr) : MetaM Expr := do
  match items with
  | [] => return mkApp2 (mkConst ``ItvsHold.nil) (← whnf (← inferType env)).appArg! env
  | it :: rest =>
    let .app (.app (.app (.app (.const ``Env.cons _) t) Γ') v) env' := env
      | throwError "analyser: unexpected environment {env}"
    let hs ← holdsPrf rest env'
    match it with
    | some (lo, hi, p) =>
      let itv := mkApp2 (mkConst ``Itv.mk) (mkNatLit lo) (mkNatLit hi)
      return mkAppN (mkConst ``ItvsHold.word) #[Γ', itv, itvList rest, v, env', p, hs]
    | none => return mkAppN (mkConst ``ItvsHold.top) #[Γ', t, itvList rest, v, env', hs]

/-- What the analyser did for a definition. -/
inductive AnResult where
  /-- Nothing was attempted or nothing was certified. -/
  | none
  /-- Every obligation was certified, with the proof of `f.SafeGoal`. -/
  | full (prf : Expr)
  /-- Some overflow obligations were certified. It holds the goal on the relaxed term `f.expR`
  for `mp_safe`, and the function from its proofs to proofs of `f.SafeGoal`. -/
  | relaxed (goal : Expr) (expRName : Name) (conv : Expr)

/-- The full proof, if any. -/
def AnResult.full? : AnResult → Option Expr
  | .full p => some p
  | _ => Option.none

/-- The goal and the term `mp_safe` works on. -/
def AnResult.mpGoal (r : AnResult) (goal : Expr) (expName : Name) : Expr × Name :=
  match r with
  | .relaxed g n _ => (g, n)
  | _ => (goal, expName)

/-- A proof of `f.SafeGoal` from a proof of `mp_safe`'s goal. -/
def AnResult.convert (r : AnResult) (prf : Expr) : Expr :=
  match r with
  | .relaxed _ _ conv => (mkApp conv prf).headBeta
  | _ => prf

/-- A list of Booleans, by kernel evaluation. -/
partial def kernelBools (env : Environment) (e : Expr) : Option (List Bool) := do
  let .ok v := Kernel.whnf env {} e | none
  if v.isAppOfArity ``List.nil 1 then return []
  unless v.isAppOfArity ``List.cons 3 do none
  let .ok b := Kernel.whnf env {} v.appFn!.appArg! | none
  let bv ← if b.isConstOf ``Bool.true then some true
    else if b.isConstOf ``Bool.false then some false else none
  return bv :: (← kernelBools env v.appArg!)

/-- The wrapping twin of an obligated primitive's constant. -/
def nuwTwin : Name → Option Name
  | ``Prim.addNuw => some ``Prim.add
  | ``Prim.subNuw => some ``Prim.sub
  | ``Prim.mulNuw => some ``Prim.mul
  | ``Prim.trunc8Nuw => some ``Prim.trunc8
  | _ => none

/-- Replace the obligated primitives of a term that are flagged `true`, in the order of the flags
of `Exp.relax`, which takes the constructors' fields left to right. -/
partial def relaxExpr (e : Expr) : StateM (List Bool) Expr := do
  match e with
  | .const n us =>
    match nuwTwin n with
    | some n' =>
      match ← get with
      | b :: rest => set rest; return if b then .const n' us else e
      | [] => return e
    | none => return e
  | .app f a => return .app (← relaxExpr f) (← relaxExpr a)
  | .mdata d b => return .mdata d (← relaxExpr b)
  | _ => return e

/-- The analyser in `mp def`. When it certifies every obligation it declares
`f.analysed : f.exp.safeBy is = true` and returns the proof of the goal `f.SafeGoal`, which is
`∀ ω w x…, requires → f.exp.safe …`. Otherwise, when it certifies some overflow obligations, it
declares the relaxed term `f.expR` and `f.relaxed : (f.exp.relax …).1 = f.expR`, and returns
the goal for `mp_safe` on it. -/
def analyse (declName : Name) (goalTy Γ expT : Expr) (expName : Name) (nParams : Nat)
    (hasReq : Bool) : Lean.Elab.TermElabM AnResult := do
  unless mp.analyser.get (← getOptions) do return .none
  let trace := mp.analyser.trace.get (← getOptions)
  let expC := mkConst expName
  let kTrue (b : Expr) : MetaM Bool := return Kernel.isDefEqGuarded (← getEnv) {} b (mkConst ``Bool.true)
  -- Skip a term it cannot help with, which has no overflow obligation and an operation it never
  -- certifies.
  unless ← kTrue (mkApp3 (mkConst ``Exp.anWorth) Γ expT expC) do return .none
  -- The hand-back constructors of loop bodies, with nothing to prove by the kernel when there is
  -- no loop.
  let hasLoop := mkApp3 (mkConst ``Exp.hasLoop) Γ expT expC
  let hL? ← if Kernel.isDefEqGuarded (← getEnv) {} hasLoop (mkConst ``Bool.false) then
      pure (some (mkApp4 (mkConst ``Exp.loopsOk_of_hasLoop) Γ expT expC
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))))
    else Millipede.Meta.tryProve (mkApp3 (mkConst ``Exp.LoopsOk) Γ expT expC) (← loopsOkTac expName)
  let some hL := hL? | do
    if trace then logInfo m!"analyser: `{declName}`: could not prove `LoopsOk`"
    return .none
  forallTelescope goalTy fun ys _ => do
    let ω := ys[0]!; let w := ys[1]!
    let xs := ys.extract 2 (2 + nParams)
    let h? := if hasReq then ys[2 + nParams]? else none
    let (bs, units) ← match h? with
      | some h => do let p ← inferType h; pure (← bounds p, ← unitLemmas p)
      | none => pure ([], #[])
    -- Intervals in de Bruijn order, where the last parameter is index 0, with their proofs.
    let mut items : Array (Option (Nat × Nat × Expr)) := #[]
    for i in [0:nParams] do
      let x := xs[nParams - 1 - i]!
      let isWord ← isDefEq (← inferType x) (mkConst ``UInt64)
      let mine := bs.filter (·.1 == x.fvarId!)
      let hi := ((mine.filter (·.2.1)).map (·.2.2)).min?.getD wmax
      let lo := ((mine.filter (!·.2.1)).map (·.2.2)).max?.getD 0
      if isWord && !mine.isEmpty && lo ≤ hi then
        let itv := mkApp2 (mkConst ``Itv.mk) (mkNatLit lo) (mkNatLit hi)
        let goal := mkApp2 (mkConst ``Itv.mem) itv (mkApp (mkConst ``UInt64.toNat) x)
        let lt ← mkAppM ``LT.lt #[mkApp (mkConst ``UInt64.toNat) x, mkNatLit (2 ^ 64)]
        match ← Millipede.Meta.tryProve (← mkArrow lt goal) (← memTac units) with
        | some p => items := items.push (some (lo, hi, mkApp p (mkApp (mkConst ``UInt64.toNat_lt) x)))
        | none => items := items.push none
      else items := items.push none
    -- Drop trailing parameters without an interval.
    while items.size > 0 && items.back!.isNone do items := items.pop
    let isList := itvList items.toList
    let env ← envOf goalTy ys
    let hI ← holdsPrf items.toList env
    -- The kernel's verdict, computed synchronously. The declarations below are checked again,
    -- possibly asynchronously.
    let safeBy := mkApp4 (mkConst ``Exp.safeBy) Γ expT isList expC
    let ok := Kernel.isDefEqGuarded (← getEnv) {} safeBy (mkConst ``Bool.true)
    let (nOv, nOther) ← if trace then oblCounts Γ expT expC else pure (0, 0)
    if ok then
      if trace then
        logInfo m!"analyser: `{declName}`: certified all ({nOv} overflow obligations, {nOther} \
          other partial operations; input intervals \
          {items.toList.map (·.map fun (lo, hi, _) => (lo, hi))})"
      let prop ← mkEq safeBy (mkConst ``Bool.true)
      let prf := mkApp3 (mkConst ``of_decide_eq_true) prop
        (mkApp2 (mkConst ``instDecidableEqBool) safeBy (mkConst ``Bool.true))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      let anName := declName ++ `analysed
      addThmChecked anName prop prf
      addDocStringCore anName s!"The verified analyser certifies the obligations of `{declName}` \
        (kernel evaluation of `Exp.safeBy`)."
      let body := mkAppN (mkConst ``Exp.safe_of_safeBy)
        #[Γ, expT, isList, expC, hL, mkConst anName, ω, env, w, hI]
      return .full (← mkLambdaFVars ys body)
    -- Partial certification relaxes the overflow obligations it certifies.
    let aEnv := mkApp2 (mkConst ``AEnv.ofItvs) Γ isList
    let relax := mkApp4 (mkConst ``Exp.relax) Γ expT expC aEnv
    let flagsE := mkApp3 (mkConst ``Prod.snd [1, 0]) (mkApp2 (mkConst ``Exp) Γ expT)
      (mkApp (mkConst ``List [0]) (mkConst ``Bool)) relax
    let some flags := kernelBools (← getEnv) flagsE | return .none
    let nRelaxed := (flags.filter id).length
    if trace then
      logInfo m!"analyser: `{declName}`: certified {nRelaxed} of the {flags.length} overflow \
        obligations ({nOther} other partial operations; input intervals \
        {items.toList.map (·.map fun (lo, hi, _) => (lo, hi))}); the rest goes to `mp_safe`"
    if nRelaxed == 0 then return .none
    let some ci := (← getEnv).find? expName | return .none
    let some val := ci.value? | return .none
    let (valR, rest) := (relaxExpr val).run flags
    unless rest.isEmpty do return .none
    let expRName := declName ++ `expR
    let decl := Declaration.defnDecl
      { name := expRName, levelParams := [], type := ci.type, value := valR,
        hints := .regular (getMaxHeight (← getEnv) valR + 1),
        safety := .safe }
    addDecl decl
    enableRealizationsForConst expRName
    let lhs := mkApp3 (mkConst ``Prod.fst [1, 0]) (mkApp2 (mkConst ``Exp) Γ expT)
      (mkApp (mkConst ``List [0]) (mkConst ``Bool)) relax
    unless Kernel.isDefEqGuarded (← getEnv) {} lhs (mkConst expRName) do return .none
    let relName := declName ++ `relaxed
    let relTy ← mkEq lhs (mkConst expRName)
    let relPrf ← mkEqRefl (mkConst expRName)
    addThmChecked relName relTy relPrf
    addDocStringCore expRName s!"`{declName}.exp` with the overflow obligations the verified \
      analyser certifies relaxed to wrapping primitives (`Exp.relax`)."
    let goalR := goalTy.replace fun e => if e.isConstOf expName then some (mkConst expRName)
      else none
    let conv ← withLocalDeclD `p goalR fun p => do
      let inner := mkAppN (mkConst ``Exp.safe_of_relax)
        #[Γ, expT, isList, expC, mkConst expRName, hL, mkConst relName, ω, env, w, hI,
          mkAppN p ys]
      mkLambdaFVars #[p] (← mkLambdaFVars ys inner)
    return .relaxed goalR expRName conv
where
  /-- The environment argument of `Exp.safe` in the goal's body. -/
  envOf (goalTy : Expr) (ys : Array Expr) : MetaM Expr := do
    let body ← instantiateForall goalTy ys
    let body ← whnfR body
    -- The body has the form `Exp.safe ω Γ t e env w`.
    unless body.isAppOfArity ``Exp.safe 6 do throwError "analyser: unexpected goal {body}"
    return body.getArg! 4

/-- What the verified analyser certified for the `mp def` `f`, which is all obligations with
`f.analysed`, `k` of its `n` overflow obligations with `f.relaxed`, or nothing, together with the
counts of overflow obligations and of other partial operations. It is `none` when `f` is not an
`mp def`. -/
def certified (f : Name) : MetaM (Option (Option Nat × Nat × Nat)) := do
  let env ← getEnv
  let some ci := env.find? (f ++ `exp) | return none
  let ty ← whnf ci.type
  let (nOv, nOther) ← oblCounts ty.appFn!.appArg! ty.appArg! (mkConst (f ++ `exp))
  if env.contains (f ++ `analysed) then return some (some (nOv + nOther), nOv, nOther)
  if let some rc := env.find? (f ++ `relaxed) then
    -- In `(Exp.relax f.exp is).1 = f.expR` the flags are the second component.
    let some (_, lhs, _) := rc.type.eq? | return some (some 0, nOv, nOther)
    let flagsE := mkApp3 (mkConst ``Prod.snd [1, 0]) lhs.appFn!.appFn!.appArg!
      lhs.appFn!.appArg! lhs.appArg!
    return some (some ((kernelBools env flagsE).getD [] |>.filter id).length, nOv, nOther)
  return some (none, nOv, nOther)

/-- `certified f` in words, for `#mp_analyse` and `#mp_report`. -/
def certifiedMsg (f : Name) : MetaM (Option String) := do
  let some (k?, nOv, nOther) ← certified f | return none
  let env ← getEnv
  if env.contains (f ++ `analysed) then
    return some s!"the analyser certified all ({nOv} overflow, {nOther} other partial operations)"
  match k? with
  | some k => return some s!"the analyser certified {k} of the {nOv} overflow obligations \
      (the rest and {nOther} other partial operations by `mp_safe` or `mp prove`)"
  | none => return some s!"the analyser certified none ({nOv} overflow, {nOther} other partial \
      operations)"

/-- `#mp_analyse f` reports what the verified analyser certified for the `mp def` `f`, which is
all obligations, some overflow obligations with `mp_safe` or `mp prove` for the rest, or none, and
whether `f.safe` is proved. -/
syntax (name := mpAnalyse) "#mp_analyse " ident : command

@[command_elab mpAnalyse] def elabMpAnalyse : Lean.Elab.Command.CommandElab := fun stx =>
  Lean.Elab.Command.liftTermElabM do
    let f ← realizeGlobalConstNoOverload stx[1]
    let some msg ← certifiedMsg f | throwErrorAt stx[1] "`{f}` is not an `mp def`"
    let proved := if (← getEnv).contains (f ++ `safe) then "proved" else "not proved"
    logInfo m!"`{f}`: {msg}; `safe` {proved}"

end Millipede.Meta.Analyse
