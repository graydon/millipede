import Lean
import Millipede.Meta.Auto
import Millipede.Meta.Reach

/-!
# Root invariants and the safety of a reactor

`mp program p (root : T) init f step g invariant I`, with `I : T → Prop`, defines the program and
the following declarations.
- `p.invariant : T → Prop := I`.
- The goal `p.InvInitGoal`, which says that `init` establishes `I`, `⦃True⦄ f ⦃fun r => I r⦄`, and
  the goal `p.InvStepGoal`, which says that `step` is safe under `I` and keeps it,
  `∀ r, (I r → R r) ∧ ⦃I r⦄ g r ⦃fun x => I x.2.1⦄`, where `R` is the `requires` of `g`. An oracle
  `ω` is added for an effectful `f` or `g`.
- `p.inv_init` and `p.inv_step`, the proved goals. Each goal is tried like a contract, with `vcgen`
  and `grind`, using a contract of `f` or `g` when there is one and unfolding them otherwise. If
  `g` is declared with `requires I r ensures I r'` both goals are immediate. A goal that is not
  proved is left for `mp prove p.inv_init := …` or `mp prove p.inv_step := …`.
- `p.inv : ∀ ω n, I (p.run ω n).1` and `p.safe : p.Safe`, derived from these without a further
  user proof once `f.safe` and `g.safe` are proved. The reactor induction is
  `Program.safe_of_inv`, written once.

Without `invariant`, `p.safe` is derived the same way with the invariant `True`, so `step` must
have no `requires`. The obligations are described in doc/design/obligations.md.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta Std.WP

/-- The `mp def` that the term `e` is or calls, found by its first `f.exp` constant. -/
def fnOfExp (e : Expr) : CoreM FnInfo := do
  let env ← getEnv
  for c in e.getUsedConstants do
    if c.isStr && c.getString! == "exp" then
      if let some (.fn f) := lookupEntry env c.getPrefix then return f
  throwError "no `mp def` in{indentExpr e}"

/-- The goals `p.InvInitGoal` and `p.InvStepGoal` that the module doc describes. -/
def invGoals (fi fs : FnInfo) (I : Expr) : TermElabM (Expr × Expr) := do
  let IS ← exprToSyntax I
  let fiS ← exprToSyntax (fi.const .anonymous)
  let initG ← match fi.isPure, fi.isRef with
    | true, false => `(⦃True⦄ $fiS ⦃fun r => $IS r⦄)
    | true, true => `(⦃True⦄ $fiS ⦃fun r => $IS r.1⦄)
    | false, false => `(∀ ω, ⦃fun _ => True⦄ $fiS ω ⦃fun r _ => $IS r⦄)
    | false, true => `(∀ ω, ⦃fun _ => True⦄ $fiS ω ⦃fun r _ => $IS r.1⦄)
  -- The `requires` of `g`, from its `SafeGoal` `∀ ω w r (h : R r), …`.
  let some sg := ((← getEnv).find? (fs.declName ++ `SafeGoal)).bind (·.value?)
    | throwError "`{fs.declName}` has no `SafeGoal`"
  let sg := sg.beta fs.genArgs
  let R ← forallTelescope sg fun ys _ => do
    let R ← match ys[3]? with
      | some h => inferType h
      | none => pure (mkConst ``True)
    mkLambdaFVars #[ys[2]!] R
  let RS ← exprToSyntax R
  let fsS ← exprToSyntax (fs.const .anonymous)
  let stepG ← if fs.isPure then `(∀ r, ($IS r → $RS r) ∧ ⦃$IS r⦄ $fsS r ⦃fun x => $IS x.2.1⦄)
    else `(∀ ω r, ($IS r → $RS r) ∧ ⦃fun _ => $IS r⦄ $fsS ω r ⦃fun x _ => $IS x.2.1⦄)
  let elab1 (s : Term) : TermElabM Expr := do
    let e ← elabTermEnsuringType s (mkSort .zero)
    synthesizeSyntheticMVarsNoPostponing
    Core.betaReduce (← instantiateMVars e)
  return (← elab1 initG, ← elab1 stepG)

/-- The automatic attempt at an invariant goal `g`. It runs `vcgen`, using the contracts of the
functions that have one and unfolding the others, and `grind`, with the invariant's predicates
unfolded, and then tries what `mp_auto` would, with the callees' contracts and the `@[mp_auto]`
facts. -/
def invTac (f : FnInfo) (step : Bool) (g : Expr) : TermElabM Syntax := do
  let env ← getEnv
  let callees ← calleesOf f.declName
  let unfold := (#[f.declName] ++ callees).filter fun g => !env.contains (g ++ `spec)
  let ids ← unfold.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let gparam (n : Name) := `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
  let preds ← (← contractPreds g).mapM gparam
  let posts ← ((#[f.declName] ++ callees).filter fun c => env.contains (c ++ `post)).mapM
    fun c => gparam (c ++ `post)
  let all := preds ++ posts ++ (← taggedParams) ++ (← u64Params)
  let vc ← `(tactic| (vcgen [$ids,*]; all_goals (first | grind [$preds,*] | grind [$all,*])))
  if step then `(tactic| (intros; exact ⟨fun h => by first | trivial | exact h | grind [$preds,*],
    by $vc:tactic⟩))
  else `(tactic| (intros; $vc:tactic))

/-- Whether `step`'s `requires` is `True`. -/
def stepReqTrivial (fs : FnInfo) : CoreM Bool := do
  let some v := ((← getEnv).find? (fs.declName ++ `req)).bind (·.value?) | return true
  return v.getLambdaBody.isConstOf ``True

/-- Derive `p.safe` and, with an invariant, `p.inv` by `Program.safe_of_inv`, from `f.safe`,
`g.Safe` and `p.inv_init` and `p.inv_step`, or from the invariant `True`. -/
def deriveProgram (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  let some (.defnInfo pv) := env.find? declName | throwError "`{declName}` is not a program"
  -- A generic program is taken at the variables in scope.
  let gvs ← genVarsRef.get
  let #[_, initE, stepE] := (pv.value.beta gvs).getAppArgs
    | throwError "`{declName}` is not a program"
  let fi ← (← fnOfExp initE).inScope
  let fs ← (← fnOfExp stepE).inScope
  let hasInv := env.contains (declName ++ `invariant)
  let short := declName.componentsRev.head!
  unless fi.hasSafe && fs.hasSafe do
    let missing := ([fi, fs].filter (!·.hasSafe)).map fun f => s!"`{f.declName}.safe`"
    logInfo m!"`{short}.safe` is not generated: {" and ".intercalate missing} must be proved \
      first"
    return
  if !hasInv && !(← stepReqTrivial fs) then
    logInfo m!"`{short}.safe` is not generated: `{fs.declName}` has a `requires`; give the \
      program an `invariant` under which it holds"
    return
  let PE := mkAppN (mkConst declName) gvs
  let P := mkCIdent declName
  let PS ← exprToSyntax PE
  let I : Term ← if hasInv then exprToSyntax (mkAppN (mkConst (declName ++ `invariant)) gvs)
    else `(fun _ => True)
  let fiR ← exprToSyntax (fi.const (if fi.isRef then `fnRef else `fn))
  let (fiS, fiS0) := (← exprToSyntax (fi.const `Safe), ← exprToSyntax (fi.const `safe))
  let (fsR, fsS) := (← exprToSyntax (fs.const `fnRef), ← exprToSyntax (fs.const `Safe))
  let unf ← `(tactic| simp only [$P:ident, Millipede.Exp.denote, Millipede.RArgs.denote,
    Millipede.RArgs.writeBack, Millipede.Place.get, Millipede.Place.set, Millipede.Atom.denote,
    Millipede.Env.get_here, Millipede.Env.get_there, Millipede.Env.set_here,
    $(mkCIdent (fi.declName ++ `exp_denote)):ident, $(mkCIdent (fs.declName ++ `exp_denote)):ident])
  let initSafe ← if fi.isRef then
      `(tactic| (refine Millipede.FnRef.safe_call $fiR $fiS _ _ ω _ _ ?_ ?_ ?_ <;> exact trivial))
    else `(tactic| exact $fiS0 ω Millipede.World.init)
  let ii ← if hasInv then exprToSyntax (mkAppN (mkConst (declName ++ `inv_init)) gvs)
    else `(trivial)
  let si ← if hasInv then exprToSyntax (mkAppN (mkConst (declName ++ `inv_step)) gvs)
    else `(trivial)
  let initInv ← if !hasInv then `(tactic| trivial)
    else if fi.isPure then `(tactic| ($unf:tactic; have hh := Millipede.Spec.run_of_triple $ii trivial; exact hh))
    else `(tactic| ($unf:tactic; have hh := Millipede.Spec.runM_of_triple ($ii ω) trivial Millipede.World.init; exact hh))
  let stepReq ← if !hasInv then `(tactic| exact trivial)
    else if fs.isPure then `(tactic| exact ($si r).1 h) else `(tactic| exact ($si ω r).1 h)
  let stepInv ← if !hasInv then `(tactic| trivial)
    else if fs.isPure then `(tactic| ($unf:tactic; have hh := Millipede.Spec.run_of_triple ($si r).2 h; exact hh))
    else `(tactic| ($unf:tactic; have hh := Millipede.Spec.runM_of_triple ($si ω r).2 h w; exact hh))
  let tac ← `(tactic| exact Millipede.Program.safe_of_inv $PS $I
    (fun ω => ⟨by $initSafe:tactic, by $initInv:tactic⟩)
    (fun ω r w h => ⟨by
      refine Millipede.FnRef.safe_call $fsR $fsS _ _ ω _ _ ?_ ?_ ?_
      · exact And.intro trivial trivial
      · $stepReq:tactic
      · exact trivial, by $stepInv:tactic⟩))
  let Iv ← if hasInv then pure (mkAppN (Lean.mkConst (declName ++ `invariant)) gvs)
    else do
      let T := mkApp (mkConst ``Ty.carrier) (mkApp (mkConst ``Program.State) PE)
      pure (.lam `_ T (mkConst ``True) .default)
  let goal ← mkAppM ``And #[mkApp (mkConst ``Program.Safe) PE,
    ← withLocalDeclD `ω (mkConst ``Oracle) fun ω => withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkForallFVars #[ω, n] (mkApp Iv (← mkAppM ``Prod.fst #[mkApp3 (mkConst ``Program.run)
        PE ω n]))]
  match ← tryProve goal tac with
  | none => logInfo m!"could not derive `{short}.safe` automatically"
  | some p =>
    addThm (declName ++ `safe) (goal.getArg! 0) (← mkAppM ``And.left #[p])
    addDocStringCore (declName ++ `safe) "The program's obligations hold on every run."
    if hasInv then
      let invTy := goal.getArg! 1
      addThm (declName ++ `inv) invTy (← mkAppM ``And.right #[p])
      addDocStringCore (declName ++ `inv) "The root invariant holds after `init` and every step, \
        on every run."

/-- The relation of an event contract `E` of `f`, as a function of its parameters `ω x…`:
`fun ω x… r h evs e => E`, and its `requires` `R`, `fun ω x… => R`, or `none` for `True`. `none`
when `f` has no event contract. -/
def eventRel (f : FnInfo) : MetaM (Option ((Array Expr → Expr) × Option (Array Expr → Expr))) := do
  let some ci := (← getEnv).find? (f.declName ++ `spec) | return none
  forallTelescope ci.type fun args tri => do
    let some (_, R, E) ← eventParts tri | return none
    let ps := args.pop
    let E ← mkLambdaFVars ps E
    let R? ← if R.isConstOf ``True then pure none else
      pure (some ((← mkLambdaFVars ps R).beta ·))
    return some ((E.beta ·), R?)

/-- When `step` has an event contract and `init` has one or is pure, the relations they state
and `p.reach`, which says that the program reaches only the states that they allow
(`Program.reach_of_contracts`), and `p.events_reach`, the same for the trace.
- `p.initRel ω r evs e`: the contract of `init` at the empty history, or for a pure `init`,
  `r` is its value and there are no events.
- `p.stepRel ω r h evs e r'`: the contract of `step` at the root `r` before and `r'` after;
  when the contract has a `requires` `R`, it is `R r → E`
  (`Program.reach_of_contracts_req`). -/
def deriveReach (declName : Name) (fi fs : FnInfo) : TermElabM Unit := do
  unless (← genVarsRef.get).isEmpty do return
  let short := declName.componentsRev.head!
  let skip (why : String) := logInfo m!"`{short}.reach` is not generated: {why}"
  let some (Es, Rs?) ← eventRel fs | return
  if fi.isRef then return ← skip "`init` returns its root through a reference"
  let Ei? ← if fi.isPure then pure none else eventRel fi
  let Ei? := match Ei? with | some (E, none) => some E | _ => none
  if !fi.isPure && Ei?.isNone then
    return ← skip s!"`{fi.declName}` needs a contract about events, without `requires`"
  let T := fi.ret.carrier
  let evL := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Event)
  let unit := Lean.mkConst ``Unit.unit
  -- `(fun ω r h evs e r' => E, fun ω r => R)`; `p.stepRel` is the first, or `R r → E`.
  let (stepE, stepR) ← withLocalDeclD `ω (Lean.mkConst ``Oracle) fun ω => withLocalDeclD `r T fun r =>
    withLocalDeclD `h evL fun h => withLocalDeclD `evs evL fun evs =>
    withLocalDeclD `e (Lean.mkConst ``Bool) fun e => withLocalDeclD `r' T fun r' => do
      let res ← mkAppM ``Prod.mk #[unit, ← mkAppM ``Prod.mk #[r', unit]]
      -- `((), (r', ())).2.1` is `r'`.
      let body ← Meta.transform ((Es #[ω, r]).beta #[res, h, evs, e]) (post := fun x => do
        if x.isAppOfArity ``Prod.fst 3 || x.isAppOfArity ``Prod.snd 3 then
          let y ← whnfR x
          if y != x then return .visit y
        return .done x)
      return (← mkLambdaFVars #[ω, r, h, evs, e, r'] body,
        ← Rs?.mapM fun Rs => mkLambdaFVars #[ω, r] (Rs #[ω, r]))
  let stepRel ← match stepR with
    | none => pure stepE
    | some R => lambdaTelescope stepE fun xs body => do
        mkLambdaFVars xs (← mkArrow ((R.beta #[xs[0]!, xs[1]!])) body)
  let initRel ← withLocalDeclD `ω (Lean.mkConst ``Oracle) fun ω => withLocalDeclD `r T fun r =>
    withLocalDeclD `evs evL fun evs => withLocalDeclD `e (Lean.mkConst ``Bool) fun e => do
      let body ← match Ei? with
        | some Ei => pure ((Ei #[ω]).beta #[r, mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``Event), evs, e])
        | none => mkAppM ``And #[← mkEq r (← mkAppM ``Id.run #[fi.const .anonymous]),
            ← mkAppM ``And #[← mkEq evs (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``Event)),
              ← mkEq e (Lean.mkConst ``Bool.false)]]
      mkLambdaFVars #[ω, r, evs, e] body
  addDef (declName ++ `initRel) (← inferType initRel) initRel (compile := false)
  addDocStringCore (declName ++ `initRel) "What `init`'s contract says of the root it builds, its \
    events and whether it exited, under the oracle."
  addDef (declName ++ `stepRel) (← inferType stepRel) stepRel (compile := false)
  addDocStringCore (declName ++ `stepRel) "What `step`'s contract says of the root before, the \
    history, the events of the step, whether it exited and the root after, under the oracle."
  let P := mkCIdent declName
  let TS ← exprToSyntax T
  let (iR, sR) := (mkCIdent (declName ++ `initRel), mkCIdent (declName ++ `stepRel))
  let (gi, gs) := (mkCIdent fi.declName, mkCIdent fs.declName)
  let (gsPost, gsDen) := (mkCIdent (fs.declName ++ `post), mkCIdent (fs.declName ++ `exp_denote))
  let initTac ← if fi.isPure then `(tactic| exact ⟨rfl, rfl, rfl⟩)
    else `(tactic| (
      obtain ⟨evs, he, hE⟩ := $(mkCIdent (fi.declName ++ `post)) ω []
      have h0 : Millipede.Program.run $P ω 0 = ($gi ω).run ⟨[], false⟩ := by
        rw [Millipede.Program.run, $P:ident, $(mkCIdent (fi.declName ++ `exp_denote)):ident]; rfl
      rw [h0, $iR:ident]; dsimp only; rw [he, List.nil_append]; exact hE))
  let eqn ← `(tactic| have e : ($P).step.denote ω (.cons r .nil) ⟨h, false⟩ =
          ((($gs ω r).run ⟨h, false⟩).1.2.1, (($gs ω r).run ⟨h, false⟩).2) := by
        simp only [$P:ident, Millipede.Exp.denote]; rw [← $gsDen:ident]; rfl)
  let tac ← match Rs? with
    | none => `(tactic| (
      intro ω n
      refine Millipede.Program.reach_of_contracts $P ω ($iR ω) ($sR ω) ?_ ?_ n
      · $initTac:tactic
      · intro (r : $TS) h
        $eqn:tactic
        rw [e]; exact $gsPost ω h r))
    | some _ => `(tactic| (
      intro ω n
      refine Millipede.Program.reach_of_contracts_req $P ω ($iR ω) ($(← exprToSyntax (stepR.getD stepE)) ω)
        ($(← exprToSyntax stepE) ω) ?_ ?_ n
      · $initTac:tactic
      · intro (r : $TS) h hR
        $eqn:tactic
        rw [e]; exact $gsPost ω h r hR))
  let PE := Lean.mkConst declName
  let goal ← withLocalDeclD `ω (Lean.mkConst ``Oracle) fun ω => withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    let reach := mkAppN (Lean.mkConst ``Program.Reach) #[PE, mkApp (Lean.mkConst (declName ++ `initRel)) ω,
      mkApp (Lean.mkConst (declName ++ `stepRel)) ω, n, ← mkAppM ``Program.run #[PE, ω, n]]
    mkForallFVars #[ω, n] reach
  match ← tryProveE goal tac with
  | .error left => skip s!"the contracts did not give it; left:\n{left}"
  | .ok prf =>
    addThm (declName ++ `reach) goal prf
    addDocStringCore (declName ++ `reach) "For every oracle, the state after `n` steps is one that \
      the contracts of `init` and `step` allow (`Program.Reach`)."
    let evGoal ← withLocalDeclD `ω (Lean.mkConst ``Oracle) fun ω => withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
      let st ← withLocalDeclD `r T fun r => do
        let w := mkApp2 (Lean.mkConst ``World.mk) (← mkAppM ``Program.events #[PE, ω, n])
          (← mkAppM ``Program.halted #[PE, ω, n])
        mkLambdaFVars #[r] (mkAppN (Lean.mkConst ``Program.Reach) #[PE,
          mkApp (Lean.mkConst (declName ++ `initRel)) ω, mkApp (Lean.mkConst (declName ++ `stepRel)) ω, n,
          ← mkAppM ``Prod.mk #[r, w]])
      mkForallFVars #[ω, n] (← mkAppM ``Exists #[st])
    let some evPrf ← tryProve evGoal (← `(tactic| (intro ω n; exact ⟨_, $(mkCIdent (declName ++ `reach)) ω n⟩)))
      | skip "`events_reach` failed"
    addThm (declName ++ `events_reach) evGoal evPrf
    addDocStringCore (declName ++ `events_reach) "For every oracle, the trace after `n` steps is \
      that of a state that the contracts of `init` and `step` allow."

/-- The programs whose `step` has a contract about events that was not proved when the program
was declared, with their `init` and `step`. `mp prove g.spec` derives their `p.reach`. -/
initialize pendingReachExt : SimplePersistentEnvExtension (Name × Name × Name)
    (Array (Name × Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- `deriveReach` now, or once `step`'s event contract is proved by `mp prove`. -/
def deriveReachOrDefer (declName : Name) (fi fs : FnInfo) : TermElabM Unit := do
  let env ← getEnv
  if !env.contains (fs.declName ++ `spec) then
    if let some g := (env.find? (fs.declName ++ `SpecGoal)).bind (·.value?) then
      if (← eventParts' g).isSome then
        modifyEnv (pendingReachExt.addEntry · (declName, fi.declName, fs.declName))
    return
  deriveReach declName fi fs

/-- After `mp prove g.spec`: `p.reach` for each program declared with the step `g`. -/
def deriveReachAfter (g : Name) : TermElabM Unit := do
  let env ← getEnv
  for (p, fi, fs) in pendingReachExt.getState env do
    unless fs == g && !env.contains (p ++ `reach) do continue
    let (some (.fn fi), some (.fn fs)) := (lookupEntry env fi, lookupEntry env fs) | continue
    deriveReach p fi fs

/-- Elaborate `mp program p (root : T) init f step g`, with an optional `invariant I`. -/
@[command_elab mpProgram] def elabMpProgram : CommandElab := fun stx => withGenVars stx do
  let (declName, fi, fs) ← mpProgramBase stx
  withRef stx[3] (deriveReachOrDefer declName fi fs)
  if stx[13].getNumArgs == 0 then return ← withRef stx[3] (deriveProgram declName)
  unless fi.hasNf && fs.hasNf do
    throwErrorAt stx[13] "an invariant is about the normal forms: `init` and `step` need them"
  let T := fi.ret.carrier
  let I ← elabTermEnsuringType stx[13][1] (← mkArrow T (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let I ← instantiateMVars I
  addDef (declName ++ `invariant) (← mkArrow T (mkSort .zero)) I (compile := false)
  addDocStringCore (declName ++ `invariant) "The root invariant (`mp program … invariant`)."
  let (initG, stepG) ← invGoals fi fs I
  let mut proved := true
  for (nm, g, f, step) in [(`inv_init, initG, fi, false), (`inv_step, stepG, fs, true)] do
    let goalName := declName ++ (if step then `InvStepGoal else `InvInitGoal)
    addDef goalName (mkSort .zero) g (compile := false)
    addDocStringCore goalName (if step then "`step` is safe under the invariant and keeps it."
      else "`init` establishes the invariant.")
    let prf? ← if mp.autoSpec.get (← getOptions) then tryProve g (← invTac f step g) else pure none
    match prf? with
    | some p => addThm (declName ++ nm) g p
    | none =>
      proved := false
      logInfoAt stx[3] m!"`{stx[3].getId}.{nm}` was not proved automatically; prove it with \
        `mp prove {stx[3].getId}.{nm} := …` (the goal is `{goalName}`)"
  if proved then withRef stx[3] (deriveProgram declName)

/-- `mp prove p.inv_init := proof` and `mp prove p.inv_step := proof` prove an invariant goal of
`mp program … invariant`. Once both are proved, `p.safe` and `p.inv` are derived. -/
def elabMpProveInv (stx : Syntax) : CommandElabM Unit := liftTermElabM do
  let target := stx[3].getId
  let last := if target.components.getLast? == some `inv_step then `inv_step else `inv_init
  let goalSuffix := if last == `inv_step then `InvStepGoal else `InvInitGoal
  let cands ← resolveGlobalName (target.getPrefix ++ goalSuffix)
  let some (goalName, _) := cands.find? (·.2.isEmpty)
    | throwErrorAt stx[3] "`{target.getPrefix}` has no invariant goal `{goalSuffix}`"
  let declName := goalName.getPrefix
  unless (← getConstInfo declName).type.isConstOf ``Program do
    throwErrorAt stx[3] "`mp prove` of an invariant goal is for closed programs: a program over \
      `variable`s gets its invariant from the contracts of `init` and `step`"
  if (← getEnv).contains (declName ++ last) then
    throwErrorAt stx[3] "`{declName ++ last}` is already proved"
  let some goalTy := ((← getEnv).find? goalName).bind (·.value?) | throwError "no goal"
  let prf ← elabTermEnsuringType stx[5] goalTy
  synthesizeSyntheticMVarsNoPostponing
  let prf ← instantiateMVars prf
  if prf.hasMVar || prf.hasSorry then throwErrorAt stx[5] "the proof is incomplete"
  addThm (declName ++ last) goalTy prf
  let other := if last == `inv_step then `inv_init else `inv_step
  if (← getEnv).contains (declName ++ other) then withRef stx[3] (deriveProgram declName)

end Millipede.Meta
