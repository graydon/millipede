import Lean
import Millipede.Meta.Contracts

/-!
# `mp_auto`, the usual proof of a contract or of obligations

`mp prove f.spec := by mp_auto` and `mp prove f.safe := by mp_auto` run what a hand proof of a
client usually is, and pass it the facts such a proof usually cites.

For a contract `f.spec`, which is a `Std.WP` triple, `mp_auto` runs `vcgen` with `f` unfolded,
using the `@[spec]` of each callee that has a contract and unfolding the others. It then reduces
tuple projections and calls `grind` with the callees' contracts `g.post`, the lemmas tagged
`@[mp_auto]`, the predicates of the contract defined in the current file, and any lemmas or
definitions given as `mp_auto [lemma, …]`. The tagged lemmas include the facts of the allocator
interface, such as `Alloc.KeyStack.push` and `Alloc.Holds`, and the arenas' contracts stated in
that interface's vocabulary. The predicates are found by `contractPreds`, so that `mp_auto`
unfolds `BrInv` in `requires BrInv r`.

For obligations `f.safe`, `mp_auto` runs `mp_safe` set up exactly as the automatic attempt of
`mp def` sets it up, with the callees' `Safe'`, `req`, `exp_denote` and `post`, and adds the
tagged and given lemmas to its `grind` calls.

When `mp_auto` does not close the goal it fails and names the first goal left. That goal can then
be continued by hand, since its steps are ordinary tactics.
-/

namespace Millipede.Meta

open Lean Elab Tactic Meta

/-- The `mp def`s whose constants `f`, `f.exp`, `f.expR`, `f.fn` or `f.fnRef` occur in `e`. -/
def fnsOf (env : Environment) (e : Expr) : Array FnInfo :=
  e.getUsedConstants.foldl (init := #[]) fun acc c =>
    let cands := [c, c.getPrefix]
    match cands.findSome? fun n => match lookupEntry env n with
        | some (.fn f) => some f | _ => none with
    | some f => if acc.any (·.declName == f.declName) then acc else acc.push f
    | none => acc

/-- The `@[mp_auto]` and `@[mp_auto_fwd]` facts as `grind` parameters. -/
def taggedParams : MetaM (Array (TSyntax ``Lean.Parser.Tactic.grindParam)) := do
  let tagged ← (← labelled `mp_auto).mapM fun n =>
    `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
  return tagged ++ (← (← labelled `mp_auto_fwd).mapM fun n =>
    `(Lean.Parser.Tactic.grindParam| → $(mkCIdent n):ident))

/-- `x % n < n` for `0 < n`, at every `x % n`, which bounds the index of modular code such as
`(head + len) % n`. `grind [Nat.mod_lt]` does not instantiate `Nat.mod_lt`, because no pattern is
chosen for it. -/
theorem mod_lt_of_pos {x n : Nat} (h : 0 < n) : x % n < n := Nat.mod_lt x h
grind_pattern mod_lt_of_pos => x % n

/-- Word comparisons as comparisons of naturals, since `requires` and `ensures` use both, and the
bound of a remainder. -/
def u64Params : MetaM (Array (TSyntax ``Lean.Parser.Tactic.grindParam)) := do
  return #[← `(Lean.Parser.Tactic.grindParam| UInt64.lt_iff_toNat_lt),
    ← `(Lean.Parser.Tactic.grindParam| UInt64.le_iff_toNat_le),
    ← `(Lean.Parser.Tactic.grindParam| Millipede.Meta.mod_lt_of_pos)]

/-- The closed subterms `g a₁ … aₙ` of `e`, each once, in the order of a traversal that visits a
term before its subterms. The traversal remembers the subterms it has visited: the terms of a
verification condition share subterms heavily, since each call's result is an argument of the
next call, and a traversal of the tree without that memory is exponential in the length of such a
chain. -/
def appsOf (g : Name) (n : Nat) (e : Expr) : MetaM (Array Expr) := do
  let calls ← IO.mkRef (#[] : Array Expr)
  e.forEachWhere (fun x => x.isAppOfArity g n && !x.hasLooseBVars) fun x => calls.modify (·.push x)
  calls.get

/-- `mp_inst_posts [g, …]` adds a callee's contract at each call. For every call `g a…` of a pure
`g`, or `(g ω a…).run w` of an effectful one, in the goal or its hypotheses, it adds `g.post a…`
as a hypothesis, with its `requires` discharged by `decide`, `simp` or `omega` when it is closed,
as `cap ≤ 64` is at `cap := 1`. `grind` alone instantiates `g.post` only through the pattern of
its conclusion, so a closed premise that it cannot see would keep it from using the contract.
`mp_inst_posts keep [g, …]` leaves every premise in place, for a later tactic to discharge. -/
elab "mp_inst_posts " keep:(&"keep ")? "[" gs:ident,* "]" : tactic => withMainContext do
  let env ← getEnv
  for gId in gs.getElems do
    let g ← try realizeGlobalConstNoOverload gId catch _ => pure gId.getId
    let post := g ++ `post
    let some pci := env.find? post | continue
    let some gci := env.find? g | continue
    let arity ← forallTelescope gci.type fun xs _ => pure xs.size
    let nPost ← forallTelescope pci.type fun xs _ => pure xs.size
    -- An effectful `post : ∀ ω w x…, …` has one binder more than `g ω x…`, and the call is
    -- `.run w`.
    let eff := nPost > arity && (← forallTelescope gci.type fun _ b => pure (b.isAppOf ``StateT))
    let tgt ← instantiateMVars (← getMainTarget)
    let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d =>
      if d.isImplementationDetail then pure acc else return acc.push d.type
    let mut seen : Array (Array Expr) := #[]
    for t in #[tgt] ++ hyps do
      let t ← instantiateMVars t
      for e in ← appsOf g arity t do
        let args := e.getAppArgs
        let pargs ← if eff then
            match t.find? fun x => x.isAppOfArity ``StateT.run 6 && x.getArg! 4 == e with
            | some r => pure (some (#[args[0]!, r.getArg! 5] ++ args.extract 1 args.size))
            | none => pure none
          else pure (some args)
        let some pargs := pargs | continue
        if seen.contains pargs then continue
        seen := seen.push pargs
        let mut p := mkAppN (mkConst post (pci.levelParams.map fun _ => Level.zero)) pargs
        let pty ← whnf (← inferType p)
        if let .forallE _ R _ _ := pty then
          if keep.isNone && (← isProp R) && !R.hasLooseBVars then
            let m ← mkFreshExprMVar R
            let ok ← try
                let rest ← Elab.Term.withoutErrToSorry <| Elab.Tactic.run m.mvarId!
                  (Elab.Tactic.evalTactic (← `(tactic| first | decide | simp | omega)))
                pure rest.isEmpty
              catch _ => pure false
            if ok then p := mkApp p (← instantiateMVars m)
        let pTy ← inferType p
        let (_, mv) ← (← (← getMainGoal).assert `hpost pTy p).intro1P
        replaceMainGoal [mv]

/-- The components of a nested product type, with their projections by `Prod.fst` and
`Prod.snd`. -/
partial def prodComps (ty : Expr) (fuel : Nat := 8) : MetaM (List (Expr × (Expr → MetaM Expr))) := do
  let ty ← whnfR ty
  if fuel == 0 || !ty.isAppOfArity ``Prod 2 then return [(ty, pure)]
  let l ← prodComps (ty.getArg! 0) (fuel - 1)
  let r ← prodComps (ty.getArg! 1) (fuel - 1)
  return l.map (fun (t, p) => (t, fun e => do p (← mkAppM ``Prod.fst #[e]))) ++
    r.map (fun (t, p) => (t, fun e => do p (← mkAppM ``Prod.snd #[e])))

/-- `mp_vcgen_post [f, …]` takes loop invariants from the contract. It runs `vcgen [f, …]` on a
contract `⦃P⦄ f x ⦃fun r => Q r⦄`, and then sets each loop invariant left open, a metavariable of
type `Invariant α β _`, whose carried value has the result's type to the postcondition at the
carried value, `fun _ _ b => Q b`. That is the right invariant when the loop computes the result
and every iteration keeps `Q`, as a bound such as `result ≤ 3` on an accumulator is kept. When
the loop's state has one carried variable of the result's type, the invariant is the
postcondition at it. For a loop with `return`, whose carried state has one `Bool` component, the
flag, and one of the result's type, the value, the invariant is
`fun _ _ b => flag = true → Q value`, which suits a search loop `for … do if p i then return v`.
Any other invariant is left open, as `vcgen` leaves it. -/
elab "mp_vcgen_post " tt:(&"true ")? "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let a := tgt.getAppArgs
  let post? := if a.size ≥ 5 then some a[a.size - 2]! else none
  evalTactic (← `(tactic| vcgen [$ls,*]))
  let some post := post? | return
  let post ← instantiateMVars post
  let .lam _ dom _ _ := post | return
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``Std.WP.Invariant 3 do continue
    let α := ty.getArg! 0
    let β := ty.getArg! 1
    let lα ← mkAppM ``List #[α]
    if ← isDefEq β dom then
      let inv ← withLocalDeclD `done lα fun d => withLocalDeclD `left lα fun l =>
        withLocalDeclD `b β fun b => mkLambdaFVars #[d, l, b] (post.beta #[b]).headBeta
      if ← isDefEq (← inferType inv) ty then
        g.assign inv
      continue
    -- The state of a loop with `return` holds the return flag, the one `Bool`, and the returned
    -- value, the one component of the result's type. The invariant says that when the loop has
    -- returned the postcondition holds of the value.
    let comps ← prodComps β
    let flags := comps.filter fun (t, _) => t.isConstOf ``Bool
    let vals ← comps.filterM fun (t, _) => do return !t.isConstOf ``Bool && (← isDefEq t dom)
    let inv ← match flags, vals with
      | [(_, flag)], [(_, val)] =>
        withLocalDeclD `done lα fun d => withLocalDeclD `left lα fun l =>
          withLocalDeclD `b β fun b => do
            let f ← flag b
            let v ← val b
            let body ← mkArrow (← mkEq f (mkConst ``Bool.true)) (post.beta #[v]).headBeta
            mkLambdaFVars #[d, l, b] body
      | [], [(_, val)] =>
        -- With one carried variable of the result's type, the postcondition at it.
        withLocalDeclD `done lα fun d => withLocalDeclD `left lα fun l =>
          withLocalDeclD `b β fun b => do
            mkLambdaFVars #[d, l, b] (post.beta #[← val b]).headBeta
      | _, _ => continue
    if ← isDefEq (← inferType inv) ty then
      g.assign inv
  -- `mp_vcgen_post true` sets every invariant still open to `True`, for a loop whose state the
  -- contract does not depend on, as in a callee without a contract.
  if tt.isSome then
    for g in ← getGoals do
      if ← g.isAssigned then continue
      let ty ← instantiateMVars (← g.getType)
      unless ty.isAppOfArity ``Std.WP.Invariant 3 do continue
      let lα ← mkAppM ``List #[ty.getArg! 0]
      let inv ← withLocalDeclD `done lα fun d => withLocalDeclD `left lα fun l =>
        withLocalDeclD `b (ty.getArg! 1) fun b => mkLambdaFVars #[d, l, b] (mkConst ``True)
      if ← isDefEq (← inferType inv) ty then g.assign inv
  setGoals (← (← getGoals).filterM fun g => return !(← g.isAssigned))

/-- `mp_auto [lemmas]` proves a contract or obligations, as the module doc describes. -/
syntax (name := mpAutoTac) "mp_auto" (" [" Lean.Parser.Tactic.grindParam,* "]")?
  (ppSpace Lean.Parser.Tactic.invariantAlts)? : tactic

/-- The message for a goal `g` left by `mp_safe` with loop invariants. It is placed at the
invariant of the loop whose state components are in the context of `g` and names the components
the goal is about. It is `none` when no invariant's loop matches. -/
def invFailure (g : MVarId) (invs : Array Syntax) (left : MessageData) :
    MetaM (Option (Syntax × MessageData)) := g.withContext do
  let lctx ← getLCtx
  let tgt ← instantiateMVars (← g.getType)
  let present (x : String) : Option LocalDecl :=
    if x == "_" then none else lctx.findFromUserName? (Name.mkSimple x)
  let used ← safeInvUsedRef.get
  let scored := used.map fun (k, names) => (k, names, (names.filter (present · |>.isSome)).size)
  let some (k, names, sc) := scored.foldl (fun b c => match b with
      | some b => if c.2.2 ≥ b.2.2 then some c else some b
      | none => some c) none | return none
  let some t := invs[k]? | return none
  if sc == 0 then return none
  -- The components in the goal, or else in its last hypothesis, which is a negated goal.
  let last? := lctx.lastDecl.map (·.type)
  let inE (e : Expr) := names.filter fun x => match present x with
    | some d => e.containsFVar d.fvarId
    | none => false
  let about := if (inE tgt).isEmpty then (last?.map inE).getD #[] else inE tgt
  let about := if about.isEmpty then "" else
    " (about " ++ ", ".intercalate (about.toList.map (s!"`{·}`")) ++ ")"
  return some (t, m!"mp_auto: this loop invariant does not prove the obligations of its loop or \
    is not kept by an iteration{about}; left:\n{left}")

@[tactic mpAutoTac] def evalMpAuto : Tactic := fun stx => do
  unfoldGoalDef
  withMainContext do
  let extra : Array (TSyntax ``Lean.Parser.Tactic.grindParam) :=
    if stx[1].isNone then #[] else stx[1][1].getSepArgs.map (⟨·⟩)
  let invs? : Option (TSyntax ``Lean.Parser.Tactic.invariantAlts) :=
    if stx[2].isNone then none else some ⟨stx[2][0]⟩
  let env ← getEnv
  let goal ← instantiateMVars (← getMainTarget)
  let tagged ← taggedParams
  let u64 ← u64Params
  let gparam (n : Name) := `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
  -- The contract's own predicates, such as `BrInv`, unfolded.
  let extra := extra ++ (← (← contractPreds goal).mapM gparam)
  let simpLemma (n : Name) := `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  -- Obligations, a goal about `Exp.safe` of `f.exp` or of the relaxed `f.expR`.
  let safeOf? := goal.find? fun e => e.isAppOf ``Exp.safe
  if let some se := safeOf? then
    let term := se.getArg! 3
    let some tn := term.getAppFn.constName? | throwError "mp_auto: the obligations of a term that is not \
      an `mp def`'s"
    -- The function need not be registered yet, since `mp def`'s own attempt runs before.
    let some v := (env.find? tn).bind (·.value?) | throwError "mp_auto: `{tn}` is not an \
      `mp def`'s term"
    let callees := (fnsOf env v).filter (·.declName != tn.getPrefix)
    -- `mp_safe`'s own `grind` calls get only the callees' contracts, since with the tagged lemmas
    -- they can run out of heartbeats, which `try` does not catch. What is left gets them all.
    evalTactic (← safeCall callees tn #[← simpLemma ``Lens.fst, ← simpLemma ``Lens.snd]
      (u64 ++ extra) invs?)
    let posts ← (callees.filter fun g => env.contains (g.declName ++ `post)).mapM fun g =>
      gparam (g.declName ++ `post)
    let gs := posts ++ u64 ++ extra ++ tagged
    let withPost := (callees.filter fun g => env.contains (g.declName ++ `post)).map
      fun g => mkCIdent g.declName
    evalTactic (← `(tactic| all_goals (try mp_inst_posts [$withPost,*])))
    if let some (t, m) ← safeInvErrRef.get then
      safeInvErrRef.set none
      throwErrorAt t m!"mp_auto: this loop invariant does not elaborate at its loop's state: {m}"
    -- With invariants, the goal left is reported at the invariant of its loop.
    if invs?.isSome then
      evalTactic (← `(tactic| all_goals (try (first | grind +splitImp [$gs,*] | grind [$gs,*]))))
    else
      evalTactic (← `(tactic| all_goals (first | grind +splitImp [$gs,*] | grind [$gs,*])))
    if let (some invs, some g) := (invs?, (← getUnsolvedGoals).head?) then
      if let some (t, m) ← invFailure g (invariantTerms invs) (← goalSummary g) then
        throwErrorAt t m
  else
    -- A contract, whose triple's program is an `mp def` applied to the parameters. A generic
    -- module's `M.f`, abstracted over the implementation, is not registered, and is recognised
    -- by its contract's goal `M.f.SpecGoal`.
    let some f := (fnsOf env goal)[0]?.map (·.declName) <|>
        goal.getUsedConstants.find? fun c => env.contains (c ++ `SpecGoal)
      | throwError "mp_auto: the goal is neither a contract nor obligations of an `mp def`"
    let callees ← calleesOf f
    let unfold := callees.filter fun g => !env.contains (g ++ `spec)
    let ids ← (#[f] ++ unfold).mapM simpLemma
    -- The contracts of the functions that `f` calls, registered or generic.
    let called := ((env.find? f).bind (·.value?)).map (·.getUsedConstants) |>.getD #[]
    let posts ← (called.filter fun g => g != f && env.contains (g ++ `post)).mapM fun g =>
      gparam (g ++ `post)
    let gs := posts ++ tagged ++ u64 ++ extra
    let withPost := (called.filter fun g => g != f && env.contains (g ++ `post)).map mkCIdent
    let run (vc : TSyntax `tactic) : TacticM Unit := do
      evalTactic (← `(tactic| (
        intros
        $vc:tactic
        all_goals (try (set_option linter.unusedSimpArgs false in simp only [Option.getD_some] at *))
        all_goals (try mp_inst_posts [$withPost,*])
        -- In a loop over `List.range n` the counter is below `n`.
        all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›)
        all_goals (try (first | grind [$gs,*] | grind +splitImp [$gs,*])))))
    -- A contract about events is proved from the live world whose history is `history`
    -- (`mp_history`), so that an invariant can state the events so far. The worlds are reduced
    -- and the events compared with `simp_all`, unfolding the definitions that `ensures` names.
    let isEvent := (← eventParts' goal).isSome
    let runE (vc : TSyntax `tactic) : TacticM Unit := do
      let defs ← (#[``World.call, ``World.ask, ``Call.event, ``fitOut, ``UInt64.ofNat_add_one_sub]
        ++ (← contractDefs goal)).mapM simpLemma
      let gsE := gs.push (← gparam ``vrange_one)
      evalTactic (← `(tactic| (
        mp_history
        $vc:tactic
        -- A callee's event contract leaves the rest under its binders `r evs e`.
        all_goals (try (repeat' (first | (apply And.intro) | mp_world_branch | intro _ |
          ((try simp only [binderNameHint]); vcgen [$ids,*]))))
        all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›)
        all_goals (try subst_vars)
        all_goals (try simp_all [$defs,*])
        all_goals (try (first | grind [$gsE,*] | grind +splitImp [$gsE,*])))))
    match invs? with
    | some i =>
      if isEvent then runE (← `(tactic| vcgen [$ids,*] $i))
      else run (← `(tactic| vcgen [$ids,*] $i))
    | none =>
      if isEvent then runE (← `(tactic| mp_vcgen_post [$ids,*]))
      else
        -- The invariants from the postcondition, then `True` for those still open.
        let s0 ← saveState
        run (← `(tactic| mp_vcgen_post [$ids,*]))
        -- Only when an invariant is still open.
        let openInv ← (← getUnsolvedGoals).anyM fun g => return (← instantiateMVars (← g.getType)).hasExprMVar
        if openInv then
          let s1 ← saveState
          s0.restore
          run (← `(tactic| mp_vcgen_post true [$ids,*]))
          unless (← getUnsolvedGoals).isEmpty do s1.restore
  let gs ← getUnsolvedGoals
  if let some g := gs.head? then
    let left ← goalSummary g
    throwError "mp_auto: a goal is left:\n{left}{keyStackHint left}"

end Millipede.Meta
