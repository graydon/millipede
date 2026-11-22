import Lean
import Millipede.Meta.Elab
import Millipede.Meta.Spec

/-!
# Contracts

`mp def f … requires P ensures Q` states a postcondition `Q` of `f`. `Q` is a Lean proposition
about the parameters, which are their values at the call, about `result`, the value returned, and
for each `&mut` parameter `p` about `p'`, its final value. `mp def` elaborates the function as it
would without `ensures` and then generates two theorems.

- `f.spec : ∀ x…, ⦃P⦄ f x… ⦃fun r => Q⦄`, or `∀ ω x…, ⦃fun _ => P⦄ f ω x… ⦃fun r _ => Q⦄` for an
  effectful `f`, tagged `@[spec]`. A caller's `vcgen` uses it at every call and never unfolds
  `f`, so its precondition becomes a verification condition there and its postcondition a
  hypothesis. `P` is the full `requires` of `f.safe`, including what every caller guarantees of
  a slice argument.
- `f.post : ∀ x…, P → Q[(f x…).run]`, or `∀ ω w x…, P → Q[((f ω x…).run w).1]` for an effectful
  `f`, which states the same fact about the value. The automatic attempt at a caller's
  obligations and hand proofs cite it.

`requires` is the precondition of both `f.safe` and `f.spec`. `f.safe` says that the obligations
of the body of `f` hold under it, a structural fact about the Core term proved by `mp_safe`, and
`f.spec` says that `ensures` holds of the result under it, a triple about the normal form proved
by `vcgen`. They are separate theorems because the Core term carries the obligations and the
normal form does not. Both use a callee's contract instead of unfolding the callee, since
`mp_safe` closes the callee's `requires` at a call from the caller's context with `g.post` of the
calls before it, and `vcgen` uses `g.spec`. A call whose arguments violate `requires` leaves an
obligation that cannot be discharged in `f.SafeGoal` and in the verification condition of
`f.spec`.

An effectful function's `ensures` may also name `history`, the events before the call, `events`,
the events it appends, and `exited`, whether it ends halted. Such an event contract has the goal
`f.SpecGoal : ∀ ω x… Q, ⦃fun w => P ∧ w.halted = false ∧ ∀ r evs e, E → Q r ⟨w.events ++ evs, e⟩⦄
f ω x… ⦃Q⦄`, about a live world. `f.spec` adds that from a halted world nothing changes
(`Spec.EventPreH`, `fullEventSpec`), and `f.post : ∀ ω h x…, P → ∃ evs, …` is about a run from
the world `⟨h, false⟩` (`Spec.runE_of_triple`). The design is in doc/phases/ensures-events.md.

The specification is proved automatically with `vcgen [f]`, which uses the specifications of the
callees that have one and unfolds the others, followed by `grind`. When that fails, because a loop
needs an invariant or a fact needs a lemma, the goal is left as `f.SpecGoal` with a message, for
`mp prove f.spec := …`, as for `f.safe`. The option `mp.autoSpec false` skips the attempt.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta Std.WP

/-- `mp def f (x : T) (p : &mut S) requires P ensures Q : R := body` defines a function with a
contract, where `Q` is stated over the parameters, `result`, and `p'`, the final value of `p`. It
generates `f.spec` and `f.post` besides what `mp def` generates. -/
syntax (name := mpDefEns) (docComment)? mpKw "def " ident (ppSpace mpBinder)*
  (&" requires " term)? " ensures " term " : " term " := " term : command

register_option mp.autoSpec : Bool := {
  defValue := true
  descr := "`mp def … ensures` tries to prove the contract (`f.spec`) with `vcgen` and `grind`; \
    when false only `f.SpecGoal` is defined, for `mp prove f.spec`"
}

/-- The type of `f.spec`. The parameters and the `requires` are those of `f.SafeGoal`. -/
def contractOf (info : FnInfo) (ens : Syntax) : TermElabM Expr := do
  let some goalTy := ((← getEnv).find? (info.declName ++ `SafeGoal)).bind (·.value?)
    | throwError "`{info.declName}` has no `SafeGoal`"
  -- A generic function is taken at the variables in scope.
  let gvs ← genVarsRef.get
  let goalTy := goalTy.beta gvs
  let info := if info.nGen > 0 then info.instantiate gvs else info
  let n := info.params.size
  forallTelescope goalTy fun ys _ => do
    let xs := ys.extract 2 (2 + n)
    let R ← match ys[2 + n]? with
      | some h => inferType h
      | none => pure (mkConst ``True)
    let fArgs := if info.isPure then xs else #[ys[0]!] ++ xs
    let prog := mkAppN (← gc info.declName) fArgs
    let α := (← inferType prog).appArg!
    let muts := info.params.toList.filterMap fun (x, t, m) =>
      if m == .mut then some (Name.mkSimple (x.toString ++ "'"), t.carrier) else none
    withLocalDeclD `result info.ret.carrier fun res =>
    withLocalDeclsDND muts.toArray fun outs =>
    -- An effectful function's `ensures` may also name the history before the call, the events
    -- it appends and whether it ends halted.
    let evNames := if info.isPure then #[] else
      #[(`history, mkApp (mkConst ``List [.zero]) (mkConst ``Event)),
        (`events, mkApp (mkConst ``List [.zero]) (mkConst ``Event)), (`exited, mkConst ``Bool)]
    withLocalDeclsDND evNames fun evs => do
      let Q ← elabTermEnsuringType ens (mkSort .zero)
      synthesizeSyntheticMVarsNoPostponing
      let Q ← instantiateMVars Q
      withLocalDeclD `r α fun r => do
        -- `r = (result, (pₖ', … (p₁', ())))`, which holds the final values of the `&mut`
        -- parameters in context order, last parameter first.
        let resE ← if info.isRef then mkAppM ``Prod.fst #[r] else pure r
        let mut tup ← if info.isRef then mkAppM ``Prod.snd #[r] else pure r
        let mut vals : Array Expr := #[]
        for _ in muts do
          vals := vals.push (← mkAppM ``Prod.fst #[tup])
          tup ← mkAppM ``Prod.snd #[tup]
        let Qr := Q.replaceFVars (#[res] ++ outs) (#[resE] ++ vals.reverse)
        let (RS, progS) := (← exprToSyntax R, ← exprToSyntax prog)
        if evs.any (Q.containsFVar ·.fvarId!) then
          -- An event contract: `∀ Q, ⦃Spec.EventPre R E Q⦄ f ω x… ⦃Q⦄`, unfolded.
          let ES ← exprToSyntax (← mkLambdaFVars (#[r] ++ evs) Qr)
          let tri ← `(∀ Q : $(← exprToSyntax α) → Millipede.World → Prop,
            ⦃fun w => $RS ∧ w.halted = false ∧
              ∀ r evs e, $ES r w.events evs e → Q r ⟨w.events ++ evs, e⟩⦄ $progS ⦃Q⦄)
          let tri ← elabTermEnsuringType tri (mkSort .zero)
          synthesizeSyntheticMVarsNoPostponing
          return ← mkForallFVars fArgs (← Core.betaReduce (← instantiateMVars tri))
        let post ← mkLambdaFVars #[r] Qr
        let postS ← exprToSyntax post
        let tri ← if info.isPure then `(⦃$RS⦄ $progS ⦃$postS⦄)
          else `(⦃fun _ => $RS⦄ $progS ⦃fun r _ => $postS r⦄)
        let tri ← elabTermEnsuringType tri (mkSort .zero)
        synthesizeSyntheticMVarsNoPostponing
        mkForallFVars fArgs (← instantiateMVars tri)

/-- The parts of an event contract `⦃fun w => R ∧ w.halted = false ∧ ∀ r evs e, E' → …⦄ prog ⦃Q⦄`,
or of the form of `f.spec`, `⦃fun w => (w.halted = false → R ∧ ∀ r evs e, E' → …) ∧ …⦄ prog ⦃Q⦄`,
under the binder `Q`: the program, the `requires` `R`, and `E := fun r h evs e => E'[h/w.events]`. -/
def eventParts (tri : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let a := tri.getAppArgs
  unless tri.isAppOf ``Std.WP.Triple && a.size ≥ 5 do return none
  let (prog, pre) := (a[a.size - 5]!, a[a.size - 3]!)
  lambdaTelescope pre fun ws body => do
    let #[w] := ws | return none
    let isLive (e : Expr) : Bool := match e.eq? with
      | some (_, lhs, _) => lhs.isAppOfArity ``World.halted 1 && lhs.appArg! == w
      | none => false
    let some (a, rest) := body.and? | return none
    -- The form of `f.spec`, `Spec.EventPreH`, `(w.halted = false → R ∧ imp) ∧ …`, or that of
    -- `f.SpecGoal`, `Spec.EventPre`, `R ∧ w.halted = false ∧ imp`.
    let (R, imp) ← match a with
      | .forallE _ d b _ =>
        if isLive d && !b.hasLooseBVars then
          let some p := b.and? | return none
          pure p
        else pure (a, rest)
      | _ => pure (a, rest)
    let imp ← if R == a then
        let some (live, imp) := rest.and? | return none
        unless isLive live do return none
        pure imp
      else pure imp
    forallBoundedTelescope imp (some 3) fun rs E' => do
      let #[r, evs, e] := rs | return none
      let E' := E'.bindingDomain!
      withLocalDeclD `history (← inferType evs) fun h => do
        let E' := E'.replace fun x =>
          if x.isAppOfArity ``World.events 1 && x.appArg! == w then some h else none
        return some (prog, R, ← mkLambdaFVars #[r, h, evs, e] E')

/-- The parts of an event contract `f.spec`, under its binders, or `none` for another contract. -/
def eventParts' (specTy : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  forallTelescope specTy fun _ tri => eventParts tri

open Lean.Elab.Tactic in
/-- `mp_history` begins a proof of an event contract whose body has a loop. It introduces the
binders of the goal, and then turns the triple for every postcondition into a triple about the run
from the live world whose history is `history`, under the `requires` (`Spec.eventSpec_of_hist`).
The postcondition is then `∃ evs, w.events = history ++ evs ∧ E`, and a loop invariant can name
`history`, as in `fun done left acc w => w = ⟨history ++ …, false⟩`. -/
elab "mp_history" : tactic => do
  evalTactic (← `(tactic| intros))
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (prog, R, E) ← eventParts tgt
    | throwError "mp_history: the goal is not a contract about events"
  let α := (← inferType prog).appArg!
  let lem := mkAppN (mkConst ``Spec.eventSpec_of_hist) #[α, R, prog, E]
  let gs ← (← getMainGoal).apply lem
  replaceMainGoal gs
  evalTactic (← `(tactic| intro $(mkIdent `history):ident _))

open Lean.Elab.Tactic in
/-- `mp_world_branch` takes a branch `X.halted = b → G` of a callee's event contract (the
precondition `Spec.EventPreH`). It introduces the hypothesis and closes the branch when the
hypotheses contradict it, as after a callee that cannot exit; otherwise `G` is left, as after a
callee that may exit. It fails on a goal of another shape. -/
elab "mp_world_branch" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let .forallE _ d _ _ := tgt | throwError "mp_world_branch: not a branch on the world"
  let some (_, l, _) := d.eq? | throwError "mp_world_branch: not a branch on the world"
  unless l.isAppOfArity ``World.halted 1 do throwError "mp_world_branch: not a branch on the world"
  evalTactic (← `(tactic| (intro hh; first | (exfalso; simp_all; done) | skip)))

/-- The definitions that an event contract names and that are neither functions of the program
nor predicates (which `contractPreds` finds): the calls and events it states, and functions such
as the events of the first `k` iterations of a loop. The automatic attempt unfolds them. They are
the definitions of the current file, and imported ones that state a call or an event (their type
ends in `Call` or `Event`) or a constant such as the bytes of a message, outside Lean's own
library. -/
def contractDefs (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let isDef (n : Name) : MetaM Bool := do
    let some (.defnInfo v) := env.find? n | return false
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if [`Init, `Std, `Lean].contains mod.getRoot then return false
      let ok ← forallTelescopeReducing v.type fun xs b => do
        let b ← whnfR b
        return b.isConstOf ``Call || b.isConstOf ``Event || (xs.isEmpty && !(← isProp b))
      unless ok do return false
    if n.isInternal || isMatcherCore env n || (lookupEntry env n).isSome then return false
    -- A structural recursion is unfolded by its equations, which fire at a constructor; a
    -- well-founded one is not.
    if v.value.getUsedConstants.any (fun c => c == n || (c.isStr && c.getString! == "fix")) then
      return false
    forallTelescopeReducing v.type fun _ b => return !b.isProp
  let mut out : Array Name := #[]
  let mut seen : Array Name := #[]
  let mut todo := e.getUsedConstants.toList
  let mut fuel := 1024
  while fuel > 0 do
    fuel := fuel - 1
    let c :: rest := todo | break
    todo := rest
    if seen.contains c then continue
    seen := seen.push c
    -- The definitions found are followed, and so are the auxiliary definitions of this file
    -- that a recursion or a `match` compiles to.
    let isAux := (env.getModuleIdxFor? c).isNone && (c.isInternal || isMatcherCore env c)
    if ← isDef c then out := out.push c
    else unless isAux do continue
    if let some v := (env.find? c).bind (·.value?) then todo := todo ++ v.getUsedConstants.toList
  return out

/-- The conjuncts of `e`. -/
partial def eventConjuncts (e : Expr) : List Expr := match e.and? with
  | some (a, b) => eventConjuncts a ++ eventConjuncts b
  | none => [e]

/-- The default loop invariant of an event contract `events = t ∧ …` of a function whose loops
run over `upto N`: the events so far are `t` with the bound `N` replaced by the number of
iterations done. For each such `N` that `t` names it gives `fun ω x… history k => t[N := k]`,
closed, for the invariant `fun done _ _ w => w = ⟨history ++ lam ω x… history done.length, false⟩`.
-/
def eventLoopInvariants (declName : Name) (specTy : Expr) : MetaM (Array Expr) := do
  let some v := ((← getEnv).find? declName).bind (·.value?) | return #[]
  -- The bounds of the loops.
  let mut bounds : Array Nat := #[]
  let ups := collectApps v ``upto
  for u in ups do
    if let some n ← evalNat (u.getArg! 0) then
      unless bounds.contains n do bounds := bounds.push n
  if bounds.isEmpty then return #[]
  forallTelescope specTy fun args tri => do
    let some (_, _, E) ← eventParts tri | return #[]
    let fArgs := args.pop
    lambdaTelescope E fun rs body => do
      let #[r, h, evs, e] := rs | return #[]
      let rhs (c : Expr) : Option Expr := match c.eq? with
        | some (_, l, t) => if l == evs then some t else none
        | none => none
      let some t := (eventConjuncts body).findSome? rhs | return #[]
      if t.containsFVar r.fvarId! || t.containsFVar e.fvarId! then return #[]
      let mut out := #[]
      for n in bounds do
        let lam ← withLocalDeclD `k (Lean.mkConst ``Nat) fun k => do
          let t' ← Meta.transform t (pre := fun x => do
            if x.isAppOfArity ``OfNat.ofNat 3 && x.getArg! 0 == Lean.mkConst ``Nat then
              if (← evalNat x) == some n then return .done k
            return .continue)
          if t' == t then return none
          return some (← mkLambdaFVars (fArgs ++ #[h, k]) t')
        if let some l := lam then out := out.push l
      return out
where
  -- The applications of `c` in `e`.
  collectApps (e : Expr) (c : Name) : Array Expr := Id.run do
    let mut acc := #[]
    let mut todo := [e]
    let mut fuel := 100000
    while fuel > 0 do
      fuel := fuel - 1
      let x :: rest := todo | break
      todo := rest
      if x.isAppOfArity c 1 then acc := acc.push x
      match x with
      | .app f a => todo := f :: a :: todo
      | .lam _ d b _ | .forallE _ d b _ => todo := d :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => todo := b :: todo
      | _ => pure ()
    return acc

/-- `f.post` of an event contract and its proof as a function of the proof of `f.spec`:
`∀ ω h x…, R → ∃ evs, ((f ω x…).run ⟨h, false⟩).2.events = h ++ evs ∧ E …`, by
`Spec.runE_of_triple`. `none` for a contract that is not about events. -/
def postOfEventSpec (specTy : Expr) : TermElabM (Option (Expr × Expr)) :=
  forallTelescope specTy fun args tri => do
    let some (prog, R, E) ← eventParts tri | return none
    let fArgs := args.pop
    let α := (← inferType prog).appArg!
    withLocalDeclD `h (mkApp (mkConst ``List [.zero]) (mkConst ``Event)) fun h =>
    withLocalDeclD `hs specTy fun hs => withLocalDeclD `hr R fun hr => do
      let hasReq := !R.isConstOf ``True
      let hp := if hasReq then hr else mkConst ``True.intro
      let prf := mkAppN (mkConst ``Spec.runE_of_triple) #[α, R, prog, E, mkAppN hs fArgs, hp, h]
      let concl ← Core.betaReduce (← instantiateMVars (← inferType prf))
      let binders := #[fArgs[0]!, h] ++ fArgs.extract 1 fArgs.size ++ (if hasReq then #[hr] else #[])
      return some (← mkForallFVars binders concl,
        ← mkLambdaFVars #[hs] (← mkLambdaFVars binders prf))

/-- `f.post` and its proof as a function of the proof of `f.spec`, from the type of `f.spec`. -/
def postOfSpec (info : FnInfo) (specTy : Expr) : TermElabM (Expr × Expr) := do
  if let some r ← postOfEventSpec specTy then return r
  forallTelescope specTy fun fArgs tri => do
    let a := tri.getAppArgs
    let (prog, pre, post) := (a[a.size - 5]!, a[a.size - 3]!, a[a.size - 2]!)
    let xs := if info.isPure then fArgs else fArgs.extract 1 fArgs.size
    withLocalDeclD `w (mkConst ``World) fun w => do
      let (R, Q) ← if info.isPure then pure (pre, post) else do
        pure ((mkApp pre w).headBeta, ← withLocalDeclD `r (← inferType post).bindingDomain! fun r =>
          do mkLambdaFVars #[r] (mkApp2 post r w).headBeta)
      let val ← if info.isPure then mkAppM ``Id.run #[prog]
        else do mkAppM ``Prod.fst #[← mkAppM ``StateT.run #[prog, w]]
      let concl := (Q.beta #[val]).headBeta
      let binders := if info.isPure then xs else #[fArgs[0]!, w] ++ xs
      let hasReq := !R.isConstOf ``True
      withLocalDeclD `hs specTy fun hs => withLocalDeclD `h R fun h => do
        let hApp := mkAppN hs fArgs
        let prf ← if info.isPure then mkAppM ``Spec.run_of_triple #[hApp, h]
          else mkAppM ``Spec.runM_of_triple #[hApp, h, w]
        let prf := if hasReq then prf else prf.replaceFVar h (mkConst ``True.intro)
        let hb := if hasReq then #[h] else #[]
        return (← mkForallFVars (binders ++ hb) concl,
          ← mkLambdaFVars #[hs] (← mkLambdaFVars (binders ++ hb) prf))

/-- The `mp def`s that a normal form calls, which are the constants of its value that are
registered functions. -/
def calleesOf (declName : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let some v := (env.find? declName).bind (·.value?) | return #[]
  return v.getUsedConstants.filter fun c =>
    c != declName && (match lookupEntry env c with | some (.fn _) => true | _ => false)

/-- The `f.spec` of an event contract, which holds from every world, and its proof, from the
contract from live worlds `specTy` (the goal `f.SpecGoal`) and its proof `prf`: the precondition
is `Spec.EventPreH`, unfolded, by `Spec.eventSpecH` with `f.exp_denote` and `Exp.denote_halted`.
`none` for another contract, or a function without `f.exp_denote`. -/
def fullEventSpec (declName : Name) (specTy prf : Expr) : TermElabM (Option (Expr × Expr)) := do
  unless (← getEnv).contains (declName ++ `exp_denote) do return none
  forallTelescope specTy fun args tri => do
    let some (prog, R, E) ← eventParts tri | return none
    let fArgs := args.pop
    let α := (← inferType prog).appArg!
    -- From a halted world the run changes nothing.
    let hhTy ← withLocalDeclD `w (mkConst ``World) fun w => do
      let hw ← mkEq (mkApp (mkConst ``World.halted) w) (mkConst ``Bool.true)
      let concl ← mkEq (← mkAppM ``Prod.snd #[← mkAppM ``StateT.run #[prog, w]]) w
      mkForallFVars #[w] (← mkArrow hw concl)
    let den := mkCIdent (declName ++ `exp_denote)
    let tac ← `(tactic| (intro w hw; rw [← $den:ident]; exact Millipede.Exp.denote_halted _ _ _ _ hw))
    let some hh ← tryProve hhTy tac | return none
    let prfH := mkAppN (mkConst ``Spec.eventSpecH) #[α, R, prog, E, mkAppN prf fArgs, hh, args.back!]
    let ty ← deltaExpand (← inferType prfH) (· == ``Spec.EventPreH)
    let ty ← Core.betaReduce (← instantiateMVars ty)
    return some (← mkForallFVars args ty, ← mkLambdaFVars args prfH)

/-- Add `f.spec`, tagged `@[spec]`, and `f.post`. For an event contract, `f.spec` holds from every
world (`fullEventSpec`), and `f.post` is derived from it through `Spec.eventSpec_live`. -/
def addContractDecls (info : FnInfo) (specTy prf : Expr) : TermElabM Unit := do
  let declName := info.declName
  let short := declName.componentsRev.head!
  let (postTy, postPrf) ← postOfSpec info specTy
  let full ← fullEventSpec declName specTy prf
  let (ty, p) := full.getD (specTy, prf)
  addThm (declName ++ `spec) ty p
  addDocStringCore (declName ++ `spec) s!"The contract of `{short}`: under its `requires`, its \
    `ensures` holds (a `vcgen` specification)."
  let spec ← gc (declName ++ `spec)
  -- `f.post` cites `f.spec`, at the contract from live worlds.
  let live ← if full.isNone then pure spec else
    forallTelescope specTy fun args tri => do
      let some (prog, R, E) ← eventParts tri | return spec
      let α := (← inferType prog).appArg!
      mkLambdaFVars args.pop (mkAppN (mkConst ``Spec.eventSpec_live)
        #[α, R, prog, E, mkAppN spec args.pop])
  addThm (declName ++ `post) postTy (postPrf.beta #[live])
  addDocStringCore (declName ++ `post) s!"The contract of `{short}` as a fact about its value."

/-- Elaborate `mp def … ensures Q`. -/
@[command_elab mpDefEns] def elabMpDefEns : CommandElab := fun stx => do
  -- The triples are stated with the instances of `Std.WP`, which `open Std.WP` brings in, and
  -- proved with `vcgen`.
  unless (← getOpenDecls).any (fun | .simple ns _ => ns == `Std.WP | _ => false) &&
      (← getOptions).getBool `experimental.vcgen do
    return ← elabCommand (← `(set_option experimental.vcgen true in open Std.WP in $(⟨stx⟩):command))
  -- `result` and `p'` name the result and the final value of `&mut p` in `ensures`, so a
  -- parameter of that name would be shadowed.
  let ps := stx[4].getArgs.flatMap fun b => b[1].getArgs.map (·, b[3].getKind == ``mpRefMut)
  for (x, _) in ps do
    if x.getId == `result then
      throwErrorAt x "a function with `ensures` cannot have a parameter named `result`: in \
        `ensures`, `result` is the value returned"
    -- In the `ensures` of a function that makes calls, these name the events.
    if [`history, `events, `exited].contains x.getId then
      throwErrorAt x "a function with `ensures` cannot have a parameter named `{x.getId}`: in \
        the `ensures` of a function that makes calls, `history` is the events before the call, \
        `events` the events it appends and `exited` whether it ends by `exit`"
    if let some (y, _) := ps.find? fun (y, m) => m && x.getId == Name.mkSimple (y.getId.toString ++ "'") then
      throwErrorAt x "a function with `ensures` cannot have a parameter named `{x.getId}`: in \
        `ensures`, `{x.getId}` is the final value of the `&mut` parameter `{y.getId}`"
  -- The `mp def` without `ensures`.
  let a := stx.getArgs
  let base := Syntax.node stx.getHeadInfo ``mpDef ((a.extract 0 6) ++ (a.extract 8 12))
  ensuresStxRef.set (some stx[7])
  try withGenVars stx (elabMpDefCore base)
  catch e =>
    ensuresStxRef.set none
    failedDefs.modify (·.insert ((← getCurrNamespace) ++ stx[3].getId))
    throw e
  ensuresStxRef.set none
  let declName := (← getCurrNamespace) ++ stx[3].getId
  let some (.fn info) := lookupEntry (← getEnv) declName | return
  unless info.hasNf do
    throwErrorAt stx[6] "`ensures` is about the normal form: `{stx[3].getId}` has none \
      (`mp.normalForm false`)"
  let proved ← withGenVars stx (force := info.nGen > 0) do
    withFnGenVars info do
    let gvs ← genVarsRef.get
    let info := if info.nGen > 0 then info.instantiate gvs else info
    let specTy ← contractOf info stx[7]
    let opts ← getOptions
    let hasLoop := ((← getEnv).find? declName).bind (·.value?) |>.any
      (·.getUsedConstants.contains ``forIn)
    let eventLoop := (← eventParts' specTy).isSome && hasLoop
    let prfE : Except String Expr ← if !mp.autoSpec.get opts then pure (.error "") else do
      let env ← getEnv
      let unfold := (← calleesOf declName).filter fun g => !env.contains (g ++ `spec)
      let ids ← (#[declName] ++ unfold).mapM fun n =>
        `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
      let preds ← (← contractPreds specTy).mapM fun n =>
        `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
      let tac ← if (← eventParts' specTy).isNone then
          `(tactic| (intros; vcgen [$ids,*]; all_goals (try grind [$preds,*])))
        else
          -- An event contract: the worlds are reduced and the events compared with `simp_all`,
          -- unfolding the definitions of this file that `ensures` names, such as a call.
          let defs ← (#[``World.call, ``World.ask, ``Call.event, ``fitOut] ++ (← contractDefs specTy)).mapM fun n =>
            `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
          let red ← `(tactic| simp_all [$defs,*])
          -- A callee's event contract leaves the rest of the caller under its binders `r evs e`
          -- in the verification condition, where `vcgen` resumes after `intro`.
          let vc ← `(tactic| repeat' (first | (refine ⟨?_, ?_⟩) | mp_world_branch | intro _ |
            ((try simp only [binderNameHint]); vcgen [$ids,*])))
          let fin ← `(tactic| all_goals (try grind [$preds,*]))
          `(tactic| (intros; vcgen [$ids,*]; all_goals ($vc:tactic); all_goals (try $red:tactic); $fin:tactic))
      let budget := mp.autoSafe.maxHeartbeats.get opts * 1000
      let attempt (tac : Syntax) := withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
          tryProveE specTy tac
      -- An event contract over a loop goes to `mp_auto`, which states it from the history
      -- before the call: first with the invariant "the events so far are the contract's events
      -- at the number of iterations done" (`eventLoopInvariants`), then with the contract as the
      -- loop's invariant.
      if eventLoop then do
        let xs : Array Ident := #[mkIdent `ω] ++ info.params.map fun (x, _, _) => mkIdent x
        let xts : Array Term := xs.map fun x => ⟨x.raw⟩
        -- `history` is the name that `mp_history` introduces, outside this quotation.
        let hist := mkIdent `history
        let mut res : Except String Expr := .error ""
        for lam in ← eventLoopInvariants declName specTy do
          let lamS ← exprToSyntax lam
          -- `mp_auto` is defined later (Auto.lean), so its syntax is built by its kind.
          let v ← `(tactic| vcgen invariants
            · fun done _ _ w => w = ⟨$hist ++ $lamS $xts* $hist done.length, false⟩)
          let some alts := v.raw.find? (·.getKind == ``Lean.Parser.Tactic.invariantAlts)
            | continue
          let auto : Syntax := Syntax.node .none `Millipede.Meta.mpAutoTac
            #[Syntax.atom .none "mp_auto", mkNullNode, mkNullNode #[alts]]
          let tac ← `(tactic| (intro $xs*; $(⟨auto⟩):tactic))
          if let .ok p ← attempt tac then
            res := .ok p
            break
        if res matches .ok _ then pure res else attempt mpAutoSyntax
      else do
      match ← attempt tac with
      | .ok p => pure (.ok p)
      | .error left =>
        -- Then `mp_auto`, with the callees' contracts as facts and the `@[mp_auto]` lemmas.
        match ← attempt mpAutoSyntax with
        | .ok p => pure (.ok p)
        | .error _ => pure (.error left)
    match prfE with
    | .ok prf =>
      withCurrHeartbeats <| addContractDecls info specTy prf
      return true
    | .error left =>
      let left := if left.isEmpty then "" else s!"; left:\n{left}"
      let goalName := declName ++ `SpecGoal
      addDef goalName (mkSort .zero) specTy (compile := false)
      addDocStringCore goalName s!"The contract of `{stx[3].getId}` (doc/design/obligations.md)."
      let f := stx[3].getId
      if mp.autoSpec.get opts then
        if eventLoop then
          let xs := ["ω"] ++ info.params.toList.map fun (x, _, _) => x.toString.replace "." "_"
          logInfoAt stx[3] m!"the contract of `{f}` was not proved automatically: a loop needs \
            an invariant (a fact about the counters done, the counters left, the carried value \
            and the world, true before and after every iteration; the contract at the carried \
            value was tried and is not one). Prove it with\n  mp prove {f}.spec := by\n    \
            intro {" ".intercalate xs}; mp_auto invariants\n    \
            · fun done left acc w => w = ⟨history ++ …, false⟩\n\
            (`history`: the events before the call; the goal is `{f}.SpecGoal`){left}"
        else if (left.splitOn "⊢ ?inv").length > 1 then
          -- A loop invariant is open, so the message says so and gives the proof's shape.
          let xs := (if info.isPure then [] else ["ω"]) ++
            info.params.toList.map fun (x, _, _) => x.toString.replace "." "_"
          let intro := if xs.isEmpty then "" else s!"intro {" ".intercalate xs}; "
          let env ← getEnv
          let unf := (← calleesOf declName).filter fun g => !env.contains (g ++ `spec)
          let ns ← getCurrNamespace
          let unf := ", ".intercalate ((#[f] ++ unf.map (·.replacePrefix ns .anonymous)).toList.map
            toString)
          logInfoAt stx[3] m!"the contract of `{f}` was not proved automatically: a loop needs \
            an invariant (a fact about the counters done, the counters left and the carried \
            value, true before and after every iteration; the postcondition at the carried value \
            was tried and is not one). Prove it with\n  mp prove {f}.spec := by\n    \
            {intro}vcgen [{unf}] invariants\n    · fun done left acc => …\n    \
            all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind\n\
            (`range_split`: the counter is below the bound; the goal is `{f}.SpecGoal`){left}"
        else
          logInfoAt stx[3] m!"the contract of `{f}` was not proved automatically; prove \
            it with `mp prove {f}.spec := …` (the goal is `{f}.SpecGoal`){left}\
            {keyStackHint left}"
      return false
  if proved then
    elabCommand (← `(attribute [spec] $(mkCIdent (declName ++ `spec))))

/-- `mp prove f.spec := proof` proves the contract of `f` when `mp def` could not. -/
def elabMpProveSpec (stx : Syntax) : CommandElabM Unit := do
  let target := stx[3].getId
  let fId := mkIdentFrom stx[3] target.getPrefix
  let some (.fn info) ← withGenVars stx ((resolveEntry fId).run' 0) (force := true)
    | throwErrorAt stx[3] "`{target.getPrefix}` is not an `mp def`"
  let declName := info.declName
  if (← getEnv).contains (declName ++ `spec) then
    throwErrorAt stx[3] "`{declName}.spec` is already proved"
  let some goalTy := ((← getEnv).find? (declName ++ `SpecGoal)).bind (·.value?)
    | throwErrorAt stx[3] "`{declName}` has no contract (`ensures`)"
  -- A generic function is proved under the same `variable`s.
  withGenVars stx (force := info.nGen > 0) do
    withFnGenVars info do
    let gvs ← genVarsRef.get
    let info := if info.nGen > 0 then info.instantiate gvs else info
    let goalTy := goalTy.beta gvs
    let prf ← elabTermEnsuringType stx[5] goalTy
    synthesizeSyntheticMVarsNoPostponing
    let prf ← instantiateMVars prf
    if prf.hasMVar || prf.hasSorry then throwErrorAt stx[5] "the proof is incomplete"
    addContractDecls info goalTy prf
  elabCommand (← `(attribute [spec] $(mkCIdent (declName ++ `spec))))
  -- When `mp def` could not prove the obligations, the contract's loop invariants are offered to
  -- them, so `f.safe` is tried by `mp_auto` with the same invariants, one text serving both.
  unless info.hasSafe do
    let some alts := stx[5].find? (·.getKind == ``Lean.Parser.Tactic.invariantAlts) | return
    let tac : Syntax := Syntax.node .none `Millipede.Meta.mpAutoTac
      #[Syntax.atom .none "mp_auto", mkNullNode, mkNullNode #[alts]]
    let prf ← `(by $(⟨tac⟩):tactic)
    let safeStx := (stx.setArg 3 (mkIdentFrom stx[3] (target.getPrefix ++ `safe))).setArg 5 prf
    let msgs := (← get).messages
    try
      elabMpProveSafe safeStx
      if !msgs.hasErrors && (← get).messages.hasErrors then throwError "not proved"
      logInfoAt stx[3] m!"`{target.getPrefix}.safe` was proved with the contract's loop invariants"
    catch _ => modify fun st => { st with messages := msgs }

end Millipede.Meta
