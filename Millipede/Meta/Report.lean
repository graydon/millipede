import Lean
import Millipede.Meta.MpDef
import Millipede.Meta.Audit
import Millipede.Top.Ledger

/-!
# `#mp_report`, the figures and proof status of a program or a function

`#mp_report X` takes a program `X`, which is an `mp program` or any `Program` constant such as
the application `abbrev P := Reqs.prog Pool8.impl _` of a generic program, or an `mp def` `X`,
closed or generic.

For a program it prints the evaluated figures for each target. They are the bytes of the root,
which is static storage, the static footprint `Program.footprint`, which is the root plus the
larger of the frames' values of `init` and `step`, the static data region `memBytes`, the stack
bound, the instructions per reactor step, and the size of the compiled image.

For each `mp def` of a program, which means `init`, `step` and what they call at the program's
arguments, it prints the stack bound per target and how the obligations and the contract were
established. That is `none` for a total term, `automatic` when `mp def` proved them, `by hand`
for an `mp prove`, `open`, or `failed` when the theorem depends on an axiom that `#audit`
rejects, as a theorem that the kernel rejected does, and a generic function's are marked `proved once`, since one
theorem covers every value of its variables. It also prints whether wrapping arithmetic flows
into an index or a slice bound, and what the verified analyser certified. `[analyser: all]` means
every obligation, and `[analyser: k of n overflow]` means `k` of the `n` overflow obligations,
with the rest proved by `mp_safe` or by hand. Nothing is shown for a term without overflow
obligations that the analyser left alone. For a function whose `mp def` stopped with an error it
says `failed`.

For a generic `mp def` alone it prints the variables it takes and how its obligations and
contract were established, once, since numeric figures exist only at a closed instance. What was
proved by hand is what `mp prove` recorded. The figures are described in doc/design/resources.md.
-/

namespace Millipede.Wraps

/-! ## Wrapping arithmetic into indices

A def-use walk over a Core term marks the variables bound to the result of a wrapping `+`, `-` or
`*`, directly or through `let x := y`, and counts each index, slice bound or pair index of a place
or of an extern's slice argument that is such a variable. `#mp_report` prints the count per
function. A wrapped size or index is an overflow that should be written with `+!`, `-!` or `*!`,
because even though the place's obligation checks the index again, the program meant something
else. -/

/-- The count of the atom if its variable is marked. `ms` holds the marks by de Bruijn index,
innermost first. -/
def marked {Γ : List Ty} {t : Ty} (ms : List Bool) : Atom Γ t → Nat
  | .var m => if ms.getD m.idx false then 1 else 0
  | .lit _ => 0

/-- Marked indices and bounds of a place. -/
def place {Γ : List Ty} (ms : List Bool) : {t : Ty} → Place Γ t → Nat
  | _, .var _ => 0
  | _, .field p _ => place ms p
  | _, .index (dflt := _) p i | _, .slot (dflt := _) p i => place ms p + marked ms i
  | _, .range p lo len => place ms p + marked ms lo + marked ms len
  | _, .pair2 (dflt := _) p i j => place ms p + marked ms i + marked ms j
  | _, .rangeS _ lo len => marked ms lo + marked ms len
  | _, .pair2S (dflt := _) _ i j => marked ms i + marked ms j

/-- Marked bounds of an extern's slice arguments. -/
def eargs {Γ : List Ty} (ms : List Bool) : {ps : List ExtParam} → EArgs Γ ps → Nat
  | _, .nil => 0
  | _, .word _ as | _, .bufIn (.const _) as | _, .bufOut as => eargs ms as
  | _, .bufIn (.slice a lo len) as | _, .sliceOut a lo len as =>
    place ms a + marked ms lo + marked ms len + eargs ms as

/-- Marked places of a call's reference arguments. -/
def rargs {Γ : List Ty} (ms : List Bool) : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own _ as => rargs ms as
  | _, _, .shr p as | _, _, .mut p as => place ms p + rargs ms as

/-- The count of marked indices and bounds in `e`, and whether its value is marked. -/
def exp {Γ : List Ty} (ms : List Bool) : {t : Ty} → Exp Γ t → Nat × Bool
  | _, .atom a => (0, marked ms a == 1)
  | _, .let_ e₁ e₂ => let r := exp ms e₁; let k := exp (r.2 :: ms) e₂; (r.1 + k.1, k.2)
  | _, .ite _ e₁ e₂ => ((exp ms e₁).1 + (exp ms e₂).1, (exp ms e₁).2 || (exp ms e₂).2)
  | _, .prim .add _ | _, .prim .sub _ | _, .prim .mul _ => (0, true)
  | _, .match_ _ eE eO | _, .case _ _ eE eO => ((exp (false :: ms) eE).1 + (exp (false :: ms) eO).1, false)
  | _, .ext _ args => (eargs ms args, false)
  | _, .extMut _ args k => (eargs ms args + (exp (false :: ms) k).1, false)
  | _, .read p => (place ms p, false)
  | _, .assign p _ k | _, .put p _ _ k => (place ms p + (exp ms k).1, false)
  | _, .take (dflt := _) p i k => (place ms p + marked ms i + (exp (false :: ms) k).1, false)
  | _, .borrowShr p body k | _, .borrowMut p body k =>
    (place ms p + (exp (false :: ms) body).1 + (exp (false :: ms) k).1, false)
  | _, .callRef _ _ _ args k => (rargs ms args + (exp (false :: ms) k).1, false)
  | _, .loop _ _ _ c body k =>
    ((exp (false :: false :: ms) c).1 + (exp (false :: false :: ms) body).1 +
      (exp (false :: ms) k).1, false)
  | _, _ => (0, false)

/-- The count of wrapping results used as an index or a bound in `e`, its callees not
included. -/
def count {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Nat := (exp [] e).1

end Millipede.Wraps

namespace Millipede.Meta

open Lean Elab Command Term Meta

/-- The evaluated figures of a program. -/
def programFigures (p : Program) : String :=
  let ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩
  let code := match compile p x64Linux with
    | .ok b => s!"{b.size} bytes (x64 Linux ELF)"
    | .error e => s!"not compiled: {e}"
  let codeA := match compile p arm64Linux with
    | .ok b => s!"{b.size} bytes (arm64 Linux ELF)"
    | .error e => s!"not compiled: {e}"
  s!"  root            {p.State.size} bytes (static storage)\n" ++
  s!"  footprint       {p.footprint} bytes (root + the larger of init's and step's values)\n" ++
  s!"  data region     {p.memBytes} bytes\n" ++
  s!"  stack           ≤ {p.stackBytes X64.φ} bytes (X64.φ)\n" ++
  s!"  steps           init ≤ {p.stepCost 0 ω0 X64.κ}, each step ≤ {p.stepCost 1 ω0 X64.κ} \
    instructions (X64.κ)\n" ++
  s!"                  (a bound, not a measurement: the Core term's cost under the cost model \
    X64.κ, which compile checks the selected code against; on the oracle answering 0 the \
    source semantics charges init {p.stepSteps ω0 X64.κ 0}, step 1 {p.stepSteps ω0 X64.κ 1})\n" ++
  s!"  code            {code}\n" ++
  s!"  arm64           stack ≤ {p.stackBytes A64.φ} bytes (A64.φ), each step ≤ \
    {p.stepCost 1 ω0 A64.κ} instructions (A64.κ); code {codeA}"

private unsafe def evalStringUnsafe (e : Expr) : TermElabM String :=
  evalExpr String (mkConst ``String) e

@[implemented_by evalStringUnsafe]
private opaque evalString (e : Expr) : TermElabM String

/-- How a theorem `f.safe` or `f.spec` was established. -/
def proofStatus (f : Name) (what : Name) : CoreM String := do
  let env ← getEnv
  let thm := f ++ what
  let some ci := env.find? thm | return if env.contains (f ++ `SpecGoal) || what == `safe then
    "open" else "none"
  if let some v := ci.value? (allowOpaque := true) then
    if what == `safe && v.getUsedConstants.contains ``Exp.safe_of_total then return "none (total)"
  -- A theorem whose check failed, which Lean adds as an axiom, or that depends on one.
  let bad ← (Audit.rejectedAxioms thm).run'
  unless bad.isEmpty do
    return s!"failed (`{thm}` depends on {bad.toList}, which `#audit` rejects)"
  if (handExt.getState env).contains thm then
    return if (autoProveExt.getState env).contains thm then "mp_auto (mp prove … := by mp_auto)"
      else "by hand (mp prove)"
  return "automatic"

/-- The applications of `f.exp` constants in `e`, outermost first, with their arguments. -/
partial def collectExps (e : Expr) : Array Expr :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let inner := e.getAppArgs.flatMap collectExps
    match f.constName? with
    | some c => if c.isStr && c.getString! == "exp" then #[e] ++ inner else inner
    | none => collectExps f ++ inner
  | .const c _ => if c.isStr && c.getString! == "exp" then #[e] else #[]
  | .lam _ t b _ | .forallE _ t b _ => collectExps t ++ collectExps b
  | .letE _ t v b _ => collectExps t ++ collectExps v ++ collectExps b
  | .mdata _ b | .proj _ _ b => collectExps b
  | _ => #[]

/-- `#mp_report X` prints the figures and proof status of `X`, as the module doc describes. -/
syntax (name := mpReport) "#mp_report " ident : command

@[command_elab mpReport] def elabMpReport : CommandElab := fun stx => do
  let id := stx[1]
  let env ← getEnv
  let ns := (← getCurrNamespace).components
  let cands := (List.range (ns.length + 1)).reverse.map fun i =>
    (ns.take i).foldl (· ++ ·) Name.anonymous ++ id.getId
  let cands := cands ++ (← getScope).openDecls.filterMap fun
    | .simple o _ => some (o ++ id.getId)
    | _ => none
  let prog? := (cands.find? fun n => match env.find? n with
    | some ci => ci.type.isConstOf ``Program
    | none => false)
  let fn? := cands.findSome? fun n => match lookupEntry env n with
    | some (.fn f) => some f
    | _ => none
  let mut out := #[]
  -- The functions, each the `exp` term at the program's arguments.
  let mut fns : Array (FnInfo × Expr) := #[]
  let mut progs : Array Name := #[]
  if let some p := prog? then
    progs := #[p]
    let some v := (env.find? p).bind (·.value?) | throwError "`{p}` has no value"
    -- `init`, `step` and every function they call, transitively, at their arguments. An
    -- application of a generic program is unfolded to its `exp` terms applied.
    let mut todo : List Expr := [v]
    let mut seen : Std.HashSet Expr := {}
    while !todo.isEmpty do
      let e :: rest := todo | break
      todo := rest
      for x in collectExps e do
        if seen.contains x then continue
        seen := seen.insert x
        let some c := x.getAppFn.constName? | continue
        if let some (.fn f) := lookupEntry env c.getPrefix then
          fns := fns.push (f, x)
        if let some ev := (env.find? c).bind (·.value?) then
          todo := todo ++ [ev.beta x.getAppArgs]
      -- A constant that is not an `exp`, such as the generic program itself, is unfolded.
      if let some c := e.getAppFn.constName? then
        unless c.isStr && c.getString! == "exp" do
          if let some ev := (env.find? c).bind (·.value?) then
            if ev.getUsedConstants.any fun d => d.isStr && d.getString! == "exp" then
              todo := todo ++ [ev.beta e.getAppArgs]
  else if let some f := fn? then
    if f.nGen > 0 then
      out := out.push s!"{f.declName}: generic over {f.nGen} variable(s); proved once, for every \
        value of them (figures: at a closed instance, `#mp_report` of a program)"
      out := out.push s!"  obligations {← liftCoreM (proofStatus f.declName `safe)}; contract \
        {← liftCoreM (proofStatus f.declName `spec)}"
      logInfo (String.intercalate "\n" out.toList)
      return
    fns := #[(f, mkConst (f.declName ++ `exp))]
  else
    let failed ← failedDefs.get
    if cands.any failed.contains then
      throwErrorAt id "`{id.getId}`: failed. Its `mp def` stopped with the error reported there, \
        so it has no proved obligations or contract and cannot be called or compiled"
    throwErrorAt id "`{id.getId}` is neither a program nor an `mp def`"
  for p in progs do
    out := out.push s!"program {p}"
    out := out.push (← liftTermElabM (evalString (mkApp (mkConst ``programFigures) (mkConst p))))
    -- The trace theorem that `mp program` derives from contracts about events, if any.
    if env.contains (p ++ `events_reach) then
      out := out.push s!"trace from the contracts of init and step: `{p ++ `events_reach}`"
    else if let some (_, _, g) := (pendingReachExt.getState env).find? (·.1 == p) then
      out := out.push <| if env.contains (g ++ `spec) then
        s!"trace from the contracts of init and step: not derived (see the message at \
          `mp prove {g}.spec`)"
      else s!"trace from the contracts of init and step: waits for `mp prove {g}.spec`"
  let fns' := fns.qsort (·.1.declName.toString < ·.1.declName.toString)
  unless fns'.isEmpty do
    out := out.push "functions (stack ≤ bytes under X64.φ / A64.φ, per target; obligations; contract)"
  for (f, fexp) in fns' do
    let stackAt (φ : Name) : TermElabM String := do
      try
        let e ← mkAppM ``Exp.stack #[mkConst φ, fexp]
        evalString (← mkAppM ``toString #[e])
      catch _ => pure "?"
    let stack ← liftTermElabM do
      pure s!"x64 {← stackAt ``X64.φ}, arm64 {← stackAt ``A64.φ}"
    -- For an operation of an interface, its safety and contract are the implementation's fields.
    let isOp := isStructure env f.declName.getPrefix
    let safe ← if isOp then pure s!"the implementation's (`{f.declName.getPrefix}` field)"
      else liftCoreM (proofStatus f.declName `safe)
    -- What the verified analyser certified.
    let an ← liftTermElabM do
      if f.nGen > 0 then return ""
      match ← Analyse.certified f.declName with
      | some (some k, nOv, _) =>
        pure <| if (← getEnv).contains (f.declName ++ `analysed) then " [analyser: all]"
          else s!" [analyser: {k} of {nOv} overflow]"
      | some (none, nOv, _) => pure <| if nOv == 0 then "" else s!" [analyser: 0 of {nOv} overflow]"
      | none => pure ""
    let safe := safe ++ an
    let spec ← if isOp then pure "the interface's" else liftCoreM (proofStatus f.declName `spec)
    -- Wrapping `+ - *` used as an index or a slice bound.
    let wraps ← liftTermElabM do
      try
        let e ← mkAppM ``Wraps.count #[fexp]
        let s ← evalString (← mkAppM ``toString #[e])
        pure (if s == "0" then "" else s!"; {s} wrapping `+ - *` into an index or slice bound")
      catch _ => pure ""
    let once := if f.nGen > 0 && !isOp then " (proved once)" else ""
    out := out.push s!"  {f.declName}: stack {stack}; obligations {safe}{once}; contract {spec}{wraps}"
  logInfo (String.intercalate "\n" out.toList)

end Millipede.Meta
