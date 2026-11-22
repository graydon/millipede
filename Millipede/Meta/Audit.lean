import Lean

/-!
# `#audit` and `#audit_ledger`

`#audit foo` collects the axioms that `foo` depends on and reports an error if any is `sorryAx` or
a user axiom, which is any axiom besides `propext`, `Classical.choice`, `Quot.sound` and the
accepted compiler-trust axioms. `#audit` with no argument audits every theorem and every axiom of
every `Millipede*` module and of the current file, internal and private names included, and
`#audit Ns` does the same under the namespace `Ns`. An axiom declared in a `Millipede*` module is
an error too, unless it is a validated `bv_decide` axiom.

`bv_decide` adds one axiom per use, named `P._native.bv_decide.ax_*`. A name is not evidence, so
`checkBvDecideAxiom` accepts such an axiom only when `P` is a theorem of the same module, its type
is exactly `verifyBVExpr P._expr_def_* P._cert_def_* = true` with both arguments definitions of
that module built from library constants only, and compiling and running that checker again
yields `true`. Any other `_native` axiom is a user axiom. Theorems that depend on an accepted axiom,
or on the global axiom `Lean.ofReduceBool`, are listed separately. They are an error unless the
tactic was used in one of the encode and decode modules of `bvDecideMods`. For a per-use axiom
that is the module declaring it, and for the global axiom the theorem's own module. Theorems that
build on such an encoding lemma elsewhere are only listed.

`#audit_ledger` prints a skeleton of the assumption ledger, which lists the modules of trusted
models and the theorems that rely on compiled evaluation. The open claims are checked by
`scripts/audit.sh`, not here. The trust model is described in doc/design/trust.md.
-/

namespace Millipede.Meta.Audit

open Lean Elab Command

/-- Axioms Lean itself accepts as the logical foundation. -/
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The global compiler-trust axioms, judged by the module of the theorem that uses them. -/
def legacyCompilerAxioms : List Name := [`Lean.ofReduceBool, `Lean.trustCompiler]

/-- Whether the name has a `_native` component, the mark of a per-use native-evaluation axiom.
Such a name is only a claim, and `checkBvDecideAxiom` decides whether to believe it. -/
def isNativeName (a : Name) : Bool := a.components.any (· == `_native)

/-- Whether `a` names compiler trust, for the ledger listing. This is not a verdict. -/
def mentionsCompilerTrust (a : Name) : Bool := legacyCompilerAxioms.contains a || isNativeName a

/-- The declaration `P` whose elaboration ran `bv_decide`, from the axiom name
`P._native.bv_decide.ax_*`. Per-use axioms of the native-decide tactic are not recognised, since
the project forbids that tactic. -/
def bvDecideOwner? : Name → Option Name
  | .str (.str (.str p "_native") "bv_decide") s => if s.startsWith "ax_" then some p else none
  | _ => none

/-- The checker whose compiled result `bv_decide` asserts. It is compared by name and not
resolved, so that Std.Tactic.BVDecide need not be imported here. -/
def verifyBVExprName : Name := `Std.Tactic.BVDecide.Reflect.verifyBVExpr

/-- The module a declaration lives in, which is the main module for a declaration of the current
file. -/
def declModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- Whether `m` is equal to or below the module or namespace `p`. -/
def under (p m : Name) : Bool := p.isPrefixOf m

/-- The modules of the trusted models, which `#audit_ledger` lists. -/
def trustedMods : List Name := [`Millipede.Target, `Millipede.Object]

/-- The modules whose theorems may use `bv_decide`, which are the encode and decode lemmas of
arm64. A use anywhere else is an `#audit` error. -/
def bvDecideMods : List Name :=
  [`Millipede.Target.A64.Word, `Millipede.Target.A64.Decode]

/-- Whether the declaration is part of the Millipede library or of the current file. -/
def isOurs (env : Environment) (n : Name) : Bool :=
  let m := declModule env n
  under `Millipede m || (env.getModuleIdxFor? n).isNone

/-- One argument of the checked `verifyBVExpr` call, which must be a constant `P.<pfx>*` without
universe parameters, defined in module `m`, whose value mentions only library constants. Since
none of the constants is ours, no `implemented_by` or `extern` of ours can make compiled and
kernel evaluation differ. It returns the value. -/
def bvDecideArg (env : Environment) (p m : Name) (pfx : String) (e : Expr) :
    Except MessageData Expr := do
  let .const x [] := e | throw m!"argument {e} is not a constant"
  let .str q s := x | throw m!"argument {x} is not named {p}.{pfx}*"
  unless q == p && s.startsWith pfx do throw m!"argument {x} is not named {p}.{pfx}*"
  let some (.defnInfo d) := env.find? x | throw m!"argument {x} is not a definition"
  unless d.levelParams.isEmpty && declModule env x == m do
    throw m!"argument {x} is not a monomorphic definition of module {m}"
  let bad := d.value.getUsedConstants.filter (isOurs env)
  unless bad.isEmpty do throw m!"argument {x} mentions non-library constants {bad.toList}"
  return d.value

/-- The structural check of a claimed per-use `bv_decide` axiom `a`. Its name must be
`P._native.bv_decide.ax_*` with `P` a theorem of the same module, and its type exactly what
`Lean.Meta.nativeEqTrue` emits for `bv_decide`, `verifyBVExpr P._expr_def_* P._cert_def_* = true`.
It returns the left-hand side with both arguments unfolded, which is a closed `Bool` term. -/
def bvDecideShape (env : Environment) (a : Name) : Except MessageData Expr := do
  let some p := bvDecideOwner? a
    | throw m!"its name is not of the form <theorem>._native.bv_decide.ax_*"
  let some (.axiomInfo ai) := env.find? a | throw m!"it is not an axiom"
  unless ai.levelParams.isEmpty && !ai.isUnsafe do
    throw m!"it is universe-polymorphic or unsafe"
  let m := declModule env a
  match env.find? p with
  | some (.thmInfo _) =>
    unless declModule env p == m do throw m!"its owner {p} is in another module"
  | _ => throw m!"its owner {p} is not a theorem"
  let some (ty, lhs, rhs) := ai.type.eq? | throw m!"its type is not an equation"
  unless ty == mkConst ``Bool && rhs == mkConst ``Bool.true do
    throw m!"its type is not `_ = true` in Bool"
  let .app (.app (.const f []) x) c := lhs
    | throw m!"its type is not `{verifyBVExprName} _ _ = true`"
  unless f == verifyBVExprName do throw m!"its type is not `{verifyBVExprName} _ _ = true`"
  let xv ← bvDecideArg env p m "_expr_def_" x
  let cv ← bvDecideArg env p m "_cert_def_" c
  return mkApp2 (mkConst f) xv cv

/-- The full check of a claimed per-use `bv_decide` axiom. It makes the structural check and then
establishes the asserted equation again by compiling and running the checker, through the same
`Lean.Meta.nativeEqTrue` path that `bv_decide` used, so the trust that remains is exactly trust in
the compiler. `none` means the axiom is accepted, and `some why` gives the reason it is not. -/
def checkBvDecideAxiomM (a : Name) : MetaM (Option MessageData) := do
  match bvDecideShape (← getEnv) a with
  | .error why => return some why
  | .ok lhs =>
    try
      let r ← withoutModifyingEnv <| Meta.nativeEqTrue `audit_bv_decide lhs
      match r with
      | .success _ => return none
      | .notTrue => return some m!"its asserted checker run evaluates to false"
    catch ex => return some m!"re-running its checker failed: {ex.toMessageData}"

/-- `checkBvDecideAxiomM` as a command. -/
def checkBvDecideAxiom (a : Name) : CommandElabM (Option MessageData) :=
  liftTermElabM (checkBvDecideAxiomM a)

/-- The outcome of auditing one declaration. -/
inductive Verdict where
  | clean
  | reduceBool (allowed : Bool)
  | bad (axs : List Name)

/-- Whether a compiler-trust axiom is acceptable for the theorem `n`. A validated per-use axiom
`<decl>._native.bv_decide.…` is acceptable when the module that declares it, where the tactic
ran, is one of `bvDecideMods`, since theorems that build on such an encoding lemma inherit the
dependency without using the tactic. The global axioms are judged by the module of `n`. -/
def compilerAxiomOk (env : Environment) (n a : Name) : Bool :=
  let m := if isNativeName a then declModule env a else declModule env n
  bvDecideMods.contains m

/-- Classify the axioms a declaration depends on. `native` is the set of `_native` axioms that
passed `checkBvDecideAxiom`, and any other `_native` axiom is a user axiom. -/
def classify (env : Environment) (native : NameSet) (n : Name) (axs : Array Name) : Verdict :=
  let isCompiler (a : Name) : Bool := legacyCompilerAxioms.contains a || native.contains a
  let bad := axs.toList.filter fun a => !(stdAxioms.contains a || isCompiler a)
  if !bad.isEmpty then .bad bad
  else if axs.any isCompiler then
    .reduceBool ((axs.filter isCompiler).all fun a => compilerAxiomOk env n a)
  else .clean

/-- The axioms of `n` that `#audit` would reject, with the same verdicts as `auditOne`. They are
`sorryAx`, which marks an incomplete proof or one with elaboration errors, any axiom besides
`stdAxioms`, the global compiler-trust axioms and the `bv_decide` axioms that pass
`checkBvDecideAxiomM`, and a compiler-trust axiom introduced outside `bvDecideMods`. The driver
calls it before it accepts a safety proof. -/
def rejectedAxioms (n : Name) : MetaM (Array Name) := do
  let axs ← collectAxioms n
  let mut native : NameSet := {}
  for a in axs do
    if isNativeName a then
      if (← checkBvDecideAxiomM a).isNone then native := native.insert a
  match classify (← getEnv) native n axs with
  | .bad bad => return bad.toArray
  | .reduceBool false =>
    return axs.filter fun a => legacyCompilerAxioms.contains a || native.contains a
  | _ => return #[]

/-- The declarations to audit in our library, which are every axiom and every theorem matching the
filter. Internal and private names are included, so that no axiom hides behind a name with a `_`
component. -/
def targets (env : Environment) (ns : Option Name) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if !isOurs env n then continue
    match ci with
    | .axiomInfo _ =>
      -- A namespace filter matches the name with any private prefix removed.
      if let some p := ns then if !p.isPrefixOf (privateToUserName n) then continue
      out := out.push n
    | .thmInfo _ =>
      if let some p := ns then if !p.isPrefixOf (privateToUserName n) then continue
      out := out.push n
    | _ => pure ()
  return out.qsort Name.lt

/-- The result of a whole audit run. -/
structure Report where
  checked : Nat := 0
  errors : Nat := 0
  reduceBool : Array Name := #[]
  /-- The cached verdicts of `checkBvDecideAxiom`, where `none` means accepted. -/
  native : Std.HashMap Name (Option MessageData) := {}

/-- `checkBvDecideAxiom`, cached in the report. -/
def nativeVerdict (a : Name) (r : Report) : CommandElabM (Option MessageData × Report) := do
  if let some v := r.native[a]? then return (v, r)
  let v ← checkBvDecideAxiom a
  return (v, { r with native := r.native.insert a v })

/-- Audit a single declaration, logging errors, and return the updated report. -/
def auditOne (n : Name) (r : Report) : CommandElabM Report := do
  let env ← getEnv
  let some ci := env.find? n | throwError "#audit: unknown declaration '{n}'"
  let mut r := { r with checked := r.checked + 1 }
  if let .axiomInfo _ := ci then
    if isOurs env n then
      if isNativeName n then
        let (v, r') ← nativeVerdict n r
        r := r'
        if let some why := v then
          logError m!"#audit: '{n}' is a user axiom disguised as a bv_decide axiom: {why}"
          return { r with errors := r.errors + 1 }
      else
        logError m!"#audit: '{n}' is a user axiom"
        return { r with errors := r.errors + 1 }
  let axs ← liftCoreM (collectAxioms n)
  let mut native : NameSet := {}
  for a in axs do
    if isNativeName a then
      let (v, r') ← nativeVerdict a r
      r := r'
      if v.isNone then native := native.insert a
  match classify env native n axs with
  | .clean => pure r
  | .reduceBool ok =>
    if ci.isTheorem then r := { r with reduceBool := r.reduceBool.push n }
    if ok then pure r else
      logError m!"#audit: '{n}' depends on a compiler-trust axiom (ofReduceBool) introduced outside the encode/decode modules {", ".intercalate (bvDecideMods.map toString)}"
      return { r with errors := r.errors + 1 }
  | .bad axs =>
    if axs.contains ``sorryAx then
      logError m!"#audit: '{n}' depends on sorryAx (an incomplete proof)"
    else
      logError m!"#audit: '{n}' depends on non-standard axioms {axs}"
    return { r with errors := r.errors + 1 }

/-- Audit a list of declarations and print a summary. -/
def auditAll (ns : Array Name) : CommandElabM Unit := do
  let mut r : Report := {}
  for n in ns do
    r ← auditOne n r
  unless r.reduceBool.isEmpty do
    logInfo m!"#audit: theorems depending on Lean.ofReduceBool: {r.reduceBool.toList}"
  if r.errors == 0 then
    logInfo m!"#audit: {r.checked} declarations checked, no incomplete proofs, no user axioms"
  else
    logInfo m!"#audit: {r.checked} declarations checked, {r.errors} failed"

/-- `#audit`, `#audit thm` and `#audit Namespace` audit axioms, as the module doc describes. -/
syntax (name := auditCmd) "#audit" (ppSpace ident)? : command

elab_rules : command
  | `(#audit $[$id]?) => do
    let env ← getEnv
    match id with
    | none => auditAll (targets env none)
    | some i =>
      let cs ← try liftCoreM (resolveGlobalConst i) catch _ => pure []
      match cs with
      | c :: _ => auditAll #[c]
      | [] =>
        let ts := targets env (some i.getId)
        if ts.isEmpty then throwErrorAt i "#audit: '{i.getId}' is neither a declaration nor a namespace with theorems"
        auditAll ts

/-- `#audit_ledger` prints a skeleton of the assumption ledger. -/
syntax (name := auditLedgerCmd) "#audit_ledger" : command

elab_rules : command
  | `(#audit_ledger) => do
    let env ← getEnv
    let mods := env.header.moduleNames.toList.filter fun m =>
      trustedMods.any (fun p => under p m) || under `Millipede.Extern m
    let mut rb : Array Name := #[]
    for n in targets env none do
      unless (env.find? n).any (·.isTheorem) do continue
      let axs ← liftCoreM (collectAxioms n)
      if axs.any mentionsCompilerTrust then rb := rb.push n
    let fmt (l : List Name) : String :=
      if l.isEmpty then "  (none)" else "\n".intercalate (l.map fun n => s!"  - {n}")
    logInfo m!"Assumption ledger skeleton\n\
      Trusted models (modules):\n{fmt mods}\n\
      Theorems depending on Lean.ofReduceBool (bv_decide):\n{fmt rb.toList}\n\
      Open claims: see doc/open-claims.md (printed by scripts/audit.sh)"

end Millipede.Meta.Audit
