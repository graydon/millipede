import Lean
import Millipede.Meta.Program
import Millipede.Meta.Audit
import Millipede.Top.Driver

/-!
# `#mp_compile` and `mp_entry%`

The driver refuses to compile a program without a proof of its safety `p.safe`.

`#mp_compile p "out"` compiles the program `p` for x64 Linux when `p` has a proof
`p.safe : p.Safe`, and writes the ELF file `out` and the ledger `out.ledger.txt`, as `lake exe mpc`
does. It is a command that can be used in any file and from `lake env lean FILE`. With a third
argument, as in `#mp_compile p "out" "arm64-linux"`, it compiles for the target of that name,
and an unknown name is refused before anything is written. Without `p.safe` it refuses and names
the missing theorem, and for an `mp program` also the obligations of `init` and `step` or the
invariant goals that are open. `set_option mp.regalloc false` compiles with register allocation
off, and `set_option mp.opt.<pass> false`, for the passes `inline`, `fold`, `dce` and `strength`,
switches a Core pass off. Every pass is on by default.

`mp_entry% "name" "description" p` is the term `Entry.mk "name" "description" p p.safe "p.safe"`
of `Examples.registry`, with the same refusal.

The kernel checks the proof when the entry is built. `p.safe` must have the type `p.Safe`, and
its axioms must pass the classifier of `#audit`, so a `p.safe` that is incomplete, or has
elaboration errors so that Lean adds it with `sorryAx`, or depends on a user axiom is refused
with the axiom named. `Entry.mk` itself cannot see axioms, so an `Entry` written by hand is
checked only by `#audit`.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta

register_option mp.opt.inline : Bool := {
  defValue := true, descr := "`#mp_compile` runs the Core pass `inline` (Millipede/Opt/Rules.lean)" }
register_option mp.opt.fold : Bool := {
  defValue := true, descr := "`#mp_compile` runs the Core pass `fold` (Millipede/Opt/Rules.lean)" }
register_option mp.opt.dce : Bool := {
  defValue := true, descr := "`#mp_compile` runs the Core pass `dce` (Millipede/Opt/Rules.lean)" }
register_option mp.opt.strength : Bool := {
  defValue := true, descr := "`#mp_compile` runs the Core pass `strength` (Millipede/Opt/Rules.lean)" }

/-- The options of `#mp_compile`: every field at its default but register allocation and the Core
passes. -/
def emitOptions (ra : Bool) (opt : Opt.Config) : Compile.Options := { regalloc := ra, opt }

/-- The Core passes the options `mp.opt.<pass>` leave on. -/
def optOn (o : Options) : List String :=
  [("inline", mp.opt.inline.get o), ("fold", mp.opt.fold.get o), ("dce", mp.opt.dce.get o),
    ("strength", mp.opt.strength.get o)].filterMap fun (n, b) => if b then some n else none

/-- Why `p.safe` does not exist for an `mp program`, naming the missing obligations or invariant
goals. It is empty for another program. -/
def safeMissingWhy (p : Name) : MetaM String := do
  let env ← getEnv
  let some (.defnInfo pv) := env.find? p | return ""
  let #[_, initE, stepE] := pv.value.getAppArgs | return ""
  let some fi ← try some <$> fnOfExp initE catch _ => pure none | return ""
  let some fs ← try some <$> fnOfExp stepE catch _ => pure none | return ""
  let mut missing : Array String := #[]
  for f in [fi, fs] do
    unless env.contains (f.declName ++ `safe) do missing := missing.push s!"`{f.declName}.safe`"
  for g in [`inv_init, `inv_step] do
    if env.contains (p ++ (if g == `inv_init then `InvInitGoal else `InvStepGoal)) &&
        !env.contains (p ++ g) then
      missing := missing.push s!"`{p ++ g}`"
  if missing.isEmpty then return ""
  return s!" Missing: {", ".intercalate missing.toList} (see the messages at their definitions; \
    prove each with `mp prove`)."

/-- The driver's entry for the program `p`, `Entry.mk name desc p p.safe "p.safe"`, type-checked.
It is an error naming the missing theorem when `p.safe` is not proved. -/
def mkEntry (p : Name) (name desc : String) : MetaM Expr := do
  let env ← getEnv
  let some ci := env.find? p | throwError "unknown constant `{p}`"
  unless ci.type.isConstOf ``Program do
    throwError "`{p}` is not a program (`mp program`, or a constant of type `Program`)"
  let thm := p ++ `safe
  unless env.contains thm do
    throwError "refused: `{thm}` is not proved. `compile_sound` needs `{p}.Safe`, so an image of \
      `{p}` would carry no guarantee.{← safeMissingWhy p}"
  let e := mkAppN (mkConst ``Entry.mk) #[toExpr name, toExpr desc, mkConst p, mkConst thm,
    toExpr thm.toString]
  try check e catch _ =>
    throwError "refused: `{thm}` is not a proof of `{p}.Safe`"
  let bad ← Audit.rejectedAxioms thm
  unless bad.isEmpty do
    let why := if bad.contains ``sorryAx then " (`sorryAx`: an incomplete proof, or one with \
      elaboration errors)" else ""
    throwError "refused: `{thm}` depends on {bad.toList}{why}, axioms `#audit` rejects; the \
      ledger would claim a safety proof that does not exist"
  return e

/-- `mp_entry% "name" "description" p` builds a driver entry, as the module doc describes. -/
syntax (name := mpEntry) "mp_entry% " str ppSpace str ppSpace ident : term

@[term_elab mpEntry] def elabMpEntry : TermElab := fun stx _ => do
  let p ← realizeGlobalConstNoOverloadWithInfo stx[3]
  mkEntry p (stx[1].isStrLit?.getD "") (stx[2].isStrLit?.getD "")

private unsafe def evalEmitUnsafe (e : Expr) : TermElabM (IO (Except String Nat)) :=
  evalExpr (IO (Except String Nat)) (mkApp (mkConst ``IO) (mkApp2 (mkConst ``Except [0, 0])
    (mkConst ``String) (mkConst ``Nat))) e

@[implemented_by evalEmitUnsafe]
private opaque evalEmit (e : Expr) : TermElabM (IO (Except String Nat))

register_option mp.regalloc : Bool := {
  defValue := true
  descr := "#mp_compile: validated register allocation before selection (Compile.Options.regalloc)"
}

/-- `#mp_compile p "out"` compiles a program with a proof of its safety, as the module doc
describes. -/
syntax (name := mpCompile) "#mp_compile " ident ppSpace str (ppSpace str)? : command

@[command_elab mpCompile] def elabMpCompile : CommandElab := fun stx => liftTermElabM do
  let p ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let out := stx[2].isStrLit?.getD ""
  let tname := if stx[3].isNone then none else stx[3][0].isStrLit?
  let some tc := (targets.zip [``x64Linux, ``arm64Linux]).find? (·.1.name == tname.getD "x64-linux")
    | throwErrorAt stx[3] "unknown target '{tname.getD ""}' (known: \
        {", ".intercalate (targets.map (·.name))})"
  let desc := ((← findDocString? (← getEnv) p).getD "").splitOn "\n" |>.head!
  let e ← withRef stx[1] (mkEntry p p.toString desc)
  let t := Lean.mkConst tc.2
  let ra := mp.regalloc.get (← getOptions)
  let opt := mkApp2 (mkConst ``Opt.Config.mk) (toExpr Opt.Config.all.rounds)
    (toExpr (optOn (← getOptions)))
  let o := mkApp2 (mkConst ``emitOptions) (toExpr ra) opt
  match ← (← evalEmit (mkApp4 (mkConst ``Entry.emit) e (toExpr out) t o) : IO _) with
  | .ok n => logInfo m!"wrote {out} ({n} bytes) and {out}.ledger.txt; safety: `{p ++ `safe}`"
  | .error err => throwError "compile refused `{p}`: {err}"

end Millipede.Meta
