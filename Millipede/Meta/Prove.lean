import Lean
import Millipede.Meta.Contracts
import Millipede.Meta.Program

/-!
# `mp prove`, one command for obligations, contracts and root invariants

`mp prove f.safe := …`, `mp prove f.spec := …`, `mp prove p.inv_init := …` and
`mp prove p.inv_step := …` dispatch on the target to the elaborators of obligations, contracts and
programs. The theorem proved is recorded for `#mp_report`, as proved by hand or by `mp_auto`.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta

/-! ## Recording `mp prove` for `#mp_report` -/

/-- The theorems proved by hand with `mp prove`. -/
initialize handExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (fun s n => s.insert n) s) {}
  }

/-- The theorems that `mp prove` proved with a one-line proof `by mp_auto …`. -/
initialize autoProveExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (fun s n => s.insert n) s) {}
  }

/-- The elaborator of `mp prove`. By the target it proves obligations `f.safe`, a contract
`f.spec` or a root invariant `p.inv_init` or `p.inv_step`, and it records the theorem proved. -/
@[command_elab mpProve] def elabMpProveCmd : CommandElab := fun stx => do
  match stx[3].getId.components.getLast? with
  | some `safe => elabMpProveSafe stx
  | some `spec =>
    elabMpProveSpec stx
    -- A program whose `step` this contract is gets `p.reach`.
    if let some (.fn f) ← liftTermElabM ((resolveEntry (mkIdentFrom stx[3]
        stx[3].getId.getPrefix)).run' 0) then
      liftTermElabM (withRef stx[3] (deriveReachAfter f.declName))
  | some `inv_init | some `inv_step => elabMpProveInv stx
  | _ => throwErrorAt stx[3] "`mp prove` proves `f.safe`, `f.spec`, `p.inv_init` or \
      `p.inv_step`"
  let tgt := stx[3].getId
  let env ← getEnv
  let ns := (← getCurrNamespace).components
  let cands := (List.range (ns.length + 1)).reverse.map fun i =>
    (ns.take i).foldl (· ++ ·) Name.anonymous ++ tgt
  if let some n := cands.find? env.contains then
    modifyEnv (handExt.addEntry · n)
    -- A proof `by mp_auto …` is recorded apart, so that `#mp_report` says "mp_auto" and not
    -- "by hand".
    let prf := stx[5]
    let txt := ((prf.reprint.getD "").trimAscii).toString
    if txt.startsWith "by mp_auto" && !txt.contains '\n' then
      modifyEnv (autoProveExt.addEntry · n)

end Millipede.Meta
