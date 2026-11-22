/- Safety-proof census. It prints one line per `mp def` of the registry, in Millipede and Tests:
   `name analysed|relaxed|generic|- status`, where status is how `f.safe` was established
   (`proofStatus`). `generic` means it was proved once for every value of the definition's
   variables, so the analyser does not run on it. Operations of interfaces (`mp interface`) are
   not listed, because their safety is a field of each implementation.
   Usage, after `lake build Millipede Tests`; it is not part of the gate:
     lake env lean scripts/census.lean | awk '{print $2, $3}' | sort | uniq -c
   The tables in doc/measurements.md ("Safety proofs") are tallies of this output. -/
import Millipede
import Tests
open Lean Millipede.Meta
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, e) in (registry.getState env).toList do
    match e with
    | .fn f =>
      if isStructure env n.getPrefix then continue
      let st ← Millipede.Meta.proofStatus n `safe
      let an := if env.contains (n ++ `analysed) then "analysed"
        else if env.contains (n ++ `relaxed) then "relaxed"
        else if f.nGen > 0 then "generic" else "-"
      IO.println s!"{n} {an} {st}"
    | _ => pure ()
