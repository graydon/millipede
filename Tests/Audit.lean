import Millipede.Meta.Audit
import Std.Tactic.BVDecide

/-!
# Tests for `#audit`

`#audit` reports incomplete proofs, user axioms and uses of the compiler in proofs. The tests seed
bad declarations and require each to be reported. They are built with `addDecl` from kernel terms
assembled by hand, so no source text of this file contains the forbidden keywords that the
scripts grep for.
-/

open Lean Elab Command

-- add a theorem of `False` whose proof is the incomplete-proof marker
#guard_msgs (drop warning) in
run_cmd liftCoreM do
  addDecl <| .thmDecl
    { name := `Seeded.incomplete, levelParams := [], type := mkConst ``False
      value := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``False) (toExpr false) }

-- add a local axiom and a theorem that uses it
run_cmd liftCoreM do
  addDecl <| .axiomDecl
    { name := `Seeded.badAx, levelParams := [], type := mkConst ``False, isUnsafe := false }
  addDecl <| .thmDecl
    { name := `Seeded.usesAx, levelParams := [], type := mkConst ``False
      value := mkConst `Seeded.badAx }

-- a genuine use of `bv_decide`, a tiny encode/decode lemma, outside the encode/decode modules
theorem Seeded.viaCompiler (x : BitVec 8) : (x <<< 1) >>> 1 = x &&& 0x7F := by bv_decide

-- a user axiom disguised as a per-use `bv_decide` axiom, with an internal `_native` name, private
-- and of an arbitrary type, and a theorem of `False` built on it
run_cmd liftCoreM do
  let ax := mkPrivateName (← getEnv) `Seeded.disguised._native.bv_decide.ax_1_1
  addDecl <| .axiomDecl
    { name := ax, levelParams := [], type := mkConst ``False, isUnsafe := false }
  addDecl <| .thmDecl
    { name := `Seeded.disguised, levelParams := [], type := mkConst ``False
      value := mkConst ax }

-- a forged axiom of exactly the `bv_decide` shape `verifyBVExpr e c = true`, which reuses the
-- genuine expression of `Seeded.viaCompiler` with an empty certificate, so the checker run it
-- asserts is false
run_cmd liftCoreM do
  let env ← getEnv
  let isExprDef (n : Name) : Bool := match n with
    | .str p s => p == `Seeded.viaCompiler && s.startsWith "_expr_def_"
    | _ => false
  let some (_, ci) := env.constants.toList.find? (isExprDef ·.1)
    | throwError "no expression definition found for Seeded.viaCompiler"
  let x := `Seeded.forged._expr_def_1_1
  let c := `Seeded.forged._cert_def_1_1
  addDecl <| .defnDecl
    { name := x, levelParams := [], type := ci.type, value := ci.value!,
      hints := .abbrev, safety := .safe }
  addDecl <| .defnDecl
    { name := c, levelParams := [], type := mkConst ``String, value := mkStrLit "",
      hints := .abbrev, safety := .safe }
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Std.Tactic.BVDecide.Reflect.verifyBVExpr) (mkConst x) (mkConst c))
    (mkConst ``Bool.true)
  addDecl <| .axiomDecl
    { name := `Seeded.forged._native.bv_decide.ax_1_1, levelParams := [], type := ty,
      isUnsafe := false }
  addDecl <| .thmDecl
    { name := `Seeded.forged, levelParams := [], type := ty
      value := mkConst `Seeded.forged._native.bv_decide.ax_1_1 }

theorem Seeded.clean : 1 + 1 = 2 := by decide

/--
error: #audit: 'Seeded.incomplete' depends on sorryAx (an incomplete proof)
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.incomplete

/--
error: #audit: 'Seeded.usesAx' depends on non-standard axioms [Seeded.badAx]
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.usesAx

/--
error: #audit: 'Seeded.badAx' is a user axiom
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.badAx

/--
error: #audit: 'Seeded.viaCompiler' depends on a compiler-trust axiom (ofReduceBool) introduced outside the encode/decode modules Millipede.Target.A64.Word, Millipede.Target.A64.Decode
---
info: #audit: theorems depending on Lean.ofReduceBool: [Seeded.viaCompiler]
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.viaCompiler

/-- info: #audit: 1 declarations checked, no incomplete proofs, no user axioms -/
#guard_msgs in
#audit Seeded.clean

-- the disguised axiom, a private `_native` axiom proving `False`, is rejected both through the
-- theorem that uses it and as an axiom in its own right, although its name is internal
/--
error: #audit: 'Seeded.disguised' depends on non-standard axioms [_private.Tests.Audit.0.Seeded.disguised._native.bv_decide.ax_1_1]
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.disguised

/--
error: #audit: '_private.Tests.Audit.0.Seeded.disguised._native.bv_decide.ax_1_1' is a user axiom disguised as a bv_decide axiom: its owner _private.Tests.Audit.0.Seeded.disguised is not a theorem
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.disguised._native

-- the forged axiom has the exact shape of `bv_decide`, and running its checker again exposes it
/--
error: #audit: 'Seeded.forged' depends on non-standard axioms [Seeded.forged._native.bv_decide.ax_1_1]
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.forged

/--
error: #audit: 'Seeded.forged._native.bv_decide.ax_1_1' is a user axiom disguised as a bv_decide axiom: its asserted checker run evaluates to false
---
info: #audit: 1 declarations checked, 1 failed
-/
#guard_msgs in
#audit Seeded.forged._native.bv_decide.ax_1_1

-- an audit of a whole namespace reaches internal and private axioms too
/--
error: #audit: 'Seeded.badAx' is a user axiom
---
error: #audit: 'Seeded.disguised' depends on non-standard axioms [_private.Tests.Audit.0.Seeded.disguised._native.bv_decide.ax_1_1]
---
error: #audit: 'Seeded.forged' depends on non-standard axioms [Seeded.forged._native.bv_decide.ax_1_1]
---
error: #audit: 'Seeded.incomplete' depends on sorryAx (an incomplete proof)
---
error: #audit: 'Seeded.usesAx' depends on non-standard axioms [Seeded.badAx]
---
error: #audit: 'Seeded.viaCompiler' depends on a compiler-trust axiom (ofReduceBool) introduced outside the encode/decode modules Millipede.Target.A64.Word, Millipede.Target.A64.Decode
---
error: #audit: 'Seeded.forged._native.bv_decide.ax_1_1' is a user axiom disguised as a bv_decide axiom: its asserted checker run evaluates to false
---
error: #audit: 'Seeded.viaCompiler._native.bv_decide.ax_1_5' depends on a compiler-trust axiom (ofReduceBool) introduced outside the encode/decode modules Millipede.Target.A64.Word, Millipede.Target.A64.Decode
---
error: #audit: '_private.Tests.Audit.0.Seeded.disguised._native.bv_decide.ax_1_1' is a user axiom disguised as a bv_decide axiom: its owner _private.Tests.Audit.0.Seeded.disguised is not a theorem
---
info: #audit: theorems depending on Lean.ofReduceBool: [Seeded.viaCompiler]
---
info: #audit: 10 declarations checked, 9 failed
-/
#guard_msgs in
#audit Seeded
