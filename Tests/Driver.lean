import Millipede.Top.Examples
import Millipede.Meta.Emit

/-!
# Tests for the driver's safety check

The compiler's soundness theorem takes `p.Safe` as a premise, so the driver refuses a program
whose `p.safe` is not proved. `#mp_compile` and `mp_entry%`, which fills the registry of `mpc`,
name the missing theorem, and an `Entry` cannot be built without the proof. A program with
`p.safe` compiles to the bytes that `mpc` writes for it.

The refused programs are one with no safety proof, two whose step or invariant has open goals,
one whose `safe` is the incomplete-proof marker and one whose `safe` rests on a user axiom. Each
`#guard_msgs` fails if its command succeeds, and the byte comparison fails if `#mp_compile` and
`Entry.emit` disagree. Unknown target names are refused too.
-/

namespace Millipede.Tests.Driver

open Millipede Std.WP

/-- A program with no safety proof at all. -/
def noSafe : Program := Examples.exit42

/-- error: refused: `Millipede.Tests.Driver.noSafe.safe` is not proved. `compile_sound` needs `Millipede.Tests.Driver.noSafe.Safe`, so an image of `Millipede.Tests.Driver.noSafe` would carry no guarantee. -/
#guard_msgs in
#mp_compile noSafe ".lake/test-driver-nosafe"

/-- error: refused: `Millipede.Tests.Driver.noSafe.safe` is not proved. `compile_sound` needs `Millipede.Tests.Driver.noSafe.Safe`, so an image of `Millipede.Tests.Driver.noSafe` would carry no guarantee. -/
#guard_msgs in
example : Entry := mp_entry% "nosafe" "" noSafe

mp extern noreturn "exit" dExit (code : UInt64) : UInt64

mp def hInit : UInt64 := 0
set_option mp.autoSafe false in
mp def hStep (r : &mut UInt64) : Unit := do
  r := r +! 1
  if r == 5 then
    let _x := dExit 0
    ()
  else ()

-- An `mp program` whose `step` has an unproved obligation: `p.safe` is not generated.
/-- info: `half.safe` is not generated: `Millipede.Tests.Driver.hStep.safe` must be proved first -/
#guard_msgs in
mp program half (root : UInt64) init hInit step hStep

/-- error: refused: `Millipede.Tests.Driver.half.safe` is not proved. `compile_sound` needs `Millipede.Tests.Driver.half.Safe`, so an image of `Millipede.Tests.Driver.half` would carry no guarantee. Missing: `Millipede.Tests.Driver.hStep.safe` (see the messages at their definitions; prove each with `mp prove`). -/
#guard_msgs in
#mp_compile half ".lake/test-driver-half"

-- A program whose invariant goals are open.
set_option mp.autoSpec false in
/-- info: `halfInv.inv_init` was not proved automatically; prove it with `mp prove halfInv.inv_init := …` (the goal is `Millipede.Tests.Driver.halfInv.InvInitGoal`)
---
info: `halfInv.inv_step` was not proved automatically; prove it with `mp prove halfInv.inv_step := …` (the goal is `Millipede.Tests.Driver.halfInv.InvStepGoal`) -/
#guard_msgs in
mp program halfInv (root : UInt64) init hInit step hStep invariant (fun r => r < 5)

/-- error: refused: `Millipede.Tests.Driver.halfInv.safe` is not proved. `compile_sound` needs `Millipede.Tests.Driver.halfInv.Safe`, so an image of `Millipede.Tests.Driver.halfInv` would carry no guarantee. Missing: `Millipede.Tests.Driver.hStep.safe`, `Millipede.Tests.Driver.halfInv.inv_init`, `Millipede.Tests.Driver.halfInv.inv_step` (see the messages at their definitions; prove each with `mp prove`). -/
#guard_msgs in
#mp_compile halfInv ".lake/test-driver-halfinv"

/-! ## A `p.safe` that is not a complete proof is refused

The seeded theorems are added with `addDecl` as kernel terms built by hand, so no source text
here contains the keywords that `scripts/check.sh` searches for. -/

/-- A program whose `safe` is the incomplete-proof marker. -/
def sorried : Program := Examples.exit42
/-- A program whose `safe` rests on a user axiom. -/
def axed : Program := Examples.exit42

open Lean Elab Command in
#guard_msgs (drop warning) in
run_cmd liftCoreM do
  let ty (p : Name) := mkApp (mkConst ``Program.Safe) (mkConst p)
  addDecl <| .thmDecl
    { name := ``sorried ++ `safe, levelParams := [], type := ty ``sorried
      value := mkApp2 (mkConst ``sorryAx [Level.zero]) (ty ``sorried) (toExpr false) }
  addDecl <| .axiomDecl
    { name := `Millipede.Tests.Driver.trustMe, levelParams := [], type := ty ``axed,
      isUnsafe := false }
  addDecl <| .thmDecl
    { name := ``axed ++ `safe, levelParams := [], type := ty ``axed
      value := mkConst `Millipede.Tests.Driver.trustMe }

/-- error: refused: `Millipede.Tests.Driver.sorried.safe` depends on [sorryAx] (`sorryAx`: an incomplete proof, or one with elaboration errors), axioms `#audit` rejects; the ledger would claim a safety proof that does not exist -/
#guard_msgs in
#mp_compile sorried ".lake/test-driver-sorried"

/-- error: refused: `Millipede.Tests.Driver.sorried.safe` depends on [sorryAx] (`sorryAx`: an incomplete proof, or one with elaboration errors), axioms `#audit` rejects; the ledger would claim a safety proof that does not exist -/
#guard_msgs in
example : Entry := mp_entry% "sorried" "" sorried

/-- error: refused: `Millipede.Tests.Driver.axed.safe` depends on [Millipede.Tests.Driver.trustMe], axioms `#audit` rejects; the ledger would claim a safety proof that does not exist -/
#guard_msgs in
#mp_compile axed ".lake/test-driver-axed"

/-- error: refused: `Millipede.Tests.Driver.axed.safe` depends on [Millipede.Tests.Driver.trustMe], axioms `#audit` rejects; the ledger would claim a safety proof that does not exist -/
#guard_msgs in
example : Entry := mp_entry% "axed" "" axed

/-! ## Target names: one spelling, unknown names refused

`#mp_compile p "out" "T"`, `mpc --target T` and `MP_TARGET=T` all take a target's full name,
`x64-linux` or `arm64-linux`, and refuse any other name before writing a file. -/

/-- error: unknown target 'arm65' (known: x64-linux, arm64-linux) -/
#guard_msgs in
#mp_compile Examples.PoolTally.prog ".lake/test-driver-arm65" "arm65"

/-- info: false -/
#guard_msgs in
#eval System.FilePath.pathExists ".lake/test-driver-arm65"

#guard (Target.ofOption (some "arm64")).toBool == false
#guard (Target.ofOption (some "a64")).toBool == false
#guard ((Target.ofOption (some "arm64-linux")).toOption.map (·.name)) == some "arm64-linux"
#guard ((Target.ofOption none).toOption.map (·.name)) == some "x64-linux"

#guard_msgs (drop info) in
#mp_compile Examples.PoolTally.prog ".lake/test-driver-pooltally-a64" "arm64-linux"

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let l ← IO.FS.readFile ".lake/test-driver-pooltally-a64.ledger.txt"
  return (l.splitOn "Millipede.compile_sound_arm64 (no hypotheses)").length == 2

/-! ## A proved program compiles to the bytes `mpc` writes -/

#guard_msgs (drop info) in
#mp_compile Examples.PoolTally.prog ".lake/test-driver-pooltally"

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let a ← IO.FS.readBinFile ".lake/test-driver-pooltally"
  -- what `lake exe mpc pooltally -o FILE` runs
  let some e := Examples.registry.find? (·.name == "pooltally") | return false
  let .ok _ ← e.emit ".lake/test-driver-mpc-pooltally" | return false
  let b ← IO.FS.readBinFile ".lake/test-driver-mpc-pooltally"
  let l ← IO.FS.readFile ".lake/test-driver-pooltally.ledger.txt"
  return a.data == b.data && a.size > 0 &&
    (l.splitOn "safety    : Millipede.Examples.PoolTally.prog.safe : p.Safe").length == 2

-- Every registered instance names its safety theorem.
#guard Examples.registry.all (·.safeThm.endsWith ".safe")

end Millipede.Tests.Driver
