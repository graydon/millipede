import Millipede.Top.Examples
import Millipede.Meta.Audit

/-!
# Tests for the evidence that the ledger names

For each target this suite renders the ledger and requires that every `scripts/…` and
`Tests/….lean` it names exists. The ledger's pipeline line must name the allocation and the
selector that the backend runs, with the register locations and their registers, or say that
allocation is off. Each target's ledger must name the scripts that give its evidence, and the
arm64 ledger must not claim that its images run under qemu. The modules named as the only users
of `bv_decide` must be exactly the target's encode and decode modules on the allow-list of
`#audit`.

Three of the guards below fail on an arm64 ledger that names no co-simulation script, says that
its images run under qemu, or names no file for its `bv_decide` lemmas.
-/

namespace Millipede.Tests.Ledger

open Millipede

/-- The words of `s` that start with `pfx`, each ending before the first character that cannot
be in a path, with trailing dots dropped. -/
def mentions (pfx : String) (s : String) : List String :=
  let isPath (c : Char) := c.isAlphanum || c == '/' || c == '.' || c == '-' || c == '_'
  let rec words : List Char → List Char → List String
    | [], cur => [String.ofList cur.reverse]
    | c :: cs, cur => if isPath c then words cs (c :: cur) else String.ofList cur.reverse :: words cs []
  let trim (w : String) : String := String.ofList (w.toList.reverse.dropWhile (· == '.')).reverse
  ((words s.toList []).filter (·.startsWith pfx)).map trim

def text (t : Target) : String := ledger "exit42" "" Examples.exit42 0 "Examples.exit42.safe" t

/-- Every `scripts/…` and `Tests/….lean` the ledger of `t` names exists. -/
def evidenceExists (t : Target) : IO Bool := do
  let ps := mentions "scripts/" (text t) ++ (mentions "Tests/" (text t)).filter (·.endsWith ".lean")
  let mut ok := !ps.isEmpty
  for p in ps do
    unless ← System.FilePath.pathExists p do
      IO.eprintln s!"{t.name}: the ledger names {p}, which does not exist"; ok := false
  return ok

/-- info: true -/
#guard_msgs in
#eval evidenceExists x64Linux

/-- info: true -/
#guard_msgs in
#eval evidenceExists arm64Linux

def contains (s pat : String) : Bool := (s.splitOn pat).length > 1

#guard ["scripts/a64-cosim.sh", "scripts/a64-encode-check.sh", "scripts/a64-elf-check.sh",
  "scripts/loader-a64.sh", "scripts/differential-a64.sh", "scripts/mpc-check.sh"].all
  (mentions "scripts/" (text arm64Linux)).contains
#guard ["scripts/x64-encode-check.sh", "scripts/cosim.sh", "scripts/mpc-check.sh"].all
  (mentions "scripts/" (text x64Linux)).contains

-- arm64 images run natively, and the images of both targets are run on the model.
#guard !contains (text arm64Linux) "under qemu"
#guard contains (text arm64Linux) "runs the images natively"
#guard contains (text arm64Linux) "Tests/Top.lean compares the model run with the source"
#guard contains (text x64Linux) "Tests/Top.lean compares the model run with the source"

-- The pipeline line names the backend's passes as they run, with the default number of
-- register locations, their registers and the selector, and says so when allocation is off or
-- there are no register locations.
#guard contains (text arm64Linux)
  s!"validated register allocation with {RegAlloc.A64Reg.kDefault} register locations x19..x{18 + RegAlloc.A64Reg.kDefault}"
#guard contains (text arm64Linux) s!"select (A64Reg.select {RegAlloc.A64Reg.kDefault}"
#guard contains (ledger "e" "" Examples.exit42 0 "" arm64Linux { regalloc := false })
  "no register allocation" &&
  contains (ledger "e" "" Examples.exit42 0 "" arm64Linux { regalloc := false }) "A64Reg.select 0"
#guard contains (ledger "e" "" Examples.exit42 0 "" arm64Linux { regs := some 0 }) "regs := (some 0)"
#guard contains (text x64Linux) s!"validated register allocation with {X64.maxK} register locations rbx rbp r12 r13 r14 r15"
#guard contains (text x64Linux) s!"select (X64.select {X64.maxK}"
#guard contains (ledger "e" "" Examples.exit42 0 "" x64Linux { regs := some 0 })
  "validated register allocation with 0 register locations"
#guard contains (ledger "e" "" Examples.exit42 0 "" x64Linux { regalloc := false }) "X64.select 0"

/-- The `bv_decide` modules named for `t` are those of `Audit.bvDecideMods` under `isaDir`. -/
def encModsNamed (t : Target) (isaDir : String) : Bool :=
  let L := LedgerTarget.of t
  let mods := Meta.Audit.bvDecideMods.filterMap fun m =>
    match m with
    | .str (.str (.str (.str .anonymous "Millipede") "Target") d) f =>
      if d == isaDir then some (f ++ ".lean") else none
    | _ => none
  !mods.isEmpty && mods.all (contains L.trustedEnc) &&
    contains L.trustedEnc s!"Millipede/Target/{isaDir}/"

-- x64 uses no `bv_decide` module, and its ledger says the theorem depends on none.
#guard !Meta.Audit.bvDecideMods.any (fun m => (m.toString.splitOn "Target.X64").length > 1) &&
  contains (LedgerTarget.of x64Linux).trustedEnc "none of which this theorem depends on"
#guard encModsNamed arm64Linux "A64"

end Millipede.Tests.Ledger
