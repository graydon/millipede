import Millipede.Opt.Rules

/-!
# Which Core passes run

`Config` has one switch per pass, all on by default, and the number of rounds for which the list
of passes is repeated, so that a later round folds what an earlier one exposed, such as a constant
that inlining produced. `Config.optimize κ φ p` runs the enabled passes, each applied under the
resource guard. With every switch off it returns `p` itself, so `Config.none` gives the
unoptimised compiler.

`Config.parse` reads the option string of the drivers, from `MP_OPT` or `mpc --opt`. It is `all`,
`none`, or a comma-separated list of pass names, each optionally prefixed with `-`. Names alone
enable only those passes, and `-name` entries disable those passes and keep the rest on.
-/

namespace Millipede.Opt

/-- The switches of the Core passes. -/
structure Config where
  /-- the number of rounds of the list of passes -/
  rounds : Nat := 2
  /-- the names of the enabled passes -/
  on : List String := []
deriving Repr, BEq

/-- The registered passes, in the order they run within a round. -/
def registry : List Pass := [inlinePass, foldPass, dcePass, strengthPass]

/-- The names of the registered passes. -/
def names : List String := registry.map (·.name)

/-- Every pass on. -/
def Config.all : Config := { on := names }

/-- Every pass off, which gives the unoptimised compiler. -/
def Config.none : Config := { on := [] }

/-- The enabled passes, in registry order. -/
def Config.passes (o : Config) : List Pass := registry.filter (o.on.contains ·.name)

/-- The optimiser, which runs the enabled passes `o.rounds` times at cost model `κ` and frame model
`φ`, each under the resource guard. -/
def Config.optimize (o : Config) (κ : CostModel) (φ : FrameModel) (p : Program) : Program :=
  if o.passes.isEmpty then p else Opt.rounds κ φ o.passes o.rounds p

/-- The optimised program is an optimisation of the source. -/
theorem Config.optimize_sim (o : Config) (κ : CostModel) (φ : FrameModel) (p : Program) :
    (o.optimize κ φ p).Sim κ φ p := by
  unfold Config.optimize; split
  · exact Sim.refl p
  · exact rounds_sim κ φ _ _ p

/-- With every pass off, the optimiser is the identity. -/
theorem Config.optimize_none (κ : CostModel) (φ : FrameModel) (p : Program) :
    Config.none.optimize κ φ p = p := by
  simp [Config.optimize, Config.passes, Config.none]

/-- Reads an option string, which is `all`, `none`, or comma-separated pass names, where `name`
enables only the named passes and `-name` disables one and keeps the rest. An unknown name is
refused. -/
def Config.parse (s : String) : Except String Config :=
  let items := (s.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")
  if items == ["all"] || items.isEmpty then .ok Config.all
  else if items == ["none"] then .ok Config.none
  else
    let bad := items.filter fun i => !names.contains (if i.startsWith "-" then (i.drop 1).toString else i)
    if !bad.isEmpty then
      .error s!"unknown optimisation pass(es) {bad} (known: {", ".intercalate names})"
    else if items.all (·.startsWith "-") then
      .ok { on := names.filter fun n => !items.contains ("-" ++ n) }
    else if items.any (·.startsWith "-") then
      .error "MP_OPT: either names (enable only those) or -names (disable those), not both"
    else .ok { on := names.filter items.contains }

/-- The configurations that enable the proper prefixes of `o`'s passes, longest first, to which
`compileWith` falls back when the pipeline refuses the optimised program. -/
def Config.prefixes (o : Config) : List Config :=
  (List.range o.on.length).reverse.map fun n => { o with on := o.on.take n }

/-- The passes that a configuration enables and its rounds, for the ledger, or `none` when no pass
is enabled. -/
def Config.describe (o : Config) : String :=
  if o.passes.isEmpty then "none"
  else s!"{", ".intercalate (o.passes.map (·.name))} ({o.rounds} rounds)"

/-- The configuration with pass `n` switched off. -/
def Config.off (o : Config) (n : String) : Config := { o with on := o.on.filter (· ≠ n) }

end Millipede.Opt
