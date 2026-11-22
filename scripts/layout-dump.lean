import Tests.Layout
/-! Prints `Tests.Layout.report` for `scripts/layout-check.sh`. With an argument it prints the
report of a layout with a seeded bug instead, for the self-test. `notail` lays out structs without
tail padding and `noalign` packs struct fields without alignment. -/
open Millipede Millipede.Tests.Layout

/-- Field offsets with no alignment padding, for the `noalign` bug. -/
def packed : Nat → List Shape → List Nat
  | _, [] => []
  | off, s :: ss => off :: packed (off + s.size) ss

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.print (report)
  | ["notail"] => IO.print (report fun
      | .prod fs => (Shape.prodEnd 0 fs, Shape.alignMax fs, Shape.prodOffsets 0 fs)
      | s => layout s)
  | ["noalign"] => IO.print (report fun
      | .prod fs => ((fs.map Shape.size).sum, Shape.alignMax fs, packed 0 fs)
      | s => layout s)
  | _ => throw (IO.userError "usage: layout-dump [notail|noalign]")
