import Millipede.Meta.Burden

/-- Prints the burden report of the text on standard input, classified by
`Millipede.Meta.Burden.classify`, which `#mp_report` also uses. `scripts/proof-burden.sh` runs it. -/
def main : IO Unit := do
  let src ← (← IO.getStdin).readToEnd
  IO.println (Millipede.Meta.Burden.classify src).report
