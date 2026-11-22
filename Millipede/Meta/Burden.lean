/-!
# The proof-burden classifier

This module classifies source lines for `scripts/proof-burden.sh`, which runs it on a file or a
region of one through `lake env lean --run scripts/burden.lean`, so that the two report the same
numbers. Each counted line falls into one of three kinds.
- Program lines are the headers and bodies of `mp def`, `mp extern` and `mp program`, data types
  declared with `structure`, `inductive` or `deriving Data`, and other `def`s. An implementation
  declared with `mp implementation` counts as program too.
- Contract lines are `requires`, `ensures` and `invariant` clauses, predicate definitions such as
  `def … : Prop`, `structure … : Prop` or `abbrev … : Prop`, and interfaces declared with
  `mp interface`. A header line with an inline `requires` counts as both program and contract.
- Proof lines are the statements and proofs of `theorem`, `lemma`, `example` and `mp prove`.

Comments, doc comments, blank lines, `open`, `namespace`, `end`, `set_option` and `variable`,
attributes and `#`-commands are not counted. The aim is that contracts and proofs together stay
within about twice the program. The module imports nothing but `Init`, because the script runs
it without the library.
-/

namespace Millipede.Meta.Burden

/-- The kinds of declarations. -/
inductive Kind where
  | program | contracts | proofs
deriving BEq, Inhabited

/-- The counts of a text, and its proof and contract declarations with their kind, name and
lines. -/
structure Counts where
  program : Nat := 0
  contracts : Nat := 0
  proofs : Nat := 0
  decls : Array (Kind × String × Nat) := #[]
deriving Inhabited

/-- Whether `s` starts with the keyword `kw`, followed by a space or the end. -/
def startsKw (s kw : String) : Bool :=
  s == kw || s.startsWith (kw ++ " ")

/-- `s` without its leading modifiers, which are `private`, `protected`, `noncomputable`,
`open … in`, and attributes `@[…]` before a keyword on the same line. -/
partial def dropModifiers (s : String) : String :=
  let mods := ["private ", "protected ", "noncomputable "]
  match mods.find? (fun m => s.startsWith m) with
  | some m => dropModifiers (s.drop m.length).toString
  | none =>
    if s.startsWith "@[" then
      match s.splitOn "] " with
      | _ :: rest@(_ :: _) => dropModifiers ("] ".intercalate rest)
      | _ => s
    else if s.startsWith "open " then
      match s.splitOn " in " with
      | _ :: rest@(_ :: _) => dropModifiers (" in ".intercalate rest)
      | _ => s
    else s

/-- The first `k` words of `s`. -/
def words (s : String) (k : Nat) : String :=
  " ".intercalate ((s.splitOn " ").filter (· ≠ "") |>.take k)

/-- Whether `s` contains one of the clause words `requires`, `ensures` or `invariant`, surrounded
by spaces. -/
def hasClause (s : String) : Bool :=
  ["requires", "ensures", "invariant"].any fun w => (s.splitOn s!" {w} ").length > 1

/-- `s` with a trailing `-- …` comment removed. -/
def stripComment (s : String) : String :=
  match s.splitOn "--" with
  | a :: _ => a.trimAscii.toString
  | [] => s

/-- Classify the lines of a text. -/
def classify (src : String) : Counts := Id.run do
  let mut c : Counts := {}
  let mut mode : Option Kind := none
  let mut depth : Int := 0
  let mut header := false
  let mut contract := false
  let skipKws := ["open", "namespace", "end", "section", "set_option", "variable", "universe",
    "attribute", "include", "omit"]
  for line in src.splitOn "\n" do
    let s := line.trimAscii.toString
    if depth > 0 || s.startsWith "/-" then
      depth := depth + ((s.splitOn "/-").length - 1 : Nat) - ((s.splitOn "-/").length - 1 : Nat)
      if depth < 0 then depth := 0
      continue
    let s := stripComment s
    if s.isEmpty then continue
    let first := dropModifiers s
    let isProp := (first.splitOn ": Prop").length > 1 || (first.splitOn ":Prop").length > 1
    if ["theorem", "lemma", "example", "mp prove"].any (startsKw first) then
      mode := some .proofs; header := false; contract := false
      c := { c with decls := c.decls.push (.proofs,
        words first (if first.startsWith "mp" then 3 else 2), 0) }
    else if (["def", "abbrev", "structure", "class"].any (startsKw first) && isProp) ||
        startsKw first "mp interface" then
      mode := some .contracts; header := false; contract := false
      c := { c with decls := c.decls.push (.contracts, words first 2, 0) }
    else if ["mp def", "mp extern", "mp program", "mp implementation"].any (startsKw first) then
      mode := some .program; header := true; contract := false
      c := { c with decls := c.decls.push (.program, words first 3, 0) }
    else if ["def", "abbrev", "structure", "inductive", "instance"].any (startsKw first) then
      mode := some .program; header := false; contract := false
      c := { c with decls := c.decls.push (.program, words first 2, 0) }
    else if (skipKws.any (startsKw first) || first.startsWith "#" || first.startsWith "@[") &&
        !line.startsWith " " then
      mode := none
      continue
    let some m := mode | continue
    if m == .program && header then
      if ["requires", "ensures", "invariant"].any (startsKw s) then contract := true
      if contract then
        c := { c with contracts := c.contracts + 1 }
        if (s.splitOn ":=").length > 1 then header := false; contract := false
        continue
      if (s.splitOn ":=").length > 1 then header := false
      if hasClause s then c := { c with contracts := c.contracts + 1 }
    c := match m with
      | .program => { c with program := c.program + 1 }
      | .contracts => { c with contracts := c.contracts + 1 }
      | .proofs => { c with proofs := c.proofs + 1 }
    if c.decls.size > 0 then
      let (k, n, l) := c.decls.back!
      c := { c with decls := c.decls.pop.push (k, n, l + 1) }
  return c

/-- The burden, which is contracts and proofs per program line as a percentage, rounded. -/
def Counts.percent (c : Counts) : Nat := ((c.contracts + c.proofs) * 1000 / max c.program 1 + 5) / 10

/-- The report `scripts/proof-burden.sh` prints. -/
def Counts.report (c : Counts) : String := Id.run do
  let mut out := ""
  for (k, n, l) in c.decls do
    if k != .program then
      let kind := if k == .proofs then "proof   " else "contract"
      out := out ++ s!"  {kind} {l} {n}\n"
  let r := c.percent
  out := out ++ s!"program    {c.program} lines\n"
  out := out ++ s!"contracts  {c.contracts} lines  (requires/ensures/invariant, predicate \
    definitions)\n"
  out := out ++ s!"proofs     {c.proofs} lines  (theorem/lemma/example/mp prove)\n"
  out := out ++ s!"burden     {r / 100}.{if r % 100 < 10 then "0" else ""}{r % 100} x program  \
    (target: about 2)"
  return out

end Millipede.Meta.Burden
