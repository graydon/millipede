import Tests.Differential.SlotFuncs
import Tests.Differential.LoopFuncs
import Tests.Differential.PairFuncs
import Tests.Differential.InPlaceFuncs
import Tests.Differential.Cost
import Tests.Differential.IoTest
import Millipede.Top.Examples
import Tests
import Tests.Differential.Main

/-! # The calibration of `X64.κ` and `A64.κ`

Each target's cost model (`X64.κ` in Millipede/Target/X64/Select.lean, `A64.κ` in
Millipede/Target/A64/Select.lean) charges machine instructions per Core construct, and `compile`
refuses a program whose selected code the charges do not cover (the target's `budgetOk`). This
tool searches for small weights for which every test program passes that check. The programs are
every differential harness, every cost program, every `mpc` instance, the key-value server and
the test programs below, each as written, with every Core pass on and with every pass but one, and
each at the three register-allocation settings the gate compiles with (`KAPPA_MODES`, default
`default,slots,off`).

The search starts from `start`, which gives each construct roughly the instructions of its
selected code on the common path, and scales all of it until every program is covered. The
budget check lets the weights of one step pay for each other's instructions, so many weightings
cover the same programs; the search then lowers each weight in turn to the least value that still
covers every program, twice over, beginning with the weights that loops multiply. It prints the
result with a margin of `KAPPA_MARGIN` percent (25 by default), rounded up. Without `KAPPA_FULL`
it only checks the installed model. `KAPPA_START` replaces the scaled start, `KAPPA_FLOOR` gives the
least value of each weight in the descent and `KAPPA_PASSES` the number of passes (2). With
`KAPPA` set to fifteen weights in the order of
`fields` it checks those, on the programs optimised at those weights.

Run it after `lake build Tests` with `KAPPA_FULL=1 lake env lean scripts/kappa.lean`, which takes
about half an hour. For arm64 set `MP_TARGET=arm64-linux`. It is not part of the build. -/

open Millipede Millipede.Tests.Differential

def progs : List (String × Program) :=
  (allFuncs.map fun f => (f.name, f.program)) ++ costProgs ++
  (Examples.registry.map fun e => (e.name, e.prog)) ++ [("io", Tests.Differential.ioProg)] ++
  [("catProg", Tests.ByteBuf.catProg), ("tProg", Tests.Bytes.tProg), ("ptCount", Tests.Lin.ptCount),
   ("ptProgL", Tests.LoopRef.ptProg), ("ptProg", Tests.Lower.ptProg), ("swapProg", Tests.PairRef.swapProg),
   ("wideProg", Tests.Top.wideProg), ("wideExit", Tests.Top.wideExit), ("narrowProg", Tests.Top.narrowProg),
   ("dropResult", Tests.Top.dropResult), ("tally", Examples.PoolTally.prog),
   ("kvsrv", Tests.FormatKV.kvsrv)]

/-- The target calibrated: arm64 if the environment variable `MP_TARGET` is `arm64-linux`, else x64. -/
def a64 : Bool := (unsafe unsafeIO (IO.getEnv "MP_TARGET")).toOption.join == some "arm64-linux"

/-- The weights that `KAPPA` gives (fifteen comma-separated numbers in the order of `fields`). -/
def given : Option (List Nat) :=
  (unsafe unsafeIO (IO.getEnv "KAPPA")).toOption.join.map fun ks => (ks.splitOn ",").map String.toNat!

/-- The target's installed cost model and frame model. -/
def installed : CostModel := if a64 then A64.κ else X64.κ
def φ : FrameModel := if a64 then A64.φ else X64.φ

/-- The register-allocation settings that the gate compiles with: the default, slot locations only
(`MP_REGALLOC=slots`) and allocation off (`MP_REGALLOC=0`). `KAPPA_MODES` selects some of them by
name. -/
def allModes : List (String × Compile.Options) :=
  [("default", {}), ("slots", { regs := some 0 }), ("off", { regalloc := false })]

def modes : List (String × Compile.Options) :=
  match (unsafe unsafeIO (IO.getEnv "KAPPA_MODES")).toOption.join with
  | some m => allModes.filter fun (n, _) => (m.splitOn ",").contains n
  | none => allModes

/-- The Core pass configurations: none, all, and all but one for each pass. -/
def configs : List (String × Opt.Config) :=
  [("", Opt.Config.none), ("+opt", Opt.Config.all)] ++
    Opt.names.map fun n => (s!"+opt-{n}", Opt.Config.all.off n)

/-- Each program in each configuration of `configs`, optimised at cost model `κ0` (`compile`
optimises at the cost model it then checks), linearized and allocated as `compile` does in each
mode of `modes`. -/
def lins (κ0 : CostModel) : List (String × Lin.Prog × Compile.Options) :=
  modes.flatMap fun (mn, o) =>
    (progs.flatMap fun (n, p) => configs.map fun (cn, c) => (n ++ cn, c.optimize κ0 φ p)).filterMap
      fun (n, p) =>
        match Flat.lower p with
        | .ok fp => some (s!"{n}/{mn}", (if a64 then Compile.a64Prep o else Compile.x64Prep o)
            (Lin.linearize fp p.memBytes), o)
        | .error _ => none

/-- Each program with its instruction counts as `compile` uses them, computed once: at the
register locations it selects with (`kcUsed`) and its validated live sets (`RegAlloc.Live.of`). -/
def countsOf (κ0 : CostModel) : List (String × Lin.Prog × Sel.Counts) :=
  (lins κ0).map fun (n, P, o) =>
    let lvo := RegAlloc.Live.of P
    (n, P, if a64 then
        let kc := RegAlloc.A64Reg.kcUsed (Compile.a64K o) (Compile.a64C o) P o.memBase
        RegAlloc.A64Reg.counts kc.1 kc.2 o.memBase lvo
      else let kx := X64.kcUsed (Compile.x64K o) (Compile.x64C o) P o.memBase
        X64.counts kx.1 kx.2 o.memBase lvo)

/-- The programs of the search, optimised at the installed weights. -/
def withCounts : List (String × Lin.Prog × Sel.Counts) := countsOf installed

/-- The target's budget check on the program as `compile` selects it, which is after the validated
allocation (`Compile.x64Prep`, `Compile.a64Prep`), at the counts of `withCounts`. -/
def budgetOk (κ : CostModel) (P : Lin.Prog) (c : Sel.Counts) : Bool :=
  Sel.budgetOk c κ P (Sel.potential c κ P).get

def okWith (κ : CostModel) : List String :=
  withCounts.filterMap fun (n, P, c) => if budgetOk κ P c then none else some n

def fields : List String :=
  ["word", "mem", "place", "ref", "ctor", "atom", "let_", "ite", "prim", "div", "call", "match_",
   "ext", "loop", "iter"]

def getF (κ : CostModel) : String → Nat
  | "atom" => κ.atom | "let_" => κ.let_ | "ite" => κ.ite | "prim" => κ.prim | "div" => κ.div
  | "loop" => κ.loop | "iter" => κ.iter | "call" => κ.call | "ctor" => κ.ctor
  | "match_" => κ.match_ | "ext" => κ.ext | "word" => κ.word | "place" => κ.place
  | "mem" => κ.mem | "ref" => κ.ref | _ => 0

def setF (κ : CostModel) (f : String) (v : Nat) : CostModel :=
  match f with
  | "atom" => { κ with atom := v } | "let_" => { κ with let_ := v } | "ite" => { κ with ite := v }
  | "prim" => { κ with prim := v } | "div" => { κ with div := v } | "loop" => { κ with loop := v }
  | "iter" => { κ with iter := v } | "call" => { κ with call := v } | "ctor" => { κ with ctor := v }
  | "match_" => { κ with match_ := v } | "ext" => { κ with ext := v } | "word" => { κ with word := v }
  | "place" => { κ with place := v } | "mem" => { κ with mem := v } | "ref" => { κ with ref := v }
  | _ => κ

def showK (κ : CostModel) : String :=
  ", ".intercalate (fields.map fun f => s!"{f} := {getF κ f}")

/-- Binary search the least value of one weight (others fixed) keeping every program covered. -/
partial def least (κ : CostModel) (f : String) (lo hi : Nat) : Nat :=
  if lo ≥ hi then hi
  else
    let mid := (lo + hi) / 2
    if (okWith (setF κ f mid)).isEmpty then least κ f lo mid else least κ f (mid + 1) hi

/-- The order of the descent: the weights that loops multiply first, so that they are lowered
before the others absorb the instructions they pay for. -/
def order : List String :=
  ["prim", "iter", "word", "mem", "place", "atom", "let_", "ite", "ctor", "match_", "ref", "div",
    "loop", "ext", "call"]

/-- Fifteen comma-separated weights from environment variable `v`, in the order of `fields`. -/
def envK (v : String) : Option CostModel :=
  (unsafe unsafeIO (IO.getEnv v)).toOption.join.map fun ks =>
    (fields.zip ((ks.splitOn ",").map String.toNat!)).foldl (fun κ (f, n) => setF κ f n) installed

/-- The least value of each weight in the descent: `KAPPA_FLOOR`, or 0. -/
def floor : CostModel := (envK "KAPPA_FLOOR").getD (fields.foldl (fun κ f => setF κ f 0) installed)

/-- Lower each weight in turn to the least value, not below `floor`, at which every program still
passes, the others fixed, for `n` passes over the weights; each step is printed. -/
def descend (κ : CostModel) : Nat → IO CostModel
  | 0 => pure κ
  | n + 1 => do
    let mut κ := κ
    for f in order do
      let v := least κ f (min (getF floor f) (getF κ f)) (getF κ f)
      let why := if v > getF floor f then s!", {v - 1} refuses {(okWith (setF κ f (v - 1))).take 4}" else ""
      IO.println s!"  {f}: {getF κ f} → {v}{why}"
      κ := setF κ f v
    descend κ n

/-- Every weight raised by `m` percent, rounded up. -/
def withMargin (m : Nat) (κ : CostModel) : CostModel :=
  fields.foldl (fun κ f => setF κ f ((getF κ f * (100 + m) + 99) / 100)) κ

/-- The starting proportions: roughly the instructions of each construct's selected x64 code on
its common path. -/
def start : CostModel :=
  [("word", 3), ("mem", 3), ("place", 2), ("ref", 3), ("ctor", 3), ("atom", 3), ("let_", 1),
    ("ite", 3), ("prim", 4), ("div", 6), ("call", 15), ("match_", 3), ("ext", 8), ("loop", 4),
    ("iter", 4)].foldl (fun κ (f, v) => setF κ f v) installed

/-- Every weight of `start` scaled to `p` percent, rounded up. -/
def scaleS (p : Nat) : CostModel :=
  fields.foldl (fun κ f => setF κ f ((getF start f * p + 99) / 100)) start

/-- The least percentage, from `lo` to `hi`, at which `scaleS p` covers every program. -/
partial def leastScaleS (lo hi : Nat) : Nat :=
  if lo ≥ hi then hi
  else
    let mid := (lo + hi) / 2
    if (okWith (scaleS mid)).isEmpty then leastScaleS lo mid else leastScaleS (mid + 1) hi

def calibrate : IO Unit := do
  IO.println s!"target {if a64 then "arm64" else "x64"}, modes {modes.map (·.1)}, {withCounts.length} programs"
  -- `KAPPA` = fifteen comma-separated weights in the order of `fields`: check those instead, on
  -- the programs optimised at those weights
  if let some vs := given then
    let κ := (fields.zip vs).foldl (fun κ (f, v) => setF κ f v) installed
    let refused := (countsOf κ).filterMap fun (n, P, c) => if budgetOk κ P c then none else some n
    IO.println s!"κ ({showK κ}) refuses: {refused}"
    return
  IO.println s!"installed κ ({showK installed}) refuses: {okWith installed}"
  if (← IO.getEnv "KAPPA_FULL").isNone then return
  -- the starting proportions scaled until every program is covered (or `KAPPA_START`), then each
  -- weight lowered in turn to its least value
  let κs ← match envK "KAPPA_START" with
    | some κ => pure κ
    | none => do
      let p := leastScaleS 1 10000
      IO.println s!"the starting weights at {p}%"
      pure (scaleS p)
  unless (okWith κs).isEmpty do
    IO.println s!"the starting weights do not cover {okWith κs}"
    return
  IO.println s!"the starting weights cover every program: {showK κs}"
  let κl ← descend κs (((← IO.getEnv "KAPPA_PASSES").bind String.toNat?).getD 2)
  IO.println s!"least weights: {showK κl}; refuses: {okWith κl}"
  let m := ((← IO.getEnv "KAPPA_MARGIN").bind String.toNat?).getD 25
  let κm := withMargin m κl
  IO.println s!"with a margin of {m}%: {showK κm}; refuses: {okWith κm}"

#eval calibrate
