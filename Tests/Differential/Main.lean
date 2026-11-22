import Tests.Differential.Funcs
import Tests.Rand
import Tests.Differential.MemFuncs
import Tests.Differential.PtrFuncs
import Tests.Differential.SliceFuncs
import Tests.Differential.LoopFuncs
import Tests.Differential.DoFuncs
import Tests.Differential.GenericFuncs
import Tests.Differential.PairFuncs
import Tests.Differential.InPlaceFuncs
import Tests.Differential.ByteFuncs
import Tests.Differential.SubViewFuncs
import Tests.Differential.SlotFuncs
import Tests.Differential.UnitFuncs
import Tests.Differential.OverflowFuncs
import Tests.Differential.IoTest
import Tests.Differential.Cost
import Tests.Differential.Harness
import Tests.Differential.Mutants
import Tests.Select
import Tests.Differential.A64Mutants
import Tests.Differential.X64RegMutants
import Tests.Differential.LoaderA64
import Millipede.RegAlloc.Compile

/-!
# The differential test generator

`lake exe differential` builds the test programs that `scripts/differential.sh` runs under qemu.
The test program of a function is a reactor that reads its cases from standard input, calls the
function on each and compares the result with the value that the reference computed in Lean
(`Harness.lean`). It writes `.` when they are equal and `X` when they are not, and then exits with
status 0, so a run is correct exactly when its output is one dot per case. Because the arguments
are read at run time, the Core passes cannot evaluate the calls when the program is compiled, and
the function's machine code runs on every case. The inputs are fixed: edge values such as `0`,
`1`, `2^63` and `2^64-1`, crossed for two and three arguments, and pseudo-random words from a fixed
seed mixed with edge values. Before it generates anything, the generator compares the reference,
the `mp def` function and the denotation of the source term on every input, and a disagreement
stops the run.

The main commands are these:
* `differential list` prints the names of all the functions.
* `differential gen <dir> <name> [limit]` compiles the test program of one function for the
  target that `MP_TARGET` selects. It writes `<dir>/<name>.0.elf`, the input file
  `<dir>/<name>.0.in` and `<dir>/<name>.cases` with the line `0 <cases> stdin`.
* `differential show <name> <index>` prints the inputs and the expected value of one case.
* `differential refuse` checks that every program outside the fragment the pipeline accepts is
  refused with a `lower` error.
* `differential genmut <dir> <mutant> <name>` builds a harness with a seeded bug in one pass, from
  `Mutants.lean`, and `list-mutants`, `list-mem`, `list-ptr`, `list-alias` and `list-slot` list
  the mutants and the functions they run on.
* `differential cost <dir> [tag]` builds the programs of the cost regression of `Cost.lean`.
* `differential probe <dir> <name> <args…>` writes a program that exits with the function's value,
  as an aid to debugging.
* `differential loader-a64 <dir> [seed]` writes an arm64 image and the loader model's facts about
  its start, for `scripts/loader-a64.sh`.
-/

namespace Millipede.Tests.Differential

open Millipede

/-- Every differential function, the scalar ones first and then those over memory. -/
def allFuncs : List TestFn := funcs ++ memFuncs ++ ptrFuncs ++ sliceFuncs ++ loopFuncs ++ pairFuncs ++ inPlaceFuncs ++ byteFuncs ++ subViewFuncs ++ slotFuncs ++ unitFuncs ++ overflowFuncs ++ doFuncs ++ genericFuncs

/-- Edge values of `U64`. -/
def edges : List UInt64 :=
  [0, 1, 2, 3, 5, 7, 8, 9, 10, 15, 16, 31, 32, 33, 63, 64, 65, 100, 127, 128, 255, 256,
   65535, 65536, 0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFF, 0x100000000, 0x100000001,
   0x7FFFFFFFFFFFFFFE, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001,
   0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xDEADBEEFCAFEBABE]

/-- Edge values for crossing in two arguments. -/
def midEdges : List UInt64 :=
  [0, 1, 2, 3, 7, 8, 63, 64, 65, 255, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000,
   0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFE,
   0xFFFFFFFFFFFFFFFF, 0xDEADBEEFCAFEBABE]

/-- A small edge set for crossing in three arguments. -/
def smallEdges : List UInt64 :=
  [0, 1, 2, 0x80000000, 0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]

/-- One pseudo-random word together with the next seed. The word is an edge value ± 1, a full random
word, or a word of random magnitude, so that small and middling values occur too. -/
def randWord (seed : UInt64) : UInt64 × UInt64 :=
  let (s, a) := splitmix seed
  let (s, b) := splitmix s
  let w :=
    match a % 4 with
    | 0 => edges[(b % edges.length.toUInt64).toNat]! + (b >>> 40) % 3 - 1
    | 1 => b
    | 2 => b >>> ((a >>> 8) % 64)
    | _ => b <<< ((a >>> 8) % 64)
  (s, w)

/-- A random `k`-tuple. -/
def randTuple (seed : UInt64) : Nat → UInt64 × List UInt64
  | 0 => (seed, [])
  | k + 1 =>
    let (s, w) := randWord seed
    let (s, ws) := randTuple s k
    (s, w :: ws)

/-- `n` random `k`-tuples. -/
def randTuples (seed : UInt64) (k : Nat) : Nat → List (List UInt64)
  | 0 => []
  | n + 1 =>
    let (s, t) := randTuple seed k
    t :: randTuples s k n

/-- All `k`-tuples over `xs`, in which the first argument varies slowest. -/
def cross (xs : List UInt64) : Nat → List (List UInt64)
  | 0 => [[]]
  | k + 1 => xs.flatMap fun x => (cross xs k).map (x :: ·)

/-- The inputs of a function of the given arity. -/
def inputs : Nat → List (List UInt64)
  | 1 => edges.map ([·]) ++ randTuples 1 1 480
  | 2 => cross midEdges 2 ++ randTuples 2 2 300
  | 3 => cross smallEdges 3 ++ randTuples 3 3 200
  | n => randTuples 4 n 500

/-- The argument atoms for a call in the order of the parameter list, which puts the last source
parameter first. -/
def mkArgs {Γ : List Ty} : (n : Nat) → List UInt64 → Args Γ (List.replicate n Ty.u64)
  | 0, _ => .nil
  | n + 1, xs => .cons (.lit (t := Ty.u64) (xs.headD 0)) (mkArgs n xs.tail)

/-- Whether three evaluations agree on `xs`: the reference, the `mp def` function, and the
denotation of the source term in a fresh world. -/
def consistent (f : TestFn) (xs : List UInt64) : Bool :=
  let ω : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩
  let v := (f.exp.denote ω (mkEnv f.arity xs.reverse) World.init).1
  f.ref xs == f.fn xs && f.ref xs == v
where
  /-- the environment for the parameters -/
  mkEnv : (n : Nat) → List UInt64 → Env (List.replicate n Ty.u64)
    | 0, _ => .nil
    | n + 1, ys => .cons (t := Ty.u64) (ys.headD 0) (mkEnv n ys.tail)

/-- The line of a case, for `show`. -/
def showCase (f : TestFn) (xs : List UInt64) : String :=
  s!"{f.name} {xs} expected {f.ref xs}"

/-- The compiler options that the environment selects. `MP_REGALLOC` is unset for each target's default
number of register locations (`X64.kDefault`, `A64Reg.kDefault`), `0` for no allocation, `slots` for slot locations only, or a number `k` of
register locations, at most 6 on x64 and 10 on arm64. `MP_CREGS=<c>` sets the number of caller-saved
register locations (at most 3 on x64 and 9 on arm64), and `MP_S4ORDER=caller` / `callee` makes the
allocator try them first / last for every value (`Compile.Options.callerFirst`; `web`: first for
the values live across no call; unset: last, the default). `MP_OPT` selects
the Core passes. `MP_MEMBASE=0` turns `Compile.Options.memBase` off, so that every data access
computes its full address. When
`MP_OPT_STRICT` is set, a refused optimised program is an error instead of falling back to fewer
passes. -/
def envOpts : IO Compile.Options := do
  let ra ← IO.getEnv "MP_REGALLOC"
  let regs := match ra with
    | some "slots" => some 0
    | some v => v.toNat?
    | none => none
  let callerFirst := match ← IO.getEnv "MP_S4ORDER" with
    | some "caller" => some true
    | some "callee" => some false
    | some "web" => none
    | _ => some false
  return { regalloc := ra != some "0", regs, cregs := (← IO.getEnv "MP_CREGS").bind String.toNat?,
           callerFirst, memBase := (← IO.getEnv "MP_MEMBASE") != some "0",
           idOps := (← IO.getEnv "MP_IDOPS") != some "0",
           opt := ← Opt.Config.fromEnv,
           fallback := (← IO.getEnv "MP_OPT_STRICT").isNone }

/-- Compile with the options that the environment selects. -/
def compileEnv (p : Program) (t : Target) : IO (Except String ByteArray) := do
  return compileWith (← envOpts) p t

/-- Generate for `arm64Linux` if the environment variable `MP_TARGET` is `arm64-linux`, for
`x64Linux` if it is unset or `x64-linux`; any other value is refused. -/
def envA64 : IO Bool := do
  match Target.ofOption (← IO.getEnv "MP_TARGET") with
  | .ok t => return t.name == arm64Linux.name
  | .error e => throw (IO.userError e)

/-- The oracle of Linux running a program on the file `inp`: `read` returns the next bytes, at most
the capacity, and `write` reports every byte written. -/
def inputOracle (inp : List UInt8) : Oracle :=
  ⟨fun hist c =>
    if c.sym = "read" then
      let used := (hist.filter (·.sym = "read")).foldl (fun a e => a + (e.bytesOut.headD []).length) 0
      let bs := (inp.drop used).take (c.outCaps.headD 0)
      ⟨UInt64.ofNat bs.length, [bs]⟩
    else if c.sym = "write" then ⟨UInt64.ofNat (c.bytesIn.headD []).length, []⟩
    else ⟨0, []⟩⟩

/-- The step of the harness of `f`. -/
def TestFn.step (f : TestFn) : Exp [Ty.unit] Ty.unit := wordHarness f.name f.arity f.exp

/-- The program that tests `f`. -/
def TestFn.program (f : TestFn) : Program :=
  match f.custom with
  | some (q, _, _) => q
  | none => harnessProgram f.step

/-- Generate the ELF `<name>.0.elf` and the input file `<name>.0.in` of a function tested through
the stdin harness, and `<name>.cases` with the single line `0 <cases> stdin`. -/
def genHarness (comp : Program → Except String ByteArray) (dir : String) (limit : Nat) (f : TestFn)
    (h : Exp [Ty.unit] Ty.unit) : IO Bool := do
  if let some (prog, inp, n) := f.custom then
    match comp prog with
    | .error e => IO.eprintln s!"differential: {f.name}: compile failed: {e}"; return false
    | .ok b =>
      let path := s!"{dir}/{f.name}.0.elf"
      IO.FS.writeBinFile path b
      IO.setAccessRights path
        { user := { read := true, write := true, execution := true },
          group := { read := true, execution := true },
          other := { read := true, execution := true } }
      IO.FS.writeBinFile s!"{dir}/{f.name}.0.in" ⟨inp.toArray⟩
      IO.FS.writeFile s!"{dir}/{f.name}.cases" s!"0 {n} stdin\n"
      return true
  let ins := (inputs f.arity).take limit
  match ins.find? (fun xs => !consistent f xs) with
  | some xs =>
    IO.eprintln s!"differential: {f.name}: reference, mp def and denotation disagree on {xs}"
    return false
  | none =>
    match comp (harnessProgram h) with
    | .error e =>
      IO.eprintln s!"differential: {f.name}: compile failed: {e}"
      return false
    | .ok b =>
      let path := s!"{dir}/{f.name}.0.elf"
      IO.FS.writeBinFile path b
      IO.setAccessRights path
        { user := { read := true, write := true, execution := true },
          group := { read := true, execution := true },
          other := { read := true, execution := true } }
      IO.FS.writeBinFile s!"{dir}/{f.name}.0.in" ⟨(harnessInput f.ref ins).toArray⟩
      IO.FS.writeFile s!"{dir}/{f.name}.cases" s!"0 {ins.length} stdin\n"
      return true

/-- The command line of `lake exe differential`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for f in allFuncs do IO.println f.name
    return 0
  | "gen" :: dir :: name :: rest =>
    let limit := match rest with | n :: _ => n.toNat?.getD 1000000 | [] => 1000000
    match allFuncs.find? (·.name == name) with
    | none => IO.eprintln s!"unknown function {name}"; return 2
    | some f =>
      IO.FS.createDirAll dir
      let a64 ← envA64
      let o ← envOpts
      let comp := fun p => compileWith o p (if a64 then arm64Linux else x64Linux)
      let ok ← genHarness comp dir limit f f.step
      return if ok then 0 else 1
  | ["fires"] =>
    -- for each function, the Core passes that each lower the Core cost of its first test program
    -- on their own; scripts/opt-compare.sh samples functions where each pass fires
    let t := if (← envA64) then arm64Linux else x64Linux
    for f in allFuncs do
      let p := f.program
      let cost (q : Program) := q.init.cost t.κ .copy + q.step.cost t.κ q.stepHb
      let fired := Opt.names.filter fun n => cost (({ on := [n] } : Opt.Config).optimize t.κ t.φ p) < cost p
      IO.println s!"{f.name} {" ".intercalate fired}"
    return 0
  | ["domut"] =>
    -- the seeded bugs of the `do` translation (`DoFuncs.lean`, `doMutants`): each function,
    -- translated with its bug, must disagree with its reference on some generated input
    let ω : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩
    let mut bad := 0
    for (m, e, ref) in doMutants do
      let caught := (inputs 2).any fun xs =>
        ref xs != (e.denote ω (.cons (xs.getD 1 0) (.cons (xs.getD 0 0) .nil)) World.init).1
      IO.println s!"{if caught then "caught" else "MISSED"} {m}"
      unless caught do bad := bad + 1
    return if bad == 0 then 0 else 1
  | ["membuf", file] =>
    -- the hand-built Flat program that writes from a memory buffer, through the passes after
    -- lowering and the ELF writer; it skips the budget check, since it carries no cost ticks
    let P := Lin.linearize Tests.Select.membufFlat 16
    match (do let A ← X64.select 0 0 P; let obj ← X64.assemble A; Link.link (Compile.linkConfig P) [obj]) with
    | .error e => IO.eprintln s!"membuf: {e}"; return 1
    | .ok img =>
      match x64Linux.fmt.write img with
      | .error e => IO.eprintln s!"membuf: {e}"; return 1
      | .ok bs => IO.FS.writeBinFile file ⟨bs.toArray⟩; return 0
  | ["list-mutants"] =>
    for m in Mutant.all do IO.println m.name
    return 0
  | "cost" :: dir :: only =>
    -- the programs of the cost regression, each written to `<dir>/cost.<tag>.elf`
    IO.FS.createDirAll dir
    let a64 ← envA64
    for (tag, prog) in costProgs do
     if only.isEmpty || only.contains tag then
      match ← compileEnv prog (if a64 then arm64Linux else x64Linux) with
      | .error e => IO.eprintln s!"differential cost: {tag}: compile failed: {e}"; return 1
      | .ok b =>
        let path := s!"{dir}/cost.{tag}.elf"
        IO.FS.writeBinFile path b
        IO.setAccessRights path
          { user := { read := true, write := true, execution := true },
            group := { read := true, execution := true },
            other := { read := true, execution := true } }
    return 0
  | "io" :: dir :: rest =>
    -- the program of `IoTest.lean` that reads, processes and writes, as `<dir>/io.elf` and
    -- `<dir>/io.script`; `differential io <dir> <mutant>` compiles it with a seeded bug
    IO.FS.createDirAll dir
    let a64 ← envA64
    let o ← envOpts
    let comp : Except String ByteArray :=
      match rest with
      | [mt] => match Mutant.ofName mt with
        | some m => compileMut m ioProg o
        | none => .error s!"unknown mutant {mt}"
      | _ => compileWith o ioProg (if a64 then arm64Linux else x64Linux)
    match comp with
    | .error e => IO.eprintln s!"differential io: compile failed: {e}"; return 1
    | .ok b =>
      let path := s!"{dir}/io.elf"
      IO.FS.writeBinFile path b
      IO.setAccessRights path
        { user := { read := true, write := true, execution := true },
          group := { read := true, execution := true },
          other := { read := true, execution := true } }
      IO.FS.writeFile s!"{dir}/io.script" ioScript
      return 0
  | ["list-ptr"] =>
    for f in ptrFuncs ++ sliceFuncs ++ loopFuncs ++ pairFuncs ++ inPlaceFuncs ++ subViewFuncs do IO.println f.name
    return 0
  | ["list-alias", mt] =>
    -- the harnesses a copy mutant must fail and the functions a slot mutant must fail
    match Mutant.ofName mt with
    | some m => for n in aliasFor m ++ slotFor m do IO.println n
    | none => pure ()
    return 0
  | ["list-slot"] =>
    for f in slotFuncs do IO.println f.name
    return 0
  | ["list-mem"] =>
    for f in memFuncs do IO.println f.name
    return 0
  | ["genmut", dir, mt, name] =>
    -- the harness of a memory function compiled with a seeded bug in one pass
    match Mutant.ofName mt, (memFuncs ++ ptrFuncs ++ sliceFuncs ++ loopFuncs ++ pairFuncs ++ inPlaceFuncs ++ byteFuncs ++ subViewFuncs ++ slotFuncs ++ overflowFuncs).find? (·.name == name) with
    | some m, some f =>
      IO.FS.createDirAll dir
      let o ← envOpts
      return if ← genHarness (compileMut m · o) dir 1000000 f f.step then 0 else 1
    | _, _ => IO.eprintln "usage: differential genmut <dir> <mutant> <memory function>"; return 2
  | ["list-a64-mutants"] =>
    for m in a64Mutants do IO.println m.name
    return 0
  | ["list-a64-mutant-funcs", mt] =>
    match a64Mutants.find? (·.name == mt) with
    | some m => for f in m.funcs do IO.println f
                return 0
    | none => IO.eprintln s!"unknown arm64 mutant {mt}"; return 2
  | ["genmut-a64", dir, mt, name] =>
    match a64Mutants.find? (·.name == mt), allFuncs.find? (·.name == name) with
    | some m, some f =>
      IO.FS.createDirAll dir
      let o ← envOpts
      let ok ← genHarness (compileA64Mut m · o) dir 1000000 f f.step
      return if ok then 0 else 1
    | _, _ => IO.eprintln "usage: differential genmut-a64 <dir> <mutant> <function>"; return 2
  | ["list-areg-mutants"] =>
    for m in aregMutants do IO.println m.name
    return 0
  | ["list-areg-mutant-funcs", mt] =>
    match aregMutants.find? (·.name == mt) with
    | some m => for f in m.funcs do IO.println f
                return 0
    | none => IO.eprintln s!"unknown register-selector mutant {mt}"; return 2
  | ["genmut-areg", dir, mt, name] =>
    -- a register-selector mutant in the configuration that the environment selects
    match aregMutants.find? (·.name == mt), allFuncs.find? (·.name == name) with
    | some m, some f =>
      IO.FS.createDirAll dir
      let o ← envOpts
      let ok ← genHarness (compileARegMut o m ·) dir 1000000 f f.step
      return if ok then 0 else 1
    | _, _ => IO.eprintln "usage: differential genmut-areg <dir> <mutant> <function>"; return 2
  | ["list-xreg-mutants"] =>
    for m in xregMutants do IO.println m.name
    return 0
  | ["list-xreg-mutant-funcs", mt] =>
    match xregMutants.find? (·.name == mt) with
    | some m => for f in m.funcs do IO.println f
                return 0
    | none => IO.eprintln s!"unknown register-selector mutant {mt}"; return 2
  | ["genmut-xreg", dir, mt, name] =>
    -- an x64 register-selector mutant in the configuration that the environment selects
    match xregMutants.find? (·.name == mt), allFuncs.find? (·.name == name) with
    | some m, some f =>
      IO.FS.createDirAll dir
      let o ← envOpts
      let ok ← genHarness (compileXRegMut o m ·) dir 1000000 f f.step
      return if ok then 0 else 1
    | _, _ => IO.eprintln "usage: differential genmut-xreg <dir> <mutant> <function>"; return 2
  | ["time"] =>
    -- the time in milliseconds to compile the suite's programs on both targets with the options
    -- of the environment, and the share of the allocator and of its checker
    let o ← envOpts
    let ps := allFuncs.map (·.program)
    let lins := ps.filterMap fun p => match Flat.lower p with
      | .ok fp => some (Lin.linearize fp p.memBytes) | .error _ => none
    let t0 ← IO.monoMsNow
    let mut n := 0
    for p in ps do
      for t in [x64Linux, arm64Linux] do
        if (compileWith o p t).toBool then n := n + 1
    let t1 ← IO.monoMsNow
    let mut c := 0
    for P in lins do
      let (P', maps, _) := RegAlloc.Alloc.allocate { k := 0 } P
      c := c + P'.funs.length + maps.length
    let t2 ← IO.monoMsNow
    for P in lins do
      let (P', maps, _) := RegAlloc.Alloc.allocate { k := 0 } P
      if RegAlloc.check P P' maps then c := c + 1
    let t3 ← IO.monoMsNow
    IO.println s!"programs {ps.length}, compiled {n}: compile (both targets) {t1 - t0} ms; allocate {t2 - t1} ms; allocate + check {t3 - t2} ms ({c})"
    return 0
  | ["ra-stats", ks] =>
    -- the register allocator's statistics for each test program
    let k := ks.toNat?.getD 10
    let mut tot : RegAlloc.Stats := ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
    for f in allFuncs do
      let p := f.program
      match RegAlloc.stats k p with
      | .error _ => pure ()
      | .ok s =>
        IO.println s!"{f.name} fns={s.fns} identity={s.identity} websReg={s.websReg} websSlot={s.websSlot} frame={s.frame0}->{s.frame1} movs={s.movs} coalesced={s.coalesced} accepted={s.accepted}"
        tot := ⟨tot.fns + s.fns, tot.identity + s.identity, tot.websReg + s.websReg,
          tot.websSlot + s.websSlot, tot.frame0 + s.frame0, tot.frame1 + s.frame1,
          tot.movs + s.movs, tot.coalesced + s.coalesced, tot.accepted && s.accepted⟩
    IO.println s!"TOTAL fns={tot.fns} identity={tot.identity} websReg={tot.websReg} websSlot={tot.websSlot} frame={tot.frame0}->{tot.frame1} movs={tot.movs} coalesced={tot.coalesced} allAccepted={tot.accepted}"
    return 0
  | ["refuse"] =>
    -- each construct outside the pipeline's fragment must be refused with an error
    let mut bad := false
    for f in refusedFuncs ++ refusedPtrFuncs ++ refusedSliceFuncs ++ refusedInPlaceFuncs do
      match ← compileEnv f.program (if (← envA64) then arm64Linux else x64Linux) with
      | .error e =>
        -- a refusal of the pipeline naming the construct, not some other failure
        if (e.splitOn "lower").length < 2 then
          IO.eprintln s!"differential: {f.name} failed with an error that is not a lower refusal: {e}"
          bad := true
        else IO.println s!"refused {f.name}: {e}"
      | .ok _ =>
        IO.eprintln s!"differential: {f.name} compiled, but it is expected to be refused"
        bad := true
    return if bad then 1 else 0
  | "probe" :: dir :: name :: rest =>
    -- a program that exits with `f args mod 256`, to debug a failing case
    match allFuncs.find? (·.name == name) with
    | none => return 2
    | some f =>
      let xs := rest.map (·.toNat!.toUInt64)
      let e : Exp [] Ty.unit :=
        .let_ (.call f.name f.exp (mkArgs f.arity xs.reverse))
          (.let_ (.ext ExtSig.exit (.word (.var .here) .nil)) (.atom (.lit (t := Ty.unit) ())))
      match compileWith (← envOpts) ⟨Ty.unit, e, Examples.keepUnit.exp⟩ x64Linux with
      | .error m => IO.eprintln m; return 1
      | .ok b =>
        let path := s!"{dir}/probe.elf"
        IO.FS.writeBinFile path b
        IO.setAccessRights path
          { user := { read := true, write := true, execution := true },
            group := { read := true, execution := true },
            other := { read := true, execution := true } }
        IO.println s!"expected {f.ref xs} (mod 256: {(f.ref xs).toNat % 256})"
        return 0
  | ["budgets", name, input] =>
    -- the proved bounds of a registered program, for scripts/bound-check.sh: its stack bound
    -- `p.stackBytes`, and for each event of its run on `input` the instructions that may have
    -- run when the event happens, which is the sum of the step bounds up to the event's step, and
    -- that step
    match Examples.registry.find? (·.name == name) with
    | none => IO.eprintln s!"unknown program {name}"; return 2
    | some e =>
      let t := if (← envA64) then arm64Linux else x64Linux
      let κ := t.κ
      let inp := (← IO.FS.readBinFile input).toList
      let ω := inputOracle inp
      let p := e.prog
      let some n := (List.range 1000).find? (p.halted ω ·)
        | IO.eprintln s!"{name} does not exit within 1000 reactor steps"; return 1
      IO.println s!"stack {p.stackBytes t.φ}"
      IO.println s!"steps {n + 1} {p.stepCost 0 ω κ} {p.stepCost 1 ω κ}"
      let evs := p.events ω n
      for j in List.range evs.length do
        let k := ((List.range (n + 1)).find? fun k => (p.events ω k).length > j).getD n
        IO.println s!"event {j} {((List.range (k + 1)).map fun i => p.stepCost i ω κ).sum} {k}"
      return 0
  | "loader-a64" :: dir :: rest =>
    -- the arm64 loader model's start, to compare with the kernel's
    loaderA64 dir (rest.headD "")
  | ["show", name, idx] =>
    match allFuncs.find? (·.name == name), idx.toNat? with
    | some f, some i =>
      match (inputs f.arity)[i]? with
      | some xs => IO.println (showCase f xs); return 0
      | none => IO.eprintln "no such case"; return 1
    | _, _ => IO.eprintln "usage: differential show <name> <index>"; return 2
  | _ =>
    IO.eprintln "usage: differential list | gen <dir> <name> [limit] | show <name> <index>"
    return 2

end Millipede.Tests.Differential

def main : List String → IO UInt32 := Millipede.Tests.Differential.main
