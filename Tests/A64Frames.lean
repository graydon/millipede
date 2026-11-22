import Millipede.Top.Compile

/-!
# arm64 frames beyond the 12-bit offsets

These tests build Lin programs directly, since deep `let` chains make `lower` slow at 100,000
slots. In the first program `main` and its callee `f` both have `F` slots. `main` calls `f 41`
into its slot `F - 2`, and `f` jumps to the next position, which ends a translation block with
`sp` at its lowest, computes `x + 1` into its slot `F - 1` and returns it. `main` then exits with
slot `F - 2`. For `F` of 510, 4,096 and 100,000 words the arm64 backend selects, assembles, links
and writes the program, and on an aarch64 host it runs natively and exits with 42. A frame of
`A64.maxFrame` slots is refused. The backend's budget check is not run, because a Lin program
built by hand carries no source cost.

Under `qemu-aarch64 -d cpu,nochain`, which logs every translation block, the lowest `sp` seen
must lie within the proved stack bound `P.stackBytes A64.φ` of the initial `sp`. Call chains of up
to 200 functions with register locations check the stack use of the saves in the same way. The
tests were shown to catch two seeded bugs. With the far offset of `farA` off by one word, the
100,000-slot program exits with 0 instead of 42, and with a frame measure two words short per
frame, `chainsSeeded` sees the chains of 4- and 8-slot frames exceed the bound.
-/

namespace Millipede.Tests.A64Frames

open Millipede

/-- The program of `f`, number 0, and `main`, number 1, both of `F` slots. `main` comes second
because a well-formed Lin program calls only lower-numbered functions. -/
def prog (F : Nat) : Lin.Prog where
  funs := [⟨"f", F, [.jmp 1, .bin .add (F - 1) (.slot 0) (.imm 1), .ret], [.slot (F - 1)]⟩,
    ⟨"main", F, [.call 0 [.imm 41] (F - 2), .ext "exit" true (F - 3) [.word (.slot (F - 2))]], []⟩]
  main := 1
  mem := 0

/-- The arm64 backend after `lower`, without the budget check. -/
def build (P : Lin.Prog) : Except String (List UInt8) := do
  let A ← a64Backend.select P
  let obj ← a64Backend.assemble A
  let img ← Link.link (a64Backend.linkConfig P) [obj]
  a64Backend.target.fmt.write img

def native : Bool := (System.Platform.target.splitOn "aarch64").length > 1

/-- A hexadecimal number. -/
def hex (cs : List Char) : Option Nat :=
  cs.foldlM (fun n c => if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10)) else none) 0

/-- The first `sp` and the lowest `sp` in a log of `qemu-aarch64 -d cpu,nochain`. -/
def spRange (log : String) : Option (Nat × Nat) :=
  let sps := (log.splitOn "\n").filterMap fun l =>
    match (l.splitOn " SP=").drop 1 with
    | s :: _ => hex ((s.toList.take 16))
    | [] => none
  match sps with
  | [] => none
  | s :: _ => some (s, sps.foldl min s)

/-- A chain of `n` calls through functions of `F` slots. Function `i > 0` adds one to its argument
and calls `i - 1` with it, which saves the caller's location registers in the callee's frame.
Function `0` adds one and returns, and `main` exits with the result `n`. -/
def chain (n F : Nat) : Lin.Prog where
  funs := (List.range n).map (fun i =>
      if i = 0 then ⟨"f0", F, [.bin .add 1 (.slot 0) (.imm 1), .ret], [.slot 1]⟩
      else ⟨s!"f{i}", F, [.bin .add 1 (.slot 0) (.imm 1), .call (i - 1) [.slot 1, .slot 0] 2, .ret],
        [.slot 2]⟩) ++
    [⟨"main", F, [.call (n - 1) [.imm 0] 1, .ext "exit" true 2 [.word (.slot 1)]], []⟩]
  main := n
  mem := 0

/-- Build `P`, run it natively expecting the exit status `code`, and check the measured excursion of
`sp` against the proved bound `P.stackBytes (φ.words k c)` at the register locations used. The
self-test passes a smaller `φ`. -/
def checkProg (tag : String) (P : Lin.Prog) (code : UInt32) (φ : FrameModel := A64.φ)
    (quiet := false) : IO Bool := do
  match build P with
  | .error e => IO.eprintln s!"{tag}: refused: {e}"; return false
  | .ok bs =>
    let f := s!".lake/test-a64frames-{tag}"
    IO.FS.writeBinFile f ⟨bs.toArray⟩
    IO.setAccessRights f { user := { read := true, write := true, execution := true } }
    unless native do return true
    let out ← IO.Process.output { cmd := f }
    unless out.exitCode == code do IO.eprintln s!"{tag}: exit {out.exitCode}"; return false
    let log := f ++ ".cpu"
    let q ← IO.Process.output { cmd := "qemu-aarch64", args := #["-d", "cpu,nochain", "-D", log, f] }
    unless q.exitCode == code do IO.eprintln s!"{tag}: qemu exit {q.exitCode}"; return false
    match spRange (← IO.FS.readFile log) with
    | none => IO.eprintln s!"{tag}: no sp in the log"; return false
    | some (s0, lo) =>
      let kc := RegAlloc.A64Reg.kcUsed (Compile.a64K {}) (Compile.a64C {}) P
      let bound := P.stackBytes (φ.words kc.1 kc.2)
      unless s0 - lo ≤ bound || quiet do
        IO.eprintln s!"{tag}: sp excursion {s0 - lo} bytes over the bound {bound}"
      return s0 - lo ≤ bound

/-- Check the frames program of `F` slots, which exits with 42. -/
def check (F : Nat) : IO Bool := checkProg (toString F) (prog F) 42

/-- Frames of `maxFrame` slots are refused. -/
def refused : Bool := match build (prog A64.maxFrame) with
  | .error _ => true
  | .ok _ => false

#guard refused

/-- info: true -/
#guard_msgs in
#eval do return (← [510, 4096, 100000].mapM check).all id

/-- Deep call chains with the default register locations of `compile`, of 200 calls with frames of
4 and 8 slots and of 60 calls with frames of 600 slots, which reach far words. Each must stay
within its proved stack bound. -/
def chains : IO Bool := do
  return (← [(200, 4), (200, 8), (60, 600)].mapM fun (n, F) =>
    checkProg s!"chain-{n}-{F}" (chain n F) (UInt32.ofNat (n % 256))).all id

/-- info: true -/
#guard_msgs in
#eval chains

/-- A seeded bug, a frame measure that charges each frame two words too few, which is one 16-byte
unit since frame sizes round to 16. -/
def φShort : FrameModel := ⟨fun w => A64.φ.frame (w - 2), fun h => A64.φ.mono (by omega)⟩

/-- With `φShort` the measured excursion of `sp` in the chains of small frames exceeds the bound,
so the check of `chains` fails. Nothing is run on a host that is not arm64. Frames of 600 slots
are rounded to 4 KiB pages, which absorb a two-word error, so they are left out. -/
def chainsSeeded : IO Bool := do
  unless native do return true
  return (← [(200, 4), (200, 8)].mapM fun (n, F) => do
    return !(← checkProg s!"seed-{n}-{F}" (chain n F) (UInt32.ofNat (n % 256)) φShort true)).all id

/-- info: true -/
#guard_msgs in
#eval chainsSeeded

end Millipede.Tests.A64Frames
