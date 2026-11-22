import Millipede.Top.Compile

/-!
# The stack of x64 call chains against the proved bound

This suite builds Lin programs directly, each a chain of `n` calls through functions of `F`
slots. Function `i > 0` adds one to its argument and calls function `i - 1` with it, saving the
caller's location registers in the callee's frame, and `main` exits with the result `n`. The x64
backend of `compile`, with its default 6 register locations, selects, assembles, links and
writes each program, without its budget check, since a Lin program built by hand has no source
cost.

Each program runs under `qemu-x86_64 -one-insn-per-tb -d cpu,nochain`, which logs the registers
before every instruction. The exit status must be `n mod 256`, and the lowest `rsp` seen must be
within the proved stack bound of the first. With a frame measure that charges one word too few
per frame, every chain exceeds the bound.
-/

namespace Millipede.Tests.X64Frames

open Millipede

/-- A chain of `n` calls through functions of `F` slots. -/
def chain (n F : Nat) : Lin.Prog where
  funs := (List.range n).map (fun i =>
      if i = 0 then ⟨"f0", F, [.bin .add 1 (.slot 0) (.imm 1), .ret], [.slot 1]⟩
      else ⟨s!"f{i}", F, [.bin .add 1 (.slot 0) (.imm 1), .call (i - 1) [.slot 1, .slot 0] 2, .ret],
        [.slot 2]⟩) ++
    [⟨"main", F, [.call (n - 1) [.imm 0] 1, .ext "exit" true 2 [.word (.slot 1)]], []⟩]
  main := n
  mem := 0

/-- The x64 backend from a Lin program to ELF bytes, without the budget check. -/
def build (P : Lin.Prog) : Except String (List UInt8) := do
  let A ← x64Backend.select P
  let obj ← x64Backend.assemble A
  let img ← Link.link (x64Backend.linkConfig P) [obj]
  x64Backend.target.fmt.write img

/-- The value of a hexadecimal number, or `none` for a non-digit. -/
def hex (cs : List Char) : Option Nat :=
  cs.foldlM (fun n c => if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10)) else none) 0

/-- The first and the lowest `rsp` in a `qemu-x86_64 -d cpu,nochain` log. -/
def spRange (log : String) : Option (Nat × Nat) :=
  let sps := (log.splitOn "\n").filterMap fun l =>
    match (l.splitOn "RSP=").drop 1 with
    | s :: _ => hex (s.toList.take 16)
    | [] => none
  match sps with
  | [] => none
  | s :: _ => some (s, sps.foldl min s)

/-- Builds `P`, runs it under qemu expecting the exit status `code`, and checks the `rsp`
excursion against the bound `P.stackBytes (φ.words k c)` at the register locations used. The
frame model `φ` is `X64.φ` unless the seeded test passes a smaller one. -/
def checkProg (tag : String) (P : Lin.Prog) (code : UInt32) (φ : FrameModel := X64.φ)
    (quiet := false) : IO Bool := do
  match build P with
  | .error e => IO.eprintln s!"{tag}: refused: {e}"; return false
  | .ok bs =>
    let f := s!".lake/test-x64frames-{tag}"
    IO.FS.writeBinFile f ⟨bs.toArray⟩
    IO.setAccessRights f { user := { read := true, write := true, execution := true } }
    let qemu := (← IO.getEnv "HOME").getD "" ++ "/tools/bin/qemu-x86_64"
    let log := f ++ ".cpu"
    let q ← IO.Process.output { cmd := qemu, args := #["-one-insn-per-tb", "-d", "cpu,nochain", "-D", log, f] }
    unless q.exitCode == code do IO.eprintln s!"{tag}: qemu exit {q.exitCode}"; return false
    match spRange (← IO.FS.readFile log) with
    | none => IO.eprintln s!"{tag}: no rsp in the log"; return false
    | some (s0, lo) =>
      let kc := X64.kcUsed (Compile.x64K {}) (Compile.x64C {}) P
      let bound := P.stackBytes (φ.words kc.1 kc.2)
      unless s0 - lo ≤ bound || quiet do
        IO.eprintln s!"{tag}: rsp excursion {s0 - lo} bytes over the bound {bound}"
      return s0 - lo ≤ bound

/-- Chains of 200 calls with frames of 4 and 8 slots and of 60 calls with 600, each saving
`min 6 F` registers per call, are each within their proved stack bound. -/
def chains : IO Bool := do
  return (← [(200, 4), (200, 8), (60, 600)].mapM fun (n, F) =>
    checkProg s!"chain-{n}-{F}" (chain n F) (UInt32.ofNat (n % 256))).all id

/-- info: true -/
#guard_msgs in
#eval chains

/-- A seeded bug, a frame measure that charges `8 w` bytes instead of `8 (w + 1)` and so leaves
out the return address. -/
def φShort : FrameModel := ⟨fun w => 8 * w, fun h => by omega⟩

/-- With `φShort`, every chain's measured `rsp` excursion exceeds the bound. -/
def chainsSeeded : IO Bool := do
  return (← [(200, 4), (200, 8), (60, 600)].mapM fun (n, F) => do
    return !(← checkProg s!"seed-{n}-{F}" (chain n F) (UInt32.ofNat (n % 256)) φShort true)).all id

/-- info: true -/
#guard_msgs in
#eval chainsSeeded


end Millipede.Tests.X64Frames
