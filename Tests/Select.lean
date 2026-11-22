import Millipede.Compile.AssembleProof
import Millipede.Target.X64.SelectProof
import Tests.Lin

/-!
# Tests for instruction selection and assembly (x64)

This suite lowers, linearizes and selects Core terms and programs to x64 assembly, places them
in memory and runs them in the x64 ISA model. Functions follow one another from `0x400000`, data
starts at `0x800000` and the data region `mp_mem` at `0x900000`. The machine's events and result
bytes are compared with the Lin interpreter and with the source, with no register locations and
with six. A runner that returns wrong bytes makes the same checks fail.

The assembler is checked against the same placement, since applying its relocations to its
`.text` section must reproduce exactly the code the machine ran.
-/

namespace Millipede.Tests.Select

open Millipede Millipede.Flat Millipede.Lin Millipede.X64 Millipede.Tests.Core Millipede.Sel
  Millipede.Tests.Lower Millipede.Tests.Lin

set_option maxRecDepth 100000

/-- Offsets of consecutive items of the given sizes from `base`, by name. -/
def layout : Nat → List (String × Nat) → List (String × Nat)
  | _, [] => []
  | a, (n, sz) :: rest => (n, a) :: layout (a + sz) rest

/-- The address of a symbol in a table. -/
def symOf (tbl : List (String × Nat)) (s : String) : Option UInt64 :=
  (tbl.lookup s).map UInt64.ofNat

def textBase : Nat := 0x400000
def dataBase : Nat := 0x800000
def bssBase : Nat := 0x900000

/-- The placement used by the tests, with functions in order from `textBase`, data from
`dataBase` and the writable regions, such as the data region `mp_mem`, from `bssBase`. -/
def placement {Ar : Asm.Arch} (A : Asm.Prog Ar) (db : Nat := dataBase) (bb : Nat := bssBase) :
    List (String × Nat) :=
  layout textBase (A.funs.map fun f => (f.name, Asm.seqSize Ar f.code)) ++
    layout db (A.data.map fun d => (d.1, d.2.length)) ++ layout bb A.bss

/-- The machine code of all functions, placed by `placement`. -/
def textOf {Ar : Asm.Arch} (A : Asm.Prog Ar) (db : Nat := dataBase) (bb : Nat := bssBase) :
    Option (List UInt8) :=
  let σ := symOf (placement A db bb)
  A.funs.foldr (fun f acc => do
    let a ← σ f.name
    let b ← f.bytes σ a
    let r ← acc
    pure (b ++ r)) (some [])

/-- The image, with code `r-x` at `textBase`, data `r--` at `dataBase`, the zero-filled writable
regions `rw-` at `bssBase` and 64 KiB of stack. -/
def imageOf {Ar : Asm.Arch} (A : Asm.Prog Ar) (db : Nat := dataBase) (bb : Nat := bssBase) :
    Option Image := do
  let text ← textOf A db bb
  let main ← A.funs[A.main]?
  let entry ← symOf (placement A db bb) main.name
  let rodata := A.data.flatMap (·.2)
  let bss := (A.bss.map (·.2)).sum
  pure ⟨⟨UInt64.ofNat textBase, text, text.length, Perm.rx⟩ ::
      (if rodata.isEmpty then [] else [⟨UInt64.ofNat db, rodata, rodata.length, Perm.r_⟩]) ++
      (if bss = 0 then [] else [⟨UInt64.ofNat bb, [], bss, Perm.rw⟩]),
    entry, 65536⟩

/-- Selects a Lin program with `k` register locations and places it. -/
def imageOfLin (k : Nat) (P : Lin.Prog) : Option Image :=
  match select k 0 P with
  | .ok A => imageOf A
  | .error _ => none

/-- Runs the machine from an image for `fuel` steps. -/
def runImage (ω : Oracle) (img : Image) (fuel : Nat) : Option (X64.State × Nat) :=
  (Asm.msem isa linux).run ω (img.init linux, 0) fuel

/-- The events of a program compiled to x64 and run for `fuel` machine steps. -/
def x64Events (k : Nat) (ω : Oracle) (p : Program) (fuel : Nat) : Option (List Event) := do
  let img ← imageOfLin k (linearize (lowerProg p) p.memBytes)
  let s ← runImage ω img fuel
  pure s.1.world.events

/-- Runs the x64 code of a Core term for `fuel` machine steps, with its parameters' bytes written
into the data region at `bssBase` before the start. It returns the result's bytes, read from the
data region, and the events. -/
def x64Run (k : Nat) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) (fuel : Nat) :
    Option (List UInt8 × List Event) := do
  let img ← imageOfLin k (linOf e)
  let s₀ := img.init linux
  let mem ← s₀.mem.write (UInt64.ofNat bssBase) (envBytes env)
  let s ← (Asm.msem isa linux).run ω ({ s₀ with mem := mem }, 0) fuel
  pure (bytesFrom s.1.mem (UInt64.ofNat (bssBase + ctxSize Γ)) t.size, s.1.world.events)

/-- The Lin interpreter's result bytes and events. -/
def linRes (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) (fuel : Nat) :
    Option (List UInt8 × List Event) :=
  (linRun κ1 ω e env fuel).map fun r => (r.1, r.2.1)

/-! ## Terms: result bytes and events agree with Lin and with the source

Machine runs are slow under kernel reduction, so they are checked by compiled evaluation with
`#guard`. -/

/-- A target's machine run of a Core term, giving result bytes and events, and of a program,
giving events. The checks below are stated once for any runner, and run for x64 here and for
arm64 in `Tests/A64Select.lean`. -/
structure Runner where
  run : Oracle → {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → Nat → Option (List UInt8 × List Event)
  events : Oracle → Program → Nat → Option (List Event)

/-- The machine agrees with Lin on every `U64` primitive for the arguments `x y`. -/
def primsAgree (r : Runner) (x y : UInt64) : Bool :=
  let env : Env [.u64, .u64] := .cons y (.cons x .nil)
  [binU .add, binU .sub, binU .mul, binU .udiv, binU .umod, binU .band, binU .bor, binU .bxor,
    binU .shl, binU .shr].all (fun e => r.run ω0 e env 2000 == linRes ω0 e env 1000) &&
  [binU .eq, binU .ne, binU .ult, binU .ule, binU .ugt, binU .uge].all
    (fun e => r.run ω0 e env 2000 == linRes ω0 e env 1000)

/-- The result bytes of a term with two `U64` parameters. -/
def res2 (r : Runner) {t : Ty} (e : Exp [.u64, .u64] t) (y x : UInt64) : Option (List UInt8) :=
  (r.run ω0 e (.cons y (.cons x .nil)) 2000).map (·.1)

/-- The names of the checks that fail. For terms, the result bytes and events must agree with
Lin and with the expected values, including `x / 0 = 0`, `x % 0 = x` and shift counts taken
mod 64. For programs, the machine trace must be the source trace. -/
def failing (r : Runner) : List String :=
  let w (n : UInt64) := some (Data.encodeBytes n)
  let checks : List (String × Bool) := [
    ("f 7", r.run ω0 f_exp (.cons 7 .nil) 2000 == linRes ω0 f_exp (.cons 7 .nil) 1000),
    ("f 7 = 50", (r.run ω0 f_exp (.cons 7 .nil) 2000).map (·.1) == w 50),
    ("f 11 = 121", (r.run ω0 f_exp (.cons 11 .nil) 2000).map (·.1) == w 121),
    ("f 2^32", r.run ω0 f_exp (.cons 4294967296 .nil) 2000 ==
      linRes ω0 f_exp (.cons 4294967296 .nil) 1000),
    ("clampAdd", r.run ω0 clampAdd.fn.body (.cons 1 (.cons 18446744073709551615 .nil)) 4000 ==
      linRes ω0 clampAdd.fn.body (.cons 1 (.cons 18446744073709551615 .nil)) 2000),
    ("clamp3 = 6", (r.run ω0 clamp3 (.cons 1 (.cons 2 (.cons 3 .nil))) 8000).map (·.1) == w 6),
    ("clamp3", r.run ω0 clamp3 (.cons 5 (.cons 7 (.cons 18446744073709551610 .nil))) 8000 ==
      linRes ω0 clamp3 (.cons 5 (.cons 7 (.cons 18446744073709551610 .nil))) 4000),
    -- A wrong value is noticed.
    ("f 7 ≠ 49", (r.run ω0 f_exp (.cons 7 .nil) 2000).map (·.1) != w 49),
    ("prims", [(3, 5), (7, 0), (0, 0), (18446744073709551615, 2),
      (18446744073709551615, 18446744073709551615), (1, 65), (12345678901, 64),
      (0x123456789abcdef0, 0xfedcba9876543210)].all fun (x, y) => primsAgree r x y),
    ("9 / 0", res2 r (binU .udiv) 0 9 == w 0), ("9 % 0", res2 r (binU .umod) 0 9 == w 9),
    ("9 % 4", res2 r (binU .umod) 4 9 == w 1), ("9 / 4", res2 r (binU .udiv) 4 9 == w 2),
    ("1 << 65", res2 r (binU .shl) 65 1 == w 2),
    ("useDiv", r.run ω0 useDiv (.cons 3 (.cons 20 .nil)) 10000 ==
      linRes ω0 useDiv (.cons 3 (.cons 20 .nil)) 5000),
    ("useDiv 0", r.run ω0 useDiv (.cons 0 (.cons 20 .nil)) 10000 ==
      linRes ω0 useDiv (.cons 0 (.cons 20 .nil)) 5000),
    ("twoWrites", r.run ωc twoWrites .nil 5000 == linRes ωc twoWrites .nil 2000),
    ("exitLoop", r.run ωc exitLoop .nil 30000 == linRes ωc exitLoop .nil 10000),
    ("hello", r.events ωc hello 2000 == some (hello.events ωc 5)),
    ("hello ω0", r.events ω0 hello 2000 == some (helloEvents ω0)),
    ("counter", r.events ωc counter 30000 == some (counter.events ωc 10)),
    ("resProg", r.events ωc resProg 60000 == some (resProg.events ωc 10)),
    ("callProg", r.events ωc callProg 60000 == some (callProg.events ωc 10)),
    -- A short run sees a prefix of the source trace.
    ("counter prefix", (r.events ωc counter 300).map (·.isPrefixOf (counter.events ωc 10)) ==
      some true)]
  checks.filterMap fun (n, b) => if b then none else some n

/-- The x64 runner with `k` register locations, where `k = 0` puts every location in a frame
slot. -/
def x64Runner (k : Nat) : Runner := ⟨x64Run k, x64Events k⟩

#guard failing (x64Runner 0) == []
-- With 6 register locations, as in `compile`, every location below 6 is a register and the
-- others are frame slots.
#guard failing (x64Runner 6) == []
-- A runner that returns the wrong bytes fails.
#guard failing ⟨fun ω _ _ e env n => (x64Run 0 ω e env n).map fun r => (r.1.map (· + 1), r.2),
  x64Events 0⟩ != []
-- The slower runs of `sumTo 10`, `sumWhile` and `resLoop` are in `Tests/SelectLoops.lean`.

/-! ## The assembler -/

/-- Assembles, places `.text` at `textBase` with each function at its offset from `placement`,
applies the relocations with the placement's symbols and compares the result with the code the
machine ran. -/
def asmAgrees (P : Lin.Prog) (k : Nat := 0) : Bool :=
  match select k 0 P with
  | .error _ => false
  | .ok A =>
    match assemble A with
    | .error _ => false
    | .ok obj =>
      match obj.sections[Asm.textSec]? with
      | none => false
      | some sec =>
        applyRelocs (symOf (placement A)) (UInt64.ofNat textBase) Asm.textSec obj.relocs sec.bytes ==
          textOf A

#guard asmAgrees (linearize (lowerProg hello) hello.memBytes)
#guard asmAgrees (linearize (lowerProg callProg) callProg.memBytes)
#guard asmAgrees (linearize (lowerProg counter) counter.memBytes)
#guard asmAgrees (linOf clamp3)
#guard asmAgrees (linOf sumWhile)
#guard asmAgrees (linearize (lowerProg callProg) callProg.memBytes) 6
#guard asmAgrees (linOf sumWhile) 6
-- Each call between functions is a relocation, because `assemble` does not know the callee's
-- address, and so is every reference to the data region `mp_mem`.
#guard (match select 0 0 (linOf clamp3) with
    | .ok A => (assemble A).toOption.map (fun o => (o.relocs.filter (·.sym != memSym)).length)
    | .error _ => none) == some 2

/-! ## The data region and refusals -/

/-- The data region becomes the writable region `mp_mem`. -/
example : (select 0 0 (memProg 16 8)).toOption.map (·.bss) = some [("mp_mem", 16)] := by
  decide +kernel
/-- A store and a byte load are selected to four instructions each, which put `&mp_mem` into
`r11` by `lea r11, [rip + mp_mem]` and access `[r11 + a + off]` with `a` in `rax`. -/
example : (select 0 0 (memProg 16 8)).toOption.map (fun A => A.funs.map (·.blocks.map List.length)) =
    some [[4, 4, 4, 1]] := by decide +kernel
example : (select 0 0 (memProg 16 8)).toOption.map (fun A => A.funs.map (·.blocks.take 1)) =
    some [[[.op (.movRI .rax 8), .lea .r11 (.sym "mp_mem"),
      .op (.movRI .rcx 0x1122334455667788), .op (.store (.sib .r11 ⟨.rax, nofun⟩ 0) .rcx)]]] := by
  decide +kernel
/-- With `Options.memBase` off, they are seven instructions each, which compute the full address
into `rax` through `lea rcx, [rip + mp_mem]`. -/
example : (select 0 0 (memProg 16 8) false).toOption.map
    (fun A => A.funs.map (·.blocks.map List.length)) = some [[7, 7, 7, 1]] := by decide +kernel
example : (select 0 0 (memProg 16 8) false).toOption.map (fun A => A.funs.map (·.blocks.take 1)) =
    some [[[.op (.movRI .rax 8), .op (.movRI .rcx 0), .op (.aluRR .add .rax .rcx),
      .lea .rcx (.sym "mp_mem"), .op (.aluRR .add .rax .rcx),
      .op (.movRI .rcx 0x1122334455667788), .op (.store (.base .rax 0) .rcx)]]] := by
  decide +kernel
/-- The assembled object has a `.bss` section of the data region's size, with `mp_mem` in it. -/
example : ((select 0 0 (memProg 16 8)).toOption.bind fun A => (assemble A).toOption).map
    (fun o => (o.sections[Asm.bssSec]?.map (·.bssSize), o.symbols.filter (·.name == "mp_mem"))) =
    some (some 16, [⟨"mp_mem", Asm.bssSec, 0, false⟩]) := by decide +kernel
/-! ### `write` from a memory buffer

A memory buffer is a pointer and a length. -/

/-- A hand-built Flat program with a 16-byte data region. It computes the little-endian word
`"hi!\n"` at run time and stores it at address 0, writes the 4 bytes from address 0 and then
the 2 bytes from address 1, and exits with status 0. `scripts/differential.sh` runs its ELF
image under qemu and expects the output `hi!\ni!`. -/
def membufFlat : Flat.Prog :=
  ⟨.seq (.bin .add 1 (.imm 0x0a216900) (.imm 0x68))
    (.seq (.store .w64 (.imm 0) 0 (.slot 1))
    (.seq (.ext "write" false 2 [.word (.imm 1), .mem (.imm 0) (.imm 4)])
    (.seq (.ext "write" false 2 [.word (.imm 1), .mem (.slot 3) (.imm 2)])
    (.ext "exit" true 2 [.word (.imm 0)])))), 4⟩

/-- The events hold the bytes of the buffers and never their addresses. -/
example : ((Flat.nextN κ1 ω0 40 membufFlat.init).world.events.map
    fun e => (e.sym, e.args, e.bytesIn)) =
    [("write", [1], [[104, 105, 33, 10]]), ("write", [1], [[104, 105]]), ("exit", [0], [])] := by
  decide +kernel

/-- The selected block of each memory `write` has ten instructions, which compute the address
(with `add rax, imm32`), set `rsi`, `rdi`, `rdx` and `rax := 1`, run `syscall` and store the
result. The first block adds an immediate by `add rax, 104`. -/
example : (select 0 0 (linearize membufFlat 16)).toOption.map
    (fun A => A.funs.map (·.blocks.map List.length)) = some [[3, 4, 10, 10, 4, 1]] := by
  decide +kernel
example : (select 0 0 (linearize membufFlat 16)).toOption.map (fun A => A.funs.map (·.blocks.take 1)) =
    some [[[.op (.movRI .rax 0x0a216900), .op (.aluRI .add .rax 104), .op (.store (.base .rsp 8) .rax)]]] := by
  decide +kernel
/-- Lin executes a memory buffer only inside the data region and is stuck outside it, so the
proof of `select` may assume that the bytes are in `mp_mem`. -/
example : (Lin.Instr.ext "write" false 0 [.word (.imm 1), .mem (.imm 12) (.imm 4)]).memOk 16
    Flat.Frame.zero = true := by decide
example : (Lin.Instr.ext "write" false 0 [.word (.imm 1), .mem (.imm 13) (.imm 4)]).memOk 16
    Flat.Frame.zero = false := by decide

/-- An unknown extern is refused. -/
example : (select 0 0 ⟨[⟨"m", 1, [.ext "open" false 0 []], []⟩], 0, 0⟩).toOption.isNone = true := by
  decide +kernel
/-- A frame too large for 32-bit displacements is refused. -/
example : (select 0 0 ⟨[⟨"m", 2 ^ 24, [], []⟩], 0, 0⟩).toOption.isNone = true := by decide +kernel
/-- A call with more arguments than the callee's frame is refused. -/
example : (select 0 0 ⟨[⟨"g", 0, [.ret], []⟩, ⟨"m", 1, [.call 0 [.imm 1] 0], []⟩], 1, 0⟩).toOption.isNone
    = true := by decide +kernel

end Millipede.Tests.Select
