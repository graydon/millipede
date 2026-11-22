import Millipede.Target.A64.Isa
import Tests.Rand

/-!
# arm64 ISA model tests

These tests check the arm64 model by kernel evaluation. Known encodings, taken from the Arm
architecture manual and checked with `llvm-mc -show-encoding`, encode and decode as expected.
Words that are non-canonical, unallocated or outside the modelled subset decode to `none`. The
execution tests cover register 31 as `sp` and as `xzr`, the flags, the 32-bit forms, division by
zero, faults on unmapped and read-only memory and on a misaligned `sp` or `pc`, and `svc` through
a trap. The native co-simulation of `scripts/a64-cosim.sh` checks `exec` systematically.

`listing` feeds an independent cross-check, `scripts/a64-encode-check.sh`. For every instruction
of `sample` it gives the encoded word, the instruction's text as `llvm-mc` assembles it and its
text as GNU objdump disassembles it with `-M no-aliases`. The script requires `llvm-mc` to
assemble the first text to the word and objdump to read the word as the second text, so two
independent tools check the encoder.
-/

namespace Millipede.A64.Tests

open Millipede Millipede.A64 Millipede.Tests

/-! ## 1. Known encodings -/

example : encode (.mov .z true 1 0x1234 1) = 0xd2a24681#32 := by decide
example : encode (.mov .n false 2 0 0) = 0x12800002#32 := by decide
example : encode (.mov .k true 3 0xffff 3) = 0xf2ffffe3#32 := by decide
example : encode (.addImm true false false 0 31 0xfff true) = 0x917fffe0#32 := by decide
example : encode (.addImm true true true 31 1 1 false) = 0xf100043f#32 := by decide
example : encode (.addReg false true true 31 1 2) = 0x6b02003f#32 := by decide
example : encode (.logReg .orr true 0 31 1) = 0xaa0103e0#32 := by decide
example : encode (.logReg .ands false 0 1 2) = 0x6a020020#32 := by decide
example : encode (.madd true true 0 1 2 3) = 0x9b028c20#32 := by decide
example : encode (.div false true 0 1 2) = 0x1ac20c20#32 := by decide
example : encode (.shiftV .ror false 0 1 2) = 0x1ac22c20#32 := by decide
example : encode (.bfm false true 0 1 3 10) = 0xd3432820#32 := by decide
example : encode (.bfm true false 0 1 31 7) = 0x131f1c20#32 := by decide
example : encode (.csel .csinc true 0 31 31 .ne) = 0x9a9f17e0#32 := by decide
example : encode (.csel .csneg false 0 1 2 .nv) = 0x5a82f420#32 := by decide
example : encode (.ldr .x 0 (.uimm 31 1)) = 0xf94007e0#32 := by decide
example : encode (.ldr .b 0 (.uimm 1 4095)) = 0x397ffc20#32 := by decide
example : encode (.str .x 0 (.reg 1 2)) = 0xf8226820#32 := by decide
example : encode (.ldr .x 0 (.simm 1 0x100)) = 0xf8500020#32 := by decide
example : encode (.str .h 0 (.simm 31 255)) = 0x780ff3e0#32 := by decide
example : encode (.adr false 0 0x1ffffc) = 0x10ffffe0#32 := by decide
example : encode (.b false 2) = 0x14000002#32 := by decide
example : encode (.b true 0x3fffffe) = 0x97fffffe#32 := by decide
example : encode (.bcond .nv 1) = 0x5400002f#32 := by decide
example : encode (.cbz false true 3 0x7ffff) = 0x35ffffe3#32 := by decide
example : encode (.ret 30) = 0xd65f03c0#32 := by decide
example : encode (.svc 0) = 0xd4000001#32 := by decide

example : bytes (.ret 30) = [0xc0, 0x03, 0x5f, 0xd6] := by decide
example : decode [0xc0, 0x03, 0x5f, 0xd6, 0xAA] = some (.ret 30, 4) := by decide
example : decode [0x20, 0x68, 0x22, 0xf8] = some (.str .x 0 (.reg 1 2), 4) := by decide
example : decodeWord 0x9a9f17e0#32 = some (.csel .csinc true 0 31 31 .ne) := by decide

/-! ## 2. Rejections -/

/-- A truncated word. -/
example : decode [0xc0, 0x03, 0x5f] = none := by decide
/-- `nop`, `hlt #0`, `brk #0`, `udf #0` are not in the subset. -/
example : decodeWord 0xd503201f#32 = none := by decide
example : decodeWord 0xd4400000#32 = none := by decide
example : decodeWord 0xd4200000#32 = none := by decide
example : decodeWord 0x00000000#32 = none := by decide
/-- `movz w0, #0, lsl #32` is unallocated, being a 32-bit form with `hw ≥ 2`. -/
example : decodeWord 0x52c00000#32 = none := by decide
/-- The unallocated `opc = 01` of the wide moves. -/
example : decodeWord 0x32800000#32 = none := by decide
/-- `add x0, x1, x2, lsl #1` has a shifted operand. -/
example : decodeWord 0x8b020420#32 = none := by decide
/-- `add x0, x1, w2, uxtw` is the extended-register form. -/
example : decodeWord 0x8b224020#32 = none := by decide
/-- The inserting `bfm x0, x1, #3, #10`, and `ubfm` with `N ≠ sf`. -/
example : decodeWord 0xb3432820#32 = none := by decide
example : decodeWord 0xd3032820#32 = none := by decide
/-- `ubfm w0, w1, #32, #0` is a 32-bit form with `immr ≥ 32`. -/
example : decodeWord 0x53200020#32 = none := by decide
/-- The sign-extending load `ldrsb x0, [x1]` and the writeback form `ldr x0, [x1], #8`. -/
example : decodeWord 0x39800020#32 = none := by decide
example : decodeWord 0xf8408420#32 = none := by decide
/-- `ldr x0, [x1, w2, uxtw]` and `ldr x0, [x1, x2, lsl #3]` use register offsets outside the
subset. -/
example : decodeWord 0xf8624820#32 = none := by decide
example : decodeWord 0xf8627820#32 = none := by decide
/-- `ldr d0, [x1]` loads a SIMD register. -/
example : decodeWord 0xfd400020#32 = none := by decide

/-! ## 3. Execution -/

/-- A memory in which page 1, `0x1000`–`0x1FFF`, is read-write, page 2 is read-only with `0x2A` at
`0x2000`, and page 4 is read-execute. Everything else is unmapped. -/
def mem0 : Memory where
  pageBits := 12
  bytes a := if a = 0x2000 then 0x2A else 0
  perm p := if p = 1 then Perm.rw else if p = 2 then Perm.r_ else if p = 4 then Perm.rx else Perm.none

/-- The state with `x0 = 7`, `x1 = 5`, `x2 = 0xFFFFFFFF`, `sp = 0x1100`, the other registers 0,
`pc = 0x4000` and the flags clear. -/
def regs0 : Regs where
  x k := if k = 0 then 7 else if k = 1 then 5 else if k = 2 then 0xFFFFFFFF else if k = 31 then 0x1100 else 0
  pc := 0x4000
  flags := ⟨false, false, false, false⟩

def s0 : State := ⟨regs0, mem0, World.init⟩

def noTrap : State → Option State := fun _ => none

/-- Run one instruction and observe something. -/
def run1 {α : Type} (i : Instr) (f : State → α) (s : State := s0) (trap := noTrap) : Option α :=
  (exec trap i 4 s).map f

def x (k : Reg) (s : State) : UInt64 := s.regs.x k
def flags (s : State) : Flags := s.regs.flags
def pc (s : State) : UInt64 := s.regs.pc

example : run1 (.addReg true false false 3 0 1) (x 3) = some 12 := by decide
/-- `subs x3, x1, x0` computes 5 - 7, which is negative and borrows, so C is clear. -/
example : run1 (.addReg true true true 3 1 0) (fun s => (x 3 s, flags s)) =
    some (0xFFFFFFFFFFFFFFFE, ⟨true, false, false, false⟩) := by decide
/-- `cmp x0, x0` sets Z, and C since nothing is borrowed. Its destination 31 is `xzr`, so `sp` is
unchanged. -/
example : run1 (.addReg true true true 31 0 0) (fun s => (x 31 s, flags s)) =
    some (0x1100, ⟨false, true, true, false⟩) := by decide
/-- In `add sp, sp, #16` register 31 is `sp`, and `adds xzr, sp, #16` sets only the flags. -/
example : run1 (.addImm true false false 31 31 16 false) (x 31) = some 0x1110 := by decide
example : run1 (.addImm true false true 31 31 16 false) (x 31) = some 0x1100 := by decide
/-- The 32-bit `add w3, w2, w1` wraps at 2^32, sets C and clears the upper half. -/
example : run1 (.addReg false false true 3 2 1) (fun s => (x 3 s, flags s)) =
    some (4, ⟨false, false, true, false⟩) := by decide
/-- `0x7FFFFFFF + 1` overflows as a signed 32-bit number. -/
example : run1 (.addImm false false true 3 2 1 false) flags
    (s := { s0 with regs := regs0.set 2 0x7FFFFFFF }) = some ⟨true, false, false, true⟩ := by decide
/-- `orr x3, xzr, x1` is `mov x3, x1`; `ands` clears C and V. -/
example : run1 (.logReg .orr true 3 31 1) (x 3) = some 5 := by decide
example : run1 (.logReg .ands true 31 0 1) flags
    (s := { s0 with regs := { regs0 with flags := ⟨false, false, true, true⟩ } }) =
    some ⟨false, false, false, false⟩ := by decide
/-- Division by zero gives 0; `msub` computes the remainder. -/
example : run1 (.div true false 3 0 4) (x 3) = some 0 := by decide
example : run1 (.madd true true 3 1 1 0) (x 3) = some (7 - 25) := by decide
/-- `lslv` takes the amount modulo the width, so at 32 bits it computes 7 << (0xFFFFFFFF mod 32). -/
example : run1 (.shiftV .lsl false 3 0 2) (x 3) = some 0x80000000 := by decide
/-- `ubfm x3, x0, #1, #2`, which is `ubfx #1, #2`, and `sbfm x3, x2, #0, #7`, which is `sxtb`. -/
example : run1 (.bfm false true 3 0 1 2) (x 3) = some 3 := by decide
example : run1 (.bfm true true 3 2 0 7) (x 3) = some 0xFFFFFFFFFFFFFFFF := by decide
/-- `cset x3, eq` is `csinc x3, xzr, xzr, ne`. -/
example : run1 (.csel .csinc true 3 31 31 .ne) (x 3) = some 0 := by decide
/-- `movz` then `movk` keeps the other halfwords; 32-bit `movn`. -/
example : run1 (.mov .k true 0 0xBEEF 1) (x 0) = some 0xBEEF0007 := by decide
example : run1 (.mov .n false 3 0 0) (x 3) = some 0xFFFFFFFF := by decide
/-- Loads from read-only memory are zero-extended and stores to it fault, and unmapped memory
faults. -/
example : run1 (.ldr .x 3 (.uimm 1 0)) (x 3) (s := { s0 with regs := regs0.set 1 0x2000 }) =
    some 0x2A := by decide
example : run1 (.str .b 3 (.uimm 1 0)) (x 3) (s := { s0 with regs := regs0.set 1 0x2000 }) =
    none := by decide
example : run1 (.ldr .x 3 (.uimm 0 0)) (x 3) = none := by decide
/-- A store then a load through `sp`; an access through a misaligned `sp` faults. -/
example : ((exec noTrap (.str .x 1 (.simm 31 0x1F8)) 4 s0).bind fun s =>
    run1 (.ldr .x 3 (.simm 31 0x1F8)) (x 3) (s := s)) = some 5 := by decide
example : run1 (.ldr .x 3 (.uimm 31 0)) (x 3) (s := { s0 with regs := regs0.set 31 0x1108 }) = none := by
  decide
/-- Branches are relative to the instruction; `bl` links `pc + 4`; `ret` jumps to its register. -/
example : run1 (.b true 0x3FFFFFF) (fun s => (pc s, x 30 s)) = some (0x3FFC, 0x4004) := by decide
example : run1 (.ret 30) pc (s := { s0 with regs := regs0.set 30 0x5000 }) = some 0x5000 := by decide
example : run1 (.cbz false false 2 8) pc = some 0x4004 := by decide
example : run1 (.bcond .ls 8) pc = some 0x4020 := by decide
/-- `adrp` gives the page of `pc` plus `4096 imm`. -/
example : run1 (.adr true 3 1) (x 3) (s := { s0 with regs := { regs0 with pc := 0x4FFC } }) =
    some 0x5000 := by decide
/-- An instruction at a misaligned `pc` faults. -/
example : run1 (.ret 30) pc (s := { s0 with regs := { regs0 with pc := 0x4002 } }) = none := by decide
/-- `svc` takes the trap's result and moves to `pc + 4`, and without a trap there is no step. -/
example : run1 (.svc 0) (fun s => (x 0 s, pc s)) (trap := fun s => some { s with regs := s.regs.set 0 99 }) =
    some (99, 0x4004) := by decide
example : run1 (.svc 0) pc = none := by decide

/-- A memory holding `orr x0, xzr, x1` at `0x1000` in a page with permission `perm`. The machine
step decodes from executable memory only, so the instruction runs when the page is read-execute
and the step is stuck when it is read-only. -/
def codeMem (perm : Perm) : Memory where
  pageBits := 12
  bytes a := if a = 0x1000 then 0xe0 else if a = 0x1001 then 0x03 else if a = 0x1002 then 0x01
    else if a = 0x1003 then 0xaa else 0
  perm p := if p = 1 then perm else Perm.none

example : (isa.step noTrap ⟨{ regs0 with pc := 0x1000 }, codeMem Perm.rx, World.init⟩).map
    (fun s => (s.regs.x 0, s.regs.pc)) = some (5, 0x1004) := by decide
example : (isa.step noTrap ⟨{ regs0 with pc := 0x1000 }, codeMem Perm.r_, World.init⟩).map
    (fun s => s.regs.pc) = none := by decide
/-- An instruction that straddles the end of the executable page is not fetched whole, so the step
is stuck. -/
example : (isa.step noTrap ⟨{ regs0 with pc := 0x1FFE }, codeMem Perm.rx, World.init⟩).map
    (fun s => s.regs.pc) = none := by decide

/-! ## 4. Listing for the cross-check with `llvm-mc` and objdump -/

/-- Lower-case hexadecimal with `0x`. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A general register at a position where 31 is the zero register. -/
def rZ (sf : Bool) (r : Reg) : String :=
  if r = 31 then (if sf then "xzr" else "wzr") else (if sf then "x" else "w") ++ toString r.toNat

/-- A general register at a position where 31 is the stack pointer. -/
def rS (sf : Bool) (r : Reg) : String :=
  if r = 31 then (if sf then "sp" else "wsp") else rZ sf r

def Cond.name (c : Cond) : String :=
  match c with
  | .eq => "eq" | .ne => "ne" | .cs => "cs" | .cc => "cc" | .mi => "mi" | .pl => "pl"
  | .vs => "vs" | .vc => "vc" | .hi => "hi" | .ls => "ls" | .ge => "ge" | .lt => "lt"
  | .gt => "gt" | .le => "le" | .al => "al" | .nv => "nv"

/-- The mnemonic suffix and the data register's width of an access size. -/
def sizeSuffix : Size → String × Bool
  | .b => ("b", false) | .h => ("h", false) | .w => ("", false) | .x => ("", true)

/-- An address as both tools print it, and the mnemonic prefix, `ld` or `st` followed by `r` or `ur`. -/
def addrText (sz : Size) : Addr → String × String
  | .uimm n imm =>
    let off := imm.toNat * sz.bytes
    ("r", if off = 0 then s!"[{rS true n}]" else s!"[{rS true n}, #{off}]")
  | .simm n imm =>
    let off := imm.toInt
    ("ur", if off = 0 then s!"[{rS true n}]" else s!"[{rS true n}, #{off}]")
  | .reg n m => ("r", s!"[{rS true n}, {rZ true m}]")

/-- The text of `i` at address `pc` as the pair of `llvm-mc` input and objdump output. The two differ
only in `ret` and in pc-relative operands, which `llvm-mc` writes as `#offset` and objdump as the
target address. -/
def text (pc : UInt64) (i : Instr) : String × String :=
  let same (s : String) := (s, s)
  let rel (mn : String) (off : Int) :=
    (s!"{mn}#{off}", s!"{mn}{hex (((pc.toNat + off) % 2 ^ 64).toNat)}")
  match i with
  | .mov op sf d imm hw =>
    let mn := match op with | .n => "movn" | .z => "movz" | .k => "movk"
    same (s!"{mn} {rZ sf d}, #{hex imm.toNat}" ++ (if hw = 0 then "" else s!", lsl #{16 * hw.toNat}"))
  | .addImm sf sub setf d n imm sh =>
    let mn := (if sub then "sub" else "add") ++ (if setf then "s" else "")
    same (s!"{mn} {if setf then rZ sf d else rS sf d}, {rS sf n}, #{hex imm.toNat}" ++
      (if sh then ", lsl #12" else ""))
  | .addReg sf sub setf d n m =>
    let mn := (if sub then "sub" else "add") ++ (if setf then "s" else "")
    same s!"{mn} {rZ sf d}, {rZ sf n}, {rZ sf m}"
  | .logReg op sf d n m =>
    let mn := match op with | .and => "and" | .orr => "orr" | .eor => "eor" | .ands => "ands"
    same s!"{mn} {rZ sf d}, {rZ sf n}, {rZ sf m}"
  | .madd sf sub d n m a =>
    same s!"{if sub then "msub" else "madd"} {rZ sf d}, {rZ sf n}, {rZ sf m}, {rZ sf a}"
  | .div sf signed d n m =>
    same s!"{if signed then "sdiv" else "udiv"} {rZ sf d}, {rZ sf n}, {rZ sf m}"
  | .shiftV op sf d n m =>
    let mn := match op with | .lsl => "lslv" | .lsr => "lsrv" | .asr => "asrv" | .ror => "rorv"
    same s!"{mn} {rZ sf d}, {rZ sf n}, {rZ sf m}"
  | .bfm signed sf d n immr imms =>
    same s!"{if signed then "sbfm" else "ubfm"} {rZ sf d}, {rZ sf n}, #{immr.toNat}, #{imms.toNat}"
  | .csel op sf d n m c =>
    let mn := match op with
      | .csel => "csel" | .csinc => "csinc" | .csinv => "csinv" | .csneg => "csneg"
    same s!"{mn} {rZ sf d}, {rZ sf n}, {rZ sf m}, {Cond.name c}"
  | .ldr sz t a | .str sz t a =>
    let (k, am) := addrText sz a
    let mn := (match i with | .ldr .. => "ld" | _ => "st") ++ k ++ (sizeSuffix sz).1
    same s!"{mn} {rZ (sizeSuffix sz).2 t}, {am}"
  | .adr false d imm => rel s!"adr {rZ true d}, " imm.toInt
  | .adr true d imm =>
    (s!"adrp {rZ true d}, #{imm.toInt * 4096}",
     s!"adrp {rZ true d}, {hex ((((pc.toNat / 4096 * 4096 : Int) + imm.toInt * 4096) % 2 ^ 64).toNat)}")
  | .b link imm => rel (if link then "bl " else "b ") (imm.toInt * 4)
  | .bcond c imm => rel s!"b.{Cond.name c} " (imm.toInt * 4)
  | .cbz sf nz t imm => rel s!"{if nz then "cbnz" else "cbz"} {rZ sf t}, " (imm.toInt * 4)
  | .ret n => (s!"ret {rZ true n}", if n = 30 then "ret" else s!"ret {rZ true n}")
  | .svc imm => same s!"svc #{hex imm.toNat}"

/-! ### Pseudo-random operands -/

/-- The generator monad, whose state is the SplitMix state. -/
abbrev G := StateM UInt64

def next : G UInt64 := modifyGet fun s => let (s', z) := splitmix s; (z, s')

/-- A field of `n` bits, which is random or one of the edge values all zeros, all ones, one and the
sign bit. -/
def field (n : Nat) : G (BitVec n) := do
  let k := (← next).toNat % 6
  let r := BitVec.ofNat n (← next).toNat
  pure (match k with | 0 => 0 | 1 => BitVec.allOnes n | 2 => 1 | 3 => BitVec.ofNat n (2 ^ (n - 1)) | _ => r)

def bool : G Bool := do pure ((← next) % 2 == 0)

def pick {α : Type} [Inhabited α] (xs : List α) : G α := do
  pure (xs[(← next).toNat % xs.length]!)

/-- A random register, which is 31 a quarter of the time. -/
def reg : G Reg := do
  if (← next) % 4 == 0 then pure 31 else pure (BitVec.ofNat 5 ((← next).toNat % 31))

def sizes : List Size := [.b, .h, .w, .x]

def addr : G Addr := do
  match (← next) % 3 with
  | 0 => pure (.uimm (← reg) (← field 12))
  | 1 => pure (.simm (← reg) (← field 9))
  | _ => pure (.reg (← reg) (← reg))

/-- A random encodable instruction of form number `k`, from 0 to 16, where every `k` from 16 on
gives `svc`. -/
def randInstr (k : Nat) : G Instr := do
  let sf ← bool
  match k with
  | 0 => do
    let hw ← field 2
    pure (.mov (← pick [.n, .z, .k]) sf (← reg) (← field 16) (if sf then hw else hw &&& 1))
  | 1 => pure (.addImm sf (← bool) (← bool) (← reg) (← reg) (← field 12) (← bool))
  | 2 => pure (.addReg sf (← bool) (← bool) (← reg) (← reg) (← reg))
  | 3 => pure (.logReg (← pick [.and, .orr, .eor, .ands]) sf (← reg) (← reg) (← reg))
  | 4 => pure (.madd sf (← bool) (← reg) (← reg) (← reg) (← reg))
  | 5 => pure (.div sf (← bool) (← reg) (← reg) (← reg))
  | 6 => pure (.shiftV (← pick [.lsl, .lsr, .asr, .ror]) sf (← reg) (← reg) (← reg))
  | 7 => do
    let r ← field 6
    let s ← field 6
    pure (.bfm (← bool) sf (← reg) (← reg) (if sf then r else r &&& 31) (if sf then s else s &&& 31))
  | 8 => pure (.csel (← pick [.csel, .csinc, .csinv, .csneg]) sf (← reg) (← reg) (← reg) (← pick Cond.all))
  | 9 => pure (.ldr (← pick sizes) (← reg) (← addr))
  | 10 => pure (.str (← pick sizes) (← reg) (← addr))
  | 11 => pure (.adr (← bool) (← reg) (← field 21))
  | 12 => pure (.b (← bool) (← field 26))
  | 13 => pure (.bcond (← pick Cond.all) (← field 19))
  | 14 => pure (.cbz sf (← bool) (← reg) (← field 19))
  | 15 => pure (.ret (← reg))
  | _ => pure (.svc (← field 16))

/-- The instructions cross-checked, which are the forms 0 to 16 60 times each with random operands,
and every condition and access size explicitly. -/
def sample : List Instr :=
  let rnd := ((List.range 17).flatMap fun k => (List.range 60).map fun _ => k).mapM randInstr
  Id.run (rnd.run' 20261118) ++
  (Cond.all.flatMap fun c => [Instr.bcond c 4, .csel .csel true 1 2 3 c]) ++
  (sizes.flatMap fun sz => [Instr.ldr sz 0 (.uimm 1 1), .str sz 2 (.simm 31 0x1ff),
    .ldr sz 31 (.reg 31 31)]) ++
  [.ret 30, .addImm true false false 31 31 16 false, .addImm true true false 31 31 16 false]

/-- The encoder with a seeded bug, each of which `scripts/a64-encode-check.sh --selftest` requires
to be caught. Bug 1 shifts wide moves by one more halfword, bug 2 encodes the opposite condition
in conditional branches, bug 3 encodes scaled offsets as byte offsets, bug 4 swaps the two
source registers of register `add` and `sub`, bug 5 drops the flag-setting bit of immediate
`adds` and `subs`, and bug 6 drops the sign bit of unscaled offsets. `0` is the real encoder. -/
def encodeBug (bug : Nat) (i : Instr) : BitVec 32 :=
  match bug, i with
  | 1, .mov op sf d imm hw => encode (.mov op sf d imm (hw + 1))
  | 2, .bcond c imm => encode (.bcond c.invert imm)
  | 3, .ldr sz t (.uimm n imm) => encode (.ldr sz t (.uimm n (imm * BitVec.ofNat 12 sz.bytes)))
  | 4, .addReg sf sub setf d n m => encode (.addReg sf sub setf d m n)
  | 5, .addImm sf sub _ d n imm sh => encode (.addImm sf sub false d n imm sh)
  | 6, .str sz t (.simm n imm) => encode (.str sz t (.simm n (imm &&& 0xff)))
  | _, i => encode i

/-- The word, the `llvm-mc` text and the objdump text of each instruction of `sample`, encoded by
`encodeBug bug` and laid out from address 0x10000 so that `adrp` targets are not all page 0. -/
def listing (bug : Nat := 0) : List (String × String × String) :=
  (sample.zip (List.range sample.length)).map fun (i, k) =>
    let (a, o) := text (0x10000 + 4 * UInt64.ofNat k) i
    (hex (encodeBug bug i).toNat, a, o)

/-- Print the listing, one instruction per line: `word<TAB>llvm text<TAB>objdump text`. -/
def printListing (bug : Nat := 0) : IO Unit :=
  for (w, a, o) in listing bug do IO.println s!"{w}\t{a}\t{o}"

end Millipede.A64.Tests
