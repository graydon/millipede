import Millipede.Target.A64.Exec
import Millipede.Target.A64.Select
import Tests.A64

/-!
# Native co-simulation of the arm64 model

`lake exe a64cosim` checks the arm64 encoder and execution model against the host CPU, which is
arm64, so the instructions run natively. For each random case the generator builds a sequence of
up to 64 instructions of the subset, with random registers biased towards edge values, random
flags, and a 512-byte memory window at `DATA = 0x20000000` into which `sp` points. The
instructions are encoded by the project's own encoder into the case file. The C harness
`Tests/A64CoSim/harness.c` runs them at `TEST = 0x10000400` between an entry and an exit stub and
records the 31 registers, `sp`, NZCV and the window, or that the CPU faulted. The Lean model runs
the intended instructions with `A64.exec` from the same initial state until `pc` reaches the exit
stub, and the harness compares the two outcomes field by field. Comparing what the CPU does with
the bytes against what the model says the instruction does tests the encoder and the execution
model at once, and the decoder is tied to the encoder by a proved law.

The sequences contain every data-processing form at both widths with any registers, wide moves,
loads and stores of every size and addressing mode based on `sp` or on a pointer into the window,
`adr` and `adrp`, forward branches of every kind, `ret` to a label computed by `adr`, and moves of
`sp` by multiples of 16. About one case in ten ends in a deliberate fault: an access through a
misaligned `sp` or to an unmapped page, a store to the code page, or a branch to a `pc` that is not
a multiple of 4. The CPU's signal must then match the model's `none`.

About one case in eight ends in system calls instead: one or two `read`s or `write`s of up to 8
bytes between the window and standard input or output, and possibly `exit` with a code below
256. The harness runs such a case in a child process whose standard input is a pipe holding the
case's input bytes and whose standard output is a pipe. The model runs `svc` with the system-call
model `A64.linux` and an oracle that answers as Linux does on those pipes, and the outcome adds
the exit code, if the case exited, and the bytes written. The registers after `svc`, `x0` holding
the result and every other register kept, are compared as for any instruction.

The last argument of `gen` seeds a bug, and `scripts/a64-cosim.sh --selftest` requires each to be
caught. Bug `n` runs the encoder `encodeBug n` of `Tests/A64.lean`, and bugs 1, 2, 3, 7 and 8
also change the model. In model bug 1 `subs` inverts C, in bug 2 a 32-bit register shift takes its
amount modulo 64, in bug 3 `ldrb` sign-extends, in bug 7 the stack-alignment check is missing, and
in bug 8 the result of a system call is one too large.
-/

namespace Millipede.A64.CoSim

open Millipede Millipede.A64 Millipede.A64.Tests

def CODE : UInt64 := 0x10000000
def TEST : UInt64 := 0x10000400
def DATA : UInt64 := 0x20000000
def WIN : Nat := 512

/-! ## Generation -/

/-- An item of a sequence, which is an instruction or an instruction with a forward word offset
`off` to the start of the `skip + 1`-th group after its own. The offset is clamped to the exit
stub at the end. A sequence is built from groups, one per generator step, and branches land only
at group starts, so a pointer set-up, a fault set-up or `adr; ret` is never entered in the
middle. -/
inductive Item where
  | ins (i : Instr)
  | rel (f : Int → Instr) (skip : Nat)

instance : Inhabited Item := ⟨.ins (.ret 30)⟩

/-- A random 64-bit word, biased towards edge values. -/
def word : G UInt64 := do
  let a ← next
  match (← next) % 5 with
  | 0 => pick [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
      0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF80000000]
  | 1 => pure (a >>> ((← next) % 64))
  | 2 => pure (a % 70)
  | _ => pure a

/-- A random data register from x0 to x30, never 31. -/
def dreg : G Reg := do pure (BitVec.ofNat 5 ((← next).toNat % 31))

/-- `movz b, #lo; movk b, #hi, lsl #16`, which sets `b` to `hi * 2^16 + lo`. -/
def setPtr (b : Reg) (v : UInt64) : List Item :=
  [.ins (.mov .z true b (BitVec.ofNat 16 (v % 65536).toNat) 0),
   .ins (.mov .k true b (BitVec.ofNat 16 (v / 65536).toNat) 1)]

/-- A load or store of size `sz` at window offset `o`, through `sp`, which is at window offset
`spo`, or through a fresh pointer register. -/
def access (sz : Size) (spo : Nat) (o : Nat) : G (List Item) := do
  let ld ← bool
  let t ← reg
  let mk (a : Addr) : Item := .ins (if ld then .ldr sz t a else .str sz t a)
  let d : Int := (o : Int) - spo
  match (← next) % 4 with
  | 0 =>
    if d ≥ 0 ∧ d % sz.bytes = 0 ∧ d / sz.bytes < 4096 then
      pure [mk (.uimm 31 (BitVec.ofInt 12 (d / sz.bytes)))]
    else pure [mk (.simm 31 (BitVec.ofInt 9 (max (-256) (min 255 d))))]
  | 1 => pure [mk (.simm 31 (BitVec.ofInt 9 (max (-256) (min 255 d))))]
  | 2 => do
    let b ← dreg
    let k := min ((← next).toNat % 64) (o / sz.bytes)
    pure (setPtr b (DATA + (o - k * sz.bytes).toUInt64) ++ [mk (.uimm b (BitVec.ofNat 12 k))])
  | _ => do
    let b ← dreg
    let m ← dreg
    if b = m then pure (setPtr b (DATA + o.toUInt64) ++ [mk (.uimm b 0)])
    else do
      let k := (← next).toNat % (o + 1)
      pure (setPtr b (DATA + (o - k).toUInt64) ++ setPtr m k.toUInt64 ++ [mk (.reg b m)])

/-- A random data-processing instruction with any registers. Register 31 is `xzr`, or `sp` where it
is only read as in `add x, sp, #imm`, and `sp` is never written. -/
def alu : G Instr := do
  let sf ← bool
  match (← next) % 10 with
  | 0 => do
    let hw ← field 2
    pure (.mov (← pick [.n, .z, .k]) sf (← reg) (← field 16) (if sf then hw else hw &&& 1))
  | 1 => do
    let setf ← bool
    let d ← (if setf then reg else dreg)
    pure (.addImm sf (← bool) setf d (← reg) (← field 12) (← bool))
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
  | _ => pure (.adr (← bool) (← reg) (← field 21))

/-- One step of a sequence, where `spo` is the window offset of `sp`, a multiple of 16. -/
def step (spo : Nat) : G (List Item × Nat) := do
  match (← next) % 16 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => do pure ([.ins (← alu)], spo)
  | 7 | 8 | 9 => do
    let sz ← pick sizes
    let o := ((← next).toNat % (WIN / sz.bytes)) * sz.bytes
    let mis := (← next).toNat % sz.bytes
    let o := if (← bool) then o else o + mis
    let o := min o (WIN - sz.bytes)
    pure (← access sz spo o, spo)
  | 10 => do
    let c ← pick Cond.all
    pure ([.rel (fun off => .bcond c (BitVec.ofInt 19 off)) ((← next).toNat % 4)], spo)
  | 11 => do
    let sf ← bool
    let nz ← bool
    let t ← reg
    pure ([.rel (fun off => .cbz sf nz t (BitVec.ofInt 19 off)) ((← next).toNat % 4)], spo)
  | 12 => do
    let link ← bool
    pure ([.rel (fun off => .b link (BitVec.ofInt 26 off)) ((← next).toNat % 4)], spo)
  | 13 => do
    -- adr x, label; ret x
    let x ← dreg
    let j : Instr := .ret x
    pure ([.rel (fun off => .adr false x (BitVec.ofInt 21 (4 * off))) (1 + (← next).toNat % 3),
      .ins j], spo)
  | 14 => do
    -- move sp by a multiple of 16 inside the window
    let target := 16 * (2 + (← next).toNat % 28)
    let sub := decide (target < spo)
    let delta := if sub then spo - target else target - spo
    pure ([.ins (.addImm true sub false 31 31 (BitVec.ofNat 12 delta) false)], target)
  | _ => do pure ([.ins (← alu)], spo)

/-- A deliberate fault of one of the kinds the module documentation lists. -/
def fault (spo : Nat) : G (List Item) := do
  let t ← reg
  match (← next) % 5 with
  | 0 => pure [.ins (.addImm true false false 31 31 (BitVec.ofNat 12 (1 + (← next).toNat % 15)) false),
      .ins (.ldr (← pick sizes) t (.uimm 31 0))]
  | 1 => pure [.ins (.addImm true true false 31 31 8 false), .ins (.str .x t (.simm 31 0))]
  | 2 => do
    let b ← dreg
    pure (setPtr b (DATA - 0x10000) ++ [.ins (.ldr .x t (.uimm b 0))])
  | 3 => do
    let b ← dreg
    pure (setPtr b TEST ++ [.ins (.str .w t (.uimm b 0))])
  | _ => do
    let x ← dreg
    let _ := spo
    pure [.rel (fun off => .adr false x (BitVec.ofInt 21 (4 * off + 2))) 1, .ins (.ret x)]

/-- Flatten groups and resolve the forward offsets. Group `g` starts at `starts[g]`, and the exit
stub is at the end `n`. -/
def resolve (groups : List (List Item)) : List Instr :=
  let starts := groups.foldl (fun acc g => acc ++ [acc.getLast! + g.length]) [0]
  let n := starts.getLast!
  ((groups.zip (List.range groups.length)).flatMap fun (g, gi) =>
    (g.zip (List.range g.length)).map fun (it, j) =>
      let k := starts[gi]! + j
      match it with
      | .ins i => i
      | .rel f skip => f ((starts.getD (gi + 1 + skip) n : Nat) - (k : Int)))

/-- A random case, with its instructions, registers, `sp`, NZCV in bits 31–28, and window. -/
structure Case where
  code : List Instr
  x : List UInt64
  sp : UInt64
  nzcv : UInt64
  win : List UInt8
  /-- whether the case makes system calls, and then the bytes on its standard input -/
  sys : Bool := false
  inp : List UInt8 := []

/-- A system call: `read(0, DATA + o, n)` or `write(1, DATA + o, n)` with `n ≤ 8`, or, when
`last`, possibly `exit(code)`. -/
def sysCall (last : Bool) : G (List Item) := do
  let o := (← next).toNat % (WIN - 8)
  let n := (← next).toNat % 9
  let k := (← next) % 5
  let code := (← next) % 256
  let (nr, a0, a1) : UInt64 × UInt64 × UInt64 :=
    if last && k == 0 then (93, code, 0)
    else if k % 2 == 0 then (63, 0, DATA + o.toUInt64) else (64, 1, DATA + o.toUInt64)
  pure (setPtr 8 nr ++ setPtr 0 a0 ++ setPtr 1 a1 ++ setPtr 2 n.toUInt64 ++ [.ins (.svc 0)])

def genCase : G Case := do
  let spo := 16 * (4 + (← next).toNat % 24)
  let len := 4 + (← next).toNat % 28
  let mut groups : List (List Item) := []
  let mut s := spo
  let mut count := 0
  while count < len do
    let (is, s') ← step s
    groups := groups ++ [is]
    count := count + is.length
    s := s'
  let sys := (← next) % 8 == 0
  if sys then
    if ← bool then groups := groups ++ [← sysCall false]
    groups := groups ++ [← sysCall true]
  else if (← next) % 10 == 0 then groups := groups ++ [← fault s]
  let x ← (List.range 31).mapM fun _ => word
  let nzcv := ((← next) % 16) <<< 28
  let win ← (List.range WIN).mapM fun _ => do pure (← next).toUInt8
  let inp ← (List.range ((← next).toNat % 17)).mapM fun _ => do pure (← next).toUInt8
  pure ⟨resolve groups, x, DATA + spo.toUInt64, nzcv, win, sys, inp⟩

/-! ## The model -/

/-- The initial machine state of a case, in which the code page is read-execute, the window page
read-write and everything else unmapped. -/
def initState (c : Case) : State where
  regs := ⟨fun k => if k = 31 then c.sp else c.x.getD k.toNat 0, TEST,
    ⟨c.nzcv >>> 31 &&& 1 == 1, c.nzcv >>> 30 &&& 1 == 1, c.nzcv >>> 29 &&& 1 == 1,
     c.nzcv >>> 28 &&& 1 == 1⟩⟩
  mem := {
    pageBits := 12
    bytes := fun a => if DATA ≤ a ∧ a < DATA + WIN.toUInt64 then c.win.getD (a - DATA).toNat 0 else 0
    perm := fun p => if p = (CODE >>> 12).toNat then Perm.rx
      else if p = (DATA >>> 12).toNat then Perm.rw else Perm.none }
  world := World.init

/-- The model's step with the model bug `bug`, which is one of 1, 2, 3 and 7 of the module
documentation or none. -/
def execBug (bug : Nat) (trap : State → Option State) (i : Instr) (s : State) : Option State :=
  let r := s.regs
  let ex := exec trap i 4 s
  match bug, i with
  | 1, .addImm _ true true .. | 1, .addReg _ true true .. =>
    ex.map fun s' => { s' with regs := { s'.regs with flags := { s'.regs.flags with c := !s'.regs.flags.c } } }
  | 2, .shiftV op false d n m =>
    ex.map fun s' => { s' with regs := { (r.setZ d (wid false (bin true op.eval (wid false (r.getZ n))
      (r.getZ m)))) with pc := s'.regs.pc } }
  | 3, .ldr .b t _ =>
    ex.map fun s' => { s' with regs := s'.regs.setZ t (sext (BitVec.ofNat 8 (s'.regs.getZ t).toNat)) }
  | 7, .ldr sz t a =>
    if r.pc % 4 ≠ 0 then none else
    (s.mem.readWord (a.ea r sz) sz.bytes).map fun v => s.goto (r.setZ t v) (r.pc + 4)
  | 7, .str sz t a =>
    if r.pc % 4 ≠ 0 then none else
    (s.mem.writeWord (a.ea r sz) sz.bytes (r.getZ t)).map fun m => { s.goto r (r.pc + 4) with mem := m }
  | _, _ => ex

/-- The oracle of Linux with standard input a pipe holding `inp` and standard output a pipe:
`read(0, …, n)` returns the next bytes, at most `n`, and `write(1, …, n)` writes all `n`. -/
def pipeOracle (inp : List UInt8) : Oracle :=
  ⟨fun hist c =>
    if c.sym = "read" then
      let used := (hist.filter (·.sym = "read")).foldl (fun a e => a + e.result.toNat) 0
      let bs := (inp.drop used).take (c.outCaps.headD 0)
      ⟨UInt64.ofNat bs.length, [bs]⟩
    else if c.sym = "write" then ⟨UInt64.ofNat (c.bytesIn.headD []).length, []⟩
    else ⟨0, []⟩⟩

/-- The system calls of a case: none, or those of `A64.linux` on the case's pipes; model bug 8
adds one to the result. -/
def trapOf (bug : Nat) (c : Case) (s : State) : Option State :=
  if !c.sys then none
  else (A64.linux.trap (pipeOracle c.inp) s).map fun s' =>
    if bug = 8 then { s' with regs := s'.regs.set 0 (s'.regs.x 0 + 1) } else s'

/-- Run the intended instructions from the initial state until `pc` is the exit stub or the case
calls `exit`, and return the outcome record: the status (0 the end reached, 1 a fault, 2 `exit`),
the registers, `sp`, NZCV and window, the exit code, and the bytes written. After a fault every
field but the status is zero, and after `exit` only the code and the bytes written are set. -/
def runModel (bug : Nat) (c : Case) : List UInt8 :=
  let n := c.code.length
  let exit := TEST + 4 * n.toUInt64
  let rec go : Nat → State → Option State
    | 0, _ => none
    | fuel + 1, s =>
      if s.regs.pc = exit || s.world.halted then some s
      else
        let k := (s.regs.pc - TEST) / 4
        let i := if s.regs.pc % 4 = 0 ∧ TEST ≤ s.regs.pc ∧ k < n.toUInt64 then c.code[k.toNat]!
          else .ret 30  -- not reached, since the generator branches only inside the sequence or to a misaligned pc, which faults first
        match execBug bug (trapOf bug c) i s with
        | some s' => go fuel s'
        | none => none
  let w64 (v : UInt64) : List UInt8 := natBytes 8 v.toNat
  let outs (s : State) : List UInt8 :=
    let o := (s.world.events.filter (·.sym = "write")).flatMap (·.bytesIn.headD [])
    w64 o.length.toUInt64 ++ o ++ List.replicate (32 - o.length) 0
  match go 1000 (initState c) with
  | some s =>
    match s.world.events.find? (·.sym = "exit") with
    | some e => w64 2 ++ List.replicate (8 * 33 + WIN) 0 ++ w64 (e.args.headD 0 % 256) ++ outs s
    | none =>
      let f := s.regs.flags
      let bitv (b : Bool) (k : UInt64) : UInt64 := if b then (1 : UInt64) <<< k else 0
      let nzcv : UInt64 := bitv f.n 31 ||| bitv f.z 30 ||| bitv f.c 29 ||| bitv f.v 28
      w64 0 ++ ((List.range 31).flatMap fun k => w64 (s.regs.x (BitVec.ofNat 5 k))) ++
        w64 (s.regs.x 31) ++ w64 nzcv ++
        ((List.range WIN).map fun k => s.mem.bytes (DATA + k.toUInt64)) ++ w64 0 ++ outs s
  | none => w64 1 ++ List.replicate (8 * 33 + WIN + 8 + 8 + 32) 0

/-- The case record for the harness, with the encoder `encodeBug bug`. -/
def caseBytes (bug : Nat) (c : Case) : List UInt8 :=
  let w64 (v : UInt64) : List UInt8 := natBytes 8 v.toNat
  let code := (c.code.map fun i => natBytes 4 (encodeBug bug i).toNat).flatten
  w64 c.code.length.toUInt64 ++ code ++ List.replicate (4 * (64 - c.code.length)) 0 ++
    (c.x.flatMap w64) ++ w64 c.sp ++ w64 c.nzcv ++ c.win ++ w64 (if c.sys then 1 else 0) ++
    w64 c.inp.length.toUInt64 ++ c.inp ++ List.replicate (16 - c.inp.length) 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", cases, expect, seed, n] | ["gen", cases, expect, seed, n, _] =>
    let bug := (args.getD 5 "0").toNat!
    let cs := Id.run ((List.range n.toNat!).mapM (fun _ => genCase) |>.run' seed.toNat!.toUInt64)
    IO.FS.writeBinFile cases ⟨(cs.flatMap (caseBytes bug)).toArray⟩
    IO.FS.writeBinFile expect ⟨(cs.flatMap (runModel bug)).toArray⟩
    pure 0
  | _ =>
    IO.eprintln "usage: a64cosim gen CASES EXPECT SEED N [BUG]"
    pure 2

end Millipede.A64.CoSim

def main : List String → IO UInt32 := Millipede.A64.CoSim.main
