import Millipede.Target.X64.Decode
import Millipede.Target.Machine

/-!
# x64 machine state and execution

The x64 registers are the 16 general-purpose registers, `rip` and the flags CF ZF SF OF, and the
machine state adds the memory and world that every ISA shares.

`exec trap i len s` executes instruction `i` of length `len` at `s.regs.rip`, and returns `none`
on a fault, which leaves the machine stuck. The fall-through address is `next = rip + len`, and
branches and `rip`-relative memory operands are relative to it. A memory access first checks
that its first and last byte addresses are canonical, with bits 63 to 47 all equal, and then
reads or writes 8 bytes, or 1 byte zero-extended on load, which needs readable or writable pages.
`div` faults when the divisor is zero or the quotient does not fit in 64 bits. `syscall` hands the
state to `trap`, the ABI's handler, which reads the call number and arguments from registers,
performs the call through the oracle and writes the result to `rax`. The hardware then sets
`rcx` to `next`, `r11` to the flags image and `rip` to `next`.

`add`, `sub` and `cmp` set CF ZF SF OF, `and`, `or` and `xor` clear CF and OF, and `imul` sets CF
and OF to the signed overflow. Where Intel leaves a flag undefined the model makes a fixed choice,
and compiled code must never read that flag. After `imul` ZF and SF follow the result, after
`div` the flags are unchanged, and after a shift by a count other than 1 OF uses the 1-bit
formula. A shift by a count of 0, taking the count as `cl mod 64`, changes no flag. `mov`, `lea`,
`setcc`, `movzx`, `push`, `pop` and the branches leave the flags unchanged.
-/

namespace Millipede.X64

/-- The arithmetic flags. -/
structure Flags where
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
deriving DecidableEq, Repr, Inhabited

/-- The register file of general-purpose registers, the instruction pointer and the flags. -/
structure Regs where
  gpr : Reg → UInt64
  rip : UInt64
  flags : Flags

namespace Regs
/-- Writes a general-purpose register. -/
def set (s : Regs) (r : Reg) (v : UInt64) : Regs :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

@[simp] theorem set_gpr_same (s : Regs) (r : Reg) (v : UInt64) : (s.set r v).gpr r = v := by
  simp [set]
@[simp] theorem set_gpr_ne (s : Regs) {r r' : Reg} (v : UInt64) (h : r' ≠ r) :
    (s.set r v).gpr r' = s.gpr r' := by simp [set, h]
@[simp] theorem set_rip (s : Regs) (r : Reg) (v : UInt64) : (s.set r v).rip = s.rip := rfl
@[simp] theorem set_flags (s : Regs) (r : Reg) (v : UInt64) : (s.set r v).flags = s.flags := rfl
end Regs

/-- The x64 machine state. -/
abbrev State := MState Regs

/-- Sign-extends 32 bits to 64. -/
def sext32 (x : UInt32) : UInt64 := UInt64.ofBitVec (x.toBitVec.signExtend 64)

/-- Bit 63. -/
def msb (x : UInt64) : Bool := x >>> 63 == 1

/-- Whether an address is canonical, with bits 63 to 47 all equal. -/
def canonical (a : UInt64) : Bool := a >>> 47 == 0 || a >>> 47 == 0x1FFFF

/-- The effective address of a memory operand, `next` being the address of the next
instruction. -/
def Mem.addr (r : Regs) (next : UInt64) : Mem → UInt64
  | .base b d => r.gpr b + sext32 d
  | .rip d => next + sext32 d
  | .sib b i d => r.gpr b + r.gpr i.1 + sext32 d

/-- Loads 8 bytes, little-endian, and faults on a non-canonical or unreadable address. -/
def load64 (m : Memory) (a : UInt64) : Option UInt64 :=
  if canonical a && canonical (a + 7) then m.readWord a 8 else none

/-- Stores 8 bytes, little-endian, and faults on a non-canonical or unwritable address. -/
def store64 (m : Memory) (a : UInt64) (v : UInt64) : Option Memory :=
  if canonical a && canonical (a + 7) then m.writeWord a 8 v else none

/-- Loads 1 byte, zero-extended, and faults on a non-canonical or unreadable address. -/
def load8 (m : Memory) (a : UInt64) : Option UInt64 :=
  if canonical a then m.readWord a 1 else none

/-- Stores the low byte, and faults on a non-canonical or unwritable address. -/
def store8 (m : Memory) (a : UInt64) (v : UInt64) : Option Memory :=
  if canonical a then m.writeWord a 1 v else none

/-- ZF and SF of a result, with the given CF and OF. -/
def flagsOf (res : UInt64) (cf of : Bool) : Flags := ⟨cf, res == 0, msb res, of⟩

/-- The result and flags of a two-operand ALU operation, where `cmp` computes as `sub` does. -/
def Alu.eval : Alu → UInt64 → UInt64 → UInt64 × Flags
  | .add, a, b => let r := a + b
    (r, flagsOf r (decide (r < a)) (msb a == msb b && msb r != msb a))
  | .sub, a, b | .cmp, a, b => let r := a - b
    (r, flagsOf r (decide (a < b)) (msb a != msb b && msb r != msb a))
  | .and, a, b => let r := a &&& b; (r, flagsOf r false false)
  | .or, a, b => let r := a ||| b; (r, flagsOf r false false)
  | .xor, a, b => let r := a ^^^ b; (r, flagsOf r false false)

/-- Whether the operation writes its destination, which every operation but `cmp` does. -/
def Alu.writes : Alu → Bool
  | .cmp => false
  | _ => true

/-- The result and flags of a shift by `c ∈ [1, 63]`. -/
def Shift.eval : Shift → UInt64 → UInt64 → UInt64 × Flags
  | .shl, a, c => let r := a <<< c
    let cf := (a >>> (64 - c)) &&& 1 == 1
    (r, flagsOf r cf (msb r != cf))
  | .shr, a, c => let r := a >>> c
    (r, flagsOf r ((a >>> (c - 1)) &&& 1 == 1) (msb a))

/-- Whether a condition code holds. -/
def Cond.eval (f : Flags) : Cond → Bool
  | .o => f.of | .no => !f.of
  | .b => f.cf | .ae => !f.cf
  | .e => f.zf | .ne => !f.zf
  | .be => f.cf || f.zf | .a => !f.cf && !f.zf
  | .s => f.sf | .ns => !f.sf
  | .l => f.sf != f.of | .ge => f.sf == f.of
  | .le => f.zf || f.sf != f.of | .g => !f.zf && f.sf == f.of

/-- Signed overflow of a 64-bit multiplication. -/
def imulOverflow (a b : UInt64) : Bool :=
  a.toBitVec.toInt * b.toBitVec.toInt != (a * b).toBitVec.toInt

/-- The RFLAGS image `syscall` leaves in `r11`, with bit 1 and IF set besides CF ZF SF OF. -/
def Flags.image (f : Flags) : UInt64 :=
  0x202 ||| (if f.cf then 1 else 0) ||| (if f.zf then 0x40 else 0) |||
    (if f.sf then 0x80 else 0) ||| (if f.of then 0x800 else 0)

/-- Sets `rip` and leaves the rest of the state alone. -/
def State.jump (s : State) (a : UInt64) : State := { s with regs := { s.regs with rip := a } }

/-- Replaces the registers. -/
def State.withRegs (s : State) (r : Regs) : State := { s with regs := r }

/-- Executes instruction `i` of length `len`, returning `none` on a fault. -/
def exec (trap : State → Option State) (i : Instr) (len : Nat) (s : State) : Option State :=
  let r := s.regs
  let next := r.rip + UInt64.ofNat len
  let fin (r' : Regs) : Option State := some (s.withRegs { r' with rip := next })
  match i with
  | .movRR d src => fin (r.set d (r.gpr src))
  | .movRI d imm => fin (r.set d imm)
  | .load d m => (load64 s.mem (m.addr r next)).bind fun v => fin (r.set d v)
  | .store m src =>
    (store64 s.mem (m.addr r next) (r.gpr src)).map fun mem' =>
      { s with mem := mem', regs := { r with rip := next } }
  | .load8 d m => (load8 s.mem (m.addr r next)).bind fun v => fin (r.set d v)
  | .store8 m src =>
    (store8 s.mem (m.addr r next) (r.gpr src)).map fun mem' =>
      { s with mem := mem', regs := { r with rip := next } }
  | .storeI m imm =>
    (store64 s.mem (m.addr r next) (sext32 imm)).map fun mem' =>
      { s with mem := mem', regs := { r with rip := next } }
  | .store8I m imm =>
    (store8 s.mem (m.addr r next) imm.toUInt64).map fun mem' =>
      { s with mem := mem', regs := { r with rip := next } }
  | .lea d m => fin (r.set d (m.addr r next))
  | .aluRR op d src =>
    let (v, f) := op.eval (r.gpr d) (r.gpr src)
    fin { (if op.writes then r.set d v else r) with flags := f }
  | .aluRI op d imm =>
    let (v, f) := op.eval (r.gpr d) (sext32 imm)
    fin { (if op.writes then r.set d v else r) with flags := f }
  | .imul d src =>
    let a := r.gpr d
    let b := r.gpr src
    let v := a * b
    let o := imulOverflow a b
    fin { r.set d v with flags := flagsOf v o o }
  | .div src =>
    let dv := (r.gpr src).toNat
    let n := (r.gpr .rdx).toNat * 2 ^ 64 + (r.gpr .rax).toNat
    if dv = 0 then none
    else if n / dv < 2 ^ 64 then
      fin ((r.set .rax (UInt64.ofNat (n / dv))).set .rdx (UInt64.ofNat (n % dv)))
    else none
  | .shiftCL op d =>
    let c := r.gpr .rcx &&& 63
    if c = 0 then fin r
    else
      let (v, f) := op.eval (r.gpr d) c
      fin { r.set d v with flags := f }
  | .setcc c d =>
    fin (r.set d ((r.gpr d &&& ~~~0xFF) ||| (if c.eval r.flags then 1 else 0)))
  | .movzx d src => fin (r.set d (r.gpr src &&& 0xFF))
  | .jcc c rel => some (s.jump (if c.eval r.flags then next + sext32 rel else next))
  | .jmp rel => some (s.jump (next + sext32 rel))
  | .call rel =>
    let sp := r.gpr .rsp - 8
    (store64 s.mem sp next).map fun mem' =>
      { s with mem := mem', regs := { r.set .rsp sp with rip := next + sext32 rel } }
  | .ret =>
    (load64 s.mem (r.gpr .rsp)).map fun a =>
      s.withRegs { r.set .rsp (r.gpr .rsp + 8) with rip := a }
  | .push src =>
    let sp := r.gpr .rsp - 8
    (store64 s.mem sp (r.gpr src)).map fun mem' =>
      { s with mem := mem', regs := { r.set .rsp sp with rip := next } }
  | .pop d =>
    (load64 s.mem (r.gpr .rsp)).bind fun v => fin ((r.set .rsp (r.gpr .rsp + 8)).set d v)
  | .syscall =>
    (trap s).map fun s' =>
      s'.withRegs { (s'.regs.set .rcx next).set .r11 s'.regs.flags.image with rip := next }

end Millipede.X64
