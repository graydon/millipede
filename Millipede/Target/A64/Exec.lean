import Millipede.Target.A64.Decode
import Millipede.Target.Machine

/-!
# arm64 machine state and execution

The register file `Regs` holds the general registers `x0` to `x30` and the stack pointer as one
map `x : Reg → UInt64`, in which number 31 is `sp`, together with the program counter `pc` and
the flags N, Z, C and V. A machine state adds the shared memory and world of `MState`.

The function `exec trap i len s` executes instruction `i` at `s.regs.pc` and returns `none` on a
fault. Every arm64 instruction is 4 bytes, so the fall-through address is `pc + 4` whatever `len`
says. Where an instruction reads register 31 as `xzr` it reads `0`, and a write to it is
discarded; where register 31 means the stack pointer, it is `sp`. A 32-bit form computes on the
low 32 bits of its operands, writes its result zero-extended and sets the flags of the 32-bit
operation.

The flags follow the architecture. `adds` and `subs` set them as `AddWithCarry` does, so after
`subs` the flag C means that there was no borrow, while `ands` sets N and Z and clears C and V, and
no other instruction changes them. Division by zero gives `0` without a fault, `sdiv` of the most
negative value by `-1` gives the most negative value, and a shift by a register takes the amount
modulo the width.

Loads and stores are little-endian, need readable or writable pages, and loads zero-extend.
Addresses wrap modulo 2⁶⁴ and are not otherwise checked. No loader model maps a page above 2⁴⁸,
so an access beyond the 48-bit address space, which the hardware would refuse, is refused by the
model as unmapped. Unaligned accesses are allowed, because Linux runs user code with alignment
checking off.

An instruction faults when it loads from unreadable memory or stores to unwritable memory, when it
accesses memory through `sp` while `sp` is not a multiple of 16, which Linux checks for user code,
and when it executes at a `pc` that is not a multiple of 4. `svc` hands the state to `trap` and
continues at `pc + 4`. Linux takes the call number in `x8` and the arguments in `x0` to `x5`,
returns the result in `x0`, and preserves every other register and the flags.

The model leaves out every instruction outside the subset, which does not decode, as well as
exception levels, the system registers, the exclusive monitor, top-byte-ignore and memory
ordering, since a program runs as one thread.
-/

namespace Millipede.A64

/-- The condition flags. -/
structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
deriving DecidableEq, Repr, Inhabited

/-- The register file, which holds `x0` to `x30`, `sp` as number 31, `pc` and the flags. -/
structure Regs where
  x : Reg → UInt64
  pc : UInt64
  flags : Flags

namespace Regs

/-- Write register `k`, where 31 is `sp`. -/
def set (r : Regs) (k : Reg) (v : UInt64) : Regs :=
  { r with x := fun k' => if k' = k then v else r.x k' }

/-- Read register `k` where 31 is `xzr`. -/
def getZ (r : Regs) (k : Reg) : UInt64 := if k = 31 then 0 else r.x k

/-- Write register `k`, where 31 is `xzr` and a write to it is discarded. -/
def setZ (r : Regs) (k : Reg) (v : UInt64) : Regs := if k = 31 then r else r.set k v

@[simp] theorem set_x (r : Regs) (k k' : Reg) (v : UInt64) :
    (r.set k v).x k' = if k' = k then v else r.x k' := rfl
@[simp] theorem set_pc (r : Regs) (k : Reg) (v : UInt64) : (r.set k v).pc = r.pc := rfl
@[simp] theorem set_flags (r : Regs) (k : Reg) (v : UInt64) : (r.set k v).flags = r.flags := rfl

end Regs

/-- The arm64 machine state. -/
abbrev State := MState Regs

/-- Sign-extend a field to 64 bits. -/
def sext {n : Nat} (x : BitVec n) : UInt64 := UInt64.ofBitVec (x.signExtend 64)

/-- The width of an operation: 64 bits if `sf`, else 32. -/
def width (sf : Bool) : Nat := if sf then 64 else 32

/-- A result at width `sf`, which for a 32-bit operation is the low 32 bits zero-extended. -/
def wid (sf : Bool) (v : UInt64) : UInt64 := if sf then v else v &&& 0xFFFFFFFF

/-- A binary operation at width `sf` on the low bits of the operands, zero-extended back. -/
def bin (sf : Bool) (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (a b : UInt64) : UInt64 :=
  if sf then UInt64.ofBitVec (f 64 a.toBitVec b.toBitVec)
  else UInt64.ofBitVec ((f 32 (a.toBitVec.setWidth 32) (b.toBitVec.setWidth 32)).setWidth 64)

/-- The architecture's `AddWithCarry` at width `w`, which returns the result and the flags. -/
def addWithCarry (w : Nat) (x y : BitVec w) (carry : Bool) : BitVec w × Flags :=
  let c := if carry then 1 else 0
  let usum := x.toNat + y.toNat + c
  let ssum := x.toInt + y.toInt + c
  let r := BitVec.ofNat w usum
  (r, ⟨r.msb, r == 0, r.toNat != usum, r.toInt != ssum⟩)

/-- `add` or `sub` at width `sf`, which returns the zero-extended result and the flags.
Subtraction is `x + ~y + 1`. -/
def addSub (sf sub : Bool) (a b : UInt64) : UInt64 × Flags :=
  let go (w : Nat) (x y : BitVec w) : BitVec w × Flags :=
    if sub then addWithCarry w x (~~~y) true else addWithCarry w x y false
  if sf then let p := go 64 a.toBitVec b.toBitVec; (UInt64.ofBitVec p.1, p.2)
  else
    let p := go 32 (a.toBitVec.setWidth 32) (b.toBitVec.setWidth 32)
    (UInt64.ofBitVec (p.1.setWidth 64), p.2)

/-- Whether a condition holds of the flags, as the architecture's `ConditionHolds`, under
which `al` and `nv` always hold. -/
def Cond.holds (f : Flags) : Cond → Bool
  | .eq => f.z | .ne => !f.z
  | .cs => f.c | .cc => !f.c
  | .mi => f.n | .pl => !f.n
  | .vs => f.v | .vc => !f.v
  | .hi => f.c && !f.z | .ls => !(f.c && !f.z)
  | .ge => f.n == f.v | .lt => f.n != f.v
  | .gt => !f.z && f.n == f.v | .le => !(!f.z && f.n == f.v)
  | .al | .nv => true

/-- The logical operations. -/
def LogOp.eval : LogOp → (w : Nat) → BitVec w → BitVec w → BitVec w
  | .and, _, x, y | .ands, _, x, y => x &&& y
  | .orr, _, x, y => x ||| y
  | .eor, _, x, y => x ^^^ y

/-- A shift by a register, which takes the amount modulo the width. -/
def ShiftOp.eval : ShiftOp → (w : Nat) → BitVec w → BitVec w → BitVec w
  | .lsl, w, x, y => x <<< (y.toNat % w)
  | .lsr, w, x, y => x >>> (y.toNat % w)
  | .asr, w, x, y => x.sshiftRight (y.toNat % w)
  | .ror, w, x, y => x.rotateRight (y.toNat % w)

/-- The second operand of a conditional select when the condition fails. -/
def CselOp.eval : CselOp → (w : Nat) → BitVec w → BitVec w
  | .csel, _, y => y
  | .csinc, _, y => y + 1
  | .csinv, _, y => ~~~y
  | .csneg, _, y => -y

/-- `sbfm` or `ubfm` at width `w` with `immr = r` and `imms = s`. When `r ≤ s` the bits `r..s` of
`x` move to the bottom, and otherwise the bits `0..s` move up to position `w - r`. Above the field
the result is sign-extended by `sbfm` and zero-extended by `ubfm`, and below it is zero. -/
def bfmVal (signed : Bool) (w : Nat) (x : BitVec w) (r s : Nat) : BitVec w :=
  let ext {k : Nat} (f : BitVec k) : BitVec w := if signed then f.signExtend w else f.setWidth w
  if r ≤ s then ext (x.extractLsb' r (s - r + 1))
  else ext (x.extractLsb' 0 (s + 1)) <<< (w - r)

/-- The wide-immediate moves at width `sf`, given the old value of the register, which `movk`
keeps outside its halfword. -/
def movVal (op : MovOp) (sf : Bool) (old : UInt64) (imm : BitVec 16) (hw : BitVec 2) : UInt64 :=
  let sh := 16 * hw.toNat.toUInt64
  let v := imm.toNat.toUInt64 <<< sh
  wid sf (match op with
    | .z => v
    | .n => ~~~v
    | .k => (old &&& ~~~((0xFFFF : UInt64) <<< sh)) ||| v)

/-- The base register of an address, where 31 is `sp`. -/
def Addr.base : Addr → Reg
  | .uimm n _ | .simm n _ | .reg n _ => n

/-- The effective address of an access of size `sz`. -/
def Addr.ea (r : Regs) (sz : Size) : Addr → UInt64
  | .uimm n imm => r.x n + imm.toNat.toUInt64 * sz.bytes.toUInt64
  | .simm n imm => r.x n + sext imm
  | .reg n m => r.x n + r.getZ m

/-- The stack-alignment check: an access based on `sp` needs `sp` to be a multiple of 16. -/
def Addr.aligned (r : Regs) (a : Addr) : Bool := a.base != 31 || r.x 31 % 16 == 0

/-- Replace the registers by `r` with `pc := a`, keeping memory and world. -/
def State.goto (s : State) (r : Regs) (a : UInt64) : State := { s with regs := { r with pc := a } }

/-- Execute instruction `i`, with `none` for a fault. -/
def exec (trap : State → Option State) (i : Instr) (_len : Nat) (s : State) : Option State :=
  let r := s.regs
  let next := r.pc + 4
  let fin (r' : Regs) : Option State := some (s.goto r' next)
  if r.pc % 4 ≠ 0 then none else
  match i with
  | .mov op sf d imm hw => fin (r.setZ d (movVal op sf (r.getZ d) imm hw))
  | .addImm sf sub setf d n imm sh =>
    let b := imm.toNat.toUInt64 <<< (if sh then 12 else 0)
    let (v, f) := addSub sf sub (r.x n) b
    fin (if setf then { r.setZ d v with flags := f } else r.set d v)
  | .addReg sf sub setf d n m =>
    let (v, f) := addSub sf sub (r.getZ n) (r.getZ m)
    fin (if setf then { r.setZ d v with flags := f } else r.setZ d v)
  | .logReg op sf d n m =>
    let v := bin sf op.eval (r.getZ n) (r.getZ m)
    let f : Flags := ⟨if sf then v >>> 63 == 1 else v >>> 31 == 1, v == 0, false, false⟩
    fin (if op = .ands then { r.setZ d v with flags := f } else r.setZ d v)
  | .madd sf sub d n m a =>
    let p := r.getZ n * r.getZ m
    fin (r.setZ d (wid sf (if sub then r.getZ a - p else r.getZ a + p)))
  | .div sf signed d n m =>
    fin (r.setZ d (bin sf (fun _ x y => if signed then x.sdiv y else x / y) (r.getZ n) (r.getZ m)))
  | .shiftV op sf d n m => fin (r.setZ d (bin sf op.eval (r.getZ n) (r.getZ m)))
  | .bfm signed sf d n immr imms =>
    fin (r.setZ d (bin sf (fun w x _ => bfmVal signed w x immr.toNat imms.toNat) (r.getZ n) 0))
  | .csel op sf d n m c =>
    fin (r.setZ d (bin sf (fun w x y => if c.holds r.flags then x else op.eval w y)
      (r.getZ n) (r.getZ m)))
  | .ldr sz t a =>
    if a.aligned r then (s.mem.readWord (a.ea r sz) sz.bytes).bind fun v => fin (r.setZ t v)
    else none
  | .str sz t a =>
    if a.aligned r then
      (s.mem.writeWord (a.ea r sz) sz.bytes (r.getZ t)).map fun m =>
        { s.goto r next with mem := m }
    else none
  | .adr page d imm =>
    fin (r.setZ d (if page then (r.pc &&& ~~~(0xFFF : UInt64)) + (sext imm <<< 12) else r.pc + sext imm))
  | .b link imm =>
    some (s.goto (if link then r.set 30 next else r) (r.pc + (sext imm <<< 2)))
  | .bcond c imm => some (s.goto r (if c.holds r.flags then r.pc + (sext imm <<< 2) else next))
  | .cbz sf nz t imm =>
    some (s.goto r (if (wid sf (r.getZ t) == 0) != nz then r.pc + (sext imm <<< 2) else next))
  | .ret n => some (s.goto r (r.getZ n))
  | .svc _ => (trap s).map fun s' => s'.goto s'.regs next

end Millipede.A64
