import Millipede.Target.A64.Instr
import Millipede.Core.LE

/-!
# The arm64 encoder

Every instruction is one 32-bit word, the `or` of a fixed opcode pattern and the operand fields at
their positions, and `bytes` stores the word little-endian. The field layouts are those of the
Arm Architecture Reference Manual, and `scripts/a64-encode-check.sh` checks them against the
assembly of the same text by `llvm-mc` and the disassembly of the bytes by GNU objdump.

Where the architecture allows several encodings, the encoder makes one canonical choice, and the
decoder accepts nothing else. Shifted-register forms use `lsl #0`, a register offset of `ldr` or
`str` uses the option `lsl` with `S = 0`, and the `N` bit of `sbfm` and `ubfm` equals `sf`. Each
enumeration has a field value `bits` and a total inverse `ofBits`, which maps an unallocated
value to some constructor that the decoder's re-encoding check then rejects.
-/

namespace Millipede.A64

/-- A field `x` placed at bit position `pos` of an instruction word. -/
def fld {n : Nat} (x : BitVec n) (pos : Nat) : BitVec 32 := x.setWidth 32 <<< pos

/-- A one-bit field. -/
def bit (b : Bool) (pos : Nat) : BitVec 32 := fld (BitVec.ofBool b) pos

namespace MovOp
def bits : MovOp → BitVec 2
  | n => 0 | z => 2 | k => 3
def ofBits (x : BitVec 2) : MovOp := if x = 0 then n else if x = 2 then z else k
@[simp] theorem ofBits_bits (o : MovOp) : ofBits o.bits = o := by cases o <;> decide
/-- The unallocated value `01` reads as `k`. -/
theorem ofBits_eq_iff (x : BitVec 2) (o : MovOp) : ofBits x = o ↔ x = o.bits ∨ (x = 1 ∧ o = k) := by
  revert x; cases o <;> decide
end MovOp

namespace LogOp
def bits : LogOp → BitVec 2
  | and => 0 | orr => 1 | eor => 2 | ands => 3
def ofBits (x : BitVec 2) : LogOp := if x = 0 then and else if x = 1 then orr else if x = 2 then eor else ands
theorem ofBits_eq_iff (x : BitVec 2) (o : LogOp) : ofBits x = o ↔ x = o.bits := by
  revert x; cases o <;> decide
end LogOp

namespace ShiftOp
def bits : ShiftOp → BitVec 2
  | lsl => 0 | lsr => 1 | asr => 2 | ror => 3
def ofBits (x : BitVec 2) : ShiftOp := if x = 0 then lsl else if x = 1 then lsr else if x = 2 then asr else ror
theorem ofBits_eq_iff (x : BitVec 2) (o : ShiftOp) : ofBits x = o ↔ x = o.bits := by
  revert x; cases o <;> decide
end ShiftOp

namespace CselOp
/-- The fields `op`, bit 30 of the instruction, and `o2`, bit 10, as `op * 2 + o2`. -/
def bits : CselOp → BitVec 2
  | csel => 0 | csinc => 1 | csinv => 2 | csneg => 3
def ofBits (x : BitVec 2) : CselOp := if x = 0 then csel else if x = 1 then csinc else if x = 2 then csinv else csneg
theorem ofBits_eq_iff (x : BitVec 2) (o : CselOp) : ofBits x = o ↔ x = o.bits := by
  revert x; cases o <;> decide
end CselOp

namespace Size
def bits : Size → BitVec 2
  | b => 0 | h => 1 | w => 2 | x => 3
def ofBits (v : BitVec 2) : Size := if v = 0 then b else if v = 1 then h else if v = 2 then w else x
theorem ofBits_eq_iff (v : BitVec 2) (s : Size) : ofBits v = s ↔ v = s.bits := by
  revert v; cases s <;> decide
end Size

namespace Cond
def bits : Cond → BitVec 4
  | eq => 0 | ne => 1 | cs => 2 | cc => 3 | mi => 4 | pl => 5 | vs => 6 | vc => 7
  | hi => 8 | ls => 9 | ge => 10 | lt => 11 | gt => 12 | le => 13 | al => 14 | nv => 15
def ofBits (v : BitVec 4) : Cond :=
  match v.toNat with
  | 0 => eq | 1 => ne | 2 => cs | 3 => cc | 4 => mi | 5 => pl | 6 => vs | 7 => vc
  | 8 => hi | 9 => ls | 10 => ge | 11 => lt | 12 => gt | 13 => le | 14 => al | _ => nv
theorem ofBits_eq_iff (v : BitVec 4) (c : Cond) : ofBits v = c ↔ v = c.bits := by
  revert v; cases c <;> decide
/-- The opposite condition, where `al` and `nv` map to each other and both always hold. -/
def invert (c : Cond) : Cond := ofBits (c.bits ^^^ 1)
end Cond

/-- The address fields of a load or store of size `sz`, where `opc` is `00` for a store and
`01` for a load. -/
def Addr.enc (sz : Size) (opc : BitVec 2) : Addr → BitVec 32
  | .uimm n imm => 0x39000000#32 ||| fld sz.bits 30 ||| fld opc 22 ||| fld imm 10 ||| fld n 5
  | .simm n imm => 0x38000000#32 ||| fld sz.bits 30 ||| fld opc 22 ||| fld imm 12 ||| fld n 5
  | .reg n m => 0x38206800#32 ||| fld sz.bits 30 ||| fld opc 22 ||| fld m 16 ||| fld n 5

/-- The instruction word of an instruction. -/
def encode : Instr → BitVec 32
  | .mov op sf d imm hw =>
    0x12800000#32 ||| bit sf 31 ||| fld op.bits 29 ||| fld hw 21 ||| fld imm 5 ||| fld d 0
  | .addImm sf sub setf d n imm sh =>
    0x11000000#32 ||| bit sf 31 ||| bit sub 30 ||| bit setf 29 ||| bit sh 22 ||| fld imm 10 |||
      fld n 5 ||| fld d 0
  | .addReg sf sub setf d n m =>
    0x0B000000#32 ||| bit sf 31 ||| bit sub 30 ||| bit setf 29 ||| fld m 16 ||| fld n 5 ||| fld d 0
  | .logReg op sf d n m =>
    0x0A000000#32 ||| bit sf 31 ||| fld op.bits 29 ||| fld m 16 ||| fld n 5 ||| fld d 0
  | .madd sf sub d n m a =>
    0x1B000000#32 ||| bit sf 31 ||| fld m 16 ||| bit sub 15 ||| fld a 10 ||| fld n 5 ||| fld d 0
  | .div sf signed d n m =>
    0x1AC00800#32 ||| bit sf 31 ||| fld m 16 ||| bit signed 10 ||| fld n 5 ||| fld d 0
  | .shiftV op sf d n m =>
    0x1AC02000#32 ||| bit sf 31 ||| fld m 16 ||| fld op.bits 10 ||| fld n 5 ||| fld d 0
  | .bfm signed sf d n immr imms =>
    0x13000000#32 ||| bit sf 31 ||| bit (!signed) 30 ||| bit sf 22 ||| fld immr 16 |||
      fld imms 10 ||| fld n 5 ||| fld d 0
  | .csel op sf d n m c =>
    0x1A800000#32 ||| bit sf 31 ||| fld (op.bits.extractLsb' 1 1) 30 ||| fld m 16 |||
      fld c.bits 12 ||| fld (op.bits.extractLsb' 0 1) 10 ||| fld n 5 ||| fld d 0
  | .ldr sz t a => a.enc sz 1 ||| fld t 0
  | .str sz t a => a.enc sz 0 ||| fld t 0
  | .adr page d imm =>
    0x10000000#32 ||| bit page 31 ||| fld (imm.extractLsb' 0 2) 29 ||| fld (imm.extractLsb' 2 19) 5 |||
      fld d 0
  | .b link imm => 0x14000000#32 ||| bit link 31 ||| fld imm 0
  | .bcond c imm => 0x54000000#32 ||| fld imm 5 ||| fld c.bits 0
  | .cbz sf nz t imm => 0x34000000#32 ||| bit sf 31 ||| bit nz 24 ||| fld imm 5 ||| fld t 0
  | .ret n => 0xD65F0000#32 ||| fld n 5
  | .svc imm => 0xD4000001#32 ||| fld imm 5

/-- The four bytes of an instruction, little-endian. -/
def bytes (i : Instr) : List UInt8 := natBytes 4 (encode i).toNat

@[simp] theorem bytes_length (i : Instr) : (bytes i).length = 4 := natBytes_length _ _

end Millipede.A64
