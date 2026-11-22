import Millipede.Target.X64.Instr

/-!
# The x64 encoder

`encode` gives the one canonical byte sequence of each instruction, as tabled in `Instr.lean`.
Every instruction of the subset is encodable, so the `Isa` encoder is `some ∘ encode`. The
decoder accepts nothing but these canonical choices:

* A 64-bit form always carries `REX.W`, a prefix from `48` to `4F`, with `REX.X` set only by an
  index register from `r8` to `r15`.
* A register-to-register `mov` and the ALU operations use the `r/m, reg` opcodes such as `89`
  and `01`.
* A memory operand always uses `mod = 10` with a 32-bit displacement, as `[base+disp32]` with the
  SIB byte `24` when the base is `rsp` or `r12`, as `[base+index+disp32]` with a SIB byte of
  scale 1, or `mod = 00, r/m = 101` as `[rip+disp32]`.
* An ALU immediate always uses `81 /digit` with a 32-bit immediate, never `83 ib`.
* `store8`, encoded `88 /r`, carries a REX prefix with `W = 0` exactly when it is needed, for
  `spl bpl sil dil`, `r8b` to `r15b` or a base or index register from `r8` to `r15`, so the byte register
  is always the low byte of the named register and never `ah ch dh bh`.
* `store8I`, encoded `C6 /0 ib`, likewise carries a REX prefix with `W = 0` only for a base or
  index register from `r8` to `r15`.
* `push` and `pop` carry the prefix `41` only for `r8` to `r15`, and `setcc` carries a REX prefix
  only for `r8b` to `r15b` or for `spl bpl sil dil`, which need a plain `40`.
-/

namespace Millipede.X64

/-- The REX prefix `0100WRXB`. -/
def rex (w r x b : Bool) : UInt8 :=
  0x40 ||| (if w then 8 else 0) ||| (if r then 4 else 0) ||| (if x then 2 else 0) |||
    (if b then 1 else 0)

/-- The ModRM byte `mod:2 reg:3 rm:3`. -/
def modrm (md reg rm : UInt8) : UInt8 := (md <<< 6) ||| (reg <<< 3) ||| rm

/-- A 32-bit value, little-endian. -/
def le32 (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- A 64-bit value, little-endian. -/
def le64 (x : UInt64) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
   (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]

/-- The REX.B bit an `r/m` operand needs. -/
def RM.hi : RM → Bool
  | .reg r => r.hi
  | .mem (.base b _) => b.hi
  | .mem (.rip _) => false
  | .mem (.sib b _ _) => b.hi

/-- The REX.X bit an `r/m` operand needs: the index register's high bit. -/
def RM.xhi : RM → Bool
  | .mem (.sib _ i _) => i.1.hi
  | _ => false

/-- The ModRM byte, the optional SIB byte and the displacement, for the 3-bit field `reg`. -/
def encModRM (reg : UInt8) : RM → List UInt8
  | .reg r => [modrm 3 reg r.lo]
  | .mem (.base b d) => modrm 2 reg b.lo :: ((if b.lo = 4 then [0x24] else []) ++ le32 d)
  | .mem (.rip d) => modrm 0 reg 5 :: le32 d
  | .mem (.sib b i d) => modrm 2 reg 4 :: modrm 0 i.1.lo b.lo :: le32 d

/-- A `REX.W` instruction with opcode bytes `opc` and a ModRM operand, whose `reg` field is
`8 * regHi + reg`. -/
def encW (opc : List UInt8) (regHi : Bool) (reg : UInt8) (rm : RM) : List UInt8 :=
  rex true regHi rm.xhi rm.hi :: (opc ++ encModRM reg rm)

namespace Alu
/-- The opcode of the `op r/m64, r64` form. -/
def rr : Alu → UInt8
  | add => 0x01 | or => 0x09 | and => 0x21 | sub => 0x29 | xor => 0x31 | cmp => 0x39
/-- The `/digit` of the `81 /digit id` form. -/
def digit : Alu → UInt8
  | add => 0 | or => 1 | and => 4 | sub => 5 | xor => 6 | cmp => 7
/-- The inverse of `rr`. -/
def ofRR (b : UInt8) : Option Alu :=
  if b = 0x01 then some add else if b = 0x09 then some or else if b = 0x21 then some and
  else if b = 0x29 then some sub else if b = 0x31 then some xor else if b = 0x39 then some cmp
  else none
/-- The inverse of `digit`. -/
def ofDigit (b : UInt8) : Option Alu :=
  if b = 0 then some add else if b = 1 then some or else if b = 4 then some and
  else if b = 5 then some sub else if b = 6 then some xor else if b = 7 then some cmp
  else none
@[simp] theorem ofRR_rr (op : Alu) : ofRR op.rr = some op := by cases op <;> rfl
@[simp] theorem ofDigit_digit (op : Alu) : ofDigit op.digit = some op := by cases op <;> rfl
theorem digit_lt (op : Alu) : op.digit < 8 := by cases op <;> decide
/-- All ALU operations. -/
def all : List Alu := [add, or, and, sub, xor, cmp]
end Alu

namespace Shift
/-- The `/digit` of `D3 /digit`. -/
def digit : Shift → UInt8
  | shl => 4 | shr => 5
/-- The inverse of `digit`. -/
def ofDigit (b : UInt8) : Option Shift :=
  if b = 4 then some shl else if b = 5 then some shr else none
@[simp] theorem ofDigit_digit (op : Shift) : ofDigit op.digit = some op := by cases op <;> rfl
theorem digit_lt (op : Shift) : op.digit < 8 := by cases op <;> decide
end Shift

/-- Whether a byte operand in this register needs a REX prefix. -/
def Reg.needsRex8 (r : Reg) : Bool := r.hi || decide (4 ≤ r.lo)

/-- The encoder, which gives the canonical bytes of each instruction. -/
def encode : Instr → List UInt8
  | .movRR d s => encW [0x89] s.hi s.lo (.reg d)
  | .movRI d imm => rex true false false d.hi :: (0xB8 + d.lo) :: le64 imm
  | .load d m => encW [0x8B] d.hi d.lo (.mem m)
  | .store m s => encW [0x89] s.hi s.lo (.mem m)
  | .load8 d m => encW [0x0F, 0xB6] d.hi d.lo (.mem m)
  | .store8 m s =>
    (if s.needsRex8 || (RM.mem m).hi || (RM.mem m).xhi then
      [rex false s.hi (RM.mem m).xhi (RM.mem m).hi] else []) ++
      0x88 :: encModRM s.lo (.mem m)
  | .storeI m imm => encW [0xC7] false 0 (.mem m) ++ le32 imm
  | .store8I m imm =>
    (if (RM.mem m).hi || (RM.mem m).xhi then [rex false false (RM.mem m).xhi (RM.mem m).hi] else []) ++
      0xC6 :: (encModRM 0 (.mem m) ++ [imm])
  | .lea d m => encW [0x8D] d.hi d.lo (.mem m)
  | .aluRR op d s => encW [op.rr] s.hi s.lo (.reg d)
  | .aluRI op d imm => encW [0x81] false op.digit (.reg d) ++ le32 imm
  | .imul d s => encW [0x0F, 0xAF] d.hi d.lo (.reg s)
  | .div s => encW [0xF7] false 6 (.reg s)
  | .shiftCL op d => encW [0xD3] false op.digit (.reg d)
  | .setcc c d =>
    (if d.needsRex8 then [rex false false false d.hi] else []) ++
      [0x0F, 0x90 + c.code, modrm 3 0 d.lo]
  | .movzx d s => encW [0x0F, 0xB6] d.hi d.lo (.reg s)
  | .jcc c rel => 0x0F :: (0x80 + c.code) :: le32 rel
  | .jmp rel => 0xE9 :: le32 rel
  | .call rel => 0xE8 :: le32 rel
  | .ret => [0xC3]
  | .push r => (if r.hi then [0x41] else []) ++ [0x50 + r.lo]
  | .pop r => (if r.hi then [0x41] else []) ++ [0x58 + r.lo]
  | .syscall => [0x0F, 0x05]

end Millipede.X64
