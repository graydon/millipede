/-!
# The modelled x64 instructions

The model covers the subset of x64 that the code generator needs. Every instruction has 64-bit
operand size except four: `setcc` writes the low byte of a register, `movzx` zero-extends the
low byte of a register into 64 bits, `load8` is a zero-extending byte load, and `store8` stores
the low byte of a register. `store8` can store the low byte of any of the 16 registers, never
`ah ch dh bh`, because the encoder adds a REX prefix where one is needed.

The following table gives each instruction's assembly and encoding.

| constructor | assembly (Intel syntax) | encoding |
|---|---|---|
| `movRR d s` | `mov d, s` | `REX.W 89 /r` (mod = 11) |
| `movRI d imm` | `movabs d, imm64` | `REX.W B8+r io` |
| `load d m` | `mov d, QWORD PTR m` | `REX.W 8B /r` |
| `store m s` | `mov QWORD PTR m, s` | `REX.W 89 /r` |
| `load8 d m` | `movzx d, BYTE PTR m` | `REX.W 0F B6 /r` (memory operand) |
| `store8 m s` | `mov BYTE PTR m, s8` | `[REX] 88 /r` |
| `storeI m imm` | `mov QWORD PTR m, imm32` (sign-extended) | `REX.W C7 /0 id` |
| `store8I m imm` | `mov BYTE PTR m, imm8` | `[REX] C6 /0 ib` |
| `lea d m` | `lea d, m` | `REX.W 8D /r` |
| `aluRR op d s` | `add/or/and/sub/xor/cmp d, s` | `REX.W 01/09/21/29/31/39 /r` |
| `aluRI op d imm` | `op d, imm32` (sign-extended) | `REX.W 81 /0,1,4,5,6,7 id` |
| `imul d s` | `imul d, s` | `REX.W 0F AF /r` |
| `div s` | `div s` (unsigned `rdx:rax / s`) | `REX.W F7 /6` |
| `shiftCL op d` | `shl/shr d, cl` | `REX.W D3 /4, /5` |
| `setcc c d` | `setCC d8` | `[REX] 0F 90+cc /0` |
| `movzx d s` | `movzx d, s8` | `REX.W 0F B6 /r` |
| `jcc c rel` | `jCC rel32` | `0F 80+cc cd` |
| `jmp rel` | `jmp rel32` | `E9 cd` |
| `call rel` | `call rel32` | `E8 cd` |
| `ret` | `ret` | `C3` |
| `push r` / `pop r` | `push r` / `pop r` | `[41] 50+r` / `[41] 58+r` |
| `syscall` | `syscall` | `0F 05` |

A memory operand is `[base + disp32]` for any base register, always encoded with a 32-bit
displacement and mod = 10 and with the SIB byte `24` for `rsp` and `r12`, `[base + index +
disp32]` with a SIB byte of scale 1 for any base and any index but `rsp` (mod = 10, `REX.X` the
index's high bit), or `[rip + disp32]`, relative to the end of the instruction. Immediates and displacements are stored at their encoded
width, with a `UInt32` sign-extended where the hardware does so, so every instruction is
encodable.

The condition codes are the 14 that depend only on CF, ZF, SF and OF. The parity conditions are
not modelled, since PF is not part of the state.
-/

namespace Millipede.X64

/-- The 16 general-purpose registers, in encoding order. -/
inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving DecidableEq, Repr, Inhabited

namespace Reg

/-- All registers, in encoding order. -/
def all : List Reg := [rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15]

/-- Bit 3 of the register number, which goes into a REX bit. -/
def hi : Reg → Bool
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi => false
  | _ => true

/-- Bits 0–2 of the register number, which go into ModRM or the opcode byte. -/
def lo : Reg → UInt8
  | rax | r8 => 0 | rcx | r9 => 1 | rdx | r10 => 2 | rbx | r11 => 3
  | rsp | r12 => 4 | rbp | r13 => 5 | rsi | r14 => 6 | rdi | r15 => 7

/-- The register with number `8 * hi + (lo % 8)`. -/
def ofBits (hi : Bool) (lo : UInt8) : Reg :=
  match hi, lo &&& 7 with
  | false, 0 => rax | false, 1 => rcx | false, 2 => rdx | false, 3 => rbx
  | false, 4 => rsp | false, 5 => rbp | false, 6 => rsi | false, 7 => rdi
  | true, 0 => r8 | true, 1 => r9 | true, 2 => r10 | true, 3 => r11
  | true, 4 => r12 | true, 5 => r13 | true, 6 => r14 | _, _ => r15

@[simp] theorem ofBits_hi_lo (r : Reg) : ofBits r.hi r.lo = r := by cases r <;> rfl

theorem lo_lt (r : Reg) : r.lo < 8 := by cases r <;> decide

/-- The register number, 0–15. -/
def num (r : Reg) : Nat := (if r.hi then 8 else 0) + r.lo.toNat

end Reg

/-- An index register of a SIB byte: any register but `rsp`, whose number there means "no
index". -/
abbrev Idx := {r : Reg // r ≠ .rsp}

/-- A memory operand. -/
inductive Mem
  /-- `[base + sext disp]`. -/
  | base (b : Reg) (disp : UInt32)
  /-- `[rip + sext disp]`, where `rip` is the address of the next instruction. -/
  | rip (disp : UInt32)
  /-- `[base + index + sext disp]`, a SIB byte with scale 1. -/
  | sib (b : Reg) (i : Idx) (disp : UInt32)
deriving DecidableEq, Repr, Inhabited

/-- A ModRM `r/m` operand: a register or memory. -/
inductive RM
  | reg (r : Reg)
  | mem (m : Mem)
deriving DecidableEq, Repr, Inhabited

/-- Two-operand integer operations sharing the `/r` and `81 /digit` encodings. -/
inductive Alu
  | add | or | and | sub | xor | cmp
deriving DecidableEq, Repr, Inhabited

/-- Shifts by `cl`. -/
inductive Shift
  | shl | shr
deriving DecidableEq, Repr, Inhabited

/-- The condition codes other than parity, named by Intel's mnemonic suffix. -/
inductive Cond
  | o | no | b | ae | e | ne | be | a | s | ns | l | ge | le | g
deriving DecidableEq, Repr, Inhabited

namespace Cond
/-- The 4-bit condition number `cc` in `0F 80+cc` / `0F 90+cc`. -/
def code : Cond → UInt8
  | o => 0 | no => 1 | b => 2 | ae => 3 | e => 4 | ne => 5 | be => 6 | a => 7
  | s => 8 | ns => 9 | l => 12 | ge => 13 | le => 14 | g => 15

/-- The inverse of `code`, which is `none` for the parity conditions 10 and 11. -/
def ofCode (c : UInt8) : Option Cond :=
  match c &&& 15 with
  | 0 => some o | 1 => some no | 2 => some b | 3 => some ae | 4 => some e | 5 => some ne
  | 6 => some be | 7 => some a | 8 => some s | 9 => some ns | 12 => some l | 13 => some ge
  | 14 => some le | 15 => some g | _ => none

@[simp] theorem ofCode_code (c : Cond) : ofCode c.code = some c := by cases c <;> rfl

/-- All condition codes. -/
def all : List Cond := [o, no, b, ae, e, ne, be, a, s, ns, l, ge, le, g]
end Cond

/-- The modelled x64 instructions, whose assembly and encoding the module doc lists. -/
inductive Instr
  | movRR (dst src : Reg)
  | movRI (dst : Reg) (imm : UInt64)
  | load (dst : Reg) (m : Mem)
  | store (m : Mem) (src : Reg)
  /-- `movzx dst, byte [m]`. -/
  | load8 (dst : Reg) (m : Mem)
  /-- `mov byte [m], src8`. -/
  | store8 (m : Mem) (src : Reg)
  /-- `mov qword [m], sext imm32`. -/
  | storeI (m : Mem) (imm : UInt32)
  /-- `mov byte [m], imm8`. -/
  | store8I (m : Mem) (imm : UInt8)
  | lea (dst : Reg) (m : Mem)
  | aluRR (op : Alu) (dst src : Reg)
  | aluRI (op : Alu) (dst : Reg) (imm : UInt32)
  | imul (dst src : Reg)
  | div (src : Reg)
  | shiftCL (op : Shift) (dst : Reg)
  | setcc (c : Cond) (dst : Reg)
  | movzx (dst src : Reg)
  | jcc (c : Cond) (rel : UInt32)
  | jmp (rel : UInt32)
  | call (rel : UInt32)
  | ret
  | push (r : Reg)
  | pop (r : Reg)
  | syscall
deriving DecidableEq, Repr, Inhabited

/-- The 64-bit name of the register. -/
def Reg.name : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The name of the low byte of the register. -/
def Reg.name8 : Reg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | r => r.name ++ "b"

/-- The mnemonic suffix of the condition. -/
def Cond.name : Cond → String
  | .o => "o" | .no => "no" | .b => "b" | .ae => "ae" | .e => "e" | .ne => "ne"
  | .be => "be" | .a => "a" | .s => "s" | .ns => "ns" | .l => "l" | .ge => "ge"
  | .le => "le" | .g => "g"

/-- The mnemonic of the operation. -/
def Alu.name : Alu → String
  | .add => "add" | .or => "or" | .and => "and" | .sub => "sub" | .xor => "xor" | .cmp => "cmp"

end Millipede.X64
