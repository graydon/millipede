import Millipede.Target.X64.Encode

/-!
# The x64 decoder

`decode bs` returns the instruction at the start of `bs` and its length, or `none`. It works in
two stages. First `parse` reads an optional REX prefix, the opcode, the ModRM and SIB bytes, the
displacement and the immediate, leniently, ignoring bits that the canonical form fixes, such as
the SIB byte or `REX.W` on `setcc`. Then `decode` encodes the parsed instruction again and
accepts it only if those bytes are exactly what `bs` starts with.

So `decode` accepts only the canonical encodings of the subset, and `decode bs = some (i, n)`
implies `bs = encode i ++ bs.drop n`. Every other byte sequence decodes to `none`, which leaves
the machine stuck. This includes other instructions, prefixes, and alternative encodings such as
`8B` for a register move or `83` for a small immediate.
-/

namespace Millipede.X64

/-- The four REX bits. -/
structure Rex where
  w : Bool
  r : Bool
  x : Bool
  b : Bool
deriving DecidableEq, Repr

/-- The REX bits of a prefix byte. -/
def rexOf (b : UInt8) : Rex := ⟨b &&& 8 != 0, b &&& 4 != 0, b &&& 2 != 0, b &&& 1 != 0⟩

/-- Whether this byte is a REX prefix, `40` to `4F`. -/
def isRex (b : UInt8) : Bool := b >>> 4 == 4

/-- No REX prefix. -/
def Rex.none : Rex := ⟨false, false, false, false⟩

/-- Reads a little-endian 32-bit value. -/
def get32 : List UInt8 → Option (UInt32 × List UInt8)
  | a :: b :: c :: d :: rest =>
    some (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24), rest)
  | _ => none

/-- Reads a little-endian 64-bit value. -/
def get64 : List UInt8 → Option (UInt64 × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
      (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
      (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56), rest)
  | _ => none

/-- The memory operand of a SIB byte `s` with a displacement: `[base + disp]` when the index field
names no index (`rsp`), else `[base + index + disp]`. The scale is ignored. -/
def sibMem (rexX rexB : Bool) (s : UInt8) (d : UInt32) : Mem :=
  if h : Reg.ofBits rexX ((s >>> 3) &&& 7) = .rsp then .base (Reg.ofBits rexB (s &&& 7)) d
  else .sib (Reg.ofBits rexB (s &&& 7)) ⟨_, h⟩ d

/-- Reads the ModRM byte with its SIB byte and displacement, and returns the 3-bit `reg` field,
the `r/m` operand and the bytes after it. It accepts `mod = 11`, `mod = 10`, reading the SIB
byte when `r/m = 100`, and the `rip`-relative `mod = 00, r/m = 101`. -/
def parseModRM (rexX rexB : Bool) : List UInt8 → Option (UInt8 × RM × List UInt8)
  | [] => none
  | m :: rest =>
    if m >>> 6 = 3 then some ((m >>> 3) &&& 7, .reg (Reg.ofBits rexB (m &&& 7)), rest)
    else if m >>> 6 = 2 then
      if m &&& 7 = 4 then
        match rest with
        | [] => none
        | sb :: rest' =>
          (get32 rest').map fun p => ((m >>> 3) &&& 7, .mem (sibMem rexX rexB sb p.1), p.2)
      else
        (get32 rest).map fun p =>
          ((m >>> 3) &&& 7, .mem (.base (Reg.ofBits rexB (m &&& 7)) p.1), p.2)
    else if m = modrm 0 ((m >>> 3) &&& 7) 5 then
      (get32 rest).map fun p => ((m >>> 3) &&& 7, .mem (.rip p.1), p.2)
    else none

/-- A ModRM operand that must be a register. -/
def parseModRMReg (rexB : Bool) (bs : List UInt8) : Option (UInt8 × Reg) :=
  match parseModRM false rexB bs with
  | some (reg, .reg r, _) => some (reg, r)
  | _ => none

/-- A ModRM operand that must be memory. -/
def parseModRMMem (rexX rexB : Bool) (bs : List UInt8) : Option (UInt8 × Mem) :=
  match parseModRM rexX rexB bs with
  | some (reg, .mem m, _) => some (reg, m)
  | _ => none

/-- Parses the instruction after the optional REX prefix `x`. -/
def parseBody (x : Rex) : List UInt8 → Option Instr
  | [] => none
  | op :: rest =>
    if op = 0x0F then
      match rest with
      | [] => none
      | op2 :: rest2 =>
        if op2 = 0x05 then some .syscall
        else if op2 = 0xAF then
          (parseModRMReg x.b rest2).map fun p => .imul (Reg.ofBits x.r p.1) p.2
        else if op2 = 0xB6 then
          match parseModRM x.x x.b rest2 with
          | some (reg, .reg s, _) => some (.movzx (Reg.ofBits x.r reg) s)
          | some (reg, .mem m, _) => some (.load8 (Reg.ofBits x.r reg) m)
          | none => none
        else if op2 >>> 4 = 8 then
          (Cond.ofCode op2).bind fun c => (get32 rest2).map fun p => .jcc c p.1
        else if op2 >>> 4 = 9 then
          (Cond.ofCode op2).bind fun c => (parseModRMReg x.b rest2).map fun p => .setcc c p.2
        else none
    else if op = 0x89 then
      match parseModRM x.x x.b rest with
      | some (reg, .reg d, _) => some (.movRR d (Reg.ofBits x.r reg))
      | some (reg, .mem m, _) => some (.store m (Reg.ofBits x.r reg))
      | none => none
    else if op = 0x88 then
      match parseModRM x.x x.b rest with
      | some (reg, .mem m, _) => some (.store8 m (Reg.ofBits x.r reg))
      | _ => none
    else if op = 0xC7 then
      match parseModRM x.x x.b rest with
      | some (0, .mem m, rest') => (get32 rest').map fun p => .storeI m p.1
      | _ => none
    else if op = 0xC6 then
      match parseModRM x.x x.b rest with
      | some (0, .mem m, b :: _) => some (.store8I m b)
      | _ => none
    else if op = 0x8B then
      (parseModRMMem x.x x.b rest).map fun p => .load (Reg.ofBits x.r p.1) p.2
    else if op = 0x8D then
      (parseModRMMem x.x x.b rest).map fun p => .lea (Reg.ofBits x.r p.1) p.2
    else if op = 0x81 then
      match parseModRM x.x x.b rest with
      | some (dg, .reg d, rest') =>
        (Alu.ofDigit dg).bind fun a => (get32 rest').map fun p => .aluRI a d p.1
      | _ => none
    else if op = 0xF7 then
      match parseModRMReg x.b rest with
      | some (6, s) => some (.div s)
      | _ => none
    else if op = 0xD3 then
      (parseModRMReg x.b rest).bind fun p => (Shift.ofDigit p.1).map fun sh => .shiftCL sh p.2
    else if op >>> 3 = 0x17 then
      (get64 rest).map fun p => .movRI (Reg.ofBits x.b op) p.1
    else if op >>> 3 = 0x0A then some (.push (Reg.ofBits x.b op))
    else if op >>> 3 = 0x0B then some (.pop (Reg.ofBits x.b op))
    else if op = 0xE9 then (get32 rest).map fun p => .jmp p.1
    else if op = 0xE8 then (get32 rest).map fun p => .call p.1
    else if op = 0xC3 then some .ret
    else
      (Alu.ofRR op).bind fun a =>
        (parseModRMReg x.b rest).map fun p => .aluRR a p.2 (Reg.ofBits x.r p.1)

/-- Parses an instruction leniently, ignoring the bits that the canonical form fixes. -/
def parse : List UInt8 → Option Instr
  | [] => none
  | b :: rest => if isRex b then parseBody (rexOf b) rest else parseBody Rex.none (b :: rest)

/-- The decoder, which returns the instruction at the start of `bs` and its length and accepts
only its canonical encoding. -/
def decode (bs : List UInt8) : Option (Instr × Nat) :=
  match parse bs with
  | some i => if bs.take (encode i).length = encode i then some (i, (encode i).length) else none
  | none => none

end Millipede.X64
