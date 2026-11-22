import Millipede.Target.X64.Isa

/-!
# Tests for the x64 ISA model

This suite checks by kernel evaluation that known instructions encode to the bytes given in the
Intel manual, checked by hand, and decode back. Byte sequences that are not canonical or not in
the modelled subset decode to `none`. Single instructions are executed on a small state to check
flags, faults, the stack instructions, branches and `syscall` through a trap.

The encoder is also checked independently. `listing` gives the bytes of several hundred
instructions together with the text the model expects, and `scripts/x64-encode-check.sh`
disassembles the bytes with GNU objdump and fails on any line whose text differs.
-/

namespace Millipede.X64.Tests

open Millipede Millipede.X64

/-! ## 1. Known encodings -/

example : encode (.movRR .rax .rbx) = [0x48, 0x89, 0xD8] := by decide
example : encode (.movRR .r8 .r15) = [0x4D, 0x89, 0xF8] := by decide
example : encode (.movRI .r9 0x1122334455667788) =
    [0x49, 0xB9, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11] := by decide
example : encode (.load .rax (.base .rbp 0xFFFFFFF8)) = [0x48, 0x8B, 0x85, 0xF8, 0xFF, 0xFF, 0xFF] := by
  decide
example : encode (.store (.base .rsp 16) .rax) = [0x48, 0x89, 0x84, 0x24, 0x10, 0, 0, 0] := by
  decide
example : encode (.store (.base .r12 0) .r13) = [0x4D, 0x89, 0xAC, 0x24, 0, 0, 0, 0] := by decide
example : encode (.lea .rsi (.rip 0x10)) = [0x48, 0x8D, 0x35, 0x10, 0, 0, 0] := by decide
example : encode (.aluRR .sub .rsp .rcx) = [0x48, 0x29, 0xCC] := by decide
example : encode (.aluRI .add .rsp 0x10) = [0x48, 0x81, 0xC4, 0x10, 0, 0, 0] := by decide
example : encode (.aluRI .cmp .r11 5) = [0x49, 0x81, 0xFB, 5, 0, 0, 0] := by decide
example : encode (.imul .r8 .rcx) = [0x4C, 0x0F, 0xAF, 0xC1] := by decide
example : encode (.div .r11) = [0x49, 0xF7, 0xF3] := by decide
example : encode (.shiftCL .shr .rax) = [0x48, 0xD3, 0xE8] := by decide
example : encode (.setcc .e .rax) = [0x0F, 0x94, 0xC0] := by decide
example : encode (.setcc .e .rsi) = [0x40, 0x0F, 0x94, 0xC6] := by decide
example : encode (.setcc .g .r12) = [0x41, 0x0F, 0x9F, 0xC4] := by decide
example : encode (.movzx .rax .rsi) = [0x48, 0x0F, 0xB6, 0xC6] := by decide
example : encode (.jcc .ne 0) = [0x0F, 0x85, 0, 0, 0, 0] := by decide
example : encode (.jmp 0xFFFFFFFB) = [0xE9, 0xFB, 0xFF, 0xFF, 0xFF] := by decide
example : encode (.call 0) = [0xE8, 0, 0, 0, 0] := by decide
example : encode .ret = [0xC3] := by decide
example : encode (.push .rbp) = [0x55] := by decide
example : encode (.push .r12) = [0x41, 0x54] := by decide
example : encode (.pop .r15) = [0x41, 0x5F] := by decide
example : encode .syscall = [0x0F, 0x05] := by decide
example : encode (.load8 .rax (.base .rbx 0)) = [0x48, 0x0F, 0xB6, 0x83, 0, 0, 0, 0] := by decide
example : encode (.store8 (.base .rbx 0) .rcx) = [0x88, 0x8B, 0, 0, 0, 0] := by decide
example : encode (.store8 (.base .rbx 0) .rsi) = [0x40, 0x88, 0xB3, 0, 0, 0, 0] := by decide
example : encode (.store8 (.base .r12 4) .rax) = [0x41, 0x88, 0x84, 0x24, 4, 0, 0, 0] := by decide
/-- `88 B3` is rejected, because without REX register 6 is `dh`, which is not modelled. -/
example : decode [0x88, 0xB3, 0, 0, 0, 0] = none := by decide
example : decode [0x40, 0x88, 0xB3, 0, 0, 0, 0] = some (.store8 (.base .rbx 0) .rsi, 7) := by
  decide

example : decode [0x48, 0x89, 0xD8, 0xC3] = some (.movRR .rax .rbx, 3) := by decide
example : decode [0x4D, 0x89, 0xAC, 0x24, 0, 0, 0, 0] = some (.store (.base .r12 0) .r13, 8) := by
  decide
example : decode [0x41, 0x54] = some (.push .r12, 2) := by decide
-- `[base + index + disp32]`: `REX.B` the base's and `REX.X` the index's high bit, scale 1
example : encode (.load .rax (.sib .r11 ⟨.rbx, nofun⟩ 8)) = [0x49, 0x8B, 0x84, 0x1B, 8, 0, 0, 0] := by
  decide
example : encode (.store8 (.sib .rax ⟨.r12, nofun⟩ 0) .rcx) = [0x42, 0x88, 0x8C, 0x20, 0, 0, 0, 0] := by
  decide
example : decode [0x42, 0x88, 0x8C, 0x20, 0, 0, 0, 0] = some (.store8 (.sib .rax ⟨.r12, nofun⟩ 0) .rcx, 8) := by
  decide
-- a SIB byte with scale 2 is not canonical
example : decode [0x49, 0x8B, 0x84, 0x5B, 8, 0, 0, 0] = none := by decide

/-! ## 2. Rejections -/

/-- `mov rax, rbx` in its `8B` form, which is not canonical. -/
example : decode [0x48, 0x8B, 0xC3] = none := by decide
/-- `add rax, 1` with an 8-bit immediate, the `83` form, which is not canonical. -/
example : decode [0x48, 0x83, 0xC0, 0x01] = none := by decide
/-- `mov rax, [rbp-8]` with an 8-bit displacement. -/
example : decode [0x48, 0x8B, 0x45, 0xF8] = none := by decide
/-- `[rsp+disp32]` with a SIB byte other than `24`. -/
example : decode [0x48, 0x89, 0x84, 0x20, 0x10, 0, 0, 0] = none := by decide
/-- `rex sete al`, with a superfluous REX prefix. -/
example : decode [0x40, 0x0F, 0x94, 0xC0] = none := by decide
/-- `push rax` with a superfluous REX prefix. -/
example : decode [0x40, 0x50] = none := by decide
/-- The 32-bit `mov eax, ebx`, without REX.W. -/
example : decode [0x89, 0xD8] = none := by decide
/-- `jp rel32`, since parity is not modelled. -/
example : decode [0x0F, 0x8A, 0, 0, 0, 0] = none := by decide
/-- `nop` and an operand-size prefix are not in the subset. -/
example : decode [0x90] = none := by decide
example : decode [0x66, 0x90] = none := by decide
/-- Truncated instructions. -/
example : decode [0xE9, 0, 0] = none := by decide
example : decode [0x48, 0xB8, 1, 2, 3] = none := by decide
example : decode [] = none := by decide
/-- `div` with `/7`, which is `idiv`. -/
example : decode [0x48, 0xF7, 0xF8] = none := by decide
/-- `lea` with a register operand. -/
example : decode [0x48, 0x8D, 0xC0] = none := by decide

/-! ## 3. Execution -/

/-- A test memory: page 1 (`0x1000`–`0x1FFF`) is read-write, page 2 is read-only and holds
`0x2A` at `0x2000`, everything else is unmapped. -/
def mem0 : Memory where
  pageBits := 12
  bytes a := if a = 0x2000 then 0x2A else 0
  perm p := if p = 1 then Perm.rw else if p = 2 then Perm.r_ else Perm.none

/-- Registers with `rax = 7`, `rbx = 5`, `rcx = 3`, `rsp = 0x1100` and the others 0,
`rip = 0x400000` and all flags clear. -/
def regs0 : Regs where
  gpr r := match r with
    | .rax => 7 | .rbx => 5 | .rcx => 3 | .rsp => 0x1100 | _ => 0
  rip := 0x400000
  flags := ⟨false, false, false, false⟩

def s0 : State := ⟨regs0, mem0, World.init⟩

/-- A trap that refuses every system call. -/
def noTrap : State → Option State := fun _ => none

/-- Runs one instruction with its encoded length and applies `f` to the resulting state. -/
def run1 {α : Type} (i : Instr) (f : State → α) (s : State := s0) (trap := noTrap) : Option α :=
  (exec trap i (encode i).length s).map f

def gpr (r : Reg) (s : State) : UInt64 := s.regs.gpr r
def flags (s : State) : Flags := s.regs.flags
def rip (s : State) : UInt64 := s.regs.rip

example : run1 (.aluRR .add .rax .rbx) (gpr .rax) = some 12 := by decide
example : run1 (.aluRR .sub .rbx .rax) (fun s => (gpr .rbx s, flags s)) =
    some (0xFFFFFFFFFFFFFFFE, ⟨true, false, true, false⟩) := by decide
example : run1 (.aluRR .cmp .rax .rax) (fun s => (gpr .rax s, flags s)) =
    some (7, ⟨false, true, false, false⟩) := by decide
/-- Signed overflow in `0x7FFF…F + 1`. -/
example : run1 (.aluRI .add .rax 1) flags
    (s := { s0 with regs := regs0.set .rax 0x7FFFFFFFFFFFFFFF }) =
    some ⟨false, false, true, true⟩ := by decide
/-- The immediate is sign-extended. -/
example : run1 (.aluRI .add .rax 0xFFFFFFFF) (gpr .rax) = some 6 := by decide
example : run1 (.aluRI .xor .rax 0xFFFFFFFF) (gpr .rax) = some (~~~(7 : UInt64)) := by decide
example : run1 (.imul .rax .rbx) (gpr .rax) = some 35 := by decide
example : run1 (.shiftCL .shl .rax) (gpr .rax) = some 56 := by decide
example : run1 (.shiftCL .shr .rax) (fun s => (gpr .rax s, (flags s).cf)) = some (0, true) := by
  decide
example : run1 (.movRI .r9 0xDEADBEEF) (gpr .r9) = some 0xDEADBEEF := by decide
example : run1 (.movRR .r9 .rbx) (gpr .r9) = some 5 := by decide
/-- `setcc` writes only the low byte, and `movzx` clears the rest. -/
example : run1 (.setcc .b .rax) (gpr .rax)
    (s := { s0 with regs := { regs0 with flags := ⟨true, false, false, false⟩ } }) = some 1 := by
  decide
example : run1 (.setcc .a .rbx) (gpr .rbx) (s := { s0 with regs := regs0.set .rbx 0x1FF }) =
    some 0x101 := by decide
example : run1 (.movzx .rax .rbx) (gpr .rax) (s := { s0 with regs := regs0.set .rbx 0x1FF }) =
    some 0xFF := by decide
/-- `div` with `rdx:rax = 7` and the divisor `rbx = 5`. -/
example : run1 (.div .rbx) (fun s => (gpr .rax s, gpr .rdx s)) = some (1, 2) := by decide
/-- Division by zero faults. -/
example : run1 (.div .rdx) (gpr .rax) = none := by decide
/-- A quotient that does not fit faults. -/
example : run1 (.div .rbx) (gpr .rax) (s := { s0 with regs := regs0.set .rdx 5 }) = none := by decide
/-- Loads from read-only memory work, and rip-relative addresses count from the next
instruction. -/
example : run1 (.load .rax (.base .rbx 0x1FFB)) (gpr .rax) = some 0x2A := by decide
example : run1 (.lea .rax (.rip 0x10)) (gpr .rax) = some (0x400000 + 7 + 0x10) := by decide
/-- Stores to read-only or unmapped memory fault, and so do non-canonical addresses. -/
example : run1 (.store (.base .rbx 0x1FFB) .rax) (gpr .rax) = none := by decide
example : run1 (.store (.base .rbx 0x2FFB) .rax) (gpr .rax) = none := by decide
example : run1 (.load .rax (.base .rbx 0)) (gpr .rax)
    (s := { s0 with regs := regs0.set .rbx 0x0000800000000000 }) = none := by decide
/-- Store then load. -/
example : ((exec noTrap (.store (.base .rsp 0xFFFFFFF8) .rbx) 8 s0).bind fun s =>
    run1 (.load .rcx (.base .rsp 0xFFFFFFF8)) (gpr .rcx) (s := s)) = some 5 := by decide
/-- `push` then `pop`. -/
example : ((exec noTrap (.push .rbx) 1 s0).bind fun s =>
    run1 (.pop .r12) (fun s => (gpr .r12 s, gpr .rsp s)) (s := s)) = some (5, 0x1100) := by decide
/-- `call` pushes the return address; `ret` returns to it. -/
example : ((exec noTrap (.call 0x100) 5 s0).bind fun s =>
    run1 .ret (fun s => (rip s, gpr .rsp s)) (s := s)) = some (0x400005, 0x1100) := by decide
example : run1 (.call 0x100) rip = some (0x400005 + 0x100) := by decide
/-- Branch targets are relative to the next instruction, and a negative offset goes backwards. -/
example : run1 (.jmp 0xFFFFFFFB) rip = some 0x400000 := by decide
example : run1 (.jcc .e 0x20) rip = some 0x400006 := by decide
example : run1 (.jcc .ne 0x20) rip = some 0x400026 := by decide
/-- A stack overflow, a push below the mapped page, faults. -/
example : run1 (.push .rax) rip (s := { s0 with regs := regs0.set .rsp 0x1000 }) = none := by
  decide
/-- `syscall` applies the trap, then sets `rcx` and `rip` to the next instruction's address and
`r11` to the image of the flags. -/
example : run1 .syscall (fun s => (gpr .rax s, gpr .rcx s, gpr .r11 s, rip s))
    (trap := fun s => some { s with regs := s.regs.set .rax 99 }) =
    some (99, 0x400002, 0x202, 0x400002) := by decide
example : run1 .syscall rip = none := by decide

/-- The machine step decodes from executable memory only, so the same bytes in a read-only page
do not run. -/
def codeMem (perm : Perm) : Memory where
  pageBits := 12
  bytes a := if a = 0x1000 then 0x48 else if a = 0x1001 then 0x89 else if a = 0x1002 then 0xD8
    else 0
  perm p := if p = 1 then perm else Perm.none

example : (isa.step noTrap ⟨{ regs0 with rip := 0x1000 }, codeMem Perm.rx, World.init⟩).map
    (fun s => (s.regs.gpr .rax, s.regs.rip)) = some (5, 0x1003) := by decide
example : (isa.step noTrap ⟨{ regs0 with rip := 0x1000 }, codeMem Perm.r_, World.init⟩).map
    (fun s => s.regs.rip) = none := by decide

/-! ## 4. Listing for the objdump cross-check -/

/-- Lower-case hexadecimal with the prefix `0x`. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A byte as two hexadecimal digits. -/
def hexByte (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length = 1 then "0" ++ s else s

/-- A memory operand as objdump prints it, plus the `# target` comment for rip-relative ones. -/
def memText (next : UInt64) : Mem → String × String
  | .base b d =>
    let v := (sext32 d).toBitVec.toInt
    (s!"[{b.name}" ++ (if v < 0 then "-" ++ hex v.natAbs else "+" ++ hex v.toNat) ++ "]", "")
  | .rip d => (s!"[rip+{hex (sext32 d).toNat}]", s!" # {hex (next + sext32 d).toNat}")
  | .sib b i d =>
    let v := (sext32 d).toBitVec.toInt
    (s!"[{b.name}+{i.1.name}*1" ++ (if v < 0 then "-" ++ hex v.natAbs else "+" ++ hex v.toNat) ++ "]",
      "")

/-- Intel-syntax text of `i` as objdump prints it, `next` being the next instruction's
address. -/
def text (next : UInt64) : Instr → String
  | .movRR d s => s!"mov {d.name},{s.name}"
  | .movRI d imm => s!"movabs {d.name},{hex imm.toNat}"
  | .load d m => let (t, c) := memText next m; s!"mov {d.name},QWORD PTR {t}{c}"
  | .store m s => let (t, c) := memText next m; s!"mov QWORD PTR {t},{s.name}{c}"
  | .load8 d m => let (t, c) := memText next m; s!"movzx {d.name},BYTE PTR {t}{c}"
  | .store8 m s => let (t, c) := memText next m; s!"mov BYTE PTR {t},{s.name8}{c}"
  | .storeI m imm => let (t, c) := memText next m; s!"mov QWORD PTR {t},{hex (sext32 imm).toNat}{c}"
  | .store8I m imm => let (t, c) := memText next m; s!"mov BYTE PTR {t},{hex imm.toNat}{c}"
  | .lea d m => let (t, c) := memText next m; s!"lea {d.name},{t}{c}"
  | .aluRR op d s => s!"{op.name} {d.name},{s.name}"
  | .aluRI op d imm => s!"{op.name} {d.name},{hex (sext32 imm).toNat}"
  | .imul d s => s!"imul {d.name},{s.name}"
  | .div s => s!"div {s.name}"
  | .shiftCL .shl d => s!"shl {d.name},cl"
  | .shiftCL .shr d => s!"shr {d.name},cl"
  | .setcc c d => s!"set{c.name} {d.name8}"
  | .movzx d s => s!"movzx {d.name},{s.name8}"
  | .jcc c rel => s!"j{c.name} {hex (next + sext32 rel).toNat}"
  | .jmp rel => s!"jmp {hex (next + sext32 rel).toNat}"
  | .call rel => s!"call {hex (next + sext32 rel).toNat}"
  | .ret => "ret"
  | .push r => s!"push {r.name}"
  | .pop r => s!"pop {r.name}"
  | .syscall => "syscall"

/-- The displacements and 32-bit immediates exercised: small values, values at the sign
boundary and negative values. -/
def imm32s : List UInt32 := [0, 8, 0x7F, 0x80, 0xFFFFFFF8, 0x7FFFFFFF, 0x80000000, 0x12345678]

/-- The index registers, every register but `rsp`. -/
def idxs : List Idx := Reg.all.filterMap fun r => if h : r = .rsp then none else some ⟨r, h⟩

/-- The instructions cross-checked against objdump. -/
def sample : List Instr :=
  (Reg.all.flatMap fun d => Reg.all.map fun s => .movRR d s) ++
  (Reg.all.map fun d => .movRI d 0x1122334455667788) ++
  [.movRI .rax 0, .movRI .rcx 0xFFFFFFFFFFFFFFFF] ++
  (Reg.all.flatMap fun b => [Instr.load .rax (.base b 0x10), .store (.base b 0xFFFFFFF8) .r9,
    .load b (.base .rsp 8), .store (.base .rbp 0) b, .lea b (.base b 0x80000000)]) ++
  (imm32s.flatMap fun d => [Instr.load .r13 (.rip d), .store (.rip d) .rdx, .lea .rdi (.rip d),
    .load .rcx (.base .r12 d)]) ++
  (Reg.all.flatMap fun b => Reg.all.flatMap fun r =>
    [Instr.load8 r (.base b 0x10), .store8 (.base b 0xFFFFFFF8) r]) ++
  (imm32s.flatMap fun d => [Instr.load8 .r9 (.rip d), .store8 (.rip d) .rsi]) ++
  (Reg.all.flatMap fun b => idxs.flatMap fun i =>
    [Instr.load (Reg.all.getD ((b.num + i.1.num) % 16) .rax) (.sib b i 0x10),
      .store8 (.sib b i 0xFFFFFFF8) (Reg.all.getD ((b.num + 3 * i.1.num) % 16) .rax)]) ++
  (imm32s.flatMap fun v => [Instr.storeI (.base .rax 8) v, .storeI (.base .r12 0xFFFFFFF8) v,
    .storeI (.sib .r11 ⟨.r9, nofun⟩ 16) v, .storeI (.rip 0x100) v,
    .store8I (.base .r13 4) v.toUInt8, .store8I (.sib .rbx ⟨.r12, nofun⟩ 0) v.toUInt8,
    .store8I (.base .rsp 4) v.toUInt8, .store8I (.rip 0x10) v.toUInt8]) ++
  (idxs.flatMap fun i => imm32s.flatMap fun d => [Instr.store (.sib .r11 i d) .rcx,
    .load8 .rdx (.sib .r11 i d), .lea .rsi (.sib .rbp i d)]) ++
  (Alu.all.flatMap fun op => Reg.all.flatMap fun d =>
    [Instr.aluRR op d (Reg.all.getD ((d.num + 5) % 16) .rax)]) ++
  (Alu.all.flatMap fun op => imm32s.map fun imm => Instr.aluRI op .r10 imm) ++
  (Alu.all.flatMap fun op => Reg.all.map fun d => Instr.aluRI op d 0x10) ++
  (Reg.all.flatMap fun d => [Instr.imul d (Reg.all.getD ((d.num + 3) % 16) .rax), .div d,
    .shiftCL .shl d, .shiftCL .shr d, .movzx d (Reg.all.getD ((d.num + 7) % 16) .rax),
    .push d, .pop d]) ++
  (Cond.all.flatMap fun c => Reg.all.map fun d => Instr.setcc c d) ++
  (Cond.all.flatMap fun c => [Instr.jcc c 0, .jcc c 0xFFFFFF00, .jcc c 0x1000]) ++
  [.jmp 0, .jmp 0xFFFFFFFB, .jmp 0x7FFFFFFF, .call 0, .call 0xFFFFF000, .ret, .syscall]

/-- The bytes in hexadecimal and the text of each instruction of `sample`, laid out one after
another from address 0. -/
def listing : List (String × String) :=
  (sample.foldl (fun (acc : List (String × String) × UInt64) i =>
    let bs := encode i
    let next := acc.2 + UInt64.ofNat bs.length
    ((String.intercalate " " (bs.map hexByte), text next i) :: acc.1, next)) ([], 0)).1.reverse

/-- Prints the listing, one instruction per line as `hex bytes<TAB>text`. -/
def printListing : IO Unit :=
  for (h, t) in listing do IO.println s!"{h}\t{t}"

end Millipede.X64.Tests
