import Millipede.Compile.Asm
import Millipede.RegAlloc.Live
import Millipede.Compile.Lin
import Millipede.Target.X64.Isa
import Millipede.Target.SelDriver
import Millipede.Target.CallArgs

/-!
# Instruction selection for x64

`select k c` translates a Lin program into an x64 Asm program with `k ≤ 6` preserved and
`c ≤ 3` caller-saved register locations. After register allocation, location `x < k` of every
frame is the register `preg x`, one of `rbx rbp r12 r13 r14 r15`, location `k + i` for `i < c` is
`r8`, `r9` or `r10` (`loc`), and every other location is its frame slot, so `k = c = 0` keeps
every location on the stack. A call destroys the caller-saved registers, so `select` refuses a
program in which a caller-saved location is live after a call that does not define it. Each Lin instruction becomes a fixed block of instructions. An operand in
a register location is used in place and any other operand is loaded into a scratch register,
while a result for a register location is computed into its register and any other result is
stored to its slot.

## The symbolic layer

An `SI` is an x64 instruction or one that names a reference, which is a `jmp`, `jcc` or `call`
with a rel32 field, or a `lea d, [rip + ref]` with a disp32 field. Every code and data reference
is relative to the instruction pointer, so the generated code is position-independent.
`rel32 target next` is the signed 32-bit distance, or `none` when the target is out of reach, in
which case the assembler refuses the program.

## The internal calling convention

A function with a Lin frame of `F` words starts with `sub rsp, 8F`, after which slot `x` is the
word at `[rsp + 8x]`. The return address is just above the frame at `[rsp + 8F]`, and the
caller's frame is above that.

To call `g` with a frame of `G` words, the caller first saves its registers `preg x` for
`x < min k G` into `g`'s frame words `x`, which `g` does not use because those locations are its
registers. It then writes the other words of the callee frame, the argument words followed by
zeros, at `[rsp - 8 - 8G + 8j]`, which is where `g`'s slot `j` will be once `call` has pushed
the return address and `g` has run `sub rsp, 8G`. Then it loads the register arguments directly
into `preg j`, reading an argument whose register was already overwritten back from its save
word. The arguments for `g`'s caller-saved locations come last: those held in caller-saved
registers by a parallel move through `rax` (`cSeq`, `Sel.PMove.seq`), the others after it. Then
it runs `call g`. Of `g`'s locations it writes only those live at `g`'s entry; the
others `g` writes before it reads them.

`ret` loads the returned words into `rax rcx rdx rsi rdi r8 r9 r10`, at most 8 of them and
at most 5 with caller-saved locations, so that no return register is a location's, restores
`preg x` for `x < min k F` from its frame words, and runs `add rsp, 8F; ret`. Back in the caller,
the block copies or stores the returned words into their locations. So the location registers
are saved through the callee's frame words, and frames do not grow. Selected code writes
`rbx rbp r12 … r15` only as locations, while `syscall` overwrites `rax`, `rcx` and `r11`, division
uses `rax` and `rdx`, and shifts read `cl`, none of which is a location's register. Nothing but
a call writes `r8 r9 r10` while they are locations.

## Primitives

`binR d n m` computes `n op m` into `d`. The operations `add sub and or xor mul` use the
two-operand forms `op d, m`, preceded by `mov d, n` unless `d` is `n`. For a commuting operation
with `d = m` the form is `op d, n`, and `sub` with `d = m` goes through `rax`. A shift moves `m`
into `rcx` and shifts `d` by `cl`, which x64 masks to 6 bits as Lin takes the count modulo 64. A
comparison is `cmp n, m`, `setCC d8` and `movzx d, d8`.

x64's `div` faults on a zero divisor, so division is guarded without branches on `rax` and `rcx`.
For `x / y` the code computes `y' := y ||| (y = 0)` and `x' := x * (y ≠ 0)` and divides `x'` by
`y'`, so that `x / 0 = 0`. For `x % y` it computes `q := x / y'` and the result `x - q * y`, so
that `x % 0 = x`. `rdx` is cleared before `div`, so the quotient always fits.

## Externs

The externs are Linux system calls. `exit(code)` is `rdi := code; rax := 60; syscall`. For
`write(fd, bytes)` the constant bytes become a read-only data item, and the code is
`rdi := fd; lea rsi, [rip + item]; rdx := length; rax := 1; syscall`. The result in `rax` goes to
the destination location. `read(fd, buf, 1)` uses the destination slot as its one-byte buffer
and refuses a register location: it clears the slot, calls `read` with `rax := 0` and `rsi`
pointing at the slot, and computes the call's value without branches, which is the byte read
when the result is 1 and `2^64 - 1` otherwise. `write` from a buffer in the data region and
`read` into one pass `rsi := &mp_mem + p` and the length. Other externs are refused.

`X64.linux` is the matching ABI model, with the number in `rax`, the arguments in `rdi rsi rdx`
and the result in `rax`. It produces exactly the `Call` records that Lin and the source produce.

## Memory

A Lin program's data region of `M` bytes becomes a zero-initialised writable region `mp_mem` of
`M` bytes, and Lin address `x` is machine address `mp_mem + x`. With the option `mb`
(`Options.memBase`) and `off < 2^31`, a `load w x a off` puts `&mp_mem` into `r11` by
`lea r11, [rip + mp_mem]` (after `rax := a` when `a` is in no register) and runs
`mov d, [r11 + a + off]` or `movzx d, byte [r11 + a + off]` into the result's register (`memX`,
`memM`), a SIB operand with `a`'s register as the index.
Otherwise it computes `rax := a + off + &mp_mem` with the operand, `movabs rcx, off`, `add`,
`lea rcx, [rip + mp_mem]` and `add`, and accesses `[rax]` (`memAddrR`). A `store w a off b`
computes the same address and stores `b` or its low byte from its register. `r11` is written by
no other block between instructions; it is the temporary of parallel moves inside a block and
`syscall` destroys it.

## Refusals

`select` refuses with an error a Lin `load` or `store` without a data region, an unknown extern,
a frame of `2^24` words or more, more than 8 returned words, a constant buffer of `2^32` bytes or
more, a call to a missing function, a call with more arguments than the callee's frame, `k > 6`,
`c > 3`, more than 5 returned words with `c > 0`, a caller-saved location live across a call, and
a one-byte `read` into a register location. On a refusal `selectFb` selects again with `(k, 0)` and
then with slot locations only (`kcUsed`).

## Resource hooks

`X64.φ` charges an activation with `w` slots `8(w + 1)` bytes, its frame and return address.
`X64.κ` is the x64 cost model, and `compile` checks that the selected code fits it.

See doc/design/compiler.md.
-/

namespace Millipede.X64

open Flat (Operand BinOp ExtArg)

/-- x64 instructions with symbolic references. -/
inductive SI where
  /-- A plain instruction. -/
  | op (i : Instr)
  /-- `jmp rel32` to a reference. -/
  | jmp (r : Asm.Ref)
  /-- `jCC rel32` to a reference. -/
  | jcc (c : Cond) (r : Asm.Ref)
  /-- `call rel32` to a reference. -/
  | call (r : Asm.Ref)
  /-- `lea d, [rip + disp32]` of a reference. -/
  | lea (d : Reg) (r : Asm.Ref)
deriving DecidableEq, Repr, Inhabited

/-- The signed 32-bit displacement from `next` to `target`, if it is in reach. -/
def rel32 (target next : UInt64) : Option UInt32 :=
  let v : Int := (target.toNat : Int) - (next.toNat : Int)
  if -2147483648 ≤ v ∧ v < 2147483648 then some (UInt32.ofInt v) else none

/-- The encoded size of a symbolic instruction, which is fixed because rel32 and disp32 fields
have a fixed width. -/
def SI.size : SI → Nat
  | .op i => (encode i).length
  | .jmp _ => 5
  | .jcc _ _ => 6
  | .call _ => 5
  | .lea d _ => (encode (.lea d (.rip 0))).length

/-- Resolves a symbolic instruction placed at `a`. -/
def SI.resolve (ρ : Asm.Ref → Option UInt64) (a : UInt64) : SI → Option Instr
  | .op i => some i
  | .jmp r => (ρ r).bind fun t => (rel32 t (a + 5)).map .jmp
  | .jcc c r => (ρ r).bind fun t => (rel32 t (a + 6)).map (.jcc c)
  | .call r => (ρ r).bind fun t => (rel32 t (a + 5)).map .call
  | .lea d r => (ρ r).bind fun t =>
      (rel32 t (a + UInt64.ofNat (encode (.lea d (.rip 0))).length)).map fun x => .lea d (.rip x)

/-- The x64 symbolic layer. -/
abbrev arch : Asm.Arch where
  isa := isa
  SInstr := SI
  size := SI.size
  resolve := SI.resolve

/-! ## The Linux system-call ABI -/

/-- The Linux x64 process and system-call model. Pages are 4 KiB, the stack is below
`2^47 - 2^12`, and the numbers are 60 for `exit`, 1 for `write` and 0 for `read`, with the number
in `rax`, the arguments in `rdi rsi rdx` and the result in `rax`. `read` writes the bytes the
oracle supplies, at most `rdx` of them, from `rsi` on. At entry every register but `rsp` is 0. -/
def linux : Abi isa where
  pageBits := 12
  stackTop := 0x7ffffffff000
  stackAlign := 16
  entryRegs entry sp := ⟨fun r => if r = .rsp then sp else 0, entry, ⟨false, false, false, false⟩⟩
  sysCall s :=
    let r : Regs := s.regs
    if r.gpr .rax = 60 then some (⟨"exit", [r.gpr .rdi], [], []⟩, true)
    else if r.gpr .rax = 1 then
      (s.mem.read (r.gpr .rsi) (r.gpr .rdx).toNat).map fun bs =>
        (⟨"write", [r.gpr .rdi], [bs], []⟩, false)
    else if r.gpr .rax = 0 then some (⟨"read", [r.gpr .rdi], [], [(r.gpr .rdx).toNat]⟩, false)
    else none
  sysOut s := if s.regs.gpr .rax = 0 then [s.regs.gpr .rsi] else []
  sysRet v r := r.set .rax v

/-! ## Resource hooks -/

/-- The x64 frame model charges `w` slots plus the return address, 8 bytes each. -/
def φ : FrameModel := ⟨fun w => 8 * (w + 1), fun h => by omega⟩

/-- The x64 cost model, which charges machine instructions per Core construct. `compile` checks
that the selected program is covered, with a potential carrying credit from one construct to the
next within a reactor step, and refuses it otherwise. Each weight is the most instructions the
selected code of its construct takes, in any register-allocation setting `compile` offers
(allocation off is the dearest: every Lin slot is a frame word and every Lin load or store of the
data region is 7 instructions, the address being offset, add, `lea` of the region, add). The
counts come from the selectors and from scripts/kappa.lean's programs (doc/phases/kappa-install.md);
the weights fitted from those programs carry a margin of 10%, rounded up.

* `word` 32: one iteration of the loop that fills or copies a value of 64 bytes or more, 8 bytes
  per iteration (element address 4, load 7, store 7, counter step 4, back jump 1, test 6,
  branch 3). A straight copy of a word, a load and a store, takes at most 14.
* `iter` 64: a loop's per-iteration code with its counter and condition flag in memory: counter
  step 18, back jump 1, counter test 13 and its branch 3, the counter's copy into its variable 14,
  the flag's load 7 and its branches 8.
* `loop` 16: entering a loop, its accumulator and counter set-up and the first test (14).
* `prim` 36: a primitive whose two operands are read through references, two loads each, and its
  operation (32). `div` 46: the same with the remainder's sequence, which guards against a zero
  divisor, 10 instructions where an addition takes 1 (41), so that `div` is never below `prim`.
* `mem` 28 and `place` 5: a read, assignment, `put`, `take` or guard (25), plus 4 for each place
  selector.
* `ref` 40: a borrow or one reference argument, the place's address and its store (36). It is
  independent of the size of the referenced value.
* `call` 15: a call's sequence beyond its words and references (13). `ext` 18: an extern call's
  argument loads, system call and result store (16).
* `ite` 11: the condition's load and branch and the arm's join jump (10). `ctor` 14: the tag and
  payload stores of a constructor that leaves a loop early (12). `atom` 5 (4). `let_` 4: the
  reactor loop's test when a step begins with a `let` (3). `match_` 0: its tag test and branch
  are paid by the word charge of the scrutinee it copies. -/
def κ : CostModel where
  atom := 5
  let_ := 4
  ite := 11
  prim := 36
  div := 46
  loop := 16
  iter := 64
  call := 15
  ctor := 14
  match_ := 0
  ext := 18
  word := 32
  place := 5
  mem := 28
  ref := 40

/-! ## Selection -/

/- The symbols `mp_f<i>`, `mp_d<i>_<pc>` and `mp_mem` are shared with arm64. -/
export Sel (fnSym dataSym memSym padArgs isC cArgs)
/-- The memory operand of frame slot `x`: `[rsp + 8x]`. -/
def slotMem (x : Nat) : Mem := .base .rsp (UInt32.ofNat (8 * x))

/-- Plain instructions as symbolic ones. -/
def ops (is : List Instr) : List SI := is.map .op

/-- The largest number of register locations, one for each of `rbx rbp r12 r13 r14 r15`. -/
def maxK : Nat := 6

/-- The register of register location `x < maxK`. -/
def preg : Nat → Reg
  | 0 => .rbx
  | 1 => .rbp
  | 2 => .r12
  | 3 => .r13
  | 4 => .r14
  | _ => .r15

/-- The largest number of caller-saved register locations, one for each of `r8 r9 r10 rdi rsi
rdx`. -/
def maxC : Nat := 6

/-- The register of caller-saved location `k + i`, for `i < maxC`: `r8`, `r9`, `r10`, then the
registers with a fixed role at some instructions, `rdi`, `rsi` and `rdx` (system-call arguments,
division and remainder, returned words 4, 3 and 2). -/
def creg : Nat → Reg
  | 0 => .r8
  | 1 => .r9
  | 2 => .r10
  | 3 => .rdi
  | 4 => .rsi
  | _ => .rdx

/-- The register of location `x < k + c`: `preg x` below `k`, a caller-saved register above. -/
def loc (k x : Nat) : Reg := if x < k then preg x else creg (x - k)

/-- The instruction loading a slot or an immediate operand into `r`, where slot `y` is the frame
word `y - c`. -/
def ldI (c : Nat) (r : Reg) : Operand → Instr
  | .slot y => .load r (slotMem (y - c))
  | .imm w => .movRI r w

/-- Puts an operand in some register, and returns the code and the register. A register
location is used in place, and any other operand is loaded into `r`. -/
def src (k c : Nat) (r : Reg) : Operand → List Instr × Reg
  | .slot y => if y < k + c then ([], loc k y) else ([ldI c r (.slot y)], r)
  | o => ([ldI c r o], r)

/-- Puts an operand into register `r`. A register location is copied, with no code when its
register is `r`. -/
def ldTo (k c : Nat) (r : Reg) : Operand → List Instr
  | .slot y =>
    if y < k + c then (if loc k y = r then [] else [.movRR r (loc k y)]) else [ldI c r (.slot y)]
  | o => [ldI c r o]

/-- Puts register `r` into location `x`, by a copy into its register or a store into its
slot. -/
def stTo (k c x : Nat) (r : Reg) : List Instr :=
  if x < k + c then (if loc k x = r then [] else [.movRR (loc k x) r])
  else [.store (slotMem (x - c)) r]

/-- The register a result for location `x` is computed in, which is `rax` for a slot. -/
def dreg (k c x : Nat) : Reg := if x < k + c then loc k x else .rax

/-- The code after computing into `dreg k x`, which is nothing for a register location and the
store of `r` into slot `x` otherwise. -/
def fin (k c x : Nat) (r : Reg) : List Instr :=
  if x < k + c then [] else [.store (slotMem (x - c)) r]

/-- The code of a binary Lin operation with the first operand in `rax` and the second in `rcx`,
and the register that holds the result. -/
def binCode : BinOp → List Instr × Reg
  | .add => ([.aluRR .add .rax .rcx], .rax)
  | .sub => ([.aluRR .sub .rax .rcx], .rax)
  | .mul => ([.imul .rax .rcx], .rax)
  | .band => ([.aluRR .and .rax .rcx], .rax)
  | .bor => ([.aluRR .or .rax .rcx], .rax)
  | .bxor => ([.aluRR .xor .rax .rcx], .rax)
  | .shl => ([.shiftCL .shl .rax], .rax)
  | .shr => ([.shiftCL .shr .rax], .rax)
  | .eq => ([.aluRR .cmp .rax .rcx, .setcc .e .rax, .movzx .rax .rax], .rax)
  | .ne => ([.aluRR .cmp .rax .rcx, .setcc .ne .rax, .movzx .rax .rax], .rax)
  | .ult => ([.aluRR .cmp .rax .rcx, .setcc .b .rax, .movzx .rax .rax], .rax)
  | .ule => ([.aluRR .cmp .rax .rcx, .setcc .be .rax, .movzx .rax .rax], .rax)
  | .udiv => ([.aluRI .cmp .rcx 0, .setcc .e .rdx, .movzx .rdx .rdx, .aluRR .or .rcx .rdx,
      .aluRI .xor .rdx 1, .imul .rax .rdx, .aluRR .xor .rdx .rdx, .div .rcx], .rax)
  | .umod => ([.movRR .rsi .rax, .movRR .rdi .rcx, .aluRI .cmp .rcx 0, .setcc .e .rdx,
      .movzx .rdx .rdx, .aluRR .or .rcx .rdx, .aluRR .xor .rdx .rdx, .div .rcx,
      .imul .rax .rdi, .aluRR .sub .rsi .rax], .rsi)

/-- `d := n op m` with a two-operand form `f d s`, which computes `d := d op s`, where `comm`
says that `op` commutes. It is one instruction when `d` is `n`, or `m` for a commuting `op`, and
otherwise copies `n` into `d` first, going through `rax` when `d` is `m`. -/
def alu2 (comm : Bool) (f : Reg → Reg → Instr) (d n m : Reg) : List Instr :=
  if d = n then [f d m]
  else if d = m then (if comm then [f d n] else [.movRR .rax n, f .rax m, .movRR d .rax])
  else [.movRR d n, f d m]

/-- `d := n shift m`, which moves the count into `rcx`, since x64 shifts by `cl`, and then
shifts `d`. -/
def shiftR (op : Shift) (d n m : Reg) : List Instr :=
  (if m = .rcx then [] else [.movRR .rcx m]) ++
    (if d = .rcx then [.movRR .rax n, .shiftCL op .rax, .movRR .rcx .rax]
     else (if d = n then [] else [.movRR d n]) ++ [.shiftCL op d])

/-- Sets `d` to 1 when `n c m` holds and to 0 otherwise, by `cmp`, `setcc` and `movzx`. -/
def cmpR (c : Cond) (d n m : Reg) : List Instr := [.aluRR .cmp n m, .setcc c d, .movzx d d]

/-- Division and remainder move the operands into `rax` and `rcx`, run `binCode` and copy the
result into `d`, except that it stays in `binCode`'s register when `d` is `rax`. -/
def divR (op : BinOp) (d n m : Reg) : List Instr :=
  (if n = .rax then [] else [.movRR .rax n]) ++ (if m = .rcx then [] else [.movRR .rcx m]) ++
    (binCode op).1 ++ (if d = .rax then [] else [.movRR d (binCode op).2])

/-- A binary operation on registers, which puts `n op m` into `binRes op d`. That register is
`d`, except `rsi` for a remainder into `rax`. It needs `n ≠ rcx` and `m ≠ rax`, because the
operands of shifts and divisions are moved into `rax` and `rcx`. -/
def binR (d n m : Reg) : BinOp → List Instr
  | .add => alu2 true (.aluRR .add) d n m
  | .sub => alu2 false (.aluRR .sub) d n m
  | .mul => alu2 true .imul d n m
  | .band => alu2 true (.aluRR .and) d n m
  | .bor => alu2 true (.aluRR .or) d n m
  | .bxor => alu2 true (.aluRR .xor) d n m
  | .shl => shiftR .shl d n m
  | .shr => shiftR .shr d n m
  | .eq => cmpR .e d n m
  | .ne => cmpR .ne d n m
  | .ult => cmpR .b d n m
  | .ule => cmpR .be d n m
  | .udiv => divR .udiv d n m
  | .umod => divR .umod d n m

/-- The register `binR d n m op` leaves its result in. -/
def binRes (op : BinOp) (d : Reg) : Reg := if d = .rax then (binCode op).2 else d

/-- A load of width `w` from `m` into `d`, zero-extended for `w8`. -/
def ldWR : Flat.Width → Reg → Mem → Instr
  | .w8, d, m => .load8 d m
  | .w64, d, m => .load d m

/-- A store of width `w` of `r` to `m`, of its low byte for `w8`. -/
def stWR : Flat.Width → Reg → Mem → Instr
  | .w8, r, m => .store8 m r
  | .w64, r, m => .store m r

/-- Whether `v` is the sign extension of its low 32 bits, so that an instruction's 32-bit
immediate can stand for it. -/
def fitsI32 (v : UInt64) : Bool := sext32 v.toUInt32 == v

/-- `d := n op imm`: `mov d, n` unless `d` is `n`, then `op d, imm32`. -/
def aluI (op : Alu) (d n : Reg) (i : UInt32) : List Instr :=
  (if d = n then [] else [.movRR d n]) ++ [.aluRI op d i]

/-- `d := (n c imm)`: `cmp n, imm32`, `setcc`, `movzx`. -/
def cmpI (c : Cond) (d n : Reg) (i : UInt32) : List Instr := [.aluRI .cmp n i, .setcc c d, .movzx d d]

/-- The immediate form of `d := n op w`, with the option `mb`, for `w` a sign-extended 32-bit
value: `add sub and or xor` by `op d, imm32` after `mov d, n` unless `d` is `n`; a comparison by
`cmp n, imm32`, `setcc` and `movzx`; a multiplication by 1 is a copy. -/
def binImm (mb : Bool) (op : BinOp) (d n : Reg) (w : UInt64) : Option (List Instr) :=
  if mb && fitsI32 w then
    match op with
    | .add => some (aluI .add d n w.toUInt32)
    | .sub => some (aluI .sub d n w.toUInt32)
    | .band => some (aluI .and d n w.toUInt32)
    | .bor => some (aluI .or d n w.toUInt32)
    | .bxor => some (aluI .xor d n w.toUInt32)
    | .eq => some (cmpI .e d n w.toUInt32)
    | .ne => some (cmpI .ne d n w.toUInt32)
    | .ult => some (cmpI .b d n w.toUInt32)
    | .ule => some (cmpI .be d n w.toUInt32)
    | .mul => if w = 1 then some [.movRR d n] else none
    | _ => none
  else none

/-- The code of `d := n op b` with `n` in a register: the immediate form, else `b` in a register
and `binR`. -/
def binCodeB (k c : Nat) (mb : Bool) (op : BinOp) (d n : Reg) (b : Operand) : List Instr :=
  let reg := (src k c .rcx b).1 ++ binR d n (src k c .rcx b).2 op
  match b with
  | .imm w => (binImm mb op d n w).getD reg
  | _ => reg

/-- Puts the machine address of the Lin address `a + off` into `rax` by `rax := a; rcx := off;
rax += rcx; rcx := &mp_mem; rax += rcx`. Every step wraps, as Lin's address arithmetic does. -/
def memAddrR (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) : List SI :=
  ops ((src k c .rax a).1 ++ binCodeB k c mb .add .rax (src k c .rax a).2 (.imm off)) ++
    [.lea .rcx (.sym memSym), .op (.aluRR .add .rax .rcx)]

/-- Whether a `load` or `store` of `a + off` uses the displacement form: with the option `mb` on
and `off` below `2^31`, so that it is its own sign extension as a 32-bit displacement. -/
def disp (mb : Bool) (off : UInt64) : Bool := mb && decide (off.toNat < 2 ^ 31)

/-- The address code of a `load` or `store` of `a + off`. With the displacement form it puts
`&mp_mem` into `r11` by `rax := a` (nothing for a register location) and `lea r11, [rip +
mp_mem]`, and the access is `[r11 + a + off]` (`memM`); otherwise it is `memAddrR`, and the
access is `[rax]`. -/
def memX (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) : List SI :=
  if disp mb off then ops (src k c .rax a).1 ++ [.lea .r11 (.sym memSym)]
  else memAddrR k c mb a off

/-- The register that holds the Lin address `a` of a data access after `memX`: `a`'s register,
or `rax`. -/
def ixR (k c : Nat) (a : Operand) : Reg := (src k c .rax a).2

theorem ixR_ne_rsp (k c : Nat) (a : Operand) : ixR k c a ≠ .rsp := by
  cases a with
  | imm => simp [ixR, src]
  | slot y =>
    simp only [ixR, src]; split
    · unfold loc preg creg; split <;> split <;> decide
    · exact nofun

/-- The memory operand of a `load` or `store` of `a + off` after `memX`: `[r11 + a + off]` with
the displacement form, else `[rax]`. -/
def memM (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) : Mem :=
  if disp mb off then .sib .r11 ⟨ixR k c a, ixR_ne_rsp k c a⟩ (UInt32.ofNat off.toNat)
  else .base .rax 0

/-- The immediate form of a store of `v` of width `w` to `a + off` after `memX`, with the option
`mb` and the displacement form: `mov qword [m], imm32` when `v` is a sign-extended 32-bit value,
`mov byte [m], imm8` for a byte. -/
def stImm (k c : Nat) (mb : Bool) (w : Flat.Width) (v : UInt64) (a : Operand) (off : UInt64) :
    Option (List Instr) :=
  if disp mb off then
    match w with
    | .w8 => some [.store8I (memM k c mb a off) v.toUInt8]
    | .w64 => if fitsI32 v then some [.storeI (memM k c mb a off) v.toUInt32] else none
  else none

/-- The code of a store of `b` after `memX`: the immediate form, else `b` in a register and a
store of it. -/
def storeCode (k c : Nat) (mb : Bool) (w : Flat.Width) (a : Operand) (off : UInt64) (b : Operand) :
    List Instr :=
  let reg := (src k c .rcx b).1 ++ [stWR w (src k c .rcx b).2 (memM k c mb a off)]
  match b with
  | .imm v => (stImm k c mb w v a off).getD reg
  | _ => reg

/-- The registers that carry returned words, in order. There are 8 of them, and they leave
`rbx rbp r12 … r15` free for register locations. -/
def retRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10]

/-- The register of returned word `i`. -/
def retReg (i : Nat) : Reg := retRegs.getD i .rax

/-- `[rsp - n]`. -/
def belowMem (n : Nat) : Mem := .base .rsp (0 - UInt32.ofNat n)

/-- Word `x` of the frame of a callee of `G` slots, addressed before the call as
`[rsp - 8 - 8G + 8x]`, because `call` pushes the return address and the callee's entry moves
`rsp` down `G` words. -/
def calleeMem (G x : Nat) : Mem := belowMem (8 * (G - x) + 8)

/-- Saves the `n` caller location registers from `x` on that `keep` names into the words from
`x` on of the callee frame of `G` slots. -/
def saves (G : Nat) (keep : Nat → Bool) : Nat → Nat → List Instr
  | _, 0 => []
  | x, n + 1 => (if keep x then [.store (calleeMem G x) (preg x)] else []) ++ saves G keep (x + 1) n

/-- Stores operand `o` into the callee frame word `j`, a slot of the callee. -/
def argMem (k c G j : Nat) (o : Operand) : List Instr :=
  (src k c .rax o).1 ++ [.store (calleeMem (Sel.frameW k c G) (j - c)) (src k c .rax o).2]

/-- Loads operand `o` into the register of location `j`. The preserved registers of the
locations below `n` are already overwritten by then, so an operand in one of them is read back
from its save word in the callee frame. -/
def argReg (k c G n j : Nat) : Operand → List Instr
  | .slot y =>
    if y < k then
      if y < n then [.load (loc k j) (calleeMem (Sel.frameW k c G) y)]
      else if y = j then [] else [.movRR (loc k j) (preg y)]
    else if y < k + c then [.movRR (loc k j) (loc k y)]
    else [ldI c (loc k j) (.slot y)]
  | .imm w => [.movRI (loc k j) w]

/-- The memory arguments from `j` on, each only when `ent` names its word. -/
def argMems (k c G : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j then argMem k c G j o else []) ++ argMems k c G ent (j + 1) os

/-- The preserved register arguments from `j` on, each only when `ent` names its location. -/
def argRegs (k c G : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j then argReg k c G j j o else []) ++ argRegs k c G ent (j + 1) os

/-- The other caller-saved register arguments from `j` on that `ent` names, after the preserved
registers below `n` are overwritten. -/
def cLoads (k c G n : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j && !isC k c o then argReg k c G n j o else []) ++ cLoads k c G n ent (j + 1) os

/-- The parallel move of the caller-saved register arguments in caller-saved registers. -/
abbrev cMoves (k c G : Nat) (args : List Operand) (ent : Nat → Bool) : List (Reg × Reg) :=
  Sel.cMoves (loc k) .rax k c ent k (cArgs k c G args)

/-- The sequential moves of the caller-saved register arguments, through `rax`. -/
def cSeq (k c G : Nat) (args : List Operand) (ent : Nat → Bool) : Option (List (Reg × Reg)) :=
  Sel.PMove.seq .rax (2 * c + 1) (cMoves k c G args ent)

/-- The call sequence before `call`. It saves the preserved location registers below `min k G`
that `keep` names, which are those live after the call, beyond the caller's frame, or used as an
argument. Then it stores the memory arguments while the caller's registers still hold its values,
loads the preserved register arguments, and then the caller-saved ones: the parallel move of
those in caller-saved registers, then the others. Of the callee's locations it writes only those
that `ent` names, which are those live at the callee's entry. -/
def callOps (k c G : Nat) (args : List Operand) (keep ent : Nat → Bool) : List Instr :=
  saves (Sel.frameW k c G) keep 0 (min k G) ++
    argMems k c G ent (min (k + c) G) ((padArgs G args).drop (min (k + c) G)) ++
    argRegs k c G ent 0 ((padArgs G args).take (min k G)) ++
    ((cSeq k c G args ent).getD []).map (fun p => .movRR p.1 p.2) ++
    cLoads k c G (min k G) ent k (cArgs k c G args)

/-- The call sequence up to and including `call g`. -/
def callIs (k c g G : Nat) (args : List Operand) (keep ent : Nat → Bool) : List SI :=
  ops (callOps k c G args keep ent) ++ [.call (.sym (fnSym g))]

/-- Restores the `n` location registers from `x` on from the running frame's words from `x` on,
where the caller saved them. -/
def restores : Nat → Nat → List Instr
  | _, 0 => []
  | x, n + 1 => .load (preg x) (slotMem x) :: restores (x + 1) n

/-- The return sequence of a function whose frame has `W` words: `add rsp, 8W; ret`. -/
def retTail (W : Nat) : List Instr := [.aluRI .add .rsp (UInt32.ofNat (8 * W)), .ret]

/-- The code of `read(fd, buf, 1)` into slot `x` after `rdi := fd`, where the buffer is slot `x`
itself. It sets `rax` to 0, the number of `read`, clears the slot, and sets `rsi := &slot` and
`rdx := 1`. -/
def rdPre (x : Nat) : List Instr :=
  [.movRI .rax 0, .store (slotMem x) .rax, .lea .rsi (slotMem x), .movRI .rdx 1]

/-- The code after the `read` system call, which computes the call's value. It loads the slot,
the byte read or 0, into `rcx`, sets `rax := (result ≠ 1)` and `rdx := 0 - rax`, which is all ones
or zero, and ORs `rdx` into `rcx`. -/
def rdFix (x : Nat) : List Instr :=
  [.load .rcx (slotMem x), .aluRI .cmp .rax 1, .setcc .ne .rax, .movzx .rax .rax,
    .movRI .rdx 0, .aluRR .sub .rdx .rax, .aluRR .or .rcx .rdx]

/-- A place a parallel move reads or writes: a register, or an operand in no register. -/
abbrev Place := Sel.Place Reg

/-- The place of operand `o`: its register for a register location. -/
abbrev place (k c : Nat) : Operand → Place := Sel.place (loc k) (k + c)

/-- The code of one move into a register: a copy, or a load of a slot or an immediate. -/
def emit (k c : Nat) : Place × Place → List Instr
  | (.inl d, .inl r) => [.movRR d r]
  | (.inl d, .inr o) => ldTo k c d o
  | (.inr _, _) => []

/-- The moves of a `write` or `read` of a buffer: `rsi := rax` (the address), `rdi := fd`,
`rdx := l` and `rax` to the number, as one parallel move. -/
abbrev memMoves (k c : Nat) (nr : UInt64) (a l : Operand) : List (Place × Place) :=
  [(.inl .rsi, .inl .rax), (.inl .rdi, place k c a), (.inl .rdx, place k c l),
    (.inl .rax, .inr (.imm nr))]

/-- The rest of a `write` or `read` of the `l` bytes at the address in `rax`: the moves of
`memMoves` through `rcx`, `syscall`, and the result into location `x`. -/
def memTail (k c : Nat) (nr : UInt64) (x : Nat) (a l : Operand) : Option (List Instr) :=
  (Sel.PMove.seq (.inl .rcx) 9 (memMoves k c nr a l)).map fun ms =>
    ms.flatMap (emit k c) ++ [.syscall] ++ stTo k c x .rax

/-- The code of one move after a call: a copy into a register, or the store of a register into
slot `x`, frame word `x - c`. -/
def emitW (c : Nat) : Place × Place → List Instr
  | (.inl d, .inl r) => [.movRR d r]
  | (.inr (.slot x), .inl r) => [.store (slotMem (x - c)) r]
  | _ => []

/-- The moves of `ret`: operand `i` into `retReg i`. -/
abbrev retMoves (k c : Nat) (os : List Operand) : List (Place × Place) :=
  Sel.retMoves retReg (place k c) 0 os

/-- The moves after a call: `retReg i` into location `d + i`, for `i < n`. -/
abbrev resMoves (k c d n : Nat) : List (Place × Place) :=
  Sel.resMoves retReg (place k c) d 0 n

/-- The fuel of the result moves, which bounds their number: `n` moves and one more for each
cycle, of which there are at most `n / 2`. -/
def resFuel (n : Nat) : Nat := n + n / 2

/-- The moves of the returned operands into the return registers, sequentialised through `r11`,
which no other code uses. -/
def retLd (k c : Nat) (os : List Operand) : Option (List Instr) :=
  (Sel.PMove.seq (.inl .r11) (2 * os.length + 1) (retMoves k c os)).map (·.flatMap (emit k c))

/-- The caller's moves of the `n` returned words into the locations from `d` on, by a copy into
a register location or a store into a slot, sequentialised through `r11`. -/
def retW (k c d n : Nat) : Option (List Instr) :=
  (Sel.PMove.seq (.inl .r11) (resFuel n) (resMoves k c d n)).map (·.flatMap (emitW c))

/-- The registers `rdi rsi rdx`, which a system call reads its arguments from, the remainder
writes, and which carry returned words 4, 3 and 2. -/
def fixRegs : List Reg := [.rdi, .rsi, .rdx]

/-- The block of one Lin instruction at position `pc` of function number `i`, whose code is
`fn`, with `k` preserved and `c` caller-saved register locations, together with the data
items it needs. -/
def selInstr (k c : Nat) (mb : Bool) (lvo : Option RegAlloc.LiveSets) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) :
    Lin.Instr → Except String (List SI × List (String × List UInt8))
  | .mov x a =>
    if x < k + c then .ok (ops (ldTo k c (loc k x) a), [])
    else if a = .slot x then .ok ([], [])
    else .ok (ops ((src k c .rax a).1 ++ [.store (slotMem (x - c)) (src k c .rax a).2]), [])
  | .bin op x a b =>
    .ok (ops ((src k c .rax a).1 ++ binCodeB k c mb op (dreg k c x) (src k c .rax a).2 b ++
      fin k c x (binRes op (dreg k c x))), [])
  | .load w x a off =>
    .ok (memX k c mb a off ++ ops (ldWR w (dreg k c x) (memM k c mb a off) :: fin k c x (dreg k c x)), [])
  | .store w a off b =>
    .ok (memX k c mb a off ++ ops (storeCode k c mb w a off b), [])
  | .jmp l => .ok ([.jmp (.label l)], [])
  | .jz o l =>
    .ok (ops ((src k c .rax o).1 ++ [.aluRI .cmp (src k c .rax o).2 0]) ++ [.jcc .e (.label l)], [])
  | .call g args d =>
    match P.funs[g]? with
    | none => .error "select: call to a missing function"
    | some gf =>
      if args.length ≤ gf.frame then
        match (cSeq k c gf.frame args (RegAlloc.Live.liveIn lvo g 0)).isSome, retW k c d gf.ret.length with
        | true, some rw =>
          .ok (callIs k c g gf.frame args (RegAlloc.Live.callKeep lvo P i pc g d args)
            (RegAlloc.Live.liveIn lvo g 0) ++ ops rw, [])
        | _, _ => .error "select: no sequence for a parallel move of the arguments or results"
      else .error "select: more arguments than the callee's frame"
  | .ret =>
    match retLd k c fn.ret with
    | none => .error "select: no sequence for the parallel move of the returned words"
    | some rl =>
    .ok (ops (rl ++ restores 0 (min k fn.frame) ++
      retTail (Sel.frameW k c fn.frame)), [])
  | .ext sym nr x args =>
    match sym, nr, args with
    | "exit", true, [.word a] =>
      .ok (ops (ldTo k c .rdi a ++ [.movRI .rax 60, .syscall] ++ stTo k c x .rax), [])
    | "write", false, [.word a, .bytes bs] =>
      if bs.length < 2 ^ 32 then
        .ok (ops (ldTo k c .rdi a) ++ [.lea .rsi (.sym (dataSym i pc))] ++
          ops ([.movRI .rdx (UInt64.ofNat bs.length), .movRI .rax 1, .syscall] ++ stTo k c x .rax),
          [(dataSym i pc, bs)])
      else .error "select: constant buffer too large"
    | "write", false, [.word a, .mem p l] =>
      match memTail k c 1 x a l with
      | some tl => .ok (memAddrR k c mb p 0 ++ ops tl, [])
      | none => .error "select: no sequence for the parallel move of the arguments"
    | "read", false, [.word a, .out 1] =>
      if x < k + c then .error "select: read into a register location"
      else .ok (ops (ldTo k c .rdi a ++ rdPre (x - c) ++ [.syscall] ++ rdFix (x - c) ++
        [.store (slotMem (x - c)) .rcx]), [])
    | "read", false, [.word a, .outMem p l] =>
      match memTail k c 0 x a l with
      | some tl => .ok (memAddrR k c mb p 0 ++ ops tl, [])
      | none => .error "select: no sequence for the parallel move of the arguments"
    | _, _, _ => .error ("select: unsupported extern " ++ sym)
  | .tick _ => .ok ([], [])

/-- A function is accepted when its frame is addressable with 32-bit displacements and its
returned words fit the return registers. -/
def fnOk (fn : Lin.Fn) : Bool := fn.frame < 2 ^ 24 && fn.ret.length ≤ 8

/-- x64's part of the shared selection driver with `k` preserved and `c` caller-saved register
locations: the blocks, the entry `sub rsp, 8F`, and the limits on frames and returned words. With
caller-saved locations a function returns at most five words, in `rax rcx rdx rsi rdi`; the last
three are also locations' registers, which `retLd` and `retW` handle as parallel moves. -/
def selector (k c : Nat) (mb : Bool) (lvo : Option RegAlloc.LiveSets) : Sel.Selector arch where
  instr := selInstr k c mb lvo
  entry fn := [SI.op (.aluRI .sub .rsp (UInt32.ofNat (8 * Sel.frameW k c fn.frame)))]
  fnOk fn := fnOk fn && decide (k ≤ maxK) && decide (c ≤ maxC) && (c == 0 || fn.ret.length ≤ 5)

/-- The register classes of x64 for the allocator. A call destroys every caller-saved register;
an extern call destroys `rdi rsi rdx` (caller-saved registers 3, 4, 5), its arguments; a
division destroys `rdx` and a remainder `rdi rsi rdx`. Returned words 2, 3, 4 are in `rdx rsi
rdi` and system-call arguments 0, 1, 2 in `rdi rsi rdx`, which the allocator tries first for
such a value (`resReg`, `argReg`). -/
def cls (k c : Nat) : RegAlloc.Alloc.Classes :=
  { k, c, kill := fun
      | .call .. => (List.range c, [])
      | .ext .. => ([3, 4, 5].filter (· < c), [])
      | .bin .udiv .. => ([5].filter (· < c), [])
      | .bin .umod .. => ([3, 4, 5].filter (· < c), [])
      | _ => ([], [])
    resReg := fun i => if i = 2 then some 5 else if i = 3 then some 4 else if i = 4 then some 3
      else none
    argReg := fun i => if i < 3 then some (3 + i) else none }

/-- Instruction selection for x64 with `k` preserved and `c` caller-saved register locations,
where `k = c = 0` puts every location in a frame slot. The data region becomes the
zero-initialised writable region `mp_mem`. With caller-saved locations it refuses a program in
which a location live after a call is a caller-saved one that the call does not define
(`Live.clobOk`). -/
def select (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Except String (Asm.Prog arch) :=
  if c = 0 ∨ RegAlloc.Live.clobOk (cls k c).across (RegAlloc.Live.of P) P = true then
    Sel.select (selector k c mb (RegAlloc.Live.of P)) P
  else .error "select: a caller-saved location is live across a call"

/-- The number of preserved register locations `compile` uses on x64 by default, the one that
executes the fewest instructions in measurement. -/
def kDefault : Nat := 6

/-- The number of caller-saved register locations `compile` uses on x64 by default, all six:
`r8 r9 r10 rdi rsi rdx`. -/
def cDefault : Nat := 6

/-- The numbers of preserved and caller-saved register locations used for `P`: `(k, c)`, or
`(k, 0)` when the selector refuses that, or `(0, 0)` when it refuses both. With caller-saved
locations the selector refuses a program in which one is live across an instruction that destroys
it, which happens when allocation fell back to the unallocated program; `compile` then allocates
again without caller-saved locations (`Compile.prep`), and `(k, 0)` refuses only a one-byte `read`
into a register location, which happens likewise. -/
def kcUsed (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Nat × Nat :=
  match select k c P mb with
  | .ok _ => (k, c)
  | .error _ => match select k 0 P mb with
    | .ok _ => (k, 0)
    | .error _ => (0, 0)

/-- The x64 selection that `compile` runs, which is `select` at `kcUsed k c P`. -/
def selectFb (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Except String (Asm.Prog arch) :=
  select (kcUsed k c P mb).1 (kcUsed k c P mb).2 P mb

theorem kcUsed_le (k c : Nat) (P : Lin.Prog) (mb : Bool) :
    (kcUsed k c P mb).1 ≤ k ∧ (kcUsed k c P mb).2 ≤ c := by
  unfold kcUsed; split
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · split <;> exact ⟨by omega, by omega⟩

theorem kcUsed_of_ok {k c : Nat} {P : Lin.Prog} {mb : Bool} (h : (select k c P mb).isOk = true) :
    kcUsed k c P mb = (k, c) := by
  unfold kcUsed; split
  · rfl
  · rename_i e he; rw [he] at h; cases h

end Millipede.X64
