import Millipede.Target.A64.Word
import Millipede.Target.SelDriver
import Millipede.Target.Budget
import Millipede.Target.CallArgs

/-!
# Pieces of arm64 instruction selection

This module defines the parts of arm64 selection that do not depend on register locations: the
Linux system-call ABI, the frame size, constants, frame words, symbol addresses, the entry
sequence and the cost model. The selector itself is `RegAlloc.A64Reg.select`. Symbolic
references are fixups of the word assembler. A `b` or `bl` reaches ±128 MiB, a `cbz` reaches
±1 MiB and is used only for local labels, and the address of a symbol is computed by `adrp` and
`add :lo12:`, which reach ±4 GiB.

The selected code uses `x16` and `x17` as scratch registers for operands and addresses, `x15` as
the base of a far slot, `x9` for the quotient of `umod`, `x0` to `x13` for the returned words and
the system-call arguments, `x8` for the system-call number and `x30` as the link register. It
never uses `x18`, which Apple platforms reserve.

A function with `F` slots has a frame of `fsize F` bytes, which holds the slots and the saved
`x30`. The size is rounded up to 16 bytes, because every access based on `sp` needs `sp` to be
16-byte aligned, and from 510 slots on to whole 4 KiB, so that one `sub sp, sp, #fsize F`
reserves it. Slot `x` is `[sp, #8x]`, `x30` is saved at `[sp, #8F]` and the caller's frame starts
at `sp + fsize F`. The scaled 12-bit offset of a load or store reaches only the words below 4,096,
so a word `x ≥ 4096` above a base `b` is reached as `add s, b, #⌊x / 512⌋, lsl 12` followed by an
access to `[s, #8 (x % 512)]`. A load uses its destination as `s` and a store uses `x15`. Frames
are limited to `maxFrame = 4095 · 512` slots, almost 16 MiB, so that every slot and every frame
size stay in reach.

A constant is `movz d, #h0` followed by `movk d, #hk, lsl #16k` for every non-zero halfword
`k = 1, 2, 3`. A Lin address `a + off` of the data region is computed into `x16` by adding `a`,
`off` and the address of `mp_mem`. A system call takes its number in `x8`, which is 63 for `read`,
64 for `write` and 93 for `exit`, its arguments in `x0` to `x2`, and returns its result in `x0`.
A one-byte `read` uses the destination slot as its buffer and then computes the value of the
call, which is the byte when the result is `1` and `2^64 - 1` otherwise.

Selection refuses frames of `maxFrame` slots or more, more than 14 returned words, constant
`write` buffers of `2^32` bytes or more, unknown externs, calls to missing functions and calls
with more arguments than the callee's frame. The assembler refuses references out of reach.
-/

namespace Millipede.A64

open Flat (Operand BinOp ExtArg)
open Sel (fnSym dataSym memSym)
export Sel (padArgs)

/-- arm64 symbolic instructions. -/
abbrev SI := Asm.WSI Instr

/-! ## The Linux system-call ABI -/

/-- The arm64 Linux ABI. It lays out segments in 64 KiB pages and places the stack below
`Abi.a64LinuxStackTop`. A system call takes its number in `x8` and its arguments in `x0` to `x2`
and returns its result in `x0`, and at entry every register except `sp` is `0`. -/
def linux : Abi isa :=
  Abi.linux 16 Abi.a64LinuxStackTop
    (fun entry sp => ⟨fun k => if k = 31 then sp else 0, entry, ⟨false, false, false, false⟩⟩)
    LinuxNums.a64 ⟨fun r => r.x 8, fun i r => r.x (BitVec.ofNat 5 i), fun v r => r.set 0 v⟩

/-! ## Resource hooks -/

/-- The bytes of a frame of `F` slots, which holds the slots and the saved `x30`. The size is
rounded up to 16, and from 510 slots on up to whole 4 KiB, so that `sub sp, sp, #fsize F` is one
instruction. -/
def fsize (F : Nat) : Nat := if F < 510 then 16 * ((F + 2) / 2) else 4096 * ((8 * F + 4103) / 4096)

/-- The arm64 frame model, under which an activation of `w` slots takes `fsize w` bytes. -/
def φ : FrameModel := ⟨fsize, fun h => by unfold fsize; split <;> split <;> omega⟩

/-- The bound on frame sizes in slots, which every frame stays below: `2,096,640` words, almost
16 MiB. Every slot and the saved `x30` then lie at a word offset below `2^21`, which `farA`
reaches, and `fsize F < 2^24` is an immediate `#n, lsl 12` with `n < 4096`. -/
def maxFrame : Nat := 4095 * 512

/-! ## Code -/

/-- The halfword `k` of `w`. -/
def half (w : UInt64) (k : Nat) : BitVec 16 := BitVec.ofNat 16 (w.toNat / 2 ^ (16 * k))

/-- Load a constant with `movz d, #h0` followed by a `movk` for every non-zero halfword above. -/
def immIs (d : Reg) (w : UInt64) : List Instr :=
  .mov .z true d (half w 0) 0 ::
    ([1, 2, 3].filter fun k => half w k != 0).map fun k => .mov .k true d (half w k) (BitVec.ofNat 2 k)

/-- `add` or `sub d, n, #fsize F`, whose immediate is `#(fsize F / 4096), lsl 12` from 510
slots on. -/
def frameI (sub : Bool) (d n : Reg) (F : Nat) : Instr :=
  if F < 510 then .addImm true sub false d n (BitVec.ofNat 12 (fsize F)) false
  else .addImm true sub false d n (BitVec.ofNat 12 (fsize F / 4096)) true

/-- The code before an access to word `x` above the base `b`, which is nothing when the scaled
12-bit offset reaches `x < 4096` and `add s, b, #⌊x / 512⌋, lsl 12` otherwise. -/
def farPre (s b : Reg) (x : Nat) : List Instr :=
  if x < 4096 then [] else [.addImm true false false s b (BitVec.ofNat 12 (x / 512)) true]

/-- The address of word `x` above the base `b` after `farPre s b x`, which is `[b, #8x]` or
`[s, #8 (x % 512)]`. -/
def farA (s b : Reg) (x : Nat) : Addr :=
  if x < 4096 then .uimm b (BitVec.ofNat 12 x) else .uimm s (BitVec.ofNat 12 (x % 512))

/-- Load an operand into register `r`, which serves itself as the base of a far slot. -/
def ldIs (r : Reg) : Operand → List Instr
  | .slot y => farPre r 31 y ++ [.ldr .x r (farA r 31 y)]
  | .imm w => immIs r w

/-- Store register `r` into frame slot `x`, a far slot through `x15`. -/
def stIs (x : Nat) (r : Reg) : List Instr := farPre 15 31 x ++ [.str .x r (farA 15 31 x)]

/-- Load the address `sp + 8x` of slot `x` into `d`. -/
def slotAddr (d : Reg) (x : Nat) : List Instr :=
  if x < 512 then [.addImm true false false d 31 (BitVec.ofNat 12 (8 * x)) false]
  else [.addImm true false false d 31 (BitVec.ofNat 12 (x / 512)) true,
    .addImm true false false d d (BitVec.ofNat 12 (8 * (x % 512))) false]

/-- Plain instructions as symbolic ones. -/
def ops (is : List Instr) : List SI := is.map .op

/-- `add d, n, m`. -/
def addR (d n m : Reg) : Instr := .addReg true false false d n m

/-- `add d, d, #lo`, the `:lo12:` half of a symbol's address. -/
def lo12I (d : Reg) (lo : BitVec 12) : Instr := .addImm true false false d d lo false

/-- Load the address of symbol `sym` into `d` with `adrp d, sym; add d, d, :lo12:sym`, which
reaches ±4 GiB. -/
def symAddr (d : Reg) (sym : String) : List SI :=
  [.fix .page21 (.adr true d 0) (.sym sym), .fix (.lo12 0) (lo12I d 0) (.sym sym)]

/-- The size of a Lin access. -/
def size : Flat.Width → Size
  | .w8 => .b
  | .w64 => .x

/-- Store the `n` registers `x_k, …` into the words `o, o+1, …` above the base `b`. -/
def retStores (b : Reg) (o : Nat) : Nat → Nat → List Instr
  | _, 0 => []
  | k, n + 1 => .str .x (BitVec.ofNat 5 k) (.uimm b (BitVec.ofNat 12 o)) :: retStores b (o + 1) (k + 1) n

/-- Whether a frame of `P` has slots beyond the 4,096 that `[sp, #8x]` reaches. -/
def farProg (P : Lin.Prog) : Bool := P.funs.any fun f => 4096 < f.frame

/-- The entry sequence of a frame of `F` slots: `sub sp, sp, #fsize F; str x30, [sp, #8F]`. -/
def entryIs (F : Nat) : List Instr := frameI true 31 31 F :: stIs F 30

/-- Whether a function's frame is below `maxFrame` slots and its returned words fit the
registers. -/
def fnOk (fn : Lin.Fn) : Bool := fn.frame < maxFrame && fn.ret.length ≤ 14

/-! ## Instruction counts -/

/-- The number of instructions of the entry sequence of a frame of `F` slots. -/
def entryLen (F : Nat) : Nat := (entryIs F).length

/-- The arm64 cost model, which charges machine instructions per Core construct, derived as
`X64.κ` is (doc/phases/kappa-install.md): each weight is the most instructions the selected code
of its construct takes in any register-allocation setting, where with allocation off a Lin load
or store of the data region is 6 or 7 instructions; the weights fitted from scripts/kappa.lean's
programs carry a margin of 10%, rounded up. arm64 has no division guard, a one-instruction `cbz`
and two-instruction comparisons, against up to four instructions for a constant and the save of
`x30` in a call.

* `word` 29: one iteration of the loop that fills or copies a value of 64 bytes or more (element
  address 4, load 7, store 7, counter step 3, back jump 1, test 5, branch 2).
* `iter` 59: a loop's per-iteration code with its counter and flag in memory (counter step 17,
  back jump 1, test 12 and branch 2, the counter's copy 14, the flag's load 7 and branches 6).
* `loop` 13 (11), `prim` 36 (32: two operands through references), `div` 37 (33: the same with
  the remainder's `udiv` and `msub`), `mem` 27 (24)
  and `place` 5 (4 per selector), `ref` 39 (35), `call` 18 (16), `ext` 19 (17), `ite` 10 (9),
  `ctor` 9 (8), `atom` 5 (4), `let_` 3 (2: the reactor loop's test), `match_` 0 (paid by the
  scrutinee's words); in brackets the count before the margin, for the same constructs as in
  `X64.κ`. -/
def κ : CostModel where
  atom := 5
  let_ := 3
  ite := 10
  prim := 36
  div := 37
  loop := 13
  iter := 59
  call := 18
  ctor := 9
  match_ := 0
  ext := 19
  word := 29
  place := 5
  mem := 27
  ref := 39

end Millipede.A64
