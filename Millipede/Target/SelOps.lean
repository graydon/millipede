import Millipede.Target.SelCases

/-!
# Frame-local cases proved over an ISA's operations

An ISA's selected code for the frame-local Lin instructions is built from a few operations on
locations, where location `x < (C.k + C.c)` of the running frame is the machine register `preg x` and
every other location is its frame slot. `Ops` names these operations, which use the scratch
registers `r0` and `r1`:

* `ld r o` puts operand `o` into register `r`, by a copy or by nothing for a register location.
* `src r o` puts operand `o` into some register and returns that register with the code. A
  register location is used in place with no code, and any other operand is loaded by `ld r o`.
* `st x r` puts register `r` into location `x`, by a slot store or a copy into `preg x`.
* `bin op d n m` puts `n op m` into `binRes op d`, which is `d` where the ISA allows it.
* `binI op d n w` is the immediate form of `bin` where the ISA has one; `binOps` uses it for an
  immediate operand.
* `memA o off` puts the data address `mp_mem + o + off` into `r0`, for the externs that pass a
  buffer.
* `memX o off` is the address code of a `load` or `store` of `o + off`, after which `ldW w d o off`
  and `stW w r o off` access the data region at the address `ea o off` of the register file, and
  `stI w v o off` is an immediate form of `stW` where the ISA has one. Each ISA chooses the
  sequence: the address in `r0`, or a base register for the region and a displacement.

The blocks `movIs`, `binIs`, `loadIs` and `storeIs` compute a result for location `x` into
`dst k x`, the location's register or `r0`, and end with `fin k x`, which is nothing or the slot
store. `Ops.Laws` states what the proofs need of an ISA: the selector builds these blocks, the
counts are their lengths, and each operation is straight-line code that runs as stated from a
state with a related state's memory, stack pointer and location registers. No operation changes
a location register other than its destination, and the location registers are distinct and not
scratch. `Ops.MemLaws` states the same of the `load` and `store` blocks.

From the laws, this module proves once for every ISA that the blocks of `mov`, `bin`, `load` and
`store` re-establish the relation. A move of a location to itself has no code and is a silent
step.
-/

namespace Millipede.Sel

open Flat (Operand BinOp)

/-- The operations that an ISA's selected code for frame-local instructions is made of. -/
structure Ops (A : Asm.Arch) where
  Reg : Type
  deq : DecidableEq Reg := by infer_instance
  get : A.isa.Regs → Reg → UInt64
  r0 : Reg
  r1 : Reg
  /-- An instruction without references, as an Asm instruction. -/
  op : A.isa.Instr → A.SInstr
  /-- Puts an operand into a given register. -/
  ld : Reg → Operand → List A.isa.Instr
  /-- Puts an operand into some register, and returns the code and the register. -/
  src : Reg → Operand → List A.isa.Instr × Reg
  /-- Puts a register into a location. -/
  st : Nat → Reg → List A.isa.Instr
  /-- Puts `n op m` into `binRes op d`. -/
  bin : BinOp → Reg → Reg → Reg → List A.isa.Instr
  binRes : BinOp → Reg → Reg
  /-- The registers besides the destination that `bin op` may destroy, such as a division's. -/
  binKill : BinOp → List Reg := fun _ => []
  /-- The register of register location `x`. -/
  preg : Nat → Reg
  /-- The address code of a `load` or `store` of the data address `o + off`, and its length
  once resolved. -/
  memX : Operand → UInt64 → List A.SInstr
  memXLen : Operand → UInt64 → Nat
  /-- The machine address that the accesses after `memX o off` reach in a register file. -/
  ea : A.isa.Regs → Operand → UInt64 → UInt64
  /-- Load from and store to the address that `memX o off` set up, at a width, into or from a
  register. -/
  ldW : Flat.Width → Reg → Operand → UInt64 → List A.isa.Instr
  stW : Flat.Width → Reg → Operand → UInt64 → List A.isa.Instr
  /-- An immediate form of `bin`, which puts `n op w` into `binRes op d`, where the ISA has one. -/
  binI : BinOp → Reg → Reg → UInt64 → Option (List A.isa.Instr)
  /-- An immediate form of `stW`, which stores `v` to the address `memX o off` set up, where the
  ISA has one. -/
  stI : Flat.Width → UInt64 → Operand → UInt64 → Option (List A.isa.Instr)
  /-- The registers `ld` may load and `st` may store, and the operand registers of `bin`. -/
  ldOk : Reg → Prop
  stOk : Reg → Prop
  binOk : Reg → Reg → Prop
  /-- An invariant of the states the code runs through. -/
  Ok : MState A.isa.Regs → Prop
  /-- The Linux system calls: the numbers, the registers of the number, the arguments and the
  result, and the system-call instruction. -/
  nums : LinuxNums
  nrR : Reg
  argR : Nat → Reg
  res : Reg
  trap : A.isa.Instr
  /-- `mv d s` copies register `s` into `d`. -/
  mv : Reg → Reg → List A.isa.Instr
  /-- Puts the address of a symbol into a register, with the code's length once resolved. -/
  symA : Reg → String → List A.SInstr
  symLen : Nat
  /-- The code of `read(fd, slot x, 1)` between the descriptor and the trap, which clears the
  slot and sets up its address, the length and the number, and the code after the trap, which
  puts the call's value into `rdRes`. -/
  rdPre : Nat → List A.isa.Instr
  rdFix : Nat → List A.isa.Instr
  rdRes : Reg

variable {A : Asm.Arch}

namespace Ops
variable (O : Ops A) (k : Nat)

instance : DecidableEq O.Reg := O.deq

/-- The register a result for location `x` is computed in. -/
def dst (x : Nat) : O.Reg := if x < k then O.preg x else O.r0

/-- The code after computing into `dst k x`, which is nothing for a register location and the
slot store otherwise. -/
def fin (x : Nat) (r : O.Reg) : List A.isa.Instr := if x < k then [] else O.st x r

/-- The code of `mov x o`, which loads the operand into the location's register, is nothing for
the move of a slot to itself, or goes through `src` into the slot. -/
def movIs (x : Nat) (o : Operand) : List A.isa.Instr :=
  if x < k then O.ld (O.preg x) o
  else if o = .slot x then [] else (O.src O.r0 o).1 ++ O.st x (O.src O.r0 o).2

/-- `n op o` into `binRes op d`, by the operand in some register and `bin`. -/
def binReg (op : BinOp) (d n : O.Reg) (o : Operand) : List A.isa.Instr :=
  (O.src O.r1 o).1 ++ O.bin op d n (O.src O.r1 o).2

/-- `n op o` into `binRes op d`, by an immediate form when `o` is an immediate the ISA has one
for, and by `binReg` otherwise. -/
def binOps (op : BinOp) (d n : O.Reg) : Operand → List A.isa.Instr
  | .imm w => (O.binI op d n w).getD (O.binReg op d n (.imm w))
  | o => O.binReg op d n o

/-- The code of `bin op x a b`. -/
def binIs (op : BinOp) (x : Nat) (a b : Operand) : List A.isa.Instr :=
  (O.src O.r0 a).1 ++ O.binOps op (O.dst k x) (O.src O.r0 a).2 b ++
    O.fin k x (O.binRes op (O.dst k x))

/-- The code of `load w x o off` after `memX o off`. -/
def loadIs (w : Flat.Width) (x : Nat) (o : Operand) (off : UInt64) : List A.isa.Instr :=
  O.ldW w (O.dst k x) o off ++ O.fin k x (O.dst k x)

/-- A store of `b` through a register after `memX o off`. -/
def storeReg (w : Flat.Width) (o : Operand) (off : UInt64) (b : Operand) : List A.isa.Instr :=
  (O.src O.r1 b).1 ++ O.stW w (O.src O.r1 b).2 o off

/-- The code of a store of `b` after `memX o off`, by an immediate form when `b` is an immediate
the ISA has one for. -/
def storeIs (w : Flat.Width) (o : Operand) (off : UInt64) : Operand → List A.isa.Instr
  | .imm v => (O.stI w v o off).getD (O.storeReg w o off (.imm v))
  | b => O.storeReg w o off b

/-- `r0 := o + off`, the first part of `memA`. -/
def memPre (o : Operand) (off : UInt64) : List A.isa.Instr :=
  (O.src O.r0 o).1 ++ O.binOps .add O.r0 (O.src O.r0 o).2 (.imm off)

/-- The code of an index `o + off` for an access through a base register: `o` in its register
(`src`) when `off = 0`, and otherwise `r0 := o + off` (`memPre`). -/
def ixCode (o : Operand) (off : UInt64) : List A.isa.Instr :=
  if off = 0 then (O.src O.r0 o).1 else O.memPre o off

/-- The register that holds the index after `ixCode o off`. -/
def ixReg (o : Operand) (off : UInt64) : O.Reg := if off = 0 then (O.src O.r0 o).2 else O.r0

/-- Puts the data address `mp_mem + o + off` into `r0` by `r0 := o + off; r1 := &mp_mem;
r0 += r1`. -/
def memA (o : Operand) (off : UInt64) : List A.SInstr :=
  (O.memPre o off).map O.op ++ O.symA O.r1 memSym ++ (O.bin .add O.r0 O.r0 O.r1).map O.op

/-- The length of `memA` once resolved. -/
def memLen (o : Operand) (off : UInt64) : Nat :=
  (O.memPre o off).length + O.symLen + (O.bin .add O.r0 O.r0 O.r1).length

/-- Without immediate forms, `binOps` is `binReg`. -/
theorem binOps_of_none (h : ∀ op d n w, O.binI op d n w = none) (op : BinOp) (d n : O.Reg)
    (o : Operand) : O.binOps op d n o = O.binReg op d n o := by
  cases o <;> simp [binOps, h]

/-- Without immediate forms, `storeIs` is `storeReg`. -/
theorem storeIs_of_none (h : ∀ w v o off, O.stI w v o off = none) (w : Flat.Width) (o : Operand)
    (off : UInt64) (b : Operand) : O.storeIs w o off b = O.storeReg w o off b := by
  cases b <;> simp [storeIs, h]

/-- The registers of the locations `x < k` hold the same values in `t'` as in `t`. -/
def Keeps (t t' : A.isa.Regs) : Prop := ∀ x, x < k → O.get t' (O.preg x) = O.get t (O.preg x)

/-- The register of operand `o`, when it is a register location below `k`, holds the same value
in `t'` as in `t`. -/
def KeepsOp (o : Operand) (t t' : A.isa.Regs) : Prop :=
  ∀ y, o = .slot y → y < k → O.get t' (O.preg y) = O.get t (O.preg y)

/-- `Keeps` for every location register other than `d`. -/
def KeepsBut (t t' : A.isa.Regs) (d : O.Reg) : Prop :=
  ∀ x, x < k → O.preg x ≠ d → O.get t' (O.preg x) = O.get t (O.preg x)

/-- `Keeps` for every location register other than `d` and those of `S`. -/
def KeepsButS (t t' : A.isa.Regs) (d : O.Reg) (S : List O.Reg) : Prop :=
  ∀ x, x < k → O.preg x ≠ d → O.preg x ∉ S → O.get t' (O.preg x) = O.get t (O.preg x)

end Ops

/-- The laws an ISA's operations satisfy for the selector `D`, the counts `cnt` and the
convention `C`. -/
structure Ops.Laws (O : Ops A) (abi : Abi A.isa) (C : Conv A) (D : Selector A)
    (cnt : Lin.Prog → Lin.Fn → Lin.Instr → Nat) : Prop where
  resolve_op : ∀ ρ a i, A.resolve ρ a (O.op i) = some i
  sel_mov : ∀ P i pc fn x o, D.instr P i pc fn (.mov x o) = .ok ((O.movIs (C.k + C.c) x o).map O.op, [])
  sel_bin : ∀ P i pc fn op x a b, D.instr P i pc fn (.bin op x a b) =
    .ok ((O.binIs (C.k + C.c) op x a b).map O.op, [])
  cnt_mov : ∀ P fn x o, cnt P fn (.mov x o) = (O.movIs (C.k + C.c) x o).length
  cnt_bin : ∀ P fn op x a b, cnt P fn (.bin op x a b) = (O.binIs (C.k + C.c) op x a b).length
  /-- A register location's value is its register's, and the location registers are distinct
  and not scratch. -/
  reg_get : ∀ r x, x < (C.k + C.c) → C.reg r x = O.get r (O.preg x)
  preg_inj : ∀ x y, x < (C.k + C.c) → y < (C.k + C.c) → O.preg x = O.preg y → x = y
  preg_ne : ∀ x, x < (C.k + C.c) → O.preg x ≠ O.r0 ∧ O.preg x ≠ O.r1
  ld_preg : ∀ x, x < (C.k + C.c) → O.ldOk (O.preg x)
  /-- An empty `ld` into a location's register is the move of the location to itself. -/
  ld_nil : ∀ x o, x < (C.k + C.c) → O.ld (O.preg x) o = [] → o = .slot x
  src_reg : ∀ r o, (O.src r o).2 = r ∨ ∃ y, y < (C.k + C.c) ∧ (O.src r o).2 = O.preg y
  ld0 : O.ldOk O.r0
  ld1 : O.ldOk O.r1
  r01 : O.r1 ≠ O.r0
  st_pos : ∀ x r, (C.k + C.c) ≤ x → 0 < (O.st x r).length
  st0 : O.stOk O.r0
  st_src : ∀ o, O.stOk (O.src O.r0 o).2
  stBin : ∀ op, O.stOk (O.binRes op O.r0)
  bin_pos : ∀ op d n m, 0 < (O.bin op d n m).length
  binOk_src : ∀ a b, O.binOk (O.src O.r0 a).2 (O.src O.r1 b).2
  binOk01 : O.binOk O.r0 O.r1
  binRes_preg : ∀ op x, x < (C.k + C.c) → O.binRes op (O.preg x) = O.preg x
  straight_ld : ∀ ω r o, O.ldOk r → ∀ i ∈ O.ld r o, StraightC C abi ω i
  straight_src : ∀ ω r o, O.ldOk r → ∀ i ∈ (O.src r o).1, StraightC C abi ω i
  straight_st : ∀ ω x r, O.stOk r → ∀ i ∈ O.st x r, StraightC C abi ω i
  straight_bin : ∀ ω op d n m, O.ldOk d → ∀ i ∈ O.bin op d n m, StraightC C abi ω i
  straight_binI : ∀ ω op d n w c, O.binI op d n w = some c → O.ldOk d → ∀ i ∈ c, StraightC C abi ω i
  binI_pos : ∀ op d n w c, O.binI op d n w = some c → 0 < c.length
  ok_match : ∀ {P AP σ lo N s m fn f a j}, MatchAt C P AP σ lo N s m fn f a j → O.Ok m
  run_ld : ∀ {ω P AP σ lo N s m fn f a j} {t : MState A.isa.Regs} {r o},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → O.ldOk r →
    Lin.OpsBelow [o] fn.frame → t.mem = m.mem → A.isa.sp t.regs = A.isa.sp m.regs →
    t.world.halted = false → O.Ok t → O.KeepsOp (C.k + C.c) o m.regs t.regs →
    ∃ t', runIs abi ω (O.ld r o) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs r = o.eval s.frame ∧
      ∀ r', r' ≠ r → O.get t'.regs r' = O.get t.regs r'
  run_src : ∀ {ω P AP σ lo N s m fn f a j} {t : MState A.isa.Regs} {r o},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → O.ldOk r →
    Lin.OpsBelow [o] fn.frame → t.mem = m.mem → A.isa.sp t.regs = A.isa.sp m.regs →
    t.world.halted = false → O.Ok t → O.KeepsOp (C.k + C.c) o m.regs t.regs →
    ∃ t', runIs abi ω (O.src r o).1 t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs (O.src r o).2 = o.eval s.frame ∧
      ∀ r', r' ≠ r → O.get t'.regs r' = O.get t.regs r'
  run_bin : ∀ {ω} op d n m {t : MState A.isa.Regs} {x y}, O.ldOk d → O.binOk n m →
    O.get t.regs n = x → O.get t.regs m = y → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω (O.bin op d n m) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs (O.binRes op d) = op.eval x y ∧
      O.KeepsButS (C.k + C.c) t.regs t'.regs d (O.binKill op)
  /-- An addition destroys nothing, and a location in a register that `bin op` destroys is a
  caller-saved one in the clobber set of every `bin op`. -/
  binKill_add : O.binKill .add = []
  kill_bin : ∀ op x, x < (C.k + C.c) → O.preg x ∈ O.binKill op →
    C.k ≤ x ∧ ∀ y a b, C.kill (.bin op y a b) x = true
  run_binI : ∀ {ω} op d n w c {t : MState A.isa.Regs} {x}, O.binI op d n w = some c → O.ldOk d →
    (∃ a, n = (O.src O.r0 a).2) → O.get t.regs n = x → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω c t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs (O.binRes op d) = op.eval x w ∧
      O.KeepsButS (C.k + C.c) t.regs t'.regs d (O.binKill op)
  run_st : ∀ {ω P AP σ lo N s m fn f a j} {t : MState A.isa.Regs} {x r mem'},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → O.stOk r → (C.k + C.c) ≤ x → x < fn.frame →
    A.isa.sp t.regs = A.isa.sp m.regs → t.world.halted = false → O.Ok t →
    t.mem.writeWord (wa lo (j + x - C.c)) 8 (O.get t.regs r) = some mem' →
    ∃ t', runIs abi ω (O.st x r) t = some t' ∧ t'.mem = mem' ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Keeps (C.k + C.c) t.regs t'.regs
  run_stReg : ∀ {ω} {t : MState A.isa.Regs} {x r}, x < (C.k + C.c) → O.stOk r → t.world.halted = false →
    O.Ok t →
    ∃ t', runIs abi ω (O.st x r) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.get t'.regs (O.preg x) = O.get t.regs r ∧
      ∀ r', r' ≠ O.preg x → O.get t'.regs r' = O.get t.regs r'
  bin_add : O.binRes .add O.r0 = O.r0
  run_sym : ∀ {ω} {ρ : Asm.Ref → Option UInt64} {p Dd : UInt64} {ds : String} {r : O.Reg}
      {xs ys is : List A.isa.Instr}, O.ldOk r → ρ (.sym ds) = some Dd →
    Asm.resolveAt A ρ p (xs.map O.op ++ O.symA r ds ++ ys.map O.op) = some is →
    ∃ pre, is = xs ++ pre ++ ys ∧ pre.length = O.symLen ∧ (∀ i ∈ pre, StraightC C abi ω i) ∧
      ∀ (cx : List UInt8) (t : MState A.isa.Regs), Asm.encodeAll A.isa xs = some cx →
        A.isa.pc t.regs = p + UInt64.ofNat cx.length → t.world.halted = false → O.Ok t →
        ∃ t', runIs abi ω pre t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
          A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs r = Dd ∧
          ∀ r', r' ≠ r → O.get t'.regs r' = O.get t.regs r'

/-- The laws of an ISA's `load` and `store` blocks: the selector builds them from `memX` and the
access forms, the counts are their lengths, `memX` puts the data address into `ea` from a related
state, and the accesses at `ea` read and write the data region. A store's operand goes into `r1`
after `memX`, which leaves `ea` unchanged. -/
structure Ops.MemLaws (O : Ops A) (abi : Abi A.isa) (C : Conv A) (D : Selector A)
    (cnt : Lin.Prog → Lin.Fn → Lin.Instr → Nat) : Prop where
  sel_load : ∀ P i pc fn w x a off, D.instr P i pc fn (.load w x a off) =
    .ok (O.memX a off ++ (O.loadIs (C.k + C.c) w x a off).map O.op, [])
  sel_store : ∀ P i pc fn w a off b, D.instr P i pc fn (.store w a off b) =
    .ok (O.memX a off ++ (O.storeIs w a off b).map O.op, [])
  cnt_load : ∀ P fn w x a off,
    cnt P fn (.load w x a off) = O.memXLen a off + (O.loadIs (C.k + C.c) w x a off).length
  cnt_store : ∀ P fn w a off b,
    cnt P fn (.store w a off b) = O.memXLen a off + (O.storeIs w a off b).length
  run_memX : ∀ {ω P AP σ lo N s m fn f a j} {o : Operand} {off Dm : UInt64}
      {L is : List A.isa.Instr} {code : List UInt8},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → Lin.OpsBelow [o] fn.frame →
    σ memSym = some Dm →
    Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) (O.memX o off ++ L.map O.op) =
      some is → Asm.encodeAll A.isa is = some code →
    ∃ pre t, is = pre ++ L ∧ pre.length = O.memXLen o off ∧ (∀ i ∈ pre, StraightC C abi ω i) ∧
      runIs abi ω pre m = some t ∧ t.mem = m.mem ∧ t.world = m.world ∧
      A.isa.sp t.regs = A.isa.sp m.regs ∧ O.Ok t ∧ O.ea t.regs o off = Dm + (o.eval s.frame + off) ∧
      O.Keeps (C.k + C.c) m.regs t.regs
  ea_r1 : ∀ (t t' : A.isa.Regs) o off, (∀ r, r ≠ O.r1 → O.get t' r = O.get t r) →
    O.ea t' o off = O.ea t o off
  straight_ldW : ∀ ω w d o off, O.ldOk d → ∀ i ∈ O.ldW w d o off, StraightC C abi ω i
  ldW_pos : ∀ w d o off, 0 < (O.ldW w d o off).length
  straight_stW : ∀ ω w r o off, ∀ i ∈ O.stW w r o off, StraightC C abi ω i
  stW_pos : ∀ w r o off, 0 < (O.stW w r o off).length
  straight_stI : ∀ ω w v o off c, O.stI w v o off = some c → ∀ i ∈ c, StraightC C abi ω i
  stI_pos : ∀ w v o off c, O.stI w v o off = some c → 0 < c.length
  run_ldW : ∀ {ω} w x o off {t : MState A.isa.Regs} {Dm : UInt64} {M : Nat} {h : Flat.Heap}
      {ad : UInt64},
    DataRel Dm M t.mem h → Dm.toNat + M ≤ 2 ^ 47 → ad.toNat + w.bytes ≤ M →
    O.ea t.regs o off = Dm + ad → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω (O.ldW w (O.dst (C.k + C.c) x) o off) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      O.get t'.regs (O.dst (C.k + C.c) x) = h.load w ad ∧
      O.KeepsBut (C.k + C.c) t.regs t'.regs (O.dst (C.k + C.c) x)
  run_stW : ∀ {ω} w o off b {t : MState A.isa.Regs} {Dm : UInt64} {M : Nat} {h : Flat.Heap}
      {ad v : UInt64},
    DataRel Dm M t.mem h → Dm.toNat + M ≤ 2 ^ 47 → ad.toNat + w.bytes ≤ M →
    O.ea t.regs o off = Dm + ad → O.get t.regs (O.src O.r1 b).2 = v → t.world.halted = false →
    O.Ok t →
    ∃ t', runIs abi ω (O.stW w (O.src O.r1 b).2 o off) t = some t' ∧
      DataRel Dm M t'.mem (h.store w ad v) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Keeps (C.k + C.c) t.regs t'.regs
  run_stI : ∀ {ω} w v o off c {t : MState A.isa.Regs} {Dm : UInt64} {M : Nat} {h : Flat.Heap}
      {ad : UInt64},
    O.stI w v o off = some c → DataRel Dm M t.mem h → Dm.toNat + M ≤ 2 ^ 47 →
    ad.toNat + w.bytes ≤ M → O.ea t.regs o off = Dm + ad → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω c t = some t' ∧ DataRel Dm M t'.mem (h.store w ad v) ∧
      Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Keeps (C.k + C.c) t.regs t'.regs

namespace Ops

variable {O : Ops A} {abi : Abi A.isa} {C : Conv A} {D : Selector A}
  {cnt : Lin.Prog → Lin.Fn → Lin.Instr → Nat} {P : Lin.Prog} {AP : Asm.Prog A}
  {σ : String → Option UInt64} {lo N : Nat}

theorem Keeps.refl {k : Nat} (t : A.isa.Regs) : O.Keeps k t t := fun _ _ => rfl

theorem Keeps.op {k : Nat} {t t' : A.isa.Regs} (h : O.Keeps k t t') (o : Operand) :
    O.KeepsOp k o t t' := fun y _ hy => h y hy

theorem Keeps.trans {k : Nat} {t₁ t₂ t₃ : A.isa.Regs} (h₁ : O.Keeps k t₁ t₂) (h₂ : O.Keeps k t₂ t₃) :
    O.Keeps k t₁ t₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- A run that changes no register but `r`, which is no location's, keeps the location
registers. -/
theorem Keeps.of_others {k : Nat} {t t' : A.isa.Regs} {r : O.Reg} (hr : ∀ x, x < k → O.preg x ≠ r)
    (h : ∀ r', r' ≠ r → O.get t' r' = O.get t r') : O.Keeps k t t' := fun x hx => h _ (hr x hx)

theorem KeepsBut.keeps {k : Nat} {t t' : A.isa.Regs} {d : O.Reg} (h : O.KeepsBut k t t' d)
    (hd : ∀ x, x < k → O.preg x ≠ d) : O.Keeps k t t' := fun x hx => h x hx (hd x hx)

theorem KeepsButS.nil {k : Nat} {t t' : A.isa.Regs} {d : O.Reg} (h : O.KeepsButS k t t' d []) :
    O.KeepsBut k t t' d := fun x hx hd => h x hx hd (by simp)

theorem Laws.ne_r0 (hO : O.Laws abi C D cnt) : ∀ x, x < (C.k + C.c) → O.preg x ≠ O.r0 :=
  fun x hx => (hO.preg_ne x hx).1

theorem Laws.ne_r1 (hO : O.Laws abi C D cnt) : ∀ x, x < (C.k + C.c) → O.preg x ≠ O.r1 :=
  fun x hx => (hO.preg_ne x hx).2

/-- The register of `src r0` is not `r1`. -/
theorem Laws.src0_ne (hO : O.Laws abi C D cnt) (o : Operand) : (O.src O.r0 o).2 ≠ O.r1 := by
  rcases hO.src_reg O.r0 o with h | ⟨y, hy, h⟩ <;> rw [h]
  · exact hO.r01.symm
  · exact hO.ne_r1 y hy

theorem Laws.ldOk_dst (hO : O.Laws abi C D cnt) (x : Nat) : O.ldOk (O.dst (C.k + C.c) x) := by
  unfold dst; split
  · exact hO.ld_preg x ‹_›
  · exact hO.ld0

theorem Laws.resolveAt_op (hO : O.Laws abi C D cnt) {ρ : Asm.Ref → Option UInt64} :
    ∀ (is : List A.isa.Instr) (a : UInt64), Asm.resolveAt A ρ a (is.map O.op) = some is
  | [], _ => rfl
  | i :: is, _ => Asm.resolveAt_cons_some (hO.resolve_op _ _ i) (resolveAt_op hO is _)

/-- Straight-line code ends where its encoding does. -/
theorem runIs_pc {ω : Oracle} : ∀ {is : List A.isa.Instr} {code : List UInt8}
    {t t' : MState A.isa.Regs}, (∀ i ∈ is, Straight abi ω i) → Asm.encodeAll A.isa is = some code →
    runIs abi ω is t = some t' → A.isa.pc t'.regs = A.isa.pc t.regs + UInt64.ofNat code.length
  | [], _, _, _, _, he, h => by cases he; cases h; simp
  | i :: is, _, t, t', hs, he, h => by
    obtain ⟨e, es, hei, hes, rfl⟩ := Asm.encodeAll_cons_inv he
    simp only [runIs] at h
    split at h
    · cases h
    · cases hx : A.isa.exec (abi.trap ω) i (ilen i) t with
      | none => rw [hx] at h; cases h
      | some t₁ =>
        rw [hx, Option.bind_some] at h
        rw [runIs_pc (fun j hj => hs j (List.mem_cons_of_mem _ hj)) hes h,
          (hs i List.mem_cons_self _ _ hx).1, ilen_of hei, List.length_append, UInt64.ofNat_add,
          UInt64.add_assoc]

/-- The pieces `binReg` and `binOps` are straight-line code of at least one instruction. -/
theorem Laws.straight_binOps (hO : O.Laws abi C D cnt) (ω : Oracle) (op : BinOp) (d n : O.Reg)
    (o : Operand) (hd : O.ldOk d) : ∀ i ∈ O.binOps op d n o, StraightC C abi ω i := by
  have hr : ∀ i ∈ O.binReg op d n o, StraightC C abi ω i :=
    List.forall_mem_append.2 ⟨hO.straight_src ω _ _ hO.ld1, hO.straight_bin ω op _ _ _ hd⟩
  cases o with
  | slot y => exact hr
  | imm w =>
    cases hc : O.binI op d n w with
    | none => simpa [binOps, hc] using hr
    | some c => simpa [binOps, hc] using hO.straight_binI ω op d n w c hc hd

theorem Laws.binOps_pos (hO : O.Laws abi C D cnt) (op : BinOp) (d n : O.Reg) (o : Operand) :
    0 < (O.binOps op d n o).length := by
  have hr : 0 < (O.binReg op d n o).length := by
    have := hO.bin_pos op d n (O.src O.r1 o).2; simp [binReg]; omega
  cases o with
  | slot y => exact hr
  | imm w =>
    cases hc : O.binI op d n w with
    | none => simpa [binOps, hc] using hr
    | some c => simpa [binOps, hc] using hO.binI_pos op d n w c hc

/-- Run from a state with a related state's memory, `sp` and location registers, `binReg op d n o`
for `n` the register of a first operand puts `n op o` into `binRes op d`. It keeps every location
register but `d`. -/
theorem Laws.run_binReg (hO : O.Laws abi C D cnt) {ω : Oracle} {s : Lin.State}
    {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) (op : BinOp) {d : O.Reg}
    (a' : Operand) {o : Operand} (hd : O.ldOk d) (ho : Lin.OpsBelow [o] fn.frame)
    {t : MState A.isa.Regs} {x : UInt64} (hm : t.mem = m.mem)
    (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hh : t.world.halted = false) (hOk : O.Ok t)
    (hK : O.Keeps (C.k + C.c) m.regs t.regs) (hx : O.get t.regs (O.src O.r0 a').2 = x) :
    ∃ t', runIs abi ω (O.binReg op d (O.src O.r0 a').2 o) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      O.get t'.regs (O.binRes op d) = op.eval x (o.eval s.frame) ∧
      O.KeepsButS (C.k + C.c) t.regs t'.regs d (O.binKill op) := by
  obtain ⟨t₂, h2, hm2, hw2, hsp2, hOk2, hv2, hk2⟩ :=
    hO.run_src (ω := ω) hM hok hO.ld1 ho hm hsp hh hOk (hK.op _)
  obtain ⟨t₃, h3, hm3, hw3, hsp3, hOk3, hv3, hk3⟩ := hO.run_bin (ω := ω) op d _ _ hd
    (hO.binOk_src a' o) ((hk2 _ (hO.src0_ne a')).trans hx) hv2 (hw2 ▸ hh) hOk2
  exact ⟨t₃, by rw [binReg, runIs_append, h2, Option.bind_some, h3], hm3.trans hm2,
    hw3.trans hw2, hsp3.trans hsp2, hOk3, hv3,
    fun z hz hzd hzs => (hk3 z hz hzd hzs).trans (hk2 _ (hO.ne_r1 z hz))⟩

/-- `binOps`, as `run_binReg` says, by the immediate form when there is one. -/
theorem Laws.run_binOps (hO : O.Laws abi C D cnt) {ω : Oracle} {s : Lin.State}
    {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) (op : BinOp) {d : O.Reg}
    (a' : Operand) {o : Operand} (hd : O.ldOk d) (ho : Lin.OpsBelow [o] fn.frame)
    {t : MState A.isa.Regs} {x : UInt64} (hm : t.mem = m.mem)
    (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hh : t.world.halted = false) (hOk : O.Ok t)
    (hK : O.Keeps (C.k + C.c) m.regs t.regs) (hx : O.get t.regs (O.src O.r0 a').2 = x) :
    ∃ t', runIs abi ω (O.binOps op d (O.src O.r0 a').2 o) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      O.get t'.regs (O.binRes op d) = op.eval x (o.eval s.frame) ∧
      O.KeepsButS (C.k + C.c) t.regs t'.regs d (O.binKill op) := by
  have hr := hO.run_binReg (ω := ω) hM hok op a' hd ho hm hsp hh hOk hK hx
  cases o with
  | slot y => exact hr
  | imm w =>
    cases hc : O.binI op d (O.src O.r0 a').2 w with
    | none => simpa [binOps, hc] using hr
    | some c =>
      obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := hO.run_binI (ω := ω) op d _ w c hc hd ⟨a', rfl⟩ hx hh hOk
      exact ⟨t', by simpa [binOps, hc] using h1, h2, h3, h4, h5, by simpa [Operand.eval] using h6, h7⟩

theorem MemLaws.straight_storeIs (hO : O.Laws abi C D cnt) (hX : O.MemLaws abi C D cnt)
    (ω : Oracle) (w : Flat.Width) (o : Operand) (off : UInt64) (b : Operand) :
    ∀ i ∈ O.storeIs w o off b, StraightC C abi ω i := by
  have hr : ∀ i ∈ O.storeReg w o off b, StraightC C abi ω i :=
    List.forall_mem_append.2 ⟨hO.straight_src ω _ _ hO.ld1, hX.straight_stW ω w _ o off⟩
  cases b with
  | slot y => exact hr
  | imm v =>
    cases hc : O.stI w v o off with
    | none => simpa [storeIs, hc] using hr
    | some c => simpa [storeIs, hc] using hX.straight_stI ω w v o off c hc

theorem MemLaws.storeIs_pos (hX : O.MemLaws abi C D cnt) (w : Flat.Width) (o : Operand)
    (off : UInt64) (b : Operand) : 0 < (O.storeIs w o off b).length := by
  have hr : 0 < (O.storeReg w o off b).length := by
    have := hX.stW_pos w (O.src O.r1 b).2 o off; simp [storeReg]; omega
  cases b with
  | slot y => exact hr
  | imm v =>
    cases hc : O.stI w v o off with
    | none => simpa [storeIs, hc] using hr
    | some c => simpa [storeIs, hc] using hX.stI_pos w v o off c hc

/-- Run with `ea o off = Dm + ad`, from a state with a related state's memory, `sp` and location
registers, `storeIs w o off b` stores `b` there and changes no other byte and no location
register. -/
theorem MemLaws.run_storeIs (hO : O.Laws abi C D cnt) (hX : O.MemLaws abi C D cnt) {ω : Oracle}
    {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) (w : Flat.Width)
    (o : Operand) (off : UInt64)
    {b : Operand} (hb : Lin.OpsBelow [b] fn.frame) {t : MState A.isa.Regs} {Dm : UInt64} {M : Nat}
    {h : Flat.Heap} {ad : UInt64} (hm : t.mem = m.mem) (hsp : A.isa.sp t.regs = A.isa.sp m.regs)
    (hh : t.world.halted = false) (hOk : O.Ok t) (hK : O.Keeps (C.k + C.c) m.regs t.regs)
    (hDR : DataRel Dm M t.mem h) (hDM : Dm.toNat + M ≤ 2 ^ 47) (hbd : ad.toNat + w.bytes ≤ M)
    (hv : O.ea t.regs o off = Dm + ad) :
    ∃ t', runIs abi ω (O.storeIs w o off b) t = some t' ∧
      DataRel Dm M t'.mem (h.store w ad (b.eval s.frame)) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Keeps (C.k + C.c) t.regs t'.regs := by
  have hr : ∃ t', runIs abi ω (O.storeReg w o off b) t = some t' ∧
      DataRel Dm M t'.mem (h.store w ad (b.eval s.frame)) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Keeps (C.k + C.c) t.regs t'.regs := by
    obtain ⟨t₂, h2, hm2, hw2, hsp2, hOk2, hv2, hk2⟩ :=
      hO.run_src (ω := ω) hM hok hO.ld1 hb hm hsp hh hOk (hK.op _)
    obtain ⟨t₃, h3, hR', hF, hout, hw3, hsp3, hk3⟩ := hX.run_stW (ω := ω) w o off b (hm2 ▸ hDR) hDM
      hbd ((hX.ea_r1 _ _ o off hk2).trans hv) hv2 (hw2 ▸ hh) hOk2
    exact ⟨t₃, by rw [storeReg, runIs_append, h2, Option.bind_some, h3], hR', hm2 ▸ hF,
      fun y hy => (hout y hy).trans (by rw [hm2]), hw3.trans hw2, hsp3.trans hsp2,
      (Keeps.of_others hO.ne_r1 hk2).trans hk3⟩
  cases b with
  | slot y => exact hr
  | imm v =>
    cases hc : O.stI w v o off with
    | none => simpa [storeIs, hc] using hr
    | some c =>
      obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ :=
        hX.run_stI (ω := ω) w v o off c hc hDR hDM hbd hv hh hOk
      exact ⟨t', by simpa [storeIs, hc] using h1, by simpa [Operand.eval] using h2, h3, h4, h5, h6, h7⟩

/-- Run from a related state, `memA` leaves `mp_mem + o + off` in `r0` and keeps the location
registers. -/
theorem Laws.run_mem (hO : O.Laws abi C D cnt) {ω : Oracle} {s : Lin.State}
    {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} {o : Operand}
    {off Dm : UInt64} {L is : List A.isa.Instr} {code : List UInt8}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true)
    (ho : Lin.OpsBelow [o] fn.frame) (hDm : σ memSym = some Dm)
    (hr : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc))
      (O.memA o off ++ L.map O.op) = some is) (hen : Asm.encodeAll A.isa is = some code) :
    ∃ pre t, is = pre ++ L ∧ pre.length = O.memLen o off ∧ (∀ i ∈ pre, StraightC C abi ω i) ∧
      runIs abi ω pre m = some t ∧ t.mem = m.mem ∧ t.world = m.world ∧
      A.isa.sp t.regs = A.isa.sp m.regs ∧ O.Ok t ∧ O.get t.regs O.r0 = Dm + (o.eval s.frame + off) ∧
      O.Keeps (C.k + C.c) m.regs t.regs := by
  rw [memA, List.append_assoc, ← List.map_append] at hr
  obtain ⟨pre, rfl, hplen, hpre, hrun⟩ := hO.run_sym (ω := ω) hO.ld1 hDm hr
  obtain ⟨cxp, -, -, hexp, -⟩ := encodeAll_append _ _ _ hen
  obtain ⟨cx, -, -, hex, -⟩ := encodeAll_append _ _ _ hexp
  obtain ⟨t₁, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_src (ω := ω) hM hok hO.ld0 ho rfl rfl
    hM.halted (hO.ok_match hM) ((Keeps.refl _).op _)
  have hK1 : O.Keeps (C.k + C.c) m.regs t₁.regs := Keeps.of_others hO.ne_r0 hk1
  obtain ⟨t₃, h3, hm3, hw3, hsp3, hOk3, hv3, hk3⟩ := hO.run_binOps (ω := ω) (o := .imm off) hM hok
    .add o hO.ld0 (by simp [Lin.OpsBelow]) hm1 hsp1 (hw1 ▸ hM.halted) hOk1 hK1 hv1
  have hK3 : O.Keeps (C.k + C.c) m.regs t₃.regs :=
    hK1.trans ((KeepsButS.nil (hO.binKill_add ▸ hk3)).keeps hO.ne_r0)
  have hxs : ∀ i ∈ O.memPre o off, StraightC C abi ω i :=
    List.forall_mem_append.2 ⟨hO.straight_src ω _ _ hO.ld0, hO.straight_binOps ω _ _ _ _ hO.ld0⟩
  have h123 : runIs abi ω (O.memPre o off) m = some t₃ := by
    rw [memPre, runIs_append, h1, Option.bind_some, h3]
  obtain ⟨t₄, h4, hm4, hw4, hsp4, hOk4, hv4, hk4⟩ := hrun cx t₃ hex
    (by rw [runIs_pc (fun i h => (hxs i h).1) hex h123, hM.rip]) (by rw [hw3, hw1]; exact hM.halted) hOk3
  obtain ⟨t₅, h5, hm5, hw5, hsp5, hOk5, hv5, hk5⟩ := hO.run_bin (ω := ω) .add O.r0 O.r0 O.r1 hO.ld0
    hO.binOk01 (by rw [hk4 _ hO.r01.symm, ← hO.bin_add]) hv4
    (by rw [hw4, hw3, hw1]; exact hM.halted) hOk4
  refine ⟨O.memPre o off ++ pre ++ O.bin .add O.r0 O.r0 O.r1, t₅,
    by simp, by simp [memLen, hplen]; omega, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨hxs,
      hpre⟩, hO.straight_bin ω _ _ _ _ hO.ld0⟩, by rw [runIs_append, runIs_append, h123,
      Option.bind_some, h4, Option.bind_some, h5], by rw [hm5, hm4, hm3, hm1],
    by rw [hw5, hw4, hw3, hw1], by rw [hsp5, hsp4, hsp3, hsp1], hOk5, ?_,
    hK3.trans ((Keeps.of_others hO.ne_r1 hk4).trans ((KeepsButS.nil (hO.binKill_add ▸ hk5)).keeps hO.ne_r0))⟩
  rw [← hO.bin_add, hv5, hv3]
  simp [BinOp.eval, Operand.eval, UInt64.add_comm]

/-- Run from a related state, `ixCode o off` leaves `o + off` in `ixReg o off` and keeps the
location registers. -/
theorem Laws.run_ix (hO : O.Laws abi C D cnt) {ω : Oracle} {s : Lin.State}
    {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} {o : Operand}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true)
    (ho : Lin.OpsBelow [o] fn.frame) (off : UInt64) :
    ∃ t, runIs abi ω (O.ixCode o off) m = some t ∧ (∀ i ∈ O.ixCode o off, StraightC C abi ω i) ∧
      t.mem = m.mem ∧ t.world = m.world ∧ A.isa.sp t.regs = A.isa.sp m.regs ∧ O.Ok t ∧
      O.get t.regs (O.ixReg o off) = o.eval s.frame + off ∧ O.Keeps (C.k + C.c) m.regs t.regs := by
  obtain ⟨t₁, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_src (ω := ω) hM hok hO.ld0 ho rfl rfl
    hM.halted (hO.ok_match hM) ((Keeps.refl _).op _)
  have hK1 : O.Keeps (C.k + C.c) m.regs t₁.regs := Keeps.of_others hO.ne_r0 hk1
  by_cases h0 : off = 0
  · subst h0
    exact ⟨t₁, by simpa [ixCode] using h1, by simpa [ixCode] using hO.straight_src ω _ _ hO.ld0,
      hm1, hw1, hsp1, hOk1, by simpa [ixReg] using hv1, hK1⟩
  · obtain ⟨t₃, h3, hm3, hw3, hsp3, hOk3, hv3, hk3⟩ := hO.run_binOps (ω := ω) (o := .imm off) hM hok
      .add o hO.ld0 (by simp [Lin.OpsBelow]) hm1 hsp1 (hw1 ▸ hM.halted) hOk1 hK1 hv1
    refine ⟨t₃, by rw [ixCode, if_neg h0, memPre, runIs_append, h1, Option.bind_some]; exact h3,
      by rw [ixCode, if_neg h0]; exact List.forall_mem_append.2 ⟨hO.straight_src ω _ _ hO.ld0,
        hO.straight_binOps ω _ _ _ _ hO.ld0⟩, hm3.trans hm1, hw3.trans hw1, hsp3.trans hsp1, hOk3,
      ?_, hK1.trans ((KeepsButS.nil (hO.binKill_add ▸ hk3)).keeps hO.ne_r0)⟩
    rw [ixReg, if_neg h0, ← hO.bin_add, hv3]; simp [BinOp.eval, Operand.eval]

/-- A block that sets location `x` to `v`, in its register or its slot, and keeps every other
location register, every other stack word below `N` and the data region related, is matched.
The machine reaches the next label related to the next Lin state and keeps `sp` throughout. -/
theorem Laws.sim_set (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) {ω : Oracle} {s s' : Lin.State} {m t : MState A.isa.Regs} {fn : Lin.Fn}
    {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    {b : List A.SInstr} (hblk : f.blocks[s.pc]? = some b) (hlt : s.pc < fn.code.length)
    {is : List A.isa.Instr} {code : List UInt8}
    (hr : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b = some is)
    (he : Asm.encodeAll A.isa is = some code)
    (hc : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) code)
    (hs : ∀ i ∈ is, StraightC C abi ω i) (hrun : runIs abi ω is m = some t)
    (hw : t.world = s'.world) (hh : s'.world.halted = false) (hfn : s'.fn = s.fn)
    (hst : s'.stack = s.stack) (hpc : s'.pc = s.pc + 1) {x : Nat} {v : UInt64}
    (hx : x < fn.frame) (hfr : s'.frame = s.frame.set x v)
    (hwd : ∀ i, i < N → ((C.k + C.c) ≤ x → i ≠ j + x - C.c) → word t.mem lo i = word m.mem lo i)
    (hslot : (C.k + C.c) ≤ x → word t.mem lo (j + x - C.c) = v)
    (hreg : ∀ z, z < (C.k + C.c) → z ≠ x → O.get t.regs (O.preg z) = O.get m.regs (O.preg z))
    (hrx : x < (C.k + C.c) → O.get t.regs (O.preg x) = v)
    (hD : DataOk P σ lo t.mem s'.mem) (c : Nat) :
    (M abi).run ω (m, c) is.length = some (t, c + is.length) ∧
      MatchAt C P AP σ lo N s' t fn f a j ∧
      RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs) (m, c) is.length := by
  have hroom := hM.room; unfold frameW at hroom
  have hL := hM.locs
  refine sim_straight hl hil hM hblk hlt hr he hc hs hrun hw hh hfn hst hpc (fun y hy => ?_)
    (fun y hy => hwd _ (by omega) fun _ => by have := Nat.min_le_left C.k fn.frame; omega)
    (fun i hi hiN => hwd i hiN fun hk => by have := slot_lt_frameW hx hk; omega)
    (fun z hz hzk => by
      have hzK : z < C.k + C.c := by omega
      rw [hO.reg_get _ _ hzK, hO.reg_get _ _ hzK]; exact hreg z hzK (by omega)) hD c
  have := hL y hy
  rw [hfr]
  by_cases hyk : y < (C.k + C.c)
  · simp only [hyk, ite_true, hO.reg_get _ _ hyk] at this ⊢
    by_cases hyx : y = x
    · subst hyx; simp [Flat.Frame.set, hrx hyk]
    · simp only [Flat.Frame.set, hyx, ite_false]; rw [hreg y hyk hyx]; exact this
  · simp only [hyk, ite_false] at this ⊢
    by_cases hyx : y = x
    · subst hyx; simp [Flat.Frame.set, hslot (by omega)]
    · simp only [Flat.Frame.set, hyx, ite_false]; rw [hwd _ (by omega) fun _ => by omega]; exact this

/-- A block ending in `st x r`, a slot store or a copy into `x`'s register, is matched. The
instructions `pre` before it must run to a state that holds the value in `r`, keeps the other
location registers and every stack word but slot `x`, and has the next Lin heap in the data
region. The machine then reaches a state related to the Lin state at `pc + 1`. -/
theorem Laws.sim_st (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) {ω : Oracle} {s s' : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn}
    {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hok : D.fnOk fn = true) {b : List A.SInstr} (hblk : f.blocks[s.pc]? = some b)
    (hlt : s.pc < fn.code.length) {pre : List A.isa.Instr} {x : Nat} {r : O.Reg}
    (hx : x < fn.frame) (hr : O.stOk r)
    (hres : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b =
      some (pre ++ O.st x r))
    (hcode : SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b)
    (hpre : ∀ i ∈ pre, StraightC C abi ω i) {t : MState A.isa.Regs}
    (hrun : runIs abi ω pre m = some t) (hR : Region t.mem lo N)
    (hwd : ∀ i, i < N → ((C.k + C.c) ≤ x → i ≠ j + x - C.c) → word t.mem lo i = word m.mem lo i)
    (hreg : ∀ z, z < (C.k + C.c) → z ≠ x → O.get t.regs (O.preg z) = O.get m.regs (O.preg z))
    (hD : DataOk P σ lo t.mem s'.mem) (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hOk : O.Ok t)
    (hw : t.world = s'.world) (hh : s'.world.halted = false) (hfn : s'.fn = s.fn)
    (hst : s'.stack = s.stack) (hpc : s'.pc = s.pc + 1)
    (hfr : s'.frame = s.frame.set x (O.get t.regs r)) (c : Nat) :
    ∃ m', (M abi).run ω (m, c) (pre ++ O.st x r).length =
        some (m', c + (pre ++ O.st x r).length) ∧ MatchAt C P AP σ lo N s' m' fn f a j ∧
      RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs) (m, c) (pre ++ O.st x r).length := by
  have hroom := hM.room; unfold frameW at hroom
  obtain ⟨is, code, hr', hen, hc⟩ := hcode
  rw [hres] at hr'; cases hr'
  have hs := List.forall_mem_append.2 ⟨hpre, hO.straight_st ω x r hr⟩
  by_cases hxk : x < (C.k + C.c)
  · obtain ⟨t2, h2, hm2, hw2, hsp2, hv2, hk2⟩ := hO.run_stReg (ω := ω) (t := t) hxk hr
      (hw ▸ hh) hOk
    exact ⟨t2, hO.sim_set hl hil hM hblk hlt hres hen hc hs
      (by rw [runIs_append, hrun, Option.bind_some]; exact h2) (hw2.trans hw) hh hfn hst hpc hx hfr
      (fun i hi h => by rw [hm2]; exact hwd i hi h) (fun h => absurd hxk (by omega))
      (fun z hz hzx => by
        rw [hk2 _ fun h => hzx (hO.preg_inj z x hz hxk h)]; exact hreg z hz hzx)
      (fun _ => hv2) (hm2 ▸ hD) c⟩
  · obtain ⟨mem', hwr, -, hF, hval, hrest⟩ := writeWord_wa hR (show j + x - C.c < N by omega)
      (O.get t.regs r)
    obtain ⟨t2, h2, hm2, hw2, hsp2, hk2⟩ := hO.run_st (ω := ω) hM hok hr (by omega) hx hsp
      (hw ▸ hh) hOk hwr
    subst hm2
    exact ⟨t2, hO.sim_set hl hil hM hblk hlt hres hen hc hs
      (by rw [runIs_append, hrun, Option.bind_some]; exact h2) (hw2.trans hw) hh hfn hst hpc hx hfr
      (fun i hi h => by rw [hrest i hi (h (by omega))]; exact hwd i hi h) (fun _ => hval)
      (fun z hz hzx => (hk2 z hz).trans (hreg z hz hzx)) (fun h => absurd h hxk)
      (dataOk_keep (by have := hR.top; omega) hD hF
        (writeWord_wa_low hR (show j + x - C.c < N by omega) hwr)) c⟩

/-- A block that computes a value into `r` and ends in `fin k x r` is matched. When `x < k`, the
register `r` is the location's own and `fin` is empty. -/
theorem Laws.sim_fin (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) {ω : Oracle} {s s' : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn}
    {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hok : D.fnOk fn = true) {b : List A.SInstr} (hblk : f.blocks[s.pc]? = some b)
    (hlt : s.pc < fn.code.length) {pre : List A.isa.Instr} {x : Nat} {r : O.Reg}
    (hx : x < fn.frame) (hr : (C.k + C.c) ≤ x → O.stOk r) (hrx : x < (C.k + C.c) → r = O.preg x)
    (hres : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b =
      some (pre ++ O.fin (C.k + C.c) x r))
    (hcode : SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b)
    (hpre : ∀ i ∈ pre, StraightC C abi ω i) {t : MState A.isa.Regs}
    (hrun : runIs abi ω pre m = some t) (htm : t.mem = m.mem)
    (hreg : ∀ z, z < (C.k + C.c) → z ≠ x → O.get t.regs (O.preg z) = O.get m.regs (O.preg z))
    (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hOk : O.Ok t)
    (hw : t.world = s'.world) (hh : s'.world.halted = false) (hfn : s'.fn = s.fn)
    (hst : s'.stack = s.stack) (hpc : s'.pc = s.pc + 1)
    (hfr : s'.frame = s.frame.set x (O.get t.regs r)) (hmem : s'.mem = s.mem) (c : Nat) :
    ∃ m', (M abi).run ω (m, c) (pre ++ O.fin (C.k + C.c) x r).length =
        some (m', c + (pre ++ O.fin (C.k + C.c) x r).length) ∧ MatchAt C P AP σ lo N s' m' fn f a j ∧
      RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs) (m, c) (pre ++ O.fin (C.k + C.c) x r).length := by
  by_cases hxk : x < (C.k + C.c)
  · have hf : O.fin (C.k + C.c) x r = [] := by simp [fin, hxk]
    rw [hf] at hres ⊢
    obtain ⟨is, code, hr', hen, hc⟩ := hcode
    rw [hres] at hr'; cases hr'
    exact ⟨t, hO.sim_set hl hil hM hblk hlt hres hen hc (by simpa using hpre) (by simpa using hrun)
      hw hh hfn hst hpc hx hfr (fun i _ _ => by rw [htm]) (fun h => absurd hxk (by omega)) hreg
      (fun _ => by rw [← hrx hxk]) (htm ▸ hmem ▸ hM.data) c⟩
  · have hf : O.fin (C.k + C.c) x r = O.st x r := by simp [fin, hxk]
    rw [hf] at hres ⊢
    exact hO.sim_st hl hil hM hok hblk hlt hx (hr (by omega)) hres hcode hpre hrun
      (htm ▸ hM.region) (fun i _ _ => by rw [htm]) hreg (htm ▸ hmem ▸ hM.data) hsp hOk hw hh hfn
      hst hpc hfr c

/-- The facts every frame-local case starts from: the selected block, its code in memory and
the well-formedness of the instruction. -/
theorem case_start {asm : Asm.Assembler A} (hl : asm.Laws) (hsel : select D P = .ok AP)
    (hwf : P.Wf) {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A}
    {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j) {ins : Lin.Instr}
    (hi : fn.code[s.pc]? = some ins) {b : List A.SInstr} {d : List (String × List UInt8)}
    (hD : ∀ i, D.instr P i s.pc fn ins = .ok (b, d)) :
    D.fnOk fn = true ∧ f.blocks[s.pc]? = some b ∧
      SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b ∧
      ins.Wf P s.fn fn.frame fn.code.length := by
  obtain ⟨b', hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d', hsi, -⟩ := hC.instr
  rw [hD] at hsi; cases hsi
  exact ⟨hC.sel.ok, hC.blk, hC.code, hC.wf⟩

theorem frame_set_self (fr : Flat.Frame) (x : Nat) : fr.set x (fr x) = fr := by
  funext y; simp only [Flat.Frame.set]; split <;> simp_all

/-- The case `mov x o`. Its code loads the operand into `x`'s register, which is nothing and a
silent step for `mov x x`, or loads it with `src` and stores it into the slot. -/
theorem sim_mov (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) :
    StepOk abi C P AP σ lo N (cnt P) fun i => ∃ x o, i = .mov x o := by
  intro ω κ s s' m c fn f a j ins hM hi ⟨x, o, he⟩ hs
  subst he
  obtain ⟨rfl, -⟩ := step_getD hM hi hs
  obtain ⟨hok, hblk, hcode, hx, ho⟩ := case_start hl hsel hwf hM hi (hO.sel_mov P · s.pc fn x o)
  rw [hO.cnt_mov]
  have hsp : ∀ {t : MState A.isa.Regs} {n}, RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs)
      (m, c) n → RunAll abi ω (SpBound C P lo N) (m, c) n :=
    fun h => RunAll.mono (fun _ => spBound_of_keep hM) h
  have hlt := pc_lt hi
  by_cases hxk : x < (C.k + C.c)
  · have hb : O.movIs (C.k + C.c) x o = O.ld (O.preg x) o := by simp [movIs, hxk]
    rw [hb] at hcode hblk ⊢
    obtain ⟨t, h1, hm, hw, hsp1, -, hv, hk⟩ := hO.run_ld (ω := ω) hM hok (hO.ld_preg x hxk) ho rfl
      rfl hM.halted (hO.ok_match hM) ((Keeps.refl _).op _)
    obtain ⟨is, code, hr, hen, hc⟩ := hcode
    rw [hO.resolveAt_op] at hr; cases hr
    obtain ⟨r1, r2, r3⟩ := hO.sim_set (s' := (Lin.exec κ ω fn (.mov x o) s).getD s) hl hil hM hblk
      hlt (hO.resolveAt_op _ _) hen hc (hO.straight_ld ω _ o (hO.ld_preg x hxk)) h1
      (hw.trans hM.world) hM.run rfl rfl rfl hx rfl (fun i _ _ => by rw [hm])
      (fun h => absurd hxk (by omega))
      (fun z hz hzx => hk _ fun h => hzx (hO.preg_inj z x hz hxk h)) (fun _ => hv)
      (hm ▸ hM.data) c
    refine ⟨_, t, r1, Or.inl ⟨fn, f, a, j, r2⟩, fun h0 => ?_, hsp (t := t) r3, rfl⟩
    obtain rfl := hO.ld_nil x o hxk (List.eq_nil_of_length_eq_zero h0)
    exact ticksAt_self hM.hfn hi
  by_cases hxo : o = .slot x
  · subst hxo
    have hb : O.movIs (C.k + C.c) x (.slot x) = [] := by simp [movIs, hxk]
    rw [hb] at hblk ⊢
    refine ⟨_, m, rfl, Or.inl ⟨fn, f, a, j, matchAt_keep hM rfl rfl (frame_set_self _ _) rfl rfl
      rfl rfl rfl (by show s.pc + 1 ≤ _; omega) ?_ (fun _ _ => rfl) hM.regOk⟩,
      fun _ => ticksAt_self hM.hfn hi, RunAll.zero (spBound_of_keep hM rfl), rfl⟩
    rw [hM.rip, show ((Lin.exec κ ω fn (.mov x (.slot x)) s).getD s).pc = s.pc + 1 from rfl,
      labelOff_succ f hblk]; rfl
  · have hb : O.movIs (C.k + C.c) x o = (O.src O.r0 o).1 ++ O.st x (O.src O.r0 o).2 := by simp [movIs, hxk, hxo]
    rw [hb] at hcode hblk ⊢
    obtain ⟨t, h1, hm, hw, hsp1, hOk, hv, hk⟩ := hO.run_src (ω := ω) hM hok hO.ld0 ho rfl rfl
      hM.halted (hO.ok_match hM) ((Keeps.refl _).op _)
    obtain ⟨m', r1, r2, r3⟩ := hO.sim_st (s' := (Lin.exec κ ω fn (.mov x o) s).getD s) hl hil hM
      hok hblk hlt hx (hO.st_src o) (hO.resolveAt_op _ _) hcode (hO.straight_src ω _ o hO.ld0) h1
      (hm ▸ hM.region) (fun i _ _ => by rw [hm]) (fun z hz _ => hk _ (hO.ne_r0 z hz))
      (hm ▸ hM.data) hsp1 hOk (hw.trans hM.world) hM.run rfl rfl rfl (by rw [hv]; rfl) c
    exact ⟨_, m', r1, Or.inl ⟨fn, f, a, j, r2⟩,
      fun h => absurd h (by have := hO.st_pos x (O.src O.r0 o).2 (by omega); simp only [List.length_append]; omega),
      hsp (t := m') r3, rfl⟩

/-- The case `load w x o off`, whose code is the address code `memX`, `ldW w (dst x)` and
`fin x`. -/
theorem sim_load (hO : O.Laws abi C D cnt) (hX : O.MemLaws abi C D cnt) {asm : Asm.Assembler A}
    (hl : asm.Laws) (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) :
    LocalOk abi C P AP σ lo N (cnt P) fun i => ∃ w x a off, i = .load w x a off := by
  intro ω κ s m c fn f a j ins hM hi ⟨w, x, o, off, he⟩ hmo
  subst he
  obtain ⟨hok, hblk, ⟨is, code, hr, hen, hc⟩, hx, ho⟩ :=
    case_start hl hsel hwf hM hi (hX.sel_load P · s.pc fn w x o off)
  obtain ⟨Dm, hDm, hDlo, hDR⟩ := hM.data
  have hb : (o.eval s.frame + off).toNat + w.bytes ≤ P.mem := by
    simpa [Lin.Instr.memOk, Lin.inData] using hmo
  have htop := hM.region.top
  obtain ⟨pre, t, rfl, hlen, hpre, h1, hm1, hw1, hsp1, hOk1, hv1, hK1⟩ :=
    hX.run_memX (ω := ω) hM hok ho hDm hr hen
  obtain ⟨t₂, h2, hm2, hw2, hsp2, hOk2, hv2, hk2⟩ := hX.run_ldW (ω := ω) w x o off (hm1 ▸ hDR)
    (by omega) hb hv1 (hw1 ▸ hM.halted) hOk1
  rw [loadIs, ← List.append_assoc] at hr hen
  rw [hX.cnt_load, ← hlen]
  refine ⟨by have := hX.ldW_pos w (O.dst (C.k + C.c) x) o off; simp [loadIs]; omega, ?_⟩
  have hdx : x < (C.k + C.c) → O.dst (C.k + C.c) x = O.preg x := fun h => by simp [dst, h]
  obtain ⟨m', r1, r2, r3⟩ := hO.sim_fin (s' := (Lin.exec κ ω fn (.load w x o off) s).getD s)
    hl hil hM hok hblk (pc_lt hi) hx
    (fun h => by have hd : O.dst (C.k + C.c) x = O.r0 := (by simp [dst]; omega); rw [hd]; exact hO.st0)
    hdx hr ⟨_, _, hr, hen, hc⟩
    (List.forall_mem_append.2 ⟨hpre, hX.straight_ldW ω w _ o off (hO.ldOk_dst x)⟩)
    (by rw [runIs_append, h1, Option.bind_some, h2]) (hm2.trans hm1)
    (fun z hz hzx => by
      rw [hk2 z hz fun h => ?_]; exact hK1 z hz
      unfold dst at h; split at h
      · exact hzx (hO.preg_inj z x hz ‹_› h)
      · exact hO.ne_r0 z hz h)
    (hsp2.trans hsp1) hOk2 (hw2.trans (hw1.trans hM.world)) hM.run rfl rfl rfl
    (by rw [hv2]; rfl) rfl c
  simp only [loadIs, List.length_append, Nat.add_assoc] at r1 r3 ⊢
  exact ⟨m', r1, r2, r3⟩

/-- The case `store w o off o'`, whose code is the address code `memX`, `src r1 o'` and `stW w`.
Only bytes of the data region change. -/
theorem sim_store (hO : O.Laws abi C D cnt) (hX : O.MemLaws abi C D cnt) {asm : Asm.Assembler A}
    (hl : asm.Laws) (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) :
    LocalOk abi C P AP σ lo N (cnt P) fun i => ∃ w a off b, i = .store w a off b := by
  intro ω κ s m c fn f a j ins hM hi ⟨w, o, off, o', he⟩ hmo
  subst he
  obtain ⟨hok, hblk, ⟨is, code, hr, hen, hc⟩, ho⟩ :=
    case_start hl hsel hwf hM hi (hX.sel_store P · s.pc fn w o off o')
  obtain ⟨Dm, hDm, hDlo, hDR⟩ := hM.data
  have hb : (o.eval s.frame + off).toNat + w.bytes ≤ P.mem := by
    simpa [Lin.Instr.memOk, Lin.inData] using hmo
  have htop := hM.region.top
  have hroom := hM.room; unfold frameW at hroom
  obtain ⟨pre, t, rfl, hlen, hpre, h1, hm1, hw1, hsp1, hOk1, hv1, hK1⟩ :=
    hX.run_memX (ω := ω) hM hok (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy)) hDm hr hen
  obtain ⟨t₃, h3, hR', hF, hout, hw3, hsp3, hk3⟩ := hX.run_storeIs hO (ω := ω) hM hok w o off
    (fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)) hm1 hsp1 (hw1 ▸ hM.halted) hOk1 hK1
    (hm1 ▸ hDR) (by omega) hb hv1
  obtain ⟨hwd, hDok⟩ := hM.data_write hDm hR'
    (fun y hy => (high_of_out hDlo hb hout y hy).trans (by rw [hm1]))
  rw [hX.cnt_store, ← hlen]
  refine ⟨by have := hX.storeIs_pos w o off o'; omega, ?_⟩
  have hK : O.Keeps (C.k + C.c) m.regs t₃.regs := hK1.trans hk3
  obtain ⟨r1, r2, r3⟩ := sim_straight (s' := (Lin.exec κ ω fn (.store w o off o') s).getD s)
    hl hil hM hblk (pc_lt hi) hr hen hc
    (List.forall_mem_append.2 ⟨hpre, hX.straight_storeIs hO ω w o off o'⟩)
    (by rw [runIs_append, h1, Option.bind_some, h3])
    (hw3.trans (hw1.trans hM.world)) hM.run rfl rfl rfl
    (locsOk_congr (fun y hy _ => hwd _ (by omega))
      (locsOk_view (fun z hz => by rw [hO.reg_get _ _ hz, hO.reg_get _ _ hz]; exact hK z hz) hM.locs))
    (fun y _ => hwd _ (by have := Nat.min_le_right C.k fn.frame; omega)) (fun k _ hk => hwd k hk)
    (fun z _ hz => by
      have hzK : z < C.k + C.c := by omega
      rw [hO.reg_get _ _ hzK, hO.reg_get _ _ hzK]; exact hK z hzK) hDok c
  simp only [List.length_append] at r1 r3 ⊢
  exact ⟨_, r1, r2, r3⟩

end Ops

end Millipede.Sel
