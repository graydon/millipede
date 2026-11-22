import Millipede.Compile.AssembleProof
import Millipede.Target.SelExt
import Millipede.Target.PMove

import Millipede.Target.X64.Budget
import Millipede.Target.X64.MemData

/-!
# Correctness of x64 instruction selection

This module proves that the code the x64 selector emits for one Lin instruction behaves as the
instruction does, for any number `k ≤ 6` of register locations. Location `x < k` of the running
function lives in one of `rbx rbp r12 r13 r14 r15`, and every other location in a frame slot, so
`k = 0` keeps every location on the stack. The call sequence, the return and `main`'s entry are
proved in `SelectCall.lean`, which assembles all the cases into the laws of the shared simulation.

x64 is an instance of the operations shared by both ISAs, so this module defines `selOps k`, the
convention `conv k` and the relation `MatchAt` at that convention, and proves the laws the shared
proofs of moves, binary operations, loads, stores and system calls need. Each law also states how
many machine instructions the step takes, which is `instrs k c mb lvo P 0 0 fn ins`. Lin's memory is a
block of bytes below the stack region, and the stores of frames, calls and returns never touch it.

The main declarations are `binR_correct`, which says every Lin binary operation on registers has
a correct lowering, the operand fetches `run_ldTo` and `run_src`, `selOps_laws`, `selOps_ext`,
`sim_jmp` and `sim_jz`.

See doc/design/compiler.md.
-/

namespace Millipede.X64

variable {lvo : Option RegAlloc.LiveSets} {mb : Bool}

open Flat (Operand BinOp)

/- Rewriting must see through `isa.Regs` and `isa.Instr` to `Regs` and `Instr`, so `isa` is
reducible in this file only. -/
set_option allowUnsafeReducibility true in
attribute [local reducible] isa

open Sel

/-! ## Memory words

The stack region and its words are defined once for both ISAs. An x64 load or store of a word
is `Memory.readWord` or `writeWord` behind a check that the address is canonical, and every
address of the stack region passes that check. -/

theorem wa_canon {lo N k : Nat} (h : lo + 8 * N ≤ 2 ^ 47) (hk : k < N) :
    canonical (wa lo k) = true ∧ canonical (wa lo k + 7) = true := by
  constructor
  · apply canonical_lt; simp only [wa, UInt64.toNat_ofNat']; omega
  · apply canonical_lt
    rw [show (7 : UInt64) = UInt64.ofNat 7 from rfl, wa_add, UInt64.toNat_ofNat']; omega

theorem load64_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) :
    load64 m (wa lo k) = m.readWord (wa lo k) 8 := by
  obtain ⟨c1, c2⟩ := wa_canon hR.top hk
  simp only [load64, c1, c2, Bool.and_self, ite_true]

theorem store64_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) (v : UInt64) :
    store64 m (wa lo k) v = m.writeWord (wa lo k) 8 v := by
  obtain ⟨c1, c2⟩ := wa_canon hR.top hk
  simp only [store64, c1, c2, Bool.and_self, ite_true]

/-- A load of stack word `k` succeeds and returns the word. -/
theorem load_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) :
    load64 m (wa lo k) = some (word m lo k) := by
  rw [load64_wa hR hk, readWord_wa hR hk]

/-- A store to stack word `k` succeeds, keeps the region and the permissions, and changes that
word alone. -/
theorem store_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) (v : UInt64) :
    ∃ m', store64 m (wa lo k) v = some m' ∧ Region m' lo N ∧ Memory.Frame m m' ∧
      word m' lo k = v ∧ ∀ j, j < N → j ≠ k → word m' lo j = word m lo j := by
  rw [store64_wa hR hk]; exact writeWord_wa hR hk v

/-- A store at stack index `k` leaves every other region word's load unchanged. -/
theorem load_after_store {m m' : Memory} {lo N k j : Nat} (hR : Region m lo N) (hk : k < N)
    {v : UInt64} (hs : store64 m (wa lo k) v = some m') (hj : j < N) (hjk : j ≠ k) :
    load64 m' (wa lo j) = load64 m (wa lo j) := by
  obtain ⟨m'', hs', hR', _, _, hrest⟩ := store_wa hR hk v
  rw [hs] at hs'; cases hs'
  rw [load_wa hR' hj, load_wa hR hj, hrest j hj hjk]

/-- A store to a stack word leaves every byte below the stack region unchanged. -/
theorem store_wa_low {m m' : Memory} {lo N k : Nat} {v : UInt64} (hR : Region m lo N) (hk : k < N)
    (hs : store64 m (wa lo k) v = some m') : LowSame lo m m' :=
  writeWord_wa_low hR hk (store64_wa hR hk v ▸ hs)

/-! ## Straight-line runs -/

/-- The x64 machine with Linux system calls. -/
abbrev M : Sem := Asm.msem isa linux

/-- An instruction's length in `Sel.runIs` is its encoding's. -/
@[simp] theorem ilen_eq (i : Instr) : Sel.ilen (A := arch) i = (encode i).length := rfl

/-- One machine step executes the instruction encoded at `rip`. -/
theorem step_exec {ω : Oracle} {s s' : State} {i : Instr} {c : Nat}
    (hh : s.world.halted = false) (hc : s.mem.CodeAt s.regs.rip (encode i))
    (he : exec (linux.trap ω) i (encode i).length s = some s') :
    M.step ω (s, c) = some (s', c + 1) :=
  Sel.step_exec (A := arch) linux laws hh rfl hc he

/-- Every state of the run `t, run t 1, …, run t n` satisfies `Q`. -/
abbrev RunAll (ω : Oracle) (Q : State → Prop) (t : M.State) (n : Nat) : Prop :=
  Sel.RunAll (A := arch) linux ω Q t n

/-! ### The stack pointer along runs -/

/-- Whether the instruction leaves `rsp` alone. `syscall` does, because it writes only `rax`,
`rcx` and `r11`. -/
def Instr.keepsSp (i : Instr) : Bool := !(i.writes.contains .rsp)

theorem Instr.keepsSp_iff (i : Instr) : i.keepsSp = true ↔ .rsp ∉ i.writes := by
  simp [Instr.keepsSp]

/- With these lemmas and those about `ldI`, `ldW` and `stW` below, `simp` proves
`∀ i ∈ is, i.branches = false ∧ i.keepsSp = true` for a concrete list `is`. They are the
equations of `Instr.writes` rather than its definition, so that `simp` does not unfold the
writes of a helper such as `ldI r o` into a stuck `match`. -/
attribute [local simp] Instr.keepsSp_iff Instr.branches.eq_5 Alu.writes Instr.writes.eq_1
  Instr.writes.eq_2 Instr.writes.eq_3 Instr.writes.eq_4 Instr.writes.eq_5 Instr.writes.eq_6
  Instr.writes.eq_7 Instr.writes.eq_8 Instr.writes.eq_9 Instr.writes.eq_10 Instr.writes.eq_11
  Instr.writes.eq_12 Instr.writes.eq_13 Instr.writes.eq_14 Instr.writes.eq_15 Instr.writes.eq_16
  Instr.writes.eq_17 Instr.writes.eq_18 Instr.writes.eq_19 Instr.writes.eq_20 Instr.writes.eq_21

theorem exec_keepsSp {ω : Oracle} {i : Instr} {n : Nat} {s s' : State} (hk : i.keepsSp = true)
    (h : exec (linux.trap ω) i n s = some s') : s'.regs.gpr .rsp = s.regs.gpr .rsp := by
  by_cases hi : i = .syscall
  · subst hi
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp only [Abi.trap] at ht
    split at ht
    · obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp ht
      simp [State.withRegs, Regs.set, linux]
    · cases ht
  · exact exec_gpr hi h .rsp (by simpa [Instr.keepsSp] using hk)
/-- `rsp` points at a stack word between `lo'` and the top `N`. -/
def SpIn (lo N lo' : Nat) (x : State) : Prop := ∃ i, lo' ≤ i ∧ i ≤ N ∧ x.regs.gpr .rsp = wa lo i
/-- Instructions at `rip` in W^X memory that neither branch nor write `rsp` run one per machine
step. Memory changes only by stores and stays W^X, and `rsp` keeps its value in every
intermediate state. For a concrete list, `simp` discharges the side condition on the
instructions. -/
theorem run_straight {ω : Oracle} {is : List Instr} {s s' : State} (c : Nat)
    (hwx : s.mem.WxorX) (hc : s.mem.CodeAt s.regs.rip (is.flatMap encode))
    (hs : ∀ i ∈ is, i.branches = false ∧ i.keepsSp = true) (h : runIs (A := arch) linux ω is s = some s') :
    M.run ω (s, c) is.length = some (s', c + is.length) ∧ Memory.Frame s.mem s'.mem ∧
      s'.mem.WxorX ∧ s'.regs.rip = s.regs.rip + UInt64.ofNat (is.flatMap encode).length ∧
      RunAll ω (fun x => x.regs.gpr .rsp = s.regs.gpr .rsp) (s, c) is.length :=
  Sel.run_straight (A := arch) laws c hwx (encodeAll_eq is) hc
    (fun i hi _ _ hx => ⟨exec_rip (hs i hi).1 hx, exec_keepsSp (hs i hi).2 hx⟩)
    h

/- These are proved by `simp` rather than by `rfl`, because as `dsimp` steps their proofs would
not check at reducible transparency when `simp` discharges a hypothesis such as `t.mem = m.mem`
of `exec_ldI_of`. -/
@[simp] theorem State.withRegs_mem (s : State) (r : Regs) : (s.withRegs r).mem = s.mem := by
  simp [State.withRegs]
@[simp] theorem State.withRegs_world (s : State) (r : Regs) : (s.withRegs r).world = s.world := by
  simp [State.withRegs]
@[simp] theorem State.withRegs_regs (s : State) (r : Regs) : (s.withRegs r).regs = r := by
  simp [State.withRegs]

/-! ## Primitive lowerings -/

@[simp] theorem sext32_zero : sext32 0 = 0 := by decide
@[simp] theorem sext32_one : sext32 1 = 1 := by decide

theorem low_byte (v : UInt64) (c : Bool) :
    ((v &&& ~~~255) ||| (if c then 1 else 0)) &&& 255 = if c then 1 else 0 := by
  apply UInt64.toBitVec_inj.mp
  cases c <;> simp <;> ext i hi <;> simp [BitVec.getElem_and, BitVec.getElem_or] <;>
    generalize v.toBitVec[i] = b <;> revert b <;> revert i <;> decide

@[simp] theorem low_byte_one (v : UInt64) : ((v &&& ~~~255) ||| 1) &&& 255 = 1 := low_byte v true
@[simp] theorem low_byte_zero (v : UInt64) : (v &&& ~~~255) &&& 255 = 0 := by
  have := low_byte v false; simpa using this

theorem sub_eq_zero' {a b : UInt64} : a - b = 0 ↔ a = b :=
  ⟨fun h => by rw [← UInt64.sub_add_cancel a b, h, UInt64.zero_add],
   fun h => by rw [h, UInt64.sub_self]⟩

theorem cond_cmp (a b : UInt64) :
    Cond.eval (Alu.eval .cmp a b).2 .e = decide (a = b) ∧
    Cond.eval (Alu.eval .cmp a b).2 .ne = !decide (a = b) ∧
    Cond.eval (Alu.eval .cmp a b).2 .b = decide (a < b) ∧
    Cond.eval (Alu.eval .cmp a b).2 .be = decide (a ≤ b) := by
  by_cases h : a = b
  · subst h; simp [Alu.eval, flagsOf, Cond.eval]
  · have hz : (a - b == 0) = false := by simp [sub_eq_zero', h]
    have hn : a.toNat ≠ b.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp only [Alu.eval, flagsOf, Cond.eval, hz, h]
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
    by_cases hl : a.toNat < b.toNat
    · simp [hl, Nat.le_of_lt hl]
    · simp [hl]; omega

theorem mask63 (y : UInt64) : (y &&& 63) % 64 = y % 64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mod, UInt64.toNat_and]
  have : (63 : UInt64).toNat = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- x64 masks a shift count to 6 bits, as Lean's `UInt64` shifts do. -/
theorem shl_mask (x y : UInt64) : x <<< (y &&& 63) = x <<< y := by
  rw [UInt64.shiftLeft_eq_shiftLeft_mod x (y &&& 63), UInt64.shiftLeft_eq_shiftLeft_mod x y,
    mask63]

theorem shr_mask (x y : UInt64) : x >>> (y &&& 63) = x >>> y := by
  rw [UInt64.shiftRight_eq_shiftRight_mod x (y &&& 63), UInt64.shiftRight_eq_shiftRight_mod x y,
    mask63]
/-- With the operands in `rax` and `rcx`, the sequence `binCode op` leaves `BinOp.eval op x y` in
its result register, keeps `rsp`, and changes neither memory nor the world. -/
theorem binCode_correct (ω : Oracle) (op : BinOp) (s : State) (x y : UInt64)
    (hx : s.regs.gpr .rax = x) (hy : s.regs.gpr .rcx = y) (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (binCode op).1 s = some s' ∧ s'.regs.gpr (binCode op).2 = op.eval x y ∧
      s'.regs.gpr .rsp = s.regs.gpr .rsp ∧ s'.mem = s.mem ∧ s'.world = s.world := by
  have hc := cond_cmp x y
  simp only [Alu.eval] at hc
  have hxl : x.toNat < 18446744073709551616 := x.toNat_lt
  have hq : x.toNat / y.toNat < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt
  cases op
  case udiv =>
    by_cases hy0 : y = 0
    · subst hy0
      simp [binCode, runIs, exec, State.withRegs, Alu.eval, Alu.writes, hx, hy, hh, BinOp.eval,
        flagsOf, Cond.eval, Regs.set, -UInt64.toNat_and, -UInt64.toNat_or, -UInt64.toNat_xor,
        -UInt64.toNat_mul]
    · have hy' : y.toNat ≠ 0 := fun e => hy0 (UInt64.toNat_inj.mp (by simpa using e))
      simp [binCode, runIs, exec, State.withRegs, Alu.eval, Alu.writes, hx, hy, hh, BinOp.eval,
        flagsOf, Cond.eval, hy0, Regs.set, -UInt64.toNat_and, -UInt64.toNat_or,
        -UInt64.toNat_xor, -UInt64.toNat_mul, hy', hxl, hq, udiv_ofNat]
  case umod =>
    by_cases hy0 : y = 0
    · subst hy0
      simp [binCode, runIs, exec, State.withRegs, Alu.eval, Alu.writes, hx, hy, hh, BinOp.eval,
        flagsOf, Cond.eval, Regs.set, -UInt64.toNat_and, -UInt64.toNat_or, -UInt64.toNat_xor,
        -UInt64.toNat_mul, hxl]
    · have hy' : y.toNat ≠ 0 := fun e => hy0 (UInt64.toNat_inj.mp (by simpa using e))
      simp [binCode, runIs, exec, State.withRegs, Alu.eval, Alu.writes, hx, hy, hh, BinOp.eval,
        flagsOf, Cond.eval, hy0, Regs.set, -UInt64.toNat_and, -UInt64.toNat_or,
        -UInt64.toNat_xor, -UInt64.toNat_mul, hy', hxl, hq, udiv_ofNat, umod_eq]
  all_goals simp [binCode, runIs, exec, State.withRegs, Alu.eval, Alu.writes, hx, hy, hh,
    BinOp.eval, Regs.set, -UInt64.toNat_and, -UInt64.toNat_or, -UInt64.toNat_xor,
    -UInt64.toNat_mul]
  case shl =>
    split
    · rename_i h0
      have : x <<< y = x := by rw [← shl_mask, h0, UInt64.shiftLeft_zero]
      simp [this, hx]
    · simp [Shift.eval, shl_mask]
  case shr =>
    split
    · rename_i h0
      have : x >>> y = x := by rw [← shr_mask, h0, UInt64.shiftRight_zero]
      simp [this, hx]
    · simp [Shift.eval, shr_mask]
  all_goals rw [low_byte]
  all_goals simp only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  all_goals by_cases hxy : x = y <;> simp [hxy]

/-! ## Displacements and branch targets -/

theorem sext32_ofNat {n : Nat} (h : n < 2 ^ 31) : sext32 (UInt32.ofNat n) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [sext32, UInt64.toNat_ofBitVec, UInt64.toNat_ofNat']
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp; omega
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega

theorem sext32_neg {n : Nat} (h0 : 0 < n) (h : n ≤ 2 ^ 31) :
    sext32 (0 - UInt32.ofNat n) = 0 - UInt64.ofNat n := by
  have e32 : (0 - UInt32.ofNat n).toNat = 2 ^ 32 - n := by
    rw [UInt32.toNat_sub, UInt32.toNat_ofNat']; simp; omega
  apply UInt64.toNat_inj.mp
  simp only [sext32, UInt64.toNat_ofBitVec]
  rw [BitVec.toNat_signExtend]
  have hm : (0 - UInt32.ofNat n).toBitVec.msb = true := by
    cases hb : (0 - UInt32.ofNat n).toBitVec.msb
    · rw [BitVec.msb_eq_false_iff_two_mul_lt] at hb
      simp only [UInt32.toNat_toBitVec, e32] at hb; omega
    · rfl
  rw [hm, BitVec.toNat_setWidth, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp only [UInt32.toNat_toBitVec, e32, ite_true]
  simp; omega

theorem sext32_ofInt {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    sext32 (UInt32.ofInt v) = UInt64.ofInt v := by
  rcases Int.lt_or_le v 0 with hv | hv
  · obtain ⟨n, rfl⟩ : ∃ n : Nat, v = -(n : Int) := ⟨v.natAbs, by omega⟩
    have e1 : UInt32.ofInt (-(n : Int)) = 0 - UInt32.ofNat n := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub, UInt32.toNat_ofNat']
      simp only [UInt32.ofInt, UInt32.toNat_ofNat']
      simp; omega
    have e2 : UInt64.ofInt (-(n : Int)) = 0 - UInt64.ofNat n := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub, UInt64.toNat_ofNat']
      simp only [UInt64.ofInt, UInt64.toNat_ofNat']
      simp; omega
    rw [e1, e2, sext32_neg (by omega) (by omega)]
  · obtain ⟨n, rfl⟩ : ∃ n : Nat, v = (n : Int) := ⟨v.toNat, by omega⟩
    have e1 : UInt32.ofInt (n : Int) = UInt32.ofNat n := by
      simp only [UInt32.ofInt]; congr 1; omega
    have e2 : UInt64.ofInt (n : Int) = UInt64.ofNat n := by
      simp only [UInt64.ofInt]
      apply UInt64.toNat_inj.mp; simp only [UInt64.toNat_ofNat']; omega
    rw [e1, e2, sext32_ofNat (by omega)]

/-- A resolved rel32 field reaches its target. -/
theorem rel32_spec {t n : UInt64} {r : UInt32} (h : rel32 t n = some r) : n + sext32 r = t := by
  simp only [rel32] at h
  split at h
  · rename_i hr
    cases h
    rw [sext32_ofInt hr.1 hr.2]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]
    simp only [UInt64.ofInt, UInt64.toNat_ofNat']
    have := t.toNat_lt
    have := n.toNat_lt
    omega
  · cases h

/-- `[rsp + 8x]` is stack word `j + x`. -/
theorem slot_addr {lo j x : Nat} (hx : 8 * x < 2 ^ 31) :
    wa lo j + sext32 (UInt32.ofNat (8 * x)) = wa lo (j + x) := by
  rw [sext32_ofNat hx, wa_add]; simp [wa, Nat.mul_add, Nat.add_assoc]

/-- `[rsp + 8(x - c)]` is the word of slot `x ≥ c`, which is `j + x - c`. -/
theorem slotW_addr {lo j x c : Nat} (hx : 8 * (x - c) < 2 ^ 31) (hc : c ≤ x) :
    wa lo j + sext32 (UInt32.ofNat (8 * (x - c))) = wa lo (j + x - c) := by
  rw [slot_addr hx, show j + (x - c) = j + x - c by omega]

/-- `[rsp - n]` is stack word `j - n/8`. -/
theorem below_addr {lo j k : Nat} (hk : 0 < k) (hk' : 8 * k ≤ 2 ^ 31) (hj : k ≤ j) :
    wa lo j + sext32 (0 - UInt32.ofNat (8 * k)) = wa lo (j - k) := by
  rw [sext32_neg (by omega) hk']
  apply UInt64.toNat_inj.mp
  simp only [wa, UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_zero]
  omega

variable {P : Lin.Prog}

/-! ## Where the code is -/
/-- A sequence placed in memory resolves to instructions whose x64 encoding sits at its
address. -/
theorem seqAt_x64 {m : Memory} {ρ : Asm.Ref → Option UInt64} {a : UInt64} {b : List SI}
    (h : Sel.SeqAt (A := arch) m ρ a b) :
    ∃ ins : List Instr, Asm.resolveAt arch ρ a b = some ins ∧ m.CodeAt a (ins.flatMap encode) := by
  obtain ⟨ins, code, hr, he, hc⟩ := h
  rw [encodeAll_eq] at he; cases he
  exact ⟨ins, hr, hc⟩

/-! ## The simulation relation

The relation is the shared frame relation at x64's convention `conv k`. A `call` pushes the
return address right above the callee's slots, so the caller's frame starts one word after the
callee's. `main`'s frame ends at the top of the stack, and the depth counts the return address of
`main`'s own call as 8 bytes. Location `x < k + c` of the running activation is the register
`loc k x`, and a call destroys the caller-saved ones, `k ≤ x`. -/

/-- x64's frame convention with `k` preserved and `c` caller-saved register locations. -/
def conv (k c : Nat) : Sel.Conv arch where
  φ := φ.words k c
  next F := Sel.frameW k c F + 1
  last F := Sel.frameW k c F
  retOff P i pc g args d := Asm.seqSize arch (ops (callOps k c (Sel.calleeFrame P g) args
    (RegAlloc.Live.callKeep (RegAlloc.Live.of P) P i pc g d args)
    (RegAlloc.Live.liveIn (RegAlloc.Live.of P) g 0))) + 5
  dtop := 8
  ok _ _ _ := True
  fnAddr _ := True
  k := k
  reg := fun (r : Regs) x => r.gpr (loc k x)
  c := c
  kill := (cls k c).across
  next_gt F := Nat.lt_succ_self _
  last_ge F := Nat.le_refl _

@[simp] theorem conv_k (k c : Nat) : (conv k c).k = k := rfl

@[simp] theorem conv_c (k c : Nat) : (conv k c).c = c := rfl

/-- The simulation relation between a Lin state and an x64 state, with `k` register
locations. -/
abbrev MatchAt (k c : Nat) (P : Lin.Prog) (A : Asm.Prog arch) (σ : String → Option UInt64)
    (lo N : Nat) :=
  Sel.MatchAt (A := arch) (conv k c) P A σ lo N

/-! ### The registers of the locations -/

/-- The registers that are no location's. They are the scratch registers `rax rcx`, `r11`, which
`syscall` overwrites, and `rsp`. -/
def Reg.notLoc (r : Reg) : Bool :=
  r ∈ [Reg.rax, .rcx, .r11, .rsp]

theorem preg_ne {x : Nat} {r : Reg} (hr : r.notLoc = true) : preg x ≠ r := by
  intro h; subst h
  unfold preg at hr; split at hr <;> simp [Reg.notLoc] at hr

theorem preg_inj {x y : Nat} (hx : x < maxK) (hy : y < maxK) (h : preg x = preg y) : x = y := by
  have : ∀ a b : Fin 6, preg a = preg b → a = b := by decide
  exact congrArg Fin.val (this ⟨x, hx⟩ ⟨y, hy⟩ h)

/-- The bounds on the numbers of locations. -/
abbrev KC (k c : Nat) : Prop := k ≤ maxK ∧ c ≤ maxC

theorem loc_of_lt {k x : Nat} (hx : x < k) : loc k x = preg x := by simp [loc, hx]

theorem creg_ne {i : Nat} {r : Reg} (hr : r.notLoc = true) : creg i ≠ r := by
  intro h; subst h; unfold creg at hr; split at hr <;> simp [Reg.notLoc] at hr

theorem loc_ne {k x : Nat} {r : Reg} (hr : r.notLoc = true) : loc k x ≠ r := by
  unfold loc; split
  · exact preg_ne hr
  · exact creg_ne hr

theorem preg_ne_creg (x i : Nat) : preg x ≠ creg i := by
  unfold preg creg; split <;> split <;> decide

theorem creg_inj {i j : Nat} (hi : i < maxC) (hj : j < maxC) (h : creg i = creg j) : i = j := by
  have : ∀ a b : Fin 6, creg a = creg b → a = b := by decide
  exact congrArg Fin.val (this ⟨i, hi⟩ ⟨j, hj⟩ h)

theorem loc_inj {k c x y : Nat} (hk : KC k c) (hx : x < k + c) (hy : y < k + c)
    (h : loc k x = loc k y) : x = y := by
  obtain ⟨hk, hc⟩ := hk; simp only [maxK, maxC] at hk hc
  unfold loc at h
  split at h <;> split at h
  · exact preg_inj (by unfold maxK; omega) (by unfold maxK; omega) h
  · exact absurd h (preg_ne_creg _ _)
  · exact absurd h.symm (preg_ne_creg _ _)
  · have := creg_inj (by unfold maxC; omega) (by unfold maxC; omega) h; omega

/-- A preserved location's register is no caller-saved location's. -/
theorem preg_ne_loc {k x y : Nat} (hy : k ≤ y) : preg x ≠ loc k y := by
  unfold loc; split
  · omega
  · exact preg_ne_creg _ _

@[simp] theorem preg_ne_rsp (x : Nat) : preg x ≠ .rsp := preg_ne rfl
@[simp] theorem preg_ne_rax (x : Nat) : preg x ≠ .rax := preg_ne rfl
@[simp] theorem preg_ne_rcx (x : Nat) : preg x ≠ .rcx := preg_ne rfl
@[simp] theorem loc_ne_rsp (k x : Nat) : loc k x ≠ .rsp := loc_ne rfl
@[simp] theorem loc_ne_rax (k x : Nat) : loc k x ≠ .rax := loc_ne rfl
@[simp] theorem loc_ne_rcx (k x : Nat) : loc k x ≠ .rcx := loc_ne rfl

theorem preg_ne_retReg (x i : Nat) : preg x ≠ retReg i := by
  unfold preg retReg retRegs; split <;> (rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp)

/-- The location of caller-saved register `i`: a location whose register is `creg i` is `k + i`. -/
theorem loc_eq_creg {k c x i : Nat} (hk : KC k c) (hx : x < k + c) (hi : i < maxC)
    (h : loc k x = creg i) : x = k + i := by
  obtain ⟨-, hc⟩ := hk
  unfold loc at h
  split at h
  · exact absurd h (preg_ne_creg _ _)
  · have := creg_inj (by unfold maxC at hc ⊢; omega) hi h; omega

/-- The scratch registers of selected code are `rax rcx`. -/
def Reg.scratch (r : Reg) : Bool := r ∈ [Reg.rax, .rcx]

/-- The registers `binR op` writes besides its destination and the scratch registers: `rdx` for a
division, `rdi rsi rdx` for a remainder. -/
def binKill : BinOp → List Reg
  | .udiv => [.rdx]
  | .umod => [.rdi, .rsi, .rdx]
  | _ => []

theorem binKill_ne_rsp {op : BinOp} {r : Reg} (h : r ∈ binKill op) : r ≠ .rsp := by
  cases op <;> simp [binKill] at h <;> (try rcases h with rfl | rfl | rfl) <;> (try subst h) <;> decide

theorem scratch_ne_rsp {r : Reg} (h : r.scratch = true) : r ≠ .rsp := by
  revert h; cases r <;> decide

/-- A location in `rdi`, `rsi` or `rdx` is caller-saved location `k + 3`, `k + 4` or `k + 5`. -/
theorem loc_fix {k c x : Nat} (hk : KC k c) (hx : x < k + c) (h : loc k x ∈ fixRegs) :
    ∃ i, (i = 3 ∨ i = 4 ∨ i = 5) ∧ x = k + i ∧ i < c := by
  simp only [fixRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · have := loc_eq_creg (i := 3) hk hx (by decide) h; exact ⟨3, by omega, this, by omega⟩
  · have := loc_eq_creg (i := 4) hk hx (by decide) h; exact ⟨4, by omega, this, by omega⟩
  · have := loc_eq_creg (i := 5) hk hx (by decide) h; exact ⟨5, by omega, this, by omega⟩

/-- A location in a register that a division or remainder destroys is in the clobber set of
every such `bin`. -/
theorem kill_bin {k c : Nat} (hk : KC k c) {op : BinOp} {x : Nat} (hx : x < k + c)
    (h : loc k x ∈ binKill op) : k ≤ x ∧ ∀ y a b, (conv k c).kill (.bin op y a b) x = true := by
  have hf : loc k x ∈ fixRegs := by
    cases op <;> simp only [binKill, List.mem_cons, List.not_mem_nil, or_false] at h <;>
      simp [fixRegs, h] <;> rcases h with h | h | h <;> simp [h]
  obtain ⟨i, hi, rfl, hic⟩ := loc_fix hk hx hf
  refine ⟨by omega, fun y a b => ?_⟩
  have e : loc k (k + i) = creg i := by
    unfold loc; rw [ite_eq_right_iff.2 fun h => absurd h (by omega)]; congr 1; omega
  rw [e] at h
  rcases hi with rfl | rfl | rfl <;> cases op <;> simp [binKill, creg] at h <;>
    simp [conv, RegAlloc.Alloc.Classes.across, cls, List.mem_filter, hic]

/-- A location in a system-call register is caller-saved and in every extern call's clobber
set. -/
theorem kill_ext {k c : Nat} (hk : KC k c) {x : Nat} (hx : x < k + c) (h : loc k x ∈ fixRegs) :
    k ≤ x ∧ ∀ sym nr y args, (conv k c).kill (.ext sym nr y args) x = true := by
  obtain ⟨i, hi, rfl, hic⟩ := loc_fix hk hx h
  refine ⟨by omega, fun _ _ _ _ => ?_⟩
  rcases hi with rfl | rfl | rfl <;>
    simp [conv, RegAlloc.Alloc.Classes.across, cls, List.mem_filter, hic]

theorem retReg_ne_rsp (i : Nat) : retReg i ≠ .rsp := by
  unfold retReg; rw [List.getD_eq_getElem?_getD]
  cases h : retRegs[i]? with
  | none => decide
  | some r =>
    have hall : ∀ r ∈ retRegs, r ≠ .rsp := by decide
    exact hall r (List.mem_of_getElem? h)

theorem retReg_ne_r11 (i : Nat) : retReg i ≠ .r11 := by
  unfold retReg; rw [List.getD_eq_getElem?_getD]
  cases h : retRegs[i]? with
  | none => decide
  | some r =>
    have hall : ∀ r ∈ retRegs, r ≠ .r11 := by decide
    exact hall r (List.mem_of_getElem? h)

theorem retReg_inj {a b : Nat} (ha : a < 8) (hb : b < 8) (h : retReg a = retReg b) : a = b := by
  have : ∀ a b : Fin 8, retReg a = retReg b → a = b := by decide
  exact congrArg Fin.val (this ⟨a, ha⟩ ⟨b, hb⟩ h)


/-! ### Runs: what straight-line code leaves alone -/

/-- A run of instructions other than `syscall` leaves the world unchanged, and every register
that no instruction writes. When no instruction stores, it leaves memory unchanged too. -/
theorem runIs_frame {ω : Oracle} : ∀ {is : List Instr} {s s' : State}, (∀ i ∈ is, i ≠ .syscall) →
    runIs (A := arch) linux ω is s = some s' →
    s'.world = s.world ∧ (∀ r, (∀ i ∈ is, r ∉ i.writes) → s'.regs.gpr r = s.regs.gpr r) ∧
      ((∀ i ∈ is, i.stores = false) → s'.mem = s.mem)
  | [], _, _, _, h => by cases h; exact ⟨rfl, fun _ _ => rfl, fun _ => rfl⟩
  | i :: is, s, s', hs, h => by
    simp only [runIs] at h
    split at h
    · cases h
    · obtain ⟨t, ht, h'⟩ := Option.bind_eq_some_iff.1 h
      have hi := hs i List.mem_cons_self
      obtain ⟨w, g, mm⟩ := runIs_frame (fun i' h => hs i' (List.mem_cons_of_mem _ h)) h'
      refine ⟨w.trans (exec_world hi ht), fun r hr => (g r fun i' h => hr i' (List.mem_cons_of_mem _ h)).trans
        (exec_gpr hi ht r (hr i List.mem_cons_self)), fun hst => (mm fun i' h => hst i' (List.mem_cons_of_mem _ h)).trans
        (exec_mem hi (hst i List.mem_cons_self) ht)⟩

/-- One instruction as a run. -/
theorem runIs_one {ω : Oracle} {i : Instr} {t t' : State} (hh : t.world.halted = false)
    (he : exec (linux.trap ω) i (encode i).length t = some t') :
    runIs (A := arch) linux ω [i] t = some t' := by
  rw [runIs_cons (A := arch) linux hh he, runIs_nil]

/-- The state after an instruction of length `n` that sets `r` to `v` and falls through. -/
def State.upd (t : State) (r : Reg) (v : UInt64) (n : Nat) : State :=
  t.withRegs { t.regs.set r v with rip := t.regs.rip + UInt64.ofNat n }

@[simp] theorem State.upd_mem (t : State) (r : Reg) (v : UInt64) (n : Nat) :
    (t.upd r v n).mem = t.mem := rfl
@[simp] theorem State.upd_world (t : State) (r : Reg) (v : UInt64) (n : Nat) :
    (t.upd r v n).world = t.world := rfl
@[simp] theorem State.upd_gpr (t : State) (r r' : Reg) (v : UInt64) (n : Nat) :
    (t.upd r v n).regs.gpr r' = if r' = r then v else t.regs.gpr r' := by
  simp [State.upd, Regs.set]

/-- `upd` keeps memory, the world and `rsp`, sets `r` to `v` and keeps every other register. -/
theorem upd_facts {t : State} {r : Reg} (hr : r ≠ .rsp) (v : UInt64) (n : Nat) :
    (t.upd r v n).mem = t.mem ∧ (t.upd r v n).world = t.world ∧
      (t.upd r v n).regs.gpr .rsp = t.regs.gpr .rsp ∧ (t.upd r v n).regs.gpr r = v ∧
      ∀ r', r' ≠ r → (t.upd r v n).regs.gpr r' = t.regs.gpr r' :=
  ⟨rfl, rfl, by simp [Ne.symm hr], by simp, fun r' h => by simp [h]⟩

/-- `mov d, r` copies `r` into `d` and falls through. -/
theorem exec_mv {trap : State → Option State} {t : State} {d r : Reg} {n : Nat} :
    exec trap (.movRR d r) n t = some (t.upd d (t.regs.gpr r) n) := rfl

/-! These lemmas let `simp` execute the register instructions without unfolding `exec`, so that
`exec` of a helper such as `ldI r o` is left for its own lemma. -/
section ExecSimp
variable {trap : State → Option State} {s : State} {n : Nat} {d r : Reg}

@[simp] theorem exec_movRI (v : UInt64) : exec trap (.movRI d v) n s =
    some (s.withRegs { s.regs.set d v with rip := s.regs.rip + UInt64.ofNat n }) := rfl
@[simp] theorem exec_movRR : exec trap (.movRR d r) n s =
    some (s.withRegs { s.regs.set d (s.regs.gpr r) with rip := s.regs.rip + UInt64.ofNat n }) := rfl
@[simp] theorem exec_lea (x : Mem) : exec trap (.lea d x) n s =
    some (s.withRegs { s.regs.set d (x.addr s.regs (s.regs.rip + UInt64.ofNat n)) with
      rip := s.regs.rip + UInt64.ofNat n }) := rfl
@[simp] theorem exec_aluRR (op : Alu) : exec trap (.aluRR op d r) n s =
    some (s.withRegs ⟨(if op.writes then s.regs.set d (op.eval (s.regs.gpr d) (s.regs.gpr r)).1
      else s.regs).gpr, s.regs.rip + UInt64.ofNat n, (op.eval (s.regs.gpr d) (s.regs.gpr r)).2⟩) :=
  rfl
@[simp] theorem exec_aluRI (op : Alu) (v : UInt32) : exec trap (.aluRI op d v) n s =
    some (s.withRegs ⟨(if op.writes then s.regs.set d (op.eval (s.regs.gpr d) (sext32 v)).1
      else s.regs).gpr, s.regs.rip + UInt64.ofNat n, (op.eval (s.regs.gpr d) (sext32 v)).2⟩) :=
  rfl
@[simp] theorem exec_setcc (c : Cond) : exec trap (.setcc c d) n s =
    some (s.withRegs { s.regs.set d ((s.regs.gpr d &&& ~~~0xFF) |||
      (if c.eval s.regs.flags then 1 else 0)) with rip := s.regs.rip + UInt64.ofNat n }) := rfl
@[simp] theorem exec_load (x : Mem) : exec trap (.load d x) n s =
    (load64 s.mem (x.addr s.regs (s.regs.rip + UInt64.ofNat n))).bind fun v =>
      some (s.withRegs { s.regs.set d v with rip := s.regs.rip + UInt64.ofNat n }) := rfl
@[simp] theorem exec_movzx : exec trap (.movzx d r) n s =
    some (s.withRegs { s.regs.set d (s.regs.gpr r &&& 0xFF) with
      rip := s.regs.rip + UInt64.ofNat n }) := rfl

end ExecSimp

theorem resolveAt_ops {ρ : Asm.Ref → Option UInt64} :
    ∀ (is : List Instr) (a : UInt64), Asm.resolveAt arch ρ a (is.map SI.op) = some is
  | [], _ => rfl
  | i :: is, _ => Asm.resolveAt_cons_some (A := arch) (i := SI.op i) rfl (resolveAt_ops is _)

theorem resolveAt_ops_inv {ρ : Asm.Ref → Option UInt64} {is ins : List Instr} {a : UInt64}
    (h : Asm.resolveAt arch ρ a (is.map SI.op) = some ins) : ins = is := by
  rw [resolveAt_ops] at h; exact (Option.some.inj h).symm

/-- A sequence that starts with plain instructions resolves to them, followed by the rest. -/
theorem resolveAt_ops_append {ρ : Asm.Ref → Option UInt64} :
    ∀ (xs : List Instr) (ys : List SI) (p : UInt64) (ins : List Instr),
    Asm.resolveAt arch ρ p (xs.map .op ++ ys) = some ins →
    ∃ ins', ins = xs ++ ins' ∧
      Asm.resolveAt arch ρ (p + UInt64.ofNat (xs.flatMap encode).length) ys = some ins'
  | [], ys, p, ins, h => ⟨ins, rfl, by simpa using h⟩
  | x :: xs, ys, p, ins, h => by
    obtain ⟨i, is, h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv h
    cases h₁
    obtain ⟨ins', rfl, h'⟩ := resolveAt_ops_append xs ys _ _ h₂
    refine ⟨ins', rfl, ?_⟩
    rwa [List.flatMap_cons, List.length_append, UInt64.ofNat_add, ← UInt64.add_assoc]

/-! ### Instructions that move the stack pointer -/

/-- `sub rsp, 8G` moves `rsp` down `G` words. -/
theorem exec_subSp {trap : State → Option State} {s : State} {lo k G n : Nat}
    (hsp : s.regs.gpr .rsp = wa lo k) (hG : 8 * G < 2 ^ 31) (hk : G ≤ k) :
    ∃ s', exec trap (.aluRI .sub .rsp (UInt32.ofNat (8 * G))) n s = some s' ∧ s'.mem = s.mem ∧
      s'.world = s.world ∧ s'.regs.gpr .rsp = wa lo (k - G) ∧
      s'.regs.rip = s.regs.rip + UInt64.ofNat n := by
  refine ⟨_, rfl, rfl, rfl, ?_, rfl⟩
  simp only [Alu.writes, hsp, sext32_ofNat hG, State.withRegs_regs, ite_true, Regs.set_gpr_same]
  apply UInt64.toNat_inj.mp
  simp only [wa, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp; omega

/-- `add rsp, 8G` moves `rsp` up `G` words and keeps every other register. -/
theorem exec_addSp {trap : State → Option State} {s : State} {lo k G n : Nat}
    (hsp : s.regs.gpr .rsp = wa lo k) (hG : 8 * G < 2 ^ 31) :
    ∃ s', exec trap (.aluRI .add .rsp (UInt32.ofNat (8 * G))) n s = some s' ∧ s'.mem = s.mem ∧
      s'.world = s.world ∧ s'.regs.gpr .rsp = wa lo (k + G) ∧
      s'.regs.rip = s.regs.rip + UInt64.ofNat n ∧ ∀ r, r ≠ .rsp → s'.regs.gpr r = s.regs.gpr r := by
  refine ⟨_, rfl, rfl, rfl, ?_, rfl, fun r hr => by simp [Alu.writes, hr]⟩
  simp only [Alu.writes, hsp, sext32_ofNat hG, State.withRegs_regs, ite_true, Regs.set_gpr_same,
    wa_add]
  simp [wa, Nat.mul_add, Nat.add_assoc]

/-- `ret` with `rsp` at stack word `k` jumps to the address stored there and pops it. -/
theorem exec_ret {trap : State → Option State} {s : State} {lo k n : Nat} {ra : UInt64}
    (hsp : s.regs.gpr .rsp = wa lo k) (hra : load64 s.mem (wa lo k) = some ra) :
    ∃ s', exec trap .ret n s = some s' ∧ s'.mem = s.mem ∧ s'.world = s.world ∧
      s'.regs.gpr .rsp = wa lo (k + 1) ∧ s'.regs.rip = ra ∧
      ∀ r, r ≠ .rsp → s'.regs.gpr r = s.regs.gpr r := by
  simp only [exec, hsp, hra, Option.map_some]
  exact ⟨_, rfl, rfl, rfl, by simp [wa_succ], rfl, fun r hr => by simp [hr]⟩

/-- `call rel` with `rsp` at stack word `k` stores the return address in word `k - 1` and jumps
by `rel`. -/
theorem exec_call {trap : State → Option State} {s : State} {lo k n : Nat} {r : UInt32}
    {mem' : Memory} (hsp : s.regs.gpr .rsp = wa lo k) (hk : 0 < k)
    (hst : store64 s.mem (wa lo (k - 1)) (s.regs.rip + UInt64.ofNat n) = some mem') :
    ∃ s', exec trap (.call r) n s = some s' ∧ s'.mem = mem' ∧ s'.world = s.world ∧
      s'.regs.gpr .rsp = wa lo (k - 1) ∧ s'.regs.rip = s.regs.rip + UInt64.ofNat n + sext32 r := by
  simp only [exec, hsp, wa_pred hk, hst, Option.map_some]
  exact ⟨_, rfl, rfl, rfl, by simp, rfl⟩

/-- The block of instruction `pc` ends at the label of `pc + 1`. -/
theorem next_rip {f : Asm.Fn arch} {pc : Nat} {b : List SI} (hb : f.blocks[pc]? = some b)
    {a : UInt64} {ρ : Asm.Ref → Option UInt64} {ins : List Instr}
    (hr : Asm.resolveAt arch ρ (a + UInt64.ofNat (f.labelOff pc)) b = some ins) :
    a + UInt64.ofNat (f.labelOff pc) + UInt64.ofNat (ins.flatMap encode).length =
      a + UInt64.ofNat (f.labelOff (pc + 1)) := by
  rw [(Asm.resolveAt_size asmLaws _ _ _ _ hr (encodeAll_eq _)).1, labelOff_succ f hb, UInt64.ofNat_add, UInt64.add_assoc]

/-- `runIs_cons` with the instruction's length taken from its encoding. -/
theorem runIs_cons' {ω : Oracle} {i : Instr} {is : List Instr} {t t₁ : State}
    (hh : t.world.halted = false) (he : exec (linux.trap ω) i (encode i).length t = some t₁) :
    runIs (A := arch) linux ω (i :: is) t = runIs (A := arch) linux ω is t₁ :=
  runIs_cons (A := arch) linux hh he

theorem word_eq_of_load {m : Memory} {lo N k : Nat} {v : UInt64} (hR : Region m lo N) (hk : k < N)
    (h : load64 m (wa lo k) = some v) : word m lo k = v := by
  rw [load_wa hR hk] at h; exact Option.some.inj h

section Match
variable {k c : Nat} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}

/-- In a related state, `rip` is at the label of the Lin instruction. -/
theorem MatchAt.rip (hM : MatchAt k c P AP σ lo N s m fn f a j) :
    m.regs.rip = a + UInt64.ofNat (f.labelOff s.pc) := Sel.MatchAt.rip hM

/-- In a related state, `rsp` is at stack word `j`, the start of the running frame. -/
theorem MatchAt.sp (hM : MatchAt k c P AP σ lo N s m fn f a j) : m.regs.gpr .rsp = wa lo j :=
  Sel.MatchAt.sp hM

/-- The running frame's words lie in the region. -/
theorem MatchAt.roomW (hM : MatchAt k c P AP σ lo N s m fn f a j) :
    j + (min fn.frame k + (fn.frame - (k + c))) ≤ N := by
  have := Sel.MatchAt.room hM; simpa [Sel.frameW] using this

/-- A location `y` of the running frame holds its Lin value in register `loc k y` when
`y < k + c`, and in its frame slot otherwise. -/
theorem loc_val (hM : MatchAt k c P AP σ lo N s m fn f a j) {y : Nat} (hy : y < fn.frame) :
    (if y < k + c then m.regs.gpr (loc k y) else word m.mem lo (j + y - c)) = s.frame y :=
  hM.locs y hy

/-- What a slot load needs of a state `t` reached inside the block of a related state `m` whose
frame starts at word `j`: the region, `m`'s words from `j` on and `m`'s `rsp`, and it has not
halted. -/
structure FetchW (lo N j : Nat) (m t : State) : Prop where
  region : Region t.mem lo N
  words : ∀ i, j ≤ i → i < N → word t.mem lo i = word m.mem lo i
  sp : t.regs.gpr .rsp = m.regs.gpr .rsp
  halted : t.world.halted = false

/-- What an operand fetch needs of a state `t` reached inside the block of a related state `m`
whose frame starts at word `j`. The state `t` keeps the region, `m`'s words from `j` on, `m`'s
`rsp` and `m`'s location registers, and it has not halted. -/
structure Fetch (k c lo N j : Nat) (m t : State) : Prop extends FetchW lo N j m t where
  regs : ∀ x, x < k + c → t.regs.gpr (loc k x) = m.regs.gpr (loc k x)

/-- A state with `m`'s memory, `rsp` and location registers satisfies `Fetch`. -/
theorem Fetch.of_mem (hM : MatchAt k c P AP σ lo N s m fn f a j) {t : State} (hm : t.mem = m.mem)
    (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false)
    (hK : ∀ x, x < k + c → t.regs.gpr (loc k x) = m.regs.gpr (loc k x)) : Fetch k c lo N j m t :=
  ⟨⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh⟩, hK⟩

/-- A register location holds its Lin value in a state that keeps its register. -/
theorem reg_of_keep (hM : MatchAt k c P AP σ lo N s m fn f a j) {t : State} {y : Nat}
    (hy : y < fn.frame) (hyk : y < k + c) (h : t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    t.regs.gpr (loc k y) = s.frame y := by
  rw [h]
  have := loc_val hM hy; rw [ite_eq_left hyk] at this; exact this

/-- In a state that satisfies `Fetch`, a register location holds its Lin value. -/
theorem Fetch.reg (hM : MatchAt k c P AP σ lo N s m fn f a j) {t : State} (hF : Fetch k c lo N j m t)
    {y : Nat} (hy : y < fn.frame) (hyk : y < k + c) : t.regs.gpr (loc k y) = s.frame y :=
  reg_of_keep hM hy hyk (hF.regs y hyk)

/-- `ldI` loads an immediate or a slot operand that is not a register location into `r`. -/
theorem exec_ldI_loc (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24)
    {t : State} (hF : FetchW lo N j m t) {trap : State → Option State} {r : Reg} {o : Operand}
    {n : Nat} (ho : Lin.OpsBelow [o] fn.frame) (hslot : ∀ y, o = .slot y → k + c ≤ y) :
    exec trap (ldI c r o) n t = some (t.upd r (o.eval s.frame) n) := by
  cases o with
  | imm w => rfl
  | slot y =>
    have hy : y < fn.frame := ho y List.mem_cons_self
    have hroom := hM.roomW
    have hv := loc_val hM hy
    have := hslot y rfl
    rw [ite_eq_right (by omega)] at hv
    simp only [ldI, exec, Mem.addr, slotMem, hF.sp.trans hM.sp,
      slot_addr (by omega : 8 * (y - c) < 2 ^ 31), show j + (y - c) = j + y - c by omega,
      load_wa hF.region (show j + y - c < N by omega),
      hF.words (j + y - c) (by omega) (by omega), hv, Option.bind_some]
    rfl

/-- `ldTo` puts an operand's value into register `r` and keeps every other register. For a
register location it is a copy, or nothing when the location's register is `r`. -/
theorem run_ldTo {ω : Oracle} (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24)
    {t : State} (hF : FetchW lo N j m t) {r : Reg} (hr : r ≠ .rsp) {o : Operand}
    (ho : Lin.OpsBelow [o] fn.frame)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t', runIs (A := arch) linux ω (ldTo k c r o) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ t'.regs.gpr r = o.eval s.frame ∧
      ∀ r', r' ≠ r → t'.regs.gpr r' = t.regs.gpr r' := by
  by_cases hreg : ∃ y, o = .slot y ∧ y < k + c
  · obtain ⟨y, rfl, hyk⟩ := hreg
    have hy : y < fn.frame := ho y List.mem_cons_self
    by_cases he : loc k y = r
    · rw [show ldTo k c r (.slot y) = [] by simp [ldTo, hyk, he]]
      exact ⟨t, rfl, rfl, rfl, rfl, by rw [← he, reg_of_keep hM hy hyk (hK y rfl hyk)]; rfl,
        fun _ _ => rfl⟩
    · rw [show ldTo k c r (.slot y) = [.movRR r (loc k y)] by simp [ldTo, hyk, he]]
      refine ⟨_, runIs_one hF.halted exec_mv, upd_facts hr _ _ |>.1, (upd_facts hr _ _).2.1,
        (upd_facts hr _ _).2.2.1, ?_, (upd_facts hr _ _).2.2.2.2⟩
      rw [(upd_facts hr _ _).2.2.2.1, reg_of_keep hM hy hyk (hK y rfl hyk)]; rfl
  · have e : ldTo k c r o = [ldI c r o] := by
      cases o with
      | imm w => rfl
      | slot y => simp only [ldTo]; rw [ite_eq_right fun h => hreg ⟨y, rfl, h⟩]
    rw [e]
    exact ⟨_, runIs_one hF.halted (exec_ldI_loc hM hsm hF ho fun y hy => by
      subst hy; exact Nat.le_of_not_lt fun h => hreg ⟨y, rfl, h⟩), upd_facts hr _ _⟩

/-- `src` puts an operand's value into the register it names, keeping every register but `r`.
A register location is used in place, with no instruction. -/
theorem run_src {ω : Oracle} (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24)
    {t : State} (hF : FetchW lo N j m t) {r : Reg} (hr : r ≠ .rsp) {o : Operand}
    (ho : Lin.OpsBelow [o] fn.frame)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t', runIs (A := arch) linux ω (src k c r o).1 t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr (src k c r o).2 = o.eval s.frame ∧ ∀ r', r' ≠ r → t'.regs.gpr r' = t.regs.gpr r' := by
  by_cases hreg : ∃ y, o = .slot y ∧ y < k + c
  · obtain ⟨y, rfl, hyk⟩ := hreg
    rw [show src k c r (.slot y) = ([], loc k y) by simp [src, hyk]]
    exact ⟨t, rfl, rfl, rfl, rfl, reg_of_keep hM (ho y List.mem_cons_self) hyk (hK y rfl hyk),
      fun _ _ => rfl⟩
  · have e : src k c r o = ([ldI c r o], r) := by
      cases o with
      | imm w => rfl
      | slot y => simp only [src]; rw [ite_eq_right fun h => hreg ⟨y, rfl, h⟩]
    rw [e]
    exact ⟨_, runIs_one hF.halted (exec_ldI_loc hM hsm hF ho fun y hy => by
      subst hy; exact Nat.le_of_not_lt fun h => hreg ⟨y, rfl, h⟩), upd_facts hr _ _⟩

/-- The register that `src` names is `r` or the register of a location below `k + c`. -/
theorem src_reg (k c : Nat) (r : Reg) (o : Operand) :
    (src k c r o).2 = r ∨ ∃ y, y < k + c ∧ (src k c r o).2 = loc k y := by
  cases o with
  | imm w => exact Or.inl rfl
  | slot y =>
    simp only [src]; split
    · exact Or.inr ⟨y, ‹_›, rfl⟩
    · exact Or.inl rfl

end Match

/-! ### Binary operations on registers -/

/-- A two-operand ALU instruction that writes sets `d` to `d op r`. -/
theorem exec_aluW {trap : State → Option State} {t : State} {op : Alu} (hw : op.writes = true)
    {d r : Reg} {n : Nat} : ∃ t', exec trap (.aluRR op d r) n t = some t' ∧
      t'.regs.gpr = (t.regs.set d (op.eval (t.regs.gpr d) (t.regs.gpr r)).1).gpr ∧
      t'.mem = t.mem ∧ t'.world = t.world :=
  ⟨_, exec_aluRR op, by simp only [State.withRegs_regs]; rw [hw]; rfl, rfl, rfl⟩

/-- `alu2` sets `d` to `g n m`, given a two-operand instruction `f` that sets its first register
to `g` of both. The operation `g` must commute when `comm` is set, and `m` must not be `rax`. -/
theorem alu2_correct {ω : Oracle} {comm : Bool} {f : Reg → Reg → Instr} {g : UInt64 → UInt64 → UInt64}
    (hf : ∀ (t : State) d r, ∃ t', exec (linux.trap ω) (f d r) (encode (f d r)).length t = some t' ∧
      t'.regs.gpr = (t.regs.set d (g (t.regs.gpr d) (t.regs.gpr r))).gpr ∧ t'.mem = t.mem ∧
      t'.world = t.world)
    (hc : comm = true → ∀ a b, g a b = g b a) {s : State} {d n m : Reg} (hm : m ≠ .rax)
    (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (alu2 comm f d n m) s = some s' ∧
      s'.regs.gpr d = g (s.regs.gpr n) (s.regs.gpr m) := by
  unfold alu2
  by_cases h1 : d = n
  · subst h1
    obtain ⟨t, e, hg, -, -⟩ := hf s d m
    exact ⟨t, by simp only [ite_true]; exact runIs_one hh e, by rw [hg]; simp⟩
  · rw [ite_eq_right h1]
    by_cases h2 : d = m
    · subst h2; rw [ite_eq_left rfl]
      cases comm
      · simp only [Bool.false_eq_true, ite_false]
        obtain ⟨t, e, hg, -, hw⟩ := hf (s.upd .rax (s.regs.gpr n) (encode (.movRR .rax n)).length) .rax d
        refine ⟨_, by
          rw [runIs_cons' hh exec_mv, runIs_cons' (by simpa using hh) e]
          exact runIs_one (by rw [hw]; simpa using hh) exec_mv, ?_⟩
        simp [hg, hm]
      · simp only [ite_true]
        obtain ⟨t, e, hg, -, -⟩ := hf s d n
        exact ⟨t, runIs_one hh e, by rw [hg]; simp [hc rfl]⟩
    · rw [ite_eq_right h2]
      obtain ⟨t, e, hg, -, hw⟩ := hf (s.upd d (s.regs.gpr n) (encode (.movRR d n)).length) d m
      exact ⟨t, by rw [runIs_cons' hh exec_mv]; exact runIs_one (by simpa using hh) e,
        by rw [hg]; simp [Ne.symm h2]⟩

/-- The Lin operation of an x64 shift. -/
def Shift.op : Shift → BinOp
  | .shl => .shl
  | .shr => .shr

/-- A shift by `cl` sets `d` to the Lin shift of `d` by `rcx`, since x64 masks the count to six
bits as Lean's shifts do. -/
theorem exec_shift {trap : State → Option State} {t : State} (op : Shift) {d : Reg} {n : Nat} :
    ∃ t', exec trap (.shiftCL op d) n t = some t' ∧
      t'.regs.gpr = (t.regs.set d (op.op.eval (t.regs.gpr d) (t.regs.gpr .rcx))).gpr ∧
      t'.mem = t.mem ∧ t'.world = t.world := by
  simp only [exec]
  split
  · rename_i h0
    refine ⟨_, rfl, ?_, rfl, rfl⟩
    funext r
    simp only [State.withRegs_regs, Regs.set]
    split
    · subst r
      cases op
      · show _ = _ <<< _; rw [← shl_mask, h0, UInt64.shiftLeft_zero]
      · show _ = _ >>> _; rw [← shr_mask, h0, UInt64.shiftRight_zero]
    · rfl
  · refine ⟨_, rfl, ?_, rfl, rfl⟩
    cases op <;> simp [Shift.eval, Shift.op, BinOp.eval, shl_mask, shr_mask, State.withRegs, Regs.set]

/-- `shiftR` sets `d` to `n` shifted by `m`, provided `n` is not `rcx`. -/
theorem shiftR_correct {ω : Oracle} (op : Shift) {s : State} {d n m : Reg} (hn : n ≠ .rcx)
    (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (shiftR op d n m) s = some s' ∧
      s'.regs.gpr d = op.op.eval (s.regs.gpr n) (s.regs.gpr m) := by
  -- the count into `rcx`
  obtain ⟨s₁, h1, hc1, hn1, hw1⟩ : ∃ s₁ : State, runIs (A := arch) linux ω (if m = .rcx then [] else [.movRR .rcx m]) s =
      some s₁ ∧ s₁.regs.gpr .rcx = s.regs.gpr m ∧ s₁.regs.gpr n = s.regs.gpr n ∧ s₁.world = s.world := by
    split
    · rename_i hm; subst hm; exact ⟨s, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, runIs_one hh exec_mv, by simp, by simp [hn], rfl⟩
  have hh1 : s₁.world.halted = false := by rw [hw1]; exact hh
  unfold shiftR
  rw [runIs_append, h1, Option.bind_some]
  split
  · rename_i hd; subst hd
    obtain ⟨s₃, e3, g3, -, w3⟩ := exec_shift (trap := linux.trap ω)
      (t := s₁.upd .rax (s₁.regs.gpr n) (encode (.movRR .rax n)).length) op (d := .rax)
      (n := (encode (.shiftCL op .rax)).length)
    refine ⟨_, by rw [runIs_cons' hh1 exec_mv, runIs_cons' (by simpa using hh1) e3]
                  exact runIs_one (by rw [w3]; simpa using hh1) exec_mv, ?_⟩
    simp [g3, hc1, hn1]
  · rename_i hd
    obtain ⟨s₂, h2, hv2, hc2, hw2⟩ : ∃ s₂ : State, runIs (A := arch) linux ω (if d = n then [] else [.movRR d n]) s₁ =
        some s₂ ∧ s₂.regs.gpr d = s.regs.gpr n ∧ s₂.regs.gpr .rcx = s.regs.gpr m ∧ s₂.world = s.world := by
      split
      · rename_i hdn; subst hdn; exact ⟨s₁, rfl, hn1, hc1, hw1⟩
      · exact ⟨_, runIs_one hh1 exec_mv, by simp [hn1], by simp [Ne.symm hd, hc1], hw1⟩
    obtain ⟨s₃, e3, g3, -, w3⟩ := exec_shift (trap := linux.trap ω) (t := s₂) op (d := d)
      (n := (encode (.shiftCL op d)).length)
    refine ⟨s₃, by rw [runIs_append, h2, Option.bind_some]; exact runIs_one (by rw [hw2]; exact hh) e3, ?_⟩
    simp [g3, hv2, hc2]

/-- The condition `binR` sets for a comparison. -/
def cmpCond : BinOp → Cond
  | .eq => .e
  | .ne => .ne
  | .ult => .b
  | _ => .be

/-- `cmpR` sets `d` to 1 when the comparison of `n` with `m` holds and to 0 otherwise. -/
theorem cmpR_correct {ω : Oracle} {op : BinOp} (hop : op = .eq ∨ op = .ne ∨ op = .ult ∨ op = .ule)
    {s : State} {d n m : Reg} (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (cmpR (cmpCond op) d n m) s = some s' ∧
      s'.regs.gpr d = op.eval (s.regs.gpr n) (s.regs.gpr m) := by
  refine ⟨_, by rw [cmpR, runIs_cons' hh (exec_aluRR _), runIs_cons' (by simpa using hh) (exec_setcc _)]
                exact runIs_one (by simpa using hh) exec_movzx, ?_⟩
  have hc := cond_cmp (s.regs.gpr n) (s.regs.gpr m)
  simp only [State.withRegs_regs, Regs.set_gpr_same, Alu.writes, Bool.false_eq_true, ite_false]
  rw [low_byte]
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [cmpCond, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, BinOp.eval] <;>
    by_cases h : s.regs.gpr n = s.regs.gpr m <;> simp [h]

/-- `divR` copies the operands into `rax` and `rcx`, runs `binCode` and copies the result into
`d`, which computes any operation for `n ≠ rcx` and `m ≠ rax`. -/
theorem divR_correct {ω : Oracle} (op : BinOp) {s : State} {d n m : Reg} (hn : n ≠ .rcx)
    (hm : m ≠ .rax) (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (divR op d n m) s = some s' ∧
      s'.regs.gpr (binRes op d) = op.eval (s.regs.gpr n) (s.regs.gpr m) := by
  obtain ⟨s₁, h1, ha1, hm1, hw1⟩ : ∃ s₁ : State, runIs (A := arch) linux ω
      (if n = .rax then [] else [.movRR .rax n]) s = some s₁ ∧ s₁.regs.gpr .rax = s.regs.gpr n ∧
      s₁.regs.gpr m = s.regs.gpr m ∧ s₁.world = s.world := by
    split
    · rename_i h; subst h; exact ⟨s, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, runIs_one hh exec_mv, by simp, by simp [hm], rfl⟩
  obtain ⟨s₂, h2, ha2, hc2, hw2⟩ : ∃ s₂ : State, runIs (A := arch) linux ω
      (if m = .rcx then [] else [.movRR .rcx m]) s₁ = some s₂ ∧ s₂.regs.gpr .rax = s.regs.gpr n ∧
      s₂.regs.gpr .rcx = s.regs.gpr m ∧ s₂.world = s.world := by
    split
    · rename_i h; subst h; exact ⟨s₁, rfl, ha1, hm1, hw1⟩
    · exact ⟨_, runIs_one (by rw [hw1]; exact hh) exec_mv, by simp [ha1], by simp [hm1], hw1⟩
  obtain ⟨s₃, h3, hv3, -, -, hw3⟩ := binCode_correct ω op s₂ _ _ ha2 hc2 (by rw [hw2]; exact hh)
  unfold divR
  rw [runIs_append, runIs_append, runIs_append, h1, Option.bind_some, h2, Option.bind_some, h3,
    Option.bind_some]
  unfold binRes
  split
  · exact ⟨s₃, rfl, hv3⟩
  · exact ⟨_, runIs_one (by rw [hw3, hw2]; exact hh) exec_mv, by simp [hv3]⟩

/-- When `binCode op` leaves its result in `rax`, the result register `binRes op d` is `d`. -/
theorem binRes_of {op : BinOp} (h : (binCode op).2 = .rax) (d : Reg) : binRes op d = d := by
  unfold binRes; split <;> simp_all

/-- `cmp n, imm32`, `setcc` and `movzx` set `d` to 1 when the comparison of `n` with the
sign-extended immediate holds and to 0 otherwise. -/
theorem cmpI_correct {ω : Oracle} {op : BinOp} (hop : op = .eq ∨ op = .ne ∨ op = .ult ∨ op = .ule)
    {s : State} {d n : Reg} {i : UInt32} (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (cmpI (cmpCond op) d n i) s = some s' ∧
      s'.regs.gpr d = op.eval (s.regs.gpr n) (sext32 i) := by
  refine ⟨_, by rw [cmpI, runIs_cons' hh (exec_aluRI _ _), runIs_cons' (by simpa using hh) (exec_setcc _)]
                exact runIs_one (by simpa using hh) exec_movzx, ?_⟩
  have hc := cond_cmp (s.regs.gpr n) (sext32 i)
  simp only [State.withRegs_regs, Regs.set_gpr_same, Alu.writes, Bool.false_eq_true, ite_false]
  rw [low_byte]
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [cmpCond, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, BinOp.eval] <;>
    by_cases h : s.regs.gpr n = sext32 i <;> simp [h]

/-- `aluI` sets `d` to `n op imm`. -/
theorem aluI_correct {ω : Oracle} {op : Alu} (hw : op.writes = true) {s : State} {d n : Reg}
    {i : UInt32} (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (aluI op d n i) s = some s' ∧
      s'.regs.gpr d = (op.eval (s.regs.gpr n) (sext32 i)).1 := by
  have e : ∀ t : State, ∃ t', exec (linux.trap ω) (.aluRI op d i) (encode (.aluRI op d i)).length t =
      some t' ∧ t'.regs.gpr d = (op.eval (t.regs.gpr d) (sext32 i)).1 ∧ t'.world = t.world :=
    fun t => ⟨_, exec_aluRI op i, by simp only [State.withRegs_regs]; rw [hw]; simp, rfl⟩
  unfold aluI; split
  · rename_i h; subst h
    obtain ⟨t, h1, h2, -⟩ := e s
    exact ⟨t, runIs_one hh h1, h2⟩
  · obtain ⟨t, h1, h2, -⟩ := e (s.upd d (s.regs.gpr n) (encode (.movRR d n)).length)
    exact ⟨t, by rw [List.singleton_append, runIs_cons' hh exec_mv]; exact runIs_one (by simpa using hh) h1,
      by rw [h2]; simp⟩

/-- The immediate form `binImm` leaves `n op w` in `binRes op d`. -/
theorem binImm_correct {ω : Oracle} {mb : Bool} {op : BinOp} {d n : Reg} {w : UInt64}
    {c : List Instr} (h : binImm mb op d n w = some c) {s : State} (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω c s = some s' ∧
      s'.regs.gpr (binRes op d) = op.eval (s.regs.gpr n) w := by
  unfold binImm at h
  by_cases hm : (mb && fitsI32 w) = true
  · simp only [hm, ite_true] at h
    have hw' : sext32 w.toUInt32 = w := by simp [fitsI32] at hm; exact hm.2
    have ha : ∀ (op' : Alu) (g : BinOp), op'.writes = true → binRes g d = d →
        (∀ x, (op'.eval x w).1 = g.eval x w) → c = aluI op' d n w.toUInt32 →
        ∃ s', runIs (A := arch) linux ω c s = some s' ∧ s'.regs.gpr (binRes g d) = g.eval (s.regs.gpr n) w := by
      intro op' g hw hr he hc; subst hc
      obtain ⟨s', h1, h2⟩ := aluI_correct (ω := ω) hw (d := d) (n := n) (i := w.toUInt32) hh
      exact ⟨s', h1, by rw [hr, h2, hw', he]⟩
    have hcm : ∀ g : BinOp, (g = .eq ∨ g = .ne ∨ g = .ult ∨ g = .ule) → binRes g d = d →
        c = cmpI (cmpCond g) d n w.toUInt32 →
        ∃ s', runIs (A := arch) linux ω c s = some s' ∧ s'.regs.gpr (binRes g d) = g.eval (s.regs.gpr n) w := by
      intro g hg hr hc; subst hc
      obtain ⟨s', h1, h2⟩ := cmpI_correct (ω := ω) hg (d := d) (n := n) (i := w.toUInt32) hh
      exact ⟨s', h1, by rw [hr, h2, hw']⟩
    cases op <;> simp only [Option.some.injEq, reduceCtorEq] at h
    case add => exact ha .add .add rfl (binRes_of rfl d) (fun _ => rfl) h.symm
    case sub => exact ha .sub .sub rfl (binRes_of rfl d) (fun _ => rfl) h.symm
    case band => exact ha .and .band rfl (binRes_of rfl d) (fun _ => rfl) h.symm
    case bor => exact ha .or .bor rfl (binRes_of rfl d) (fun _ => rfl) h.symm
    case bxor => exact ha .xor .bxor rfl (binRes_of rfl d) (fun _ => rfl) h.symm
    case eq => exact hcm .eq (by simp) (binRes_of rfl d) h.symm
    case ne => exact hcm .ne (by simp) (binRes_of rfl d) h.symm
    case ult => exact hcm .ult (by simp) (binRes_of rfl d) h.symm
    case ule => exact hcm .ule (by simp) (binRes_of rfl d) h.symm
    case mul =>
      split at h
      · rename_i h1; subst h1; cases h
        exact ⟨_, runIs_one hh exec_mv, by simp [binRes_of (op := .mul) rfl, BinOp.eval]⟩
      · cases h
  · simp only [hm] at h; cases h

/-- An ALU instruction that writes, in the form `alu2_correct` takes. -/
theorem aluF {ω : Oracle} {op : Alu} (hw : op.writes = true) (t : State) (d r : Reg) :
    ∃ t', exec (linux.trap ω) (.aluRR op d r) (encode (.aluRR op d r)).length t = some t' ∧
      t'.regs.gpr = (t.regs.set d ((op.eval (t.regs.gpr d) (t.regs.gpr r)).1)).gpr ∧
      t'.mem = t.mem ∧ t'.world = t.world := exec_aluW hw

/-- `imul` in the form `alu2_correct` takes. -/
theorem imulF {ω : Oracle} (t : State) (d r : Reg) :
    ∃ t', exec (linux.trap ω) (.imul d r) (encode (.imul d r)).length t = some t' ∧
      t'.regs.gpr = (t.regs.set d (t.regs.gpr d * t.regs.gpr r)).gpr ∧
      t'.mem = t.mem ∧ t'.world = t.world := ⟨_, rfl, rfl, rfl, rfl⟩

/-- For every Lin binary operation, `binR d n m op` leaves `n op m` in `binRes op d`, provided
`n` is not `rcx` and `m` is not `rax`. -/
theorem binR_correct {ω : Oracle} (op : BinOp) {s : State} {d n m : Reg} (hn : n ≠ .rcx)
    (hm : m ≠ .rax) (hh : s.world.halted = false) :
    ∃ s', runIs (A := arch) linux ω (binR d n m op) s = some s' ∧
      s'.regs.gpr (binRes op d) = op.eval (s.regs.gpr n) (s.regs.gpr m) := by
  cases op
  case udiv => exact divR_correct .udiv hn hm hh
  case umod => exact divR_correct .umod hn hm hh
  all_goals (rw [binRes_of rfl]; simp only [binR])
  case add =>
    exact alu2_correct (f := .aluRR .add) (g := fun a b => (Alu.eval .add a b).1)
      (aluF rfl) (fun _ a b => UInt64.add_comm a b) hm hh
  case sub =>
    exact alu2_correct (comm := false) (f := .aluRR .sub)
      (g := fun a b => (Alu.eval .sub a b).1) (aluF rfl) nofun hm hh
  case mul => exact alu2_correct (f := .imul) imulF (fun _ a b => UInt64.mul_comm a b) hm hh
  case band =>
    exact alu2_correct (f := .aluRR .and) (g := fun a b => (Alu.eval .and a b).1)
      (aluF rfl) (fun _ a b => UInt64.and_comm a b) hm hh
  case bor =>
    exact alu2_correct (f := .aluRR .or) (g := fun a b => (Alu.eval .or a b).1)
      (aluF rfl) (fun _ a b => UInt64.or_comm a b) hm hh
  case bxor =>
    exact alu2_correct (f := .aluRR .xor) (g := fun a b => (Alu.eval .xor a b).1)
      (aluF rfl) (fun _ a b => UInt64.xor_comm a b) hm hh
  case shl => exact shiftR_correct (ω := ω) .shl hn hh
  case shr => exact shiftR_correct (ω := ω) .shr hn hh
  case eq => exact cmpR_correct (ω := ω) (op := .eq) (Or.inl rfl) hh
  case ne => exact cmpR_correct (ω := ω) (op := .ne) (Or.inr (Or.inl rfl)) hh
  case ult => exact cmpR_correct (ω := ω) (op := .ult) (Or.inr (Or.inr (Or.inl rfl))) hh
  case ule => exact cmpR_correct (ω := ω) (op := .ule) (Or.inr (Or.inr (Or.inr rfl))) hh


/-- Whether an instruction may appear in a block that computes into `d` and may destroy `S`. It
is not `syscall`, does not branch or store, and writes only `d`, scratch registers and `S`. -/
def Instr.okIn (d : Reg) (S : List Reg) (i : Instr) : Bool :=
  i != .syscall && !i.branches && !i.stores && i.writes.all fun r => r == d || r.scratch || S.contains r

theorem Instr.okIn_spec {d : Reg} {S : List Reg} {i : Instr} (h : i.okIn d S = true) :
    i ≠ .syscall ∧ i.branches = false ∧ i.stores = false ∧
      ∀ r ∈ i.writes, r = d ∨ r.scratch = true ∨ r ∈ S := by
  simp only [Instr.okIn, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun r hr => (h.2 r hr).elim (·.elim Or.inl (Or.inr ∘ Or.inl))
    (Or.inr ∘ Or.inr)⟩

theorem binR_okIn (op : BinOp) (d n m : Reg) : (binR d n m op).all (Instr.okIn d (binKill op)) = true := by
  cases op <;> simp only [binR, alu2, shiftR, cmpR, divR, binCode] <;> (repeat' split) <;>
    simp [Instr.okIn, Instr.writes, Instr.branches, Instr.stores, Alu.writes, Reg.scratch, binKill]

/-- Every instruction of `binR` is straight-line, is not `syscall`, does not store, and writes
only `d`, scratch registers and `binKill op`. -/
theorem binR_instrs (op : BinOp) (d n m : Reg) : ∀ i ∈ binR d n m op, i ≠ .syscall ∧
    i.branches = false ∧ i.stores = false ∧
      ∀ r ∈ i.writes, r = d ∨ r.scratch = true ∨ r ∈ binKill op :=
  fun i hi => Instr.okIn_spec (List.all_eq_true.1 (binR_okIn op d n m) i hi)

/-! ## The operations -/

@[simp] theorem ldI_branches (c : Nat) (r : Reg) (o : Operand) : (ldI c r o).branches = false := by
  cases o <;> rfl
@[simp] theorem ldI_writes (c : Nat) (r : Reg) (o : Operand) : (ldI c r o).writes = [r] := by
  cases o <;> rfl
@[simp] theorem ldI_stores (c : Nat) (r : Reg) (o : Operand) : (ldI c r o).stores = false := by
  cases o <;> rfl
@[simp] theorem ldI_ne_syscall (c : Nat) (r : Reg) (o : Operand) : ldI c r o ≠ .syscall := by
  cases o <;> nofun
@[simp] theorem ldWR_branches (w : Flat.Width) (d : Reg) (m : Mem) : (ldWR w d m).branches = false := by
  cases w <;> rfl
@[simp] theorem ldWR_writes (w : Flat.Width) (d : Reg) (m : Mem) : (ldWR w d m).writes = [d] := by
  cases w <;> rfl
@[simp] theorem stWR_branches (w : Flat.Width) (r : Reg) (m : Mem) : (stWR w r m).branches = false := by
  cases w <;> rfl
@[simp] theorem stWR_writes (w : Flat.Width) (r : Reg) (m : Mem) : (stWR w r m).writes = [] := by
  cases w <;> rfl

/-- x64's convention has no register invariant, so a straight instruction keeps it. -/
theorem sc {k c : Nat} {ω : Oracle} {i : Instr} (h : Sel.Straight (A := arch) linux ω i) :
    Sel.StraightC (conv k c) linux ω i :=
  Sel.StraightC.of_true (fun _ _ => trivial) h

theorem scs {k c : Nat} {ω : Oracle} {is : List Instr} (h : ∀ i ∈ is, Sel.Straight (A := arch) linux ω i) :
    ∀ i ∈ is, Sel.StraightC (conv k c) linux ω i := fun i hi => sc (h i hi)

theorem straight_of {ω : Oracle} {i : Instr} (h : i.branches = false ∧ i.keepsSp = true) :
    Sel.Straight (A := arch) linux ω i :=
  fun _ _ hx => ⟨exec_rip h.1 hx, exec_keepsSp h.2 hx⟩

theorem resolve_lea_sym {ρ : Asm.Ref → Option UInt64} {addr D : UInt64}
    {ds : String} {d : Reg} (hD : ρ (.sym ds) = some D) {i : Instr}
    (h : SI.resolve ρ addr (.lea d (.sym ds)) = some i) :
    ∃ r, i = .lea d (.rip r) ∧ addr + 7 + sext32 r = D := by
  have e7 : (encode (.lea d (.rip 0))).length = 7 := by simp [encode, encW, encModRM, le32]
  simp only [SI.resolve, hD, Option.bind_some, e7] at h
  cases hr : rel32 D (addr + UInt64.ofNat 7) with
  | none => rw [hr] at h; cases h
  | some r => rw [hr] at h; cases h; exact ⟨r, rfl, rel32_spec hr⟩

/-- A sequence of plain instructions around one `lea` of a symbol resolves to the same
instructions, with a `rip`-relative displacement in the `lea` that reaches the symbol. -/
theorem resolveAt_lea_sym {ρ : Asm.Ref → Option UInt64} {D : UInt64}
    {ds : String} {d : Reg} (hD : ρ (.sym ds) = some D) (xs ys : List Instr) {p : UInt64}
    {ins : List Instr}
    (h : Asm.resolveAt arch ρ p (xs.map .op ++ .lea d (.sym ds) :: ys.map .op) =
      some ins) :
    ∃ r, ins = xs ++ .lea d (.rip r) :: ys ∧
      p + UInt64.ofNat (xs.flatMap encode).length + 7 + sext32 r = D := by
  obtain ⟨ins', rfl, h'⟩ := resolveAt_ops_append xs _ p ins h
  obtain ⟨i, is, h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv h'
  obtain ⟨r, rfl, hr⟩ := resolve_lea_sym hD h₁
  exact ⟨r, by rw [resolveAt_ops_inv h₂], hr⟩

/-- The Linux system-call argument registers. -/
def sysArg : Nat → Reg
  | 0 => .rdi
  | 1 => .rsi
  | _ => .rdx

/-- x64's operations for the shared selection proofs, with `k` register locations. The scratch
registers are `rax` and `rcx`. An operand in a register location is used in place by `src` or
copied by `ldTo`, a result is copied into a location by `stTo`, and `binR` computes on any
registers. -/
def selOps (k c : Nat) (mb : Bool) : Sel.Ops arch where
  Reg := Reg
  get r x := r.gpr x
  r0 := .rax
  r1 := .rcx
  op := .op
  ld := ldTo k c
  src := src k c
  st := stTo k c
  bin op d n m := binR d n m op
  binRes := binRes
  binKill := binKill
  preg := loc k
  memX := memX k c mb
  memXLen a off := (memX k c mb a off).length
  ea r o off := if disp mb off then r.gpr .r11 + r.gpr (ixR k c o) + off else r.gpr .rax
  ldW w d o off := [ldWR w d (memM k c mb o off)]
  stW w r o off := [stWR w r (memM k c mb o off)]
  binI op d n w := binImm mb op d n w
  stI w v o off := stImm k c mb w v o off
  ldOk r := r ≠ .rsp
  stOk _ := True
  binOk n m := n ≠ .rcx ∧ m ≠ .rax
  Ok _ := True
  nums := LinuxNums.x64
  nrR := .rax
  argR := sysArg
  res := .rax
  trap := .syscall
  mv d r := [.movRR d r]
  symA r ds := [.lea r (.sym ds)]
  symLen := 1
  rdPre x := rdPre (x - c)
  rdFix x := rdFix (x - c)
  rdRes := .rcx

theorem fnOk_iff {k c : Nat} {fn : Lin.Fn} :
    (selector k c mb lvo).fnOk fn = true ↔
      (fn.frame < 2 ^ 24 ∧ fn.ret.length ≤ 8) ∧ KC k c ∧ (c = 0 ∨ fn.ret.length ≤ 5) := by
  simp [selector, fnOk, and_assoc]

theorem select_ok {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} (h : select k c P mb = .ok A) :
    Sel.select (selector k c mb (RegAlloc.Live.of P)) P = .ok A := by
  unfold select at h; split at h
  · exact h
  · cases h

/-- An accepted selection with caller-saved locations passed the clobber check. -/
theorem clob_of_select {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} (h : select k c P mb = .ok A) :
    Sel.ClobOk (conv k c) P := by
  unfold select at h; split at h
  · rename_i hc
    rcases hc with rfl | hc
    · exact Or.inr fun ins y => by
        simp only [conv, RegAlloc.Alloc.Classes.across, cls, Nat.add_zero, Bool.and_eq_false_iff,
          decide_eq_false_iff_not]; omega
    · exact Or.inl hc
  · cases h

theorem binOps_eq (k c : Nat) (op : BinOp) (d n : (selOps k c mb).Reg) (o : Operand) :
    (selOps k c mb).binOps op d n o = binCodeB k c mb op d n o := by
  cases o <;> rfl

theorem storeIs_eq (k c : Nat) (w : Flat.Width) (a : Operand) (off : UInt64) (b : Operand) :
    (selOps k c mb).storeIs w a off b = storeCode k c mb w a off b := by
  cases b <;> rfl

theorem memA_eq (k c : Nat) (a : Operand) (off : UInt64) :
    (selOps k c mb).memA a off = memAddrR k c mb a off := by
  simp only [Sel.Ops.memA, Sel.Ops.memPre, binOps_eq]
  simp [selOps, memAddrR, ops, binR, alu2]

theorem ldTo_nil {k c x : Nat} {o : Operand} (hx : x < k + c) (hk : KC k c)
    (h : ldTo k c (loc k x) o = []) : o = .slot x := by
  cases o with
  | imm w => cases h
  | slot y =>
    simp only [ldTo] at h
    split at h
    · split at h
      · rename_i hy he; rw [loc_inj hk hy hx he]
      · cases h
    · cases h

theorem ldTo_ok {k c : Nat} {r : Reg} (o : Operand) :
    ∀ i ∈ ldTo k c r o, i ≠ .syscall ∧ i.branches = false ∧ i.stores = false ∧ i.writes = [r] := by
  cases o with
  | imm w => simp [ldTo]
  | slot y =>
    simp only [ldTo]; split
    · split
      · simp
      · simp only [List.mem_singleton, forall_eq]; exact ⟨nofun, rfl, rfl, rfl⟩
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨ldI_ne_syscall _ _ _, ldI_branches _ _ _, ldI_stores _ _ _, ldI_writes _ _ _⟩

theorem src_ok (k c : Nat) (r : Reg) (o : Operand) :
    ∀ i ∈ (src k c r o).1, i ≠ .syscall ∧ i.branches = false ∧ i.stores = false ∧ i.writes = [r] := by
  cases o with
  | imm w => simp [src]
  | slot y =>
    simp only [src]; split
    · simp
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨ldI_ne_syscall _ _ _, ldI_branches _ _ _, ldI_stores _ _ _, ldI_writes _ _ _⟩

/-- An instruction that does not branch and does not write `rsp` is straight-line. -/
theorem straight_writes {ω : Oracle} {i : Instr} (hb : i.branches = false)
    (hw : ∀ r ∈ i.writes, r ≠ .rsp) : Sel.Straight (A := arch) linux ω i :=
  straight_of ⟨hb, by simpa [Instr.keepsSp] using fun h => hw _ h rfl⟩

/-- After the instructions `xs`, `lea r, [rip + disp]` loads a symbol's address into `r` and
keeps every other register. -/
theorem ops_run_sym {ω : Oracle} {ρ : Asm.Ref → Option UInt64} {p Dd : UInt64} {ds : String}
    {r : Reg} {xs ys is : List Instr} (hr : r ≠ .rsp) (hD : ρ (.sym ds) = some Dd)
    (h : Asm.resolveAt arch ρ p (xs.map SI.op ++ [SI.lea r (.sym ds)] ++ ys.map SI.op) = some is) :
    ∃ pre, is = xs ++ pre ++ ys ∧ pre.length = 1 ∧
      (∀ i ∈ pre, Sel.Straight (A := arch) linux ω i) ∧
      ∀ (cx : List UInt8) (t : State), Asm.encodeAll isa xs = some cx →
        t.regs.rip = p + UInt64.ofNat cx.length → t.world.halted = false →
        ∃ t', runIs (A := arch) linux ω pre t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
          t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ t'.regs.gpr r = Dd ∧
          ∀ r', r' ≠ r → t'.regs.gpr r' = t.regs.gpr r' := by
  obtain ⟨d, rfl, hd⟩ := resolveAt_lea_sym hD xs ys (by simpa using h)
  refine ⟨[.lea r (.rip d)], by simp, rfl, fun i hi => by
    rw [List.mem_singleton.1 hi]; exact straight_of (by simp [Ne.symm hr]),
    fun cx t hcx hpc hh => ?_⟩
  rw [encodeAll_eq] at hcx; cases hcx
  have e7 : (encode (Instr.lea r (.rip d))).length = 7 := by simp [encode, encW, encModRM, le32]
  simp only [runIs, ilen_eq, hh, Bool.false_eq_true, ite_false, exec_lea, e7, Option.bind_some]
  exact ⟨_, rfl, by simp, by simp, by simp [Ne.symm hr],
    by simp [Mem.addr, hpc, ← hd, UInt64.add_assoc], fun r' h => by simp [h]⟩

/-- A data load of width `w` from `m` sets `d` to the loaded value. -/
theorem exec_ldWR {trap : State → Option State} {s : State} {w : Flat.Width} {d : Reg} {m : Mem}
    {v : UInt64} (n : Nat) (h : loadW s.mem (m.addr s.regs (s.regs.rip + UInt64.ofNat n)) w = some v) :
    exec trap (ldWR w d m) n s = some (s.upd d v n) := by
  cases w <;> simp only [loadW] at h <;> simp [ldWR, exec, h] <;> rfl

/-- A data store of width `w` of `r` to `m` changes memory and keeps the registers. -/
theorem exec_stWR {trap : State → Option State} {s : State} {w : Flat.Width} {r : Reg} {m : Mem}
    {mem' : Memory} (n : Nat)
    (h : storeW s.mem (m.addr s.regs (s.regs.rip + UInt64.ofNat n)) (s.regs.gpr r) w = some mem') :
    exec trap (stWR w r m) n s =
      some { s with mem := mem', regs := { s.regs with rip := s.regs.rip + UInt64.ofNat n } } := by
  cases w <;> simp only [storeW] at h <;> simp [stWR, exec, h]

/-- The memory operand of a data access is `[rax]` or `[r11 + a + off]`, whose effective address
is `ea`. -/
theorem memM_addr (k c : Nat) (mb : Bool) (o : Operand) (off : UInt64) (r : Regs) (next : UInt64) :
    (memM k c mb o off).addr r next =
      if disp mb off then r.gpr .r11 + r.gpr (ixR k c o) + off else r.gpr .rax := by
  unfold memM; split
  · rename_i h
    have h2 : off.toNat < 2 ^ 31 := by simp [disp] at h; exact h.2
    rw [Mem.addr, sext32_ofNat h2]; simp
  · simp [Mem.addr, *]

section Ops
variable {k c : Nat} {ω : Oracle} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64}
  {lo N : Nat} {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}

/-- A store of `r` into slot `x` at `[rsp + 8x]`, from a state with the related state's `rsp`,
writes the slot's stack word and keeps the registers. -/
theorem run_stSlot (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24) {t : State}
    {x : Nat} {r : Reg} {mem' : Memory} (hkx : k + c ≤ x) (hx : x < fn.frame)
    (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false)
    (hw : t.mem.writeWord (wa lo (j + x - c)) 8 (t.regs.gpr r) = some mem') :
    ∃ t' : State, runIs (A := arch) linux ω [.store (slotMem (x - c)) r] t = some t' ∧
      t'.mem = mem' ∧ t'.world = t.world ∧ t'.regs.gpr = t.regs.gpr := by
  have hroom := hM.roomW
  obtain ⟨c1, c2⟩ := wa_canon hM.region.top (show j + x - c < N by omega)
  have he : exec (linux.trap ω) (.store (slotMem (x - c)) r)
      (encode (.store (slotMem (x - c)) r)).length t =
      some { t with mem := mem', regs := { t.regs with
        rip := t.regs.rip + UInt64.ofNat (encode (.store (slotMem (x - c)) r)).length } } := by
    simp only [exec, Mem.addr, slotMem, hsp.trans hM.sp,
      slot_addr (show 8 * (x - c) < 2 ^ 31 by omega), show j + (x - c) = j + x - c by omega,
      store64, c1, c2, Bool.and_self, ite_true, hw, Option.map_some]
  exact ⟨_, runIs_one hh he, rfl, rfl, rfl⟩

/-- `run_ldTo` in the form of the shared law `Sel.Ops.Laws.run_ld`. -/
theorem ops_run_ldTo (hM : MatchAt k c P AP σ lo N s m fn f a j) (hok : (selector k c mb lvo).fnOk fn = true)
    {t : State} {r : Reg} {o : Operand} (hr : r ≠ .rsp) (ho : Lin.OpsBelow [o] fn.frame)
    (hm : t.mem = m.mem) (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t' : State, runIs (A := arch) linux ω (ldTo k c r o) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ True ∧
      t'.regs.gpr r = o.eval s.frame ∧ ∀ r', r' ≠ r → t'.regs.gpr r' = t.regs.gpr r' := by
  obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := run_ldTo (ω := ω) hM (fnOk_iff.1 hok).1.1
    ⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh⟩ hr ho hK
  exact ⟨t', h1, h2, h3, h4, trivial, h5, h6⟩

theorem ops_run_src (hM : MatchAt k c P AP σ lo N s m fn f a j) (hok : (selector k c mb lvo).fnOk fn = true)
    {t : State} {r : Reg} {o : Operand} (hr : r ≠ .rsp) (ho : Lin.OpsBelow [o] fn.frame)
    (hm : t.mem = m.mem) (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t' : State, runIs (A := arch) linux ω (src k c r o).1 t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ True ∧
      t'.regs.gpr (src k c r o).2 = o.eval s.frame ∧ ∀ r', r' ≠ r → t'.regs.gpr r' = t.regs.gpr r' := by
  obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := run_src (ω := ω) hM (fnOk_iff.1 hok).1.1
    ⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh⟩ hr ho hK
  exact ⟨t', h1, h2, h3, h4, trivial, h5, h6⟩

end Ops

theorem binImm_okIn {mb : Bool} {op : BinOp} {d n : Reg} {w : UInt64} {c : List Instr}
    (h : binImm mb op d n w = some c) : c.all (Instr.okIn d (binKill op)) = true := by
  unfold binImm at h
  by_cases hm : (mb && fitsI32 w) = true
  · simp only [hm, ite_true] at h
    cases op <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> (try split at h) <;>
      (try cases h) <;> (try subst h) <;> (try simp only [aluI, cmpI]) <;> (repeat' split) <;>
      simp [Instr.okIn, Instr.writes, Instr.branches, Instr.stores, Alu.writes, Reg.scratch, binKill]
  · simp only [hm] at h; cases h

theorem binImm_pos {mb : Bool} {op : BinOp} {d n : Reg} {w : UInt64} {c : List Instr}
    (h : binImm mb op d n w = some c) : 0 < c.length := by
  unfold binImm at h
  by_cases hm : (mb && fitsI32 w) = true
  · simp only [hm, ite_true] at h
    cases op <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> (try split at h) <;>
      (try cases h) <;> (try subst h) <;> simp [aluI, cmpI]
  · simp only [hm] at h; cases h

/-- A run of instructions that may appear in a block computing into `d` and destroying `S`
keeps `rsp`, memory, the world and every register but `d`, the scratch registers and `S`. -/
theorem run_okIn {ω : Oracle} {is : List Instr} {d : Reg} {S : List Reg} (hd : d ≠ .rsp)
    (hS : ∀ r ∈ S, r ≠ .rsp) (hi : is.all (Instr.okIn d S) = true) {t t' : State}
    (h1 : runIs (A := arch) linux ω is t = some t') :
    t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      ∀ r, r ≠ d → r.scratch = false → r ∉ S → t'.regs.gpr r = t.regs.gpr r := by
  have hi i h := Instr.okIn_spec (List.all_eq_true.1 hi i h)
  obtain ⟨hw, hg, hmem⟩ := runIs_frame (fun i h => (hi i h).1) h1
  refine ⟨hmem fun i h => (hi i h).2.2.1, hw, hg _ fun i h hr => ?_,
    fun r hrd hrs hrk => hg r fun i h hr => ?_⟩
  · rcases (hi i h).2.2.2 _ hr with e | e | e
    · exact hd e.symm
    · revert e; decide
    · exact hS _ e rfl
  · rcases (hi i h).2.2.2 _ hr with e | e | e
    · exact hrd e
    · rw [hrs] at e; cases e
    · exact hrk e

/-- `binR` in the form of the shared law `Sel.Ops.Laws.run_bin`. It leaves the result in
`binRes op d` and keeps `rsp`, memory, the world and every register but `d`, the scratch
registers and `binKill op`. -/
theorem ops_run_bin {ω : Oracle} (op : BinOp) {d n m : Reg} {t : State} (hd : d ≠ .rsp)
    (hn : n ≠ .rcx) (hm : m ≠ .rax) (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω (binR d n m op) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr (binRes op d) = op.eval (t.regs.gpr n) (t.regs.gpr m) ∧
      ∀ r, r ≠ d → r.scratch = false → r ∉ binKill op → t'.regs.gpr r = t.regs.gpr r := by
  obtain ⟨t', h1, h2⟩ := binR_correct (ω := ω) op hn hm hh
  obtain ⟨a, b, c, e⟩ := run_okIn hd (fun _ h => binKill_ne_rsp h) (binR_okIn op d n m) h1
  exact ⟨t', h1, a, b, c, h2, e⟩

/-- `binImm` in the form of the shared law `Sel.Ops.Laws.run_binI`. -/
theorem ops_run_binI {ω : Oracle} {mb : Bool} {op : BinOp} {d n : Reg} {w : UInt64}
    {c : List Instr} (hc : binImm mb op d n w = some c) {t : State} (hd : d ≠ .rsp)
    (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω c t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr (binRes op d) = op.eval (t.regs.gpr n) w ∧
      ∀ r, r ≠ d → r.scratch = false → r ∉ binKill op → t'.regs.gpr r = t.regs.gpr r := by
  obtain ⟨t', h1, h2⟩ := binImm_correct (ω := ω) hc hh
  obtain ⟨a, b, c, e⟩ := run_okIn hd (fun _ h => binKill_ne_rsp h) (binImm_okIn hc) h1
  exact ⟨t', h1, a, b, c, h2, e⟩

/-! ### The selector's blocks as the shared operations -/

theorem sel_mov (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (x : Nat) (o : Operand) :
    (selector k c mb lvo).instr P i pc fn (.mov x o) =
      .ok (((selOps k c mb).movIs (k + c) x o).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.mov x o) = _
  by_cases hx : x < k + c <;> by_cases ho : o = .slot x <;> simp [selInstr, Sel.Ops.movIs, selOps, hx, ho, stTo, ops]

theorem sel_bin (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (op : BinOp) (x : Nat)
    (a b : Operand) : (selector k c mb lvo).instr P i pc fn (.bin op x a b) =
      .ok (((selOps k c mb).binIs (k + c) op x a b).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.bin op x a b) = _
  simp only [Sel.Ops.binIs, binOps_eq]
  by_cases hx : x < k + c <;>
    simp [selInstr, Sel.Ops.dst, Sel.Ops.fin, selOps, hx, stTo, ops, dreg, fin]

theorem sel_load (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (w : Flat.Width) (x : Nat)
    (a : Operand) (off : UInt64) : (selector k c mb lvo).instr P i pc fn (.load w x a off) =
      .ok ((selOps k c mb).memX a off ++ ((selOps k c mb).loadIs (k + c) w x a off).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.load w x a off) = _
  by_cases hx : x < k + c <;>
    simp [selInstr, Sel.Ops.loadIs, Sel.Ops.dst, Sel.Ops.fin, selOps, hx, stTo, ops, dreg, fin]

theorem sel_store (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (w : Flat.Width)
    (a : Operand) (off : UInt64) (b : Operand) : (selector k c mb lvo).instr P i pc fn (.store w a off b) =
      .ok ((selOps k c mb).memX a off ++ ((selOps k c mb).storeIs w a off b).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.store w a off b) = _
  rw [storeIs_eq]; simp [selInstr, ops, selOps]

theorem memA_length (k c : Nat) (a : Operand) (off : UInt64) :
    (memAddrR k c mb a off).length = (selOps k c mb).memLen a off := by
  rw [← memA_eq (mb := mb)]; simp [Sel.Ops.memA, Sel.Ops.memLen, selOps]; omega

theorem cnt_mov (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (x : Nat) (o : Operand) :
    instrs k c mb lvo P 0 0 fn (.mov x o) = ((selOps k c mb).movIs (k + c) x o).length := by
  have := sel_mov (lvo := none) (mb := mb) k c P 0 0 fn x o
  simp only [selector] at this
  simp [instrs, this]

theorem cnt_bin (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (op : BinOp) (x : Nat) (a b : Operand) :
    instrs k c mb lvo P 0 0 fn (.bin op x a b) = ((selOps k c mb).binIs (k + c) op x a b).length := by
  have := sel_bin (lvo := none) (mb := mb) k c P 0 0 fn op x a b
  simp only [selector] at this
  simp [instrs, this]

theorem cnt_load (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (w : Flat.Width) (x : Nat) (a : Operand)
    (off : UInt64) : instrs k c mb lvo P 0 0 fn (.load w x a off) =
      (selOps k c mb).memXLen a off + ((selOps k c mb).loadIs (k + c) w x a off).length := by
  have := sel_load (lvo := none) (mb := mb) k c P 0 0 fn w x a off
  simp only [selector] at this
  simp [instrs, this, selOps]

theorem cnt_store (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (w : Flat.Width) (a : Operand)
    (off : UInt64) (b : Operand) : instrs k c mb lvo P 0 0 fn (.store w a off b) =
      (selOps k c mb).memXLen a off + ((selOps k c mb).storeIs w a off b).length := by
  have := sel_store (lvo := none) (mb := mb) k c P 0 0 fn w a off b
  simp only [selector] at this
  simp [instrs, this, selOps]

theorem bin_pos (op : BinOp) (d n m : Reg) : 0 < (binR d n m op).length := by
  cases op <;> simp only [binR, alu2, shiftR, cmpR, divR, binCode] <;> (repeat' split) <;> simp

theorem stTo_ok {k c x : Nat} {r : Reg} : ∀ i ∈ stTo k c x r, i ≠ .syscall ∧ i.branches = false ∧
    i.writes ⊆ [loc k x] := by
  unfold stTo; split
  · split
    · simp
    · simp only [List.mem_singleton, forall_eq]; exact ⟨nofun, rfl, by simp [Instr.writes]⟩
  · simp only [List.mem_singleton, forall_eq]; exact ⟨nofun, rfl, by simp [Instr.writes]⟩

theorem straight_ldTo {ω : Oracle} {k c : Nat} {r : Reg} (hr : r ≠ .rsp) (o : Operand) :
    ∀ i ∈ ldTo k c r o, Sel.Straight (A := arch) linux ω i := fun i hi =>
  straight_writes (ldTo_ok o i hi).2.1 (by rw [(ldTo_ok o i hi).2.2.2]; simpa using hr)

theorem straight_src {ω : Oracle} {k c : Nat} {r : Reg} (hr : r ≠ .rsp) (o : Operand) :
    ∀ i ∈ (src k c r o).1, Sel.Straight (A := arch) linux ω i := fun i hi =>
  straight_writes (src_ok k c r o i hi).2.1 (by rw [(src_ok k c r o i hi).2.2.2]; simpa using hr)

theorem straight_stTo {ω : Oracle} {k c x : Nat} {r : Reg} :
    ∀ i ∈ stTo k c x r, Sel.Straight (A := arch) linux ω i := fun i hi =>
  straight_writes (stTo_ok i hi).2.1 fun r' h => by
    have := (stTo_ok i hi).2.2 h; simp at this; rw [this]; exact loc_ne_rsp k x

theorem straight_ldWR {ω : Oracle} (w : Flat.Width) {d : Reg} (hd : d ≠ .rsp) (m : Mem) :
    ∀ i ∈ [ldWR w d m], Sel.Straight (A := arch) linux ω i := by
  simp only [List.mem_singleton, forall_eq]
  exact straight_writes (ldWR_branches w d m) (by simpa using hd)

theorem straight_stWR {ω : Oracle} (w : Flat.Width) (r : Reg) (m : Mem) :
    ∀ i ∈ [stWR w r m], Sel.Straight (A := arch) linux ω i := by
  simp only [List.mem_singleton, forall_eq]
  exact straight_writes (stWR_branches w r m) (by simp)

theorem run_stReg {ω : Oracle} {k c : Nat} {t : State} {x : Nat} {r : Reg} (hx : x < k + c)
    (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω (stTo k c x r) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr (loc k x) = t.regs.gpr r ∧ ∀ r', r' ≠ loc k x → t'.regs.gpr r' = t.regs.gpr r' := by
  by_cases he : loc k x = r
  · exact ⟨t, by rw [show stTo k c x r = [] by simp [stTo, hx, he]]; rfl, rfl, rfl, rfl,
      by rw [he], fun _ _ => rfl⟩
  · refine ⟨t.upd (loc k x) (t.regs.gpr r) (encode (.movRR (loc k x) r)).length,
      by rw [show stTo k c x r = [.movRR (loc k x) r] by simp [stTo, hx, he]]; exact runIs_one hh exec_mv,
      rfl, rfl, by simp [Ne.symm (loc_ne_rsp k x)], by simp, fun r' h => by simp [h]⟩

theorem run_stTo_slot {ω : Oracle} {k c : Nat} {P : Lin.Prog} {AP : Asm.Prog arch}
    {σ : String → Option UInt64} {lo N : Nat} {s : Lin.State} {m : State} {fn : Lin.Fn}
    {f : Asm.Fn arch} {a : UInt64} {j : Nat} (hM : MatchAt k c P AP σ lo N s m fn f a j)
    (hsm : fn.frame < 2 ^ 24) {t : State} {x : Nat} {r : Reg} {mem' : Memory} (hkx : k + c ≤ x)
    (hx : x < fn.frame) (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false)
    (hw : t.mem.writeWord (wa lo (j + x - c)) 8 (t.regs.gpr r) = some mem') :
    ∃ t' : State, runIs (A := arch) linux ω (stTo k c x r) t = some t' ∧ t'.mem = mem' ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      ∀ z, z < k + c → t'.regs.gpr (loc k z) = t.regs.gpr (loc k z) := by
  obtain ⟨t', h1, h2, h3, h4⟩ := run_stSlot (ω := ω) hM hsm hkx hx hsp hh hw
  exact ⟨t', by rw [show stTo k c x r = [.store (slotMem (x - c)) r] by
    simp [stTo, Nat.not_lt.2 hkx]]; exact h1,
    h2, h3, by rw [h4], fun _ _ => by rw [h4]⟩

theorem run_stWR {ω : Oracle} (w : Flat.Width) {r : Reg} (mb : Bool) (o : Operand) (off : UInt64)
    {t : State} {Dm : UInt64} {M : Nat} {h : Flat.Heap} {ad v : UInt64} (hR : DataRel Dm M t.mem h)
    (hDM : Dm.toNat + M ≤ 2 ^ 47) (hb : ad.toNat + w.bytes ≤ M)
    (hv : (if disp mb off then t.regs.gpr .r11 + t.regs.gpr (ixR k c o) + off else t.regs.gpr .rax) =
      Dm + ad)
    (hv' : t.regs.gpr r = v) (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω [stWR w r (memM k c mb o off)] t = some t' ∧
      DataRel Dm M t'.mem (h.store w ad v) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ t'.regs.gpr = t.regs.gpr := by
  obtain ⟨mem', hst, hR', hF, hout⟩ := store_data hR hDM w ad v hb
  exact ⟨_, runIs_one hh (exec_stWR _ (by rw [memM_addr, hv, hv']; exact hst)), hR', hF, hout, rfl,
    rfl, rfl⟩

theorem run_ldWR {ω : Oracle} (w : Flat.Width) {d : Reg} (hd : d ≠ .rsp) (mb : Bool) (o : Operand)
    (off : UInt64) {t : State} {Dm : UInt64} {M : Nat} {h : Flat.Heap} {ad : UInt64}
    (hR : DataRel Dm M t.mem h) (hDM : Dm.toNat + M ≤ 2 ^ 47) (hb : ad.toNat + w.bytes ≤ M)
    (hv : (if disp mb off then t.regs.gpr .r11 + t.regs.gpr (ixR k c o) + off else t.regs.gpr .rax) =
      Dm + ad)
    (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω [ldWR w d (memM k c mb o off)] t = some t' ∧
      t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr d = h.load w ad ∧ ∀ r, r ≠ d → t'.regs.gpr r = t.regs.gpr r :=
  ⟨_, runIs_one hh (exec_ldWR _ (by rw [memM_addr, hv]; exact load_data hR hDM w ad hb)),
    upd_facts hd _ _⟩

theorem stImm_spec {k c : Nat} {mb : Bool} {w : Flat.Width} {v : UInt64} {o : Operand}
    {off : UInt64} {is : List Instr} (h : stImm k c mb w v o off = some is) :
    disp mb off = true ∧ ((w = .w8 ∧ is = [.store8I (memM k c mb o off) v.toUInt8]) ∨
      (w = .w64 ∧ sext32 v.toUInt32 = v ∧ is = [.storeI (memM k c mb o off) v.toUInt32])) := by
  unfold stImm at h
  by_cases hd : disp mb off = true
  · simp only [hd, ite_true] at h
    refine ⟨hd, ?_⟩
    cases w
    · cases h; exact Or.inl ⟨rfl, rfl⟩
    · by_cases hf : fitsI32 v = true
      · simp only [hf, ite_true, Option.some.injEq] at h
        exact Or.inr ⟨rfl, by simpa [fitsI32] using hf, h.symm⟩
      · simp [hf] at h
  · simp [hd] at h

/-- A byte store writes the low byte only. -/
theorem store8_low (m : Memory) (a v : UInt64) : store8 m a v.toUInt8.toUInt64 = store8 m a v := by
  simp only [store8, Memory.writeWord, natBytes, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_mod]

/-- An immediate store of `v` to `[r11 + a + off]` stores `v` as `stW` would. -/
theorem run_stImm {ω : Oracle} {k c : Nat} {mb : Bool} {w : Flat.Width} {v : UInt64}
    {o : Operand} {off : UInt64} {is : List Instr} (h : stImm k c mb w v o off = some is)
    {t : State} {Dm : UInt64} {M : Nat} {hp : Flat.Heap} {ad : UInt64}
    (hR : DataRel Dm M t.mem hp) (hDM : Dm.toNat + M ≤ 2 ^ 47) (hb : ad.toNat + w.bytes ≤ M)
    (hv : (if disp mb off then t.regs.gpr .r11 + t.regs.gpr (ixR k c o) + off else t.regs.gpr .rax) =
      Dm + ad) (hh : t.world.halted = false) :
    ∃ t' : State, runIs (A := arch) linux ω is t = some t' ∧
      DataRel Dm M t'.mem (hp.store w ad v) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ t'.regs.gpr = t.regs.gpr := by
  obtain ⟨mem', hst, hR', hF, hout⟩ := store_data hR hDM w ad v hb
  have ha : ∀ n, (memM k c mb o off).addr t.regs (t.regs.rip + UInt64.ofNat n) = Dm + ad :=
    fun n => by rw [memM_addr, hv]
  obtain ⟨-, h⟩ := stImm_spec h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, hs, rfl⟩
  all_goals simp only [storeW] at hst
  · exact ⟨{ t with mem := mem', regs := { t.regs with
        rip := t.regs.rip + UInt64.ofNat (encode (.store8I (memM k c mb o off) v.toUInt8)).length } },
      runIs_one hh (by simp only [exec, ha, store8_low, hst]; rfl), hR', hF, hout, rfl, rfl, rfl⟩
  · exact ⟨{ t with mem := mem', regs := { t.regs with
        rip := t.regs.rip + UInt64.ofNat (encode (.storeI (memM k c mb o off) v.toUInt32)).length } },
      runIs_one hh (by simp only [exec, ha, hs, hst]; rfl), hR', hF, hout, rfl, rfl, rfl⟩

theorem bin_add' : binRes .add .rax = .rax := by simp [binRes, binCode]

/-- x64's operations satisfy the shared laws for any `k ≤ 6` preserved and `c ≤ 3` caller-saved
register locations. -/
theorem selOps_laws {k c : Nat} (hk : KC k c) :
    (selOps k c mb).Laws linux (conv k c) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  resolve_op _ _ _ := rfl
  sel_mov := sel_mov k c
  sel_bin := sel_bin k c
  cnt_mov := cnt_mov k c
  cnt_bin := cnt_bin k c
  reg_get _ _ _ := rfl
  preg_inj x y hx hy h := loc_inj hk hx hy h
  preg_ne x _ := ⟨loc_ne_rax k x, loc_ne_rcx k x⟩
  ld_preg x _ := loc_ne_rsp k x
  ld_nil x o hx h := ldTo_nil hx hk h
  src_reg r o := src_reg k c r o
  ld0 := show Reg.rax ≠ .rsp by decide
  ld1 := show Reg.rcx ≠ .rsp by decide
  r01 := show Reg.rcx ≠ .rax by decide
  st_pos x r hx := by simp only [conv_k, conv_c] at hx; simp [selOps, stTo, Nat.not_lt.2 hx]
  st0 := trivial
  st_src _ := trivial
  stBin _ := trivial
  bin_pos op d n m := bin_pos op d n m
  binOk_src a b := by
    constructor
    · rcases src_reg k c .rax a with h | ⟨y, -, h⟩ <;> simp [selOps, h]
    · rcases src_reg k c .rcx b with h | ⟨y, -, h⟩ <;> simp [selOps, h]
  binOk01 := ⟨show Reg.rax ≠ .rcx by decide, show Reg.rcx ≠ .rax by decide⟩
  binRes_preg _ x _ := by simp [selOps, binRes]
  straight_ld _ r o hr := scs (straight_ldTo (k := k) (c := c) (r := r) hr o)
  straight_src _ r o hr := scs (straight_src (k := k) (c := c) (r := r) hr o)
  straight_st _ x r _ := scs (straight_stTo (k := k) (c := c) (x := x) (r := r))
  straight_bin _ op d n m hd i hi := sc <| straight_writes (binR_instrs op d n m i hi).2.1 fun r h => by
    rcases (binR_instrs op d n m i hi).2.2.2 r h with e | e | e
    · rw [e]; exact hd
    · exact scratch_ne_rsp e
    · exact binKill_ne_rsp e
  straight_binI _ op d n w c h hd i hi := by
    have hs := Instr.okIn_spec (List.all_eq_true.1 (binImm_okIn h) i hi)
    exact sc <| straight_writes hs.2.1 fun r hr => by
      rcases hs.2.2.2 r hr with e | e | e
      · rw [e]; exact hd
      · exact scratch_ne_rsp e
      · exact binKill_ne_rsp e
  binI_pos _ _ _ _ _ h := binImm_pos h
  run_binI {ω} op d n w c t x h hd _ hx hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := ops_run_binI (ω := ω) h hd hh
    refine ⟨t', h1, h2, h3, h4, trivial, ?_, fun z _ hz hzk => h6 _ hz ?_ hzk⟩
    · show t'.regs.gpr (binRes op d) = _; rw [h5, ← hx]; rfl
    · show (loc k z).scratch = false
      unfold loc preg creg; split <;> split <;> decide
  ok_match _ := trivial
  run_ld hM hok hr ho hm hsp hh _ hK := ops_run_ldTo hM hok hr ho hm hsp hh hK
  run_src hM hok hr ho hm hsp hh _ hK := ops_run_src hM hok hr ho hm hsp hh hK
  run_bin {ω} op d n m t x y hd hnm hx hy hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := ops_run_bin (ω := ω) op hd hnm.1 hnm.2 hh
    refine ⟨t', h1, h2, h3, h4, trivial, ?_, fun z _ hz hzk => h6 _ hz ?_ hzk⟩
    · show t'.regs.gpr (binRes op d) = _; rw [h5, ← hx, ← hy]; rfl
    · show (loc k z).scratch = false
      unfold loc preg creg; split <;> split <;> decide
  binKill_add := rfl
  kill_bin op x hx h := kill_bin hk hx h
  run_st {ω} _ _ _ _ _ _ _ _ _ _ _ t x r _ hM hok _ hkx hx hsp hh _ hw :=
    run_stTo_slot (ω := ω) (r := r) hM (fnOk_iff.1 hok).1.1 hkx hx hsp hh hw
  run_stReg {ω} t x r hx _ hh _ := run_stReg (ω := ω) (k := k) (c := c) (r := r) hx hh
  bin_add := bin_add'
  run_sym hr hD h := by
    obtain ⟨pre, h1, h2, h3, h4⟩ := ops_run_sym hr hD h
    exact ⟨pre, h1, h2, scs h3, fun cx t hcx hpc hh _ => by
      obtain ⟨t', e1, e2, e3, e4, e5, e6⟩ := h4 cx t hcx hpc hh
      exact ⟨t', e1, e2, e3, e4, trivial, e5, e6⟩⟩

/-- The displacement form of `memX`: `rax := o` (nothing for a register location) and
`lea r11, [rip + mp_mem]`, which leave `&mp_mem` in `r11` and `o` in `ixR k c o`. -/
theorem run_memX_disp (hM : MatchAt k c P AP σ lo N s m fn f a j)
    (hok : (selector k c mb lvo).fnOk fn = true) {o : Operand} {Dm : UInt64}
    {L is : List Instr} (ho : Lin.OpsBelow [o] fn.frame) (hDm : σ memSym = some Dm)
    (hr : Asm.resolveAt arch (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc))
      ((ops (src k c .rax o).1 ++ [.lea .r11 (.sym memSym)]) ++ L.map SI.op) = some is)
    {code : List UInt8} (hen : Asm.encodeAll isa is = some code) :
    ∃ pre t, is = pre ++ L ∧ pre.length = (src k c .rax o).1.length + 1 ∧
      (∀ i ∈ pre, Sel.Straight (A := arch) linux ω i) ∧ runIs (A := arch) linux ω pre m = some t ∧
      t.mem = m.mem ∧ t.world = m.world ∧ t.regs.gpr .rsp = m.regs.gpr .rsp ∧
      t.regs.gpr .r11 + t.regs.gpr (ixR k c o) = Dm + o.eval s.frame ∧
      ∀ z, z < k + c → t.regs.gpr (loc k z) = m.regs.gpr (loc k z) := by
  have hra : ixR k c o ≠ .r11 := by
    rcases src_reg k c .rax o with h | ⟨y, -, h⟩ <;> rw [ixR, h]
    · decide
    · unfold loc preg creg; split <;> split <;> decide
  rw [show (ops (src k c .rax o).1 ++ [SI.lea .r11 (.sym memSym)]) ++ L.map SI.op =
      (src k c .rax o).1.map SI.op ++ [SI.lea .r11 (.sym memSym)] ++ L.map SI.op by simp [ops]] at hr
  obtain ⟨pre, rfl, hplen, hpre, hrun⟩ := ops_run_sym (ω := ω) (show Reg.r11 ≠ .rsp by decide)
    hDm hr
  obtain ⟨cxp, -, -, hexp, -⟩ := Sel.encodeAll_append _ _ _ hen
  obtain ⟨cx, -, -, hex, -⟩ := Sel.encodeAll_append _ _ _ hexp
  obtain ⟨t₁, h1, hm1, hw1, hsp1, -, hv1, hk1⟩ := ops_run_src (ω := ω) hM hok
    (show Reg.rax ≠ .rsp by decide) ho rfl rfl hM.halted (fun _ _ _ => rfl)
  have hxs : ∀ i ∈ (src k c .rax o).1, Sel.Straight (A := arch) linux ω i :=
    straight_src (show Reg.rax ≠ .rsp by decide) o
  obtain ⟨t₂, h2, hm2, hw2, hsp2, hv2, hk2⟩ := hrun cx t₁ hex
    ((Sel.Ops.runIs_pc hxs hex h1).trans (by rw [show arch.isa.pc m.regs = _ from hM.rip]))
    (by rw [hw1]; exact hM.halted)
  have hloc : ∀ z, loc k z ≠ .r11 := fun z => by unfold loc preg creg; split <;> split <;> decide
  refine ⟨(src k c .rax o).1 ++ pre, t₂, by simp, by simp [hplen], List.forall_mem_append.2 ⟨hxs, hpre⟩,
    by rw [Sel.runIs_append, h1, Option.bind_some, h2], by rw [hm2, hm1], by rw [hw2, hw1],
    by rw [hsp2, hsp1], ?_, fun z _ => ?_⟩
  · rw [hv2, hk2 _ hra, ixR, hv1]
  · rw [hk2 _ (hloc z), hk1 _ (loc_ne_rax k z)]

/-- x64's `load` and `store` blocks satisfy the shared laws. -/
theorem selOps_memLaws {k c : Nat} (hk : KC k c) :
    (selOps k c mb).MemLaws linux (conv k c) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  sel_load := sel_load k c
  sel_store := sel_store k c
  cnt_load := cnt_load k c
  cnt_store := cnt_store k c
  run_memX {ω P AP σ lo N s m fn f a j o off Dm L is code} hM hok ho hDm hr hen := by
    change Asm.resolveAt arch _ _ (memX k c mb o off ++ L.map SI.op) = some is at hr
    by_cases hd : disp mb off = true
    · rw [memX, ite_eq_left hd] at hr
      obtain ⟨pre, t, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := run_memX_disp hM hok ho hDm hr hen
      refine ⟨pre, t, h1, by simp [h2, selOps, memX, hd, ops], scs h3, h4, h5, h6, h7, trivial, ?_,
        fun z hz => h9 z hz⟩
      show (if disp mb off then t.regs.gpr .r11 + t.regs.gpr (ixR k c o) + off else t.regs.gpr .rax) = _
      rw [ite_eq_left hd, h8, UInt64.add_assoc]
    · rw [memX, ite_eq_right hd, ← memA_eq (mb := mb)] at hr
      obtain ⟨pre, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        (selOps_laws (lvo := lvo) (mb := mb) hk).run_mem (ω := ω) hM hok ho hDm hr hen
      refine ⟨pre, t, h1, ?_, h3, h4, h5, h6, h7, h8, ?_, h10⟩
      · rw [h2, ← memA_length (mb := mb)]; simp [selOps, memX, hd]
      · show (if disp mb off then t.regs.gpr .r11 + t.regs.gpr (ixR k c o) + off else t.regs.gpr .rax) = _
        rw [ite_eq_right hd]; exact h9
  ea_r1 t t' o off h := by
    show (if disp mb off then t'.gpr .r11 + t'.gpr (ixR k c o) + off else t'.gpr .rax) =
      (if disp mb off then t.gpr .r11 + t.gpr (ixR k c o) + off else t.gpr .rax)
    have hi : ixR k c o ≠ .rcx := by
      rcases src_reg k c .rax o with e | ⟨y, -, e⟩ <;> rw [ixR, e]
      · decide
      · exact loc_ne_rcx k y
    rw [show t'.gpr .r11 = t.gpr .r11 from h .r11 (show Reg.r11 ≠ .rcx by decide),
      show t'.gpr .rax = t.gpr .rax from h .rax (show Reg.rax ≠ .rcx by decide),
      show t'.gpr (ixR k c o) = t.gpr (ixR k c o) from h _ hi]
  straight_ldW _ w d _ off hd := scs (straight_ldWR (d := d) w hd _)
  ldW_pos _ _ _ _ := Nat.one_pos
  straight_stW _ w r _ _ := scs (straight_stWR w (r : Reg) _)
  stW_pos _ _ _ _ := Nat.one_pos
  straight_stI _ w v o off c h := by
    obtain ⟨-, h⟩ := stImm_spec h
    rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp only [List.mem_singleton, forall_eq] <;>
      exact sc (straight_writes rfl (by simp [Instr.writes]))
  stI_pos _ _ _ _ _ h := by
    obtain ⟨-, h⟩ := stImm_spec h
    rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  run_ldW {ω} w x o off t _ _ _ ad hR hDM hb hv hh _ := by
    have hd : dreg k c x ≠ .rsp := by unfold dreg; split <;> simp
    obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := run_ldWR (ω := ω) w hd mb o off hR hDM hb hv hh
    exact ⟨t', h1, h2, h3, h4, trivial, h5, fun z _ hz => h6 _ hz⟩
  run_stW {ω} w o off b t _ _ _ ad v hR hDM hb hv hv' hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_stWR (ω := ω) w mb o off hR hDM hb hv hv' hh
    exact ⟨t', h1, h2, h3, h4, h5, h6, fun z _ => congrFun h7 (loc k z)⟩
  run_stI {ω} w v o off c t _ _ _ ad h hR hDM hb hv hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_stImm (ω := ω) h hR hDM hb hv hh
    exact ⟨t', h1, h2, h3, h4, h5, h6, fun z _ => congrFun h7 (loc k z)⟩

/-! ### System calls -/

/-- The Linux system-call handler writes only `rax`. -/
theorem trap_regs {ω : Oracle} {t t' : State} (h : linux.trap ω t = some t') :
    ∃ v, t'.regs = t.regs.set .rax v := by
  unfold Abi.trap at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
  · cases h

/-- `syscall` runs the handler and then overwrites `rcx` and `r11`, so it keeps the handler's
`rax` and every location's register. -/
theorem ops_run_trap (ω : Oracle) (t t' : State) (h : linux.trap ω t = some t') :
    ∃ t'', exec (linux.trap ω) .syscall (Sel.ilen (A := arch) .syscall) t = some t'' ∧
      t''.mem = t'.mem ∧ t''.world = t'.world ∧ t''.regs.gpr .rax = t'.regs.gpr .rax ∧
      ∀ k x, t''.regs.gpr (loc k x) = t.regs.gpr (loc k x) := by
  obtain ⟨v, hv⟩ := trap_regs h
  refine ⟨_, by simp only [exec, h, Option.map_some]; exact rfl, by simp, by simp, by simp [Regs.set],
    fun k x => ?_⟩
  simp [Regs.set, hv, loc_ne (k := k) (x := x) (r := .rcx) rfl, loc_ne (k := k) (x := x) (r := .r11) rfl,
    loc_ne (k := k) (x := x) (r := .rax) rfl]

/-- The code before the trap of `read(fd, slot x, 1)` sets `rax` to 0, the number of `read`,
clears the slot with it, and sets `rsi` to the slot's address and `rdx` to 1. -/
theorem ops_run_rdPre {ω : Oracle} {P : Lin.Prog} {AP : Asm.Prog arch}
    {σ : String → Option UInt64} {lo N : Nat} {s : Lin.State} {m : State} {fn : Lin.Fn}
    {f : Asm.Fn arch} {a : UInt64} {j : Nat} {t : State} {x : Nat} {mz : Memory} {k c : Nat}
    (hM : MatchAt k c P AP σ lo N s m fn f a j) (hok : (selector k c mb lvo).fnOk fn = true)
    (hkx : k + c ≤ x) (hx : x < fn.frame) (hm : t.mem = m.mem)
    (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp)
    (hh : t.world.halted = false) (hwz : m.mem.writeWord (wa lo (j + x - c)) 8 0 = some mz) :
    ∃ t', runIs (A := arch) linux ω (rdPre (x - c)) t = some t' ∧ t'.mem = mz ∧ t'.world = t.world ∧
      t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ t'.regs.gpr .rax = 0 ∧
      t'.regs.gpr .rsi = wa lo (j + x - c) ∧ t'.regs.gpr .rdx = 1 ∧
      t'.regs.gpr .rdi = t.regs.gpr .rdi ∧
      ∀ z, loc k z ≠ .rsi → loc k z ≠ .rdx → t'.regs.gpr (loc k z) = t.regs.gpr (loc k z) := by
  have hsm := (fnOk_iff.1 hok).1.1
  have hroom := hM.roomW
  have hx31 : 8 * (x - c) < 2 ^ 31 := by omega
  have hst : store64 t.mem (wa lo (j + (x - c))) 0 = some mz := by
    rw [hm, store64_wa hM.region (by omega), show j + (x - c) = j + x - c by omega]; exact hwz
  rw [show j + x - c = j + (x - c) by omega]
  simp (config := { contextual := true }) [rdPre, runIs, hh, exec, Mem.addr, slotMem,
    hsp.trans hM.sp, slot_addr hx31, hst, Regs.set, -UInt32.ofNat_mul,
    loc_ne (k := k) (x := _) (r := .rax) rfl]

/-- The value the code after a one-byte `read` computes is the byte read when `read` returned 1,
and all ones otherwise. -/
theorem read_value (res v w : UInt64) :
    v ||| (0 - ((w &&& ~~~255 ||| if Cond.eval (Alu.eval .cmp res 1).2 .ne then 1 else 0) &&& 255)) =
    (if res = 1 then v else UInt64.ofNat (2 ^ 64 - 1)) := by
  have hc := (cond_cmp res 1).2.1
  by_cases h : res = 1
  · subst h; simp at hc; simp [hc]
  · simp [h] at hc
    simp only [hc, ite_true, low_byte_one, h, ite_false]
    apply UInt64.toBitVec_inj.mp; simp

/-- The code after the trap of `read(fd, slot x, 1)` loads the slot into `rcx` and then ORs in
`0 - (rax ≠ 1)`, so `rcx` holds the byte read or all ones. -/
theorem ops_run_rdFix {ω : Oracle} {P : Lin.Prog} {AP : Asm.Prog arch}
    {σ : String → Option UInt64} {lo N : Nat} {s : Lin.State} {m : State} {fn : Lin.Fn}
    {f : Asm.Fn arch} {a : UInt64} {j : Nat} {t : State} {x : Nat} {k c : Nat}
    (hM : MatchAt k c P AP σ lo N s m fn f a j) (hok : (selector k c mb lvo).fnOk fn = true)
    (hkx : k + c ≤ x) (hx : x < fn.frame) (hR : Region t.mem lo N)
    (hsp : t.regs.gpr .rsp = m.regs.gpr .rsp) (hh : t.world.halted = false) :
    ∃ t', runIs (A := arch) linux ω (rdFix (x - c)) t = some t' ∧
      t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      t'.regs.gpr .rcx = (if t.regs.gpr .rax = 1 then word t.mem lo (j + x - c)
        else UInt64.ofNat (2 ^ 64 - 1)) ∧
      ∀ z, loc k z ≠ .rdx → t'.regs.gpr (loc k z) = t.regs.gpr (loc k z) := by
  have hsm := (fnOk_iff.1 hok).1.1
  have hroom := hM.roomW
  have hx31 : 8 * (x - c) < 2 ^ 31 := by omega
  rw [show j + x - c = j + (x - c) by omega]
  simp (config := { contextual := true }) [rdFix, runIs, hh, Mem.addr, slotMem, hsp.trans hM.sp, slot_addr hx31,
    load_wa hR (show j + (x - c) < N by omega), -UInt32.ofNat_mul, loc_ne (k := k) (x := _) (r := .rax) rfl,
    loc_ne (k := k) (x := _) (r := .rcx) rfl]
  simpa [Alu.eval] using read_value _ _ _

theorem mv_straight {d r : Reg} (hd : d ≠ .rsp) :
    (Instr.movRR d r).branches = false ∧ (Instr.movRR d r).keepsSp = true := by
  simp [Instr.writes, Instr.branches, Ne.symm hd]

theorem ops_run_mv {ω : Oracle} {t : State} {d r : Reg} (hd : d ≠ .rsp)
    (hh : t.world.halted = false) :
    ∃ t', runIs (A := arch) linux ω [.movRR d r] t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧ True ∧
      t'.regs.gpr d = t.regs.gpr r ∧ ∀ r', r' ≠ d → t'.regs.gpr r' = t.regs.gpr r' :=
  ⟨_, by simp [runIs, hh]; exact rfl, by simp, by simp, by simp [Ne.symm hd], trivial, by simp,
    fun r' h => by simp [h]⟩

/-- Running the moves `ms` one after the other, as `mov` instructions, sets the registers as the
sequence `Sel.PMove.run` says; with `Sel.PMove.seq_run` this is a parallel move. -/
theorem run_moves {ω : Oracle} : ∀ (ms : List (Reg × Reg)) {t : State}, (∀ p ∈ ms, p.1 ≠ .rsp) →
    t.world.halted = false →
    ∃ t', runIs (A := arch) linux ω (ms.map fun p => .movRR p.1 p.2) t = some t' ∧
      t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      ∀ r, t'.regs.gpr r = Sel.PMove.run t.regs.gpr ms r
  | [], t, _, _ => ⟨t, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | (d, s) :: ms, t, hd, hh => by
    obtain ⟨t₁, h1, m1, w1, x1, -, g1, o1⟩ :=
      ops_run_mv (ω := ω) (r := s) (hd (d, s) (List.mem_cons_self ..)) hh
    obtain ⟨t₂, h2, m2, w2, x2, g2⟩ :=
      run_moves (ω := ω) ms (fun p hp => hd p (List.mem_cons_of_mem _ hp)) (w1 ▸ hh)
    have he : t₁.regs.gpr = Sel.PMove.step t.regs.gpr d s := funext fun r => by
      by_cases hr : r = d
      · subst hr; simp only [Sel.PMove.step, ite_true]; exact g1
      · simp only [Sel.PMove.step, hr, ite_false]; exact o1 r hr
    refine ⟨t₂, ?_, m2.trans m1, w2.trans w1, x2.trans x1, fun r => ?_⟩
    · show runIs (A := arch) linux ω ([.movRR d s] ++ ms.map fun p => .movRR p.1 p.2) t = some t₂
      rw [runIs_append, h1]; exact h2
    · rw [g2, he]; rfl


theorem emit_eq (k c : Nat) : (selOps k c mb).emit = emit k c := by
  funext p; rcases p with ⟨d | d, r | r⟩ <;> rfl

theorem memTail_eq (k c : Nat) (n : UInt64) (x : Nat) (o l : Operand) :
    (selOps k c mb).memTail (k + c) n x o l = memTail k c n x o l := by
  simp only [Sel.Ops.memTail, memTail, emit_eq]; rfl

/-- The code of a `write` or `read` of a buffer is the data address and `memTail`. -/
theorem sel_memTail {k c : Nat} {P : Lin.Prog} {i pc : Nat} {fn : Lin.Fn} {x : Nat}
    {sym : String} {n : UInt64} {o p l : Operand} {args : List Flat.ExtArg}
    (hs : (sym = "write" ∧ n = 1 ∧ args = [.word o, .mem p l]) ∨
      (sym = "read" ∧ n = 0 ∧ args = [.word o, .outMem p l])) {b : List SI}
    {d : List (String × List UInt8)} :
    selInstr k c mb lvo P i pc fn (.ext sym false x args) = .ok (b, d) ↔
      ∃ tl, memTail k c n x o l = some tl ∧ b = memAddrR k c mb p 0 ++ ops tl ∧ d = [] := by
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [selInstr]
    cases memTail k c _ x o l <;> simp [eq_comm]

theorem straight_rdPre {ω : Oracle} (x : Nat) : ∀ i ∈ rdPre x, Sel.Straight (A := arch) linux ω i := by
  simp only [rdPre, List.mem_cons, List.mem_nil_iff, or_false]
  rintro i (rfl | rfl | rfl | rfl) <;> exact straight_of (by simp)

theorem straight_rdFix {ω : Oracle} (x : Nat) : ∀ i ∈ rdFix x, Sel.Straight (A := arch) linux ω i := by
  simp only [rdFix, List.mem_cons, List.mem_nil_iff, or_false]
  rintro i (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact straight_of (by simp)

/-- x64's system calls satisfy the shared laws for any `k ≤ 6` register locations. -/
theorem selOps_ext {k c : Nat} (hk : KC k c) :
    (selOps k c mb).ExtLaws linux (conv k c) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  linux := ⟨12, 0x7ffffffff000, _, ⟨fun r => r.gpr .rax, fun i r => r.gpr (sysArg i),
    fun v r => r.set .rax v⟩, rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => by simp [selOps]⟩
  nums := by simp only [selOps]; decide
  r1_sys := show Reg.rcx ∉ [Reg.rax, .rdi, .rsi, .rdx, .rax] by decide
  nodup := show [Reg.rax, .rdi, .rsi, .rdx].Nodup by decide
  preg_rd x _ := loc_ne rfl
  kill_sys x hx h := by
    have h' : loc k x ∈ [Reg.rax, sysArg 0, sysArg 1, sysArg 2, .rax] := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with e | e | e | e | e
    · exact absurd e (loc_ne rfl)
    all_goals first | exact absurd e (loc_ne rfl) |
      exact kill_ext hk hx (by simp [fixRegs, e, sysArg])
  ld_nr := show Reg.rax ≠ .rsp by decide
  ld_arg i hi := by
    show sysArg i ≠ .rsp
    match i, hi with | 0, _ | 1, _ | 2, _ => decide
  st_res := trivial
  st_rd := trivial
  straight_trap _ := sc <| straight_of (show Instr.branches .syscall = false ∧ Instr.keepsSp .syscall = true by decide)
  run_trap ω t t' _ h := by
    obtain ⟨t'', h1, h2, h3, h4, h5⟩ := ops_run_trap ω t t' h
    exact ⟨t'', h1, h2, h3, h4, trivial, fun z _ _ => h5 k z⟩
  straight_mv _ d _ hd := by
    simp only [selOps, List.mem_singleton, forall_eq]; exact sc (straight_of (mv_straight hd))
  run_mv hd hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := ops_run_mv hd hh
    exact ⟨t', h1, h2, h3, h4, h5, h6, h7⟩
  straight_rdPre _ x := scs (straight_rdPre (x - c))
  straight_rdFix _ x := scs (straight_rdFix (x - c))
  run_rdPre hM hok hkx hx hm hsp hh _ hwz := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ops_run_rdPre hM hok hkx hx hm hsp hh hwz
    exact ⟨t', h1, h2, h3, h4, trivial, h5, h6, h7, h8, fun z _ hz =>
      h9 z (fun e => hz (show loc k z ∈ [Reg.rax, .rdi, .rsi, .rdx, .rax] by rw [e]; decide))
        (fun e => hz (show loc k z ∈ [Reg.rax, .rdi, .rsi, .rdx, .rax] by rw [e]; decide))⟩
  run_rdFix hM hok hkx hx hR hsp hh _ := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := ops_run_rdFix hM hok hkx hx hR hsp hh
    exact ⟨t', h1, h2, h3, h4, trivial, h5, fun z _ hz =>
      h6 z (fun e => hz (show loc k z ∈ [Reg.rax, .rdi, .rsi, .rdx, .rax] by rw [e]; decide))⟩
  sel_exit P i pc fn x o := by
    show selInstr k c mb lvo P i pc fn (.ext "exit" true x [.word o]) = _
    simp [selInstr, Sel.Ops.ldAll, selOps, ops, sysArg, ldI, ldTo, LinuxNums.x64]
  cnt_exit P fn x o := by simp [instrs, Sel.Ops.ldAll, selOps, sysArg, ldTo, ldI]
  sel_write P i pc fn x o bs b d h := by
    change selInstr k c mb lvo P i pc fn (.ext "write" false x [.word o, .bytes bs]) = _ at h
    simp only [selInstr] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by assumption, rfl, ?_⟩
      simp [Sel.Ops.ldAll, selOps, ops, sysArg, ldTo, ldI, LinuxNums.x64]
    · cases h
  cnt_write P fn x o bs := by simp [instrs, Sel.Ops.ldAll, selOps, sysArg, ldTo, ldI]
  sel_writeMem P i pc fn x o p l b d h := by
    obtain ⟨tl, h1, rfl, rfl⟩ := (sel_memTail (lvo := lvo) (mb := mb) (P := P) (i := i) (pc := pc) (fn := fn)
      (Or.inl ⟨rfl, rfl, rfl⟩)).1 h
    exact ⟨tl, (memTail_eq k c _ x o l).trans h1, by rw [memA_eq (mb := mb)]; rfl, rfl⟩
  sel_readMem P i pc fn x o p l b d h := by
    obtain ⟨tl, h1, rfl, rfl⟩ := (sel_memTail (lvo := lvo) (mb := mb) (P := P) (i := i) (pc := pc) (fn := fn)
      (Or.inr ⟨rfl, rfl, rfl⟩)).1 h
    exact ⟨tl, (memTail_eq k c _ x o l).trans h1, by rw [memA_eq (mb := mb)]; rfl, rfl⟩
  cnt_writeMem P fn x o p l is h := by
    have e := (sel_memTail (lvo := none) (mb := mb) (k := k) (c := c) (P := P) (i := 0) (pc := 0) (fn := fn)
      (x := x) (p := p) (Or.inl ⟨rfl, rfl, rfl⟩)).2 ⟨is, (memTail_eq k c _ x o l).symm.trans h, rfl, rfl⟩
    show (match selInstr k c mb none P 0 0 fn _ with | .ok (b, _) => b.length | .error _ => 0) = _
    rw [e]; show (memAddrR k c mb p 0 ++ ops is).length = _
    rw [List.length_append, ← memA_eq (mb := mb)]
    simp [Sel.Ops.memA, Sel.Ops.memLen, ops]; rfl
  cnt_readMem P fn x o p l is h := by
    have e := (sel_memTail (lvo := none) (mb := mb) (k := k) (c := c) (P := P) (i := 0) (pc := 0) (fn := fn)
      (x := x) (p := p) (Or.inr ⟨rfl, rfl, rfl⟩)).2 ⟨is, (memTail_eq k c _ x o l).symm.trans h, rfl, rfl⟩
    show (match selInstr k c mb none P 0 0 fn _ with | .ok (b, _) => b.length | .error _ => 0) = _
    rw [e]; show (memAddrR k c mb p 0 ++ ops is).length = _
    rw [List.length_append, ← memA_eq (mb := mb)]
    simp [Sel.Ops.memA, Sel.Ops.memLen, ops]; rfl
  sel_read P i pc fn x o b d h := by
    change selInstr k c mb lvo P i pc fn (.ext "read" false x [.word o, .out 1]) = _ at h
    simp only [selInstr] at h
    split at h
    · cases h
    · rename_i hx
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using hx, rfl, by simp [selOps, ops, stTo, hx]; rfl⟩
  cnt_read P fn x o := rfl

/-- A jump to label `l` resolves to a `jmp` whose rel32 displacement reaches the label. -/
theorem resolve_jmp {f : Asm.Fn arch} {σ : String → Option UInt64} {a addr : UInt64} {l : Nat}
    (hl : l ≤ f.blocks.length) {i : Instr} (h : SI.resolve (f.refAddr σ a) addr (.jmp (.label l)) = some i) :
    ∃ r, i = .jmp r ∧ addr + 5 + sext32 r = a + UInt64.ofNat (f.labelOff l) := by
  simp only [SI.resolve, label_addr hl, Option.bind_some] at h
  cases hr : rel32 (a + UInt64.ofNat (f.labelOff l)) (addr + 5) with
  | none => rw [hr] at h; cases h
  | some r => rw [hr] at h; cases h; exact ⟨r, rfl, rel32_spec hr⟩

theorem resolve_jcc {f : Asm.Fn arch} {σ : String → Option UInt64} {a addr : UInt64} {l : Nat}
    {cc : Cond} (hl : l ≤ f.blocks.length) {i : Instr}
    (h : SI.resolve (f.refAddr σ a) addr (.jcc cc (.label l)) = some i) :
    ∃ r, i = .jcc cc r ∧ addr + 6 + sext32 r = a + UInt64.ofNat (f.labelOff l) := by
  simp only [SI.resolve, label_addr hl, Option.bind_some] at h
  cases hr : rel32 (a + UInt64.ofNat (f.labelOff l)) (addr + 6) with
  | none => rw [hr] at h; cases h
  | some r => rw [hr] at h; cases h; exact ⟨r, rfl, rel32_spec hr⟩

section Jumps
variable {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- The Lin instruction `jmp l` takes one machine step, a jump to the label of `l`, and keeps
the relation. -/
theorem sim_jmp (hsel : select k c P mb = .ok A) (hwf : P.Wf) {ω : Oracle} {κ : CostModel}
    {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}
    (hM : MatchAt k c P A σ lo N s m fn f a j) {l : Nat}
    (hi : fn.code[s.pc]? = some (.jmp l)) (cy : Nat) :
    ∃ m', M.run ω (m, cy) 1 = some (m', cy + 1) ∧
      MatchAt k c P A σ lo N (Lin.exec κ ω fn (.jmp l) s |>.getD s) m' fn f a j ∧
      RunAll ω (fun x => x.regs.gpr .rsp = m.regs.gpr .rsp) (m, cy) 1 := by
  obtain ⟨b, hC⟩ := ctx_of asmLaws (select_ok hsel) hwf hM hi
  obtain ⟨d, hsi, _⟩ := hC.instr
  simp only [selector, selInstr, Except.ok.injEq, Prod.mk.injEq] at hsi
  obtain ⟨rfl, rfl⟩ := hsi
  have hl : l < fn.code.length := hC.wf
  obtain ⟨ins, hr, hcode⟩ := seqAt_x64 hC.code
  obtain ⟨i', is', h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv hr
  cases h₂
  obtain ⟨r, rfl, hrt⟩ := resolve_jmp (by rw [hC.nblocks]; omega) h₁
  have he : exec (linux.trap ω) (.jmp r) (encode (.jmp r)).length m =
      some (m.jump (a + UInt64.ofNat (f.labelOff l))) := by
    simp only [exec, hM.rip]
    rw [← hrt]; rfl
  have hst := step_exec (c := cy) hM.halted (by rw [hM.rip]; simpa using hcode) he
  exact ⟨_, Sem.run_one hst, matchAt_keep hM rfl rfl rfl rfl rfl rfl rfl rfl
    (by show l ≤ _; omega) rfl (fun _ _ => rfl) trivial, RunAll.one rfl hst rfl⟩

/-- The Lin instruction `jz o l` puts the operand in a register with `src`, compares it with
zero and jumps on equality, and the machine state after it is related to the Lin state. -/
theorem sim_jz (hsel : select k c P mb = .ok A) (hwf : P.Wf) {ω : Oracle} {κ : CostModel}
    {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}
    (hM : MatchAt k c P A σ lo N s m fn f a j) {o : Operand} {l : Nat}
    (hi : fn.code[s.pc]? = some (.jz o l)) (cy : Nat) :
    ∃ m', M.run ω (m, cy) ((src k c .rax o).1.length + 1 + 1) =
        some (m', cy + ((src k c .rax o).1.length + 1 + 1)) ∧
      MatchAt k c P A σ lo N (Lin.exec κ ω fn (.jz o l) s |>.getD s) m' fn f a j ∧
      RunAll ω (fun x => x.regs.gpr .rsp = m.regs.gpr .rsp) (m, cy) ((src k c .rax o).1.length + 1 + 1) := by
  obtain ⟨b, hC⟩ := ctx_of asmLaws (select_ok hsel) hwf hM hi
  obtain ⟨d, hsi, _⟩ := hC.instr
  simp only [selector, selInstr, Except.ok.injEq, Prod.mk.injEq] at hsi
  obtain ⟨rfl, rfl⟩ := hsi
  obtain ⟨ho, hl⟩ := hC.wf
  have hsm := (fnOk_iff.1 hC.sel.ok).1.1
  have hlt := pc_lt hi
  obtain ⟨ins, hr, hcode⟩ := seqAt_x64 hC.code
  obtain ⟨ins', rfl, hr'⟩ := resolveAt_ops_append ((src k c .rax o).1 ++ [.aluRI .cmp (src k c .rax o).2 0])
    _ _ _ (by simpa [ops] using hr)
  obtain ⟨i', is', h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv hr'
  cases h₂
  obtain ⟨r, rfl, hrt⟩ := resolve_jcc (by rw [hC.nblocks]; omega) h₁
  have hnext := next_rip hC.blk hr
  rw [List.flatMap_append, List.length_append, UInt64.ofNat_add, ← UInt64.add_assoc] at hnext
  rw [List.flatMap_append] at hcode
  obtain ⟨hc₁, hc₂⟩ := codeAt_append _ _ _ _ hcode
  -- the operand and `cmp r, 0`
  obtain ⟨t1, h1, hm1, hw1, hsp1, hv1, hk1⟩ := run_src (ω := ω) hM hsm (Fetch.of_mem hM rfl rfl hM.halted
    fun _ _ => rfl).toFetchW (r := .rax) (by decide) ho (fun _ _ _ => rfl)
  obtain ⟨t2, h2, hm2, hw2, hsp2, hfl2, hk2⟩ : ∃ t2 : State,
      runIs (A := arch) linux ω [.aluRI .cmp (src k c .rax o).2 0] t1 = some t2 ∧ t2.mem = m.mem ∧
      t2.world = m.world ∧ t2.regs.gpr .rsp = m.regs.gpr .rsp ∧
      t2.regs.flags = (Alu.eval .cmp (o.eval s.frame) 0).2 ∧ t2.regs.gpr = t1.regs.gpr :=
    ⟨_, runIs_one (by rw [hw1]; exact hM.halted) (exec_aluRI _ _), hm1, hw1, hsp1,
      by simp [hv1], by simp [Alu.writes]⟩
  have hrun : runIs (A := arch) linux ω ((src k c .rax o).1 ++ [.aluRI .cmp (src k c .rax o).2 0]) m =
      some t2 := by rw [runIs_append, h1, Option.bind_some, h2]
  obtain ⟨hrun', hF', -, hrip', hall⟩ := run_straight cy hM.wx (by rw [hM.rip]; exact hc₁)
    (by
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ⟨(src_ok k c .rax o i hi).2.1, by simp [Instr.keepsSp, (src_ok k c .rax o i hi).2.2.2]⟩
      · simp at hi; subst hi; simp [Instr.keepsSp, Instr.writes, Instr.branches, Alu.writes])
    hrun
  -- the conditional jump
  have he3 : exec (linux.trap ω) (.jcc .e r) (encode (.jcc .e r)).length t2 = some (t2.jump
      (a + UInt64.ofNat (f.labelOff (if o.eval s.frame = 0 then l else s.pc + 1)))) := by
    have h6 : UInt64.ofNat (encode (Instr.jcc .e r)).length = 6 := rfl
    simp only [exec, hfl2, (cond_cmp _ _).1, hrip', hM.rip, h6]
    by_cases hz : o.eval s.frame = 0
    · simp only [hz, decide_true, ite_true, hrt]
    · simp [hz, ← hnext]; rfl
  have hst := step_exec (c := cy + ((src k c .rax o).1.length + 1)) (by rw [hw2]; exact hM.halted)
    (by rw [hrip', hM.rip]; exact codeAt_frame hM.wx hF' _ _ hc₂) he3
  have hlen : ((src k c .rax o).1 ++ [Instr.aluRI .cmp (src k c .rax o).2 0]).length =
      (src k c .rax o).1.length + 1 := by simp
  rw [hlen] at hrun' hall
  refine ⟨_, Sem.run_add_of hrun' 1 |>.trans (Sem.run_one hst), ?_,
    RunAll.add hall hrun' (RunAll.one hsp2 hst hsp2)⟩
  refine matchAt_keep hM rfl rfl rfl rfl rfl hm2 hw2 hsp2
    (by show (if o.eval s.frame = 0 then l else s.pc + 1) ≤ _; split <;> omega) rfl (fun x hx => ?_)
    trivial
  show t2.regs.gpr (loc k x) = m.regs.gpr (loc k x)
  rw [hk2]; exact hk1 _ (loc_ne_rax k x)

end Jumps

end Millipede.X64
