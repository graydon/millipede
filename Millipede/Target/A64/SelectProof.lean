import Millipede.Target.SelExt
import Millipede.Target.A64.Select

/-!
# Machine-level lemmas of arm64 instruction selection

This module proves what the pieces of arm64 selected code do when they run, building on the
lemmas about single instructions in `A64/Laws.lean`. The selector itself and its simulation proof
are in `RegAlloc.A64Reg`, which uses these lemmas for every value of its number of register
locations.

The lemmas cover, in order, single instructions executed at an aligned `pc`, straight-line code
that neither branches, traps nor writes `sp`, the `movz` and `movk` sequences that build a 64-bit
constant, frame and word accesses, the entry and return sequences, symbol addresses in the data
region and the pieces of the system-call blocks. The structure `Init` states what the loader
provides at the start of a run.
-/

namespace Millipede.A64

open Flat (Operand BinOp)
open Sel (wa word Region)

set_option allowUnsafeReducibility true in
attribute [local reducible] isa W

/-! ## Instructions as executed -/

theorem aligned_add4 {p : UInt64} (h : p % 4 = 0) : (p + 4) % 4 = 0 := by grind

section ExecSimp
variable {trap : State → Option State} {s : State} {n : Nat}
@[simp] theorem exec_mov (h : s.regs.pc % 4 = 0) (op : MovOp) (sf : Bool) (d : Reg)
    (imm : BitVec 16) (hw : BitVec 2) : exec trap (.mov op sf d imm hw) n s =
    some (s.goto (s.regs.setZ d (movVal op sf (s.regs.getZ d) imm hw)) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_addReg (h : s.regs.pc % 4 = 0) (sf sub setf : Bool) (d a b : Reg) :
    exec trap (.addReg sf sub setf d a b) n s =
    some (s.goto (if setf then { s.regs.setZ d (addSub sf sub (s.regs.getZ a) (s.regs.getZ b)).1 with
        flags := (addSub sf sub (s.regs.getZ a) (s.regs.getZ b)).2 }
      else s.regs.setZ d (addSub sf sub (s.regs.getZ a) (s.regs.getZ b)).1) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_addImm (h : s.regs.pc % 4 = 0) (sf sub setf : Bool) (d a : Reg)
    (imm : BitVec 12) (sh : Bool) : exec trap (.addImm sf sub setf d a imm sh) n s =
    some (s.goto (if setf then { s.regs.setZ d (addSub sf sub (s.regs.x a)
        (imm.toNat.toUInt64 <<< (if sh then 12 else 0))).1 with
        flags := (addSub sf sub (s.regs.x a) (imm.toNat.toUInt64 <<< (if sh then 12 else 0))).2 }
      else s.regs.set d (addSub sf sub (s.regs.x a)
        (imm.toNat.toUInt64 <<< (if sh then 12 else 0))).1) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_logReg (h : s.regs.pc % 4 = 0) (op : LogOp) (sf : Bool) (d a b : Reg)
    (hop : op ≠ .ands) : exec trap (.logReg op sf d a b) n s =
    some (s.goto (s.regs.setZ d (bin sf op.eval (s.regs.getZ a) (s.regs.getZ b))) (s.regs.pc + 4)) := by
  simp [exec, h, hop]

@[simp] theorem exec_madd (h : s.regs.pc % 4 = 0) (sf sub : Bool) (d a b c : Reg) :
    exec trap (.madd sf sub d a b c) n s =
    some (s.goto (s.regs.setZ d (wid sf (if sub then s.regs.getZ c - s.regs.getZ a * s.regs.getZ b
      else s.regs.getZ c + s.regs.getZ a * s.regs.getZ b))) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_div (h : s.regs.pc % 4 = 0) (sf signed : Bool) (d a b : Reg) :
    exec trap (.div sf signed d a b) n s =
    some (s.goto (s.regs.setZ d (bin sf (fun _ x y => if signed then x.sdiv y else x / y)
      (s.regs.getZ a) (s.regs.getZ b))) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_shiftV (h : s.regs.pc % 4 = 0) (op : ShiftOp) (sf : Bool) (d a b : Reg) :
    exec trap (.shiftV op sf d a b) n s =
    some (s.goto (s.regs.setZ d (bin sf op.eval (s.regs.getZ a) (s.regs.getZ b))) (s.regs.pc + 4)) := by
  simp [exec, h]

@[simp] theorem exec_csel (h : s.regs.pc % 4 = 0) (op : CselOp) (sf : Bool) (d a b : Reg)
    (c : Cond) : exec trap (.csel op sf d a b c) n s =
    some (s.goto (s.regs.setZ d (bin sf (fun w x y => if c.holds s.regs.flags then x else op.eval w y)
      (s.regs.getZ a) (s.regs.getZ b))) (s.regs.pc + 4)) := by
  simp [exec, h]

end ExecSimp

@[simp] theorem goto_regs (s : State) (r : Regs) (a : UInt64) :
    (s.goto r a).regs = { r with pc := a } := rfl
@[simp] theorem goto_mem (s : State) (r : Regs) (a : UInt64) : (s.goto r a).mem = s.mem := rfl
@[simp] theorem goto_world (s : State) (r : Regs) (a : UInt64) : (s.goto r a).world = s.world := rfl

@[simp] theorem setZ_x (r : Regs) (d k : Reg) (v : UInt64) :
    (r.setZ d v).x k = if d = 31 then r.x k else if k = d then v else r.x k := by
  simp only [Regs.setZ]; split <;> simp
@[simp] theorem setZ_pc (r : Regs) (d : Reg) (v : UInt64) : (r.setZ d v).pc = r.pc := by
  simp only [Regs.setZ]; split <;> simp
@[simp] theorem setZ_flags (r : Regs) (d : Reg) (v : UInt64) : (r.setZ d v).flags = r.flags := by
  simp only [Regs.setZ]; split <;> simp
@[simp] theorem getZ_eq (r : Regs) (k : Reg) : r.getZ k = if k = 31 then 0 else r.x k := rfl

theorem getZ_ne {r : Regs} {k : Reg} (h : k ≠ 31) : r.getZ k = r.x k := by simp [show ¬ k = 31#5 from h]

/-! ## Straight-line code -/

theorem ilen_valid {i : Instr} (h : i.valid = true) : Sel.ilen (A := arch) i = 4 := by
  show ((isa.encode i).map List.length).getD 0 = 4
  simp [h, bytes_length]

/-- An encodable instruction that does not branch, trap or write `sp` falls through and keeps
`sp`. -/
theorem straight {ω : Oracle} {i : Instr} (hv : i.valid = true) (hb : i.branches = false)
    (ht : i.isTrap = false) (hs : (31 : Reg) ∉ i.writes) : Sel.Straight (A := arch) linux ω i := by
  intro s s' h
  rw [ilen_valid hv] at h ⊢
  show s'.regs.pc = s.regs.pc + 4 ∧ s'.regs.x 31 = s.regs.x 31
  exact ⟨exec_pc (n := 4) hb h, exec_x (n := 4) ht h 31 hs⟩

/-- The encoding of a list of plain instructions. -/
theorem encodeAll_valid : ∀ (is : List Instr), (∀ i ∈ is, i.valid = true) →
    Asm.encodeAll isa is = some (is.flatMap bytes)
  | [], _ => rfl
  | i :: is, h => by
    simp only [Asm.encodeAll, List.flatMap_cons]
    have hi := h i List.mem_cons_self
    simp only [isa, hi, ite_true]
    rw [encodeAll_valid is fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem encodeAll_length : ∀ {is : List Instr} {code : List UInt8},
    Asm.encodeAll isa is = some code → code.length = 4 * is.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    obtain ⟨e, es, he, hes, rfl⟩ := Asm.encodeAll_cons_inv h
    obtain ⟨-, rfl⟩ := isa_encode he
    rw [List.length_append, bytes_length, encodeAll_length hes, List.length_cons]; omega

theorem resolveAt_ops {ρ : Asm.Ref → Option UInt64} :
    ∀ (is : List Instr) (a : UInt64), Asm.resolveAt arch ρ a (ops is) = some is
  | [], _ => rfl
  | i :: is, _ => Asm.resolveAt_cons_some (A := arch) (i := .op i) rfl (resolveAt_ops is _)

theorem resolveAt_ops_inv {ρ : Asm.Ref → Option UInt64} {is ins : List Instr} {a : UInt64}
    (h : Asm.resolveAt arch ρ a (ops is) = some ins) : ins = is := by
  rw [resolveAt_ops] at h; exact (Option.some.inj h).symm

theorem seqSize_ops : ∀ (L : List Instr), Asm.seqSize arch (ops L) = 4 * L.length
  | [] => rfl
  | _ :: L => by
    show 4 + Asm.seqSize arch (ops L) = 4 * (L.length + 1)
    rw [seqSize_ops L]; omega

/-- A block that starts with plain instructions resolves to them, then the rest. -/
theorem resolveAt_ops_append {ρ : Asm.Ref → Option UInt64} {L : List Instr} {rest : List SI}
    {p : UInt64} {is : List Instr} (h : Asm.resolveAt arch ρ p (ops L ++ rest) = some is) :
    ∃ is', is = L ++ is' ∧ Asm.resolveAt arch ρ (p + UInt64.ofNat (4 * L.length)) rest = some is' := by
  obtain ⟨i₁, i₂, rfl, h₁, h₂⟩ := Sel.resolveAt_append _ _ _ _ h
  obtain rfl := resolveAt_ops_inv h₁
  refine ⟨i₂, rfl, ?_⟩
  rwa [seqSize_ops i₁] at h₂

theorem resolveAt_single {ρ : Asm.Ref → Option UInt64} {x : SI} {p : UInt64} {is : List Instr}
    (h : Asm.resolveAt arch ρ p [x] = some is) : ∃ i, is = [i] ∧ arch.resolve ρ p x = some i := by
  obtain ⟨i, is', h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv h
  cases h₂; exact ⟨i, rfl, h₁⟩

/-! ## Constants and operands -/

/-- Halfword `k` of `w`, as a word. -/
def hw (w : UInt64) (k : Nat) : UInt64 := (w >>> UInt64.ofNat (16 * k)) &&& 0xFFFF

theorem half_val (w : UInt64) (k : Nat) (hk : k < 4) :
    (half w k).toNat.toUInt64 = hw w k := by
  apply UInt64.toNat_inj.mp
  simp only [half, hw, BitVec.toNat_ofNat, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt64.toNat_and, UInt64.toNat_shiftRight]
  have e : (0xFFFF : UInt64).toNat = 2 ^ 16 - 1 := rfl
  have e2 : (UInt64.ofNat (16 * k)).toNat % 64 = 16 * k := by
    rw [UInt64.toNat_ofNat']; simp; omega
  have e3 : 16 * k % 2 ^ 64 % 64 = 16 * k := by omega
  rw [e3, e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  omega

theorem half_ne (w : UInt64) (k : Nat) (hk : k < 4) : (half w k != 0) = decide (hw w k ≠ 0) := by
  rw [← half_val w k hk]
  cases h : half w k == 0
  · have : half w k ≠ 0 := by simpa using h
    have : (half w k).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq (by simpa using e))
    have hl := (half w k).isLt
    simp only [bne, h, Bool.not_false, Bool.true_eq, decide_eq_true_eq]
    intro e; apply this
    have := congrArg UInt64.toNat e
    simp [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this; omega
  · simp only [beq_iff_eq] at h
    simp [bne, h]

/-- `movz` of halfword `0` and `movk` of halfword `k`, as values. -/
theorem movz_val (old w : UInt64) : movVal .z true old (half w 0) 0 = hw w 0 := by
  simp [movVal, wid, half_val w 0 (by omega)]

theorem movk_val (old w : UInt64) (k : Nat) (hk : 0 < k ∧ k < 4) :
    movVal .k true old (half w k) (BitVec.ofNat 2 k) =
      (old &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * k))) ||| (hw w k <<< UInt64.ofNat (16 * k)) := by
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rw [← half_val w k hk.2]
  rcases hk' with rfl | rfl | rfl <;> rfl

/-! Bits of the halfword pieces, which `immFold_eq` uses. -/

theorem ffff_bit (j : Nat) : (65535#64).getLsbD j = decide (j < 16) := by
  rw [show (65535#64) = BitVec.ofNat 64 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : j < 16 <;> simp [h] <;> omega

theorem bit_hw (w : UInt64) (k i : Nat) (hk : k < 4) :
    (hw w k <<< UInt64.ofNat (16 * k)).toBitVec.getLsbD i =
      (decide (16 * k ≤ i) && decide (i < 16 * k + 16) && decide (i < 64) &&
        w.toBitVec.getLsbD i) := by
  simp only [hw, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_ofNat]
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, ffff_bit]
  all_goals by_cases a : i < 64 <;> simp [a] <;> grind

theorem bit_hw0 (w : UInt64) (i : Nat) :
    (hw w 0).toBitVec.getLsbD i = (decide (i < 16) && w.toBitVec.getLsbD i) := by
  simp only [hw, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.getLsbD_and, ffff_bit]
  simp; grind

theorem bit_mask (k i : Nat) (hk : k < 4) :
    ((0xFFFF : UInt64) <<< UInt64.ofNat (16 * k)).toBitVec.getLsbD i =
      (decide (16 * k ≤ i) && decide (i < 16 * k + 16) && decide (i < 64)) := by
  have e : hw (~~~0) k = 0xFFFF := by
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals rfl
  rw [← e, bit_hw _ _ _ hk, show (~~~(0 : UInt64)).toBitVec = BitVec.allOnes 64 from rfl]
  simp only [BitVec.getLsbD_allOnes]; by_cases a : i < 64 <;> simp [a]

/-- A zero halfword `k` of `w` is sixteen zero bits. -/
theorem bits_of_hw (w : UInt64) (k : Nat) (hk : k < 4) (h : hw w k = 0) (i : Nat) (h1 : 16 * k ≤ i)
    (h2 : i < 16 * k + 16) : w.toBitVec.getLsbD i = false := by
  have := congrArg (fun x : UInt64 => x.toBitVec.getLsbD (i - 16 * k)) h
  simp [hw, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, ffff_bit] at this
  rw [show 16 * k % 64 + (i - 16 * k) = i by omega] at this
  cases e : w.toBitVec.getLsbD i <;> simp_all; omega

/-- The halfwords of a constant reassemble it, whichever of them are zero, so the `movz` and
`movk` sequence that `immIs` emits builds the constant. The proof goes bit by bit. -/
theorem immFold_eq (w : UInt64) :
    let m (k : Nat) (v : UInt64) := (v &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * k))) |||
      (hw w k <<< UInt64.ofNat (16 * k))
    (([1, 2, 3].filter fun k => decide (hw w k ≠ 0)).foldl (fun v k => m k v) (hw w 0)) = w := by
  intro m
  simp only [m]
  by_cases h1 : hw w 1 = 0 <;> by_cases h2 : hw w 2 = 0 <;> by_cases h3 : hw w 3 = 0 <;>
    simp only [List.filter, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true,
      decide_false, List.foldl_cons, List.foldl_nil] <;>
    apply UInt64.toBitVec_inj.mp <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not, BitVec.getLsbD_and,
      BitVec.getLsbD_or, BitVec.getLsbD_not, bit_hw w 1 i (by omega), bit_hw w 2 i (by omega),
      bit_hw w 3 i (by omega), bit_hw0, bit_mask 1 i (by omega), bit_mask 2 i (by omega),
      bit_mask 3 i (by omega)] <;>
    have b1 := bits_of_hw w 1 (by omega) <;> have b2 := bits_of_hw w 2 (by omega) <;>
    have b3 := bits_of_hw w 3 (by omega) <;>
    by_cases c1 : i < 16 <;> by_cases c2 : i < 32 <;> by_cases c3 : i < 48 <;> simp_all <;> grind

/-- One `movk` of halfword `k` of `w`, on the old value `v`. -/
def mk (w : UInt64) (k : Nat) (v : UInt64) : UInt64 :=
  (v &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * k))) ||| (hw w k <<< UInt64.ofNat (16 * k))

theorem goto_goto (s : State) (r r' : Regs) (a a' : UInt64) :
    (s.goto r a).goto r' a' = s.goto r' a' := rfl

theorem set_set (r : Regs) (d : Reg) (v v' : UInt64) : (r.set d v).set d v' = r.set d v' := by
  simp only [Regs.set]; congr 1; funext k; split <;> rfl

theorem setZ_ne (r : Regs) {d : Reg} (hd : d ≠ 31) (v : UInt64) : r.setZ d v = r.set d v := by
  simp only [Regs.setZ, ite_eq_right hd]

theorem set_self (r : Regs) (d : Reg) : r.set d (r.x d) = r := by
  cases r; simp only [Regs.set, Regs.mk.injEq, and_true, and_self]; funext k; split <;> simp_all

@[simp] theorem set_pc' (r : Regs) (d : Reg) (v a : UInt64) :
    ({ r with pc := a } : Regs).set d v = { r.set d v with pc := a } := rfl

@[simp] theorem goto_with (s : State) (r : Regs) (a b : UInt64) :
    s.goto { r with pc := b } a = s.goto r a := rfl

theorem goto_self (s : State) : s.goto s.regs s.regs.pc = s := rfl

theorem add4_ofNat (n : Nat) : (4 : UInt64) + UInt64.ofNat (4 * n) = UInt64.ofNat (4 * (n + 1)) := by
  rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, ← UInt64.ofNat_add]; congr 1; omega

/-- The run of a list of arm64 instructions under Linux. -/
def runA (ω : Oracle) (is : List Instr) (s : State) : Option State :=
  Sel.runIs (A := arch) linux ω is s

@[simp] theorem runA_nil (ω : Oracle) (s : State) : runA ω [] s = some s := rfl

theorem runA_cons {ω : Oracle} {i : Instr} {is : List Instr} {s s₁ : State}
    (hh : s.world.halted = false) (hv : i.valid = true)
    (he : exec (linux.trap ω) i 4 s = some s₁) : runA ω (i :: is) s = runA ω is s₁ := by
  unfold runA; exact Sel.runIs_cons (A := arch) linux hh (by rw [ilen_valid hv]; exact he)

theorem runA_append (ω : Oracle) (xs ys : List Instr) (s : State) :
    runA ω (xs ++ ys) s = (runA ω xs s).bind (runA ω ys) := by
  unfold runA; exact Sel.runIs_append (A := arch) linux ω xs ys s

/-- Running the `movk`s of a constant. -/
theorem run_movks {ω : Oracle} (w : UInt64) {d : Reg} (hd : d ≠ 31) : ∀ (ks : List Nat),
    (∀ k ∈ ks, 0 < k ∧ k < 4) → ∀ (s : State), s.world.halted = false → s.regs.pc % 4 = 0 →
    runA ω (ks.map fun k => .mov .k true d (half w k) (BitVec.ofNat 2 k)) s =
      some (s.goto (s.regs.set d (ks.foldl (fun v k => mk w k v) (s.regs.x d)))
        (s.regs.pc + UInt64.ofNat (4 * ks.length)))
  | [], _, s, _, _ => by simp [set_self, goto_self]
  | k :: ks, hk, s, hh, ha => by
    have hk1 := hk k List.mem_cons_self
    rw [List.map_cons, runA_cons hh rfl (exec_mov ha _ _ _ _ _),
      run_movks w hd ks (fun k' h => hk k' (List.mem_cons_of_mem _ h)) _ (by simpa using hh)
        (by simpa using aligned_add4 ha)]
    simp only [goto_regs, goto_goto, getZ_eq, hd, ite_false, setZ_ne _ hd, movk_val _ w k hk1,
      List.foldl_cons, List.length_cons, set_pc', Regs.set_x, ite_true, set_set, goto_with]
    congr 2
    · rw [UInt64.add_assoc, add4_ofNat]

/-- Running `immIs d w` leaves `w` in `d`. -/
theorem run_immIs {ω : Oracle} {s : State} {d : Reg} (hd : d ≠ 31) (w : UInt64)
    (hh : s.world.halted = false) (ha : s.regs.pc % 4 = 0) :
    runA ω (immIs d w) s =
      some (s.goto (s.regs.set d w) (s.regs.pc + UInt64.ofNat (4 * (immIs d w).length))) := by
  have hf : ∀ k ∈ [1, 2, 3].filter (fun k => half w k != 0), 0 < k ∧ k < 4 := by
    intro k hk; have := (List.mem_filter.mp hk).1; simp at this; omega
  unfold immIs
  rw [runA_cons hh rfl (exec_mov ha _ _ _ _ _),
    run_movks w hd _ hf _ (by simpa using hh) (by simpa using aligned_add4 ha)]
  have hfl : ([1, 2, 3].filter fun k => half w k != 0) =
      ([1, 2, 3].filter fun k => decide (hw w k ≠ 0)) := by
    simp only [List.filter, half_ne w 1 (by omega), half_ne w 2 (by omega), half_ne w 3 (by omega)]
  have hw' := immFold_eq w
  simp only at hw'
  simp only [goto_regs, goto_goto, getZ_eq, hd, ite_false, setZ_ne _ hd, movz_val, set_pc',
    Regs.set_x, ite_true, set_set, hfl, mk, hw', List.length_cons, List.length_map, goto_with]
  rw [UInt64.add_assoc, add4_ofNat]

theorem ilen_eq (i : Instr) : Sel.ilen (A := arch) i = if i.valid then 4 else 0 := by
  show ((isa.encode i).map List.length).getD 0 = _
  split <;> simp_all [bytes_length]

theorem runA_cons_eq (ω : Oracle) (i : Instr) (is : List Instr) (s : State) :
    runA ω (i :: is) s = if s.world.halted then none
      else (exec (linux.trap ω) i (if i.valid then 4 else 0) s).bind (runA ω is) := by
  simp only [runA, Sel.runIs, ilen_eq]; rfl

/-! ## Frames and the loader's start

The frame of a function with `F` slots is `fw F = fsize F / 8` words long. When `sp` is word `j`,
slot `x` is word `j + x`, the saved `x30` is word `j + F`, and the caller's frame starts at word
`j + fw F`. The saved `x30` of a suspended activation is the address right after the `bl` of its
call block. -/

/-- The number of words of a frame of `F` slots. -/
def fw (F : Nat) : Nat := fsize F / 8

theorem fw_gt (F : Nat) : F < fw F := by unfold fw fsize; split <;> omega

section Rel
variable (P : Lin.Prog) (A : Asm.Prog arch) (σ : String → Option UInt64) (lo N : Nat)

/-- What the loader must provide at the start of a run. Besides the facts it also provides on x64,
`sp` is 16-byte aligned because `lo` is a multiple of 16 and `N` is even, every function's symbol
is 4-byte aligned, and the `fw W` words of `main`'s frame below the top are zero, where `W` is the
number of words of a frame with `k` preserved and `c` caller-saved register locations
(`Sel.frameW`). -/
structure Init (k c : Nat) (m₀ : State) : Prop where
  world : m₀.world = World.init
  wx : m₀.mem.WxorX
  loaded : A.Loaded σ m₀.mem
  region : Region m₀.mem lo N
  entry : ∃ f, A.funs[P.main]? = some f ∧ σ f.name = some m₀.regs.pc
  aligned : ∀ f ∈ A.funs, ∀ a, σ f.name = some a → a % 4 = 0
  sp : m₀.regs.x 31 = wa lo N
  lo16 : lo % 16 = 0
  even : N % 2 = 0
  zero : ∀ fn, P.funs[P.main]? = some fn → ∀ x, x < fw (Sel.frameW k c fn.frame) →
    word m₀.mem lo (N - fw (Sel.frameW k c fn.frame) + x) = 0
  bound : P.stackBytes (φ.words k c) ≤ 8 * N
  bss : A.BssAt σ m₀.mem
  below : ∀ b ∈ A.bss, ∀ D, σ b.1 = some D → D.toNat + b.2 ≤ lo

end Rel

section Cases
variable (P : Lin.Prog) (A : Asm.Prog arch) (σ : String → Option UInt64) (lo N : Nat)

end Cases

/-! ## Steps and code offsets -/

section Proofs
variable {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s s' : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}
  {ins : Lin.Instr} {κ : CostModel} {ω : Oracle}

theorem aligned_add {p : UInt64} {k : Nat} (h : p % 4 = 0) (hk : k % 4 = 0) :
    (p + UInt64.ofNat k) % 4 = 0 := by grind

theorem seqSize_eq : ∀ (xs : List arch.SInstr), Asm.seqSize arch xs = 4 * xs.length
  | [] => rfl
  | _ :: xs => by simp only [Asm.seqSize, seqSize_eq xs, List.length_cons]; show 4 + _ = _; omega

theorem seqSize_si (xs : List SI) : Asm.seqSize arch xs = 4 * xs.length := seqSize_eq xs

theorem blocksOff_4 : ∀ (bs : List (List arch.SInstr)) (l : Nat), Asm.blocksOff arch bs l % 4 = 0
  | _, 0 => by simp [Asm.blocksOff]
  | [], _ + 1 => by simp [Asm.blocksOff]
  | b :: bs, l + 1 => by simp only [Asm.blocksOff, seqSize_eq]; have := blocksOff_4 bs l; omega

theorem labelOff_4 (f : Asm.Fn arch) (l : Nat) : f.labelOff l % 4 = 0 := by
  simp only [Asm.Fn.labelOff, seqSize_eq]; have := blocksOff_4 f.blocks l; omega

/-- One machine step of an encodable instruction at `pc`. -/
theorem step_one {i : Instr} {m m' : State} {c : Nat} (hh : m.world.halted = false)
    {e : List UInt8} (he : isa.encode i = some e) (hc : m.mem.CodeAt m.regs.pc e)
    (hx : exec (linux.trap ω) i 4 m = some m') : (Sel.M (A := arch) linux).step ω (m, c) = some (m', c + 1) := by
  obtain ⟨-, rfl⟩ := isa_encode he
  exact Sel.step_exec (A := arch) linux laws hh he hc (by rw [bytes_length]; exact hx)

theorem pc_add (p : UInt64) (a b : Nat) :
    p + UInt64.ofNat a + UInt64.ofNat b = p + UInt64.ofNat (a + b) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

/-! ### Plain instructions -/

/-- An instruction that is encodable, does not branch or trap and does not write `sp`. -/
def plain (i : Instr) : Bool :=
  i.valid && !i.branches && !i.isTrap && !decide ((31 : Reg) ∈ i.writes)

theorem straight_all {is : List Instr} (h : ∀ i ∈ is, plain i = true) :
    ∀ i ∈ is, Sel.Straight (A := arch) linux ω i := by
  intro i hi
  have := h i hi
  simp only [plain, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact straight this.1.1.1 (by simpa using this.1.1.2) (by simpa using this.1.2) this.2

/-- Plain instructions none of which writes `x29` keep it. -/
theorem runA_k29 {ω : Oracle} : ∀ {is : List Instr} {t t' : State}, (∀ i ∈ is, plain i = true) →
    (∀ i ∈ is, (29 : Reg) ∉ i.writes) → runA ω is t = some t' → t'.regs.x 29 = t.regs.x 29
  | [], _, _, _, _, h => by cases h; rfl
  | i :: is, t, t', hp, h29, h => by
    rw [runA_cons_eq] at h
    split at h
    · cases h
    · cases hx : exec (linux.trap ω) i (if i.valid then 4 else 0) t with
      | none => rw [hx] at h; cases h
      | some t₁ =>
        rw [hx, Option.bind_some] at h
        have ht : i.isTrap = false := by
          have := hp i List.mem_cons_self
          simp only [plain, Bool.and_eq_true, Bool.not_eq_true'] at this; exact this.1.2
        rw [runA_k29 (fun j hj => hp j (List.mem_cons_of_mem _ hj))
          (fun j hj => h29 j (List.mem_cons_of_mem _ hj)) h, exec_x ht hx 29 (h29 i List.mem_cons_self)]

theorem immIs_plain {d : Reg} (hd : d ≠ 31) (w : UInt64) : ∀ i ∈ immIs d w, plain i = true := by
  have h1 : ¬ d = 31#5 := hd
  have h2 : ¬ 31#5 = d := fun h => hd h.symm
  intro i hi
  simp only [immIs, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩ <;>
    simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, zw, h1, h2]

theorem farPre_plain {s : Reg} (hs : s ≠ 31) (b : Reg) (x : Nat) :
    ∀ i ∈ farPre s b x, plain i = true := by
  have h2 : ¬ 31#5 = s := fun h => hs h.symm
  unfold farPre; split <;> simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, h2]

theorem ldIs_plain {d : Reg} (hd : d ≠ 31) (o : Operand) : ∀ i ∈ ldIs d o, plain i = true := by
  have h1 : ¬ d = 31#5 := hd
  have h2 : ¬ 31#5 = d := fun h => hd h.symm
  cases o with
  | slot y =>
    exact List.forall_mem_append.2 ⟨farPre_plain hd 31 y, by
      simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, zw, h1, h2]⟩
  | imm w => exact immIs_plain hd w

theorem immIs_length (d d' : Reg) (w : UInt64) : (immIs d w).length = (immIs d' w).length := by
  simp [immIs]

theorem farPre_length (s b s' b' : Reg) (x : Nat) :
    (farPre s b x).length = (farPre s' b' x).length := by
  unfold farPre; split <;> rfl

/-! ### Frame accesses

Word `x` above a base register `b` is addressed as `[b, #8x]` when `x < 4096`, and otherwise
through a scratch register `s := b + 4096 ⌊x / 512⌋` as `[s, #8 (x % 512)]`. The frame size is
one `add` or `sub` immediate, shifted left by 12 from 510 slots on. -/

theorem wa16 {lo j : Nat} (hlo : lo % 16 = 0) (hj : j % 2 = 0) (_h : lo + 8 * j < 2 ^ 64) :
    wa lo j % 16 = 0 := by
  apply UInt64.toNat_inj.mp
  simp only [wa, UInt64.toNat_mod, UInt64.toNat_ofNat']
  simp; omega

/-- The value of an `add` or `sub` immediate, `#n` or `#n, lsl 12`. -/
theorem imm_val (n : Nat) (sh : Bool) (hn : n < 4096) :
    (BitVec.ofNat 12 n).toNat.toUInt64 <<< (if sh then 12 else 0) =
      UInt64.ofNat (if sh then 4096 * n else n) := by
  apply UInt64.toNat_inj.mp
  cases sh <;> simp [UInt64.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftLeft_eq] <;> omega

theorem imm_lsl12 (n : Nat) (hn : n < 4096) :
    (BitVec.ofNat 12 n).toNat.toUInt64 <<< 12 = UInt64.ofNat (4096 * n) := by
  simpa using imm_val n true hn

theorem frameI_eq (sub : Bool) (d n : Reg) {F : Nat} (hF : F < maxFrame) :
    ∃ imm sh, frameI sub d n F = .addImm true sub false d n imm sh ∧
      imm.toNat.toUInt64 <<< (if sh then 12 else 0) = UInt64.ofNat (fsize F) := by
  unfold frameI
  split
  · refine ⟨_, false, rfl, ?_⟩
    rw [imm_val _ false (by unfold fsize; split <;> omega)]; simp
  · refine ⟨_, true, rfl, ?_⟩
    rw [imm_val _ true (by unfold fsize maxFrame at *; split <;> omega)]
    simp only [ite_true]; congr 1; unfold fsize; split <;> omega

@[simp] theorem frameI_plain17 (sub : Bool) (F : Nat) : plain (frameI sub 17 31 F) = true := by
  unfold frameI; split <;> simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes]

/-- The value `farPre s b x` leaves in `s`. -/
def farV (s b : Reg) (x : Nat) (r : Regs) : UInt64 :=
  if x < 4096 then r.x s else r.x b + UInt64.ofNat (4096 * (x / 512))

/-- Running `farPre s b x` leaves `farV s b x` in `s`. -/
theorem run_farPre {t : State} (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    {s b : Reg} {x : Nat} (hx : x < 2 ^ 21) :
    runA ω (farPre s b x) t = some (t.goto (t.regs.set s (farV s b x t.regs))
      (t.regs.pc + UInt64.ofNat (4 * (farPre s b x).length))) := by
  unfold farPre farV
  split
  · simp [set_self, goto_self]
  · rw [runA_cons hh rfl (exec_addImm ha _ _ _ _ _ _ _), runA_nil]
    simp only [Bool.false_eq_true, ite_false, ite_true, addSub_add, imm_lsl12 (x / 512) (by omega)]
    rfl

/-- After `farPre s b x`, with `b` at word `i`, the address `farA s b x` is word `i + x`. -/
theorem farA_ea {r : Regs} {s b : Reg} {lo i x : Nat} (hb : r.x b = wa lo i)
    (hs : 4096 ≤ x → r.x s = wa lo i + UInt64.ofNat (4096 * (x / 512))) :
    (farA s b x).ea r .x = wa lo (i + x) := by
  unfold farA; split
  · simp only [Addr.ea, hb, Size.bytes, ← Sel.wa_add_words]
    congr 1; apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_mul, BitVec.toNat_ofNat]; omega
  · simp only [Addr.ea, hs (by omega), Size.bytes, ← Sel.wa_add_words]
    rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_mul, UInt64.toNat_add, BitVec.toNat_ofNat]; omega

theorem farA_aligned {r : Regs} {s b : Reg} (hs : s ≠ 31) (x : Nat)
    (hal : x < 4096 → b = 31 → r.x 31 % 16 = 0) : (farA s b x).aligned r = true := by
  unfold farA; split
  · by_cases hb : b = 31
    · subst hb; simp [Addr.aligned, Addr.base]; exact hal ‹_› rfl
    · simp [Addr.aligned, Addr.base]; exact Or.inl hb
  · simp [Addr.aligned, Addr.base]; exact Or.inl hs

theorem exec_ldr_x {trap : State → Option State} {t : State} {n : Nat} {d : Reg} {ad : Addr}
    {v : UInt64} (ha : t.regs.pc % 4 = 0) (hal : ad.aligned t.regs = true)
    (hr : t.mem.readWord (ad.ea t.regs .x) 8 = some v) :
    exec trap (.ldr .x d ad) n t = some (t.goto (t.regs.setZ d v) (t.regs.pc + 4)) := by
  simp [exec, ha, hal, Size.bytes, hr]

theorem exec_str_x {trap : State → Option State} {t : State} {n : Nat} {d : Reg} {ad : Addr}
    {mem' : Memory} (ha : t.regs.pc % 4 = 0) (hal : ad.aligned t.regs = true)
    (hw : t.mem.writeWord (ad.ea t.regs .x) 8 (t.regs.getZ d) = some mem') :
    exec trap (.str .x d ad) n t = some { t.goto t.regs (t.regs.pc + 4) with mem := mem' } := by
  simp only [Regs.getZ] at hw; simp [exec, ha, hal, Size.bytes]; exact hw

/-- Running `ldIs d (.slot y)` loads slot `y` into `d`, using `d` itself as the scratch register
when the slot is far. -/
theorem run_ldSlot {t : State} {lo N j y : Nat} {d : Reg} (hd : d ≠ 31)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) (hsp : t.regs.x 31 = wa lo j)
    (h16 : t.regs.x 31 % 16 = 0) (hy : y < 2 ^ 21) (hR : Region t.mem lo N) (hk : j + y < N) :
    runA ω (ldIs d (.slot y)) t = some (t.goto (t.regs.set d (word t.mem lo (j + y)))
      (t.regs.pc + UInt64.ofNat (4 * (ldIs d (.slot y)).length))) := by
  have hd' : ¬ 31#5 = d := fun h => hd h.symm
  have hsp' : t.regs.x 31#5 = wa lo j := hsp
  have h16' : t.regs.x 31#5 % 16 = 0 := h16
  have ha1 := aligned_add (k := 4 * (farPre d 31 y).length) ha (Nat.mul_mod_right 4 _)
  rw [ldIs, runA_append, run_farPre hh ha hy, Option.bind_some,
    runA_cons (by simpa using hh) rfl (exec_ldr_x (v := word t.mem lo (j + y)) (by simpa using ha1)
      (farA_aligned hd y (fun _ _ => by simpa [hd'] using h16'))
      (by rw [farA_ea (lo := lo) (i := j) (by simp [hd', hsp'])
            (fun h => by simp [farV, hsp', show ¬ y < 4096 by omega])]
          simpa using Sel.readWord_wa hR hk)), runA_nil]
  simp only [goto_regs, setZ_ne _ hd, set_pc', set_set, goto_goto, List.length_append,
    List.length_singleton]
  rw [UInt64.add_assoc, show (4 : UInt64) = UInt64.ofNat 4 from rfl, ← UInt64.ofNat_add]; rfl

theorem getZ_goto_set {t : State} {k r : Reg} (h : r ≠ k) (v a : UInt64) :
    (t.goto (t.regs.set k v) a).regs.getZ r = t.regs.getZ r := by
  simp [Regs.getZ, h]

/-- Storing `r` into word `x` above the base `b`, which is at word `i`, through `x15` when the
word is far. -/
theorem run_stW {t : State} {lo i x : Nat} {r b : Reg} {mem' : Memory} (hr : r ≠ 15)
    (hb : b ≠ 15) (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (hbv : t.regs.x b = wa lo i) (hal : b = 31 → t.regs.x 31 % 16 = 0) (hx : x < 2 ^ 21)
    (hw : t.mem.writeWord (wa lo (i + x)) 8 (t.regs.getZ r) = some mem') :
    ∃ t', runA ω (farPre 15 b x ++ [Instr.str .x r (farA 15 b x)]) t = some t' ∧
      t'.mem = mem' ∧ t'.world = t.world ∧
      t'.regs.pc = t.regs.pc + UInt64.ofNat (4 * (farPre 15 b x ++ [Instr.str .x r (farA 15 b x)]).length) ∧
      ∀ k : Reg, k ≠ 15 → t'.regs.x k = t.regs.x k := by
  suffices heq : runA ω (farPre 15 b x ++ [Instr.str .x r (farA 15 b x)]) t =
      some { t.goto (t.regs.set 15 (farV 15 b x t.regs)) (t.regs.pc + UInt64.ofNat
        (4 * (farPre 15 b x ++ [Instr.str .x r (farA 15 b x)]).length)) with mem := mem' } from
    ⟨_, heq, rfl, rfl, rfl, fun k hk => by simp [show ¬ k = 15#5 from hk]⟩
  have hb' : ¬ b = 15#5 := hb
  have ha1 := aligned_add (k := 4 * (farPre 15 b x).length) ha (Nat.mul_mod_right 4 _)
  rw [runA_append, run_farPre hh ha hx, Option.bind_some,
    runA_cons (by simpa using hh) rfl (exec_str_x (d := r) (mem' := mem') (by simpa using ha1)
      (farA_aligned (by decide) x (fun _ h => by subst h; simpa using hal rfl))
      (by rw [farA_ea (lo := lo) (i := i) (by simp [hb', hbv])
            (fun h => by simp [farV, hbv, show ¬ x < 4096 by omega])]
          rw [getZ_goto_set hr]; exact hw)), runA_nil]
  simp only [goto_regs, goto_goto, List.length_append, List.length_singleton]
  rw [UInt64.add_assoc, show (4 : UInt64) = UInt64.ofNat 4 from rfl, ← UInt64.ofNat_add]; rfl

/-- Storing `r` into slot `x`. -/
theorem run_stIs {lo j x : Nat} {t : State} (hsp : t.regs.x 31 = wa lo j)
    (h16 : t.regs.x 31 % 16 = 0) (hx : x < maxFrame) {r : Reg} (hr : r ≠ 15) {mem' : Memory}
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (hw : t.mem.writeWord (wa lo (j + x)) 8 (t.regs.getZ r) = some mem') :
    ∃ t', runA ω (stIs x r) t = some t' ∧ t'.mem = mem' ∧ t'.world = t.world ∧
      t'.regs.pc = t.regs.pc + UInt64.ofNat (4 * (stIs x r).length) ∧
      ∀ k : Reg, k ≠ 15 → t'.regs.x k = t.regs.x k :=
  run_stW hr (by decide) hh ha hsp (fun _ => h16) (by unfold maxFrame at *; omega) hw

theorem imm_lsl0 (n : Nat) (hn : n < 4096) :
    (BitVec.ofNat 12 n).toNat.toUInt64 <<< 0 = UInt64.ofNat n := by
  simpa using imm_val n false hn

theorem slotAddr_plain {d : Reg} (hd : d ≠ 31) (x : Nat) : ∀ i ∈ slotAddr d x, plain i = true := by
  have h2 : ¬ 31#5 = d := fun h => hd h.symm
  unfold slotAddr; split <;> simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, h2]

/-- Running `slotAddr d x` leaves the address `sp + 8x` of slot `x` in `d`. -/
theorem run_slotAddr {t : State} {lo j x : Nat} {d : Reg}
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) (hsp : t.regs.x 31 = wa lo j)
    (hx : x < 2 ^ 21) :
    runA ω (slotAddr d x) t = some (t.goto (t.regs.set d (wa lo (j + x)))
      (t.regs.pc + UInt64.ofNat (4 * (slotAddr d x).length))) := by
  unfold slotAddr; split
  · rw [runA_cons hh rfl (exec_addImm ha _ _ _ _ _ _ _), runA_nil]
    simp only [Bool.false_eq_true, ite_false, addSub_add, imm_lsl0 (8 * x) (by omega)]
    rw [hsp, Sel.wa_add_words]; rfl
  · rw [runA_cons hh rfl (exec_addImm ha _ _ _ _ _ _ _), runA_cons (by simpa using hh) rfl
      (exec_addImm (by simpa using aligned_add4 ha) _ _ _ _ _ _ _), runA_nil]
    simp only [Bool.false_eq_true, ite_false, ite_true, addSub_add, goto_regs, Regs.set_x,
      imm_lsl0 (8 * (x % 512)) (by omega), imm_lsl12 (x / 512) (by omega), set_pc', set_set,
      goto_goto]
    rw [hsp, show 4096 * (x / 512) = 8 * (512 * (x / 512)) by omega, Sel.wa_add_words,
      Sel.wa_add_words, show j + 512 * (x / 512) + x % 512 = j + x by omega, UInt64.add_assoc]
    rfl

theorem stIs_plain (x : Nat) (r : Reg) : ∀ i ∈ stIs x r, plain i = true :=
  List.forall_mem_append.2 ⟨farPre_plain (by decide) 31 x, by
    simp only [List.mem_singleton, forall_eq]; rfl⟩

/-! ### Addresses in the data region -/

/-- `adrp d, imm; add d, d, #lo` placed at `q` computes `D`. -/
def SymReach (q : UInt64) (imm : BitVec 21) (lo : BitVec 12) (D : UInt64) : Prop :=
  (q &&& ~~~(0xFFF : UInt64)) + (sext imm <<< 12) + lo.toNat.toUInt64 = D

/-- `symAddr` resolves to an `adrp` and an `add :lo12:` that compute the symbol's address. -/
theorem resolve_symAddr {ρ : Asm.Ref → Option UInt64} {d : Reg} {sym : String}
    {rest : List SI} {q : UInt64} {is : List Instr}
    (h : Asm.resolveAt arch ρ q (symAddr d sym ++ rest) = some is) :
    ∃ D imm lo is', ρ (.sym sym) = some D ∧ SymReach q imm lo D ∧
      is = .adr true d imm :: lo12I d lo :: is' ∧
      Asm.resolveAt arch ρ (q + UInt64.ofNat 8) rest = some is' := by
  obtain ⟨i₁, is₂, h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv h
  obtain ⟨i₂, is', h₃, h₄, rfl⟩ := Asm.resolveAt_cons_inv h₂
  obtain ⟨D, imm, hD, rfl, hreach⟩ := resolve_adrp h₁
  obtain ⟨D', hD', rfl⟩ := resolve_lo12 h₃
  rw [hD] at hD'; cases hD'
  refine ⟨D, imm, _, is', hD, ?_, rfl, ?_⟩
  · unfold SymReach; rw [hreach]; exact page_add_lo12 D
  · rw [show q + UInt64.ofNat 8 = q + UInt64.ofNat 4 + UInt64.ofNat 4 by rw [UInt64.add_assoc]; rfl]
    exact h₄

@[simp] theorem exec_adr {s : State} (h : s.regs.pc % 4 = 0) {trap : State → Option State} {n : Nat}
    (d : Reg) (imm : BitVec 21) : exec trap (.adr false d imm) n s =
    some (s.goto (s.regs.setZ d (s.regs.pc + sext imm)) (s.regs.pc + 4)) := by
  simp [exec, h]

/-- Running `adrp` and `add :lo12:` leaves the symbol's address in `d`. -/
theorem run_symAddr {t : State} (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    {d : Reg} (hd : d ≠ 31) {imm : BitVec 21} {lo : BitVec 12} {D : UInt64}
    (hR : SymReach t.regs.pc imm lo D) :
    runA ω [.adr true d imm, lo12I d lo] t =
      some (t.goto (t.regs.set d D) (t.regs.pc + 8)) := by
  have hd' : ¬ d = 31#5 := hd
  unfold SymReach at hR; subst hR
  simp [runA_cons_eq, hh, ha, aligned_add4, lo12I, addSub_add, exec, hd', Regs.setZ,
    Nat.toUInt64_eq, UInt64.add_assoc, State.goto, Regs.set]
  funext k; split <;> rfl

theorem size_bytes (w : Flat.Width) : (size w).bytes = w.bytes := by cases w <;> rfl

/-- `ldr d, [n]`, where `n` is not `sp`. -/
theorem exec_ldr0 {trap : State → Option State} {t : State} {k : Nat} {sz : Size} {d n : Reg}
    (hn : n ≠ 31) (ha : t.regs.pc % 4 = 0) :
    exec trap (.ldr sz d (.uimm n 0)) k t = (t.mem.readWord (t.regs.x n) sz.bytes).bind
      fun v => some (t.goto (t.regs.setZ d v) (t.regs.pc + 4)) := by
  have hn' : ¬ n = 31#5 := hn
  simp [exec, ha, Addr.aligned, Addr.base, hn', Addr.ea]

/-- `ldr d, ad`, for an address not based on `sp`. -/
theorem exec_ldrA {trap : State → Option State} {t : State} {k : Nat} {sz : Size} {d : Reg}
    {ad : Addr} (hn : ad.base ≠ 31) (ha : t.regs.pc % 4 = 0) :
    exec trap (.ldr sz d ad) k t = (t.mem.readWord (ad.ea t.regs sz) sz.bytes).bind
      fun v => some (t.goto (t.regs.setZ d v) (t.regs.pc + 4)) := by
  have hn' : ¬ ad.base = 31#5 := hn
  simp [exec, ha, Addr.aligned, hn']

/-- `str d, ad`, for an address not based on `sp`. -/
theorem exec_strA {trap : State → Option State} {t : State} {k : Nat} {sz : Size} {d : Reg}
    {ad : Addr} (hn : ad.base ≠ 31) (ha : t.regs.pc % 4 = 0) :
    exec trap (.str sz d ad) k t = (t.mem.writeWord (ad.ea t.regs sz) sz.bytes (t.regs.getZ d)).map
      fun mem => { t.goto t.regs (t.regs.pc + 4) with mem := mem } := by
  have hn' : ¬ ad.base = 31#5 := hn
  simp [exec, ha, Addr.aligned, hn']

/-- `str d, [n]`, where `n` is not `sp`. -/
theorem exec_str0 {trap : State → Option State} {t : State} {k : Nat} {sz : Size} {d n : Reg}
    (hn : n ≠ 31) (ha : t.regs.pc % 4 = 0) :
    exec trap (.str sz d (.uimm n 0)) k t = (t.mem.writeWord (t.regs.x n) sz.bytes (t.regs.getZ d)).map
      fun mem => { t.goto t.regs (t.regs.pc + 4) with mem := mem } := by
  have hn' : ¬ n = 31#5 := hn
  simp [exec, ha, Addr.aligned, Addr.base, hn', Addr.ea]

/-- A block `xs`, `symAddr r ds`, `ys` resolves to `xs`, two straight-line instructions and `ys`,
and running the two instructions after `xs` leaves the symbol's address in `r`. -/
theorem ops_run_sym {ρ : Asm.Ref → Option UInt64} {p Dd : UInt64} {ds : String} {r : Reg}
    {xs ys is : List Instr} (hr : r ≠ 31) (hD : ρ (.sym ds) = some Dd)
    (h : Asm.resolveAt arch ρ p (xs.map Asm.WSI.op ++ symAddr r ds ++ ys.map Asm.WSI.op) = some is) :
    ∃ pre, is = xs ++ pre ++ ys ∧ pre.length = 2 ∧
      (∀ i ∈ pre, plain i = true ∧ ∀ q ∈ i.writes, q = r) ∧
      ∀ (cx : List UInt8) (t : State), Asm.encodeAll isa xs = some cx →
        t.regs.pc = p + UInt64.ofNat cx.length → t.world.halted = false → t.regs.pc % 4 = 0 →
        ∃ t', runA ω pre t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
          t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧ t'.regs.getZ r = Dd ∧
          ∀ r', r' ≠ r → t'.regs.getZ r' = t.regs.getZ r' := by
  have hr' : ¬ r = 31#5 := hr
  have hr'' : ¬ 31#5 = r := fun h => hr h.symm
  rw [List.append_assoc] at h
  obtain ⟨is₁, rfl, h₁⟩ := resolveAt_ops_append (L := xs) h
  obtain ⟨D, imm, lo, is', hD', hreach, rfl, h₂⟩ := resolve_symAddr h₁
  rw [hD] at hD'; cases hD'
  obtain rfl := resolveAt_ops_inv h₂
  refine ⟨[.adr true r imm, lo12I r lo], by simp, rfl, fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
      simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, zw, lo12I, hr''],
    fun cx t hcx hpc hh ha => ⟨_, run_symAddr hh ha hr (by rw [hpc, encodeAll_length hcx]; exact hreach),
      rfl, rfl, by simp [hr''], by simpa using aligned_add (k := 8) ha rfl, by simp [hr'],
      fun r' h => by simp [h]⟩⟩

/-! ### System calls -/

/-- `svc` falls through and keeps `sp`, because the system call writes only `x0`. -/
theorem straight_svc (k : BitVec 16) : Sel.Straight (A := arch) linux ω (.svc k) := by
  intro s s' h
  rw [ilen_valid rfl] at h ⊢
  show s'.regs.pc = s.regs.pc + 4 ∧ s'.regs.x 31 = s.regs.x 31
  change exec (linux.trap ω) (.svc k) 4 s = some s' at h
  by_cases ha : s.regs.pc % 4 = 0
  · simp only [exec, ha, ne_eq, not_true_eq_false, ite_false] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold Abi.trap at hu
    split at hu
    · obtain ⟨mm, -, rfl⟩ := Option.map_eq_some_iff.1 hu
      simp [linux, Abi.linux]
    · cases hu
  · simp [exec, ha] at h

/-- `svc` runs the handler and falls through. -/
theorem ops_run_trap (ω : Oracle) (t t' : State) (ha : t.regs.pc % 4 = 0)
    (h : linux.trap ω t = some t') :
    ∃ t'', exec (linux.trap ω) (.svc 0) (Sel.ilen (A := arch) (.svc 0)) t = some t'' ∧
      t''.mem = t'.mem ∧ t''.world = t'.world ∧ t''.regs.getZ 0 = t'.regs.getZ 0 ∧
      t''.regs.pc % 4 = 0 :=
  ⟨t'.goto t'.regs (t.regs.pc + 4), by rw [ilen_valid rfl]; simp [exec, ha, h], rfl, rfl,
    by simp, by simpa using aligned_add4 ha⟩

/-- `orr d, xzr, r`. -/
theorem ops_run_mv {t : State} {d r : Reg} (hd : d ≠ 31) (hh : t.world.halted = false)
    (ha : t.regs.pc % 4 = 0) :
    ∃ t', runA ω [.logReg .orr true d 31 r] t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧ t'.regs.getZ d = t.regs.getZ r ∧
      ∀ r', r' ≠ d → t'.regs.getZ r' = t.regs.getZ r' := by
  have hd' : ¬ d = 31#5 := hd
  rw [runA_cons hh rfl (exec_logReg (n := 4) ha .orr true d 31 r (by decide))]
  exact ⟨_, rfl, rfl, rfl, by simp [Ne.symm hd'], by simpa using aligned_add4 ha,
    by simp [hd', bin_orr], fun r' h => by simp [hd', h]⟩

/-- Running `immIs d w` loads the constant `w` into `d`. -/
theorem run_imm {t : State} {d : Reg} (hd : d ≠ 31) (w : UInt64) (hh : t.world.halted = false)
    (ha : t.regs.pc % 4 = 0) :
    ∃ t', runA ω (immIs d w) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧ t'.regs.x d = w ∧ ∀ k, k ≠ d → t'.regs.x k = t.regs.x k :=
  ⟨_, run_immIs hd w hh ha, rfl, rfl, by simpa using aligned_add ha (Nat.mul_mod_right 4 _),
    by simp, fun k h => by simp [h]⟩

/-- The part of `read(fd, slot x, 1)` before the trap clears the slot with `str xzr` and sets
`x1 := sp + 8x`, `x2 := 1` and `x8 := 63`. -/
theorem ops_run_rdPre {lo j : Nat} {t : State} {x : Nat} {mz : Memory}
    (hsp : t.regs.x 31 = wa lo j) (h16 : t.regs.x 31 % 16 = 0) (hxm : x < maxFrame)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (hwz : t.mem.writeWord (wa lo (j + x)) 8 0 = some mz) :
    ∃ t', runA ω (stIs x 31 ++ slotAddr 1 x ++ immIs 2 1 ++ immIs 8 63) t = some t' ∧
      t'.mem = mz ∧ t'.world = t.world ∧ t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧
      t'.regs.getZ 8 = 63 ∧ t'.regs.getZ 1 = wa lo (j + x) ∧ t'.regs.getZ 2 = 1 ∧
      t'.regs.getZ 0 = t.regs.getZ 0 ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → r ≠ 2 → r ≠ 8 → t'.regs.x r = t.regs.x r := by
  have hx21 : x < 2 ^ 21 := by unfold maxFrame at hxm; omega
  obtain ⟨t2, x2, hm2, hw2, hpc2, hk2⟩ := run_stIs (ω := ω) (x := x) (r := 31) hsp h16 hxm
    (by decide) hh ha (by simpa using hwz)
  have ha2 : t2.regs.pc % 4 = 0 := by rw [hpc2]; exact aligned_add ha (Nat.mul_mod_right 4 _)
  have hsp2 : t2.regs.x 31 = wa lo j := by rw [hk2 _ (by decide)]; exact hsp
  obtain ⟨t3, x3, hm3, hw3, ha3, hv3, hk3⟩ : ∃ t3, runA ω (slotAddr 1 x) t2 = some t3 ∧
      t3.mem = t2.mem ∧ t3.world = t2.world ∧ t3.regs.pc % 4 = 0 ∧ t3.regs.x 1 = wa lo (j + x) ∧
      ∀ k, k ≠ 1 → t3.regs.x k = t2.regs.x k :=
    ⟨_, run_slotAddr (ω := ω) (d := 1) (by rw [hw2]; exact hh) ha2 hsp2 hx21, rfl, rfl,
      by simpa using aligned_add ha2 (Nat.mul_mod_right 4 _), by simp,
      fun k h => by simp [show ¬ k = 1#5 from h]⟩
  obtain ⟨t4, x4, hm4, hw4, ha4, hv4, hk4⟩ := run_imm (ω := ω) (t := t3) (d := 2) (by decide) 1
    (by rw [hw3, hw2]; exact hh) ha3
  obtain ⟨t5, x5, hm5, hw5, ha5, hv5, hk5⟩ := run_imm (ω := ω) (t := t4) (d := 8) (by decide) 63
    (by rw [hw4, hw3, hw2]; exact hh) ha4
  refine ⟨t5, by rw [runA_append, runA_append, runA_append, x2, Option.bind_some, x3,
    Option.bind_some, x4, Option.bind_some, x5], by rw [hm5, hm4, hm3, hm2],
    by rw [hw5, hw4, hw3, hw2], ?_, ha5, ?_, ?_, ?_, ?_,
    fun r h15 h1 h2 h8 => by rw [hk5 _ h8, hk4 _ h2, hk3 _ h1, hk2 _ h15]⟩
  · rw [hk5 31 (by decide), hk4 31 (by decide), hk3 31 (by decide), hsp2, hsp]
  · rw [getZ_ne (by decide)]; exact hv5
  · rw [getZ_ne (by decide), hk5 _ (by decide), hk4 _ (by decide)]; exact hv3
  · rw [getZ_ne (by decide), hk5 _ (by decide)]; exact hv4
  · rw [getZ_ne (by decide), getZ_ne (by decide), hk5 _ (by decide), hk4 _ (by decide),
      hk3 _ (by decide), hk2 _ (by decide)]

/-- The value that `cmp x0, #1; csinv x16, x16, xzr, eq` computes in the read block is the value
of the call, which is the byte if one was read and `2^64 - 1` otherwise. -/
theorem read_value (res v : UInt64) :
    bin true (fun w x y => if Cond.holds (addSub true true res 1).2 .eq then x else CselOp.csinv.eval w y)
      v 0 = if res = 1 then v else UInt64.ofNat (2 ^ 64 - 1) := by
  rw [(subs_cond res 1).1]
  by_cases h : res = 1 <;> simp [h, bin, CselOp.eval] <;> rfl

/-- The part of `read(fd, slot x, 1)` after the trap is `ldr x16, slot; cmp x0, #1;
csinv x16, x16, xzr, eq`. -/
theorem ops_run_rdFix {lo N j : Nat} {t : State} {x : Nat} (hsp : t.regs.x 31 = wa lo j)
    (h16 : t.regs.x 31 % 16 = 0) (hx21 : x < 2 ^ 21) (hk : j + x < N) (hR : Region t.mem lo N)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) :
    ∃ t', runA ω (ldIs 16 (.slot x) ++ [.addImm true true true 31 0 1 false,
        .csel .csinv true 16 16 31 .eq]) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧
      t'.regs.getZ 16 = (if t.regs.getZ 0 = 1 then word t.mem lo (j + x)
        else UInt64.ofNat (2 ^ 64 - 1)) ∧ ∀ r : Reg, r ≠ 16 → t'.regs.x r = t.regs.x r := by
  rw [runA_append, run_ldSlot (d := 16) (by decide) hh ha hsp h16 hx21 hR hk, Option.bind_some]
  have ha7 := aligned_add (k := 4 * (ldIs 16 (.slot x)).length) ha (Nat.mul_mod_right 4 _)
  simp at ha7
  simp [runA_cons_eq, hh, ha7, Instr.valid]
  rw [exec_csel (by simp [aligned_add4, ha7])]
  simp [State.goto]
  exact ⟨by simpa using aligned_add4 (aligned_add4 ha7),
    read_value _ _, fun r hr => by simp [show ¬ r = 16#5 from hr]⟩

theorem mv_plain {d r : Reg} (hd : d ≠ 31) : plain (.logReg .orr true d 31 r) = true := by
  have hd' : ¬ 31#5 = d := fun h => hd h.symm
  have hd'' : ¬ d = 31#5 := hd
  simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, zw, hd', hd'']

/-! ### Instructions that keep `x29`

With `Options.memBase`, `x29` holds the data region's address for the whole run. An instruction
keeps it when no register it writes is `x29` (`exec_x`), and `svc` keeps it because the handler
writes only `x0`. -/

theorem ne29 {d : Reg} (hd : d ≠ 29) : ¬ (29#5 : Reg) = d := fun e => hd e.symm

theorem zw_k29 {d : Reg} (hd : d ≠ 29) : (29 : Reg) ∉ zw d := by
  unfold zw; split <;> simp [ne29 hd]

theorem immIs_k29 {d : Reg} (hd : d ≠ 29) (w : UInt64) :
    ∀ i ∈ immIs d w, (29 : Reg) ∉ i.writes := by
  intro i hi
  simp only [immIs, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩ <;> exact zw_k29 hd

theorem farPre_k29 {s : Reg} (hs : s ≠ 29) (b : Reg) (x : Nat) :
    ∀ i ∈ farPre s b x, (29 : Reg) ∉ i.writes := by
  unfold farPre; split <;> simp [Instr.writes, ne29 hs]

theorem ldIs_k29 {d : Reg} (hd : d ≠ 29) (o : Operand) : ∀ i ∈ ldIs d o, (29 : Reg) ∉ i.writes := by
  cases o with
  | slot y =>
    exact List.forall_mem_append.2 ⟨farPre_k29 hd 31 y, by
      simp only [List.mem_singleton, forall_eq]; exact zw_k29 hd⟩
  | imm w => exact immIs_k29 hd w

theorem stIs_k29 (x : Nat) (r : Reg) : ∀ i ∈ stIs x r, (29 : Reg) ∉ i.writes :=
  List.forall_mem_append.2 ⟨farPre_k29 (by decide) 31 x, by simp [Instr.writes]⟩

theorem slotAddr_k29 {d : Reg} (hd : d ≠ 29) (x : Nat) : ∀ i ∈ slotAddr d x, (29 : Reg) ∉ i.writes := by
  unfold slotAddr; split <;> simp [Instr.writes, ne29 hd]

theorem mv_k29 {d r : Reg} (hd : d ≠ 29) : (29 : Reg) ∉ (Instr.logReg .orr true d 31 r).writes :=
  zw_k29 hd

/-- `svc` keeps every register but `x0`. -/
theorem exec_svc_x {k : BitVec 16} {s s' : State} (h : exec (linux.trap ω) (.svc k) 4 s = some s')
    (r : Reg) (hr : r ≠ 0) : s'.regs.x r = s.regs.x r := by
  by_cases ha : s.regs.pc % 4 = 0
  · simp only [exec, ha, ne_eq, not_true_eq_false, ite_false] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold Abi.trap at hu
    split at hu
    · obtain ⟨mm, -, rfl⟩ := Option.map_eq_some_iff.1 hu
      have hr' : ¬ r = 0#5 := hr
      simp [linux, Abi.linux, Regs.set_x, hr']
    · cases hu
  · simp [exec, ha] at h

/-! ### Returned words -/

theorem reg_toNat {k : Nat} (hk : k < 32) : (BitVec.ofNat 5 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

theorem reg_ne {k k' : Nat} (hk : k < 32) (hk' : k' < 32) (h : k ≠ k') :
    BitVec.ofNat 5 k ≠ BitVec.ofNat 5 k' := fun e => h (by
  have := congrArg BitVec.toNat e; rwa [reg_toNat hk, reg_toNat hk'] at this)

theorem ea_uimm {r : Regs} {b : Reg} {lo j x : Nat} (hb : r.x b = wa lo j) (hx : x < 4096) :
    (Addr.uimm b (BitVec.ofNat 12 x)).ea r .x = wa lo (j + x) := by
  simp only [Addr.ea, hb, Size.bytes, ← Sel.wa_add_words]
  congr 1
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega

theorem uimm_aligned {r : Regs} {b : Reg} (imm : BitVec 12) (h : b = 31 → r.x 31 % 16 = 0) :
    (Addr.uimm b imm).aligned r = true := by
  by_cases hb : b = 31
  · subst hb; simp [Addr.aligned, Addr.base]; exact h rfl
  · simp [Addr.aligned, Addr.base]; exact Or.inl hb

theorem retStores_plain (b : Reg) : ∀ (n o k : Nat), ∀ i ∈ retStores b o k n, plain i = true
  | 0, _, _ => by simp [retStores]
  | n + 1, o, k => by
    simp only [retStores, List.forall_mem_cons]
    exact ⟨rfl, retStores_plain b n (o + 1) (k + 1)⟩

/-- Running `retStores b o k n`, with the base `b` at word `i`, stores the registers `x_k, …` into
the words `i + o, …`. It changes no register but `pc` and no other word of the region. -/
theorem run_retStores {lo N i : Nat} {b : Reg} : ∀ (n o k : Nat) (t : State),
    t.regs.x b = wa lo i → (b = 31 → t.regs.x 31 % 16 = 0) → Region t.mem lo N →
    o + n ≤ 4096 → i + o + n ≤ N → k + n ≤ 31 → t.world.halted = false → t.regs.pc % 4 = 0 →
    ∃ t', runA ω (retStores b o k n) t = some t' ∧
      t'.regs = { t.regs with pc := t.regs.pc + UInt64.ofNat (4 * n) } ∧ t'.world = t.world ∧
      Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧ Region t'.mem lo N ∧
      ∀ q, q < N → word t'.mem lo q = if i + o ≤ q ∧ q < i + o + n
        then t.regs.x (BitVec.ofNat 5 (k + (q - i - o))) else word t.mem lo q
  | 0, o, k, t, _, _, hR, _, _, _, _, _ => ⟨t, rfl, by simp, rfl, Memory.Frame.refl _,
      Sel.LowSame.refl _ _, hR, fun q _ => by simp; omega⟩
  | n + 1, o, k, t, hb, h16, hR, ho, hiN, hk, hh, ha => by
    obtain ⟨mem1, hw1, hR1, hF1, hv1, hr1⟩ := Sel.writeWord_wa hR (show i + o < N by omega)
      (t.regs.x (BitVec.ofNat 5 k))
    have hk31 : ¬ BitVec.ofNat 5 k = 31#5 := reg_ne (k' := 31) (by omega) (by omega) (by omega)
    have x1 := exec_str_x (trap := linux.trap ω) (n := 4) (d := BitVec.ofNat 5 k) (t := t)
      (ad := .uimm b (BitVec.ofNat 12 o)) ha (uimm_aligned _ h16)
      (by rw [ea_uimm hb (by omega)]; simpa [getZ_eq, hk31] using hw1)
    obtain ⟨t', h2, hregs, hw, hF', hl', hR', hq⟩ := run_retStores n (o + 1) (k + 1)
      { t.goto t.regs (t.regs.pc + 4) with mem := mem1 } (by simpa using hb)
      (fun e => by simpa using h16 e) hR1 (by omega) (by omega) (by omega) (by simpa using hh)
      (by simpa using aligned_add4 ha)
    refine ⟨t', by rw [retStores, runA_cons hh rfl x1, h2], ?_, by simpa using hw,
      hF1.trans hF', (Sel.writeWord_wa_low hR (by omega) hw1).trans hl', hR', fun q hq' => ?_⟩
    · rw [hregs]; simp only [goto_regs, pc_add, show (4 : UInt64) = UInt64.ofNat 4 from rfl]
      rw [show 4 + 4 * n = 4 * (n + 1) by omega]
    · rw [hq q hq']
      by_cases h1 : i + (o + 1) ≤ q ∧ q < i + (o + 1) + n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]; simp; congr 2; omega
      · rw [ite_eq_right h1]
        by_cases h2 : q = i + o
        · subst h2; rw [hv1, ite_eq_left (by omega)]; simp
        · rw [hr1 q hq' h2, ite_eq_right (by omega)]

theorem farProg_le {P : Lin.Prog} (h : farProg P = false) {g : Nat} {fa : Lin.Fn}
    (hfa : P.funs[g]? = some fa) : fa.frame ≤ 4096 := by
  have := List.any_eq_false.1 h fa (List.mem_of_getElem? hfa)
  simpa using this

end Proofs

section Cases
variable {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

theorem fsize_eq (F : Nat) : fsize F = 8 * fw F := by unfold fw fsize; split <;> omega

theorem fw_even (F : Nat) : fw F % 2 = 0 := by unfold fw fsize; split <;> omega

/-- `frameI sub d n F` sets `d` to `n - fsize F` when `sub` holds and to `n + fsize F` otherwise. -/
theorem exec_frameI {t : State} (ha : t.regs.pc % 4 = 0) (sub : Bool) (d n : Reg) {F : Nat}
    (hF : F < maxFrame) : exec (linux.trap ω) (frameI sub d n F) 4 t =
      some (t.goto (t.regs.set d (if sub then t.regs.x n - UInt64.ofNat (fsize F)
        else t.regs.x n + UInt64.ofNat (fsize F))) (t.regs.pc + 4)) := by
  obtain ⟨imm, sh, he, hv⟩ := frameI_eq sub d n hF
  rw [he, exec_addImm ha]
  cases sub <;> simp only [Bool.false_eq_true, ite_false, ite_true, hv, addSub_add, addSub_sub]

theorem frame_sub {lo k F : Nat} (hk : fw F ≤ k) (htop : lo + 8 * k < 2 ^ 64) :
    wa lo k - UInt64.ofNat (fsize F) = wa lo (k - fw F) := by
  rw [fsize_eq]; exact Sel.wa_sub_words hk htop

theorem frame_add (lo k F : Nat) : wa lo k + UInt64.ofNat (fsize F) = wa lo (k + fw F) := by
  rw [fsize_eq]; exact Sel.wa_add_words lo k _

theorem entryIs_length (F : Nat) : (entryIs F).length = 1 + (stIs F 30).length := by
  simp [entryIs]; omega

/-- The entry sequence `sub sp, sp, #fsize F; str x30, [sp, #8F]`, run with `sp` at word `k`,
leaves `sp` at word `k - fw F` and `x30` in word `k - fw F + F`, and keeps every other word.
Throughout the run `sp` is at one of the two words. -/
theorem run_entry {t : State} {lo N k F : Nat} {code : List UInt8} (c : Nat) (hF : F < maxFrame)
    (hk : fw F ≤ k) (hkN : k ≤ N) (hR : Region t.mem lo N) (hsp : t.regs.x 31 = wa lo k)
    (hlo : lo % 16 = 0) (hk2 : k % 2 = 0) (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (hwx : t.mem.WxorX) (he : Asm.encodeAll isa (entryIs F) = some code)
    (hc : t.mem.CodeAt t.regs.pc code) :
    ∃ t', (Sel.M (A := arch) linux).run ω (t, c) (entryIs F).length =
        some (t', c + (entryIs F).length) ∧
      t'.regs.x 31 = wa lo (k - fw F) ∧
      t'.regs.pc = t.regs.pc + UInt64.ofNat (4 * (entryIs F).length) ∧ t'.world = t.world ∧
      Memory.Frame t.mem t'.mem ∧ t'.mem.WxorX ∧ Sel.LowSame lo t.mem t'.mem ∧
      Region t'.mem lo N ∧ word t'.mem lo (k - fw F + F) = t.regs.x 30 ∧
      (∀ q, q < N → q ≠ k - fw F + F → word t'.mem lo q = word t.mem lo q) ∧
      Sel.RunAll (A := arch) linux ω
        (fun x => x.regs.x 31 = wa lo k ∨ x.regs.x 31 = wa lo (k - fw F)) (t, c) (entryIs F).length ∧
      ∀ r : Reg, r ≠ 31 → r ≠ 15 → t'.regs.x r = t.regs.x r := by
  have hgt := fw_gt F
  have htop := hR.top
  obtain ⟨e1, es1, he1, hes1, rfl⟩ := Asm.encodeAll_cons_inv he
  obtain ⟨hc1, hc2⟩ := Sel.codeAt_append _ _ _ _ hc
  obtain ⟨-, rfl⟩ := isa_encode he1
  have x1 := exec_frameI (ω := ω) ha true 31 31 hF (t := t)
  simp only [ite_true, hsp] at x1
  rw [frame_sub hk (by omega)] at x1
  have st1 := step_one (c := c) hh he1 hc1 x1
  have hsp1 : (t.goto (t.regs.set 31 (wa lo (k - fw F))) (t.regs.pc + 4)).regs.x 31 =
      wa lo (k - fw F) := by simp
  obtain ⟨mem', hw, hR', hF', hv, hrest⟩ := Sel.writeWord_wa hR
    (show k - fw F + F < N by omega) (t.regs.x 30)
  obtain ⟨t2, r2, hm2, hw2, -, hx2⟩ := run_stIs (ω := ω) (x := F) (r := 30)
    (t := t.goto (t.regs.set 31 (wa lo (k - fw F))) (t.regs.pc + 4)) hsp1
    (by rw [hsp1]; exact wa16 (j := k - fw F) hlo (by have := fw_even F; omega) (by omega))
    hF (by decide)
    (by simpa using hh) (by simpa using aligned_add4 ha) (by simpa [getZ_eq] using hw)
  obtain ⟨hrun2, hF2, hwx2, hpc2, hall2⟩ := Sel.run_straight (A := arch) (abi := linux) laws
    (s := t.goto (t.regs.set 31 (wa lo (k - fw F))) (t.regs.pc + 4)) (c + 1) hwx hes1
    (by show t.mem.CodeAt (t.regs.pc + 4) es1; rw [bytes_length] at hc2; simpa using hc2)
    (straight_all (stIs_plain F 30)) r2
  have hsp2 : t2.regs.x 31 = wa lo (k - fw F) := by rw [hx2 _ (by decide)]; exact hsp1
  refine ⟨t2, ?_, hsp2, ?_, by rw [hw2]; rfl, hF2, hwx2, hm2 ▸ Sel.writeWord_wa_low hR (by omega) hw,
    hm2 ▸ hR', by rw [hm2, hv], fun q hq hq' => by rw [hm2, hrest q hq hq'], ?_,
    fun r h31 h15 => by rw [hx2 _ h15]; simp [show ¬ r = 31#5 from h31]⟩
  · rw [entryIs_length, Sem.run_add_of (Sem.run_one st1), ← Nat.add_assoc]; exact hrun2
  · rw [show t2.regs.pc = _ from hpc2, encodeAll_length hes1, entryIs_length]
    show t.regs.pc + 4 + _ = _
    rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, pc_add]; congr 2; omega
  · rw [entryIs_length]
    exact Sel.RunAll.add (Sel.RunAll.one (Or.inl hsp) st1 (Or.inr hsp1)) (Sem.run_one st1)
      (Sel.RunAll.mono (fun x h => Or.inr (h.trans hsp1)) hall2)

/-- The entry sequence of a frame of `F` slots followed, when `mb`, by `adrp x29, mp_mem;
add x29, x29, :lo12:mp_mem`, which leaves the data region's address `D` in `x29`. It is
`run_entry` and, when `mb`, two more straight-line steps. -/
theorem run_entryB {t : State} {lo N k F : Nat} {mb : Bool} {ρ : Asm.Ref → Option UInt64}
    {D : UInt64} {ie : List Instr} {code : List UInt8} (c : Nat) (hF : F < maxFrame)
    (hk : fw F ≤ k) (hkN : k ≤ N) (hR : Region t.mem lo N) (hsp : t.regs.x 31 = wa lo k)
    (hlo : lo % 16 = 0) (hk2 : k % 2 = 0) (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (hwx : t.mem.WxorX) (hD : ρ (.sym Sel.memSym) = some D)
    (hr : Asm.resolveAt arch ρ t.regs.pc
      (ops (entryIs F) ++ (if mb then symAddr 29 Sel.memSym else [])) = some ie)
    (he : Asm.encodeAll isa ie = some code) (hc : t.mem.CodeAt t.regs.pc code) :
    ∃ t', (Sel.M (A := arch) linux).run ω (t, c) ie.length = some (t', c + ie.length) ∧
      ie.length = (entryIs F).length + (if mb then 2 else 0) ∧
      t'.regs.x 31 = wa lo (k - fw F) ∧
      t'.regs.pc = t.regs.pc + UInt64.ofNat (4 * ie.length) ∧ t'.world = t.world ∧
      Memory.Frame t.mem t'.mem ∧ t'.mem.WxorX ∧ Sel.LowSame lo t.mem t'.mem ∧
      Region t'.mem lo N ∧ word t'.mem lo (k - fw F + F) = t.regs.x 30 ∧
      (∀ q, q < N → q ≠ k - fw F + F → word t'.mem lo q = word t.mem lo q) ∧
      Sel.RunAll (A := arch) linux ω
        (fun x => x.regs.x 31 = wa lo k ∨ x.regs.x 31 = wa lo (k - fw F)) (t, c) ie.length ∧
      (∀ r : Reg, r ≠ 31 → r ≠ 15 → r ≠ 29 → t'.regs.x r = t.regs.x r) ∧
      t'.regs.x 29 = (if mb then D else t.regs.x 29) := by
  cases mb with
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.append_nil] at hr
    obtain rfl := resolveAt_ops_inv hr
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      run_entry (ω := ω) c hF hk hkN hR hsp hlo hk2 hh ha hwx he hc
    exact ⟨t', h1, rfl, h2, by rw [h3], h4, h5, h6, h7, h8, h9, h10, h11,
      fun r a b _ => h12 r a b, by simpa using h12 29 (by decide) (by decide)⟩
  | true =>
    rw [if_pos rfl] at hr
    rw [show ops (entryIs F) ++ symAddr 29 Sel.memSym =
      (entryIs F).map Asm.WSI.op ++ symAddr 29 Sel.memSym ++ ([] : List Instr).map Asm.WSI.op by
        simp [ops]] at hr
    obtain ⟨pre, rfl, hplen, hpre, hrun⟩ := ops_run_sym (ω := ω) (show (29 : Reg) ≠ 31 by decide) hD hr
    rw [List.append_nil] at he ⊢
    obtain ⟨c₁, c₂, rfl, he₁, he₂⟩ := Sel.encodeAll_append _ _ _ he
    obtain ⟨hc₁, hc₂⟩ := Sel.codeAt_append _ _ _ _ hc
    obtain ⟨t₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      run_entry (ω := ω) c hF hk hkN hR hsp hlo hk2 hh ha hwx he₁ hc₁
    have hpc₁ : t₁.regs.pc = t.regs.pc + UInt64.ofNat c₁.length := by
      rw [h3, encodeAll_length he₁]
    obtain ⟨t₂, r2, hm2, hw2, hsp2, ha2, hv2, hk2'⟩ := hrun c₁ t₁ he₁ hpc₁ (by rw [h4]; exact hh)
      (by rw [h3]; exact aligned_add ha (Nat.mul_mod_right 4 _))
    obtain ⟨hrun2, hF2, hwx2, hpc2, hall2⟩ := Sel.run_straight (A := arch) (abi := linux) laws
      (c + (entryIs F).length) h6 he₂
      (by show t₁.mem.CodeAt t₁.regs.pc c₂; rw [hpc₁]; exact Sel.codeAt_frame hwx h5 _ _ hc₂)
      (straight_all fun i hi => (hpre i hi).1) r2
    have hx : ∀ r : Reg, r ≠ 29 → t₂.regs.x r = t₁.regs.x r := fun r hr => by
      by_cases h31 : r = 31
      · subst h31; exact hsp2
      · have h31' : ¬ r = 31#5 := h31
        have := hk2' r hr; simpa [Regs.getZ, h31'] using this
    refine ⟨t₂, ?_, by simp [hplen], by rw [hx 31 (by decide)]; exact h2, ?_, by rw [hw2, h4],
      h5.trans hF2, hwx2, ?_, Sel.region_frame h8 hF2, ?_, fun q hq hq' => ?_, ?_,
      fun r a b d => by rw [hx r d]; exact h12 r a b, by simpa [Regs.getZ] using hv2⟩
    · rw [List.length_append, ← Nat.add_assoc, Sem.run_add_of h1]; exact hrun2
    · rw [show t₂.regs.pc = t₁.regs.pc + UInt64.ofNat c₂.length from hpc2, hpc₁,
        encodeAll_length he₁, encodeAll_length he₂,
        List.length_append, show 4 * ((entryIs F).length + pre.length) =
          4 * (entryIs F).length + 4 * pre.length by omega, pc_add]
    · rw [show t₂.mem = t₁.mem from hm2]; exact h7
    · rw [show t₂.mem = t₁.mem from hm2]; exact h9
    · rw [show t₂.mem = t₁.mem from hm2]; exact h10 q hq hq'
    · rw [List.length_append]
      exact Sel.RunAll.add h11 h1 (Sel.RunAll.mono (fun x hx' => Or.inr (hx'.trans h2)) hall2)

/-- The sequence `add sp, sp, #fsize F; ret x30`, run with `sp` at word `j`, takes two steps to
the address in `x30` with `sp` at word `j + fw F`, and keeps the memory and every other
register. -/
theorem run_popRet {ω : Oracle} {t : State} {lo j F c : Nat} {code : List UInt8}
    {Q : State → Prop} (hF : F < maxFrame) (hsp : t.regs.x 31 = wa lo j)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0)
    (he : Asm.encodeAll isa [frameI false 31 31 F, .ret 30] = some code)
    (hc : t.mem.CodeAt t.regs.pc code) (hQ : Q t)
    (hQ' : ∀ x : State, x.regs.x 31 = wa lo (j + fw F) → Q x) :
    Sel.Leg (A := arch) linux ω Q t c (1 + 1) ((t.goto (t.regs.set 31 (wa lo (j + fw F)))
      (t.regs.pc + 4)).goto (t.regs.set 31 (wa lo (j + fw F))) (t.regs.x 30)) := by
  obtain ⟨e3, es3, he3, hes3, rfl⟩ := Asm.encodeAll_cons_inv he
  obtain ⟨e4, es4, he4, -, rfl⟩ := Asm.encodeAll_cons_inv hes3
  obtain ⟨hc3, hc4⟩ := Sel.codeAt_append _ _ _ _ hc
  obtain ⟨-, rfl⟩ := isa_encode he3
  have x3 : exec (linux.trap ω) (frameI false 31 31 F) 4 t =
      some (State.goto t (t.regs.set 31 (wa lo (j + fw F))) (t.regs.pc + 4)) := by
    rw [exec_frameI ha false 31 31 hF]; simp only [Bool.false_eq_true, ite_false, hsp, frame_add]
  have x4 : exec (linux.trap ω) (.ret 30) 4 (t.goto (t.regs.set 31 (wa lo (j + fw F)))
      (t.regs.pc + 4)) = some ((t.goto (t.regs.set 31 (wa lo (j + fw F))) (t.regs.pc + 4)).goto
        (t.regs.set 31 (wa lo (j + fw F))) (t.regs.x 30)) := by
    simp only [exec, goto_regs, aligned_add4 ha, ne_eq, not_true_eq_false, ite_false, getZ_eq]
    simp <;> rfl
  exact (Sel.Leg.one (step_one hh he3 hc3 x3) hQ (hQ' _ (by simp))).trans
    (Sel.Leg.one (step_one (by simpa using hh) he4 (by simpa [bytes_length] using
      (Sel.codeAt_append _ _ _ _ hc4).1) x4) (hQ' _ (by simp)) (hQ' _ (by simp)))

end Cases

end Millipede.A64
