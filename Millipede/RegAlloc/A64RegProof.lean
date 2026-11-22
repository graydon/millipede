import Millipede.Target.A64.SelectProof
import Millipede.RegAlloc.A64Reg
import Millipede.Target.PMove

/-!
# arm64 with register locations: the operations and the frame-local cases

This module defines the convention `conv k c` of the register selector `selector k c`, which keeps
the register locations `0 … k-1` in `x19 … x(18+k)` and `k … k+c-1` in the caller-saved
registers (`loc`), and gives the selector's operations `selOps k c mb` as an instance of the shared
selection operations. An operand in a register location is used in place or copied, a result for
a register location is computed into its register or copied there, and every other location is
its frame slot. The convention's clobber set is every caller-saved location at a call.

Once `selOps_laws` and `selOps_ext` show that the operations are lawful, the shared proofs give
the cases of `mov`, `bin`, `load`, `store` and the extern calls. This module proves the cases of
`jmp` and `jz` itself, and `A64RegCall` proves those of `call` and `ret`.
-/

namespace Millipede.RegAlloc.A64Reg

variable {lvo : Option LiveSets} {mb : Bool}

open Flat (Operand BinOp)
open Millipede.A64 (State Regs Reg Instr runA runA_cons runA_append runA_nil arch linux isa
  ldIs stIs immIs farPre farA maxFrame fw fsize symAddr size plain straight_all)

/-- The arm64 frame convention with `k` preserved register locations in `x19, …, x(18+k)` and
`c` caller-saved ones in `x4 … x7, x10 … x14, x8`, which a call destroys and which have no frame
word. The frame of a function with `F` locations has `W = Sel.frameW k c F` words, it is `fw W`
words long and its caller's frame starts `fw W` words above it. Each callee, `main` included,
saves `x30` in word `W` of its own frame, and the return address follows the call sequence. Code
addresses are 4-aligned and `sp` is 16-aligned. With `mb` (`Options.memBase`), `x29` holds the
data region's address (`regOk`). -/
def conv (k c : Nat) (mb : Bool) : Sel.Conv A64.arch where
  φ := A64.φ.words k c
  next F := fw (Sel.frameW k c F)
  last F := fw (Sel.frameW k c F)
  retOff P i pc g args d :=
    4 * (callIs k c 0 (Sel.calleeFrame P g) args (Live.callKeep (Live.of P) P i pc g d args)
      (Live.liveIn (Live.of P) g 0)).length
  dtop := 0
  ok a lo j := a % 4 = 0 ∧ lo % 16 = 0 ∧ j % 2 = 0
  fnAddr b := b % 4 = 0
  k := k
  reg := fun (r : A64.Regs) x => r.x (loc k x)
  c := c
  kill := (cls k c).across
  regOk σ r := mb = true → ∀ D, σ Sel.memSym = some D → r.x 29 = D
  next_gt F := A64.fw_gt _
  last_ge F := Nat.le_of_lt (A64.fw_gt _)

@[simp] theorem conv_k (k c : Nat) : (conv k c mb).k = k := rfl

@[simp] theorem conv_c (k c : Nat) : (conv k c mb).c = c := rfl

/-! ## The registers of the locations -/

theorem preg_toNat {x : Nat} (hx : x < 10) : (preg x).toNat = 19 + x := by
  simp [preg, BitVec.toNat_ofNat]; omega

/-- The register of a location is none of the registers below 19 or above 28. -/
theorem preg_ne {x : Nat} (hx : x < 10) {r : Reg} (hr : r.toNat < 19 ∨ 29 ≤ r.toNat) :
    preg x ≠ r := fun h => by
  have := congrArg BitVec.toNat h; rw [preg_toNat hx] at this; omega

theorem preg_inj {x y : Nat} (hx : x < 10) (hy : y < 10) (h : preg x = preg y) : x = y := by
  have := congrArg BitVec.toNat h; rw [preg_toNat hx, preg_toNat hy] at this; omega

theorem preg_ne31 {x : Nat} (hx : x < 10) : preg x ≠ 31 := preg_ne hx (by decide)

theorem loc_toNat {k c x : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) :
    (loc k x).toNat = if x < k then 19 + x else if x - k < 4 then 4 + (x - k)
      else if x - k < 9 then 6 + (x - k) else if x - k < 10 then 8 else x - k - 10 := by
  unfold loc creg
  split
  · exact preg_toNat (by omega)
  · simp only [BitVec.toNat_ofNat]; split <;> (try split) <;> (try split) <;> omega

theorem loc_of_lt {k x : Nat} (hx : x < k) : loc k x = preg x := by simp [loc, hx]

/-- The registers that are no location's: `x9`, `x15 … x18` and `x29 … x31`. -/
abbrev Free (r : Reg) : Prop :=
  r.toNat = 9 ∨ (15 ≤ r.toNat ∧ r.toNat < 19) ∨ 29 ≤ r.toNat

theorem loc_ne {k c x : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) {r : Reg} (hr : Free r) :
    loc k x ≠ r := fun h => by
  have := congrArg BitVec.toNat h; rw [loc_toNat hk hx] at this
  split at this <;> (try split at this) <;> (try split at this) <;> (try split at this) <;> omega

theorem loc_ne31 {k c x : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) : loc k x ≠ 31 :=
  loc_ne hk hx (by decide)

theorem loc_inj {k c x y : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) (hy : y < k + c)
    (h : loc k x = loc k y) : x = y := by
  have := congrArg BitVec.toNat h; rw [loc_toNat hk hx, loc_toNat hk hy] at this
  split at this <;> split at this <;> (try split at this) <;> (try split at this) <;>
    (try split at this) <;> (try split at this) <;> (try split at this) <;> (try split at this) <;>
    omega

/-- A preserved location's register is no caller-saved location's. -/
theorem preg_ne_loc {k c x y : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < 10) (hy : k ≤ y)
    (hy' : y < k + c) : preg x ≠ loc k y := fun h => by
  have := congrArg BitVec.toNat h; rw [loc_toNat hk hy', preg_toNat hx] at this
  split at this <;> (try split at this) <;> (try split at this) <;> (try split at this) <;> omega

/-! ## Runs of the blocks' pieces -/

section Run
variable {ω : Oracle}

/-- Running `binR d n m op` sets `d` to `n op m` and changes no other register except `x9`, which
`umod` uses. -/
theorem binR_correct (op : BinOp) {s : State} {d n m : Reg} {x y : UInt64}
    (hd : d ≠ 31) (hn : n ≠ 9) (hm : m ≠ 9)
    (hx : s.regs.getZ n = x) (hy : s.regs.getZ m = y) (hh : s.world.halted = false)
    (ha : s.regs.pc % 4 = 0) :
    ∃ s', runA ω (binR d n m op) s = some s' ∧ s'.regs.getZ d = op.eval x y ∧
      s'.regs.pc = s.regs.pc + UInt64.ofNat (4 * (binR d n m op).length) ∧
      s'.regs.x 31 = s.regs.x 31 ∧ s'.mem = s.mem ∧ s'.world = s.world ∧
      ∀ r, r ≠ d → r ≠ 9 → s'.regs.getZ r = s.regs.getZ r := by
  subst hx hy
  have hc := A64.subs_cond (if n = 31#5 then 0 else s.regs.x n) (if m = 31#5 then 0 else s.regs.x m)
  by_cases hd9 : d = 9
  · subst hd9
    have hn' : ¬ n = 9#5 := hn
    have hm' : ¬ m = 9#5 := hm
    cases op <;> simp [binR, cmpSetR, A64.addR, A64.runA_cons_eq, hh, ha,
      A64.aligned_add4, BinOp.eval, A64.addSub_add, A64.addSub_sub, A64.bin_and, A64.bin_orr,
      A64.bin_eor, A64.bin_lsl, A64.bin_lsr, A64.bin_udiv, A64.wid, UInt64.add_assoc, Sel.umod_eq,
      hn', hm', A64.exec, State.goto]
    all_goals (try (intro r h1; simp [h1]; done))
    all_goals refine ⟨(A64.cset_val _ _ (by decide)).trans ?_, fun r h1 => by simp [h1]⟩
    all_goals obtain ⟨h1, h2, h3, h4⟩ := hc
    · simp only [h1, decide_eq_true_eq]; congr
    · simp only [h2, decide_eq_true_eq]; split <;> split <;> simp_all
    · simp only [h3, decide_eq_true_eq]; congr
    · simp only [h4, decide_eq_true_eq]; congr
  have hd' : ¬ d = 31#5 := hd
  have hd'' : ¬ (31#5 : Reg) = d := fun h => hd h.symm
  have hd9' : ¬ d = 9#5 := hd9
  have hn' : ¬ n = 9#5 := hn
  have hm' : ¬ m = 9#5 := hm
  cases op <;> simp [binR, cmpSetR, A64.addR, A64.runA_cons_eq, hh, ha,
    A64.aligned_add4, BinOp.eval, A64.addSub_add, A64.addSub_sub, A64.bin_and, A64.bin_orr,
    A64.bin_eor, A64.bin_lsl, A64.bin_lsr, A64.bin_udiv, A64.wid, UInt64.add_assoc, Sel.umod_eq,
    hd', hd'', hd9', hn', hm', A64.exec, State.goto]
  all_goals (try (intro r h1 h2; simp [h1, h2]; done))
  all_goals refine ⟨(A64.cset_val _ _ (by decide)).trans ?_, fun r h1 h2 => by simp [h1, h2]⟩
  all_goals obtain ⟨h1, h2, h3, h4⟩ := hc
  · simp only [h1, decide_eq_true_eq]; congr
  · simp only [h2, decide_eq_true_eq]; split <;> split <;> simp_all
  · simp only [h3, decide_eq_true_eq]; congr
  · simp only [h4, decide_eq_true_eq]; congr

/-- The facts about a state that has set register `r` and advanced `pc`. -/
theorem set_facts {t : State} {r : Reg} (hr : r ≠ 31) (v : UInt64) (n : Nat)
    (ha : t.regs.pc % 4 = 0) :
    (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).mem = t.mem ∧
    (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).world = t.world ∧
    (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).regs.x 31 = t.regs.x 31 ∧
    (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).regs.pc % 4 = 0 ∧
    (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).regs.getZ r = v ∧
    ∀ r', r' ≠ r → (t.goto (t.regs.set r v) (t.regs.pc + UInt64.ofNat (4 * n))).regs.getZ r' =
      t.regs.getZ r' := by
  have hr' : ¬ (31#5 : Reg) = r := fun h => hr h.symm
  have hr'' : ¬ r = 31#5 := hr
  refine ⟨rfl, rfl, by simp [hr'], by simpa using A64.aligned_add ha (Nat.mul_mod_right 4 n),
    by simp [hr''], fun r' h => by simp [h]⟩

/-- Running the moves `ms` one after the other, as `mv` instructions, sets the registers as the
sequence `Sel.PMove.run` says; with `Sel.PMove.seq_run` this is a parallel move. -/
theorem run_moves : ∀ (ms : List (Reg × Reg)) {t : State}, (∀ p ∈ ms, p.1 ≠ 31) →
    t.world.halted = false → t.regs.pc % 4 = 0 →
    ∃ t', runA ω (ms.map fun p => mv p.1 p.2) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧
      ∀ r, t'.regs.getZ r = Sel.PMove.run t.regs.getZ ms r
  | [], t, _, _, ha => ⟨t, rfl, rfl, rfl, rfl, ha, fun _ => rfl⟩
  | (d, s) :: ms, t, hd, hh, ha => by
    obtain ⟨t₁, h1, m1, w1, x1, a1, g1, o1⟩ :=
      A64.ops_run_mv (ω := ω) (r := s) (hd (d, s) (List.mem_cons_self ..)) hh ha
    obtain ⟨t₂, h2, m2, w2, x2, a2, g2⟩ :=
      run_moves ms (fun p hp => hd p (List.mem_cons_of_mem _ hp)) (w1 ▸ hh) a1
    have he : t₁.regs.getZ = Sel.PMove.step t.regs.getZ d s := funext fun r => by
      by_cases hr : r = d
      · subst hr; simp only [Sel.PMove.step, ite_true]; exact g1
      · simp only [Sel.PMove.step, hr, ite_false]; exact o1 r hr
    refine ⟨t₂, ?_, m2.trans m1, w2.trans w1, x2.trans x1, a2, fun r => ?_⟩
    · show runA ω ([mv d s] ++ ms.map fun p => mv p.1 p.2) t = some t₂
      rw [runA_append]; simp only [mv] at h1 ⊢; rw [h1]; exact h2
    · rw [g2, he]; rfl

end Run

/-! ## The relation at `conv k c` -/

section Match
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}

theorem pc4 (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) : m.regs.pc % 4 = 0 := by
  have h : m.regs.pc = _ := hM.rip
  rw [h]; exact A64.aligned_add hM.ok.1 (A64.labelOff_4 f s.pc)

theorem room_fw (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) :
    j + fw (Sel.frameW k c fn.frame) ≤ N := by
  have hfr := Sel.calleeFrame_eq hM.hfn
  have hF := hM.frames
  cases hst : s.stack with
  | nil => rw [hst] at hF; have := hF.1; rw [hfr] at this; exact Nat.le_of_eq this
  | cons a st =>
    rw [hst] at hF
    have := (Sel.frames_le _ _ _ _ _ hF).2 (by simp)
    rw [hfr] at this; exact this

theorem sp16 (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) : m.regs.x 31 % 16 = 0 := by
  have hsp : m.regs.x 31 = Sel.wa lo j := hM.sp
  have := room_fw hM; have := A64.fw_gt (Sel.frameW k c fn.frame); have htop := hM.region.top
  rw [hsp]; exact A64.wa16 hM.ok.2.1 hM.ok.2.2 (by omega)

/-- A location of the running frame holds its value in its register below `k` and in its slot
otherwise. -/
theorem loc_val (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) {y : Nat} (hy : y < fn.frame) :
    (if y < k + c then m.regs.x (loc k y) else Sel.word m.mem lo (j + y - c)) = s.frame y :=
  hM.locs y hy

end Match

/-! ## Operands -/

section Operands
variable {ω : Oracle} {k c : Nat} {mb : Bool} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64}
  {lo N : Nat} {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat}

/-- What a slot load needs of a state `t` inside the block of a related state `m` whose frame is
at word `j`. The state `t` keeps the region, the words of `m` from `j` on and the `sp` of `m`, and
its `pc` is aligned. -/
structure Words (lo N j : Nat) (m t : State) : Prop where
  region : Sel.Region t.mem lo N
  words : ∀ i, j ≤ i → i < N → Sel.word t.mem lo i = Sel.word m.mem lo i
  sp : t.regs.x 31 = m.regs.x 31
  halted : t.world.halted = false
  pc : t.regs.pc % 4 = 0

/-- What an operand fetch needs, which is `Words` and the location registers of `m`. -/
structure Fetch (k c lo N j : Nat) (m t : State) : Prop extends Words lo N j m t where
  regs : ∀ x, x < k + c → t.regs.getZ (loc k x) = m.regs.getZ (loc k x)

/-- The fetch facts at a related state itself. -/
theorem Fetch.self (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) :
    Fetch k c lo N j m m :=
  ⟨⟨hM.region, fun _ _ _ => rfl, rfl, hM.halted, pc4 hM⟩, fun _ _ => rfl⟩

/-- The fetch facts at a state with the memory of `m`. -/
theorem Fetch.of_mem (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) {t : State}
    (hm : t.mem = m.mem) (hsp : t.regs.x 31 = m.regs.x 31) (hh : t.world.halted = false)
    (ha : t.regs.pc % 4 = 0) (hK : ∀ x, x < k + c → t.regs.getZ (loc k x) = m.regs.getZ (loc k x)) :
    Fetch k c lo N j m t :=
  ⟨⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh, ha⟩, hK⟩

/-- The value of a register location in a state that keeps its register. -/
theorem reg_of_keep (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    {t : State} {y : Nat} (hy : y < fn.frame) (hyk : y < k + c)
    (h : t.regs.getZ (loc k y) = m.regs.getZ (loc k y)) : t.regs.getZ (loc k y) = s.frame y := by
  rw [h, A64.getZ_ne (loc_ne31 hk hyk)]
  have := loc_val hM hy; simp only [hyk, ite_true] at this; exact this

/-- The value of a register location in a fetching state. -/
theorem Fetch.reg (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14) {t : State}
    (hF : Fetch k c lo N j m t) {y : Nat} (hy : y < fn.frame) (hyk : y < k + c) :
    t.regs.getZ (loc k y) = s.frame y := reg_of_keep hM hk hy hyk (hF.regs y hyk)

/-- Running `ldIs` loads an immediate or a slot that is not a register location. -/
theorem run_ldIs_loc (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j)
    (hsm : fn.frame < maxFrame) {t : State} (hF : Words lo N j m t) {r : Reg} (hr : r ≠ 31)
    {o : Operand} (ho : Lin.OpsBelow [o] fn.frame) (hslot : ∀ y, o = .slot y → k + c ≤ y) :
    runA ω (ldIsC c r o) t = some (t.goto (t.regs.set r (o.eval s.frame))
      (t.regs.pc + UInt64.ofNat (4 * (ldIsC c r o).length))) := by
  cases o with
  | imm w => exact A64.run_immIs hr w hF.halted hF.pc
  | slot y =>
    have hy : y < fn.frame := ho y List.mem_cons_self
    have hky := hslot y rfl
    have := room_fw hM; have := A64.fw_gt (Sel.frameW k c fn.frame)
    have := Sel.slot_lt_frameW hy hky
    have hv := loc_val hM hy
    simp only [show ¬ y < k + c by omega, ite_false] at hv
    simp only [ldIsC]
    rw [A64.run_ldSlot hr hF.halted hF.pc (hF.sp.trans hM.sp) (hF.sp ▸ sp16 hM)
      (by unfold maxFrame at hsm; omega) hF.region (by omega), hF.words _ (by omega) (by omega),
      show j + (y - c) = j + y - c by omega, hv]; rfl

/-- Running `ldTo` loads an operand into register `r`, which for a register location is a copy
or nothing. -/
theorem run_ldTo (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {t : State} (hF : Words lo N j m t) {r : Reg} (hr : r ≠ 31)
    {o : Operand} (ho : Lin.OpsBelow [o] fn.frame)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.getZ (loc k y) = m.regs.getZ (loc k y)) :
    ∃ t', runA ω (ldTo k c r o) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧ t'.regs.getZ r = o.eval s.frame ∧
      ∀ r', r' ≠ r → t'.regs.getZ r' = t.regs.getZ r' := by
  by_cases hreg : ∃ y, o = .slot y ∧ y < k + c
  · obtain ⟨y, rfl, hyk⟩ := hreg
    have hy : y < fn.frame := ho y List.mem_cons_self
    by_cases he : loc k y = r
    · have e : ldTo k c r (.slot y) = [] := by simp [ldTo, hyk, he]
      rw [e]
      exact ⟨t, rfl, rfl, rfl, rfl, hF.pc, by rw [← he, reg_of_keep hM hk hy hyk (hK y rfl hyk)]; rfl,
        fun _ _ => rfl⟩
    · have e : ldTo k c r (.slot y) = [mv r (loc k y)] := by simp [ldTo, hyk, he]
      rw [e]
      obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := A64.ops_run_mv (ω := ω) (r := loc k y) hr
        hF.halted hF.pc
      exact ⟨t', h1, h2, h3, h4, h5, by rw [h6, reg_of_keep hM hk hy hyk (hK y rfl hyk)]; rfl, h7⟩
  · have e : ldTo k c r o = ldIsC c r o := by
      cases o with
      | imm w => rfl
      | slot y => simp only [ldTo]; rw [ite_eq_right fun h => hreg ⟨y, rfl, h⟩]
    rw [e, run_ldIs_loc hM hsm hF hr ho fun y hy => by
      subst hy; exact Nat.le_of_not_lt fun h => hreg ⟨y, rfl, h⟩]
    exact ⟨_, rfl, set_facts hr _ _ hF.pc⟩

/-- Running the code of `src` puts an operand into some register, and an operand in a register
location needs no code. -/
theorem run_src (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {t : State} (hF : Words lo N j m t) {r : Reg} (hr : r ≠ 31)
    {o : Operand} (ho : Lin.OpsBelow [o] fn.frame)
    (hK : ∀ y, o = .slot y → y < k + c → t.regs.getZ (loc k y) = m.regs.getZ (loc k y)) :
    ∃ t', runA ω (src k c r o).1 t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧ t'.regs.getZ (src k c r o).2 = o.eval s.frame ∧
      ∀ r', r' ≠ r → t'.regs.getZ r' = t.regs.getZ r' := by
  by_cases hreg : ∃ y, o = .slot y ∧ y < k + c
  · obtain ⟨y, rfl, hyk⟩ := hreg
    have e : src k c r (.slot y) = ([], loc k y) := by simp [src, hyk]
    rw [e]
    exact ⟨t, rfl, rfl, rfl, rfl, hF.pc,
      reg_of_keep hM hk (ho y List.mem_cons_self) hyk (hK y rfl hyk), fun _ _ => rfl⟩
  · have e : src k c r o = (ldIsC c r o, r) := by
      cases o with
      | imm w => rfl
      | slot y => simp only [src]; rw [ite_eq_right fun h => hreg ⟨y, rfl, h⟩]
    rw [e, run_ldIs_loc hM hsm hF hr ho fun y hy => by
      subst hy; exact Nat.le_of_not_lt fun h => hreg ⟨y, rfl, h⟩]
    exact ⟨_, rfl, set_facts hr _ _ hF.pc⟩

end Operands

/-! ## The operations (`Sel.Ops`) -/

/-- The register selector's operations, with `x16` and `x17` as scratch registers. Operands and
results go through `ldTo`, `src` and `stTo` over the locations, a binary operation is `binR` on
any registers, and the system calls are those of `A64.selOps`. -/
def selOps (k c : Nat) (mb : Bool) : Sel.Ops arch where
  Reg := Reg
  get r x := r.getZ x
  r0 := 16
  r1 := 17
  op := .op
  ld := ldTo k c
  src := src k c
  st := stTo k c
  bin op d n m := binR d n m op
  binRes _ d := d
  preg := loc k
  memX := memX k c mb
  memXLen a off := (memX k c mb a off).length
  ea r a off := if mb then r.x 29 + r.getZ (memIx k c a off).2 else r.getZ 16
  ldW w d a off := [.ldr (size w) d (memAd k c mb a off)]
  stW w r a off := [.str (size w) r (memAd k c mb a off)]
  binI := binImm
  stI w v a off := stImm w (memAd k c mb a off) v
  ldOk r := r ≠ 31 ∧ r ≠ 29
  stOk r := r ≠ 15
  binOk n m := n ≠ 9 ∧ m ≠ 9
  Ok t := t.regs.pc % 4 = 0
  nums := LinuxNums.a64
  nrR := 8
  argR i := BitVec.ofNat 5 i
  res := 0
  trap := .svc 0
  mv d r := [mv d r]
  symA := symAddr
  symLen := 2
  rdPre x := stIs (x - c) 31 ++ A64.slotAddr 1 (x - c) ++ immIs 2 1 ++ immIs 8 63
  rdFix x := ldIs 16 (.slot (x - c)) ++
    [.addImm true true true 31 0 1 false, .csel .csinv true 16 16 31 .eq]
  rdRes := 16

theorem fnOk_iff {k c : Nat} {fn : Lin.Fn} :
    (selector k c mb lvo).fnOk fn = true ↔
      (fn.frame < maxFrame ∧ fn.ret.length ≤ 14) ∧ (k ≤ 10 ∧ c ≤ 14) ∧ (c = 0 ∨ fn.ret.length ≤ 4) := by
  simp [selector, A64.fnOk, and_assoc]

theorem select_ok {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} (h : select k c P mb = .ok A) :
    Sel.select (selector k c mb (Live.of P)) P = .ok A := by
  unfold select at h; split at h
  · exact h
  · cases h

/-- An accepted selection with caller-saved locations passed the clobber check. -/
theorem select_clob {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} (h : select k c P mb = .ok A) :
    c = 0 ∨ Live.clobOk (cls k c).across (Live.of P) P = true := by
  unfold select at h; split at h
  · assumption
  · cases h

theorem clob_of_select {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} (h : select k c P mb = .ok A) :
    Sel.ClobOk (conv k c mb) P := by
  rcases select_clob h with rfl | h
  · exact Or.inr fun ins y => by
      simp only [conv, Alloc.Classes.across, cls, Nat.add_zero, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]; omega
  · exact Or.inl h

theorem sel_mov (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (x : Nat) (o : Operand) :
    (selector k c mb lvo).instr P i pc fn (.mov x o) = .ok (((selOps k c mb).movIs (k + c) x o).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.mov x o) = Except.ok (A64.ops ((selOps k c mb).movIs (k + c) x o), [])
  by_cases hx : x < k + c <;> by_cases ho : o = .slot x <;> simp [selInstr, Sel.Ops.movIs, selOps, hx, ho, stTo, A64.ops]
  all_goals first | rfl | exact List.map_append.symm

theorem binOps_eq (k c : Nat) (op : BinOp) (d n : (selOps k c mb).Reg) (o : Operand) :
    (selOps k c mb).binOps op d n o = binOps k c op d n o := by
  cases o <;> rfl

theorem storeIs_eq (k c : Nat) (w : Flat.Width) (a : Operand) (off : UInt64) (b : Operand) :
    (selOps k c mb).storeIs w a off b = storeOps k c w (memAd k c mb a off) b := by
  cases b <;> rfl

theorem sel_bin (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (op : BinOp) (x : Nat)
    (a b : Operand) : (selector k c mb lvo).instr P i pc fn (.bin op x a b) =
      .ok (((selOps k c mb).binIs (k + c) op x a b).map (selOps k c mb).op, []) := by
  simp only [Sel.Ops.binIs, binOps_eq]
  show selInstr k c mb lvo P i pc fn (.bin op x a b) = Except.ok (A64.ops ((src k c 16 a).1 ++
    binOps k c op (dreg k c x 16) (src k c 16 a).2 b ++
    (if x < k + c then [] else stTo k c x (dreg k c x 16))), [])
  simp only [selInstr]
  cases src k c 16 a
  by_cases hx : x < k + c <;> simp [hx, fin, stTo, dreg]

theorem memA_eq (k c : Nat) (a : Operand) (off : UInt64) : (selOps k c mb).memA a off = memAddrR k c a off := by
  simp only [Sel.Ops.memA, Sel.Ops.memPre, binOps_eq]
  show A64.ops ((src k c 16 a).1 ++ binOps k c .add 16 (src k c 16 a).2 (.imm off)) ++
    symAddr 17 Sel.memSym ++ A64.ops [A64.addR 16 16 17] = memAddrR k c a off
  simp only [memAddrR]
  cases src k c 16 a
  rfl

theorem sel_load (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (w : Flat.Width) (x : Nat)
    (a : Operand) (off : UInt64) : (selector k c mb lvo).instr P i pc fn (.load w x a off) =
      .ok ((selOps k c mb).memX a off ++ ((selOps k c mb).loadIs (k + c) w x a off).map (selOps k c mb).op, []) := by
  show selInstr k c mb lvo P i pc fn (.load w x a off) =
    Except.ok (memX k c mb a off ++ A64.ops ([.ldr (size w) (dreg k c x 16) (memAd k c mb a off)] ++
      (if x < k + c then [] else stTo k c x (dreg k c x 16))), [])
  by_cases hx : x < k + c <;> simp [selInstr, hx, stTo, dreg, fin, A64.ops]

theorem sel_store (k c : Nat) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) (w : Flat.Width)
    (a : Operand) (off : UInt64) (b : Operand) : (selector k c mb lvo).instr P i pc fn (.store w a off b) =
      .ok ((selOps k c mb).memX a off ++ ((selOps k c mb).storeIs w a off b).map (selOps k c mb).op, []) := by
  rw [storeIs_eq]
  rfl

theorem memA_length (k c : Nat) (a : Operand) (off : UInt64) :
    ((selOps k c mb).memA a off).length = (selOps k c mb).memLen a off := by
  simp only [Sel.Ops.memA, Sel.Ops.memLen, List.length_append, List.length_map]; rfl

theorem cnt_mov (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (x : Nat) (o : Operand) :
    instrs k c mb lvo P 0 0 fn (.mov x o) = ((selOps k c mb).movIs (k + c) x o).length := by
  have h := sel_mov (lvo := none) (mb := mb) k c P 0 0 fn x o
  simp only [selector] at h
  simp only [instrs, h]; exact List.length_map ..

theorem cnt_bin (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (op : BinOp) (x : Nat) (a b : Operand) :
    instrs k c mb lvo P 0 0 fn (.bin op x a b) = ((selOps k c mb).binIs (k + c) op x a b).length := by
  have h := sel_bin (lvo := none) (mb := mb) k c P 0 0 fn op x a b
  simp only [selector] at h
  simp only [instrs, h]; exact List.length_map ..

theorem cnt_load (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (w : Flat.Width) (x : Nat) (a : Operand)
    (off : UInt64) : instrs k c mb lvo P 0 0 fn (.load w x a off) =
      (selOps k c mb).memXLen a off + ((selOps k c mb).loadIs (k + c) w x a off).length := by
  have h := sel_load (lvo := none) (mb := mb) k c P 0 0 fn w x a off
  simp only [selector] at h
  simp only [instrs, h]
  exact (List.length_append (as := (selOps k c mb).memX a off)).trans (by rw [List.length_map]; rfl)

theorem cnt_store (k c : Nat) (P : Lin.Prog) (fn : Lin.Fn) (w : Flat.Width) (a : Operand)
    (off : UInt64) (b : Operand) : instrs k c mb lvo P 0 0 fn (.store w a off b) =
      (selOps k c mb).memXLen a off + ((selOps k c mb).storeIs w a off b).length := by
  have h := sel_store (lvo := none) (mb := mb) k c P 0 0 fn w a off b
  simp only [selector] at h
  simp only [instrs, h]
  exact (List.length_append (as := (selOps k c mb).memX a off)).trans (by rw [List.length_map]; rfl)

/-! ## The laws (`Sel.Ops.Laws`) -/

section Laws
variable {ω : Oracle}

theorem binR_plain (d n m : Reg) (op : BinOp) : ∀ i ∈ binR d n m op, plain i = true := by
  cases op <;> simp [binR, cmpSetR, plain, A64.addR, Instr.valid, Instr.branches, Instr.isTrap,
    Instr.writes, A64.zw] <;> exact fun h e => h e.symm

theorem ldTo_plain (k c : Nat) {r : Reg} (hr : r ≠ 31) (o : Operand) : ∀ i ∈ ldTo k c r o, plain i = true := by
  cases o with
  | imm w => exact A64.ldIs_plain hr (.imm w)
  | slot y =>
    simp only [ldTo]; split
    · split
      · simp
      · simp only [List.mem_singleton, forall_eq]; exact A64.mv_plain hr
    · exact A64.ldIs_plain hr (.slot (y - c))

theorem src_plain (k c : Nat) {r : Reg} (hr : r ≠ 31) (o : Operand) : ∀ i ∈ (src k c r o).1, plain i = true := by
  cases o with
  | imm w => exact A64.ldIs_plain hr (.imm w)
  | slot y => simp only [src]; split
              · simp
              · exact A64.ldIs_plain hr (.slot (y - c))

theorem stTo_plain {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (x : Nat) (r : Reg) : ∀ i ∈ stTo k c x r, plain i = true := by
  simp only [stTo]; split
  · split
    · simp
    · simp only [List.mem_singleton, forall_eq]; exact A64.mv_plain (loc_ne31 hk ‹_›)
  · exact A64.stIs_plain (x - c) r

/-- `ldr d, A` from the data region, for an address `A` not based on `sp`. -/
theorem run_ldW_reg (w : Flat.Width) {A : A64.Addr} (hA : A.base ≠ 31) {t : State} {d : Reg}
    {Dm : UInt64} {M : Nat} {h : Flat.Heap}
    {ad : UInt64} (hd : d ≠ 31) (hR : Sel.DataRel Dm M t.mem h) (hDM : Dm.toNat + M ≤ 2 ^ 47)
    (hb : ad.toNat + w.bytes ≤ M) (hv : A.ea t.regs (size w) = Dm + ad) (hh : t.world.halted = false)
    (ha : t.regs.pc % 4 = 0) :
    ∃ t' : State, runA ω [.ldr (size w) d A] t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧
      t'.regs.getZ d = h.load w ad ∧ ∀ r, r ≠ d → t'.regs.getZ r = t.regs.getZ r := by
  have hld := Sel.readWord_data hR (by omega) w ad hb
  have hd' : ¬ d = 31#5 := hd
  have hd'' : ¬ (31#5 : Reg) = d := fun e => hd e.symm
  have e : A64.exec (linux.trap ω) (.ldr (size w) d A) 4 t =
      some (t.goto (t.regs.setZ d (h.load w ad)) (t.regs.pc + 4)) := by
    rw [A64.exec_ldrA (trap := linux.trap ω) hA ha, hv, A64.size_bytes, hld]; rfl
  exact ⟨t.goto (t.regs.setZ d (h.load w ad)) (t.regs.pc + 4), by rw [runA_cons hh rfl e]; rfl,
    rfl, rfl, by simp [hd''], A64.aligned_add4 ha,
    by simp [hd'], fun r hr => by simp [hd', hr]⟩

/-- `str r, A` into the data region, for an address `A` not based on `sp`. -/
theorem run_stW_reg (w : Flat.Width) {A : A64.Addr} (hA : A.base ≠ 31) {t : State} {r : Reg}
    {Dm : UInt64} {M : Nat} {h : Flat.Heap}
    {ad v : UInt64} (hR : Sel.DataRel Dm M t.mem h) (hDM : Dm.toNat + M ≤ 2 ^ 47)
    (hb : ad.toNat + w.bytes ≤ M) (hv : A.ea t.regs (size w) = Dm + ad) (hv' : t.regs.getZ r = v)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) :
    ∃ t' : State, runA ω [.str (size w) r A] t = some t' ∧
      Sel.DataRel Dm M t'.mem (h.store w ad v) ∧ Memory.Frame t.mem t'.mem ∧
      (∀ y, ¬ Memory.InRange (Dm + ad) w.bytes y → t'.mem.bytes y = t.mem.bytes y) ∧
      t'.world = t.world ∧ t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.x = t.regs.x := by
  obtain ⟨mem', hwr, hR', hF, hout⟩ := Sel.writeWord_data hR (by omega) w ad v hb
  have e : A64.exec (linux.trap ω) (.str (size w) r A) 4 t =
      some { t.goto t.regs (t.regs.pc + 4) with mem := mem' } := by
    rw [A64.exec_strA (trap := linux.trap ω) hA ha, hv, A64.size_bytes, hv', hwr]
    rfl
  exact ⟨{ t.goto t.regs (t.regs.pc + 4) with mem := mem' }, by rw [runA_cons hh rfl e]; rfl,
    hR', hF, hout, rfl, rfl, rfl⟩

theorem binImm_spec {op : BinOp} {d n : Reg} {w : UInt64} {c : List Instr}
    (h : binImm op d n w = some c) : w.toNat < 4096 ∧
      ∃ sub, op.eval = (if sub then (· - ·) else (· + ·)) ∧
        c = [.addImm true sub false d n (BitVec.ofNat 12 w.toNat) false] := by
  unfold binImm at h
  split at h
  · refine ⟨‹_›, ?_⟩
    split at h
    · cases h; exact ⟨false, rfl, rfl⟩
    · cases h; exact ⟨true, rfl, rfl⟩
    · cases h
  · cases h

/-- `add`/`sub` of an immediate below 4096 sets `d` to `n op w` and changes no other register. -/
theorem run_binImm {op : BinOp} {d n : Reg} {w : UInt64} {c : List Instr} (hc : binImm op d n w = some c)
    {t : State} (hd : d ≠ 31) (hn : n ≠ 31) (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) :
    ∃ t', runA ω c t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.x 31 = t.regs.x 31 ∧
      t'.regs.pc % 4 = 0 ∧ t'.regs.getZ d = op.eval (t.regs.getZ n) w ∧
      ∀ r, r ≠ d → t'.regs.getZ r = t.regs.getZ r := by
  obtain ⟨hw, sub, hop, rfl⟩ := binImm_spec hc
  have hd' : ¬ d = 31#5 := hd
  have hn' : ¬ n = 31#5 := hn
  have hv : (BitVec.ofNat 12 w.toNat).toNat.toUInt64 <<< (if false = true then 12 else 0) = w := by
    simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hw]; simp
  let v := (A64.addSub true sub (t.regs.x n) w).1
  have e : A64.exec (linux.trap ω) (.addImm true sub false d n (BitVec.ofNat 12 w.toNat) false) 4 t =
      some (t.goto (t.regs.set d v) (t.regs.pc + 4)) := by
    simp only [A64.exec, ha]; rw [hv]; rfl
  have hd'' : ¬ (31#5 : Reg) = d := fun e => hd' e.symm
  refine ⟨t.goto (t.regs.set d v) (t.regs.pc + 4), by rw [runA_cons hh rfl e]; rfl, rfl, rfl,
    by simp [hd''], A64.aligned_add4 ha, ?_, fun r hr => by simp [Regs.getZ, hr]⟩
  simp only [A64.goto_regs, Regs.getZ, Regs.set_x, ite_true, v, hop]
  rw [ite_eq_right hd, ite_eq_right hn]
  cases sub
  · exact A64.addSub_add _ _
  · exact A64.addSub_sub _ _

theorem binImm_plain {op : BinOp} {d n : Reg} {w : UInt64} {c : List Instr}
    (hc : binImm op d n w = some c) (hd : d ≠ 31 ∧ d ≠ 29) :
    ∀ i ∈ c, plain i = true ∧ (29 : Reg) ∉ i.writes := by
  obtain ⟨-, sub, -, rfl⟩ := binImm_spec hc
  have hd'' : ¬ (31#5 : Reg) = d := fun e => hd.1 e.symm
  have h29 : ¬ (29#5 : Reg) = d := fun e => hd.2 e.symm
  simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, hd'', h29]

theorem stImm_spec {w : Flat.Width} {ad : A64.Addr} {v : UInt64} {c : List Instr}
    (h : stImm w ad v = some c) : v = 0 ∧ c = [.str (size w) 31 ad] := by
  unfold stImm at h; split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem src16_ne31 {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (a : Operand) : (src k c 16 a).2 ≠ 31 := by
  cases a with
  | slot y =>
    by_cases h : y < k + c
    · simp only [src, h, ite_true]; exact loc_ne31 hk h
    · simp only [src, h, ite_false]; decide
  | imm _ => show (16 : Reg) ≠ 31; decide

end Laws

theorem ldr_plain (sz : A64.Size) (d : Reg) (hd : d ≠ 31) {A : A64.Addr} :
    plain (.ldr sz d A) = true := by
  have hd' : ¬ d = 31#5 := hd
  have hd'' : ¬ (31#5 : Reg) = d := fun e => hd' e.symm
  simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, A64.zw, hd', hd'']

theorem dst_ne {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (x : Nat) : (if x < k + c then loc k x else (16 : Reg)) ≠ 31 := by
  split
  · exact loc_ne31 hk ‹_›
  · decide

/-- The register invariant depends on `x29` only. -/
theorem regOk_of_x29 {k c : Nat} {σ : String → Option UInt64} {r r' : Regs} (h : r'.x 29 = r.x 29)
    (hB : (conv k c mb).regOk σ r) : (conv k c mb).regOk σ r' :=
  fun hm D hD => h.trans (hB hm D hD)

/-- An instruction that `plain` accepts and that does not write `x29` falls through, keeps `sp`
and keeps the convention's register invariant. -/
theorem straightC {k c : Nat} {ω : Oracle} {i : Instr} (hp : plain i = true)
    (h29 : (29 : Reg) ∉ i.writes) : Sel.StraightC (conv k c mb) linux ω i := by
  have ht : i.isTrap = false := by
    simp only [plain, Bool.and_eq_true, Bool.not_eq_true'] at hp; exact hp.1.2
  refine ⟨straight_all (is := [i]) (by simpa using hp) i List.mem_cons_self,
    fun σ (s s' : State) he hB hmb D hD => ?_⟩
  exact (A64.exec_x (n := Sel.ilen (A := arch) i) ht he 29 h29).trans (hB hmb D hD)

theorem straightC_all {k c : Nat} {ω : Oracle} {is : List Instr} (h : ∀ i ∈ is, plain i = true)
    (h29 : ∀ i ∈ is, (29 : Reg) ∉ i.writes) : ∀ i ∈ is, Sel.StraightC (conv k c mb) linux ω i :=
  fun i hi => straightC (h i hi) (h29 i hi)

theorem straightC_svc {k c : Nat} {ω : Oracle} : Sel.StraightC (conv k c mb) linux ω (.svc 0) := by
  refine ⟨A64.straight_svc 0, fun σ (s s' : State) he hB hmb D hD => ?_⟩
  have he' : A64.exec (linux.trap ω) (.svc 0) 4 s = some s' := by
    rw [A64.ilen_valid rfl] at he; exact he
  exact (A64.exec_svc_x he' 29 (by decide)).trans (hB hmb D hD)

theorem binR_k29 {d : Reg} (hd : d ≠ 29) (n m : Reg) (op : BinOp) :
    ∀ i ∈ binR d n m op, (29 : Reg) ∉ i.writes := by
  have h : ¬ (29#5 : Reg) = d := A64.ne29 hd
  cases op <;> simp [binR, cmpSetR, A64.addR, Instr.writes, A64.zw, h]

theorem ldTo_k29 (k c : Nat) {r : Reg} (hr : r ≠ 29) (o : Operand) :
    ∀ i ∈ ldTo k c r o, (29 : Reg) ∉ i.writes := by
  cases o with
  | imm w => exact A64.ldIs_k29 hr (.imm w)
  | slot y =>
    simp only [ldTo]; split
    · split
      · simp
      · simp only [List.mem_singleton, forall_eq]; exact A64.mv_k29 hr
    · exact A64.ldIs_k29 hr (.slot (y - c))

theorem src_k29 (k c : Nat) {r : Reg} (hr : r ≠ 29) (o : Operand) :
    ∀ i ∈ (src k c r o).1, (29 : Reg) ∉ i.writes := by
  cases o with
  | imm w => exact A64.ldIs_k29 hr (.imm w)
  | slot y => simp only [src]; split
              · simp
              · exact A64.ldIs_k29 hr (.slot (y - c))

theorem loc_ne29 {k c x : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) : loc k x ≠ 29 :=
  loc_ne hk hx (by decide)

theorem stTo_k29 {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (x : Nat) (r : Reg) :
    ∀ i ∈ stTo k c x r, (29 : Reg) ∉ i.writes := by
  simp only [stTo]; split
  · split
    · simp
    · simp only [List.mem_singleton, forall_eq]; exact A64.mv_k29 (loc_ne29 hk ‹_›)
  · exact A64.stIs_k29 (x - c) r

/-- The register selector's operations are lawful at `conv k c` for `k ≤ 10`. -/
theorem selOps_laws {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) :
    (selOps k c mb).Laws linux (conv k c mb) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  resolve_op _ _ _ := rfl
  sel_mov := sel_mov k c
  sel_bin := sel_bin k c
  cnt_mov := cnt_mov k c
  cnt_bin := cnt_bin k c
  reg_get r x hx := (A64.getZ_ne (loc_ne31 hk hx)).symm
  preg_inj x y hx hy h := loc_inj hk hx hy h
  preg_ne x hx := ⟨loc_ne (r := 16) hk hx (by decide), loc_ne (r := 17) hk hx (by decide)⟩
  ld_preg x hx := ⟨loc_ne31 hk hx, loc_ne29 hk hx⟩
  ld_nil x o hx h := by
    cases o with
    | imm w => simp [selOps, ldTo, ldIsC, ldIs, immIs] at h
    | slot y =>
      simp only [selOps, ldTo] at h
      split at h
      · split at h
        · rename_i hy hb
          exact congrArg _ (loc_inj hk hy hx (by simpa using hb))
        · cases h
      · exact absurd h (List.ne_nil_of_length_pos (by simp [ldIsC, ldIs]))
  src_reg r o := by
    cases o with
    | imm w => exact Or.inl rfl
    | slot y =>
      show (src k c r (.slot y)).2 = r ∨ ∃ z, z < k + c ∧ (src k c r (.slot y)).2 = loc k z
      simp only [src]; split
      · exact Or.inr ⟨y, ‹_›, rfl⟩
      · exact Or.inl rfl
  ld0 := show (16 : Reg) ≠ 31 ∧ (16 : Reg) ≠ 29 by decide
  ld1 := show (17 : Reg) ≠ 31 ∧ (17 : Reg) ≠ 29 by decide
  r01 := show (17 : Reg) ≠ 16 by decide
  st_pos x r hx := by
    show 0 < (stTo k c x r).length
    simp [stTo, show ¬ x < k + c by simpa using hx, stIs]
  st0 := show (16 : Reg) ≠ 15 by decide
  st_src o := by
    show (src k c 16 o).2 ≠ 15
    cases o with
    | imm w => show (16 : Reg) ≠ 15; decide
    | slot y => simp only [src]; split
                · exact loc_ne hk ‹_› (by decide)
                · show (16 : Reg) ≠ 15; decide
  stBin _ := show (16 : Reg) ≠ 15 by decide
  bin_pos op _ _ _ := by cases op <;> exact Nat.succ_pos _
  binOk_src a b := by
    show (src k c 16 a).2 ≠ 9 ∧ (src k c 17 b).2 ≠ 9
    constructor
    · cases a with
      | imm w => show (16 : Reg) ≠ 9; decide
      | slot y => simp only [src]; split
                  · exact loc_ne hk ‹_› (by decide)
                  · show (16 : Reg) ≠ 9; decide
    · cases b with
      | imm w => show (17 : Reg) ≠ 9; decide
      | slot y => simp only [src]; split
                  · exact loc_ne hk ‹_› (by decide)
                  · show (17 : Reg) ≠ 9; decide
  binOk01 := show (16 : Reg) ≠ 9 ∧ (17 : Reg) ≠ 9 by decide
  binRes_preg _ _ _ := rfl
  straight_ld _ _ o hr := straightC_all (ldTo_plain k c hr.1 o) (ldTo_k29 k c hr.2 o)
  straight_src _ _ o hr := straightC_all (src_plain k c hr.1 o) (src_k29 k c hr.2 o)
  straight_st _ x r _ := straightC_all (stTo_plain hk x r) (stTo_k29 hk x r)
  straight_bin _ op d n m hd := straightC_all (binR_plain d n m op) (binR_k29 hd.2 n m op)
  ok_match hM := pc4 hM
  run_ld hM hok hr ho hm hsp hh ha hK := by
    obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hok
    exact run_ldTo hM hk hsm ⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh, ha⟩ hr.1 ho hK
  run_src hM hok hr ho hm hsp hh ha hK := by
    obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hok
    exact run_src hM hk hsm ⟨hm ▸ hM.region, fun _ _ _ => by rw [hm], hsp, hh, ha⟩ hr.1 ho hK
  run_bin op d n m _ x y hd hnm hx hy hh ha := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := binR_correct (ω := ‹_›) op hd.1 hnm.1 hnm.2
      hx hy hh ha
    exact ⟨t', h1, h5, h6, h4, by show t'.regs.pc % 4 = 0; rw [h3]
                                  exact A64.aligned_add ha (Nat.mul_mod_right 4 _), h2,
      fun z hz hzd _ => h7 _ hzd (loc_ne hk hz (by decide))⟩
  binKill_add := rfl
  kill_bin _ _ _ h := by cases h
  run_st {ω _ _ _ lo _ _ m fn _ _ j t x r _} hM hok hr hkx hx hsp hh ha hw := by
    obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hok
    have e : stTo k c x r = stIs (x - c) r := by simp [stTo, show ¬ x < k + c by simpa using hkx]
    have hsp' : t.regs.x 31 = m.regs.x 31 := hsp
    have hkx' : k + c ≤ x := by simpa using hkx
    obtain ⟨t', h1, h2, h3, -, h5⟩ := A64.run_stIs (ω := ω) (x := x - c) (hsp'.trans hM.sp)
      (by rw [hsp']; exact sp16 hM) (by omega) hr hh ha
      (by rw [show j + (x - c) = j + x - c by omega]; exact hw)
    refine ⟨t', by show runA ω (stTo k c x r) t = _; rw [e]; exact h1, h2, h3, h5 31 (by decide),
      fun z hz => ?_⟩
    show t'.regs.getZ (loc k z) = t.regs.getZ (loc k z)
    unfold Regs.getZ
    rw [h5 _ (loc_ne hk hz (by decide))]
  run_stReg {ω t x r} hx _ hh ha := by
    have hx' : x < k + c := hx
    show ∃ t', runA ω (stTo k c x r) t = some t' ∧ _
    by_cases he : loc k x = r
    · have e : stTo k c x r = [] := by subst he; simp [stTo, hx']
      rw [e]
      exact ⟨t, rfl, rfl, rfl, rfl, by show t.regs.getZ (loc k x) = t.regs.getZ r; rw [he],
        fun _ _ => rfl⟩
    · have e : stTo k c x r = [mv (loc k x) r] := by simp [stTo, hx', beq_false_of_ne he]
      rw [e]
      obtain ⟨t', h1, h2, h3, h4, -, h6, h7⟩ := A64.ops_run_mv (ω := ω) (r := r)
        (loc_ne31 hk hx') hh ha
      exact ⟨t', h1, h2, h3, h4, h6, h7⟩
  bin_add := rfl
  run_sym hr hD h := by
    obtain ⟨pre, h1, h2, h3, h4⟩ := A64.ops_run_sym hr.1 hD h
    exact ⟨pre, h1, h2, fun i hi => straightC (h3 i hi).1 fun e => hr.2 ((h3 i hi).2 _ e).symm, h4⟩
  straight_binI _ _ _ _ _ _ hc hd := fun i hi => straightC (binImm_plain hc hd i hi).1
    (binImm_plain hc hd i hi).2
  binI_pos _ _ _ _ c hc := by obtain ⟨-, -, -, rfl⟩ := binImm_spec hc; exact Nat.one_pos
  run_binI {ω} op d n w c t x hc hd hn hx hh ha := by
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_binImm (ω := ω) hc hd.1 (src16_ne31 hk a) hh ha
    exact ⟨t', h1, h2, h3, h4, h5, h6.trans (by rw [← hx]; rfl), fun z _ hzd _ => h7 _ hzd⟩

theorem memAd_base (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) :
    (memAd k c mb a off).base ≠ 31 := by
  unfold memAd; split
  · show (29 : Reg) ≠ 31; decide
  · show (16 : Reg) ≠ 31; decide

theorem memAd_ea (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) (r : Regs) (sz : A64.Size) :
    (memAd k c mb a off).ea r sz = (selOps k c mb).ea r a off := by
  show _ = if mb then r.x 29 + r.getZ (memIx k c a off).2 else r.getZ 16
  unfold memAd; cases mb <;> simp [A64.Addr.ea, Regs.getZ]

/-- The index of an arm64 access is the shared `ixCode`/`ixReg`. -/
theorem memIx_eq (k c : Nat) (a : Operand) (off : UInt64) :
    memIx k c a off = ((selOps k c mb).ixCode a off, (selOps k c mb).ixReg a off) := by
  unfold memIx Sel.Ops.ixCode Sel.Ops.ixReg Sel.Ops.memPre
  split
  · rfl
  · rw [binOps_eq]; rfl

/-- The index register of an access is `x16` or a location's. -/
theorem memIx_reg {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (a : Operand) (off : UInt64) :
    (memIx k c a off).2 = 16 ∨ ∃ y, y < k + c ∧ (memIx k c a off).2 = loc k y := by
  unfold memIx; split
  · cases a with
    | imm w => exact Or.inl rfl
    | slot y => simp only [src]; split
                · exact Or.inr ⟨y, ‹_›, rfl⟩
                · exact Or.inl rfl
  · exact Or.inl rfl

/-- The register selector's `load` and `store` blocks are lawful at `conv k c` for `k ≤ 10`. -/
theorem selOps_memLaws {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) :
    (selOps k c mb).MemLaws linux (conv k c mb) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  sel_load := sel_load k c
  sel_store := sel_store k c
  cnt_load := cnt_load k c
  cnt_store := cnt_store k c
  run_memX {ω P AP σ lo N s m fn f a j o off Dm L is code} hM hok ho hDm hr hen := by
    cases mb with
    | false =>
      have e : (selOps k c false).memX o off = (selOps k c false).memA o off := by
        rw [memA_eq]; rfl
      rw [e] at hr
      obtain ⟨pre, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        (selOps_laws (lvo := lvo) (mb := false) hk).run_mem hM hok ho hDm hr hen
      exact ⟨pre, t, h1, by rw [h2, ← memA_length, memA_eq]; rfl, h3, h4, h5, h6, h7, h8, h9, h10⟩
    | true =>
      have hO := selOps_laws (lvo := lvo) (mb := true) hk
      obtain ⟨is', rfl, hr'⟩ := A64.resolveAt_ops_append (L := (memIx k c o off).1) hr
      rw [hO.resolveAt_op] at hr'; cases hr'
      obtain ⟨t, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hO.run_ix (ω := ω) hM hok ho off
      have hB := Sel.runIs_regOk h2 h1 hM.regOk rfl Dm hDm
      refine ⟨_, t, rfl, by simp [selOps, memX, A64.ops]; rfl, ?_, ?_, h3, h4, h5, h6, ?_, h8⟩
      · rw [memIx_eq (mb := true)]; exact h2
      · rw [memIx_eq (mb := true)]; exact h1
      · have e : (selOps k c true).ea t.regs o off =
            Regs.x t.regs 29 + Regs.getZ t.regs (memIx k c o off).2 := rfl
        rw [e, memIx_eq (mb := true)]
        erw [hB]; exact congrArg (Dm + ·) h7
  ea_r1 t t' o off h := by
    have hg : ∀ r : Reg, r ≠ 17 → Regs.getZ t' r = Regs.getZ t r := fun r hr => h r hr
    have h29 : Regs.x t' 29 = Regs.x t 29 := by simpa [Regs.getZ] using hg 29 (by decide)
    have hix : Regs.getZ t' (memIx k c o off).2 = Regs.getZ t (memIx k c o off).2 := by
      apply hg
      rcases memIx_reg hk o off with e | ⟨y, hy, e⟩ <;> rw [e]
      · decide
      · exact loc_ne hk hy (r := 17) (by decide)
    show (if mb then Regs.x t' 29 + Regs.getZ t' (memIx k c o off).2 else Regs.getZ t' 16) =
      (if mb then Regs.x t 29 + Regs.getZ t (memIx k c o off).2 else Regs.getZ t 16)
    rw [h29, hix, hg 16 (by decide)]
  straight_ldW _ w d _ _ hd := straightC_all (fun i hi => by
    rw [List.mem_singleton.1 hi]; exact ldr_plain _ d hd.1) (fun i hi => by
    rw [List.mem_singleton.1 hi]; exact A64.zw_k29 hd.2)
  ldW_pos _ _ _ _ := Nat.one_pos
  straight_stW _ w r _ _ := straightC_all (fun i hi => by
    rw [List.mem_singleton.1 hi]; rfl) (fun i hi => by
    rw [List.mem_singleton.1 hi]; simp [Instr.writes])
  stW_pos _ _ _ _ := Nat.one_pos
  run_ldW {ω} w x o off t _ _ _ _ hR hDM hb hv hh ha := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_ldW_reg (ω := ω) w (memAd_base k c mb o off)
      (d := (selOps k c mb).dst (k + c) x) (dst_ne hk x) hR hDM hb
      (by rw [memAd_ea]; exact hv) hh ha
    exact ⟨t', h1, h2, h3, h4, h5, h6, fun z _ hz => h7 _ hz⟩
  straight_stI _ _ _ _ _ _ hc := by
    obtain ⟨-, rfl⟩ := stImm_spec hc
    exact straightC_all (by simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes])
      (by simp [Instr.writes])
  stI_pos _ _ _ _ c hc := by obtain ⟨-, rfl⟩ := stImm_spec hc; exact Nat.one_pos
  run_stI {ω} w v o off c t _ _ _ _ hc hR hDM hb hv hh ha := by
    obtain ⟨rfl, rfl⟩ := stImm_spec hc
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_stW_reg (ω := ω) (r := 31) (v := 0) w
      (memAd_base k c mb o off) hR hDM hb (by rw [memAd_ea]; exact hv)
      (by simp [Regs.getZ]) hh ha
    exact ⟨t', h1, h2, h3, h4, h5, h6, fun z _ => by
      show t'.regs.getZ _ = t.regs.getZ _; simp only [Regs.getZ, h7]⟩
  run_stW {ω} w o off b t _ _ _ _ _ hR hDM hb hv hv' hh ha := by
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_stW_reg (ω := ω) w (memAd_base k c mb o off)
      hR hDM hb (by rw [memAd_ea]; exact hv) hv' hh ha
    exact ⟨t', h1, h2, h3, h4, h5, h6, fun z _ => by
      show t'.regs.getZ _ = t.regs.getZ _; simp only [Regs.getZ, h7]⟩

/-! ## The system calls (`Sel.Ops.ExtLaws`) -/

/-- A Linux system call writes only `x0`. -/
theorem trap_regs {ω : Oracle} {t t' : State} (h : linux.trap ω t = some t') :
    ∃ v, t'.regs = t.regs.set 0 v := by
  unfold Abi.trap at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
  · cases h

theorem preg_low {x : Nat} (hx : x < 10) {r : Nat} (hr : r < 19) : preg x ≠ BitVec.ofNat 5 r :=
  preg_ne hx (Or.inl (by simp [BitVec.toNat_ofNat]; omega))

theorem emit_eq (k c : Nat) : (selOps k c mb).emit = emit k c := by
  funext p; rcases p with ⟨d | d, r | r⟩ <;> rfl

theorem memTail_eq (k c : Nat) (n : UInt64) (x : Nat) (o l : Operand) :
    (selOps k c mb).memTail (k + c) n x o l = memTail k c n x o l := by
  simp only [Sel.Ops.memTail, memTail, emit_eq]; rfl

/-- The code of a `write` or `read` of a buffer is the data address and `memTail`. -/
theorem sel_memTail {k c : Nat} {P : Lin.Prog} {i pc : Nat} {fn : Lin.Fn} {x : Nat}
    {sym : String} {n : UInt64} {o p l : Operand} {args : List Flat.ExtArg}
    (hs : (sym = "write" ∧ n = 64 ∧ args = [.word o, .mem p l]) ∨
      (sym = "read" ∧ n = 63 ∧ args = [.word o, .outMem p l])) {b : List A64.SI}
    {d : List (String × List UInt8)} :
    selInstr k c mb lvo P i pc fn (.ext sym false x args) = .ok (b, d) ↔
      ∃ tl, memTail k c n x o l = some tl ∧ b = memAddrR k c p 0 ++ A64.ops tl ∧ d = [] := by
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [selInstr]
    cases memTail k c _ x o l <;> simp [eq_comm]

/-- The register selector's system calls are lawful at `conv k c` for `k ≤ 10`. -/
theorem selOps_ext {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) :
    (selOps k c mb).ExtLaws linux (conv k c mb) (selector k c mb lvo) (fun P => instrs k c mb lvo P 0 0) where
  linux := ⟨16, Abi.a64LinuxStackTop, _, ⟨fun r => r.x 8, fun i r => r.x (BitVec.ofNat 5 i),
      fun v r => r.set 0 v⟩, rfl, fun _ => rfl,
    fun i _ hi => by match i, hi with | 0, _ | 1, _ | 2, _ => rfl, fun _ _ => rfl⟩
  nums := show LinuxNums.a64.read ≠ LinuxNums.a64.exit ∧ LinuxNums.a64.read ≠ LinuxNums.a64.write ∧
    LinuxNums.a64.write ≠ LinuxNums.a64.exit by decide
  nodup := show [(8 : Reg), 0, 1, 2].Nodup by decide
  r1_sys := show (17 : Reg) ∉ [(8 : Reg), 0, 1, 2, 0] by decide
  preg_rd x hx := loc_ne (r := 16) hk hx (by decide)
  kill_sys x hx h := by
    simp only [conv_k, conv_c] at hx ⊢
    have h' : loc k x ∈ [(8 : Reg), 0, 1, 2, 0] := h
    have e : (loc k x).toNat = 8 ∨ (loc k x).toNat = 0 ∨ (loc k x).toNat = 1 ∨
        (loc k x).toNat = 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with e | e | e | e | e <;> simp [e]
    rw [loc_toNat hk hx] at e
    have hxk : k ≤ x ∧ (x - k = 9 ∨ x - k = 10 ∨ x - k = 11 ∨ x - k = 12) := by
      split at e <;> (try split at e) <;> (try split at e) <;> (try split at e) <;> omega
    refine ⟨hxk.1, fun _ _ _ _ => ?_⟩
    have hc : x - k < c := by omega
    simp only [conv, cls, Alloc.Classes.across, hxk.1, hx, decide_true, Bool.true_and]
    rcases hxk.2 with e | e | e | e <;> rw [e] at hc ⊢ <;> simp [List.mem_filter, hc]
  ld_nr := show (8 : Reg) ≠ 31 ∧ (8 : Reg) ≠ 29 by decide
  ld_arg i hi := by
    show BitVec.ofNat 5 i ≠ 31 ∧ BitVec.ofNat 5 i ≠ 29
    match i, hi with | 0, _ | 1, _ | 2, _ => decide
  st_res := show (0 : Reg) ≠ 15 by decide
  st_rd := show (16 : Reg) ≠ 15 by decide
  straight_trap _ := straightC_svc
  run_trap ω (t : State) (t' : State) ha h := by
    obtain ⟨v, hv⟩ := trap_regs h
    have ha' : t.regs.pc % 4 = 0 := ha
    refine ⟨t'.goto t'.regs (t.regs.pc + 4), ?_, rfl, rfl,
      by show (t'.goto t'.regs (t.regs.pc + 4)).regs.getZ 0 = t'.regs.getZ 0; simp,
      by show (t'.goto t'.regs (t.regs.pc + 4)).regs.pc % 4 = 0; simpa using A64.aligned_add4 ha',
      fun x hx hS => ?_⟩
    · show A64.exec (linux.trap ω) (.svc 0) (Sel.ilen (A := arch) (.svc 0)) t = _
      rw [A64.ilen_valid rfl]; simp [A64.exec, ha']; erw [h]; rfl
    have h0 : loc k x ≠ 0 := fun e => hS (by show loc k x ∈ [(8 : Reg), 0, 1, 2, 0]; rw [e]; simp)
    show (t'.goto t'.regs (t.regs.pc + 4)).regs.getZ (loc k x) = t.regs.getZ (loc k x)
    simp only [A64.goto_regs]
    unfold Regs.getZ
    simp [hv, show ¬ loc k x = 0#5 from h0]
  straight_mv _ d _ hd := straightC_all (fun i hi => by
    obtain rfl : i = _ := List.mem_singleton.1 hi; exact A64.mv_plain hd.1) (fun i hi => by
    obtain rfl : i = _ := List.mem_singleton.1 hi; exact A64.mv_k29 hd.2)
  run_mv hd hh ha := A64.ops_run_mv hd.1 hh ha
  straight_rdPre _ x := straightC_all (List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨A64.stIs_plain (x - c) 31, A64.slotAddr_plain (by decide) (x - c)⟩,
    A64.immIs_plain (by decide) _⟩, A64.immIs_plain (by decide) _⟩)
    (List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨A64.stIs_k29 (x - c) 31, A64.slotAddr_k29 (by decide) (x - c)⟩,
    A64.immIs_k29 (by decide) _⟩, A64.immIs_k29 (by decide) _⟩)
  straight_rdFix _ x := straightC_all (List.forall_mem_append.2 ⟨A64.ldIs_plain (by decide) _, by
    simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, A64.zw]⟩)
    (List.forall_mem_append.2 ⟨A64.ldIs_k29 (by decide) _, by simp [Instr.writes, A64.zw]⟩)
  run_rdPre {ω _ _ _ lo N _ m fn _ _ j t x _} hM hok hkx hx hm hsp hh hOk hwz := by
    obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hok
    have hsp' : t.regs.x 31 = m.regs.x 31 := hsp
    have hkx' : k + c ≤ x := by simpa using hkx
    have e : j + (x - c) = j + x - c := by omega
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := A64.ops_run_rdPre (ω := ω) (x := x - c)
      (hsp'.trans hM.sp) (by rw [hsp']; exact sp16 hM) (by omega) hh hOk (by rw [hm, e]; exact hwz)
    rw [e] at h7
    refine ⟨t', h1, h2, h3, h4, h5, h6, h7, h8, h9, fun z hz hS => ?_⟩
    have hS' : ∀ r : Reg, r ∈ [(8 : Reg), 0, 1, 2, 0] → loc k z ≠ r := fun r hr e =>
      hS (by show loc k z ∈ [(8 : Reg), 0, 1, 2, 0]; rw [e]; exact hr)
    show t'.regs.getZ (loc k z) = t.regs.getZ (loc k z)
    unfold Regs.getZ
    rw [h10 _ (loc_ne hk hz (by decide)) (hS' 1 (by simp)) (hS' 2 (by simp)) (hS' 8 (by simp))]
  run_rdFix {ω _ _ _ lo N _ m fn _ _ j t x} hM hok hkx hx hR hsp hh hOk := by
    obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hok
    have hsp' : t.regs.x 31 = m.regs.x 31 := hsp
    have hkx' : k + c ≤ x := by simpa using hkx
    have := room_fw hM; have := A64.fw_gt (Sel.frameW k c fn.frame)
    have := Sel.slot_lt_frameW hx hkx'
    obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := A64.ops_run_rdFix (ω := ω) (x := x - c)
      (hsp'.trans hM.sp) (by rw [hsp']; exact sp16 hM) (by unfold maxFrame at hsm; omega)
      (by omega) hR hh hOk
    rw [show j + (x - c) = j + x - c by omega] at h6
    refine ⟨t', h1, h2, h3, h4, h5, h6, fun z hz _ => ?_⟩
    show t'.regs.getZ (loc k z) = t.regs.getZ (loc k z)
    unfold Regs.getZ
    rw [h7 _ (loc_ne hk hz (by decide))]
  sel_exit P i pc fn x o := by
    show _ = Except.ok (A64.ops (ldTo k c 0 o ++ (immIs 8 93 ++ []) ++
      [Instr.svc 0] ++ stTo k c x 0), [])
    simp [selector, selInstr, A64.ops]
  cnt_exit P fn x o := by
    show _ = (ldTo k c 0 o ++ (immIs 8 93 ++ []) ++ [Instr.svc 0]).length
    simp [instrs]; rfl
  sel_write P i pc fn x o bs b d h := by
    simp only [selector, selInstr] at h
    split at h
    · cases h
      refine ⟨by assumption, rfl, ?_⟩
      show _ = A64.ops (ldTo k c 0 o) ++ symAddr 1 _ ++ A64.ops (immIs 2 (UInt64.ofNat bs.length) ++
        (immIs 8 64 ++ []) ++ [Instr.svc 0] ++ stTo k c x 0)
      rfl
    · cases h
  cnt_write P fn x o bs := by
    show _ = (ldTo k c 0 o).length + 2 + (immIs 2 (UInt64.ofNat bs.length) ++ (immIs 8 64 ++ []) ++
      [Instr.svc 0] ++ stTo k c x 0).length
    simp [instrs]
  sel_writeMem P i pc fn x o p l b d h := by
    obtain ⟨tl, h1, rfl, rfl⟩ := (sel_memTail (lvo := lvo) (mb := mb) (P := P) (i := i) (pc := pc) (fn := fn) (Or.inl ⟨rfl, rfl, rfl⟩)).1 h
    exact ⟨tl, (memTail_eq k c _ x o l).trans h1, by rw [memA_eq]; rfl, rfl⟩
  sel_readMem P i pc fn x o p l b d h := by
    obtain ⟨tl, h1, rfl, rfl⟩ := (sel_memTail (lvo := lvo) (mb := mb) (P := P) (i := i) (pc := pc) (fn := fn) (Or.inr ⟨rfl, rfl, rfl⟩)).1 h
    exact ⟨tl, (memTail_eq k c _ x o l).trans h1, by rw [memA_eq]; rfl, rfl⟩
  cnt_writeMem P fn x o p l is h := by
    have e := (sel_memTail (lvo := none) (mb := mb) (k := k) (c := c) (P := P) (i := 0) (pc := 0) (fn := fn)
      (x := x) (p := p) (Or.inl ⟨rfl, rfl, rfl⟩)).2 ⟨is, (memTail_eq k c _ x o l).symm.trans h, rfl, rfl⟩
    show (match selInstr k c mb none P 0 0 fn _ with | .ok (b, _) => b.length | .error _ => 0) = _
    rw [e]; show (memAddrR k c p 0 ++ A64.ops is).length = _
    rw [List.length_append, ← memA_eq (mb := mb)]; erw [memA_length]; simp only [A64.ops]; erw [List.length_map]; rfl
  cnt_readMem P fn x o p l is h := by
    have e := (sel_memTail (lvo := none) (mb := mb) (k := k) (c := c) (P := P) (i := 0) (pc := 0) (fn := fn)
      (x := x) (p := p) (Or.inr ⟨rfl, rfl, rfl⟩)).2 ⟨is, (memTail_eq k c _ x o l).symm.trans h, rfl, rfl⟩
    show (match selInstr k c mb none P 0 0 fn _ with | .ok (b, _) => b.length | .error _ => 0) = _
    rw [e]; show (memAddrR k c p 0 ++ A64.ops is).length = _
    rw [List.length_append, ← memA_eq (mb := mb)]; erw [memA_length]; simp only [A64.ops]; erw [List.length_map]; rfl
  sel_read P i pc fn x o b d h := by
    simp only [selector, selInstr] at h
    split at h
    · cases h
    · cases h
      rename_i hx
      refine ⟨Nat.le_of_not_lt hx, rfl, ?_⟩
      show _ = A64.ops (ldTo k c 0 o ++ (stIs (x - c) 31 ++ A64.slotAddr 1 (x - c) ++ immIs 2 1 ++
        immIs 8 63) ++ [Instr.svc 0] ++ (ldIs 16 (.slot (x - c)) ++
        [Instr.addImm true true true 31 0 1 false, Instr.csel .csinv true 16 16 31 .eq]) ++
        stTo k c x 16)
      simp [stTo, hx, A64.ops]
  cnt_read P fn x o := by
    show _ = (ldTo k c 0 o ++ (stIs (x - c) 31 ++ A64.slotAddr 1 (x - c) ++ immIs 2 1 ++
      immIs 8 63) ++ [Instr.svc 0] ++ (ldIs 16 (.slot (x - c)) ++
      [Instr.addImm true true true 31 0 1 false, Instr.csel .csinv true 16 16 31 .eq]) ++
      stTo k c x 16).length
    simp [instrs]

/-! ## Jumps -/

section Jumps
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- The `jmp l` case, whose block is one `b`. -/
theorem simJmp (hsel : select k c P mb = .ok A) (hwf : P.Wf) :
    Sel.StepOk linux (conv k c mb) P A σ lo N (instrs k c mb lvo P 0 0) fun i => ∃ l, i = .jmp l := by
  intro ω κ s s' (m : State) cy fn f a j ins hM hi ⟨l, hl⟩ hs
  subst hl
  obtain ⟨ins', hi', -, he⟩ := Sel.step_fetch_inv hM.run hM.hfn hs
  rw [hi] at hi'; cases hi'
  obtain ⟨b, hC⟩ := Sel.ctx_of A64.asm_laws (select_ok hsel) hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  simp only [selector, selInstr] at hsi
  obtain ⟨rfl, rfl⟩ := hsi
  simp only [Lin.exec, Option.some.injEq] at he
  subst he
  have hl : l < fn.code.length := hC.wf
  obtain ⟨is, code, hr, hen, hcode⟩ := hC.code
  obtain ⟨i', is', h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv hr
  cases h₂
  obtain ⟨t, imm, ht, rfl, hreach⟩ := A64.resolve_b h₁
  rw [Sel.label_addr (by rw [hC.nblocks]; omega)] at ht
  cases ht
  obtain ⟨e, es, he1, -, rfl⟩ := Asm.encodeAll_cons_inv hen
  have hrip : m.regs.pc = _ := hM.rip
  have hx : A64.exec (linux.trap ω) (.b false imm) 4 m =
      some (m.goto m.regs (a + UInt64.ofNat (f.labelOff l))) := by
    have h4 := pc4 hM; simp [A64.exec, h4]; rw [hrip, hreach]
  have hst := A64.step_one (c := cy) hM.halted he1
    (by rw [hrip]; exact (Sel.codeAt_append _ _ _ _ hcode).1) hx
  exact ⟨1, _, Sem.run_one hst, Or.inl ⟨fn, f, a, j, Sel.matchAt_keep hM rfl rfl rfl rfl rfl rfl rfl
    rfl (by show l ≤ _; omega) rfl (fun _ _ => rfl) (regOk_of_x29 rfl hM.regOk)⟩,
    fun h => absurd h (by omega),
    Sel.RunAll.one (Sel.spBound_of_keep hM rfl) hst (Sel.spBound_of_keep hM rfl), by simp [instrs, selInstr]⟩

/-- The `jz o l` case, whose block puts the operand into some register and branches with
`cbz`. -/
theorem simJz (hsel : select k c P mb = .ok A) (hwf : P.Wf) :
    Sel.StepOk linux (conv k c mb) P A σ lo N (instrs k c mb lvo P 0 0) fun i => ∃ c l, i = .jz c l := by
  intro ω κ s s' (m : State) cy fn f a j ins hM hi ⟨o, l, hx⟩ hs
  subst hx
  obtain ⟨ins', hi', -, he⟩ := Sel.step_fetch_inv hM.run hM.hfn hs
  rw [hi] at hi'; cases hi'
  obtain ⟨b, hC⟩ := Sel.ctx_of A64.asm_laws (select_ok hsel) hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  obtain ⟨⟨hsm, -⟩, hk, -⟩ := fnOk_iff.1 hC.sel.ok
  have hb : b = A64.ops (src k c 16 o).1 ++ [.fix .cond19 (.cbz true false (src k c 16 o).2 0) (.label l)] := by
    simp only [selector, selInstr] at hsi
    cases hsi; rfl
  subst hb
  simp only [Lin.exec, Option.some.injEq] at he
  subst he
  obtain ⟨ho, hl⟩ := hC.wf
  have hlt := Sel.pc_lt hi
  obtain ⟨is, code, hr, hen, hcode⟩ := hC.code
  obtain ⟨is', rfl, hr'⟩ := A64.resolveAt_ops_append hr
  obtain ⟨i', rfl, h₁⟩ := A64.resolveAt_single hr'
  obtain ⟨t, imm, ht, rfl, hreach⟩ := A64.resolve_cbz h₁
  rw [Sel.label_addr (by rw [hC.nblocks]; omega)] at ht
  cases ht
  obtain ⟨c₁, c₂, rfl, he₁, he₂⟩ := Sel.encodeAll_append _ _ _ hen
  obtain ⟨e, es, he3, -, rfl⟩ := Asm.encodeAll_cons_inv he₂
  obtain ⟨hc₁, hc₂⟩ := Sel.codeAt_append _ _ _ _ hcode
  have hrip : m.regs.pc = _ := hM.rip
  obtain ⟨t1, h1, hm1, hw1, hsp1, ha1, hv1, hk1⟩ := run_src (ω := ω) hM hk hsm
    (Fetch.self hM).toWords (r := 16) (by decide) ho (fun _ _ _ => rfl)
  obtain ⟨hrun, hF, -, hpc1, hall⟩ := Sel.run_straight (A := arch) (abi := linux) A64.laws cy hM.wx he₁
    (by rw [hM.rip]; exact hc₁) (straight_all (ω := ω) (src_plain k c (r := 16) (by decide) o)) h1
  have hlen := A64.encodeAll_length he₁
  have hpc1' : t1.regs.pc = a + UInt64.ofNat (f.labelOff s.pc) + UInt64.ofNat (4 * (src k c 16 o).1.length) := by
    have hpc1x : t1.regs.pc = m.regs.pc + UInt64.ofNat c₁.length := hpc1
    rw [hpc1x, hrip, hlen]
  have hnext : a + UInt64.ofNat (f.labelOff s.pc) + UInt64.ofNat (4 * (src k c 16 o).1.length) + 4 =
      a + UInt64.ofNat (f.labelOff (s.pc + 1)) := by
    have hseq : Asm.seqSize arch (A64.ops (src k c 16 o).1 ++
        [.fix .cond19 (.cbz true false (src k c 16 o).2 0) (.label l)]) =
        4 * (src k c 16 o).1.length + 4 := by
      rw [A64.seqSize_eq]; erw [List.length_append, List.length_map]; rfl
    rw [Sel.labelOff_succ f hC.blk, hseq, show (4 : UInt64) = UInt64.ofNat 4 from rfl,
      UInt64.add_assoc, UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add]
  have hx : A64.exec (linux.trap ω) (.cbz true false (src k c 16 o).2 imm) 4 t1 = some (t1.goto t1.regs
      (a + UInt64.ofNat (f.labelOff (if o.eval s.frame = 0 then l else s.pc + 1)))) := by
    simp only [A64.exec, ha1, ne_eq, not_true_eq_false, ite_false, hv1]
    rw [hpc1', hreach, hnext]
    by_cases hz : o.eval s.frame = 0 <;> simp [hz, A64.wid]
  have hst := A64.step_one (c := cy + (src k c 16 o).1.length) (by rw [hw1]; exact hM.halted) he3
    (by rw [hpc1', ← hlen]; exact Sel.codeAt_frame hM.wx hF _ _ (Sel.codeAt_append _ _ _ _ hc₂).1) hx
  have hcnt : instrs k c mb lvo P 0 0 fn (.jz o l) = (src k c 16 o).1.length + 1 := by
    simp [instrs, selInstr, A64.ops]
  refine ⟨(src k c 16 o).1.length + 1, _, (Sem.run_add_of hrun 1).trans (Sem.run_one hst),
    Or.inl ⟨fn, f, a, j, Sel.matchAt_keep hM rfl rfl rfl rfl rfl (show t1.mem = m.mem from hm1)
      (show t1.world = m.world from hw1) (show t1.regs.x 31 = m.regs.x 31 from hsp1)
      (by show (if o.eval s.frame = 0 then l else s.pc + 1) ≤ fn.code.length; split <;> omega) rfl
      (fun x hx => ?_) (regOk_of_x29 (by
        have := hk1 (29 : Reg) (by decide); simpa [Regs.getZ] using this) hM.regOk)⟩,
    fun h => absurd h (by omega),
    Sel.RunAll.add (Sel.RunAll.mono (fun _ h => Sel.spBound_of_keep hM h) hall) hrun
      (Sel.RunAll.one (Sel.spBound_of_keep hM hsp1) hst
        (Sel.spBound_of_keep hM (show t1.regs.x 31 = m.regs.x 31 from hsp1))), hcnt.symm⟩
  show t1.regs.x (loc k x) = m.regs.x (loc k x)
  have := hk1 (loc k x) (loc_ne hk hx (by decide))
  simp only [A64.getZ_eq, loc_ne31 hk hx, ite_false] at this
  simpa using this

end Jumps

/-! ## The cases -/

theorem selInstr_ext {k c : Nat} {P : Lin.Prog} {i pc : Nat} {fn : Lin.Fn} {sym : String} {nr : Bool}
    {x : Nat} {args : List Flat.ExtArg} {b : List A64.SI} {d : List (String × List UInt8)}
    (h : (selector k c mb lvo).instr P i pc fn (.ext sym nr x args) = .ok (b, d)) :
    Sel.ExtShape sym nr args := by
  simp only [selector, selInstr] at h
  split at h
  · exact Or.inl ⟨_, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, rfl, rfl⟩)))
  · cases h

end Millipede.RegAlloc.A64Reg
