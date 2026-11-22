import Millipede.Target.X64.SelectProof
import Millipede.RegAlloc.Live

/-!
# Correctness of x64 calls, returns and entry

This module proves the `call` and `ret` cases of the x64 selector with `k ≤ 6` preserved and
`c ≤ 3` caller-saved register locations, and assembles all the cases into the package of laws
that the shared simulation needs. A call saves the caller's location registers below `min k G` in the callee's frame words,
where `G` is the size of the callee's frame, so a register location of a suspended activation is
found in the frame of the activation it called.

A call block runs in order. It saves the caller's location registers, writes the memory
arguments while the caller's registers are still in place, and loads the preserved register
arguments, reading an argument whose register was already overwritten back from its save word,
and then the caller-saved ones (`run_cArgs`: the parallel move, then the loads). Then
`call` pushes the return address and the callee's `sub rsp` sets up its frame. A return block
loads the returned words into the return registers, restores the location registers, pops the
frame with `add rsp` and runs `ret`, after which the caller's code moves each returned word to its
location. The caller-saved locations the call does not define are destroyed, so the state after
the return is related to Lin's only up to them (`Sel.matchAt_ret_kill`).

The main declarations are `sim_call`, `sim_ret`, `cases`, the loader's start state `Init`,
`sim_entry`, the package `pkg k` and `pkg_laws`.
-/

namespace Millipede.X64

open Flat (Operand BinOp)

set_option allowUnsafeReducibility true in
attribute [local reducible] isa

open Sel

/- `simp` proves straight-line side conditions from the equations of `Instr.writes` and
`Instr.branches`, as in SelectProof.lean. -/
attribute [local simp] Instr.keepsSp_iff Instr.branches.eq_5 Alu.writes Instr.writes.eq_1
  Instr.writes.eq_2 Instr.writes.eq_3 Instr.writes.eq_4 Instr.writes.eq_5 Instr.writes.eq_6
  Instr.writes.eq_7 Instr.writes.eq_8 Instr.writes.eq_9 Instr.writes.eq_10 Instr.writes.eq_11
  Instr.writes.eq_12 Instr.writes.eq_13 Instr.writes.eq_14 Instr.writes.eq_15 Instr.writes.eq_16
  Instr.writes.eq_17 Instr.writes.eq_18 Instr.writes.eq_19 Instr.writes.eq_20 Instr.writes.eq_21

/-! ### Pieces of calls and returns -/

/-- Storing register `r` at `[rsp + d]`, with `rsp` at stack word `j` and the address at word
`q`, sets word `q` to `r` and keeps every other word of the region. -/
theorem exec_store_word {trap : State → Option State} {s : State} {lo N j q : Nat} {d : UInt32}
    {r : Reg} {n : Nat} (hR : Region s.mem lo N) (hsp : s.regs.gpr .rsp = wa lo j)
    (hd : wa lo j + sext32 d = wa lo q) (hq : q < N) :
    ∃ s', exec trap (.store (.base .rsp d) r) n s = some s' ∧ s'.world = s.world ∧
      s'.regs.gpr = s.regs.gpr ∧ s'.regs.rip = s.regs.rip + UInt64.ofNat n ∧
      Region s'.mem lo N ∧ Memory.Frame s.mem s'.mem ∧ LowSame lo s.mem s'.mem ∧
      ∀ i, i < N → word s'.mem lo i = if i = q then s.regs.gpr r else word s.mem lo i := by
  obtain ⟨m', hs, hR', hF, hv, hrest⟩ := store_wa hR hq (s.regs.gpr r)
  refine ⟨{ s with mem := m', regs := { s.regs with rip := s.regs.rip + UInt64.ofNat n } },
    by simp only [exec, Mem.addr, hsp, hd, hs, Option.map_some], rfl, rfl, rfl, hR', hF,
    store_wa_low hR hq hs, fun i hi => ?_⟩
  split
  · subst i; exact hv
  · exact hrest i hi ‹_›

/-- The address of word `x` of a callee frame of `G` slots, relative to the caller's `rsp` at
word `j`, is stack word `j - 1 - G + x`. -/
theorem calleeMem_addr {lo j G x : Nat} (hG : 8 * (G + 1) ≤ 2 ^ 31) (hjG : G + 1 ≤ j) (hx : x < G) :
    wa lo j + sext32 (0 - UInt32.ofNat (8 * (G - x) + 8)) = wa lo (j - 1 - G + x) := by
  rw [show 8 * (G - x) + 8 = 8 * (G - x + 1) by omega, below_addr (by omega) (by omega) (by omega)]
  congr 1; omega

/-- What a run of stores to stack words keeps of a state: the world, the registers, the region,
the permissions and every byte below the region. -/
structure Stored (lo N : Nat) (t t' : State) : Prop where
  world : t'.world = t.world
  regs : t'.regs.gpr = t.regs.gpr
  region : Region t'.mem lo N
  frame : Memory.Frame t.mem t'.mem
  low : LowSame lo t.mem t'.mem

theorem Stored.refl {lo N : Nat} {t : State} (hR : Region t.mem lo N) : Stored lo N t t :=
  ⟨rfl, rfl, hR, Memory.Frame.refl _, LowSame.refl _ _⟩

theorem Stored.trans {lo N : Nat} {t₁ t₂ t₃ : State} (h₁ : Stored lo N t₁ t₂) (h₂ : Stored lo N t₂ t₃) :
    Stored lo N t₁ t₃ :=
  ⟨h₂.world.trans h₁.world, h₂.regs.trans h₁.regs, h₂.region, h₁.frame.trans h₂.frame,
    h₁.low.trans h₂.low⟩

/-- The saves store the `n` location registers from `x` on that `keep` names into the callee
frame words from `j - 1 - G + x` on, and change no other word. -/
theorem run_saves {ω : Oracle} {lo N j G : Nat} (keep : Nat → Bool) (hG : 8 * (G + 1) ≤ 2 ^ 31)
    (hjG : G + 1 ≤ j) (hjN : j ≤ N) : ∀ (n x : Nat) (t : State), Region t.mem lo N →
    t.regs.gpr .rsp = wa lo j → t.world.halted = false → x + n ≤ G →
    ∃ t', runIs (A := arch) linux ω (saves G keep x n) t = some t' ∧ Stored lo N t t' ∧
      ∀ q, q < N → word t'.mem lo q = if j - 1 - G + x ≤ q ∧ q < j - 1 - G + x + n
        then (if keep (q - (j - 1 - G)) then t.regs.gpr (preg (q - (j - 1 - G))) else word t.mem lo q)
        else word t.mem lo q
  | 0, _, t, hR, _, _, _ => ⟨t, rfl, Stored.refl hR, fun q _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, x, t, hR, hsp, hh, hn => by
    cases hk : keep x
    · obtain ⟨t', h2, hS2, hq2⟩ := run_saves keep hG hjG hjN n (x + 1) t hR hsp hh (by omega)
      refine ⟨t', by simpa [saves, hk] using h2, hS2, fun q hq => ?_⟩
      rw [hq2 q hq]
      by_cases h2 : q = j - 1 - G + x
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), show q - (j - 1 - G) = x by omega, hk]
        rfl
      · by_cases h1 : j - 1 - G + (x + 1) ≤ q ∧ q < j - 1 - G + (x + 1) + n
        · rw [ite_eq_left h1, ite_eq_left (show j - 1 - G + x ≤ q ∧ q < j - 1 - G + x + (n + 1)
            from ⟨by have := h1.1; omega, by have := h1.2; omega⟩)]
        · rw [ite_eq_right h1, ite_eq_right (show ¬(j - 1 - G + x ≤ q ∧ q < j - 1 - G + x + (n + 1))
            from fun h => h1 ⟨by have := h.1; omega, by have := h.2; omega⟩)]
    · obtain ⟨t₁, e1, hw1, hg1, -, hR1, hF1, hl1, hv1⟩ := exec_store_word (trap := linux.trap ω)
        (r := preg x) (n := (encode (.store (.base .rsp (0 - UInt32.ofNat (8 * (G - x) + 8))) (preg x))).length) hR hsp
        (calleeMem_addr hG hjG (by omega)) (show j - 1 - G + x < N by omega)
      obtain ⟨t', h2, hS2, hq2⟩ := run_saves keep hG hjG hjN n (x + 1) t₁ hR1 (by rw [hg1]; exact hsp)
        (by rw [hw1]; exact hh) (by omega)
      refine ⟨t', by simp only [saves, hk, calleeMem, belowMem, ite_true, List.singleton_append]
                     rw [runIs_cons' hh e1]; exact h2,
        Stored.trans ⟨hw1, hg1, hR1, hF1, hl1⟩ hS2, fun q hq => ?_⟩
      rw [hq2 q hq, hv1 q hq, hg1]
      by_cases h1 : j - 1 - G + (x + 1) ≤ q ∧ q < j - 1 - G + (x + 1) + n
      · rw [ite_eq_left h1, ite_eq_left (show j - 1 - G + x ≤ q ∧ q < j - 1 - G + x + (n + 1)
          from ⟨by have := h1.1; omega, by have := h1.2; omega⟩),
          ite_eq_right (show ¬ q = j - 1 - G + x by have := h1.1; omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : q = j - 1 - G + x
        · rw [ite_eq_left h2, ite_eq_left (by omega), show q - (j - 1 - G) = x by omega, hk]; rfl
        · rw [ite_eq_right h2, ite_eq_right (show ¬(j - 1 - G + x ≤ q ∧ q < j - 1 - G + x + (n + 1))
            from fun h => h1 ⟨by have := h.1; omega, by have := h.2; omega⟩)]

/-- Loading `[rsp + d]` into `r`, with `rsp` at stack word `j` and the address at word `q`,
sets `r` to word `q`. -/
theorem exec_load_word {trap : State → Option State} {s : State} {lo N j q : Nat} {d : UInt32}
    {r : Reg} {n : Nat} (hR : Region s.mem lo N) (hsp : s.regs.gpr .rsp = wa lo j)
    (hd : wa lo j + sext32 d = wa lo q) (hq : q < N) :
    exec trap (.load r (.base .rsp d)) n s = some (s.upd r (word s.mem lo q) n) := by
  simp only [exec, Mem.addr, hsp, hd, load_wa hR hq, Option.bind_some]; rfl

section Call
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat} {ω : Oracle}

/-- `argMems` stores the arguments `os` whose words `ent` names into the callee frame words from
`j - 1 - G + l` on. It runs while the caller's location registers are still in place, and it
keeps them, the words from `j` on and every other word. -/
theorem run_argMems (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24) {G W : Nat}
    (hW : Sel.frameW k c G = W) (hG : 8 * (W + 1) ≤ 2 ^ 31) (hjG : W + 1 ≤ j) (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), Fetch k c lo N j m t → Lin.OpsBelow os fn.frame →
    l + os.length ≤ G → (os = [] ∨ k + c ≤ l) →
    ∃ t', runIs (A := arch) linux ω (argMems k c G ent l os) t = some t' ∧ Fetch k c lo N j m t' ∧
      t'.world = t.world ∧ Memory.Frame t.mem t'.mem ∧ LowSame lo t.mem t'.mem ∧
      (∀ r, r ≠ .rax → t'.regs.gpr r = t.regs.gpr r) ∧
      ∀ q, q < N → word t'.mem lo q =
        if j - 1 - W + (l - c) ≤ q ∧ q < j - 1 - W + (l - c) + os.length ∧ ent (q - (j - 1 - W) + c) = true
        then (os.map (Operand.eval s.frame)).getD (q - (j - 1 - W) + c - l) 0 else word t.mem lo q
  | [], _, t, hF, _, _, _ => ⟨t, rfl, hF, rfl, Memory.Frame.refl _, LowSame.refl _ _, fun _ _ => rfl,
      fun q _ => by rw [ite_eq_right fun h => by simp at h; omega]⟩
  | o :: os, l, t, hF, ho, hl, hl0 => by
    simp only [List.length_cons] at hl
    have hkl : k + c ≤ l := hl0.resolve_left (by simp)
    have hWG : W = G - c := by rw [← hW]; unfold Sel.frameW; omega
    have hjN := (matchAt_room hM).1
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have shift : ∀ q, ¬ q = j - 1 - W + (l - c) → ((j - 1 - W + (l + 1 - c) ≤ q ∧
        q < j - 1 - W + (l + 1 - c) + os.length ∧ ent (q - (j - 1 - W) + c) = true) ↔
        (j - 1 - W + (l - c) ≤ q ∧ q < j - 1 - W + (l - c) + (o :: os).length ∧ ent (q - (j - 1 - W) + c) = true)) :=
      fun q h2 => by
        simp only [List.length_cons]
        exact ⟨fun h => ⟨by omega, by omega, h.2.2⟩, fun h => ⟨by omega, by omega, h.2.2⟩⟩
    have getD1 : ∀ q, j - 1 - W + (l + 1 - c) ≤ q → (os.map (Operand.eval s.frame)).getD
        (q - (j - 1 - W) + c - (l + 1)) 0 = ((o :: os).map (Operand.eval s.frame)).getD (q - (j - 1 - W) + c - l) 0 :=
      fun q hq => by rw [show q - (j - 1 - W) + c - l = (q - (j - 1 - W) + c - (l + 1)) + 1 by omega]; simp
    cases he : ent l
    · obtain ⟨t', h3, hF3, hw3, hF3', hl3, hk3, hq3⟩ := run_argMems hM hsm hW hG hjG ent os (l + 1) t hF
        ho' (by omega) (Or.inr (by omega))
      refine ⟨t', by simpa [argMems, he] using h3, hF3, hw3, hF3', hl3, hk3, fun q hq => ?_⟩
      rw [hq3 q hq]
      by_cases h2 : q = j - 1 - W + (l - c)
      · subst h2
        rw [ite_eq_right (by omega), ite_eq_right (by
          rw [show j - 1 - W + (l - c) - (j - 1 - W) + c = l by omega]; simp [he])]
      · by_cases hc : j - 1 - W + (l + 1 - c) ≤ q ∧ q < j - 1 - W + (l + 1 - c) + os.length ∧
            ent (q - (j - 1 - W) + c) = true
        · rw [ite_eq_left hc, ite_eq_left ((shift q h2).1 hc), getD1 q hc.1]
        · rw [ite_eq_right hc, ite_eq_right fun h => hc ((shift q h2).2 h)]
    obtain ⟨t1, h1, hm1, hw1, hsp1, hv1, hk1⟩ := run_src (ω := ω) hM hsm hF.toFetchW (r := .rax) (by decide)
      (o := o) (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy)) (fun y _ hy => hF.regs y hy)
    obtain ⟨t2, e2, hw2, hg2, -, hR2, hF2, hl2, hv2⟩ := exec_store_word (trap := linux.trap ω)
      (r := (src k c .rax o).2) (n := (encode (.store (.base .rsp (0 - UInt32.ofNat (8 * (W - (l - c)) + 8)))
        (src k c .rax o).2)).length) (hm1 ▸ hF.region) (hsp1.trans (hF.sp.trans hM.sp))
      (calleeMem_addr hG hjG (by omega)) (show j - 1 - W + (l - c) < N by omega)
    have hk2 : ∀ r, r ≠ .rax → t2.regs.gpr r = t.regs.gpr r := fun r hr => by rw [hg2]; exact hk1 _ hr
    have hF2' : Fetch k c lo N j m t2 := ⟨⟨hR2, fun i h1 h2 => by
        rw [hv2 i h2, ite_eq_right (by omega), hm1]; exact hF.words i h1 h2,
      by rw [hg2, hsp1]; exact hF.sp, by rw [hw2, hw1]; exact hF.halted⟩,
      fun x hx => (hk2 _ (loc_ne_rax k x)).trans (hF.regs x hx)⟩
    obtain ⟨t', h3, hF3, hw3, hF3', hl3, hk3, hq3⟩ := run_argMems hM hsm hW hG hjG ent os (l + 1) t2
      hF2' ho' (by omega) (Or.inr (by omega))
    refine ⟨t', ?_, hF3, by rw [hw3, hw2, hw1], hm1 ▸ hF2.trans hF3', hm1 ▸ hl2.trans hl3,
      fun r hr => (hk3 r hr).trans (hk2 r hr), fun q hq => ?_⟩
    · simp only [argMems, argMem, calleeMem, belowMem, he, ite_true, hW]
      rw [runIs_append, runIs_append, h1, Option.bind_some,
        runIs_one (by rw [hw1]; exact hF.halted) e2, Option.bind_some]
      exact h3
    · rw [hq3 q hq, hv2 q hq, hm1]
      by_cases h2 : q = j - 1 - W + (l - c)
      · subst h2
        rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left ⟨by omega, by simp <;> omega,
          by rw [show j - 1 - W + (l - c) - (j - 1 - W) + c = l by omega]; exact he⟩, hv1,
          show j - 1 - W + (l - c) - (j - 1 - W) + c - l = 0 by omega]
        simp
      · rw [ite_eq_right h2]
        by_cases hc : j - 1 - W + (l + 1 - c) ≤ q ∧ q < j - 1 - W + (l + 1 - c) + os.length ∧
            ent (q - (j - 1 - W) + c) = true
        · rw [ite_eq_left hc, ite_eq_left ((shift q h2).1 hc), getD1 q hc.1]
        · rw [ite_eq_right hc, ite_eq_right fun h => hc ((shift q h2).2 h)]

/-- What loading the register arguments needs of a state `t` of the call block, where `m` is the
related state at the call and the callee frame starts at word `j - 1 - G`. Its memory is `mem`,
whose words `j - 1 - G + y` for `y < g` hold the saved location registers of `m` and whose words
from `j` on are `m`'s. It has `m`'s `rsp`, and its preserved location registers from `l` on are
still `m`'s. -/
structure ArgSt (k lo N j G g l : Nat) (keep : Nat → Bool) (m : State) (mem : Memory) (t : State) :
    Prop where
  hmem : t.mem = mem
  region : Region mem lo N
  sp : t.regs.gpr .rsp = m.regs.gpr .rsp
  halted : t.world.halted = false
  saves : ∀ y, y < g → keep y = true → word mem lo (j - 1 - G + y) = m.regs.gpr (preg y)
  slots : ∀ i, j ≤ i → i < N → word mem lo i = word m.mem lo i
  regs : ∀ x, x < k → l ≤ x → t.regs.gpr (preg x) = m.regs.gpr (preg x)

/-- An `ArgSt` state after a run that keeps memory, the world, `rsp` and the preserved
registers from `l'` on. -/
theorem ArgSt.next {k lo N j G g l l' : Nat} {keep : Nat → Bool} {m : State} {mem : Memory}
    {t t' : State} (hS : ArgSt k lo N j G g l keep m mem t) (hm : t'.mem = t.mem)
    (hw : t'.world = t.world) (hsp : t'.regs.gpr .rsp = t.regs.gpr .rsp) (hl : l ≤ l')
    (hr : ∀ x, x < k → l' ≤ x → t'.regs.gpr (preg x) = t.regs.gpr (preg x)) :
    ArgSt k lo N j G g l' keep m mem t' :=
  ⟨hm.trans hS.hmem, hS.region, hsp.trans hS.sp, by rw [hw]; exact hS.halted, hS.saves, hS.slots,
    fun x hx hlx => (hr x hx hlx).trans (hS.regs x hx (by omega))⟩

/-- `argReg k c G n jd o` sets the register of location `jd`, the next preserved location `n` or
a caller-saved one, to the operand's value. It reads the value from the caller's slot, from a
register not yet overwritten, or from the save word of a preserved one that was. -/
theorem run_argReg (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24)
    {G W g n jd : Nat} {keep : Nat → Bool} {mem : Memory} {t : State}
    (hS : ArgSt k lo N j W g n keep m mem t) (hW : Sel.frameW k c G = W) (hG : 8 * (W + 1) ≤ 2 ^ 31) (hjG : W + 1 ≤ j)
    (hgG : g ≤ W) (hn : n ≤ g) (hjd : jd < k → jd = n ∧ n < g)
    {o : Operand} (ho : Lin.OpsBelow [o] fn.frame) (hko : ∀ y, o = .slot y → keep y = true)
    (hC : ∀ y, o = .slot y → k ≤ y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t', runIs (A := arch) linux ω (argReg k c G n jd o) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ t'.regs.gpr (loc k jd) = o.eval s.frame ∧
      ∀ r, r ≠ loc k jd → t'.regs.gpr r = t.regs.gpr r := by
  have hsp : t.regs.gpr .rsp = wa lo j := hS.sp.trans hM.sp
  have hjN := (matchAt_room hM).1
  -- one instruction that sets `loc k jd` to the operand's value
  have one : ∀ i : Instr, (∀ e, exec (linux.trap ω) i e t =
      some (t.upd (loc k jd) (o.eval s.frame) e)) →
      ∃ t', runIs (A := arch) linux ω [i] t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
        t'.regs.gpr (loc k jd) = o.eval s.frame ∧ ∀ r, r ≠ loc k jd → t'.regs.gpr r = t.regs.gpr r :=
    fun i hi => ⟨_, runIs_one hS.halted (hi _), rfl, rfl, by simp, fun r hr => by simp [hr]⟩
  cases o with
  | imm w => exact one _ fun _ => exec_movRI w
  | slot y =>
    have hy : y < fn.frame := ho y List.mem_cons_self
    have hv := loc_val hM hy
    have hroom := hM.roomW
    by_cases hyk : y < k
    · rw [ite_eq_left (by omega), loc_of_lt hyk] at hv
      by_cases hyl : y < n
      · rw [show argReg k c G n jd (.slot y) = [.load (loc k jd) (calleeMem W y)] by
          simp [argReg, hyk, hyl, hW]]
        refine one _ fun e => (exec_load_word (hS.hmem ▸ hS.region) hsp
          (calleeMem_addr hG hjG (by omega)) (by omega)).trans ?_
        rw [hS.hmem, hS.saves y (by omega) (hko y rfl), hv]; rfl
      · by_cases hyl' : y = jd
        · subst hyl'
          refine ⟨t, by rw [show argReg k c G n y (.slot y) = [] by simp [argReg, hyk, hyl]]; rfl, rfl, rfl,
            ?_, fun _ _ => rfl⟩
          rw [loc_of_lt hyk, hS.regs y hyk (Nat.le_of_not_lt hyl), hv]; rfl
        · rw [show argReg k c G n jd (.slot y) = [.movRR (loc k jd) (preg y)] by
            simp [argReg, hyk, hyl, hyl']]
          exact one _ fun _ => by rw [exec_mv, hS.regs y hyk (Nat.le_of_not_lt hyl), hv]; rfl
    · by_cases hyc : y < k + c
      · rw [ite_eq_left hyc] at hv
        rw [show argReg k c G n jd (.slot y) = [.movRR (loc k jd) (loc k y)] by
          simp [argReg, hyk, hyc]]
        exact one _ fun _ => by rw [exec_mv, hC y rfl (by omega) hyc, hv]; rfl
      · rw [ite_eq_right hyc] at hv
        rw [show argReg k c G n jd (.slot y) = [ldI c (loc k jd) (.slot y)] by simp [argReg, hyk, hyc]]
        refine one _ fun e => (exec_load_word (hS.hmem ▸ hS.region) hsp
          (slotW_addr (show 8 * (y - c) < 2 ^ 31 by omega) (by omega)) (by omega)).trans ?_
        rw [hS.hmem, hS.slots _ (by omega) (by omega), hv]; rfl

/-- `argRegs` sets `preg (l + i)` to operand `i` of `os` when `ent` names `l + i`. It writes no
memory and keeps the other preserved location registers and every other register. -/
theorem run_argRegs (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24) {G W g : Nat}
    {keep : Nat → Bool} {mem : Memory} (hW : Sel.frameW k c G = W) (hG : 8 * (W + 1) ≤ 2 ^ 31) (hjG : W + 1 ≤ j) (hg : g ≤ k)
    (hgG : g ≤ W) (hk : KC k c) (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), ArgSt k lo N j W g l keep m mem t →
    Lin.OpsBelow os fn.frame → l + os.length ≤ g → (∀ y, Operand.slot y ∈ os → keep y = true) →
    (∀ y, k ≤ y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) →
    ∃ t', runIs (A := arch) linux ω (argRegs k c G ent l os) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧
      (∀ i, i < os.length → ent (l + i) = true →
        t'.regs.gpr (preg (l + i)) = (os.map (Operand.eval s.frame)).getD i 0) ∧
      (∀ x, x < maxK → (x < l ∨ l + os.length ≤ x ∨ ent x = false) →
        t'.regs.gpr (preg x) = t.regs.gpr (preg x)) ∧
      ∀ r : Reg, (∀ x, x < maxK → preg x ≠ r) → t'.regs.gpr r = t.regs.gpr r
  | [], _, t, _, _, _, _, _ => ⟨t, rfl, rfl, rfl, fun _ h _ => absurd h (by simp), fun _ _ _ => rfl,
      fun _ _ => rfl⟩
  | o :: os, l, t, hS, ho, hl, hko, hC => by
    simp only [List.length_cons] at hl
    have hkK : k ≤ maxK := hk.1
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have hko' : ∀ y, Operand.slot y ∈ os → keep y = true := fun y hy => hko y (List.mem_cons_of_mem _ hy)
    have hpos : ∀ x, (x < l ∨ l + (os.length + 1) ≤ x ∨ ent x = false) → x ≠ l →
        (x < l + 1 ∨ l + 1 + os.length ≤ x ∨ ent x = false) := fun x h hxl => by
      rcases h with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)
    have hval : ∀ (t' : State) (v : UInt64), (∀ i, i < os.length → ent (l + 1 + i) = true →
        t'.regs.gpr (preg (l + 1 + i)) = (os.map (Operand.eval s.frame)).getD i 0) →
        (ent l = true → t'.regs.gpr (preg l) = v) → v = o.eval s.frame →
        ∀ i, i < os.length + 1 → ent (l + i) = true →
          t'.regs.gpr (preg (l + i)) = ((o :: os).map (Operand.eval s.frame)).getD i 0 :=
      fun t' v hv h0 hv0 i hi hei => by
        cases i with
        | zero => rw [Nat.add_zero] at hei ⊢; rw [h0 hei, hv0]; simp
        | succ i =>
          rw [show l + (i + 1) = l + 1 + i by omega] at hei ⊢
          rw [hv i (by omega) hei]; simp
    cases he : ent l
    · obtain ⟨t', r2, m2, w2, v2, k2, o2⟩ := run_argRegs hM hsm hW hG hjG hg hgG hk ent os (l + 1) t
        (hS.next rfl rfl rfl (by omega) fun _ _ _ => rfl) ho' (by omega) hko' hC
      exact ⟨t', by simpa [argRegs, he] using r2, m2, w2,
        hval t' (o.eval s.frame) v2 (by simp [he]) rfl,
        fun x hx hlx => k2 x hx (by
          by_cases hxl : x = l
          · subst hxl; exact Or.inr (Or.inr he)
          · exact hpos x hlx hxl),
        o2⟩
    obtain ⟨t1, r1, m1, w1, v1, k1⟩ := run_argReg (ω := ω) hM hsm hS hW hG hjG hgG (by omega)
      (jd := l) (fun _ => ⟨rfl, by omega⟩) (o := o) (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy))
      (fun y hy => hko y (hy ▸ List.mem_cons_self)) (fun y _ h1 h2 => hC y h1 h2)
    rw [loc_of_lt (by omega)] at v1 k1
    have hne : ∀ x, x < maxK → x ≠ l → preg x ≠ preg l := fun x hx hxl e =>
      hxl (preg_inj hx (by unfold maxK at hkK ⊢; omega) e)
    obtain ⟨t', r2, m2, w2, v2, k2, o2⟩ := run_argRegs hM hsm hW hG hjG hg hgG hk ent os (l + 1) t1
      (hS.next m1 w1 (k1 _ (Ne.symm (preg_ne_rsp l))) (by omega) fun x hx hlx =>
        k1 _ (hne x (by omega) (by omega))) ho' (by omega) hko'
      (fun y h1 h2 => (k1 _ (Ne.symm (preg_ne_loc h1))).trans (hC y h1 h2))
    refine ⟨t', by simp only [argRegs, he, ite_true]; rw [runIs_append, r1, Option.bind_some, r2],
      m2.trans m1, w2.trans w1, hval t' (o.eval s.frame) v2
        (fun _ => (k2 _ (by omega) (Or.inl (by omega))).trans v1) rfl,
      fun x hx hlx => ?_, fun r hr => by rw [o2 r hr, k1 r (Ne.symm (hr l (by omega)))]⟩
    have hxl : x ≠ l := by
      rintro rfl; rcases hlx with h | h | h
      · omega
      · simp at h <;> omega
      · simp [he] at h
    rw [k2 x hx (hpos x hlx hxl), k1 _ (hne x hx hxl)]

/-- `cLoads k c G g ent l os`, after the preserved register arguments, loads each operand `i` that
is in no caller-saved location into the register of location `l + i` when `ent` names it. It
writes no memory and changes no other register. -/
theorem run_cLoads (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24) (hk : KC k c)
    {G W g : Nat} {keep : Nat → Bool} {mem : Memory} (hW : Sel.frameW k c G = W) (hG : 8 * (W + 1) ≤ 2 ^ 31) (hjG : W + 1 ≤ j)
    (hgG : g ≤ W) (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), ArgSt k lo N j W g g keep m mem t →
    Lin.OpsBelow os fn.frame → k ≤ l → l + os.length ≤ k + c →
    (∀ y, Operand.slot y ∈ os → keep y = true) →
    ∃ t', runIs (A := arch) linux ω (cLoads k c G g ent l os) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧
      (∀ i, i < os.length → ent (l + i) = true → isC k c (os[i]?.getD (.imm 0)) = false →
        t'.regs.gpr (loc k (l + i)) = (os[i]?.getD (.imm 0)).eval s.frame) ∧
      ∀ r : Reg, (∀ i, i < os.length → ent (l + i) = true →
        isC k c (os[i]?.getD (.imm 0)) = false → loc k (l + i) ≠ r) → t'.regs.gpr r = t.regs.gpr r
  | [], _, t, _, _, _, _, _ => ⟨t, rfl, rfl, rfl, fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | o :: os, l, t, hS, ho, hkl, hl, hko => by
    simp only [List.length_cons] at hl
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have hko' : ∀ y, Operand.slot y ∈ os → keep y = true := fun y hy => hko y (List.mem_cons_of_mem _ hy)
    have tail : ∀ (P' : Nat → Prop), (∀ i, i < os.length → P' (l + 1 + i)) →
        ∀ i, i < os.length + 1 → i ≠ 0 → P' (l + i) := fun P' h i hi hi0 => by
      have := h (i - 1) (by omega); rwa [show l + 1 + (i - 1) = l + i by omega] at this
    have shift : ∀ i, 0 < i → (o :: os)[i]?.getD (Operand.imm 0) = os[i - 1]?.getD (.imm 0) :=
      fun i hi => by cases i <;> simp_all
    cases he : ent l && !isC k c o
    · obtain ⟨t', r2, m2, w2, v2, k2⟩ := run_cLoads hM hsm hk hW hG hjG hgG ent os (l + 1) t hS ho'
        (by omega) (by omega) hko'
      refine ⟨t', by simpa [cLoads, he] using r2, m2, w2, fun i hi hei hci => ?_,
        fun r hr => k2 r fun i hi h1 h2 => ?_⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simp at hei hci; simp [hei, hci] at he
        · rw [shift i hi0] at hci ⊢
          have := v2 (i - 1) (by simp at hi; omega) (by rw [← hei]; congr 1; omega) hci
          rwa [show l + 1 + (i - 1) = l + i by omega] at this
      · have := hr (i + 1) (by simp; omega) (by rw [← h1]; congr 1; omega) (by simpa using h2)
        rwa [show l + (i + 1) = l + 1 + i by omega] at this
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
      obtain ⟨t1, r1, m1, w1, v1, k1⟩ := run_argReg (ω := ω) hM hsm hS hW hG hjG hgG (Nat.le_refl _)
        (jd := l) (fun h => absurd h (by omega)) (o := o)
        (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy)) (fun y hy => hko y (hy ▸ List.mem_cons_self))
        (fun y hy h1 h2 => by subst hy; simp [isC, h1, h2] at he)
      obtain ⟨t', r2, m2, w2, v2, k2⟩ := run_cLoads hM hsm hk hW hG hjG hgG ent os (l + 1) t1
        (hS.next m1 w1 (k1 _ (Ne.symm (loc_ne_rsp k l))) (Nat.le_refl _) fun x _ _ =>
          k1 _ (preg_ne_loc hkl)) ho' (by omega) (by omega) hko'
      have hne : ∀ i, i < os.length → loc k (l + 1 + i) ≠ loc k l := fun i hi e => by
        have := loc_inj hk (by omega) (by omega) e; omega
      refine ⟨t', by simp only [cLoads, he, Bool.not_false, Bool.and_self, ite_true]
                     rw [runIs_append, r1, Option.bind_some, r2],
        m2.trans m1, w2.trans w1, fun i hi hei hci => ?_, fun r hr => ?_⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [Nat.add_zero, k2 _ fun i hi _ _ => hne i hi]; exact v1
        · rw [shift i hi0] at hci ⊢
          have := v2 (i - 1) (by simp at hi; omega) (by rw [← hei]; congr 1; omega) hci
          rwa [show l + 1 + (i - 1) = l + i by omega] at this
      · rw [k2 r fun i hi h1 h2 => by
            have := hr (i + 1) (by simp; omega) (by rw [← h1]; congr 1; omega) (by simpa using h2)
            rwa [show l + (i + 1) = l + 1 + i by omega] at this,
          k1 r fun e => hr 0 (by simp) (by simpa using he.1) (by simpa using he.2) e.symm]

/-- The caller-saved register arguments: the moves `mvs` of the parallel move from caller-saved
registers, through `rax`, then `cLoads`. Each caller-saved location of the callee that `ent`
names gets its argument, and no register but `rax` and those locations changes. -/
theorem run_cArgs (hM : MatchAt k c P AP σ lo N s m fn f a j) (hsm : fn.frame < 2 ^ 24) (hk : KC k c)
    {G W : Nat} {args : List Operand} {keep ent : Nat → Bool} {mem : Memory} {mvs : List (Reg × Reg)}
    (hW : Sel.frameW k c G = W) (hG : 8 * (W + 1) ≤ 2 ^ 31) (hjG : W + 1 ≤ j)
    (hargs : args.length ≤ G)
    (ho : Lin.OpsBelow args fn.frame) (hka : ∀ y, Operand.slot y ∈ args → keep y = true)
    (hseq : cSeq k c G args ent = some mvs) {t : State}
    (hS : ArgSt k lo N j W (min k G) (min k G) keep m mem t)
    (hC : ∀ y, k ≤ y → y < k + c → t.regs.gpr (loc k y) = m.regs.gpr (loc k y)) :
    ∃ t', runIs (A := arch) linux ω (mvs.map (fun p => .movRR p.1 p.2) ++
        cLoads k c G (min k G) ent k (cArgs k c G args)) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧
      (∀ x, k ≤ x → x < k + c → x < G → ent x = true →
        t'.regs.gpr (loc k x) = (args.map (Operand.eval s.frame)).getD x 0) ∧
      ∀ r : Reg, r ≠ .rax → (∀ x, k ≤ x → x < k + c → x < G → ent x = true → loc k x ≠ r) →
        t'.regs.gpr r = t.regs.gpr r := by
  have hlen := cArgs_length (k := k) (c := c) hargs
  have hinj : ∀ x y, x < k + c → y < k + c → loc k x = loc k y → x = y :=
    fun x y hx hy e => loc_inj hk hx hy e
  have hnd := Sel.cMoves_nodup (loc := loc k) (d := .rax) hinj ent k (cArgs k c G args) (by omega)
  have hrax : ∀ p ∈ cMoves k c G args ent, p.1 ≠ .rax := fun p hp => by
    obtain ⟨x, -, -, -, -, he⟩ := Sel.cMoves_dst hargs ent hp; rw [he]; exact loc_ne_rax k x
  have hsp : ∀ p ∈ mvs, p.1 ≠ .rsp := fun p hp => by
    rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
    · rw [h]; decide
    · obtain ⟨x, -, -, -, -, he'⟩ := Sel.cMoves_dst hargs ent hq; rw [← he, he']; exact loc_ne_rsp k x
  obtain ⟨t1, r1, m1, w1, sp1, g1⟩ := run_moves (ω := ω) mvs hsp hS.halted
  have hpar : ∀ r, r ≠ .rax → t1.regs.gpr r = Sel.PMove.par t.regs.gpr (cMoves k c G args ent) r :=
    fun r hr => by rw [g1]; exact Sel.PMove.seq_run _ hnd hrax hseq _ r hr
  have hkeep1 : ∀ r, r ≠ .rax → (∀ x, k ≤ x → x < k + c → x < G → ent x = true → loc k x ≠ r) →
      t1.regs.gpr r = t.regs.gpr r := fun r hr hn => by
    rw [hpar r hr]
    exact Sel.PMove.par_of_not _ fun s' hs => by
      obtain ⟨x, h1, h2, h3, h4, he⟩ := Sel.cMoves_dst hargs ent hs; exact hn x h1 h2 h3 h4 he.symm
  obtain ⟨t', r2, m2, w2, v2, k2⟩ := run_cLoads (ω := ω) hM hsm hk hW hG hjG
    (by rw [← hW]; unfold Sel.frameW; omega) ent
    (cArgs k c G args) k t1 (hS.next m1 w1 sp1 (Nat.le_refl _) fun x hx _ =>
      hkeep1 _ (preg_ne rfl) fun y h1 _ _ _ e => preg_ne_loc h1 e.symm)
    (Sel.cArgs_below ho) (Nat.le_refl _) (by omega) (fun y hy => hka y (Sel.cArgs_slot hy))
  refine ⟨t', by rw [runIs_append, r1, Option.bind_some, r2], m2.trans m1, w2.trans w1,
    fun x h1 h2 h3 h4 => ?_, fun r hr hn => ?_⟩
  · have hi : x - k < (cArgs k c G args).length := by omega
    have hxk : k + (x - k) = x := by omega
    obtain ⟨o, hoi⟩ : ∃ o, (cArgs k c G args)[x - k]? = some o := ⟨_, List.getElem?_eq_getElem hi⟩
    have hval := Sel.cArgs_val (k := k) (c := c) hargs s.frame hi
    rw [hoi, Option.getD_some, hxk] at hval
    rw [← hval]
    cases hc : isC k c o
    · have := v2 (x - k) hi (by rw [hxk]; exact h4) (by rw [hoi]; exact hc)
      rwa [hxk, hoi] at this
    · rw [k2 _ fun i hi' _ hc' e => by
          have := loc_inj hk (by omega) (by omega) e
          rw [show i = x - k by omega, hoi, Option.getD_some, hc] at hc'; cases hc']
      rw [hpar _ (loc_ne_rax k x), Sel.par_cMoves hinj hargs ent _ h1 h3 h4 hoi hc h2]
      cases o with
      | imm w => simp [isC] at hc
      | slot y =>
        simp only [isC, Bool.and_eq_true, decide_eq_true_eq] at hc
        have hv := loc_val hM (Sel.cArgs_below ho y (List.mem_of_getElem? hoi))
        rw [ite_eq_left hc.2] at hv
        rw [show Sel.oreg (loc k) Reg.rax (.slot y) = loc k y from rfl, hC y hc.1 hc.2, hv]; rfl
  · rw [k2 r fun i hi h1 h2 e => hn (k + i) (by omega) (by omega) (by omega) h1 e, hkeep1 r hr hn]

/-- The instructions of a call sequence neither branch nor move `rsp`. -/
theorem callOps_ok (k c G : Nat) (args : List Operand) (keep ent : Nat → Bool) :
    ∀ i ∈ callOps k c G args keep ent, i.branches = false ∧ i.keepsSp = true := by
  have hs : ∀ G x n, ∀ i ∈ saves G keep x n, i.branches = false ∧ i.keepsSp = true := by
    intro G x n; induction n generalizing x with
    | zero => simp [saves]
    | succ n ih =>
      simp only [saves, List.forall_mem_append]
      exact ⟨by split <;> simp, ih (x + 1)⟩
  have hm : ∀ l os, ∀ i ∈ argMems k c G ent l os, i.branches = false ∧ i.keepsSp = true := by
    intro l os; induction os generalizing l with
    | nil => simp [argMems]
    | cons o os ih =>
      simp only [argMems, argMem, List.forall_mem_append]
      refine ⟨?_, ih (l + 1)⟩
      split
      · exact List.forall_mem_append.2 ⟨fun i hi => ⟨(src_ok k c .rax o i hi).2.1,
          by simp [(src_ok k c .rax o i hi).2.2.2]⟩, by simp [Instr.writes, Instr.branches]⟩
      · simp
  have h1 : ∀ n jd o, ∀ i ∈ argReg k c G n jd o, i.branches = false ∧ i.keepsSp = true := by
    intro n jd o
    cases o with
    | imm w => simp [argReg, Ne.symm (loc_ne_rsp k jd)]
    | slot y =>
      simp only [argReg]; split
      · split
        · simp [Ne.symm (loc_ne_rsp k jd)]
        · split <;> simp [Instr.writes, Instr.branches, Ne.symm (loc_ne_rsp k jd)]
      · split <;> simp [Ne.symm (loc_ne_rsp k jd)]
  have hr : ∀ l os, ∀ i ∈ argRegs k c G ent l os, i.branches = false ∧ i.keepsSp = true := by
    intro l os; induction os generalizing l with
    | nil => simp [argRegs]
    | cons o os ih =>
      simp only [argRegs, List.forall_mem_append]
      exact ⟨by split; exact h1 _ _ _; simp, ih (l + 1)⟩
  have hl : ∀ l os, ∀ i ∈ cLoads k c G (min k G) ent l os, i.branches = false ∧ i.keepsSp = true := by
    intro l os; induction os generalizing l with
    | nil => simp [cLoads]
    | cons o os ih =>
      simp only [cLoads, List.forall_mem_append]
      exact ⟨by split; exact h1 _ _ _; simp, ih (l + 1)⟩
  have hv : ∀ i ∈ ((cSeq k c G args ent).getD []).map (fun p => Instr.movRR p.1 p.2),
      i.branches = false ∧ i.keepsSp = true := by
    cases h : cSeq k c G args ent with
    | none => simp
    | some mvs =>
      intro i hi
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
      refine mv_straight ?_
      rcases Sel.PMove.seq_dst _ h p hp with h | ⟨q, hq, he⟩
      · rw [h]; decide
      · obtain ⟨i, -, -, -, rfl⟩ := Sel.mem_cMoves ent k _ hq; rw [← he]; exact loc_ne_rsp k _
  intro i hi
  simp only [callOps, List.mem_append] at hi
  rcases hi with (((hi | hi) | hi) | hi) | hi
  · exact hs _ _ _ i hi
  · exact hm _ _ i hi
  · exact hr _ _ i hi
  · exact hv i hi
  · exact hl _ _ i hi

/-- What the call sequence `callOps` leaves when run from a related state `m`. The callee frame
at word `j - 1 - G` holds the saved location registers in its words below `min k G` and the
memory arguments from `min (k + c) G` on. Every word from `j` on and `rsp` are kept, the location
registers below `min (k + c) G` that `ent` names hold their arguments, and the other location
registers are kept. -/
structure CallSt (k c lo N j G : Nat) (args : List Operand) (keep ent : Nat → Bool) (fr : Flat.Frame)
    (m t : State) : Prop where
  world : t.world = m.world
  frame : Memory.Frame m.mem t.mem
  low : LowSame lo m.mem t.mem
  region : Region t.mem lo N
  sp : t.regs.gpr .rsp = m.regs.gpr .rsp
  saves : ∀ x, x < min k G → keep x = true →
    word t.mem lo (j - 1 - Sel.frameW k c G + x) = m.regs.gpr (preg x)
  margs : ∀ x, min (k + c) G ≤ x → x < G → ent x = true →
    word t.mem lo (j - 1 - Sel.frameW k c G + x - c) = (args.map (Operand.eval fr)).getD x 0
  keep : ∀ q, j ≤ q → q < N → word t.mem lo q = word m.mem lo q
  regs : ∀ x, x < k + c → t.regs.gpr (loc k x) =
    if x < min (k + c) G ∧ ent x = true then (args.map (Operand.eval fr)).getD x 0
    else m.regs.gpr (loc k x)

/-- The call sequence before `call` runs the saves, then the memory arguments while the caller's
registers are in place, then the preserved register arguments and the caller-saved ones, and
leaves the state `CallSt` describes. -/
theorem run_callOps (hM : MatchAt k c P AP σ lo N s m fn f a j) (hk : KC k c) (hsm : fn.frame < 2 ^ 24)
    {G : Nat} {args : List Operand} (hG : G < 2 ^ 24) (hroomG : Sel.frameW k c G + 2 ≤ j)
    (hargs : args.length ≤ G)
    (hbelow : Lin.OpsBelow args fn.frame) {keep : Nat → Bool}
    (hka : ∀ y, Operand.slot y ∈ args → keep y = true) {ent : Nat → Bool} {mvs : List (Reg × Reg)}
    (hseq : cSeq k c G args ent = some mvs) :
    ∃ t, runIs (A := arch) linux ω (callOps k c G args keep ent) m = some t ∧
      CallSt k c lo N j G args keep ent s.frame m t := by
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c G = W := ⟨_, rfl⟩
  have hWG : W = min G k + (G - (k + c)) := by rw [← hW]; rfl
  have hjN := (matchAt_room hM).1
  have hG' : 8 * (W + 1) ≤ 2 ^ 31 := by omega
  have hjG : W + 1 ≤ j := by omega
  have hmm := Nat.min_le_left k G
  have hmG : min k G ≤ W := by omega
  have hlen := padArgs_length G args
  obtain ⟨t1, r1, hS1, hq1⟩ := run_saves (ω := ω) keep hG' hjG hjN (min k G) 0 m hM.region hM.sp
    hM.halted (by omega)
  have hF1 : Fetch k c lo N j m t1 := ⟨⟨hS1.region, fun i h1 h2 => by rw [hq1 i h2, ite_eq_right (by omega)],
    by rw [hS1.regs], by rw [hS1.world]; exact hM.halted⟩, fun x _ => by rw [hS1.regs]⟩
  obtain ⟨t2, r2, hF2, hw2, hFr2, hl2, hk2, hq2⟩ := run_argMems (ω := ω) hM hsm hW hG' hjG ent
    ((padArgs G args).drop (min (k + c) G)) (min (k + c) G) t1 hF1
    (fun y hy => Sel.padArgs_below hbelow y (List.mem_of_mem_drop hy)) (by simp [hlen]; omega)
    (by
      by_cases h : k + c ≤ G
      · exact Or.inr (by omega)
      · exact Or.inl (by simp [hlen]; omega))
  have hsv : ∀ y, y < min k G → keep y = true → word t2.mem lo (j - 1 - W + y) = m.regs.gpr (preg y) :=
    fun y hy hky => by
    rw [hq2 _ (by omega), ite_eq_right (fun h => by simp [hlen] at h; omega), hq1 _ (by omega),
      ite_eq_left (by omega), show j - 1 - W + y - (j - 1 - W) = y by omega, hky]; rfl
  have hreg2 : ∀ x, x < k + c → t2.regs.gpr (loc k x) = m.regs.gpr (loc k x) := hF2.regs
  obtain ⟨t3, r3, hm3, hw3, hv3, hk3, ho3⟩ := run_argRegs (ω := ω) hM hsm (g := min k G)
    (mem := t2.mem) hW hG' hjG hmm hmG hk ent ((padArgs G args).take (min k G)) 0 t2
    ⟨rfl, hF2.region, hF2.sp, hF2.halted, hsv, hF2.words,
      fun x hx _ => by rw [← loc_of_lt hx]; exact hreg2 x (by omega)⟩
    (fun y hy => Sel.padArgs_below hbelow y (List.mem_of_mem_take hy)) (by simp [hlen])
    (fun y hy => hka y (Sel.slot_of_pad hy)) (fun y _ hy => hreg2 y hy)
  have hpk : ∀ x, x < maxK → preg x ≠ .rsp := fun x _ => preg_ne_rsp x
  have hsp3 : t3.regs.gpr .rsp = m.regs.gpr .rsp := (ho3 _ fun x _ => preg_ne_rsp x).trans hF2.sp
  obtain ⟨t4, r4, hm4, hw4, hv4, hk4⟩ := run_cArgs (ω := ω) hM hsm hk hW hG' hjG hargs hbelow hka hseq
    (mem := t2.mem) (t := t3)
    ⟨hm3, hF2.region, hsp3, by rw [hw3]; exact hF2.halted, hsv, hF2.words, fun x hx hlx => by
      rw [hk3 x (by have := hk.1; omega) (Or.inr (Or.inl (by simp [hlen]; omega))),
        ← loc_of_lt hx]; exact hreg2 x (by omega)⟩
    (fun y h1 h2 => (ho3 _ fun x _ e => preg_ne_loc h1 e).trans (hreg2 y h2))
  rw [runIs_append] at r4
  refine ⟨t4, by unfold callOps; rw [hW, hseq, Option.getD_some, runIs_append, runIs_append, runIs_append,
                   runIs_append, r1, Option.bind_some, r2, Option.bind_some, r3, Option.bind_some]
                 exact r4,
    ⟨by rw [hw4, hw3, hw2, hS1.world], hm4 ▸ hm3 ▸ hS1.frame.trans hFr2,
      hm4 ▸ hm3 ▸ hS1.low.trans hl2, by rw [hm4, hm3]; exact hF2.region,
      (hk4 _ (by decide) fun x _ _ _ _ => loc_ne_rsp k x).trans hsp3,
      fun x hx hk => by rw [hm4, hm3, hW]; exact hsv x hx hk, fun x h1 h2 he => ?_,
      fun q h1 h2 => by rw [hm4, hm3]; exact hF2.words q h1 h2, fun x hx => ?_⟩⟩
  · have hkx : k + c ≤ x := by omega
    rw [hm4, hm3, hW, hq2 _ (by omega), ite_eq_left ⟨by omega, by simp [hlen]; omega,
        by rw [show j - 1 - W + x - c - (j - 1 - W) + c = x by omega]; exact he⟩,
      show j - 1 - W + x - c - (j - 1 - W) + c - min (k + c) G = x - min (k + c) G by omega,
      Sel.pad_drop hargs h1 h2]
  · by_cases hxk : x < k
    · have hkeep4 := hk4 (preg x) (preg_ne rfl) fun y h1 _ _ _ e => preg_ne_loc h1 e.symm
      rw [loc_of_lt hxk, hkeep4]
      split
      · rename_i hxm
        have := hv3 x (by simp [hlen]; omega) (by simpa using hxm.2); rw [Nat.zero_add] at this
        rw [this, Sel.pad_take hargs (show x < min k G by omega) (Nat.min_le_right k G)]
      · rename_i hxm
        rw [hk3 x (by have := hk.1; omega) (by
          by_cases h : x < min k G
          · exact Or.inr (Or.inr (by simpa [h, show x < min (k + c) G by omega] using hxm))
          · exact Or.inr (Or.inl (by simp [hlen]; omega))), ← loc_of_lt hxk]
        exact hreg2 x hx
    · split
      · rename_i hxm; exact hv4 x (by omega) hx (by omega) hxm.2
      · rename_i hxm
        rw [hk4 _ (loc_ne_rax k x) fun y h1 h2 h3 h4 e => by
            have := loc_inj hk h2 hx e; subst this; exact hxm ⟨by omega, h4⟩,
          ho3 _ fun y _ e => preg_ne_loc (by omega) e]
        exact hreg2 x hx

theorem seqSize_ops (is : List Instr) : Asm.seqSize arch (ops is) = (is.flatMap encode).length :=
  (Asm.resolveAt_size asmLaws _ _ _ _ (resolveAt_ops (ρ := fun _ => none) is 0) (encodeAll_eq _)).1.symm

/-- A call block, the call sequence followed by `call`, run from a related state ends at the
callee's address `ag` with `rsp` one word down. The return address is in word `j - 1`, and the
callee frame is as `CallSt` says. -/
theorem run_callBlock (hM : MatchAt k c P AP σ lo N s m fn f a j) (hk : KC k c)
    (hsm : fn.frame < 2 ^ 24) {G : Nat} {args : List Operand} (hG : G < 2 ^ 24)
    (hroomG : Sel.frameW k c G + 2 ≤ j)
    (hargs : args.length ≤ G) (hbelow : Lin.OpsBelow args fn.frame) {keep : Nat → Bool}
    (hka : ∀ y, Operand.slot y ∈ args → keep y = true) {ent : Nat → Bool} {mvs : List (Reg × Reg)}
    (hseq : cSeq k c G args ent = some mvs) {r : UInt32} {ag : UInt64}
    (hcode : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc))
      ((callOps k c G args keep ent).flatMap encode ++ encode (.call r)))
    (hjump : a + UInt64.ofNat (f.labelOff s.pc) +
      UInt64.ofNat (Asm.seqSize arch (ops (callOps k c G args keep ent))) + 5 + sext32 r = ag) (cy : Nat) :
    ∃ m₂ : State, Sel.Leg (A := arch) linux ω (SpIn lo N (j - 1)) m cy
        ((callOps k c G args keep ent).length + 1) m₂ ∧
      m₂.regs.rip = ag ∧ m₂.regs.gpr .rsp = wa lo (j - 1) ∧
      word m₂.mem lo (j - 1) = a + UInt64.ofNat (f.labelOff s.pc +
        (Asm.seqSize arch (ops (callOps k c G args keep ent)) + 5)) ∧
      ∃ t, CallSt k c lo N j G args keep ent s.frame m t ∧ m₂.world = t.world ∧ Memory.Frame t.mem m₂.mem ∧
        LowSame lo t.mem m₂.mem ∧ Region m₂.mem lo N ∧
        (∀ q, q < N → q ≠ j - 1 → word m₂.mem lo q = word t.mem lo q) ∧
        ∀ r, r ≠ .rsp → m₂.regs.gpr r = t.regs.gpr r := by
  have hjN := (matchAt_room hM).1
  obtain ⟨hcodeA, hcodeC⟩ := codeAt_append _ _ _ _ hcode
  obtain ⟨t, hr, hC⟩ := run_callOps (ω := ω) hM hk hsm hG hroomG hargs hbelow hka hseq
  obtain ⟨hrunA, hFA, -, hripA, hall⟩ := run_straight cy hM.wx (by rw [hM.rip]; exact hcodeA)
    (callOps_ok k c G args keep ent) hr
  have hrip₁ : t.regs.rip = a + UInt64.ofNat (f.labelOff s.pc) +
      UInt64.ofNat (Asm.seqSize arch (ops (callOps k c G args keep ent))) := by
    rw [hripA, hM.rip, seqSize_ops]
  have hsp₁ : t.regs.gpr .rsp = wa lo j := hC.sp.trans hM.sp
  obtain ⟨m₂mem, hst₂, hR₂, hF₂, hv₂, hrest₂⟩ := writeWord_wa hC.region (show j - 1 < N by omega)
    (t.regs.rip + UInt64.ofNat (encode (Instr.call r)).length)
  obtain ⟨m₂, e2, hmem2, hw2, hsp2, hrip2⟩ := exec_call (trap := linux.trap ω) (r := r) hsp₁ (by omega)
    (by rw [store64_wa hC.region (show j - 1 < N by omega)]; exact hst₂)
  have hst2 := step_exec (c := cy + (callOps k c G args keep ent).length) (by rw [hC.world]; exact hM.halted)
    (by rw [hrip₁, seqSize_ops]; exact codeAt_frame hM.wx hFA _ _ hcodeC) e2
  refine ⟨m₂, (Sel.Leg.mono (fun x hx => ⟨j, by omega, by omega, hx.trans hM.sp⟩)
      ⟨hrunA, hall⟩).trans (Sel.Leg.one hst2 ⟨j, by omega, by omega, hsp₁⟩
        ⟨j - 1, by omega, by omega, hsp2⟩), by rw [hrip2, hrip₁, ← hjump]; rfl, hsp2, ?_,
    t, hC, hw2, hmem2 ▸ hF₂, hmem2 ▸ writeWord_wa_low hC.region (by omega) hst₂, hmem2 ▸ hR₂,
    fun q hq hne => by rw [hmem2]; exact hrest₂ q hq hne, fun x hx => exec_gpr (by nofun) e2 _ ?_⟩
  · rw [hmem2, hv₂, hrip₁]
    simp only [UInt64.ofNat_add, UInt64.add_assoc]
    rfl
  · simpa [Instr.writes] using hx

end Call

theorem frameBytes_eq {k c : Nat} {P : Lin.Prog} {g : Nat} {gf : Lin.Fn} (h : P.funs[g]? = some gf) :
    P.frameBytes (φ.words k c) g = 8 * (Sel.frameW k c gf.frame + 1) := by
  simp [Lin.Prog.frameBytes, h, φ, FrameModel.words]

section Sim
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- The Lin instruction `call g args d` runs as the call block followed by the callee's
`sub rsp, 8G`. The machine is then at the callee's first label with its frame in place, related
to the Lin state after the call. -/
theorem sim_call (hk : KC k c) (hsel : select k c P mb = .ok A) (hwf : P.Wf)
    (hB : P.stackBytes (conv k c).φ ≤ 8 * N) {ω : Oracle} {κ : CostModel} {s : Lin.State} {m : State}
    {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat} (hM : MatchAt k c P A σ lo N s m fn f a j)
    {g : Nat} {args : List Operand} {d : Nat} (hi : fn.code[s.pc]? = some (.call g args d)) (cy : Nat) :
    ∃ n m' gf fg ag j' s'', M.run ω (m, cy) n = some (m', cy + n) ∧
      n = (callOps k c (calleeFrame P g) args
        (RegAlloc.Live.callKeep (RegAlloc.Live.of P) P s.fn s.pc g d args)
        (RegAlloc.Live.liveIn (RegAlloc.Live.of P) g 0)).length + 2 ∧
      (RegAlloc.Live.flex P).R (Lin.exec κ ω fn (.call g args d) s |>.getD s) s'' ∧
      MatchAt k c P A σ lo N s'' m' gf fg ag j' ∧
      RunAll ω (SpIn lo N j') (m, cy) n := by
  obtain ⟨b, hC⟩ := ctx_of asmLaws (select_ok hsel) hwf hM hi
  obtain ⟨hg, hargs, gf, hgf, hal, hdr⟩ := hC.wf
  obtain ⟨dd, hsi, _⟩ := hC.instr
  simp only [selector, selInstr, hgf, ite_eq_left hal] at hsi
  split at hsi
  rotate_left
  · cases hsi
  rename_i rw hsome hrw
  obtain ⟨mvs, hseq⟩ := Option.isSome_iff_exists.1 hsome
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsi
  obtain ⟨rfl, rfl⟩ := hsi
  obtain ⟨_, _, _, hk'⟩ := Sel.select_spec (select_ok hsel)
  obtain ⟨fg, hfg, hsfg⟩ := hk' g gf hgf
  obtain ⟨ag, hag, hentry, _⟩ := Sel.fn_code asmLaws hM.loaded (List.mem_of_getElem? hfg)
  rw [hsfg.name] at hag
  have hgsm := (fnOk_iff.1 hsfg.ok).1.1
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c gf.frame = W := ⟨_, rfl⟩
  have hWG : W = min gf.frame k + (gf.frame - (k + c)) := by rw [← hW]; rfl
  have hroomG : Sel.frameW k c gf.frame + 2 ≤ j := by
    have := hM.room_call hB hi hg hgf; simp only [conv, φ, FrameModel.words] at this; omega
  have hroomW : W + 2 ≤ j := hW ▸ hroomG
  have hjN := (matchAt_room hM).1
  -- the call block
  obtain ⟨ins, hr, hcode⟩ := seqAt_x64 hC.code
  obtain ⟨i₀, i₃, rfl, hr₀, _⟩ := resolveAt_append (A := arch) _ _ _ ins hr
  obtain ⟨i₁, i₂₁, rfl, hr₁, hr₂₁⟩ := resolveAt_append (A := arch) _ _ _ i₀ hr₀
  obtain rfl := resolveAt_ops_inv hr₁
  obtain ⟨ic, isc, hc₁, hc₂, rfl⟩ := Asm.resolveAt_cons_inv hr₂₁
  cases hc₂
  simp only [SI.resolve, Asm.Fn.refAddr, hag, Option.bind_some] at hc₁
  obtain ⟨r, hrel, rfl⟩ := Option.map_eq_some_iff.1 hc₁
  rw [List.flatMap_append, List.flatMap_append] at hcode
  have hfr := calleeFrame_eq hM.hfn
  obtain ⟨m₂, L₂, hrip2, hsp2, hra2, t, hCS, hw2, hF2, hlow2, hR2, hq2, hk2⟩ := run_callBlock hM hk
    (fnOk_iff.1 hC.sel.ok).1.1 hgsm hroomG hal hargs
    (fun y hy => by simp [RegAlloc.Live.callKeep, RegAlloc.Live.keepCall, hy]) hseq
    (by simpa using (codeAt_append _ _ _ _ hcode).1) (rel32_spec hrel) cy
  -- the callee's frame set-up
  obtain ⟨ie, he, hecode⟩ := seqAt_x64 hentry
  rw [hsfg.entry] at he
  simp only [selector, hW] at he
  obtain rfl := resolveAt_ops_inv (is := [Instr.aluRI .sub .rsp (UInt32.ofNat (8 * W))]) he
  obtain ⟨m₃, e3, hmem3, hw3, hsp3, hrip3⟩ := exec_subSp (trap := linux.trap ω) (G := W)
    (n := (encode (Instr.aluRI .sub .rsp (UInt32.ofNat (8 * W)))).length) hsp2
    (by omega) (by omega)
  have hst3 := step_exec (c := cy + ((callOps k c gf.frame args
      (RegAlloc.Live.callKeep (RegAlloc.Live.of P) P s.fn s.pc g d args)
      (RegAlloc.Live.liveIn (RegAlloc.Live.of P) g 0)).length + 1))
    (by rw [hw2, hCS.world]; exact hM.halted)
    (by rw [hrip2]; simpa using codeAt_frame hM.wx (hCS.frame.trans hF2) _ _ hecode) e3
  have L := (Sel.Leg.mono (Q' := SpIn lo N (j - 1 - W))
    (fun x ⟨i, h1, h2, h3⟩ => ⟨i, by omega, h2, h3⟩) L₂).trans
    (Sel.Leg.one hst3 ⟨j - 1, by omega, by omega, hsp2⟩ ⟨_, Nat.le_refl _, by omega, hsp3⟩)
  have hk3 : ∀ x, m₃.regs.gpr (loc k x) = t.regs.gpr (loc k x) := fun x => by
    rw [exec_gpr (by nofun) e3 _ (by simp [Instr.writes, Alu.writes]), hk2 _ (loc_ne_rsp k x)]
  have hmm := Nat.min_le_left k gf.frame
  simp only [Lin.exec, Option.getD_some]
  -- the callee's frame as the machine holds it: the arguments in the locations live at entry
  let cf : Flat.Frame := fun x => if RegAlloc.Live.liveIn (RegAlloc.Live.of P) g 0 x then
    (args.map (Operand.eval s.frame)).getD x 0
    else if x < k + c then m₃.regs.gpr (loc k x) else word m₃.mem lo (j - 1 - W + x - c)
  refine ⟨_, m₃, gf, fg, ag, j - 1 - W, ⟨g, 0, cf,
    ⟨s.fn, s.pc + 1, Sel.savedFrame lo (conv k c).k gf.frame
      (RegAlloc.Live.callKeep (RegAlloc.Live.of P) P s.fn s.pc g d args) m₃.mem (j - 1 - W)
      s.frame, d⟩ :: s.stack, s.mem, s.world, s.clock⟩, L.run, by simp [calleeFrame, hgf],
    RegAlloc.Live.R_call P (args := args) (F := calleeFrame P s.fn)
      (fun x hx => by simp [cf, hx, Flat.Frame.ofList]) fun x hx => ?_, ?_, L.all⟩
  · simp only [Sel.savedFrame]
    rw [ite_eq_right fun h => by
      have h2 := h.2; unfold RegAlloc.Live.callKeep at h2; rw [hx] at h2; cases h2]
  refine Sel.matchAt_call hM hi hg hgf hfg (by rw [hsfg.name]; exact hag) (j' := j - 1 - W)
    (by simp only [conv, hW]; omega) (by simp [conv, φ, FrameModel.words, hW])
    (by rw [hw3, hw2, hCS.world])
    (hmem3 ▸ hCS.frame.trans hF2) (hmem3 ▸ hCS.low.trans hlow2) (hmem3 ▸ hR2) trivial ?_ hsp3
    (fun x hx => ?_) (by rw [conv_k, conv_c, hW, hmem3, show j - 1 - W + W = j - 1 by omega, hra2]
                         simp [conv, calleeFrame_eq hgf])
    (fun q hq hq' => by rw [hmem3, hq2 q hq' (by omega)]; exact hCS.keep q hq hq')
    (keep := RegAlloc.Live.callKeep (RegAlloc.Live.of P) P s.fn s.pc g d args)
    (fun x hx => by simp [RegAlloc.Live.callKeep, RegAlloc.Live.keepCall, hfr, hx])
    (fun x hx hkx => ?_) (fun x hx hxk => ?_) trivial
  · show m₃.regs.rip = _
    rw [hrip3, hrip2]
    simp only [Asm.Fn.labelOff, hsfg.entry, Asm.blocksOff, Nat.add_zero]
    rfl
  · show (if x < k + c then m₃.regs.gpr (loc k x) else word m₃.mem lo (j - 1 - W + x - c)) = cf x
    simp only [cf]
    by_cases he : RegAlloc.Live.liveIn (RegAlloc.Live.of P) g 0 x = true
    · rw [ite_eq_left he]
      split
      · rename_i hxk; rw [hk3, hCS.regs x hxk, ite_eq_left ⟨by omega, he⟩]
      · rw [hmem3, hq2 _ (by omega) (by omega), ← hW, hCS.margs x (by omega) hx he]
    · rw [ite_eq_right he]
  · change x < min k gf.frame at hx
    show word m₃.mem lo (j - 1 - W + x) = m.regs.gpr (loc k x)
    rw [hmem3, hq2 _ (by omega) (by omega), ← hW, hCS.saves x hx hkx, loc_of_lt (by omega)]
  · change min k gf.frame ≤ x at hx
    have hxk' : x < k := hxk
    show m₃.regs.gpr (loc k x) = m.regs.gpr (loc k x)
    rw [hk3, hCS.regs x (by omega), ite_eq_right (fun h => by omega)]

end Sim

/-! ### Returns -/

section Ret
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat} {ω : Oracle}

theorem emit_ok {k c : Nat} : ∀ (l : List (Place × Place)),
    (∀ p ∈ l, ∀ d, p.1 = .inl d → d ≠ .rsp) →
    ∀ x ∈ l.flatMap (emit k c), x.branches = false ∧ x.keepsSp = true
  | [], _ => by simp
  | (p1, p2) :: l, h => by
    rw [List.flatMap_cons]
    refine List.forall_mem_append.2 ⟨?_, emit_ok l fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
    rcases p1 with d | o
    · have hd := h _ List.mem_cons_self d rfl
      rcases p2 with r | o'
      · simp [emit, Instr.writes, Instr.branches, Ne.symm hd]
      · exact fun x hx => ⟨(ldTo_ok o' x hx).2.1,
          by simp [Instr.keepsSp, (ldTo_ok o' x hx).2.2.2, Ne.symm hd]⟩
    · simp [emit]

/-- Running the code of `retLd` puts the returned operands into the return registers by one
parallel move and changes no other register but `r11`. -/
theorem run_retLd (hM : MatchAt k c P AP σ lo N s m fn f a j) (hk : KC k c)
    (hok : (selector k c mb lvo).fnOk fn = true) (hret : fn.ret.length ≤ 8)
    (hbelow : Lin.OpsBelow fn.ret fn.frame) {rl : List Instr} (hrl : retLd k c fn.ret = some rl) :
    ∃ t', runIs (A := arch) linux ω rl m = some t' ∧
      (∀ x ∈ rl, x.branches = false ∧ x.keepsSp = true) ∧ t'.mem = m.mem ∧ t'.world = m.world ∧
      (∀ r, (∀ q, q < fn.ret.length → r ≠ retReg q) → r ≠ .r11 → t'.regs.gpr r = m.regs.gpr r) ∧
      ∀ q, q < fn.ret.length → t'.regs.gpr (retReg q) = (fn.ret.map (Operand.eval s.frame)).getD q 0 := by
  simp only [retLd, Option.map_eq_some_iff] at hrl
  obtain ⟨l, hseq, rfl⟩ := hrl
  have hO := selOps_laws (lvo := lvo) (mb := mb) hk
  have hE := selOps_ext (lvo := lvo) (mb := mb) hk
  have hmem : ∀ {p : Place × Place}, p ∈ retMoves k c fn.ret ↔
      ∃ i, i < fn.ret.length ∧ p = (.inl (retReg (0 + i)), place k c (fn.ret[i]?.getD (.imm 0))) :=
    Sel.mem_retMoves 0 fn.ret
  have hget : ∀ i, i < fn.ret.length → Lin.OpsBelow [fn.ret[i]?.getD (.imm 0)] fn.frame :=
    fun i hi y hy => hbelow y (by
      simp only [List.mem_singleton] at hy
      rw [hy, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
  have hms : ∀ p ∈ retMoves k c fn.ret, (selOps k c mb).EmitOk ((conv k c).k + (conv k c).c) fn.frame p :=
    fun p hp => by
      obtain ⟨i, hi, rfl⟩ := hmem.1 hp
      exact ⟨⟨_, rfl, retReg_ne_rsp _⟩, Sel.Ops.emitOk_place (O := selOps k c mb) (hget i hi)⟩
  have hnd : ((retMoves k c fn.ret).map (·.1)).Nodup := Sel.retMoves_nodup _ 0 fn.ret
    fun a b _ ha _ hb he => retReg_inj (by omega) (by omega) he
  have ht : ∀ p ∈ retMoves k c fn.ret, p.1 ≠ .inl .r11 := fun p hp e => by
    obtain ⟨i, hi, rfl⟩ := hmem.1 hp
    exact retReg_ne_r11 _ (Sum.inl.inj e)
  obtain ⟨hl, t', h1, hm1, hw1, hsp1, hOk1, hv1⟩ := hE.run_seq hO hM hok (tmp := Reg.r11)
    (show Reg.r11 ≠ .rsp by decide) hseq hms hnd ht rfl rfl hM.halted (hO.ok_match hM)
  rw [emit_eq] at h1
  refine ⟨t', h1, emit_ok l fun p hp d hd => ?_, hm1, hw1, fun r hr h11 => ?_, fun i hi => ?_⟩
  · rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
    · rw [hd] at h; cases h; decide
    · obtain ⟨i, hi, rfl⟩ := hmem.1 hq; rw [hd] at he; cases he; exact retReg_ne_rsp _
  · refine (hv1 r h11).trans ((Sel.PMove.par_of_not _ fun s' hs => ?_).trans rfl)
    obtain ⟨i, hi, he⟩ := hmem.1 hs
    exact hr i hi (by rw [← Nat.zero_add i]; exact Sum.inl.inj (Prod.mk.inj he).1)
  · have hm := hmem.2 ⟨i, hi, rfl⟩
    rw [Nat.zero_add] at hm
    refine (hv1 _ (retReg_ne_r11 i)).trans ((Sel.PMove.par_of_mem hnd _ hm).trans ?_)
    refine (hO.view_place hM (hget i hi) ((Sel.Ops.Keeps.refl _).op _)).trans ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The restores load the `n` location registers from `x` on from the running frame's words from
`j + x` on, and keep every other register. -/
theorem run_restores {lo N j : Nat} (hjN : j ≤ N) : ∀ (n x : Nat) (t : State), Region t.mem lo N →
    t.regs.gpr .rsp = wa lo j → t.world.halted = false → x + n ≤ maxK → j + x + n ≤ N →
    8 * (x + n) < 2 ^ 31 →
    ∃ t', runIs (A := arch) linux ω (restores x n) t = some t' ∧ t'.mem = t.mem ∧
      t'.world = t.world ∧ (∀ l, l < n → t'.regs.gpr (preg (x + l)) = word t.mem lo (j + x + l)) ∧
      ∀ r, (∀ l, l < n → r ≠ preg (x + l)) → t'.regs.gpr r = t.regs.gpr r
  | 0, _, t, _, _, _, _, _, _ => ⟨t, rfl, rfl, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | n + 1, x, t, hR, hsp, hh, hx, hxN, h31 => by
    have e := exec_load_word (trap := linux.trap ω) (s := t) (r := preg x) (q := j + x)
      (n := (encode (.load (preg x) (slotMem x))).length) hR hsp (slot_addr (by omega)) (by omega)
    obtain ⟨t', h2, hm2, hw2, hv2, hk2⟩ := run_restores hjN n (x + 1)
      (t.upd (preg x) (word t.mem lo (j + x)) (encode (.load (preg x) (slotMem x))).length) hR
      (by rw [State.upd_gpr, ite_eq_right (Ne.symm (preg_ne_rsp x))]; exact hsp) hh (by omega) (by omega)
      (by omega)
    refine ⟨t', by rw [restores]; exact (runIs_cons' hh e).trans h2, hm2, hw2, fun l hl => ?_,
      fun r hr => ?_⟩
    · cases l with
      | zero =>
        rw [hk2 _ fun l' hl' e' => by have := preg_inj (by omega) (by omega) e'; omega]
        simp
      | succ l =>
        rw [show x + (l + 1) = x + 1 + l by omega, hv2 l (by omega)]; simp; congr 1; omega
    · rw [hk2 r fun l hl => by have := hr (l + 1) (by omega); rwa [show x + (l + 1) = x + 1 + l by omega] at this]
      have h0 := hr 0 (by omega); rw [Nat.add_zero] at h0
      simp [h0]

theorem restores_ok : ∀ (x n : Nat), ∀ i ∈ restores x n, i.branches = false ∧ i.keepsSp = true
  | _, 0 => by simp [restores]
  | x, n + 1 => by
    simp only [restores, List.forall_mem_cons]
    exact ⟨by simp [Ne.symm (preg_ne_rsp x)], restores_ok (x + 1) n⟩

/-- The callee's return block loads the returned words, restores the location registers, runs
`add rsp, 8F` and `ret`. Run from a related state, it leaves the returned words in the return
registers and the location registers as the caller sees them, restored below `min k F` and kept
above. Then `rsp` is at the caller's frame word `j + F + 1` and `rip` at the return address from
word `j + F`, and memory and the world are unchanged. -/
theorem run_retBlock (hM : MatchAt k c P AP σ lo N s m fn f a j) (hk : KC k c)
    (hok : (selector k c mb lvo).fnOk fn = true) (hret : fn.ret.length ≤ 8)
    (hbelow : Lin.OpsBelow fn.ret fn.frame) {rl : List Instr} (hrl : retLd k c fn.ret = some rl)
    {W : Nat} (hW : Sel.frameW k c fn.frame = W) (hjn : j + W < N)
    (hcode : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) ((rl ++
      restores 0 (min k fn.frame) ++ retTail W).flatMap encode)) (cy : Nat) :
    ∃ t : State, Sel.Leg (A := arch) linux ω (SpIn lo N j) m cy
        ((rl ++ restores 0 (min k fn.frame)).length + (1 + 1)) t ∧
      t.regs.rip = word m.mem lo (j + W) ∧ t.regs.gpr .rsp = wa lo (j + W + 1) ∧
      t.mem = m.mem ∧ t.world = m.world ∧
      (∀ i, i < fn.ret.length → t.regs.gpr (retReg i) = (fn.ret.map (Operand.eval s.frame)).getD i 0) ∧
      ∀ x, x < k → t.regs.gpr (preg x) =
        Sel.callerView lo k m.mem j fn.frame (fun y => m.regs.gpr (preg y)) x := by
  have hroom := hM.roomW
  have hsm := (fnOk_iff.1 hok).1.1
  have hWF : W = min fn.frame k + (fn.frame - (k + c)) := by rw [← hW]; rfl
  obtain ⟨t1, h1, hok1, hm1, hw1, hk1, hv1⟩ := run_retLd (ω := ω) hM hk hok hret hbelow hrl
  have hsp1 : t1.regs.gpr .rsp = wa lo j :=
    (hk1 _ (fun q _ => Ne.symm (retReg_ne_rsp q)) (by decide)).trans hM.sp
  obtain ⟨t2, h2, hm2, hw2, hv2, hk2⟩ := run_restores (ω := ω) (lo := lo) (N := N) (j := j)
    (by omega) (min k fn.frame) 0 t1 (hm1 ▸ hM.region) hsp1 (by rw [hw1]; exact hM.halted)
    (by have := Nat.min_le_left k fn.frame; omega) (by have := Nat.min_le_right k fn.frame; omega)
    (by have := Nat.min_le_right k fn.frame; omega)
  have hsp2 : t2.regs.gpr .rsp = wa lo j :=
    (hk2 _ fun l _ => Ne.symm (preg_ne_rsp _)).trans hsp1
  rw [List.flatMap_append] at hcode
  obtain ⟨hcodeL, hcodeT⟩ := codeAt_append _ _ _ _ hcode
  have hrun : runIs (A := arch) linux ω (rl ++ restores 0 (min k fn.frame)) m =
      some t2 := by rw [runIs_append, h1, Option.bind_some, h2]
  obtain ⟨hrunL, -, -, hripL, hallL⟩ := run_straight cy hM.wx (by rw [hM.rip]; exact hcodeL)
    (fun i hi => (List.mem_append.1 hi).elim (hok1 i) (restores_ok 0 _ i)) hrun
  obtain ⟨t3, e3, hmem3, hw3, hsp3, hrip3, hoth3⟩ := exec_addSp (trap := linux.trap ω)
    (G := W) (n := (encode (Instr.aluRI .add .rsp (UInt32.ofNat (8 * W)))).length)
    hsp2 (by omega)
  obtain ⟨t4, e4, hmem4, hw4, hsp4, hrip4, hoth4⟩ := exec_ret (trap := linux.trap ω)
    (n := (encode Instr.ret).length) hsp3
    (by rw [hmem3, hm2, hm1]; exact load_wa hM.region (by omega))
  have hst3 := step_exec (c := cy + (rl ++ restores 0 (min k fn.frame)).length)
    (by rw [hw2, hw1]; exact hM.halted)
    (by rw [hripL, hM.rip, hm2, hm1]; simpa [retTail] using (codeAt_append _ _ _ _ hcodeT).1) e3
  have hst4 := step_exec (c := cy + (rl ++ restores 0 (min k fn.frame)).length + 1)
    (by rw [hw3, hw2, hw1]; exact hM.halted)
    (by rw [hrip3, hripL, hM.rip, hmem3, hm2, hm1]
        simpa [retTail, UInt64.add_assoc] using (codeAt_append _ _ _ _ hcodeT).2) e4
  refine ⟨t4, (Sel.Leg.mono (fun x hx => ⟨j, by omega, by omega, hx.trans hM.sp⟩)
      ⟨hrunL, hallL⟩).trans ((Sel.Leg.one hst3 ⟨j, by omega, by omega, hsp2⟩
        ⟨j + W, by omega, by omega, hsp3⟩).trans (Sel.Leg.one hst4
        ⟨j + W, by omega, by omega, hsp3⟩ ⟨j + W + 1, by omega, by omega, hsp4⟩)),
    hrip4, hsp4, by rw [hmem4, hmem3, hm2, hm1], by rw [hw4, hw3, hw2, hw1], fun i hi => ?_,
    fun x hx => ?_⟩
  · rw [hoth4 _ (retReg_ne_rsp i), hoth3 _ (retReg_ne_rsp i),
      hk2 _ fun l _ => Ne.symm (preg_ne_retReg _ i)]
    simpa using hv1 i hi
  · rw [hoth4 _ (preg_ne_rsp x), hoth3 _ (preg_ne_rsp x)]
    simp only [Sel.callerView]
    split
    · rename_i hxm; have := hv2 x hxm; simp only [Nat.zero_add, Nat.add_zero] at this; rw [this, hm1]
    · rw [hk2 _ fun l hl e => by have := preg_inj (by omega) (by omega) e; omega,
        hk1 _ (fun q _ => preg_ne_retReg _ _) (preg_ne (r := .r11) rfl)]

end Ret

/-- The values at the places of the moves after a call, with the caller's frame at word `jc`: a
register, or the word of slot `x`, which is frame word `x - c`. -/
def resView (c lo jc : Nat) (t : State) : Place → UInt64
  | .inl r => t.regs.gpr r
  | .inr (.slot x) => word t.mem lo (jc + x - c)
  | .inr (.imm _) => 0

/-- The places the moves after a call may touch: a register other than `rsp`, or a slot whose
word lies in the region and is addressable from `rsp`. -/
def ResOk (c N jc : Nat) : Place → Prop
  | .inl r => r ≠ .rsp
  | .inr (.slot x) => c ≤ x ∧ jc + x - c < N ∧ 8 * (x - c) < 2 ^ 31
  | .inr (.imm _) => False

/-- Running the moves `l` after a call, copies into registers and stores of registers into slots,
follows `PMove.run` on the places `ResOk` admits and changes no other word. -/
theorem run_emitW {ω : Oracle} {c lo N jc : Nat} : ∀ (l : List (Place × Place)) (t : State),
    (∀ p ∈ l, ResOk c N jc p.1 ∧ ∃ r, p.2 = .inl r ∧ ResOk c N jc (.inl r)) →
    Region t.mem lo N → t.regs.gpr .rsp = wa lo jc → t.world.halted = false →
    ∃ t', runIs (A := arch) linux ω (l.flatMap (emitW c)) t = some t' ∧ t'.world = t.world ∧
      Memory.Frame t.mem t'.mem ∧ LowSame lo t.mem t'.mem ∧ Region t'.mem lo N ∧
      t'.regs.gpr .rsp = t.regs.gpr .rsp ∧
      (∀ q, q < N → (∀ x s, (Sum.inr (Operand.slot x), s) ∈ l → q ≠ jc + x - c) →
        word t'.mem lo q = word t.mem lo q) ∧
      ∀ p, ResOk c N jc p → resView c lo jc t' p = Sel.PMove.run (resView c lo jc t) l p
  | [], t, _, hR, _, _ => ⟨t, rfl, rfl, Memory.Frame.refl _, LowSame.refl _ _, hR, rfl,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
  | (p1, p2) :: l, t, hl, hR, hsp, hh => by
    obtain ⟨hd, r, hr, hrok⟩ := hl _ List.mem_cons_self
    simp only at hd hr; subst hr
    have one : ∃ t₁, runIs (A := arch) linux ω (emitW c (p1, .inl r)) t = some t₁ ∧
        t₁.world = t.world ∧ Memory.Frame t.mem t₁.mem ∧ LowSame lo t.mem t₁.mem ∧
        Region t₁.mem lo N ∧ t₁.regs.gpr .rsp = t.regs.gpr .rsp ∧
        (∀ q, q < N → (∀ x, p1 = .inr (.slot x) → q ≠ jc + x - c) →
          word t₁.mem lo q = word t.mem lo q) ∧
        ∀ p, ResOk c N jc p →
          resView c lo jc t₁ p = Sel.PMove.step (resView c lo jc t) p1 (.inl r) p := by
      rcases p1 with d | o
      · have hd' : d ≠ .rsp := hd
        refine ⟨t.upd d (t.regs.gpr r) (encode (.movRR d r)).length,
          (runIs_cons' hh exec_mv).trans rfl, rfl, Memory.Frame.refl _, LowSame.refl _ _, hR,
          by rw [State.upd_gpr, ite_eq_right (Ne.symm hd')], fun _ _ _ => rfl, fun p _ => ?_⟩
        rcases p with q | o
        · simp only [resView, Sel.PMove.step, Sum.inl.injEq, State.upd_gpr]
        · cases o <;> simp [resView, Sel.PMove.step]
      · rcases o with x | w
        · obtain ⟨hx1, hx2, hx3⟩ := hd
          obtain ⟨t₁, e1, hw1, hg1, -, hR1, hF1, hl1, hv1⟩ := exec_store_word (trap := linux.trap ω)
            (r := r) (q := jc + x - c) (n := (encode (.store (slotMem (x - c)) r)).length)
            hR hsp (slotW_addr hx3 hx1) hx2
          refine ⟨t₁, (runIs_cons' hh e1).trans rfl, hw1, hF1, hl1, hR1, by rw [hg1],
            fun q hq hne => by rw [hv1 q hq, ite_eq_right (hne x rfl)], fun p hp => ?_⟩
          rcases p with q | o
          · simp [resView, Sel.PMove.step, hg1]
          · rcases o with x' | w
            · obtain ⟨h1, h2, h3⟩ := hp
              simp only [resView, Sel.PMove.step, Sum.inr.injEq, Operand.slot.injEq]
              rw [hv1 _ h2]
              by_cases hx : x' = x
              · subst hx; simp
              · rw [ite_eq_right (by omega), ite_eq_right hx]
            · cases hp
        · cases hd
    obtain ⟨t₁, h1, w1, hF1, hl1, hR1, sp1, hq1, hv1⟩ := one
    obtain ⟨t', h2, w2, hF2, hl2, hR2, sp2, hq2, hv2⟩ := run_emitW l t₁
      (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hR1 (sp1.trans hsp) (w1 ▸ hh)
    refine ⟨t', by rw [List.flatMap_cons, runIs_append, h1, Option.bind_some, h2], w2.trans w1,
      hF1.trans hF2, hl1.trans hl2, hR2, sp2.trans sp1, fun q hq hne => ?_, fun p hp => ?_⟩
    · rw [hq2 q hq fun x s hs => hne x s (List.mem_cons_of_mem _ hs),
        hq1 q hq fun x he => hne x (.inl r) (by rw [← he]; exact List.mem_cons_self)]
    · rw [hv2 p hp]
      exact Sel.PMove.run_congr (G := ResOk c N jc) l
        (fun q hq => by obtain ⟨-, r', h, h'⟩ := hl q (List.mem_cons_of_mem _ hq); rw [h]; exact h')
        hv1 p hp

/-- `retW` moves the `n` return registers into the locations from `d` on of the frame at word
`jc`, as one parallel move: a copy into a register location, a store into a slot. It keeps
`rsp` and every location outside `d … d + n - 1`. -/
theorem run_retW {ω : Oracle} {k c : Nat} (hk : KC k c) {lo N jc d n : Nat} {rw : List Instr}
    (hrw : retW k c d n = some rw) (t : State) (hR : Region t.mem lo N)
    (hsp : t.regs.gpr .rsp = wa lo jc) (hh : t.world.halted = false) (hN : jc + (d + n - c) ≤ N)
    (h31 : 8 * (d + n) < 2 ^ 31) (hn : n ≤ 8) :
    ∃ t', runIs (A := arch) linux ω rw t = some t' ∧
      (∀ x ∈ rw, x.branches = false ∧ x.keepsSp = true) ∧ rw.length ≤ resFuel n ∧
      t'.world = t.world ∧ Memory.Frame t.mem t'.mem ∧ LowSame lo t.mem t'.mem ∧
      Region t'.mem lo N ∧
      (∀ q, q < N → word t'.mem lo q =
        if jc + d ≤ q + c ∧ q + c < jc + d + n ∧ k + c ≤ q + c - jc then
          t.regs.gpr (retReg (q + c - jc - d))
        else word t.mem lo q) ∧
      (∀ x, x < k + c → t'.regs.gpr (loc k x) =
        if d ≤ x ∧ x < d + n then t.regs.gpr (retReg (x - d)) else t.regs.gpr (loc k x)) ∧
      t'.regs.gpr .rsp = t.regs.gpr .rsp := by
  simp only [retW, Option.map_eq_some_iff] at hrw
  obtain ⟨l, hseq, rfl⟩ := hrw
  have hmem : ∀ {p : Place × Place}, p ∈ resMoves k c d n ↔
      ∃ i, i < n ∧ p = (place k c (.slot (d + 0 + i)), .inl (retReg (0 + i))) :=
    Sel.mem_resMoves 0 n
  have hpl : ∀ x, place k c (.slot x) = if x < k + c then .inl (loc k x) else .inr (.slot x) :=
    fun _ => rfl
  have hnd : ((resMoves k c d n).map (·.1)).Nodup := Sel.resMoves_nodup 0 n fun a b _ _ _ _ he => by
    have := Sel.place_slot_inj (fun x y hx hy h => loc_inj hk hx hy h) he; omega
  have ht : ∀ p ∈ resMoves k c d n, p.1 ≠ .inl .r11 := fun p hp e => by
    obtain ⟨i, hi, rfl⟩ := hmem.1 hp
    simp only [hpl] at e; split at e
    · exact loc_ne (r := .r11) rfl (Sum.inl.inj e)
    · cases e
  have hok : ∀ p ∈ l, ResOk c N jc p.1 ∧ ∃ r, p.2 = .inl r ∧ ResOk c N jc (.inl r) := fun p hp => by
    constructor
    · rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
      · rw [h]; exact (by decide : Reg.r11 ≠ .rsp)
      · obtain ⟨i, hi, rfl⟩ := hmem.1 hq; rw [← he]; simp only [hpl]
        split
        · exact loc_ne_rsp _ _
        · exact ⟨by omega, by omega, by omega⟩
    · rcases Sel.PMove.seq_src _ hseq p hp with h | ⟨q, hq, he⟩
      · exact ⟨.r11, h, (by decide : Reg.r11 ≠ .rsp)⟩
      · obtain ⟨i, hi, rfl⟩ := hmem.1 hq
        exact ⟨_, he.symm, retReg_ne_rsp _⟩
  obtain ⟨t', h1, w1, hF1, hl1, hR1, sp1, hq1, hv1⟩ := run_emitW (ω := ω) l t hok hR hsp hh
  have par : ∀ p, ResOk c N jc p → p ≠ .inl .r11 →
      resView c lo jc t' p = Sel.PMove.par (resView c lo jc t) (resMoves k c d n) p :=
    fun p hp hp11 => by rw [hv1 p hp, Sel.PMove.seq_run _ hnd ht hseq _ _ hp11]
  have into : ∀ x, d ≤ x → x < d + n →
      (place k c (.slot x), (.inl (retReg (x - d)) : Place)) ∈ resMoves k c d n :=
    fun x h1 h2 => hmem.2 ⟨x - d, by omega, by simp [show d + (x - d) = x by omega]⟩
  have hlenW : ∀ (l' : List (Place × Place)), (l'.flatMap (emitW c)).length ≤ l'.length := by
    intro l'; induction l' with
    | nil => simp
    | cons p l' ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have : (emitW c p).length ≤ 1 := by
        rcases p with ⟨d' | o, r | o'⟩ <;> (try rcases o with x | w) <;> simp [emitW]
      omega
  refine ⟨t', h1, fun x hx => ?_, Nat.le_trans (hlenW l) (Sel.PMove.seq_length _ hseq), w1, hF1, hl1,
    hR1, fun q hq => ?_, fun x hx => ?_, sp1⟩
  · obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨hd, r, hr, -⟩ := hok p hp
    rcases p with ⟨d' | o, r'⟩ <;> simp only at hr <;> subst hr
    · simp only [emitW, List.mem_singleton] at hx; subst hx
      simp [Instr.writes, Instr.branches, Ne.symm (show d' ≠ .rsp from hd)]
    · rcases o with x' | w
      · simp only [emitW, List.mem_singleton] at hx; subst hx; simp [Instr.writes, Instr.branches]
      · simp [emitW] at hx
  · by_cases hc : jc + d ≤ q + c ∧ q + c < jc + d + n ∧ k + c ≤ q + c - jc
    · rw [if_pos hc]
      have e := par (.inr (.slot (q + c - jc))) ⟨by omega, by omega, by omega⟩ (by simp)
      rw [Sel.PMove.par_of_mem hnd _ (by
        have := into (q + c - jc) (by omega) (by omega); rwa [hpl, if_neg (by omega)] at this)] at e
      simp only [resView] at e
      rw [show jc + (q + c - jc) - c = q by omega] at e
      exact e
    · rw [if_neg hc, hq1 q hq fun x s hs he => ?_]
      rcases Sel.PMove.seq_dst _ hseq _ hs with h | ⟨p, hp, hpe⟩
      · cases h
      · obtain ⟨i, hi, rfl⟩ := hmem.1 hp
        simp only [hpl] at hpe; split at hpe
        · cases hpe
        · cases hpe; exact hc ⟨by omega, by omega, by omega⟩
  · have e := par (.inl (loc k x)) (loc_ne_rsp _ _) (fun h => loc_ne (r := .r11) rfl (Sum.inl.inj h))
    simp only [resView] at e
    rw [e]
    by_cases hd' : d ≤ x ∧ x < d + n
    · rw [if_pos hd', Sel.PMove.par_of_mem hnd _ (by
        have := into x hd'.1 hd'.2; rwa [hpl, if_pos hx] at this)]
      rfl
    · rw [if_neg hd', Sel.PMove.par_of_not _ fun s hs => ?_]
      · rfl
      · obtain ⟨i, hi, he⟩ := hmem.1 hs
        simp only [Prod.mk.injEq, hpl] at he
        obtain ⟨he, -⟩ := he
        split at he
        · exact hd' (by have := loc_inj hk hx ‹_› (Sum.inl.inj he); omega)
        · cases he

section Sim
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- The caller of the running activation finds its preserved locations through the running
activation's save words, as `callerView` describes. -/
theorem caller_locs {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64}
    {j : Nat} (hM : MatchAt k c P A σ lo N s m fn f a j) {act : Lin.Act}
    {st : List Lin.Act} (hst : s.stack = act :: st) {fa : Lin.Fn} (hfa : P.funs[act.fn]? = some fa) :
    ∃ rv₀ : Sel.RegView, (∀ x, x < k →
      rv₀ x = Sel.callerView lo k m.mem j fn.frame (fun y => m.regs.gpr (preg y)) x) ∧
      Sel.LocsOk lo k c rv₀ m.mem (j + (Sel.frameW k c fn.frame + 1)) fa.frame act.frame := by
  have hFr := hM.frames; rw [hst] at hFr
  obtain ⟨rv₀, hv, hL⟩ := Sel.frames_caller hFr
  rw [Sel.calleeFrame_eq hM.hfn, Sel.calleeFrame_eq hfa] at hL
  rw [Sel.calleeFrame_eq hM.hfn] at hv
  exact ⟨rv₀, fun x hx => by rw [hv x hx]; simp [Sel.callerView, conv, loc_of_lt hx], hL⟩

/-- The Lin instruction `ret` runs as the callee's return block followed, back in the caller's
call block, by the moves of the returned words into their locations. The machine state after
them is related to a state related to the Lin state after the return, up to the caller-saved
locations that the call destroys and does not define. -/
theorem sim_ret (hk : KC k c) (hsel : select k c P mb = .ok A) (hwf : P.Wf) {ω : Oracle}
    {κ : CostModel} {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64}
    {j : Nat} (hM : MatchAt k c P A σ lo N s m fn f a j) (hi : fn.code[s.pc]? = some .ret)
    {act : Lin.Act} {st : List Lin.Act} (hst : s.stack = act :: st) (cy : Nat) :
    ∃ n m' fa fc addr j' s'', M.run ω (m, cy) n = some (m', cy + n) ∧
      n ≤ instrs k c mb none P 0 0 fn .ret ∧ 0 < n ∧
      (RegAlloc.Live.flex P).R (Lin.exec κ ω fn .ret s |>.getD s) s'' ∧
      MatchAt k c P A σ lo N s'' m' fa fc addr j' ∧ RunAll ω (SpIn lo N j) (m, cy) n := by
  obtain ⟨b, hC⟩ := ctx_of asmLaws (select_ok hsel) hwf hM hi
  obtain ⟨dd, hsi, _⟩ := hC.instr
  simp only [selector, selInstr] at hsi
  split at hsi
  · cases hsi
  rename_i rl hrl
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsi
  obtain ⟨rfl, rfl⟩ := hsi
  obtain ⟨fa, args, fc, addr, hfa, hfc, haddr, hpc0, hcall, hra, hroomc⟩ := hM.caller hst
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c fn.frame = W := ⟨_, rfl⟩
  change j + (Sel.frameW k c fn.frame + 1) + Sel.frameW k c fa.frame ≤ N at hroomc
  change word m.mem lo (j + Sel.frameW k c fn.frame) = _ at hra
  rw [hW] at hroomc hra
  have hWa : Sel.frameW k c fa.frame = min fa.frame k + (fa.frame - (k + c)) := rfl
  obtain ⟨rv₀, hrv, hCL⟩ := caller_locs hM hst hfa
  rw [hW] at hCL
  -- the callee's return block
  obtain ⟨ins, hr, hcode⟩ := seqAt_x64 hC.code
  obtain rfl := resolveAt_ops_inv (is := rl ++ restores 0 (min k fn.frame) ++
    retTail W) (by simpa [ops, hW] using hr)
  obtain ⟨⟨-, hret⟩, -, -⟩ := fnOk_iff.1 hC.sel.ok
  obtain ⟨m₃, L₃, hrip₃, hsp₃, hmem₃, hw₃, hgpr₃, hcv₃⟩ := run_retBlock (ω := ω) hM hk hC.sel.ok
    hret hC.fwf.1 hrl hW (by omega) hcode cy
  -- the caller's result stores, in its call block
  obtain ⟨bc, dc, hbc, hsic, hcodec, hsfc⟩ := Sel.block_at asmLaws (select_ok hsel) hM.loaded hfa
    hfc haddr hcall
  obtain ⟨_, -, gf, hgf, hal, hdst⟩ := (hwf.2 act.fn fa hfa).2 _ (List.mem_of_getElem? hcall)
  rw [hM.hfn] at hgf; cases hgf
  simp only [selector, selInstr, hM.hfn, ite_eq_left hal] at hsic
  split at hsic
  rotate_left
  · cases hsic
  rename_i rw _ hrw
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsic
  obtain ⟨rfl, rfl⟩ := hsic
  obtain ⟨insc, hrc, hcodec'⟩ := seqAt_x64 hcodec
  obtain ⟨i₀, i₃, rfl, hr₀, hr₃⟩ := resolveAt_append (A := arch) _ _ _ insc hrc
  obtain rfl := resolveAt_ops_inv hr₃
  rw [List.flatMap_append] at hcodec'
  obtain ⟨m₄, hr₄, hok₄, hlen₄, hw₄, hF₄, hl₄, hR₄, hq₄, hp₄, ho₄⟩ := run_retW (ω := ω) (lo := lo)
    (N := N) (jc := j + W + 1) (d := act.dst) (n := fn.ret.length) hk hrw m₃ (hmem₃ ▸ hM.region)
    hsp₃ (by rw [hw₃]; exact hM.halted) (by omega) (by have := (fnOk_iff.1 hsfc.ok).1.1; omega)
    (by omega)
  have hraddr : m₃.regs.rip = addr + UInt64.ofNat (fc.labelOff (act.pc - 1)) +
      UInt64.ofNat ((i₀.flatMap encode).length) := by
    rw [hrip₃, (Asm.resolveAt_size asmLaws _ _ _ _ hr₀ (encodeAll_eq _)).1, hra]
    simp only [conv, callIs, UInt64.ofNat_add, UInt64.add_assoc, calleeFrame_eq hM.hfn]
    rw [Asm.seqSize_append, UInt64.ofNat_add]; rfl
  obtain ⟨hrunS, hFS, -, hripS, hallS⟩ := run_straight
    (cy + ((rl ++ restores 0 (min k fn.frame)).length + (1 + 1))) (hmem₃ ▸ hM.wx)
    (by rw [hraddr, hmem₃]; exact (codeAt_append _ _ _ _ hcodec').2) hok₄ hr₄
  have L := L₃.trans (Sel.Leg.mono (fun x hx => ⟨j + W + 1, by omega, by omega,
    hx.trans hsp₃⟩) ⟨hrunS, hallS⟩)
  have hLT : ∀ y, y < fa.frame → ((conv k c).kill (.call s.fn args act.dst) y = false ∨
      RegAlloc.Live.defs P (.call s.fn args act.dst) y = true) →
      Sel.locVal (conv k c) lo m₄ (j + W + 1) y =
        Flat.Frame.writes act.frame act.dst (fn.ret.map (Operand.eval s.frame)) y := by
    intro y hy hky
    have hcl := hCL y hy
    show (if y < k + c then m₄.regs.gpr (loc k y) else word m₄.mem lo (j + W + 1 + y - c)) = _
    rw [Sel.writes_apply]
    simp only [List.length_map]
    by_cases hyc : y < k + c
    · rw [ite_eq_left hyc, hp₄ y hyc]; rw [ite_eq_left hyc] at hcl
      by_cases hd : act.dst ≤ y ∧ y < act.dst + fn.ret.length
      · rw [ite_eq_left hd, ite_eq_left hd, hgpr₃ _ (by omega)]
      · rw [ite_eq_right hd, ite_eq_right hd]
        have hyk : y < k := by
          rcases hky with h | h
          · simp [conv, RegAlloc.Alloc.Classes.across, cls] at h; omega
          · simp [RegAlloc.Live.defs, RegAlloc.retLen, hM.hfn] at h; omega
        rw [loc_of_lt hyk, hcv₃ y hyk, ← hrv y hyk, hcl]
    · rw [ite_eq_right hyc, hq₄ _ (by omega)]; rw [ite_eq_right hyc] at hcl
      by_cases hd : act.dst ≤ y ∧ y < act.dst + fn.ret.length
      · rw [ite_eq_left (by omega), ite_eq_left hd, hgpr₃ _ (by omega)]; congr 3; omega
      · rw [ite_eq_right (by omega), ite_eq_right hd, hmem₃, ← hcl]; rfl
  simp only [Lin.exec, hst, Option.getD_some]
  obtain ⟨s'', hR'', hM''⟩ := Sel.matchAt_ret_kill hM hst hfa hfc haddr
    (by have := pc_lt hcall; omega) (j' := j + W + 1) (by simp only [conv]; omega)
    (by simp [conv, φ, FrameModel.words, hW]) (by rw [hw₄, hw₃]) (hmem₃ ▸ hFS) (by rw [← hmem₃]; exact hl₄) hR₄ trivial
    (by
      show m₄.regs.rip = addr + UInt64.ofNat (fc.labelOff act.pc)
      rw [hripS, hraddr, UInt64.add_assoc, ← UInt64.ofNat_add, ← List.length_append,
        ← List.flatMap_append, next_rip hbc hrc, show act.pc - 1 + 1 = act.pc by omega])
    (show m₄.regs.gpr .rsp = _ by rw [ho₄]; exact hsp₃) (clob_of_select hsel) hpc0 hcall hLT
    (fun x hx => by simp at hx; rw [hq₄ _ (by omega), ite_eq_right (by omega), hmem₃])
    (fun i hi hi' => by
      simp only [conv_k, conv_c] at hi; rw [hq₄ _ hi', ite_eq_right (by omega), hmem₃])
    (fun x hx hxk => by
      change x < k at hxk
      show m₄.regs.gpr (loc k x) = _
      rw [hp₄ x (by omega), ite_eq_right (by omega), loc_of_lt hxk, hcv₃ x hxk]
      simp [Sel.callerView, conv, loc_of_lt hxk]) trivial
  have e : instrs k c mb none P 0 0 fn .ret =
      (rl ++ restores 0 (min k fn.frame) ++ retTail W).length + resFuel fn.ret.length := by
    simp only [instrs, hrl, Option.getD_some, hW]
  exact ⟨_, m₄, fa, fc, addr, j + W + 1, s'', L.run, by
    rw [e]; simp only [List.length_append, retTail, List.length_cons, List.length_nil] at hlen₄ ⊢
    omega, by omega, hR'', hM'', L.all⟩

end Sim

/-! ## One Lin step -/

section Sim
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- `rsp` is within the static stack bound of the program below the top of the stack. -/
abbrev SpBound (k c : Nat) (P : Lin.Prog) (lo N : Nat) : State → Prop :=
  Sel.SpBound (A := arch) (conv k c) P lo N

theorem spBound_of_spIn {lo N lo' : Nat} (_htop : lo + 8 * N ≤ 2 ^ 47)
    (hb : 8 * (N - lo') ≤ P.stackBytes (conv k c).φ) {x : State} (h : SpIn lo N lo' x) :
    SpBound k c P lo N x := by
  obtain ⟨i, h1, h2, h3⟩ := h
  show (wa lo N - x.regs.gpr .rsp).toNat ≤ P.stackBytes (conv k c).φ
  rw [h3]
  have : lo + 8 * i ≤ lo + 8 * N := by omega
  simp only [wa, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp; omega

theorem spBound_of_match' {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch}
    {a : UInt64} {j : Nat} (hM : MatchAt k c P A σ lo N s m fn f a j) {x : State}
    (h : SpIn lo N j x) : SpBound k c P lo N x :=
  spBound_of_spIn hM.region.top (matchAt_room hM).2 h

theorem selInstr_ext {P : Lin.Prog} {i pc : Nat} {fn : Lin.Fn} {sym : String} {nr : Bool}
    {x : Nat} {args : List Flat.ExtArg} {b : List SI} {d : List (String × List UInt8)}
    {lvo : Option RegAlloc.LiveSets}
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

/-- x64's cases of one Lin step with `k ≤ 6` register locations, one for each kind of Lin
instruction. -/
theorem cases (hk : KC k c) (hsel : select k c P mb = .ok A) (hwf : P.Wf)
    (hB : P.stackBytes (conv k c).φ ≤ 8 * N) :
    Sel.Cases (A := arch) linux (conv k c) P A σ lo N (RegAlloc.Live.flex P)
      ((counts k c mb (RegAlloc.Live.of P)).ins P) (selector k c mb (RegAlloc.Live.of P)) where
  mov := ((Ops.sim_mov (selOps_laws (lvo := RegAlloc.Live.of P) hk) asmLaws laws (select_ok hsel) hwf).at _).of_eq
    fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  bin := ((Ops.sim_bin (selOps_laws (lvo := RegAlloc.Live.of P) hk) asmLaws laws (select_ok hsel) hwf
    (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  load := ((Ops.sim_load (selOps_laws (lvo := RegAlloc.Live.of P) hk)
    (selOps_memLaws (lvo := RegAlloc.Live.of P) hk) asmLaws laws (select_ok hsel) hwf).step.at
    _).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  store := ((Ops.sim_store (selOps_laws (lvo := RegAlloc.Live.of P) hk)
    (selOps_memLaws (lvo := RegAlloc.Live.of P) hk) asmLaws laws (select_ok hsel) hwf).step.at
    _).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  jmp := (StepOk.at (cnt := instrs k c mb none P 0 0) _ <| LocalOk.step fun ω κ s m cy fn f a j _ hM hi ⟨l, he⟩ _ => by
    subst he; exact ⟨by simp [instrs, selInstr], sim_jmp hsel hwf (κ := κ) hM hi cy⟩).of_eq
    fun _ _ _ _ ⟨_, h⟩ => by subst h; rfl
  jz := (StepOk.at (cnt := instrs k c mb none P 0 0) _ <| LocalOk.step fun ω κ s m cy fn f a j _ hM hi ⟨o, l, he⟩ _ => by
    subst he
    have hc : instrs k c mb none P 0 0 fn (.jz o l) = (src k c .rax o).1.length + 1 + 1 := by
      simp [instrs, selInstr, ops]
    rw [hc]; exact ⟨by omega, sim_jz hsel hwf (κ := κ) hM hi cy⟩).of_eq
    fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  call ω κ s s' m cy fn f a j _ hM hi := fun ⟨g, args, d, he⟩ hs => by
    subst he
    obtain ⟨rfl, -⟩ := step_getD hM hi hs
    obtain ⟨n, m', _, _, _, _, s'', h1, h0, hR, h2, h3⟩ := sim_call hk hsel hwf hB (ω := ω) (κ := κ) hM hi cy
    exact ⟨n, m', h1, Or.inl ⟨s'', hR, _, _, _, _, h2⟩, by omega,
      RunAll.mono (fun _ => spBound_of_match' h2) h3, by rw [h0]; exact Nat.le_refl _⟩
  ret ω κ s s' m cy fn f a j _ hM hi := fun he hs => by
    subst he
    obtain ⟨rfl, -⟩ := step_getD hM hi hs
    cases hst : s.stack with
    | nil => simp [Lin.step, Lin.exec, hM.run, hM.hfn, hi, hst, Lin.Instr.memOk] at hs
    | cons act st =>
      obtain ⟨n, m', _, _, _, _, s'', h1, h0, hpos, hR, h2, h3⟩ :=
        sim_ret hk hsel hwf (ω := ω) (κ := κ) hM hi hst cy
      exact ⟨n, m', h1, Or.inl ⟨s'', hR, _, _, _, _, h2⟩, fun h => absurd h (by omega),
        RunAll.mono (fun _ => spBound_of_match' hM) h3, h0⟩
  exit := ((Ops.sim_exit (selOps_laws (lvo := RegAlloc.Live.of P) hk) (selOps_ext hk) asmLaws laws (select_ok hsel)
    hwf).step.at _).of_eq fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  write := ((Ops.sim_write (selOps_laws (lvo := RegAlloc.Live.of P) hk) (selOps_ext hk) asmLaws laws (select_ok hsel)
    hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, h⟩ => by subst h; rfl
  writeMem := ((Ops.sim_writeMem (selOps_laws (lvo := RegAlloc.Live.of P) hk) (selOps_ext hk) asmLaws laws
    (select_ok hsel) hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  read := ((Ops.sim_read (selOps_laws (lvo := RegAlloc.Live.of P) hk) (selOps_ext hk) asmLaws laws (select_ok hsel)
    hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  readMem := ((Ops.sim_readMem (selOps_laws (lvo := RegAlloc.Live.of P) hk) (selOps_ext hk) asmLaws laws
    (select_ok hsel) hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  tick _ _ _ _ := ⟨by simp [counts, instrs, selInstr], fun _ _ _ _ h => by
    simp only [selector, selInstr] at h; cases h; rfl⟩
  ext _ _ _ _ _ _ _ _ _ h := selInstr_ext h

end Sim

/-! ## The forward simulation -/

section Sim
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

/-- The state the loader must provide, for `k` preserved and `c` caller-saved register
locations. The program is loaded under `σ` in W^X memory, with a stack region of `N` words below
`wa lo N` whose top words, `main`'s frame, read as zero and which has room for the static stack
bound. `rip` is at `main`'s symbol, `rsp` at the top of the
region, the world is empty and the location registers are zero, since Linux and the loader
model start every register but `rsp` at zero. -/
structure Init (k c : Nat) (P : Lin.Prog) (A : Asm.Prog arch) (σ : String → Option UInt64)
    (lo N : Nat) (m₀ : State) : Prop where
  world : m₀.world = World.init
  wx : m₀.mem.WxorX
  loaded : A.Loaded σ m₀.mem
  region : Region m₀.mem lo N
  entry : ∃ f, A.funs[P.main]? = some f ∧ σ f.name = some m₀.regs.rip
  sp : m₀.regs.gpr .rsp = wa lo N
  zero : ∀ fn, P.funs[P.main]? = some fn → ∀ x, x < Sel.frameW k c fn.frame →
    load64 m₀.mem (wa lo (N - Sel.frameW k c fn.frame + x)) = some 0
  bound : P.stackBytes (φ.words k c) ≤ 8 * N
  /-- The program's zero-initialised writable regions, such as the data region `mp_mem`, are in
  place, readable, writable and zero. -/
  bss : A.BssAt σ m₀.mem
  /-- Those regions lie below the stack region. -/
  below : ∀ b ∈ A.bss, ∀ D, σ b.1 = some D → D.toNat + b.2 ≤ lo
  /-- Every register but `rsp` is zero. -/
  regs0 : ∀ r, r ≠ .rsp → m₀.regs.gpr r = 0

/-- From the loaded state, `main`'s `sub rsp, 8F` takes one step to a state related to the
initial Lin state `P.init`. -/
theorem sim_entry (hsel : select k c P mb = .ok A) {ω : Oracle} {m₀ : State}
    (hI : Init k c P A σ lo N m₀) (cy : Nat) :
    ∃ m₁ fn f a j, M.step ω (m₀, cy) = some (m₁, cy + 1) ∧ MatchAt k c P A σ lo N P.init m₁ fn f a j := by
  obtain ⟨hmain, hml, _, hk⟩ := Sel.select_spec (select_ok hsel)
  obtain ⟨fn, hfn⟩ : ∃ fn, P.funs[P.main]? = some fn := ⟨_, List.getElem?_eq_getElem hml⟩
  obtain ⟨f, hf, hsf⟩ := hk P.main fn hfn
  obtain ⟨f', hf', hσ⟩ := hI.entry
  rw [hf] at hf'; cases hf'
  obtain ⟨a, ha, hentry, _⟩ := Sel.fn_code asmLaws hI.loaded (List.mem_of_getElem? hf)
  rw [hσ] at ha; cases ha
  have hok := (fnOk_iff.1 hsf.ok).1
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c fn.frame = W := ⟨_, rfl⟩
  have hWF : W ≤ fn.frame := hW ▸ Sel.frameW_le k c fn.frame
  have hroom : W + 1 ≤ N := by
    have h1 := Lin.frameBytes_le (φ.words k c) P P.main
    rw [frameBytes_eq hfn] at h1
    have h2 := hI.bound
    simp only [Lin.Prog.stackBytes] at h2
    omega
  obtain ⟨ie, he, hecode⟩ := seqAt_x64 hentry
  rw [hsf.entry] at he
  simp only [selector, hW] at he
  obtain rfl := resolveAt_ops_inv (is := [Instr.aluRI .sub .rsp (UInt32.ofNat (8 * W))]) he
  obtain ⟨m₁, e1, hmem, hw, hsp, hrip⟩ := exec_subSp (trap := linux.trap ω) (G := W)
    (n := (encode (Instr.aluRI .sub .rsp (UInt32.ofNat (8 * W)))).length) hI.sp
    (by omega) (by omega)
  have hregs : ∀ x, m₁.regs.gpr (loc k x) = 0 := fun x => by
    rw [exec_gpr (by nofun) e1 _ (by simp [Instr.writes, Alu.writes])]
    exact hI.regs0 _ (loc_ne_rsp k x)
  have hst := step_exec (c := cy) (by rw [hI.world]; rfl) (by simpa using hecode) e1
  refine ⟨m₁, fn, f, m₀.regs.rip, N - W, hst, ?_⟩
  refine ⟨hw.trans hI.world, rfl, by rw [hmem]; exact hI.wx,
    by rw [hmem]; exact hI.loaded, by rw [hmem]; exact hI.region, hfn, hf, hσ, trivial,
    Nat.zero_le _, ?_, hsp, ?_, ?_, rfl,
    by rw [hmem]; exact dataOk_init (Sel.select_bss (select_ok hsel)) hI.bss hI.below, fun _ _ _ _ => trivial, trivial⟩
  · show m₁.regs.rip = m₀.regs.rip + UInt64.ofNat (f.labelOff 0)
    rw [hrip]
    simp only [Asm.Fn.labelOff, hsf.entry, Asm.blocksOff, Nat.add_zero]
    rfl
  · show Frames (conv k c) P A σ lo N m₁.mem P.main Flat.Frame.zero [] (N - W) _
    refine ⟨show N - W + Sel.frameW k c (calleeFrame P P.main) = N by
      rw [calleeFrame_eq hfn, hW]; omega, fun x hx => ?_⟩
    rw [calleeFrame_eq hfn] at hx
    show (if x < k + c then m₁.regs.gpr (loc k x) else _) = 0
    split
    · exact hregs x
    · have hx' : x - c < W := hW ▸ Sel.slot_lt_frameW hx (by omega)
      rw [hmem, conv_c, show N - W + x - c = N - W + (x - c) by omega]
      have hz := hI.zero fn hfn (x - c) (hW ▸ hx'); rw [hW] at hz
      exact word_eq_of_load hI.region (by omega) hz
  · show 8 * (N - W) + Lin.State.depth (φ.words k c) P P.init = 8 * N + 8
    simp only [Lin.State.depth, Lin.Prog.init, List.map_nil, List.sum_nil, frameBytes_eq hfn, hW]
    omega

/-- x64's package for the shared simulation. Related states satisfy `MatchAt`, the loader
provides `Init`, the stack pointer stays within `P.stackBytes φ` of the top, and a Lin step takes
`instrs` machine instructions. -/
abbrev pkg (k c : Nat) (mb : Bool) (P : Lin.Prog) (A : Asm.Prog arch) (σ : String → Option UInt64) (lo N : Nat) :
    Sel.SimPkg (A := arch) linux P :=
  Sel.pkg linux (conv k c) P A σ lo N (RegAlloc.Live.flex P) (Init k c P A σ lo N)
    (counts k c mb (RegAlloc.Live.of P))

/-- x64's package satisfies the laws of the shared simulation, so the shared soundness, stack
and cost theorems hold for x64. -/
theorem pkg_laws (hk : KC k c) (hsel : select k c P mb = .ok A) (hwf : P.Wf)
    (hB : P.stackBytes (φ.words k c) ≤ 8 * N) : (pkg k c mb P A σ lo N).Laws :=
  Sel.pkg_laws asmLaws (select_ok hsel) hwf (cases hk hsel hwf hB) (fun _ hI => hI.world)
    (fun m₀ hI => by show (wa lo N - m₀.regs.gpr .rsp).toNat ≤ _; rw [hI.sp]; simp) Nat.one_pos
    fun ω m₀ c hI => by
      obtain ⟨m₁, fn, f, a, j, hst, hM⟩ := sim_entry hsel hI c
      exact ⟨m₁, Sem.run_one hst, ⟨fn, f, a, j, hM⟩, RunAll.one
        (show (wa lo N - m₀.regs.gpr .rsp).toNat ≤ _ by rw [hI.sp]; simp) hst
        (spBound_of_match' hM ⟨j, Nat.le_refl _, (matchAt_room hM).1, hM.sp⟩)⟩

end Sim

end Millipede.X64
