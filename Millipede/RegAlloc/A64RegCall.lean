import Millipede.RegAlloc.A64RegProof
import Millipede.RegAlloc.Live

/-!
# arm64 with register locations: calls and returns

This module proves the `call` and `ret` cases of the register selector `selector k c` at the
convention `conv k c`, in which each preserved location register is saved by the caller into a
word of the callee's frame and the caller-saved ones are destroyed by the call. Each piece of the
call and return blocks gets a lemma that runs it, and the two cases compose those runs.

A call block sets `x17` to the callee frame, saves the preserved location registers that
`Live.callKeep` names into its low words, writes the memory arguments while the caller's registers
are still in place, loads the preserved register arguments (`run_argRegs`), then the caller-saved
ones (`run_cArgs`: the parallel move of those in caller-saved registers, then `run_cLoads`), and
branches with `bl` to the callee's entry. A return block loads the returned words into `x0, …`,
restores the saved registers, reloads `x30` and pops the frame. Back in the caller, the result
words go to their locations, by a copy into a register location and by a store into a slot, and
the caller is related to Lin's state up to the caller-saved locations the call destroyed
(`Sel.matchAt_ret_kill`).

The main results are `run_callBlock`, `run_retBlock`, `simCall`, `simRet` and `cases`.
-/

namespace Millipede.RegAlloc.A64Reg

open Flat (Operand)
open Millipede.A64 (State Regs Reg Instr runA runA_cons runA_append runA_nil arch linux isa
  ldIs stIs immIs farPre farA maxFrame fw fsize padArgs retStores frameI farProg plain
  straight_all)

/-! ## Runs of the pieces -/

section Run
variable {ω : Oracle}

theorem preg_eq (x : Nat) : preg x = BitVec.ofNat 5 (19 + x) := rfl

theorem saves_plain (keep : Nat → Bool) : ∀ (x n : Nat), ∀ i ∈ saves keep x n, plain i = true
  | _, 0 => by simp [saves]
  | x, n + 1 => by
    simp only [saves]
    refine List.forall_mem_append.2 ⟨?_, saves_plain keep (x + 1) n⟩
    split <;> simp only [List.mem_singleton, forall_eq, List.not_mem_nil, false_imp_iff,
      implies_true]
    rfl

/-- Running `saves keep x n` with `x17` at word `i` sets each word `i + y` with
`x ≤ y < x + n` and `keep y` to the register `x(19+y)`. It changes no register but `pc` and no
other word of the region. -/
theorem run_saves {lo N i : Nat} (keep : Nat → Bool) : ∀ (n x : Nat) (t : State),
    t.regs.x 17 = Sel.wa lo i → Sel.Region t.mem lo N → i + x + n ≤ N → x + n ≤ 10 →
    t.world.halted = false → t.regs.pc % 4 = 0 →
    ∃ t', runA ω (saves keep x n) t = some t' ∧
      t'.regs = { t.regs with pc := t.regs.pc + UInt64.ofNat (4 * (saves keep x n).length) } ∧
      t'.world = t.world ∧ Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧
      Sel.Region t'.mem lo N ∧
      ∀ q, q < N → Sel.word t'.mem lo q = if i + x ≤ q ∧ q < i + x + n
        then (if keep (q - i) then t.regs.x (preg (q - i)) else Sel.word t.mem lo q)
        else Sel.word t.mem lo q
  | 0, x, t, _, hR, _, _, _, _ => ⟨t, rfl, by simp [saves], rfl, Memory.Frame.refl _,
      Sel.LowSame.refl _ _, hR, fun q _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, x, t, hb, hR, hiN, hx, hh, ha => by
    cases hk : keep x
    · obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_saves keep n (x + 1) t hb hR (by omega)
        (by omega) hh ha
      refine ⟨t', by simpa [saves, hk] using h1, by simpa [saves, hk] using h2, h3, h4, h5, h6,
        fun q hq => ?_⟩
      rw [h7 q hq]
      by_cases hq' : q = i + x
      · subst hq'
        rw [ite_eq_right (by omega), ite_eq_left (by omega), show i + x - i = x by omega, hk]; rfl
      · by_cases hc : i + (x + 1) ≤ q ∧ q < i + (x + 1) + n
        · rw [ite_eq_left hc, ite_eq_left (show i + x ≤ q ∧ q < i + x + (n + 1) from ⟨by have := hc.1; omega, by have := hc.2; omega⟩)]
        · rw [ite_eq_right hc, ite_eq_right (show ¬(i + x ≤ q ∧ q < i + x + (n + 1)) from fun h => hc ⟨by have := h.1; omega, by have := h.2; omega⟩)]
    · obtain ⟨t1, r1, hreg1, hw1, hF1, hl1, hR1, hq1⟩ := A64.run_retStores (ω := ω) (b := 17)
        (i := i) (N := N) (lo := lo) 1 x (19 + x) t hb (fun h => absurd h (by decide)) hR
        (by omega) (by omega) (by omega) hh ha
      have hb1 : t1.regs.x 17 = Sel.wa lo i := by rw [hreg1]; exact hb
      have ha1 : t1.regs.pc % 4 = 0 := by rw [hreg1]; simpa using A64.aligned_add4 ha
      obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_saves keep n (x + 1) t1 hb1 hR1 (by omega)
        (by omega) (by rw [hw1]; exact hh) ha1
      have e : saves keep x (n + 1) = A64.retStores 17 x (19 + x) 1 ++ saves keep (x + 1) n := by
        simp [saves, hk, A64.retStores, preg]
      have hr : ∀ r, t1.regs.x r = t.regs.x r := fun r => by rw [hreg1]
      refine ⟨t', by rw [e, runA_append, r1, Option.bind_some, h1], ?_, by rw [h3, hw1],
        hF1.trans h4, hl1.trans h5, h6, fun q hq => ?_⟩
      · rw [h2, hreg1, e]
        simp only [List.length_append, A64.retStores, List.length_cons, List.length_nil]
        rw [A64.pc_add, show 4 * 1 + 4 * (saves keep (x + 1) n).length =
          4 * (0 + 1 + (saves keep (x + 1) n).length) by omega]
      · rw [h7 q hq]
        by_cases hq' : q = i + x
        · subst hq'
          rw [ite_eq_right (by omega), hq1 _ hq, ite_eq_left (by omega), ite_eq_left (by omega),
            show i + x - i = x by omega, hk, ite_eq_left rfl]
          simp [preg]
        · rw [hq1 q hq, ite_eq_right (show ¬(i + x ≤ q ∧ q < i + x + 1) by omega)]
          by_cases hc : i + (x + 1) ≤ q ∧ q < i + (x + 1) + n
          · rw [ite_eq_left hc, ite_eq_left (show i + x ≤ q ∧ q < i + x + (n + 1) from ⟨by have := hc.1; omega, by have := hc.2; omega⟩), hr]
          · rw [ite_eq_right hc, ite_eq_right (show ¬(i + x ≤ q ∧ q < i + x + (n + 1)) from fun h => hc ⟨by have := h.1; omega, by have := h.2; omega⟩)]

/-- Running `ldWords b o r n` with the base `b` at word `i` loads each register `x(r+l)` with
`l < n` from word `i + o + l` and changes no other general register. -/
theorem run_ldWords {lo N i : Nat} {b : Reg} : ∀ (n o r : Nat) (t : State),
    t.regs.x b = Sel.wa lo i → (b = 31 → t.regs.x 31 % 16 = 0) → Sel.Region t.mem lo N →
    o + n ≤ 4096 → i + o + n ≤ N → r + n ≤ 31 → (b.toNat < r ∨ r + n ≤ b.toNat) →
    t.world.halted = false → t.regs.pc % 4 = 0 →
    ∃ t', runA ω (ldWords b o r n) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧
      (∀ l, l < n → t'.regs.x (BitVec.ofNat 5 (r + l)) = Sel.word t.mem lo (i + o + l)) ∧
      ∀ q : Reg, (q.toNat < r ∨ r + n ≤ q.toNat) → t'.regs.x q = t.regs.x q
  | 0, _, _, t, _, _, _, _, _, _, _, _, ha =>
    ⟨t, rfl, rfl, rfl, ha, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | n + 1, o, r, t, hb, h16, hR, ho, hiN, hr, hbr, hh, ha => by
    have hr31 : (BitVec.ofNat 5 r : Reg) ≠ 31 := A64.reg_ne (k' := 31) (by omega) (by omega) (by omega)
    have hr31' : ¬ (BitVec.ofNat 5 r : Reg) = 31#5 := hr31
    have h31r : ¬ (31#5 : Reg) = BitVec.ofNat 5 r := fun e => hr31 e.symm
    have hbr' : b ≠ BitVec.ofNat 5 r := fun e => by
      subst e; rw [A64.reg_toNat (by omega)] at hbr; omega
    have x1 := A64.exec_ldr_x (trap := linux.trap ω) (n := 4) (d := BitVec.ofNat 5 r) ha
      (A64.uimm_aligned (BitVec.ofNat 12 o) h16)
      (by rw [A64.ea_uimm hb (by omega)]; exact Sel.readWord_wa hR (show i + o < N by omega))
    obtain ⟨t', h2, hm, hw, ha', hv, hk⟩ := run_ldWords (b := b) (i := i) (N := N) n (o + 1) (r + 1)
      (t.goto (t.regs.setZ (BitVec.ofNat 5 r) (Sel.word t.mem lo (i + o))) (t.regs.pc + 4))
      (by simp [hb, hbr']) (fun e => by subst e; simpa [hr31', h31r] using h16 rfl)
      hR (by omega) (by omega) (by omega) (by omega) (by simpa using hh)
      (by simpa using A64.aligned_add4 ha)
    refine ⟨t', by rw [ldWords, runA_cons hh rfl x1, h2], hm, by simpa using hw, ha',
      fun l hl => ?_, fun q hq => ?_⟩
    · cases l with
      | zero =>
        rw [hk _ (by rw [A64.reg_toNat (by omega)]; omega)]; simp [hr31']
      | succ l =>
        rw [show r + (l + 1) = r + 1 + l by omega, hv l (by omega),
          show i + (o + 1) + l = i + o + (l + 1) by omega]; rfl
    · rw [hk q (by omega)]
      have : q ≠ BitVec.ofNat 5 r := fun e => by subst e; rw [A64.reg_toNat (by omega)] at hq; omega
      simp [hr31', this]

/-- The values at the places of the moves after a call: a register, or the word of slot `x`,
which is word `B + (x - c - bs)` of the region. -/
def resView (c lo B bs : Nat) (t : State) : Place → UInt64
  | .inl r => t.regs.x r
  | .inr (.slot x) => Sel.word t.mem lo (B + (x - c - bs))
  | .inr (.imm _) => 0

/-- The places the moves after a call may touch: a register other than `sp` and the base `b`, or
a slot whose word is addressable from the base and lies in the region. -/
def ResOk (c N B bs : Nat) (b : Reg) : Place → Prop
  | .inl r => r ≠ 31 ∧ r ≠ b
  | .inr (.slot x) => bs + c ≤ x ∧ x - c - bs < 4096 ∧ B + (x - c - bs) < N
  | .inr (.imm _) => False

/-- Running the moves `l` after a call, copies into registers and stores into slots from
registers, follows `Sel.PMove.run` on the places `ResOk` admits, and changes no other word. -/
theorem run_emitW {c lo N B bs : Nat} {b : Reg} (hb : b = 31 ∨ b = 15) :
    ∀ (l : List (Place × Place)) (t : State),
    (∀ p ∈ l, ResOk c N B bs b p.1 ∧ ∃ r, p.2 = .inl r ∧ ResOk c N B bs b (.inl r)) →
    t.regs.x b = Sel.wa lo B → (b = 31 → t.regs.x 31 % 16 = 0) → Sel.Region t.mem lo N →
    t.world.halted = false → t.regs.pc % 4 = 0 →
    ∃ t', runA ω (l.flatMap (emitW c b bs)) t = some t' ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧ Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧
      Sel.Region t'.mem lo N ∧ t'.regs.x 31 = t.regs.x 31 ∧
      (∀ q, q < N → (∀ x s, (Sum.inr (Operand.slot x), s) ∈ l → q ≠ B + (x - c - bs)) →
        Sel.word t'.mem lo q = Sel.word t.mem lo q) ∧
      ∀ p, ResOk c N B bs b p → resView c lo B bs t' p = Sel.PMove.run (resView c lo B bs t) l p
  | [], t, _, _, _, hR, _, ha => ⟨t, rfl, rfl, ha, Memory.Frame.refl _, Sel.LowSame.refl _ _, hR,
      rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | (p1, p2) :: l, t, hl, hbv, h16, hR, hh, ha => by
    obtain ⟨hd, r, hr, hrok⟩ := hl _ List.mem_cons_self
    simp only at hd hr; subst hr
    have hr31 : r ≠ 31 := hrok.1
    have hr31' : ¬ r = 31#5 := hr31
    -- one move: a state that steps the view and keeps the base, `sp` and the other words
    have one : ∃ t₁, runA ω (emitW c b bs (p1, .inl r)) t = some t₁ ∧ t₁.world = t.world ∧
        t₁.regs.pc % 4 = 0 ∧ Memory.Frame t.mem t₁.mem ∧ Sel.LowSame lo t.mem t₁.mem ∧
        Sel.Region t₁.mem lo N ∧ t₁.regs.x 31 = t.regs.x 31 ∧ t₁.regs.x b = t.regs.x b ∧
        (∀ q, q < N → (∀ x, p1 = .inr (.slot x) → q ≠ B + (x - c - bs)) →
          Sel.word t₁.mem lo q = Sel.word t.mem lo q) ∧
        ∀ p, ResOk c N B bs b p →
          resView c lo B bs t₁ p = Sel.PMove.step (resView c lo B bs t) p1 (.inl r) p := by
      rcases p1 with d | o
      · obtain ⟨hd31, hdb⟩ := hd
        have hd31' : ¬ d = 31#5 := hd31
        obtain ⟨t₁, h1, m1, w1, sp1, a1, v1, k1⟩ := A64.ops_run_mv (ω := ω) (r := r) hd31 hh ha
        have kx : ∀ q : Reg, q ≠ d → t₁.regs.x q = t.regs.x q := fun q hq => by
          by_cases h : q = 31#5
          · subst h; exact sp1
          · have := k1 q hq; simpa [Regs.getZ, h] using this
        refine ⟨t₁, h1, w1, a1, m1 ▸ Memory.Frame.refl _, m1 ▸ Sel.LowSame.refl _ _, m1 ▸ hR, sp1,
          kx b (Ne.symm hdb), fun q _ _ => by rw [m1], fun p hp => ?_⟩
        rcases p with q | o
        · simp only [resView, Sel.PMove.step, Sum.inl.injEq]
          split
          · subst q; simpa [Regs.getZ, hd31', hr31'] using v1
          · exact kx q ‹_›
        · cases o <;> simp [resView, Sel.PMove.step, m1]
      · rcases o with x | w
        · obtain ⟨hx1, hx2, hx3⟩ := hd
          obtain ⟨mem1, hw1, hR1, hF1, hv1, hr1⟩ := Sel.writeWord_wa hR hx3 (t.regs.x r)
          have x1 := A64.exec_str_x (trap := linux.trap ω) (n := 4) (d := r) (t := t)
            (ad := .uimm b (BitVec.ofNat 12 (x - c - bs))) ha (A64.uimm_aligned _ h16)
            (by rw [A64.ea_uimm hbv (by omega)]; simpa [A64.getZ_eq, hr31'] using hw1)
          refine ⟨{ t.goto t.regs (t.regs.pc + 4) with mem := mem1 },
            by simp only [emitW]; rw [runA_cons hh rfl x1]; rfl, rfl,
            by simpa using A64.aligned_add4 ha, hF1, Sel.writeWord_wa_low hR (by omega) hw1, hR1,
            rfl, rfl, fun q hq hne => hr1 q hq (hne x rfl), fun p hp => ?_⟩
          rcases p with q | o
          · simp [resView, Sel.PMove.step]
          · rcases o with x' | w
            · simp only [resView, Sel.PMove.step, Sum.inr.injEq, Operand.slot.injEq]
              split
              · subst x'; exact hv1.trans (by simp [A64.getZ_eq, hr31'])
              · obtain ⟨h1, h2, h3⟩ := hp
                exact hr1 _ h3 (by omega)
            · cases hp
        · cases hd
    obtain ⟨t₁, h1, w1, a1, hF1, hl1, hR1, sp1, b1, hq1, hv1⟩ := one
    obtain ⟨t', h2, w2, a2, hF2, hl2, hR2, sp2, hq2, hv2⟩ := run_emitW hb l t₁
      (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (b1.trans hbv)
      (fun e => by rw [sp1]; exact h16 e) hR1 (w1 ▸ hh) a1
    refine ⟨t', by rw [List.flatMap_cons, runA_append, h1, Option.bind_some, h2], w2.trans w1, a2,
      hF1.trans hF2, hl1.trans hl2, hR2, sp2.trans sp1, fun q hq hne => ?_, fun p hp => ?_⟩
    · rw [hq2 q hq fun x s hs => hne x s (List.mem_cons_of_mem _ hs),
        hq1 q hq fun x he => hne x (.inl r) (by rw [← he]; exact List.mem_cons_self)]
    · rw [hv2 p hp]
      exact Sel.PMove.run_congr (G := ResOk c N B bs b) l
        (fun q hq => by obtain ⟨-, r', h, h'⟩ := hl q (List.mem_cons_of_mem _ hq); rw [h]; exact h')
        hv1 p hp

theorem emitW_plain {c : Nat} {b : Reg} {bs : Nat} : ∀ (l : List (Place × Place)),
    (∀ p ∈ l, ∀ d, p.1 = .inl d → d ≠ 31) → ∀ x ∈ l.flatMap (emitW c b bs), plain x = true
  | [], _ => by simp
  | (p1, p2) :: l, h => by
    rw [List.flatMap_cons]
    refine List.forall_mem_append.2 ⟨?_, emitW_plain l fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
    rcases p1 with d | o <;> rcases p2 with r | o' <;> simp only [emitW]
    · simp only [List.mem_singleton, forall_eq]; exact A64.mv_plain (h _ List.mem_cons_self d rfl)
    · simp
    · rcases o with x | w <;> simp [emitW]; rfl
    · rcases o with x | w <;> simp [emitW]

theorem emitW_k29 {c : Nat} {b : Reg} {bs : Nat} : ∀ (l : List (Place × Place)),
    (∀ p ∈ l, ∀ d, p.1 = .inl d → d ≠ 29) → ∀ x ∈ l.flatMap (emitW c b bs), (29 : Reg) ∉ x.writes
  | [], _ => by simp
  | (p1, p2) :: l, h => by
    rw [List.flatMap_cons]
    refine List.forall_mem_append.2 ⟨?_, emitW_k29 l fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
    rcases p1 with d | o <;> rcases p2 with r | o' <;> simp only [emitW]
    · simp only [List.mem_singleton, forall_eq]; exact A64.mv_k29 (h _ List.mem_cons_self d rfl)
    · simp
    · rcases o with x | w <;> simp [emitW, Instr.writes]
    · rcases o with x | w <;> simp [emitW]

/-- No instruction of `retR` writes `x29`: its moves write locations' registers and `x16`, and
its base is `x15`. -/
theorem retR_k29 {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) {P : Lin.Prog} {d n : Nat} {rr : List Instr}
    (hrr : retR k c P d n = some rr) : ∀ x ∈ rr, (29 : Reg) ∉ x.writes := by
  simp only [retR, Option.map_eq_some_iff] at hrr
  obtain ⟨l, hseq, rfl⟩ := hrr
  have hdst : ∀ p ∈ l, ∀ r, p.1 = .inl r → r ≠ 29 := fun p hp r e => by
    rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
    · rw [h] at e; cases e; decide
    · obtain ⟨i, hi, rfl⟩ := (Sel.mem_resMoves 0 n).1 hq
      rw [← he] at e
      simp only [place, Sel.place] at e
      split at e
      · cases e; exact loc_ne29 hk ‹_›
      · cases e
  split
  · exact List.forall_mem_cons.2 ⟨by simp [Instr.writes], emitW_k29 l hdst⟩
  · exact emitW_k29 l hdst

/-- Running `retR`, with the caller's frame at word `j`, puts the returned words `x0, …` into the
locations `d, …`, a register location by its register and a slot `x` in word `x - c`, as one
parallel move. It keeps `sp` and every other location. -/
theorem run_retR {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) {P : Lin.Prog} {lo N j F : Nat}
    (hfar : farProg P = false → F ≤ 4096) (hFm : F < maxFrame) (n d : Nat) {rr : List Instr}
    (hrr : retR k c P d n = some rr) (t : State)
    (hsp : t.regs.x 31 = Sel.wa lo j) (h16 : t.regs.x 31 % 16 = 0) (hR : Sel.Region t.mem lo N)
    (hd : d + n ≤ F) (hjF : j + Sel.frameW k c F ≤ N) (hn : n ≤ 14)
    (hh : t.world.halted = false) (ha : t.regs.pc % 4 = 0) :
    ∃ t', runA ω rr t = some t' ∧ (∀ x ∈ rr, plain x = true) ∧
      rr.length ≤ resFuel n + (if farProg P then 1 else 0) ∧ t'.world = t.world ∧
      Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧ Sel.Region t'.mem lo N ∧
      (∀ q, q < N → Sel.word t'.mem lo q = if j + d ≤ q + c ∧ q + c < j + d + n ∧ k + c ≤ q + c - j
        then t.regs.x (BitVec.ofNat 5 (q + c - j - d)) else Sel.word t.mem lo q) ∧
      (∀ x, x < k + c → t'.regs.x (loc k x) = if d ≤ x ∧ x < d + n
        then t.regs.x (BitVec.ofNat 5 (x - d)) else t.regs.x (loc k x)) ∧
      t'.regs.x 31 = t.regs.x 31 := by
  have hW : Sel.frameW k c F = min F k + (F - (k + c)) := rfl
  simp only [retR, Option.map_eq_some_iff] at hrr
  obtain ⟨l, hseq, rfl⟩ := hrr
  have hlen := Sel.PMove.seq_length _ hseq
  have hmem : ∀ {p : Place × Place}, p ∈ resMoves k c d n ↔
      ∃ i, i < n ∧ p = (place k c (.slot (d + 0 + i)), .inl (BitVec.ofNat 5 (0 + i))) :=
    Sel.mem_resMoves 0 n
  have hpl : ∀ x, place k c (.slot x) = if x < k + c then .inl (loc k x) else .inr (.slot x) :=
    fun _ => rfl
  have hnd : ((resMoves k c d n).map (·.1)).Nodup := Sel.resMoves_nodup 0 n fun a b _ _ _ _ he => by
    have := Sel.place_slot_inj (fun x y hx hy h => loc_inj hk hx hy h) he; omega
  have ht : ∀ p ∈ resMoves k c d n, p.1 ≠ .inl 16 := fun p hp e => by
    obtain ⟨i, hi, rfl⟩ := hmem.1 hp
    simp only [hpl] at e; split at e
    · exact loc_ne hk ‹_› (r := 16) (by decide) (Sum.inl.inj e)
    · cases e
  have xne : ∀ i r, i < 15 → 15 ≤ r → r < 32 → (BitVec.ofNat 5 i : Reg) ≠ BitVec.ofNat 5 r :=
    fun i r h1 h2 h3 => A64.reg_ne (by omega) h3 (by omega)
  -- the moves after the base, at base `b` with word `j + bs`
  have main : ∀ (b : Reg) (bs : Nat) (t0 : State), (b = 31 ∨ b = 15) →
      (∀ x, k + c ≤ x → d ≤ x → x < d + n → bs + c ≤ x ∧ x - c - bs < 4096 ∧ j + bs + (x - c - bs) < N) →
      t0.regs.x b = Sel.wa lo (j + bs) → (b = 31 → t0.regs.x 31 % 16 = 0) → t0.mem = t.mem →
      (∀ i, i < 15 → t0.regs.x (BitVec.ofNat 5 i) = t.regs.x (BitVec.ofNat 5 i)) →
      (∀ x, x < k + c → t0.regs.x (loc k x) = t.regs.x (loc k x)) → t0.regs.x 31 = t.regs.x 31 →
      t0.world.halted = false → t0.regs.pc % 4 = 0 →
      ∃ t', runA ω (l.flatMap (emitW c b bs)) t0 = some t' ∧ t'.world = t0.world ∧
        Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧ Sel.Region t'.mem lo N ∧
        (∀ q, q < N → Sel.word t'.mem lo q = if j + d ≤ q + c ∧ q + c < j + d + n ∧
          k + c ≤ q + c - j then t.regs.x (BitVec.ofNat 5 (q + c - j - d)) else Sel.word t.mem lo q) ∧
        (∀ x, x < k + c → t'.regs.x (loc k x) = if d ≤ x ∧ x < d + n
          then t.regs.x (BitVec.ofNat 5 (x - d)) else t.regs.x (loc k x)) ∧
        t'.regs.x 31 = t.regs.x 31 := by
    intro b bs t0 hb hfr hbv h16' hm0 hx0 hl0 hsp0 hh0 ha0
    have hb31 : ∀ r : Reg, r = 16 ∨ r.toNat < 15 → r ≠ 31 ∧ r ≠ b := fun r hr => by
      rcases hr with rfl | hr
      · rcases hb with rfl | rfl <;> decide
      · refine ⟨fun e => by subst e; simp at hr, fun e => by
          subst e; rcases hb with h | h <;> rw [h] at hr <;> simp at hr⟩
    have hlocb : ∀ x, x < k + c → loc k x ≠ 31 ∧ loc k x ≠ b := fun x hx =>
      ⟨loc_ne31 hk hx, by rcases hb with rfl | rfl; exact loc_ne31 hk hx; exact loc_ne hk hx (r := 15) (by decide)⟩
    have hok : ∀ p ∈ l, ResOk c N (j + bs) bs b p.1 ∧
        ∃ r, p.2 = .inl r ∧ ResOk c N (j + bs) bs b (.inl r) := fun p hp => by
      constructor
      · rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
        · rw [h]; exact hb31 16 (Or.inl rfl)
        · obtain ⟨i, hi, rfl⟩ := hmem.1 hq; rw [← he]; simp only [hpl]
          split
          · exact hlocb _ ‹_›
          · exact hfr _ (by omega) (by omega) (by omega)
      · rcases Sel.PMove.seq_src _ hseq p hp with h | ⟨q, hq, he⟩
        · exact ⟨16, h, hb31 16 (Or.inl rfl)⟩
        · obtain ⟨i, hi, rfl⟩ := hmem.1 hq
          exact ⟨_, he.symm, hb31 _ (Or.inr (by rw [A64.reg_toNat (by omega)]; omega))⟩
    obtain ⟨t', h1, w1, -, hF1, hl1, hR1, sp1, hq1, hv1⟩ :=
      run_emitW (ω := ω) (N := N) hb l t0 hok hbv h16' (hm0 ▸ hR) hh0 ha0
    have par : ∀ p, ResOk c N (j + bs) bs b p → p ≠ .inl 16 →
        resView c lo (j + bs) bs t' p = Sel.PMove.par (resView c lo (j + bs) bs t0) (resMoves k c d n) p :=
      fun p hp hp16 => by rw [hv1 p hp, Sel.PMove.seq_run _ hnd ht hseq _ _ hp16]
    have into : ∀ x, d ≤ x → x < d + n →
        (place k c (.slot x), (.inl (BitVec.ofNat 5 (x - d)) : Place)) ∈ resMoves k c d n :=
      fun x h1 h2 => hmem.2 ⟨x - d, by omega, by simp [show d + (x - d) = x by omega]⟩
    refine ⟨t', h1, w1, hm0 ▸ hF1, hm0 ▸ hl1, hR1, fun q hq => ?_, fun x hx => ?_, sp1.trans hsp0⟩
    · by_cases hc : j + d ≤ q + c ∧ q + c < j + d + n ∧ k + c ≤ q + c - j
      · rw [if_pos hc]
        obtain ⟨hf1, hf2, hf3⟩ := hfr (q + c - j) hc.2.2 (by omega) (by omega)
        have e := par (.inr (.slot (q + c - j))) ⟨hf1, hf2, hf3⟩ (by simp)
        rw [Sel.PMove.par_of_mem hnd _ (by
          have := into (q + c - j) (by omega) (by omega); rwa [hpl, if_neg (by omega)] at this)] at e
        simp only [resView] at e
        rw [show j + bs + (q + c - j - c - bs) = q by omega, hx0 _ (by omega)] at e
        exact e
      · rw [if_neg hc, hq1 q hq fun x s hs he => ?_, hm0]
        rcases Sel.PMove.seq_dst _ hseq _ hs with h | ⟨p, hp, hpe⟩
        · cases h
        · obtain ⟨i, hi, rfl⟩ := hmem.1 hp
          simp only [hpl] at hpe; split at hpe
          · cases hpe
          · cases hpe
            have := hfr (d + 0 + i) (by omega) (by omega) (by omega)
            exact hc ⟨by omega, by omega, by omega⟩
    · rw [← hl0 x hx]
      have e := par (.inl (loc k x)) (hlocb x hx) (fun h => loc_ne hk hx (r := 16) (by decide)
        (Sum.inl.inj h))
      simp only [resView] at e
      rw [e]
      by_cases hd' : d ≤ x ∧ x < d + n
      · rw [if_pos hd', Sel.PMove.par_of_mem hnd _ (by
          have := into x hd'.1 hd'.2; rwa [hpl, if_pos hx] at this)]
        exact hx0 _ (by omega)
      · rw [if_neg hd', Sel.PMove.par_of_not _ fun s hs => ?_]
        · rfl
        · obtain ⟨i, hi, he⟩ := hmem.1 hs
          simp only [Prod.mk.injEq, hpl] at he
          obtain ⟨he, -⟩ := he
          split at he
          · exact hd' (by have := loc_inj hk hx ‹_› (Sum.inl.inj he); omega)
          · cases he
  have hlenW : ∀ (b : Reg) (bs : Nat) (l' : List (Place × Place)),
      (l'.flatMap (emitW c b bs)).length ≤ l'.length := fun b bs l' => by
    induction l' with
    | nil => simp
    | cons p l' ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have : (emitW c b bs p).length ≤ 1 := by
        rcases p with ⟨d' | o, r | o'⟩ <;> (try rcases o with x | w) <;> simp [emitW]
      omega
  have hpl' : ∀ (b : Reg) (bs : Nat), ∀ x ∈ l.flatMap (emitW c b bs), plain x = true := fun b bs =>
    emitW_plain l fun p hp d' hd' => by
      rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
      · rw [hd'] at h; cases h; decide
      · obtain ⟨i, hi, rfl⟩ := hmem.1 hq
        rw [hd'] at he; simp only [hpl] at he; split at he
        · cases he; exact loc_ne31 hk ‹_›
        · cases he
  split
  · rename_i hf
    have e15 : Sel.wa lo j + UInt64.ofNat (4096 * ((d - c) / 512)) =
        Sel.wa lo (j + 512 * ((d - c) / 512)) := by
      rw [← Sel.wa_add_words]; congr 2; omega
    let t1 := t.goto (t.regs.set 15 (Sel.wa lo j + UInt64.ofNat (4096 * ((d - c) / 512))))
      (t.regs.pc + 4)
    have hx1 : ∀ r : Reg, r ≠ 15 → t1.regs.x r = t.regs.x r := fun r hr => by
      show (t.regs.set 15 _).x r = _; rw [Regs.set_x, ite_eq_right hr]
    obtain ⟨t', h2, w2, hF, hl, hR', hq, hp, hr⟩ := main 15 (512 * ((d - c) / 512)) t1 (Or.inr rfl)
      (fun x h1 h0 h2 => by
        have := Sel.slot_lt_frameW (show x < F by omega) h1; rw [hW] at this hjF
        unfold maxFrame at hFm; refine ⟨by omega, by omega, by omega⟩)
      (by show (t.regs.set 15 _).x 15 = _; simp only [Regs.set_x, ite_true]; exact e15)
      (fun h => absurd h (by decide)) rfl (fun i hi => hx1 _ (xne i 15 hi (by omega) (by omega)))
      (fun x hx => hx1 _ (loc_ne hk hx (r := 15) (by decide))) (hx1 31 (by decide))
      (by simpa [t1] using hh) (by simpa [t1] using A64.aligned_add4 ha)
    refine ⟨t', ?_, List.forall_mem_cons.2 ⟨rfl, hpl' _ _⟩,
      by have := hlenW 15 (512 * ((d - c) / 512)) l; rw [List.length_cons]; omega,
      by simpa [t1] using w2, hF, hl, hR', hq, hp, hr⟩
    rw [runA_cons hh rfl (A64.exec_addImm ha _ _ _ _ _ _ _)]
    simp only [Bool.false_eq_true, ite_false, ite_true, A64.addSub_add]
    rw [hsp, A64.imm_lsl12 ((d - c) / 512) (by unfold maxFrame at hFm; omega)]
    exact h2
  · rename_i hf
    have hF := hfar (by simpa using hf)
    obtain ⟨t', h2, w2, hF', hl, hR', hq, hp, hr⟩ := main 31 0 t (Or.inl rfl)
      (fun x h1 h0 h2 => by
        have := Sel.slot_lt_frameW (show x < F by omega) h1; rw [hW] at this hjF
        refine ⟨by omega, by omega, by omega⟩)
      (by simpa using hsp) (fun _ => h16) rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl hh ha
    exact ⟨t', h2, hpl' _ _, by have := hlenW 31 0 l; omega, w2, hF', hl, hR', hq, hp, hr⟩

end Run

section Match
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {AP : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}
  {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64} {j : Nat} {ω : Oracle}

theorem emit_plain {k c : Nat} : ∀ (l : List (Place × Place)),
    (∀ p ∈ l, ∀ d, p.1 = .inl d → d ≠ 31) → ∀ x ∈ l.flatMap (emit k c), plain x = true
  | [], _ => by simp
  | (p1, p2) :: l, h => by
    rw [List.flatMap_cons]
    refine List.forall_mem_append.2 ⟨?_, emit_plain l fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
    rcases p1 with d | o
    · have hd := h _ List.mem_cons_self d rfl
      rcases p2 with r | o'
      · simp only [emit, List.mem_singleton, forall_eq]; exact A64.mv_plain hd
      · exact ldTo_plain k c hd o'
    · simp [emit]

/-- Running the code of `retLd` puts the returned operands into `x0, x1, …` by one parallel move
and changes no other register but `x16`. -/
theorem run_retLd (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hok : (selector k c mb lvo).fnOk fn = true) (hret : fn.ret.length ≤ 14)
    (hbelow : Lin.OpsBelow fn.ret fn.frame) {rl : List Instr} (hrl : retLd k c fn.ret = some rl) :
    ∃ t', runA ω rl m = some t' ∧ (∀ x ∈ rl, plain x = true) ∧ t'.mem = m.mem ∧
      t'.world = m.world ∧ t'.regs.pc % 4 = 0 ∧ t'.regs.x 31 = m.regs.x 31 ∧
      (∀ i, i < fn.ret.length →
        t'.regs.x (BitVec.ofNat 5 i) = (fn.ret.map (Operand.eval s.frame)).getD i 0) ∧
      ∀ r : Reg, r ≠ 31 → r ≠ 16 → fn.ret.length ≤ r.toNat → t'.regs.x r = m.regs.x r := by
  simp only [retLd, Option.map_eq_some_iff] at hrl
  obtain ⟨l, hseq, rfl⟩ := hrl
  have hO := selOps_laws (lvo := lvo) (mb := mb) hk
  have hE := selOps_ext (lvo := lvo) (mb := mb) hk
  have hmem : ∀ {p : Place × Place}, p ∈ retMoves k c fn.ret ↔
      ∃ i, i < fn.ret.length ∧ p = (.inl (BitVec.ofNat 5 (0 + i)), place k c (fn.ret[i]?.getD (.imm 0))) :=
    Sel.mem_retMoves 0 fn.ret
  have hx : ∀ i, i < 15 → (BitVec.ofNat 5 i : Reg).toNat = i := fun i hi => A64.reg_toNat (by omega)
  have hget : ∀ i, i < fn.ret.length → Lin.OpsBelow [fn.ret[i]?.getD (.imm 0)] fn.frame :=
    fun i hi y hy => hbelow y (by
      simp only [List.mem_singleton] at hy
      rw [hy, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
  have hms : ∀ p ∈ retMoves k c fn.ret, (selOps k c mb).EmitOk ((conv k c mb).k + (conv k c mb).c) fn.frame p :=
    fun p hp => by
      obtain ⟨i, hi, rfl⟩ := hmem.1 hp
      exact ⟨⟨_, rfl, A64.reg_ne (k' := 31) (by omega) (by omega) (by omega),
          A64.reg_ne (k' := 29) (by omega) (by omega) (by omega)⟩,
        Sel.Ops.emitOk_place (O := selOps k c mb) (hget i hi)⟩
  have hnd : ((retMoves k c fn.ret).map (·.1)).Nodup := Sel.retMoves_nodup _ 0 fn.ret
    fun a b _ ha _ hb he => by
      have := congrArg BitVec.toNat he; rw [hx a (by omega), hx b (by omega)] at this; exact this
  have ht : ∀ p ∈ retMoves k c fn.ret, p.1 ≠ .inl 16 := fun p hp e => by
    obtain ⟨i, hi, rfl⟩ := hmem.1 hp
    exact A64.reg_ne (k' := 16) (by omega) (by omega) (by omega) (Sum.inl.inj e)
  obtain ⟨hl, t', h1, hm1, hw1, hsp1, hOk1, hv1⟩ := hE.run_seq hO hM hok (tmp := (16 : Reg))
    (show (16 : Reg) ≠ 31 ∧ (16 : Reg) ≠ 29 by decide) hseq hms hnd ht rfl rfl hM.halted (hO.ok_match hM)
  have hv : ∀ r : Reg, r ≠ 31 → r ≠ 16 → t'.regs.x r =
      Sel.PMove.par ((selOps k c mb).view s.frame m.regs) (retMoves k c fn.ret) (.inl r) :=
    fun r h31 h16 => by
      have := hv1 r h16; simp only [selOps] at this
      rwa [show t'.regs.getZ r = t'.regs.x r by simp [Regs.getZ, show ¬ r = 31#5 from h31]] at this
  rw [emit_eq] at h1
  refine ⟨t', h1, emit_plain l fun p hp d hd => ?_, hm1, hw1, hOk1, hsp1, fun i hi => ?_,
    fun r h31 h16 hr => ?_⟩
  · rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
    · rw [hd] at h; cases h; decide
    · obtain ⟨i, hi, rfl⟩ := hmem.1 hq; rw [hd] at he; cases he
      exact A64.reg_ne (k' := 31) (by omega) (by omega) (by omega)
  · rw [hv _ (A64.reg_ne (k' := 31) (by omega) (by omega) (by omega))
      (A64.reg_ne (k' := 16) (by omega) (by omega) (by omega))]
    have hm := hmem.2 ⟨i, hi, rfl⟩
    rw [Nat.zero_add] at hm
    refine (Sel.PMove.par_of_mem hnd _ hm).trans ?_
    refine (hO.view_place hM (hget i hi) ((Sel.Ops.Keeps.refl _).op _)).trans ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rw [hv r h31 h16]
    refine (Sel.PMove.par_of_not _ fun s' hs => ?_).trans ?_
    · obtain ⟨i, hi, he⟩ := hmem.1 hs
      have := congrArg BitVec.toNat (Sum.inl.inj (Prod.mk.inj he).1)
      rw [Nat.zero_add, hx i (by omega)] at this; omega
    · simp [Sel.Ops.view, selOps, Regs.getZ, show ¬ r = 31#5 from h31]

theorem ldWords_plain (b : Reg) : ∀ (o r n : Nat), r + n ≤ 31 → ∀ x ∈ ldWords b o r n, plain x = true
  | _, _, 0, _ => by simp [ldWords]
  | o, r, n + 1, h => by
    simp only [ldWords, List.forall_mem_cons]
    have hr : ¬ (BitVec.ofNat 5 r : Reg) = 31#5 := A64.reg_ne (k' := 31) (by omega) (by omega) (by omega)
    have hr' : ¬ (31#5 : Reg) = BitVec.ofNat 5 r := fun e => hr e.symm
    exact ⟨by simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, A64.zw, hr, hr'],
      ldWords_plain b (o + 1) (r + 1) n (by omega)⟩

theorem emit_k29 {k c : Nat} : ∀ (l : List (Place × Place)),
    (∀ p ∈ l, ∀ d, p.1 = .inl d → d ≠ 29) → ∀ x ∈ l.flatMap (emit k c), (29 : Reg) ∉ x.writes
  | [], _ => by simp
  | (p1, p2) :: l, h => by
    rw [List.flatMap_cons]
    refine List.forall_mem_append.2 ⟨?_, emit_k29 l fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
    rcases p1 with d | o
    · have hd := h _ List.mem_cons_self d rfl
      rcases p2 with r | o'
      · simp only [emit, List.mem_singleton, forall_eq]; exact A64.mv_k29 hd
      · exact ldTo_k29 k c hd o'
    · simp [emit]

/-- No instruction of `retLd` writes `x29`: its moves write `x0 … x13` and `x16`. -/
theorem retLd_k29 {k c : Nat} {os : List Operand} {rl : List Instr} (hret : os.length ≤ 14)
    (hrl : retLd k c os = some rl) : ∀ x ∈ rl, (29 : Reg) ∉ x.writes := by
  simp only [retLd, Option.map_eq_some_iff] at hrl
  obtain ⟨l, hseq, rfl⟩ := hrl
  refine emit_k29 l fun p hp r e => ?_
  rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
  · rw [h] at e; cases e; decide
  · obtain ⟨i, hi, rfl⟩ := (Sel.mem_retMoves 0 os).1 hq
    rw [← he] at e; cases e
    exact A64.reg_ne (k' := 29) (by omega) (by omega) (by omega)

theorem ldWords_k29 (b : Reg) : ∀ (o r n : Nat), r + n ≤ 29 → ∀ x ∈ ldWords b o r n, (29 : Reg) ∉ x.writes
  | _, _, 0, _ => by simp [ldWords]
  | o, r, n + 1, h => by
    simp only [ldWords, List.forall_mem_cons]
    exact ⟨A64.zw_k29 (A64.reg_ne (k' := 29) (by omega) (by omega) (by omega)),
      ldWords_k29 b (o + 1) (r + 1) n (by omega)⟩

/-- The callee's return block, run from a related state, leaves the returned words in `x0, …`,
`sp` at the caller's frame word `j + fw F` and `pc` at the return address, with memory and world
unchanged. Each location register holds the caller's view of it, which is restored from the save
word below `min k F` and kept above. -/
theorem run_retBlock (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hok : (selector k c mb lvo).fnOk fn = true) (hsm : fn.frame < maxFrame)
    (hret : fn.ret.length ≤ 14) (hbelow : Lin.OpsBelow fn.ret fn.frame) {rl : List Instr}
    (hrl : retLd k c fn.ret = some rl) {W : Nat} (hW : Sel.frameW k c fn.frame = W)
    {code : List UInt8} (hen : Asm.encodeAll isa (rl ++
      ldWords 31 0 19 (min k fn.frame) ++ ldIs 30 (.slot W) ++ [frameI false 31 31 W, .ret 30]) =
      some code)
    (hcode : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) code) (cy : Nat) :
    ∃ t : State, Sel.Leg (A := arch) linux ω (Sel.SpBound (conv k c mb) P lo N) m cy
        ((rl ++ ldWords 31 0 19 (min k fn.frame) ++ ldIs 30 (.slot W)).length +
          (1 + 1)) t ∧
      t.regs.pc = Sel.word m.mem lo (j + W) ∧ t.regs.x 31 = Sel.wa lo (j + fw W) ∧
      t.mem = m.mem ∧ t.world = m.world ∧ (∀ i, i < fn.ret.length →
        t.regs.x (BitVec.ofNat 5 i) = (fn.ret.map (Operand.eval s.frame)).getD i 0) ∧
      (∀ x, x < k → t.regs.x (preg x) =
        Sel.callerView lo k m.mem j fn.frame (fun y => m.regs.x (preg y)) x) ∧
      t.regs.x 29 = m.regs.x 29 := by
  have hroom := room_fw hM
  rw [hW] at hroom
  have hfwF := A64.fw_gt W
  have hWF : W = min fn.frame k + (fn.frame - (k + c)) := by rw [← hW]; rfl
  have hsp0 : m.regs.x 31 = Sel.wa lo j := hM.sp
  have hrip : m.regs.pc = _ := hM.rip
  obtain ⟨c₁, c₂, rfl, he₁, he₂⟩ := Sel.encodeAll_append _ _ _ hen
  obtain ⟨hc₁, hc₂⟩ := Sel.codeAt_append _ _ _ _ (hrip ▸ hcode)
  obtain ⟨t1, r1, hpl1, hm1, hw1, ha1, hs1, hv1, hk1⟩ := run_retLd (ω := ω) hM hk hok hret hbelow hrl
  have hsp1 : t1.regs.x 31 = Sel.wa lo j := hs1.trans hsp0
  have h16 : t1.regs.x 31 % 16 = 0 := hsp1 ▸ hsp0 ▸ sp16 hM
  obtain ⟨t2, r2, hm2, hw2, ha2, hv2, hk2⟩ := run_ldWords (ω := ω) (b := 31) (i := j) (N := N)
    (min k fn.frame) 0 19 t1 hsp1 (fun _ => h16) (hm1 ▸ hM.region) (by omega) (by omega) (by omega)
    (Or.inr (by simp; omega)) (by rw [hw1]; exact hM.halted) ha1
  have hsp2 : t2.regs.x 31 = Sel.wa lo j := (hk2 31 (Or.inr (by simp; omega))).trans hsp1
  have x3 := A64.run_ldSlot (ω := ω) (d := 30) (y := W) (j := j) (N := N) (lo := lo) (t := t2)
    (by decide) (by rw [hw2, hw1]; exact hM.halted) ha2 hsp2 (hsp2 ▸ hsp1 ▸ h16)
    (by unfold maxFrame at hsm; omega) (hm2 ▸ hm1 ▸ hM.region) (by omega)
  generalize ht3 : t2.goto (t2.regs.set 30 (Sel.word t2.mem lo (j + W)))
    (t2.regs.pc + UInt64.ofNat (4 * (ldIs 30 (.slot W)).length)) = t3 at x3
  have hrun : runA ω (rl ++ ldWords 31 0 19 (min k fn.frame) ++
      ldIs 30 (.slot W)) m = some t3 := by
    rw [runA_append, runA_append, r1, Option.bind_some, r2, Option.bind_some, x3]
  obtain ⟨hrunA, -, -, hpcA, hallA⟩ := Sel.run_straight (A := arch) (abi := linux) A64.laws cy hM.wx
    he₁ hc₁ (straight_all (ω := ω) (List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨hpl1, ldWords_plain 31 0 19 _ (by omega)⟩,
      A64.ldIs_plain (by decide) _⟩)) hrun
  have h29 : t3.regs.x 29 = m.regs.x 29 := A64.runA_k29 (List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨hpl1, ldWords_plain 31 0 19 _ (by omega)⟩,
      A64.ldIs_plain (by decide) _⟩) (List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨retLd_k29 hret hrl, ldWords_k29 31 0 19 _ (by have := Nat.min_le_left k fn.frame; omega)⟩,
      A64.ldIs_k29 (by decide) _⟩) hrun
  have hm3 : t3.mem = m.mem := by rw [← ht3, A64.goto_mem, hm2, hm1]
  have hw3 : t3.world = m.world := by rw [← ht3, A64.goto_world, hw2, hw1]
  have hsp3 : t3.regs.x 31 = Sel.wa lo j := by
    rw [← ht3]; simp only [A64.goto_regs, Regs.set_x]; rw [ite_eq_right (by decide)]; exact hsp2
  have hpc3 : t3.regs.pc = m.regs.pc + UInt64.ofNat c₁.length := hpcA
  have ha3 : t3.regs.pc % 4 = 0 := by
    rw [hpc3, A64.encodeAll_length he₁]; exact A64.aligned_add (pc4 hM) (Nat.mul_mod_right 4 _)
  have sb : ∀ x : State, ∀ i, j ≤ i → i ≤ N → x.regs.x 31 = Sel.wa lo i →
      Sel.SpBound (conv k c mb) P lo N x := fun x i h1 h2 h3 => Sel.spBound_of_match hM h1 h2 h3
  refine ⟨_, (Sel.Leg.mono (fun x h => Sel.spBound_of_keep hM h) ⟨hrunA, hallA⟩).trans
      (A64.run_popRet (F := W) (by unfold maxFrame at hsm ⊢; omega) hsp3 (by rw [hw3]; exact hM.halted) ha3 he₂
        (by rw [hm3, hpc3]; exact hc₂) (sb _ j (Nat.le_refl _) (by omega) hsp3)
        fun x h => sb x _ (Nat.le_add_right _ _) hroom h),
    by simp [← ht3, hm2, hm1], by simp, by simp [hm3], by simp [hw3], fun i hi => ?_, fun x hx => ?_,
    by simpa using h29⟩
  · have h30 : BitVec.ofNat 5 i ≠ 30 := A64.reg_ne (k' := 30) (by omega) (by omega) (by omega)
    have h31 : BitVec.ofNat 5 i ≠ 31 := A64.reg_ne (k' := 31) (by omega) (by omega) (by omega)
    simp only [← ht3, A64.goto_regs, Regs.set_x]; rw [ite_eq_right h31, ite_eq_right h30]
    rw [hk2 _ (Or.inl (by rw [A64.reg_toNat (by omega)]; omega))]
    simpa using hv1 i hi
  · have hx10 : x < 10 := by omega
    simp only [← ht3, A64.goto_regs, Regs.set_x]
    rw [ite_eq_right (preg_ne31 hx10), ite_eq_right (preg_ne hx10 (by decide))]
    simp only [Sel.callerView]
    split
    · rw [preg_eq, hv2 x (by omega), hm1]; rfl
    · rw [hk2 _ (by rw [preg_toNat hx10]; omega), hk1 _ (preg_ne31 hx10)
        (preg_ne hx10 (by decide)) (by rw [preg_toNat hx10]; omega)]

theorem src16_ne15 {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (o : Operand) : (src k c 16 o).2 ≠ 15 := by
  cases o with
  | imm w => show (16 : Reg) ≠ 15; decide
  | slot y =>
    simp only [src]; split
    · rename_i h; exact loc_ne hk h (by decide)
    · show (16 : Reg) ≠ 15; decide

/-- Running the code of `srcZ k c o` leaves the value of `o` in its register and changes only `x16`. -/
theorem run_srcZ (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {t : State} (hF : Fetch k c lo N j m t) {o : Operand}
    (ho : Lin.OpsBelow [o] fn.frame) :
    ∃ t', runA ω (srcZ k c o).1 t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.x 31 = t.regs.x 31 ∧ t'.regs.pc % 4 = 0 ∧
      t'.regs.getZ (srcZ k c o).2 = o.eval s.frame ∧ (srcZ k c o).2 ≠ 15 ∧
      ∀ r', r' ≠ 16 → t'.regs.getZ r' = t.regs.getZ r' := by
  unfold srcZ
  split
  · exact ⟨t, rfl, rfl, rfl, rfl, hF.pc, by simp [Operand.eval], by decide, fun _ _ => rfl⟩
  · obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := run_src (ω := ω) hM hk hsm hF.toWords (r := 16) (by decide) ho
      (fun y _ hy => hF.regs y hy)
    exact ⟨t', h1, h2, h3, h4, h5, h6, src16_ne15 hk _, h7⟩

/-- Running `argMems k c ent l os`, while the caller's location registers are still in place,
stores the memory arguments for the callee slots `l, …` that `ent` names into their words
`j' + l - c, …` of the callee frame at `x17`. It keeps the words from `j` on, `sp`, `x17` and the location registers. -/
theorem run_argMems (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {j' G : Nat} (hG : G < maxFrame) (hjg : j' + G ≤ j)
    (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), Fetch k c lo N j m t →
    t.regs.x 17 = Sel.wa lo j' → Lin.OpsBelow os fn.frame → l + os.length ≤ G + c →
    (os = [] ∨ k + c ≤ l) →
    ∃ t', runA ω (argMems k c ent l os) t = some t' ∧ Fetch k c lo N j m t' ∧ t'.world = t.world ∧
      t'.regs.x 17 = t.regs.x 17 ∧ Memory.Frame t.mem t'.mem ∧ Sel.LowSame lo t.mem t'.mem ∧
      ∀ q, q < N → Sel.word t'.mem lo q =
        if j' + l ≤ q + c ∧ q + c < j' + l + os.length ∧ ent (q + c - j') = true
        then (os.map (Operand.eval s.frame)).getD (q + c - j' - l) 0 else Sel.word t.mem lo q
  | [], _, t, hF, _, _, _, _ => ⟨t, rfl, hF, rfl, rfl, Memory.Frame.refl _, Sel.LowSame.refl _ _,
      fun q _ => by rw [ite_eq_right fun h => by simp at h; omega]⟩
  | o :: os, l, t, hF, h17, ho, hl, hl0 => by
    simp only [List.length_cons] at hl
    have hkl : k + c ≤ l := hl0.resolve_left (by simp)
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have hshift : ∀ q, j' + (l + 1) ≤ q + c ∧ q + c < j' + (l + 1) + os.length ∧
        ent (q + c - j') = true →
        (os.map (Operand.eval s.frame)).getD (q + c - j' - (l + 1)) 0 =
          ((o :: os).map (Operand.eval s.frame)).getD (q + c - j' - l) 0 := fun q hq => by
      rw [show q + c - j' - l = (q + c - j' - (l + 1)) + 1 by omega]; simp
    cases he : ent l
    · obtain ⟨t', r3, hF3, w3, x3, hF3', hl3, hq3⟩ := run_argMems hM hk hsm hG hjg ent os (l + 1) t
        hF h17 ho' (by omega) (Or.inr (by omega))
      refine ⟨t', by simpa [argMems, he] using r3, hF3, w3, x3, hF3', hl3, fun q hq => ?_⟩
      rw [hq3 q hq]
      by_cases h2 : q + c = j' + l
      · rw [ite_eq_right (by omega), ite_eq_right (by rw [h2, show j' + l - j' = l by omega]; simp [he])]
      · by_cases hc : j' + (l + 1) ≤ q + c ∧ q + c < j' + (l + 1) + os.length ∧
            ent (q + c - j') = true
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by simp <;> omega, hc.2.2⟩, hshift q hc]
        · rw [ite_eq_right hc, ite_eq_right fun h => hc ⟨by omega, by simp at h; omega, h.2.2⟩]
    have hroom := room_fw hM
    have := A64.fw_gt (Sel.frameW k c fn.frame)
    obtain ⟨t1, r1, m1, w1, sp1, a1, v1, n15, k1⟩ := run_srcZ (ω := ω) hM hk hsm hF (o := o)
      (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy))
    have h17' : t1.regs.x 17 = t.regs.x 17 := by
      have := k1 17 (by decide); simpa using this
    obtain ⟨mem1, hw1, hR1, hF1, hv1, hr1⟩ := Sel.writeWord_wa (m1 ▸ hF.region)
      (show j' + (l - c) < N by omega) (o.eval s.frame)
    obtain ⟨t2, x2, hm2, hw2, hpc2, hx2⟩ := A64.run_stW (ω := ω) (r := (srcZ k c o).2) (b := 17)
      (x := l - c) (i := j') (lo := lo) (mem' := mem1) (t := t1) n15 (by decide)
      (by rw [w1]; exact hF.halted) a1 (h17'.trans h17) (fun h => absurd h (by decide))
      (by unfold maxFrame at hG; omega) (by rw [v1]; exact hw1)
    have ha2 : t2.regs.pc % 4 = 0 := by
      rw [hpc2]; exact A64.aligned_add a1 (Nat.mul_mod_right 4 _)
    have hF2 : Fetch k c lo N j m t2 :=
      ⟨⟨hm2 ▸ hR1, fun i h1 h2 => by
          rw [hm2, hr1 i h2 (by omega), m1]; exact hF.words i h1 h2,
        (hx2 31 (by decide)).trans (sp1.trans hF.sp), by rw [hw2, w1]; exact hF.halted, ha2⟩,
        fun x hx => by
          rw [A64.getZ_ne (loc_ne31 hk hx), hx2 _ (loc_ne (r := 15) hk hx (by decide)),
            ← A64.getZ_ne (loc_ne31 hk hx), k1 _ (loc_ne (r := 16) hk hx (by decide))]
          exact hF.regs x hx⟩
    obtain ⟨t', r3, hF3, w3, x3, hF3', hl3, hq3⟩ := run_argMems hM hk hsm hG hjg ent os (l + 1) t2
      hF2 (by rw [hx2 _ (by decide), h17']; exact h17) ho' (by omega) (Or.inr (by omega))
    refine ⟨t', ?_, hF3, by rw [w3, hw2, w1], by rw [x3, hx2 _ (by decide), h17'],
      m1 ▸ hF1.trans (hm2 ▸ hF3'), m1 ▸ (Sel.writeWord_wa_low (m1 ▸ hF.region) (by omega) hw1).trans (hm2 ▸ hl3),
      fun q hq => ?_⟩
    · rw [show argMems k c ent l (o :: os) = (srcZ k c o).1 ++ ((farPre 15 17 (l - c) ++
          [.str .x (srcZ k c o).2 (farA 15 17 (l - c))]) ++ argMems k c ent (l + 1) os) by
          simp [argMems, argMem, he],
        runA_append, r1, Option.bind_some, runA_append, x2, Option.bind_some, r3]
    · rw [hq3 q hq, hm2]
      by_cases hc : j' + (l + 1) ≤ q + c ∧ q + c < j' + (l + 1) + os.length ∧
          ent (q + c - j') = true
      · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by simp <;> omega, hc.2.2⟩, hshift q hc]
      · rw [ite_eq_right hc]
        by_cases h2 : q = j' + (l - c)
        · subst h2
          rw [hv1, ite_eq_left ⟨by omega, by simp <;> omega,
            by rw [show j' + (l - c) + c - j' = l by omega]; simpa using he⟩,
            show j' + (l - c) + c - j' - l = 0 by omega]; simp
        · rw [hr1 q hq h2, m1, ite_eq_right fun h => hc ⟨by omega, by simp at h; omega, h.2.2⟩]

/-- What loading the register arguments needs of a state `t` of the call block, where `m` is the
related state at the call and the callee frame is at word `j'`. The memory `mem` holds in its
words `j' + y` with `y < g` the saved location registers of `m` and from word `j` on the words of
`m`, and the preserved location registers from `l` on still hold the values of `m`. -/
structure ArgSt (k lo N j j' g l : Nat) (keep : Nat → Bool) (m : State) (mem : Memory) (t : State) :
    Prop where
  hmem : t.mem = mem
  region : Sel.Region mem lo N
  sp : t.regs.x 31 = m.regs.x 31
  x17 : t.regs.x 17 = Sel.wa lo j'
  halted : t.world.halted = false
  pc : t.regs.pc % 4 = 0
  saves : ∀ y, y < g → keep y = true → Sel.word mem lo (j' + y) = m.regs.x (preg y)
  slots : ∀ i, j ≤ i → i < N → Sel.word mem lo i = Sel.word m.mem lo i
  regs : ∀ x, x < k → l ≤ x → t.regs.x (preg x) = m.regs.x (preg x)

/-- Running `argReg k c n jd o` loads the operand into the register of location `jd`, which is
the next preserved location `n` or a caller-saved one, reading it from the caller's slot, from a
register not yet overwritten, or from the save word of a preserved one that was. -/
theorem run_argReg (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {j' g n jd : Nat} {keep : Nat → Bool} {mem : Memory} {t : State}
    (hS : ArgSt k lo N j j' g n keep m mem t) (hn : n ≤ g) (hjg : j' + g ≤ N)
    (hjd : jd < k + c) (hjn : jd < k → jd = n ∧ n < g)
    {o : Operand} (ho : Lin.OpsBelow [o] fn.frame) (hko : ∀ y, o = .slot y → keep y = true)
    (hC : ∀ y, o = .slot y → k ≤ y → y < k + c → t.regs.x (loc k y) = m.regs.x (loc k y)) :
    ∃ t', runA ω (argReg k c n jd o) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧ t'.regs.x (loc k jd) = o.eval s.frame ∧
      ∀ r, r ≠ loc k jd → t'.regs.x r = t.regs.x r := by
  have hd := loc_ne31 hk hjd
  have hd' : ¬ loc k jd = 31#5 := hd
  cases o with
  | imm w =>
    obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := A64.run_imm (ω := ω) hd w hS.halted hS.pc
    exact ⟨t', h1, h2, h3, h4, h5, h6⟩
  | slot y =>
    have hy : y < fn.frame := ho y List.mem_cons_self
    have hv := loc_val hM hy
    have hroom := room_fw hM
    have := A64.fw_gt (Sel.frameW k c fn.frame)
    have hWF : Sel.frameW k c fn.frame = min fn.frame k + (fn.frame - (k + c)) := rfl
    have hmv : ∀ r : Reg, r ≠ 31 → t.regs.x r = s.frame y →
        ∃ t', runA ω [mv (loc k jd) r] t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
          t'.regs.pc % 4 = 0 ∧ t'.regs.x (loc k jd) = s.frame y ∧
          ∀ r', r' ≠ loc k jd → t'.regs.x r' = t.regs.x r' := fun r hr hrv => by
      obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := A64.ops_run_mv (ω := ω) (d := loc k jd) (r := r)
        hd hS.halted hS.pc
      refine ⟨t', h1, h2, h3, h5, ?_, fun r' hr' => ?_⟩
      · rw [A64.getZ_ne hd, A64.getZ_ne hr] at h6; rw [h6, hrv]
      · by_cases h : r' = 31#5
        · subst h; exact h4
        · have := h7 r' hr'; simpa [h] using this
    by_cases hyk : y < k
    · rw [ite_eq_left (by omega), loc_of_lt hyk] at hv
      by_cases hyl : y < n
      · have x1 := A64.exec_ldr_x (trap := linux.trap ω) (n := 4) (d := loc k jd) hS.pc
          (A64.uimm_aligned (b := 17) (BitVec.ofNat 12 y) (fun h => absurd h (by decide)))
          (by rw [A64.ea_uimm hS.x17 (by omega), hS.hmem]
              exact Sel.readWord_wa hS.region (show j' + y < N by omega))
        refine ⟨t.goto (t.regs.setZ (loc k jd) (Sel.word mem lo (j' + y))) (t.regs.pc + 4),
          by rw [argReg, ite_eq_left hyk, ite_eq_left hyl, runA_cons hS.halted rfl x1]; rfl,
          rfl, rfl, by simpa using A64.aligned_add4 hS.pc, ?_, fun r hr => by simp [hd', hr]⟩
        simp [hd']; rw [hS.saves y (by omega) (hko y rfl), hv]
      · by_cases hyl' : y = jd
        · subst hyl'
          exact ⟨t, by simp [argReg, hyk, hyl], rfl, rfl,
            hS.pc, by rw [loc_of_lt hyk, hS.regs y hyk (by omega), hv]; rfl, fun _ _ => rfl⟩
        · obtain ⟨t', h1, h⟩ := hmv (preg y) (preg_ne31 (by omega))
            (by rw [hS.regs y hyk (by omega), hv])
          exact ⟨t', by rw [argReg, ite_eq_left hyk, ite_eq_right hyl, ite_eq_right hyl']; exact h1, h⟩
    · by_cases hyc : y < k + c
      · rw [ite_eq_left hyc] at hv
        obtain ⟨t', h1, h⟩ := hmv (loc k y) (loc_ne31 hk hyc)
          (by rw [hC y rfl (by omega) hyc, hv])
        exact ⟨t', by rw [argReg, ite_eq_right hyk, ite_eq_left hyc]; exact h1, h⟩
      rw [ite_eq_right hyc] at hv
      have e := A64.run_ldSlot (ω := ω) (d := loc k jd) (y := y - c) (j := j) (N := N) (lo := lo)
        (t := t) hd hS.halted hS.pc (hS.sp.trans hM.sp) (hS.sp ▸ sp16 hM)
        (by unfold maxFrame at hsm; omega) (hS.hmem ▸ hS.region) (by omega)
      refine ⟨t.goto (t.regs.set (loc k jd) (Sel.word t.mem lo (j + (y - c))))
        (t.regs.pc + UInt64.ofNat (4 * (ldIs (loc k jd) (Operand.slot (y - c))).length)),
        by rw [argReg, ite_eq_right hyk, ite_eq_right hyc]; exact e, rfl, rfl,
        by simpa using A64.aligned_add hS.pc (Nat.mul_mod_right 4 _), ?_, fun r hr => by simp [hr]⟩
      simp only [A64.goto_regs, Regs.set_x, ite_true]
      rw [hS.hmem, hS.slots _ (by omega) (by omega), show j + (y - c) = j + y - c by omega, hv]; rfl

/-- Running `argRegs k c ent l os` loads operand `i` into `x(19+l+i)` when `ent` names `l + i`.
It writes no memory and keeps the other location registers and every register outside the
preserved locations. -/
theorem run_argRegs (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {j' g : Nat} {keep : Nat → Bool} {mem : Memory} (hg : g ≤ k)
    (hjg : j' + g ≤ N) (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), ArgSt k lo N j j' g l keep m mem t →
    Lin.OpsBelow os fn.frame → l + os.length ≤ g → (∀ y, Operand.slot y ∈ os → keep y = true) →
    (∀ y, k ≤ y → y < k + c → t.regs.x (loc k y) = m.regs.x (loc k y)) →
    ∃ t', runA ω (argRegs k c ent l os) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧
      (∀ i, i < os.length → ent (l + i) = true →
        t'.regs.x (preg (l + i)) = (os.map (Operand.eval s.frame)).getD i 0) ∧
      (∀ x, x < 10 → (x < l ∨ l + os.length ≤ x ∨ ent x = false) →
        t'.regs.x (preg x) = t.regs.x (preg x)) ∧
      ∀ r : Reg, (∀ x, x < 10 → preg x ≠ r) → t'.regs.x r = t.regs.x r
  | [], _, t, hS, _, _, _, _ => ⟨t, rfl, rfl, rfl, hS.pc, fun _ h => absurd h (by simp),
      fun _ _ _ => rfl, fun _ _ => rfl⟩
  | o :: os, l, t, hS, ho, hl, hko, hC => by
    simp only [List.length_cons] at hl
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have hko' : ∀ y, Operand.slot y ∈ os → keep y = true := fun y hy => hko y (List.mem_cons_of_mem _ hy)
    cases he : ent l
    · obtain ⟨t', r2, m2, w2, a2, v2, k2, o2⟩ := run_argRegs hM hk hsm hg hjg ent os (l + 1) t
        ⟨hS.hmem, hS.region, hS.sp, hS.x17, hS.halted, hS.pc, hS.saves, hS.slots,
          fun x hx hlx => hS.regs x hx (by omega)⟩ ho' (by omega) hko' hC
      refine ⟨t', by simpa [argRegs, he] using r2, m2, w2, a2, fun i hi hei => ?_,
        fun x hx hlx => k2 x hx ?_, o2⟩
      · cases i with
        | zero => simp [he] at hei
        | succ i =>
          rw [show l + (i + 1) = l + 1 + i by omega] at hei ⊢
          rw [v2 i (by simpa using hi) hei]; simp
      · by_cases hxl : x = l
        · subst hxl; exact Or.inr (Or.inr he)
        · simp only [List.length_cons] at hlx
          rcases hlx with h | h | h
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inr h)
    obtain ⟨t1, r1, m1, w1, a1, v1, k1⟩ := run_argReg (ω := ω) hM hk hsm hS (by omega) hjg
      (jd := l) (by omega) (fun _ => ⟨rfl, by omega⟩)
      (o := o) (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy))
      (fun y hy => hko y (hy ▸ List.mem_cons_self)) (fun y _ h1 h2 => hC y h1 h2)
    rw [loc_of_lt (by omega)] at v1 k1
    have hS1 : ArgSt k lo N j j' g (l + 1) keep m mem t1 :=
      ⟨m1.trans hS.hmem, hS.region,
        (k1 31 (preg_ne (by omega) (by decide)).symm).trans hS.sp,
        (k1 17 (preg_ne (by omega) (by decide)).symm).trans hS.x17, by rw [w1]; exact hS.halted, a1,
        hS.saves, hS.slots, fun x hx hlx => by
          rw [k1 _ (fun e => by have := preg_inj (by omega) (by omega) e; omega)]
          exact hS.regs x hx (by omega)⟩
    obtain ⟨t', r2, m2, w2, a2, v2, k2, o2⟩ := run_argRegs hM hk hsm hg hjg ent os (l + 1) t1 hS1
      ho' (by omega) hko' (fun y h1 h2 => by
        rw [k1 _ (fun e => preg_ne_loc hk (by omega) h1 h2 e.symm)]; exact hC y h1 h2)
    refine ⟨t', by simp only [argRegs, he, ite_true]; rw [runA_append, r1, Option.bind_some, r2],
      m2.trans m1, w2.trans w1, a2, fun i hi hei => ?_, fun x hx hlx => ?_, fun r hr => ?_⟩
    · cases i with
      | zero => rw [k2 _ (by omega) (by omega)]; simpa using v1
      | succ i =>
        rw [show l + (i + 1) = l + 1 + i by omega] at hei ⊢
        rw [v2 i (by simpa using hi) hei]; simp
    · simp only [List.length_cons] at hlx
      have hxl : x ≠ l := fun h => by
        subst h; rcases hlx with h | h | h
        · omega
        · omega
        · simp [he] at h
      rw [k2 x hx (by
          rcases hlx with h | h | h
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inr h)),
        k1 _ (fun e => hxl (preg_inj (by omega) (by omega) e))]
    · rw [o2 r hr, k1 r (fun e => hr l (by omega) e.symm)]

theorem argMems_plain (k c : Nat) (ent : Nat → Bool) :
    ∀ (l : Nat) (os : List Operand), ∀ x ∈ argMems k c ent l os, plain x = true
  | _, [] => by simp [argMems]
  | l, o :: os => by
    simp only [argMems, argMem]
    refine List.forall_mem_append.2 ⟨?_, argMems_plain k c ent (l + 1) os⟩
    split
    rotate_left
    · simp
    refine List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨?_, A64.farPre_plain (by decide) 17 (l - c)⟩, by simp only [List.mem_singleton, forall_eq]; rfl⟩
    unfold srcZ; split
    · simp
    · exact src_plain k c (by decide) _

theorem argReg_plain {k c n jd : Nat} (hd : loc k jd ≠ 31) (o : Operand) :
    ∀ x ∈ argReg k c n jd o, plain x = true := by
  cases o with
  | imm w => exact A64.immIs_plain hd w
  | slot y =>
    have hd' : ¬ loc k jd = 31#5 := hd
    have hd'' : ¬ (31#5 : Reg) = loc k jd := fun e => hd' e.symm
    simp only [argReg]; split
    · split
      · simp [plain, Instr.valid, Instr.branches, Instr.isTrap, Instr.writes, A64.zw, hd', hd'']
      · split
        · simp
        · simp only [List.mem_singleton, forall_eq]; exact A64.mv_plain hd
    · split
      · simp only [List.mem_singleton, forall_eq]; exact A64.mv_plain hd
      · exact A64.ldIs_plain hd (.slot (y - c))

theorem argRegs_plain {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (ent : Nat → Bool) :
    ∀ (l : Nat) (os : List Operand), l + os.length ≤ k + c → ∀ x ∈ argRegs k c ent l os, plain x = true
  | _, [], _ => by simp [argRegs]
  | l, o :: os, h => by
    simp only [List.length_cons] at h
    simp only [argRegs]
    refine List.forall_mem_append.2 ⟨?_, argRegs_plain hk ent (l + 1) os (by omega)⟩
    split
    · exact argReg_plain (loc_ne31 hk (by omega)) o
    · simp

theorem cLoads_plain {k c : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (n : Nat) (ent : Nat → Bool) :
    ∀ (l : Nat) (os : List Operand), l + os.length ≤ k + c → ∀ x ∈ cLoads k c n ent l os, plain x = true
  | _, [], _ => by simp [cLoads]
  | l, o :: os, h => by
    simp only [List.length_cons] at h
    simp only [cLoads]
    refine List.forall_mem_append.2 ⟨?_, cLoads_plain hk n ent (l + 1) os (by omega)⟩
    split
    · exact argReg_plain (loc_ne31 hk (by omega)) o
    · simp

theorem moves_plain {ms : List (Reg × Reg)} (h : ∀ p ∈ ms, p.1 ≠ 31) :
    ∀ x ∈ ms.map (fun p => mv p.1 p.2), plain x = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact A64.mv_plain (h p hp)

/-- Running `cLoads k c n ent l os`, after the preserved register arguments, loads each operand
`i` that is in no caller-saved location into the register of location `l + i` when `ent` names
it. It writes no memory and changes no other register. -/
theorem run_cLoads (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {j' g : Nat} {keep : Nat → Bool} {mem : Memory} (hg : g ≤ k)
    (hjg : j' + g ≤ N) (ent : Nat → Bool) :
    ∀ (os : List Operand) (l : Nat) (t : State), ArgSt k lo N j j' g g keep m mem t →
    Lin.OpsBelow os fn.frame → k ≤ l → l + os.length ≤ k + c →
    (∀ y, Operand.slot y ∈ os → keep y = true) →
    ∃ t', runA ω (cLoads k c g ent l os) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      t'.regs.pc % 4 = 0 ∧
      (∀ i, i < os.length → ent (l + i) = true → isC k c (os[i]?.getD (.imm 0)) = false →
        t'.regs.x (loc k (l + i)) = (os[i]?.getD (.imm 0)).eval s.frame) ∧
      ∀ r : Reg, (∀ i, i < os.length → ent (l + i) = true →
        isC k c (os[i]?.getD (.imm 0)) = false → loc k (l + i) ≠ r) → t'.regs.x r = t.regs.x r
  | [], _, t, hS, _, _, _, _ => ⟨t, rfl, rfl, rfl, hS.pc, fun _ h => absurd h (by simp),
      fun _ _ => rfl⟩
  | o :: os, l, t, hS, ho, hkl, hl, hko => by
    simp only [List.length_cons] at hl
    have ho' : Lin.OpsBelow os fn.frame := fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)
    have hko' : ∀ y, Operand.slot y ∈ os → keep y = true := fun y hy => hko y (List.mem_cons_of_mem _ hy)
    have shift : ∀ i, (o :: os)[i + 1]?.getD (Operand.imm 0) = os[i]?.getD (.imm 0) := fun _ => rfl
    cases he : ent l && !isC k c o
    · obtain ⟨t', r2, m2, w2, a2, v2, k2⟩ := run_cLoads hM hk hsm hg hjg ent os (l + 1) t hS ho'
        (by omega) (by omega) hko'
      refine ⟨t', by simpa [cLoads, he] using r2, m2, w2, a2, fun i hi hei hci => ?_,
        fun r hr => k2 r fun i hi h1 h2 => ?_⟩
      · cases i with
        | zero => simp at hei hci; simp [hei, hci] at he
        | succ i =>
          rw [show l + (i + 1) = l + 1 + i by omega] at hei ⊢
          exact v2 i (by simpa using hi) hei hci
      · rw [show l + 1 + i = l + (i + 1) by omega] at h1 ⊢
        exact hr (i + 1) (by simp; omega) h1 h2
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
      have hko0 : ∀ y, o = .slot y → keep y = true := fun y hy => hko y (hy ▸ List.mem_cons_self)
      obtain ⟨t1, r1, m1, w1, a1, v1, k1⟩ := run_argReg (ω := ω) hM hk hsm hS (Nat.le_refl _) hjg
        (jd := l) (by omega) (fun h => absurd h (by omega))
        (o := o) (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy)) hko0
        (fun y hy h1 h2 => by subst hy; simp [isC, h1, h2] at he)
      have hS1 : ArgSt k lo N j j' g g keep m mem t1 :=
        ⟨m1.trans hS.hmem, hS.region, (k1 31 (loc_ne31 hk (by omega)).symm).trans hS.sp,
          (k1 17 (loc_ne hk (r := 17) (by omega) (by decide)).symm).trans hS.x17,
          by rw [w1]; exact hS.halted, a1, hS.saves, hS.slots, fun x hx hlx => by
            rw [k1 _ (preg_ne_loc hk (by omega) hkl (by omega))]; exact hS.regs x hx hlx⟩
      obtain ⟨t', r2, m2, w2, a2, v2, k2⟩ := run_cLoads hM hk hsm hg hjg ent os (l + 1) t1 hS1 ho'
        (by omega) (by omega) hko'
      have hne : ∀ i, i < os.length → loc k (l + 1 + i) ≠ loc k l := fun i hi e => by
        have := loc_inj hk (by omega) (by omega) e; omega
      refine ⟨t', by simp only [cLoads, he, Bool.not_false, Bool.and_self, ite_true]
                     rw [runA_append, r1, Option.bind_some, r2],
        m2.trans m1, w2.trans w1, a2, fun i hi hei hci => ?_, fun r hr => ?_⟩
      · cases i with
        | zero => rw [Nat.add_zero, k2 _ fun i hi _ _ => hne i hi]; exact v1
        | succ i =>
          rw [show l + (i + 1) = l + 1 + i by omega] at hei ⊢
          exact v2 i (by simpa using hi) hei hci
      · rw [k2 r fun i hi h1 h2 => by
            rw [show l + 1 + i = l + (i + 1) by omega] at h1 ⊢
            exact hr (i + 1) (by simp; omega) h1 h2,
          k1 r fun e => hr 0 (by simp) (by simpa using he.1) (by simpa using he.2) e.symm]

/-- The caller-saved register arguments: the moves `mvs` of the parallel move from caller-saved
registers, then `cLoads`. Each caller-saved location of the callee that `ent` names gets its
argument, and no register but `x9` and those locations changes. -/
theorem run_cArgs (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {j' G : Nat} {args : List Operand} {keep ent : Nat → Bool}
    {mem : Memory} {mvs : List (Reg × Reg)} (hargs : args.length ≤ G) (hjg : j' + min k G ≤ N)
    (ho : Lin.OpsBelow args fn.frame) (hka : ∀ y, Operand.slot y ∈ args → keep y = true)
    (hseq : cSeq k c G args ent = some mvs) {t : State}
    (hS : ArgSt k lo N j j' (min k G) (min k G) keep m mem t)
    (hC : ∀ y, k ≤ y → y < k + c → t.regs.x (loc k y) = m.regs.x (loc k y)) :
    ∃ t', runA ω (mvs.map (fun p => mv p.1 p.2) ++ cLoads k c (min k G) ent k (cArgs k c G args)) t =
        some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧ t'.regs.pc % 4 = 0 ∧
      (∀ x, k ≤ x → x < k + c → x < G → ent x = true →
        t'.regs.x (loc k x) = (args.map (Operand.eval s.frame)).getD x 0) ∧
      ∀ r : Reg, r ≠ 9 → (∀ x, k ≤ x → x < k + c → x < G → ent x = true → loc k x ≠ r) →
        t'.regs.x r = t.regs.x r := by
  have hlen := cArgs_length (k := k) (c := c) hargs
  have hinj : ∀ x y, x < k + c → y < k + c → loc k x = loc k y → x = y :=
    fun x y hx hy e => loc_inj hk hx hy e
  have hnd := Sel.cMoves_nodup (loc := loc k) (d := 31) hinj ent k (cArgs k c G args) (by omega)
  -- the destinations of the moves are caller-saved locations named by `ent`
  have hdst : ∀ p ∈ cMoves k c G args ent, ∃ x, k ≤ x ∧ x < k + c ∧ x < G ∧
      ent x = true ∧ p.1 = loc k x := fun p hp => Sel.cMoves_dst hargs ent hp
  have h9 : ∀ p ∈ cMoves k c G args ent, p.1 ≠ 9 := fun p hp => by
    obtain ⟨x, -, hx, -, -, he⟩ := hdst p hp; rw [he]; exact loc_ne hk hx (by decide)
  have h31 : ∀ p ∈ mvs, p.1 ≠ 31 := fun p hp => by
    rcases Sel.PMove.seq_dst _ hseq p hp with h | ⟨q, hq, he⟩
    · rw [h]; decide
    · obtain ⟨x, -, hx, -, -, he'⟩ := hdst q hq; rw [← he, he']; exact loc_ne31 hk hx
  obtain ⟨t1, r1, m1, w1, sp1, a1, g1⟩ := run_moves (ω := ω) mvs h31 hS.halted hS.pc
  have hpar : ∀ r, r ≠ 9 → t1.regs.getZ r =
      Sel.PMove.par t.regs.getZ (cMoves k c G args ent) r := fun r hr => by
    rw [g1]; exact Sel.PMove.seq_run _ hnd h9 hseq _ r hr
  have hkeep1 : ∀ r, r ≠ 9 → (∀ x, k ≤ x → x < k + c → x < G → ent x = true → loc k x ≠ r) →
      t1.regs.getZ r = t.regs.getZ r := fun r hr hn => by
    rw [hpar r hr]
    exact Sel.PMove.par_of_not _ fun s' hs => by
      obtain ⟨x, h1, h2, h3, h4, he⟩ := hdst _ hs; exact hn x h1 h2 h3 h4 he.symm
  have hx1 : ∀ r : Reg, r ≠ 9 → r ≠ 31 → (∀ x, k ≤ x → x < k + c → x < G → ent x = true →
      loc k x ≠ r) → t1.regs.x r = t.regs.x r := fun r h9 h31 hn => by
    have := hkeep1 r h9 hn; rwa [A64.getZ_ne h31, A64.getZ_ne h31] at this
  have hS1 : ArgSt k lo N j j' (min k G) (min k G) keep m mem t1 :=
    ⟨m1.trans hS.hmem, hS.region, sp1.trans hS.sp,
      (hx1 17 (by decide) (by decide) fun x _ hx _ _ => loc_ne hk hx (by decide)).trans hS.x17,
      by rw [w1]; exact hS.halted, a1, hS.saves, hS.slots, fun x hx hlx => by
        rw [hx1 _ (preg_ne (by omega) (by decide)) (preg_ne31 (by omega))
          fun y h1 h2 _ _ e => preg_ne_loc hk (by omega) h1 h2 e.symm]
        exact hS.regs x hx hlx⟩
  obtain ⟨t', r2, m2, w2, a2, v2, k2⟩ := run_cLoads (ω := ω) hM hk hsm (Nat.min_le_left k G) hjg ent
    (cArgs k c G args) k t1 hS1 (cArgs_below ho) (Nat.le_refl _) (by omega)
    (fun y hy => hka y (cArgs_slot hy))
  refine ⟨t', by rw [runA_append, r1, Option.bind_some, r2], m2.trans m1, w2.trans w1, a2,
    fun x h1 h2 h3 h4 => ?_, fun r hr hn => ?_⟩
  · have hi : x - k < (cArgs k c G args).length := by omega
    have hxk : k + (x - k) = x := by omega
    obtain ⟨o, hoi⟩ : ∃ o, (cArgs k c G args)[x - k]? = some o := ⟨_, List.getElem?_eq_getElem hi⟩
    have hval := cArgs_val (k := k) (c := c) hargs s.frame hi
    rw [hoi, Option.getD_some, hxk] at hval
    rw [← hval]
    have hom : o ∈ cArgs k c G args := List.mem_of_getElem? hoi
    cases hc : isC k c o
    · have := v2 (x - k) hi (by rw [hxk]; exact h4) (by rw [hoi]; exact hc)
      rwa [hxk, hoi] at this
    · rw [k2 _ fun i hi' _ hc' e => by
          have := loc_inj hk (by omega) (by omega) e
          rw [show i = x - k by omega, hoi, Option.getD_some, hc] at hc'; cases hc']
      have hp := hpar (loc k x) (loc_ne hk h2 (by decide))
      rw [Sel.par_cMoves hinj hargs ent _ h1 h3 h4 hoi hc h2, A64.getZ_ne (loc_ne31 hk h2)] at hp
      rw [hp]
      cases o with
      | imm w => simp [isC] at hc
      | slot y =>
        simp only [isC, Bool.and_eq_true, decide_eq_true_eq] at hc
        have hy : y < fn.frame := cArgs_below ho y hom
        have hv := loc_val hM hy
        rw [ite_eq_left hc.2] at hv
        rw [show Sel.oreg (loc k) 31 (.slot y) = loc k y from rfl, A64.getZ_ne (loc_ne31 hk hc.2),
          hC y hc.1 hc.2, hv]; rfl
  · rw [k2 r fun i hi h1 h2 e => hn (k + i) (by omega) (by omega) (by omega) h1 e]
    by_cases h31 : r = 31
    · subst h31; exact sp1
    · exact hx1 r hr h31 hn

/-- Every move of the caller-saved arguments' sequence writes `x9` or a location register. -/
theorem cSeq_dst {k c G : Nat} (hk : k ≤ 10 ∧ c ≤ 14) {args : List Operand} {ent : Nat → Bool}
    {mvs : List (Reg × Reg)} (hargs : args.length ≤ G) (h : cSeq k c G args ent = some mvs) :
    ∀ p ∈ mvs, p.1 ≠ 31 := fun p hp => by
  rcases Sel.PMove.seq_dst _ h p hp with h | ⟨q, hq, he⟩
  · rw [h]; decide
  · obtain ⟨x, -, hx, -, -, he'⟩ := Sel.cMoves_dst hargs ent hq
    rw [← he, he']; exact loc_ne31 hk hx

theorem callOps_plain {k c G : Nat} (hk : k ≤ 10 ∧ c ≤ 14) {args : List Operand}
    (keep ent : Nat → Bool) (hargs : args.length ≤ G) :
    ∀ x ∈ callOps k c G args keep ent, plain x = true := by
  unfold callOps
  refine List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨List.forall_mem_cons.2 ⟨A64.frameI_plain17 true _,
      saves_plain keep _ _⟩, argMems_plain k c ent _ _⟩,
    argRegs_plain hk ent _ _ (by simp [List.length_take]; omega)⟩, moves_plain ?_⟩,
    cLoads_plain hk _ ent _ _ (by rw [cArgs_length hargs]; omega)⟩
  cases h : cSeq k c G args ent with
  | none => simp
  | some mvs => exact cSeq_dst hk hargs h

/-- A call block, run from a related state, stops at the callee's address `ag` with the return
address in `x30` and `sp` unchanged. The callee frame of `W = Sel.frameW k c G` words at
`j' = j - fw W` holds the location registers that `keep` names in its words below `min k G` and
the memory argument of each slot `x` from `min (k + c) G` on in its word `x - c`, every other word
is unchanged, and the callee's register locations that `ent` names hold their arguments. -/
theorem run_callBlock (hM : Sel.MatchAt (conv k c mb) P AP σ lo N s m fn f a j) (hk : k ≤ 10 ∧ c ≤ 14)
    (hsm : fn.frame < maxFrame) {G : Nat} {args : List Operand} (hG : G < maxFrame)
    (hroomG : fw (Sel.frameW k c G) ≤ j) (hargs : args.length ≤ G) (ho : Lin.OpsBelow args fn.frame)
    {keep : Nat → Bool} (hka : ∀ y, Operand.slot y ∈ args → keep y = true) {ent : Nat → Bool}
    {mvs : List (Reg × Reg)} (hseq : cSeq k c G args ent = some mvs)
    {cX eb : List UInt8} (heX : Asm.encodeAll isa (callOps k c G args keep ent) = some cX)
    (hcX : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) cX) {imm : BitVec 26}
    (heb : isa.encode (.b true imm) = some eb)
    (hcb : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc) + UInt64.ofNat cX.length) eb)
    {ag : UInt64} (hreach : a + UInt64.ofNat (f.labelOff s.pc) +
      UInt64.ofNat (4 * (callOps k c G args keep ent).length) + (A64.sext imm <<< 2) = ag) (cy : Nat) :
    ∃ t : State, Sel.Leg (A := arch) linux ω (Sel.SpBound (conv k c mb) P lo N) m cy
        ((callOps k c G args keep ent).length + 1) t ∧
      t.regs.pc = ag ∧ t.regs.x 31 = Sel.wa lo j ∧
      t.regs.x 30 = a + UInt64.ofNat (f.labelOff s.pc + 4 * ((callOps k c G args keep ent).length + 1)) ∧
      t.world = m.world ∧ t.mem.WxorX ∧ Memory.Frame m.mem t.mem ∧ Sel.LowSame lo m.mem t.mem ∧
      Sel.Region t.mem lo N ∧
      (∀ q, q < N → Sel.word t.mem lo q =
        if j - fw (Sel.frameW k c G) ≤ q ∧ q < j - fw (Sel.frameW k c G) + min k G then
          (if keep (q - (j - fw (Sel.frameW k c G))) then
            m.regs.x (preg (q - (j - fw (Sel.frameW k c G)))) else Sel.word m.mem lo q)
        else if j - fw (Sel.frameW k c G) + min (k + c) G ≤ q + c ∧
            q + c < j - fw (Sel.frameW k c G) + G ∧ ent (q + c - (j - fw (Sel.frameW k c G))) = true
          then (args.map (Operand.eval s.frame)).getD (q + c - (j - fw (Sel.frameW k c G))) 0
        else Sel.word m.mem lo q) ∧
      ∀ x, x < k + c → t.regs.x (loc k x) =
        if x < G ∧ ent x = true then (args.map (Operand.eval s.frame)).getD x 0
        else m.regs.x (loc k x) := by
  have htop := hM.region.top
  have hroom := room_fw hM
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c G = W := ⟨_, rfl⟩
  have hWG : W = min G k + (G - (k + c)) := by rw [← hW]; rfl
  rw [hW] at hroomG ⊢
  have hgt := A64.fw_gt W
  have hrip : m.regs.pc = _ := hM.rip
  have hsp0 : m.regs.x 31 = Sel.wa lo j := hM.sp
  have hmm : min k G ≤ k := Nat.min_le_left k G
  have hmG : min k G ≤ G := Nat.min_le_right k G
  have hcG : min (k + c) G ≤ G := Nat.min_le_right (k + c) G
  have hlen : (padArgs G args).length = G := Sel.padArgs_length G args
  generalize hj' : j - fw W = j' at *
  have hj'G : j' + W ≤ j := by omega
  -- 1. `x17 :=` the callee frame
  have x1 : A64.exec (linux.trap ω) (frameI true 17 31 W) 4 m =
      some (m.goto (m.regs.set 17 (Sel.wa lo j')) (m.regs.pc + 4)) := by
    rw [A64.exec_frameI (pc4 hM) true 17 31 (by omega)]
    simp only [ite_true, hsp0, ← hj', A64.frame_sub (lo := lo) hroomG (by omega)]
  generalize ht1 : m.goto (m.regs.set 17 (Sel.wa lo j')) (m.regs.pc + 4) = t1 at x1
  have h1x : ∀ r : Reg, r ≠ 17 → t1.regs.x r = m.regs.x r := fun r hr => by
    rw [← ht1]; simp [show ¬ r = 17#5 from hr]
  -- 2. the saves
  obtain ⟨t2, r2, hreg2, hw2, hF2, hl2, hR2, hq2⟩ := run_saves (ω := ω) (i := j')
    (N := N) (lo := lo) keep (min k G) 0 t1 (by rw [← ht1]; simp)
    (by rw [← ht1]; exact hM.region) (by omega) (by omega)
    (by rw [← ht1]; exact hM.halted) (by rw [← ht1]; simpa using A64.aligned_add4 (pc4 hM))
  have h2x : ∀ r : Reg, t2.regs.x r = t1.regs.x r := fun r => by rw [hreg2]
  have hm1 : t1.mem = m.mem := by rw [← ht1]; rfl
  have ha2 : t2.regs.pc % 4 = 0 := by
    rw [hreg2]; simp only
    rw [← ht1]; simpa using A64.aligned_add (A64.aligned_add4 (pc4 hM)) (Nat.mul_mod_right 4 _)
  have hF2' : Fetch k c lo N j m t2 :=
    ⟨⟨hR2, fun i h1 h2 => by rw [hq2 i h2, ite_eq_right (by omega), hm1], by
        rw [h2x, h1x _ (by decide)], by rw [hw2, ← ht1]; exact hM.halted, ha2⟩, fun x hx => by
      rw [A64.getZ_ne (loc_ne31 hk hx), A64.getZ_ne (loc_ne31 hk hx), h2x,
        h1x _ (loc_ne hk hx (by decide))]⟩
  -- 3. the memory arguments
  obtain ⟨t3, r3, hF3, hw3, h17, hF3', hl3, hq3⟩ := run_argMems (ω := ω) hM hk hsm (G := W) (by omega) hj'G
    ent ((padArgs G args).drop (min (k + c) G)) (min (k + c) G) t2 hF2' (by rw [h2x, ← ht1]; simp)
    (fun y hy => Sel.padArgs_below ho y (List.mem_of_mem_drop hy)) (by simp [hlen]; omega)
    (by
      by_cases h : k + c ≤ G
      · exact Or.inr (by omega)
      · exact Or.inl (by simp [hlen]; omega))
  have hx3 : ∀ x, x < k + c → t3.regs.x (loc k x) = m.regs.x (loc k x) := fun x hx => by
    have := hF3.regs x hx
    rwa [A64.getZ_ne (loc_ne31 hk hx), A64.getZ_ne (loc_ne31 hk hx)] at this
  have hS3 : ArgSt k lo N j j' (min k G) 0 keep m t3.mem t3 :=
    ⟨rfl, hF3.region, hF3.sp, by rw [h17, h2x, ← ht1]; simp, hF3.halted, hF3.pc,
      fun y hy hky => by
        rw [hq3 _ (by omega), ite_eq_right (fun h => by simp [hlen] at h; omega), hq2 _ (by omega),
          ite_eq_left (by omega),
          show j' + y - j' = y by omega, ite_eq_left hky, h1x _ (preg_ne (by omega) (by decide))],
      hF3.words, fun x hx _ => by rw [← loc_of_lt hx]; exact hx3 x (by omega)⟩
  -- 4. the preserved register arguments
  obtain ⟨t4, r4, hm4, hw4, ha4, hv4, hk4, ho4⟩ := run_argRegs (ω := ω) hM hk hsm (j' := j')
    (g := min k G) (mem := t3.mem) hmm (by omega) ent ((padArgs G args).take (min k G)) 0 t3 hS3
    (fun y hy => Sel.padArgs_below ho y (List.mem_of_mem_take hy)) (by simp [hlen])
    (fun y hy => hka y (slot_of_pad hy)) (fun y h1 h2 => hx3 y h2)
  have hx4 : ∀ x, k ≤ x → x < k + c → t4.regs.x (loc k x) = m.regs.x (loc k x) := fun x h1 h2 => by
    rw [ho4 _ fun y hy e => preg_ne_loc hk hy h1 h2 e, hx3 x h2]
  -- 5. the caller-saved register arguments
  obtain ⟨t5, r5, hm5, hw5, ha5, hv5, hk5⟩ := run_cArgs (ω := ω) hM hk hsm hargs (by omega) ho hka
    hseq (t := t4) (mem := t3.mem) ⟨hm4, hF3.region, (ho4 31 fun x hx => preg_ne31 hx).trans hF3.sp,
      by rw [ho4 17 fun x hx => preg_ne hx (by decide), h17, h2x, ← ht1]; simp,
      by rw [hw4]; exact hF3.halted, ha4, hS3.saves, hF3.words, fun x hx hlx => by
        rw [hk4 x (by omega) (Or.inr (Or.inl (by simp [hlen]; omega)))]
        exact hS3.regs x hx (Nat.zero_le _)⟩ hx4
  -- the straight-line part as one run
  have hrun : runA ω (callOps k c G args keep ent) m = some t5 := by
    simp only [callOps, hseq, hW, Option.getD_some, List.cons_append, List.append_assoc]
    rw [runA_cons hM.halted (by unfold frameI; split <;> rfl) x1, runA_append, r2, Option.bind_some,
      runA_append, r3, Option.bind_some, runA_append, r4, Option.bind_some]; exact r5
  obtain ⟨hrunX, hFX, hwxX, hpcX, hallX⟩ := Sel.run_straight (A := arch) (abi := linux) A64.laws cy
    hM.wx heX (by rw [hM.rip]; exact hcX) (straight_all (callOps_plain hk keep ent hargs)) hrun
  have hpc5 : t5.regs.pc = a + UInt64.ofNat (f.labelOff s.pc) +
      UInt64.ofNat (4 * (callOps k c G args keep ent).length) := by
    rw [← A64.encodeAll_length heX, ← hrip]; exact hpcX
  have hsp5 : t5.regs.x 31 = Sel.wa lo j := by
    rw [hk5 31 (by decide) fun x _ hx _ _ => loc_ne31 hk hx, ho4 31 fun x hx => preg_ne31 hx,
      hF3.sp, hsp0]
  -- 6. `bl`
  have x6 : A64.exec (linux.trap ω) (.b true imm) 4 t5 =
      some (State.goto t5 (t5.regs.set 30 (t5.regs.pc + 4)) ag) := by
    simp only [A64.exec, ha5, ne_eq, not_true_eq_false, ite_false, ite_true]; rw [hpc5, hreach]
  have st6 := A64.step_one (c := cy + (callOps k c G args keep ent).length)
    (by rw [hw5, hw4, hF3.halted]) heb
    (by rw [hpc5, ← A64.encodeAll_length heX]; exact Sel.codeAt_frame hM.wx hFX _ _ hcb) x6
  have sbj : ∀ x : State, x.regs.x 31 = Sel.wa lo j → Sel.SpBound (conv k c mb) P lo N x :=
    fun x h => Sel.spBound_of_match hM (Nat.le_refl _) (Sel.matchAt_room hM).1 h
  refine ⟨_, (Sel.Leg.mono (fun x h => Sel.spBound_of_keep hM h) ⟨hrunX, hallX⟩).trans
      (Sel.Leg.one st6 (sbj _ hsp5) (sbj _ (by simpa using hsp5))), rfl, by simpa using hsp5,
    ?_, by simp [hw5, hw4, hw3, hw2, ← ht1], hwxX, hFX,
    (hm1 ▸ hl2).trans (hm5 ▸ hm4 ▸ hl3), hm5 ▸ hm4 ▸ hF3.region, fun q hq => ?_, fun x hx => ?_⟩
  · simp only [A64.goto_regs, Regs.set_x, ite_true, hpc5]
    rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, A64.pc_add, A64.pc_add]; congr 2
  · show Sel.word t5.mem lo q = _
    rw [hm5, hm4, hq3 q hq, hq2 q hq, hm1]
    simp only [List.length_drop, hlen]
    by_cases h1 : j' ≤ q ∧ q < j' + min k G
    · rw [ite_eq_right (fun h => by omega), ite_eq_left (by omega), ite_eq_left h1]
      split
      · rw [h1x _ (preg_ne (by omega) (by decide))]
      · rfl
    · rw [ite_eq_right h1]
      by_cases h2 : j' + min (k + c) G ≤ q + c ∧ q + c < j' + min (k + c) G + (G - min (k + c) G) ∧
          ent (q + c - j') = true
      · rw [ite_eq_left h2, ite_eq_left ⟨by omega, by omega, h2.2.2⟩,
          pad_drop hargs (by omega) (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega),
          ite_eq_right (fun h => h2 ⟨by omega, by omega, h.2.2⟩)]
  · simp only [A64.goto_regs, Regs.set_x]
    rw [ite_eq_right (loc_ne hk hx (by decide))]
    by_cases hxk : x < k
    · rw [loc_of_lt hxk, hk5 _ (preg_ne (by omega) (by decide))
        fun y h1 _ _ _ e => preg_ne_loc hk (by omega) h1 (by omega) e.symm]
      by_cases hxm : x < G ∧ ent x = true
      · rw [ite_eq_left hxm]
        have := hv4 x (by simp [hlen]; omega) (by simpa using hxm.2); rw [Nat.zero_add] at this
        rw [this, pad_take hargs (by omega) hmG]
      · rw [ite_eq_right hxm, hk4 x (by omega) (by
          by_cases h : x < G
          · exact Or.inr (Or.inr (by simpa [h] using hxm))
          · exact Or.inr (Or.inl (by simp [hlen]; omega))), ← loc_of_lt hxk, hx3 x hx]
    · by_cases hxm : x < G ∧ ent x = true
      · rw [ite_eq_left hxm, hv5 x (by omega) hx hxm.1 hxm.2]
      · rw [ite_eq_right hxm, hk5 _ (loc_ne hk hx (by decide)) fun y _ hy h3 h4 e => hxm
            (by rw [← loc_inj hk hy hx e]; exact ⟨h3, h4⟩), hx4 x (by omega) hx]

end Match

end Millipede.RegAlloc.A64Reg

/-! ## The cases -/

namespace Millipede.RegAlloc.A64Reg

open Flat (Operand)
open Millipede.A64 (State Regs Reg Instr runA arch linux isa ldIs fw maxFrame frameI farProg
  straight_all)

section Cases
variable {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {σ : String → Option UInt64} {lo N : Nat}

theorem callIs_length (k c g g' G : Nat) (args : List Operand) (keep ent : Nat → Bool) :
    (callIs k c g G args keep ent).length = (callIs k c g' G args keep ent).length := by
  simp [callIs, A64.ops]

/-- The caller of the running activation holds its frame in a view that agrees below `k` with the
running activation's save words (`callerView`). -/
theorem caller_locs {s : Lin.State} {m : State} {fn : Lin.Fn} {f : Asm.Fn arch} {a : UInt64}
    {j : Nat} (hM : Sel.MatchAt (conv k c mb) P A σ lo N s m fn f a j) {act : Lin.Act}
    {st : List Lin.Act} (hst : s.stack = act :: st) {fa : Lin.Fn} (hfa : P.funs[act.fn]? = some fa) :
    ∃ rv₀ : Sel.RegView, (∀ x, x < k →
      rv₀ x = Sel.callerView lo k m.mem j fn.frame (fun y => m.regs.x (preg y)) x) ∧
      Sel.LocsOk lo k c rv₀ m.mem (j + fw (Sel.frameW k c fn.frame)) fa.frame act.frame := by
  have hFr := hM.frames; rw [hst] at hFr
  obtain ⟨rv₀, hv, hL⟩ := Sel.frames_caller hFr
  rw [Sel.calleeFrame_eq hM.hfn, Sel.calleeFrame_eq hfa] at hL
  rw [Sel.calleeFrame_eq hM.hfn] at hv
  exact ⟨rv₀, fun x hx => by rw [hv x hx]; simp [Sel.callerView, conv, loc_of_lt hx], hL⟩

/-- The `ret` case: the callee's return block, followed by the caller's stores of the result
words into their locations, ends in a state related to Lin's state after the return up to the
caller-saved locations that the call destroys and does not define. -/
theorem simRet (hk : k ≤ 10 ∧ c ≤ 14) (hsel : select k c P mb = .ok A) (hwf : P.Wf) :
    Sel.StepOkAt linux (conv k c mb) P A σ lo N (Live.flex P) (fun _ _ => instrs k c mb none P 0 0)
      fun i => i = .ret := by
  intro ω κ s s' (m : State) cy fn f a j ins hM hi hx hs
  subst hx
  obtain ⟨ins', hi', -, he⟩ := Sel.step_fetch_inv hM.run hM.hfn hs
  rw [hi] at hi'; cases hi'
  obtain ⟨b, hC⟩ := Sel.ctx_of A64.asm_laws (select_ok hsel) hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  obtain ⟨⟨hsm, hret⟩, -, h4⟩ := fnOk_iff.1 hC.sel.ok
  simp only [selector, selInstr] at hsi
  split at hsi
  · cases hsi
  rename_i rl hrl
  obtain ⟨rfl, rfl⟩ := hsi
  cases hst : s.stack with
  | nil => simp [Lin.exec, hst] at he
  | cons act st =>
  simp only [Lin.exec, hst, Option.some.injEq] at he
  subst he
  obtain ⟨fa, args, fc, addr, hfa, hfc, hσ, hpc0, hcall, hra, hroomc⟩ := hM.caller hst
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c fn.frame = W := ⟨_, rfl⟩
  change j + fw (Sel.frameW k c fn.frame) + Sel.frameW k c fa.frame ≤ N at hroomc
  change Sel.word m.mem lo (j + Sel.frameW k c fn.frame) = _ at hra
  rw [hW] at hroomc hra
  have hWa : Sel.frameW k c fa.frame = min fa.frame k + (fa.frame - (k + c)) := rfl
  have hroom := room_fw hM
  rw [hW] at hroom
  obtain ⟨rv₀, hrv, hCL⟩ := caller_locs hM hst hfa
  rw [hW] at hCL
  -- 1. the callee's return block
  obtain ⟨is, code, hr, hen, hcode⟩ := hC.code
  obtain rfl := A64.resolveAt_ops_inv hr
  obtain ⟨t4, L4, hpc4, hsp4, hm4, hw4, hval, hcv, h29₄⟩ :=
    run_retBlock (ω := ω) hM hk hC.sel.ok hsm hret hC.fwf.1 hrl hW (hW ▸ hen) hcode cy
  -- 2. the caller's result stores, from its call block
  obtain ⟨bc, dc, hbc, hsic, hseq, hsfc⟩ := Sel.block_at A64.asm_laws (select_ok hsel) hM.loaded hfa
    hfc hσ hcall
  obtain ⟨-, -, gf, hgf, -, hdst⟩ := (hwf.2 act.fn fa hfa).2 _ (List.mem_of_getElem? hcall)
  rw [hM.hfn] at hgf; cases hgf
  simp only [selector, selInstr, hM.hfn] at hsic
  split at hsic
  · split at hsic
    rotate_left
    · cases hsic
    rename_i rr _ hrR
    cases hsic
    obtain ⟨⟨hfsm, -⟩, -⟩ := fnOk_iff.1 hsfc.ok
    obtain ⟨isr, cr, hrr, henr, hcr⟩ := (Sel.seqAt_append A64.asm_laws hseq).2
    obtain rfl := A64.resolveAt_ops_inv hrr
    rw [A64.seqSize_si, A64.pc_add, show 4 * (callIs k c s.fn fn.frame args _ _).length =
      (conv k c mb).retOff P act.fn (act.pc - 1) s.fn args act.dst by
        simp [conv, callIs_length k c s.fn 0, Sel.calleeFrame_eq hM.hfn], ← hra, ← hpc4] at hcr
    have haddr4 : addr % 4 = 0 := hM.syms fc (List.mem_of_getElem? hfc) addr hσ
    have hj2 : (j + fw W) % 2 = 0 := by
      have := hM.ok.2.2; have := A64.fw_even W; omega
    obtain ⟨t5, r5, hpl5, hlen5, hw5, hF5, hl5, hR5, hq5, hp5, hsp5⟩ := run_retR (ω := ω) (P := P) hk
      (fun h => A64.farProg_le h hfa) hfsm fn.ret.length act.dst hrR t4 hsp4
      (hsp4 ▸ A64.wa16 hM.ok.2.1 hj2 (by have := hM.region.top; omega)) (hm4 ▸ hM.region) hdst
      hroomc hret (by rw [hw4]; exact hM.halted)
      (by rw [hpc4, hra]; exact A64.aligned_add haddr4 (by
        have := A64.labelOff_4 fc (act.pc - 1); simp [conv]; omega))
    obtain ⟨hrun6, hF6, -, hpc6, hall6⟩ := Sel.run_straight (A := arch) (abi := linux) A64.laws _
      (hm4 ▸ hM.wx) henr (by rw [hm4]; exact hcr) (straight_all hpl5) r5
    have L := L4.trans (Sel.Leg.mono (fun x h => Sel.spBound_of_match hM (by omega) hroom
      (h.trans hsp4)) ⟨hrun6, hall6⟩)
    have hpcT : t5.regs.pc = addr + UInt64.ofNat (fc.labelOff act.pc) := by
      rw [show t5.regs.pc = t4.regs.pc + UInt64.ofNat cr.length from hpc6, hpc4, hra, A64.pc_add,
        A64.encodeAll_length henr]
      conv => rhs; rw [show act.pc = act.pc - 1 + 1 by omega, Sel.labelOff_succ fc hbc, A64.seqSize_si]
      congr 2
      simp [conv, A64.ops, callIs_length k c s.fn 0, Sel.calleeFrame_eq hM.hfn]
      erw [List.length_map]; omega
    have hLT : ∀ y, y < fa.frame → ((conv k c mb).kill (.call s.fn args act.dst) y = false ∨
        Live.defs P (.call s.fn args act.dst) y = true) →
        Sel.locVal (conv k c mb) lo t5 (j + fw W) y =
          Flat.Frame.writes act.frame act.dst (fn.ret.map (Operand.eval s.frame)) y := by
      intro y hy hky
      have hcl := hCL y hy
      show (if y < k + c then t5.regs.x (loc k y) else Sel.word t5.mem lo (j + fw W + y - c)) = _
      rw [Sel.writes_apply]
      simp only [List.length_map]
      by_cases hyc : y < k + c
      · rw [ite_eq_left hyc, hp5 y hyc]; rw [ite_eq_left hyc] at hcl
        by_cases hd : act.dst ≤ y ∧ y < act.dst + fn.ret.length
        · rw [ite_eq_left hd, ite_eq_left hd, hval _ (by omega)]
        · rw [ite_eq_right hd, ite_eq_right hd]
          have hyk : y < k := by
            rcases hky with h | h
            · simp [conv, Alloc.Classes.across, cls] at h; omega
            · simp [Live.defs, retLen, hM.hfn] at h; omega
          rw [loc_of_lt hyk, hcv y hyk, ← hrv y hyk, hcl]
      · rw [ite_eq_right hyc, hq5 _ (by omega)]; rw [ite_eq_right hyc] at hcl
        by_cases hd : act.dst ≤ y ∧ y < act.dst + fn.ret.length
        · rw [ite_eq_left (by omega), ite_eq_left hd, hval _ (by omega)]; congr 2; omega
        · rw [ite_eq_right (by omega), ite_eq_right hd, hm4, hcl]
    obtain ⟨s'', hR'', hM''⟩ := Sel.matchAt_ret_kill hM hst hfa hfc hσ
      (by have := Sel.pc_lt hcall; omega) (j' := j + fw W) (by simp [conv, hW])
      (by simp [conv, A64.φ, A64.fsize_eq, FrameModel.words, hW]) (hw5.trans hw4) (hm4 ▸ hF5)
      (hm4 ▸ hl5) hR5
      ⟨haddr4, hM.ok.2.1, hj2⟩ hpcT (hsp5.trans hsp4) (clob_of_select hsel) hpc0 hcall hLT
      (fun x hx => by simp at hx; rw [hq5 _ (by omega), ite_eq_right (by omega), hm4])
      (fun i hi hi' => by
        simp only [conv_k, conv_c] at hi; rw [hq5 _ (by omega), ite_eq_right (by omega), hm4])
      (fun x hx hxk => by
        change x < k at hxk
        show t5.regs.x (loc k x) = _
        rw [hp5 x (by omega), ite_eq_right (by omega), loc_of_lt hxk, hcv x hxk]
        simp [Sel.callerView, conv, loc_of_lt hxk])
      (regOk_of_x29 (by rw [A64.runA_k29 hpl5 (retR_k29 hk hrR) r5, h29₄]) hM.regOk)
    exact ⟨_, t5, L.run, Or.inl ⟨s'', hR'', _, _, _, _, hM''⟩, fun h => absurd h (by omega),
      L.all, by
        simp only [instrs, selInstr, hrl, A64.ops, List.length_map, List.length_append,
          List.length_cons, List.length_nil, hW]
        replace hlen5 : List.length (α := arch.isa.Instr) isr ≤
          resFuel fn.ret.length + (if farProg P = true then 1 else 0) := hlen5
        generalize (if farProg P = true then 1 else 0) = z at hlen5 ⊢
        generalize resFuel fn.ret.length = z' at hlen5 ⊢
        simp only [Nat.zero_add] at hlen5 ⊢
        exact Nat.le_trans (Nat.add_le_add_left hlen5 _) (Nat.le_of_eq (Nat.add_assoc _ _ _).symm)⟩
  · cases hsic

/-- The encoded size of an entry sequence: the frame set-up and, with `mb`, the two
instructions that set `x29`. -/
theorem entry_size (k c : Nat) (mb : Bool) (lvo : Option LiveSets) (fn : Lin.Fn) :
    Asm.seqSize arch ((selector k c mb lvo).entry fn) =
      4 * ((A64.entryIs (Sel.frameW k c fn.frame)).length + if mb then 2 else 0) := by
  cases mb <;> simp [selector, A64.seqSize_si, A64.ops, A64.symAddr, Asm.seqSize_append] <;> omega

/-- The `call` case: the call block and the callee's entry end in a state related to Lin's state
at the callee's entry. The related state differs from Lin's in the suspended caller, which reads
each unsaved register from its save word, and the two agree on the locations live after the
call. -/
theorem simCall (hk : k ≤ 10 ∧ c ≤ 14) (hsel : select k c P mb = .ok A) (hwf : P.Wf)
    (hB : P.stackBytes (conv k c mb).φ ≤ 8 * N) :
    Sel.StepOkAt linux (conv k c mb) P A σ lo N (Live.flex P) ((counts k c mb (Live.of P)).ins P)
      fun i => ∃ g args d, i = .call g args d := by
  intro ω κ s s' (m : State) cy fn f a j ins hM hi ⟨g, args, dst, hx⟩ hs
  subst hx
  obtain ⟨ins', hi', -, he⟩ := Sel.step_fetch_inv hM.run hM.hfn hs
  rw [hi] at hi'; cases hi'
  obtain ⟨b, hC⟩ := Sel.ctx_of A64.asm_laws (select_ok hsel) hwf hM hi
  obtain ⟨dd, hsi, -⟩ := hC.instr
  obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hC.sel.ok
  obtain ⟨hg, ho, gf, hgf, hargs, -⟩ := hC.wf
  simp only [selector, selInstr, hgf] at hsi
  split at hsi
  rotate_left
  · exact absurd hargs ‹_›
  split at hsi
  rotate_left
  · cases hsi
  rename_i rr hsome hrR
  obtain ⟨mvs, hseq⟩ := Option.isSome_iff_exists.1 hsome
  cases hsi
  simp only [Lin.exec, Option.some.injEq] at he
  subst he
  -- the callee
  obtain ⟨-, -, -, hk'⟩ := Sel.select_spec (select_ok hsel)
  obtain ⟨fg, hfg, hsfg⟩ := hk' g gf hgf
  have hmemg : fg ∈ A.funs := List.mem_of_getElem? hfg
  obtain ⟨ag, hag, ⟨ie, ce, hre, hene, hce⟩, -⟩ := Sel.fn_code A64.asm_laws hM.loaded hmemg
  rw [hsfg.entry] at hre
  obtain ⟨Dm, hDm, -, -⟩ := hM.data
  obtain ⟨⟨hgsm, -⟩, -⟩ := fnOk_iff.1 hsfg.ok
  have hag4 : ag % 4 = 0 := hM.syms fg hmemg ag hag
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c gf.frame = W := ⟨_, rfl⟩
  have hWG : W = min gf.frame k + (gf.frame - (k + c)) := by rw [← hW]; rfl
  have hroomG : fw W ≤ j := by
    have := hM.room_call hB hi hg hgf
    simp only [conv, A64.φ, A64.fsize_eq, FrameModel.words, hW] at this; omega
  have hgt := A64.fw_gt W
  have hroom := room_fw hM
  -- 1. the call block
  obtain ⟨is, code, hr, hen, hcode⟩ := hC.code
  obtain ⟨i₀, i₃, rfl, hr₀, -⟩ := Sel.resolveAt_append _ _ _ _ hr
  obtain ⟨is', rfl, hr₁⟩ := A64.resolveAt_ops_append hr₀
  obtain ⟨i', rfl, h₁⟩ := A64.resolveAt_single hr₁
  obtain ⟨t, imm, ht, rfl, hreach⟩ := A64.resolve_b h₁
  simp only [Asm.Fn.refAddr, ← hsfg.name, hag, Option.some.injEq] at ht
  subst ht
  obtain ⟨c₀, c₃, rfl, he₀, -⟩ := Sel.encodeAll_append _ _ _ hen
  obtain ⟨cX, cb, rfl, heX, heb⟩ := Sel.encodeAll_append _ _ _ he₀
  obtain ⟨eb, eb2, heb1, -, rfl⟩ := Asm.encodeAll_cons_inv heb
  obtain ⟨hcX, hcb⟩ := Sel.codeAt_append _ _ _ _ (Sel.codeAt_append _ _ _ _ hcode).1
  have hfr := Sel.calleeFrame_eq hM.hfn
  obtain ⟨t3, L3, hpc3, hsp3, h30, hw3, hwx3, hF3, hl3, hR3, hq3, hv3⟩ := run_callBlock hM hk hsm
    hgsm (by rw [hW]; exact hroomG) hargs ho (fun y hy => by simp [Live.callKeep, Live.keepCall, hy]) hseq heX hcX heb1
    (Sel.codeAt_append _ _ _ _ hcb).1 hreach cy
  -- 2. the callee's entry
  obtain ⟨t5, st5, hlen5, hsp5, hpc5, hw5, hF5, -, hl5, hR5, hv5, hr5, hall5, hk5, h29⟩ :=
    A64.run_entryB (ω := ω) (mb := mb)
    (cy + ((callOps k c gf.frame args (Live.callKeep (Live.of P) P s.fn s.pc g dst args)
      (Live.liveIn (Live.of P) g 0)).length + 1)) (F := W) (by omega) hroomG (by omega) hR3 hsp3
    hM.ok.2.1 hM.ok.2.2 (by rw [hw3]; exact hM.halted) (by rw [hpc3]; exact hag4) hwx3
    (show fg.refAddr σ ag (.sym Sel.memSym) = some Dm from hDm)
    (by rw [hpc3, ← hW]; exact hre) hene
    (by rw [hpc3]; exact Sel.codeAt_frame hM.wx hF3 _ _ hce)
  have hj2 : (j - fw W) % 2 = 0 := by
    have := hM.ok.2.2; have := A64.fw_even W; omega
  simp only [hW] at hq3
  have hmm := Nat.min_le_left k gf.frame
  have hmG := Nat.min_le_right k gf.frame
  have hk5' : ∀ x, x < k + c → t5.regs.x (loc k x) = t3.regs.x (loc k x) := fun x hx =>
    hk5 _ (loc_ne31 hk hx) (loc_ne hk hx (by decide)) (loc_ne29 hk hx)
  -- the callee's frame as the machine holds it: the arguments in the locations live at entry
  let cf : Flat.Frame := fun x => if Live.liveIn (Live.of P) g 0 x then
    (args.map (Operand.eval s.frame)).getD x 0
    else if x < k + c then t5.regs.x (loc k x) else Sel.word t5.mem lo (j - fw W + x - c)
  have hM' := Sel.matchAt_call hM hi hg hgf hfg hag (j' := j - fw W) (cf := cf)
    (by simp only [conv, hW]; omega) (by simp [conv, A64.φ, A64.fsize_eq, FrameModel.words, hW])
    (by rw [hw5, hw3]) (hF3.trans hF5) (hl3.trans hl5) hR5 ⟨hag4, hM.ok.2.1, hj2⟩
    (by show t5.regs.pc = _; rw [hpc5, hpc3, hlen5, Asm.Fn.labelOff, hsfg.entry]
        simp only [Asm.blocksOff, entry_size, Nat.add_zero, hW])
    hsp5 (fun x hx => ?_)
    (by rw [conv_k, conv_c, hW, hv5, h30]; simp [conv, callIs, A64.ops, Sel.calleeFrame_eq hgf])
    (fun i hi hi' => ?_) (keep := Live.callKeep (Live.of P) P s.fn s.pc g dst args)
    (fun x hx => by simp [Live.callKeep, Live.keepCall, hfr, hx]) (fun x hx hkx => ?_)
    (fun x hx hxk => ?_) (fun hmb D hD => by
      rw [h29, if_pos hmb]; rw [hDm] at hD; exact Option.some.inj hD)
  · have L := L3.trans (Sel.Leg.mk st5 (hall5.mono fun x h => h.elim
      (fun h => Sel.spBound_of_match hM (Nat.le_refl _) (by omega) h)
      (fun h => Sel.spBound_of_match hM' (Nat.le_refl _) (by omega) h)))
    refine ⟨_, _, L.run, Or.inl ⟨_, Live.R_call P (args := args) (F := Sel.calleeFrame P s.fn)
      (fun x hx => by simp [cf, hx, Flat.Frame.ofList]) fun x hx => ?_, _, _, _, _, hM'⟩,
      fun h => absurd h (by omega), L.all, ?_⟩
    · simp only [Sel.savedFrame]
      rw [ite_eq_right fun h => by have h2 := h.2; unfold Live.callKeep at h2; rw [hx] at h2; cases h2]
    · refine Nat.le_of_eq ?_
      simp only [counts, instrs, callIs, A64.ops, List.length_append, List.length_map,
        List.length_singleton, A64.entryLen, Sel.calleeFrame_eq hgf, hW, hlen5]
      omega
  · show (if x < k + c then t5.regs.x (loc k x) else Sel.word t5.mem lo (j - fw W + x - c)) = cf x
    simp only [cf]
    by_cases he : Live.liveIn (Live.of P) g 0 x = true
    · rw [ite_eq_left he]
      by_cases hxk : x < k + c
      · rw [ite_eq_left hxk, hk5' x hxk, hv3 x hxk, ite_eq_left ⟨hx, he⟩]
      · rw [ite_eq_right hxk, hr5 _ (by omega) (by omega), hq3 _ (by omega),
          ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by
            rw [show j - fw W + x - c + c - (j - fw W) = x by omega]; exact he⟩]
        congr 1; omega
    · rw [ite_eq_right he]
  · rw [hr5 i hi' (by omega), hq3 i hi', ite_eq_right (by omega), ite_eq_right (fun h => by omega)]
  · change x < min k gf.frame at hx
    show Sel.word t5.mem lo (j - fw W + x) = m.regs.x (loc k x)
    rw [hr5 _ (by omega) (by omega), hq3 _ (by omega), ite_eq_left (by omega),
      show j - fw W + x - (j - fw W) = x by omega, ite_eq_left hkx, loc_of_lt (by omega)]
  · change min k gf.frame ≤ x at hx; change x < k at hxk
    show t5.regs.x (loc k x) = m.regs.x (loc k x)
    rw [hk5' x (by omega), hv3 x (by omega), ite_eq_right (fun h => by omega)]

/-- The cases of the simulation proof for the register selector at the convention `conv k c`. -/
theorem cases (hk : k ≤ 10 ∧ c ≤ 14) (hsel : select k c P mb = .ok A) (hwf : P.Wf)
    (hB : P.stackBytes (conv k c mb).φ ≤ 8 * N) :
    Sel.Cases (A := arch) linux (conv k c mb) P A σ lo N (Live.flex P) ((counts k c mb (Live.of P)).ins P)
      (selector k c mb (Live.of P)) where
  mov := ((Sel.Ops.sim_mov (selOps_laws (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel) hwf).at _).of_eq
    fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  bin := ((Sel.Ops.sim_bin (selOps_laws (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel) hwf
    (clob_of_select hsel)).stepAt).of_eq
    fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  load := ((Sel.Ops.sim_load (selOps_laws (lvo := Live.of P) hk) (selOps_memLaws (lvo := Live.of P) hk)
    A64.asm_laws A64.laws (select_ok hsel) hwf).step.at _).of_eq
    fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  store := ((Sel.Ops.sim_store (selOps_laws (lvo := Live.of P) hk) (selOps_memLaws (lvo := Live.of P) hk)
    A64.asm_laws A64.laws (select_ok hsel) hwf).step.at _).of_eq
    fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  jmp := ((simJmp (lvo := Live.of P) hsel hwf).at _).of_eq fun _ _ _ _ ⟨_, h⟩ => by subst h; rfl
  jz := ((simJz (lvo := Live.of P) hsel hwf).at _).of_eq fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  call := simCall hk hsel hwf hB
  ret := (simRet hk hsel hwf).of_eq fun _ _ _ _ h => by subst h; rfl
  exit := ((Sel.Ops.sim_exit (selOps_laws (lvo := Live.of P) hk) (selOps_ext (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel) hwf).step.at
    _).of_eq fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  write := ((Sel.Ops.sim_write (selOps_laws (lvo := Live.of P) hk) (selOps_ext (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel) hwf
    (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, h⟩ => by subst h; rfl
  writeMem := ((Sel.Ops.sim_writeMem (selOps_laws (lvo := Live.of P) hk) (selOps_ext (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel)
    hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  read := ((Sel.Ops.sim_read (selOps_laws (lvo := Live.of P) hk) (selOps_ext (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel) hwf
    (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, h⟩ => by subst h; rfl
  readMem := ((Sel.Ops.sim_readMem (selOps_laws (lvo := Live.of P) hk) (selOps_ext (lvo := Live.of P) hk) A64.asm_laws A64.laws (select_ok hsel)
    hwf (clob_of_select hsel)).stepAt).of_eq fun _ _ _ _ ⟨_, _, _, _, h⟩ => by subst h; rfl
  tick _ _ _ _ := ⟨by simp [counts, instrs, selInstr], fun _ _ _ _ h => by
    simp only [selector, selInstr] at h; cases h; rfl⟩
  ext _ _ _ _ _ _ _ _ _ h := selInstr_ext h

end Cases

end Millipede.RegAlloc.A64Reg
