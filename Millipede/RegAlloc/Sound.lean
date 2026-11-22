import Millipede.RegAlloc.Alloc
import Millipede.RegAlloc.Lock
import Millipede.Target.SelSim

/-!
# Soundness of the register allocation checker

When `check P P' maps` accepts, the allocated program `P'` refines `P` in lock-step, which means
that each source step is matched by exactly one target step. This module proves that refinement,
`lockOfCheck`, by a relation `Rel` between a source state and a target state. Related states
have the same function, position, memory, world and clock, and at the current position each
entry `(y, l)` of the map has the value of slot `y` in location `l`. Every suspended activation
is related in the same way for every list of results the callee may return.

The proof of `step_sim` takes one case per Lin instruction, and each case ends in a lemma about
maps for operands, a definition, an instruction that defines nothing, a call's results or a
callee's entry. Further results say that the allocated program has the same runs and clocks as
the source, that its static stack bound is at most the source's for every frame model, and that
it is well formed.
-/

namespace Millipede.RegAlloc

open Flat (Operand ExtArg Frame)
open Lin (Instr Prog)

/-- A frame `g` agrees with `f` under the map `M` when each entry's location in `g` holds the
value of its slot in `f`. -/
def Agree (M : LocMap) (f g : Frame) : Prop := ∀ p ∈ M, g p.2 = f p.1

theorem opOk_eval {M : LocMap} {f g : Frame} (hA : Agree M f g) :
    ∀ {o o' : Operand}, opOk M o o' = true → o'.eval g = o.eval f
  | .imm w, .imm w', h => by simp only [opOk, beq_iff_eq] at h; simp [h]
  | .slot y, .slot l, h => by simp only [opOk, decide_eq_true_eq] at h; exact hA _ h
  | .imm _, .slot _, h => by simp [opOk] at h
  | .slot _, .imm _, h => by simp [opOk] at h

theorem opsOk_eval {M : LocMap} {f g : Frame} (hA : Agree M f g) :
    ∀ {os os' : List Operand}, opsOk M os os' = true → os'.map (Operand.eval g) = os.map (Operand.eval f)
  | [], [], _ => rfl
  | o :: os, o' :: os', h => by
    simp only [opsOk, Bool.and_eq_true] at h
    simp [opOk_eval hA h.1, opsOk_eval hA h.2]
  | [], _ :: _, h => by simp [opsOk] at h
  | _ :: _, [], h => by simp [opsOk] at h

theorem opsOk_length {M : LocMap} :
    ∀ {os os' : List Operand}, opsOk M os os' = true → os'.length = os.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [opsOk, Bool.and_eq_true] at h; simp [opsOk_length h.2]
  | [], _ :: _, h => by simp [opsOk] at h
  | _ :: _, [], h => by simp [opsOk] at h

/-! ## Extern calls -/

section Ext
-- The alternatives below share one argument list, and each case uses only some of it.
set_option linter.unusedSimpArgs false
variable {M : LocMap} {f g : Frame} (hA : Agree M f g)
include hA

theorem extsOk_words : ∀ {as as' : List ExtArg}, extsOk M as as' = true →
    Flat.extWords g as' = Flat.extWords f as
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [extsOk, Bool.and_eq_true] at h
    have ih := extsOk_words h.2
    cases a <;> cases a' <;> simp only [extOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_and] at h
    all_goals first
      | (simp [Flat.extWords, ih, opOk_eval hA h.1.1, opOk_eval hA h.1.2]; done)
      | (simp [Flat.extWords, ih, opOk_eval hA h.1]; done)
      | (simp [Flat.extWords, ih, h.1]; done)
      | (simp [Flat.extWords, ih]; done)
  | [], _ :: _, h => by simp [extsOk] at h
  | _ :: _, [], h => by simp [extsOk] at h

theorem extsOk_bytes (hp : Flat.Heap) : ∀ {as as' : List ExtArg}, extsOk M as as' = true →
    Flat.extBytes hp g as' = Flat.extBytes hp f as
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [extsOk, Bool.and_eq_true] at h
    have ih := extsOk_bytes hp h.2
    cases a <;> cases a' <;> simp only [extOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_and] at h
    all_goals first
      | (simp [Flat.extBytes, ih, opOk_eval hA h.1.1, opOk_eval hA h.1.2]; done)
      | (simp [Flat.extBytes, ih, opOk_eval hA h.1]; done)
      | (simp [Flat.extBytes, ih, h.1]; done)
      | (simp [Flat.extBytes, ih]; done)
  | [], _ :: _, h => by simp [extsOk] at h
  | _ :: _, [], h => by simp [extsOk] at h

theorem extsOk_caps : ∀ {as as' : List ExtArg}, extsOk M as as' = true →
    Flat.extCaps g as' = Flat.extCaps f as
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [extsOk, Bool.and_eq_true] at h
    have ih := extsOk_caps h.2
    cases a <;> cases a' <;> simp only [extOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_and] at h
    all_goals first
      | (simp [Flat.extCaps, ih, opOk_eval hA h.1.1, opOk_eval hA h.1.2]; done)
      | (simp [Flat.extCaps, ih, opOk_eval hA h.1]; done)
      | (simp [Flat.extCaps, ih, h.1]; done)
      | (simp [Flat.extCaps, ih]; done)
  | [], _ :: _, h => by simp [extsOk] at h
  | _ :: _, [], h => by simp [extsOk] at h

theorem extsOk_out : ∀ {as as' : List ExtArg}, extsOk M as as' = true →
    (Flat.extOutArg as').map (fun p => p.1.eval g) = (Flat.extOutArg as).map (fun p => p.1.eval f)
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [extsOk, Bool.and_eq_true] at h
    have ih := extsOk_out h.2
    cases a <;> cases a' <;> simp only [extOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_and] at h
    all_goals first
      | (simp [Flat.extOutArg, ih, opOk_eval hA h.1.1, opOk_eval hA h.1.2]; done)
      | (simp [Flat.extOutArg, ih, opOk_eval hA h.1]; done)
      | (simp [Flat.extOutArg, ih, h.1]; done)
      | (simp [Flat.extOutArg, ih]; done)
  | [], _ :: _, h => by simp [extsOk] at h
  | _ :: _, [], h => by simp [extsOk] at h

theorem extsOk_memOk (D : Nat) : ∀ {as as' : List ExtArg}, extsOk M as as' = true →
    Lin.extMemOk D g as' = Lin.extMemOk D f as
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [extsOk, Bool.and_eq_true] at h
    have ih := extsOk_memOk D h.2
    cases a <;> cases a' <;> simp only [extOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_and] at h
    all_goals first
      | (simp [Lin.extMemOk, ih, opOk_eval hA h.1.1, opOk_eval hA h.1.2]; done)
      | (simp [Lin.extMemOk, ih, opOk_eval hA h.1]; done)
      | (simp [Lin.extMemOk, ih, h.1]; done)
      | (simp [Lin.extMemOk, ih]; done)
  | [], _ :: _, h => by simp [extsOk] at h
  | _ :: _, [], h => by simp [extsOk] at h

/-- An extern call on related arguments has the same outcome. -/
theorem extRun_eq (ω : Oracle) (sym : String) (nr : Bool) {as as' : List ExtArg} (hp : Flat.Heap)
    (w : World) (h : extsOk M as as' = true) :
    Flat.extRun ω sym nr as' g hp w = Flat.extRun ω sym nr as f hp w := by
  have ho := extsOk_out hA h
  unfold Flat.extRun
  rw [extsOk_words hA h, extsOk_bytes hA hp h, extsOk_caps hA h]
  cases e : Flat.extOutArg as <;> cases e' : Flat.extOutArg as' <;> simp_all

end Ext

/-! ## The map lemmas -/

theorem sub_agree {M M₁ : LocMap} {f g : Frame} (hA : Agree M f g) (h : sub M₁ M = true) :
    Agree M₁ f g := by
  simp only [sub, List.all_eq_true, decide_eq_true_eq] at h
  exact fun p hp => hA p (h p hp)

theorem defOk_agree {M M₁ : LocMap} {f g : Frame} {x x' : Nat} {keep : Nat → Bool} {v : UInt64}
    (hA : Agree M f g) (h : defOk M M₁ x x' keep = true) (hk : ∀ l, keep l = true → g l = v) :
    Agree M₁ (f.set x v) (g.set x' v) := by
  simp only [defOk, List.all_eq_true] at h
  intro p hp
  have := h p hp
  by_cases h1 : p.1 = x
  · simp only [h1, ite_true, beq_iff_eq] at this
    simp [h1, this]
  · simp only [h1, ite_false, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      bne_iff_ne, ne_eq] at this
    rw [Frame.set_ne _ _ h1]
    by_cases h2 : p.2 = x'
    · rcases this.2 with h3 | h3
      · exact absurd h2 h3
      · rw [h2, Frame.set_same, ← hk _ h3, h2]; exact hA p this.1 ▸ (by rw [h2])
    · rw [Frame.set_ne _ _ h2]; exact hA p this.1

theorem resOk_agree {M M₁ : LocMap} {f g : Frame} {d d' n : Nat} (hA : Agree M f g)
    (h : resOk M M₁ d d' n = true) (vs : List UInt64) (hl : vs.length = n) :
    Agree M₁ (f.writes d vs) (g.writes d' vs) := by
  simp only [resOk, List.all_eq_true] at h
  intro p hp
  have := h p hp
  rw [Sel.writes_apply, Sel.writes_apply]
  by_cases h1 : d ≤ p.1 ∧ p.1 < d + n
  · simp only [h1, and_self, ite_true, beq_iff_eq] at this
    rw [ite_eq_left (by omega), ite_eq_left (by omega), this]
    congr 1; omega
  · simp only [h1, ite_false, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at this
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hA p this.1

theorem ofList_apply (os : List Operand) (f : Frame) (y : Nat) :
    Frame.ofList (os.map (Operand.eval f)) y = (os.getD y (.imm 0)).eval f := by
  simp only [Frame.ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases os[y]? <;> rfl

theorem argsOk_agree {M E : LocMap} {f g : Frame} {args args' : List Operand} (hA : Agree M f g)
    (h : argsOk M E args args' = true) :
    Agree E (Frame.ofList (args.map (Operand.eval f))) (Frame.ofList (args'.map (Operand.eval g))) := by
  simp only [argsOk, List.all_eq_true] at h
  intro p hp
  rw [ofList_apply, ofList_apply]
  exact opOk_eval hA (h p hp)

/-! ## What the checker established -/

theorem all2_spec {α β : Type} {F : Nat → α → β → Bool} :
    ∀ {k : Nat} {as : List α} {bs : List β}, all2 F k as bs = true →
      bs.length = as.length ∧ ∀ j a, as[j]? = some a → ∃ b, bs[j]? = some b ∧ F (k + j) a b = true
  | _, [], [], _ => ⟨rfl, fun _ _ h => by simp at h⟩
  | k, a :: as, b :: bs, h => by
    simp only [all2, Bool.and_eq_true] at h
    obtain ⟨hl, ih⟩ := all2_spec h.2
    refine ⟨by simp [hl], fun j a' hj => ?_⟩
    cases j with
    | zero => simp at hj; subst hj; exact ⟨b, rfl, by simpa using h.1⟩
    | succ j =>
      obtain ⟨b', h1, h2⟩ := ih j a' (by simpa using hj)
      exact ⟨b', by simpa using h1, by rw [show k + (j + 1) = k + 1 + j by omega]; exact h2⟩
  | _, [], _ :: _, h => by simp [all2] at h
  | _, _ :: _, [], h => by simp [all2] at h

variable {P P' : Prog} {maps : List (List LocMap)}

/-- The parts of an accepted check. -/
structure Checked (P P' : Prog) (maps : List (List LocMap)) : Prop where
  main : P'.main = P.main
  mem : P'.mem = P.mem
  len : P'.funs.length = P.funs.length
  fn : ∀ i fn, P.funs[i]? = some fn → ∃ fn', P'.funs[i]? = some fn' ∧ fnOk P maps i fn fn' = true
  wf : wfCheck P' = true

theorem checked_of (h : check P P' maps = true) : Checked P P' maps := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hm, hmem⟩, hf⟩, hw⟩ := h
  obtain ⟨hl, hk⟩ := all2_spec hf
  exact ⟨hm, hmem, hl, fun i fn h => by simpa using hk i fn h, hw⟩

theorem fnOk_spec {i : Nat} {fn fn' : Lin.Fn} (h : fnOk P maps i fn fn' = true) :
    fn'.ret.length = fn.ret.length ∧ fn'.code.length = fn.code.length ∧
      ∀ pc ins, fn.code[pc]? = some ins → ∃ ins', fn'.code[pc]? = some ins' ∧
        instrOk P maps i pc fn.ret fn'.ret ins ins' = true := by
  simp only [fnOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hr, hc⟩ := h
  obtain ⟨hl, hk⟩ := all2_spec hc
  exact ⟨hr.symm, hl, fun pc ins h => by simpa using hk pc ins h⟩

/-- What the frame check established: each target frame, in words, is no larger. -/
theorem frameOk_spec {k c : Nat} (h : frameOk k c P P' = true) {i : Nat} {fn fn' : Lin.Fn}
    (hf : P.funs[i]? = some fn) (hf' : P'.funs[i]? = some fn') : Sel.frameW k c fn'.frame ≤ fn.frame := by
  obtain ⟨-, hk⟩ := all2_spec h
  obtain ⟨b, hb, hok⟩ := hk i fn hf
  rw [hf'] at hb; cases hb
  simpa using hok

theorem Checked.retLen (hc : Checked P P' maps) (g : Nat) : retLen P' g = retLen P g := by
  unfold RegAlloc.retLen
  cases h : P.funs[g]? with
  | none =>
    have : P'.funs[g]? = none := by
      rw [List.getElem?_eq_none_iff] at h ⊢; rw [hc.len]; exact h
    simp [this]
  | some fn =>
    obtain ⟨fn', h', hok⟩ := hc.fn g fn h
    simp [h', (fnOk_spec hok).1]

/-! ## The relation -/

variable (P maps) in
/-- Two stacks of suspended activations are related when each pair has the same function and
return position and the map at the return position holds once the callee's results are written,
for every list of results of the callee's length. -/
def StackRel : Nat → List Lin.Act → List Lin.Act → Prop
  | _, [], [] => True
  | g, a :: st, b :: st' => b.fn = a.fn ∧ b.pc = a.pc ∧
      (∀ vs : List UInt64, vs.length = retLen P g →
        Agree (mapOf maps a.fn a.pc) (a.frame.writes a.dst vs) (b.frame.writes b.dst vs)) ∧
      StackRel a.fn st st'
  | _, _, _ => False

variable (P maps) in
/-- The lock-step relation of a source state and a target state. -/
structure Rel (s t : Lin.State) : Prop where
  fn : t.fn = s.fn
  pc : t.pc = s.pc
  mem : t.mem = s.mem
  world : t.world = s.world
  clock : t.clock = s.clock
  frame : Agree (mapOf maps s.fn s.pc) s.frame t.frame
  stack : StackRel P maps s.fn s.stack t.stack

theorem rel_init (hc : Checked P P' maps) : Rel P maps P.init P'.init :=
  ⟨by simp [Lin.Prog.init, hc.main], rfl, rfl, rfl, rfl, fun _ _ => rfl, trivial⟩

/-- The target instruction's memory access is in the data region iff the source's is. -/
theorem memOk_eq {M : LocMap} {f g : Frame} (hA : Agree M f g) (D : Nat) {i pc : Nat}
    {ret ret' : List Operand} {ins ins' : Instr}
    (hM : M = mapOf maps i pc) (h : instrOk P maps i pc ret ret' ins ins' = true) :
    ins'.memOk D g = ins.memOk D f := by
  subst hM
  cases ins <;> cases ins' <;> simp only [instrOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h <;>
    simp only [Lin.Instr.memOk]
  case load.load => rw [opOk_eval hA h.1.2, h.1.1.1, h.1.1.2]
  case store.store => rw [opOk_eval hA h.1.1.2, h.1.1.1.1, h.1.1.1.2]
  case ext.ext => exact extsOk_memOk hA D h.1.2

/-- A source step from related states is matched by one target step to related states. -/
theorem step_sim (hc : Checked P P' maps) {κ : CostModel} {ω : Oracle} {s t s' : Lin.State}
    (hR : Rel P maps s t) (hs : Lin.step κ P ω s = some s') :
    ∃ t', Lin.step κ P' ω t = some t' ∧ Rel P maps s' t' := by
  obtain ⟨tfn, tpc, tfr, tst, tmem, tw, tclk⟩ := t
  obtain ⟨hfn, hpc, hmem, hw, hclk, hA, hS⟩ := hR
  simp only at hfn hpc hmem hw hclk hA hS
  subst hfn hpc hmem hw hclk
  cases hh : s.world.halted
  case true =>
    rw [Lin.step_halted κ P ω s hh] at hs; cases hs
    exact ⟨_, Lin.step_halted κ P' ω _ hh, ⟨rfl, rfl, rfl, rfl, rfl, hA, hS⟩⟩
  case false =>
  have hf : ∃ fn, P.funs[s.fn]? = some fn := by
    cases h : P.funs[s.fn]? with
    | none => simp [Lin.step, hh, h] at hs
    | some fn => exact ⟨fn, rfl⟩
  obtain ⟨fn, hf⟩ := hf
  obtain ⟨ins, hi, hmo, hex⟩ := Sel.step_fetch_inv hh hf hs
  obtain ⟨fn', hf', hok⟩ := hc.fn _ _ hf
  obtain ⟨hrl, -, hcode⟩ := fnOk_spec hok
  obtain ⟨ins', hi', hins⟩ := hcode _ _ hi
  have hmo' : ins'.memOk P'.mem tfr = true := by
    rw [hc.mem, memOk_eq hA P.mem rfl hins]; exact hmo
  rw [Lin.step_fetch (s := ⟨s.fn, s.pc, tfr, tst, s.mem, s.world, s.clock⟩) hh hf' hi' hmo']
  clear hmo hmo' hs
  cases ins <;> cases ins' <;> simp only [instrOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hins <;>
    simp only [Lin.exec, Option.some.injEq] at hex
  case mov.mov x a x' a' =>
    subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hS⟩
    simp only [opOk_eval hA hins.1]
    exact defOk_agree hA hins.2 fun l hl => by
      simp only [beq_iff_eq] at hl; rw [← opOk_eval hA hins.1, hl]; rfl
  case bin.bin op x a b op' x' a' b' =>
    subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hS⟩
    simp only [opOk_eval hA hins.1.1.2, opOk_eval hA hins.1.2, hins.1.1.1]
    exact defOk_agree hA hins.2 fun _ h => by cases h
  case load.load w x a off w' x' a' off' =>
    subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hS⟩
    simp only [opOk_eval hA hins.1.2, hins.1.1.1, hins.1.1.2]
    exact defOk_agree hA hins.2 fun _ h => by cases h
  case store.store w a off b w' a' off' b' =>
    subst hex
    refine ⟨_, rfl, rfl, rfl, ?_, rfl, rfl, sub_agree hA hins.2, hS⟩
    simp only [opOk_eval hA hins.1.1.2, opOk_eval hA hins.1.2, hins.1.1.1.1, hins.1.1.1.2]
  case jmp.jmp l l' =>
    subst hex
    obtain ⟨hl, h1⟩ := hins
    subst hl
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, sub_agree hA h1, hS⟩
  case jz.jz c l c' l' =>
    subst hex
    obtain ⟨⟨⟨hl, hcc⟩, h1⟩, h2⟩ := hins
    subst hl
    refine ⟨_, rfl, rfl, by simp only [opOk_eval hA hcc], rfl, rfl, rfl, ?_, hS⟩
    split
    · exact sub_agree hA h1
    · exact sub_agree hA h2
  case call.call g args d g' args' d' =>
    subst hex
    obtain ⟨⟨hg, ha⟩, hr⟩ := hins
    subst hg
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, argsOk_agree hA ha,
      ⟨rfl, rfl, fun vs hl => resOk_agree hA hr vs hl, hS⟩⟩
  case ret.ret =>
    split at hex
    · cases hex
    · rename_i a st hst
      cases hex
      rw [hst] at hS
      cases tst with
      | nil => exact hS.elim
      | cons b st' =>
        obtain ⟨hbf, hbp, hW, hS'⟩ := hS
        refine ⟨_, rfl, by simp [hbf], by simp [hbp], rfl, rfl, rfl, ?_, hS'⟩
        rw [opsOk_eval hA hins]
        refine hW _ ?_
        simp [RegAlloc.retLen, hf]
  case ext.ext sym nr x args sym' nr' x' args' =>
    subst hex
    obtain ⟨⟨⟨hsy, hnr⟩, ha⟩, hd⟩ := hins
    subst hsy hnr
    refine ⟨_, rfl, ?_⟩
    rw [extRun_eq hA ω sym nr s.mem s.world ha]
    exact ⟨rfl, rfl, rfl, rfl, rfl, defOk_agree hA hd (fun _ h => by cases h), hS⟩
  case tick.tick t t' =>
    subst hex
    obtain ⟨ht, h1⟩ := hins
    subst ht
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, sub_agree hA h1, hS⟩

/-! ## The stack bound and well-formedness of the target -/

theorem callMax_le (acc : List Nat) (B : Nat) :
    ∀ (code : List Instr), (∀ g args d, Instr.call g args d ∈ code → acc.getD g 0 ≤ B) →
      Lin.callMax acc code ≤ B
  | [], _ => Nat.zero_le _
  | i :: is, h => by
    have ih := callMax_le acc B is fun g a d hm => h g a d (List.mem_cons_of_mem _ hm)
    cases i <;> simp only [Lin.callMax] <;> try exact ih
    exact Nat.max_le.2 ⟨h _ _ _ List.mem_cons_self, ih⟩

/-- Every call of the target code is a call of the same function in the source code. -/
theorem call_of_target {i : Nat} {fn fn' : Lin.Fn} (h : fnOk P maps i fn fn' = true) {g : Nat}
    {args' : List Operand} {d' : Nat} (hm : Instr.call g args' d' ∈ fn'.code) :
    ∃ args d, Instr.call g args d ∈ fn.code := by
  obtain ⟨-, hl, hk⟩ := fnOk_spec h
  obtain ⟨pc, hpc⟩ := List.mem_iff_getElem?.1 hm
  have hlt : pc < fn.code.length := by
    rw [← hl]; exact (List.getElem?_eq_some_iff.1 hpc).1
  obtain ⟨ins', h1, h2⟩ := hk pc _ (List.getElem?_eq_getElem hlt)
  rw [hpc] at h1; cases h1
  cases hi : fn.code[pc] <;> rw [hi] at h2 <;> simp [instrOk] at h2
  rename_i g₀ args d
  exact ⟨args, d, h2.1.1 ▸ hi ▸ List.getElem_mem hlt⟩

/-- The target's stack need of every function, counted in the words of `(k, c)`, is at most the
source's. -/
theorem needs_le {k c : Nat} (hc : Checked P P' maps) (hF : frameOk k c P P' = true) (φ : FrameModel)
    (i : Nat) : (Lin.needs (φ.words k c) P'.funs).getD i 0 ≤ (Lin.needs φ P.funs).getD i 0 := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
  cases hf : P.funs[i]? with
  | none =>
    have : P'.funs[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hf ⊢; rw [hc.len]; exact hf
    have hn : (Lin.needs (φ.words k c) P'.funs)[i]? = none := by
      rw [List.getElem?_eq_none_iff, Lin.needs_length]; exact List.getElem?_eq_none_iff.1 this
    simp [List.getD_eq_getElem?_getD, hn]
  | some fn =>
    obtain ⟨fn', hf', hok⟩ := hc.fn i fn hf
    simp only [List.getD_eq_getElem?_getD, Lin.needs_get φ _ _ _ hf,
      Lin.needs_get (φ.words k c) _ _ _ hf', Option.getD_some, Lin.fnNeed]
    have h1 : (φ.words k c).frame fn'.frame ≤ φ.frame fn.frame := φ.mono (frameOk_spec hF hf hf')
    have h2 : Lin.callMax ((Lin.needs (φ.words k c) P'.funs).take i) fn'.code ≤
        Lin.callMax ((Lin.needs φ P.funs).take i) fn.code := by
      refine callMax_le _ _ _ fun g args' d' hm => ?_
      obtain ⟨args, d, hm'⟩ := call_of_target hok hm
      refine Nat.le_trans ?_ (Lin.callMax_ge _ _ g args d hm')
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      split
      · have := ih g (by omega)
        simpa [List.getD_eq_getElem?_getD] using this
      · simp
    omega

/-- The allocated program's static stack bound, counted in the words of `(k, c)`, is at most the
source's, for every frame model. -/
theorem check_stackBytes {k c : Nat} (h : check P P' maps = true) (hF : frameOk k c P P' = true)
    (φ : FrameModel) : P'.stackBytes (φ.words k c) ≤ P.stackBytes φ := by
  have hc := checked_of h
  unfold Lin.Prog.stackBytes; rw [hc.main]; exact needs_le hc hF φ _

theorem opsBelow_sound {ops : List Operand} {n : Nat} (h : opsBelow ops n = true) :
    Lin.OpsBelow ops n := by
  intro x hx
  simp only [opsBelow, List.all_eq_true] at h
  simpa using h _ hx

theorem instrWf_sound {Q : Prog} {i fr len : Nat} {ins : Instr} (h : instrWf Q i fr len ins = true) :
    ins.Wf Q i fr len := by
  cases ins <;> simp only [instrWf, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    simp only [Lin.Instr.Wf]
  case mov => exact ⟨h.1, opsBelow_sound h.2⟩
  case bin => exact ⟨h.1, opsBelow_sound h.2⟩
  case load => exact ⟨h.1, opsBelow_sound h.2⟩
  case store => exact opsBelow_sound h
  case jmp => exact h
  case jz => exact ⟨opsBelow_sound h.1, h.2⟩
  case call g args d =>
    obtain ⟨⟨hg, ha⟩, hr⟩ := h
    refine ⟨hg, opsBelow_sound ha, ?_⟩
    split at hr
    · rename_i gf hgf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      exact ⟨gf, hgf, hr⟩
    · cases hr
  case ext sym nr x args =>
    obtain ⟨hx, ha⟩ := h
    simp only [List.all_eq_true] at ha
    refine ⟨hx, fun o ho => ?_, fun a l ho => ?_, fun a l ho => ?_⟩
    · exact opsBelow_sound (by simpa using ha _ ho)
    · exact opsBelow_sound (by simpa using ha _ ho)
    · exact opsBelow_sound (by simpa using ha _ ho)

theorem wfCheck_sound {Q : Prog} (h : wfCheck Q = true) : Q.Wf := by
  simp only [wfCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, hf⟩ := h
  obtain ⟨-, hk⟩ := all2_spec hf
  refine ⟨hm, fun i fn hfn => ?_⟩
  obtain ⟨_, -, hb⟩ := hk i fn hfn
  simp only [Nat.zero_add, Bool.and_eq_true, List.all_eq_true] at hb
  exact ⟨opsBelow_sound hb.1, fun ins hi => instrWf_sound (hb.2 ins hi)⟩

/-- The allocated program is well formed. -/
theorem check_wf (h : check P P' maps = true) : P'.Wf := wfCheck_sound (checked_of h).wf


/-- The checker's relation at a reactor-step boundary: the target is at the same `jz` on the
same constant, with an empty stack. -/
theorem rel_boundary (hc : Checked P P' maps) {s t : Lin.State} (hR : Rel P maps s t)
    (hs : s.stack = []) (hb : ∃ fn l, P.funs[s.fn]? = some fn ∧ fn.code[s.pc]? = some (.jz (.imm 1) l)) :
    t.stack = [] ∧ ∃ fn l, P'.funs[t.fn]? = some fn ∧ fn.code[t.pc]? = some (.jz (.imm 1) l) := by
  obtain ⟨fn, l, hf, hi⟩ := hb
  have hst := hR.stack
  rw [hs] at hst
  refine ⟨by cases h : t.stack with
    | nil => rfl
    | cons _ _ => rw [h] at hst; exact hst.elim, ?_⟩
  obtain ⟨fn', hf', hok⟩ := hc.fn _ _ hf
  obtain ⟨ins', hi', hins⟩ := (fnOk_spec hok).2.2 _ _ hi
  cases ins' <;> simp only [instrOk, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hins
  rename_i c' l'
  obtain ⟨⟨⟨hl, hc'⟩, -⟩, -⟩ := hins
  cases c' <;> simp only [opOk, beq_iff_eq, Bool.false_eq_true] at hc'
  subst hc' hl
  exact ⟨fn', l, by rw [hR.fn]; exact hf', by rw [hR.pc]; exact hi'⟩

/-- An allocation that the checker accepts is a lock-step refinement of the source, whose stack
bound in the words of `(k, c)` is no larger when the frame check at `(k, c)` accepts it. -/
def lockOfCheck {k c : Nat} (h : check P P' maps = true) (hF : frameOk k c P P' = true) :
    Lock P P' k c where
  R := Rel P maps
  init := rel_init (checked_of h)
  step hR hs := step_sim (checked_of h) hR hs
  world h := h.world
  clock h := h.clock
  boundary hR hs hb := rel_boundary (checked_of h) hR hs hb
  stackBytes := check_stackBytes h hF
  wf _ := check_wf h

/-- The allocation pass is a lock-step refinement, whose stack bound is no larger in the frame
words of its classes. Its result is the checked allocation, or the source itself when the checker
or the frame check refuses the allocator's proposal. -/
def allocOrId_lock (cl : Alloc.Classes) (P : Lin.Prog) : Lock P (Alloc.allocOrId cl P) cl.k cl.c := by
  unfold Alloc.allocOrId
  rcases Alloc.allocate cl P with ⟨P', maps, _⟩
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact lockOfCheck h.1 h.2
  · exact Lock.id P _ _

end Millipede.RegAlloc
