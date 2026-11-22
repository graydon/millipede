import Millipede.Compile.Linearize
import Millipede.Top.Statement

/-!
# Correctness of `linearize`

This module proves that `linearize` is a forward simulation from Flat to Lin with factor 1. For
every cost model `κ`, oracle `ω` and Flat program `fp`, `linearize_sim fp M ω κ` relates `fp.init`
to `(linearize fp M).init`. Related states have equal frames, memories, worlds and clocks, so the
traces agree at every matched point and Lin takes exactly Flat's ticks.

The matching relation is built from four predicates. `CodeAt P f pc is` says that function `f` of
`P` exists and its code has `is` at position `pc`. `Compiled P f pc s` says that the code of `s`
sits at `(f, pc)`, compiled against some function list whose extension is a prefix of `P.funs`.
`MatchK P f k pc stk` says that running Lin from position `pc` of `f` with stack `stk` does what the
Flat continuation `k` does, possibly after a chain of jumps. `Rel P s t` says that the data are
equal, `s.cur` is compiled at `(t.fn, t.pc)` and `s.kont` is matched at the end of it.

Flat steps that Lin does not need, which are entering a `seq`, falling into the next statement and
entering a `while`, are matched by zero Lin steps, and the measure `measure s`, the size of the
current statement plus the pending `seq` statements, then strictly decreases. Every other Flat
step is matched by one Lin instruction, possibly preceded by jumps.

Lin's `load` and `store` are stuck outside a program's data region, while Flat's are not. The
step lemma `sim_step` therefore asks that the Flat state's access lie in the region, and
`linSimI P ω κ Inv` is the simulation along Flat states satisfying an invariant `Inv` that is
closed under steps and implies it. `linearize_sim` instantiates `Inv` with reachability.

The module also proves that linearized programs have no recursion, that they are well formed when
every slot, jump target, argument count and result range of the Flat program fits the declared
frames, and that the static Lin stack bound is exactly `φ.frame fp.frame` plus the Flat call
measure.

See doc/design/compiler.md.
-/

namespace Millipede.Lin

open Flat (Stmt Kont Operand)

/-! ## Code placement -/

/-- Function `f` of `P` exists and has the instructions `is` at position `pc`. -/
def CodeAt (P : Prog) (f pc : Nat) (is : List Instr) : Prop :=
  ∃ fn, P.funs[f]? = some fn ∧ ∃ post, fn.code.drop pc = is ++ post

theorem CodeAt.append {P : Prog} {f pc : Nat} {a b : List Instr} (h : CodeAt P f pc (a ++ b)) :
    CodeAt P f pc a ∧ CodeAt P f (pc + a.length) b := by
  obtain ⟨fn, hf, post, hp⟩ := h
  refine ⟨⟨fn, hf, b ++ post, by rw [hp, List.append_assoc]⟩, fn, hf, post, ?_⟩
  rw [← List.drop_drop, hp, List.append_assoc, List.drop_left' rfl]

theorem CodeAt.fetch {P : Prog} {f pc : Nat} {i : Instr} {rest : List Instr}
    (h : CodeAt P f pc (i :: rest)) : ∃ fn, P.funs[f]? = some fn ∧ fn.code[pc]? = some i := by
  obtain ⟨fn, hf, post, hp⟩ := h
  refine ⟨fn, hf, ?_⟩
  rw [← List.head?_drop, hp]; rfl

theorem CodeAt.fetch1 {P : Prog} {f pc : Nat} {i : Instr}
    (h : CodeAt P f pc [i]) : ∃ fn, P.funs[f]? = some fn ∧ fn.code[pc]? = some i := h.fetch

theorem CodeAt.valid {P : Prog} {f pc : Nat} {is : List Instr} (h : CodeAt P f pc is) :
    ∃ fn, P.funs[f]? = some fn := by obtain ⟨fn, hf, _⟩ := h; exact ⟨fn, hf⟩

theorem CodeAt.nil {P : Prog} {f : Nat} (h : ∃ fn, P.funs[f]? = some fn) (pc : Nat) :
    CodeAt P f pc [] := by
  obtain ⟨fn, hf⟩ := h; exact ⟨fn, hf, _, rfl⟩

/-- The code of `s` sits at `(f, pc)` of `P`, compiled against some function list whose
extension by `s`'s callees is a prefix of `P.funs`. -/
def Compiled (P : Prog) (f pc : Nat) (s : Stmt) : Prop :=
  ∃ fs, (linS s pc fs).2 <+: P.funs ∧ CodeAt P f pc (linS s pc fs).1

theorem Compiled.valid {P : Prog} {f pc : Nat} {s : Stmt} (h : Compiled P f pc s) :
    ∃ fn, P.funs[f]? = some fn := by obtain ⟨_, _, hc⟩ := h; exact hc.valid

theorem Compiled.skip {P : Prog} {f : Nat} (h : ∃ fn, P.funs[f]? = some fn) (pc : Nat) :
    Compiled P f pc .skip := ⟨[], List.nil_prefix, CodeAt.nil h pc⟩

theorem Compiled.seq {P : Prog} {f pc : Nat} {a b : Stmt} (h : Compiled P f pc (.seq a b)) :
    Compiled P f pc a ∧ Compiled P f (pc + Stmt.len a) b := by
  obtain ⟨fs, hp, hc⟩ := h
  simp only [linS] at hp hc
  have hc' := hc.append
  rw [linS_length] at hc'
  exact ⟨⟨fs, (linS_prefix b _ _).trans hp, hc'.1⟩, ⟨_, hp, hc'.2⟩⟩

theorem Compiled.ite {P : Prog} {f pc : Nat} {c : Operand} {t e : Stmt}
    (h : Compiled P f pc (.ite c t e)) :
    CodeAt P f pc [.jz c (pc + Stmt.len t + 2)] ∧ Compiled P f (pc + 1) t ∧
    CodeAt P f (pc + 1 + Stmt.len t) [.jmp (pc + Stmt.len t + 2 + Stmt.len e)] ∧
    Compiled P f (pc + Stmt.len t + 2) e := by
  obtain ⟨fs, hp, hc⟩ := h
  simp only [linS] at hp hc
  obtain ⟨h₁, h₂⟩ := hc.append
  obtain ⟨h₃, h₄⟩ := h₁.append
  obtain ⟨h₅, h₆⟩ := h₃.append
  simp only [List.length_append, List.length_singleton, linS_length] at h₂ h₄ h₆
  rw [← Nat.add_assoc] at h₄
  rw [show pc + (1 + Stmt.len t + 1) = pc + Stmt.len t + 2 by omega] at h₂
  exact ⟨h₅, ⟨fs, (linS_prefix e _ _).trans hp, h₆⟩, h₄, ⟨_, hp, h₂⟩⟩

theorem Compiled.while {P : Prog} {f L : Nat} {pre : Stmt} {c : Operand} {body : Stmt}
    (h : Compiled P f L (.while pre c body)) :
    Compiled P f L pre ∧
    CodeAt P f (L + Stmt.len pre) [.jz c (L + Stmt.len (.while pre c body))] ∧
    Compiled P f (L + Stmt.len pre + 1) body ∧
    CodeAt P f (L + Stmt.len pre + 1 + Stmt.len body) [.jmp L] := by
  obtain ⟨fs, hp, hc⟩ := h
  simp only [linS] at hp hc
  obtain ⟨h₁, h₂⟩ := hc.append
  obtain ⟨h₃, h₄⟩ := h₁.append
  obtain ⟨h₅, h₆⟩ := h₃.append
  simp only [List.length_append, List.length_singleton, linS_length] at h₂ h₄ h₆
  refine ⟨⟨fs, (linS_prefix body _ _).trans hp, h₅⟩, ?_, ⟨_, hp, h₄⟩, ?_⟩
  · simp only [Stmt.len]; rw [show L + (Stmt.len pre + Stmt.len body + 2) =
      L + Stmt.len pre + Stmt.len body + 2 by omega]; exact h₆
  · rw [show L + Stmt.len pre + 1 + Stmt.len body = L + (Stmt.len pre + 1 + Stmt.len body) by
      omega]; exact h₂

/-- A one-instruction statement sits at `(f, pc)` as that instruction. -/
theorem Compiled.single {P : Prog} {f pc : Nat} {s : Stmt} {i : Instr}
    (hs : ∀ fs, (linS s pc fs).1 = [i]) (h : Compiled P f pc s) : CodeAt P f pc [i] := by
  obtain ⟨fs, _, hc⟩ := h; rw [hs] at hc; exact hc

theorem Compiled.call {P : Prog} {f pc : Nat} {name : String} {fr : Nat} {body : Stmt}
    {ret args : List Operand} {d : Nat} (h : Compiled P f pc (.call name fr body ret args d)) :
    ∃ g fn, CodeAt P f pc [.call g args d] ∧ P.funs[g]? = some fn ∧ fn.ret = ret ∧
      Compiled P g 0 body ∧ CodeAt P g (Stmt.len body) [.ret] := by
  obtain ⟨fs, hp, hc⟩ := h
  simp only [linS] at hp hc
  obtain ⟨r, hr⟩ := hp
  have hg : P.funs[(linS body 0 fs).2.length]? =
      some ⟨name, fr, (linS body 0 fs).1 ++ [.ret], ret⟩ := by
    rw [← hr]; simp
  refine ⟨_, _, hc, hg, rfl, ⟨fs, ⟨[_] ++ r, by rw [← hr, List.append_assoc]⟩,
    ⟨_, hg, [.ret], by simp⟩⟩, ⟨_, hg, [], ?_⟩⟩
  simp only [List.append_nil]
  rw [← linS_length body 0 fs]; exact List.drop_left' rfl

/-! ## Continuations -/

/-- Lin from `(f, pc)` with stack `stk` matches the Flat continuation `k`. -/
inductive MatchK (P : Prog) : Nat → List Kont → Nat → List Act → Prop
  /-- The end of `main` is a self-jump, at which the finished Flat program stutters. -/
  | stop {f pc : Nat} : CodeAt P f pc [.jmp pc] → MatchK P f [] pc []
  /-- Next, run `b`, which is compiled here. -/
  | seq {f pc : Nat} {b : Stmt} {k : List Kont} {stk : List Act} :
      Compiled P f pc b → MatchK P f k (pc + Stmt.len b) stk → MatchK P f (.seq b :: k) pc stk
  /-- The `pre` of the `while` compiled at `L` has run, and its test comes next. -/
  | loop {f pc L : Nat} {pre : Stmt} {c : Operand} {body : Stmt} {k : List Kont}
      {stk : List Act} : pc = L + Stmt.len pre → Compiled P f L (.while pre c body) →
      MatchK P f k (L + Stmt.len (.while pre c body)) stk →
      MatchK P f (.loop pre c body :: k) pc stk
  /-- The callee's body has finished, and it returns. -/
  | ret {f pc g rpc : Nat} {fn : Fn} {ops : List Operand} {d : Nat} {saved : Flat.Frame}
      {k : List Kont} {stk : List Act} : P.funs[f]? = some fn → fn.ret = ops →
      CodeAt P f pc [.ret] → MatchK P g k rpc stk →
      MatchK P f (.ret ops d saved :: k) pc (⟨g, rpc, saved, d⟩ :: stk)
  /-- A jump comes first. -/
  | jmp {f pc l : Nat} {k : List Kont} {stk : List Act} :
      CodeAt P f pc [.jmp l] → MatchK P f k l stk → MatchK P f k pc stk

theorem MatchK.valid {P : Prog} {f : Nat} {k : List Kont} {pc : Nat} {stk : List Act}
    (h : MatchK P f k pc stk) : ∃ fn, P.funs[f]? = some fn := by
  cases h with
  | stop h => exact h.valid
  | seq h _ => exact h.valid
  | loop _ h _ => exact h.valid
  | ret h _ _ _ => exact ⟨_, h⟩
  | jmp h _ => exact h.valid

/-- What `MatchK` says once the leading jumps have been taken. -/
def Head (P : Prog) (f : Nat) : List Kont → Nat → List Act → Prop
  | [], pc, stk => stk = [] ∧ CodeAt P f pc [.jmp pc]
  | .seq b :: k, pc, stk => Compiled P f pc b ∧ MatchK P f k (pc + Stmt.len b) stk
  | .loop pre c body :: k, pc, stk => ∃ L, pc = L + Stmt.len pre ∧
      Compiled P f L (.while pre c body) ∧ MatchK P f k (L + Stmt.len (.while pre c body)) stk
  | .ret ops d saved :: k, pc, stk => ∃ fn g rpc st, P.funs[f]? = some fn ∧ fn.ret = ops ∧
      CodeAt P f pc [.ret] ∧ stk = ⟨g, rpc, saved, d⟩ :: st ∧ MatchK P g k rpc st

/-! ## Running Lin -/

section Run

variable {κ : CostModel} {P : Prog} {ω : Oracle}

/-- `t'` is reached from `t` in exactly `n` Lin steps. -/
abbrev Steps (κ : CostModel) (P : Prog) (ω : Oracle) (t : State) (n : Nat) (t' : State) : Prop :=
  (sem κ P).run ω t n = some t'

theorem Steps.trans {t₁ t₂ t₃ : State} {m n : Nat} (h₁ : Steps κ P ω t₁ m t₂)
    (h₂ : Steps κ P ω t₂ n t₃) : Steps κ P ω t₁ (m + n) t₃ := by
  unfold Steps at *; rw [Sem.run_add_of h₁]; exact h₂

theorem Steps.one {t t' : State} (h : step κ P ω t = some t') : Steps κ P ω t 1 t' :=
  Sem.run_one h

/-- Takes the leading jumps of a matched continuation. -/
theorem MatchK.unjmp {f : Nat} {k : List Kont} {pc : Nat} {stk : List Act}
    (h : MatchK P f k pc stk) :
    ∀ t : State, t.fn = f → t.pc = pc → t.stack = stk → t.world.halted = false →
      ∃ n pc', Steps κ P ω t n { t with pc := pc' } ∧ Head P f k pc' stk := by
  induction h with
  | stop h =>
    intro t _ hp _ _; exact ⟨0, t.pc, rfl, rfl, by rw [hp]; exact h⟩
  | seq h₁ h₂ =>
    intro t _ hp _ _; exact ⟨0, t.pc, rfl, by rw [hp]; exact ⟨h₁, h₂⟩⟩
  | loop h₀ h₁ h₂ =>
    intro t _ hp _ _; exact ⟨0, t.pc, rfl, _, by rw [hp]; exact h₀, h₁, h₂⟩
  | ret h₀ h₁ h₂ h₃ =>
    intro t _ hp _ _
    exact ⟨0, t.pc, rfl, _, _, _, _, h₀, h₁, by rw [hp]; exact h₂, rfl, h₃⟩
  | @jmp f pc l k stk hc _ ih =>
    intro t hf hp hs hw
    obtain ⟨fn, hfn, hi⟩ := hc.fetch1
    have h1 : step κ P ω t = some { t with pc := l } := by
      rw [step_fetch hw (by rw [hf]; exact hfn) (by rw [hp]; exact hi) rfl]; rfl
    obtain ⟨n, pc', hn, hh⟩ := ih { t with pc := l } hf rfl hs hw
    exact ⟨1 + n, pc', (Steps.one h1).trans hn, hh⟩

theorem step_single {t : State} {i : Instr} (hw : t.world.halted = false)
    (hc : CodeAt P t.fn t.pc [i]) (hm : i.memOk P.mem t.frame = true) :
    ∃ fn, step κ P ω t = exec κ ω fn i t := by
  obtain ⟨fn, hf, hi⟩ := hc.fetch1
  exact ⟨fn, step_fetch hw hf hi hm⟩

end Run

/-! ## The simulation relation -/

/-- The size of a Flat statement, for the stuttering measure. -/
def Stmt.size : Stmt → Nat
  | .seq a b => Stmt.size a + Stmt.size b + 1
  | .ite _ t e => Stmt.size t + Stmt.size e + 1
  | .while pre _ body => Stmt.size pre + Stmt.size body + 2
  | _ => 1

/-- Sizes of the statements still pending in `seq` continuations. -/
def kontSize : List Kont → Nat
  | [] => 0
  | .seq b :: k => Stmt.size b + kontSize k
  | _ :: k => kontSize k

/-- The stuttering measure: it decreases on every Flat step that Lin matches with no step. -/
def measure (s : Flat.State) : Nat := Stmt.size s.cur + kontSize s.kont

/-- Flat state `s` is matched by Lin state `t` in program `P` when their data are equal, `s.cur` is
compiled at `(t.fn, t.pc)` and `s.kont` is matched after it. -/
structure Rel (P : Prog) (s : Flat.State) (t : State) : Prop where
  frame : t.frame = s.frame
  mem : t.mem = s.mem
  world : t.world = s.world
  clock : t.clock = s.clock
  cur : Compiled P t.fn t.pc s.cur
  kont : MatchK P t.fn s.kont (t.pc + Stmt.len s.cur) t.stack

/-- The memory access that Flat state `s` is about to make, if any, lies in the data region
`[0, M)`. -/
def MemIn (M : Nat) (s : Flat.State) : Prop :=
  match s.cur with
  | .load w _ a off => inData M (a.eval s.frame + off) w = true
  | .store w a off _ => inData M (a.eval s.frame + off) w = true
  | .ext _ _ _ args => extMemOk M s.frame args = true
  | _ => True

/-- One Flat step is matched. From related states, Lin takes `n` steps to a state related to
Flat's successor, and if `n = 0` the measure decreases. The Flat state's memory access, if any,
must lie in `P`'s data region. -/
theorem sim_step (κ : CostModel) (ω : Oracle) (P : Prog) (s : Flat.State) (t : State)
    (h : Rel P s t) (hmi : MemIn P.mem s) :
    ∃ n t', Steps κ P ω t n t' ∧ Rel P (Flat.next κ ω s) t' ∧
      (0 < n ∨ measure (Flat.next κ ω s) < measure s) := by
  obtain ⟨cur, kont, frame, mem, world, clock⟩ := s
  obtain ⟨fn, pc, tframe, stk, tmem, tworld, tclock⟩ := t
  obtain ⟨hf, hm, hw, hc, hcur, hk⟩ := h
  simp only at hf hm hw hc hcur hk
  subst hf hm hw hc
  cases hh : tworld.halted with
  | true =>
    refine ⟨1, _, Steps.one (step_halted κ P ω _ hh), ?_, Or.inl Nat.one_pos⟩
    simp only [Flat.next, hh, ite_true]
    exact ⟨rfl, rfl, rfl, rfl, hcur, hk⟩
  | false =>
  simp only [Flat.next, hh, Bool.false_eq_true, ite_false]
  have hv := hcur.valid
  have stepAt' : ∀ {pc' : Nat} {stk' : List Act} {i : Instr}, CodeAt P fn pc' [i] →
      i.memOk P.mem tframe = true →
      ∃ fnr, step κ P ω ⟨fn, pc', tframe, stk', tmem, tworld, tclock⟩ =
        exec κ ω fnr i ⟨fn, pc', tframe, stk', tmem, tworld, tclock⟩ :=
    fun hc hm => step_single (t := ⟨fn, _, tframe, _, tmem, tworld, tclock⟩) hh hc hm
  cases cur with
  | skip =>
    cases kont with
    | nil =>
      obtain ⟨n, pc', hn, hstk, hj⟩ := 
        hk.unjmp (κ := κ) (ω := ω) ⟨fn, pc, tframe, stk, tmem, tworld, tclock⟩ rfl rfl rfl
          hh
      subst hstk
      obtain ⟨fnr, hs⟩ := stepAt' (stk' := []) hj rfl
      refine ⟨n + 1, _, hn.trans (Steps.one (by rw [hs]; rfl)), ?_, Or.inl (Nat.succ_pos _)⟩
      exact ⟨rfl, rfl, rfl, rfl, Compiled.skip hv _, MatchK.stop hj⟩
    | cons k₀ k =>
      cases k₀ with
      | seq b =>
        obtain ⟨n, pc', hn, hb, hk'⟩ := 
          hk.unjmp (κ := κ) (ω := ω) ⟨fn, pc, tframe, stk, tmem, tworld, tclock⟩ rfl rfl rfl
            hh
        refine ⟨n, _, hn, ⟨rfl, rfl, rfl, rfl, hb, hk'⟩, Or.inr ?_⟩
        simp only [Flat.exec1, measure, kontSize, Stmt.size]; omega
      | loop pre c body =>
        obtain ⟨n, pc', hn, L, hpc, hW, hk'⟩ := 
          hk.unjmp (κ := κ) (ω := ω) ⟨fn, pc, tframe, stk, tmem, tworld, tclock⟩ rfl rfl rfl
            hh
        obtain ⟨_, hjz, hbody, hjmp⟩ := hW.while
        rw [← hpc] at hjz
        obtain ⟨fnr, hs⟩ := stepAt' hjz rfl
        refine ⟨n + 1, _, hn.trans (Steps.one (by rw [hs]; rfl)), ?_, Or.inl (Nat.succ_pos _)⟩
        simp only [Flat.exec1]
        by_cases hc0 : c.eval tframe = 0
        · simp only [hc0, ite_true]
          exact ⟨rfl, rfl, rfl, rfl, Compiled.skip hv _, hk'⟩
        · simp only [hc0, ite_false]
          refine ⟨rfl, rfl, rfl, rfl, by rw [hpc]; exact hbody, ?_⟩
          refine MatchK.jmp (l := L) (by rw [hpc]; exact hjmp) (MatchK.seq hW hk')
      | ret ops d saved =>
        obtain ⟨n, pc', hn, fnr, g, rpc, st, hfn, hret, hcode, hstk, hk'⟩ :=
          hk.unjmp (κ := κ) (ω := ω) ⟨fn, pc, tframe, stk, tmem, tworld, tclock⟩ rfl rfl
            rfl hh
        subst hstk
        obtain ⟨fn', hfn', hi⟩ := hcode.fetch1
        rw [hfn] at hfn'; cases hfn'
        have hs := step_fetch (κ := κ) (ω := ω) 
          (s := ⟨fn, pc', tframe, ⟨g, rpc, saved, d⟩ :: st, tmem, tworld, tclock⟩)
          hh hfn hi rfl
        refine ⟨n + 1, _, hn.trans (Steps.one (by rw [hs]; rfl)), ?_, Or.inl (Nat.succ_pos _)⟩
        simp only [Flat.exec1]
        exact ⟨by simp [hret], rfl, rfl, rfl, Compiled.skip hk'.valid _, hk'⟩
  | seq a b =>
    obtain ⟨ha, hb⟩ := hcur.seq
    refine ⟨0, _, rfl, ⟨rfl, rfl, rfl, rfl, ha, MatchK.seq hb ?_⟩, Or.inr ?_⟩
    · simp only [Stmt.len] at hk; rw [Nat.add_assoc]; exact hk
    · simp only [Flat.exec1, measure, kontSize, Stmt.size]; omega
  | mov _ _ | bin _ _ _ _ | load _ _ _ _ | store _ _ _ _ | ext _ _ _ _ | tick _ =>
    obtain ⟨fnr, hs⟩ := stepAt' (hcur.single (fun _ => rfl)) (by first | rfl | exact hmi)
    exact ⟨1, _, Steps.one (by rw [hs]; rfl), ⟨rfl, rfl, rfl, rfl, Compiled.skip hv _, hk⟩,
      Or.inl Nat.one_pos⟩
  | ite c a b =>
    obtain ⟨hjz, ha, hjmp, hb⟩ := hcur.ite
    obtain ⟨fnr, hs⟩ := stepAt' hjz rfl
    refine ⟨1, _, Steps.one (by rw [hs]; rfl), ?_, Or.inl Nat.one_pos⟩
    simp only [Flat.exec1]
    have hk2 : MatchK P fn kont (pc + Stmt.len a + 2 + Stmt.len b) stk := by
      simp only [Stmt.len] at hk
      rw [show pc + Stmt.len a + 2 + Stmt.len b = pc + (Stmt.len a + Stmt.len b + 2) by omega]
      exact hk
    by_cases hc0 : c.eval tframe = 0
    · simp only [hc0, ite_true]
      exact ⟨rfl, rfl, rfl, rfl, hb, hk2⟩
    · simp only [hc0, ite_false]
      exact ⟨rfl, rfl, rfl, rfl, ha, MatchK.jmp hjmp hk2⟩
  | «while» pre c body =>
    have ⟨hpre, _⟩ := hcur.while
    refine ⟨0, _, rfl, ⟨rfl, rfl, rfl, rfl, hpre, MatchK.loop rfl hcur hk⟩, Or.inr ?_⟩
    simp only [Flat.exec1, measure, kontSize, Stmt.size]; omega
  | call name fr body ret args d =>
    obtain ⟨g, fng, hcall, hg, hret, hbody, hretc⟩ := hcur.call
    obtain ⟨fnr, hs⟩ := stepAt' hcall rfl
    refine ⟨1, _, Steps.one (by rw [hs]; rfl), ⟨rfl, rfl, rfl, rfl, hbody, ?_⟩,
      Or.inl Nat.one_pos⟩
    exact MatchK.ret hg hret (by simp only [Flat.exec1, Nat.zero_add]; exact hretc) hk

/-! ## The forward simulation -/

/-- The forward simulation from Flat to Lin with factor 1, for any Lin program `P`, along Flat
states that satisfy an invariant `Inv`. `Inv` must be closed under Flat steps and put every memory
access in `P`'s data region. The index is the stuttering measure and the relation is `Rel P`
together with `Inv`. -/
def linSimI (P : Prog) (ω : Oracle) (κ : CostModel) (Inv : Flat.State → Prop)
    (hinv : ∀ s, Inv s → Inv (Flat.next κ ω s)) (hmem : ∀ s, Inv s → MemIn P.mem s) :
    FwdSim (Flat.sem κ) (Lin.sem κ P) ω where
  Idx := Nat
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  R i s t := i = measure s ∧ Rel P s t ∧ Inv s
  factor := 1
  events_eq := by
    intro _ s t h
    show s.world.events = t.world.events
    rw [h.2.1.world]
  step := by
    intro i s t s' h hs
    cases hs
    obtain ⟨n, t', hn, hR, hd⟩ := sim_step κ ω P s t h.2.1 (hmem s h.2.2)
    refine ⟨measure (Flat.next κ ω s), t', n, hn, ⟨rfl, hR, hinv s h.2.2⟩, ?_, ?_⟩
    · rcases hd with hd | hd
      · exact Or.inl hd
      · exact Or.inr (h.1 ▸ hd)
    · show t'.clock + 1 * s.clock ≤ t.clock + 1 * (Flat.next κ ω s).clock
      rw [hR.clock, h.2.1.clock]; omega

/-- The initial states of a Flat program and of its linearization are related. -/
theorem rel_init (fp : Flat.Prog) (M : Nat) : Rel (linearize fp M) fp.init (linearize fp M).init := by
  have hmain : (linearize fp M).funs[(linS fp.main 0 []).2.length]? =
      some ⟨"main", fp.frame, (linS fp.main 0 []).1 ++ [.jmp (Stmt.len fp.main)], []⟩ := by
    simp [linearize]
  refine ⟨rfl, rfl, rfl, rfl, ⟨[], List.prefix_append _ _, _, hmain, _, rfl⟩, ?_⟩
  refine MatchK.stop ⟨_, hmain, [], ?_⟩
  simp only [Flat.Prog.init, Prog.init, linearize, Nat.zero_add, List.append_nil]
  rw [← linS_length fp.main 0 []]; exact List.drop_left' rfl

/-! ## No recursion -/

/-- In the function list `fs`, every call goes to a smaller index. -/
def DownList (fs : List Fn) : Prop :=
  ∀ (i : Nat) (fn : Fn), fs[i]? = some fn → ∀ g a d, Instr.call g a d ∈ fn.code → g < i

/-- Linearizing keeps calls going down, and the code's own calls go to functions it has already
created. -/
theorem linS_down : ∀ (s : Stmt) (pc : Nat) (fs : List Fn), DownList fs →
    DownList (linS s pc fs).2 ∧
      ∀ g a d, Instr.call g a d ∈ (linS s pc fs).1 → g < (linS s pc fs).2.length
  | .seq a b, pc, fs, h => by
    have ha := linS_down a pc fs h
    have hb := linS_down b (pc + Stmt.len a) _ ha.1
    have := (linS_prefix b (pc + Stmt.len a) (linS a pc fs).2).length_le
    grind [linS]
  | .ite c t e, pc, fs, h => by
    have ha := linS_down t (pc + 1) fs h
    have hb := linS_down e (pc + Stmt.len t + 2) _ ha.1
    have := (linS_prefix e (pc + Stmt.len t + 2) (linS t (pc + 1) fs).2).length_le
    grind [linS]
  | .while pre c body, pc, fs, h => by
    have ha := linS_down pre pc fs h
    have hb := linS_down body (pc + Stmt.len pre + 1) _ ha.1
    have := (linS_prefix body (pc + Stmt.len pre + 1) (linS pre pc fs).2).length_le
    grind [linS]
  | .call name fr body ret args d, _, fs, h => by
    have := linS_down body 0 fs h
    grind [linS, DownList]
  | .skip, _, _, h | .mov .., _, _, h | .bin .., _, _, h | .load .., _, _, h | .store .., _, _, h
  | .ext .., _, _, h | .tick _, _, _, h => ⟨h, by simp [linS]⟩

/-- In a linearized program every call goes to a function with a smaller index, so there is no
recursion. -/
theorem linearize_callsDown (fp : Flat.Prog) (M : Nat) : (linearize fp M).CallsDown := by
  obtain ⟨h1, h2⟩ := linS_down fp.main 0 [] (fun i fn h => by simp at h)
  intro i fn hi g x d hm
  simp only [linearize] at hi
  rw [List.getElem?_append] at hi
  split at hi
  · exact h1 i fn hi g x d hm
  · rename_i hlt
    simp only [List.getElem?_singleton] at hi
    split at hi
    · cases hi
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      have := h2 g x d hm; omega
    · cases hi

/-! ## Frame sizes -/

/-- The callee need of linearized code is the Flat call measure of the statement. -/
theorem linS_callMax (φ : FrameModel) : ∀ (s : Stmt) (pc : Nat) (fs F : List Fn),
    (linS s pc fs).2 <+: F → callMax (needs φ F) (linS s pc fs).1 = Stmt.callBytes φ s
  | .seq a b, pc, fs, F, h => by
    simp only [linS, callMax_append, Stmt.callBytes] at h ⊢
    rw [linS_callMax φ a pc fs F ((linS_prefix b _ _).trans h), linS_callMax φ b _ _ F h]
  | .ite c t e, pc, fs, F, h => by
    simp only [linS, callMax_append, Stmt.callBytes] at h ⊢
    rw [linS_callMax φ t _ fs F ((linS_prefix e _ _).trans h), linS_callMax φ e _ _ F h]
    simp only [callMax]; omega
  | .while pre c body, pc, fs, F, h => by
    simp only [linS, callMax_append, Stmt.callBytes] at h ⊢
    rw [linS_callMax φ pre _ fs F ((linS_prefix body _ _).trans h), linS_callMax φ body _ _ F h]
    simp only [callMax]; omega
  | .call name fr body ret args d, _, fs, F, h => by
    simp only [linS, Stmt.callBytes] at h ⊢
    obtain ⟨r, hr⟩ := h
    have hg : F[(linS body 0 fs).2.length]? =
        some ⟨name, fr, (linS body 0 fs).1 ++ [.ret], ret⟩ := by rw [← hr]; simp
    have ht : F.take (linS body 0 fs).2.length = (linS body 0 fs).2 := by
      rw [← hr, List.append_assoc]; exact List.take_left' rfl
    simp only [callMax, List.getD_eq_getElem?_getD, needs_get φ _ _ _ hg, Option.getD_some,
      fnNeed, ← needs_take, ht, callMax_append,
      linS_callMax φ body 0 fs _ (List.prefix_refl _)]
    omega
  | .skip, _, _, _, _ => rfl
  | .mov .., _, _, _, _ => rfl
  | .bin .., _, _, _, _ => rfl
  | .load .., _, _, _, _ => rfl
  | .store .., _, _, _, _ => rfl
  | .ext .., _, _, _, _ => rfl
  | .tick _, _, _, _, _ => rfl

/-- The static stack bound of a linearized program is exactly the main frame plus the Flat call
measure, in which every callee is counted with its declared frame. -/
theorem linearize_stackBytes (φ : FrameModel) (fp : Flat.Prog) (M : Nat) :
    (linearize fp M).stackBytes φ = φ.frame fp.frame + Stmt.callBytes φ fp.main := by
  have hg : (linearize fp M).funs[(linS fp.main 0 []).2.length]? =
      some ⟨"main", fp.frame, (linS fp.main 0 []).1 ++ [.jmp (Stmt.len fp.main)], []⟩ := by
    simp [linearize]
  have ht : (linearize fp M).funs.take (linS fp.main 0 []).2.length = (linS fp.main 0 []).2 :=
    List.take_left' rfl
  simp only [Prog.stackBytes, List.getD_eq_getElem?_getD]
  rw [show (linearize fp M).main = (linS fp.main 0 []).2.length from rfl, needs_get φ _ _ _ hg]
  simp only [Option.getD_some, fnNeed, ← needs_take, ht, callMax_append,
    linS_callMax φ fp.main 0 [] _ (List.prefix_refl _)]
  simp only [callMax]; omega

/-! ## Well-formedness of linearized code -/

/-- Lin's and Flat's `OpsBelow` are the same predicate. -/
theorem opsBelow_flat (ops : List Operand) (n : Nat) : OpsBelow ops n = Flat.OpsBelow ops n :=
  rfl

/-- Linearized code is well formed when the Flat statement stays within its frame. Every
instruction of the code, placed in function `i` with frame `fr` and code length `len`, and every
function it creates satisfy the Lin well-formedness conditions. -/
theorem linS_wf (P : Prog) : ∀ (s : Stmt) (pc : Nat) (fs : List Fn) (i fr len : Nat),
    s.Within fr → (linS s pc fs).2 <+: P.funs → (linS s pc fs).2.length ≤ i →
    pc + Stmt.len s < len →
    (∀ ins ∈ (linS s pc fs).1, ins.Wf P i fr len) ∧
    (∀ (j : Nat) (fn : Fn), fs.length ≤ j → j < (linS s pc fs).2.length →
      P.funs[j]? = some fn → fn.Wf P j)
  | .seq a b, pc, fs, i, fr, len, hw, hp, hi, hl => by
    have hpb := linS_prefix b (pc + Stmt.len a) (linS a pc fs).2
    simp only [linS, Stmt.len] at hp hi hl ⊢
    have := linS_wf P a pc fs i fr len hw.1 (hpb.trans hp) (Nat.le_trans hpb.length_le hi)
      (by omega)
    have := linS_wf P b (pc + Stmt.len a) _ i fr len hw.2 hp hi (by omega)
    grind
  | .ite c t e, pc, fs, i, fr, len, hw, hp, hi, hl => by
    have hpe := linS_prefix e (pc + Stmt.len t + 2) (linS t (pc + 1) fs).2
    simp only [linS, Stmt.len] at hp hi hl ⊢
    have := linS_wf P t (pc + 1) fs i fr len hw.2.1 (hpe.trans hp)
      (Nat.le_trans hpe.length_le hi) (by omega)
    have := linS_wf P e (pc + Stmt.len t + 2) _ i fr len hw.2.2 hp hi (by omega)
    simp only [Stmt.Within] at hw
    grind [Instr.Wf, opsBelow_flat]
  | .while pre c body, pc, fs, i, fr, len, hw, hp, hi, hl => by
    have hpb := linS_prefix body (pc + Stmt.len pre + 1) (linS pre pc fs).2
    simp only [linS, Stmt.len] at hp hi hl ⊢
    have := linS_wf P pre pc fs i fr len hw.1 (hpb.trans hp) (Nat.le_trans hpb.length_le hi)
      (by omega)
    have := linS_wf P body (pc + Stmt.len pre + 1) _ i fr len hw.2.2 hp hi (by omega)
    simp only [Stmt.Within] at hw
    grind [Instr.Wf, opsBelow_flat]
  | .mov .., _, _, _, _, _, hw, _, _, _ | .bin .., _, _, _, _, _, hw, _, _, _
  | .load .., _, _, _, _, _, hw, _, _, _ | .store .., _, _, _, _, _, hw, _, _, _
  | .ext .., _, _, _, _, _, hw, _, _, _ | .tick _, _, _, _, _, _, hw, _, _, _
  | .skip, _, _, _, _, _, hw, _, _, _ => by
    simp only [linS, Stmt.Within, List.mem_singleton, forall_eq] at *
    grind [Instr.Wf, opsBelow_flat]
  | .call name fr' body ret args d, pc, fs, i, fr, len, hw, hp, hi, hl => by
    obtain ⟨hwb, hret, hargs, hargsb, hdst⟩ := hw
    change (linS body 0 fs).2 ++ [_] <+: P.funs at hp
    change ((linS body 0 fs).2 ++ [_]).length ≤ i at hi
    have hg : P.funs[(linS body 0 fs).2.length]? =
        some ⟨name, fr', (linS body 0 fs).1 ++ [.ret], ret⟩ := by
      obtain ⟨r, hr⟩ := hp; rw [← hr]; simp
    have := linS_wf P body 0 fs (linS body 0 fs).2.length fr' (Stmt.len body + 1) hwb
      ((List.prefix_append _ _).trans hp) (Nat.le_refl _) (by omega)
    simp only [linS, List.length_append, List.length_singleton, List.mem_singleton,
      forall_eq] at *
    grind [Instr.Wf, Fn.Wf, opsBelow_flat, linS_length]

/-- A linearized program is well formed when the Flat main statement stays within the declared main
frame. Its slots, jump targets, callee indices, argument counts and result ranges then all fit the
declared frames, and calls go only to smaller indices. -/
theorem linearize_wf (fp : Flat.Prog) (M : Nat) (h : fp.main.Within fp.frame) :
    (linearize fp M).Wf := by
  have hg : (linearize fp M).funs[(linS fp.main 0 []).2.length]? =
      some ⟨"main", fp.frame, (linS fp.main 0 []).1 ++ [.jmp (Stmt.len fp.main)], []⟩ := by
    simp [linearize]
  obtain ⟨ia, fa⟩ := linS_wf (linearize fp M) fp.main 0 [] (linS fp.main 0 []).2.length fp.frame
    (Stmt.len fp.main + 1) h (List.prefix_append _ _) (Nat.le_refl _) (by omega)
  refine ⟨by simp [linearize], fun j fn hj => ?_⟩
  have hlen : (linearize fp M).funs.length = (linS fp.main 0 []).2.length + 1 := by
    simp [linearize]
  have hjl : j < (linearize fp M).funs.length := by
    rcases Nat.lt_or_ge j (linearize fp M).funs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  rcases Nat.lt_or_ge j (linS fp.main 0 []).2.length with h' | h'
  · exact fa j fn (Nat.zero_le _) h' hj
  · have hj' : j = (linS fp.main 0 []).2.length := by omega
    subst hj'
    rw [hg] at hj; cases hj
    refine ⟨fun x hx => by simp at hx, fun ins hm => ?_⟩
    simp only [List.length_append, List.length_singleton, linS_length]
    rcases List.mem_append.1 hm with hm | hm
    · exact ia ins hm
    · simp only [List.mem_singleton] at hm; subst hm; show _ < _; omega

/-! ## The data region of a lowered program

The lowering `lower` keeps every Core value in byte memory at addresses `[0, Program.memBytes)`,
with the root at `0` and every activation's values above it. Its Lin image `linearize fp M` has
that data region, so Lin's `load` and `store` outside `[0, M)` are stuck, which lets `select` keep
Lin's memory in a machine region of exactly `M` bytes.

`InBounds κ ω fp M` states that every Flat state reachable from `fp.init` accesses memory only in
`[0, M)`. Under it, `linearize_sim` is the simulation from Flat to Lin with the data region. The
decidable check `withinB` decides `Flat.Stmt.Within`, so that the lowering can prove its code stays
within its frames and its linearization is therefore well formed.
-/

/-! ## The bounds hypothesis -/

/-- Every Flat state reachable from `fp.init` under `κ` and `ω` makes its memory access, if any,
inside `[0, M)`. -/
def InBounds (κ : CostModel) (ω : Oracle) (fp : Flat.Prog) (M : Nat) : Prop :=
  ∀ s, Flat.Reach κ ω fp.init s → MemIn M s

/-! ## The simulation -/

theorem reach_next {κ : CostModel} {ω : Oracle} {s₀ s : Flat.State} (h : Flat.Reach κ ω s₀ s) :
    Flat.Reach κ ω s₀ (Flat.next κ ω s) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by rw [Flat.nextN_add]; rfl⟩

/-- The forward simulation from Flat to Lin with a data region, with factor 1, along the Flat states
reachable from `fp.init`, provided every such state accesses only `[0, M)`. -/
def linearize_sim (fp : Flat.Prog) (M : Nat) (ω : Oracle) (κ : CostModel)
    (hB : InBounds κ ω fp M) : FwdSim (Flat.sem κ) (Lin.sem κ (linearize fp M)) ω :=
  linSimI (linearize fp M) ω κ (Flat.Reach κ ω fp.init) (fun _ h => reach_next h)
    (fun s h => hB s h)

theorem linearize_sim_init (fp : Flat.Prog) (M : Nat) (ω : Oracle) (κ : CostModel)
    (hB : InBounds κ ω fp M) :
    (linearize_sim fp M ω κ hB).R (measure fp.init) fp.init (linearize fp M).init :=
  ⟨rfl, rel_init fp M, Flat.Reach.refl _⟩

/-- `linearize` is correct. It is a forward simulation with factor 1 from Flat to Lin with the data
region, relating the initial states. -/
theorem linearize_sound (fp : Flat.Prog) (M : Nat) (ω : Oracle) (κ : CostModel)
    (hB : InBounds κ ω fp M) :
    ∃ sim : FwdSim (Flat.sem κ) (Lin.sem κ (linearize fp M)) ω, sim.factor = 1 ∧
      ∃ i, sim.R i fp.init (linearize fp M).init :=
  ⟨linearize_sim fp M ω κ hB, rfl, _, linearize_sim_init fp M ω κ hB⟩

/-! ## A decidable frame check -/

/-- A decidable form of `OpsBelow`. -/
def opsBelowB (ops : List Operand) (n : Nat) : Bool :=
  ops.all fun o => match o with
    | .slot x => decide (x < n)
    | .imm _ => true

theorem opsBelowB_spec {ops : List Operand} {n : Nat} (h : opsBelowB ops n = true) :
    Flat.OpsBelow ops n := by
  intro x hx
  have := List.all_eq_true.1 h _ hx
  simpa using this

/-- A decidable form of `Flat.Stmt.Within`, by structural recursion. -/
def withinB : Stmt → Nat → Bool
  | .skip, _ => true
  | .seq a b, n => withinB a n && withinB b n
  | .mov x a, n => decide (x < n) && opsBelowB [a] n
  | .bin _ x a b, n => decide (x < n) && opsBelowB [a, b] n
  | .load _ x a _, n => decide (x < n) && opsBelowB [a] n
  | .store _ a _ b, n => opsBelowB [a, b] n
  | .ite c a b, n => opsBelowB [c] n && withinB a n && withinB b n
  | .while p c b, n => withinB p n && opsBelowB [c] n && withinB b n
  | .call _ fr body ret args d, n =>
    withinB body fr && opsBelowB ret fr && decide (args.length ≤ fr) && opsBelowB args n &&
      decide (d + ret.length ≤ n)
  | .ext _ _ x args, n =>
    decide (x < n) && (args.all fun a => match a with
      | .word o => opsBelowB [o] n
      | .bytes _ => true
      | .mem a l => opsBelowB [a, l] n
      | .out _ => true
      | .outMem a l => opsBelowB [a, l] n)
  | .tick _, _ => true

theorem withinB_spec : ∀ (s : Stmt) (n : Nat), withinB s n = true → s.Within n
  | .skip, _, _ => trivial
  | .seq a b, n, h => by
    simp only [withinB, Bool.and_eq_true] at h
    exact ⟨withinB_spec a n h.1, withinB_spec b n h.2⟩
  | .mov x a, n, h => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, opsBelowB_spec h.2⟩
  | .bin _ x a b, n, h => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, opsBelowB_spec h.2⟩
  | .load _ x a _, n, h => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, opsBelowB_spec h.2⟩
  | .store _ a _ b, n, h => opsBelowB_spec h
  | .ite c a b, n, h => by
    simp only [withinB, Bool.and_eq_true] at h
    exact ⟨opsBelowB_spec h.1.1, withinB_spec a n h.1.2, withinB_spec b n h.2⟩
  | .while p c b, n, h => by
    simp only [withinB, Bool.and_eq_true] at h
    exact ⟨withinB_spec p n h.1.1, opsBelowB_spec h.1.2, withinB_spec b n h.2⟩
  | .call _ fr body ret args d, n, h => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨withinB_spec body fr h.1.1.1.1, opsBelowB_spec h.1.1.1.2, h.1.1.2,
      opsBelowB_spec h.1.2, h.2⟩
  | .ext _ _ x args, n, h => by
    simp only [withinB, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, fun o ho => ?_, fun a l ha => ?_, fun a l ha => ?_⟩
    · have := List.all_eq_true.1 h.2 _ ho
      exact opsBelowB_spec (by simpa using this)
    · have := List.all_eq_true.1 h.2 _ ha
      exact opsBelowB_spec (by simpa using this)
    · have := List.all_eq_true.1 h.2 _ ha
      exact opsBelowB_spec (by simpa using this)
  | .tick _, _, _ => trivial

end Millipede.Lin
