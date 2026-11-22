import Millipede.Target.SelRun
import Millipede.RegAlloc.Lock
import Millipede.Target.Budget
import Millipede.Compile.LinearizeProof
import Millipede.Compile.LowerStack
import Millipede.Compile.LinearizeLower

/-!
# The simulation skeleton of instruction selection

The only part of the correctness of `select` that depends on the ISA is one Lin step: from
related states, the selected code takes the machine to a state related to the next Lin state.
An ISA supplies its relation and that lemma as a `SimPkg` with `SimPkg.Laws`, which has these
parts:

* `Match s m` relates a running Lin state to a machine state.
* `Init m` is what the loader must establish, which includes an empty world and the stack bound.
* `SpOk m` says the stack pointer is within the static bound.
* `counts` gives the number of machine instructions of each Lin step.
* `entry` says that from an `Init` state, `main`'s entry sequence of at least one instruction
  reaches a state related to `P.init`, with `SpOk` throughout.
* `step` says that from related states a Lin step is matched by at most `counts.ins` machine
  steps, to related states or to halted states with equal worlds. A step takes no machine
  instruction only when `ticksAt` decreases, and `SpOk` holds on every intermediate state.

Everything else is proved here once for every ISA. `selectSim` makes `select` a forward
simulation of Lin by the machine without its clock, and `select_sound` and `select_stack` follow:
when Lin never gets stuck, neither does the machine, the traces are equal, and every state the
machine reaches satisfies `SpOk`. The cost argument gives each Lin state a potential `pot` and
shows that each Lin step pays for its machine instructions out of it. Composed with the lowering,
`select_lower_sound` and `select_lower_cost` state these results from the source program.

See doc/design/compiler.md.
-/

namespace Millipede.Sel

open Flat (Operand)

/-! ## Ticks -/

/-- The number of silent instructions at the start of a code list, which is the measure of
stuttering steps. The silent instructions are `tick`s and moves of a location to itself, whose
code is empty when the location is a register. -/
def tickPrefix : List Lin.Instr → Nat
  | .tick _ :: is => tickPrefix is + 1
  | .mov x (.slot y) :: is => if x = y then tickPrefix is + 1 else 0
  | _ => 0

/-- The number of consecutive silent instructions from the running position, each of which may
take no machine step. -/
def ticksAt (P : Lin.Prog) (s : Lin.State) : Nat :=
  match P.funs[s.fn]? with
  | some fn => tickPrefix (fn.code.drop s.pc)
  | none => 0

theorem pc_lt {fn : Lin.Fn} {pc : Nat} {ins : Lin.Instr} (h : fn.code[pc]? = some ins) :
    pc < fn.code.length := by
  rcases Nat.lt_or_ge pc fn.code.length with h' | h'
  · exact h'
  · simp [List.getElem?_eq_none h'] at h

/-- A `tick` decreases `ticksAt`. -/
theorem ticksAt_tick {P : Lin.Prog} {κ : CostModel} {ω : Oracle} {s : Lin.State} {fn : Lin.Fn}
    {t : Flat.Tick} (hf : P.funs[s.fn]? = some fn) (hi : fn.code[s.pc]? = some (.tick t)) :
    ticksAt P ((Lin.exec κ ω fn (.tick t) s).getD s) < ticksAt P s := by
  have hd : fn.code.drop s.pc = .tick t :: fn.code.drop (s.pc + 1) := by
    rw [List.drop_eq_getElem_cons (pc_lt hi)]
    simp only [List.getElem?_eq_getElem (pc_lt hi), Option.some.injEq] at hi
    rw [hi]
  simp [ticksAt, Lin.exec, hf, hd, tickPrefix]

/-- A move of a location to itself decreases `ticksAt`. -/
theorem ticksAt_self {P : Lin.Prog} {κ : CostModel} {ω : Oracle} {s : Lin.State} {fn : Lin.Fn}
    {x : Nat} (hf : P.funs[s.fn]? = some fn) (hi : fn.code[s.pc]? = some (.mov x (.slot x))) :
    ticksAt P ((Lin.exec κ ω fn (.mov x (.slot x)) s).getD s) < ticksAt P s := by
  have hd : fn.code.drop s.pc = .mov x (.slot x) :: fn.code.drop (s.pc + 1) := by
    rw [List.drop_eq_getElem_cons (pc_lt hi)]
    simp only [List.getElem?_eq_getElem (pc_lt hi), Option.some.injEq] at hi
    rw [hi]
  simp [ticksAt, Lin.exec, hf, hd, tickPrefix]

/-- A Lin step from a running state fetches and executes an instruction. -/
theorem step_fetch_inv {κ : CostModel} {P : Lin.Prog} {ω : Oracle} {s s' : Lin.State}
    {fn : Lin.Fn} (hh : s.world.halted = false) (hf : P.funs[s.fn]? = some fn)
    (hs : Lin.step κ P ω s = some s') :
    ∃ ins, fn.code[s.pc]? = some ins ∧ ins.memOk P.mem s.frame = true ∧
      Lin.exec κ ω fn ins s = some s' := by
  simp only [Lin.step, hh, Bool.false_eq_true, ite_false, hf] at hs
  cases hi : fn.code[s.pc]? with
  | none => rw [hi] at hs; cases hs
  | some ins =>
    rw [hi] at hs
    cases h : ins.memOk P.mem s.frame
    · simp [h] at hs
    · simp only [h, ite_true] at hs; exact ⟨ins, rfl, h, hs⟩

/-! ## The package -/

variable {A : Asm.Arch} {abi : Abi A.isa}

/-- What an ISA supplies about its selected code for the Lin program `P`: the relation, the
loader's start states, the stack bound and the instruction counts. -/
structure SimPkg (abi : Abi A.isa) (P : Lin.Prog) where
  Match : Lin.State → MState A.isa.Regs → Prop
  Init : MState A.isa.Regs → Prop
  SpOk : MState A.isa.Regs → Prop
  counts : Counts

/-- The laws of a `SimPkg`. -/
structure SimPkg.Laws {P : Lin.Prog} (S : SimPkg abi P) : Prop where
  run : ∀ s m, S.Match s m → s.world.halted = false ∧ m.world = s.world
  init_world : ∀ m, S.Init m → m.world = World.init
  init_sp : ∀ m, S.Init m → S.SpOk m
  entry_pos : 0 < (S.counts.entry P)
  entry : ∀ ω m₀ c, S.Init m₀ → ∃ m₁, (M abi).run ω (m₀, c) (S.counts.entry P) =
      some (m₁, c + (S.counts.entry P)) ∧ S.Match P.init m₁ ∧
      RunAll abi ω S.SpOk (m₀, c) (S.counts.entry P)
  step : ∀ ω κ s s' m c, S.Match s m → Lin.step κ P ω s = some s' →
    ∃ n m', (M abi).run ω (m, c) n = some (m', c + n) ∧
      (S.Match s' m' ∨ (s'.world.halted = true ∧ m'.world = s'.world)) ∧
      (n = 0 → ticksAt P s' < ticksAt P s) ∧ RunAll abi ω S.SpOk (m, c) n ∧
      ∀ fn ins, P.funs[s.fn]? = some fn → fn.code[s.pc]? = some ins → n ≤ S.counts.ins P s.fn s.pc fn ins

/-! ## The forward simulation -/

variable (abi) in
/-- The machine without its instruction counter. -/
abbrev Mu : Sem where
  State := (M abi).State
  step := (M abi).step
  events := (M abi).events
  clock _ := 0

theorem Mu_run (ω : Oracle) : ∀ (n : Nat) (t : (M abi).State), (Mu abi).run ω t n = (M abi).run ω t n
  | 0, _ => rfl
  | n + 1, t => by
    show ((M abi).step ω t).bind (fun s' => (Mu abi).run ω s' n) =
      ((M abi).step ω t).bind (fun s' => (M abi).run ω s' n)
    congr 1; funext t'; exact Mu_run ω n t'

variable {P : Lin.Prog} (S : SimPkg abi P)

/-- The simulation relation holds between running states related by `Match`, with the index
counting the silent instructions ahead, between halted states with equal worlds, and at the
start, where the machine has `main`'s entry sequence still to run before `P.init`. -/
def SimR (i : Nat) (s : Lin.State) (t : (Mu abi).State) : Prop :=
  (S.Match s t.1 ∧ i = ticksAt P s) ∨ (s.world.halted = true ∧ t.1.world = s.world) ∨
    (s = P.init ∧ S.Init t.1)

variable {S}

/-- `select` is a forward simulation of Lin by the machine without its instruction counter. -/
def selectSim (hS : S.Laws) (ω : Oracle) (κ : CostModel) : FwdSim (Lin.sem κ P) (Mu abi) ω where
  Idx := Nat
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  R := SimR S
  factor := 0
  events_eq := by
    intro i s t h
    rcases h with ⟨hM, _⟩ | ⟨_, hw⟩ | ⟨rfl, hI⟩
    · show s.world.events = t.1.world.events; rw [(hS.run _ _ hM).2]
    · show s.world.events = t.1.world.events; rw [hw]
    · show (P.init).world.events = t.1.world.events; rw [hS.init_world _ hI]; rfl
  step := by
    intro i s t s' hR hs
    change Lin.step κ P ω s = some s' at hs
    obtain ⟨m, c⟩ := t
    rcases hR with ⟨hM, hi⟩ | ⟨hh, hw⟩ | ⟨rfl, hI⟩
    · obtain ⟨n, m', hrun, hout, hn, -, -⟩ := hS.step ω κ s s' m c hM hs
      refine ⟨ticksAt P s', (m', c + n), n, (Mu_run ω n (m, c)).trans hrun, ?_, ?_, by simp⟩
      · rcases hout with h | h
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr (Or.inl h)
      · rcases Nat.eq_zero_or_pos n with h0 | h0
        · exact Or.inr (hi ▸ hn h0)
        · exact Or.inl h0
    · have hs' : s' = s := by
        rw [show Lin.step κ P ω s = some s from Lin.step_halted κ P ω s hh] at hs
        exact (Option.some.inj hs).symm
      subst hs'
      have hm : (M abi).step ω (m, c) = some (m, c) :=
        M_step_halted abi (by show m.world.halted = true; rw [hw]; exact hh)
      exact ⟨i, (m, c), 1, (Mu_run ω 1 (m, c)).trans (Sem.run_one hm),
        Or.inr (Or.inl ⟨hh, hw⟩), Or.inl Nat.one_pos, by simp⟩
    · obtain ⟨m₁, hst, hM, -⟩ := hS.entry ω m c hI
      obtain ⟨n, m', hrun, hout, _, -, -⟩ := hS.step ω κ _ s' m₁ _ hM hs
      refine ⟨ticksAt P s', (m', c + (S.counts.entry P) + n), (S.counts.entry P) + n, ?_, ?_,
        Or.inl (by have := hS.entry_pos; omega), by simp⟩
      · refine (Mu_run ω _ (m, c)).trans ?_
        rw [Sem.run_add_of hst]
        exact hrun
      · rcases hout with h | h
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr (Or.inl h)

theorem Mu_mono (hl : A.isa.Laws) : (Mu abi).Mono where
  events ω s s' h := (M_mono abi hl).events ω s s' h
  clock _ _ _ _ := Nat.le_refl _

theorem Mu_traceAt (ω : Oracle) (t : (M abi).State) (n : Nat) :
    (Mu abi).traceAt ω t n = (M abi).traceAt ω t n := by
  unfold Sem.traceAt
  have h := Mu_run (abi := abi) ω n t
  revert h
  generalize (Mu abi).run ω t n = x
  intro h
  subst h
  cases (M abi).run ω t n <;> rfl

/-- When the Lin program never gets stuck, the machine started from an `Init` state never gets
stuck either and produces the same trace. -/
theorem select_sound (hl : A.isa.Laws) (hS : S.Laws) (ω : Oracle) (κ : CostModel)
    {m₀ : MState A.isa.Regs} (hI : S.Init m₀) (hs : (Lin.sem κ P).NeverStuck ω P.init) :
    (M abi).NeverStuck ω (m₀, 0) ∧
      TraceEq ((Lin.sem κ P).traceAt ω P.init) ((M abi).traceAt ω (m₀, 0)) := by
  have hR : (selectSim hS ω κ).R (0 : Nat) P.init ((m₀, 0) : (Mu abi).State) :=
    show SimR S 0 P.init (m₀, 0) from Or.inr (Or.inr ⟨rfl, hI⟩)
  refine ⟨fun n => ?_, ?_⟩
  · have := (selectSim hS ω κ).neverStuck hR hs n
    exact (Mu_run ω n (m₀, 0)) ▸ this
  · have := (selectSim hS ω κ).traceEq (Mu_mono hl) hR hs
    have e : (Mu abi).traceAt ω ((m₀, 0) : (M abi).State) = (M abi).traceAt ω ((m₀, 0) : (M abi).State) :=
      funext fun n => Mu_traceAt ω _ n
    exact e ▸ this

/-! ## The stack bound on every machine state -/

/-- From a reachable Lin state related to the machine state, or from a halted machine state
within the bound, every machine state the run reaches satisfies `SpOk`. The proof is by strong
induction on the number of machine steps, and inside it on `ticksAt`, because a silent
instruction may take no machine step. -/
theorem spOk_run (hS : S.Laws) {ω : Oracle} {κ : CostModel}
    (hns : (Lin.sem κ P).NeverStuck ω P.init) :
    ∀ (k T r : Nat) (s : Lin.State) (t : (M abi).State), ticksAt P s ≤ T →
      (Lin.sem κ P).run ω P.init r = some s →
      (S.Match s t.1 ∨ (t.1.world.halted = true ∧ S.SpOk t.1)) →
      ∀ t', (M abi).run ω t k = some t' → S.SpOk t'.1 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro T
  induction T using Nat.strongRecOn with
  | _ T ihT =>
  intro r s t hT hr hG t' ht
  rcases hG with hM | ⟨hh, hb⟩
  · obtain ⟨m, c⟩ := t
    have hstep : ∃ s', Lin.step κ P ω s = some s' := by
      have h1 := hns (r + 1)
      rw [Sem.run_add_of hr 1] at h1
      cases h2 : Lin.step κ P ω s with
      | none =>
        have h3 : (Lin.sem κ P).run ω s 1 = none := by
          rw [Sem.run_succ]; show (Lin.step κ P ω s).bind _ = none; rw [h2]; rfl
        rw [h3] at h1; cases h1
      | some s' => exact ⟨s', rfl⟩
    obtain ⟨s', hs⟩ := hstep
    obtain ⟨n, m', hrun, hout, hn, hall, -⟩ := hS.step ω κ s s' m c hM hs
    by_cases hkn : k ≤ n
    · exact hall k hkn t' ht
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hkn)
      rw [Sem.run_add_of hrun] at ht
      have hr' : (Lin.sem κ P).run ω P.init (r + 1) = some s' := by
        rw [Sem.run_add_of hr 1]; exact Sem.run_one (S := Lin.sem κ P) hs
      have hG' : S.Match s' (m', c + n).1 ∨
          ((m', c + n).1.world.halted = true ∧ S.SpOk (m', c + n).1) := by
        rcases hout with h | ⟨hh, hw⟩
        · exact Or.inl h
        · exact Or.inr ⟨by show m'.world.halted = true; rw [hw]; exact hh,
            hall n (Nat.le_refl _) _ hrun⟩
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have hlt := hn h0
        subst h0
        exact ihT (ticksAt P s') (by omega) (r + 1) s' _ (Nat.le_refl _) hr' hG' t'
          (by rw [Nat.zero_add]; exact ht)
      · exact ihk d (by omega) (ticksAt P s') (r + 1) s' _ (Nat.le_refl _) hr' hG' t' ht
  · rw [M_run_halted abi hh k] at ht
    cases ht; exact hb

/-- When the Lin program never gets stuck, every state the machine reaches from an `Init` state
satisfies `SpOk`, including the states inside call and return sequences. -/
theorem select_stack (hS : S.Laws) {m₀ : MState A.isa.Regs} (hI : S.Init m₀) (ω : Oracle)
    (κ : CostModel) (hns : (Lin.sem κ P).NeverStuck ω P.init) (n : Nat) (t : (M abi).State)
    (h : (M abi).run ω (m₀, 0) n = some t) : S.SpOk t.1 := by
  obtain ⟨m₁, hst, hM, hall⟩ := hS.entry ω m₀ 0 hI
  by_cases hn : n ≤ (S.counts.entry P)
  · exact hall n hn t h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hn)
    rw [Sem.run_add_of hst] at h
    exact spOk_run hS hns d _ 0 P.init _ (Nat.le_refl _) rfl (Or.inl hM) t h

/-! ## Instructions per reactor step -/

theorem codeOk_spec {C : Counts} {κ : CostModel} {P : Lin.Prog} {N : Cert} {i : Nat} {fn : Lin.Fn} :
    ∀ (code : List Lin.Instr) (pc0 : Nat), codeOk C κ P N i fn pc0 code = true →
      ∀ k ins, code[k]? = some ins → ∀ v, N i (pc0 + k) = some v →
        instrOk C κ P N i (pc0 + k) fn v ins = true
  | [], _, _, k, ins, h, _, _ => by simp at h
  | ins' :: rest, pc0, h, k, ins, hk, v, hv => by
    simp only [codeOk, Bool.and_eq_true] at h
    cases k with
    | zero => grind
    | succ k =>
      have := codeOk_spec rest (pc0 + 1) h.2 k ins (by simpa using hk) v (by grind)
      grind

theorem funsOk_spec {C : Counts} {κ : CostModel} {P : Lin.Prog} {N : Cert} :
    ∀ (fs : List Lin.Fn) (i0 : Nat), funsOk C κ P N i0 fs = true →
      ∀ k fn, fs[k]? = some fn → codeOk C κ P N (i0 + k) fn 0 fn.code = true
  | [], _, _, k, fn, hk => by simp at hk
  | f :: fs, i0, h, k, fn, hk => by
    simp only [funsOk, Bool.and_eq_true] at h
    cases k with
    | zero => grind
    | succ k => have := funsOk_spec fs (i0 + 1) h.2 k fn (by simpa using hk); grind

/-- When `budgetOk` holds, `main`'s first position has a certified potential `v ≤ -entry`, and
every certified position passes its local check. -/
theorem budgetOk_spec {C : Counts} {κ : CostModel} {P : Lin.Prog} {N : Cert}
    (h : budgetOk C κ P N = true) :
    (∃ v, N P.main 0 = some v ∧ (C.entry P : Int) + v ≤ 0) ∧
      ∀ i fn, P.funs[i]? = some fn → ∀ pc ins, fn.code[pc]? = some ins → ∀ v, N i pc = some v →
        instrOk C κ P N i pc fn v ins = true := by
  simp only [budgetOk, Bool.and_eq_true] at h
  refine ⟨?_, fun i fn hf pc ins hi v hv => ?_⟩
  · have h1 := h.1
    split at h1
    · rename_i v hv; exact ⟨v, hv, by simpa using h1⟩
    · cases h1
  · have h1 := funsOk_spec P.funs 0 h.2 i fn hf
    rw [Nat.zero_add] at h1
    have := codeOk_spec fn.code 0 h1 pc ins hi v (by rw [Nat.zero_add]; exact hv)
    rwa [Nat.zero_add] at this

section Pot
variable (P : Lin.Prog) (N : Cert)

/-- The potential of the suspended activations `st`, the topmost of which called function `g`.
Each activation contributes the certificate of its return position and the result stores that
run after the return. -/
def stackPot : Nat → List Lin.Act → Int
  | _, [] => 0
  | g, a :: st => (resLen P g : Int) + (N a.fn a.pc).getD 0 + stackPot a.fn st

/-- Every suspended activation's return position is certified, and its share of the potential
is not negative. -/
def StackOk : Nat → List Lin.Act → Prop
  | _, [] => True
  | g, a :: st => (∃ v, N a.fn a.pc = some v ∧ 0 ≤ (resLen P g : Int) + v) ∧ StackOk a.fn st

/-- The potential of a Lin state. -/
def pot (s : Lin.State) : Int := (N s.fn s.pc).getD 0 + stackPot P N s.fn s.stack

/-- The state's position and all return positions are certified. -/
def PotOk (s : Lin.State) : Prop := (N s.fn s.pc).isSome ∧ StackOk P N s.fn s.stack

end Pot

theorem stackPot_nonneg {P : Lin.Prog} {N : Cert} :
    ∀ (g : Nat) (st : List Lin.Act), StackOk P N g st → 0 ≤ stackPot P N g st
  | _, [], _ => by simp [stackPot]
  | g, a :: st, ⟨⟨v, hv, hle⟩, h⟩ => by
    have := stackPot_nonneg a.fn st h
    simp only [stackPot, hv, Option.getD_some]
    omega

theorem pot_eq {P : Lin.Prog} {N : Cert} {s : Lin.State} {v : Int} (hv : N s.fn s.pc = some v) :
    pot P N s = v + stackPot P N s.fn s.stack := by
  simp [pot, hv]

/-- One Lin step pays for its machine instructions out of the potential and the advance of the
Lin clock, using only the local checks of `budgetOk`. A step that halts the world, such as an
`exit`, needs no potential afterwards. -/
theorem pot_step {C : Counts} {κ : CostModel} {P : Lin.Prog} {N : Cert}
    (hb : budgetOk C κ P N = true) {ω : Oracle} {s s' : Lin.State} {fn : Lin.Fn}
    {ins : Lin.Instr} (hh : s.world.halted = false) (hf : P.funs[s.fn]? = some fn)
    (hi : fn.code[s.pc]? = some ins) (hp : PotOk P N s)
    (hs : Lin.exec κ ω fn ins s = some s') :
    (s'.world.halted = true → (C.ins P s.fn s.pc fn ins : Int) + s.clock ≤ pot P N s + s'.clock) ∧
    (s'.world.halted = false → PotOk P N s' ∧
      (C.ins P s.fn s.pc fn ins : Int) + pot P N s' + s.clock ≤ pot P N s + s'.clock) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp.1
  have hok := (budgetOk_spec hb).2 s.fn fn hf s.pc ins hi v hv
  have := stackPot_nonneg s.fn s.stack hp.2
  have hrl : resLen P s.fn = fn.ret.length := by simp [resLen, hf]
  cases ins
  case jz o l =>
    cases o <;> grind [Lin.exec, pot, stackPot, PotOk, instrOk, succOk, Operand.eval]
  case ext sym nr x args =>
    have := Flat.extRun_halted ω sym nr args s.frame s.mem hh
    cases nr <;> grind [Lin.exec, pot, stackPot, PotOk, StackOk, instrOk, resLen, succOk]
  all_goals grind [Lin.exec, pot, stackPot, PotOk, StackOk, instrOk, resLen, succOk]

section Rc
variable {N : Cert}

variable (S N) in
/-- Running states related by `Match` with potential `q`, or halted states with equal worlds and
potential 0. -/
def RcRun (s : Lin.State) (t : (M abi).State) (q : Int) : Prop :=
  (S.Match s t.1 ∧ PotOk P N s ∧ q = pot P N s) ∨
    (s.world.halted = true ∧ t.1.world = s.world ∧ q = 0)

variable (S N) in
/-- `RcRun`, or the start, where the Lin state is `P.init` and the machine state satisfies
`Init` with the entry sequence still to run, at potential `entry + pot P.init`. -/
def Rc (s : Lin.State) (t : (M abi).State) (q : Int) : Prop :=
  RcRun S N s t q ∨
    (s = P.init ∧ S.Init t.1 ∧ PotOk P N s ∧ q = (S.counts.entry P) + pot P N s)

/-- Related states have the same world. -/
theorem Rc.world (hS : S.Laws) {s : Lin.State} {t : (M abi).State} {q : Int}
    (h : Rc S N s t q) : t.1.world = s.world := by
  rcases h with (⟨hM, _⟩ | ⟨_, hw, _⟩) | ⟨rfl, hI, _⟩
  · exact (hS.run _ _ hM).2
  · exact hw
  · exact hS.init_world _ hI

/-- A Lin step from states related by `Match` is matched by machine steps, and the machine clock
plus the potential grows by at most the advance of the Lin clock. -/
theorem rc_match {κ : CostModel} (hS : S.Laws) (hb : budgetOk S.counts κ P N = true)
    {ω : Oracle} {s s' : Lin.State} {m : MState A.isa.Regs} (hM : S.Match s m) (hp : PotOk P N s)
    (hs : Lin.step κ P ω s = some s') (c : Nat) :
    ∃ n t' q', (M abi).run ω (m, c) n = some t' ∧ RcRun S N s' t' q' ∧
      (t'.2 : Int) + q' + s.clock ≤ c + pot P N s + s'.clock := by
  obtain ⟨n, m', hrun, hout, -, -, hcnt⟩ := hS.step ω κ s s' m c hM hs
  have hh := (hS.run _ _ hM).1
  obtain ⟨fn, hf⟩ : ∃ fn, P.funs[s.fn]? = some fn := by
    cases h : P.funs[s.fn]? with
    | none => simp [Lin.step, hh, h] at hs
    | some fn => exact ⟨fn, rfl⟩
  obtain ⟨ins, hi, -, he⟩ := step_fetch_inv hh hf hs
  have hn := hcnt fn ins hf hi
  obtain ⟨hhalt, hrunning⟩ := pot_step hb hh hf hi hp he
  rcases hout with hM' | ⟨hh', hw'⟩
  · obtain ⟨hp', hle⟩ := hrunning (hS.run _ _ hM').1
    refine ⟨n, (m', c + n), pot P N s', hrun, Or.inl ⟨hM', hp', rfl⟩, ?_⟩
    have : (n : Int) ≤ S.counts.ins P s.fn s.pc fn ins := by exact_mod_cast hn
    push_cast; omega
  · have hle := hhalt hh'
    refine ⟨n, (m', c + n), 0, hrun, Or.inr ⟨hh', hw', rfl⟩, ?_⟩
    have : (n : Int) ≤ S.counts.ins P s.fn s.pc fn ins := by exact_mod_cast hn
    push_cast; omega

/-- The counted step of `rc_match`, from any states related by `Rc`. -/
theorem rc_step {κ : CostModel} (hS : S.Laws) (hb : budgetOk S.counts κ P N = true)
    {ω : Oracle} {s s' : Lin.State} {t : (M abi).State} {q : Int} (hR : Rc S N s t q)
    (hs : Lin.step κ P ω s = some s') :
    ∃ n t' q', (M abi).run ω t n = some t' ∧ RcRun S N s' t' q' ∧
      (t'.2 : Int) + q' + s.clock ≤ t.2 + q + s'.clock := by
  obtain ⟨m, c⟩ := t
  rcases hR with (⟨hM, hp, rfl⟩ | ⟨hh, hw, rfl⟩) | ⟨rfl, hI, hp, rfl⟩
  · exact rc_match hS hb hM hp hs c
  · have hs' : s' = s := by
      rw [Lin.step_halted κ P ω s hh] at hs; exact (Option.some.inj hs).symm
    subst hs'
    have hm : (M abi).step ω (m, c) = some (m, c) :=
      M_step_halted abi (by show m.world.halted = true; rw [hw]; exact hh)
    exact ⟨1, (m, c), 0, Sem.run_one hm, Or.inr ⟨hh, hw, rfl⟩, by simp⟩
  · obtain ⟨m₁, hst, hM, -⟩ := hS.entry ω m c hI
    obtain ⟨n, t', q', hrun, hR', hle⟩ := rc_match hS hb hM hp hs (c + (S.counts.entry P))
    refine ⟨(S.counts.entry P) + n, t', q', ?_, hR', ?_⟩
    · rw [Sem.run_add_of hst]; exact hrun
    · push_cast at hle ⊢; omega

/-- Inversion for a run of `n + 1` steps: a first step, then `n`. -/
theorem _root_.Millipede.Sem.run_succ_some {S : Sem} {ω : Oracle} {s s' : S.State} {n : Nat}
    (h : S.run ω s (n + 1) = some s') : ∃ s₁, S.step ω s = some s₁ ∧ S.run ω s₁ n = some s' := by
  rw [Sem.run_succ] at h
  cases hs : S.step ω s <;> simp_all

/-- `d` Lin steps from related states are matched by machine steps to related states, and the
machine clock plus the potential grows by at most the advance of the Lin clock. -/
theorem rc_run {κ : CostModel} (hS : S.Laws) (hb : budgetOk S.counts κ P N = true)
    {ω : Oracle} :
    ∀ (d : Nat) {s s' : Lin.State} {t : (M abi).State} {q : Int}, Rc S N s t q →
      (Lin.sem κ P).run ω s d = some s' →
      ∃ e t' q', (M abi).run ω t e = some t' ∧ Rc S N s' t' q' ∧
        (t'.2 : Int) + q' + s.clock ≤ t.2 + q + s'.clock ∧
        (d = 0 → q' = q) ∧ (0 < d → RcRun S N s' t' q')
  | 0, s, s', t, q, hR, h => by
    cases h
    exact ⟨0, t, q, rfl, hR, by omega, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | d + 1, s, s', t, q, hR, h => by
    obtain ⟨s₁, hs, h⟩ := Sem.run_succ_some h
    obtain ⟨n, t₁, q₁, hrun₁, hR₁, hle₁⟩ := rc_step hS hb hR hs
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; cases h
      exact ⟨n, t₁, q₁, hrun₁, Or.inl hR₁, hle₁, fun h => absurd h (Nat.succ_ne_zero 0),
        fun _ => hR₁⟩
    obtain ⟨e, t', q', hrun', hR', hle', -, hlast⟩ := rc_run hS hb d (Or.inl hR₁) h
    exact ⟨n + e, t', q', by rw [Sem.run_add_of hrun₁]; exact hrun', hR', by omega,
      fun h => absurd h (Nat.succ_ne_zero d), fun _ => hlast hd⟩

/-- At a reactor-step boundary the potential is `0`. -/
theorem rcRun_boundary {κ : CostModel} (hS : S.Laws) (hb : budgetOk S.counts κ P N = true)
    {u : Lin.State} {t : (M abi).State} {q : Int} (hR : RcRun S N u t q)
    (hbd : u.world.halted = false → u.stack = [] ∧
      ∃ fn l, P.funs[u.fn]? = some fn ∧ fn.code[u.pc]? = some (.jz (.imm 1) l)) : q = 0 := by
  rcases hR with ⟨hM, hp, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨hst, fn, l, hf, hi⟩ := hbd (hS.run _ _ hM).1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp.1
    have hok := (budgetOk_spec hb).2 u.fn fn hf u.pc _ hi v hv
    have h1 : ((1 : UInt64) = 0) = False := by decide
    simp only [instrOk, h1, ite_false, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [pot_eq hv, hst, hok.2]; rfl
  · rfl

end Rc

/-! ## Composition with the lowering -/

theorem matchK_nil {P : Lin.Prog} {f : Nat} {k : List Flat.Kont} {pc : Nat} {stk : List Lin.Act}
    (h : Lin.MatchK P f k pc stk) : k = [] → stk = [] := by
  induction h with
  | stop _ => intro; rfl
  | seq _ _ _ => intro h; cases h
  | loop _ _ _ _ => intro h; cases h
  | ret _ _ _ _ _ => intro h; cases h
  | jmp _ _ ih => exact ih

/-- At a reactor-step boundary, Lin is at the reactor loop's test `jz 1` with an empty
stack. -/
theorem memBoundary {p : Program} {ω : Oracle} {P : Lin.Prog} {j : Nat} {t : Flat.State}
    {u : Lin.State} (hR : Flat.MReactorRel p ω (j + 1) t) (hrel : Lin.Rel P t u)
    (hh : u.world.halted = false) :
    u.stack = [] ∧ ∃ fn l, P.funs[u.fn]? = some fn ∧ fn.code[u.pc]? = some (.jz (.imm 1) l) := by
  simp only [Flat.MReactorRel] at hR
  obtain ⟨-, hR⟩ := hR
  rcases hR with hh' | ⟨hcur, hk, -⟩
  · rw [← hrel.world, hh] at hh'; cases hh'
  have hc := hrel.cur
  rw [hcur] at hc
  obtain ⟨-, hjz, -, -⟩ := Lin.Compiled.while hc
  obtain ⟨fn, hf, hi⟩ := hjz.fetch1
  refine ⟨?_, fn, _, hf, by simpa [Lin.Stmt.len] using hi⟩
  have hk2 := hrel.kont
  rw [hk] at hk2
  exact matchK_nil hk2 rfl

section Pipeline
variable {p : Program} {fp : Flat.Prog} {P' : Lin.Prog} {S' : SimPkg abi P'} {kL cL : Nat}

open RegAlloc (Lock)

/-- The machine running the selected code of a lowered program never gets stuck, produces the
source program's events, and keeps the stack bound. `P'` is any lock-step refinement `L` of the
linearized program, such as the checked register allocation or `Lock.id`, and the machine
starts from an `Init` state of a selection package for `P'`. -/
theorem select_lower_sound (κ : CostModel) (hl : A.isa.Laws) (hlow : Flat.lower p = .ok fp)
    (hH : Flat.MemHyp p) (L : Lock (Lin.linearize fp p.memBytes) P' kL cL)
    (hS : S'.Laws) {m₀ : MState A.isa.Regs} (hI : S'.Init m₀) (ω : Oracle) :
    (M abi).NeverStuck ω (m₀, 0) ∧ TraceEq ((M abi).traceAt ω (m₀, 0)) (p.events ω) ∧
      ∀ n t, (M abi).run ω (m₀, 0) n = some t → S'.SpOk t.1 := by
  have hns := Lin.lower_linearize_neverStuck p fp hlow hH ω κ
  have hns' := L.neverStuck κ ω hns
  obtain ⟨h1, h2⟩ := select_sound hl hS ω κ hI hns'
  exact ⟨h1, h2.symm.trans ((L.traceEq κ ω hns).symm.trans
    (Lin.lower_linearize_traceEq p fp hlow hH ω κ)),
    fun n t h => select_stack hS hI ω κ hns' n t h⟩

/-- A bound on the machine instructions of each reactor step. Take a program that is lowered,
linearized with its data region, refined in lock-step by `P'` and selected, and whose selected
code passes the budget check `budgetOk counts κ P' N`. From any `Init` state and for every
oracle, there are monotone machine times `marks k` with `marks 0 = 0`, at which the machine's
trace is the source trace after reactor step `k`, and at most `p.stepCost k ω κ` machine
instructions run between `marks k` and `marks (k + 1)`. -/
theorem select_lower_cost {κ : CostModel} (hlow : Flat.lower p = .ok fp) (hH : Flat.MemHyp p)
    (L : Lock (Lin.linearize fp p.memBytes) P' kL cL)
    (hS : S'.Laws) {N : Cert} (hb : budgetOk S'.counts κ P' N = true)
    {m₀ : MState A.isa.Regs} (hI : S'.Init m₀) (ω : Oracle) :
    ∃ marks : Nat → Nat, marks 0 = 0 ∧ ∀ k, marks k ≤ marks (k + 1) ∧
      (M abi).traceAt ω (m₀, 0) (marks (k + 1)) = p.events ω k ∧
      (M abi).clockAt ω (m₀, 0) (marks (k + 1)) - (M abi).clockAt ω (m₀, 0) (marks k) ≤
        p.stepCost k ω κ := by
  have hmem : p.memBytes < UInt64.size := by
    unfold Flat.lower at hlow
    split at hlow
    · rename_i hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    · cases hlow
  have hfp : fp = Flat.lowerProg p := by
    unfold Flat.lower at hlow
    split at hlow
    · exact (Except.ok.inj hlow).symm
    · cases hlow
  -- the reactor is simulated by the selected Lin program with factor 1
  let sim := ((Flat.lowerSim p ω κ hH hmem).comp
    (Lin.linearize_sim fp p.memBytes ω κ (Lin.lowerInBounds p fp hlow hH κ ω))).comp (L.sim κ ω)
  have hR0 : sim.R ((), (Lin.measure fp.init, ())) (0 : Nat) P'.init :=
    ⟨_, ⟨fp.init, show fp.init = (Flat.lowerProg p).init by rw [hfp], rfl,
      Lin.rel_init fp p.memBytes, Flat.Reach.refl _⟩, L.init⟩
  obtain ⟨μ, hμ0, hμ⟩ := sim.schedule hR0 (p.sem_neverStuck ω κ ω 0)
  obtain ⟨⟨v0, hv0, hle0⟩, -⟩ := budgetOk_spec hb
  let Lc := fun n => (Lin.sem κ P').clockAt ω P'.init n
  let Q : Nat → Nat × (M abi).State × Int → Prop := fun k x =>
    (M abi).run ω (m₀, 0) x.1 = some x.2.1 ∧ ∃ u,
      (Lin.sem κ P').run ω P'.init (μ k) = some u ∧ Rc S' N u x.2.1 x.2.2 ∧ x.2.2 ≤ 0
  have hQ0 : Q 0 (0, (m₀, 0), (S'.counts.entry P') + v0) := by
    refine ⟨rfl, _, by rw [hμ0]; rfl, Or.inr ⟨rfl, hI, ⟨by simp [Lin.Prog.init, hv0], trivial⟩,
      ?_⟩, by omega⟩
    simp [pot, Lin.Prog.init, hv0, stackPot]
  have key : ∀ k (x : Nat × (M abi).State × Int), Q k x → ∃ y : Nat × (M abi).State × Int,
      Q (k + 1) y ∧ x.1 ≤ y.1 ∧ (y.2.1.2 : Int) + y.2.2 + Lc (μ k) ≤ x.2.1.2 + x.2.2 + Lc (μ (k + 1)) ∧
      x.2.2 ≤ y.2.2 := by
    intro k x ⟨hx, u, hu, hRc, hq⟩
    obtain ⟨hmono, -, -⟩ := hμ k
    obtain ⟨-, ⟨j, s, u', hs, hu', hR'⟩, -⟩ := hμ (k + 1)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmono
    rw [hd, Sem.run_add_of hu] at hu'
    obtain ⟨e, t', q', hrun, hRc', hle, h0, hpos⟩ := rc_run hS hb d hRc hu'
    have hq' : q' ≤ 0 ∧ x.2.2 ≤ q' := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · rw [h0 hd0]; exact ⟨hq, Int.le_refl _⟩
      · have hs' : s = k + 1 := by
          rw [Program.sem_run, Nat.zero_add] at hs; exact (Option.some.inj hs).symm
        subst hs'
        obtain ⟨u₀, ⟨tf, hRR, -, hrel⟩, hL⟩ := hR'
        have := rcRun_boundary hS hb (hpos hd0) fun hh => by
          have hh₀ : u₀.world.halted = false := by rw [← L.world hL]; exact hh
          obtain ⟨h1, h2⟩ := memBoundary hRR hrel.1 hh₀
          exact L.boundary hL h1 h2
        omega
    refine ⟨(x.1 + e, t', q'), ⟨by rw [Sem.run_add_of hx]; exact hrun, u', ?_, hRc', hq'.1⟩,
      Nat.le_add_right _ _, ?_, hq'.2⟩
    · rw [hd, Sem.run_add_of hu]; exact hu'
    · have e1 : Lc (μ k) = u.clock := by simp only [Lc, Sem.clockAt, hu]
      have e2 : Lc (μ (k + 1)) = u'.clock := by
        simp only [Lc, Sem.clockAt, hd, Sem.run_add_of hu, hu']
      rw [e1, e2]; exact hle
  let f : (k : Nat) → {x : Nat × (M abi).State × Int // Q k x} := fun k =>
    @Nat.rec (fun k => {x : Nat × (M abi).State × Int // Q k x})
      ⟨(0, (m₀, 0), (S'.counts.entry P') + v0), hQ0⟩
      (fun k ih => ⟨Classical.choose (key k ih.1 ih.2),
        (Classical.choose_spec (key k ih.1 ih.2)).1⟩) k
  refine ⟨fun k => (f k).1.1, rfl, fun k => ?_⟩
  have hspec := Classical.choose_spec (key k (f k).1 (f k).2)
  have hf1 : (f (k + 1)).1 = Classical.choose (key k (f k).1 (f k).2) := rfl
  obtain ⟨hle, hclk, hqq⟩ := hspec.2
  rw [← hf1] at hle hclk hqq
  obtain ⟨hxk, -⟩ := (f k).2
  obtain ⟨hxk1, u, hu, hRc, -⟩ := (f (k + 1)).2
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨-, ⟨j, s, u', hs, hu', hR'⟩, -⟩ := hμ (k + 1)
    rw [hu] at hu'; cases hu'
    have hs' : s = k + 1 := by
      rw [Program.sem_run, Nat.zero_add] at hs; exact (Option.some.inj hs).symm
    subst hs'
    have he := sim.events_eq hR'
    simp only [Sem.traceAt, hxk1]
    show (f (k + 1)).1.2.1.1.world.events = _
    rw [Rc.world hS hRc]
    exact he.symm
  · obtain ⟨-, -, hc⟩ := hμ k
    rw [Program.sem_clockAt, Program.sem_clockAt] at hc
    have hfac : sim.factor = 1 := rfl
    rw [hfac] at hc
    simp only [Sem.clockAt, hxk, hxk1]
    show (f (k + 1)).1.2.1.2 - (f k).1.2.1.2 ≤ _
    have hcp : p.costPrefix ω κ (k + 1) = p.costPrefix ω κ k + p.stepCost k ω κ := rfl
    have hL : Lc (μ (k + 1)) ≤ Lc (μ k) + p.stepCost k ω κ := by
      simp only [Lc]; omega
    omega

end Pipeline

end Millipede.Sel
