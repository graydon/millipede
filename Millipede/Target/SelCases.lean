import Millipede.Target.SelFrame
import Millipede.RegAlloc.Live
import Millipede.Target.CallArgs

/-!
# The cases of one Lin step and their dispatch

The law `SimPkg.Laws.step` asks for the machine steps that match one Lin step from related
states. Every ISA proves it the same way, with one lemma for each kind of Lin instruction and a
dispatch on the instruction, so this module states the cases and does the dispatch once.

* `StepOk pred` is the full statement for the instructions that satisfy `pred`, used for `call`
  and `ret`, which change the activation.
* `LocalOk pred` is the statement for an instruction that stays in the running activation, such
  as `mov`, `bin`, `load`, `store`, `jmp`, `jz` and an extern call that returns. Its code takes at
  least one and exactly `cnt fn ins` machine steps, keeps the stack pointer, and reaches a state
  related to the next Lin state in the same frame.
* `HaltOk pred` is the statement for `exit`, after which the machine halts with the Lin world.
* `StepOkAt F cnt pred` is the statement up to dead locations. The machine may reach a state
  related to one that differs from the next Lin state only in locations dead there, as the
  validated live sets `F` say, and the count may depend on the position, because a call saves
  only the locations live after it.
* `Cases` has one `StepOkAt` field for each kind of instruction, together with what the dispatch
  needs of the selector: a `tick` has an empty block, and every extern call it selects has one of
  the five accepted shapes. `Cases.step` proves the law `SimPkg.Laws.step` from them.
* `sim_straight_kill` is `sim_straight` for a block that destroys the locations of the
  convention's clobber set: the machine is matched to the next Lin state with those locations,
  dead there by the clobber check, reading what the machine holds (`killFrame`).
* `pkg` is the package of an ISA, in which the machine is related at the ISA's convention to a
  state that agrees with the Lin state on its live locations. `pkg_laws` proves its laws from
  `Cases` and the entry sequence.
-/

namespace Millipede.Sel

open Flat (Operand)

section Statements
variable {A : Asm.Arch} (abi : Abi A.isa) (C : Conv A) (P : Lin.Prog) (AP : Asm.Prog A)
  (σ : String → Option UInt64) (lo N : Nat) (cnt : Lin.Fn → Lin.Instr → Nat)

/-- One Lin step of an instruction satisfying `pred`, from related states, takes exactly
`cnt fn ins` machine steps to related states or to two halted states. It takes none only when
the silent instructions ahead decrease, and the stack pointer stays within the bound
throughout. -/
def StepOk (pred : Lin.Instr → Prop) : Prop :=
  ∀ (ω : Oracle) (κ : CostModel) (s s' : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64) (j : Nat) (ins : Lin.Instr),
    MatchAt C P AP σ lo N s m fn f a j → fn.code[s.pc]? = some ins → pred ins →
    Lin.step κ P ω s = some s' →
    ∃ n m', (M abi).run ω (m, c) n = some (m', c + n) ∧
      ((∃ fn f a j, MatchAt C P AP σ lo N s' m' fn f a j) ∨
        (s'.world.halted = true ∧ m'.world = s'.world)) ∧
      (n = 0 → ticksAt P s' < ticksAt P s) ∧ RunAll abi ω (SpBound C P lo N) (m, c) n ∧
      n = cnt fn ins

/-- A step in the running activation takes `cnt fn ins` machine steps, at least one, that keep
the stack pointer, to a state related to the next Lin state with the same frame word. -/
def LocalOk (pred : Lin.Instr → Prop) : Prop :=
  ∀ (ω : Oracle) (κ : CostModel) (s : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64) (j : Nat) (ins : Lin.Instr),
    MatchAt C P AP σ lo N s m fn f a j → fn.code[s.pc]? = some ins → pred ins →
    ins.memOk P.mem s.frame = true →
    0 < cnt fn ins ∧ ∃ m', (M abi).run ω (m, c) (cnt fn ins) = some (m', c + cnt fn ins) ∧
      MatchAt C P AP σ lo N ((Lin.exec κ ω fn ins s).getD s) m' fn f a j ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp m.regs) (m, c) (cnt fn ins)

/-- A halting step takes `cnt fn ins` machine steps, at least one, that keep the stack pointer,
to a halted state with the next Lin state's world, which has halted too. -/
def HaltOk (pred : Lin.Instr → Prop) : Prop :=
  ∀ (ω : Oracle) (κ : CostModel) (s : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64) (j : Nat) (ins : Lin.Instr),
    MatchAt C P AP σ lo N s m fn f a j → fn.code[s.pc]? = some ins → pred ins →
    0 < cnt fn ins ∧ ∃ m', (M abi).run ω (m, c) (cnt fn ins) = some (m', c + cnt fn ins) ∧
      ((Lin.exec κ ω fn ins s).getD s).world.halted = true ∧
      m'.world = ((Lin.exec κ ω fn ins s).getD s).world ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp m.regs) (m, c) (cnt fn ins)

/-- One Lin step up to dead locations, the form of the fields of `Cases`. It is `StepOk`, except
that the machine may reach a state related to one that differs from the next Lin state only in
dead locations, such as a location a call left unsaved, and the count `cnt i pc fn ins` may
depend on the position. -/
def StepOkAt (F : RegAlloc.Flex P) (cnt : Nat → Nat → Lin.Fn → Lin.Instr → Nat)
    (pred : Lin.Instr → Prop) : Prop :=
  ∀ (ω : Oracle) (κ : CostModel) (s s' : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64) (j : Nat) (ins : Lin.Instr),
    MatchAt C P AP σ lo N s m fn f a j → fn.code[s.pc]? = some ins → pred ins →
    Lin.step κ P ω s = some s' →
    ∃ n m', (M abi).run ω (m, c) n = some (m', c + n) ∧
      ((∃ s'', F.R s' s'' ∧ ∃ fn f a j, MatchAt C P AP σ lo N s'' m' fn f a j) ∨
        (s'.world.halted = true ∧ m'.world = s'.world)) ∧
      (n = 0 → ticksAt P s' < ticksAt P s) ∧ RunAll abi ω (SpBound C P lo N) (m, c) n ∧
      n ≤ cnt s.fn s.pc fn ins

/-- `LocalOk` up to dead locations: the machine reaches a state related to one that agrees with
the next Lin state on the locations live there, as the validated live sets say. It is the
statement for a block that destroys locations, such as a system call. -/
def LocalOkK (pred : Lin.Instr → Prop) : Prop :=
  ∀ (ω : Oracle) (κ : CostModel) (s : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64) (j : Nat) (ins : Lin.Instr),
    MatchAt C P AP σ lo N s m fn f a j → fn.code[s.pc]? = some ins → pred ins →
    ins.memOk P.mem s.frame = true →
    0 < cnt fn ins ∧ ∃ m', (M abi).run ω (m, c) (cnt fn ins) = some (m', c + cnt fn ins) ∧
      (∃ s'', (RegAlloc.Live.flex P).R ((Lin.exec κ ω fn ins s).getD s) s'' ∧
        MatchAt C P AP σ lo N s'' m' fn f a j) ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp m.regs) (m, c) (cnt fn ins)

/-- The five extern calls a selector accepts. -/
def ExtShape (sym : String) (nr : Bool) (args : List Flat.ExtArg) : Prop :=
  (∃ o, sym = "exit" ∧ nr = true ∧ args = [.word o]) ∨
    (∃ o bs, sym = "write" ∧ nr = false ∧ args = [.word o, .bytes bs]) ∨
    (∃ o p l, sym = "write" ∧ nr = false ∧ args = [.word o, .mem p l]) ∨
    (∃ o, sym = "read" ∧ nr = false ∧ args = [.word o, .out 1]) ∨
    (∃ o p l, sym = "read" ∧ nr = false ∧ args = [.word o, .outMem p l])

variable (F : RegAlloc.Flex P) (cnt : Nat → Nat → Lin.Fn → Lin.Instr → Nat) in
/-- The cases of one Lin step for the selector `D`, up to the dead locations of `F`, with counts
`cnt` that may depend on the position. -/
structure Cases (D : Selector A) : Prop where
  mov : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ x o, i = .mov x o
  bin : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ op x a b, i = .bin op x a b
  load : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ w x a off, i = .load w x a off
  store : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ w a off b, i = .store w a off b
  jmp : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ l, i = .jmp l
  jz : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ o l, i = .jz o l
  call : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ g args d, i = .call g args d
  ret : StepOkAt abi C P AP σ lo N F cnt fun i => i = .ret
  exit : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ x o, i = .ext "exit" true x [.word o]
  write : StepOkAt abi C P AP σ lo N F cnt fun i =>
    ∃ x o bs, i = .ext "write" false x [.word o, .bytes bs]
  writeMem : StepOkAt abi C P AP σ lo N F cnt fun i =>
    ∃ x o p l, i = .ext "write" false x [.word o, .mem p l]
  read : StepOkAt abi C P AP σ lo N F cnt fun i => ∃ x o, i = .ext "read" false x [.word o, .out 1]
  readMem : StepOkAt abi C P AP σ lo N F cnt fun i =>
    ∃ x o p l, i = .ext "read" false x [.word o, .outMem p l]
  /-- A `tick` is selected to no code and costs nothing. -/
  tick : ∀ i pc fn t, cnt i pc fn (.tick t) = 0 ∧
    ∀ i pc b d, D.instr P i pc fn (.tick t) = .ok (b, d) → b = []
  /-- Every extern call the selector accepts has one of the five shapes. -/
  ext : ∀ i pc fn sym nr x args b d, D.instr P i pc fn (.ext sym nr x args) = .ok (b, d) →
    ExtShape sym nr args

end Statements

variable {A : Asm.Arch} {abi : Abi A.isa} {C : Conv A} {P : Lin.Prog} {AP : Asm.Prog A}
  {σ : String → Option UInt64} {lo N : Nat} {cnt : Lin.Fn → Lin.Instr → Nat}

/-- A Lin step from a related state executes the instruction at its position. -/
theorem step_getD {s s' : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A}
    {a : UInt64} {j : Nat} {ins : Lin.Instr} {κ : CostModel} {ω : Oracle}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hi : fn.code[s.pc]? = some ins)
    (hs : Lin.step κ P ω s = some s') :
    s' = (Lin.exec κ ω fn ins s).getD s ∧ ins.memOk P.mem s.frame = true := by
  obtain ⟨ins', hi', hmo, he⟩ := step_fetch_inv hM.run hM.hfn hs
  rw [hi] at hi'; cases hi'
  rw [he]; exact ⟨rfl, hmo⟩

theorem LocalOk.step {pred : Lin.Instr → Prop} (h : LocalOk abi C P AP σ lo N cnt pred) :
    StepOk abi C P AP σ lo N cnt pred := by
  intro ω κ s s' m c fn f a j ins hM hi hp hs
  obtain ⟨rfl, hmo⟩ := step_getD hM hi hs
  obtain ⟨hpos, m', h1, h2, h3⟩ := h ω κ s m c fn f a j ins hM hi hp hmo
  exact ⟨_, m', h1, Or.inl ⟨fn, f, a, j, h2⟩, fun h => absurd h (by omega),
    RunAll.mono (fun _ => spBound_of_keep hM) h3, rfl⟩

theorem HaltOk.step {pred : Lin.Instr → Prop} (h : HaltOk abi C P AP σ lo N cnt pred) :
    StepOk abi C P AP σ lo N cnt pred := by
  intro ω κ s s' m c fn f a j ins hM hi hp hs
  obtain ⟨rfl, -⟩ := step_getD hM hi hs
  obtain ⟨hpos, m', h1, h2, h3, h4⟩ := h ω κ s m c fn f a j ins hM hi hp
  exact ⟨_, m', h1, Or.inr ⟨h2, h3⟩, fun h => absurd h (by omega),
    RunAll.mono (fun _ => spBound_of_keep hM) h4, rfl⟩

theorem LocalOkK.stepAt {pred : Lin.Instr → Prop} (h : LocalOkK abi C P AP σ lo N cnt pred) :
    StepOkAt abi C P AP σ lo N (RegAlloc.Live.flex P) (fun _ _ => cnt) pred := by
  intro ω κ s s' m c fn f a j ins hM hi hp hs
  obtain ⟨rfl, hmo⟩ := step_getD hM hi hs
  obtain ⟨hpos, m', h1, ⟨s'', hR, h2⟩, h3⟩ := h ω κ s m c fn f a j ins hM hi hp hmo
  exact ⟨_, m', h1, Or.inl ⟨s'', hR, fn, f, a, j, h2⟩, fun h => absurd h (by omega),
    RunAll.mono (fun _ => spBound_of_keep hM) h3, Nat.le_refl _⟩

/-- A step that reaches the next Lin state itself, at a count that ignores the position. -/
theorem StepOk.at {pred : Lin.Instr → Prop} {cnt : Lin.Fn → Lin.Instr → Nat} (F : RegAlloc.Flex P)
    (h : StepOk abi C P AP σ lo N cnt pred) : StepOkAt abi C P AP σ lo N F (fun _ _ => cnt) pred := by
  intro ω κ s s' m c fn f a j ins hM hi hp hs
  obtain ⟨n, m', h1, h2, h3, h4, h5⟩ := h ω κ s s' m c fn f a j ins hM hi hp hs
  exact ⟨n, m', h1, h2.imp_left fun h => ⟨s', F.refl s', h⟩, h3, h4, Nat.le_of_eq h5⟩

theorem StepOkAt.of_eq {pred : Lin.Instr → Prop} {F : RegAlloc.Flex P}
    {c₁ c₂ : Nat → Nat → Lin.Fn → Lin.Instr → Nat} (h : StepOkAt abi C P AP σ lo N F c₁ pred)
    (e : ∀ i pc fn ins, pred ins → c₂ i pc fn ins = c₁ i pc fn ins) :
    StepOkAt abi C P AP σ lo N F c₂ pred := by
  intro ω κ s s' m c fn f a j ins hM hi hp hs
  obtain ⟨n, m', h1, h2, h3, h4, h5⟩ := h ω κ s s' m c fn f a j ins hM hi hp hs
  exact ⟨n, m', h1, h2, h3, h4, Nat.le_trans h5 (Nat.le_of_eq (e _ _ _ _ hp).symm)⟩

/-- The dispatch: given the cases, every Lin step from a state that agrees on its live locations
with a related state is matched, with the count of the instruction executed. -/
theorem Cases.step {asm : Asm.Assembler A} (hl : asm.Laws) {D : Selector A}
    (hsel : select D P = .ok AP) (hwf : P.Wf) {F : RegAlloc.Flex P}
    {cnt : Nat → Nat → Lin.Fn → Lin.Instr → Nat} (h : Cases abi C P AP σ lo N F cnt D)
    (ω : Oracle) (κ : CostModel) (s₀ s' : Lin.State) (m : MState A.isa.Regs) (c : Nat)
    (hM : ∃ s, F.R s₀ s ∧ ∃ fn f a j, MatchAt C P AP σ lo N s m fn f a j)
    (hs₀ : Lin.step κ P ω s₀ = some s') :
    ∃ n m', (M abi).run ω (m, c) n = some (m', c + n) ∧
      ((∃ s, F.R s' s ∧ ∃ fn f a j, MatchAt C P AP σ lo N s m' fn f a j) ∨
        (s'.world.halted = true ∧ m'.world = s'.world)) ∧
      (n = 0 → ticksAt P s' < ticksAt P s₀) ∧ RunAll abi ω (SpBound C P lo N) (m, c) n ∧
      ∀ fn ins, P.funs[s₀.fn]? = some fn → fn.code[s₀.pc]? = some ins →
        n ≤ cnt s₀.fn s₀.pc fn ins := by
  obtain ⟨s, hR, fn, f, a, j, hM⟩ := hM
  obtain ⟨t', hs, hR'⟩ := F.step hR hs₀
  obtain ⟨hfn, hpc, -⟩ := F.same hR
  obtain ⟨-, -, hw'⟩ := F.same hR'
  have htk : ∀ {u v : Lin.State}, F.R u v → ticksAt P v = ticksAt P u := fun h => by
    obtain ⟨h1, h2, -⟩ := F.same h; simp only [ticksAt, h1, h2]
  obtain ⟨ins, hi, -, -⟩ := step_fetch_inv hM.run hM.hfn hs
  obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  suffices key : StepOkAt abi C P AP σ lo N F cnt (· = ins) by
    obtain ⟨n, m', h1, h2, h3, h4, h5⟩ := key ω κ s t' m c fn f a j ins hM hi rfl hs
    refine ⟨n, m', h1, ?_, fun h0 => by rw [← htk hR', ← htk hR]; exact h3 h0, h4,
      fun fn' ins' hf' hi' => ?_⟩
    · rcases h2 with ⟨s'', h, hM'⟩ | ⟨hh, hw⟩
      · exact Or.inl ⟨s'', F.trans hR' h, hM'⟩
      · exact Or.inr ⟨hw' ▸ hh, hw.trans hw'⟩
    · rw [← hfn, hM.hfn] at hf'; cases hf'; rw [← hpc, hi] at hi'; cases hi'
      rw [← hfn, ← hpc]; exact h5
  have mono : ∀ {pred : Lin.Instr → Prop}, StepOkAt abi C P AP σ lo N F cnt pred → pred ins →
      StepOkAt abi C P AP σ lo N F cnt (· = ins) := fun hp hq ω κ s s' m c fn f a j i hM hi he hs =>
    hp ω κ s s' m c fn f a j i hM hi (he ▸ hq) hs
  cases ins with
  | mov x o => exact mono h.mov ⟨x, o, rfl⟩
  | bin op x o₁ o₂ => exact mono h.bin ⟨op, x, o₁, o₂, rfl⟩
  | load w x o off => exact mono h.load ⟨w, x, o, off, rfl⟩
  | store w o off o' => exact mono h.store ⟨w, o, off, o', rfl⟩
  | jmp l => exact mono h.jmp ⟨l, rfl⟩
  | jz o l => exact mono h.jz ⟨o, l, rfl⟩
  | call g args d => exact mono h.call ⟨g, args, d, rfl⟩
  | ret => exact mono h.ret rfl
  | ext sym nr x args =>
    rcases h.ext _ _ _ _ _ _ _ _ _ hsi with ⟨o, rfl, rfl, rfl⟩ | ⟨o, bs, rfl, rfl, rfl⟩ |
      ⟨o, p, l, rfl, rfl, rfl⟩ | ⟨o, rfl, rfl, rfl⟩ | ⟨o, p, l, rfl, rfl, rfl⟩
    · exact mono h.exit ⟨x, o, rfl⟩
    · exact mono h.write ⟨x, o, bs, rfl⟩
    · exact mono h.writeMem ⟨x, o, p, l, rfl⟩
    · exact mono h.read ⟨x, o, rfl⟩
    · exact mono h.readMem ⟨x, o, p, l, rfl⟩
  | tick t =>
    intro ω κ s s' m c fn f a j i hM hi he hs
    subst he
    obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
    obtain ⟨d, hsi, -⟩ := hC.instr
    obtain ⟨h0, hb⟩ := h.tick s.fn s.pc fn t
    obtain rfl := hb _ _ _ _ hsi
    obtain ⟨rfl, -⟩ := step_getD hM hi hs
    have hd := ticksAt_tick (κ := κ) (ω := ω) hM.hfn hi
    have hM' := matchAt_tick (κ := κ) (ω := ω) hM hi hC.blk
    exact ⟨0, m, rfl, Or.inl ⟨_, F.refl _, fn, f, a, j, hM'⟩, fun _ => hd,
      RunAll.zero (spBound_of_keep hM rfl), Nat.zero_le _⟩

section Pkg
variable (abi C P AP σ lo N)

/-- The package of an ISA whose relation is `MatchAt` at its convention `C`, up to dead
locations: the machine is related to some state that agrees with the Lin state as `F` says. -/
def pkg (F : RegAlloc.Flex P) (Init : MState A.isa.Regs → Prop) (counts : Counts) : SimPkg abi P where
  Match s m := ∃ t, F.R s t ∧ ∃ fn f a j, MatchAt C P AP σ lo N t m fn f a j
  Init := Init
  SpOk := SpBound C P lo N
  counts := counts

variable {abi C P AP σ lo N}

/-- `pkg` satisfies its laws, given the cases and the entry sequence. -/
theorem pkg_laws {asm : Asm.Assembler A} (hl : asm.Laws) {D : Selector A}
    (hsel : select D P = .ok AP) (hwf : P.Wf) {F : RegAlloc.Flex P}
    {Init : MState A.isa.Regs → Prop} {counts : Counts}
    (hc : Cases abi C P AP σ lo N F (counts.ins P) D)
    (hiw : ∀ m, Init m → m.world = World.init) (his : ∀ m, Init m → SpBound C P lo N m)
    (hpos : 0 < counts.entry P)
    (hentry : ∀ ω m₀ c, Init m₀ → ∃ m₁, (M abi).run ω (m₀, c) (counts.entry P) =
      some (m₁, c + counts.entry P) ∧ (∃ fn f a j, MatchAt C P AP σ lo N P.init m₁ fn f a j) ∧
      RunAll abi ω (SpBound C P lo N) (m₀, c) (counts.entry P)) :
    (pkg abi C P AP σ lo N F Init counts).Laws where
  run _ _ := fun ⟨_, hR, _, _, _, _, hM⟩ => by
    obtain ⟨-, -, hw⟩ := F.same hR
    exact ⟨hw ▸ hM.run, hM.world.trans hw⟩
  init_world := hiw
  init_sp := his
  entry_pos := hpos
  entry ω m₀ c hI := by
    obtain ⟨m₁, h1, h2, h3⟩ := hentry ω m₀ c hI
    exact ⟨m₁, h1, ⟨_, F.refl _, h2⟩, h3⟩
  step ω κ s s' m c hM hs := hc.step hl hsel hwf ω κ s s' m c hM hs

end Pkg

/-! ## Blocks that destroy locations -/

/-- The value of location `y` of the running frame at word `j` in a machine state: its register
below `k + c`, its stack word above. -/
def locVal (C : Conv A) (lo : Nat) (m : MState A.isa.Regs) (j y : Nat) : UInt64 :=
  if y < C.k + C.c then C.reg m.regs y else word m.mem lo (j + y - C.c)

/-- The frame `fr` with the locations that `ins` destroys and does not define replaced by what the
machine holds there. -/
def killFrame (C : Conv A) (P : Lin.Prog) (ins : Lin.Instr) (lo : Nat) (m : MState A.isa.Regs)
    (j : Nat) (fr : Flat.Frame) : Flat.Frame := fun y =>
  if C.kill ins y = true ∧ RegAlloc.Live.defs P ins y = false then locVal C lo m j y else fr y

/-- The running frame's locations hold `killFrame` when they hold the frame at every location the
instruction does not destroy or defines. -/
theorem locsOk_kill {ins : Lin.Instr} {m : MState A.isa.Regs} {j F : Nat} {fr : Flat.Frame}
    (hS : ∀ y, y < F → (C.kill ins y = false ∨ RegAlloc.Live.defs P ins y = true) →
      locVal C lo m j y = fr y) :
    LocsOk lo C.k C.c (C.reg m.regs) m.mem j F (killFrame C P ins lo m j fr) := fun y hy => by
  show locVal C lo m j y = killFrame C P ins lo m j fr y
  simp only [killFrame]
  split
  · rfl
  · rename_i h
    refine hS y hy ?_
    cases h1 : C.kill ins y
    · exact Or.inl rfl
    · cases h2 : RegAlloc.Live.defs P ins y
      · exact absurd ⟨h1, h2⟩ h
      · exact Or.inr rfl

/-- The clobber check of the convention's clobber set, which holds trivially when the set is
empty. -/
def ClobOk (C : Conv A) (P : Lin.Prog) : Prop :=
  RegAlloc.Live.clobOk C.kill (RegAlloc.Live.of P) P = true ∨ ∀ ins y, C.kill ins y = false

/-- `killFrame` is related to the frame after the instruction, when the clobber check holds. -/
theorem R_killFrame (hclob : ClobOk C P)
    {i pc : Nat} {fn : Lin.Fn} {ins : Lin.Instr} (hfn : P.funs[i]? = some fn)
    (hi : fn.code[pc]? = some ins) (m : MState A.isa.Regs) (j : Nat) {fr : Flat.Frame}
    {st : List Lin.Act} {mem : Flat.Heap} {w : World} {clk : Nat} :
    (RegAlloc.Live.flex P).R ⟨i, pc + 1, fr, st, mem, w, clk⟩
      ⟨i, pc + 1, killFrame C P ins lo m j fr, st, mem, w, clk⟩ := by
  rcases hclob with hclob | hnil
  · exact RegAlloc.Live.R_kill P hclob hfn hi fun x hx => by
      simp only [killFrame]
      rw [ite_eq_right (by rcases hx with h | h <;> simp [h])]
  · have : killFrame C P ins lo m j fr = fr := funext fun y => by simp [killFrame, hnil]
    rw [this]; exact (RegAlloc.Live.flex P).refl _

/-- A block of straight-line code that destroys the locations of `C.kill ins`: when the clobber
check holds and the machine's locations hold the next Lin state's frame at every location the
block does not destroy or defines, the machine is matched to a state related to the next Lin state
up to dead locations. -/
theorem sim_straight_kill {asm : Asm.Assembler A} (hl : asm.Laws) (hil : A.isa.Laws)
    {abi : Abi A.isa} {ω : Oracle} {s s' : Lin.State} {m m' : MState A.isa.Regs} {fn : Lin.Fn}
    {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    {ins : Lin.Instr} (hi : fn.code[s.pc]? = some ins)
    (hclob : ClobOk C P) {b : List A.SInstr}
    (hblk : f.blocks[s.pc]? = some b) {is : List A.isa.Instr} {code : List UInt8}
    (hr : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b = some is)
    (he : Asm.encodeAll A.isa is = some code)
    (hcode : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) code)
    (hs : ∀ i ∈ is, StraightC C abi ω i) (hrun : runIs abi ω is m = some m')
    (hw : m'.world = s'.world) (hh : s'.world.halted = false) (hfn : s'.fn = s.fn)
    (hst : s'.stack = s.stack) (hpc : s'.pc = s.pc + 1)
    (hS : ∀ y, y < fn.frame → (C.kill ins y = false ∨ RegAlloc.Live.defs P ins y = true) →
      locVal C lo m' j y = s'.frame y)
    (hsave : ∀ x, x < min C.k fn.frame → word m'.mem lo (j + x) = word m.mem lo (j + x))
    (hc : ∀ k, j + frameW C.k C.c fn.frame ≤ k → k < N → word m'.mem lo k = word m.mem lo k)
    (hreg : ∀ x, fn.frame ≤ x → x < C.k → C.reg m'.regs x = C.reg m.regs x)
    (hD : DataOk P σ lo m'.mem s'.mem) (c : Nat) :
    (M abi).run ω (m, c) is.length = some (m', c + is.length) ∧
      (∃ s'', (RegAlloc.Live.flex P).R s' s'' ∧ MatchAt C P AP σ lo N s'' m' fn f a j) ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp m.regs) (m, c) is.length := by
  obtain ⟨r1, r2, r3⟩ := sim_straight (s' := { s' with frame := killFrame C P ins lo m' j s'.frame })
    hl hil hM hblk (pc_lt hi) hr he hcode hs hrun hw hh hfn hst hpc (locsOk_kill hS) hsave hc hreg
    hD c
  refine ⟨r1, ⟨_, ?_, r2⟩, r3⟩
  obtain ⟨fn', pc', fr', st', mem', w', clk'⟩ := s'
  simp only at hfn hpc ⊢
  subst hfn hpc
  exact R_killFrame hclob hM.hfn hi m' j

/-- The relation back in the caller after a call whose sequence destroys the locations of
`C.kill`: `matchAt_ret`, where the caller's locations must hold the next frame `fr` only where the
call does not destroy them or defines them (its results), and the machine is matched to a state
related to the next Lin state up to dead locations. -/
theorem matchAt_ret_kill {s : Lin.State} {m m' : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A}
    {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j) {act : Lin.Act}
    {st : List Lin.Act} (hst : s.stack = act :: st) {fa : Lin.Fn} (hfa : P.funs[act.fn]? = some fa)
    {fc : Asm.Fn A} (hfc : AP.funs[act.fn]? = some fc) {addr : UInt64}
    (haddr : σ fc.name = some addr) (hpcL : act.pc ≤ fa.code.length) {j' : Nat}
    (hj : j' = j + C.next fn.frame) (hφ : C.φ.frame fn.frame = 8 * C.next fn.frame)
    (hw : m'.world = m.world) (hF : Memory.Frame m.mem m'.mem) (hlow : LowSame lo m.mem m'.mem)
    (hR : Region m'.mem lo N) (hok : C.ok addr lo j')
    (hpc : A.isa.pc m'.regs = addr + UInt64.ofNat (fc.labelOff act.pc))
    (hsp : A.isa.sp m'.regs = wa lo j')
    (hclob : ClobOk C P) {ins : Lin.Instr}
    (h0 : 0 < act.pc) (hcall : fa.code[act.pc - 1]? = some ins) {fr : Flat.Frame}
    (hL : ∀ y, y < fa.frame → (C.kill ins y = false ∨ RegAlloc.Live.defs P ins y = true) →
      locVal C lo m' j' y = fr y)
    (hsave : ∀ x, x < min C.k fa.frame → word m'.mem lo (j' + x) = word m.mem lo (j' + x))
    (hc : ∀ i, j' + frameW C.k C.c fa.frame ≤ i → i < N → word m'.mem lo i = word m.mem lo i)
    (hreg : ∀ x, fa.frame ≤ x → x < C.k →
      C.reg m'.regs x = callerView lo C.k m.mem j fn.frame (C.reg m.regs) x)
    (hB : C.regOk σ m'.regs) :
    ∃ s'', (RegAlloc.Live.flex P).R ⟨act.fn, act.pc, fr, st, s.mem, s.world, s.clock⟩ s'' ∧
      MatchAt C P AP σ lo N s'' m' fa fc addr j' := by
  refine ⟨_, ?_, matchAt_ret hM hst hfa hfc haddr hpcL hj hφ hw hF hlow hR hok hpc hsp
    (locsOk_kill hL) hsave hc hreg hB⟩
  obtain ⟨p, hp⟩ : ∃ p, act.pc = p + 1 := ⟨act.pc - 1, by omega⟩
  rw [hp] at hcall ⊢
  exact R_killFrame hclob hfa hcall m' j'

end Millipede.Sel
