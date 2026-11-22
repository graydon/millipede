import Millipede.Compile.Flat
import Millipede.Target.Target

/-!
# The Lin language

Lin is Flat with its structured control replaced by labels and jumps, and with calls made between
numbered functions instead of carrying the callee's code at the call site. A program is a list of
functions `funs` with the index `main` of the entry function. A function has an explicit frame size
in word slots, a code list, and the operands `ret` whose values, read in its own frame, it returns.
Every temporary lives in a frame slot, and there are no registers.

The instructions behave as follows:

- `jmp l` and `jz c l` set the program counter to `l`, an index into the current function's code.
- `call f args dst` evaluates the argument words in the caller's frame, pushes an activation record
  holding the caller, the return position, the caller's frame and `dst`, and enters `f` at position
  `0` with a fresh frame that holds the arguments in slots `0, 1, …` and zeros elsewhere. `ret` pops
  the record and writes the function's `ret` operands, evaluated in the callee's frame, to the
  caller's slots `dst, dst+1, …`.
- `load` and `store` access the byte memory, whose data region is `[0, Prog.mem)`. An access
  outside the region is stuck, so a Lin program that never gets stuck touches only its data region.
- `ext` calls an extern exactly as Flat does, with the same call record, and writes the reply's
  bytes when the call has an output buffer in memory.
- `tick t` pays for one Core construct, so the clock is the sum of the `κ`-weights of the ticks
  executed, as in Flat. Every other instruction is free, which gives the passes into and out of Lin
  a resource factor of `1`.

`step κ P ω s` fetches the instruction at `(s.fn, s.pc)`. A missing function, a pc outside the
code, a `ret` with an empty stack and a memory access outside the data region are stuck, and a
state whose world has halted steps to itself.

The stack depth `State.depth φ P s` counts one `φ.frame` per activation, the running one and every
suspended one. `Prog.stackBytes φ P` is its static maximum over call paths, computed function by
function, and `depth_le` proves that every state reached from `P.init` stays within it when calls
go only to functions with a smaller index, so that there is no recursion. `Prog.Wf` is the
well-formedness that `select` relies on. Every slot a function uses is below its declared frame,
jump targets are inside the code, callees have smaller indices, argument counts fit the callee's
frame, and returned words fit the caller's frame.

See doc/design/compiler.md.
-/

namespace Millipede.Lin

open Flat (Operand BinOp Width Tick ExtArg Frame Heap)

/-- Lin instructions. -/
inductive Instr where
  /-- `x := a`. -/
  | mov (x : Nat) (a : Operand)
  /-- `x := op a b`. -/
  | bin (op : BinOp) (x : Nat) (a b : Operand)
  /-- `x := mem[a + off]`. -/
  | load (w : Flat.Width) (x : Nat) (a : Operand) (off : UInt64)
  /-- `mem[a + off] := b`. -/
  | store (w : Flat.Width) (a : Operand) (off : UInt64) (b : Operand)
  /-- `pc := l`. -/
  | jmp (l : Nat)
  /-- `pc := l` when `c = 0`, and otherwise falls through. -/
  | jz (c : Operand) (l : Nat)
  /-- Calls function number `f` with the argument words `args`, and its results go to
  `dst, dst+1, …`. -/
  | call (f : Nat) (args : List Operand) (dst : Nat)
  /-- Returns the current function's `ret` operands to the caller. -/
  | ret
  /-- Calls an extern, and the result word goes to slot `x`. -/
  | ext (sym : String) (noreturn : Bool) (x : Nat) (args : List ExtArg)
  /-- Pays for one Core construct. -/
  | tick (t : Tick)
deriving Repr, Inhabited

/-- A Lin function has a name for symbols, a declared frame size in words, code, and the operands
it returns. -/
structure Fn where
  name : String
  frame : Nat
  code : List Instr
  ret : List Operand
deriving Repr, Inhabited

/-- A Lin program has functions referred to by index, an entry function, and a data region. The
program's memory is the `mem` bytes at addresses `[0, mem)`, which hold the static storage of
`lower`, the root and every activation's values, and a `load` or `store` touching any other byte
is stuck. -/
structure Prog where
  funs : List Fn
  main : Nat
  mem : Nat
deriving Repr, Inhabited

/-- An access of width `w` at address `a` lies in the data region `[0, M)`. -/
def inData (M : Nat) (a : UInt64) (w : Flat.Width) : Bool := decide (a.toNat + w.bytes ≤ M)

/-- The `n` bytes from address `a` lie in the data region `[0, M)`. -/
def inDataN (M : Nat) (a : UInt64) (n : Nat) : Bool := decide (a.toNat + n ≤ M)

/-- The memory buffers of an extern call lie in the data region `M`, in frame `fr`. -/
def extMemOk (M : Nat) (fr : Frame) : List ExtArg → Bool
  | [] => true
  | .mem a n :: as => inDataN M (a.eval fr) (n.eval fr).toNat && extMemOk M fr as
  | .outMem a n :: as => inDataN M (a.eval fr) (n.eval fr).toNat && extMemOk M fr as
  | _ :: as => extMemOk M fr as

/-- The memory access of instruction `i`, if any, lies in the data region `M`, in frame `fr`. -/
def Instr.memOk (M : Nat) (fr : Frame) : Instr → Bool
  | .load w _ a off => inData M (a.eval fr + off) w
  | .store w a off _ => inData M (a.eval fr + off) w
  | .ext _ _ _ args => extMemOk M fr args
  | _ => true

/-- A suspended activation: the caller's function, its return position, its frame, and where
the callee's results go. -/
structure Act where
  fn : Nat
  pc : Nat
  frame : Frame
  dst : Nat

/-- A Lin machine state. -/
structure State where
  fn : Nat
  pc : Nat
  frame : Frame
  stack : List Act
  mem : Heap
  world : World
  clock : Nat

/-- The initial state: `main` at position `0`, zero frame, empty stack, zero memory. -/
def Prog.init (P : Prog) : State :=
  ⟨P.main, 0, Frame.zero, [], fun _ => 0, World.init, 0⟩

/-- Executes one instruction `i` of the running function `fn` in state `s`. -/
def exec (κ : CostModel) (ω : Oracle) (fn : Fn) (i : Instr) (s : State) : Option State :=
  match i with
  | .mov x a => some { s with pc := s.pc + 1, frame := s.frame.set x (a.eval s.frame) }
  | .bin op x a b =>
    some { s with pc := s.pc + 1,
                  frame := s.frame.set x (op.eval (a.eval s.frame) (b.eval s.frame)) }
  | .load w x a off =>
    some { s with pc := s.pc + 1, frame := s.frame.set x (s.mem.load w (a.eval s.frame + off)) }
  | .store w a off b =>
    some { s with pc := s.pc + 1, mem := s.mem.store w (a.eval s.frame + off) (b.eval s.frame) }
  | .jmp l => some { s with pc := l }
  | .jz c l => some { s with pc := if c.eval s.frame = 0 then l else s.pc + 1 }
  | .call f args d =>
    some { s with fn := f, pc := 0, frame := Frame.ofList (args.map (Operand.eval s.frame)),
                  stack := ⟨s.fn, s.pc + 1, s.frame, d⟩ :: s.stack }
  | .ret =>
    match s.stack with
    | [] => none
    | a :: st =>
      some { s with fn := a.fn, pc := a.pc, stack := st,
                    frame := a.frame.writes a.dst (fn.ret.map (Operand.eval s.frame)) }
  | .ext sym nr x args =>
    let r := Flat.extRun ω sym nr args s.frame s.mem s.world
    some { s with pc := s.pc + 1, frame := s.frame.set x r.1, mem := r.2.1, world := r.2.2 }
  | .tick t => some { s with pc := s.pc + 1, clock := s.clock + t.cost κ }

/-- One transition. A halted state stutters, and otherwise the instruction is fetched and
executed, with `none` meaning stuck. -/
def step (κ : CostModel) (P : Prog) (ω : Oracle) (s : State) : Option State :=
  if s.world.halted then some s
  else
    match P.funs[s.fn]? with
    | none => none
    | some fn =>
      match fn.code[s.pc]? with
      | none => none
      | some i => if i.memOk P.mem s.frame then exec κ ω fn i s else none

/-- Lin as a `Sem` for cost model `κ` and program `P`. Its events are the world's, and its clock is
the sum of the ticks executed. -/
abbrev sem (κ : CostModel) (P : Prog) : Sem where
  State := State
  step ω s := step κ P ω s
  events s := s.world.events
  clock s := s.clock

theorem exec_mono (κ : CostModel) (ω : Oracle) (fn : Fn) (i : Instr) (s s' : State)
    (h : exec κ ω fn i s = some s') :
    s.world.events <+: s'.world.events ∧ s.clock ≤ s'.clock := by
  cases i <;> simp only [exec, Option.some.injEq] at h
  case ret =>
    split at h
    · cases h
    · cases h; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  case ext => subst h; exact ⟨Flat.extRun_prefix .., Nat.le_refl _⟩
  case tick => subst h; exact ⟨List.prefix_refl _, Nat.le_add_right _ _⟩
  all_goals (subst h; exact ⟨List.prefix_refl _, Nat.le_refl _⟩)

theorem step_mono (κ : CostModel) (P : Prog) (ω : Oracle) (s s' : State)
    (h : step κ P ω s = some s') :
    s.world.events <+: s'.world.events ∧ s.clock ≤ s'.clock := by
  unfold step at h
  split at h
  · cases h; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · exact exec_mono κ ω _ _ s s' h
        · cases h

/-- Lin only extends the trace and never decreases the clock. -/
theorem sem_mono (κ : CostModel) (P : Prog) : (sem κ P).Mono where
  events ω s s' h := (step_mono κ P ω s s' h).1
  clock ω s s' h := (step_mono κ P ω s s' h).2

/-- A halted state stutters. -/
theorem step_halted (κ : CostModel) (P : Prog) (ω : Oracle) (s : State)
    (h : s.world.halted = true) : step κ P ω s = some s := by
  simp [step, h]

/-- A running state with function `fn` and instruction `i` at its pc, whose memory access, if any,
lies in the data region, executes `i`. -/
theorem step_fetch {κ : CostModel} {P : Prog} {ω : Oracle} {s : State} {fn : Fn} {i : Instr}
    (hw : s.world.halted = false) (hf : P.funs[s.fn]? = some fn) (hi : fn.code[s.pc]? = some i)
    (hm : i.memOk P.mem s.frame = true) :
    step κ P ω s = exec κ ω fn i s := by
  simp [step, hw, hf, hi, hm]

/-! ## Stack depth -/

/-- The bytes of stack of one activation of function `f` under `φ`, which is `0` for a missing
function. -/
def Prog.frameBytes (φ : FrameModel) (P : Prog) (f : Nat) : Nat :=
  match P.funs[f]? with
  | some fn => φ.frame fn.frame
  | none => 0

/-- The stack in bytes: the running activation plus every suspended one. -/
def State.depth (φ : FrameModel) (P : Prog) (s : State) : Nat :=
  P.frameBytes φ s.fn + (s.stack.map (fun a => P.frameBytes φ a.fn)).sum

/-- The largest stack need of the callees in `code`, given the needs `acc` of the functions before
it. A call to an unknown index counts `0`. -/
def callMax (acc : List Nat) : List Instr → Nat
  | [] => 0
  | .call g _ _ :: is => max (acc.getD g 0) (callMax acc is)
  | _ :: is => callMax acc is

/-- The stack need of function `fn`, its frame plus its deepest callee, given the needs `acc` of
the functions before it. -/
def fnNeed (φ : FrameModel) (acc : List Nat) (fn : Fn) : Nat :=
  φ.frame fn.frame + callMax acc fn.code

/-- The needs of the functions `fs`, appended to `acc`, by structural recursion on `fs`. -/
def needsFrom (φ : FrameModel) (acc : List Nat) : List Fn → List Nat
  | [] => acc
  | f :: fs => needsFrom φ (acc ++ [fnNeed φ acc f]) fs

/-- The stack need of each function, its frame plus the maximum of the callees' needs over its call
instructions. In a `CallsDown` program the callees have smaller indices. -/
def needs (φ : FrameModel) (fs : List Fn) : List Nat := needsFrom φ [] fs

/-- The static stack bound of a program is the need of `main`, the maximum over call paths of the
sum of the frames, in bytes under `φ`. -/
def Prog.stackBytes (φ : FrameModel) (P : Prog) : Nat := (needs φ P.funs).getD P.main 0

/-- Calls go only to functions with a smaller index, so there is no recursion. -/
def Prog.CallsDown (P : Prog) : Prop :=
  ∀ i fn, P.funs[i]? = some fn → ∀ g args d, Instr.call g args d ∈ fn.code → g < i

theorem needsFrom_prefix (φ : FrameModel) :
    ∀ (fs : List Fn) (acc : List Nat), acc <+: needsFrom φ acc fs
  | [], acc => List.prefix_refl acc
  | _ :: fs, acc => (List.prefix_append acc _).trans (needsFrom_prefix φ fs _)

theorem needsFrom_length (φ : FrameModel) :
    ∀ (fs : List Fn) (acc : List Nat), (needsFrom φ acc fs).length = acc.length + fs.length
  | [], acc => by simp [needsFrom]
  | f :: fs, acc => by
    simp only [needsFrom, needsFrom_length φ fs, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem needsFrom_get (φ : FrameModel) :
    ∀ (fs : List Fn) (acc : List Nat) (i : Nat) (h : i < fs.length),
      (needsFrom φ acc fs)[acc.length + i]? =
        some (fnNeed φ ((needsFrom φ acc fs).take (acc.length + i)) fs[i])
  | [], _, _, h => by simp at h
  | f :: fs, acc, 0, _ => by
    have hp := needsFrom_prefix φ fs (acc ++ [fnNeed φ acc f])
    obtain ⟨r, hr⟩ := hp
    simp only [needsFrom, ← hr, Nat.add_zero, List.getElem_cons_zero]
    simp
  | f :: fs, acc, i + 1, h => by
    have := needsFrom_get φ fs (acc ++ [fnNeed φ acc f]) i (by simp at h; omega)
    simp only [List.length_append, List.length_singleton] at this
    simp only [needsFrom, List.getElem_cons_succ]
    rw [show acc.length + (i + 1) = acc.length + 1 + i by omega]
    exact this

theorem needs_length (φ : FrameModel) (fs : List Fn) : (needs φ fs).length = fs.length := by
  simp [needs, needsFrom_length]

/-- The need of function `i` is computed from the needs of the functions before it. -/
theorem needs_get (φ : FrameModel) (fs : List Fn) (i : Nat) (fn : Fn) (h : fs[i]? = some fn) :
    (needs φ fs)[i]? = some (fnNeed φ ((needs φ fs).take i) fn) := by
  have hi : i < fs.length := by
    rcases Nat.lt_or_ge i fs.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  have := needsFrom_get φ fs [] i hi
  simp only [List.length_nil, Nat.zero_add] at this
  have hfn : fs[i] = fn := by simp [List.getElem?_eq_getElem hi] at h; exact h
  rw [← hfn]; exact this

theorem callMax_ge (acc : List Nat) :
    ∀ (code : List Instr) (g : Nat) (args : List Operand) (d : Nat),
      Instr.call g args d ∈ code → acc.getD g 0 ≤ callMax acc code
  | [], _, _, _, h => by simp at h
  | i :: is, g, args, d, h => by
    rcases List.mem_cons.1 h with h | h
    · subst h; simp only [callMax]; exact Nat.le_max_left _ _
    · have := callMax_ge acc is g args d h
      cases i <;> simp only [callMax] <;> omega

/-- One activation fits in its function's need. -/
theorem frameBytes_le (φ : FrameModel) (P : Prog) (f : Nat) :
    P.frameBytes φ f ≤ (needs φ P.funs).getD f 0 := by
  unfold Prog.frameBytes
  split
  · rename_i fn hf
    simp only [List.getD_eq_getElem?_getD, needs_get φ _ _ _ hf, Option.getD_some, fnNeed]
    omega
  · exact Nat.zero_le _

/-- The stack invariant: walking from the running function down the stack, each callee's need
plus its caller's frame fits in the caller's need, and the bottom function is `main`. -/
def Chain (φ : FrameModel) (P : Prog) : Nat → List Act → Prop
  | f, [] => f = P.main
  | f, a :: st =>
    (needs φ P.funs).getD f 0 + P.frameBytes φ a.fn ≤ (needs φ P.funs).getD a.fn 0 ∧
      Chain φ P a.fn st

theorem chain_le (φ : FrameModel) (P : Prog) :
    ∀ (st : List Act) (f : Nat), Chain φ P f st →
      (needs φ P.funs).getD f 0 + (st.map (fun a => P.frameBytes φ a.fn)).sum ≤ P.stackBytes φ
  | [], _, h => by simp only [Chain] at h; subst h; simp [Prog.stackBytes]
  | a :: st, f, h => by
    have := chain_le φ P st a.fn h.2
    simp only [List.map_cons, List.sum_cons]
    have := h.1
    omega

/-- Under the invariant, the depth is within the static bound. -/
theorem depth_le_of_chain (φ : FrameModel) (P : Prog) (s : State) (h : Chain φ P s.fn s.stack) :
    s.depth φ P ≤ P.stackBytes φ := by
  have h₁ := chain_le φ P s.stack s.fn h
  have h₂ := frameBytes_le φ P s.fn
  unfold State.depth; omega

/-- A call from function `i` to some `g < i` satisfies the invariant's step. -/
theorem need_call (φ : FrameModel) (P : Prog) (i : Nat) (fn : Fn) (hf : P.funs[i]? = some fn)
    (g : Nat) (args : List Operand) (d : Nat) (hc : Instr.call g args d ∈ fn.code) (hg : g < i) :
    (needs φ P.funs).getD g 0 + P.frameBytes φ i ≤ (needs φ P.funs).getD i 0 := by
  have h₁ := callMax_ge ((needs φ P.funs).take i) fn.code g args d hc
  have h₂ : ((needs φ P.funs).take i).getD g 0 = (needs φ P.funs).getD g 0 := by
    simp [List.getD_eq_getElem?_getD, hg]
  simp only [List.getD_eq_getElem?_getD, needs_get φ _ _ _ hf, Option.getD_some, fnNeed,
    Prog.frameBytes, hf] at h₁ h₂ ⊢
  omega

theorem chain_step (κ : CostModel) (φ : FrameModel) (P : Prog) (hP : P.CallsDown) (ω : Oracle)
    (s s' : State) (h : step κ P ω s = some s') (hc : Chain φ P s.fn s.stack) :
    Chain φ P s'.fn s'.stack := by
  unfold step at h
  split at h
  · cases h; exact hc
  · split at h
    · cases h
    · rename_i fn hf
      split at h
      · cases h
      · rename_i i hi
        have hmem : i ∈ fn.code := List.mem_of_getElem? hi
        cases hmo : i.memOk P.mem s.frame with
        | false => simp [hmo] at h
        | true =>
          simp only [hmo, ite_true] at h
          clear hmo
          cases i <;> simp only [exec, Option.some.injEq] at h
          case call g args d =>
            subst h
            exact ⟨need_call φ P s.fn fn hf g args d hmem (hP _ _ hf _ _ _ hmem), hc⟩
          case ret =>
            split at h
            · cases h
            · rename_i a st hst
              cases h; rw [hst] at hc; exact hc.2
          all_goals (subst h; exact hc)

/-- The stack bound. In a program whose calls go down, every state reached from `P.init` has stack
depth at most `P.stackBytes φ`, for every frame model `φ`. -/
theorem depth_le (κ : CostModel) (φ : FrameModel) (P : Prog) (hP : P.CallsDown) (ω : Oracle)
    (n : Nat) (s : State) (h : (sem κ P).run ω P.init n = some s) :
    s.depth φ P ≤ P.stackBytes φ := by
  suffices ∀ n (s₀ s : State), Chain φ P s₀.fn s₀.stack →
      (sem κ P).run ω s₀ n = some s →
      Chain φ P s.fn s.stack from
    depth_le_of_chain φ P s (this n P.init s rfl h)
  intro n
  induction n with
  | zero => intro s₀ s hc h; cases h; exact hc
  | succ n ih =>
    intro s₀ s hc h
    rw [Sem.run_succ] at h
    cases hs : step κ P ω s₀ with
    | none => simp [hs] at h
    | some s₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih s₁ s (chain_step κ φ P hP ω s₀ s₁ hs hc) h

theorem needsFrom_append (φ : FrameModel) :
    ∀ (a b : List Fn) (acc : List Nat),
      needsFrom φ acc (a ++ b) = needsFrom φ (needsFrom φ acc a) b
  | [], _, _ => rfl
  | f :: a, b, acc => needsFrom_append φ a b (acc ++ [fnNeed φ acc f])

/-- The needs of a prefix of the functions are the prefix of the needs. -/
theorem needs_take (φ : FrameModel) (F : List Fn) (g : Nat) :
    needs φ (F.take g) = (needs φ F).take g := by
  rcases Nat.le_total g F.length with hg | hg
  · have h : needs φ F = needsFrom φ (needs φ (F.take g)) (F.drop g) := by
      conv => lhs; rw [← List.take_append_drop g F]
      exact needsFrom_append φ _ _ _
    obtain ⟨r, hr⟩ := needsFrom_prefix φ (F.drop g) (needs φ (F.take g))
    rw [h, ← hr, List.take_left' (by rw [needs_length, List.length_take]; omega)]
  · rw [List.take_of_length_le hg, List.take_of_length_le (by rw [needs_length]; exact hg)]

theorem callMax_append (acc : List Nat) :
    ∀ (a b : List Instr), callMax acc (a ++ b) = max (callMax acc a) (callMax acc b)
  | [], b => by simp [callMax]
  | i :: a, b => by
    cases i <;> simp only [List.cons_append, callMax, callMax_append acc a b] <;> omega

/-! ## Well-formedness -/

/-- The operands mention only slots `< n`. -/
def OpsBelow (ops : List Operand) (n : Nat) : Prop := ∀ x, Operand.slot x ∈ ops → x < n

/-- Well-formedness of instruction `ins` in function number `i` of `P`, whose frame has `fr` slots
and whose code has `len` instructions. -/
def Instr.Wf (P : Prog) (i fr len : Nat) : Instr → Prop
  | .mov x a => x < fr ∧ OpsBelow [a] fr
  | .bin _ x a b => x < fr ∧ OpsBelow [a, b] fr
  | .load _ x a _ => x < fr ∧ OpsBelow [a] fr
  | .store _ a _ b => OpsBelow [a, b] fr
  | .jmp l => l < len
  | .jz c l => OpsBelow [c] fr ∧ l < len
  | .call g args d => g < i ∧ OpsBelow args fr ∧
      ∃ gf, P.funs[g]? = some gf ∧ args.length ≤ gf.frame ∧ d + gf.ret.length ≤ fr
  | .ret => True
  | .ext _ _ x args => x < fr ∧ (∀ o, ExtArg.word o ∈ args → OpsBelow [o] fr) ∧
    (∀ a l, ExtArg.mem a l ∈ args → OpsBelow [a, l] fr) ∧
    ∀ a l, ExtArg.outMem a l ∈ args → OpsBelow [a, l] fr
  | .tick _ => True

/-- A well-formed function keeps its returned operands and every instruction within its frame. -/
def Fn.Wf (P : Prog) (i : Nat) (fn : Fn) : Prop :=
  OpsBelow fn.ret fn.frame ∧ ∀ ins ∈ fn.code, ins.Wf P i fn.frame fn.code.length

/-- A well-formed program has `main` and every function well formed. -/
def Prog.Wf (P : Prog) : Prop :=
  P.main < P.funs.length ∧ ∀ (i : Nat) (fn : Fn), P.funs[i]? = some fn → fn.Wf P i

end Millipede.Lin
