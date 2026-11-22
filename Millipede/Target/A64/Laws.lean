import Millipede.Target.A64.Exec

/-!
# Laws of the arm64 ISA model

This module proves the laws of execution that the shared ISA interface asks for, while the laws of
the encoder and decoder are in `Decode.lean`. Since `exec` is a function, execution is
deterministic by construction.

Memory changes only through stores to writable memory, and the trace only grows, provided the
system-call handler behaves the same way. The frame lemmas say that an instruction changes only
the registers it names as written, that only `str` touches memory, that only `adds`, `subs` and
`ands` change the flags, and that every instruction except a branch continues at `pc + 4`. Only
an `add` or `sub` immediate that does not set flags writes `sp`. The module then states the frame
law of the interface over the locations `ALoc` of the register file, and proves the values that
instruction selection relies on for addition, subtraction, comparison, division, shifts, the
logical operations and `cset`.
-/

namespace Millipede.A64

/-! ## What an instruction writes -/

/-- A destination where 31 is `xzr`, which is written unless it is 31. -/
def zw (d : Reg) : List Reg := if d = 31 then [] else [d]

/-- The registers an instruction may write other than through `svc`, where 31 is `sp`. -/
def Instr.writes : Instr → List Reg
  | .mov _ _ d _ _ | .addReg _ _ _ d _ _ | .logReg _ _ d _ _ | .madd _ _ d _ _ _
  | .div _ _ d _ _ | .shiftV _ _ d _ _ | .bfm _ _ d _ _ _ | .csel _ _ d _ _ _ | .ldr _ d _
  | .adr _ d _ => zw d
  | .addImm _ _ setf d _ _ _ => if setf then zw d else [d]
  | .b link _ => if link then [30] else []
  | .str .. | .bcond .. | .cbz .. | .ret _ | .svc _ => []

/-- Whether the instruction sets the flags. -/
def Instr.setsFlags : Instr → Bool
  | .addImm _ _ setf .. | .addReg _ _ setf .. => setf
  | .logReg op .. => op == .ands
  | _ => false

/-- Whether the instruction stores to memory. -/
def Instr.stores : Instr → Bool
  | .str .. => true
  | _ => false

/-- Whether the instruction transfers control other than by falling through. -/
def Instr.branches : Instr → Bool
  | .b .. | .bcond .. | .cbz .. | .ret _ => true
  | _ => false

/-- Whether the instruction is the system call `svc`. -/
def Instr.isTrap : Instr → Bool
  | .svc _ => true
  | _ => false

/-- Unfold one successful `exec` into equations about the new state. -/
local macro "exec_cases" h:ident : tactic => `(tactic| (
  simp only [exec, State.goto, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at $h:ident
  obtain ⟨-, $h:ident⟩ := $h:ident
  first
    | subst $h:ident
    | (obtain ⟨_, _, e⟩ := $h:ident; subst e)
    | (obtain ⟨_, _, _, e⟩ := $h:ident; subst e)))

/-! ## Memory access -/

/-- Execution respects memory permissions and only extends the trace, given a system-call
handler that does the same. -/
theorem exec_respects (trap : State → Option State) (i : Instr) (n : Nat) (s s' : State)
    (ht : ∀ t t', trap t = some t' → t.Respects t') (h : exec trap i n s = some s') :
    s.Respects s' := by
  cases i <;> exec_cases h
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | exact Memory.Frame.refl _
    | exact List.prefix_refl _
    | exact Memory.writeWord_frame ‹_›
    | (rename_i ht0; exact (ht _ _ ht0).1)
    | (rename_i ht0; exact (ht _ _ ht0).2)

/-! ## Frame lemmas -/

/-- An instruction other than `svc` changes no register outside `i.writes`, where 31 is
`sp`. -/
theorem exec_x {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') :
    ∀ k, k ∉ i.writes → s'.regs.x k = s.regs.x k := by
  intro k hk
  cases i <;> simp only [Instr.isTrap, Bool.true_eq_false] at hi <;> exec_cases h <;>
    simp_all [Instr.writes, Regs.setZ, zw]
  all_goals grind [Regs.set]

/-- An instruction other than `svc` does not touch the world. -/
theorem exec_world {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') : s'.world = s.world := by
  cases i <;> simp only [Instr.isTrap, Bool.true_eq_false] at hi <;> exec_cases h <;> simp_all

/-- Among the instructions other than `svc`, only `str` changes memory. -/
theorem exec_mem {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (hs : i.stores = false) (h : exec trap i n s = some s') :
    s'.mem = s.mem := by
  cases i <;> simp only [Instr.isTrap, Instr.stores, Bool.true_eq_false] at hi hs <;>
    exec_cases h <;> simp_all

/-- Only `adds`, `subs` and `ands` change the flags. -/
theorem exec_flags {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (hs : i.setsFlags = false) (h : exec trap i n s = some s') :
    s'.regs.flags = s.regs.flags := by
  cases i <;> simp only [Instr.isTrap, Instr.setsFlags, Bool.true_eq_false] at hi hs <;>
    exec_cases h <;> simp_all [Regs.setZ]
  all_goals grind [Regs.set]

/-- Every instruction that does not branch, `svc` included, continues at `pc + 4`. -/
theorem exec_pc {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hb : i.branches = false) (h : exec trap i n s = some s') : s'.regs.pc = s.regs.pc + 4 := by
  cases i <;> simp only [Instr.branches, Bool.true_eq_false] at hb <;> exec_cases h <;> simp_all

/-! ## The frame law of the ISA interface

The locations `ALoc` of the register file are the 32 register numbers, with 31 as `sp`, then
`pc`, and the flags read as the word `Flags.bits`. `Instr.regWrites` names the locations an
instruction writes, and `Instr.memWrites` the bytes it stores to, computed from the registers
before it. -/

/-- The flags as the word `n + 2 z + 4 c + 8 v`. -/
def Flags.bits (f : Flags) : UInt64 :=
  (if f.n then 1 else 0) + (if f.z then 2 else 0) + (if f.c then 4 else 0) + (if f.v then 8 else 0)

theorem Flags.bits_inj {f g : Flags} (h : f.bits = g.bits) : f = g := by
  obtain ⟨a, b, c, d⟩ := f
  obtain ⟨a', b', c', d'⟩ := g
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases a' <;> cases b' <;> cases c' <;>
    cases d' <;> decide

/-- The locations of the arm64 register file. -/
inductive ALoc where
  | x (k : Reg)
  | pc
  | flags
deriving DecidableEq, Repr

/-- Read a location. -/
def ALoc.get (r : Regs) : ALoc → UInt64
  | .x k => r.x k
  | .pc => r.pc
  | .flags => r.flags.bits

/-- The locations cover the register file, so two register files that agree on every location
are equal. -/
theorem regs_ext {r r' : Regs} (h : ∀ l, ALoc.get r l = ALoc.get r' l) : r = r' := by
  obtain ⟨g, p, f⟩ := r
  obtain ⟨g', p', f'⟩ := r'
  have hg : g = g' := funext fun k => h (.x k)
  have hp : p = p' := h .pc
  have hf : f = f' := Flags.bits_inj (h .flags)
  subst hg hp hf; rfl

/-- The locations an instruction may write, which are `pc`, its `writes` and the flags if it
sets them. -/
def Instr.regWrites (i : Instr) : List ALoc :=
  .pc :: (i.writes.map ALoc.x ++ if i.setsFlags then [ALoc.flags] else [])

/-- The memory range an instruction may store to, given the registers before it. -/
def Instr.memWrites (i : Instr) (_n : Nat) (r : Regs) : List (UInt64 × Nat) :=
  match i with
  | .str sz _ a => [(a.ea r sz, sz.bytes)]
  | _ => []

/-- An instruction other than `svc` changes no location outside `regWrites`. -/
theorem exec_regs {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') :
    ∀ l, l ∉ i.regWrites → ALoc.get s'.regs l = ALoc.get s.regs l := by
  intro l hl
  cases l with
  | x k => exact exec_x hi h k fun hk => hl (by simp [Instr.regWrites, hk])
  | pc => exact absurd (by simp [Instr.regWrites]) hl
  | flags =>
    cases hf : i.setsFlags
    · show s'.regs.flags.bits = s.regs.flags.bits
      rw [exec_flags hi hf h]
    · exact absurd (by simp [Instr.regWrites, hf]) hl

/-- An instruction other than `svc` changes only the bytes in `memWrites`. -/
theorem exec_bytes {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') (a : UInt64)
    (ha : ∀ w ∈ i.memWrites n s.regs, ¬ Memory.InRange w.1 w.2 a) :
    s'.mem.bytes a = s.mem.bytes a := by
  cases hst : i.stores
  · rw [exec_mem hi hst h]
  · cases i <;> simp only [Instr.stores, Bool.false_eq_true] at hst
    simp only [Instr.memWrites, List.mem_singleton, forall_eq] at ha
    exec_cases h
    exact Memory.writeWord_outside (by assumption) ha

/-- The system call's memory and world are the handler's. -/
theorem exec_trap {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = true) (h : exec trap i n s = some s') :
    ∃ t, trap s = some t ∧ s'.mem = t.mem ∧ s'.world = t.world := by
  cases i <;> simp only [Instr.isTrap, Bool.false_eq_true] at hi
  exec_cases h
  rename_i ht0
  exact ⟨_, ht0, rfl, rfl⟩

/-! ## Primitive lowerings

These are the 64-bit values and conditions that instruction selection relies on. `add`, `sub`
and `subs` compute `a + b` and `a - b`, and after `cmp a, b`, which is `subs xzr, a, b`, the
conditions `eq`, `ne`, `cc` and `ls` mean `a = b`, `a ≠ b`, `a < b` and `a ≤ b`. `udiv` is
`UInt64` division, which gives `x / 0 = 0` and so needs no guard. `lslv` and `lsrv` are `UInt64`
shifts that take the amount modulo 64, as Lin does, and `cset` gives `1` or `0`. -/

theorem addSub_add (a b : UInt64) : (addSub true false a b).1 = a + b := by
  apply UInt64.toBitVec_inj.mp
  simp [addSub, addWithCarry]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem addSub_sub (a b : UInt64) : (addSub true true a b).1 = a - b := by
  apply UInt64.toBitVec_inj.mp
  simp [addSub, addWithCarry]
  have := a.toNat_lt; have := b.toNat_lt
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem subs_z (a b : UInt64) : (addSub true true a b).2.z = (a == b) := by
  simp [addSub, addWithCarry]
  have := a.toNat_lt; have := b.toNat_lt
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, ← UInt64.toNat_inj]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp; omega

theorem subs_c (a b : UInt64) : (addSub true true a b).2.c = decide (b ≤ a) := by
  simp [addSub, addWithCarry]
  have := a.toNat_lt; have := b.toNat_lt
  by_cases h : b.toNat ≤ a.toNat <;> simp [UInt64.le_iff_toNat_le, h] <;> omega

/-- The conditions that selected code reads after `cmp a, b`, which is `subs xzr, a, b`. -/
theorem subs_cond (a b : UInt64) :
    Cond.holds (addSub true true a b).2 .eq = decide (a = b) ∧
    Cond.holds (addSub true true a b).2 .ne = decide (a ≠ b) ∧
    Cond.holds (addSub true true a b).2 .cc = decide (a < b) ∧
    Cond.holds (addSub true true a b).2 .ls = decide (a ≤ b) := by
  simp only [Cond.holds, subs_z, subs_c]
  grind

theorem bin_udiv (a b : UInt64) : bin true (fun _ x y => x / y) a b = a / b := rfl

theorem bin_lsl (a b : UInt64) : bin true ShiftOp.lsl.eval a b = a <<< b := by
  apply UInt64.toBitVec_inj.mp
  simp [bin, ShiftOp.eval, UInt64.toBitVec_shiftLeft]

theorem bin_lsr (a b : UInt64) : bin true ShiftOp.lsr.eval a b = a >>> b := by
  apply UInt64.toBitVec_inj.mp
  simp [bin, ShiftOp.eval, UInt64.toBitVec_shiftRight]

theorem bin_and (a b : UInt64) : bin true LogOp.and.eval a b = a &&& b := rfl
theorem bin_orr (a b : UInt64) : bin true LogOp.orr.eval a b = a ||| b := rfl
theorem bin_eor (a b : UInt64) : bin true LogOp.eor.eval a b = a ^^^ b := rfl

/-- `cset d, c`, which is `csinc d, xzr, xzr, invert c`, gives `1` if `c` holds and `0`
otherwise. -/
theorem cset_val (f : Flags) (c : Cond) (hc : c ≠ .al ∧ c ≠ .nv) :
    bin true (fun w x y => if c.invert.holds f then x else CselOp.csinc.eval w y) 0 0 =
      if c.holds f then 1 else 0 := by
  cases c <;> simp at hc <;> cases f with
  | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;> decide

end Millipede.A64
