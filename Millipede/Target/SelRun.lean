import Millipede.Compile.AssembleLaws
import Millipede.Target.SelMem

/-!
# Machine runs and code location

This module holds the facts about machine runs that the selection proofs of every ISA share. It
is generic over the symbolic layer `A`, an assembler whose resolved instructions have their
layout size, and an ABI `abi`.

The machine `M abi` steps by executing the instruction encoded at `pc`. `runIs` executes a list
of instructions, each with its encoded length, and `run_straight` shows that instructions at
`pc` in W^X memory that fall through and keep `sp` run one per machine step. `RunAll` states a
property of every intermediate state, and a `Leg` is a run with such a property; the runs of a
case are composed from legs.

`SeqAt` says that the resolved and encoded code of a symbolic sequence is at an address.
`fn_code` places a loaded function's entry sequence and blocks, and `loaded_frame` shows that
stores keep a program loaded.
-/

namespace Millipede.Sel

variable {A : Asm.Arch}

/-! ## The machine -/

/-- The machine of an ISA with an ABI's system calls. -/
abbrev M (abi : Abi A.isa) : Sem := Asm.msem A.isa abi

/-- The encoded length of an instruction, or 0 when it cannot be encoded. -/
def ilen (i : A.isa.Instr) : Nat := ((A.isa.encode i).map List.length).getD 0

theorem ilen_of {i : A.isa.Instr} {e : List UInt8} (h : A.isa.encode i = some e) :
    ilen (A := A) i = e.length := by simp [ilen, h]

variable (abi : Abi A.isa)

/-- One machine step executes the instruction encoded at `pc`. -/
theorem step_exec (hl : A.isa.Laws) {ω : Oracle} {s s' : MState A.isa.Regs} {i : A.isa.Instr}
    {e : List UInt8} {c : Nat} (hh : s.world.halted = false) (he : A.isa.encode i = some e)
    (hc : s.mem.CodeAt (A.isa.pc s.regs) e)
    (hx : A.isa.exec (abi.trap ω) i e.length s = some s') :
    (M abi).step ω (s, c) = some (s', c + 1) := by
  have hd : A.isa.fetchDecode s = some (i, e.length) := Isa.fetchDecode_codeAt hl he hc
  simp only [M, Asm.msem, hh, Bool.false_eq_true, ite_false, Isa.step, hd, hx, Option.map_some]

theorem M_step_halted {ω : Oracle} {t : (M abi).State} (h : t.1.world.halted = true) :
    (M abi).step ω t = some t := by
  simp [M, Asm.msem, h]

theorem M_run_halted {ω : Oracle} {t : (M abi).State} (h : t.1.world.halted = true) :
    ∀ k, (M abi).run ω t k = some t
  | 0 => rfl
  | k + 1 => by rw [Sem.run_succ, M_step_halted abi h, Option.bind_some]; exact M_run_halted h k

/-- The machine only extends the trace, and its instruction counter only counts up. -/
theorem M_mono (hl : A.isa.Laws) : (M abi).Mono where
  events ω s s' h := by
    simp only [M, Asm.msem] at h ⊢
    split at h
    · cases h; exact List.prefix_refl _
    · cases hs : A.isa.step (abi.trap ω) s.1 with
      | none => rw [hs] at h; cases h
      | some s₁ => rw [hs] at h; cases h; exact (abi.step_respects hl ω hs).2
  clock ω s s' h := by
    simp only [M, Asm.msem] at h ⊢
    split at h
    · cases h; exact Nat.le_refl _
    · cases hs : A.isa.step (abi.trap ω) s.1 with
      | none => rw [hs] at h; cases h
      | some s₁ => rw [hs] at h; cases h; exact Nat.le_succ _

/-! ## Straight-line runs -/

/-- Executes instructions one after the other, each with its encoded length, and fails on a
fault or once the world has halted. -/
def runIs (ω : Oracle) : List A.isa.Instr → MState A.isa.Regs → Option (MState A.isa.Regs)
  | [], s => some s
  | i :: is, s =>
    if s.world.halted then none else (A.isa.exec (abi.trap ω) i (ilen i) s).bind (runIs ω is)

@[simp] theorem runIs_nil (ω : Oracle) (s : MState A.isa.Regs) : runIs abi ω [] s = some s := rfl

theorem runIs_cons {ω : Oracle} {i : A.isa.Instr} {is : List A.isa.Instr}
    {s s₁ : MState A.isa.Regs} (hh : s.world.halted = false)
    (he : A.isa.exec (abi.trap ω) i (ilen i) s = some s₁) :
    runIs abi ω (i :: is) s = runIs abi ω is s₁ := by
  simp [runIs, hh, he]

theorem runIs_append (ω : Oracle) : ∀ (xs ys : List A.isa.Instr) (s : MState A.isa.Regs),
    runIs abi ω (xs ++ ys) s = (runIs abi ω xs s).bind (runIs abi ω ys)
  | [], _, _ => rfl
  | x :: xs, ys, s => by
    simp only [List.cons_append, runIs]
    split
    · rfl
    · cases A.isa.exec (abi.trap ω) x (ilen x) s with
      | none => rfl
      | some s₁ => simp only [Option.bind_some]; exact runIs_append ω xs ys s₁

/-- Every state of the run `t, run t 1, …, run t n` satisfies `Q`. -/
def RunAll (ω : Oracle) (Q : MState A.isa.Regs → Prop) (t : (M abi).State) (n : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ t', (M abi).run ω t k = some t' → Q t'.1

variable {abi}

theorem RunAll.zero {ω : Oracle} {Q : MState A.isa.Regs → Prop} {t : (M abi).State}
    (h : Q t.1) : RunAll abi ω Q t 0 := by
  intro k hk t' ht
  obtain rfl : k = 0 := by omega
  cases ht; exact h

theorem RunAll.add {ω : Oracle} {Q : MState A.isa.Regs → Prop} {t t₁ : (M abi).State}
    {n₁ n₂ : Nat} (h₁ : RunAll abi ω Q t n₁) (hr : (M abi).run ω t n₁ = some t₁)
    (h₂ : RunAll abi ω Q t₁ n₂) : RunAll abi ω Q t (n₁ + n₂) := by
  intro k hk t' ht
  by_cases hk1 : k ≤ n₁
  · exact h₁ k hk1 t' ht
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hk1)
    rw [Sem.run_add_of hr] at ht
    exact h₂ d (by omega) t' ht

theorem RunAll.one {ω : Oracle} {Q : MState A.isa.Regs → Prop} {t t₁ : (M abi).State}
    (h : Q t.1) (hs : (M abi).step ω t = some t₁) (h₁ : Q t₁.1) : RunAll abi ω Q t 1 := by
  intro k hk t' ht
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
  · cases ht; exact h
  · rw [Sem.run_one hs] at ht; cases ht; exact h₁

theorem RunAll.mono {ω : Oracle} {Q Q' : MState A.isa.Regs → Prop} {t : (M abi).State} {n : Nat}
    (hQ : ∀ x, Q x → Q' x) (h : RunAll abi ω Q t n) : RunAll abi ω Q' t n :=
  fun k hk t' ht => hQ _ (h k hk t' ht)

/-- A leg of a run is `n` machine steps from `s` at clock `c` to `t`, with every state in `Q`.
The runs of a case are composed from legs with `Leg.trans`. -/
structure Leg (abi : Abi A.isa) (ω : Oracle) (Q : MState A.isa.Regs → Prop) (s : MState A.isa.Regs) (c n : Nat)
    (t : MState A.isa.Regs) : Prop where
  run : (M abi).run ω (s, c) n = some (t, c + n)
  all : RunAll abi ω Q (s, c) n

theorem Leg.trans {ω : Oracle} {Q : MState A.isa.Regs → Prop} {s t u : MState A.isa.Regs}
    {c n₁ n₂ : Nat} (h₁ : Leg abi ω Q s c n₁ t) (h₂ : Leg abi ω Q t (c + n₁) n₂ u) :
    Leg abi ω Q s c (n₁ + n₂) u :=
  ⟨(Sem.run_add_of h₁.run _).trans (by rw [h₂.run, Nat.add_assoc]), h₁.all.add h₁.run h₂.all⟩

theorem Leg.one {ω : Oracle} {Q : MState A.isa.Regs → Prop} {s t : MState A.isa.Regs} {c : Nat}
    (hs : (M abi).step ω (s, c) = some (t, c + 1)) (hQ : Q s) (hQ' : Q t) : Leg abi ω Q s c 1 t :=
  ⟨Sem.run_one hs, RunAll.one hQ hs hQ'⟩

theorem Leg.mono {ω : Oracle} {Q Q' : MState A.isa.Regs → Prop} {s t : MState A.isa.Regs}
    {c n : Nat} (hQ : ∀ x, Q x → Q' x) (h : Leg abi ω Q s c n t) : Leg abi ω Q' s c n t :=
  ⟨h.run, h.all.mono hQ⟩

/-- Under W^X, executable bytes are not writable, so code stays in place under stores. -/
theorem codeAt_frame {m m' : Memory} (hwx : m.WxorX) (hF : Memory.Frame m m') :
    ∀ (bs : List UInt8) (a : UInt64), m.CodeAt a bs → m'.CodeAt a bs
  | [], _, _ => trivial
  | b :: bs, a, ⟨hx, hb, hr⟩ => by
    have hx' : m'.executable a = m.executable a := by
      simp [Memory.executable, Memory.permAt, Memory.page, hF.1, hF.2.1]
    have hw : m.writable a = false := by
      cases hwa : m.writable a with
      | false => rfl
      | true => exact absurd ⟨hwa, hx⟩ (hwx (m.page a))
    exact ⟨hx'.trans hx, (hF.2.2 a hw).trans hb, codeAt_frame hwx hF bs (a + 1) hr⟩

theorem codeAt_append : ∀ (m : Memory) (a : UInt64) (xs ys : List UInt8),
    m.CodeAt a (xs ++ ys) → m.CodeAt a xs ∧ m.CodeAt (a + UInt64.ofNat xs.length) ys
  | _, a, [], ys, h => ⟨trivial, by simpa using h⟩
  | m, a, x :: xs, ys, ⟨h1, h2, h3⟩ => by
    obtain ⟨h4, h5⟩ := codeAt_append m (a + 1) xs ys h3
    refine ⟨⟨h1, h2, h4⟩, ?_⟩
    rw [show a + UInt64.ofNat (x :: xs).length = a + 1 + UInt64.ofNat xs.length by
      rw [add_one_ofNat]; rfl]
    exact h5

/-- An instruction that, as executed, falls through and keeps the stack pointer. -/
def Straight (abi : Abi A.isa) (ω : Oracle) (i : A.isa.Instr) : Prop :=
  ∀ s s', A.isa.exec (abi.trap ω) i (ilen i) s = some s' →
    A.isa.pc s'.regs = A.isa.pc s.regs + UInt64.ofNat (ilen i) ∧ A.isa.sp s'.regs = A.isa.sp s.regs

/-- Instructions at `pc` in W^X memory that fall through and keep `sp` run one per machine step.
Memory changes only by stores and stays W^X, and `sp` keeps its value in every intermediate
state. -/
theorem run_straight (hl : A.isa.Laws) {ω : Oracle} {is : List A.isa.Instr} {code : List UInt8}
    {s s' : MState A.isa.Regs} (c : Nat) (hwx : s.mem.WxorX) (he : Asm.encodeAll A.isa is = some code)
    (hc : s.mem.CodeAt (A.isa.pc s.regs) code) (hs : ∀ i ∈ is, Straight abi ω i)
    (h : runIs abi ω is s = some s') :
    (M abi).run ω (s, c) is.length = some (s', c + is.length) ∧ Memory.Frame s.mem s'.mem ∧
      s'.mem.WxorX ∧ A.isa.pc s'.regs = A.isa.pc s.regs + UInt64.ofNat code.length ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp s.regs) (s, c) is.length := by
  induction is generalizing s c code with
  | nil =>
    cases h; cases he
    exact ⟨rfl, Memory.Frame.refl _, hwx, by simp, RunAll.zero rfl⟩
  | cons i is ih =>
    obtain ⟨e, es, hei, hes, rfl⟩ := Asm.encodeAll_cons_inv he
    simp only [runIs] at h
    split at h
    · cases h
    · rename_i hh
      cases hx : A.isa.exec (abi.trap ω) i (ilen i) s with
      | none => rw [hx] at h; cases h
      | some s₁ =>
        rw [hx, Option.bind_some] at h
        obtain ⟨hc₁, hc₂⟩ := codeAt_append _ _ _ _ hc
        have hlen := ilen_of (A := A) hei
        rw [hlen] at hx
        have hst := step_exec abi hl (c := c) (Bool.not_eq_true _ ▸ hh) hei hc₁ hx
        have hresp := hl.exec_respects (abi.trap ω) i _ s s₁ (abi.trap_respects ω) hx
        rw [← hlen] at hx
        obtain ⟨hpc, hsp₁⟩ := hs i List.mem_cons_self s s₁ hx
        rw [hlen] at hpc
        obtain ⟨hr, hF, hwx', hpc', hall⟩ := ih (c := c + 1) (he := hes) (hwx := hresp.1.wxorx hwx)
          (hc := by rw [hpc]; exact codeAt_frame hwx hresp.1 _ _ hc₂)
          (hs := fun j hj => hs j (List.mem_cons_of_mem _ hj)) (h := h)
        refine ⟨?_, hresp.1.trans hF, hwx', ?_, ?_⟩
        · rw [List.length_cons, Nat.add_comm is.length 1, Sem.run_add_of (Sem.run_one hst), hr,
            Nat.add_assoc, Nat.add_comm 1]
        · rw [hpc', hpc, List.length_append, UInt64.add_assoc, ← UInt64.ofNat_add]
        · rw [List.length_cons, Nat.add_comm]
          exact RunAll.add (RunAll.one rfl hst hsp₁) (Sem.run_one hst)
            (RunAll.mono (fun x hx => hx.trans hsp₁) hall)

/-! ## Code location -/

theorem resolveAt_append {ρ : Asm.Ref → Option UInt64} : ∀ (xs ys : List A.SInstr) (a : UInt64)
    (ins : List A.isa.Instr), Asm.resolveAt A ρ a (xs ++ ys) = some ins →
    ∃ i₁ i₂ : List A.isa.Instr, ins = i₁ ++ i₂ ∧ Asm.resolveAt A ρ a xs = some i₁ ∧
      Asm.resolveAt A ρ (a + UInt64.ofNat (Asm.seqSize A xs)) ys = some i₂
  | [], ys, a, ins, h => ⟨[], ins, rfl, rfl, by simpa [Asm.seqSize] using h⟩
  | x :: xs, ys, a, ins, h => by
    obtain ⟨i', is', h₁, h₂, rfl⟩ := Asm.resolveAt_cons_inv h
    obtain ⟨i₁, i₂, rfl, h₃, h₄⟩ := resolveAt_append xs ys _ is' h₂
    refine ⟨i' :: i₁, i₂, rfl, Asm.resolveAt_cons_some h₁ h₃, ?_⟩
    rw [show a + UInt64.ofNat (Asm.seqSize A (x :: xs)) =
      a + UInt64.ofNat (A.size x) + UInt64.ofNat (Asm.seqSize A xs) by
      simp only [Asm.seqSize, UInt64.ofNat_add, UInt64.add_assoc]]
    exact h₄

theorem encodeAll_append {isa : Isa} : ∀ (xs ys : List isa.Instr) (code : List UInt8),
    Asm.encodeAll isa (xs ++ ys) = some code →
    ∃ c₁ c₂, code = c₁ ++ c₂ ∧ Asm.encodeAll isa xs = some c₁ ∧ Asm.encodeAll isa ys = some c₂
  | [], ys, code, h => ⟨[], code, rfl, rfl, h⟩
  | x :: xs, ys, code, h => by
    obtain ⟨e, es, he, hes, rfl⟩ := Asm.encodeAll_cons_inv h
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := encodeAll_append xs ys es hes
    exact ⟨e ++ c₁, c₂, by simp, Asm.encodeAll_cons he h₁, h₂⟩

/-- The resolved code of a sequence sits at an address. -/
def SeqAt (m : Memory) (ρ : Asm.Ref → Option UInt64) (a : UInt64) (b : List A.SInstr) : Prop :=
  ∃ (ins : List A.isa.Instr) (code : List UInt8), Asm.resolveAt A ρ a b = some ins ∧
    Asm.encodeAll A.isa ins = some code ∧ m.CodeAt a code

variable {asm : Asm.Assembler A}

theorem seqAt_append (hl : asm.Laws) {m : Memory} {ρ : Asm.Ref → Option UInt64} {a : UInt64}
    {xs ys : List A.SInstr} (h : SeqAt m ρ a (xs ++ ys)) :
    SeqAt m ρ a xs ∧ SeqAt m ρ (a + UInt64.ofNat (Asm.seqSize A xs)) ys := by
  obtain ⟨ins, code, hr, he, hc⟩ := h
  obtain ⟨i₁, i₂, rfl, h₁, h₂⟩ := resolveAt_append xs ys a ins hr
  obtain ⟨c₁, c₂, rfl, he₁, he₂⟩ := encodeAll_append i₁ i₂ code he
  obtain ⟨hc₁, hc₂⟩ := codeAt_append _ _ _ _ hc
  rw [(Asm.resolveAt_size hl _ _ _ _ h₁ he₁).1] at hc₂
  exact ⟨⟨i₁, c₁, h₁, he₁, hc₁⟩, ⟨i₂, c₂, h₂, he₂, hc₂⟩⟩

theorem blocksOff_succ : ∀ (bs : List (List A.SInstr)) (l : Nat) (b : List A.SInstr),
    bs[l]? = some b → Asm.blocksOff A bs (l + 1) = Asm.blocksOff A bs l + Asm.seqSize A b
  | [], _, _, h => by simp at h
  | c :: bs, 0, b, h => by cases h; simp [Asm.blocksOff]
  | c :: bs, l + 1, b, h => by
    simp only [Asm.blocksOff]
    rw [blocksOff_succ bs l b (by simpa using h)]; omega

/-- The next label follows block `l`. -/
theorem labelOff_succ (f : Asm.Fn A) {l : Nat} {b : List A.SInstr} (h : f.blocks[l]? = some b) :
    f.labelOff (l + 1) = f.labelOff l + Asm.seqSize A b := by
  simp only [Asm.Fn.labelOff, blocksOff_succ _ _ _ h]; omega

/-- A loaded function has its entry sequence at its symbol and every block at its label. -/
theorem fn_code (hl : asm.Laws) {P : Asm.Prog A} {σ : String → Option UInt64} {m : Memory}
    (hL : P.Loaded σ m) {f : Asm.Fn A} (hf : f ∈ P.funs) :
    ∃ a, σ f.name = some a ∧ SeqAt m (f.refAddr σ a) a f.entry ∧
      ∀ l b, f.blocks[l]? = some b →
        SeqAt m (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff l)) b := by
  obtain ⟨a, bs, ha, hb, hc⟩ := hL.1 f hf
  simp only [Asm.Fn.bytes, Asm.Fn.resolve] at hb
  cases hr : Asm.resolveAt A (f.refAddr σ a) a f.code with
  | none => rw [hr] at hb; cases hb
  | some ins =>
    rw [hr, Option.bind_some] at hb
    have hall : SeqAt m (f.refAddr σ a) a f.code := ⟨ins, bs, hr, hb, hc⟩
    simp only [Asm.Fn.code] at hall
    obtain ⟨he, hbl⟩ := seqAt_append hl hall
    refine ⟨a, ha, he, fun l b hl' => ?_⟩
    have hlt : l < f.blocks.length := by
      rcases Nat.lt_or_ge l f.blocks.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hl'
    have hsplit : f.blocks.flatten =
        (f.blocks.take l).flatten ++ (b ++ (f.blocks.drop (l + 1)).flatten) := by
      conv => lhs; rw [← List.take_append_drop l f.blocks]
      rw [List.drop_eq_getElem_cons hlt, List.flatten_append, List.flatten_cons]
      simp only [List.getElem?_eq_getElem hlt, Option.some.injEq] at hl'
      rw [hl']
    rw [hsplit] at hbl
    obtain ⟨_, hbl'⟩ := seqAt_append hl hbl
    obtain ⟨hb', _⟩ := seqAt_append hl hbl'
    rw [Asm.Fn.labelOff, Asm.blocksOff_eq _ _ (Nat.le_of_lt hlt), UInt64.ofNat_add,
      ← UInt64.add_assoc]
    exact hb'

/-- A read of bytes that are not writable, such as a data item, gives the same bytes after
stores. -/
theorem read_frame {m m' : Memory} (hF : Memory.Frame m m') : ∀ (n : Nat) (a : UInt64)
    (bs : List UInt8), m.read a n = some bs →
    (∀ i, i < n → m.writable (a + UInt64.ofNat i) = false) → m'.read a n = some bs
  | 0, _, bs, h, _ => h
  | n + 1, a, bs, h, hw => by
    simp only [Memory.read] at h ⊢
    have hr : m'.readable a = m.readable a := by
      simp [Memory.readable, Memory.permAt, Memory.page, hF.1, hF.2.1]
    rw [hr]
    split at h
    · cases hn : m.read (a + 1) n with
      | none => rw [hn] at h; cases h
      | some bs' =>
        rw [hn] at h; cases h
        have h0 := hw 0 (by omega)
        simp only [add_ofNat_zero] at h0
        rw [read_frame hF n (a + 1) bs' hn (fun i hi => by
          rw [add_one_ofNat]; exact hw (i + 1) (by omega)), hF.2.2 a h0]
        simp_all
    · cases h

/-- Stores keep a program loaded, because under W^X code is not writable and data items are
read-only. -/
theorem loaded_frame {P : Asm.Prog A} {σ : String → Option UInt64} {m m' : Memory}
    (hL : P.Loaded σ m) (hwx : m.WxorX) (hF : Memory.Frame m m') : P.Loaded σ m' := by
  refine ⟨fun f hf => ?_, fun d hd => ?_⟩
  · obtain ⟨a, bs, h1, h2, h3⟩ := hL.1 f hf
    exact ⟨a, bs, h1, h2, codeAt_frame hwx hF _ _ h3⟩
  · obtain ⟨a, h1, h2, h3⟩ := hL.2 d hd
    refine ⟨a, h1, read_frame hF _ _ _ h2 h3, fun i hi => ?_⟩
    have := h3 i hi
    simpa [Memory.writable, Memory.permAt, Memory.page, hF.1, hF.2.1] using this

/-- The target of a local label. -/
theorem label_addr {f : Asm.Fn A} {σ : String → Option UInt64} {a : UInt64} {l : Nat}
    (hl : l ≤ f.blocks.length) :
    f.refAddr σ a (.label l) = some (a + UInt64.ofNat (f.labelOff l)) := by
  simp [Asm.Fn.refAddr, hl]

/-- The block of instruction `pc` ends at the label of `pc + 1`. -/
theorem next_pc (hl : asm.Laws) {f : Asm.Fn A} {pc : Nat} {b : List A.SInstr}
    (hb : f.blocks[pc]? = some b) {a : UInt64} {ρ : Asm.Ref → Option UInt64}
    {ins : List A.isa.Instr} {code : List UInt8}
    (hr : Asm.resolveAt A ρ (a + UInt64.ofNat (f.labelOff pc)) b = some ins)
    (he : Asm.encodeAll A.isa ins = some code) :
    a + UInt64.ofNat (f.labelOff pc) + UInt64.ofNat code.length =
      a + UInt64.ofNat (f.labelOff (pc + 1)) := by
  rw [(Asm.resolveAt_size hl _ _ _ _ hr he).1, labelOff_succ f hb, UInt64.ofNat_add,
    UInt64.add_assoc]

end Millipede.Sel
