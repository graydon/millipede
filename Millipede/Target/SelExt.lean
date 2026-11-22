import Millipede.Target.SelOps

/-!
# Extern calls proved over an ISA's operations

The five extern calls a selector accepts are Linux system calls. An ISA's block for one loads
the descriptor and the other arguments into its ABI's argument registers and the call number into
`nrR`, runs the system-call instruction `trap`, and stores the result register `res` into the
destination location. `Ops.ExtLaws` states what the proofs need beyond `Ops.Laws`:

* The ABI is `Abi.linux` with the number, the arguments and the result in `nrR`, `argR` and `res`.
  The trap instruction runs its handler and falls through. A register copy `mv` and a symbol's
  address `symA` run as stated, where `symA` is `pc`-relative and so runs from where the code
  before it ends.
* The selector's blocks and counts for the five calls are built from `ldAll`, which loads
  operands into registers in order, `symA`, the data address `memA`, and `memTail`.
* For `read(fd, buf, 1)`, whose buffer is the destination slot, `rdPre` clears the slot and points
  argument 1 at it before the trap, and `rdFix` makes the call's value after it, which is the byte
  read when the result is 1 and `2^64 - 1` otherwise.

From these laws, this module proves the cases of `exit`, `write` of constant bytes, `write` and
`read` of a data-region buffer, and the one-byte `read`, once for every ISA.
-/

namespace Millipede.Sel

open Flat (Operand)

variable {A : Asm.Arch}

namespace Ops

/-- Operands loaded into registers, in order. -/
def ldAll (O : Ops A) (L : List (O.Reg × Operand)) : List A.isa.Instr :=
  L.flatMap fun q => O.ld q.1 q.2

@[simp] theorem ldAll_nil (O : Ops A) : O.ldAll [] = [] := rfl

@[simp] theorem ldAll_cons (O : Ops A) (r : O.Reg) (o : Operand) (L : List (O.Reg × Operand)) :
    O.ldAll ((r, o) :: L) = O.ld r o ++ O.ldAll L := rfl

/-- The place of operand `o` with `k` register locations: its register for a register location. -/
abbrev place (O : Ops A) (k : Nat) : Operand → Place O.Reg := Sel.place O.preg k

/-- The code of one move into a register: a copy from a register, or a load of an operand. -/
def emit (O : Ops A) : Place O.Reg × Place O.Reg → List A.isa.Instr
  | (.inl d, .inl r) => O.mv d r
  | (.inl d, .inr o) => O.ld d o
  | (.inr _, _) => []

/-- The value at a place in registers `t`: a register's, or an operand's in frame `fr`. -/
def view (O : Ops A) (fr : Flat.Frame) (t : A.isa.Regs) : Place O.Reg → UInt64
  | .inl r => O.get t r
  | .inr o => o.eval fr

/-- A move that `emit` runs: into a register that `ld` may load, and from a register or from an
operand below `F` in no register location below `k`. -/
def EmitOk (O : Ops A) (k F : Nat) (p : Place O.Reg × Place O.Reg) : Prop :=
  (∃ d, p.1 = .inl d ∧ O.ldOk d) ∧ ∀ o, p.2 = .inr o → Lin.OpsBelow [o] F ∧ ∀ y, o = .slot y → k ≤ y

/-- The moves that set up a `write` or `read` of the `l` bytes at the address in `r0`: the
address into argument 1, the descriptor `o` into argument 0, `l` into argument 2 and the number
`n`. They form one parallel move, so an operand may already sit in an argument register. -/
def memMoves (O : Ops A) (k : Nat) (n : UInt64) (o l : Operand) : List (Place O.Reg × Place O.Reg) :=
  [(.inl (O.argR 1), .inl O.r0), (.inl (O.argR 0), O.place k o), (.inl (O.argR 2), O.place k l),
    (.inl O.nrR, .inr (.imm n))]

/-- The rest of a `write` or `read` of the `l` bytes at a Lin address, once the address is in
`r0`: the moves of `memMoves`, sequentialised through `r1`, the trap, and the store of the result
into location `x`. It is `none` when `PMove.seq` refuses. -/
def memTail (O : Ops A) (k : Nat) (n : UInt64) (x : Nat) (o l : Operand) :
    Option (List A.isa.Instr) :=
  (PMove.seq (.inl O.r1) 9 (O.memMoves k n o l)).map fun ms =>
    ms.flatMap O.emit ++ [O.trap] ++ O.st x O.res

/-- The registers an extern call's code writes besides scratch registers: the number, the three
arguments and the result. -/
def sysRegs (O : Ops A) : List O.Reg := [O.nrR, O.argR 0, O.argR 1, O.argR 2, O.res]

/-- The registers of the locations `x < k` outside `S` hold the same values in `t'` as in `t`. -/
def KeepsExc (O : Ops A) (k : Nat) (S : List O.Reg) (t t' : A.isa.Regs) : Prop :=
  ∀ x, x < k → O.preg x ∉ S → O.get t' (O.preg x) = O.get t (O.preg x)

/-- No operand of `L` is in a register that `ldAll L` loads before it. -/
def NoClash (O : Ops A) (k : Nat) : List (O.Reg × Operand) → Prop
  | [] => True
  | q :: L => (∀ q' ∈ L, ∀ y, q'.2 = .slot y → y < k → O.preg y ≠ q.1) ∧ O.NoClash k L

end Ops

@[simp] theorem opsBelow_imm (w : UInt64) (F : Nat) : Lin.OpsBelow [.imm w] F := by
  simp [Lin.OpsBelow]

/-- The laws an ISA's system-call code satisfies beyond `Ops.Laws`. -/
structure Ops.ExtLaws (O : Ops A) (abi : Abi A.isa) (C : Conv A) (D : Selector A)
    (cnt : Lin.Prog → Lin.Fn → Lin.Instr → Nat) : Prop where
  linux : ∃ (pb : Nat) (st : UInt64) (er : UInt64 → UInt64 → A.isa.Regs) (R : LinuxRegs A.isa),
    abi = Abi.linux pb st er O.nums R ∧
    (∀ r, R.nr r = O.get r O.nrR) ∧ (∀ i r, i < 3 → R.arg i r = O.get r (O.argR i)) ∧
    ∀ v r, O.get (R.setRet v r) O.res = v
  nums : O.nums.read ≠ O.nums.exit ∧ O.nums.read ≠ O.nums.write ∧ O.nums.write ≠ O.nums.exit
  nodup : [O.nrR, O.argR 0, O.argR 1, O.argR 2].Nodup
  /-- The temporary of the moves of `memTail` is no system-call register. -/
  r1_sys : O.r1 ∉ O.sysRegs
  /-- The register of a one-byte `read`'s value is no location's. -/
  preg_rd : ∀ x, x < (C.k + C.c) → O.preg x ≠ O.rdRes
  /-- A location in a system-call register is a caller-saved one, which every extern call
  destroys. -/
  kill_sys : ∀ x, x < (C.k + C.c) → O.preg x ∈ O.sysRegs →
    C.k ≤ x ∧ ∀ sym nr y args, C.kill (.ext sym nr y args) x = true
  ld_nr : O.ldOk O.nrR
  ld_arg : ∀ i, i < 3 → O.ldOk (O.argR i)
  st_res : O.stOk O.res
  st_rd : O.stOk O.rdRes
  straight_trap : ∀ ω, StraightC C abi ω O.trap
  run_trap : ∀ ω (t t' : MState A.isa.Regs), O.Ok t → abi.trap ω t = some t' →
    ∃ t'', A.isa.exec (abi.trap ω) O.trap (ilen O.trap) t = some t'' ∧ t''.mem = t'.mem ∧
      t''.world = t'.world ∧ O.get t''.regs O.res = O.get t'.regs O.res ∧ O.Ok t'' ∧
      O.KeepsExc (C.k + C.c) O.sysRegs t.regs t''.regs
  straight_mv : ∀ ω d r, O.ldOk d → ∀ i ∈ O.mv d r, StraightC C abi ω i
  run_mv : ∀ {ω} {t : MState A.isa.Regs} {d r}, O.ldOk d → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω (O.mv d r) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs d = O.get t.regs r ∧
      ∀ r', r' ≠ d → O.get t'.regs r' = O.get t.regs r'
  straight_rdPre : ∀ ω x, ∀ i ∈ O.rdPre x, StraightC C abi ω i
  straight_rdFix : ∀ ω x, ∀ i ∈ O.rdFix x, StraightC C abi ω i
  run_rdPre : ∀ {ω P AP σ lo N s m fn f a j} {t : MState A.isa.Regs} {x : Nat} {mz : Memory},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → C.k + C.c ≤ x → x < fn.frame →
    t.mem = m.mem → A.isa.sp t.regs = A.isa.sp m.regs → t.world.halted = false → O.Ok t →
    m.mem.writeWord (wa lo (j + x - C.c)) 8 0 = some mz →
    ∃ t', runIs abi ω (O.rdPre x) t = some t' ∧ t'.mem = mz ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧ O.get t'.regs O.nrR = O.nums.read ∧
      O.get t'.regs (O.argR 1) = wa lo (j + x - C.c) ∧ O.get t'.regs (O.argR 2) = 1 ∧
      O.get t'.regs (O.argR 0) = O.get t.regs (O.argR 0) ∧
      O.KeepsExc (C.k + C.c) O.sysRegs t.regs t'.regs
  run_rdFix : ∀ {ω P AP σ lo N s m fn f a j} {t : MState A.isa.Regs} {x : Nat},
    MatchAt C P AP σ lo N s m fn f a j → D.fnOk fn = true → C.k + C.c ≤ x → x < fn.frame →
    Region t.mem lo N → A.isa.sp t.regs = A.isa.sp m.regs → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω (O.rdFix x) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      O.get t'.regs O.rdRes =
        (if O.get t.regs O.res = 1 then word t.mem lo (j + x - C.c) else UInt64.ofNat (2 ^ 64 - 1)) ∧
      O.KeepsExc (C.k + C.c) O.sysRegs t.regs t'.regs
  sel_exit : ∀ P i pc fn x o, D.instr P i pc fn (.ext "exit" true x [.word o]) =
    .ok ((O.ldAll [(O.argR 0, o), (O.nrR, .imm O.nums.exit)] ++ [O.trap] ++ O.st x O.res).map O.op,
      [])
  cnt_exit : ∀ P fn x o, cnt P fn (.ext "exit" true x [.word o]) =
    (O.ldAll [(O.argR 0, o), (O.nrR, .imm O.nums.exit)] ++ [O.trap]).length
  sel_write : ∀ P i pc fn x o bs b d,
    D.instr P i pc fn (.ext "write" false x [.word o, .bytes bs]) = .ok (b, d) →
    bs.length < 2 ^ 32 ∧ d = [(dataSym i pc, bs)] ∧
      b = (O.ld (O.argR 0) o).map O.op ++ O.symA (O.argR 1) (dataSym i pc) ++
        (O.ldAll [(O.argR 2, .imm (UInt64.ofNat bs.length)), (O.nrR, .imm O.nums.write)] ++
          [O.trap] ++ O.st x O.res).map O.op
  cnt_write : ∀ P fn x o bs, cnt P fn (.ext "write" false x [.word o, .bytes bs]) =
    (O.ld (O.argR 0) o).length + O.symLen +
      (O.ldAll [(O.argR 2, .imm (UInt64.ofNat bs.length)), (O.nrR, .imm O.nums.write)] ++
        [O.trap] ++ O.st x O.res).length
  sel_writeMem : ∀ P i pc fn x o p l b d,
    D.instr P i pc fn (.ext "write" false x [.word o, .mem p l]) = .ok (b, d) →
      ∃ is, O.memTail (C.k + C.c) O.nums.write x o l = some is ∧ b = O.memA p 0 ++ is.map O.op ∧
        d = []
  sel_readMem : ∀ P i pc fn x o p l b d,
    D.instr P i pc fn (.ext "read" false x [.word o, .outMem p l]) = .ok (b, d) →
      ∃ is, O.memTail (C.k + C.c) O.nums.read x o l = some is ∧ b = O.memA p 0 ++ is.map O.op ∧
        d = []
  cnt_writeMem : ∀ P fn x o p l is, O.memTail (C.k + C.c) O.nums.write x o l = some is →
    cnt P fn (.ext "write" false x [.word o, .mem p l]) = O.memLen p 0 + is.length
  cnt_readMem : ∀ P fn x o p l is, O.memTail (C.k + C.c) O.nums.read x o l = some is →
    cnt P fn (.ext "read" false x [.word o, .outMem p l]) = O.memLen p 0 + is.length
  /-- The buffer of a one-byte `read` is its destination slot, which is never a register
  location. -/
  sel_read : ∀ P i pc fn x o b d, D.instr P i pc fn (.ext "read" false x [.word o, .out 1]) =
    .ok (b, d) → (C.k + C.c) ≤ x ∧ d = [] ∧
      b = (O.ld (O.argR 0) o ++ O.rdPre x ++ [O.trap] ++ O.rdFix x ++ O.st x O.rdRes).map O.op
  cnt_read : ∀ P fn x o, cnt P fn (.ext "read" false x [.word o, .out 1]) =
    (O.ld (O.argR 0) o ++ O.rdPre x ++ [O.trap] ++ O.rdFix x ++ O.st x O.rdRes).length

namespace Ops

variable {O : Ops A} {abi : Abi A.isa} {C : Conv A} {D : Selector A}
  {cnt : Lin.Prog → Lin.Fn → Lin.Instr → Nat} {P : Lin.Prog} {AP : Asm.Prog A}
  {σ : String → Option UInt64} {lo N : Nat}

theorem Keeps.exc {k : Nat} {t t' : A.isa.Regs} {S : List O.Reg} (h : O.Keeps k t t') :
    O.KeepsExc k S t t' := fun x hx _ => h x hx

theorem KeepsExc.trans {k : Nat} {t₁ t₂ t₃ : A.isa.Regs} {S : List O.Reg}
    (h₁ : O.KeepsExc k S t₁ t₂) (h₂ : O.KeepsExc k S t₂ t₃) : O.KeepsExc k S t₁ t₃ :=
  fun x hx hS => (h₂ x hx hS).trans (h₁ x hx hS)

/-- A run that changes only registers of `L`, each in `S` or no location's, keeps the location
registers outside `S`. -/
theorem KeepsExc.of_regs {k : Nat} {t t' : A.isa.Regs} {S L : List O.Reg}
    (hL : ∀ r ∈ L, r ∈ S ∨ ∀ x, x < k → O.preg x ≠ r) (h : ∀ r, r ∉ L → O.get t' r = O.get t r) :
    O.KeepsExc k S t t' := fun x hx hS => h _ fun hm => by
  rcases hL _ hm with h' | h'
  · exact hS h'
  · exact h' x hx rfl

/-- An operand that reads no register of `S` reads the same value after a run that keeps the
location registers outside `S`. -/
theorem KeepsExc.op {k : Nat} {t t' : A.isa.Regs} {S : List O.Reg} (h : O.KeepsExc k S t t')
    {o : Operand} (ho : ∀ y, o = .slot y → y < k → O.preg y ∉ S) : O.KeepsOp k o t t' :=
  fun y hy hyk => h y hyk (ho y hy hyk)

theorem KeepsOp.imm {k : Nat} {t t' : A.isa.Regs} (w : UInt64) : O.KeepsOp k (.imm w) t t' :=
  fun _ h => by cases h

theorem Laws.straight_ldAll (hO : O.Laws abi C D cnt) (ω : Oracle) :
    ∀ (L : List (O.Reg × Operand)), (∀ q ∈ L, O.ldOk q.1) → ∀ i ∈ O.ldAll L, StraightC C abi ω i
  | [], _ => by simp
  | (r, o) :: L, h => by
    rw [ldAll_cons]
    exact List.forall_mem_append.2 ⟨hO.straight_ld ω r o (h _ List.mem_cons_self),
      hO.straight_ldAll ω L fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- `ldAll` into distinct registers, from a state with a related state's memory and stack pointer
in which each operand's register holds its value, leaves each register holding its operand and
every other register unchanged, when no operand reads a register loaded before it. -/
theorem Laws.run_ldAll (hO : O.Laws abi C D cnt) {ω : Oracle} {s : Lin.State}
    {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) :
    ∀ (L : List (O.Reg × Operand)) {t : MState A.isa.Regs},
    (∀ q ∈ L, O.ldOk q.1 ∧ Lin.OpsBelow [q.2] fn.frame) → O.NoClash (C.k + C.c) L →
    (L.map Prod.fst).Nodup →
    t.mem = m.mem → A.isa.sp t.regs = A.isa.sp m.regs → t.world.halted = false → O.Ok t →
    (∀ q ∈ L, O.KeepsOp (C.k + C.c) q.2 m.regs t.regs) →
    ∃ t', runIs abi ω (O.ldAll L) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      (∀ q ∈ L, O.get t'.regs q.1 = q.2.eval s.frame) ∧
      ∀ r, r ∉ L.map Prod.fst → O.get t'.regs r = O.get t.regs r
  | [], t, _, _, _, _, _, _, hOk, _ => ⟨t, rfl, rfl, rfl, rfl, hOk, by simp, fun _ _ => rfl⟩
  | (r, o) :: L, t, hL, hC, hnd, hm, hsp, hh, hOk, hK => by
    obtain ⟨t₁, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_ld (ω := ω) hM hok
      (hL _ List.mem_cons_self).1 (hL _ List.mem_cons_self).2 hm hsp hh hOk (hK _ List.mem_cons_self)
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨t₂, h2, hm2, hw2, hsp2, hOk2, hv2, hk2⟩ := hO.run_ldAll hM hok L
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hC.2 hnd.2 (hm1.trans hm) (hsp1.trans hsp)
      (hw1 ▸ hh) hOk1 fun q hq y hy hyk => by
        rw [hk1 _ (hC.1 q hq y hy hyk)]; exact hK q (List.mem_cons_of_mem _ hq) y hy hyk
    refine ⟨t₂, by rw [ldAll_cons, runIs_append, h1, Option.bind_some]; exact h2,
      hm2.trans hm1, hw2.trans hw1, hsp2.trans hsp1, hOk2, fun q hq => ?_, fun r' hr' => ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · rw [hk2 _ hnd.1, hv1]
      · exact hv2 q hq
    · simp only [List.map_cons, List.mem_cons, not_or] at hr'
      rw [hk2 _ hr'.2, hk1 _ hr'.1]

/-! ## Parallel moves -/

/-- A register location below `k + c` holds its location's value in a related state. -/
theorem Laws.get_preg (hO : O.Laws abi C D cnt) {s : Lin.State} {m : MState A.isa.Regs}
    {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    {y : Nat} (hy : y < C.k + C.c) (hF : y < fn.frame) : O.get m.regs (O.preg y) = s.frame y := by
  have := hM.locs y hF
  rw [if_pos hy, hO.reg_get _ _ hy] at this
  exact this

/-- The place of an operand holds its value, when its register still holds the related state's. -/
theorem Laws.view_place (hO : O.Laws abi C D cnt) {s : Lin.State} {m : MState A.isa.Regs}
    {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    {t : A.isa.Regs} {o : Operand} (ho : Lin.OpsBelow [o] fn.frame)
    (hk : O.KeepsOp (C.k + C.c) o m.regs t) :
    O.view s.frame t (O.place (C.k + C.c) o) = o.eval s.frame := by
  cases o with
  | imm w => rfl
  | slot y =>
    simp only [place, Sel.place]
    split
    · rename_i hy
      simp only [view, Operand.eval]
      rw [hk y rfl hy, hO.get_preg hM hy (ho y (by simp))]
    · rfl

/-- The place of an operand meets `EmitOk` as a source. -/
theorem emitOk_place {k F : Nat} {o : Operand} (ho : Lin.OpsBelow [o] F) :
    ∀ o', O.place k o = .inr o' → Lin.OpsBelow [o'] F ∧ ∀ y, o' = .slot y → k ≤ y := by
  intro o' h
  cases o with
  | imm w => cases h; exact ⟨ho, fun _ h => by cases h⟩
  | slot y =>
    simp only [place, Sel.place] at h
    split at h
    · cases h
    · cases h; exact ⟨ho, fun y' h => by cases h; omega⟩

theorem ExtLaws.straight_emit (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (ω : Oracle)
    {k F : Nat} : ∀ (l : List (Place O.Reg × Place O.Reg)), (∀ p ∈ l, O.EmitOk k F p) →
      ∀ i ∈ l.flatMap O.emit, StraightC C abi ω i
  | [], _ => by simp
  | p :: l, h => by
    rw [List.flatMap_cons]
    obtain ⟨⟨d, hd, hdk⟩, -⟩ := h p List.mem_cons_self
    refine List.forall_mem_append.2 ⟨?_, hE.straight_emit hO ω l fun q hq =>
      h q (List.mem_cons_of_mem _ hq)⟩
    obtain ⟨p1, p2⟩ := p
    cases hd
    cases p2 with
    | inl r => exact hE.straight_mv ω d r hdk
    | inr o => exact hO.straight_ld ω d o hdk

/-- Running the moves `l` one after another leaves each register as `PMove.run` does to the view
of the starting registers. -/
theorem ExtLaws.run_emit (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) {ω : Oracle}
    {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) :
    ∀ (l : List (Place O.Reg × Place O.Reg)) {t : MState A.isa.Regs},
    (∀ p ∈ l, O.EmitOk (C.k + C.c) fn.frame p) →
    t.mem = m.mem → A.isa.sp t.regs = A.isa.sp m.regs → t.world.halted = false → O.Ok t →
    ∃ t', runIs abi ω (l.flatMap O.emit) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      ∀ r, O.get t'.regs r = PMove.run (O.view s.frame t.regs) l (.inl r)
  | [], t, _, _, _, _, hOk => ⟨t, rfl, rfl, rfl, rfl, hOk, fun _ => rfl⟩
  | (p1, p2) :: l, t, hl, hm, hsp, hh, hOk => by
    obtain ⟨⟨d, hd, hdk⟩, hsrc⟩ := hl _ List.mem_cons_self
    simp only at hd hsrc; subst hd
    have one : ∃ t₁, runIs abi ω (O.emit (.inl d, p2)) t = some t₁ ∧ t₁.mem = t.mem ∧
        t₁.world = t.world ∧ A.isa.sp t₁.regs = A.isa.sp t.regs ∧ O.Ok t₁ ∧
        O.view s.frame t₁.regs = PMove.step (O.view s.frame t.regs) (.inl d) p2 := by
      have fin : ∀ (t₁ : MState A.isa.Regs) (v : UInt64), v = O.view s.frame t.regs p2 →
          O.get t₁.regs d = v → (∀ r', r' ≠ d → O.get t₁.regs r' = O.get t.regs r') →
          O.view s.frame t₁.regs = PMove.step (O.view s.frame t.regs) (.inl d) p2 := by
        intro t₁ v hv h1 h2
        funext q
        cases q with
        | inl r =>
          simp only [PMove.step, view, Sum.inl.injEq]
          split
          · subst r; rw [h1, hv]; cases p2 <;> rfl
          · exact h2 r ‹_›
        | inr o => simp [PMove.step, view]
      cases p2 with
      | inl r =>
        obtain ⟨t₁, h1, h2, h3, h4, h5, h6, h7⟩ := hE.run_mv (ω := ω) (r := r) hdk hh hOk
        exact ⟨t₁, h1, h2, h3, h4, h5, fin t₁ _ rfl h6 h7⟩
      | inr o =>
        obtain ⟨hob, hoy⟩ := hsrc o rfl
        obtain ⟨t₁, h1, h2, h3, h4, h5, h6, h7⟩ := hO.run_ld (ω := ω) hM hok hdk hob hm hsp hh hOk
          fun y hy hyk => absurd (hoy y hy) (by omega)
        exact ⟨t₁, h1, h2, h3, h4, h5, fin t₁ _ rfl h6 h7⟩
    obtain ⟨t₁, h1, hm1, hw1, hsp1, hOk1, hv1⟩ := one
    obtain ⟨t', h2, hm2, hw2, hsp2, hOk2, hv2⟩ := hE.run_emit hO hM hok l
      (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hm1.trans hm) (hsp1.trans hsp)
      (hw1 ▸ hh) hOk1
    refine ⟨t', by rw [List.flatMap_cons, runIs_append, h1, Option.bind_some, h2],
      hm2.trans hm1, hw2.trans hw1, hsp2.trans hsp1, hOk2, fun r => ?_⟩
    rw [hv2 r, hv1]; rfl

/-- The parallel move `ms` into registers, sequentialised by `PMove.seq` through `tmp`, leaves
every register but `tmp` as `PMove.par` does to the view of the starting registers. -/
theorem ExtLaws.run_seq (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) {ω : Oracle}
    {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) {tmp : O.Reg}
    (htmp : O.ldOk tmp) {n : Nat} {ms l : List (Place O.Reg × Place O.Reg)}
    (hs : PMove.seq (.inl tmp) n ms = some l) (hms : ∀ p ∈ ms, O.EmitOk (C.k + C.c) fn.frame p)
    (hnd : (ms.map (·.1)).Nodup) (ht : ∀ p ∈ ms, p.1 ≠ .inl tmp) {t : MState A.isa.Regs}
    (hm : t.mem = m.mem) (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hh : t.world.halted = false)
    (hOk : O.Ok t) :
    (∀ p ∈ l, O.EmitOk (C.k + C.c) fn.frame p) ∧
    ∃ t', runIs abi ω (l.flatMap O.emit) t = some t' ∧ t'.mem = t.mem ∧ t'.world = t.world ∧
      A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.Ok t' ∧
      ∀ r, r ≠ tmp → O.get t'.regs r = PMove.par (O.view s.frame t.regs) ms (.inl r) := by
  have hl : ∀ p ∈ l, O.EmitOk (C.k + C.c) fn.frame p := fun p hp => by
    refine ⟨?_, fun o ho => ?_⟩
    · rcases PMove.seq_dst n hs p hp with h | ⟨q, hq, he⟩
      · exact ⟨tmp, h, htmp⟩
      · exact he ▸ (hms q hq).1
    · rcases PMove.seq_src n hs p hp with h | ⟨q, hq, he⟩
      · rw [h] at ho; cases ho
      · exact (hms q hq).2 o (he.trans ho)
  obtain ⟨t', h1, h2, h3, h4, h5, h6⟩ := hE.run_emit hO hM hok l hl hm hsp hh hOk
  exact ⟨hl, t', h1, h2, h3, h4, h5, fun r hr => by
    rw [h6, PMove.seq_run n hnd ht hs _ _ fun e => hr (Sum.inl.inj e)]⟩

/-! ## The system calls -/

/-- The trap instruction as a run of one instruction. -/
theorem ExtLaws.run_trap1 (hE : O.ExtLaws abi C D cnt) {ω : Oracle} {t t' : MState A.isa.Regs}
    (hOk : O.Ok t) (hh : t.world.halted = false) (h : abi.trap ω t = some t') :
    ∃ t'', runIs abi ω [O.trap] t = some t'' ∧ t''.mem = t'.mem ∧ t''.world = t'.world ∧
      O.get t''.regs O.res = O.get t'.regs O.res ∧ O.Ok t'' ∧
      A.isa.sp t''.regs = A.isa.sp t.regs ∧ O.KeepsExc (C.k + C.c) O.sysRegs t.regs t''.regs := by
  obtain ⟨t'', he, h1, h2, h3, h4, h5⟩ := hE.run_trap ω t t' hOk h
  exact ⟨t'', by rw [runIs_cons abi hh he]; rfl, h1, h2, h3, h4, ((hE.straight_trap ω).1 t t'' he).2, h5⟩

/-- The trap with the number of `exit` leaves the world after the call. -/
theorem ExtLaws.trap_exit (hE : O.ExtLaws abi C D cnt) {ω : Oracle} {t : MState A.isa.Regs}
    (hOk : O.Ok t) (hh : t.world.halted = false) (hn : O.get t.regs O.nrR = O.nums.exit) :
    ∃ t', runIs abi ω [O.trap] t = some t' ∧
      t'.world = (t.world.call ω ⟨"exit", [O.get t.regs (O.argR 0)], [], []⟩ true).2 := by
  obtain ⟨pb, st, er, R, rfl, hnr, harg, -⟩ := hE.linux
  obtain ⟨t', h1, -, h2, -⟩ := hE.run_trap1 (ω := ω) hOk hh (t' := { t with
    regs := R.setRet (t.world.ask ω ⟨"exit", [O.get t.regs (O.argR 0)], [], []⟩ true).1.result t.regs,
    world := (t.world.ask ω ⟨"exit", [O.get t.regs (O.argR 0)], [], []⟩ true).2 })
    (by simp [Abi.trap, Abi.linux, hnr, hn, harg 0 t.regs (by omega), Ne.symm hE.nums.1,
      Memory.writeAll, fitOut])
  exact ⟨t', h1, by rw [h2, World.ask_snd]⟩

/-- The trap with the number of `write` writes the bytes at argument 1, as many as argument 2
says, and leaves the call's result in `res`. -/
theorem ExtLaws.trap_write (hE : O.ExtLaws abi C D cnt) {ω : Oracle} {t : MState A.isa.Regs}
    {bs : List UInt8} (hOk : O.Ok t) (hh : t.world.halted = false)
    (hn : O.get t.regs O.nrR = O.nums.write)
    (hrd : t.mem.read (O.get t.regs (O.argR 1)) (O.get t.regs (O.argR 2)).toNat = some bs) :
    ∃ t', runIs abi ω [O.trap] t = some t' ∧ t'.mem = t.mem ∧
      t'.world = (t.world.call ω ⟨"write", [O.get t.regs (O.argR 0)], [bs], []⟩ false).2 ∧
      O.get t'.regs O.res = (t.world.call ω ⟨"write", [O.get t.regs (O.argR 0)], [bs], []⟩ false).1 ∧
      O.Ok t' ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.KeepsExc (C.k + C.c) O.sysRegs t.regs t'.regs := by
  obtain ⟨pb, st, er, R, rfl, hnr, harg, hret⟩ := hE.linux
  obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := hE.run_trap1 (ω := ω) hOk hh (t' := { t with
    regs := R.setRet (t.world.ask ω ⟨"write", [O.get t.regs (O.argR 0)], [bs], []⟩ false).1.result t.regs,
    world := (t.world.ask ω ⟨"write", [O.get t.regs (O.argR 0)], [bs], []⟩ false).2 })
    (by simp [Abi.trap, Abi.linux, hnr, hn, harg 0 t.regs (by omega), harg 1 t.regs (by omega),
      harg 2 t.regs (by omega), hrd, hE.nums.2.2, Ne.symm hE.nums.2.1, Memory.writeAll, fitOut])
  exact ⟨t', h1, h2, by rw [h3, World.ask_snd], by rw [h4, hret, World.ask_fst_nil], h5, h6, h7⟩

/-- The trap with the number of `read` writes at most argument 2 bytes into the buffer at
argument 1 and leaves the call's result in `res`. -/
theorem ExtLaws.trap_read (hE : O.ExtLaws abi C D cnt) {ω : Oracle} {t : MState A.isa.Regs}
    {m' : Memory} (hOk : O.Ok t) (hh : t.world.halted = false)
    (hn : O.get t.regs O.nrR = O.nums.read)
    (hw : t.mem.write (O.get t.regs (O.argR 1)) ((fitOut [(O.get t.regs (O.argR 2)).toNat]
      (t.world.ask ω ⟨"read", [O.get t.regs (O.argR 0)], [], [(O.get t.regs (O.argR 2)).toNat]⟩
        false).1.bytesOut).headD []) = some m') :
    ∃ t', runIs abi ω [O.trap] t = some t' ∧ t'.mem = m' ∧
      t'.world = (t.world.ask ω ⟨"read", [O.get t.regs (O.argR 0)], [],
        [(O.get t.regs (O.argR 2)).toNat]⟩ false).2 ∧
      O.get t'.regs O.res = (t.world.ask ω ⟨"read", [O.get t.regs (O.argR 0)], [],
        [(O.get t.regs (O.argR 2)).toNat]⟩ false).1.result ∧
      O.Ok t' ∧ A.isa.sp t'.regs = A.isa.sp t.regs ∧ O.KeepsExc (C.k + C.c) O.sysRegs t.regs t'.regs := by
  obtain ⟨pb, st, er, R, rfl, hnr, harg, hret⟩ := hE.linux
  obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := hE.run_trap1 (ω := ω) hOk hh (t' := { t with
    mem := m',
    regs := R.setRet (t.world.ask ω ⟨"read", [O.get t.regs (O.argR 0)], [],
      [(O.get t.regs (O.argR 2)).toNat]⟩ false).1.result t.regs,
    world := (t.world.ask ω ⟨"read", [O.get t.regs (O.argR 0)], [],
      [(O.get t.regs (O.argR 2)).toNat]⟩ false).2 }) (by
      simp only [Abi.trap, Abi.linux, hnr, hn, harg 0 t.regs (by omega), harg 1 t.regs (by omega),
        harg 2 t.regs (by omega), hE.nums.1, hE.nums.2.1, ite_false, ite_true]
      rw [fitOut_single]
      simp only [Memory.writeAll, hw, Option.bind_some, Option.map_some])
  exact ⟨t', h1, h2, h3, by rw [h4, hret], h5, h6, h7⟩


/-! ## The cases -/

/-- A block that sets location `x` and destroys the locations of `C.kill ins` is matched when it
is straight-line code `pre` followed by `post`, which is the store of `r` into `x`, or nothing
when `x` is a register location that `pre` leaves `r = preg x` in. The code `pre` must run from a
related state to a state that holds the value in `r`, has the next world and Lin heap, and keeps
every location register but `x` that is preserved or that `ins` does not destroy. The machine
reaches a state related to the next Lin state up to the destroyed locations, which the clobber
check shows dead after the instruction. -/
theorem sim_setK (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) {ω : Oracle} {κ : CostModel} {s : Lin.State} {m : MState A.isa.Regs}
    {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hok : D.fnOk fn = true) {b : List A.SInstr} (hblk : f.blocks[s.pc]? = some b)
    {ins : Lin.Instr} (hi : fn.code[s.pc]? = some ins) {x : Nat} (hx : x < fn.frame)
    (hdef : ∀ y, RegAlloc.Live.defs P ins y = true → y = x) (hclob : ClobOk C P)
    {pre post : List A.isa.Instr} {r : O.Reg}
    (hpost : (post = O.st x r ∧ O.stOk r) ∨ (x < C.k + C.c ∧ post = [] ∧ r = O.preg x))
    (hres : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b =
      some (pre ++ post))
    (hcode : SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b)
    (hpre : ∀ i ∈ pre, StraightC C abi ω i) {t : MState A.isa.Regs}
    (hrun : runIs abi ω pre m = some t) (hR : Region t.mem lo N)
    (hwd : ∀ i, i < N → ((C.k + C.c) ≤ x → i ≠ j + x - C.c) → word t.mem lo i = word m.mem lo i)
    (hK : ∀ z, z < C.k + C.c → z ≠ x → (z < C.k ∨ C.kill ins z = false) →
      O.get t.regs (O.preg z) = O.get m.regs (O.preg z))
    {v : UInt64} {h' : Flat.Heap} {w' : World}
    (he : (Lin.exec κ ω fn ins s).getD s =
      { s with pc := s.pc + 1, frame := s.frame.set x v, mem := h', world := w' })
    (hD : DataOk P σ lo t.mem h') (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hOk : O.Ok t)
    (hw : t.world = w') (hh : w'.halted = false) (hv : O.get t.regs r = v) (c : Nat) :
    ∃ m', (M abi).run ω (m, c) (pre ++ post).length = some (m', c + (pre ++ post).length) ∧
      (∃ s'', (RegAlloc.Live.flex P).R ((Lin.exec κ ω fn ins s).getD s) s'' ∧
        MatchAt C P AP σ lo N s'' m' fn f a j) ∧
      RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs) (m, c) (pre ++ post).length := by
  rw [he]
  have hroom := hM.room; unfold frameW at hroom
  obtain ⟨is, code, hr', hen, hc⟩ := hcode
  rw [hres] at hr'; cases hr'
  obtain ⟨t2, h2, hw2, hwd2, hreg2, hx2, hD2, hs2⟩ : ∃ t2, runIs abi ω post t = some t2 ∧
      t2.world = t.world ∧
      (∀ i, i < N → ((C.k + C.c) ≤ x → i ≠ j + x - C.c) → word t2.mem lo i = word m.mem lo i) ∧
      (∀ z, z < C.k + C.c → z ≠ x → O.get t2.regs (O.preg z) = O.get t.regs (O.preg z)) ∧
      locVal C lo t2 j x = v ∧ DataOk P σ lo t2.mem h' ∧ ∀ i ∈ post, StraightC C abi ω i := by
    rcases hpost with ⟨rfl, hr⟩ | ⟨hxk, rfl, rfl⟩
    · by_cases hxk : x < C.k + C.c
      · obtain ⟨t2, h2, hm2, hw2, -, hv2, hk2⟩ := hO.run_stReg (ω := ω) (t := t) hxk hr (hw ▸ hh) hOk
        refine ⟨t2, h2, hw2, fun i hi h => by rw [hm2]; exact hwd i hi h,
          fun z hz hzx => hk2 _ fun he => hzx (hO.preg_inj z x hz hxk he), ?_, hm2 ▸ hD,
          hO.straight_st ω x r hr⟩
        simp only [locVal, hxk, ite_true, hO.reg_get _ _ hxk, hv2, hv]
      · obtain ⟨mem', hwr, -, hF, hval, hrest⟩ := writeWord_wa hR (show j + x - C.c < N by omega)
          (O.get t.regs r)
        obtain ⟨t2, h2, hm2, hw2, -, hk2⟩ := hO.run_st (ω := ω) hM hok hr (by omega) hx hsp
          (hw ▸ hh) hOk hwr
        subst hm2
        refine ⟨t2, h2, hw2, fun i hi h => by rw [hrest i hi (h (by omega))]; exact hwd i hi h,
          fun z hz _ => hk2 z hz, ?_, dataOk_keep (by have := hR.top; omega) hD hF
            (writeWord_wa_low hR (show j + x - C.c < N by omega) hwr), hO.straight_st ω x r hr⟩
        simp only [locVal, hxk, ite_false, hval, hv]
    · refine ⟨t, rfl, rfl, hwd, fun _ _ _ => rfl, ?_, hD, by simp⟩
      simp only [locVal, hxk, ite_true, hO.reg_get _ _ hxk, hv]
  have hL := hM.locs
  refine ⟨t2, ?_⟩
  exact sim_straight_kill
    (s' := { s with pc := s.pc + 1, frame := s.frame.set x v, mem := h', world := w' })
    hl hil hM hi hclob hblk hres hen hc (List.forall_mem_append.2 ⟨hpre, hs2⟩)
    (by rw [runIs_append, hrun, Option.bind_some]; exact h2) (hw2.trans hw) hh rfl rfl rfl
    (fun y hy hk => by
      by_cases hyx : y = x
      · subst hyx; simp only [Flat.Frame.set, ite_true]; exact hx2
      · have hkf : C.kill ins y = false := by
          rcases hk with h | h
          · exact h
          · exact absurd (hdef y h) hyx
        have := hL y hy
        simp only [Flat.Frame.set, hyx, ite_false, locVal]
        by_cases hyk : y < C.k + C.c
        · simp only [hyk, ite_true, hO.reg_get _ _ hyk] at this ⊢
          rw [hreg2 y hyk hyx, hK y hyk hyx (Or.inr hkf)]; exact this
        · simp only [hyk, ite_false] at this ⊢
          rw [hwd2 _ (by omega) fun _ => by omega]; exact this)
    (fun y hy => hwd2 _ (by omega) fun _ => by have := Nat.min_le_left C.k fn.frame; omega)
    (fun i hi hiN => hwd2 i hiN fun hk => by have := slot_lt_frameW hx hk; omega)
    (fun z hz hzk => by
      have hzK : z < C.k + C.c := by omega
      rw [hO.reg_get _ _ hzK, hO.reg_get _ _ hzK, hreg2 z hzK (by omega),
        hK z hzK (by omega) (Or.inl hzk)])
    hD2 c

/-- An extern call's block is matched when it is straight-line code `pre` followed by the store
of `r` into location `x`, as `sim_setK` says. -/
theorem sim_ext (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) {ω : Oracle} {κ : CostModel} {s : Lin.State} {m : MState A.isa.Regs}
    {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hok : D.fnOk fn = true) {b : List A.SInstr} (hblk : f.blocks[s.pc]? = some b)
    {sym : String} {nr : Bool} {x : Nat} {args : List Flat.ExtArg}
    (hi : fn.code[s.pc]? = some (.ext sym nr x args)) (hx : x < fn.frame) (hclob : ClobOk C P)
    {pre : List A.isa.Instr} {r : O.Reg} (hr : O.stOk r)
    (hres : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b =
      some (pre ++ O.st x r))
    (hcode : SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b)
    (hpre : ∀ i ∈ pre, StraightC C abi ω i) (hpos : 0 < pre.length) {t : MState A.isa.Regs}
    (hrun : runIs abi ω pre m = some t) (hR : Region t.mem lo N)
    (hwd : ∀ i, i < N → ((C.k + C.c) ≤ x → i ≠ j + x - C.c) → word t.mem lo i = word m.mem lo i)
    (hK : ∀ z, z < C.k + C.c → (z < C.k ∨ C.kill (.ext sym nr x args) z = false) →
      O.get t.regs (O.preg z) = O.get m.regs (O.preg z))
    {v : UInt64} {h' : Flat.Heap} {w' : World}
    (hext : Flat.extRun ω sym nr args s.frame s.mem s.world = (v, h', w'))
    (hD : DataOk P σ lo t.mem h') (hsp : A.isa.sp t.regs = A.isa.sp m.regs) (hOk : O.Ok t)
    (hw : t.world = w') (hh : w'.halted = false) (hv : O.get t.regs r = v) (c : Nat) {n : Nat}
    (hn : n = (pre ++ O.st x r).length) :
    0 < n ∧ ∃ m', (M abi).run ω (m, c) n = some (m', c + n) ∧
      (∃ s'', (RegAlloc.Live.flex P).R ((Lin.exec κ ω fn (.ext sym nr x args) s).getD s) s'' ∧
        MatchAt C P AP σ lo N s'' m' fn f a j) ∧
      RunAll abi ω (fun y => A.isa.sp y.regs = A.isa.sp m.regs) (m, c) n := by
  subst hn
  exact ⟨by simp only [List.length_append]; omega,
    sim_setK hO hl hil hM hok hblk hi hx (fun y h => by simpa [RegAlloc.Live.defs] using h) hclob
      (Or.inl ⟨rfl, hr⟩) hres hcode hpre hrun hR hwd (fun z hz _ hk => hK z hz hk)
      (by simp [Lin.exec, hext]) hD hsp hOk hw hh hv c⟩

/-- The case `bin op x o₁ o₂`, whose code is `src r0 o₁`, `binOps op (dst x)` and `fin x`. It
destroys the locations in the registers `binKill op`, which the clobber check shows dead. -/
theorem sim_bin (hO : O.Laws abi C D cnt) {asm : Asm.Assembler A} (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) (hclob : ClobOk C P) :
    LocalOkK abi C P AP σ lo N (cnt P) fun i => ∃ op x a b, i = .bin op x a b := by
  intro ω κ s m c fn f a j ins hM hi ⟨op, x, o₁, o₂, he⟩ _
  subst he
  obtain ⟨hok, hblk, hcode, hx, ho⟩ :=
    case_start hl hsel hwf hM hi (hO.sel_bin P · s.pc fn op x o₁ o₂)
  obtain ⟨t₁, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_src (ω := ω) hM hok hO.ld0
    (fun y hy => ho y (by simp at hy ⊢; exact Or.inl hy)) rfl rfl hM.halted (hO.ok_match hM)
    ((Keeps.refl _).op _)
  have hK1 : O.Keeps (C.k + C.c) m.regs t₁.regs := Keeps.of_others hO.ne_r0 hk1
  obtain ⟨t₃, h3, hm3, hw3, hsp3, hOk3, hv3, hk3⟩ := hO.run_binOps (ω := ω) hM hok op o₁
    (hO.ldOk_dst x) (fun y hy => ho y (by simp at hy ⊢; exact Or.inr hy)) hm1 hsp1
    (hw1 ▸ hM.halted) hOk1 hK1 hv1
  rw [hO.cnt_bin]
  have hpos : 0 < (O.binIs (C.k + C.c) op x o₁ o₂).length := by
    have := hO.binOps_pos op (O.dst (C.k + C.c) x) (O.src O.r0 o₁).2 o₂; simp [binIs]; omega
  refine ⟨hpos, ?_⟩
  have hb : O.binIs (C.k + C.c) op x o₁ o₂ = ((O.src O.r0 o₁).1 ++
      O.binOps op (O.dst (C.k + C.c) x) (O.src O.r0 o₁).2 o₂) ++
      O.fin (C.k + C.c) x (O.binRes op (O.dst (C.k + C.c) x)) := rfl
  rw [hb] at hpos ⊢
  exact sim_setK hO hl hil hM hok hblk hi hx
    (fun y h => by simpa [RegAlloc.Live.defs] using h) hclob
    (by
      unfold fin
      by_cases hxk : x < C.k + C.c
      · refine Or.inr ⟨hxk, by simp [hxk], ?_⟩
        simp only [dst, hxk, ite_true]; exact hO.binRes_preg op x hxk
      · refine Or.inl ⟨by simp [hxk], ?_⟩
        have hd : O.dst (C.k + C.c) x = O.r0 := by simp [dst, hxk]
        rw [hd]; exact hO.stBin op)
    (by rw [← hb]; exact hO.resolveAt_op _ _) hcode
    (List.forall_mem_append.2 ⟨hO.straight_src ω _ _ hO.ld0,
      hO.straight_binOps ω op _ _ _ (hO.ldOk_dst x)⟩)
    (by rw [runIs_append, h1, Option.bind_some, h3])
    (by rw [hm3, hm1]; exact hM.region) (fun i _ _ => by rw [hm3, hm1])
    (fun z hz hzx hk => by
      rw [hk3 z hz (fun h => ?_) (fun h => ?_)]
      · exact hK1 z hz
      · unfold dst at h; split at h
        · exact hzx (hO.preg_inj z x hz ‹_› h)
        · exact hO.ne_r0 z hz h
      · obtain ⟨hkz, hkill⟩ := hO.kill_bin op z hz h
        rcases hk with h' | h'
        · omega
        · rw [hkill] at h'; cases h')
    (v := op.eval (o₁.eval s.frame) (o₂.eval s.frame)) (h' := s.mem) (w' := s.world)
    (by simp [Lin.exec]) (by rw [hm3, hm1]; exact hM.data) (by rw [hsp3, hsp1]) hOk3
    (by rw [hw3, hw1, hM.world]) (hM.world ▸ hM.halted) hv3 c

theorem KeepsExc.of_one {k : Nat} {t t' : A.isa.Regs} {S : List O.Reg} {r : O.Reg} (hr : r ∈ S)
    (h : ∀ r', r' ≠ r → O.get t' r' = O.get t r') : O.KeepsExc k S t t' :=
  KeepsExc.of_regs (L := [r]) (by simp [hr]) fun r' h' => h r' (by simpa using h')

theorem KeepsExc.of_ldAll {k : Nat} {t t' : A.isa.Regs} {S : List O.Reg}
    {L : List (O.Reg × Operand)} (hL : ∀ q ∈ L, q.1 ∈ S)
    (h : ∀ r, r ∉ L.map Prod.fst → O.get t' r = O.get t r) : O.KeepsExc k S t t' :=
  KeepsExc.of_regs (L := L.map Prod.fst) (fun r hr => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr; exact Or.inl (hL q hq)) h

/-- A run that keeps every location register outside the system-call registers keeps every
preserved location register and every one an extern call does not destroy. -/
theorem ExtLaws.keep_kill (hE : O.ExtLaws abi C D cnt) {t t' : A.isa.Regs}
    (h : O.KeepsExc (C.k + C.c) O.sysRegs t t') {sym : String} {nr : Bool} {y : Nat}
    {args : List Flat.ExtArg} :
    ∀ z, z < C.k + C.c → (z < C.k ∨ C.kill (.ext sym nr y args) z = false) →
      O.get t' (O.preg z) = O.get t (O.preg z) := fun z hz hk => h z hz fun he => by
  obtain ⟨hkz, hkill⟩ := hE.kill_sys z hz he
  rcases hk with hk | hk
  · omega
  · rw [hkill] at hk; cases hk

/-- The register of the number and the three argument registers are distinct. -/
theorem ExtLaws.regs_ne (hE : O.ExtLaws abi C D cnt) :
    O.nrR ≠ O.argR 0 ∧ O.nrR ≠ O.argR 1 ∧ O.nrR ≠ O.argR 2 ∧ O.argR 0 ≠ O.argR 1 ∧
      O.argR 0 ≠ O.argR 2 ∧ O.argR 1 ≠ O.argR 2 := by
  have h := hE.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2.1⟩

variable {asm : Asm.Assembler A}

theorem sim_exit (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) :
    HaltOk abi C P AP σ lo N (cnt P) fun i => ∃ x o, i = .ext "exit" true x [.word o] := by
  intro ω κ s m c fn f a j ins hM hi ⟨x, o, he⟩
  subst he
  obtain ⟨hok, -, hcode, -, ho, -⟩ :=
    case_start hl hsel hwf hM hi (hE.sel_exit P · s.pc fn x o)
  have ⟨is, code, hr, hen, hc⟩ := hcode
  rw [hO.resolveAt_op] at hr; cases hr
  obtain ⟨c₁, c₂, hcc, he₁, -⟩ := encodeAll_append _ _ _ hen
  have hne := hE.regs_ne
  obtain ⟨t, h1, -, hw1, -, hOk1, hv1, -⟩ := hO.run_ldAll (ω := ω) hM hok
    [(O.argR 0, o), (O.nrR, .imm O.nums.exit)]
    (by simp [hE.ld_nr, hE.ld_arg 0 (by omega), ho o]) (by simp [NoClash])
    (by simp [Ne.symm hne.1]) rfl rfl hM.halted (hO.ok_match hM) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      · exact (Keeps.refl _).op _
      · exact KeepsOp.imm _)
  obtain ⟨t', h2, hw2⟩ := hE.trap_exit (ω := ω) hOk1 (hw1 ▸ hM.halted)
    (hv1 (O.nrR, .imm O.nums.exit) (by simp))
  obtain ⟨hrun, -, -, -, hall⟩ := run_straight hil c hM.wx he₁
    (by rw [hM.rip]; exact (codeAt_append _ _ _ _ (hcc ▸ hc)).1)
    (fun i hi => (List.forall_mem_append.2 ⟨hO.straight_ldAll ω _ (by simp [hE.ld_nr, hE.ld_arg 0]),
      by simpa using hE.straight_trap ω⟩ i hi).1)
    (by rw [runIs_append, h1, Option.bind_some, h2])
  rw [hE.cnt_exit]
  refine ⟨by simp; omega, t', hrun, by simp [Lin.exec, Flat.extRun, Flat.extOutArg, World.call, hM.run],
    ?_, hall⟩
  rw [hw2, hw1, hM.world, hv1 (O.argR 0, o) (by simp)]
  simp [Lin.exec, Flat.extRun, Flat.extOutArg, Flat.extWords, Flat.extBytes, Flat.extCaps]

/-- The case `write(o, bs)` of constant bytes. Its code loads the descriptor, the bytes' address
with `symA`, the length and the number, runs the trap and stores the result into location `x`. -/
theorem sim_write (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) (hclob : ClobOk C P) :
    LocalOkK abi C P AP σ lo N (cnt P) fun i => ∃ x o bs, i = .ext "write" false x [.word o, .bytes bs] := by
  intro ω κ s m c fn f a j ins hM hi ⟨x, o, bs, he⟩ _
  subst he
  obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d, hsi, hdata⟩ := hC.instr
  obtain ⟨hlen, rfl, rfl⟩ := hE.sel_write _ _ _ _ _ _ _ _ _ hsi
  obtain ⟨hx, ho, -⟩ := hC.wf
  have hok := hC.sel.ok
  have hne := hE.regs_ne
  obtain ⟨Dd, hDd, hread, -⟩ := hM.loaded.2 _ (hdata _ List.mem_cons_self)
  obtain ⟨is, code, hr, hen, -⟩ := hC.code
  obtain ⟨pre, rfl, hplen, hpre, hrun⟩ :=
    hO.run_sym (ω := ω) (ρ := f.refAddr σ a) (hE.ld_arg 1 (by omega)) hDd hr
  obtain ⟨cxp, -, -, hexp, -⟩ := encodeAll_append _ _ _ hen
  obtain ⟨cx, -, -, hex, -⟩ := encodeAll_append _ _ _ hexp
  obtain ⟨t1, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_ld (ω := ω) hM hok
    (hE.ld_arg 0 (by omega)) (ho o (by simp)) rfl rfl hM.halted (hO.ok_match hM)
    ((Keeps.refl _).op _)
  obtain ⟨t2, h2, hm2, hw2, hsp2, hOk2, hv2, hk2⟩ := hrun cx t1 hex
    (by rw [runIs_pc (fun i h => (hO.straight_ld ω _ o (hE.ld_arg 0 (by omega)) i h).1) hex h1, hM.rip])
    (hw1 ▸ hM.halted) hOk1
  obtain ⟨t3, h3, hm3, hw3, hsp3, hOk3, hv3, hk3⟩ := hO.run_ldAll (ω := ω) hM hok
    [(O.argR 2, .imm (UInt64.ofNat bs.length)), (O.nrR, .imm O.nums.write)]
    (by simp [hE.ld_nr, hE.ld_arg 2]) (by simp [NoClash]) (by simp [Ne.symm hne.2.2.1])
    (hm2.trans hm1) (hsp2.trans hsp1) (by rw [hw2, hw1]; exact hM.halted) hOk2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl) <;> exact KeepsOp.imm _)
  have e0 : O.get t3.regs (O.argR 0) = o.eval s.frame := by
    rw [hk3 _ (by simp [hne.1.symm, hne.2.2.2.2.1]), hk2 _ hne.2.2.2.1, hv1]
  have e1 : O.get t3.regs (O.argR 1) = Dd := by
    rw [hk3 _ (by simp [hne.2.1.symm, hne.2.2.2.2.2]), hv2]
  obtain ⟨t4, h4, hm4, hw4, hv4, hOk4, hsp4, hk4⟩ := hE.trap_write (ω := ω) (bs := bs) hOk3
    (by rw [hw3, hw2, hw1]; exact hM.halted) (hv3 (O.nrR, .imm O.nums.write) (by simp))
    (by rw [e1, hv3 (O.argR 2, .imm (UInt64.ofNat bs.length)) (by simp), hm3, hm2, hm1]
        simpa [Nat.mod_eq_of_lt (show bs.length < 2 ^ 64 by omega)] using hread)
  have htm : t4.mem = m.mem := by rw [hm4, hm3, hm2, hm1]
  rw [hE.cnt_write]
  refine sim_ext hO hl hil hM hok hC.blk hi hx hclob hE.st_res (pre := O.ld (O.argR 0) o ++ pre ++
    O.ldAll [(O.argR 2, .imm (UInt64.ofNat bs.length)), (O.nrR, .imm O.nums.write)] ++ [O.trap])
    (v := (s.world.call ω ⟨"write", [o.eval s.frame], [bs], []⟩ false).1) (h' := s.mem)
    (w' := (s.world.call ω ⟨"write", [o.eval s.frame], [bs], []⟩ false).2)
    (by rw [hr]; simp) hC.code
    (List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨hO.straight_ld ω _ o (hE.ld_arg 0 (by omega)), hpre⟩,
      hO.straight_ldAll ω _ (by simp [hE.ld_nr, hE.ld_arg 2])⟩, by simpa using hE.straight_trap ω⟩)
    (by simp; omega)
    (by rw [runIs_append, runIs_append, runIs_append, h1, Option.bind_some, h2, Option.bind_some,
      h3, Option.bind_some, h4])
    (htm ▸ hM.region) (fun _ _ _ => by rw [htm])
    (hE.keep_kill (((KeepsExc.of_one (by simp [sysRegs]) hk1).trans
      (KeepsExc.of_one (by simp [sysRegs]) hk2)).trans
      ((KeepsExc.of_ldAll (by simp [sysRegs]) hk3).trans hk4)))
    (by simp [Flat.extRun, Flat.extOutArg, Flat.extWords, Flat.extBytes, Flat.extCaps])
    (htm ▸ hM.data) (by rw [hsp4, hsp3, hsp2, hsp1]) hOk4
    (by rw [hw4, e0, hw3, hw2, hw1, hM.world]) (by simp [World.call, hM.run])
    (by rw [hv4, e0, hw3, hw2, hw1, hM.world]) c (by simp [hplen]; omega)

/-- The code of a `write` or `read` of a data-region buffer up to the trap. It computes the
address with `memA` and then runs the parallel move of `memMoves`, which puts the address into
argument 1, the descriptor, the length and the number into their registers. -/
theorem ExtLaws.run_memArgs (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) {ω : Oracle}
    {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) (hok : D.fnOk fn = true) {nr : UInt64} {x : Nat}
    {o p l : Operand} (ho : Lin.OpsBelow [o] fn.frame) (hpl : Lin.OpsBelow [p, l] fn.frame)
    {Dm : UInt64} (hDm : σ memSym = some Dm) {tl : List A.isa.Instr}
    (htl : O.memTail (C.k + C.c) nr x o l = some tl) {is : List A.isa.Instr}
    (hr : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc))
      (O.memA p 0 ++ tl.map O.op) = some is)
    {code : List UInt8} (hen : Asm.encodeAll A.isa is = some code) :
    ∃ pre t, is = pre ++ [O.trap] ++ O.st x O.res ∧
      (pre ++ [O.trap] ++ O.st x O.res).length = O.memLen p 0 + tl.length ∧
      (∀ i ∈ pre, StraightC C abi ω i) ∧ runIs abi ω pre m = some t ∧ t.mem = m.mem ∧
      t.world = m.world ∧ A.isa.sp t.regs = A.isa.sp m.regs ∧ O.Ok t ∧
      O.get t.regs O.nrR = nr ∧ O.get t.regs (O.argR 0) = o.eval s.frame ∧
      O.get t.regs (O.argR 1) = Dm + p.eval s.frame ∧ O.get t.regs (O.argR 2) = l.eval s.frame ∧
      O.KeepsExc (C.k + C.c) O.sysRegs m.regs t.regs := by
  have hne := hE.regs_ne
  have hl : Lin.OpsBelow [l] fn.frame := fun y hy => hpl y (by simp at hy ⊢; exact Or.inr hy)
  simp only [memTail, Option.map_eq_some_iff] at htl
  obtain ⟨ms, hseq, rfl⟩ := htl
  obtain ⟨pre, t, rfl, hlen, hpre, h1, hm1, hw1, hsp1, hOk1, hv1, hK1⟩ :=
    hO.run_mem (ω := ω) hM hok (fun y hy => hpl y (by simp at hy ⊢; exact Or.inl hy)) hDm hr hen
  have hr1 := hE.r1_sys
  simp only [sysRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr1
  have hms : ∀ q ∈ O.memMoves (C.k + C.c) nr o l, O.EmitOk (C.k + C.c) fn.frame q := by
    simp only [memMoves, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    · exact ⟨⟨_, rfl, hE.ld_arg 1 (by omega)⟩, fun _ h => by cases h⟩
    · exact ⟨⟨_, rfl, hE.ld_arg 0 (by omega)⟩, emitOk_place ho⟩
    · exact ⟨⟨_, rfl, hE.ld_arg 2 (by omega)⟩, emitOk_place hl⟩
    · exact ⟨⟨_, rfl, hE.ld_nr⟩, fun _ h => by cases h; exact ⟨by simp, fun _ h => by cases h⟩⟩
  obtain ⟨hl2, t2, h2, hm2, hw2, hsp2, hOk2, hv2⟩ := hE.run_seq hO hM hok hO.ld1 hseq hms
    (by simp [memMoves, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2, Ne.symm hne.1, Ne.symm hne.2.1, Ne.symm hne.2.2.1, Ne.symm hne.2.2.2.1, Ne.symm hne.2.2.2.2.1, Ne.symm hne.2.2.2.2.2])
    (by simp [memMoves, Ne.symm hr1.1, Ne.symm hr1.2.1, Ne.symm hr1.2.2.1, Ne.symm hr1.2.2.2.1])
    hm1 hsp1 (hw1 ▸ hM.halted) hOk1
  have hnd : ((O.memMoves (C.k + C.c) nr o l).map (·.1)).Nodup := by
    simp [memMoves, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2, Ne.symm hne.1, Ne.symm hne.2.1, Ne.symm hne.2.2.1, Ne.symm hne.2.2.2.1, Ne.symm hne.2.2.2.2.1, Ne.symm hne.2.2.2.2.2]
  have val : ∀ r q, (Sum.inl r, q) ∈ O.memMoves (C.k + C.c) nr o l → r ≠ O.r1 →
      O.get t2.regs r = O.view s.frame t.regs q := fun r q hq hr => by
    rw [hv2 r hr, PMove.par_of_mem hnd _ hq]
  have hK := hK1
  refine ⟨pre ++ ms.flatMap O.emit, t2, by simp, by simp [hlen], List.forall_mem_append.2
    ⟨hpre, hE.straight_emit hO ω ms hl2⟩,
    by rw [runIs_append, h1, Option.bind_some, h2], by rw [hm2, hm1], by rw [hw2, hw1],
    by rw [hsp2, hsp1], hOk2, val _ (.inr (.imm nr)) (by simp [memMoves]) (Ne.symm hr1.1),
    (val _ (O.place (C.k + C.c) o) (by simp [memMoves]) (Ne.symm hr1.2.1)).trans (hO.view_place hM ho (hK.op o)),
    (val _ (.inl O.r0) (by simp [memMoves]) (Ne.symm hr1.2.2.1)).trans (by simp [view, hv1]),
    (val _ (O.place (C.k + C.c) l) (by simp [memMoves]) (Ne.symm hr1.2.2.2.1)).trans (hO.view_place hM hl (hK.op l)),
    fun z hz hS => ?_⟩
  simp only [sysRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
  rw [hv2 _ (hO.ne_r1 z hz), PMove.par_of_not _ fun q hq => by
    simp only [memMoves, List.mem_cons, Prod.mk.injEq, Sum.inl.injEq, List.not_mem_nil,
      or_false] at hq
    rcases hq with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hS.2.2.1 h
    · exact hS.2.1 h
    · exact hS.2.2.2.1 h
    · exact hS.1 h]
  exact hK z hz

/-- The case `write(o, p, l)` of a data-region buffer. After the arguments, the trap reads Lin's
bytes from the data region and the result is stored into location `x`. -/
theorem sim_writeMem (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) (hclob : ClobOk C P) :
    LocalOkK abi C P AP σ lo N (cnt P) fun i => ∃ x o p l, i = .ext "write" false x [.word o, .mem p l] := by
  intro ω κ s m c fn f a j ins hM hi ⟨x, o, p, l, he⟩ hmo
  subst he
  obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  obtain ⟨tl, htl, rfl, rfl⟩ := hE.sel_writeMem _ _ _ _ _ _ _ _ _ _ hsi
  obtain ⟨hx, ho, hml, -⟩ := hC.wf
  have hok := hC.sel.ok
  have hblk := hC.blk
  have hcode := hC.code
  obtain ⟨Dm, hDm, hDlo, hDR⟩ := hM.data
  have hb : (p.eval s.frame).toNat + (l.eval s.frame).toNat ≤ P.mem := by
    simpa [Lin.Instr.memOk, Lin.extMemOk, Lin.inDataN] using hmo
  obtain ⟨is, code, hr, hen, -⟩ := id hcode
  obtain ⟨pre, t, rfl, hlen, hpre, h1, hm1, hw1, hsp1, hOk1, hn1, ha0, ha1, ha2, hK1⟩ :=
    hE.run_memArgs hO (ω := ω) hM hok (ho o (by simp)) (hml p l (by simp)) hDm htl hr hen
  obtain ⟨t2, h2, hm2, hw2, hv2, hOk2, hsp2, hk2⟩ := hE.trap_write (ω := ω) hOk1 (hw1 ▸ hM.halted) hn1
    (bs := s.mem.read (p.eval s.frame) (l.eval s.frame).toNat)
    (by rw [ha1, ha2, hm1]; exact read_data hDR (by have := hM.region.top; omega) _ _ hb)
  have htm : t2.mem = m.mem := hm2.trans hm1
  rw [hE.cnt_writeMem _ _ _ _ _ _ _ htl, ← hlen]
  exact sim_ext hO hl hil hM hok hblk hi hx hclob hE.st_res (h' := s.mem)
    (v := (s.world.call ω ⟨"write", [o.eval s.frame],
      [s.mem.read (p.eval s.frame) (l.eval s.frame).toNat], []⟩ false).1)
    (w' := (s.world.call ω ⟨"write", [o.eval s.frame],
      [s.mem.read (p.eval s.frame) (l.eval s.frame).toNat], []⟩ false).2) hr hcode
    (List.forall_mem_append.2 ⟨hpre, by simpa using hE.straight_trap ω⟩) (by simp)
    (by rw [runIs_append, h1, Option.bind_some, h2]) (htm ▸ hM.region) (fun _ _ _ => by rw [htm])
    (hE.keep_kill (hK1.trans hk2))
    (by simp [Flat.extRun, Flat.extOutArg, Flat.extWords, Flat.extBytes, Flat.extCaps])
    (htm ▸ hM.data) (by rw [hsp2, hsp1]) hOk2 (by rw [hw2, ha0, hw1, hM.world])
    (by simp [World.call, hM.run]) (by rw [hv2, ha0, hw1, hM.world]) c rfl

/-- The case `read(o, p, l)` into a data-region buffer. After the arguments, the trap writes the
bytes the oracle supplies, as Lin writes the same bytes, and the result is stored into location
`x`. -/
theorem sim_readMem (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) (hclob : ClobOk C P) :
    LocalOkK abi C P AP σ lo N (cnt P) fun i =>
      ∃ x o p l, i = .ext "read" false x [.word o, .outMem p l] := by
  intro ω κ s m c fn f a j ins hM hi ⟨x, o, p, l, he⟩ hmo
  subst he
  obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  obtain ⟨tl, htl, rfl, rfl⟩ := hE.sel_readMem _ _ _ _ _ _ _ _ _ _ hsi
  obtain ⟨hx, ho, -, hml⟩ := hC.wf
  have hok := hC.sel.ok
  have hblk := hC.blk
  have hcode := hC.code
  obtain ⟨Dm, hDm, hDlo, hDR⟩ := hM.data
  have hb : (p.eval s.frame).toNat + (l.eval s.frame).toNat ≤ P.mem := by
    simpa [Lin.Instr.memOk, Lin.extMemOk, Lin.inDataN] using hmo
  obtain ⟨is, code, hr, hen, -⟩ := id hcode
  obtain ⟨pre, t, rfl, hlen, hpre, h1, hm1, hw1, hsp1, hOk1, hn1, ha0, ha1, ha2, hK1⟩ :=
    hE.run_memArgs hO (ω := ω) hM hok (ho o (by simp)) (hml p l (by simp)) hDm htl hr hen
  generalize hq : s.world.ask ω ⟨"read", [o.eval s.frame], [], [(l.eval s.frame).toNat]⟩ false = q
  generalize hbs : (fitOut [(l.eval s.frame).toNat] q.1.bytesOut).headD [] = bs
  have hbl : bs.length ≤ (l.eval s.frame).toNat := hbs ▸ fitOut_one_le _ _
  obtain ⟨mem', hwr, hR', hF, hout⟩ :=
    write_data hDR (by have := hM.region.top; omega) bs (p.eval s.frame) (by omega)
  obtain ⟨t2, h2, hm2, hw2, hv2, hOk2, hsp2, hk2⟩ := hE.trap_read (ω := ω) (m' := mem') hOk1
    (hw1 ▸ hM.halted) hn1 (by rw [ha0, ha1, ha2, hm1, hw1, hM.world, hq, hbs]; exact hwr)
  rw [ha0, ha2, hw1, hM.world, hq] at hw2 hv2
  obtain ⟨hwd, hDok⟩ := hM.data_write hDm hR' (high_of_out hDlo (by omega) hout)
  rw [hE.cnt_readMem _ _ _ _ _ _ _ htl, ← hlen]
  exact sim_ext hO hl hil hM hok hblk hi hx hclob hE.st_res (v := q.1.result)
    (h' := Flat.Heap.writeBytes s.mem (p.eval s.frame) bs) (w' := q.2) hr hcode
    (List.forall_mem_append.2 ⟨hpre, by simpa using hE.straight_trap ω⟩) (by simp)
    (by rw [runIs_append, h1, Option.bind_some, h2])
    (hm2 ▸ region_frame hM.region (hm1 ▸ hF)) (fun k hk _ => by rw [hm2]; exact hwd k hk)
    (hE.keep_kill (hK1.trans hk2))
    (by simp only [Flat.extRun, Flat.extOutArg, Flat.extWords, Flat.extBytes, Flat.extCaps, hq,
      ← hbs])
    (by rw [hm2, ← hwrite_eq]; exact hDok) (by rw [hsp2, hsp1]) hOk2 hw2
    (by rw [← hq]; simp [World.ask, hM.run]) hv2 c rfl

/-- The case `read(o, buf, 1)` into slot `x`. Its code loads the descriptor and runs `rdPre`,
which clears the slot and loads its address, the length and the number. The trap writes at most
one byte into the slot, and `rdFix` makes the call's value, which is stored into slot `x`. -/
theorem sim_read (hO : O.Laws abi C D cnt) (hE : O.ExtLaws abi C D cnt) (hl : asm.Laws)
    (hil : A.isa.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf) (hclob : ClobOk C P) :
    LocalOkK abi C P AP σ lo N (cnt P) fun i => ∃ x o, i = .ext "read" false x [.word o, .out 1] := by
  intro ω κ s m c fn f a j ins hM hi ⟨x, o, he⟩ _
  subst he
  obtain ⟨b, hC⟩ := ctx_of hl hsel hwf hM hi
  obtain ⟨d, hsi, -⟩ := hC.instr
  obtain ⟨hxk, rfl, rfl⟩ := hE.sel_read _ _ _ _ _ _ _ _ hsi
  obtain ⟨hx, ho, -⟩ := hC.wf
  have hok := hC.sel.ok
  have hblk := hC.blk
  have hcode := hC.code
  have hroom := hM.room; unfold frameW at hroom
  have hk : j + x - C.c < N := by omega
  obtain ⟨t1, h1, hm1, hw1, hsp1, hOk1, hv1, hk1⟩ := hO.run_ld (ω := ω) hM hok
    (hE.ld_arg 0 (by omega)) (ho o (by simp)) rfl rfl hM.halted (hO.ok_match hM)
    ((Keeps.refl _).op _)
  obtain ⟨mz, hwz, hRz, hFz, -, hrestz⟩ := writeWord_wa hM.region hk 0
  have hzb := writeWord_wa_bytes hM.region hk hwz
  obtain ⟨t2, h2, hm2, hw2, hsp2, hOk2, hn2, ha1, ha2, ha0, hk2⟩ := hE.run_rdPre (ω := ω) hM hok hxk hx hm1
    hsp1 (hw1 ▸ hM.halted) hOk1 hwz
  let cl : Call := ⟨"read", [o.eval s.frame], [], [1]⟩
  obtain ⟨mb, hwb⟩ := write_some ((fitOut [1] (s.world.ask ω cl false).1.bytesOut).headD []) mz
    (wa lo (j + x - C.c)) (fun i hi => by
      have := fitOut_one_le 1 (s.world.ask ω cl false).1.bytesOut
      rw [show i = 0 by omega, wa_add, Nat.add_assoc]
      exact (hRz.rw (8 * (j + x - C.c) + 0) (by omega)).2)
  obtain ⟨hRb, hFb, hwordb, hrestb, hlowb⟩ := byte_word hRz hk hzb (fitOut_one_le 1 _) hwb
  obtain ⟨t3, h3, hm3, hw3, hv3, hOk3, hsp3, hk3⟩ := hE.trap_read (ω := ω) (m' := mb) hOk2
    (by rw [hw2, hw1]; exact hM.halted) hn2
    (by rw [hm2, ha1, ha2, ha0, hv1, hw2, hw1, hM.world]; exact hwb)
  rw [ha2, ha0, hv1, hw2, hw1, hM.world, UInt64.toNat_one] at hw3 hv3
  obtain ⟨t4, h4, hm4, hw4, hsp4, hOk4, hv4, hk4⟩ := hE.run_rdFix (ω := ω) (x := x) hM hok hxk hx
    (hm3 ▸ hRb) (by rw [hsp3, hsp2, hsp1])
    (by rw [hw3, World.ask_snd]; simp [World.call, hM.run]) hOk3
  have htm : t4.mem = mb := hm4.trans hm3
  rw [hE.cnt_read]
  refine sim_ext hO hl hil hM hok hblk hi hx hclob hE.st_rd
    (pre := O.ld (O.argR 0) o ++ O.rdPre x ++ [O.trap] ++ O.rdFix x)
    (v := (s.world.call ω cl false).1) (h' := s.mem) (w' := (s.world.call ω cl false).2)
    (by rw [hO.resolveAt_op]) hcode
    (List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨hO.straight_ld ω _ o (hE.ld_arg 0 (by omega)), hE.straight_rdPre ω x⟩,
      by simpa using hE.straight_trap ω⟩, hE.straight_rdFix ω x⟩) (by simp; omega)
    (by rw [runIs_append, runIs_append, runIs_append, h1, Option.bind_some, h2, Option.bind_some,
      h3, Option.bind_some, h4])
    (htm ▸ hRb) (fun k hk' hne => by rw [htm, hrestb k hk' (hne hxk), hrestz k hk' (hne hxk)])
    (hE.keep_kill ((KeepsExc.of_one (by simp [sysRegs]) hk1).trans (hk2.trans (hk3.trans hk4))))
    (by simp [Flat.extRun, Flat.extOutArg, Flat.extWords, Flat.extBytes, Flat.extCaps, cl])
    (htm ▸ dataOk_keep (by have := hRz.top; omega) hM.data (hFz.trans hFb)
      ((writeWord_wa_low hM.region hk hwz).trans hlowb))
    (by rw [hsp4, hsp3, hsp2, hsp1]) hOk4 (by rw [hw4, hw3, World.ask_snd])
    (by simp [World.call, hM.run])
    (by rw [hv4, hv3, hm3, hwordb, World.call_fst _ _ _ hM.run]; simp [Call.value, cl]) c rfl


end Ops

end Millipede.Sel
