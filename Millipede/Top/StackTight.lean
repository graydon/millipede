import Millipede.Top.SoundA64

/-!
# The stack the image asks for

`compile_sound` bounds the machine's stack by `p.stackBytes t.φ`, which is computed from the
source and charges every frame its Core size. The compiler computes a second bound after register
allocation, the Lin program's `stackBytes`, and writes it into the image as the stack size it asks
the kernel for. `compile_stack_tight` says that the machine's stack stays within that size, and that
the size is at most the source bound.

`CompileStack.Statement compile t` states this for a compiler and a target: for a program that
compiled to the bytes `b` and is `Safe`, there is an image `img` whose initial state the loader
model produces from `b`, whose stack size is at most `p.stackBytes t.φ`, and from whose initial
state the machine keeps its stack within `img.stackSize` bytes for every oracle.

The proof uses the same pieces as `compile_sound`: the selection simulation bounds the stack by
the bound of the selected Lin program, which the linker records as the image's stack size, and the
lock-step allocation, linearization and the Core passes do not raise it.
-/

namespace Millipede

/-- The statement of `compile_stack_tight` for a compiler `compile` and a target `t`. -/
def CompileStack.Statement (compile : Program → Target → Except String ByteArray)
    (t : Target) : Prop :=
  ∀ (p : Program) (b : ByteArray), compile p t = .ok b → p.Safe →
    ∃ img : Image, t.fmt.load b.data.toList = some (img.init t.abi) ∧
      img.stackSize ≤ p.stackBytes t.φ ∧
      ∀ ω : Oracle, (Machine.run t (img.init t.abi) ω).StackWithin img.stackSize

/-- What a backend proves about the stack of its image: the image's stack size is at most the
bound of the linearized program, and the machine stays within it. -/
def Backend.StackLaw (B : Backend) : Prop :=
  ∀ {p : Program} {fp : Flat.Prog} {A : Asm.Prog B.arch} {obj : Obj} {img : Image},
    Flat.lower p = .ok fp → Flat.MemHyp p →
    B.select (B.prep (Lin.linearize fp p.memBytes)) = .ok A →
    B.assemble A = .ok obj →
    Link.link (B.linkConfig (B.prep (Lin.linearize fp p.memBytes))) [obj] = .ok img →
    img.stackSize ≤ (Lin.linearize fp p.memBytes).stackBytes B.target.φ ∧
      ∀ ω : Oracle, (Machine.run B.target (img.init B.target.abi) ω).StackWithin img.stackSize

/-- `CompileStack.Statement` for every backend with its laws and its stack law. -/
theorem compileWith_stack_of_backend (o : Compile.Options) (B : Backend) (hB : B.Laws)
    (hS : B.StackLaw) (hreg : Backend.of? B.target o = some B) :
    CompileStack.Statement (compileWith o) B.target := by
  intro p b hc hs
  obtain ⟨B', hB', -, q, hq, h⟩ := Compile.compile_spec hc
  rw [hreg] at hB'; cases hB'
  obtain ⟨fp, A, obj, img, hm, hl, hA, -, ho, hk, hw⟩ := Compile.bytesOf_spec h
  have hL := checks_lawful hm
  simp only [Compile.checks, Bool.and_eq_true] at hm
  have hH : Flat.MemHyp q := Flat.MemHyp.of_checks hl hm.2 hL (Opt.Sim.safe hq hs)
  obtain ⟨hsz, hrun⟩ := hS hl hH hA ho hk
  exact ⟨img, hB.load_write img _ hw, Nat.le_trans hsz (Nat.le_trans
    (Lin.lower_linearize_stackBytes_le B.target.φ hl q.memBytes) (Opt.Sim.stackBytes_le hq)), hrun⟩

/-- The x64 backend's stack law. -/
theorem x64Backend_stackLaw (o : Compile.Options) : (x64Backend o).StackLaw := by
  intro p fp A obj img hl hH hA ho hk
  let L := Compile.x64Prep_lock o (Lin.linearize fp p.memBytes)
  have hkc : X64.KC (X64.kcUsed (Compile.x64K o) (Compile.x64C o)
      (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase).1
      (X64.kcUsed (Compile.x64K o) (Compile.x64C o) (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase).2 := by
    obtain ⟨h1, h2⟩ := X64.kcUsed_le (Compile.x64K o) (Compile.x64C o)
      (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase
    have e1 : Compile.x64K o ≤ X64.maxK := by unfold Compile.x64K; split <;> omega
    have e2 : Compile.x64C o ≤ X64.maxC := by unfold Compile.x64C; split <;> omega
    exact ⟨Nat.le_trans h1 e1, Nat.le_trans h2 e2⟩
  obtain ⟨σ, lo, N, hI⟩ := X64.init_of_link hA ho hk
  have hsz : img.stackSize = (Compile.x64Prep o (Lin.linearize fp p.memBytes)).stackBytes
      (X64.φ.words _ _) := Sel.link_stackSize hk
  refine ⟨hsz ▸ L.stackBytes _, fun ω => ?_⟩
  obtain ⟨-, -, h3⟩ := Sel.select_lower_sound (S' := X64.pkg _ _ o.memBase _ A σ lo N) X64.κ X64.laws hl hH L
    (X64.pkg_laws hkc hA (L.wf (Lin.lower_linearize_wf hl p.memBytes)) hI.bound) hI ω
  intro n s hn
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hn
  show ((img.init X64.linux).regs.gpr .rsp - t.1.regs.gpr .rsp).toNat ≤ _
  rw [hI.sp, hsz]
  exact h3 n t ht

open RegAlloc.A64Reg in
/-- The arm64 backend's stack law. -/
theorem a64Backend_stackLaw (o : Compile.Options) : (a64Backend o).StackLaw := by
  intro p fp A obj img hl hH hA ho hlk
  let L := Compile.a64Prep_lock o (Lin.linearize fp p.memBytes)
  let kc := kcUsed (Compile.a64K o) (Compile.a64C o) (Compile.a64Prep o (Lin.linearize fp p.memBytes)) o.memBase
  have hk : kc.1 ≤ 10 ∧ kc.2 ≤ 14 := by
    obtain ⟨h1, h2⟩ := kcUsed_le (Compile.a64K o) (Compile.a64C o)
      (Compile.a64Prep o (Lin.linearize fp p.memBytes)) o.memBase
    have e1 : Compile.a64K o ≤ 10 := by unfold Compile.a64K; split <;> omega
    have e2 : Compile.a64C o ≤ 14 := by unfold Compile.a64C; split <;> omega
    exact ⟨Nat.le_trans h1 e1, Nat.le_trans h2 e2⟩
  have hA' := select_ok (k := kc.1) (c := kc.2) (mb := o.memBase) hA
  obtain ⟨σ, lo, N, hI⟩ := A64.init_of_link hA' ho hlk
  have hwf := L.wf (Lin.lower_linearize_wf hl p.memBytes)
  have hI' : Init kc.1 kc.2 _ A σ lo N (img.init A64.linux) := ⟨hI, fun x hx => init_zero img hk hx⟩
  have hlaws : (pkg kc.1 kc.2 o.memBase _ A σ lo N).Laws :=
    Sel.pkg_laws A64.asm_laws hA' hwf (cases hk hA hwf hI.bound) (fun _ h => h.1.world)
      (fun _ h => by
        show (Sel.wa lo N - (_ : A64.State).regs.x 31).toNat ≤ _; rw [h.1.sp]; simp)
      (by simp only [counts, A64.entryLen, A64.entryIs, List.length_cons]; omega) (entry_ok kc.1 kc.2 o.memBase hk _ A σ lo N hA hI.bound)
  have hsz : img.stackSize = (Compile.a64Prep o (Lin.linearize fp p.memBytes)).stackBytes
      (A64.φ.words kc.1 kc.2) := Sel.link_stackSize hlk
  refine ⟨hsz ▸ L.stackBytes _, fun ω => ?_⟩
  obtain ⟨-, -, h3⟩ := Sel.select_lower_sound (S' := pkg kc.1 kc.2 o.memBase _ A σ lo N) A64.κ A64.laws hl hH
    L hlaws hI' ω
  intro n s hn
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hn
  show ((img.init A64.linux).regs.x 31 - t.1.regs.x 31).toNat ≤ _
  rw [hI.sp, hsz]
  exact h3 n t ht

/-- The machine's stack stays within the stack size that the compiled image asks for, which is at
most the source bound `p.stackBytes X64.φ`, for x64 Linux, with no hypotheses. -/
theorem compile_stack_tight : CompileStack.Statement compile x64Linux :=
  compileWith_stack_of_backend {} x64Backend (x64Backend_laws {}) (x64Backend_stackLaw {}) rfl

/-- `compile_stack_tight` for arm64 Linux. -/
theorem compile_stack_tight_arm64 : CompileStack.Statement compile arm64Linux :=
  compileWith_stack_of_backend {} a64Backend (a64Backend_laws {}) (a64Backend_stackLaw {}) rfl

end Millipede
