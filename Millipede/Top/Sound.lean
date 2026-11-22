import Millipede.Target.X64.Pipeline
import Millipede.Compile.LowerOf
import Millipede.RegAlloc.Sound

/-!
# Soundness of the compiler

`compile_sound` says that for every program that `compile` compiles for `x64Linux` and that is
`Safe`, the bytes load, and for every oracle the machine never gets stuck, has exactly the
source's event trace, keeps its stack within `p.stackBytes X64.φ`, and executes at most
`p.stepCost k ω X64.κ` instructions in reactor step `k`. It has no hypotheses.

The theorem is proved once for every lawful backend by `compile_sound_of_backend`, which composes
the passes that all backends share. These are the Core passes, the checks, the memory refinement
of every term the lowering accepts, and the stack bound of linearization. A backend proves its
`Backend.Laws`, which are the round trip of its loader and the simulation, loader start and
instruction budget of its selected code. `compile_sound` is the instance for x64, and
`compile_sound_arm64` in `Top/SoundA64.lean` is the instance for arm64.

The design is described in doc/design/trust.md.
-/

namespace Millipede

/-- The building blocks of a program, which are its lenses, constructors and splits, agree with
the layouts. -/
def Program.Lawful (p : Program) : Prop := p.init.Lawful ∧ p.step.Lawful

/-- What a backend proves. `load_write` says that the target's loader model maps the bytes its
writer produced to the image's initial state. `run` says that for an image the backend produced
from a lowered program `p` that meets the hypotheses of the memory refinement, the machine from
the image's initial state never gets stuck, has the source trace, keeps its stack within the Lin
bound, and runs each reactor step within `p.stepCost k ω κ`. -/
structure Backend.Laws (B : Backend) : Prop where
  load_write : ∀ img bs, B.target.fmt.write img = .ok bs →
    B.target.fmt.load bs = some (img.init B.target.abi)
  run : ∀ {p : Program} {fp : Flat.Prog} {A : Asm.Prog B.arch} {obj : Obj} {img : Image},
    Flat.lower p = .ok fp → Flat.MemHyp p →
    B.select (B.prep (Lin.linearize fp p.memBytes)) = .ok A →
    B.budgetOk (B.prep (Lin.linearize fp p.memBytes)) = true →
    B.assemble A = .ok obj →
    Link.link (B.linkConfig (B.prep (Lin.linearize fp p.memBytes))) [obj] = .ok img →
    ∀ ω : Oracle, let m := Machine.run B.target (img.init B.target.abi) ω
      m.NeverStuck ∧ TraceEq m.trace (p.events ω) ∧
      m.StackWithin ((Lin.linearize fp p.memBytes).stackBytes B.target.φ) ∧
      m.StepsWithin (p.events ω) (fun k => p.stepCost k ω B.target.κ)

namespace Compile

/-- What a successful pipeline of backend `B` did, pass by pass. -/
theorem bytesOf_spec {B : Backend} {p : Program} {bs : List UInt8} (h : bytesOf B p = .ok bs) :
    ∃ fp A obj img, checks p = true ∧ Flat.lower p = .ok fp ∧
      B.select (B.prep (Lin.linearize fp p.memBytes)) = .ok A ∧
      B.budgetOk (B.prep (Lin.linearize fp p.memBytes)) = true ∧
      B.assemble A = .ok obj ∧
      Link.link (B.linkConfig (B.prep (Lin.linearize fp p.memBytes))) [obj] = .ok img ∧
      B.target.fmt.write img = .ok bs := by
  unfold bytesOf at h
  cases hm : checks p with
  | false => simp [hm] at h; cases h
  | true =>
    simp only [hm, Bool.true_eq_false, ↓reduceIte] at h
    obtain ⟨fp, hl, h⟩ := Link.bind_ok h
    obtain ⟨img, hb, hw⟩ := Link.bind_ok h
    unfold backendOf at hb
    obtain ⟨A, hA, hb⟩ := Link.bind_ok hb
    cases hbud : B.budgetOk (B.prep (Lin.linearize fp p.memBytes)) with
    | false => simp [hbud] at hb; cases hb
    | true =>
      simp only [hbud, Bool.true_eq_false, ↓reduceIte] at hb
      obtain ⟨obj, ho, hk⟩ := Link.bind_ok hb
      exact ⟨fp, A, obj, img, rfl, hl, hA, hbud, ho, hk, hw⟩

theorem firstOk_spec {B : Backend} {κ : CostModel} {φ : FrameModel} {p : Program}
    {bs : List UInt8} {c : Opt.Config} :
    ∀ {cs : List Opt.Config} {e : String}, firstOk B κ φ p cs (.error e) = .ok (bs, c) →
      bytesOf B (c.optimize κ φ p) = .ok bs
  | [], _, h => by cases h
  | c' :: cs, _, h => by
    unfold firstOk at h; split at h
    · rename_i hq; cases h; exact hq
    · exact firstOk_spec h

/-- What a successful `compileWith o` did, which is the pipeline of the backend registered for `t`
under `o`, run either on the source or on the result of the Core passes. -/
theorem compile_spec {o : Options} {p : Program} {t : Target} {b : ByteArray}
    (h : compileWith o p t = .ok b) :
    ∃ B, Backend.of? t o = some B ∧ checks p = true ∧ ∃ q, q.Sim t.κ t.φ p ∧
      bytesOf B q = .ok b.data.toList := by
  unfold compileWith compileRun at h
  split at h
  · rename_i B hB
    refine ⟨B, hB, ?_⟩
    split at h
    · cases hb : bytesOf B p with
      | error e => rw [hb] at h; cases h
      | ok bs =>
        rw [hb] at h; cases h
        obtain ⟨-, -, -, -, hm, -⟩ := bytesOf_spec hb
        exact ⟨hm, p, Opt.Sim.refl p, by rw [hb]⟩
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or] at hc
      split at h
      · rename_i bs hq
        cases h; exact ⟨by simpa using hc.2, _, o.opt.optimize_sim t.κ t.φ p, hq⟩
      · split at h
        · rename_i e _ _
          cases hf : firstOk B t.κ t.φ p o.opt.prefixes (.error e) with
          | error => rw [hf] at h; cases h
          | ok r =>
            obtain ⟨bs, c⟩ := r
            rw [hf] at h; cases h
            exact ⟨by simpa using hc.2, _, c.optimize_sim t.κ t.φ p, firstOk_spec hf⟩
        · cases h
  · cases h

end Compile

/-- `compile` refuses every program that the borrow checker rejects. -/
theorem compile_wf {o : Compile.Options} {p : Program} {t : Target} {b : ByteArray}
    (hc : compileWith o p t = .ok b) : p.wf = true := by
  obtain ⟨B, -, hm, -⟩ := Compile.compile_spec hc
  simp only [Compile.checks, Bool.and_eq_true] at hm
  exact hm.2

/-- Every program that passes the checks before lowering is lawful, because the checks require
every building block to carry a certificate of its law, and a certified term is lawful. -/
theorem checks_lawful {p : Program} (hm : Compile.checks p = true) : p.Lawful := by
  simp only [Compile.checks, Bool.and_eq_true] at hm
  exact ⟨p.init.lawful_of_certified hm.1.1, p.step.lawful_of_certified hm.1.2⟩

/-- Every program that `compile` accepts is lawful. -/
theorem compile_lawful {o : Compile.Options} {p : Program} {t : Target} {b : ByteArray}
    (hc : compileWith o p t = .ok b) : p.Lawful := by
  obtain ⟨B, -, hm, -⟩ := Compile.compile_spec hc
  exact checks_lawful hm

/-- A stack bound holds for every larger bound. -/
theorem Machine.Exec.StackWithin.mono {t : Target} {m : Machine.Exec t} {a b : Nat} (h : m.StackWithin a)
    (hab : a ≤ b) : m.StackWithin b := fun n s hs => Nat.le_trans (h n s hs) hab

/-- A step bound holds for every larger bound. -/
theorem Machine.Exec.StepsWithin.mono {t : Target} {m : Machine.Exec t} {ev : Nat → List Event}
    {a b : Nat → Nat} (h : m.StepsWithin ev a) (hab : ∀ k, a k ≤ b k) : m.StepsWithin ev b := by
  obtain ⟨marks, h0, h⟩ := h
  exact ⟨marks, h0, fun k => ⟨(h k).1, (h k).2.1, Nat.le_trans (h k).2.2 (hab k)⟩⟩

/-- `compile_sound` for every lawful backend. If `B` is the backend registered for its target
under options `o`, then `CompileSound.Statement (compileWith o) B.target` holds, for every
configuration of the Core passes and of register allocation, with or without the fallback. -/
theorem compileWith_sound_of_backend (o : Compile.Options) (B : Backend) (hB : B.Laws)
    (hreg : Backend.of? B.target o = some B) : CompileSound.Statement (compileWith o) B.target := by
  intro p b hc hs
  obtain ⟨B', hB', -, q, hq, h⟩ := Compile.compile_spec hc
  rw [hreg] at hB'; cases hB'
  obtain ⟨fp, A, obj, img, hm, hl, hA, hbud, ho, hk, hw⟩ := Compile.bytesOf_spec h
  have hL := checks_lawful hm
  simp only [Compile.checks, Bool.and_eq_true] at hm
  have hH : Flat.MemHyp q := Flat.MemHyp.of_checks hl hm.2 hL (Opt.Sim.safe hq hs)
  have hst := Lin.lower_linearize_stackBytes_le B.target.φ hl q.memBytes
  refine ⟨_, hB.load_write img _ hw, fun ω => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hB.run hl hH hA hbud ho hk ω
  refine ⟨h1, Opt.Sim.events hq ω ▸ h2,
    Machine.Exec.StackWithin.mono h3 (Nat.le_trans hst (Opt.Sim.stackBytes_le hq)), ?_⟩
  rw [← Opt.Sim.events hq ω]
  exact h4.mono fun k => Opt.Sim.stepCost_le hq k ω

/-- `compile_sound_of_backend` at the default options. -/
theorem compile_sound_of_backend (B : Backend) (hB : B.Laws) (hreg : Backend.of? B.target = some B) :
    CompileSound.Statement compile B.target :=
  compileWith_sound_of_backend {} B hB hreg

/-- The Lin pass of the options is a lock-step refinement, since it is either a checked
allocation or the identity, whose stack bound is no larger in the frame words of the selection
`kcU` chooses for its result. This needs that the selection is at `(cl.k, cl.c)` whenever `ok`
accepts, and that `cl0` has no caller-saved locations: its frames, checked in locations, fit
every selection. -/
def Compile.prepA_lock (o : Compile.Options) (cl cl0 : RegAlloc.Alloc.Classes) (ok : Lin.Prog → Bool)
    (kcU : Lin.Prog → Nat × Nat) (hkc : ∀ Q, ok Q = true → kcU Q = (cl.k, cl.c)) (h0 : cl0.c = 0)
    (P : Lin.Prog) :
    RegAlloc.Lock P (Compile.prepA o cl cl0 ok P) (kcU (Compile.prepA o cl cl0 ok P)).1
      (kcU (Compile.prepA o cl cl0 ok P)).2 := by
  have any : ∀ (cl' : RegAlloc.Alloc.Classes), cl'.c = 0 → ∀ k c,
      RegAlloc.Lock P (RegAlloc.Alloc.allocOrId cl' P) k c := fun cl' h k c =>
    RegAlloc.Lock.weaken (k := cl'.k) (c := cl'.c) (RegAlloc.allocOrId_lock cl' P)
      (k' := k) (c' := c) fun F => by
        have h1 := Sel.frameW_le k c F
        have h2 : Sel.frameW cl'.k cl'.c F = F := by rw [h]; exact Sel.frameW_zero _ _
        omega
  unfold Compile.prepA
  split
  · dsimp only
    split
    · rename_i h
      by_cases hok : ok (RegAlloc.Alloc.allocOrId { cl with callerFirst := o.callerFirst } P) = true
      · rw [hkc _ hok]; exact RegAlloc.allocOrId_lock _ P
      · simp only [hok, Bool.or_false, beq_iff_eq] at h
        exact any { cl with callerFirst := o.callerFirst } h _ _
    · exact any { cl0 with callerFirst := o.callerFirst } h0 _ _
  · exact RegAlloc.Lock.id P _ _

/-- The Lin passes of the options are a lock-step refinement: `prepA_lock`, preceded by the
identity operations as moves (`RegAlloc.Lock.pre`) when `o.idOps`. -/
def Compile.prep_lock (o : Compile.Options) (cl cl0 : RegAlloc.Alloc.Classes) (ok : Lin.Prog → Bool)
    (kcU : Lin.Prog → Nat × Nat) (hkc : ∀ Q, ok Q = true → kcU Q = (cl.k, cl.c)) (h0 : cl0.c = 0)
    (P : Lin.Prog) :
    RegAlloc.Lock P (Compile.prep o cl cl0 ok P) (kcU (Compile.prep o cl cl0 ok P)).1
      (kcU (Compile.prep o cl cl0 ok P)).2 := by
  unfold Compile.prep
  split
  · exact RegAlloc.Lock.pre (Compile.prepA_lock o cl cl0 ok kcU hkc h0 _)
  · exact Compile.prepA_lock o cl cl0 ok kcU hkc h0 P

/-- The Lin pass of the x64 backend, as a lock-step refinement at the register locations the
selection uses. -/
def Compile.x64Prep_lock (o : Compile.Options) (P : Lin.Prog) :
    RegAlloc.Lock P (Compile.x64Prep o P)
      (X64.kcUsed (Compile.x64K o) (Compile.x64C o) (Compile.x64Prep o P) o.memBase).1
      (X64.kcUsed (Compile.x64K o) (Compile.x64C o) (Compile.x64Prep o P) o.memBase).2 :=
  Compile.prep_lock o _ _ _ _ (fun _ h => X64.kcUsed_of_ok h) rfl P

/-- The x64 backend's laws, for every setting of the options. They are the ELF round trip, the
loader's start, in which the location registers are zero, and the simulation and cost of the
selected code at the register locations actually used, composed with the allocation's lock-step
refinement. -/
theorem x64Backend_laws (o : Compile.Options) : (x64Backend o).Laws where
  load_write img bs hw := (Elf.x64Linux_laws X64.linux).load_write img bs hw
  run {p fp A obj img} hl hH hA hbud ho hk ω := by
    let L := Compile.x64Prep_lock o (Lin.linearize fp p.memBytes)
    have hkc : X64.KC (X64.kcUsed (Compile.x64K o) (Compile.x64C o)
        (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase).1
        (X64.kcUsed (Compile.x64K o) (Compile.x64C o)
        (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase).2 := by
      obtain ⟨h1, h2⟩ := X64.kcUsed_le (Compile.x64K o) (Compile.x64C o)
        (Compile.x64Prep o (Lin.linearize fp p.memBytes)) o.memBase
      have e1 : Compile.x64K o ≤ X64.maxK := by unfold Compile.x64K; split <;> omega
      have e2 : Compile.x64C o ≤ X64.maxC := by unfold Compile.x64C; split <;> omega
      exact ⟨Nat.le_trans h1 e1, Nat.le_trans h2 e2⟩
    obtain ⟨σ, lo, N, hI⟩ := X64.init_of_link hA ho hk
    obtain ⟨h1, h2, h3⟩ := X64.select_lower_sound hkc p fp hl hH L hA hI ω
    refine ⟨h1, h2, ?_, X64.select_lower_cost hkc p fp hl hH L hA hbud hI ω⟩
    intro n s hn
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hn
    show ((img.init X64.linux).regs.gpr .rsp - t.1.regs.gpr .rsp).toNat ≤ _
    rw [hI.sp]
    exact h3 n t ht

/-- The compiler is sound for x64 Linux, with no hypotheses. For every program that compiles for
`x64Linux` and is `Safe`, the bytes load, and for every oracle the machine never gets stuck, has
exactly the source's event trace, keeps its stack within `p.stackBytes X64.φ`, and executes at
most `p.stepCost k ω X64.κ` instructions in reactor step `k`. -/
theorem compile_sound : CompileSound.Statement compile x64Linux :=
  compile_sound_of_backend x64Backend (x64Backend_laws {}) rfl

end Millipede
