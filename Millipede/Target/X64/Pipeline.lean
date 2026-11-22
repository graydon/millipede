import Millipede.Top.Compile
import Millipede.Compile.LowerStack
import Millipede.Compile.LinearizeLower
import Millipede.Target.X64.SelectCall
import Millipede.Target.SelInit

/-!
# The pipeline on x64 Linux

This module follows a lowered program through the x64 backend, which linearizes it with the
data region `[0, memBytes)`, selects instructions, checks the budget, assembles and links, and
proves the result correct on the x64 machine model. `init_of_link` shows that the initial state
of a linked image is a correct start for the simulation of `select`: the code is loaded in W^X
memory, the stack region is in place with `main`'s frame zero, the data region is readable,
writable, zero and below the stack, and the location registers are zero.

From any such start, `select_lower_sound` gives the source program's trace, progress and the
stack bound on the machine, and `select_lower_cost` bounds the machine instructions of each
reactor step when the selected code passes the budget check that `compile` runs. Both are the
shared theorems at x64's package `pkg`.
-/

namespace Millipede.X64

open Sel (wa)

set_option allowUnsafeReducibility true in
attribute [local reducible] isa

/-! ## The initial state of the image -/

/-- The initial state of a linked image satisfies `Init` for the Lin program, the Asm program
and the linker's symbol map, with the stack region formed by the image's stack pages. -/
theorem init_of_link {k c : Nat} {mb : Bool} {P : Lin.Prog} {A : Asm.Prog arch} {obj : Obj} {img : Image}
    (hs : select k c P mb = .ok A) (ha : assemble A = .ok obj)
    (hk : Link.link (Compile.linkConfigW k c P) [obj] = .ok img) :
    ∃ σ lo N, Init k c P A σ lo N (img.init linux) := by
  have st := Sel.link_start asmLaws ha hk linux rfl rfl (show 3 ≤ 12 by decide)
    (show (0x7ffffffff000 : UInt64).toNat ≤ 2 ^ 47 by decide)
  obtain ⟨hmain, hml, _, hfk⟩ := Sel.select_spec (select_ok hs)
  refine ⟨_, _, _, ⟨st.world, st.wx, st.loaded, st.region, ?_, ?_, fun fn hfn x hx => ?_,
    st.size, st.bss, st.below, fun r hr => ?_⟩⟩
  · -- `rip` at `main`'s symbol
    obtain ⟨fn, hfn⟩ : ∃ fn, P.funs[P.main]? = some fn := ⟨_, List.getElem?_eq_getElem hml⟩
    obtain ⟨f, hf, hsf⟩ := hfk P.main fn hfn
    exact ⟨f, hf, st.entry f (List.mem_of_getElem? hf) hsf.name⟩
  · -- stack pointer at the top
    exact st.top.symm
  · -- `main`'s frame is zero
    have hroom : Sel.frameW k c fn.frame + 1 ≤ Sel.stackWords (Compile.linkConfigW k c P) := by
      have h1 := Lin.frameBytes_le (φ.words k c) P P.main
      rw [frameBytes_eq hfn] at h1
      have h2 : P.stackBytes (φ.words k c) = (Lin.needs (φ.words k c) P.funs).getD P.main 0 := rfl
      have h3 : (Compile.linkConfigW k c P).stackSize = P.stackBytes (φ.words k c) := rfl
      have := st.size
      omega
    rw [load_wa st.region (by omega), st.zero _ (by omega)]
  · -- every register but `rsp` is zero
    simp only [Image.init, linux, Abi.linux]
    exact ite_eq_right_iff.2 fun h => absurd h hr

/-! ## Soundness -/

/-- From any `Init` state, the x64 machine running the selected code of a lowered program never
gets stuck, produces the source program's events and keeps the stack bound. `P'` is any lock-step
refinement `L` of the linearized program by the Lin passes before selection, whose stack bound is
no larger in the frame words of `(k, c)`. -/
theorem select_lower_sound {k c : Nat} {mb : Bool} (hk : KC k c) (p : Program) (fp : Flat.Prog)
    (hl : Flat.lower p = .ok fp) (hH : Flat.MemHyp p) {P' : Lin.Prog}
    (L : RegAlloc.Lock (Lin.linearize fp p.memBytes) P' k c) {A : Asm.Prog arch}
    (hsel : select k c P' mb = .ok A)
    {σ : String → Option UInt64} {lo N : Nat} {m₀ : State}
    (hI : Init k c P' A σ lo N m₀) (ω : Oracle) :
    M.NeverStuck ω (m₀, 0) ∧ TraceEq (M.traceAt ω (m₀, 0)) (p.events ω) ∧
      ∀ n t, M.run ω (m₀, 0) n = some t →
        (wa lo N - t.1.regs.gpr .rsp).toNat ≤ (Lin.linearize fp p.memBytes).stackBytes φ := by
  obtain ⟨h1, h2, h3⟩ := Sel.select_lower_sound (S' := pkg k c mb _ A σ lo N) κ laws hl hH L
    (pkg_laws hk hsel (L.wf (Lin.lower_linearize_wf hl p.memBytes)) hI.bound) hI ω
  exact ⟨h1, h2, fun n t h => Nat.le_trans (h3 n t h) (L.stackBytes φ)⟩

/-- A bound on the x64 instructions of each reactor step. Take a program that is lowered,
linearized with its data region, refined in lock-step by `P'` and selected, and whose selected
code passes the budget check. From any `Init` state and for every oracle, there are monotone
machine times `marks k` with `marks 0 = 0`, at which the machine's trace is the source trace
after reactor step `k`, and at most `p.stepCost k ω κ` machine instructions run between
`marks k` and `marks (k + 1)`. -/
theorem select_lower_cost {k c : Nat} {mb : Bool} (hk : KC k c) {κ : CostModel} (p : Program) (fp : Flat.Prog)
    (hl : Flat.lower p = .ok fp) (hH : Flat.MemHyp p) {P' : Lin.Prog}
    {kL cL : Nat} (L : RegAlloc.Lock (Lin.linearize fp p.memBytes) P' kL cL) {A : Asm.Prog arch}
    (hsel : select k c P' mb = .ok A) {C : Cert} (hb : Sel.budgetOk (counts k c mb (RegAlloc.Live.of P')) κ P' C = true)
    {σ : String → Option UInt64} {lo N : Nat} {m₀ : State}
    (hI : Init k c P' A σ lo N m₀) (ω : Oracle) :
    ∃ marks : Nat → Nat, marks 0 = 0 ∧ ∀ k, marks k ≤ marks (k + 1) ∧
      M.traceAt ω (m₀, 0) (marks (k + 1)) = p.events ω k ∧
      M.clockAt ω (m₀, 0) (marks (k + 1)) - M.clockAt ω (m₀, 0) (marks k) ≤
        p.stepCost k ω κ :=
  Sel.select_lower_cost (S' := pkg k c mb _ A σ lo N) hl hH L
    (pkg_laws hk hsel (L.wf (Lin.lower_linearize_wf hl p.memBytes)) hI.bound) hb hI ω

end Millipede.X64
