import Millipede.RegAlloc.Lock

/-!
# Identity operations as moves

The lowering emits operations that leave their left operand unchanged: `bor x, a, 0` for a byte
widened to a word and `mul i, i, 1` for the index of a byte array. `idOps` rewrites every
`bin op x a (imm w)` whose immediate is a right identity of `op` (`BinOp.rightId`) to `mov x a`.
A move of a location to itself selects to no code, so `bor x, x, 0` and `mul i, i, 1` disappear,
and any other identity operation becomes a copy.

The rewritten instruction executes exactly as the original (`exec_idOp`), and the pass changes no
frame, call, return operand or jump, so the program steps exactly as the original from every
state (`step_idOps`), its stack bound is the same under every frame model (`stackBytes_idOps`),
and it is a lock-step refinement whose relation is equality. `Lock.pre` puts it in front of any
other lock-step refinement, which is how `Compile.prep` runs it before the allocation.
-/

namespace Millipede.RegAlloc

open Lin (Prog Instr)
open Flat (BinOp Operand)

/-- `w` is a right identity of `op`: `op.eval a w = a` for every `a` (`BinOp.eval_rightId`). -/
def _root_.Millipede.Flat.BinOp.rightId : BinOp → UInt64 → Bool
  | .add, w | .sub, w | .bor, w | .bxor, w | .shl, w | .shr, w => w == 0
  | .mul, w | .udiv, w => w == 1
  | _, _ => false

theorem _root_.Millipede.Flat.BinOp.eval_rightId {op : BinOp} {w : UInt64} (h : op.rightId w = true)
    (a : UInt64) : op.eval a w = a := by
  cases op <;> simp only [BinOp.rightId, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [BinOp.eval]

/-- An identity operation as a move; every other instruction unchanged. -/
def idOp : Instr → Instr
  | .bin op x a (.imm w) => if op.rightId w then .mov x a else .bin op x a (.imm w)
  | i => i

/-- The function with its identity operations as moves. -/
def idOpsFn (fn : Lin.Fn) : Lin.Fn := { fn with code := fn.code.map idOp }

/-- The program with its identity operations as moves. -/
def idOps (P : Prog) : Prog := { P with funs := P.funs.map idOpsFn }

theorem exec_idOp (κ : CostModel) (ω : Oracle) (fn : Lin.Fn) (i : Instr) (s : Lin.State) :
    Lin.exec κ ω (idOpsFn fn) (idOp i) s = Lin.exec κ ω fn i s := by
  unfold idOp
  split
  · rename_i op x a w
    split
    · rename_i h
      simp only [Lin.exec, Operand.eval, BinOp.eval_rightId h]
    · rfl
  · cases i <;> rfl

theorem memOk_idOp (M : Nat) (fr : Flat.Frame) (i : Instr) : (idOp i).memOk M fr = i.memOk M fr := by
  unfold idOp; split
  · split <;> rfl
  · rfl

/-- The rewritten program steps exactly as the original from every state. -/
theorem step_idOps (κ : CostModel) (P : Prog) (ω : Oracle) (s : Lin.State) :
    Lin.step κ (idOps P) ω s = Lin.step κ P ω s := by
  simp only [Lin.step, idOps, List.getElem?_map]
  split
  · rfl
  · cases P.funs[s.fn]? with
    | none => rfl
    | some fn =>
      simp only [Option.map_some, idOpsFn, List.getElem?_map]
      cases fn.code[s.pc]? with
      | none => rfl
      | some i =>
        simp only [Option.map_some, memOk_idOp]
        split
        · exact exec_idOp κ ω fn i s
        · rfl

theorem callMax_idOps (acc : List Nat) : ∀ code : List Instr,
    Lin.callMax acc (code.map idOp) = Lin.callMax acc code
  | [] => rfl
  | i :: is => by
    have ih := callMax_idOps acc is
    cases i with
    | bin op x a b =>
      cases b with
      | imm w =>
        simp only [List.map_cons, idOp]
        split <;> simp only [Lin.callMax, ih]
      | slot => simp only [List.map_cons, idOp, Lin.callMax, ih]
    | _ => simp only [List.map_cons, idOp, Lin.callMax, ih]

theorem needsFrom_idOps (φ : FrameModel) : ∀ (fs : List Lin.Fn) (acc : List Nat),
    Lin.needsFrom φ acc (fs.map idOpsFn) = Lin.needsFrom φ acc fs
  | [], _ => rfl
  | f :: fs, acc => by
    simp only [List.map_cons, Lin.needsFrom, Lin.fnNeed, idOpsFn, callMax_idOps]
    exact needsFrom_idOps φ fs _

/-- The rewritten program's stack bound is the original's, under every frame model. -/
theorem stackBytes_idOps (φ : FrameModel) (P : Prog) :
    (idOps P).stackBytes φ = P.stackBytes φ := by
  simp only [Lin.Prog.stackBytes, Lin.needs, idOps, needsFrom_idOps]

theorem wf_idOp {P : Prog} {i fr len : Nat} {ins : Instr} (h : ins.Wf P i fr len) :
    (idOp ins).Wf (idOps P) i fr len := by
  unfold idOp
  split
  · split
    · exact ⟨h.1, fun y hy => h.2 y (List.mem_cons.2 (Or.inl (List.mem_singleton.1 hy)))⟩
    · exact h
  · cases ins with
    | call g args d =>
      obtain ⟨h1, h2, gf, h3, h4, h5⟩ := h
      exact ⟨h1, h2, idOpsFn gf, by simp [idOps, h3], h4, h5⟩
    | _ => exact h

/-- The rewritten program is well formed when the original is. -/
theorem wf_idOps {P : Prog} (h : P.Wf) : (idOps P).Wf := by
  refine ⟨by simpa [idOps] using h.1, fun i fn hfn => ?_⟩
  simp only [idOps, List.getElem?_map, Option.map_eq_some_iff] at hfn
  obtain ⟨fn₀, h₀, rfl⟩ := hfn
  obtain ⟨hr, hc⟩ := h.2 i fn₀ h₀
  refine ⟨hr, fun ins hins => ?_⟩
  simp only [idOpsFn, List.mem_map] at hins
  obtain ⟨ins₀, hm, rfl⟩ := hins
  simpa [idOpsFn] using wf_idOp (hc ins₀ hm)

/-- A lock-step refinement of `idOps P` is one of `P`: the two programs step alike, start alike,
and have the same stack bound and reactor boundaries. -/
def Lock.pre {P P' : Prog} {k c : Nat} (L : Lock (idOps P) P' k c) : Lock P P' k c where
  R := L.R
  init := L.init
  step {κ ω s t s'} h hs := L.step h (by rw [step_idOps]; exact hs)
  world := L.world
  clock := L.clock
  boundary {s t} h h1 h2 := by
    refine L.boundary h h1 ?_
    obtain ⟨fn, l, hf, hc⟩ := h2
    exact ⟨idOpsFn fn, l, by simp [idOps, hf], by simp [idOpsFn, hc, idOp]⟩
  stackBytes φ := by rw [← stackBytes_idOps φ P]; exact L.stackBytes φ
  wf h := L.wf (wf_idOps h)

end Millipede.RegAlloc
