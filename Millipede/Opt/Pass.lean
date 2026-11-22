import Millipede.Core.Program

/-!
# The interface of the Core passes

A pass `Opt.Pass` rewrites Core terms and proves two laws for every oracle, environment and world.
`denote` says that the result has the same value and world as the input, and so the same event
trace. `safe` says that the input's obligations imply the result's, so a pass may drop
obligations but never add one.

The resource laws are not proved for each pass. `Pass.apply κ φ p` keeps a pass's result only when
its static step bounds and its stack bound are at most those of the input, which is decided at
compile time like the budget check, and otherwise returns the input. Every applied pass therefore
relates its output `q` to its input `p` by `Program.Sim κ φ q p`, which says that they have the
same root type and the same denotations of `init` and `step`, that `q` is safe when `p` is, and
that `q` has no larger cost or stack bound. `Sim` is reflexive and transitive, so any sequence of
applied passes is `Sim` to the source, and `Sim.events`, `Sim.safe`, `Sim.stepCost_le` and
`Sim.stackBytes_le` carry the four clauses of `CompileSound.Statement` from the optimised program
back to the source.

The compiler checks again on the optimised program what the lowering needs of its input. When the
optimised pipeline refuses, the compiler falls back to the source program, so a pass never makes
an accepted program refused. `Config` selects the passes, and with every pass off the optimiser is
the identity.
-/

namespace Millipede.Opt

/-- A Core pass and its semantic laws. -/
structure Pass where
  name : String
  run : {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  denote : ∀ (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) (w : World),
    (run e).denote ω env w = e.denote ω env w
  safe : ∀ (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) (w : World),
    e.safe ω env w → (run e).safe ω env w

/-- The identity pass. -/
def Pass.id : Pass := ⟨"id", fun e => e, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

/-- The pass that runs `Q` after `P`. -/
def Pass.comp (P Q : Pass) : Pass where
  name := P.name ++ ";" ++ Q.name
  run e := Q.run (P.run e)
  denote ω _ _ e env w := (Q.denote ω _ env w).trans (P.denote ω e env w)
  safe ω _ _ e env w h := Q.safe ω _ env w (P.safe ω e env w h)

/-- `P` run `n + 1` times, for a rewrite that exposes another at a parent node. -/
def Pass.iter (P : Pass) : Nat → Pass
  | 0 => P
  | n + 1 => { P.comp (P.iter n) with name := P.name }

/-- The pass applied to both bodies of a program. -/
def Pass.onProg (P : Pass) (p : Program) : Program :=
  { p with init := P.run p.init, step := P.run p.step }

/-- The resource guard, which holds when `q`'s static step bounds and stack bound are at most
`p`'s. -/
def _root_.Millipede.Program.Within (q : Program) (κ : CostModel) (φ : FrameModel) (p : Program) : Bool :=
  decide (q.init.cost κ .copy ≤ p.init.cost κ .copy) &&
    decide (q.step.cost κ q.stepHb ≤ p.step.cost κ p.stepHb) &&
    decide (q.stackBytes φ ≤ p.stackBytes φ)

/-- Applies a pass at cost model `κ` and frame model `φ`, returning its result when it is within
the input's bounds and the input otherwise. -/
def Pass.apply (P : Pass) (κ : CostModel) (φ : FrameModel) (p : Program) : Program :=
  if (P.onProg p).Within κ φ p then P.onProg p else p

/-! ## The relation between an optimised program and its source -/

/-- `q` is an optimisation of `p` at `κ` and `φ`. It has the same root type, `init` and `step` with
the same denotations, at least `p`'s safety, and no larger step bounds or stack bound. -/
def _root_.Millipede.Program.Sim (κ : CostModel) (φ : FrameModel) (q p : Program) : Prop :=
  ∃ (i : Exp [] p.State) (s : Exp [p.State] p.State), q = { p with init := i, step := s } ∧
    (∀ ω env w, i.denote ω env w = p.init.denote ω env w) ∧
    (∀ ω env w, s.denote ω env w = p.step.denote ω env w) ∧
    (∀ ω env w, p.init.safe ω env w → i.safe ω env w) ∧
    (∀ ω env w, p.step.safe ω env w → s.safe ω env w) ∧
    i.cost κ .copy ≤ p.init.cost κ .copy ∧ s.cost κ q.stepHb ≤ p.step.cost κ p.stepHb ∧
    q.stackBytes φ ≤ p.stackBytes φ

namespace Sim

variable {κ : CostModel} {φ : FrameModel}

theorem refl (p : Program) : p.Sim κ φ p :=
  ⟨p.init, p.step, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ h => h, fun _ _ _ h => h,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem trans {r q p : Program} (h₁ : r.Sim κ φ q) (h₂ : q.Sim κ φ p) : r.Sim κ φ p := by
  obtain ⟨i, s, rfl, hi, hs, hsi, hss, hci, hcs, hst⟩ := h₂
  obtain ⟨i', s', rfl, hi', hs', hsi', hss', hci', hcs', hst'⟩ := h₁
  exact ⟨i', s', rfl, fun ω env w => (hi' ω env w).trans (hi ω env w),
    fun ω env w => (hs' ω env w).trans (hs ω env w),
    fun ω env w h => hsi' ω env w (hsi ω env w h), fun ω env w h => hss' ω env w (hss ω env w h),
    Nat.le_trans hci' hci, Nat.le_trans hcs' hcs, Nat.le_trans hst' hst⟩

/-- The runs of the two programs agree. -/
theorem run_with {p : Program} {i : Exp [] p.State} {s : Exp [p.State] p.State}
    (hi : ∀ ω env w, i.denote ω env w = p.init.denote ω env w)
    (hs : ∀ ω env w, s.denote ω env w = p.step.denote ω env w) (ω : Oracle) :
    ∀ n, Program.run { p with init := i, step := s } ω n = p.run ω n
  | 0 => hi ω _ _
  | n + 1 => by simp only [Program.run]; rw [run_with hi hs ω n]; exact hs ω _ _

/-- An optimisation has the same event traces as its source. -/
theorem events {q p : Program} (h : q.Sim κ φ p) (ω : Oracle) : q.events ω = p.events ω := by
  obtain ⟨i, s, rfl, hi, hs, -⟩ := h
  funext n; simp only [Program.events]; rw [run_with hi hs]

/-- Safety carries over from the source to an optimisation. -/
theorem safe {q p : Program} (h : q.Sim κ φ p) (hp : p.Safe) : q.Safe := by
  obtain ⟨i, s, rfl, hi, hs, hsi, hss, -⟩ := h
  intro ω
  exact ⟨hsi ω _ _ (hp ω).1, fun n => by rw [run_with hi hs]; exact hss ω _ _ ((hp ω).2 n)⟩

/-- An optimisation has no larger step bound than its source. -/
theorem stepCost_le {q p : Program} (h : q.Sim κ φ p) (k : Nat) (ω : Oracle) :
    q.stepCost k ω κ ≤ p.stepCost k ω κ := by
  obtain ⟨i, s, rfl, -, -, -, -, hci, hcs, -⟩ := h
  cases k
  · exact hci
  · exact hcs

/-- An optimisation has no larger stack bound than its source. -/
theorem stackBytes_le {q p : Program} (h : q.Sim κ φ p) : q.stackBytes φ ≤ p.stackBytes φ := by
  obtain ⟨i, s, rfl, -, -, -, -, -, -, hst⟩ := h; exact hst

end Sim

/-- An applied pass is an optimisation of its input. -/
theorem Pass.apply_sim (P : Pass) (κ : CostModel) (φ : FrameModel) (p : Program) :
    (P.apply κ φ p).Sim κ φ p := by
  unfold Pass.apply
  split
  · next h =>
    simp only [Program.Within, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, _, rfl, fun ω => P.denote ω _, fun ω => P.denote ω _, fun ω => P.safe ω _,
      fun ω => P.safe ω _, h.1.1, h.1.2, h.2⟩
  · exact Sim.refl p

/-- Applies a list of passes in order. -/
def applyAll (κ : CostModel) (φ : FrameModel) : List Pass → Program → Program
  | [], p => p
  | P :: Ps, p => applyAll κ φ Ps (P.apply κ φ p)

theorem applyAll_sim (κ : CostModel) (φ : FrameModel) :
    ∀ (Ps : List Pass) (p : Program), (applyAll κ φ Ps p).Sim κ φ p
  | [], p => Sim.refl p
  | P :: Ps, p => Sim.trans (applyAll_sim κ φ Ps _) (P.apply_sim κ φ p)

/-- Repeats a list of passes `n` times, so that a later round folds what an earlier one exposed. -/
def rounds (κ : CostModel) (φ : FrameModel) (Ps : List Pass) : Nat → Program → Program
  | 0, p => p
  | n + 1, p => rounds κ φ Ps n (applyAll κ φ Ps p)

theorem rounds_sim (κ : CostModel) (φ : FrameModel) (Ps : List Pass) :
    ∀ (n : Nat) (p : Program), (rounds κ φ Ps n p).Sim κ φ p
  | 0, p => Sim.refl p
  | n + 1, p => Sim.trans (rounds_sim κ φ Ps n _) (applyAll_sim κ φ Ps p)

end Millipede.Opt
