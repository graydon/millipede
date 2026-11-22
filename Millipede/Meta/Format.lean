import Lean
import Millipede.Meta.MpDef
import Millipede.Format.Code
import Millipede.Format.Seq
import Millipede.Format.Leaves

namespace Millipede.Meta.Format

open Lean Elab Tactic Meta

/-! ## The tactics of the generated proofs -/

/-- Split every hypothesis that is a conjunction. -/
partial def splitAnds (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 then
      let gs ← g.cases d.fvarId
      return ← splitAnds (gs[0]?.map (·.mvarId) |>.getD g)
  return g

/-- `fmt_split` splits every hypothesis that is a conjunction. -/
elab "fmt_split" : tactic => liftMetaTactic fun g => return [← splitAnds g]

/-- `fmt_is c` fails unless the goal, unfolded by reducible definitions, is an application of `c`.
The walks are tried only on their own goals, because a walk that fails on another goal can take
seconds over the long terms of a verification condition. -/
elab "fmt_is " c:ident : tactic => withMainContext do
  let n ← realizeGlobalConstNoOverload c
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.getAppFn.isConstOf n do throwError "fmt_is: the goal is not an application of `{n}`"

end Millipede.Meta.Format

/-- Normalise the hypotheses of a verification condition of generated format code: tuple
projections, the leaves' widths and byte orders, the results of calls that the code tested, and
word equalities as equalities of naturals. -/
macro "fmt_norm" : tactic => `(tactic| (
  (try dsimp only at *)
  (try simp only [UInt64.reduceToNat, Millipede.Format.endian, ite_true, ite_false,
    Bool.false_eq_true, Bool.not_eq_false, Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false',
    eq_self_iff_true, true_implies, false_implies, implies_true, beq_iff_eq,
    decide_eq_true_eq, decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, Nat.not_lt] at *)
  (try subst_vars)
  (try simp only [← UInt64.toNat_inj, UInt64.reduceToNat, eq_self_iff_true, true_implies,
    false_implies, implies_true, Bool.false_eq_true] at *)
  fmt_split))

/-- Close `p.toNat ≤ (Slots.bytes s n).length` and like goals from the hypotheses. -/
macro "fmt_le" : tactic => `(tactic| (simp only [Millipede.Format.Slots.bytes_length]; omega))

/-- Give each position or value that a walk left open, because no field fixes it, any value. -/
macro "fmt_junk" : tactic => `(tactic|
  (try (all_goals (first | exact (0 : UInt64) | exact Millipede.Format.Val.unit | exact 0))))

/-- Prove `ParsedT f t B p ok p' v` by walking the description `f`, from the leaves' contracts in
the hypotheses and the composition lemmas. -/
syntax "fmt_parsed" : tactic
macro_rules
  | `(tactic| fmt_parsed) => `(tactic| first
    | with_reducible assumption
    | ((with_reducible apply Millipede.Format.ParsedT.noArm); fmt_junk)
    | ((with_reducible apply Millipede.Format.ParsedT.unit); fmt_le)
    | ((with_reducible apply Millipede.Format.Parsed.pair_cont);
        (case ha => fmt_parsed); (case hb => fmt_parsed); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Parsed.pair_stop); (case ha => fmt_parsed); fmt_junk)
    | ((with_reducible apply Millipede.Format.Parsed.union_cont);
        (case ht => fmt_parsed); (case ha => fmt_parsed); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Parsed.union_stop); (case ht => fmt_parsed); fmt_junk)
    | ((with_reducible apply Millipede.Format.Parsed.array);
        (case ht => with_reducible assumption); (case hc => omega); (case hi => with_reducible assumption); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Parsed.array_stop); (case ht => with_reducible assumption); fmt_junk)
    | ((with_reducible apply Millipede.Format.Parsed.array_big);
        (case ht => with_reducible assumption); (case hc => omega); (case hp => fmt_le))
    | (rw [Millipede.Format.ParsedT.arm_eq]; split <;> rename_i hArm <;>
        first | (exfalso; omega) | ((try simp only [hArm, ↓reduceIte]) <;> fmt_parsed)); fmt_junk)

/-- Prove `CheckedT f t B p ok p'` by walking the description `f`; a union's tag is a parser's. -/
syntax "fmt_checked" : tactic
macro_rules
  | `(tactic| fmt_checked) => `(tactic| first
    | with_reducible assumption
    | ((with_reducible apply Millipede.Format.CheckedT.noArm); fmt_junk)
    | ((with_reducible apply Millipede.Format.CheckedT.unit); fmt_le)
    | ((with_reducible apply Millipede.Format.Checked.pair_cont);
        (case ha => fmt_checked); (case hb => fmt_checked); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Checked.pair_stop); (case ha => fmt_checked); fmt_junk)
    | ((with_reducible apply Millipede.Format.Checked.union_cont);
        (case ht => with_reducible assumption); (case ha => fmt_checked); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Checked.union_stop); (case ht => with_reducible assumption); fmt_junk)
    | ((with_reducible apply Millipede.Format.Checked.array);
        (case ht => with_reducible assumption); (case hc => omega); (case hi => with_reducible assumption); (case hp => fmt_le))
    | ((with_reducible apply Millipede.Format.Checked.array_stop); (case ht => with_reducible assumption); fmt_junk)
    | ((with_reducible apply Millipede.Format.Checked.array_big);
        (case ht => with_reducible assumption); (case hc => omega); (case hp => fmt_le))
    | (rw [Millipede.Format.CheckedT.arm_eq]; split <;> rename_i hArm <;>
        first | (exfalso; omega) | ((try simp only [hArm, ↓reduceIte]) <;> fmt_checked)); fmt_junk
    | ((with_reducible apply Millipede.Format.CheckedT.of_parsed); with_reducible assumption))

/-- Prove `WrittenT f t d d' p p' v` by walking the description `f`. -/
syntax "fmt_written" : tactic
macro_rules
  | `(tactic| fmt_written) => `(tactic| first
    | with_reducible assumption
    | ((with_reducible apply Millipede.Format.WrittenT.of_forall); with_reducible assumption)
    | ((with_reducible apply Millipede.Format.WrittenT.noArm); fmt_junk)
    | ((with_reducible apply Millipede.Format.WrittenT.unit); fmt_junk)
    | ((with_reducible apply Millipede.Format.Written.pair); (case ha => fmt_written); (case hb => fmt_written))
    | ((with_reducible apply Millipede.Format.Written.union); (case ht => fmt_written); (case ha => fmt_written))
    | ((with_reducible apply Millipede.Format.Written.array);
        (case ht => with_reducible assumption); (case hi => with_reducible assumption); (case hl => (simp; omega)))
    | (rw [Millipede.Format.WrittenT.arm_eq]; split <;> rename_i hArm <;>
        first | (exfalso; omega) | ((try simp only [hArm, ↓reduceIte]) <;> fmt_written)); fmt_junk)

/-- Prove that the cells of a buffer are full after writers, from the writers' contracts. -/
syntax "fmt_full" : tactic
macro_rules
  | `(tactic| fmt_full) => `(tactic| first
    | with_reducible assumption
    | ((with_reducible apply Millipede.Format.isFull_of_lt); (case hf => with_reducible assumption); (case hk => with_reducible assumption))
    | ((with_reducible apply Millipede.Format.WrittenT.isFull); (case hw => with_reducible assumption); (case hf => fmt_full))
    | ((with_reducible apply Millipede.Format.WrittenT.isFull_forall); (case hw => with_reducible assumption); (case hf => fmt_full))
    | ((with_reducible apply Millipede.Format.WrittenItems.isFull); (case hw => with_reducible assumption); (case hf => fmt_full))
    | (intro _ _; fmt_full))

/-- Close a goal that is a conjunction of bounds and full cells, as a callee's `requires` is. -/
syntax "fmt_pre" : tactic
macro_rules
  | `(tactic| fmt_pre) => `(tactic| first
    | exact True.intro
    | omega
    | fmt_full
    | (refine ⟨?_, ?_⟩ <;> fmt_pre)
    | (intro; fmt_pre))

/-- Close a goal of a verification condition of generated format code: a parser's or a writer's
contract by walking the description, or a conjunction of bounds. -/
syntax "fmt_close" : tactic
macro_rules
  | `(tactic| fmt_close) => `(tactic| first
    | (fmt_is Millipede.Format.ParsedT; fmt_parsed)
    | (fmt_is Millipede.Format.CheckedT; fmt_checked)
    | (fmt_is Millipede.Format.WrittenT; fmt_written)
    | exact True.intro
    | omega
    | fmt_full
    | (refine ⟨?_, ?_⟩ <;> fmt_close)
    | solve_by_elim
    | (intro; fmt_close)
    | fail "no step of the walk over the description proves this goal")
