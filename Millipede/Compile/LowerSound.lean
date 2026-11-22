import Millipede.Compile.LowerLoop

/-!
# The memory refinement theorem for `lower`

`lowerM_sound` states that, for every oracle `ω` and cost model `κ`, the memory lowering of every
term it accepts simulates the instrumented semantics `Exp.exec`, in every tail mode the term
conforms to. It starts from a state whose memory represents the environment at each variable's
address, which is the variable's own storage or the storage a reference binder points to. The Flat
run then either halts after `exit` in `exec`'s world, or reaches a state with the following
properties:

* the world is exactly `exec`'s, so the events are the same for every oracle;
* the clock has advanced by exactly `exec`'s step count, so by at most `e.cost κ`;
* the destination holds bytes that represent `exec`'s value, or in a tail mode the handed-back
  references are in place;
* every address the term may not touch is unchanged, which is everything below the watermark
  except the destination and the storage of the variables the term may write;
* every memory access of the run is below `bp + n + e.memNeed`.

The hypotheses are the block rule, the borrow discipline that `Exp.wf` gives, lawful building
blocks, the obligations, and memory that fits below `2^64`.

A borrow or a reference argument passes an address, and the body or the callee works on the
lender's storage in place, so nothing is copied when the borrow begins or ends. While a `&mut`
borrow is live, the refinement relates the lender to its stale source value through a hole, and
the borrow checker's loans make every access avoid that hole and keep the arguments of a call
apart.

The proof is compositional, with one case lemma per construct and one lemma per primitive. Every
construct that `lower` accepts is covered, so the proved fragment is the lowered fragment. The
method is described in doc/design/compiler.md.
-/

namespace Millipede.Flat

/-- The memory refinement theorem, for every term that the memory lowering accepts. -/
theorem lowerM_sound (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (hp : e.memOk = true) : MSoundAt κ ω e := by
  induction e with
  | atom a => exact msound_atom a
  | let_ e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_let e₁ e₂ (ih₁ hp.1) (ih₂ hp.2)
  | ite c e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_ite c e₁ e₂ (ih₁ hp.1) (ih₂ hp.2)
  | prim p args => exact msound_prim p args
  | ok a => exact msound_ok a
  | err a => exact msound_err a
  | match_ s eE eO ihE ihO =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_match s eE eO (ihE hp.1) (ihO hp.2)
  | ext sig args =>
    simp only [Exp.memOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact msound_ext sig args hp.1.1 hp.1.2 hp.2
  | extMut sig args k ih =>
    simp only [Exp.memOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact msound_extMut sig args k hp.1.1.1 hp.1.1.2 hp.1.2 (ih hp.2)
  | call name body args ih => exact msound_call name body args (ih hp)
  | mk c args => exact msound_mk c args
  | read p => cases p <;> first | exact msound_read_pair2 _ _ _ hp | exact msound_read _ hp
  | put p i a k ih =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_put p i a k hp.1 (ih hp.2)
  | take p i k ih =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_take p i k hp.1 (ih hp.2)
  | borrowShr p body k ihb ihk =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨hpo, hpr⟩, hb⟩, hk⟩ := hp
    cases p
    case range q lo len =>
      simp only [Place.refOk, Place.borrowOk, Place.contig, Bool.false_or] at hpo hpr
      exact msound_borrowShr_range q lo len body k hpo hpr (ihb hb) (ihk hk)
    case pair2 q i j =>
      simp only [Place.refOk, Place.contig, Bool.false_or] at hpo hpr
      exact msound_borrowShr_pair2 q i j body k hpo hpr (ihb hb) (ihk hk)
    case rangeS m lo len =>
      simp only [Place.contig, Bool.false_or] at hpr
      exact msound_borrowShr_rangeS m lo len body k hpr (ihb hb) (ihk hk)
    case pair2S m i j =>
      simp only [Place.contig, Bool.false_or] at hpr
      exact msound_borrowShr_pair2S m i j body k hpr (ihb hb) (ihk hk)
    all_goals exact msound_borrowShr _ body k hpo (ihb hb) (ihk hk)
  | borrowMut p body k ihb ihk =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨hpo, hpr⟩, hCb⟩, hb⟩, hk⟩ := hp
    cases p
    case range q lo len =>
      simp only [Place.refOk, Place.borrowOk, Place.contig, Place.isRange, Bool.not_true,
        Bool.false_or, Bool.and_eq_true] at hpo hpr
      exact msound_borrowMut_range q lo len body k hpo hCb hpr.1 hpr.2 (ihb hb) (ihk hk)
    case pair2 q i j =>
      simp only [Place.refOk, Place.contig, Place.isRange, Bool.not_false, Bool.true_or,
        Bool.and_true, Bool.false_or] at hpo hpr
      exact msound_borrowMut_pair2 q i j body k hpo hCb hpr (ihb hb) (ihk hk)
    case rangeS m lo len =>
      simp only [Place.contig, Place.isRange, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hpr
      exact msound_borrowMut_rangeS m lo len body k hCb hpr.1 hpr.2 (ihb hb) (ihk hk)
    case pair2S m i j =>
      simp only [Place.contig, Place.isRange, Bool.not_false, Bool.true_or, Bool.and_true,
        Bool.false_or] at hpr
      exact msound_borrowMut_pair2S m i j body k hCb hpr (ihb hb) (ihk hk)
    all_goals exact msound_borrowMut _ body k hpo hCb (ihb hb) (ihk hk)
  | assign p a k ih =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    cases p <;> first
      | exact msound_assign_pair2 _ _ _ a k hp.1 (ih hp.2) | exact msound_assign _ a k hp.1 (ih hp.2)
  | case s sp eP eQ ihP ihQ =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_case s sp eP eQ (ihP hp.1.2) (ihQ hp.2)
  | callRef name req body args k ihb ihk =>
    simp only [Exp.memOk, Bool.and_eq_true] at hp
    exact msound_callRef name req body args k hp.1.1.1.1.1 hp.1.1.1.1.2 hp.1.1.1.2 hp.1.1.2
      (ihb hp.1.2) (ihk hp.2)
  | guard g =>
    cases g with
    | valid p hck => exact msound_guard p hck hp
  | loop N cs init c body k ihc ihb ihk =>
    simp only [Exp.memOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact msound_loop N cs init c body k hp.1.1.1.1.1 hp.1.1.1.1.2 hp.1.1.1.2 (ihc hp.1.1.2)
      (ihb hp.1.2) (ihk hp.2)

end Millipede.Flat
