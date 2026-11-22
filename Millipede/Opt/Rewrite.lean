import Millipede.Opt.Pass
import Millipede.Opt.Subst

/-!
# Bottom-up rewriting

`Exp.bu f e` rewrites every subterm of `e` bottom-up, the children of a node first, callee bodies
included, and then `f` at the node. A local rule is a `Pass` whose laws hold at every node, and
`Pass.bu R` is the pass that applies it everywhere. Its laws follow from `R`'s by one induction,
since a node whose children have the same denotations and at most their obligations has the same
denotation and at most its obligations.
-/

namespace Millipede.Opt

open Millipede

/-- Rewrites bottom-up with `f`. -/
def _root_.Millipede.Exp.bu (f : ∀ {Γ : List Ty} {t : Ty}, Exp Γ t → Exp Γ t) :
    {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  | _, _, .atom a => f (.atom a)
  | _, _, .let_ e₁ e₂ => f (.let_ (e₁.bu f) (e₂.bu f))
  | _, _, .ite c e₁ e₂ => f (.ite c (e₁.bu f) (e₂.bu f))
  | _, _, .prim p args => f (.prim p args)
  | _, _, .call n body args => f (.call n (body.bu f) args)
  | _, _, .ok a => f (.ok a)
  | _, _, .err a => f (.err a)
  | _, _, .match_ s eE eO => f (.match_ s (eE.bu f) (eO.bu f))
  | _, _, .ext sig args => f (.ext sig args)
  | _, _, .extMut sig args k => f (.extMut sig args (k.bu f))
  | _, _, .mk c args => f (.mk c args)
  | _, _, .read p => f (.read p)
  | _, _, .assign p a k => f (.assign p a (k.bu f))
  | _, _, .case s sp eP eQ => f (.case s sp (eP.bu f) (eQ.bu f))
  | _, _, .put p i a k => f (.put p i a (k.bu f))
  | _, _, .take (dflt := _) p i k => f (.take p i (k.bu f))
  | _, _, .borrowShr p b k => f (.borrowShr p (b.bu f) (k.bu f))
  | _, _, .borrowMut p b k => f (.borrowMut p (b.bu f) (k.bu f))
  | _, _, .callRef n req b args k => f (.callRef n req (b.bu f) args (k.bu f))
  | _, _, .guard g => f (.guard g)
  | _, _, .loop n cs init c b k => f (.loop n cs init (c.bu f) (b.bu f) (k.bu f))

theorem bu_denote (R : Pass) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), (e.bu R.run).denote ω env w = e.denote ω env w := by
  induction e <;> intro env w <;> rw [Exp.bu, R.denote] <;> simp only [Exp.denote, *]

theorem bu_safe (R : Pass) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), e.safe ω env w → (e.bu R.run).safe ω env w := by
  induction e <;> intro env w hs <;> rw [Exp.bu] <;> apply R.safe <;>
    simp only [Exp.safe, bu_denote] at hs ⊢
  case loop ihc ihb ihk =>
    exact ⟨loopSafe_imp _ _ _ _ _ _ (fun _ _ _ h => ihc _ _ h) (fun _ _ _ h => ihb _ _ h) _ _ _ _
      hs.1, ihk _ _ hs.2⟩
  all_goals grind

/-- A local rule applied everywhere, bottom-up. -/
def Pass.bu (R : Pass) : Pass where
  name := R.name
  run e := e.bu R.run
  denote ω _ _ e := bu_denote R ω e
  safe ω _ _ e := bu_safe R ω e

end Millipede.Opt
