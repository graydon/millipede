import Millipede.Compile.LowerInv
import Millipede.Meta.Sem

/-!
# Lawfulness of derived building blocks

`Exp.Lawful` asks every lens, constructor and split of a term to agree with the byte layout. Each
building block that `deriving Data` and `mp def` produce carries its law as a certificate, so a
certified block is lawful (`Lens.lawful_of_law` and its siblings). `Exp.certified` checks that every
block of a term carries its certificate, and `Exp.lawful_of_certified` turns that check, which
`compile` runs, into `Exp.Lawful`.
-/

namespace Millipede.Flat

/-! ## Certified building blocks are lawful -/

theorem _root_.Millipede.Lens.lawful_of_law {s t : Ty} (l : Lens s t) (h : l.law.isSome = true)
    (ha : l.aligned = true) : l.Lawful := by
  match hl : l.law, h with
  | some ⟨h⟩, _ => exact ⟨h.1, l.aligned_spec ha⟩

theorem _root_.Millipede.Ctor.lawful_of_law {ps : List Ty} {t : Ty} (c : Ctor ps t)
    (h : c.law.isSome = true) : c.Lawful := by
  match hl : c.law, h with
  | some ⟨h⟩, _ => exact h

theorem _root_.Millipede.Split.lawful_of_law {t p q : Ty} (sp : Split t p q)
    (h : sp.law.isSome = true) : sp.Lawful := by
  match hl : sp.law, h with
  | some ⟨h⟩, _ => exact h

/-! ## The certification check `compile` runs -/

/-- Every lens of a place carries a certificate of its law. -/
def _root_.Millipede.Place.certified {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p l => p.certified && l.law.isSome && l.aligned
  | _, .index (dflt := _) p _ => p.certified
  | _, .slot (dflt := _) p _ => p.certified
  | _, .range p _ _ => p.certified
  | _, .pair2 (dflt := _) p _ _ => p.certified
  | _, .rangeS _ _ _ => true
  | _, .pair2S (dflt := _) _ _ _ => true

/-- The argument places of a reference call are certified. -/
def _root_.Millipede.RArgs.certified {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Bool
  | _, _, .nil => true
  | _, _, .own _ as => as.certified
  | _, _, .shr p as => p.certified && as.certified
  | _, _, .mut p as => p.certified && as.certified

/-- The array places of an extern call's slices are certified. -/
def _root_.Millipede.EArgs.certified {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.certified
  | _, .bufIn (.const _) as => as.certified
  | _, .bufIn (.slice a _ _) as => a.certified && as.certified
  | _, .bufOut as => as.certified
  | _, .sliceOut a _ _ as => a.certified && as.certified

/-- Every building block of a term, callees included, carries a certificate of its law. This is
the check that `compile` runs. -/
def _root_.Millipede.Exp.certified : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .atom _ => true
  | _, _, .let_ e₁ e₂ => e₁.certified && e₂.certified
  | _, _, .ite _ e₁ e₂ => e₁.certified && e₂.certified
  | _, _, .prim _ _ => true
  | _, _, .call _ body _ => body.certified
  | _, _, .ok _ => true
  | _, _, .err _ => true
  | _, _, .match_ _ eE eO => eE.certified && eO.certified
  | _, _, .ext _ args => args.certified
  | _, _, .extMut _ args k => args.certified && k.certified
  | _, _, .mk c _ => c.law.isSome
  | _, _, .read p => p.certified
  | _, _, .assign p _ k => p.certified && k.certified
  | _, _, .case _ sp eP eQ => sp.law.isSome && eP.certified && eQ.certified
  | _, _, .put p _ _ k => p.certified && k.certified
  | _, _, .take (dflt := _) p _ k => p.certified && k.certified
  | _, _, .borrowShr p body k => p.certified && body.certified && k.certified
  | _, _, .borrowMut p body k => p.certified && body.certified && k.certified
  | _, _, .callRef _ _ body args k => args.certified && body.certified && k.certified
  | _, _, .guard g =>
    match g with
    | .valid p _ => p.certified
  | _, _, .loop _ _ _ c body k => c.certified && body.certified && k.certified

theorem _root_.Millipede.Place.lawful_of_certified {Γ : List Ty} :
    {t : Ty} → (p : Place Γ t) → p.certified = true → p.Lawful
  | _, .var _, _ => trivial
  | _, .field p l, h => by
    simp only [Place.certified, Bool.and_eq_true] at h
    exact ⟨p.lawful_of_certified h.1.1, l.lawful_of_law h.1.2 h.2⟩
  | _, .index (dflt := _) p _, h => p.lawful_of_certified h
  | _, .slot (dflt := _) p _, h => p.lawful_of_certified h
  | _, .range p _ _, h => p.lawful_of_certified h
  | _, .pair2 (dflt := _) p _ _, h => p.lawful_of_certified h
  | _, .rangeS _ _ _, _ => trivial
  | _, .pair2S (dflt := _) _ _ _, _ => trivial

theorem _root_.Millipede.RArgs.lawful_of_certified {Γ : List Ty} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → as.certified = true → as.Lawful
  | _, _, .nil, _ => trivial
  | _, _, .own _ as, h => as.lawful_of_certified h
  | _, _, .shr p as, h => by
    simp only [RArgs.certified, Bool.and_eq_true] at h
    exact ⟨p.lawful_of_certified h.1, as.lawful_of_certified h.2⟩
  | _, _, .mut p as, h => by
    simp only [RArgs.certified, Bool.and_eq_true] at h
    exact ⟨p.lawful_of_certified h.1, as.lawful_of_certified h.2⟩

theorem _root_.Millipede.EArgs.lawful_of_certified {Γ : List Ty} {ps : List ExtParam}
    (as : EArgs Γ ps) (h : as.certified = true) : as.Lawful := by
  induction as with
  | nil => trivial
  | word _ _ ih | bufOut _ ih => exact ih h
  | bufIn b _ ih =>
    cases b with
    | const => exact ih h
    | slice a _ _ =>
      simp only [EArgs.certified, Bool.and_eq_true] at h
      exact ⟨a.lawful_of_certified h.1, ih h.2⟩
  | sliceOut a _ _ _ ih =>
    simp only [EArgs.certified, Bool.and_eq_true] at h
    exact ⟨a.lawful_of_certified h.1, ih h.2⟩

/-- A certified term is lawful. -/
theorem _root_.Millipede.Exp.lawful_of_certified {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (h : e.certified = true) : e.Lawful := by
  induction e with
  | atom => trivial
  | prim => trivial
  | ok => trivial
  | err => trivial
  | ext _ args => exact args.lawful_of_certified h
  | extMut _ args _ ih =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨args.lawful_of_certified h.1, ih h.2⟩
  | call _ body _ ih => exact ih h
  | mk c _ => exact c.lawful_of_law h
  | read p => exact p.lawful_of_certified h
  | guard g =>
    cases g with
    | valid p _ => exact p.lawful_of_certified h
  | let_ _ _ ih₁ ih₂ | ite _ _ _ ih₁ ih₂ | match_ _ _ _ ih₁ ih₂ =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | assign p _ _ ih | put p _ _ _ ih | take p _ _ ih =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨p.lawful_of_certified h.1, ih h.2⟩
  | case _ sp _ _ ihP ihQ =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨sp.lawful_of_law h.1.1, ihP h.1.2, ihQ h.2⟩
  | borrowShr p _ _ ihb ihk | borrowMut p _ _ ihb ihk =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨p.lawful_of_certified h.1.1, ihb h.1.2, ihk h.2⟩
  | callRef _ _ _ args _ ihb ihk =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨args.lawful_of_certified h.1.1, ihb h.1.2, ihk h.2⟩
  | loop _ _ _ _ _ _ ihc ihb ihk =>
    simp only [Exp.certified, Bool.and_eq_true] at h
    exact ⟨ihc h.1.1, ihb h.1.2, ihk h.2⟩

end Millipede.Flat
