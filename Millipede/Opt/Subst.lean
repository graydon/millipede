import Millipede.Analysis.Domain

/-!
# Substitution of atoms for variables

A substitution `σ : Sub Γ Δ` maps each variable of `Γ` to an atom of `Δ` where the variable is
read, and to a variable of `Δ` where a variable is required, as at the root of a place or for a
loop-carried variable. Either map may give `none`, which means that the variable must not occur
in that position. `e.subst σ` replaces every variable of `e` and returns `none` on such an
occurrence. Callee bodies are closed, so they are left as they are.

Every rewrite of the Core passes that changes contexts uses this one operation. Dropping an unused
binder and propagating a constant into a binder's scope use `Sub.under`, and inlining a call
replaces the callee's parameters by the argument atoms with `Sub.args`.

`Exp.subst_denote` and `Exp.subst_safe` prove that the substituted term has the same denotation
and at most the same obligations. They need two conditions. `Sub.Rel` says that each variable's
image denotes, in the new environment, the variable's value in the old one, and `Sub.Inj` says
that a variable written through its image `x` is the only one whose image reads `x`, so the
relation survives every write. Costs, slots and stack are not proved unchanged, because the
passes check them when they are applied.
-/

namespace Millipede.Opt

open Millipede

/-- A substitution, which maps each variable of `Γ` to an atom of `Δ` where it is read, and to a
variable of `Δ` where a variable is required, at the root of a place or for a loop-carried
variable. A map that gives `none` means that the variable must not occur there, and where both
maps give a result they agree. -/
structure Sub (Γ Δ : List Ty) where
  f : {t : Ty} → Mem t Γ → Option (Atom Δ t)
  g : {t : Ty} → Mem t Γ → Option (Mem t Δ)
  fg : ∀ {t : Ty} (m : Mem t Γ) (x : Mem t Δ), g m = some x → f m = some (.var x)

namespace Sub

variable {Γ Δ : List Ty}

/-- The substitution under a binder, which maps the new variable to itself and shifts the
others. -/
def lift (σ : Sub Γ Δ) (s : Ty) : Sub (s :: Γ) (s :: Δ) where
  f := fun {_} m => match m with
    | .here => some (.var .here)
    | .there m => (σ.f m).map Atom.shift
  g := fun {_} m => match m with
    | .here => some .here
    | .there m => (σ.g m).map .there
  fg := fun m x h => by
    cases m with
    | here => cases h; rfl
    | there m =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨y, hy, rfl⟩ := h
      exact ⟨_, σ.fg m y hy, rfl⟩

/-- The variable a variable becomes where a variable is required. -/
abbrev mem (σ : Sub Γ Δ) {t : Ty} (m : Mem t Γ) : Option (Mem t Δ) := σ.g m

/-- `σ` relates `env` to `env'` when each variable's image denotes its value. -/
def Rel (σ : Sub Γ Δ) (env : Env Γ) (env' : Env Δ) : Prop :=
  ∀ {t : Ty} (m : Mem t Γ) (a : Atom Δ t), σ.f m = some a → a.denote env' = env.get m

/-- A variable written through its image `x` is the only one whose image reads `x`, so a write
through an image changes the images of exactly one source variable. -/
def Inj (σ : Sub Γ Δ) : Prop :=
  ∀ {t u : Ty} (m₁ : Mem t Γ) (m₂ : Mem u Γ) (x : Mem t Δ) (y : Mem u Δ),
    σ.g m₁ = some x → σ.f m₂ = some (.var y) → x.idx = y.idx → m₁.idx = m₂.idx

theorem Rel.get {σ : Sub Γ Δ} {env : Env Γ} {env' : Env Δ} (h : σ.Rel env env') {t : Ty}
    {m : Mem t Γ} {x : Mem t Δ} (hm : σ.mem m = some x) : env'.get x = env.get m :=
  h m (.var x) (σ.fg m x hm)

/-- A write through an image is the write through its source variable. -/
theorem Rel.set {σ : Sub Γ Δ} (hσ : σ.Inj) {env : Env Γ} {env' : Env Δ} (h : σ.Rel env env')
    {t : Ty} {m : Mem t Γ} {x : Mem t Δ} (hm : σ.mem m = some x) (v : t.carrier) :
    σ.Rel (env.set m v) (env'.set x v) := by
  have hx := σ.fg m x hm
  intro u m₂ a ha
  by_cases he : m₂.idx = m.idx
  · obtain ⟨rfl, hh⟩ := Mem.eq_of_idx m₂ m he
    cases hh; rw [hx] at ha; cases ha
    simp only [Atom.denote, Env.get_set_same]
  · rw [Env.get_set_ne _ _ _ _ he]
    cases a with
    | lit c => exact h m₂ _ ha
    | var y =>
      have hy : y.idx ≠ x.idx := fun e => he (hσ _ _ _ _ hm ha e.symm).symm
      simp only [Atom.denote]; rw [Env.get_set_ne _ _ _ _ hy]; exact h m₂ _ ha

theorem Rel.lift {σ : Sub Γ Δ} {env : Env Γ} {env' : Env Δ} (h : σ.Rel env env') {s : Ty}
    (v : s.carrier) : (σ.lift s).Rel (.cons v env) (.cons v env') := by
  intro t m a ha
  cases m with
  | here => cases ha; rfl
  | there m =>
    simp only [Sub.lift, Option.map_eq_some_iff] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    cases b <;> simp only [Atom.shift, Atom.denote, Env.get] <;> exact h m _ hb

theorem Inj.lift {σ : Sub Γ Δ} (h : σ.Inj) (s : Ty) : (σ.lift s).Inj := by
  intro t u m₁ m₂ x y h₁ h₂ he
  cases m₁ with
  | here =>
    cases h₁; cases m₂ with
    | here => rfl
    | there m₂ =>
      simp only [Sub.lift, Option.map_eq_some_iff] at h₂
      obtain ⟨b, -, hb⟩ := h₂
      cases b <;> simp only [Atom.shift, Atom.var.injEq, reduceCtorEq] at hb
      subst hb; simp [Mem.idx] at he
  | there m₁ =>
    simp only [Sub.lift, Option.map_eq_some_iff] at h₁
    obtain ⟨x', hx', rfl⟩ := h₁
    cases m₂ with
    | here => cases h₂; simp [Mem.idx] at he
    | there m₂ =>
      simp only [Sub.lift, Option.map_eq_some_iff] at h₂
      obtain ⟨b₂, hb₂, e₂⟩ := h₂
      cases b₂ <;> simp only [Atom.shift, Atom.var.injEq, reduceCtorEq] at e₂
      subst e₂
      simp only [Mem.idx, Nat.add_right_cancel_iff] at he ⊢
      exact h _ _ _ _ hx' hb₂ he

end Sub

/-! ## Applying a substitution -/

section
variable {Γ Δ : List Ty}

def _root_.Millipede.Atom.subst {t : Ty} (σ : Sub Γ Δ) : Atom Γ t → Option (Atom Δ t)
  | .var m => σ.f m
  | .lit v => some (.lit v)

def _root_.Millipede.Args.subst (σ : Sub Γ Δ) : {ps : List Ty} → Args Γ ps → Option (Args Δ ps)
  | _, .nil => some .nil
  | _, .cons a as => do some (.cons (← a.subst σ) (← as.subst σ))

def _root_.Millipede.Place.subst (σ : Sub Γ Δ) : {t : Ty} → Place Γ t → Option (Place Δ t)
  | _, .var m => do some (.var (← σ.mem m))
  | _, .field p l => do some (.field (← p.subst σ) l)
  | _, .index (dflt := _) p i => do some (.index (← p.subst σ) (← i.subst σ))
  | _, .slot (dflt := _) p i => do some (.slot (← p.subst σ) (← i.subst σ))
  | _, .range p lo len => do some (.range (← p.subst σ) (← lo.subst σ) (← len.subst σ))
  | _, .pair2 (dflt := _) p i j => do some (.pair2 (← p.subst σ) (← i.subst σ) (← j.subst σ))
  | _, .rangeS m lo len => do some (.rangeS (← σ.mem m) (← lo.subst σ) (← len.subst σ))
  | _, .pair2S (dflt := _) m i j => do some (.pair2S (← σ.mem m) (← i.subst σ) (← j.subst σ))

/-- Substitution in a guard, which returns `none` if the substituted place is not checkable. It
always is, because `subst` keeps the selectors. -/
def _root_.Millipede.Guard.subst (σ : Sub Γ Δ) : Guard Γ → Option (Guard Δ)
  | .valid p _ => do
    let p' ← p.subst σ
    if hc : p'.checkable = true then some (.valid p' hc) else none

def _root_.Millipede.RArgs.subst (σ : Sub Γ Δ) : {ps os : List Ty} → RArgs Γ ps os →
    Option (RArgs Δ ps os)
  | _, _, .nil => some .nil
  | _, _, .own a as => do some (.own (← a.subst σ) (← as.subst σ))
  | _, _, .shr p as => do some (.shr (← p.subst σ) (← as.subst σ))
  | _, _, .mut p as => do some (.mut (← p.subst σ) (← as.subst σ))

def _root_.Millipede.Buf.subst (σ : Sub Γ Δ) : Buf Γ → Option (Buf Δ)
  | .const bs => some (.const bs)
  | .slice a lo len => do some (.slice (← a.subst σ) (← lo.subst σ) (← len.subst σ))

def _root_.Millipede.EArgs.subst (σ : Sub Γ Δ) : {ps : List ExtParam} → EArgs Γ ps →
    Option (EArgs Δ ps)
  | _, .nil => some .nil
  | _, .word a as => do some (.word (← a.subst σ) (← as.subst σ))
  | _, .bufIn b as => do some (.bufIn (← b.subst σ) (← as.subst σ))
  | _, .bufOut as => do some (.bufOut (← as.subst σ))
  | _, .sliceOut a lo cap as =>
    do some (.sliceOut (← a.subst σ) (← lo.subst σ) (← cap.subst σ) (← as.subst σ))

def _root_.Millipede.Carry.subst (σ : Sub Γ Δ) : {ts : List Ty} → Carry Γ ts → Option (Carry Δ ts)
  | _, .nil => some .nil
  | _, .cons m cs => do some (.cons (← σ.mem m) (← cs.subst σ))

end

/-- Substitution in a term. It returns `none` when a variable that must not occur does, or when a
literal appears where a variable is required. -/
def _root_.Millipede.Exp.subst : {Γ Δ : List Ty} → {t : Ty} → Sub Γ Δ → Exp Γ t → Option (Exp Δ t)
  | _, _, _, σ, .atom a => do some (.atom (← a.subst σ))
  | _, _, _, σ, .let_ (s := s) e₁ e₂ => do some (.let_ (← e₁.subst σ) (← e₂.subst (σ.lift s)))
  | _, _, _, σ, .ite c e₁ e₂ => do some (.ite (← c.subst σ) (← e₁.subst σ) (← e₂.subst σ))
  | _, _, _, σ, .prim p args => do some (.prim p (← args.subst σ))
  | _, _, _, σ, .call name body args => do some (.call name body (← args.subst σ))
  | _, _, _, σ, .ok a => do some (.ok (← a.subst σ))
  | _, _, _, σ, .err a => do some (.err (← a.subst σ))
  | _, _, _, σ, .match_ (ε := ε) (α := α) s eE eO =>
    do some (.match_ (← s.subst σ) (← eE.subst (σ.lift ε)) (← eO.subst (σ.lift α)))
  | _, _, _, σ, .ext sig args => do some (.ext sig (← args.subst σ))
  | _, _, _, σ, .extMut sig args k => do some (.extMut sig (← args.subst σ) (← k.subst (σ.lift .u64)))
  | _, _, _, σ, .mk c args => do some (.mk c (← args.subst σ))
  | _, _, _, σ, .read p => do some (.read (← p.subst σ))
  | _, _, _, σ, .assign p a k => do some (.assign (← p.subst σ) (← a.subst σ) (← k.subst σ))
  | _, _, _, σ, .case (p := pt) (q := qt) s sp eP eQ =>
    do some (.case (← s.subst σ) sp (← eP.subst (σ.lift pt)) (← eQ.subst (σ.lift qt)))
  | _, _, _, σ, .put p i a k => do some (.put (← p.subst σ) (← i.subst σ) (← a.subst σ) (← k.subst σ))
  | _, _, _, σ, .take (t := t) (dflt := _) p i k =>
    do some (.take (← p.subst σ) (← i.subst σ) (← k.subst (σ.lift t)))
  | _, _, _, σ, .borrowShr (t := t) (u := u) p body k =>
    do some (.borrowShr (← p.subst σ) (← body.subst (σ.lift t)) (← k.subst (σ.lift u)))
  | _, _, _, σ, .borrowMut (t := t) (u := u) p body k =>
    do some (.borrowMut (← p.subst σ) (← body.subst (σ.lift t)) (← k.subst (σ.lift u)))
  | _, _, _, σ, .callRef (r := r) name req body args k =>
    do some (.callRef name req body (← args.subst σ) (← k.subst (σ.lift r)))
  | _, _, _, σ, .guard g => do some (.guard (← g.subst σ))
  | _, _, _, σ, .loop (s := s) n cs init c body k =>
    do some (.loop n (← cs.subst σ) (← init.subst σ) (← c.subst ((σ.lift s).lift .u64))
      (← body.subst ((σ.lift s).lift .u64)) (← k.subst (σ.lift s)))

/-! ## Soundness of the pieces -/

section
variable {Γ Δ : List Ty} {σ : Sub Γ Δ} {env : Env Γ} {env' : Env Δ}

theorem _root_.Millipede.Atom.subst_denote {t : Ty} {a : Atom Γ t} {a' : Atom Δ t}
    (h : a.subst σ = some a') (hr : σ.Rel env env') : a'.denote env' = a.denote env := by
  cases a with
  | var m => exact hr m a' h
  | lit v => cases h; rfl

theorem _root_.Millipede.Args.subst_denote {ps : List Ty} {as : Args Γ ps} {as' : Args Δ ps}
    (h : as.subst σ = some as') (hr : σ.Rel env env') : as'.denote env' = as.denote env := by
  induction as with
  | nil => cases h; rfl
  | cons a as ih =>
    simp only [Args.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a', ha, as'', has, rfl⟩ := h
    simp only [Args.denote, Atom.subst_denote ha hr, ih has]

theorem _root_.Millipede.Place.subst_get {t : Ty} {p : Place Γ t} {p' : Place Δ t}
    (h : p.subst σ = some p') (hr : σ.Rel env env') : p'.get env' = p.get env := by
  induction p <;>
    simp only [Place.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Place.get, Atom.subst_denote, Sub.Rel.get]

theorem _root_.Millipede.Place.subst_set (hσ : σ.Inj) {t : Ty} {p : Place Γ t} {p' : Place Δ t}
    (h : p.subst σ = some p') (hr : σ.Rel env env') (v : t.carrier) :
    σ.Rel (p.set env v) (p'.set env' v) := by
  induction p <;>
    simp only [Place.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Place.set, Place.subst_get, Atom.subst_denote, Sub.Rel.get, Sub.Rel.set]

theorem _root_.Millipede.Place.subst_ok {t : Ty} {p : Place Γ t} {p' : Place Δ t}
    (h : p.subst σ = some p') (hr : σ.Rel env env') : p'.ok env' ↔ p.ok env := by
  induction p <;>
    simp only [Place.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Place.ok, Place.subst_get, Atom.subst_denote, Sub.Rel.get]

theorem _root_.Millipede.Guard.subst_denote {g : Guard Γ} {g' : Guard Δ}
    (h : g.subst σ = some g') (hr : σ.Rel env env') : g'.denote env' = g.denote env := by
  cases g with
  | valid p hp =>
    simp only [Guard.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨p', hp', h⟩ := h
    split at h
    · cases h; simp only [Guard.denote]
      exact Bool.eq_iff_iff.mpr (by rw [Place.check_iff, Place.check_iff]; exact Place.subst_ok hp' hr)
    · cases h

theorem _root_.Millipede.RArgs.subst_denote {ps os : List Ty} {as : RArgs Γ ps os}
    {as' : RArgs Δ ps os} (h : as.subst σ = some as') (hr : σ.Rel env env') :
    as'.denote env' = as.denote env := by
  induction as <;>
    simp only [RArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.denote, Atom.subst_denote, Place.subst_get]

theorem _root_.Millipede.RArgs.subst_ok {ps os : List Ty} {as : RArgs Γ ps os}
    {as' : RArgs Δ ps os} (h : as.subst σ = some as') (hr : σ.Rel env env') :
    as'.ok env' ↔ as.ok env := by
  induction as <;>
    simp only [RArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.ok, Place.subst_ok]

theorem _root_.Millipede.RArgs.subst_writeBack (hσ : σ.Inj) {ps os : List Ty} {as : RArgs Γ ps os}
    {as' : RArgs Δ ps os} (h : as.subst σ = some as') (hr : σ.Rel env env')
    (vs : (Ty.tup os).carrier) : σ.Rel (as.writeBack env vs) (as'.writeBack env' vs) := by
  induction as generalizing env env' <;>
    simp only [RArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [RArgs.writeBack, Place.subst_set]

theorem _root_.Millipede.Buf.subst_denote {b : Buf Γ} {b' : Buf Δ} (h : b.subst σ = some b')
    (hr : σ.Rel env env') : b'.denote env' = b.denote env := by
  cases b <;>
    simp only [Buf.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Buf.denote, Place.subst_get, Atom.subst_denote]

theorem _root_.Millipede.EArgs.subst_call {sig : ExtSig} {as : EArgs Γ sig.params}
    {as' : EArgs Δ sig.params} (h : as.subst σ = some as') (hr : σ.Rel env env') :
    sig.call as' env' = sig.call as env := by
  suffices ∀ {ps : List ExtParam} {as : EArgs Γ ps} {as' : EArgs Δ ps}, as.subst σ = some as' →
      as'.words env' = as.words env ∧ as'.bytesIn env' = as.bytesIn env ∧
        as'.outCaps env' = as.outCaps env by
    obtain ⟨h1, h2, h3⟩ := this h; simp only [ExtSig.call, h1, h2, h3]
  intro ps as as' h
  induction as <;>
    simp only [EArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [EArgs.words, EArgs.bytesIn, EArgs.outCaps, Atom.subst_denote, Buf.subst_denote]

theorem _root_.Millipede.EArgs.subst_ok {ps : List ExtParam} {as : EArgs Γ ps} {as' : EArgs Δ ps}
    (h : as.subst σ = some as') (hr : σ.Rel env env') : as'.ok env' ↔ as.ok env := by
  induction as with
  | bufIn b as ih =>
    simp only [EArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b', hb, as'', has, rfl⟩ := h
    cases b <;> simp only [Buf.subst, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hb <;> grind [EArgs.ok, Place.subst_ok, Atom.subst_denote]
  | _ =>
    simp only [EArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [EArgs.ok, Place.subst_ok, Atom.subst_denote]

theorem _root_.Millipede.EArgs.subst_fill (hσ : σ.Inj) {ps : List ExtParam} {as : EArgs Γ ps}
    {as' : EArgs Δ ps} (h : as.subst σ = some as') (hr : σ.Rel env env') {env₀ : Env Γ}
    {env₀' : Env Δ} (hr₀ : σ.Rel env₀ env₀') (bss : List (List UInt8)) :
    σ.Rel (as.fill env env₀ bss) (as'.fill env' env₀' bss) := by
  induction as generalizing env₀ env₀' bss <;>
    simp only [EArgs.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [EArgs.fill, Place.subst_set, Place.subst_get, Atom.subst_denote]

theorem _root_.Millipede.Carry.subst_get {ts : List Ty} {cs : Carry Γ ts} {cs' : Carry Δ ts}
    (h : cs.subst σ = some cs') (hr : σ.Rel env env') : cs'.get env' = cs.get env := by
  induction cs <;>
    simp only [Carry.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Carry.get, Sub.Rel.get]

theorem _root_.Millipede.Carry.subst_set (hσ : σ.Inj) {ts : List Ty} {cs : Carry Γ ts}
    {cs' : Carry Δ ts} (h : cs.subst σ = some cs') (hr : σ.Rel env env')
    (vs : (Ty.tup ts).carrier) : σ.Rel (cs.set env vs) (cs'.set env' vs) := by
  induction cs generalizing env env' <;>
    simp only [Carry.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    grind [Carry.set, Sub.Rel.set]

end

end Millipede.Opt

namespace Millipede.Opt

/-- Substitution preserves the denotation. -/
theorem _root_.Millipede.Exp.subst_denote (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {Δ : List Ty} (σ : Sub Γ Δ) (e' : Exp Δ t), σ.Inj → e.subst σ = some e' →
      ∀ (env : Env Γ) (env' : Env Δ), σ.Rel env env' → ∀ w,
        e'.denote ω env' w = e.denote ω env w := by
  induction e <;> intro Δ σ e' hσ h env env' hr w <;>
    simp only [Exp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  case atom => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Atom.subst_denote ha hr]
  case let_ ih₁ ih₂ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, ih₁ _ _ hσ ha _ _ hr]
    exact ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _
  case ite ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, Atom.subst_denote hc hr, ih₁ _ _ hσ ha _ _ hr, ih₂ _ _ hσ hb _ _ hr]
  case prim => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Args.subst_denote ha hr]
  case call => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Args.subst_denote ha hr]
  case ok => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Atom.subst_denote ha hr]
  case err => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Atom.subst_denote ha hr]
  case match_ ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, Atom.subst_denote hc hr]
    congr 1 <;> funext x
    · exact ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _
    · exact ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _
  case ext => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, EArgs.subst_call ha hr]
  case extMut ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, EArgs.subst_call ha hr]
    exact ih _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (EArgs.subst_fill hσ ha hr hr _) _) _
  case mk => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Args.subst_denote ha hr]
  case read => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Place.subst_get ha hr]
  case assign ih =>
    obtain ⟨p, hp, a, ha, k, hk, rfl⟩ := h
    simp only [Exp.denote, ← Atom.subst_denote ha hr]
    exact ih _ _ hσ hk _ _ (Place.subst_set hσ hp hr _) _
  case case ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, Atom.subst_denote hc hr]
    congr 1 <;> funext x
    · exact ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _
    · exact ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _
  case put ih =>
    obtain ⟨p, hp, i, hi, a, ha, k, hk, rfl⟩ := h
    simp only [Exp.denote, ← Atom.subst_denote ha hr, ← Atom.subst_denote hi hr, ← Place.subst_get hp hr]
    exact ih _ _ hσ hk _ _ (Place.subst_set hσ hp hr _) _
  case take ih =>
    obtain ⟨p, hp, i, hi, k, hk, rfl⟩ := h
    simp only [Exp.denote, ← Atom.subst_denote hi hr, ← Place.subst_get hp hr]
    exact ih _ _ (hσ.lift _) hk _ _ (Sub.Rel.lift (Place.subst_set hσ hp hr _) _) _
  case borrowShr ih₁ ih₂ =>
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, Place.subst_get hp hr, ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _)]
    exact ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _
  case borrowMut ih₁ ih₂ =>
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, Place.subst_get hp hr, ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _)]
    exact ih₂ _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (Place.subst_set hσ hp hr _) _) _
  case callRef ih₁ ih₂ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.denote, RArgs.subst_denote ha hr]
    exact ih₂ _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (RArgs.subst_writeBack hσ ha hr _) _) _
  case guard => obtain ⟨a, ha, rfl⟩ := h; simp only [Exp.denote, Guard.subst_denote ha hr]
  case loop n cs₀ a₀ c₀ b₀ k₀ ihc ihb ihk =>
    obtain ⟨cs, hcs, a, ha, c, hc, b, hb, k, hk, rfl⟩ := h
    have hcf : (fun i (st : _ × _) w => c.denote ω (.cons i (.cons st.1 (cs.set env' st.2))) w) =
        (fun i st w => c₀.denote ω (.cons i (.cons st.1 (cs₀.set env st.2))) w) := by
      funext i st w
      exact ihc _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hc _ _ (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _
    have hbf : (fun i (st : _ × _) w => b.denote ω (.cons i (.cons st.1 (cs.set env' st.2))) w) =
        (fun i st w => b₀.denote ω (.cons i (.cons st.1 (cs₀.set env st.2))) w) := by
      funext i st w
      exact ihb _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hb _ _ (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _
    simp only [Exp.denote, hcf, hbf, Atom.subst_denote ha hr, Carry.subst_get hcs hr]
    exact ihk _ _ (hσ.lift _) hk _ _ (Sub.Rel.lift (Carry.subst_set hσ hcs hr _) _) _

end Millipede.Opt

namespace Millipede.Opt

/-- Weaker obligations per iteration give weaker loop obligations. -/
theorem loopSafe_imp {σ : Type} (cS bS cS' bS' : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (hc : ∀ i st w, cS i st w → cS' i st w) (hb : ∀ i st w, bS i st w → bS' i st w) :
    ∀ n i st w, loopSafe cS bS cond body n i st w → loopSafe cS' bS' cond body n i st w
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, _, ⟨h₁, h₂⟩ => ⟨hc _ _ _ h₁, fun h => ⟨hb _ _ _ (h₂ h).1,
      loopSafe_imp cS bS cS' bS' cond body hc hb n _ _ _ (h₂ h).2⟩⟩

/-- Substitution keeps the obligations. -/
theorem _root_.Millipede.Exp.subst_safe (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {Δ : List Ty} (σ : Sub Γ Δ) (e' : Exp Δ t), σ.Inj → e.subst σ = some e' →
      ∀ (env : Env Γ) (env' : Env Δ), σ.Rel env env' → ∀ w,
        e.safe ω env w → e'.safe ω env' w := by
  induction e <;> intro Δ σ e' hσ h env env' hr w hs <;>
    simp only [Exp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  case atom => obtain ⟨a, ha, rfl⟩ := h; trivial
  case let_ e₁ _ ih₁ ih₂ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Exp.subst_denote ω e₁ _ _ hσ ha _ _ hr] at hs ⊢
    exact ⟨ih₁ _ _ hσ ha _ _ hr _ hs.1, ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _ hs.2⟩
  case ite ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Atom.subst_denote hc hr] at hs ⊢
    exact ⟨fun h => ih₁ _ _ hσ ha _ _ hr _ (hs.1 h), fun h => ih₂ _ _ hσ hb _ _ hr _ (hs.2 h)⟩
  case prim => obtain ⟨a, ha, rfl⟩ := h; simpa only [Exp.safe, Args.subst_denote ha hr] using hs
  case call => obtain ⟨a, ha, rfl⟩ := h; simpa only [Exp.safe, Args.subst_denote ha hr] using hs
  case ok => obtain ⟨a, ha, rfl⟩ := h; trivial
  case err => obtain ⟨a, ha, rfl⟩ := h; trivial
  case match_ ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Atom.subst_denote hc hr] at hs ⊢
    exact ⟨fun x hx => ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _ (hs.1 x hx),
      fun x hx => ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _ (hs.2 x hx)⟩
  case ext => obtain ⟨a, ha, rfl⟩ := h; exact (EArgs.subst_ok ha hr).2 hs
  case extMut ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, EArgs.subst_call ha hr] at hs ⊢
    exact ⟨(EArgs.subst_ok ha hr).2 hs.1,
      ih _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (EArgs.subst_fill hσ ha hr hr _) _) _ hs.2⟩
  case mk => obtain ⟨a, ha, rfl⟩ := h; trivial
  case read => obtain ⟨a, ha, rfl⟩ := h; exact (Place.subst_ok ha hr).2 hs
  case assign ih =>
    obtain ⟨p, hp, a, ha, k, hk, rfl⟩ := h
    simp only [Exp.safe, ← Atom.subst_denote ha hr] at hs ⊢
    exact ⟨(Place.subst_ok hp hr).2 hs.1, ih _ _ hσ hk _ _ (Place.subst_set hσ hp hr _) _ hs.2⟩
  case case ih₁ ih₂ =>
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Atom.subst_denote hc hr] at hs ⊢
    exact ⟨fun x hx => ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _ (hs.1 x hx),
      fun x hx => ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _ (hs.2 x hx)⟩
  case put ih =>
    obtain ⟨p, hp, i, hi, a, ha, k, hk, rfl⟩ := h
    simp only [Exp.safe, ← Atom.subst_denote ha hr, ← Atom.subst_denote hi hr,
      ← Place.subst_get hp hr] at hs ⊢
    exact ⟨⟨(Place.subst_ok hp hr).2 hs.1.1, hs.1.2⟩,
      ih _ _ hσ hk _ _ (Place.subst_set hσ hp hr _) _ hs.2⟩
  case take ih =>
    obtain ⟨p, hp, i, hi, k, hk, rfl⟩ := h
    simp only [Exp.safe, ← Atom.subst_denote hi hr, ← Place.subst_get hp hr] at hs ⊢
    exact ⟨⟨(Place.subst_ok hp hr).2 hs.1.1, hs.1.2⟩,
      ih _ _ (hσ.lift _) hk _ _ (Sub.Rel.lift (Place.subst_set hσ hp hr _) _) _ hs.2⟩
  case borrowShr body₀ _ ih₁ ih₂ =>
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Place.subst_get hp hr,
      Exp.subst_denote ω body₀ _ _ (hσ.lift _) ha _ _ (hr.lift _)] at hs ⊢
    exact ⟨(Place.subst_ok hp hr).2 hs.1, ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _ hs.2.1,
      ih₂ _ _ (hσ.lift _) hb _ _ (hr.lift _) _ hs.2.2⟩
  case borrowMut body₀ _ ih₁ ih₂ =>
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, Place.subst_get hp hr,
      Exp.subst_denote ω body₀ _ _ (hσ.lift _) ha _ _ (hr.lift _)] at hs ⊢
    exact ⟨(Place.subst_ok hp hr).2 hs.1, ih₁ _ _ (hσ.lift _) ha _ _ (hr.lift _) _ hs.2.1,
      ih₂ _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (Place.subst_set hσ hp hr _) _) _ hs.2.2⟩
  case callRef ih₁ ih₂ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Exp.safe, RArgs.subst_denote ha hr] at hs ⊢
    exact ⟨(RArgs.subst_ok ha hr).2 hs.1, hs.2.1, hs.2.2.1,
      ih₂ _ _ (hσ.lift _) hb _ _ (Sub.Rel.lift (RArgs.subst_writeBack hσ ha hr _) _) _ hs.2.2.2⟩
  case guard => obtain ⟨a, ha, rfl⟩ := h; trivial
  case loop n cs₀ a₀ c₀ b₀ k₀ ihc ihb ihk =>
    obtain ⟨cs, hcs, a, ha, c, hc, b, hb, k, hk, rfl⟩ := h
    have hcf : (fun i (st : _ × _) w => c.denote ω (.cons i (.cons st.1 (cs.set env' st.2))) w) =
        (fun i st w => c₀.denote ω (.cons i (.cons st.1 (cs₀.set env st.2))) w) := by
      funext i st w; exact Exp.subst_denote ω c₀ _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hc _ _ (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _
    have hbf : (fun i (st : _ × _) w => b.denote ω (.cons i (.cons st.1 (cs.set env' st.2))) w) =
        (fun i st w => b₀.denote ω (.cons i (.cons st.1 (cs₀.set env st.2))) w) := by
      funext i st w; exact Exp.subst_denote ω b₀ _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hb _ _ (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _
    simp only [Exp.safe, hcf, hbf, Atom.subst_denote ha hr, Carry.subst_get hcs hr] at hs ⊢
    refine ⟨loopSafe_imp _ _ _ _ _ _ (fun i st w h => ?_) (fun i st w h => ?_) _ _ _ _ hs.1,
      ihk _ _ (hσ.lift _) hk _ _ (Sub.Rel.lift (Carry.subst_set hσ hcs hr _) _) _ hs.2⟩
    · exact ihc _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hc _ _
        (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _ h
    · exact ihb _ _ (Sub.Inj.lift (Sub.Inj.lift hσ _) _) hb _ _
        (Sub.Rel.lift (Sub.Rel.lift (Carry.subst_set hσ hcs hr st.2) _) _) _ h

end Millipede.Opt
