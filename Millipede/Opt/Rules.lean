import Millipede.Opt.Rewrite

/-!
# The Core passes

Each pass is a local rule, an `Opt.Pass` whose laws hold at one node, applied everywhere bottom-up
by `Pass.bu`. A rule that changes a binder's scope goes through `Exp.subst`, with one of two
substitutions. `Sub.under h` removes the innermost binder, mapping it to the atom `h`, or forbidding
it when `h` is `none`, and `Sub.args as` maps a callee's parameters to the argument atoms. The
passes are the following:

* `inline` replaces a call `f(as)` whose body reads its parameters only as atoms, and so never
  writes one, by the body with the arguments substituted and then folded, when that needs no more
  frame slots than the call.
* `fold` replaces `let x := v; k`, where `v` is a constant that can be evaluated now, by `k` with
  `x` replaced by the literal. It replaces an `if` on a literal by the branch taken, and a `match`
  or `case` on a literal by the arm taken with the payload substituted.
* `dce` replaces `let x := e; k` by `k` when `x` does not occur in `k` and `e` is pure, which
  means that it calls no extern and writes nothing. The obligations of `e` are dropped, which
  `safe` allows.
* `strength` replaces the unsigned `x / 2^k` and `x % 2^k` by `x >>> k` and `x &&& (2^k - 1)`.

The passes are described in doc/design/compiler.md.
-/

namespace Millipede.Opt

open Millipede

variable {Γ : List Ty}

/-! ## Three substitutions -/

/-- Removes the innermost binder, which becomes the atom `h` where it is read and must not occur
when `h` is `none`. It is never written, and the other variables move down by one. -/
def Sub.under {s : Ty} (h : Option (Atom Γ s)) : Sub (s :: Γ) Γ where
  f := fun {_} m => match m with
    | .here => h
    | .there m => some (.var m)
  g := fun {_} m => match m with
    | .here => none
    | .there m => some m
  fg := fun m x hx => by cases m with
    | here => cases hx
    | there m => cases hx; rfl

theorem Sub.under_rel {s : Ty} {h : Option (Atom Γ s)} {v : s.carrier} {env : Env Γ}
    (hv : ∀ a, h = some a → a.denote env = v) : (Sub.under h).Rel (.cons v env) env := by
  intro t m a ha
  cases m with
  | here => exact hv a ha
  | there m => cases ha; rfl

theorem Sub.under_inj {s : Ty} {h : Option (Atom Γ s)} (hh : ∀ y, h ≠ some (.var y)) :
    (Sub.under h).Inj := by
  intro t u m₁ m₂ x y h₁ h₂ he
  cases m₁ with
  | here => cases h₁
  | there m₁ =>
    cases h₁
    cases m₂ with
    | here => exact absurd h₂ (hh y)
    | there m₂ => cases h₂; simp only [Mem.idx] at he ⊢; omega

/-- The atom of argument `m`. -/
def _root_.Millipede.Args.nth : {ps : List Ty} → Args Γ ps → {t : Ty} → Mem t ps → Atom Γ t
  | _, .cons a _, _, .here => a
  | _, .cons _ as, _, .there m => as.nth m

theorem _root_.Millipede.Args.nth_denote {ps : List Ty} (as : Args Γ ps) {t : Ty} (m : Mem t ps)
    (env : Env Γ) : (as.nth m).denote env = (as.denote env).get m := by
  induction as with
  | nil => cases m
  | cons a as ih => cases m <;> simp [Args.nth, Args.denote, ih]

/-- Maps a callee's parameters to the argument atoms, none of which is written. -/
def Sub.args {ps : List Ty} (as : Args Γ ps) : Sub ps Γ where
  f := fun m => some (as.nth m)
  g := fun _ => none
  fg := fun _ _ h => by cases h

theorem Sub.args_rel {ps : List Ty} (as : Args Γ ps) (env : Env Γ) :
    (Sub.args as).Rel (as.denote env) env := by
  intro t m a ha; cases ha; exact Args.nth_denote as m env

theorem Sub.args_inj {ps : List Ty} (as : Args Γ ps) : (Sub.args as).Inj := by
  intro t u m₁ m₂ x y h₁; cases h₁

/-! ## Constants and purity -/

/-- The values of literal arguments. -/
def _root_.Millipede.Args.lits? : {ps : List Ty} → Args Γ ps → Option (Env ps)
  | _, .nil => some .nil
  | _, .cons (.lit v) as => (as.lits?).map (.cons v)
  | _, .cons (.var _) _ => none

theorem _root_.Millipede.Args.lits?_denote {ps : List Ty} {as : Args Γ ps} {vs : Env ps}
    (h : as.lits? = some vs) (env : Env Γ) : as.denote env = vs := by
  induction as with
  | nil => cases h; rfl
  | cons a as ih =>
    cases a with
    | var => cases h
    | lit v =>
      simp only [Args.lits?, Option.map_eq_some_iff] at h
      obtain ⟨vs', h', rfl⟩ := h
      simp only [Args.denote, Atom.denote, ih h']

/-- The value of a term that is a constant, which is a literal, a primitive applied to literals,
or `ok` or `err` of a literal. -/
def _root_.Millipede.Exp.litVal? : {Γ : List Ty} → {t : Ty} → Exp Γ t → Option t.carrier
  | _, _, .atom (.lit v) => some v
  | _, _, .prim p args => (args.lits?).map p.denote
  | _, _, .ok (.lit v) => some (.ok v)
  | _, _, .err (.lit v) => some (.error v)
  | _, _, _ => none

theorem _root_.Millipede.Exp.litVal?_denote {t : Ty} {e : Exp Γ t} {v : t.carrier}
    (h : e.litVal? = some v) (ω : Oracle) (env : Env Γ) (w : World) : e.denote ω env w = (v, w) := by
  cases e
  case atom a => cases a <;> simp only [Exp.litVal?, Option.some.injEq, reduceCtorEq] at h; subst h; rfl
  case prim p args =>
    simp only [Exp.litVal?, Option.map_eq_some_iff] at h
    obtain ⟨vs, hv, rfl⟩ := h
    simp only [Exp.denote, Args.lits?_denote hv]
  case ok a => cases a <;> simp only [Exp.litVal?, Option.some.injEq, reduceCtorEq] at h; subst h; rfl
  case err a => cases a <;> simp only [Exp.litVal?, Option.some.injEq, reduceCtorEq] at h; subst h; rfl
  all_goals simp [Exp.litVal?] at h

/-- A term that calls no extern, writes nothing, so its world is unchanged, and moves no linear
value, since every value it binds, reads, builds or passes may be copied. Dropping it therefore
keeps the borrow checker's accounting. -/
def _root_.Millipede.Exp.pure : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .atom (t := t) _ => !t.linear
  | _, _, .prim _ _ => true
  | _, _, .mk (ps := ps) (t := t) _ _ => !t.linear && ps.all (!·.linear)
  | _, _, .read (t := t) _ => !t.linear
  | _, _, .let_ (s := s) e₁ e₂ => !s.linear && e₁.pure && e₂.pure
  | _, _, .ite _ e₁ e₂ => e₁.pure && e₂.pure
  | _, _, .call (ps := ps) (r := r) _ body _ => !r.linear && ps.all (!·.linear) && body.pure
  | _, _, .case (t := t) _ _ eP eQ => !t.linear && eP.pure && eQ.pure
  | _, _, _ => false

theorem _root_.Millipede.Exp.pure_world (ω : Oracle) {t : Ty} (e : Exp Γ t) (h : e.pure = true) :
    ∀ (env : Env Γ) (w : World), (e.denote ω env w).2 = w := by
  induction e <;> intro env w <;> simp only [Exp.pure, Bool.and_eq_true, reduceCtorEq] at h
  case case s sp _ _ _ _ =>
    cases hs : sp.split (s.denote env) <;>
      simp only [Exp.denote, hs, Sum.elim_inl, Sum.elim_inr] <;> grind
  all_goals grind [Exp.denote]

/-! ## The rules -/

/-- The arm of a node that introduces a binder whose value is the constant `v`. It is the
continuation with `v` substituted, or `let x := v; k` when the substitution fails. -/
def instOr {s t : Ty} (v : s.carrier) (k : Exp (s :: Γ) t) : Exp Γ t :=
  (k.subst (Sub.under (some (.lit v)))).getD (.let_ (.atom (.lit v)) k)

theorem instOr_denote (ω : Oracle) {s t : Ty} (v : s.carrier) (k : Exp (s :: Γ) t) (env : Env Γ)
    (w : World) : (instOr v k).denote ω env w = k.denote ω (.cons v env) w := by
  unfold instOr
  cases h : k.subst (Sub.under (some (.lit v))) with
  | none => rfl
  | some k' =>
    exact Exp.subst_denote ω k _ _ (Sub.under_inj (by simp)) h _ _
      (Sub.under_rel (by intro a ha; cases ha; rfl)) w

theorem instOr_safe (ω : Oracle) {s t : Ty} (v : s.carrier) (k : Exp (s :: Γ) t) (env : Env Γ)
    (w : World) (hs : k.safe ω (.cons v env) w) : (instOr v k).safe ω env w := by
  unfold instOr
  cases h : k.subst (Sub.under (some (.lit v))) with
  | none => exact ⟨trivial, hs⟩
  | some k' =>
    exact Exp.subst_safe ω k _ _ (Sub.under_inj (by simp)) h _ _
      (Sub.under_rel (by intro a ha; cases ha; rfl)) w hs

/-- The `fold` rule at one node. -/
def foldRule : {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  | _, _, .ite (.lit b) e₁ e₂ => if b then e₁ else e₂
  | _, _, .let_ e₁ e₂ => match e₁.litVal? with
    | some v => instOr v e₂
    | none => .let_ e₁ e₂
  | _, _, .match_ (.lit r) eE eO => match r with
    | .error e => instOr e eE
    | .ok a => instOr a eO
  | _, _, .case (.lit v) sp eP eQ => match sp.split v with
    | .inl x => instOr x eP
    | .inr y => instOr y eQ
  | _, _, e => e

/-- Constant folding and propagation, with dead branches removed. It makes three sweeps, because a
constant substituted into a binder's scope is folded there by the next sweep. -/
def foldPass : Pass := (Pass.bu {
  name := "fold"
  run := foldRule
  denote := fun ω _ _ e env w => by
    unfold foldRule; split
    · rename_i b _ _; cases b <;> rfl
    · rename_i e₁ e₂
      split
      · rename_i v hv
        simp only [Exp.denote, Exp.litVal?_denote hv, instOr_denote]
      · rfl
    · rename_i r _ _; cases r <;> simp [Exp.denote, Atom.denote, instOr_denote]
    · rename_i v sp _ _; split <;> rename_i h <;> simp [Exp.denote, Atom.denote, instOr_denote, h]
    · rfl
  safe := fun ω _ _ e env w hs => by
    revert hs; unfold foldRule; split
    · rename_i b _ _; cases b <;> simp [Exp.safe, Atom.denote]
    · rename_i e₁ e₂
      split
      · rename_i v hv
        intro hs; simp only [Exp.safe, Exp.litVal?_denote hv] at hs
        exact instOr_safe ω v e₂ env w hs.2
      · exact id
    · rename_i r _ _; cases r <;> simp only [Exp.safe, Atom.denote] <;>
        intro hs <;> exact instOr_safe ω _ _ env w (by simp_all)
    · rename_i v sp _ _; split <;> rename_i h <;> simp only [Exp.safe, Atom.denote, h] <;>
        intro hs <;> exact instOr_safe ω _ _ env w (by simp_all)
    · exact id }).iter 2

/-- The `dce` rule at one node. -/
def dceRule : {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  | _, _, .let_ e₁ e₂ =>
    if e₁.pure then (e₂.subst (Sub.under none)).getD (.let_ e₁ e₂) else .let_ e₁ e₂
  | _, _, e => e

/-- Dead `let` elimination. -/
def dcePass : Pass := Pass.bu {
  name := "dce"
  run := dceRule
  denote := fun ω _ _ e env w => by
    unfold dceRule; split
    · rename_i e₁ e₂
      split
      · rename_i hp
        cases h : e₂.subst (Sub.under none) with
        | none => rfl
        | some k =>
          simp only [Option.getD_some, Exp.denote]
          rw [Exp.subst_denote ω e₂ _ _ (Sub.under_inj (by simp)) h _ _
            (Sub.under_rel (v := (e₁.denote ω env w).1) (by simp)) w]
          conv => rhs; rw [Exp.pure_world ω e₁ hp env w]
      · rfl
    · rfl
  safe := fun ω _ _ e env w hs => by
    revert hs; unfold dceRule; split
    · rename_i e₁ e₂
      split
      · rename_i hp
        intro hs
        cases h : e₂.subst (Sub.under none) with
        | none => exact hs
        | some k =>
          have := Exp.subst_safe ω e₂ _ _ (Sub.under_inj (by simp)) h _ _
            (Sub.under_rel (v := (e₁.denote ω env w).1) (env := env) (by simp)) _ hs.2
          rwa [Exp.pure_world ω e₁ hp env w] at this
      · exact id
    · exact id }

/-! ## Inlining -/

/-- The `inline` rule at one node, which gives the callee's body with the arguments substituted
and folded. It applies when that succeeds and needs no more frame slots than the call itself, so
neither the frame nor the stack bound grows, since the callee's frame is gone. -/
def inlineRule : {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  | _, _, .call (ps := ps) (r := r) n body args =>
    match body.subst (Sub.args args) with
    | some b =>
      let b' := foldPass.run b
      if b'.slotWords ≤ r.words + ctxWords ps then b' else .call n body args
    | none => .call n body args
  | _, _, e => e

/-- Inlining. -/
def inlinePass : Pass := Pass.bu {
  name := "inline"
  run := inlineRule
  denote := fun ω _ _ e env w => by
    unfold inlineRule; split
    · rename_i args body
      cases h : body.subst (Sub.args args) with
      | none => rfl
      | some b =>
        simp only
        split
        · rw [foldPass.denote]; simp only [Exp.denote]
          exact Exp.subst_denote ω body _ _ (Sub.args_inj args) h _ _ (Sub.args_rel args env) w
        · rfl
    · rfl
  safe := fun ω _ _ e env w hs => by
    revert hs; unfold inlineRule; split
    · rename_i args body
      cases h : body.subst (Sub.args args) with
      | none => exact id
      | some b =>
        simp only
        split
        · intro hs; apply foldPass.safe
          exact Exp.subst_safe ω body _ _ (Sub.args_inj args) h _ _ (Sub.args_rel args env) w hs
        · exact id
    · exact id }

/-! ## Strength reduction -/

theorem udiv_pow2 (x d k : UInt64) (hd : d.toNat = 2 ^ k.toNat) (hk : k.toNat < 64) :
    x / d = x >>> k := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow, hd]

theorem umod_pow2 (x d k : UInt64) (hd : d.toNat = 2 ^ k.toNat) : x % d = x &&& (d - 1) := by
  apply UInt64.toNat_inj.mp
  have h1 : (1 : UInt64) ≤ d := by
    rw [UInt64.le_iff_toNat_le]; simp [hd]; exact Nat.one_le_two_pow
  rw [UInt64.toNat_mod, UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ h1, hd]; simp

/-- The exponent `k` of a power of two `d = 2^k` with `k < 64`. -/
def log2? (d : UInt64) : Option UInt64 :=
  if d.toNat = 2 ^ d.toNat.log2 ∧ d.toNat.log2 < 64 then some (UInt64.ofNat d.toNat.log2) else none

theorem log2?_spec {d k : UInt64} (h : log2? d = some k) : d.toNat = 2 ^ k.toNat ∧ k.toNat < 64 := by
  unfold log2? at h; split at h
  · rename_i hc; cases h
    have : (UInt64.ofNat d.toNat.log2).toNat = d.toNat.log2 := by
      exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    rw [this]; exact hc
  · cases h

/-- Recognises the arguments `x, 2^k` and returns `x`, `2^k` and `k`. -/
def pow2Args? : Args Γ [.u64, .u64] → Option (Atom Γ .u64 × UInt64 × UInt64)
  | .cons x (.cons a .nil) => match a with
    | .lit d => (log2? d).map fun k => (x, d, k)
    | .var _ => none

theorem pow2Args?_spec {args : Args Γ [.u64, .u64]} {x : Atom Γ .u64} {d k : UInt64}
    (h : pow2Args? args = some (x, d, k)) :
    args = .cons x (.cons (.lit d) .nil) ∧ d.toNat = 2 ^ k.toNat ∧ k.toNat < 64 := by
  rcases args with _ | ⟨x', _ | ⟨a, _ | _⟩⟩
  cases a with
  | var => cases h
  | lit d' =>
    simp only [pow2Args?, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨k', hk, h1, h2, h3⟩ := h
    subst h1 h2 h3
    exact ⟨rfl, log2?_spec hk⟩

/-- The `strength` rule on a primitive. -/
def strengthPrim : {ps : List Ty} → {r : Ty} → Prim ps r → Args Γ ps → Exp Γ r
  | _, _, .udiv, args => match pow2Args? args with
    | some (x, _, k) => .prim .shr (.cons x (.cons (.lit k) .nil))
    | none => .prim .udiv args
  | _, _, .umod, args => match pow2Args? args with
    | some (x, d, _) => .prim .band (.cons x (.cons (.lit (d - 1)) .nil))
    | none => .prim .umod args
  | _, _, p, args => .prim p args

/-- The `strength` rule at one node. -/
def strengthRule : {Γ : List Ty} → {t : Ty} → Exp Γ t → Exp Γ t
  | _, _, .prim p args => strengthPrim p args
  | _, _, e => e

/-- Strength reduction. -/
def strengthPass : Pass := Pass.bu {
  name := "strength"
  run := strengthRule
  denote := fun ω _ _ e env w => by
    cases e <;> try rfl
    case prim args p =>
    cases p <;> try rfl
    all_goals
      simp only [strengthRule, strengthPrim]; split
      · rename_i x d k hk; obtain ⟨h1, hd, hk'⟩ := pow2Args?_spec hk
        subst h1
        simp only [Exp.denote, Prim.denote, Args.denote, Atom.denote, udiv_pow2 _ _ _ hd hk',
          umod_pow2 _ _ _ hd]
      · rfl
  safe := fun ω _ _ e env w hs => by
    cases e <;> try exact hs
    case prim args p =>
    cases p <;> try exact hs
    all_goals simp only [strengthRule, strengthPrim]; split <;> trivial }

end Millipede.Opt
