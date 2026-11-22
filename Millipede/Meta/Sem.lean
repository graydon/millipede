import Millipede.Core.Program
import Millipede.Core.Checked

/-!
# Monadic views of the denotation

`mp def f` defines the ordinary Lean function `f` as the simp-normal form of the meaning of
`f.exp`. This module provides the two monadic views that simp normalises, with one rewrite lemma
per constructor, so that the normal form is a plain `do` program that `vcgen` can reason about.

A pure term, in which no extern call occurs, callee bodies included, is viewed in `Id` through
`Exp.run`. `Exp.denote_of_isPure` shows that for such a term the full denotation is
`(e.run env, w)` for every oracle and world, so the world is untouched. Any other term is viewed
in `StateM World` through `Exp.denoteM ω`, which is definitionally `Exp.denote ω`, and its extern
calls appear as `World.callM ω c noreturn`.

Loops normalise to `forIn (upto n) init (fun i acc => …)` with an early `done` when the condition
fails, which is the form `vcgen` expects. This module does not import `Lean`.
-/

namespace Millipede

/-! ## Purity -/

/-- `true` if no extern call occurs in `e`, including inside the bodies of called functions. -/
def Exp.isPure : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .atom _ => true
  | _, _, .let_ e₁ e₂ => e₁.isPure && e₂.isPure
  | _, _, .ite _ e₁ e₂ => e₁.isPure && e₂.isPure
  | _, _, .prim _ _ => true
  | _, _, .call _ body _ => body.isPure
  | _, _, .ok _ => true
  | _, _, .err _ => true
  | _, _, .match_ _ eE eO => eE.isPure && eO.isPure
  | _, _, .ext _ _ => false
  | _, _, .extMut _ _ _ => false
  | _, _, .mk _ _ => true
  | _, _, .read _ => true
  | _, _, .assign _ _ k => k.isPure
  | _, _, .case _ _ eP eQ => eP.isPure && eQ.isPure
  | _, _, .put _ _ _ k => k.isPure
  | _, _, .take (dflt := _) _ _ k => k.isPure
  | _, _, .borrowShr _ body k => body.isPure && k.isPure
  | _, _, .borrowMut _ body k => body.isPure && k.isPure
  | _, _, .callRef _ _ body _ k => body.isPure && k.isPure
  | _, _, .guard _ => true
  | _, _, .loop _ _ _ c body k => c.isPure && body.isPure && k.isPure

/-! ## Pure evaluation -/

/-- The pure loop driver, which uses no world and mirrors `loopDenote`. It is structural on the
fuel. -/
def loopEval {σ : Type} (cond : UInt64 → σ → Bool) (body : UInt64 → σ → σ) :
    Nat → Nat → σ → σ
  | 0, _, acc => acc
  | n + 1, i, acc =>
    match cond (UInt64.ofNat i) acc with
    | false => acc
    | true => loopEval cond body n (i + 1) (body (UInt64.ofNat i) acc)

/-- Pure evaluation of a term. An extern call evaluates to `0`, which does not matter because none
occurs in a pure term, and on pure terms `Exp.eval` agrees with `Exp.denote`. -/
def Exp.eval : {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → t.carrier
  | _, _, .atom a, env => a.denote env
  | _, _, .let_ e₁ e₂, env => e₂.eval (.cons (e₁.eval env) env)
  | _, _, .ite c e₁ e₂, env =>
    match (c.denote env : Bool) with
    | true => e₁.eval env
    | false => e₂.eval env
  | _, _, .prim p args, env => p.denote (args.denote env)
  | _, _, .call _ body args, env => body.eval (args.denote env)
  | _, _, .ok a, env => Except.ok (a.denote env)
  | _, _, .err a, env => Except.error (a.denote env)
  | _, _, @Exp.match_ _ ε α _ s eE eO, env =>
    Except.elim (s.denote env : Except ε.carrier α.carrier)
      (fun e => eE.eval (.cons e env)) (fun a => eO.eval (.cons a env))
  | _, _, .ext _ _, _ => 0
  | _, _, .extMut _ _ k, env => k.eval (.cons 0 env)
  | _, _, .mk c args, env => c.build (args.denote env)
  | _, _, .read p, env => p.get env
  | _, _, .assign p a k, env => k.eval (p.set env (a.denote env))
  | _, _, .case s sp eP eQ, env =>
    Sum.elim (fun x => eP.eval (.cons x env)) (fun y => eQ.eval (.cons y env))
      (sp.split (s.denote env))
  | _, _, .put p i a k, env =>
    k.eval (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env))))
  | _, _, .take (dflt := _) p i k, env =>
    k.eval (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none)))
  | _, _, .borrowShr p body k, env => k.eval (.cons (body.eval (.cons (p.get env) env)) env)
  | _, _, .borrowMut p body k, env =>
    k.eval (.cons (body.eval (.cons (p.get env) env)).1
      (p.set env (body.eval (.cons (p.get env) env)).2))
  | _, _, .callRef _ _ body args k, env =>
    k.eval (.cons (body.eval (args.denote env)).1 (args.writeBack env (body.eval (args.denote env)).2))
  | _, _, .guard g, env => if g.denote env then .ok () else .error ()
  | _, _, .loop n cs init c body k, env =>
    let r := loopEval (fun i st => c.eval (.cons i (.cons st.1 (cs.set env st.2))))
      (fun i st => body.eval (.cons i (.cons st.1 (cs.set env st.2)))) n 0
      (init.denote env, cs.get env)
    k.eval (.cons r.1 (cs.set env r.2))

/-- Pure evaluation as an `Id` program. The generated function `f` of a pure `mp def` is the
simp-normal form of this view. -/
def Exp.run {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) : Id t.carrier :=
  pure (e.eval env)

theorem loopDenote_of_pure {σ : Type} (ω : Oracle) (cond : UInt64 → σ → World → Bool × World)
    (body : UInt64 → σ → World → σ × World) (condP : UInt64 → σ → Bool) (bodyP : UInt64 → σ → σ)
    (hc : ∀ i a w, cond i a w = (condP i a, w)) (hb : ∀ i a w, body i a w = (bodyP i a, w)) :
    ∀ n i acc w, loopDenote cond body n i acc w = (loopEval condP bodyP n i acc, w) := by
  have _ := ω
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro i acc w
    simp only [loopDenote, loopEval, hc, hb]
    cases condP (UInt64.ofNat i) acc <;> simp [ih]

/-- On a pure term the denotation leaves the world unchanged and its value is `Exp.eval`, for
every oracle and world. -/
theorem Exp.denote_of_isPure (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    e.isPure = true → ∀ (env : Env Γ) (w : World), e.denote ω env w = (e.eval env, w) := by
  induction e with
  | atom => intro _ _ _; rfl
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval, ih₁ h.1, ih₂ h.2]
  | ite c e₁ e₂ ih₁ ih₂ =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval]
    cases (c.denote env : Bool) <;> simp [ih₁ h.1, ih₂ h.2]
  | prim => intro _ _ _; rfl
  | call _ body args ih => intro h env w; exact ih h _ _
  | ok => intro _ _ _; rfl
  | err => intro _ _ _; rfl
  | match_ s eE eO ihE ihO =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval]
    cases (s.denote env : Except _ _) <;> simp [ihE h.1, ihO h.2]
  | ext => intro h; simp [Exp.isPure] at h
  | extMut => intro h; simp [Exp.isPure] at h
  | mk => intro _ _ _; rfl
  | read => intro _ _ _; rfl
  | assign p a k ih => intro h env w; exact ih h _ _
  | case s sp eP eQ ihP ihQ =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval]
    cases sp.split (s.denote env) <;> simp [ihP h.1, ihQ h.2]
  | put p i a k ih => intro h env w; exact ih h _ _
  | take p i k ih => intro h env w; exact ih h _ _
  | borrowShr p body k ihb ihk =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval, ihb h.1, ihk h.2]
  | borrowMut p body k ihb ihk =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval, ihb h.1, ihk h.2]
  | callRef _ _ body args k ihb ihk =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval, ihb h.1, ihk h.2]
  | guard => intro _ _ _; rfl
  | loop n cs init c body k ihc ihb ihk =>
    intro h env w
    simp only [Exp.isPure, Bool.and_eq_true] at h
    simp only [Exp.denote, Exp.eval]
    rw [loopDenote_of_pure ω _ _ _ _ (fun i a w => ihc h.1.1 (.cons i (.cons a.1 (cs.set env a.2))) w)
      (fun i a w => ihb h.1.2 (.cons i (.cons a.1 (cs.set env a.2))) w)]
    exact ihk h.2 _ _

/-! ### Rewrite lemmas for `Exp.run`, the simp set of `mp def` for pure terms -/

theorem Exp.run_atom {Γ : List Ty} {t : Ty} (a : Atom Γ t) (env : Env Γ) :
    (Exp.atom a).run env = pure (a.denote env) := rfl

theorem Exp.run_let {Γ : List Ty} {s t : Ty} (e₁ : Exp Γ s) (e₂ : Exp (s :: Γ) t) (env : Env Γ) :
    (Exp.let_ e₁ e₂).run env = (do let v ← e₁.run env; e₂.run (.cons v env)) := rfl

theorem Exp.run_ite {Γ : List Ty} {t : Ty} (c : Atom Γ .bool) (e₁ e₂ : Exp Γ t) (env : Env Γ) :
    (Exp.ite c e₁ e₂).run env =
      if (c.denote env : Bool) = true then e₁.run env else e₂.run env := by
  simp only [Exp.run, Exp.eval]
  cases (c.denote env : Bool) <;> rfl

theorem Exp.run_prim {Γ ps : List Ty} {r : Ty} (p : Prim ps r) (args : Args Γ ps) (env : Env Γ) :
    (Exp.prim p args).run env = pure (p.denote (args.denote env)) := rfl

universe u v

/-! ## The counters of a loop

A loop of the normal form iterates over `upto n`, the counters `0, …, n - 1`. In the logic
`forIn (upto n)` is `forIn (List.range n)` by `rfl`, and `vcgen` sees `List.range n` through
`Spec.forIn_upto`. Compiled code counts instead of building the list, so a loop whose static cap
is near `2^64` and that stops early at run time runs in constant memory. -/

/-- The counters `0, …, bound - 1` of a loop, printed as `upto n`. -/
structure Upto where
  bound : Nat

/-- `upto n`, the counters `0, …, n - 1`. -/
abbrev upto (n : Nat) : Upto := ⟨n⟩

/-- The compiled loop over `upto n`, which counts from `i` without building a list. -/
def Upto.loopImpl {m : Type u → Type v} [Monad m] {β : Type u} (n : Nat)
    (f : Nat → β → m (ForInStep β)) (i : Nat) (b : β) : m β :=
  if i < n then do
    match ← f i b with
    | .done b => pure b
    | .yield b => Upto.loopImpl n f (i + 1) b
  else pure b
termination_by n - i

def Upto.forInImpl {m : Type u → Type v} [Monad m] {β : Type u} (r : Upto) (init : β)
    (f : Nat → β → m (ForInStep β)) : m β :=
  Upto.loopImpl r.bound f 0 init

/-- Iterating over `upto n` is iterating over `List.range n`. Compiled code uses
`Upto.forInImpl` instead. -/
@[implemented_by Upto.forInImpl]
def Upto.forIn {m : Type u → Type v} [Monad m] {β : Type u} (r : Upto) (init : β)
    (f : Nat → β → m (ForInStep β)) : m β :=
  ForIn.forIn (List.range r.bound) init f

instance {m : Type u → Type v} [Monad m] : ForIn m Upto Nat where
  forIn r init f := Upto.forIn r init f

theorem forIn_upto {m : Type u → Type v} [Monad m] {β : Type u} (n : Nat) (init : β)
    (f : Nat → β → m (ForInStep β)) : forIn (upto n) init f = forIn (List.range n) init f := rfl

theorem loopEval_forIn {σ : Type} (cond : UInt64 → σ → Bool) (body : UInt64 → σ → σ) :
    ∀ n i acc, (pure (loopEval cond body n i acc) : Id σ) =
      forIn (List.range' i n) acc (fun j a => do
        let b ← (pure (cond (UInt64.ofNat j) a) : Id Bool)
        if b = true then do
          let a' ← (pure (body (UInt64.ofNat j) a) : Id σ)
          pure (ForInStep.yield a')
        else pure (ForInStep.done a)) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro i acc
    simp only [loopEval, List.range'_succ, List.forIn_cons]
    cases cond (UInt64.ofNat i) acc
    · rfl
    · simp only [pure_bind, ite_true]
      exact ih _ _


/-- A loop writing carried variables is `forIn` over the accumulator and the carried variables'
values, followed by the continuation with the final accumulator and the carried values stored. -/
theorem Exp.run_loop {Γ ts : List Ty} {s u : Ty} (n : Nat) (cs : Carry Γ ts) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts)))
    (k : Exp (s :: Γ) u) (env : Env Γ) :
    (Exp.loop n cs init c body k).run env = (do
      let r ← forIn (upto n) ((init.denote env, cs.get env) : s.carrier × (Ty.tup ts).carrier)
        (fun i st => do
          let b ← c.run (.cons (UInt64.ofNat i) (.cons st.1 (cs.set env st.2)))
          if b = true then do
            let a ← body.run (.cons (UInt64.ofNat i) (.cons st.1 (cs.set env st.2)))
            pure (ForInStep.yield a)
          else pure (ForInStep.done st))
      k.run (.cons r.1 (cs.set env r.2))) := by
  rw [forIn_upto]
  rw [List.range_eq_range']; simp only [Exp.run]
  rw [← loopEval_forIn (fun i st => c.eval (.cons i (.cons st.1 (cs.set env st.2))))
    (fun i st => body.eval (.cons i (.cons st.1 (cs.set env st.2))))]
  rfl

/-- The loop driver on an accumulator paired with the empty carried tuple, as in `Exp.loop0`, is
the driver on the accumulator alone. -/
theorem loopEval_unit {σ : Type} (cond : UInt64 → σ × Unit → Bool)
    (body : UInt64 → σ × Unit → σ × Unit) : ∀ n i a,
    loopEval cond body n i (a, ()) =
      (loopEval (fun j x => cond j (x, ())) (fun j x => (body j (x, ())).1) n i a, ()) := by
  intro n; induction n <;> intro i a
  case zero => rfl
  case succ n ih =>
    simp only [loopEval]; cases cond (UInt64.ofNat i) (a, ()) <;> simp only [← ih]

/-- `map` into the branches of an `if`. The normal form pushes the projection of a loop body that
carries nothing to the body's tails. -/
theorem map_ite {m : Type → Type} [Functor m] {α β : Type} (f : α → β) (c : Prop) [Decidable c]
    (x y : m α) : f <$> (if c then x else y) = if c then f <$> x else f <$> y := by
  split <;> rfl

/-- A loop carrying nothing, `Exp.loop0`, is `forIn` over the accumulator alone. This is the
normal form of a plain loop, in which the body's handed-back `(acc', ())` is projected at its
tails. -/
theorem Exp.run_loop_nil {Γ : List Ty} {s u : Ty} (n : Nat) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) (.pair s (.tup [])))
    (k : Exp (s :: Γ) u) (env : Env Γ) :
    (Exp.loop n .nil init c body k).run env = (do
      let r ← forIn (upto n) (init.denote env) (fun i acc => do
          let b ← c.run (.cons (UInt64.ofNat i) (.cons acc env))
          if b = true then do
            let a ← Prod.fst <$> body.run (.cons (UInt64.ofNat i) (.cons acc env))
            pure (ForInStep.yield a)
          else pure (ForInStep.done acc))
      k.run (.cons r env)) := by
  rw [forIn_upto]
  have h := loopEval_forIn (fun i a => c.eval (.cons i (.cons a env)))
    (fun i a => (body.eval (.cons i (.cons a env))).1) n 0 (init.denote env)
  simp only [pure_bind] at h
  simp only [Exp.run, Exp.eval, Carry.get, Carry.set, pure_bind, List.range_eq_range']
  erw [loopEval_unit, ← h]; rfl

theorem Exp.run_call {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r)
    (args : Args Γ ps) (env : Env Γ) :
    (Exp.call name body args).run env = body.run (args.denote env) := rfl

theorem Exp.run_ok {Γ : List Ty} {ε α : Ty} (a : Atom Γ α) (env : Env Γ) :
    (Exp.ok (ε := ε) a).run env = pure (Except.ok (a.denote env)) := rfl

theorem Exp.run_err {Γ : List Ty} {ε α : Ty} (a : Atom Γ ε) (env : Env Γ) :
    (Exp.err (α := α) a).run env = pure (Except.error (a.denote env)) := rfl

theorem Exp.run_match {Γ : List Ty} {ε α t : Ty} (s : Atom Γ (.result ε α))
    (eE : Exp (ε :: Γ) t) (eO : Exp (α :: Γ) t) (env : Env Γ) :
    (Exp.match_ s eE eO).run env =
      match (s.denote env : Except ε.carrier α.carrier) with
      | .error e => eE.run (.cons e env)
      | .ok a => eO.run (.cons a env) := by
  simp only [Exp.run, Exp.eval]
  cases (s.denote env : Except ε.carrier α.carrier) <;> rfl

theorem Exp.run_mk {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) (env : Env Γ) :
    (Exp.mk c args).run env = pure (c.build (args.denote env)) := rfl

theorem Exp.run_read {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) :
    (Exp.read p).run env = pure (p.get env) := rfl

theorem Exp.run_assign {Γ : List Ty} {t u : Ty} (p : Place Γ t) (a : Atom Γ t) (k : Exp Γ u)
    (env : Env Γ) : (Exp.assign p a k).run env = k.run (p.set env (a.denote env)) := rfl

theorem Exp.run_case {Γ : List Ty} {t p q u : Ty} (s : Atom Γ t) (sp : Split t p q)
    (eP : Exp (p :: Γ) u) (eQ : Exp (q :: Γ) u) (env : Env Γ) :
    (Exp.case s sp eP eQ).run env =
      Sum.elim (fun x => eP.run (.cons x env)) (fun y => eQ.run (.cons y env))
        (sp.split (s.denote env)) := by
  simp only [Exp.run, Exp.eval]
  cases sp.split (s.denote env) <;> rfl

theorem Exp.run_put {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty} (p : Place Γ (.slots t n))
    (i : Atom Γ .u64) (a : Atom Γ t) (k : Exp Γ u) (env : Env Γ) :
    (Exp.put p i a k).run env =
      k.run (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) :=
  rfl

theorem Exp.run_take {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty} [Inhabited t.carrier]
    (p : Place Γ (.slots t n)) (i : Atom Γ .u64) (k : Exp (t :: Γ) u) (env : Env Γ) :
    (Exp.take p i k).run env =
      k.run (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
        (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) := rfl

theorem Exp.run_borrowShr {Γ : List Ty} {t u v : Ty} (p : Place Γ t) (body : Exp (t :: Γ) u)
    (k : Exp (u :: Γ) v) (env : Env Γ) :
    (Exp.borrowShr p body k).run env =
      (do let r ← body.run (.cons (p.get env) env); k.run (.cons r env)) := rfl

theorem Exp.run_borrowMut {Γ : List Ty} {t u v : Ty} (p : Place Γ t)
    (body : Exp (t :: Γ) (.pair u t)) (k : Exp (u :: Γ) v) (env : Env Γ) :
    (Exp.borrowMut p body k).run env =
      (do let r ← body.run (.cons (p.get env) env); k.run (.cons r.1 (p.set env r.2))) := rfl

theorem Exp.run_callRef {Γ ps os : List Ty} {r u : Ty} (name : String) (req : Env ps → Prop)
    (body : Exp ps (.pair r (.tup os))) (args : RArgs Γ ps os) (k : Exp (r :: Γ) u)
    (env : Env Γ) :
    (Exp.callRef name req body args k).run env =
      (do let x ← body.run (args.denote env); k.run (.cons x.1 (args.writeBack env x.2))) := rfl

theorem Exp.run_guard {Γ : List Ty} (g : Guard Γ) (env : Env Γ) :
    (Exp.guard g).run env = pure (if g.denote env then .ok () else .error ()) := rfl

/-! ## Effectful terms in `StateM World` -/

/-- An extern call as a `StateM World` action, built from `World.call`. -/
def World.callM (ω : Oracle) (c : Call) (noreturn : Bool) : StateM World UInt64 :=
  fun w => w.call ω c noreturn

/-- The raw answer to an extern call as a `StateM World` action, built from `World.ask`. -/
def World.askM (ω : Oracle) (c : Call) (noreturn : Bool) : StateM World Reply :=
  fun w => w.ask ω c noreturn

/-- The denotation as a `StateM World` program, which is definitionally `Exp.denote ω e env`. -/
def Exp.denoteM (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) :
    StateM World t.carrier :=
  fun w => e.denote ω env w

/-- The denotation at a world from an equation for the `StateM World` view. `mp def` proves
`f.exp_denote` with it, so that the kernel never compares `f`'s body with the unfolded view. -/
theorem Exp.denote_of_denoteM_eq (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ)
    (m : StateM World t.carrier) (h : e.denoteM ω env = m) (w : World) :
    e.denote ω env w = m.run w := by
  rw [← h]; rfl

/-- A pure term, viewed in `StateM World`, is `pure` of its `Id` view. -/
theorem Exp.denoteM_of_isPure (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (h : e.isPure = true) (env : Env Γ) : e.denoteM ω env = pure (e.run env).run := by
  funext w
  exact e.denote_of_isPure ω h env w

theorem Exp.denoteM_atom (ω : Oracle) {Γ : List Ty} {t : Ty} (a : Atom Γ t) (env : Env Γ) :
    (Exp.atom a).denoteM ω env = pure (a.denote env) := rfl

theorem Exp.denoteM_let (ω : Oracle) {Γ : List Ty} {s t : Ty} (e₁ : Exp Γ s)
    (e₂ : Exp (s :: Γ) t) (env : Env Γ) :
    (Exp.let_ e₁ e₂).denoteM ω env =
      (do let v ← e₁.denoteM ω env; e₂.denoteM ω (.cons v env)) := rfl

theorem Exp.denoteM_ite (ω : Oracle) {Γ : List Ty} {t : Ty} (c : Atom Γ .bool) (e₁ e₂ : Exp Γ t)
    (env : Env Γ) :
    (Exp.ite c e₁ e₂).denoteM ω env =
      if (c.denote env : Bool) = true then e₁.denoteM ω env else e₂.denoteM ω env := by
  funext w
  simp only [Exp.denoteM, Exp.denote]
  cases (c.denote env : Bool) <;> rfl

theorem Exp.denoteM_prim (ω : Oracle) {Γ ps : List Ty} {r : Ty} (p : Prim ps r)
    (args : Args Γ ps) (env : Env Γ) :
    (Exp.prim p args).denoteM ω env = pure (p.denote (args.denote env)) := rfl

theorem loopDenote_forIn {σ : Type} (cond : UInt64 → σ → StateM World Bool)
    (body : UInt64 → σ → StateM World σ) :
    ∀ n i acc, (fun w => loopDenote (fun j a w => cond j a w) (fun j a w => body j a w)
        n i acc w : StateM World σ) =
      forIn (List.range' i n) acc (fun j a => do
        let b ← cond (UInt64.ofNat j) a
        if b = true then do
          let a' ← body (UInt64.ofNat j) a
          pure (ForInStep.yield a')
        else pure (ForInStep.done a)) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro i acc
    simp only [List.range'_succ, List.forIn_cons, ← ih]
    funext w
    simp only [loopDenote, bind, StateT.bind, pure]
    rcases cond (UInt64.ofNat i) acc w with ⟨b, w'⟩
    cases b <;> rfl


/-- A loop writing carried variables, in `StateM World`, as `Exp.run_loop` states it in `Id`. -/
theorem Exp.denoteM_loop (ω : Oracle) {Γ ts : List Ty} {s u : Ty} (n : Nat) (cs : Carry Γ ts)
    (init : Atom Γ s) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) (env : Env Γ) :
    (Exp.loop n cs init c body k).denoteM ω env = (do
      let r ← forIn (upto n) ((init.denote env, cs.get env) : s.carrier × (Ty.tup ts).carrier)
        (fun i st => do
          let b ← c.denoteM ω (.cons (UInt64.ofNat i) (.cons st.1 (cs.set env st.2)))
          if b = true then do
            let a ← body.denoteM ω (.cons (UInt64.ofNat i) (.cons st.1 (cs.set env st.2)))
            pure (ForInStep.yield a)
          else pure (ForInStep.done st))
      k.denoteM ω (.cons r.1 (cs.set env r.2))) := by
  rw [forIn_upto]
  rw [List.range_eq_range', ← loopDenote_forIn (fun i a => c.denoteM ω (.cons i (.cons a.1 (cs.set env a.2))))
    (fun i a => body.denoteM ω (.cons i (.cons a.1 (cs.set env a.2)))) n 0 _]
  rfl

/-- A loop carrying nothing, in `StateM World`, as `Exp.run_loop_nil` states it in `Id`. -/
theorem Exp.denoteM_loop_nil (ω : Oracle) {Γ : List Ty} {s u : Ty} (n : Nat) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) (.pair s (.tup [])))
    (k : Exp (s :: Γ) u) (env : Env Γ) :
    (Exp.loop n .nil init c body k).denoteM ω env = (do
      let r ← forIn (upto n) (init.denote env) (fun i acc => do
          let b ← c.denoteM ω (.cons (UInt64.ofNat i) (.cons acc env))
          if b = true then do
            let a ← Prod.fst <$> body.denoteM ω (.cons (UInt64.ofNat i) (.cons acc env))
            pure (ForInStep.yield a)
          else pure (ForInStep.done acc))
      k.denoteM ω (.cons r env)) := by
  rw [forIn_upto]
  have h := loopDenote_forIn (fun i a => c.denoteM ω (.cons i (.cons a env)))
    (fun i a => Prod.fst <$> body.denoteM ω (.cons i (.cons a env))) n 0 (init.denote env)
  rw [List.range_eq_range', ← h]
  funext w
  simp only [Exp.denoteM, Exp.denote, Carry.get, Carry.set]
  erw [loopDenote_unit]; rfl

theorem Exp.denoteM_call (ω : Oracle) {Γ ps : List Ty} {r : Ty} (name : String) (body : Exp ps r)
    (args : Args Γ ps) (env : Env Γ) :
    (Exp.call name body args).denoteM ω env = body.denoteM ω (args.denote env) := rfl

theorem Exp.denoteM_ok (ω : Oracle) {Γ : List Ty} {ε α : Ty} (a : Atom Γ α) (env : Env Γ) :
    (Exp.ok (ε := ε) a).denoteM ω env = pure (Except.ok (a.denote env)) := rfl

theorem Exp.denoteM_err (ω : Oracle) {Γ : List Ty} {ε α : Ty} (a : Atom Γ ε) (env : Env Γ) :
    (Exp.err (α := α) a).denoteM ω env = pure (Except.error (a.denote env)) := rfl

theorem Exp.denoteM_match (ω : Oracle) {Γ : List Ty} {ε α t : Ty} (s : Atom Γ (.result ε α))
    (eE : Exp (ε :: Γ) t) (eO : Exp (α :: Γ) t) (env : Env Γ) :
    (Exp.match_ s eE eO).denoteM ω env =
      match (s.denote env : Except ε.carrier α.carrier) with
      | .error e => eE.denoteM ω (.cons e env)
      | .ok a => eO.denoteM ω (.cons a env) := by
  funext w
  simp only [Exp.denoteM, Exp.denote]
  cases (s.denote env : Except ε.carrier α.carrier) <;> rfl

theorem Exp.denoteM_ext (ω : Oracle) {Γ : List Ty} (sig : ExtSig) (args : EArgs Γ sig.params)
    (env : Env Γ) :
    (Exp.ext sig args).denoteM ω env = World.callM ω (sig.call args env) sig.noreturn := rfl

theorem Exp.denoteM_extMut (ω : Oracle) {Γ : List Ty} {u : Ty} (sig : ExtSig)
    (args : EArgs Γ sig.params) (k : Exp (.u64 :: Γ) u) (env : Env Γ) :
    (Exp.extMut sig args k).denoteM ω env = (do
      let r ← World.askM ω (sig.call args env) sig.noreturn
      k.denoteM ω (.cons r.result
        (args.fill env env (fitOut (sig.call args env).outCaps r.bytesOut)))) := rfl

theorem Exp.denoteM_mk (ω : Oracle) {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps)
    (env : Env Γ) : (Exp.mk c args).denoteM ω env = pure (c.build (args.denote env)) := rfl

theorem Exp.denoteM_read (ω : Oracle) {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ) :
    (Exp.read p).denoteM ω env = pure (p.get env) := rfl

theorem Exp.denoteM_assign (ω : Oracle) {Γ : List Ty} {t u : Ty} (p : Place Γ t) (a : Atom Γ t)
    (k : Exp Γ u) (env : Env Γ) :
    (Exp.assign p a k).denoteM ω env = k.denoteM ω (p.set env (a.denote env)) := rfl

theorem Exp.denoteM_case (ω : Oracle) {Γ : List Ty} {t p q u : Ty} (s : Atom Γ t)
    (sp : Split t p q) (eP : Exp (p :: Γ) u) (eQ : Exp (q :: Γ) u) (env : Env Γ) :
    (Exp.case s sp eP eQ).denoteM ω env =
      Sum.elim (fun x => eP.denoteM ω (.cons x env)) (fun y => eQ.denoteM ω (.cons y env))
        (sp.split (s.denote env)) := by
  funext w
  simp only [Exp.denoteM, Exp.denote]
  cases sp.split (s.denote env) <;> rfl

theorem Exp.denoteM_put (ω : Oracle) {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty}
    (p : Place Γ (.slots t n)) (i : Atom Γ .u64) (a : Atom Γ t) (k : Exp Γ u) (env : Env Γ) :
    (Exp.put p i a k).denoteM ω env =
      k.denoteM ω
        (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) := rfl

theorem Exp.denoteM_take (ω : Oracle) {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty}
    [Inhabited t.carrier] (p : Place Γ (.slots t n)) (i : Atom Γ .u64) (k : Exp (t :: Γ) u)
    (env : Env Γ) :
    (Exp.take p i k).denoteM ω env =
      k.denoteM ω (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
        (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) := rfl

theorem Exp.denoteM_borrowShr (ω : Oracle) {Γ : List Ty} {t u v : Ty} (p : Place Γ t)
    (body : Exp (t :: Γ) u) (k : Exp (u :: Γ) v) (env : Env Γ) :
    (Exp.borrowShr p body k).denoteM ω env =
      (do let r ← body.denoteM ω (.cons (p.get env) env); k.denoteM ω (.cons r env)) := rfl

theorem Exp.denoteM_borrowMut (ω : Oracle) {Γ : List Ty} {t u v : Ty} (p : Place Γ t)
    (body : Exp (t :: Γ) (.pair u t)) (k : Exp (u :: Γ) v) (env : Env Γ) :
    (Exp.borrowMut p body k).denoteM ω env =
      (do let r ← body.denoteM ω (.cons (p.get env) env)
          k.denoteM ω (.cons r.1 (p.set env r.2))) := rfl

theorem Exp.denoteM_callRef (ω : Oracle) {Γ ps os : List Ty} {r u : Ty} (name : String)
    (req : Env ps → Prop) (body : Exp ps (.pair r (.tup os))) (args : RArgs Γ ps os)
    (k : Exp (r :: Γ) u) (env : Env Γ) :
    (Exp.callRef name req body args k).denoteM ω env =
      (do let x ← body.denoteM ω (args.denote env)
          k.denoteM ω (.cons x.1 (args.writeBack env x.2))) := rfl

theorem Exp.denoteM_guard (ω : Oracle) {Γ : List Ty} (g : Guard Γ) (env : Env Γ) :
    (Exp.guard g).denoteM ω env = pure (if g.denote env then .ok () else .error ()) := rfl

/-! ## Constructors used by `mp def` -/

/-- The pair `(a, b)`, which also builds the tuples that a function with `mut` parameters hands
back. -/
def Ctor.pairMk (a b : Ty) : Ctor [a, b] (.pair a b) :=
  ⟨"pair", .struct, fun env => (env.get .here, env.get (.there .here)), some ⟨Flat.CtorLaw.pair a b⟩,
    some ⟨fun | .cons _ (.cons _ .nil) => rfl⟩⟩

@[simp] theorem Ctor.pairMk_build (a b : Ty) (x : a.carrier) (y : b.carrier) :
    (Ctor.pairMk a b).build (.cons x (.cons y .nil)) = (x, y) := rfl

/-- The elements of an environment of `n` values of one type, in order. -/
def Env.elems {t : Ty} : (n : Nat) → Env (List.replicate n t) → List t.carrier
  | 0, _ => []
  | n + 1, .cons x env => x :: Env.elems n env

@[simp] theorem Env.elems_length {t : Ty} : (n : Nat) → (env : Env (List.replicate n t)) →
    (Env.elems n env).length = n
  | 0, _ => rfl
  | n + 1, .cons _ env => by simp [Env.elems, Env.elems_length n env]

namespace Flat

theorem placements_replicate (t : Ty) (f : Nat → Nat) :
    ∀ (m : Nat) (L : List Nat), L.length = m →
      placements (List.replicate m t) (L.map fun j => [f j]) = L.map fun j => (f j, t.size)
  | 0, [], _ => by simp [placements]
  | m + 1, l :: L, h => by
    simp only [List.replicate_succ, List.map_cons, placements, List.map_cons, List.map_nil,
      List.singleton_append]
    rw [placements_replicate t f m L (by simpa using h)]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h

theorem argsAt_replicate (t : Ty) (f : Nat → Nat) (bs : List UInt8) :
    ∀ (m : Nat) (L : List Nat) (hL : L.length = m) (env : Env (List.replicate m t)),
      ArgsAt (L.map fun j => [f j]) env bs →
      ∀ k (hk : k < m), Data.reprBytes ((Env.elems m env)[k]'(by simp; omega))
        (slice bs (f (L[k]'(by omega))) t.size)
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, l :: L, hL, .cons x env, ha, k, hk => by
    simp only [List.map_cons, ArgsAt, List.mem_singleton, forall_eq] at ha
    cases k with
    | zero => exact ha.1
    | succ k =>
      exact argsAt_replicate t f bs m L (by simpa using hL) env ha.2 k (by omega)
  | _ + 1, [], hL, _, _, _, _ => by simp at hL

/-- The array literal `#v[a₀, …, aₙ₋₁]` of kind `array` is lawful, since argument `j` is element
`j`. -/
theorem CtorLaw.vec (t : Ty) (n : Nat) :
    CtorLaw (List.replicate n t) (.arr t n) .array
      fun env => ⟨(Env.elems n env).toArray, by simp⟩ := by
  have hp : planOf (List.replicate n t) (.arr t n) .array =
      ((List.range n).map fun j => [j * t.size], none) := by
    show (((List.range (List.replicate n t).length).map fun j => [j * t.size]), none) = _
    rw [List.length_replicate]
  have hpl := placements_replicate t (· * t.size) n (List.range n) (by simp)
  have hsz : (Ty.arr t n).size = n * t.size := rfl
  refine ⟨?_, ?_, by rw [hp]; simp, fun env bs hl _ ha => ⟨hl, fun i h => ?_⟩⟩
  · rw [hp, hpl, hsz]; intro q hq
    simp only [List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    refine ⟨?_, by simp⟩
    show j * t.size + t.size ≤ n * t.size
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  · rw [hp, hpl]
    refine List.pairwise_map.mpr ((List.pairwise_lt_range (n := n)).imp fun {a b} hab => ?_)
    left; show a * t.size + t.size ≤ b * t.size
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hab
  · rw [hp] at ha
    have := argsAt_replicate t (· * t.size) bs n (List.range n) (by simp) env ha i h
    simp only [List.getElem_range] at this
    show Data.reprBytes (Vector.mk (Env.elems n env).toArray _)[i] _
    simpa [Shape.elemOffset] using this

end Flat

/-- The array literal `#v[a₀, …, aₙ₋₁]`. -/
def Ctor.vec (t : Ty) (n : Nat) : Ctor (List.replicate n t) (.arr t n) :=
  ⟨"#v", .array, fun env => ⟨(Env.elems n env).toArray, by simp⟩, some ⟨Flat.CtorLaw.vec t n⟩, none⟩

/-- `Vector.replicate n a`, in which every element is `a`. -/
def Ctor.fill (t : Ty) (n : Nat) : Ctor [t] (.arr t n) :=
  ⟨"fill", .fill, fun env => Vector.replicate n (env.get .here), some ⟨Flat.CtorLaw.fill t n⟩, none⟩

/-- `Slots.empty n`, in which every cell is empty. -/
def Ctor.slotsEmpty (t : Ty) (n : Nat) : Ctor [] (.slots t n) :=
  ⟨"Slots.empty", .fill, fun _ => Slots.empty n, some ⟨Flat.CtorLaw.slotsEmpty t n⟩, none⟩

/-! ## Obligations of loops -/

/-- `loopSafe` from the obligations of every iteration, where the body's are needed only when the
loop condition holds. For `for i in 0...s.len` the condition is `i < s.len` under a static cap
`N`, so the body may index the slice `s` by `i`. The automatic discharge of `f.safe` uses it, with
the counter below the loop bound. -/
theorem loopSafe_of_forall_cond {σ : Type} (condS bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    ∀ (n i : Nat) (acc : σ) (w : World),
      (∀ j, i ≤ j → j < i + n → ∀ a w, condS (UInt64.ofNat j) a w ∧
        ((cond (UInt64.ofNat j) a w).1 = true →
          bodyS (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2)) →
      loopSafe condS bodyS cond body n i acc w := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro i acc w h
    have hi := h i (Nat.le_refl _) (by omega)
    exact ⟨(hi _ _).1, fun hc => ⟨(hi _ _).2 hc, ih _ _ _ fun j h1 h2 => h j (by omega) (by omega)⟩⟩

/-- An invariant of a loop's state indexed by the counter. When it holds of the start at `i` and
every iteration `j` that runs keeps it from `j` to `j + 1`, it holds of the final state at some
counter value. The verified analyser's loop invariants use it. -/
theorem loopDenote_invJ {σ : Type} (P : Nat → σ → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    ∀ (n i : Nat) (acc : σ) (w : World), P i acc →
      (∀ j a w, i ≤ j → j < i + n → P j a → (cond (UInt64.ofNat j) a w).1 = true →
        P (j + 1) (body (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2).1) →
      ∃ j, j ≤ i + n ∧ P j (loopDenote cond body n i acc w).1 := by
  intro n
  induction n with
  | zero => intro i acc w hP _; exact ⟨i, by omega, hP⟩
  | succ n ih =>
    intro i acc w hP h
    simp only [loopDenote]
    split
    · exact ⟨i, by omega, hP⟩
    · next hc =>
      obtain ⟨j, hj, hP'⟩ := ih _ _ _ (h i acc w (Nat.le_refl _) (by omega) hP hc)
        (fun j a w h1 h2 => h j a w (by omega) (by omega))
      exact ⟨j, by omega, hP'⟩

/-- A loop's obligations hold if they hold in every iteration for every loop state satisfying
an invariant `P` indexed by the counter that the start satisfies and every iteration keeps. -/
theorem loopSafe_invJ {σ : Type} (P : Nat → σ → Prop) (condS bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    ∀ (n i : Nat) (acc : σ) (w : World), P i acc →
      (∀ j a w, i ≤ j → j < i + n → P j a → condS (UInt64.ofNat j) a w ∧
        ((cond (UInt64.ofNat j) a w).1 = true →
          bodyS (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2 ∧
            P (j + 1) (body (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2).1)) →
      loopSafe condS bodyS cond body n i acc w := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro i acc w hP h
    have hi := h i acc w (Nat.le_refl _) (by omega) hP
    exact ⟨hi.1, fun hc => ⟨(hi.2 hc).1,
      ih _ _ _ (hi.2 hc).2 fun j a w h1 h2 => h j a w (by omega) (by omega)⟩⟩

/-- A loop's obligations hold if they hold in every iteration for every loop state satisfying an
invariant `P` that the loop's start satisfies and every iteration keeps. It is used for loops
that carry slice views, whose cells stay full. -/
theorem loopSafe_of_inv_cond {σ : Type} (P : σ → Prop) (condS bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (n i : Nat) (acc : σ) (w : World) (hP : P acc)
    (h : ∀ j, i ≤ j → j < i + n → ∀ a w, P a → condS (UInt64.ofNat j) a w ∧
        ((cond (UInt64.ofNat j) a w).1 = true →
          bodyS (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2 ∧
            P (body (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2).1)) :
    loopSafe condS bodyS cond body n i acc w :=
  loopSafe_invJ (fun _ a => P a) condS bodyS cond body n i acc w hP
    fun j a w h1 h2 hPa => h j h1 h2 a w hPa

/-- An invariant of a loop's state. When it holds of the start and every iteration that runs, with
its condition true and its counter in range, keeps it, it holds of the final state. `mp_loop_lift`
uses it for an inner loop in the body of a loop carrying a slice view, so that the outer
invariant that the cells stay full survives the inner loop. -/
theorem loopDenote_inv_cond {σ : Type} (P : σ → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (n i : Nat) (acc : σ) (w : World) (hP : P acc)
    (h : ∀ j, i ≤ j → j < i + n → ∀ a w, P a → (cond (UInt64.ofNat j) a w).1 = true →
        P (body (UInt64.ofNat j) a (cond (UInt64.ofNat j) a w).2).1) :
    P (loopDenote cond body n i acc w).1 := by
  obtain ⟨_, _, h'⟩ := loopDenote_invJ (fun _ a => P a) cond body n i acc w hP
    fun j a w h1 h2 hPa hc => h j h1 h2 a w hPa hc
  exact h'

/-! ## Helpers for loop proofs with `vcgen`

`vcgen` presents a loop iteration over `List.range n` as a split `pref ++ cur :: suff`, in which
the counter is `cur = pref.length`. -/

/-- In a split of `List.range n` at `cur`, `cur` is the length of the prefix and below `n`. -/
theorem range_split {n cur : Nat} {pref suff : List Nat}
    (h : List.range n = pref ++ cur :: suff) : cur = pref.length ∧ pref.length < n := by
  have hl := congrArg List.length h
  simp only [List.length_range, List.length_append, List.length_cons] at hl
  have hg : (List.range n)[pref.length]'(by simp; omega) =
      (pref ++ cur :: suff)[pref.length]'(by simp) := by
    simp only [h]
  simp only [List.getElem_range, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at hg
  omega

/-- The cost model charging `1` for every construct, which `#mp_cost … with` uses for display. -/
def CostModel.ones : CostModel :=
  ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

end Millipede
