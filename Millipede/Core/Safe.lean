import Millipede.Core.Denote

/-!
# Obligations

`Exp.safe ω e env w` collects the obligations of the partial operations in `e`, structurally and
along its evaluation, each evaluated in the environment and world where the operation runs. A
place that is read, written or borrowed contributes `Place.ok`, which says that every index is in
range, every `Slots` cell reached is full, and the two indices of a pair of elements differ. The
slices passed to an extern lie inside their arrays. `put! i` needs cell `i` to exist and be empty,
and `take! i` needs it to exist and be full. A primitive contributes `Prim.ok`, which says that
`+!`, `-!` and `*!` do not overflow. A branch contributes its obligations under the branch
condition, and a loop contributes them iteration by iteration.

A plain call contributes the obligations of the callee's body at the arguments. A call with
reference arguments contributes the validity of the argument places and the callee's `requires`
at the arguments. Its body's obligations are proved once per function as `FnRef.Safe`, under the
`requires`, and cited at every call. That a `&mut` slice hands back a view that still holds its
elements is not an obligation, because it follows from the hand-back condition that the
compiler checks.

A partial operation whose obligation can be tested at run time also has a checked form, a guard
followed by the obligated form in the `ok` arm. Its obligations hold in every environment,
because the `ok` arm runs only when the guard succeeds. A term without partial operations is
safe everywhere, by `Exp.safe_of_total`.

The design is described in doc/design/obligations.md.
-/

namespace Millipede

/-- The obligations of a loop, iteration by iteration, in the same way as `loopDenote`. -/
def loopSafe {σ : Type} (condS : UInt64 → σ → World → Prop) (bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    Nat → Nat → σ → World → Prop
  | 0, _, _, _ => True
  | n + 1, i, acc, w =>
    condS (UInt64.ofNat i) acc w ∧
      ((cond (UInt64.ofNat i) acc w).1 = true →
        bodyS (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2 ∧
        loopSafe condS bodyS cond body n (i + 1)
          (body (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2).1
          (body (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2).2)

/-- The obligations of `e` when evaluated in `env` from world `w` under `ω`. -/
def Exp.safe (ω : Oracle) : {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → World → Prop
  | _, _, .atom _, _, _ => True
  | _, _, .let_ e₁ e₂, env, w =>
    e₁.safe ω env w ∧ e₂.safe ω (.cons (e₁.denote ω env w).1 env) (e₁.denote ω env w).2
  | _, _, .ite c e₁ e₂, env, w =>
    ((c.denote env : Bool) = true → e₁.safe ω env w) ∧
    ((c.denote env : Bool) = false → e₂.safe ω env w)
  | _, _, .prim p args, env, _ => p.ok (args.denote env)
  | _, _, .call _ body args, env, w => body.safe ω (args.denote env) w
  | _, _, .ok _, _, _ => True
  | _, _, .err _, _, _ => True
  | _, _, @Exp.match_ _ ε α _ s eE eO, env, w =>
    (∀ e, (s.denote env : Except ε.carrier α.carrier) = .error e → eE.safe ω (.cons e env) w) ∧
    (∀ a, (s.denote env : Except ε.carrier α.carrier) = .ok a → eO.safe ω (.cons a env) w)
  | _, _, .ext _ args, env, _ => args.ok env
  | _, _, .extMut sig args k, env, w =>
    args.ok env ∧
      k.safe ω (.cons (w.ask ω (sig.call args env) sig.noreturn).1.result
        (args.fill env env (fitOut (sig.call args env).outCaps
          (w.ask ω (sig.call args env) sig.noreturn).1.bytesOut)))
        (w.ask ω (sig.call args env) sig.noreturn).2
  | _, _, .mk _ _, _, _ => True
  | _, _, .read p, env, _ => p.ok env
  | _, _, .assign p a k, env, w => p.ok env ∧ k.safe ω (p.set env (a.denote env)) w
  | _, _, .case s sp eP eQ, env, w =>
    (∀ x, sp.split (s.denote env) = .inl x → eP.safe ω (.cons x env) w) ∧
    (∀ y, sp.split (s.denote env) = .inr y → eQ.safe ω (.cons y env) w)
  | _, _, .put p i a k, env, w =>
    (p.ok env ∧ (p.get env : Slots _ _).isVacant (i.denote env).toNat = true) ∧
      k.safe ω (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) w
  | _, _, .take (dflt := _) p i k, env, w =>
    (p.ok env ∧ (p.get env : Slots _ _).isFull (i.denote env).toNat = true) ∧
      k.safe ω (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
        (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) w
  | _, _, .borrowShr p body k, env, w =>
    p.ok env ∧ body.safe ω (.cons (p.get env) env) w ∧
      k.safe ω (.cons (body.denote ω (.cons (p.get env) env) w).1 env)
        (body.denote ω (.cons (p.get env) env) w).2
  | _, _, .borrowMut p body k, env, w =>
    p.ok env ∧ body.safe ω (.cons (p.get env) env) w ∧
      k.safe ω (.cons (body.denote ω (.cons (p.get env) env) w).1.1
          (p.set env (body.denote ω (.cons (p.get env) env) w).1.2))
        (body.denote ω (.cons (p.get env) env) w).2
  | _, _, .callRef _ req body args k, env, w =>
    args.ok env ∧ req (args.denote env) ∧ (∀ env' w', req env' → body.safe ω env' w') ∧
      k.safe ω (.cons (body.denote ω (args.denote env) w).1.1
          (args.writeBack env (body.denote ω (args.denote env) w).1.2))
        (body.denote ω (args.denote env) w).2
  | _, _, .guard _, _, _ => True
  | _, _, .loop n cs init c body k, env, w =>
    loopSafe (fun i st w => c.safe ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.safe ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
      (init.denote env, cs.get env) w ∧
    k.safe ω (.cons (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.1
        (cs.set env (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.2))
      (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).2

/-- A function's obligations hold whenever its `requires` does. This is the goal `f.safe` of
`mp def`. -/
def Fn.Safe {ps : List Ty} {r : Ty} (f : Fn ps r) : Prop :=
  ∀ ω env w, f.requires env → f.body.safe ω env w

/-- A function with reference parameters satisfies its obligations whenever its `requires`
holds. -/
def FnRef.Safe {ps os : List Ty} {r : Ty} (f : FnRef ps os r) : Prop :=
  ∀ ω env w, f.requires env → f.body.safe ω env w

/-- Given `f.Safe`, the obligations of `f.call args k` are those of the argument places,
`f.requires` of the arguments, and those of `k`. -/
theorem FnRef.safe_call {Γ ps os : List Ty} {r u : Ty} (f : FnRef ps os r) (hf : f.Safe)
    (args : RArgs Γ ps os) (k : Exp (r :: Γ) u) (ω : Oracle) (env : Env Γ) (w : World)
    (ha : args.ok env) (hr : f.requires (args.denote env))
    (hk : k.safe ω (.cons (f.body.denote ω (args.denote env) w).1.1
          (args.writeBack env (f.body.denote ω (args.denote env) w).1.2))
        (f.body.denote ω (args.denote env) w).2) :
    (f.call args k).safe ω env w :=
  ⟨ha, hr, fun env' w' h => hf ω env' w' h, hk⟩

/-! ## Terms without partial operations -/

/-- `e` has no partial operation, which means no partial place selector, no `put` or `take`, and
no `callRef`, whose callee has a `requires`. -/
def Exp.total : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .atom _ => true
  | _, _, .let_ e₁ e₂ => e₁.total && e₂.total
  | _, _, .ite _ e₁ e₂ => e₁.total && e₂.total
  | _, _, .prim p _ => p.total
  | _, _, .call _ body _ => body.total
  | _, _, .ok _ => true
  | _, _, .err _ => true
  | _, _, .match_ _ eE eO => eE.total && eO.total
  | _, _, .ext _ args => args.total
  | _, _, .extMut _ _ _ => false
  | _, _, .mk _ _ => true
  | _, _, .read p => p.total
  | _, _, .assign p _ k => p.total && k.total
  | _, _, .case _ _ eP eQ => eP.total && eQ.total
  | _, _, .put _ _ _ _ => false
  | _, _, .take (dflt := _) _ _ _ => false
  | _, _, .borrowShr p body k => p.total && body.total && k.total
  | _, _, .borrowMut p body k => p.total && body.total && k.total
  | _, _, .callRef _ _ _ _ _ => false
  | _, _, .guard _ => true
  | _, _, .loop _ _ _ c body k => c.total && body.total && k.total

theorem loopSafe_of {σ : Type} (condS bodyS : UInt64 → σ → World → Prop)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (hc : ∀ i a w, condS i a w) (hb : ∀ i a w, bodyS i a w) :
    ∀ n i acc w, loopSafe condS bodyS cond body n i acc w := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih => intro i acc w; exact ⟨hc _ _ _, fun _ => ⟨hb _ _ _, ih _ _ _⟩⟩

/-- A term without partial operations is safe in every environment and world, under every
oracle. -/
theorem Exp.safe_of_total (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t)
    (h : e.total = true) : ∀ (env : Env Γ) (w : World), e.safe ω env w := by
  induction e <;> intro env w
  case loop ihc ihb ihk =>
    simp only [Exp.total, Bool.and_eq_true] at h
    exact ⟨loopSafe_of _ _ _ _ (fun _ _ _ => ihc h.1.1 _ _) (fun _ _ _ => ihb h.1.2 _ _) _ _ _ _,
      ihk h.2 _ _⟩
  all_goals grind [Exp.total, Exp.safe, Place.ok_of_total, EArgs.ok_of_total, Prim.ok_of_total]

/-- The obligations of a loop on an accumulator paired with the empty carried tuple are those of
the loop on the accumulator alone. -/
theorem loopSafe_unit {σ : Type} (condS bodyS : UInt64 → σ × Unit → World → Prop)
    (cond : UInt64 → σ × Unit → World → Bool × World)
    (body : UInt64 → σ × Unit → World → (σ × Unit) × World) (condS' bodyS' : UInt64 → σ → World → Prop)
    (hc : ∀ i a w, condS i (a, ()) w ↔ condS' i a w) (hb : ∀ i a w, bodyS i (a, ()) w ↔ bodyS' i a w) :
    ∀ n i a w, loopSafe condS bodyS cond body n i (a, ()) w ↔
      loopSafe condS' bodyS' (fun j x w => cond j (x, ()) w)
        (fun j x w => ((body j (x, ()) w).1.1, (body j (x, ()) w).2)) n i a w := by
  intro n; induction n <;> intro i a w
  case zero => exact Iff.rfl
  case succ n ih =>
    exact and_congr (hc _ _ _) (imp_congr_right fun _ => and_congr (hb _ _ _) (ih _ _ _))

/-- The obligations of a loop that carries nothing are those of its condition and body, iteration
by iteration. -/
theorem Exp.safe_loop0 (ω : Oracle) {Γ : List Ty} {s : Ty} (n : Nat) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) s) (env : Env Γ) (w : World) :
    (Exp.loop0 n init c body).safe ω env w ↔
      loopSafe (fun i a w => c.safe ω (.cons i (.cons a env)) w)
        (fun i a w => body.safe ω (.cons i (.cons a env)) w)
        (fun i a w => c.denote ω (.cons i (.cons a env)) w)
        (fun i a w => body.denote ω (.cons i (.cons a env)) w) n 0 (init.denote env) w := by
  simp only [Exp.safe, Carry.get, Carry.set, and_true]
  exact loopSafe_unit _ _ _ _ _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) _ _ _ _

end Millipede
