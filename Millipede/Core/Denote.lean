import Millipede.Core.Lawful

/-!
# Value semantics

`Exp.denote ω e env w` is the value of `e` in the environment `env`, starting from the world `w`
under the oracle `ω`, and it returns the value together with the new world. The world records the
events so far. `denote` is a plain Lean function defined by structural recursion, with no memory,
addresses or cost.

The world changes only at extern calls, which append events, and after `exit` it is frozen:
`Exp.denote_halted` says that nothing changes after `exit`, for every term and every oracle.

Places are lenses, so `assign p a k` runs `k` in the environment where `p` holds `a`. A borrow
binds the place's value when it begins, and an exclusive borrow writes the body's handed-back
value to the place when it ends. A call with reference arguments writes the callee's updated
`mut` parameters back to the argument places. An extern that writes mutable byte slices takes the
oracle's raw reply, writes its bytes into the slices, at most each slice's capacity, and passes
the result word to the continuation. Partial operations are total here and return defaults, and
their obligations are defined in `Safe.lean`.
-/

namespace Millipede

/-- The loop driver, with `n` remaining iterations, the current counter `i` and the accumulator
`acc`. Each iteration evaluates the condition, stops with `acc` when it is `false`, and otherwise
runs the body and continues. It recurses structurally on `n`. -/
def loopDenote {σ : Type} (cond : UInt64 → σ → World → Bool × World)
    (body : UInt64 → σ → World → σ × World) : Nat → Nat → σ → World → σ × World
  | 0, _, acc, w => (acc, w)
  | n + 1, i, acc, w =>
    let c := cond (UInt64.ofNat i) acc w
    match c.1 with
    | false => (acc, c.2)
    | true =>
      let b := body (UInt64.ofNat i) acc c.2
      loopDenote cond body n (i + 1) b.1 b.2

/-- A match on a `Result` as a function, which keeps `Exp.denote` free of nested matches. -/
def Except.elim {ε α β : Type} (r : Except ε α) (f : ε → β) (g : α → β) : β :=
  match r with
  | .error e => f e
  | .ok a => g a

@[simp] theorem Except.elim_error {ε α β : Type} (e : ε) (f : ε → β) (g : α → β) :
    Except.elim (.error e) f g = f e := rfl
@[simp] theorem Except.elim_ok {ε α β : Type} (a : α) (f : ε → β) (g : α → β) :
    Except.elim (.ok a) f g = g a := rfl

/-- The value semantics of `e` under oracle `ω`, which returns the value and the new world. -/
def Exp.denote (ω : Oracle) : {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → World → t.carrier × World
  | _, _, .atom a, env, w => (a.denote env, w)
  | _, _, .let_ e₁ e₂, env, w =>
    let r := e₁.denote ω env w
    e₂.denote ω (.cons r.1 env) r.2
  | _, _, .ite c e₁ e₂, env, w =>
    match (c.denote env : Bool) with
    | true => e₁.denote ω env w
    | false => e₂.denote ω env w
  | _, _, .prim p args, env, w => (p.denote (args.denote env), w)
  | _, _, .call _ body args, env, w => body.denote ω (args.denote env) w
  | _, _, .ok a, env, w => (Except.ok (a.denote env), w)
  | _, _, .err a, env, w => (Except.error (a.denote env), w)
  | _, _, @Exp.match_ _ ε α _ s eE eO, env, w =>
    Except.elim (s.denote env : Except ε.carrier α.carrier)
      (fun e => eE.denote ω (.cons e env) w) (fun a => eO.denote ω (.cons a env) w)
  | _, _, .ext sig args, env, w => w.call ω (sig.call args env) sig.noreturn
  | _, _, .extMut sig args k, env, w =>
    let r := w.ask ω (sig.call args env) sig.noreturn
    k.denote ω (.cons r.1.result
      (args.fill env env (fitOut (sig.call args env).outCaps r.1.bytesOut))) r.2
  | _, _, .mk c args, env, w => (c.build (args.denote env), w)
  | _, _, .read p, env, w => (p.get env, w)
  | _, _, .assign p a k, env, w => k.denote ω (p.set env (a.denote env)) w
  | _, _, .case s sp eP eQ, env, w =>
    Sum.elim (fun x => eP.denote ω (.cons x env) w) (fun y => eQ.denote ω (.cons y env) w)
      (sp.split (s.denote env))
  | _, _, .put p i a k, env, w =>
    k.denote ω (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) w
  | _, _, .take (dflt := _) p i k, env, w =>
    k.denote ω (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) w
  | _, _, .borrowShr p body k, env, w =>
    let r := body.denote ω (.cons (p.get env) env) w
    k.denote ω (.cons r.1 env) r.2
  | _, _, .borrowMut p body k, env, w =>
    let r := body.denote ω (.cons (p.get env) env) w
    k.denote ω (.cons r.1.1 (p.set env r.1.2)) r.2
  | _, _, .callRef _ _ body args k, env, w =>
    let r := body.denote ω (args.denote env) w
    k.denote ω (.cons r.1.1 (args.writeBack env r.1.2)) r.2
  | _, _, .guard g, env, w => (if g.denote env then .ok () else .error (), w)
  | _, _, .loop n cs init c body k, env, w =>
    let r := loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      n 0 (init.denote env, cs.get env) w
    k.denote ω (.cons r.1.1 (cs.set env r.1.2)) r.2

/-- The denotation of a function on argument values. -/
abbrev Fn.denote {ps : List Ty} {r : Ty} (f : Fn ps r) (ω : Oracle) (env : Env ps) (w : World) :
    r.carrier × World :=
  f.body.denote ω env w

/-! ## Frame theorems -/

theorem loopDenote_halted {σ : Type} (cond : UInt64 → σ → World → Bool × World)
    (body : UInt64 → σ → World → σ × World)
    (hc : ∀ i a w, w.halted = true → (cond i a w).2 = w)
    (hb : ∀ i a w, w.halted = true → (body i a w).2 = w) :
    ∀ n i acc w, w.halted = true → (loopDenote cond body n i acc w).2 = w := by
  intro n
  induction n <;> intro i acc w hw
  case zero => rfl
  case succ n ih =>
    have h1 := hc (UInt64.ofNat i) acc w hw
    have := hb (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2
    grind [loopDenote]

/-- After `exit`, evaluation leaves the world unchanged, so it adds no events and stays halted. -/
theorem Exp.denote_halted (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), w.halted = true → (e.denote ω env w).2 = w := by
  induction e <;> intro env w hw
  case match_ s _ _ _ _ =>
    cases h : (s.denote env : Except _ _) <;>
      simp only [Exp.denote, h, Except.elim_error, Except.elim_ok] <;> grind
  case case s sp _ _ _ _ =>
    cases h : sp.split (s.denote env) <;>
      simp only [Exp.denote, h, Sum.elim_inl, Sum.elim_inr] <;> grind
  case ext => simp [Exp.denote, hw]
  case extMut ih => simp only [Exp.denote, World.ask, hw, ite_true]; exact ih _ _ hw
  case loop n cs init c body k ihc ihb ihk =>
    have h := loopDenote_halted
      (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun _ _ _ h => ihc _ _ h) (fun _ _ _ h => ihb _ _ h) n 0 (init.denote env, cs.get env) w hw
    simp only [Exp.denote]; rw [ihk _ _ (by rw [h]; exact hw), h]
  all_goals grind [Exp.denote]

/-- The loop driver on an accumulator paired with the empty carried tuple is the driver on the
accumulator alone. -/
theorem loopDenote_unit {σ : Type} (cond : UInt64 → σ × Unit → World → Bool × World)
    (body : UInt64 → σ × Unit → World → (σ × Unit) × World) : ∀ n i a w,
    loopDenote cond body n i (a, ()) w =
      (((loopDenote (fun j x w => cond j (x, ()) w) (fun j x w => ((body j (x, ()) w).1.1,
        (body j (x, ()) w).2)) n i a w).1, ()),
        (loopDenote (fun j x w => cond j (x, ()) w) (fun j x w => ((body j (x, ()) w).1.1,
          (body j (x, ()) w).2)) n i a w).2) := by
  intro n; induction n <;> intro i a w
  case zero => rfl
  case succ n ih =>
    simp only [loopDenote]; cases (cond (UInt64.ofNat i) (a, ()) w).1 <;> simp only [← ih]

/-- A loop carrying nothing denotes the loop driver on its accumulator alone. -/
theorem Exp.denote_loop0 (ω : Oracle) {Γ : List Ty} {s : Ty} (n : Nat) (init : Atom Γ s)
    (c : Exp (.u64 :: s :: Γ) .bool) (body : Exp (.u64 :: s :: Γ) s) (env : Env Γ) (w : World) :
    (Exp.loop0 n init c body).denote ω env w =
      loopDenote (fun i a w => c.denote ω (.cons i (.cons a env)) w)
        (fun i a w => body.denote ω (.cons i (.cons a env)) w) n 0 (init.denote env) w := by
  simp only [Exp.denote, Carry.get, Carry.set]; erw [loopDenote_unit]; rfl

end Millipede
