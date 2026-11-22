import Millipede.Core.Cost

/-!
# Stack and footprint

This file defines two static quantities computed from the syntax of a term. Each has an
instrumented counterpart that follows the path a run actually takes, and a theorem that the usage
never exceeds the bound, for every oracle, environment and world.

The stack bound is parameterised by a `FrameModel φ`, which gives the bytes of stack that an
activation with `w` word slots uses. `Exp.slotWords e` is the number of word slots of a frame
that runs `e` with every binder and every intermediate result in its own slot, and
`Exp.stackBytes φ e` is the stack used by the calls inside `e` beyond that frame. `Exp.stack φ e`
is the frame of `e` together with its calls. Every activation is charged `scratchWords` slots on
top of its value slots. `Exp.stackUse_le` proves that the stack a run uses stays within
`Exp.stackBytes`, and the compiler's stack theorem is stated with these definitions.

The footprint `Exp.footprint e` is the bytes of the values bound at once while `e` runs, laid out
as `Shape.size` says, along the worst path and summed along nested calls. A reference binder
counts as 16 bytes, a pointer and, for a slice, a length. `Exp.footUse_le` proves that a run
stays within it.
-/

namespace Millipede

/-- A frame-size model, which gives the bytes of stack used by one activation whose frame holds
`w` word slots, with the return address and alignment padding included. A frame with more slots
never needs less stack, so a bound computed from an upper bound on the slot count is sound. -/
structure FrameModel where
  frame : Nat → Nat
  mono : ∀ {a b : Nat}, a ≤ b → frame a ≤ frame b

/-! ## Frame slots -/

/-- The number of scratch slots charged to every activation on top of the slots its values need.
A compiler may keep values in memory and use a fixed set of scratch slots besides their frame
slots, and the memory lowering gives every activation exactly this many. -/
def scratchWords : Nat := 16

/-- The word slots charged to an activation whose values need `w` slots, which is `scratchWords`
more. -/
def frameWords (w : Nat) : Nat := scratchWords + w

/-- The word slots a frame needs to run `e` with every binder and every intermediate result in
its own slot. Callee bodies are excluded, because they run in their own frames. -/
def Exp.slotWords : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .atom (t := t) _ => t.data.shape.words
  | _, _, .let_ (t := t) e₁ e₂ => t.data.shape.words + e₁.slotWords + e₂.slotWords
  | _, _, .ite (t := t) _ e₁ e₂ => t.data.shape.words + 1 + e₁.slotWords + e₂.slotWords
  | _, _, .prim (ps := ps) (r := r) _ _ => r.data.shape.words + ctxWords ps
  | _, _, .call (ps := ps) (r := r) _ _ _ => r.data.shape.words + ctxWords ps
  | _, _, .ok (ε := ε) (α := α) _ => (Ty.result ε α).data.shape.words
  | _, _, .err (ε := ε) (α := α) _ => (Ty.result ε α).data.shape.words
  | _, _, .match_ (ε := ε) (α := α) (t := t) _ eE eO =>
    t.data.shape.words + ε.data.shape.words + α.data.shape.words + eE.slotWords + eO.slotWords
  | _, _, .ext sig _ => 1 + 2 * sig.params.length
  | _, _, .extMut (u := u) sig _ k => u.words + 1 + 2 * sig.params.length + k.slotWords
  | _, _, .mk (ps := ps) (t := t) _ _ => t.words + ctxWords ps
  | _, _, .read (t := t) p => t.words + p.depth
  | _, _, .assign (t := t) (u := u) p _ k => u.words + t.words + p.depth + k.slotWords
  | _, _, .case (t := t) (p := pt) (q := qt) (u := u) _ _ eP eQ =>
    u.words + t.words + pt.words + qt.words + eP.slotWords + eQ.slotWords
  | _, _, .put (t := t) (u := u) p _ _ k => u.words + t.words + p.depth + 1 + k.slotWords
  | _, _, .take (t := t) (u := u) (dflt := _) p _ k => u.words + t.words + p.depth + 1 + k.slotWords
  | _, _, .borrowShr (t := t) (u := u) (v := v) p body k =>
    v.words + t.words + u.words + p.depth + body.slotWords + k.slotWords
  | _, _, .borrowMut (t := t) (u := u) (v := v) p body k =>
    v.words + 2 * t.words + 2 * u.words + p.depth + body.slotWords + k.slotWords
  | _, _, .callRef (ps := ps) (os := os) (r := r) (u := u) _ _ _ args k =>
    u.words + ctxWords ps + r.words + ctxWords os + args.depth + k.slotWords
  | _, _, .guard g => (Ty.result .unit .unit).words + g.depth
  | _, _, .loop (ts := ts) (s := s) (u := u) _ _ _ c body k =>
    u.words + 2 * s.data.shape.words + 1 + (Ty.tup ts).words + c.slotWords + body.slotWords +
      k.slotWords

/-! ## Stack -/

/-- The stack bytes used by the calls inside `e` beyond the frame that runs `e`, which is the
maximum over call sites of the callee's frame plus its own calls. -/
def Exp.stackBytes (φ : FrameModel) : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .atom _ => 0
  | _, _, .let_ e₁ e₂ => max (e₁.stackBytes φ) (e₂.stackBytes φ)
  | _, _, .ite _ e₁ e₂ => max (e₁.stackBytes φ) (e₂.stackBytes φ)
  | _, _, .prim _ _ => 0
  | _, _, .call (ps := ps) _ body _ =>
    φ.frame (frameWords (ctxWords ps + body.slotWords)) + body.stackBytes φ
  | _, _, .ok _ => 0
  | _, _, .err _ => 0
  | _, _, .match_ _ eE eO => max (eE.stackBytes φ) (eO.stackBytes φ)
  | _, _, .ext _ _ => 0
  | _, _, .extMut _ _ k => k.stackBytes φ
  | _, _, .mk _ _ => 0
  | _, _, .read _ => 0
  | _, _, .assign _ _ k => k.stackBytes φ
  | _, _, .case _ _ eP eQ => max (eP.stackBytes φ) (eQ.stackBytes φ)
  | _, _, .put _ _ _ k => k.stackBytes φ
  | _, _, .take (dflt := _) _ _ k => k.stackBytes φ
  | _, _, .borrowShr _ body k => max (body.stackBytes φ) (k.stackBytes φ)
  | _, _, .borrowMut _ body k => max (body.stackBytes φ) (k.stackBytes φ)
  | _, _, .callRef (ps := ps) _ _ body _ k =>
    max (φ.frame (frameWords (ctxWords ps + body.slotWords)) + body.stackBytes φ) (k.stackBytes φ)
  | _, _, .guard _ => 0
  | _, _, .loop _ _ _ c body k => max (max (c.stackBytes φ) (body.stackBytes φ)) (k.stackBytes φ)

/-- The static stack measure, which is the frame that runs `e`, holding its context and its
slots, plus the calls inside it. -/
def Exp.stack {Γ : List Ty} {t : Ty} (φ : FrameModel) (e : Exp Γ t) : Nat :=
  φ.frame (frameWords (ctxWords Γ + e.slotWords)) + e.stackBytes φ

theorem max_le_max' {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) : max a b ≤ max c d := by
  simp only [Nat.max_le]; omega

/-- The maximum of a per-iteration quantity over the iterations that a loop actually runs, in the
same way as `loopDenote`. -/
def loopMax {σ : Type} (condU bodyU : UInt64 → σ → World → Nat)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World) :
    Nat → Nat → σ → World → Nat
  | 0, _, _, _ => 0
  | n + 1, i, acc, w =>
    let c := cond (UInt64.ofNat i) acc w
    match c.1 with
    | false => condU (UInt64.ofNat i) acc w
    | true =>
      let b := body (UInt64.ofNat i) acc c.2
      max (condU (UInt64.ofNat i) acc w) (max (bodyU (UInt64.ofNat i) acc c.2)
        (loopMax condU bodyU cond body n (i + 1) b.1 b.2))

theorem loopMax_le {σ : Type} (condU bodyU : UInt64 → σ → World → Nat)
    (cond : UInt64 → σ → World → Bool × World) (body : UInt64 → σ → World → σ × World)
    (kc kb : Nat) (hc : ∀ i a w, condU i a w ≤ kc) (hb : ∀ i a w, bodyU i a w ≤ kb) :
    ∀ n i acc w, loopMax condU bodyU cond body n i acc w ≤ max kc kb := by
  intro n
  induction n <;> intro i acc w
  case zero => exact Nat.zero_le _
  case succ n ih =>
    have := hc (UInt64.ofNat i) acc w
    have := hb (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2
    have := ih (i + 1) (body (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2).1
      (body (UInt64.ofNat i) acc (cond (UInt64.ofNat i) acc w).2).2
    grind [loopMax]

/-- The stack bytes used by the calls made on the path actually taken. -/
def Exp.stackUse (ω : Oracle) (φ : FrameModel) :
    {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → World → Nat
  | _, _, .atom _, _, _ => 0
  | _, _, .let_ e₁ e₂, env, w =>
    max (e₁.stackUse ω φ env w)
      (e₂.stackUse ω φ (.cons (e₁.denote ω env w).1 env) (e₁.denote ω env w).2)
  | _, _, .ite c e₁ e₂, env, w =>
    match (c.denote env : Bool) with
    | true => e₁.stackUse ω φ env w
    | false => e₂.stackUse ω φ env w
  | _, _, .prim _ _, _, _ => 0
  | _, _, .call (ps := ps) _ body args, env, w =>
    φ.frame (frameWords (ctxWords ps + body.slotWords)) + body.stackUse ω φ (args.denote env) w
  | _, _, .ok _, _, _ => 0
  | _, _, .err _, _, _ => 0
  | _, _, @Exp.match_ _ ε α _ s eE eO, env, w =>
    match (s.denote env : Except ε.carrier α.carrier) with
    | .error e => eE.stackUse ω φ (.cons e env) w
    | .ok a => eO.stackUse ω φ (.cons a env) w
  | _, _, .ext _ _, _, _ => 0
  | _, _, .extMut sig args k, env, w =>
    k.stackUse ω φ (.cons (w.ask ω (sig.call args env) sig.noreturn).1.result
      (args.fill env env (fitOut (sig.call args env).outCaps
        (w.ask ω (sig.call args env) sig.noreturn).1.bytesOut)))
      (w.ask ω (sig.call args env) sig.noreturn).2
  | _, _, .mk _ _, _, _ => 0
  | _, _, .read _, _, _ => 0
  | _, _, .assign p a k, env, w => k.stackUse ω φ (p.set env (a.denote env)) w
  | _, _, .case s sp eP eQ, env, w =>
    match sp.split (s.denote env) with
    | .inl x => eP.stackUse ω φ (.cons x env) w
    | .inr y => eQ.stackUse ω φ (.cons y env) w
  | _, _, .put p i a k, env, w =>
    k.stackUse ω φ
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) w
  | _, _, .take (dflt := _) p i k, env, w =>
    k.stackUse ω φ (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) w
  | _, _, .borrowShr p body k, env, w =>
    max (body.stackUse ω φ (.cons (p.get env) env) w)
      (k.stackUse ω φ (.cons (body.denote ω (.cons (p.get env) env) w).1 env)
        (body.denote ω (.cons (p.get env) env) w).2)
  | _, _, .borrowMut p body k, env, w =>
    max (body.stackUse ω φ (.cons (p.get env) env) w)
      (k.stackUse ω φ (.cons (body.denote ω (.cons (p.get env) env) w).1.1
          (p.set env (body.denote ω (.cons (p.get env) env) w).1.2))
        (body.denote ω (.cons (p.get env) env) w).2)
  | _, _, .callRef (ps := ps) _ _ body args k, env, w =>
    max (φ.frame (frameWords (ctxWords ps + body.slotWords)) + body.stackUse ω φ (args.denote env) w)
      (k.stackUse ω φ (.cons (body.denote ω (args.denote env) w).1.1
          (args.writeBack env (body.denote ω (args.denote env) w).1.2))
        (body.denote ω (args.denote env) w).2)
  | _, _, .guard _, _, _ => 0
  | _, _, .loop n cs init c body k, env, w =>
    max (loopMax (fun i st w => c.stackUse ω φ (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.stackUse ω φ (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
      (init.denote env, cs.get env) w)
      (k.stackUse ω φ (.cons (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.1
        (cs.set env (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.2)) (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).2)

/-- The stack bound is sound, since on every run the calls made use at most `e.stackBytes φ`
bytes beyond `e`'s frame. -/
theorem Exp.stackUse_le (ω : Oracle) (φ : FrameModel) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), e.stackUse ω φ env w ≤ e.stackBytes φ := by
  induction e <;> intro env w
  case loop ihc ihb ihk =>
    simp only [Exp.stackUse, Exp.stackBytes]
    exact max_le_max' (loopMax_le _ _ _ _ _ _ (fun _ _ _ => ihc _ _) (fun _ _ _ => ihb _ _) _ _ _ _)
      (ihk _ _)
  all_goals grind [Exp.stackUse, Exp.stackBytes]

/-! ## Footprint -/

/-- The bytes that a binder of type `t` and mode `m` occupies. An owned binder holds the value,
and a reference holds a pointer and, for a slice, a length, counted as 16 bytes either way. -/
def Mode.bytes (m : Mode) (t : Ty) : Nat :=
  match m with
  | .own => t.size
  | _ => 16

/-- The bytes of a callee's parameters, by argument mode. -/
def RArgs.bytes {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own (t := t) _ as => t.size + as.bytes
  | _, _, .shr (t := t) _ as => Mode.bytes .shr t + as.bytes
  | _, _, .mut (t := t) _ as => Mode.bytes .mut t + as.bytes

/-- The bytes of the values in a context, all owned. -/
def ctxBytes : List Ty → Nat
  | [] => 0
  | t :: ts => t.size + ctxBytes ts

/-- The static footprint in bytes, which counts the values bound at once while `e` runs, along
the worst path and with nested calls included. -/
def Exp.footprint : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .atom _ => 0
  | _, _, .let_ (s := s) e₁ e₂ => max e₁.footprint (s.size + e₂.footprint)
  | _, _, .ite _ e₁ e₂ => max e₁.footprint e₂.footprint
  | _, _, .prim _ _ => 0
  | _, _, .call (ps := ps) _ body _ => ctxBytes ps + body.footprint
  | _, _, .ok _ => 0
  | _, _, .err _ => 0
  | _, _, .match_ (ε := ε) (α := α) _ eE eO => max (ε.size + eE.footprint) (α.size + eO.footprint)
  | _, _, .ext _ _ => 0
  | _, _, .extMut _ _ k => Ty.u64.size + k.footprint
  | _, _, .mk _ _ => 0
  | _, _, .read _ => 0
  | _, _, .assign _ _ k => k.footprint
  | _, _, .case (p := pt) (q := qt) _ _ eP eQ =>
    max (pt.size + eP.footprint) (qt.size + eQ.footprint)
  | _, _, .put _ _ _ k => k.footprint
  | _, _, .take (t := t) (dflt := _) _ _ k => t.size + k.footprint
  | _, _, .borrowShr (t := t) (u := u) _ body k =>
    max (Mode.bytes .shr t + body.footprint) (u.size + k.footprint)
  | _, _, .borrowMut (t := t) (u := u) _ body k =>
    max (Mode.bytes .mut t + body.footprint) (u.size + k.footprint)
  | _, _, .callRef (r := r) _ _ body args k => max (args.bytes + body.footprint) (r.size + k.footprint)
  | _, _, .guard _ => 0
  | _, _, .loop (s := s) _ _ _ c body k =>
    max (Ty.u64.size + s.size + max c.footprint body.footprint) (s.size + k.footprint)

/-- The footprint on the path actually taken. -/
def Exp.footUse (ω : Oracle) : {Γ : List Ty} → {t : Ty} → Exp Γ t → Env Γ → World → Nat
  | _, _, .atom _, _, _ => 0
  | _, _, .let_ (s := s) e₁ e₂, env, w =>
    max (e₁.footUse ω env w)
      (s.size + e₂.footUse ω (.cons (e₁.denote ω env w).1 env) (e₁.denote ω env w).2)
  | _, _, .ite c e₁ e₂, env, w =>
    match (c.denote env : Bool) with
    | true => e₁.footUse ω env w
    | false => e₂.footUse ω env w
  | _, _, .prim _ _, _, _ => 0
  | _, _, .call (ps := ps) _ body args, env, w => ctxBytes ps + body.footUse ω (args.denote env) w
  | _, _, .ok _, _, _ => 0
  | _, _, .err _, _, _ => 0
  | _, _, @Exp.match_ _ ε α _ s eE eO, env, w =>
    match (s.denote env : Except ε.carrier α.carrier) with
    | .error e => ε.size + eE.footUse ω (.cons e env) w
    | .ok a => α.size + eO.footUse ω (.cons a env) w
  | _, _, .ext _ _, _, _ => 0
  | _, _, .extMut sig args k, env, w =>
    Ty.u64.size + k.footUse ω (.cons (w.ask ω (sig.call args env) sig.noreturn).1.result
      (args.fill env env (fitOut (sig.call args env).outCaps
        (w.ask ω (sig.call args env) sig.noreturn).1.bytesOut)))
      (w.ask ω (sig.call args env) sig.noreturn).2
  | _, _, .mk _ _, _, _ => 0
  | _, _, .read _, _, _ => 0
  | _, _, .assign p a k, env, w => k.footUse ω (p.set env (a.denote env)) w
  | _, _, .case (p := pt) (q := qt) s sp eP eQ, env, w =>
    match sp.split (s.denote env) with
    | .inl x => pt.size + eP.footUse ω (.cons x env) w
    | .inr y => qt.size + eQ.footUse ω (.cons y env) w
  | _, _, .put p i a k, env, w =>
    k.footUse ω
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) w
  | _, _, .take (t := t) (dflt := _) p i k, env, w =>
    t.size + k.footUse ω (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) w
  | _, _, .borrowShr (t := t) (u := u) p body k, env, w =>
    max (Mode.bytes .shr t + body.footUse ω (.cons (p.get env) env) w)
      (u.size + k.footUse ω (.cons (body.denote ω (.cons (p.get env) env) w).1 env)
        (body.denote ω (.cons (p.get env) env) w).2)
  | _, _, .borrowMut (t := t) (u := u) p body k, env, w =>
    max (Mode.bytes .mut t + body.footUse ω (.cons (p.get env) env) w)
      (u.size + k.footUse ω (.cons (body.denote ω (.cons (p.get env) env) w).1.1
          (p.set env (body.denote ω (.cons (p.get env) env) w).1.2))
        (body.denote ω (.cons (p.get env) env) w).2)
  | _, _, .callRef (r := r) _ _ body args k, env, w =>
    max (args.bytes + body.footUse ω (args.denote env) w)
      (r.size + k.footUse ω (.cons (body.denote ω (args.denote env) w).1.1
          (args.writeBack env (body.denote ω (args.denote env) w).1.2))
        (body.denote ω (args.denote env) w).2)
  | _, _, .guard _, _, _ => 0
  | _, _, .loop (s := s) n cs init c body k, env, w =>
    max (Ty.u64.size + s.size + loopMax (fun i st w => c.footUse ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.footUse ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
      (init.denote env, cs.get env) w)
      (s.size + k.footUse ω (.cons (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.1
        (cs.set env (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).1.2)) (loopDenote (fun i st w => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w)
          (fun i st w => body.denote ω (.cons i (.cons st.1 (cs.set env st.2))) w) n 0
          (init.denote env, cs.get env) w).2)

/-- The footprint is sound, since on every run the values bound at once never exceed
`e.footprint` bytes. -/
theorem Exp.footUse_le (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (env : Env Γ) (w : World), e.footUse ω env w ≤ e.footprint := by
  induction e <;> intro env w
  case loop ihc ihb ihk =>
    simp only [Exp.footUse, Exp.footprint]
    exact max_le_max' (Nat.add_le_add_left
      (loopMax_le _ _ _ _ _ _ (fun _ _ _ => ihc _ _) (fun _ _ _ => ihb _ _) _ _ _ _) _)
      (Nat.add_le_add_left (ihk _ _) _)
  all_goals grind [Exp.footUse, Exp.footprint]

end Millipede
