import Millipede.Core.Denote

/-!
# Cost

A `CostModel κ` holds one constant per construct. It is a variable in every theorem, and each
backend supplies its own model and proves that its code stays within it. `Exp.cost κ hb e` is a
static bound computed from the syntax, in which a conditional is bounded by the larger of its
branches and a loop by `n` full iterations. `Exp.exec ω κ hb e env w` is an instrumented semantics,
which computes the value and the world independently of `denote` and counts the steps of the path
actually taken, charging each construct as it runs. `Exp.exec_sound` proves that, for every
oracle, environment and world, `exec` agrees with `denote` and takes at most `cost` steps.

A construct that copies a value pays `κ.word` for each 64-bit word of it on top of its constant.
This applies to the result of an atom or a constructor, a call's arguments and result, a place
read or write, the scrutinee of a `match` or `case`, whose payload is copied into the arm, and a
loop's accumulator. Each place selector pays `κ.place`, each memory operation pays `κ.mem`, and an
extern call pays `κ.ext`.

Nothing is charged for a value that is not copied. A conditional's arms write their values where
the conditional's value goes, so the join itself is free. A reference is the place's address,
together with a length for a slice, so a borrow pays `κ.ref` and its address computation, and a
call passes each `&` or `&mut` argument for `κ.ref` and its selectors. The body of a borrow or of
a call with references writes its result where the continuation's variable lives.

The mode `hb : Hb` says how the value of a term reaches its consumer. A function with `&mut`
parameters returns their final values with its result, a mutable borrow's body returns the
borrowed value, and a loop body returns the variables it writes with its accumulator. These
components are handed back in place, so in mode `split` a tail constructor pays only for its first
argument. The reactor step hands back its root in place when every tail of it is the root's
variable, which is mode `whole`, and such a tail atom pays no words.
-/

namespace Millipede

/-- One cost constant per construct. -/
structure CostModel where
  atom : Nat
  let_ : Nat
  ite : Nat
  /-- arithmetic, bitwise and comparison primitives -/
  prim : Nat
  /-- division and remainder -/
  div : Nat
  /-- loop entry -/
  loop : Nat
  /-- per-iteration overhead of a loop -/
  iter : Nat
  call : Nat
  /-- `ok` and `err` -/
  ctor : Nat
  match_ : Nat
  ext : Nat
  /-- per 64-bit word moved or copied -/
  word : Nat
  /-- per place selector, which is a field, an index, a cell, a slice or an element -/
  place : Nat
  /-- a memory operation, which is a read, an assignment, `put`, `take` or a guard -/
  mem : Nat
  /-- making a reference by a borrow or by passing one `&` or `&mut` argument, which is an
  address and, for a slice, a length, whatever the width of the referenced value -/
  ref : Nat
deriving Repr

/-- The words moved when a value of type `t` is copied, which is the width of its shape. -/
abbrev Ty.words (t : Ty) : Nat := t.data.shape.words

/-- The words occupied by values of the types in a context. -/
def ctxWords : List Ty → Nat
  | [] => 0
  | t :: ts => t.data.shape.words + ctxWords ts

@[simp] theorem ctxWords_nil : ctxWords [] = 0 := rfl
@[simp] theorem ctxWords_cons (t : Ty) (ts : List Ty) :
    ctxWords (t :: ts) = t.words + ctxWords ts := rfl
@[simp] theorem Ty.words_u64 : Ty.u64.words = 1 := rfl
@[simp] theorem Ty.words_bool : Ty.bool.words = 1 := rfl
@[simp] theorem Ty.words_unit : Ty.unit.words = 0 := rfl
@[simp] theorem Ty.words_result (ε α : Ty) :
    (Ty.result ε α).words = 1 + max ε.words α.words := by
  simp only [Ty.words, Data.shape, Shape.words, Shape.wordsMax]
  omega

/-- The number of selectors of the places a guard tests. -/
def Guard.depth {Γ : List Ty} : Guard Γ → Nat
  | .valid p _ => p.depth

/-- The words of the owned arguments of a call, which are copied into the callee's frame.
Reference arguments are addresses and cost only their selectors and a constant each. -/
def RArgs.ownWords {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own (t := t) _ as => t.words + as.ownWords
  | _, _, .shr _ as => as.ownWords
  | _, _, .mut _ as => as.ownWords

/-- The number of reference arguments of a call. -/
def RArgs.refs {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own _ as => as.refs
  | _, _, .shr _ as => as.refs + 1
  | _, _, .mut _ as => as.refs + 1

/-- The cost of passing the arguments of a call. Each owned argument costs its words, and each
reference argument costs `κ.ref` and `κ.place` per selector. -/
def RArgs.cost {Γ : List Ty} {ps os : List Ty} (κ : CostModel) (as : RArgs Γ ps os) : Nat :=
  as.depth * κ.place + as.refs * κ.ref + as.ownWords * κ.word

/-- The cost of passing the slice arguments of an extern call, each of which is an address and a
length and costs `κ.ref` and `κ.place` per selector. -/
def EArgs.cost {Γ : List Ty} {ps : List ExtParam} (κ : CostModel) (as : EArgs Γ ps) : Nat :=
  κ.place * as.depth + κ.ref * as.slices

/-- The cost of one primitive under `κ`. -/
def Prim.cost {ps : List Ty} {r : Ty} (κ : CostModel) : Prim ps r → Nat
  | .udiv => κ.div
  | .umod => κ.div
  | _ => κ.prim

/-- How the value of a term reaches its consumer, which decides what its tail copies:
* `copy`: the value is written where its consumer reads it;
* `whole x`: the value is variable `x`'s, handed back in place, and nothing is copied;
* `split`: the value is a pair or tuple whose first component is written and whose other
  components, the final values of `&mut` parameters or of loop-carried variables, are handed back
  in place. -/
inductive Hb where
  | copy
  | whole (x : Nat)
  | split
deriving DecidableEq, Repr

/-- The mode under one more binder. -/
def Hb.up : Hb → Hb
  | .whole x => .whole (x + 1)
  | h => h

/-- `split` when some component is handed back in place, and `copy` otherwise. -/
def Hb.of (b : Bool) : Hb := if b then .split else .copy

/-- The words that a tail atom of type `t` copies. -/
def Hb.atomW (t : Ty) : Hb → Nat
  | .whole _ => 0
  | _ => t.words

/-- The words that a tail constructor of type `t` with argument types `ps` copies: in mode `split`
only its first argument. -/
def Hb.mkW (ps : List Ty) (t : Ty) : Hb → Nat
  | .split => match ps with
    | p :: _ => p.words
    | [] => t.words
  | _ => t.words

@[simp] theorem Hb.up_copy : Hb.copy.up = .copy := rfl
@[simp] theorem Hb.up_split : Hb.split.up = .split := rfl
@[simp] theorem Hb.up_whole (x : Nat) : (Hb.whole x).up = .whole (x + 1) := rfl

/-- Every tail of the term is variable `x`, through `let`, branches and the continuations of
statements, so that its value is that variable's and can be handed back in place. -/
def Exp.tailVar : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → Bool
  | _, _, .atom (.var m), x => m.idx == x
  | _, _, .let_ _ e₂, x => e₂.tailVar (x + 1)
  | _, _, .ite _ e₁ e₂, x => e₁.tailVar x && e₂.tailVar x
  | _, _, .match_ _ eE eO, x => eE.tailVar (x + 1) && eO.tailVar (x + 1)
  | _, _, .assign _ _ k, x => k.tailVar x
  | _, _, .case _ _ eP eQ, x => eP.tailVar (x + 1) && eQ.tailVar (x + 1)
  | _, _, .put _ _ _ k, x => k.tailVar x
  | _, _, .take (dflt := _) _ _ k, x => k.tailVar (x + 1)
  | _, _, .borrowShr _ _ k, x => k.tailVar (x + 1)
  | _, _, .borrowMut _ _ k, x => k.tailVar (x + 1)
  | _, _, .callRef _ _ _ _ k, x => k.tailVar (x + 1)
  | _, _, .extMut _ _ k, x => k.tailVar (x + 1)
  | _, _, .loop _ _ _ _ _ k, x => k.tailVar (x + 1)
  | _, _, _, _ => false

/-- The static step bound of a term, computed from syntax. -/
def Exp.cost (κ : CostModel) : {Γ : List Ty} → {t : Ty} → Hb → Exp Γ t → Nat
  | _, _, hb, .atom (t := t) _ => κ.atom + hb.atomW t * κ.word
  | _, _, hb, .let_ e₁ e₂ => κ.let_ + e₁.cost κ .copy + e₂.cost κ hb.up
  | _, _, hb, .ite _ e₁ e₂ => κ.ite + max (e₁.cost κ hb) (e₂.cost κ hb)
  | _, _, _, .prim p _ => p.cost κ
  | _, _, _, .call (ps := ps) (r := r) _ body _ =>
    κ.call + (ctxWords ps + r.words) * κ.word + body.cost κ .copy
  | _, _, _, .ok (ε := ε) (α := α) _ => κ.ctor + (Ty.result ε α).words * κ.word
  | _, _, _, .err (ε := ε) (α := α) _ => κ.ctor + (Ty.result ε α).words * κ.word
  | _, _, hb, .match_ (ε := ε) (α := α) _ eE eO =>
    κ.match_ + (Ty.result ε α).words * κ.word + max (eE.cost κ hb.up) (eO.cost κ hb.up)
  | _, _, _, .ext _ args => κ.ext + args.cost κ
  | _, _, hb, .extMut _ args k => κ.ext + args.cost κ + k.cost κ hb.up
  | _, _, hb, .mk (ps := ps) (t := t) _ _ => κ.ctor + hb.mkW ps t * κ.word
  | _, _, _, .read (t := t) p => κ.mem + p.depth * κ.place + t.words * κ.word
  | _, _, hb, .assign (t := t) p _ k => κ.mem + p.depth * κ.place + t.words * κ.word + k.cost κ hb
  | _, _, hb, .case (t := t) _ _ eP eQ =>
    κ.match_ + t.words * κ.word + max (eP.cost κ hb.up) (eQ.cost κ hb.up)
  | _, _, hb, .put (t := t) p _ _ k =>
    κ.mem + (p.depth + 1) * κ.place + t.words * κ.word + k.cost κ hb
  | _, _, hb, .take (t := t) (dflt := _) p _ k =>
    κ.mem + (p.depth + 1) * κ.place + t.words * κ.word + k.cost κ hb.up
  | _, _, hb, .borrowShr p body k =>
    κ.ref + p.depth * κ.place + body.cost κ .copy + k.cost κ hb.up
  | _, _, hb, .borrowMut p body k =>
    κ.ref + p.depth * κ.place + body.cost κ .split + k.cost κ hb.up
  | _, _, hb, .callRef (os := os) _ _ body args k =>
    κ.call + args.cost κ + body.cost κ (Hb.of !os.isEmpty) + k.cost κ hb.up
  | _, _, _, .guard g => κ.mem + g.depth * κ.place
  | _, _, hb, .loop (ts := ts) (s := s) n _ _ c body k =>
    κ.loop + s.words * κ.word +
      n * (κ.iter + s.words * κ.word + c.cost κ .copy + body.cost κ (Hb.of !ts.isEmpty)) +
      k.cost κ hb.up

/-- The result of an instrumented run, which is the value, the world with its events, and the
number of steps taken. -/
structure Out (α : Type) where
  val : α
  world : World
  steps : Nat

/-- The instrumented loop driver, which charges `κ.iter` for each iteration started. It recurses
structurally on `n`. -/
def loopExec {σ : Type} (κ : CostModel) (cond : UInt64 → σ → World → Out Bool)
    (body : UInt64 → σ → World → Out σ) : Nat → Nat → σ → World → Out σ
  | 0, _, acc, w => ⟨acc, w, 0⟩
  | n + 1, i, acc, w =>
    let c := cond (UInt64.ofNat i) acc w
    match c.val with
    | false => ⟨acc, c.world, κ.iter + c.steps⟩
    | true =>
      let b := body (UInt64.ofNat i) acc c.world
      let r := loopExec κ cond body n (i + 1) b.val b.world
      ⟨r.val, r.world, κ.iter + c.steps + b.steps + r.steps⟩

/-- The instrumented semantics, which returns the value, the world and the steps of the path
actually taken. -/
def Exp.exec (ω : Oracle) (κ : CostModel) :
    {Γ : List Ty} → {t : Ty} → Hb → Exp Γ t → Env Γ → World → Out t.carrier
  | _, _, hb, .atom (t := t) a, env, w => ⟨a.denote env, w, κ.atom + hb.atomW t * κ.word⟩
  | _, _, hb, .let_ e₁ e₂, env, w =>
    let r₁ := e₁.exec ω κ .copy env w
    let r₂ := e₂.exec ω κ hb.up (.cons r₁.val env) r₁.world
    ⟨r₂.val, r₂.world, κ.let_ + r₁.steps + r₂.steps⟩
  | _, _, hb, .ite c e₁ e₂, env, w =>
    match (c.denote env : Bool) with
    | true => let r := e₁.exec ω κ hb env w; ⟨r.val, r.world, κ.ite + r.steps⟩
    | false => let r := e₂.exec ω κ hb env w; ⟨r.val, r.world, κ.ite + r.steps⟩
  | _, _, _, .prim p args, env, w => ⟨p.denote (args.denote env), w, p.cost κ⟩
  | _, _, _, .call (ps := ps) (r := rt) _ body args, env, w =>
    let r := body.exec ω κ .copy (args.denote env) w
    ⟨r.val, r.world, κ.call + (ctxWords ps + rt.words) * κ.word + r.steps⟩
  | _, _, _, .ok (ε := ε) (α := α) a, env, w =>
    ⟨Except.ok (a.denote env), w, κ.ctor + (Ty.result ε α).words * κ.word⟩
  | _, _, _, .err (ε := ε) (α := α) a, env, w =>
    ⟨Except.error (a.denote env), w, κ.ctor + (Ty.result ε α).words * κ.word⟩
  | _, _, hb, @Exp.match_ _ ε α _ s eE eO, env, w =>
    match (s.denote env : Except ε.carrier α.carrier) with
    | .error e => let r := eE.exec ω κ hb.up (.cons e env) w
      ⟨r.val, r.world, κ.match_ + (Ty.result ε α).words * κ.word + r.steps⟩
    | .ok a => let r := eO.exec ω κ hb.up (.cons a env) w
      ⟨r.val, r.world, κ.match_ + (Ty.result ε α).words * κ.word + r.steps⟩
  | _, _, _, .ext sig args, env, w =>
    let r := w.call ω (sig.call args env) sig.noreturn
    ⟨r.1, r.2, κ.ext + args.cost κ⟩
  | _, _, hb, .extMut sig args k, env, w =>
    let r := w.ask ω (sig.call args env) sig.noreturn
    let rk := k.exec ω κ hb.up (.cons r.1.result
      (args.fill env env (fitOut (sig.call args env).outCaps r.1.bytesOut))) r.2
    ⟨rk.val, rk.world, κ.ext + args.cost κ + rk.steps⟩
  | _, _, hb, .mk (ps := ps) (t := t) c args, env, w =>
    ⟨c.build (args.denote env), w, κ.ctor + hb.mkW ps t * κ.word⟩
  | _, _, _, .read (t := t) p, env, w =>
    ⟨p.get env, w, κ.mem + p.depth * κ.place + t.words * κ.word⟩
  | _, _, hb, .assign (t := t) p a k, env, w =>
    let r := k.exec ω κ hb (p.set env (a.denote env)) w
    ⟨r.val, r.world, κ.mem + p.depth * κ.place + t.words * κ.word + r.steps⟩
  | _, _, hb, .case (t := t) s sp eP eQ, env, w =>
    match sp.split (s.denote env) with
    | .inl x => let r := eP.exec ω κ hb.up (.cons x env) w
      ⟨r.val, r.world, κ.match_ + t.words * κ.word + r.steps⟩
    | .inr y => let r := eQ.exec ω κ hb.up (.cons y env) w
      ⟨r.val, r.world, κ.match_ + t.words * κ.word + r.steps⟩
  | _, _, hb, .put (t := t) p i a k, env, w =>
    let r := k.exec ω κ hb
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some (a.denote env)))) w
    ⟨r.val, r.world, κ.mem + (p.depth + 1) * κ.place + t.words * κ.word + r.steps⟩
  | _, _, hb, .take (t := t) (dflt := _) p i k, env, w =>
    let r := k.exec ω κ hb.up (.cons (((p.get env : Slots _ _).cell (i.denote env).toNat).getD default)
      (p.set env (Slots.setCell (p.get env) (i.denote env).toNat none))) w
    ⟨r.val, r.world, κ.mem + (p.depth + 1) * κ.place + t.words * κ.word + r.steps⟩
  | _, _, hb, .borrowShr p body k, env, w =>
    let rb := body.exec ω κ .copy (.cons (p.get env) env) w
    let rk := k.exec ω κ hb.up (.cons rb.val env) rb.world
    ⟨rk.val, rk.world, κ.ref + p.depth * κ.place + rb.steps + rk.steps⟩
  | _, _, hb, .borrowMut p body k, env, w =>
    let rb := body.exec ω κ .split (.cons (p.get env) env) w
    let rk := k.exec ω κ hb.up (.cons rb.val.1 (p.set env rb.val.2)) rb.world
    ⟨rk.val, rk.world, κ.ref + p.depth * κ.place + rb.steps + rk.steps⟩
  | _, _, hb, .callRef (os := os) _ _ body args k, env, w =>
    let rb := body.exec ω κ (Hb.of !os.isEmpty) (args.denote env) w
    let rk := k.exec ω κ hb.up (.cons rb.val.1 (args.writeBack env rb.val.2)) rb.world
    ⟨rk.val, rk.world, κ.call + args.cost κ + rb.steps + rk.steps⟩
  | _, _, _, .guard g, env, w =>
    ⟨if g.denote env then .ok () else .error (), w, κ.mem + g.depth * κ.place⟩
  | _, _, hb, .loop (ts := ts) (s := s) n cs init c body k, env, w =>
    let r := loopExec { κ with iter := κ.iter + s.words * κ.word }
      (fun i st w => c.exec ω κ .copy (.cons i (.cons st.1 (cs.set env st.2))) w)
      (fun i st w => body.exec ω κ (Hb.of !ts.isEmpty) (.cons i (.cons st.1 (cs.set env st.2))) w)
      n 0 (init.denote env, cs.get env) w
    let rk := k.exec ω κ hb.up (.cons r.val.1 (cs.set env r.val.2)) r.world
    ⟨rk.val, rk.world, κ.loop + s.words * κ.word + r.steps + rk.steps⟩

theorem loopExec_sound {σ : Type} (κ : CostModel)
    (condE : UInt64 → σ → World → Out Bool) (bodyE : UInt64 → σ → World → Out σ)
    (condD : UInt64 → σ → World → Bool × World) (bodyD : UInt64 → σ → World → σ × World)
    (kc kb : Nat)
    (hc : ∀ i a w, (condE i a w).val = (condD i a w).1 ∧ (condE i a w).world = (condD i a w).2 ∧
      (condE i a w).steps ≤ kc)
    (hb : ∀ i a w, (bodyE i a w).val = (bodyD i a w).1 ∧ (bodyE i a w).world = (bodyD i a w).2 ∧
      (bodyE i a w).steps ≤ kb) :
    ∀ n i acc w,
      (loopExec κ condE bodyE n i acc w).val = (loopDenote condD bodyD n i acc w).1 ∧
      (loopExec κ condE bodyE n i acc w).world = (loopDenote condD bodyD n i acc w).2 ∧
      (loopExec κ condE bodyE n i acc w).steps ≤ n * (κ.iter + kc + kb) := by
  intro n
  induction n <;> intro i acc w
  case zero => simp [loopExec, loopDenote]
  case succ n ih =>
    have := hc (UInt64.ofNat i) acc w
    have := hb (UInt64.ofNat i) acc (condE (UInt64.ofNat i) acc w).world
    have := ih (i + 1) (bodyE (UInt64.ofNat i) acc (condE (UInt64.ofNat i) acc w).world).val
      (bodyE (UInt64.ofNat i) acc (condE (UInt64.ofNat i) acc w).world).world
    grind [loopExec, loopDenote]

/-- The cost bound is sound. For every oracle `ω`, cost model `κ`, mode, environment and world, the
instrumented semantics computes exactly the value and the world of `denote`, and so the same
events, and takes at most `e.cost κ hb` steps. -/
theorem Exp.exec_sound (ω : Oracle) (κ : CostModel) {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ (hb : Hb) (env : Env Γ) (w : World),
      (e.exec ω κ hb env w).val = (e.denote ω env w).1 ∧
      (e.exec ω κ hb env w).world = (e.denote ω env w).2 ∧
      (e.exec ω κ hb env w).steps ≤ e.cost κ hb := by
  induction e <;> intro hb env w
  case match_ s eE eO ihE ihO =>
    cases hs' : (s.denote env : Except _ _) <;>
      simp only [Exp.exec, Exp.denote, Exp.cost, hs', Except.elim_error, Except.elim_ok] <;> grind
  case loop ts s u n cs init c body k ihc ihb ihk =>
    obtain ⟨hv, hw, hs⟩ := loopExec_sound { κ with iter := κ.iter + s.words * κ.word }
      (fun i st => c.exec ω κ .copy (.cons i (.cons st.1 (cs.set env st.2))))
      (fun i st => body.exec ω κ (Hb.of !ts.isEmpty) (.cons i (.cons st.1 (cs.set env st.2))))
      (fun i st => c.denote ω (.cons i (.cons st.1 (cs.set env st.2))))
      (fun i st => body.denote ω (.cons i (.cons st.1 (cs.set env st.2)))) (c.cost κ .copy)
      (body.cost κ (Hb.of !ts.isEmpty))
      (fun i a w => ihc _ _ w) (fun i a w => ihb _ _ w) n 0 (init.denote env, cs.get env) w
    simp only [Exp.exec, Exp.denote, Exp.cost]
    rw [hv, hw]
    refine ⟨(ihk _ _ _).1, (ihk _ _ _).2.1, ?_⟩
    exact Nat.add_le_add (Nat.add_le_add_left hs _) (ihk _ _ _).2.2
  all_goals grind [Exp.exec, Exp.denote, Exp.cost]

/-- The value of `exec` is the value of `denote`. -/
theorem Exp.exec_val (ω : Oracle) (κ : CostModel) {Γ : List Ty} {t : Ty} {hb : Hb} (e : Exp Γ t)
    (env : Env Γ) (w : World) : (e.exec ω κ hb env w).val = (e.denote ω env w).1 :=
  (e.exec_sound ω κ hb env w).1

/-- The world of `exec`, and so its events, is the world of `denote`. -/
theorem Exp.exec_world (ω : Oracle) (κ : CostModel) {Γ : List Ty} {t : Ty} {hb : Hb} (e : Exp Γ t)
    (env : Env Γ) (w : World) : (e.exec ω κ hb env w).world = (e.denote ω env w).2 :=
  (e.exec_sound ω κ hb env w).2.1

/-- `exec` never takes more than `cost` steps. -/
theorem Exp.exec_steps_le (ω : Oracle) (κ : CostModel) {Γ : List Ty} {t : Ty} {hb : Hb}
    (e : Exp Γ t) (env : Env Γ) (w : World) : (e.exec ω κ hb env w).steps ≤ e.cost κ hb :=
  (e.exec_sound ω κ hb env w).2.2

end Millipede
