import Millipede.Analysis.Domain

/-!
# The obligation analyser

`Exp.an e A` interprets `e` over the abstract domain from the abstract environment `A` and returns
a `Res`. The result says whether every obligation of `e` is certified, describes its value, and
for a loop body describes the components of the tuple it hands back. The analyser is structurally
recursive and computes on `Nat`, `Bool` and `List` only, so the kernel can evaluate it with
`decide`.

The analyser treats each kind of term as follows.
- A primitive is interpreted by `anPrim` with interval arithmetic on words. `+ - *` are exact when
  the bounds show no wrap, and `/ % &&& >>> <<<` are bounded. Bytes go through `zext8` and
  `trunc8`, and comparisons become facts. The obligation of a `…Nuw` primitive is certified when
  the intervals show no overflow, and for `-` also when the path knows `y ≤ x`.
- A place is certified when an index is below the array's length, a slice lies inside it, or the
  two indices of a pair are in range and differ. `Slots` cells are not certified, because their
  fullness is not a number.
- A branch refines the environment by the comparisons that its condition implies.
- A write forgets the variables it may change, and assigning a word variable records the
  description of the value assigned.
- A loop, analysed by `loopAn`, has its counter in `[0, n - 1]`. Its state, the accumulator and the
  carried variables, is described by candidates `Cand` that hold at every iteration. There are up
  to three attempts. The first uses the initial values, and the second, per component, either the
  join with the first iteration's result or, for a component that grows by at most `d` per
  iteration, the bound `c0 + d · i` affine in the counter, with the loop bound as the widening
  limit. The third uses top. Each attempt is checked by `Cand.ok`, so the soundness proof never
  trusts the widening.
- `put` and `take`, whose obligation is a `Slots` cell's occupancy, `callRef`, whose obligation is
  the callee's `requires`, a loop of `2^64` iterations or more, and a loop carrying a variable
  twice are not certified.

The loop body's hand-back tuple is read component by component from its tail constructor.
`Exp.TailsOk`, part of the hypothesis `Exp.LoopsOk` of the soundness theorem, says that this
constructor builds the tuple of its arguments, and `rfl` proves it for the terms that `mp def`
emits. The obligations are described in doc/design/obligations.md.
-/

namespace Millipede.Analysis

open Millipede

variable {Γ : List Ty}

/-! ## Interval transfer functions -/

/-- `x + y` on words, exact when the bounds show no wrap. -/
def wAdd (a b : Itv) : Itv := if a.hi + b.hi ≤ wmax then ⟨a.lo + b.lo, a.hi + b.hi⟩ else Itv.top
/-- `x * y` on words. -/
def wMul (a b : Itv) : Itv := if a.hi * b.hi ≤ wmax then ⟨a.lo * b.lo, a.hi * b.hi⟩ else Itv.top
/-- `x - y` on words when `y ≤ x` is known, given by `ge`, and top otherwise. -/
def wSub (ge : Bool) (a b : Itv) : Itv := if ge then ⟨a.lo - b.hi, a.hi - b.lo⟩ else Itv.top
/-- `x / y`, where `x / 0 = 0`. -/
def wDiv (a b : Itv) : Itv := if 0 < b.lo then ⟨a.lo / b.hi, a.hi / b.lo⟩ else ⟨0, a.hi⟩
/-- `x % y`, where `x % 0 = x`. -/
def wMod (a b : Itv) : Itv := ⟨0, if 0 < b.lo then min a.hi (b.hi - 1) else a.hi⟩
/-- `x &&& y`. -/
def wAnd (a b : Itv) : Itv := ⟨0, min a.hi b.hi⟩
/-- `x >>> y`, with the amount taken modulo 64. -/
def wShr (a b : Itv) : Itv :=
  if b.lo = b.hi ∧ b.hi < 64 then ⟨a.lo / 2 ^ b.hi, a.hi / 2 ^ b.hi⟩ else ⟨0, a.hi⟩
/-- `x <<< y`, with the amount taken modulo 64. -/
def wShl (a b : Itv) : Itv :=
  if b.lo = b.hi ∧ b.hi < 64 ∧ a.hi * 2 ^ b.hi ≤ wmax then ⟨a.lo * 2 ^ b.hi, a.hi * 2 ^ b.hi⟩
  else Itv.top
/-- Narrowing to a byte. -/
def wTrunc8 (a : Itv) : Itv := if a.hi < 256 then a else Itv.top8

/-! ## Primitives -/

/-- Whether `y ≤ x` is known, from the intervals or from the path. -/
def AEnv.geq (A : AEnv Γ) (x y : Atom Γ .u64) : Bool :=
  (A.atomW y).hi ≤ (A.atomW x).lo || A.has ⟨.le, y, x⟩ || A.has ⟨.lt, y, x⟩

/-- The upper bounds of `x + y`, from those of either operand, when nothing wraps. -/
def AEnv.sumUB (A : AEnv Γ) (x y : Atom Γ .u64) : List (UB Γ) :=
  (A.atomUB x).map (fun u => { u with c0 := u.c0 + (A.atomW y).hi }) ++
    (A.atomUB y).map (fun u => { u with c0 := u.c0 + (A.atomW x).hi })

/-- The value of `x + y`. -/
def AEnv.addV (A : AEnv Γ) (x y : Atom Γ .u64) : AVal Γ :=
  if (A.atomW x).hi + (A.atomW y).hi ≤ wmax then .ofW (wAdd (A.atomW x) (A.atomW y)) (A.sumUB x y)
  else .ofW Itv.top

/-- The first argument. -/
def _root_.Millipede.Args.a0 {t : Ty} {ps : List Ty} : Args Γ (t :: ps) → Atom Γ t
  | .cons a _ => a
/-- The second argument. -/
def _root_.Millipede.Args.a1 {t u : Ty} {ps : List Ty} : Args Γ (t :: u :: ps) → Atom Γ u
  | .cons _ (.cons b _) => b

@[simp] theorem _root_.Millipede.Args.a0_cons {t : Ty} {ps : List Ty} (a : Atom Γ t)
    (as : Args Γ ps) : (Args.cons a as).a0 = a := rfl
@[simp] theorem _root_.Millipede.Args.a1_cons {t u : Ty} {ps : List Ty} (a : Atom Γ t)
    (b : Atom Γ u) (as : Args Γ ps) : (Args.cons a (.cons b as)).a1 = b := rfl

/-- A primitive's analysis, which is whether its obligation is certified and its value. -/
def anPrim (A : AEnv Γ) : {ps : List Ty} → {r : Ty} → Prim ps r → Args Γ ps → Bool × AVal Γ
  | _, _, .add, as => (true, A.addV as.a0 as.a1)
  | _, _, .addNuw, as => ((A.atomW as.a0).hi + (A.atomW as.a1).hi ≤ wmax, A.addV as.a0 as.a1)
  | _, _, .sub, as => (true, .ofW (wSub (A.geq as.a0 as.a1) (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .subNuw, as =>
    (A.geq as.a0 as.a1, .ofW (wSub (A.geq as.a0 as.a1) (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .mul, as => (true, .ofW (wMul (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .mulNuw, as =>
    ((A.atomW as.a0).hi * (A.atomW as.a1).hi ≤ wmax, .ofW (wMul (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .udiv, as => (true, .ofW (wDiv (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .umod, as => (true, .ofW (wMod (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .band, as => (true, .ofW (wAnd (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .bor, _ => (true, {})
  | _, _, .bxor, _ => (true, {})
  | _, _, .shl, as => (true, .ofW (wShl (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .shr, as => (true, .ofW (wShr (A.atomW as.a0) (A.atomW as.a1)))
  | _, _, .bnot, _ => (true, {})
  | _, _, .eq, as => (true, .ofBool [⟨.eq, as.a0, as.a1⟩] [⟨.ne, as.a0, as.a1⟩])
  | _, _, .ne, as => (true, .ofBool [⟨.ne, as.a0, as.a1⟩] [⟨.eq, as.a0, as.a1⟩])
  | _, _, .ult, as => (true, .ofBool [⟨.lt, as.a0, as.a1⟩] [⟨.le, as.a1, as.a0⟩])
  | _, _, .ule, as => (true, .ofBool [⟨.le, as.a0, as.a1⟩] [⟨.lt, as.a1, as.a0⟩])
  | _, _, .ugt, as => (true, .ofBool [⟨.lt, as.a1, as.a0⟩] [⟨.le, as.a0, as.a1⟩])
  | _, _, .uge, as => (true, .ofBool [⟨.le, as.a1, as.a0⟩] [⟨.lt, as.a0, as.a1⟩])
  | _, _, .not, as => (true, .ofBool (A.atomV as.a0).f (A.atomV as.a0).t)
  | _, _, .and, as => (true, .ofBool ((A.atomV as.a0).t ++ (A.atomV as.a1).t) [])
  | _, _, .or, as => (true, .ofBool [] ((A.atomV as.a0).f ++ (A.atomV as.a1).f))
  | _, _, .beq, _ => (true, {})
  | _, _, .zext8, as => (true, .ofW (A.atomV as.a0).b)
  | _, _, .trunc8, as => (true, .ofB (wTrunc8 (A.atomW as.a0)))
  | _, _, .trunc8Nuw, as => ((A.atomW as.a0).hi < 256, .ofB (wTrunc8 (A.atomW as.a0)))

/-! ## Places and extern arguments -/

/-- Whether the place's obligations `Place.ok` are certified. -/
def Place.okA (A : AEnv Γ) : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => Place.okA A p
  | _, .index (n := n) (dflt := _) p i => Place.okA A p && (A.atomW i).hi < n
  | _, .slot (dflt := _) _ _ => false
  | _, .range (n := n) p lo len => Place.okA A p && (A.atomW lo).hi + (A.atomW len).hi ≤ n
  | _, .pair2 (n := n) (dflt := _) p i j =>
    Place.okA A p && (A.atomW i).hi < n && (A.atomW j).hi < n &&
      ((A.atomW i).hi < (A.atomW j).lo || (A.atomW j).hi < (A.atomW i).lo || A.has ⟨.ne, i, j⟩)
  | _, .rangeS _ _ _ => false
  | _, .pair2S (dflt := _) _ _ _ => false

/-- The description of a place's value, which is a variable's own and top otherwise. -/
def Place.readV (A : AEnv Γ) : {t : Ty} → Place Γ t → AVal Γ
  | _, .var m => A.get m.idx
  | _, _ => {}

/-- Whether the obligations `EArgs.ok` of an extern's slice arguments are certified. -/
def EArgs.okA (A : AEnv Γ) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => EArgs.okA A as
  | _, .bufIn (.const _) as => EArgs.okA A as
  | _, .bufIn (.slice (n := n) a lo len) as =>
    Place.okA A a && (A.atomW lo).hi + (A.atomW len).hi ≤ n && EArgs.okA A as
  | _, .bufOut as => EArgs.okA A as
  | _, .sliceOut (n := n) a lo cap as =>
    Place.okA A a && (A.atomW lo).hi + (A.atomW cap).hi ≤ n && EArgs.okA A as

/-- The roots of the slices an extern writes. -/
def EArgs.outRoots : {ps : List ExtParam} → EArgs Γ ps → List Nat
  | _, .nil => []
  | _, .word _ as | _, .bufIn _ as | _, .bufOut as => EArgs.outRoots as
  | _, .sliceOut a _ _ as => a.root :: EArgs.outRoots as

/-- The roots of the `&mut` arguments of a call. -/
def RArgs.mutRoots : {ps os : List Ty} → RArgs Γ ps os → List Nat
  | _, _, .nil => []
  | _, _, .own _ as => RArgs.mutRoots as
  | _, _, .shr _ as => RArgs.mutRoots as
  | _, _, .mut p as => p.root :: RArgs.mutRoots as

/-- Write the value described by `a` to the place `p`. A variable gets the description, without
the facts that mention it, and otherwise the root is forgotten. -/
def AEnv.write {t : Ty} (A : AEnv Γ) (p : Place Γ t) (a : AVal Γ) : AEnv Γ :=
  match p with
  | .var m => (A.kill [m.idx]).setv m.idx (a.forget [m.idx])
  | _ => A.kill [p.root]

/-- The descriptions of call arguments as the callee's environment, with the facts dropped. -/
def argsAVals (A : AEnv Γ) {Δ : List Ty} : {ps : List Ty} → Args Γ ps → List (AVal Δ)
  | _, .nil => []
  | _, .cons a as => (A.atomV a).plain :: argsAVals A as

/-! ## Results -/

/-- The analysis of a term, which records whether its obligations are certified, its value, and
the components of a hand-back tuple. -/
structure Res (Γ : List Ty) where
  ok : Bool
  v : AVal Γ := {}
  cs : List (AVal Γ) := []

/-- Leave a binder. -/
def Res.unshift {s : Ty} (r : Res (s :: Γ)) : Res Γ := ⟨r.ok, r.v.unshift, r.cs.map AVal.unshift⟩

/-- The two arms of a branch. -/
def Res.join (r₁ r₂ : Res Γ) : Res Γ :=
  ⟨r₁.ok && r₂.ok, r₁.v.join r₂.v, List.zipWith AVal.join r₁.cs r₂.cs⟩

/-! ## Loops -/

/-- Whether a word atom is the variable with index 0, which is the loop counter in a body. -/
def _root_.Millipede.Atom.idx0 {t : Ty} : Atom Γ t → Bool
  | .var m => m.idx == 0
  | .lit _ => false


/-- A candidate description of one component of a loop's state at every iteration `j`, which says
that a word lies in `[lo, hi]` and is at most `c0 + d · j`, and that a byte lies in `b`. -/
structure Cand where
  lo : Nat
  hi : Nat
  c0 : Nat
  d : Nat
  b : Itv

namespace Cand

/-- The description at iteration `j`. -/
def atJ (c : Cand) (j : Nat) : AVal Γ := { w := ⟨c.lo, min c.hi (c.c0 + c.d * j)⟩, b := c.b }
/-- Top. -/
def top : Cand := ⟨0, wmax, wmax, 0, Itv.top8⟩
/-- The candidate from the description of the initial value. -/
def ofAVal (a : AVal Γ) : Cand := ⟨a.w.lo, a.w.hi, a.w.hi, 0, a.b⟩
/-- Whether the initial value is described at iteration 0. -/
def init (c : Cand) (a : AVal Γ) : Bool :=
  c.lo ≤ a.w.lo && a.w.hi ≤ c.hi && a.w.hi ≤ c.c0 && a.b.sub c.b
/-- Whether the value handed back by an iteration, described by `o` in the body, whose index 0 is
the counter, is described at the next iteration. -/
def ok (c : Cand) (o : AVal Γ) : Bool :=
  c.lo ≤ o.w.lo && o.w.hi ≤ c.hi && o.b.sub c.b &&
    (o.w.hi ≤ c.c0 + c.d ||
      o.ub.any fun u => u.y.idx0 && u.c0 ≤ c.c0 + c.d && u.d ≤ c.d)
/-- The next candidate after a failed check. It is the join with the iteration's result, or, when
the result grows by a constant `δ` per iteration, the bound `c0 + δ · j`. -/
def widen (c : Cand) (o : AVal Γ) : Cand :=
  if c.ok o then c else
  match o.ub.find? (fun u => u.y.idx0 && u.d == 0 && c.c0 < u.c0) with
  | some u => ⟨min c.lo o.w.lo, wmax, c.c0, u.c0 - c.c0, c.b.join o.b⟩
  | none => let h := max c.hi o.w.hi; ⟨min c.lo o.w.lo, h, h, 0, c.b.join o.b⟩

end Cand

/-- The carried variables described by candidates at iteration `j`, after forgetting them. -/
def AEnv.setCands (j : Nat) {ts : List Ty} (A : AEnv Γ) : Carry Γ ts → List Cand → AEnv Γ
  | .cons m cs, c :: cc => AEnv.setCands j (A.setv m.idx (c.atJ j)) cs cc
  | _, _ => A

/-- The candidate of each carried variable, from its current description. -/
def candsOf (A : AEnv Γ) {ts : List Ty} : Carry Γ ts → List Cand
  | .nil => []
  | .cons m cs => Cand.ofAVal (A.get m.idx) :: candsOf A cs

/-- The environment of the continuation, and of an iteration `j`, with the accumulator and the
carried variables at iteration `j`. -/
def stateA {s : Ty} {ts : List Ty} (A : AEnv Γ) (cs : Carry Γ ts) (j : Nat) (ca : Cand)
    (cc : List Cand) : AEnv (s :: Γ) :=
  ((A.kill cs.idxs).setCands j cs cc).push (ca.atJ j)

/-- Add the bound `≤ c0 + d · (variable 0)` to variable `pos`. -/
def AEnv.addUB {Δ : List Ty} (A : AEnv (.u64 :: Δ)) (pos : Nat) (c : Cand) : AEnv (.u64 :: Δ) :=
  A.setv pos { A.get pos with ub := ⟨c.c0, c.d, .var .here⟩ :: (A.get pos).ub }

/-- The bounds of the carried variables, which are at `idx + 2` in the body. -/
def AEnv.addUBs {Δ : List Ty} (A : AEnv (.u64 :: Δ)) {ts : List Ty} :
    Carry Γ ts → List Cand → AEnv (.u64 :: Δ)
  | .cons m cs, c :: cc => AEnv.addUBs (A.addUB (m.idx + 2) c) cs cc
  | _, _ => A

/-- The environment of the loop body, with the counter in `[0, n - 1]` and the state at its
widest, at iteration `n - 1`, together with its growth bounds in the counter. -/
def bodyA {s : Ty} {ts : List Ty} (n : Nat) (A : AEnv Γ) (cs : Carry Γ ts) (ca : Cand)
    (cc : List Cand) : AEnv (.u64 :: s :: Γ) :=
  ((((stateA (s := s) A cs (n - 1) ca cc).push (.ofW ⟨0, n - 1⟩)).addUB 1 ca).addUBs cs cc)

/-- Whether every candidate holds of the handed-back value described by `os`, where missing
descriptions are top. -/
def candsOk {Δ : List Ty} : List Cand → List (AVal Δ) → Bool
  | [], _ => true
  | c :: cc, os => c.ok (os.headD {}) && candsOk cc os.tail

/-- The candidates after a failed attempt. -/
def candsWiden {Δ : List Ty} : List Cand → List (AVal Δ) → List Cand
  | [], _ => []
  | c :: cc, os => c.widen (os.headD {}) :: candsWiden cc os.tail

/-- Whether the initial values are described. -/
def candsInit (A : AEnv Γ) {ts : List Ty} : Carry Γ ts → List Cand → Bool
  | .cons m cs, c :: cc => c.init (A.get m.idx) && candsInit A cs cc
  | .nil, [] => true
  | _, _ => false

/-- One attempt with candidates, holding the condition's and the body's analyses in the body
environment and whether the candidates hold. -/
structure Attempt (Δ : List Ty) where
  ca : Cand
  cc : List Cand
  ok : Bool
  valid : Bool
  outs : List (AVal Δ)

/-- The attempt with the candidates `ca` for the accumulator and `cc` for the carried
variables. -/
def loopAttempt {s : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts) (A : AEnv Γ) (a0 : AVal Γ)
    (fc fb : AEnv (.u64 :: s :: Γ) → Res (.u64 :: s :: Γ)) (ca : Cand) (cc : List Cand) :
    Attempt (.u64 :: s :: Γ) :=
  let B := bodyA n A cs ca cc
  let rc := fc B
  let rb := fb (B.assumeAll rc.v.t)
  ⟨ca, cc, rc.ok && rb.ok, ca.init a0 && candsInit A cs cc && candsOk (ca :: cc) rb.cs, rb.cs⟩

/-- Up to three attempts, with the initial values, then widened, then top. -/
def loopPick {s : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts) (A : AEnv Γ) (a0 : AVal Γ)
    (fc fb : AEnv (.u64 :: s :: Γ) → Res (.u64 :: s :: Γ)) : Attempt (.u64 :: s :: Γ) :=
  let at1 := loopAttempt n cs A a0 fc fb (Cand.ofAVal a0) (candsOf A cs)
  if at1.valid then at1 else
  let at2 := loopAttempt n cs A a0 fc fb ((Cand.ofAVal a0).widen (at1.outs.headD {}))
    (candsWiden (candsOf A cs) at1.outs.tail)
  if at2.valid then at2 else loopAttempt n cs A a0 fc fb Cand.top (cs.idxs.map fun _ => Cand.top)

/-- The analysis of a loop `loop n cs init c body k` from `A`, given the analyses of `c`, `body`
and `k` as functions of their environments. -/
def loopAn {s : Ty} {ts : List Ty} (n : Nat) (cs : Carry Γ ts) (a0 : AVal Γ)
    (fc fb : AEnv (.u64 :: s :: Γ) → Res (.u64 :: s :: Γ))
    (fk : AEnv (s :: Γ) → Res (s :: Γ)) (A : AEnv Γ) : Res Γ :=
  if n < 2 ^ 64 && cs.distinct then
    let att := loopPick n cs A a0 fc fb
    let rk := fk (if att.valid then stateA A cs n att.ca att.cc else (A.kill cs.idxs).push {})
    ⟨att.valid && att.ok && rk.ok, rk.v.unshift.forget cs.idxs, []⟩
  else
    let rk := fk ((A.kill cs.idxs).push {})
    ⟨false, rk.v.unshift.forget cs.idxs, []⟩

/-! ## Relaxing the certified overflow obligations -/

/-- The wrapping twin of an obligated primitive. Every other primitive is its own twin. -/
def _root_.Millipede.Prim.wrap : {ps : List Ty} → {r : Ty} → Prim ps r → Prim ps r
  | _, _, .addNuw => .add
  | _, _, .subNuw => .sub
  | _, _, .mulNuw => .mul
  | _, _, .trunc8Nuw => .trunc8
  | _, _, p => p

/-- Whether a primitive is an obligated one. -/
def _root_.Millipede.Prim.isNuw {ps : List Ty} {r : Ty} (p : Prim ps r) : Bool := !p.total

/-- The number of obligated primitives of a term, not counting callee bodies. -/
def _root_.Millipede.Exp.nuwCount : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .let_ e₁ e₂ => e₁.nuwCount + e₂.nuwCount
  | _, _, .ite _ e₁ e₂ => e₁.nuwCount + e₂.nuwCount
  | _, _, .prim p _ => if p.isNuw then 1 else 0
  | _, _, .match_ _ eE eO => eE.nuwCount + eO.nuwCount
  | _, _, .extMut _ _ k => k.nuwCount
  | _, _, .assign _ _ k => k.nuwCount
  | _, _, .case _ _ eP eQ => eP.nuwCount + eQ.nuwCount
  | _, _, .put _ _ _ k => k.nuwCount
  | _, _, .take (dflt := _) _ _ k => k.nuwCount
  | _, _, .borrowShr _ body k => body.nuwCount + k.nuwCount
  | _, _, .borrowMut _ body k => body.nuwCount + k.nuwCount
  | _, _, .callRef _ _ _ _ k => k.nuwCount
  | _, _, .loop _ _ _ c body k => c.nuwCount + body.nuwCount + k.nuwCount
  | _, _, _ => 0

/-- `e` unchanged, with none of its obligated primitives relaxed. -/
def keep {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Exp Γ t × List Bool :=
  (e, List.replicate e.nuwCount false)

/-! ## The analyser -/

/-- The analyser, which interprets `e` from the abstract environment `A`. The first component is
the analysis `Exp.an`. The second is `e` with the obligated primitives it certifies replaced by
their wrapping twins, together with a flag per obligated primitive of `e` in order, from which
the elaborator rebuilds the relaxed term. -/
def _root_.Millipede.Exp.anR : {Γ : List Ty} → {t : Ty} → Exp Γ t → AEnv Γ →
    Res Γ × (Exp Γ t × List Bool)
  | _, _, .atom a, A => (⟨true, A.atomV a, []⟩, keep (.atom a))
  | _, _, .let_ e₁ e₂, A =>
    let r₁ := e₁.anR A
    let r₂ := e₂.anR (A.push r₁.1.v.shift)
    (⟨r₁.1.ok && r₂.1.unshift.ok, r₂.1.unshift.v, r₂.1.unshift.cs⟩,
      (.let_ r₁.2.1 r₂.2.1, r₁.2.2 ++ r₂.2.2))
  | _, _, .ite c e₁ e₂, A =>
    match c with
    | .lit true => ((e₁.anR A).1, keep (.ite c e₁ e₂))
    | .lit false => ((e₂.anR A).1, keep (.ite c e₁ e₂))
    | .var m =>
      let r₁ := e₁.anR (A.assumeAll (A.get m.idx).t)
      let r₂ := e₂.anR (A.assumeAll (A.get m.idx).f)
      (r₁.1.join r₂.1, (.ite (.var m) r₁.2.1 r₂.2.1, r₁.2.2 ++ r₂.2.2))
  | _, _, .prim p args, A =>
    (⟨(anPrim A p args).1, (anPrim A p args).2, []⟩,
      if p.isNuw then
        if (anPrim A p args).1 then (.prim p.wrap args, [true]) else (.prim p args, [false])
      else (.prim p args, []))
  | _, _, .call f body args, A =>
    (⟨(body.anR ⟨argsAVals A args, []⟩).1.ok, (body.anR ⟨argsAVals A args, []⟩).1.v.plain, []⟩,
      keep (.call f body args))
  | _, _, .ok a, _ => (⟨true, {}, []⟩, keep (.ok a))
  | _, _, .err a, _ => (⟨true, {}, []⟩, keep (.err a))
  | _, _, .match_ s eE eO, A =>
    let rE := eE.anR (A.push {})
    let rO := eO.anR (A.push {})
    let r := rE.1.unshift.join rO.1.unshift
    (⟨r.ok, r.v, []⟩, (.match_ s rE.2.1 rO.2.1, rE.2.2 ++ rO.2.2))
  | _, _, .ext sig args, A => (⟨EArgs.okA A args, {}, []⟩, keep (.ext sig args))
  | _, _, .extMut sig args k, A =>
    let r := k.anR ((A.kill (EArgs.outRoots args)).push {})
    (⟨EArgs.okA A args && r.1.unshift.ok, r.1.unshift.v.forget (EArgs.outRoots args), []⟩,
      (.extMut sig args r.2.1, r.2.2))
  | _, _, .mk c args, A =>
    (⟨true, {}, if c.kind == .tuple then argsAVals' A args else []⟩, keep (.mk c args))
  | _, _, .read p, A => (⟨Place.okA A p, Place.readV A p, []⟩, keep (.read p))
  | _, _, .assign p a k, A =>
    let r := k.anR (A.write p (A.atomV a))
    (⟨Place.okA A p && r.1.ok, r.1.v.forget [p.root], r.1.cs.map (AVal.forget [p.root])⟩,
      (.assign p a r.2.1, r.2.2))
  | _, _, .case s sp eP eQ, A =>
    let rP := eP.anR (A.push {})
    let rQ := eQ.anR (A.push {})
    let r := rP.1.unshift.join rQ.1.unshift
    (⟨r.ok, r.v, []⟩, (.case s sp rP.2.1 rQ.2.1, rP.2.2 ++ rQ.2.2))
  -- Not certified, since the obligation is a `Slots` cell's occupancy. The continuation is still
  -- analysed, for its value and the overflow obligations it relaxes.
  | _, _, .put p i a k, A =>
    let r := k.anR (A.kill [p.root])
    (⟨false, r.1.v.forget [p.root], []⟩, (.put p i a r.2.1, r.2.2))
  | _, _, .take (dflt := _) p i k, A =>
    let r := k.anR ((A.kill [p.root]).push {})
    (⟨false, r.1.unshift.v.forget [p.root], []⟩, (.take p i r.2.1, r.2.2))
  | _, _, .borrowShr p body k, A =>
    let rb := body.anR (A.push (Place.readV A p).shift)
    let rk := k.anR (A.push rb.1.v.unshift.shift)
    (⟨Place.okA A p && rb.1.ok && rk.1.unshift.ok, rk.1.unshift.v, []⟩,
      (.borrowShr p rb.2.1 rk.2.1, rb.2.2 ++ rk.2.2))
  | _, _, .borrowMut p body k, A =>
    let rb := body.anR (A.push (Place.readV A p).shift)
    let rk := k.anR ((A.kill [p.root]).push {})
    (⟨Place.okA A p && rb.1.ok && rk.1.unshift.ok, rk.1.unshift.v.forget [p.root], []⟩,
      (.borrowMut p rb.2.1 rk.2.1, rb.2.2 ++ rk.2.2))
  -- Not certified, since the obligation is the callee's `requires`. The continuation is still
  -- analysed.
  | _, _, .callRef name req body args k, A =>
    let r := k.anR ((A.kill (RArgs.mutRoots args)).push {})
    (⟨false, r.1.unshift.v.forget (RArgs.mutRoots args), []⟩,
      (.callRef name req body args r.2.1, r.2.2))
  | _, _, .guard g, _ => (⟨true, {}, []⟩, keep (.guard g))
  | _, _, .loop n cs init c body k, A =>
    (loopAn n cs (A.atomV init) (fun B => (c.anR B).1) (fun B => (body.anR B).1)
      (fun B => (k.anR B).1) A,
      let att := loopPick n cs A (A.atomV init) (fun B => (c.anR B).1) (fun B => (body.anR B).1)
      if n < 2 ^ 64 && cs.distinct && att.valid then
        let B := bodyA n A cs att.ca att.cc
        let rc := (c.anR B).2
        let rb := (body.anR (B.assumeAll (c.anR B).1.v.t)).2
        let rk := (k.anR (stateA A cs n att.ca att.cc)).2
        (.loop n cs init rc.1 rb.1 rk.1, rc.2 ++ rb.2 ++ rk.2)
      else
        let rk := (k.anR ((A.kill cs.idxs).push {})).2
        (.loop n cs init c body rk.1, (keep c).2 ++ (keep body).2 ++ rk.2))
where
  /-- The descriptions of a constructor's arguments, which are the components of a tuple. -/
  argsAVals' {Γ : List Ty} (A : AEnv Γ) : {ps : List Ty} → Args Γ ps → List (AVal Γ)
    | _, .nil => []
    | _, .cons a as => A.atomV a :: argsAVals' A as

/-- The analysis of `e` from `A`, the first component of `Exp.anR`. -/
abbrev _root_.Millipede.Exp.an {Γ : List Ty} {t : Ty} (e : Exp Γ t) (A : AEnv Γ) : Res Γ :=
  (e.anR A).1

/-- `e` with the obligated primitives that the analyser certifies from `A` relaxed to their
wrapping twins, and the flags, the second component of `Exp.anR`. -/
abbrev _root_.Millipede.Exp.relax {Γ : List Ty} {t : Ty} (e : Exp Γ t) (A : AEnv Γ) :
    Exp Γ t × List Bool :=
  (e.anR A).2

/-! ## The hypothesis on hand-back constructors -/

/-- The tails of a loop body of type `pair s (tup ts)`, from which the analyser reads components
through `let`, `if` and assignments down to a constructor of kind `tuple`, build the tuple of
their arguments. -/
def _root_.Millipede.Exp.TailsOk {s : Ty} {ts : List Ty} :
    {Γ : List Ty} → {t : Ty} → Exp Γ t → t = .pair s (.tup ts) → Prop
  | _, _, .let_ _ e₂, ht => e₂.TailsOk ht
  | _, _, .ite _ e₁ e₂, ht => e₁.TailsOk ht ∧ e₂.TailsOk ht
  | _, _, .assign _ _ k, ht => k.TailsOk ht
  | _, _, .mk (ps := ps) c _, ht => c.kind = .tuple →
    ∃ hps : ps = s :: ts, ∀ env, cast (congrArg Ty.carrier ht) (c.build env) =
      Flat.tupBuild (s :: ts) (hps ▸ env)
  | _, _, _, _ => True

/-- Every loop's body satisfies `TailsOk`, which `rfl` proves for the terms of `mp def`. -/
def _root_.Millipede.Exp.LoopsOk : {Γ : List Ty} → {t : Ty} → Exp Γ t → Prop
  | _, _, .let_ e₁ e₂ => e₁.LoopsOk ∧ e₂.LoopsOk
  | _, _, .ite _ e₁ e₂ => e₁.LoopsOk ∧ e₂.LoopsOk
  | _, _, .call _ body _ => body.LoopsOk
  | _, _, .match_ _ eE eO => eE.LoopsOk ∧ eO.LoopsOk
  | _, _, .extMut _ _ k => k.LoopsOk
  | _, _, .assign _ _ k => k.LoopsOk
  | _, _, .case _ _ eP eQ => eP.LoopsOk ∧ eQ.LoopsOk
  | _, _, .borrowShr _ body k => body.LoopsOk ∧ k.LoopsOk
  | _, _, .borrowMut _ body k => body.LoopsOk ∧ k.LoopsOk
  | _, _, .put _ _ _ k => k.LoopsOk
  | _, _, .take (dflt := _) _ _ k => k.LoopsOk
  | _, _, .callRef _ _ _ _ k => k.LoopsOk
  | _, _, .loop _ _ _ c body k => c.LoopsOk ∧ body.LoopsOk ∧ body.TailsOk rfl ∧ k.LoopsOk
  | _, _, _ => True

end Millipede.Analysis
