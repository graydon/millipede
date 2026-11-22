import Millipede.Core.Program
import Millipede.Core.Checked
import Millipede.Core.WfSound

/-!
# Core tests

These tests write Core terms by hand and check what they mean, what they cost and whether the
checker accepts them. They cover simple functions and calls, loops, the linear `Result` type, a
reactor that writes bytes and exits, a struct updated through `&mut`, an array sum whose
obligation is proved for every length, `Slots`, slice views, enums and the borrow checker.

Each test of a rule has teeth. An obligation that holds is proved next to a term where it fails
and is refuted, and each term the checker rejects sits next to an accepted term that differs only
in the rule's condition. The rejected terms are also shown not to satisfy the property that the
checker guarantees.
-/

namespace Millipede.Tests.Core

open Millipede

/-! ## Small helpers for writing terms by hand -/

/-- Variable with de Bruijn index 0, 1, 2. -/
abbrev v0 {t : Ty} {Γ : List Ty} : Atom (t :: Γ) t := .var .here
abbrev v1 {t s : Ty} {Γ : List Ty} : Atom (s :: t :: Γ) t := .var (.there .here)
abbrev v2 {t s s' : Ty} {Γ : List Ty} : Atom (s' :: s :: t :: Γ) t := .var (.there (.there .here))

/-- A binary primitive applied to two atoms. -/
abbrev bin {Γ : List Ty} {a b r : Ty} (p : Prim [a, b] r) (x : Atom Γ a) (y : Atom Γ b) : Exp Γ r :=
  .prim p (.cons x (.cons y .nil))

/-! ## A function with a branch -/

def f (x : UInt64) : UInt64 := let y := x * x; if y < 100 then y + 1 else y

/-- `let y := x * x; let c := y < 100; if c then y + 1 else y` -/
def f_exp : Exp [.u64] .u64 :=
  .let_ (bin .mul v0 v0)
    (.let_ (bin .ult v0 (.lit 100))
      (.ite v0 (bin .add v1 (.lit 1)) (.atom v1)))

theorem f_exp_correct (ω : Oracle) (w : World) (x : UInt64) :
    f_exp.denote ω (.cons x .nil) w = (f x, w) := by
  simp only [f_exp, f, Exp.denote, Prim.denote, Atom.denote, Args.denote, Env.get_here,
    Env.get_there]
  by_cases h : x * x < 100 <;> simp [h]

example (ω : Oracle) : (f_exp.denote ω (.cons 7 .nil) World.init).1 = 50 := rfl
example (ω : Oracle) : (f_exp.denote ω (.cons 11 .nil) World.init).1 = 121 := rfl

/-! ## A saturating addition and a call

`clampAdd` takes the parameters `x y`, and `y` is the variable with index 0. -/

def clampAdd (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then 18446744073709551615 else s

def clampAdd.fn : Fn [.u64, .u64] .u64 where
  name := "clampAdd"
  body :=
    .let_ (bin .add v1 v0)                 -- s := x + y      ctx: [s, y, x]
      (.let_ (bin .ult v0 v2)              -- c := s < x      ctx: [c, s, y, x]
        (.ite v0 (.atom (.lit 18446744073709551615)) (.atom v1)))

theorem clampAdd.exp_denote (ω : Oracle) (w : World) (x y : UInt64) :
    clampAdd.fn.body.denote ω (.cons y (.cons x .nil)) w = (clampAdd x y, w) := by
  simp only [clampAdd.fn, clampAdd, Exp.denote, Prim.denote, Atom.denote, Args.denote,
    Env.get_here, Env.get_there]
  by_cases h : x + y < x <;> simp [h]

example (ω : Oracle) : (clampAdd.fn.body.denote ω (.cons 5 (.cons 3 .nil)) World.init).1 = 8 :=
  rfl
example (ω : Oracle) :
    (clampAdd.fn.body.denote ω (.cons 1 (.cons 18446744073709551615 .nil)) World.init).1 =
      18446744073709551615 := rfl

/-- A caller: `clampAdd (clampAdd a b) c`, parameters `a b c` (`c` is index 0). Arguments are
listed in the callee's context order (index 0 first), so `clampAdd x y` passes `y, x`. -/
def clamp3 : Exp [.u64, .u64, .u64] .u64 :=
  .let_ (clampAdd.fn.call (.cons v1 (.cons v2 .nil)))       -- s := clampAdd a b
    (clampAdd.fn.call (.cons v1 (.cons v0 .nil)))           -- clampAdd s c

theorem clamp3_denote (ω : Oracle) (w : World) (a b c : UInt64) :
    clamp3.denote ω (.cons c (.cons b (.cons a .nil))) w = (clampAdd (clampAdd a b) c, w) := by
  simp only [clamp3, Fn.call, Exp.denote, Args.denote, Atom.denote, Env.get_here,
    Env.get_there, clampAdd.exp_denote]

/-! ## Loops -/

/-- `let mut acc := 0; for i in 0...n do acc := acc + i`: the sum `0 + 1 + … + (n-1)`, wrapping. -/
def sumTo (n : Nat) : Exp [] .u64 :=
  .loop0 n (.lit 0) (.atom (.lit true)) (bin .add v1 v0)

/-- The list model of the summing loop. -/
def sumModel (i n : Nat) (acc : UInt64) : UInt64 :=
  ((List.range' i n).map UInt64.ofNat).foldl (· + ·) acc

theorem loopDenote_sum (n : Nat) : ∀ (i : Nat) (acc : UInt64) (w : World),
    loopDenote (fun _ _ w => (true, w)) (fun i a w => (a + i, w)) n i acc w =
      (sumModel i n acc, w) := by
  induction n with
  | zero => intro i acc w; simp [loopDenote, sumModel]
  | succ n ih =>
    intro i acc w
    simp only [loopDenote, ih, sumModel, List.range'_succ, List.map_cons, List.foldl_cons]

theorem sumTo_denote (ω : Oracle) (w : World) (n : Nat) :
    (sumTo n).denote ω .nil w = (sumModel 0 n 0, w) := by
  simp only [sumTo, Exp.denote_loop0, Exp.denote, Prim.denote, Atom.denote, Args.denote,
    Env.get_here, Env.get_there]
  exact loopDenote_sum n 0 0 w

example (ω : Oracle) : ((sumTo 10).denote ω .nil World.init).1 = 45 := rfl

theorem sumTo_cost (κ : CostModel) (n : Nat) :
    (sumTo n).cost κ .copy = κ.loop + κ.word +
      n * (κ.iter + κ.word + (κ.atom + κ.word) + (κ.let_ + κ.prim + (κ.ctor + κ.word))) +
      (κ.atom + κ.word) := by
  have h : (Ty.pair .u64 .unit).words = 1 := by decide
  simp [sumTo, Exp.cost, Prim.cost, h, Hb.atomW, Hb.mkW, Hb.of, Hb.up]

/-- The run-time exit: `let mut acc := 0; for i in 0...100 do (if acc ≥ 20 then break); acc := acc + i` stops at `21`. -/
def sumWhile : Exp [] .u64 :=
  .loop0 100 (.lit 0) (bin .ult v1 (.lit 20)) (bin .add v1 v0)

example (ω : Oracle) : (sumWhile.denote ω .nil World.init).1 = 21 := rfl

/-- A cost model whose constants are all 1. Under it the instrumented run of `sumWhile` tests the
condition 8 times and runs the body 7 times, far below the static bound of 100 iterations. -/
def κ1 : CostModel := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/-- An oracle that answers `0` to everything. -/
def ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩

example : (sumWhile.exec ω0 κ1 .copy .nil World.init).steps = 2 + 8 * 3 + 7 * 4 + 2 := by
  decide +kernel
example : sumWhile.cost κ1 .copy = 2 + 100 * 7 + 2 := by decide +kernel

/-! ## Machine-exact primitives -/

example : Prim.denote .udiv (.cons (7 : UInt64) (.cons (0 : UInt64) .nil)) = (0 : UInt64) := rfl
example : Prim.denote .umod (.cons (7 : UInt64) (.cons (0 : UInt64) .nil)) = (7 : UInt64) := rfl
example : Prim.denote .shl (.cons (1 : UInt64) (.cons (65 : UInt64) .nil)) = (2 : UInt64) := rfl
example : Prim.denote .shr (.cons (4 : UInt64) (.cons (66 : UInt64) .nil)) = (1 : UInt64) := rfl
example : Prim.denote .sub (.cons (0 : UInt64) (.cons (1 : UInt64) .nil)) =
    (18446744073709551615 : UInt64) := rfl
example : Prim.denote .mul (.cons (4294967296 : UInt64) (.cons (4294967296 : UInt64) .nil)) =
    (0 : UInt64) := rfl
theorem udiv_zero (x : UInt64) : Prim.denote .udiv (.cons x (.cons (0 : UInt64) .nil)) = (0 : UInt64) :=
  UInt64.div_zero
theorem umod_zero (x : UInt64) : Prim.denote .umod (.cons x (.cons (0 : UInt64) .nil)) = x :=
  UInt64.mod_zero

/-! ## Linear `Result` -/

abbrev R : Ty := .result .u64 .u64

/-- `checkedDiv x y`: `err 0` on division by zero, else `ok (x / y)`. Parameters `x y`. -/
def checkedDiv.fn : Fn [.u64, .u64] R where
  name := "checkedDiv"
  body :=
    .let_ (bin .eq v0 (.lit 0))
      (.ite v0 (.err (.lit 0)) (.let_ (bin .udiv v2 v1) (.ok v0)))

/-- `match checkedDiv x y with | err e => e | ok q => q + 1` -/
def useDiv : Exp [.u64, .u64] .u64 :=
  .let_ (checkedDiv.fn.call (.cons v0 (.cons v1 .nil)))
    (.match_ v0 (.atom v0) (bin .add v0 (.lit 1)))

theorem useDiv_denote (ω : Oracle) (w : World) (x y : UInt64) :
    useDiv.denote ω (.cons y (.cons x .nil)) w = (if y = 0 then 0 else x / y + 1, w) := by
  simp only [useDiv, checkedDiv.fn, Fn.call, Exp.denote, Prim.denote, Atom.denote, Args.denote,
    Env.get_here, Env.get_there]
  by_cases h : y = 0 <;> simp [h]

example : checkedDiv.fn.wf = true := by decide
example : useDiv.wf = true := by decide

/-- An unused `let` that drops a `Result` is rejected. -/
def dropResult : Exp [] .u64 := .let_ (.ok (ε := .u64) (α := .u64) (.lit 1)) (.atom (.lit 0))
example : dropResult.wf = false := by decide

/-- A `Result` used twice is rejected, as in `let r := ok 1; let s := r; match s with | _ => r`. -/
def dupResult : Exp [] R :=
  .let_ (.ok (ε := .u64) (.lit (1 : UInt64)))
    (.let_ (.atom v0) (.match_ v0 (.atom v2) (.atom v2)))
example : dupResult.wf = false := by decide

/-- A branch that drops a `Result` the other branch consumes is rejected. -/
def branchResult : Exp [.bool] R :=
  .let_ (.ok (ε := .u64) (.lit (1 : UInt64))) (.ite v1 (.atom v0) (.err (.lit 0)))
example : branchResult.wf = false := by decide

/-- When both branches consume it, the term is accepted. -/
def branchResultOk : Exp [.bool] R :=
  .let_ (.ok (ε := .u64) (.lit (1 : UInt64)))
    (.ite v1 (.atom v0) (.match_ v0 (.err v0) (.ok v0)))
example : branchResultOk.wf = true := by decide

/-- A loop body that consumes an outer `Result` is rejected. -/
def loopResult : Exp [] R :=
  .let_ (.ok (ε := .u64) (.lit (1 : UInt64)))
    (.loop0 3 (.lit (.ok 0)) (.atom (.lit true)) (.atom v2))
example : loopResult.wf = false := by decide

/-- A function that drops its linear parameter is rejected. -/
def dropParam : Fn [R] .u64 := ⟨"dropParam", .atom (.lit 0), fun _ => True⟩
example : dropParam.wf = false := by decide

/-! ## A reactor that writes bytes and exits -/

/-- `"hi\n"` -/
def hiBytes : List UInt8 := [104, 105, 10]

/-- `init`: `write(1, "hi\n"); exit(0)`; `step` keeps the (unit) state. -/
def hello : Program where
  State := .unit
  init :=
    .let_ (.ext .write (.word (.lit 1) (.bufIn (.const hiBytes) .nil)))
      (.let_ (.ext .exit (.word (.lit 0) .nil)) (.atom (.lit ())))
  step := .atom v0

/-- The two events of `hello`; the result of `write` is whatever the oracle answered. -/
def helloEvents (ω : Oracle) : List Event :=
  [ ⟨"write", [1], [hiBytes], (ω.answer [] ⟨"write", [1], [hiBytes], []⟩).result, []⟩,
    ⟨"exit", [0], [], 0, []⟩ ]

theorem hello_run0 (ω : Oracle) : (hello.run ω 0).2 = ⟨helloEvents ω, true⟩ := by
  simp [hello, Program.run, Exp.denote, World.call, World.init, ExtSig.call, ExtSig.write,
    ExtSig.exit, EArgs.words, EArgs.bytesIn, EArgs.outCaps, Atom.denote, Buf.denote, Call.event, fitOut,
    helloEvents]

/-- For every oracle and every number of steps, the trace is exactly `write` then `exit`. -/
theorem hello_events (ω : Oracle) (n : Nat) : hello.events ω n = helloEvents ω := by
  have h0 : hello.halted ω 0 = true := by simp [Program.halted, hello_run0]
  have := hello.events_halted ω 0 h0 n
  simp only [Nat.zero_add] at this
  simp [Program.events, this, hello_run0]

example : hello.wf = true := by decide
example (κ : CostModel) : hello.stepCost 0 ω0 κ =
    κ.let_ + κ.ext + (κ.let_ + κ.ext + (κ.atom + 0 * κ.word)) := rfl

/-! ## Structs, places and `&mut` -/

/-- A struct with two `U64` fields, whose `Data` instance is what `deriving Data` would produce. -/
structure Pt where
  x : UInt64
  y : UInt64
deriving DecidableEq, Repr

instance : Data Pt := Data.struct [⟨Pt.x⟩, ⟨Pt.y⟩]
instance : Inhabited Pt := ⟨⟨0, 0⟩⟩

abbrev PT : Ty := ⟨Pt⟩

/-- The lenses of the fields `x` and `y`, whose field numbers are 0 and 1. -/
def Pt.lx : Lens PT .u64 := ⟨"x", 0, Pt.x, fun p v => { p with x := v }, none⟩
def Pt.ly : Lens PT .u64 := ⟨"y", 1, Pt.y, fun p v => { p with y := v }, none⟩

/-- `Pt { x, y }`. -/
def Pt.ctor : Ctor [.u64, .u64] PT := ⟨"Pt", .struct, fun | .cons x (.cons y .nil) => ⟨x, y⟩, none, none⟩

/-- The constructor of a pair. -/
def pairC (a b : Ty) : Ctor [a, b] (.pair a b) :=
  ⟨"pair", .struct, fun | .cons x (.cons y .nil) => (x, y), none,
    some ⟨fun | .cons _ (.cons _ .nil) => rfl⟩⟩

/-- The constructor of the tuple that a function with `&mut` parameters hands back, which holds
its result and the final values of its references. -/
def tupC (ps : List Ty) : Ctor ps (.tup ps) := ⟨"tuple", .tuple, Flat.tupBuild ps, none,
  some ⟨Flat.tupBuild_occs ps⟩⟩

/-- `fn bumpX(r : &mut Pt) { r.x := r.x + 1 }`: the body returns `()` and the final `*r`. -/
def bumpX : FnRef [PT] [PT] .unit where
  name := "bumpX"
  body :=
    .let_ (.read (.field (.var .here) Pt.lx))                       -- x := r.x      [x, r]
      (.let_ (bin .add v0 (.lit 1))                                   -- x' := x + 1   [x', x, r]
        (.assign (.field (.var (.there (.there .here))) Pt.lx) v0     -- r.x := x'
          (.mk (tupC [.unit, PT]) (.cons (.lit ()) (.cons v2 .nil)))))  -- ((), r)

/-- `bumpX(&mut p); p.x + p.y` -/
def useBump : Exp [PT] .u64 :=
  bumpX.call (.mut (.var .here) .nil)
    (.let_ (.read (.field (.var (.there .here)) Pt.lx))
      (.let_ (.read (.field (.var (.there (.there .here))) Pt.ly))
        (bin .add v1 v0)))

/-- The struct is updated through the reference: the caller sees the new `x`. -/
theorem useBump_denote (ω : Oracle) (w : World) (p : Pt) :
    useBump.denote ω (.cons p .nil) w = (p.x + 1 + p.y, w) := rfl

example : bumpX.wf [.mut] = true := by decide
example : useBump.wf = true := by decide
/-- `bumpX` has no partial operation, so it is safe under its trivial precondition. -/
theorem bumpX_safe : bumpX.Safe := fun ω env w _ => Exp.safe_of_total ω _ (by decide) env w
example (ω : Oracle) (p : Pt) (w : World) : useBump.safe ω (.cons p .nil) w :=
  bumpX.safe_call bumpX_safe _ _ ω _ w ⟨trivial, trivial⟩ trivial
    (Exp.safe_of_total ω _ (by decide) _ _)

/-- A reactor whose root is a `Pt` in static storage, and each of whose steps calls
`bumpX(&mut root)`. -/
def bumpProg : Program where
  State := PT
  init := .mk Pt.ctor (.cons (.lit 0) (.cons (.lit 10) .nil))
  step := bumpX.call (.mut (.var .here) .nil) (.atom v1)

example : bumpProg.wf = true := by decide
theorem bumpProg_run (ω : Oracle) : (bumpProg.run ω 3).1 = (⟨3, 10⟩ : Pt) := rfl
/-- The footprint is the 16-byte root, the 16-byte reference and the two locals `x` and `x'` of
`bumpX`. -/
example : bumpProg.footprint = 16 + 16 + 8 + 8 := by decide

/-- Copying a `Pt` costs two words. -/
example (κ : CostModel) : (Exp.read (Γ := [PT]) (.var .here)).cost κ .copy = κ.mem + 2 * κ.word := by
  simp [Exp.cost, Place.depth]; rfl

/-! ## Arrays: a sum loop with `a[i]!` and its obligation -/

/-- The loop body of `sumArr`: `acc + a[i]!` (context `[i, acc, a]`). -/
def sumArrBody (n : Nat) : Exp [.u64, .u64, .arr .u64 n] .u64 :=
  .let_ (.read (.index (.var (.there (.there .here))) v0))   -- x := a[i]!   [x, i, acc, a]
    (bin .add v2 v0)

/-- The loop condition of `sumArr`: always `true`. -/
def sumArrCond (n : Nat) : Exp [.u64, .u64, .arr .u64 n] .bool := .atom (.lit true)

/-- `let mut acc := 0; for i in 0...n do acc := acc + a[i]!` -/
def sumArr (n : Nat) : Exp [.arr .u64 n] .u64 :=
  .loop0 n (.lit 0) (sumArrCond n) (sumArrBody n)

example : ((sumArr 4).denote ω0 (.cons #v[1, 2, 3, 4] .nil) World.init).1 = 10 := by
  decide +kernel
example : (sumArr 4).wf = true := by decide

/-- The obligation of `a[i]!` in the loop holds for every array and every length that a loop
counter can index, because the counter stays below `n`. -/
theorem sumArr_safe (n : Nat) (hn : n < 2 ^ 64) (ω : Oracle) (env : Env [.arr .u64 n])
    (w : World) : (sumArr n).safe ω env w := by
  rw [sumArr, Exp.safe_loop0]
  have key : ∀ m i (acc : UInt64) (w : World), i + m = n →
      loopSafe (fun i a w => (sumArrCond n).safe ω (.cons i (.cons a env)) w)
        (fun i a w => (sumArrBody n).safe ω (.cons i (.cons a env)) w)
        (fun i a w => (sumArrCond n).denote ω (.cons i (.cons a env)) w)
        (fun i a w => (sumArrBody n).denote ω (.cons i (.cons a env)) w) m i acc w := by
    intro m
    induction m with
    | zero => intro _ _ _ _; trivial
    | succ m ih =>
      intro i acc w hi
      refine ⟨trivial, fun _ => ⟨⟨⟨trivial, ?_⟩, trivial⟩, ih _ _ _ (by omega)⟩⟩
      simp only [Atom.denote, Env.get_here, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  exact key n 0 0 w (by omega)

/-- The checked form `a[i]?` is safe without any hypothesis, and is `err` out of range. -/
example (ω : Oracle) (env : Env [.u64, .arr .u64 4]) (w : World) :
    (Exp.readChk (Γ := [.u64, .arr .u64 4]) (.index (.var (.there .here)) v0) rfl).safe ω env w :=
  Exp.readChk_safe _ _ _ _ _
example :
    ((Exp.readChk (Γ := [.u64, .arr .u64 4]) (.index (.var (.there .here)) v0) rfl).denote ω0
      (.cons 7 (.cons #v[1, 2, 3, 4] .nil)) World.init).1 = .error () := rfl
example :
    ((Exp.readChk (Γ := [.u64, .arr .u64 4]) (.index (.var (.there .here)) v0) rfl).denote ω0
      (.cons 2 (.cons #v[1, 2, 3, 4] .nil)) World.init).1 = .ok 3 := rfl
/-- The `!` read is not safe out of range. -/
example (ω : Oracle) : ¬ (Exp.read (.index (.var (.there .here)) v0) : Exp [.u64, .arr .u64 4] _).safe
    ω (.cons 7 (.cons #v[1, 2, 3, 4] .nil)) World.init := by
  simp [Exp.safe, Place.ok, Atom.denote]

/-! ## `Slots`: put and take -/

/-- `s.put! 0 7; let x := s.take! 0; x + 1` -/
def slotsDemo : Exp [.slots .u64 2] .u64 :=
  .put (.var .here) (.lit 0) (.lit 7)
    (.take (.var .here) (.lit 0) (bin .add v0 (.lit 1)))

example : (slotsDemo.denote ω0 (.cons (Slots.empty 2) .nil) World.init).1 = 8 := by
  decide +kernel
example : slotsDemo.wf = true := by decide

/-- On empty slots the obligations (cell 0 vacant for `put`, then full for `take`) hold. -/
theorem slotsDemo_safe (ω : Oracle) (w : World) :
    slotsDemo.safe ω (.cons (Slots.empty 2) .nil) w := by
  simp only [slotsDemo, Exp.safe, Place.ok, Place.get, Place.set, Atom.denote, Env.get_here,
    Env.set_here]
  refine ⟨⟨trivial, by decide⟩, ⟨trivial, by decide⟩, trivial⟩

/-- If cell 0 is already full, the obligation of `put!` fails. -/
theorem slotsDemo_unsafe (ω : Oracle) (w : World) :
    ¬ slotsDemo.safe ω (.cons ((Slots.empty 2).setCell 0 (some (1 : UInt64))) .nil) w := by
  simp only [slotsDemo, Exp.safe, Place.ok, Place.get, Atom.denote, Env.get_here]
  intro h
  exact absurd h.1.2 (by decide)

/-- A cell's value is linear, so a `Result` taken from it must be consumed. -/
def takeDrop : Exp [.slots R 2] .u64 :=
  .take (.var .here) (.lit 0) (.atom (.lit 0))
def takeUse : Exp [.slots R 2] .u64 :=
  .take (.var .here) (.lit 0) (.match_ v0 (.atom v0) (.atom v0))
example : takeDrop.wf = false := by decide
example : takeUse.wf = true := by decide

/-- `Slots` have no checked forms. A guard needs a `checkable` place, and a `Slots` cell is not
one, so no guard on a `Slots` cell can be built. -/
example : (Place.slot (Γ := [.u64, .slots .u64 2]) (.var (.there .here)) v0).checkable = false :=
  rfl
example : (Place.index (Γ := [.u64, .arr .u64 2]) (.var (.there .here)) v0).checkable = true := rfl

/-! ## Slice views -/

/-- The term `{ let r = &mut a[1..3]; r[0]! := 9 }; a` writes through a mutable slice view. The
view's value is a `Slots` whose full cells are the viewed elements, and element `0` is the cell
place `r[0]!`. -/
def sliceDemo : Exp [.arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.range (.var .here) (.lit 1) (.lit 2))
    (.assign (.slot (.var .here) (.lit 0)) (.lit 9)
      (.mk (pairC .unit (.view .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v1)

example : (sliceDemo.denote ω0 (.cons #v[1, 2, 3, 4] .nil) World.init).1 = #v[1, 9, 3, 4] := by
  decide +kernel
example : sliceDemo.wf = true := by decide
/-- Its obligations hold, since the range fits, `1 + 2 ≤ 4`, and the element is in the view,
`0 < 2`. -/
example (ω : Oracle) (a : Vector UInt64 4) (w : World) : sliceDemo.safe ω (.cons a .nil) w := by
  simp only [sliceDemo, Exp.safe, Place.ok, Place.get, Atom.denote, Env.get_here]
  exact ⟨⟨trivial, by decide⟩, ⟨⟨trivial, (vview_full_iff a _ _ _ (by decide)).mpr (by decide)⟩,
    trivial⟩, trivial⟩
/-- The view holds exactly the viewed elements: the list `[a[1], a[2]]`. -/
example : (vview #v[(1 : UInt64), 2, 3, 4] 1 2).cell 0 = some 2 ∧
    (vview #v[(1 : UInt64), 2, 3, 4] 1 2).cell 1 = some 3 ∧
    (vview #v[(1 : UInt64), 2, 3, 4] 1 2).cell 2 = none := by decide
/-- Element `2` of a view of length `2` is not in the view, so the obligation fails, although the
element is inside the array. -/
def sliceOut : Exp [.arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.range (.var .here) (.lit 1) (.lit 2))
    (.assign (.slot (.var .here) (.lit 2)) (.lit 9)
      (.mk (pairC .unit (.view .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v1)
example : sliceOut.wf = true := by decide
example (ω : Oracle) (w : World) : ¬ sliceOut.safe ω (.cons #v[1, 2, 3, 4] .nil) w := by
  simp only [sliceOut, Exp.safe, Place.ok, Place.get, Atom.denote, Env.get_here]
  intro h
  exact absurd h.2.1.1.2 (by decide)
/-- The range itself must fit, and `3 + 2 > 4` does not. -/
def sliceBad : Exp [.arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.range (.var .here) (.lit 3) (.lit 2))
    (.mk (pairC .unit (.view .u64 4)) (.cons (.lit ()) (.cons v0 .nil)))
    (.atom v1)
example (ω : Oracle) (w : World) : ¬ sliceBad.safe ω (.cons #v[1, 2, 3, 4] .nil) w := by
  simp only [sliceBad, Exp.safe, Place.ok, Atom.denote]
  intro h
  exact absurd h.1.2 (by decide)

/-- A view cannot be filled, because `put!` into a view could fill a cell past its length where
there is no storage behind it. The checker rejects it … -/
def slicePut : Exp [.arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.range (.var .here) (.lit 1) (.lit 2))
    (.put (.var .here) (.lit 3) (.lit 9)
      (.mk (pairC .unit (.view .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v1)
example : slicePut.wf = false := by decide
/-- … as is assigning a whole view … -/
def sliceAssign : Exp [.slots .u64 4, .arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.range (.var (.there .here)) (.lit 1) (.lit 2))
    (.assign (.var .here) v1
      (.mk (pairC .unit (.view .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v2)
/-- The same body is accepted when the borrowed place is not a slice. -/
def sliceAssignOk : Exp [.slots .u64 4, .slots .u64 4] (.slots .u64 4) :=
  .borrowMut (.var (.there .here))
    (.assign (.var .here) v1
      (.mk (pairC .unit (.slots .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v2)
example : sliceAssignOk.wf = true := by decide
example : sliceAssign.wf = false := by decide
/-- … while the same operations on a `Slots` binder that is not a view are accepted. The view
flag of the binder decides, since the types are the same. -/
def slotsAssign : Exp [.slots .u64 4, .arr .u64 4] (.slots .u64 4) :=
  .borrowMut (.var .here)
    (.put (.var .here) (.lit 3) (.lit 9)
      (.mk (pairC .unit (.slots .u64 4)) (.cons (.lit ()) (.cons v0 .nil))))
    (.atom v1)
example : slotsAssign.wf = true := by decide

/-- The function `fill0 (s : &mut [U64]) := s[0]! := 0` takes a slice view and, like every
function with a `&mut` parameter, hands back the parameter's final value. -/
def fill0 : FnRef [.view .u64 4] [.view .u64 4] .unit where
  name := "fill0"
  body := .assign (.slot (.var .here) (.lit 0)) (.lit 0)
    (.let_ (.mk (pairC (.view .u64 4) .unit) (.cons v0 (.cons (.lit ()) .nil)))
      (.mk (pairC .unit (.tup [.view .u64 4])) (.cons (.lit ()) (.cons v0 .nil))))
  requires := fun env => match env with
    | .cons s .nil => (s : Slots UInt64 4).isFull 0 = true

/-- `fill0(&mut a[1..3])`: the callee writes element `1` of the array through the view. -/
def useFill0 : Exp [.arr .u64 4] (.arr .u64 4) :=
  fill0.call (.mut (.range (.var .here) (.lit 1) (.lit 2)) .nil) (.atom v1)
example : (useFill0.denote ω0 (.cons #v[1, 2, 3, 4] .nil) World.init).1 = #v[1, 0, 3, 4] := by
  decide +kernel
example : useFill0.wf = true := by decide
/-- Passing a view costs a constant `κ.ref` for its address and length and one selector,
whatever the view's width, so nothing is charged per word of the 32-byte view. -/
example (κ : CostModel) : useFill0.cost κ .copy = κ.call + κ.place + κ.ref + fill0.body.cost κ .split +
    κ.atom + (Ty.arr .u64 4).words * κ.word := by
  simp [useFill0, FnRef.call, Exp.cost, RArgs.cost, RArgs.depth, RArgs.refs, RArgs.ownWords,
    Place.depth, Hb.of, Hb.atomW]
  omega

/-- The checker treats any two elements of one array as overlapping, even disjoint ranges, so two
`&mut` slices of one array are rejected … -/
def twoSlices : Exp [.arr .u64 4] (.arr .u64 4) :=
  .callRef "f2" (fun _ => True)
    (.mk (pairC .unit (.tup [.view .u64 4, .view .u64 4]))
      (.cons (.lit ()) (.cons (.lit (vview #v[0, 0, 0, 0] 0 0, vview #v[0, 0, 0, 0] 0 0, ())) .nil)))
    (.mut (.range (.var .here) (.lit 0) (.lit 2)) (.mut (.range (.var .here) (.lit 2) (.lit 2)) .nil))
    (.atom v1)
example : twoSlices.wf = false := by decide
/-- … but a slice of each of two arrays is accepted, and the checker shows that the arguments are
separated. -/
def twoArrays : Exp [.arr .u64 4, .arr .u64 4] (.arr .u64 4) :=
  .callRef "f2" (fun _ => True)
    (.mk (pairC .unit (.tup [.view .u64 4, .view .u64 4]))
      (.cons (.lit ()) (.cons (.lit (vview #v[0, 0, 0, 0] 0 0, vview #v[0, 0, 0, 0] 0 0, ())) .nil)))
    (.mut (.range (.var .here) (.lit 0) (.lit 2))
      (.mut (.range (.var (.there .here)) (.lit 2) (.lit 2)) .nil))
    (.atom v1)
example : twoArrays.wf = true := by decide
example : twoArrays.Frozen := twoArrays.frozen_of_wf (by decide)

/-! ## Enums: an exhaustive match, one arm per constructor -/

/-- A three-variant enum. -/
inductive Cmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving DecidableEq, Repr

instance : Data Cmd :=
  Data.sum [⟨fun | .stop => some () | _ => none⟩, ⟨fun | .add n => some n | _ => none⟩,
    ⟨fun | .mul n => some n | _ => none⟩] (fun c => by cases c <;> simp)

abbrev CMD : Ty := ⟨Cmd⟩

/-- `Cmd.add n` -/
def Cmd.addC : Ctor [.u64] CMD := ⟨"Cmd.add", .variant 1, fun | .cons n .nil => .add n, none, none⟩

/-- The first step of the match, which separates `stop` from the other two. Those come back as a
`Result` in which `err` is `add` and `ok` is `mul`. -/
def Cmd.split : Split CMD .unit (.result .u64 .u64) where
  name := "Cmd"
  tag := 0
  split
    | .stop => .inl ()
    | .add n => .inr (.error n)
    | .mul n => .inr (.ok n)

/-- `match c with | stop => acc | add n => acc + n | mul n => acc * n`, with the parameters
`acc c`. -/
def runCmd : Exp [CMD, .u64] .u64 :=
  .case v0 Cmd.split (.atom v2)
    (.match_ v0 (bin .add (.var (.there (.there (.there .here)))) v0)
      (bin .mul (.var (.there (.there (.there .here)))) v0))

example : runCmd.wf = true := by decide
example : (runCmd.denote ω0 (.cons .stop (.cons 5 .nil)) World.init).1 = 5 := by decide +kernel
example : (runCmd.denote ω0 (.cons (.add 3) (.cons 5 .nil)) World.init).1 = 8 := by decide +kernel
example : (runCmd.denote ω0 (.cons (.mul 3) (.cons 5 .nil)) World.init).1 = 15 := by
  decide +kernel
example : ((Exp.mk Cmd.addC (.cons (.lit 4) .nil) : Exp [] CMD).denote ω0 .nil World.init).1 =
    .add 4 := by decide +kernel

/-! ## The borrow checker, rule by rule

Each rejection is next to an accepted term that differs only in the rule's condition. -/

/-- A callee that swaps its two `&mut U64` parameters. -/
def swap2 : FnRef [.u64, .u64] [.u64, .u64] .unit where
  name := "swap2"
  body := .let_ (.atom v0)                                                       -- t := a
    (.assign (.var (.there .here)) v2                                            -- a := b
      (.assign (.var (.there (.there .here))) v0                                 -- b := t
        (.mk (tupC [.unit, .u64, .u64]) (.cons (.lit ()) (.cons v1 (.cons v2 .nil))))))

/-- A callee taking `&mut U64` and `&U64`. -/
def addTo : FnRef [.u64, .u64] [.u64] .unit where
  name := "addTo"
  body := .let_ (bin .add v0 v1)
    (.assign (.var (.there .here)) v0
      (.mk (tupC [.unit, .u64]) (.cons (.lit ()) (.cons v1 .nil))))

example : swap2.wf [.mut, .mut] = true := by decide
example : addTo.wf [.mut, .shr] = true := by decide

/-- Disjoint fields can be borrowed together, so `swap2(&mut p.x, &mut p.y)` is accepted. -/
def swapFields : Exp [PT] PT :=
  swap2.call (.mut (.field (.var .here) Pt.lx) (.mut (.field (.var .here) Pt.ly) .nil)) (.atom v1)
example : swapFields.wf = true := by decide
example : (swapFields.denote ω0 (.cons ⟨1, 2⟩ .nil) World.init).1 = ⟨2, 1⟩ := by decide +kernel
/-- Two `&mut` borrows of the same field are rejected. -/
def swapSame : Exp [PT] PT :=
  swap2.call (.mut (.field (.var .here) Pt.lx) (.mut (.field (.var .here) Pt.lx) .nil)) (.atom v1)
example : swapSame.wf = false := by decide

/-- `&mut p.x` together with `&p.y` is accepted, and together with the overlapping `&p.x` it is
rejected. -/
def addFields : Exp [PT] PT :=
  addTo.call (.mut (.field (.var .here) Pt.lx) (.shr (.field (.var .here) Pt.ly) .nil)) (.atom v1)
def addSame : Exp [PT] PT :=
  addTo.call (.mut (.field (.var .here) Pt.lx) (.shr (.field (.var .here) Pt.lx) .nil)) (.atom v1)
example : addFields.wf = true := by decide
example : addSame.wf = false := by decide

/-- `&mut x` and `&x` of the same variable in one call are rejected. An exclusive borrow forbids
every other use of an overlapping place, reads included. -/
def mutAndShr : Exp [.u64] .u64 :=
  addTo.call (.mut (.var .here) (.shr (.var .here) .nil)) (.atom v1)
example : mutAndShr.wf = false := by decide

/-- Two elements of one array cannot both be borrowed `&mut` by index, since the indices may be
equal … -/
def swapElems : Exp [.u64, .u64, .arr .u64 4] (.arr .u64 4) :=
  swap2.call (.mut (.index (.var (.there (.there .here))) v1)
    (.mut (.index (.var (.there (.there .here))) v0) .nil)) (.atom (.var (.there (.there (.there .here)))))
example : swapElems.wf = false := by decide

/-- … but together as `pair2`, whose obligation is `i ≠ j`. -/
def swapPair2 : Exp [.u64, .u64, .arr .u64 4] (.arr .u64 4) :=
  .borrowMut (.pair2 (.var (.there (.there .here))) v1 v0)
    (swap2.call (.mut (.field (.var .here) (Lens.fst .u64 .u64))
        (.mut (.field (.var .here) (Lens.snd .u64 .u64)) .nil))
      (.mk (pairC .unit (.pair .u64 .u64)) (.cons (.lit ()) (.cons v1 .nil))))
    (.atom (.var (.there (.there (.there .here)))))
example : swapPair2.wf = true := by decide
example : (swapPair2.denote ω0 (.cons 3 (.cons 0 (.cons #v[1, 2, 3, 4] .nil)))
    World.init).1 = #v[4, 2, 3, 1] := by decide +kernel
/-- Its obligation, that `i ≠ j` and both are in range, is refuted for `i = j`. -/
example (ω : Oracle) : ¬ swapPair2.safe ω (.cons 2 (.cons 2 (.cons #v[1, 2, 3, 4] .nil)))
    World.init := by
  simp [swapPair2, Exp.safe, Place.ok, Atom.denote]

/-- While `&mut p` is live, `p` itself cannot be used, and here it is read through the variable
instead of the reference … -/
def mutThenRead : Exp [.u64] .u64 :=
  .borrowMut (.var .here)
    (.mk (pairC .u64 .u64) (.cons (.var (.there .here)) (.cons v0 .nil))) (.atom v0)
example : mutThenRead.wf = false := by decide
/-- … but it can be used through the reference. -/
def mutThenReadRef : Exp [.u64] .u64 :=
  .borrowMut (.var .here) (.mk (pairC .u64 .u64) (.cons v0 (.cons v0 .nil))) (.atom v0)
example : mutThenReadRef.wf = true := by decide

/-- Any number of `&p` can coexist, as in a shared borrow inside a shared borrow of the same
place. -/
def shrShr : Exp [.u64] .u64 :=
  .borrowShr (.var .here)
    (.borrowShr (.var (.there .here)) (bin .add v0 v1) (.atom v0)) (.atom v0)
example : shrShr.wf = true := by decide

/-- A shared reference is never written. -/
def shrWrite : Exp [.u64] .u64 :=
  .borrowShr (.var .here) (.assign (.var .here) (.lit 1) (.atom (.lit (0 : UInt64)) : Exp _ .u64))
    (.atom v0)
example : shrWrite.wf = false := by decide

/-- A linear value is not moved while borrowed … -/
def moveBorrowed : Exp [R] R :=
  .borrowShr (.var .here) (.atom (.var (.there .here))) (.atom v0)
example : moveBorrowed.wf = false := by decide
/-- … nor copied out of a place … -/
def readLinear : Exp [R] R := .read (.var .here)
example : readLinear.wf = false := by decide
/-- … but moved as a whole variable it is fine. -/
def moveLinear : Exp [R] R := .atom v0
example : moveLinear.wf = true := by decide

/-- Writes are scoped by their block. Assigning an outer variable inside the bound term of a `let`
is rejected, because the update would not reach the code after the block … -/
def assignInBlock : Exp [.u64] .u64 :=
  .let_ (.assign (.var .here) (.lit 5) (.atom (.lit (0 : UInt64)) : Exp _ .u64)) (.atom v1)
example : assignInBlock.wf = false := by decide
/-- … at statement level it is accepted, and visible to the rest of the block. -/
def assignStmt : Exp [.u64] .u64 := .assign (.var .here) (.lit 5) (.atom v0)
example : assignStmt.wf = true := by decide
example (ω : Oracle) : (assignStmt.denote ω (.cons 1 .nil) World.init).1 = 5 := rfl

/-! ## What the checker guarantees

An accepted term is frozen: it touches a place lent by `&mut` only through the borrow binder,
never writes a place lent by `&`, and passes separated reference arguments. The rejected terms
above are shown not to be frozen. -/

example : swapPair2.Frozen := swapPair2.frozen_of_wf (by decide)
example : addFields.Frozen := addFields.frozen_of_wf (by decide)
example : sliceDemo.Frozen := sliceDemo.frozen_of_wf (by decide)
example : useFill0.Frozen := useFill0.frozen_of_wf (by decide)
/-- Reading the lender inside its `&mut` borrow is not frozen … -/
example : ¬ mutThenRead.Frozen := by
  simp [mutThenRead, Exp.Frozen, Exp.Avoids, Args.Avoids, Atom.Avoids, Loan.blocks, Mem.idx,
    Sel.overlap, Place.root, Place.path]
/-- … nor are two overlapping arguments, one of them `&mut`. -/
example : ¬ addSame.Frozen := by
  simp [addSame, FnRef.call, Exp.Frozen, RArgs.Sep, RArgs.Avoids, Place.Avoids, Loan.blocks,
    Mem.idx, Sel.overlap, Place.root, Place.path, Pt.lx]
example : ¬ swapSame.Frozen := by
  simp [swapSame, FnRef.call, Exp.Frozen, RArgs.Sep, RArgs.Avoids, Place.Avoids, Loan.blocks,
    Mem.idx, Sel.overlap, Place.root, Place.path, Pt.lx]
/-- The write-backs of an accepted call go to the places as they were passed. -/
example (env : Env [PT]) (vs : (Ty.tup [.u64, .u64]).carrier) :
    RArgs.writeBack (.mut (.field (.var .here) Pt.lx) (.mut (.field (.var .here) Pt.ly) .nil)) env vs =
      RArgs.writeBackAt env (.mut (.field (.var .here) Pt.lx) (.mut (.field (.var .here) Pt.ly) .nil))
        env vs := by
  have h := (Exp.frozen_of_wf _ (by decide : (swap2.call (.mut (.field (.var .here) Pt.lx)
    (.mut (.field (.var .here) Pt.ly) .nil)) (.atom v1) : Exp [PT] PT).wf = true)).1
  exact RArgs.writeBack_idx _ h env vs

/-! ## Stack and footprint -/

/-- The counter, the accumulator, and the element read. -/
example : (sumArr 4).footprint = 8 + 8 + 8 := by decide
/-- The stack of `useBump` beyond its own frame is the frame of `bumpX`, which makes no further
call, and that frame is charged at least the scratch slots. -/
example (φ : FrameModel) :
    useBump.stackBytes φ = φ.frame (frameWords (ctxWords [PT] + bumpX.body.slotWords)) := by
  simp [useBump, bumpX, Exp.stackBytes]

end Millipede.Tests.Core
