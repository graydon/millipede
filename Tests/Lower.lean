import Millipede.Compile.LowerProg
import Millipede.Compile.LowerOf
import Tests.Core

/-!
# Tests for `lower` and the Flat interpreter

This suite runs lowered Core terms and programs in the Flat interpreter and compares each run
with the source. The result's bytes must equal the encoding of the value that `denote` gives,
the events must equal those of `denote` and `exec`, and the Flat clock must equal the step count
of `exec`. The runs use two cost models and an oracle whose answers depend on the history. Short
runs are checked by kernel reduction with `decide +kernel`, and runs with loops or memory by
compiled evaluation with `#guard`, because the kernel is slow on them.

Each term runs with the encodings of its parameters at consecutive offsets from address 0 and
writes its result at the next offset. The types compared byte for byte have no padding, so their
representation in memory is their encoding.

A reference is lowered to the address of its place, so a callee works on its caller's storage.
Some tests have results that depend on this, such as a callee that writes `p.x` through `&mut p`
before the caller reads `p.x`. Several tests are negated twins that must fail, such as the same
comparison for code lowered with its parameters at the wrong offsets.
-/

namespace Millipede.Tests.Lower

open Millipede Millipede.Flat Millipede.Tests.Core

set_option maxRecDepth 100000

/-- The variable with de Bruijn index 3. -/
abbrev v3 {t s s' s'' : Ty} {Γ : List Ty} : Atom (s'' :: s' :: s :: t :: Γ) t :=
  .var (.there (.there (.there .here)))

/-- An oracle whose answer depends on the history: 5 plus the number of earlier events. -/
def ωc : Oracle := ⟨fun h _ => ⟨UInt64.ofNat h.length + 5, []⟩⟩

/-- A cost model with distinct constants, so a misplaced tick changes the clock. -/
def κ2 : CostModel := ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15⟩

/-- The bytes of an environment, in order. -/
def envBytes : {Γ : List Ty} → Env Γ → List UInt8
  | _, .nil => []
  | _, .cons v e => Data.encodeBytes v ++ envBytes e

/-- Runs the memory lowering of `e` for `fuel` transitions and returns the result's bytes, the
events and the clock. -/
def memRun (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ)
    (fuel : Nat) : List UInt8 × List Event × Nat :=
  let d := ctxSize Γ
  let bs := envBytes env
  let s := nextN κ ω fuel ⟨lowerM e .none ((paramOffs Γ 0).map .own) (d + t.size) d, [], Frame.zero,
    fun a => bs.getD a.toNat 0, World.init, 0⟩
  (rd s.mem d t.size, s.world.events, s.clock)

/-- The source's counterpart of `memRun`: the encoding of the value of `denote`, the events of
`denote` and the step count of `exec`. -/
def memCore (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) :
    List UInt8 × List Event × Nat :=
  let r := e.denote ω env World.init
  (Data.encodeBytes r.1, r.2.events, (e.exec ω κ .copy env World.init).steps)

/-- Whether the lowered run and the source agree. -/
def agree (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ)
    (fuel : Nat) : Bool :=
  memRun κ ω e env fuel == memCore κ ω e env

/-! ## Straight-line code, conditionals, calls -/

example : agree κ1 ω0 f_exp (.cons 7 .nil) 300 := by decide +kernel
example : agree κ2 ω0 f_exp (.cons 11 .nil) 300 := by decide +kernel
example : agree κ2 ω0 f_exp (.cons 4294967296 .nil) 300 := by decide +kernel
example : (memRun κ1 ω0 f_exp (.cons 7 .nil) 300).1 = Data.encodeBytes (50 : UInt64) := by
  decide +kernel
example : agree κ2 ω0 clampAdd.fn.body (.cons 1 (.cons 18446744073709551615 .nil)) 600 := by
  decide +kernel
example : agree κ2 ω0 clamp3 (.cons 5 (.cons 7 (.cons 18446744073709551610 .nil))) 1000 := by
  decide +kernel
example : (memRun κ2 ω0 clamp3 (.cons 1 (.cons 2 (.cons 3 .nil))) 1000).1 =
    Data.encodeBytes (6 : UInt64) := by decide +kernel

/-! ## Every primitive

The arguments cover operand order, division and remainder by zero, shifts of 64 or more and
wrap-around. -/

/-- `p x y` with the parameters `x y`, where `y` has index 0. -/
def binU {r : Ty} (p : Prim [.u64, .u64] r) : Exp [.u64, .u64] r := .prim p (.cons v1 (.cons v0 .nil))
/-- `p a b` on booleans. -/
def binB (p : Prim [.bool, .bool] .bool) : Exp [.bool, .bool] .bool :=
  .prim p (.cons v1 (.cons v0 .nil))

/-- Flat agrees with the source on every `U64` primitive for the arguments `x y`. -/
def primsAgree (x y : UInt64) : Bool :=
  let env : Env [.u64, .u64] := .cons y (.cons x .nil)
  agree κ2 ω0 (binU .add) env 100 && agree κ2 ω0 (binU .sub) env 100 &&
  agree κ2 ω0 (binU .mul) env 100 && agree κ2 ω0 (binU .udiv) env 100 &&
  agree κ2 ω0 (binU .umod) env 100 && agree κ2 ω0 (binU .band) env 100 &&
  agree κ2 ω0 (binU .bor) env 100 && agree κ2 ω0 (binU .bxor) env 100 &&
  agree κ2 ω0 (binU .shl) env 100 && agree κ2 ω0 (binU .shr) env 100 &&
  agree κ2 ω0 (binU .eq) env 100 && agree κ2 ω0 (binU .ne) env 100 &&
  agree κ2 ω0 (binU .ult) env 100 && agree κ2 ω0 (binU .ule) env 100 &&
  agree κ2 ω0 (binU .ugt) env 100 && agree κ2 ω0 (binU .uge) env 100 &&
  agree κ2 ω0 (.prim .bnot (.cons v0 .nil) : Exp [.u64, .u64] .u64) env 100

/-- Flat agrees with the source on every `Bool` primitive for the arguments `a b`. -/
def boolsAgree (a b : Bool) : Bool :=
  let env : Env [.bool, .bool] := .cons b (.cons a .nil)
  agree κ2 ω0 (binB .and) env 100 && agree κ2 ω0 (binB .or) env 100 &&
  agree κ2 ω0 (binB .beq) env 100 &&
  agree κ2 ω0 (.prim .not (.cons v0 .nil) : Exp [.bool, .bool] .bool) env 100

example : primsAgree 3 5 = true := by decide +kernel
example : primsAgree 5 3 = true := by decide +kernel
example : primsAgree 7 0 = true := by decide +kernel
example : primsAgree 18446744073709551615 2 = true := by decide +kernel
example : primsAgree 1 65 = true := by decide +kernel
example : primsAgree 9 9 = true := by decide +kernel
example : boolsAgree true false = true := by decide +kernel
example : boolsAgree false true = true := by decide +kernel
example : boolsAgree true true = true := by decide +kernel
example : boolsAgree false false = true := by decide +kernel
/-- A wrong expected value is noticed. -/
example : (memRun κ2 ω0 (binU .sub) (.cons 3 (.cons 5 .nil)) 100).1 ≠
    Data.encodeBytes (8 : UInt64) := by decide +kernel

/-! ## Loops -/

#guard agree κ2 ω0 (sumTo 10) .nil 4000
#guard (memRun κ1 ω0 (sumTo 10) .nil 4000).1 = Data.encodeBytes (45 : UInt64)
#guard agree κ2 ω0 (sumTo 0) .nil 400
#guard agree κ2 ω0 sumWhile .nil 3000
/- The early exit is visible in the Flat clock exactly as in `exec`. -/
#guard (memRun κ1 ω0 sumWhile .nil 3000).2.2 = 2 + 8 * 3 + 7 * 4 + 2

/-! ## `Result`: constructors, `match`, calls -/

example : agree κ2 ω0 useDiv (.cons 3 (.cons 20 .nil)) 1000 := by decide +kernel
example : agree κ2 ω0 useDiv (.cons 0 (.cons 20 .nil)) 1000 := by decide +kernel
example : (memRun κ1 ω0 useDiv (.cons 3 (.cons 20 .nil)) 1000).1 = Data.encodeBytes (7 : UInt64) := by
  decide +kernel
example : agree κ2 ω0 checkedDiv.fn.body (.cons 0 (.cons 9 .nil)) 1000 := by decide +kernel

/-- A loop whose accumulator is a `Result`, in the surface syntax
`let mut r := ok 0; for i in 0...6 do r := match r with | err e => err e | ok a => if a < 3 then ok (a+1) else err (a+i)`. -/
def resLoop : Exp [] R :=
  .loop0 6 (.lit (.ok 0)) (.atom (.lit true))
    (.match_ v1 (.err v0)
      (.let_ (bin .ult v0 (.lit 3))
        (.ite v0 (.let_ (bin .add v1 (.lit 1)) (.ok v0)) (.let_ (bin .add v1 v2) (.err v0)))))

example : agree κ2 ω0 resLoop .nil 1000 := by decide +kernel

/-! ## Externs -/

/-- `let r := write(1, "hi\n"); let q := write(r, "x"); r + q` -/
def twoWrites : Exp [] .u64 :=
  .let_ (.ext .write (.word (.lit 1) (.bufIn (.const hiBytes) .nil)))
    (.let_ (.ext .write (.word v0 (.bufIn (.const [120]) .nil)))
      (bin .add v1 v0))

#guard agree κ2 ωc twoWrites .nil 500
#guard (memRun κ2 ωc twoWrites .nil 500).2.1 =
    [⟨"write", [1], [hiBytes], 5, []⟩, ⟨"write", [5], [[120]], 6, []⟩]

/-- `exit` inside a loop, in the surface syntax
`let mut acc := 0; for i in 0...10 do acc := (if i == 3 then exit(7) else 0) + acc + i`.
The Flat run stops at `exit` with the world of `exec` and a clock no greater than that of `exec`. -/
def exitLoop : Exp [] .u64 :=
  .loop0 10 (.lit 0) (.atom (.lit true))
    (.let_ (bin .eq v0 (.lit 3))
      (.let_ (.ite v0 (.ext .exit (.word (.lit 7) .nil)) (.atom (.lit 0)))
        (.let_ (bin .add v0 v3) (bin .add v0 v3))))

#guard (memRun κ2 ωc exitLoop .nil 3000).2.1 = (exitLoop.denote ωc .nil World.init).2.events
#guard (memRun κ2 ωc exitLoop .nil 3000).2.1 = [⟨"exit", [7], [], 0, []⟩]
#guard (memRun κ2 ωc exitLoop .nil 3000).2.2 ≤ (exitLoop.exec ωc κ2 .copy .nil World.init).steps
/- The Flat run does strictly less work than `exec`, which keeps going after `exit`. -/
#guard (memRun κ2 ωc exitLoop .nil 3000).2.2 < (exitLoop.exec ωc κ2 .copy .nil World.init).steps

/-! ## Programs (reactors) -/

/-- Runs a lowered program for `fuel` transitions and returns its events. -/
def progEvents (κ : CostModel) (ω : Oracle) (p : Program) (fuel : Nat) : List Event :=
  (nextN κ ω fuel (lowerProg p).init).world.events

example : progEvents κ2 ωc hello 40 = hello.events ωc 5 := by decide +kernel
example : progEvents κ1 ω0 hello 40 = helloEvents ω0 := by decide +kernel

/-- A counter: each step writes `"t"` to fd `s`, and exits with code `s` once `s = 3`. -/
def counter : Program where
  State := .u64
  init := .atom (.lit 0)
  step :=
    .let_ (.ext .write (.word v0 (.bufIn (.const [116]) .nil)))
      (.let_ (bin .eq v1 (.lit 3))
        (.ite v0 (.let_ (.ext .exit (.word v2 .nil)) (.atom v0)) (bin .add v2 (.lit 1))))

example : progEvents κ2 ωc counter 600 = counter.events ωc 10 := by decide +kernel
example : (progEvents κ2 ωc counter 600).length = 5 := by decide +kernel
/-- A partial run sees a prefix of the source trace. -/
example : progEvents κ2 ωc counter 80 = counter.events ωc 1 := by decide +kernel

/-- A reactor whose state is a two-word `Result` carried across steps. -/
def resProg : Program where
  State := R
  init := .ok (.lit 0)
  step :=
    .match_ v0
      (.let_ (.ext .exit (.word v0 .nil)) (.err v0))
      (.let_ (.ext .write (.word v0 (.bufIn (.const [33]) .nil)))
        (.let_ (bin .ult v1 (.lit 2))
          (.ite v0 (.let_ (bin .add v2 (.lit 1)) (.ok v0)) (.err v2))))

example : progEvents κ2 ωc resProg 700 = resProg.events ωc 10 := by decide +kernel
example : (progEvents κ2 ωc resProg 700).length = 4 := by decide +kernel

/-! ## `lower` refuses loop bounds that do not fit a word -/

def bigLoop : Program where
  State := .u64
  init := .loop0 (2 ^ 64) (.lit 0) (.atom (.lit true)) (.atom v1)
  step := .atom v0

example : (lower bigLoop).toBool = false := by decide +kernel
example : (lower counter).toBool = true := by decide +kernel

/-! ## Arrays, `Slots`, structs and enums -/

/- A loop over an array with `a[i]!`. -/
#guard memRun κ2 ω0 (sumArr 4) (.cons #v[1, 2, 3, 4] .nil) 6000 =
    memCore κ2 ω0 (sumArr 4) (.cons #v[1, 2, 3, 4] .nil)
#guard (memRun κ2 ω0 (sumArr 4) (.cons #v[1, 2, 3, 4] .nil) 6000).1 = [10, 0, 0, 0, 0, 0, 0, 0]
/- `put` then `take` on untagged cells. -/
#guard memRun κ2 ω0 slotsDemo (.cons (Slots.empty 2) .nil) 2000 =
    memCore κ2 ω0 slotsDemo (.cons (Slots.empty 2) .nil)
/- An enum `match` tests the tag and reads the payload. -/
#guard memRun κ2 ω0 runCmd (.cons .stop (.cons 5 .nil)) 1000 =
    memCore κ2 ω0 runCmd (.cons .stop (.cons 5 .nil))
#guard memRun κ2 ω0 runCmd (.cons (.add 3) (.cons 5 .nil)) 1000 =
    memCore κ2 ω0 runCmd (.cons (.add 3) (.cons 5 .nil))
#guard memRun κ2 ω0 runCmd (.cons (.mul 3) (.cons 5 .nil)) 1000 =
    memCore κ2 ω0 runCmd (.cons (.mul 3) (.cons 5 .nil))
/- Building a variant. -/
#guard memRun κ2 ω0 (Exp.mk Cmd.addC (.cons (.lit 4) .nil) : Exp [] CMD) .nil 200 =
    memCore κ2 ω0 (Exp.mk Cmd.addC (.cons (.lit 4) .nil) : Exp [] CMD) .nil

/-! ## References as addresses -/

/- In `bumpX(&mut p); p.x + p.y` the callee writes `p.x` through its pointer parameter into the
caller's storage, and the caller then reads `p.x` and `p.y`. -/
#guard memRun κ2 ω0 useBump (.cons ⟨5, 7⟩ .nil) 3000 =
    memCore κ2 ω0 useBump (.cons ⟨5, 7⟩ .nil)
#guard (memRun κ2 ω0 useBump (.cons ⟨5, 7⟩ .nil) 3000).1 = Data.encodeBytes (13 : UInt64)
/- The caller does not see the stale `p.x`, which a write to a copy would leave as `5 + 7`. -/
#guard (memRun κ2 ω0 useBump (.cons ⟨5, 7⟩ .nil) 3000).1 ≠ Data.encodeBytes (12 : UInt64)
/- Two `&mut` arguments, disjoint fields of one struct, go to one callee, which swaps them in
place. -/
#guard memRun κ2 ω0 swapFields (.cons ⟨1, 2⟩ .nil) 3000 =
    memCore κ2 ω0 swapFields (.cons ⟨1, 2⟩ .nil)
#guard (memRun κ2 ω0 swapFields (.cons ⟨1, 2⟩ .nil) 3000).1 = Data.encodeBytes (⟨2, 1⟩ : Pt)
/- `&mut p.x` with `&p.y` to one callee. -/
#guard memRun κ2 ω0 addFields (.cons ⟨1, 2⟩ .nil) 3000 =
    memCore κ2 ω0 addFields (.cons ⟨1, 2⟩ .nil)
example : (Exp.memOk swapFields, Exp.memOk addFields, Exp.memOk useBump) = (true, true, true) := by
  decide

/-- A scoped mutable borrow `{ let r = &mut p.y; r := r + 5 }; p.x + p.y`, written through the
pointer, whose body hands back the reference itself. -/
def borrowY : Exp [PT] .u64 :=
  .borrowMut (.field (.var .here) Pt.ly)
    (.let_ (bin .add v0 (.lit 5))
      (.assign (.var (.there .here)) v0
        (.mk (pairC .unit .u64) (.cons (.lit ()) (.cons v1 .nil)))))
    (.let_ (.read (.field (.var (.there .here)) Pt.lx))
      (.let_ (.read (.field (.var (.there (.there .here))) Pt.ly)) (bin .add v1 v0)))

example : borrowY.wf = true := by decide
example : borrowY.memOk = true := by decide
#guard memRun κ2 ω0 borrowY (.cons ⟨1, 2⟩ .nil) 3000 = memCore κ2 ω0 borrowY (.cons ⟨1, 2⟩ .nil)
#guard (memRun κ2 ω0 borrowY (.cons ⟨1, 2⟩ .nil) 3000).1 = [8, 0, 0, 0, 0, 0, 0, 0]

/-- In `{ let r = &mut p.y; r := p.x + 10 }; p.y` the body reads the lender's other field while
the `&mut` borrow is live, which is allowed because the paths do not overlap. -/
def holeRead : Exp [PT] .u64 :=
  .borrowMut (.field (.var .here) Pt.ly)
    (.let_ (.read (.field (.var (.there .here)) Pt.lx))
      (.let_ (bin .add v0 (.lit 10))
        (.assign (.var (.there (.there .here))) v0
          (.mk (pairC .unit .u64) (.cons (.lit ()) (.cons v2 .nil))))))
    (.read (.field (.var (.there .here)) Pt.ly))

example : holeRead.wf = true := by decide
example : holeRead.memOk = true := by decide
#guard memRun κ2 ω0 holeRead (.cons ⟨3, 4⟩ .nil) 3000 = memCore κ2 ω0 holeRead (.cons ⟨3, 4⟩ .nil)
#guard (memRun κ2 ω0 holeRead (.cons ⟨3, 4⟩ .nil) 3000).1 = Data.encodeBytes (13 : UInt64)
/-- Reading the lent field itself inside the borrow, which the checker rejects. -/
def holeSame : Exp [PT] .u64 :=
  .borrowMut (.field (.var .here) Pt.ly)
    (.let_ (.read (.field (.var (.there .here)) Pt.ly))
      (.mk (pairC .unit .u64) (.cons (.lit ()) (.cons v1 .nil))))
    (.read (.field (.var (.there .here)) Pt.ly))
example : holeSame.wf = false := by decide

/-- The shared borrow `{ let r = &p.x; r + p.y }`, read in place next to the lender. -/
def shrX : Exp [PT] .u64 :=
  .borrowShr (.field (.var .here) Pt.lx)
    (.let_ (.read (.field (.var (.there .here)) Pt.ly)) (bin .add v1 v0))
    (.atom v0)
example : shrX.wf = true := by decide
#guard memRun κ2 ω0 shrX (.cons ⟨20, 22⟩ .nil) 2000 = memCore κ2 ω0 shrX (.cons ⟨20, 22⟩ .nil)

/-- Writes two elements together, `a[0], a[2] := (7, 9); a`. -/
def pair2Write : Exp [.arr .u64 3] (.arr .u64 3) :=
  .let_ (.mk (pairC .u64 .u64) (.cons (.lit 7) (.cons (.lit 9) .nil)))
    (.assign (.pair2 (.var (.there .here)) (.lit 0) (.lit 2)) v0 (.atom v1))
example : pair2Write.memOk = true := by decide
#guard memRun κ2 ω0 pair2Write (.cons #v[1, 2, 3] .nil) 2000 =
    memCore κ2 ω0 pair2Write (.cons #v[1, 2, 3] .nil)

/- The same comparison fails for code lowered with the parameter at the wrong offset, that of
its second field. -/
#guard (let s := nextN κ2 ω0 3000 ⟨lowerM borrowY .none [.own 8] 32 16, [], Frame.zero,
      fun a => (envBytes (Env.cons (t := PT) ⟨1, 2⟩ .nil)).getD a.toNat 0, World.init, 0⟩
    rd s.mem 16 8) ≠ (memCore κ2 ω0 borrowY (.cons ⟨1, 2⟩ .nil)).1

/-! ## Slices -/

/-- In `{ let r = &mut a[1..3]; r[0]! := 9 }; a` the slice is lowered to a 16-byte slot holding
the address of `a[1]` and the length 2. It is written through in place, and the array reads back
with the element changed. -/
example : sliceDemo.memOk = true := by decide
#guard memRun κ2 ω0 sliceDemo (.cons #v[1, 2, 3, 4] .nil) 3000 =
    memCore κ2 ω0 sliceDemo (.cons #v[1, 2, 3, 4] .nil)

/-- In `{ let r = &a[1..3]; r[1]! }` element 1 of the view is element 2 of the array. -/
def sliceRead : Exp [.arr .u64 4] .u64 :=
  .borrowShr (.range (.var .here) (.lit 1) (.lit 2)) (.read (.slot (.var .here) (.lit 1))) (.atom v0)
example : sliceRead.memOk = true := by decide
#guard memRun κ2 ω0 sliceRead (.cons #v[10, 20, 30, 40] .nil) 3000 =
    memCore κ2 ω0 sliceRead (.cons #v[10, 20, 30, 40] .nil)
#guard (memCore κ2 ω0 sliceRead (.cons #v[10, 20, 30, 40] .nil)).1 = Data.encodeBytes (30 : UInt64)
/- Lowered with the array at the wrong offset, the slice reads another element. -/
#guard (let s := nextN κ2 ω0 3000 ⟨lowerM sliceRead .none [.own 8] 40 32, [], Frame.zero,
      fun a => (envBytes (Env.cons (t := .arr .u64 4) #v[10, 20, 30, 40] .nil)).getD a.toNat 0,
      World.init, 0⟩
    rd s.mem 32 8) ≠ (memCore κ2 ω0 sliceRead (.cons #v[10, 20, 30, 40] .nil)).1

/-- A view copied whole is refused, because in memory a view is only its first `len` elements,
while its `Slots` type is laid out past them. -/
def sliceCopy : Exp [.arr .u64 4] (.view .u64 4) :=
  .borrowShr (.range (.var .here) (.lit 1) (.lit 2)) (.atom v0) (.atom v0)
example : sliceCopy.memOk = false := by decide
example : sliceCopy.wf = true := by decide
/-- A borrow body that hands back a fresh value instead of its reference is refused, because
the value would have to be copied into the place. -/
def borrowFresh : Exp [PT] .u64 :=
  .borrowMut (.field (.var .here) Pt.ly)
    (.let_ (bin .add v0 (.lit 5)) (.mk (pairC .unit .u64) (.cons (.lit ()) (.cons v0 .nil))))
    (.read (.field (.var (.there .here)) Pt.ly))
example : borrowFresh.wf = true := by decide
example : (Exp.memOk borrowFresh) = false := by decide
example : (Exp.memOk (sumArr 4)) = true := by decide

/-! ## Programs with a root updated in place -/

/-- A reactor whose root is a `Pt` and whose step increments `root.x` in place. -/
def ptProg : Program where
  State := PT
  init := .mk Pt.ctor (.cons (.lit 0) (.cons (.lit 10) .nil))
  step :=
    .let_ (.read (.field (.var .here) Pt.lx))
      (.let_ (bin .add v0 (.lit 1))
        (.assign (.field (.var (.there (.there .here))) Pt.lx) v0 (.atom v2)))

example : ptProg.wf = true := by decide
theorem ptProg_run (ω : Oracle) : (ptProg.run ω 3).1 = (⟨3, 10⟩ : Pt) := rfl
/-- The memory is one 16-byte root, with no second copy, and the step's own memory above it. -/
example : ptProg.memBytes = 16 + 24 := by decide

/-- The root's bytes after `fuel` transitions of the lowered program. -/
def rootAfter (κ : CostModel) (ω : Oracle) (p : Program) (fuel : Nat) : List UInt8 :=
  rd (nextN κ ω fuel (lowerProg p).init).mem 0 p.State.size

example : (lower ptProg).toBool = true := by decide +kernel
/-- After 250 transitions the lowered program has done three steps, and the root's bytes are
those of the source root. -/
example : rootAfter κ2 ω0 ptProg 250 = Data.encodeBytes (ptProg.run ω0 3).1 := by decide +kernel
example : rootAfter κ2 ω0 bumpProg 230 = Data.encodeBytes (bumpProg.run ω0 2).1 := by decide +kernel
/-- The root differs from the root after two steps. -/
example : rootAfter κ2 ω0 ptProg 250 ≠ Data.encodeBytes (ptProg.run ω0 2).1 := by decide +kernel
/-- A step that does not hand back its root in place writes its result to a temporary above the
root, which is then copied over the root. -/
def ptFresh : Program where
  State := PT
  init := .mk Pt.ctor (.cons (.lit 0) (.cons (.lit 10) .nil))
  step :=
    .let_ (.read (.field (.var .here) Pt.lx))
      (.let_ (.read (.field (.var (.there .here)) Pt.ly))
        (.let_ (bin .add v0 (.lit 1)) (.mk Pt.ctor (.cons v0 (.cons v2 .nil)))))
example : (lower ptFresh).toBool = true := by decide +kernel
example : ptFresh.stepTmp = 16 := by decide
/-- Each step swaps the fields and increments one, reading the old root while it builds the new
one. -/
example : rootAfter κ2 ω0 ptFresh 330 = Data.encodeBytes (ptFresh.run ω0 3).1 := by decide +kernel
example : (ptFresh.run ω0 3).1 = (⟨12, 1⟩ : Pt) := rfl
/-- The root differs from the root after two steps. -/
example : rootAfter κ2 ω0 ptFresh 330 ≠ Data.encodeBytes (ptFresh.run ω0 2).1 := by decide +kernel

/-! ## The memory refinement for one program

The lens and constructor of `Pt` are lawful, so the refinement theorem of `lower` applies to
`ptProg`. -/

theorem pt_repr (x : Pt) (bs : List UInt8) :
    Data.reprBytes x bs ↔ bs.length = 16 ∧ Data.reprBytes x.x (slice bs 0 8) ∧
      Data.reprBytes x.y (slice bs 8 8) := by
  constructor
  · rintro ⟨hl, h1, h2, _⟩; exact ⟨hl, h1, h2⟩
  · rintro ⟨hl, h1, h2⟩; exact ⟨hl, h1, h2, trivial⟩

theorem Pt.lx_lawful : Pt.lx.Lawful := by
  refine ⟨⟨by decide, fun x bs h => ((pt_repr x bs).1 h).2.1, fun x v bs vb h hv => ?_⟩,
    ⟨[Data.shape UInt64, Data.shape UInt64], rfl, rfl⟩⟩
  obtain ⟨hl, _, h2⟩ := (pt_repr x bs).1 h
  have hvl : vb.length = 8 := hv.1
  have hoff : lensOff Pt.lx = 0 := by decide
  rw [hoff]
  refine (pt_repr _ _).2 ⟨by simp [splice, hvl, hl], ?_, ?_⟩
  · have := slice_splice_same bs 0 vb (by omega)
    rw [hvl] at this; rw [this]; exact hv
  · have e : slice (splice bs 0 vb) 8 8 = slice bs 8 8 := by
      simp [splice, slice, hvl]
    rw [e]; exact h2

theorem Pt.ctor_lawful : Pt.ctor.Lawful := by
  refine ⟨by decide, by decide, by decide, fun env bs hl _ ha => ?_⟩
  match env, ha with
  | .cons x (.cons y .nil), ⟨h1, h2, _⟩ =>
    exact (pt_repr _ _).2 ⟨hl, h1 0 (by decide), h2 8 (by decide)⟩

theorem ptProg_lower : lower ptProg = .ok (lowerProg ptProg) := by
  unfold lower; rw [ite_eq_left_iff.mpr (fun h => absurd (by decide +kernel) h)]

theorem ptProg_hyp : MemHyp ptProg :=
  MemHyp.of_checks ptProg_lower (by decide)
    ⟨Pt.ctor_lawful, ⟨trivial, Pt.lx_lawful⟩, trivial, ⟨trivial, Pt.lx_lawful⟩, trivial⟩
    (Program.safe_of_total _ (by decide) (by decide))

/-- For every oracle and cost model, the lowered `ptProg` has exactly the source trace. -/
example (ω : Oracle) (κ : CostModel) :
    TraceEq ((Flat.sem κ).traceAt ω (lowerProg ptProg).init) (ptProg.events ω) :=
  lower_traceEq ptProg _ ptProg_lower ptProg_hyp ω κ

/-- `bumpProg`, whose step passes its root by address to a callee, is lowered. -/
example : (lower bumpProg).toBool = true := by decide +kernel

/-! ## A checked slice bound -/

/-- `guard (a[lo..lo+len])` for `a : [U64; 4]`, where `lo` and `len` are the variables 1 and 0.
Its value is a `Result Unit Unit` whose tag is `lo + len ≤ 4`, computed without overflow. -/
def guardRange : Exp [.u64, .u64, Ty.arr .u64 4] (Ty.result .unit .unit) :=
  .guard (.valid (.range (.var (.there (.there .here))) v1 v0) rfl)

#guard guardRange.memOk
#guard [(0, 4), (1, 3), (4, 0), (2, 3), (5, 0), (18446744073709551615, 2), (3, 18446744073709551615)].all
  fun (lo, len) => agree κ2 ω0 guardRange (.cons len (.cons lo (.cons (Vector.replicate 4 7) .nil))) 200
-- The in-range and the overflowing cases differ.
#guard (memRun κ2 ω0 guardRange (.cons 3 (.cons 1 (.cons (Vector.replicate 4 7) .nil))) 200).1 !=
  (memRun κ2 ω0 guardRange (.cons 2 (.cons 18446744073709551615 (.cons (Vector.replicate 4 7) .nil))) 200).1

end Millipede.Tests.Lower
