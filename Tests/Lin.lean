import Millipede.Compile.LinearizeProof
import Millipede.Compile.LowerStack
import Tests.Lower

/-!
# Tests for `linearize` and the Lin interpreter

This suite linearizes lowered Core terms and programs, runs them in the Lin interpreter by
kernel reduction, and compares the result's bytes, the events and the clock with the source.
The runs use two cost models and an oracle whose answers depend on the history. The stack tests
check that Lin's static stack bound is within Core's stack measure and is attained by the
deepest stack a run reaches.

A Lin program has a data region, in which memory accesses run while an access outside it is
stuck. Lowered programs run in Lin with the source trace and leave the root's bytes in the data
region. Negated twins show that each comparison can fail, for example that a run with a data
region too small for the step's locals is stuck.
-/

namespace Millipede.Tests.Lin

open Millipede Millipede.Flat Millipede.Lin Millipede.Tests.Core Millipede.Tests.Lower

set_option maxRecDepth 100000

/-- Linearizes the lowered code of a term, with its parameters from offset 0 of the data region,
the result after them and the term's own memory above. -/
def linOf {Γ : List Ty} {t : Ty} (e : Exp Γ t) : Lin.Prog :=
  let d := ctxSize Γ
  linearize ⟨lowerM e .none ((paramOffs Γ 0).map .own) (d + t.size) d, FR + e.slotNeed⟩
    (d + t.size + e.memNeed)

/-- Runs the linearized code of `e` from `main` with `env`'s bytes in memory for `fuel` Lin
steps. It returns the result's bytes, the events and the clock, or `none` if the run got stuck. -/
def linRun (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ)
    (fuel : Nat) : Option (List UInt8 × List Event × Nat) :=
  let P := linOf e
  let bs := envBytes env
  ((Lin.sem κ P).run ω ⟨P.main, 0, Frame.zero, [], fun a => bs.getD a.toNat 0, World.init, 0⟩
    fuel).map fun s => (rd s.mem (ctxSize Γ) t.size, s.world.events, s.clock)

/-- Whether the Lin run agrees with the source. -/
def linAgree (κ : CostModel) (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ)
    (fuel : Nat) : Bool :=
  linRun κ ω e env fuel == some (memCore κ ω e env)

/-! ## Straight-line code, conditionals and calls

Each callee becomes a function of the Lin program. -/

example : linAgree κ1 ω0 f_exp (.cons 7 .nil) 300 := by decide +kernel
example : linAgree κ2 ω0 f_exp (.cons 4294967296 .nil) 300 := by decide +kernel
example : linAgree κ2 ω0 clampAdd.fn.body (.cons 1 (.cons 18446744073709551615 .nil)) 600 := by
  decide +kernel
example : linAgree κ2 ω0 clamp3 (.cons 5 (.cons 7 (.cons 18446744073709551610 .nil))) 1000 := by
  decide +kernel
/-- A wrong expected value is noticed. -/
example : (linRun κ2 ω0 clamp3 (.cons 1 (.cons 2 (.cons 3 .nil))) 1000).map (·.1) ≠
    some (Data.encodeBytes (7 : UInt64)) := by decide +kernel
/-- `clamp3` has two call sites, which give two hoisted callees before `main`. -/
example : (linOf clamp3).funs.length = 3 ∧ (linOf clamp3).main = 2 := by decide +kernel

/-! ## Every primitive -/

/-- Lin agrees with the source on `U64` primitives for the arguments `x y`. -/
def primsAgree (x y : UInt64) : Bool :=
  let env : Env [.u64, .u64] := .cons y (.cons x .nil)
  linAgree κ2 ω0 (binU .add) env 100 && linAgree κ2 ω0 (binU .sub) env 100 &&
  linAgree κ2 ω0 (binU .mul) env 100 && linAgree κ2 ω0 (binU .udiv) env 100 &&
  linAgree κ2 ω0 (binU .umod) env 100 && linAgree κ2 ω0 (binU .shl) env 100 &&
  linAgree κ2 ω0 (binU .ult) env 100 && linAgree κ2 ω0 (binU .ugt) env 100 &&
  linAgree κ2 ω0 (binU .uge) env 100

example : primsAgree 3 5 = true := by decide +kernel
example : primsAgree 7 0 = true := by decide +kernel
example : primsAgree 18446744073709551615 2 = true := by decide +kernel
example : primsAgree 1 65 = true := by decide +kernel

/-! ## Loops -/

example : linAgree κ2 ω0 (sumTo 10) .nil 4000 := by decide +kernel
example : linAgree κ2 ω0 (sumTo 0) .nil 400 := by decide +kernel
-- `sumWhile` is unfolded first, because the kernel decides the folded constant far more slowly.
example : linAgree κ2 ω0 sumWhile .nil 3000 := by unfold sumWhile; decide +kernel
/-- The early exit is visible in the Lin clock exactly as in `exec`. -/
example : (linRun κ1 ω0 sumWhile .nil 3000).map (·.2.2) = some (2 + 8 * 3 + 7 * 4 + 2) := by
  unfold sumWhile; decide +kernel

/-! ## `Result`, `match`, calls -/

example : linAgree κ2 ω0 useDiv (.cons 3 (.cons 20 .nil)) 1000 := by decide +kernel
example : linAgree κ2 ω0 useDiv (.cons 0 (.cons 20 .nil)) 1000 := by decide +kernel
example : linAgree κ2 ω0 resLoop .nil 1000 := by decide +kernel

/-! ## Externs -/

example : linAgree κ2 ωc twoWrites .nil 500 := by decide +kernel
example : (linRun κ2 ωc exitLoop .nil 3000).map (·.2.1) = some [⟨"exit", [7], [], 0, []⟩] := by
  decide +kernel

/-! ## Programs (reactors) -/

/-- Runs a lowered and linearized program for `fuel` Lin steps and returns its events. -/
def linEvents (κ : CostModel) (ω : Oracle) (p : Program) (fuel : Nat) : Option (List Event) :=
  let P := linearize (lowerProg p) p.memBytes
  ((Lin.sem κ P).run ω P.init fuel).map (·.world.events)

example : linEvents κ2 ωc hello 40 = some (hello.events ωc 5) := by decide +kernel
example : linEvents κ1 ω0 hello 40 = some (helloEvents ω0) := by decide +kernel
example : linEvents κ2 ωc counter 250 = some (counter.events ωc 10) := by decide +kernel
/-- A partial run sees a prefix of the source trace. -/
example : (linEvents κ2 ωc counter 30).map (·.isPrefixOf (counter.events ωc 10)) =
    some true := by
  decide +kernel

example : linEvents κ2 ωc resProg 300 = some (resProg.events ωc 10) := by decide +kernel

/-- `clamp3` as a function, which calls `clampAdd` twice. -/
def clamp3.fn : Millipede.Fn [.u64, .u64, .u64] .u64 := ⟨"clamp3", clamp3, fun _ => True⟩

/-- A reactor with nested calls, whose step is
`x := clamp3 st st 1; write(x, "c"); if x > 20 then exit(x)` with the new state `x`. Its states
are 1, 3, 7, 15 and 31. -/
def callProg : Program where
  State := .u64
  init := .atom (.lit 1)
  step :=
    .let_ (clamp3.fn.call (.cons (.lit 1) (.cons v0 (.cons v0 .nil))))
      (.let_ (.ext .write (.word v0 (.bufIn (.const [99]) .nil)))
        (.let_ (bin .ugt v1 (.lit 20))
          (.ite v0 (.let_ (.ext .exit (.word v2 .nil)) (.atom v3)) (.atom v2))))

example : linEvents κ2 ωc callProg 600 = some (callProg.events ωc 10) := by decide +kernel
example : (linEvents κ2 ωc callProg 600).map (·.map (·.args)) =
    some [[3], [7], [15], [31], [31]] := by decide +kernel

/-! ## Stack depth -/

/-- A frame model of 8 bytes per slot plus 16 for the return address and alignment. -/
def φ8 : FrameModel := ⟨fun w => 8 * w + 16, fun h => by omega⟩

/-- Runs `fuel` Lin steps and returns the deepest stack seen, or `none` if the run got stuck. -/
def maxDepth (κ : CostModel) (ω : Oracle) (φ : FrameModel) (P : Lin.Prog) :
    Nat → Lin.State → Option Nat
  | 0, s => some (s.depth φ P)
  | n + 1, s =>
    match Lin.step κ P ω s with
    | none => none
    | some s' => (maxDepth κ ω φ P n s').map (max (s.depth φ P))

/-- Nested calls from `main` to `clamp3` to `clampAdd` give three frames. -/
example : (linearize (lowerProg callProg) callProg.memBytes).funs.length = 4 := by decide +kernel
/-- The static bound is the main frame plus the frames of the calls it makes, and it is within
Core's stack measure, which charges every activation at least the scratch slots. -/
example : (linearize (lowerProg callProg) callProg.memBytes).stackBytes φ8 =
    φ8.frame (lowerProg callProg).frame + Stmt.callBytes φ8 (lowerProg callProg).main := by
  decide +kernel
example : (linearize (lowerProg callProg) callProg.memBytes).stackBytes φ8 ≤
    callProg.stackBytes φ8 := by decide +kernel
/-- The deepest stack reached is exactly the static bound. -/
example : maxDepth κ2 ωc φ8 (linearize (lowerProg callProg) callProg.memBytes) 600
    (linearize (lowerProg callProg) callProg.memBytes).init =
      some ((linearize (lowerProg callProg) callProg.memBytes).stackBytes φ8) := by decide +kernel
example : maxDepth κ2 ωc φ8 (linOf clamp3) 100 (linOf clamp3).init =
    some ((linOf clamp3).stackBytes φ8) := by decide +kernel
/-- Without calls the stack is the main frame alone. -/
example : (linearize (lowerProg counter) counter.memBytes).stackBytes φ8 = φ8.frame (lowerProg counter).frame := by
  decide +kernel

/-! ## The data region -/

/-- A Lin program with a data region of `M` bytes that stores `0x1122334455667788` at address
`a`, then loads the byte at `a + 1` into slot 0 and the word at `a` into slot 1. -/
def memProg (M : Nat) (a : UInt64) : Lin.Prog :=
  { funs := [⟨"main", 3, [.store .w64 (.imm a) 0 (.imm 0x1122334455667788), .load .w8 0 (.imm a) 1,
      .load .w64 1 (.imm 0) a, .jmp 3], [.slot 0, .slot 1]⟩], main := 0, mem := M }

/-- Runs a Lin program for `fuel` steps and returns slots 0 and 1 and the memory byte at 15, or
`none` if the run got stuck. -/
def runSlots (P : Lin.Prog) (fuel : Nat) : Option (UInt64 × UInt64 × UInt8) :=
  ((Lin.sem κ1 P).run ω0 P.init fuel).map fun s => (s.frame 0, s.frame 1, s.mem 15)

example : runSlots (memProg 16 8) 10 = some (0x77, 0x1122334455667788, 0x11) := by
  decide +kernel
/-- An access out of bounds is stuck, here because the store's last byte, at address 16, is
outside `[0, 16)`. -/
example : runSlots (memProg 16 9) 10 = none := by decide +kernel
/-- The word at `[8, 16)` fits exactly at the edge. -/
example : runSlots (memProg 16 8) 1 = some (0, 0, 0x11) := by decide +kernel
/-- A data region one byte too small refuses the same program. -/
example : runSlots (memProg 15 8) 10 = none := by decide +kernel

/-! ### Lowering then linearizing -/

/-- A reactor over a struct root whose step increments `root.x` in place, writes it and exits
after the third step. -/
def ptCount : Program where
  State := PT
  init := .mk Pt.ctor (.cons (.lit 0) (.cons (.lit 10) .nil))
  step :=
    .let_ (.read (.field (.var .here) Pt.lx))
      (.let_ (bin .add v0 (.lit 1))
        (.assign (.field (.var (.there (.there .here))) Pt.lx) v0
          (.let_ (.ext .write (.word v0 (.bufIn (.const [112]) .nil)))
            (.let_ (bin .eq v1 (.lit 3))
              (.ite v0
                (.let_ (.ext .exit (.word (.var (.there (.there .here))) .nil))
                  (.atom (.var (.there (.there (.there (.there (.there .here))))))))
                (.atom (.var (.there (.there (.there (.there .here)))))))))))

example : ptCount.wf = true := by decide
example : (lower ptCount).toBool = true := by decide +kernel

/-- The lowered and linearized program. -/
def ptCountLin : Option Lin.Prog :=
  (lower ptCount).toOption.map fun fp => linearize fp ptCount.memBytes

example : ptCountLin.isSome = true := by decide +kernel
example : ptCountLin.map (·.mem) = some ptCount.memBytes := by decide +kernel

/-- The events and the root's bytes after `fuel` Lin steps, or `none` if the run got stuck. -/
def linMemRun (P : Option Lin.Prog) (fuel : Nat) : Option (List Event × List UInt8) := do
  let P ← P
  let s ← (Lin.sem κ2 P).run ωc P.init fuel
  pure (s.world.events, rd s.mem 0 16)

-- Lin has the source trace, and the root at address 0 holds the source root's bytes, because
-- the step that exits has already updated the root in place.
#guard (linMemRun ptCountLin 3000).map (·.1) == some (ptCount.events ωc 10)
#guard (linMemRun ptCountLin 3000).map (·.2) == some (Data.encodeBytes (ptCount.run ωc 3).1)
/-- The data region is the 16-byte root, updated in place, with the step's locals above it. -/
example : ptCount.memBytes = 16 + 33 := by decide
-- With a data region of only the root's 16 bytes the run is stuck, since each step's locals
-- live above it.
#guard ((lower ptCount).toOption.bind fun fp =>
  (linMemRun (some (linearize fp 16)) 3000)) == none

/-- The decidable frame check, by which lowered code is proved to stay within its frames,
refuses a statement that uses a slot outside its frame. -/
example : withinB (.mov 5 (.imm 0)) 3 = false := by decide
example : withinB (.mov 2 (.imm 0)) 3 = true := by decide

/-! ## The pipeline's stack bound

`lower` gives every activation the scratch frame `FR = 16` plus a slot for each binder that
lives in a slot, and Core charges every activation the scratch slots on top of its own slot
words. The step of `nest` calls `f`, which calls `g`, both with one parameter and almost no
slots. So the Lin bound is three scratch frames, the step's frame larger by the slot of its
`let` binder, and Core's bound is above it. -/

/-- `g x = x`. -/
def nestG : Exp [.u64] .u64 := .atom v0
/-- `f x = g x`. -/
def nestF : Exp [.u64] .u64 := .call "g" nestG (.cons v0 .nil)
/-- A reactor whose step calls `f`, which calls `g`, and keeps its state since `f x = x`. The
result is bound and used, so its binder lives in a slot. -/
def nest : Program where
  State := .u64
  init := .atom (.lit 1)
  step := .let_ (.call "f" nestF (.cons v0 .nil)) (.atom v0)

/-- The Lin stack bound of the pipeline's image of `nest`. -/
def nestStack (φ : FrameModel) : Option Nat :=
  (lower nest).toOption.map fun fp => (linearize fp nest.memBytes).stackBytes φ

-- The main code's frame holds the scratch slots and its binder. Each callee's frame holds the
-- scratch slots, its word parameter and its result, which is returned as a word.
#guard nestStack φ8 == some (φ8.frame (FR + 1) + 2 * φ8.frame (FR + 2))
#guard (nestStack φ8).all (· ≤ nest.stackBytes φ8)
#guard nest.stackBytes φ8 == φ8.frame (FR + 2 + nest.step.slotWords) + φ8.frame (FR + 1 + nestF.slotWords) +
  φ8.frame (FR + 1 + nestG.slotWords)
-- The callees' own slot words are far below the scratch frame they run in, so a measure that
-- charged callees only their own slot words would fall below the Lin bound.
#guard 2 * φ8.frame (ctxWords [.u64] + nestG.slotWords) + φ8.frame FR < 3 * φ8.frame FR

/-- The pipeline's stack bound is within Core's stack measure for every frame model. -/
example (φ : FrameModel) (M : Nat) :
    (linearize (lowerProg nest) M).stackBytes φ ≤ nest.stackBytes φ :=
  linearize_stackBytes_le φ nest M

/-! ## The theorems, instantiated -/

/-- Every reachable state of the linearized `callProg` is within the static bound, which is
within Core's stack measure. -/
example (κ : CostModel) (φ : FrameModel) (ω : Oracle) (n : Nat) (s : Lin.State)
    (hs : (Lin.sem κ (linearize (lowerProg callProg) callProg.memBytes)).run ω
      (linearize (lowerProg callProg) callProg.memBytes).init n = some s) :
    s.depth φ (linearize (lowerProg callProg) callProg.memBytes) ≤ callProg.stackBytes φ :=
  Nat.le_trans (depth_le κ φ _ (linearize_callsDown _ _) ω n s hs)
    (linearize_stackBytes_le φ callProg _)

example (fp : Flat.Prog) (h : lower callProg = .ok fp) : (linearize fp callProg.memBytes).Wf :=
  lower_linearize_wf h _

end Millipede.Tests.Lin
