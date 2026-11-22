import Millipede.Meta.MpDef
import Std.Tactic.Do
import Std.WP

/-!
# Tests for `mp def` on words, loops, `Result` and externs

This suite defines small functions with `mp def` and checks what it generates for them: the
Lean function, the Core term, the equation between them and the cost bound printed by
`#mp_cost`. The functions cover straight-line code, a caller of another function, loops with an
early exit, `Result` values and `match`, and calls of the externs `write` and `exit`. Four of
them get a `vcgen` specification, one of which is proved from its callee's.

Every checker of the elaborator has a rejection test that pins its message with `#guard_msgs`.
At the end, `#guard` runs four functions on thousands of pseudo-random inputs against reference
functions written directly on `Nat`, so a wrong meaning of a primitive or a loop fails the suite.

The normal form and the proofs about it are described in doc/design/embedding.md.
-/

namespace Millipede.Tests.MpDef

open Millipede Std.WP

/-- An oracle that always answers 0, for kernel evaluation of closed runs. -/
def ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩

set_option experimental.vcgen true

/-! ## Saturating addition -/

mp def clampAdd (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then 18446744073709551615 else s

/-- The generated function is the expected normal form, a Lean `if` on the wrapped sum. -/
example : clampAdd = fun x y => if x + y < x then pure 18446744073709551615 else pure (x + y) :=
  rfl

/-- The generated Core term, in which the last parameter `y` has index 0. -/
example : clampAdd.exp =
    .let_ (.prim .add (.cons (.var (.there .here)) (.cons (.var .here) .nil)))
      (.let_ (.prim .ult (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil)))
        (.ite (.var .here) (.atom (.lit 18446744073709551615)) (.atom (.var (.there .here))))) :=
  rfl

/-- The equation between the term's meaning and the Lean function, for every oracle and world. -/
example (ω : Oracle) (w : World) (x y : UInt64) :
    clampAdd.exp.denote ω (.cons y (.cons x .nil)) w = ((clampAdd x y).run, w) :=
  clampAdd.exp_denote ω w x y

example : clampAdd.fn.wf = true := clampAdd.wf
example : clampAdd.fn = ⟨"clampAdd", clampAdd.exp, fun _ => True⟩ := rfl

/-- Kernel evaluation of the term gives the expected values. -/
example (ω : Oracle) : (clampAdd.exp.denote ω (.cons 4 (.cons 3 .nil)) World.init).1 = 7 := rfl
example (ω : Oracle) :
    (clampAdd.exp.denote ω (.cons 1 (.cons 18446744073709551615 .nil)) World.init).1 =
      18446744073709551615 := rfl

/-- `clampAdd` is saturating addition. -/
@[spec] theorem clampAdd_spec (x y : UInt64) :
    ⦃True⦄ clampAdd x y ⦃fun r => r.toNat = min (x.toNat + y.toNat) (2 ^ 64 - 1)⦄ := by
  vcgen [clampAdd]
  all_goals
    have := x.toNat_lt_size
    have := y.toNat_lt_size
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.size] at * <;> simp <;> omega

-- `#mp_cost` prints the static cost bound symbolically, or as a number under a given cost model.
/-- info: cost clampAdd ≤ κ.atom + κ.ite + 2 * κ.let_ + 2 * κ.prim + κ.word -/
#guard_msgs in
#mp_cost clampAdd

/-- info: cost clampAdd ≤ 7 -/
#guard_msgs in
#mp_cost clampAdd with CostModel.ones

/-! ## A caller

The normal form of a caller calls `clampAdd` by name. -/

mp def clamp3 (a b c : UInt64) : UInt64 := clampAdd (clampAdd a b) c

example : clamp3 = fun a b c => (do let v ← clampAdd a b; clampAdd v c) := rfl

/-- The caller's specification, proved from the callee's, which is tagged `@[spec]`. -/
theorem clamp3_spec (a b c : UInt64) :
    ⦃True⦄ clamp3 a b c
      ⦃fun r => r.toNat = min (min (a.toNat + b.toNat) (2 ^ 64 - 1) + c.toNat) (2 ^ 64 - 1)⦄ := by
  vcgen [clamp3]
  all_goals grind

-- The caller's cost includes the cost of the callees' bodies.
/-- info: cost clamp3 ≤ 2 * κ.atom + 2 * κ.call + 2 * κ.ite + 5 * κ.let_ + 4 * κ.prim + 8 * κ.word -/
#guard_msgs in
#mp_cost clamp3

/-! ## Loops -/

/-- Counts up to `n` but at most to 100, leaving the loop early when it reaches `n`. -/
mp def countBelow (n : UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...100 do
    if i ≥ n then break
    acc := acc + 1
  acc

example : countBelow = fun n =>
    forIn (List.range 100) (0 : UInt64) (fun i acc =>
      if UInt64.ofNat i < n then pure (ForInStep.yield (acc + 1)) else pure (ForInStep.done acc)) :=
  rfl

/-- `countBelow n` is the smaller of `n` and 100. The invariant still holds at the early exit. -/
theorem countBelow_spec (n : UInt64) :
    ⦃True⦄ countBelow n ⦃fun r => r.toNat = min n.toNat 100⦄ := by
  vcgen [countBelow] invariants
  · fun done _ acc => acc.toNat = min done.length n.toNat
  case vc1 => simp
  case vc2 h => simp at h; omega
  case vc3 _ _ _ hr acc _ hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hc
    have := acc.toNat_lt_size
    simp only [UInt64.toNat_add, List.length_append, List.length_singleton, UInt64.size] at *
    simp
    omega
  case vc4 _ _ _ hr _ _ hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hc
    simp
    omega

/-- The sum `0 + 1 + … + (k-1)` with `k = min n 10`, with a type annotation on the
accumulator. -/
mp def sumTo (n : UInt64) : UInt64 := do
  let mut acc : UInt64 := 0
  for i in 0...10 do
    if i ≥ n then break
    acc := acc + i
  acc

example : (sumTo.exp.denote ω0 (.cons 4 .nil) World.init).1 = 6 := by decide +kernel
example : (sumTo.exp.denote ω0 (.cons 100 .nil) World.init).1 = 45 := by decide +kernel

/-- info: cost sumTo ≤ κ.atom + 10 * κ.ctor + 10 * κ.iter + 10 * κ.let_ + κ.loop + 20 * κ.prim + 22 * κ.word -/
#guard_msgs in
#mp_cost sumTo

/-- A loop whose body calls a function and uses `if`. -/
mp def clampSum (x : UInt64) : UInt64 := do
  let mut acc := x
  for i in 0...5 do
    let t := clampAdd acc i
    acc := if t == 0 then 1 else t
  acc

example : (clampSum.exp.denote ω0 (.cons 1 .nil) World.init).1 = 11 := by decide +kernel

/-! ## `Result` -/

/-- Equality on `Except`, for the checks below. -/
def exceptEq : Except UInt64 UInt64 → Except UInt64 UInt64 → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false


mp def checkedDiv (x y : UInt64) : Result UInt64 UInt64 :=
  if y == 0 then err 1 else ok (x / y)

example : checkedDiv = fun x y =>
    if y = 0 then pure (Except.error 1) else pure (Except.ok (x / y)) := rfl

/-- A specification whose postcondition is about a `Result`. -/
theorem checkedDiv_spec (x y : UInt64) :
    ⦃True⦄ checkedDiv x y ⦃fun r => r = if y = 0 then .error 1 else .ok (x / y)⦄ := by
  vcgen [checkedDiv]
  all_goals simp_all

mp def useDiv (x y : UInt64) : UInt64 :=
  match checkedDiv x y with
  | ok q => q
  | err e => e + 100

example : (useDiv.exp.denote ω0 (.cons 0 (.cons 7 .nil)) World.init).1 = 101 := by decide +kernel
example : (useDiv.exp.denote ω0 (.cons 2 (.cons 7 .nil)) World.init).1 = 3 := by decide +kernel

/-- A linear parameter used once, a linear let, and a linear loop accumulator. -/
mp def passOn (r : Result UInt64 UInt64) (b : Bool) : Result UInt64 UInt64 := do
  let s := r
  let mut acc := s
  for i in 0...3 do
    if !b then break
    match acc with
    | ok a => acc := ok (a + i)
    | err e => acc := err e
  acc

example :
    exceptEq (passOn.exp.denote ω0 (.cons true (.cons (.ok 1) .nil)) World.init).1 (.ok 4) :=
  by decide +kernel
example : passOn.fn.wf = true := passOn.wf

/-! ## Externs -/

mp extern "write" write (fd : UInt64) (buf : Bytes) : UInt64
mp extern noreturn "exit" exit (code : UInt64) : UInt64

/-- The declared signatures are those of Core's `write` and `exit`. -/
example : write = ExtSig.write := rfl
example : exit = ExtSig.exit := rfl

/-- Calls `write(1, "hi\n")` and `exit(0)` and returns the result of `write`. -/
mp def hello : UInt64 :=
  let r := write 1 "hi\n"
  let _x := exit 0
  r

example : hello = fun ω => (do
    let v ← World.callM ω { sym := "write", args := [1], bytesIn := [[104, 105, 10]] } false
    let _ ← World.callM ω { sym := "exit", args := [0], bytesIn := [] } true
    pure v) := rfl

/-- For every oracle, `hello` produces exactly the `write` event, answered by the oracle, and the
`exit` event, and then halts. -/
theorem hello_world (ω : Oracle) :
    (hello.exp.denote ω .nil World.init).2 =
      ⟨[⟨"write", [1], [[104, 105, 10]],
          (ω.answer [] ⟨"write", [1], [[104, 105, 10]], []⟩).result, []⟩,
        ⟨"exit", [0], [], 0, []⟩], true⟩ := by
  rw [hello.exp_denote]
  simp [hello, World.callM, World.call, World.init, Call.event, fitOut, StateT.run, bind,
    StateT.bind, pure, StateT.pure]

/-- An effectful caller of a pure and an effectful function. -/
mp def helloPlus (k : UInt64) : UInt64 := hello + clampAdd k 1

example : helloPlus = fun ω k => (do
    let v ← hello ω
    pure (v + (clampAdd k 1).run)) := rfl

/-- info: cost helloPlus ≤ 2 * κ.atom + 2 * κ.call + 2 * κ.ext + κ.ite + 6 * κ.let_ + 3 * κ.prim + 6 * κ.word -/
#guard_msgs in
#mp_cost helloPlus

/-- An extern call inside a loop, whose normal form is a `forIn` that threads the world. -/
mp def writeN (k : UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...3 do
    if i ≥ k then break
    acc := acc + write 1 "x"
  acc

example : writeN = fun ω k =>
    forIn (List.range 3) (0 : UInt64) (fun i acc =>
      if UInt64.ofNat i < k then (do
        let x ← World.callM ω { sym := "write", args := [1], bytesIn := [[120]] } false
        pure (ForInStep.yield (acc + x)))
      else pure (ForInStep.done acc)) := rfl

/-- info: cost writeN ≤ κ.atom + 3 * κ.ctor + 3 * κ.ext + 3 * κ.iter + 6 * κ.let_ + κ.loop + 6 * κ.prim + 8 * κ.word -/
#guard_msgs in
#mp_cost writeN

/-- Nested `match` on nested `Result`s. -/
mp def nested (r : Result UInt64 (Result Bool UInt64)) : UInt64 :=
  match r with
  | err e => e
  | ok inner =>
    match inner with
    | ok v => v * 2
    | err b => if b then 1 else 0

example : (nested (.ok (.ok 4))).run = 8 := by decide +kernel
example : (nested (.ok (.error true))).run = 1 := by decide +kernel

/-- Shadowing resolves to the innermost binder. -/
mp def shadow (x : UInt64) : UInt64 :=
  let x := x + 1
  let x := x * 2
  x

example : shadow = fun x => pure ((x + 1) * 2) := rfl

/-! ## Rejection tests: one per checker -/

/-- error: unknown variable `z` -/
#guard_msgs in
mp def bad1 (x : UInt64) : UInt64 := x + z

/-- error: unknown function `foo` (not an earlier `mp def` or `mp extern`) -/
#guard_msgs in
mp def bad2 (x : UInt64) : UInt64 := foo x

-- A function is not in scope in its own body, so it cannot recurse.
/-- error: unknown function `bad3` (not an earlier `mp def` or `mp extern`) -/
#guard_msgs in
mp def bad3 (x : UInt64) : UInt64 := bad3 x

/-- error: type mismatch: expected Bool, but this has type UInt64 -/
#guard_msgs in
mp def bad4 (x : UInt64) : Bool := x + 1

/-- error: type mismatch: expected Bool, but this has type UInt64 -/
#guard_msgs in
mp def bad5 (x : UInt64) : UInt64 := if x then 1 else 2

/-- error: type mismatch: expected UInt64, but `ok …` is a Result -/
#guard_msgs in
mp def bad6 (x : UInt64) : UInt64 := ok x

/-- error: cannot infer the Result type of `ok`; add a type ascription `(… : Result ε α)` -/
#guard_msgs in
mp def bad7 (x : UInt64) : UInt64 :=
  let r := ok x
  match r with
  | ok a => a
  | err e => e

/-- error: `clampAdd` expects 2 argument(s), got 1 -/
#guard_msgs in
mp def bad8 (x : UInt64) : UInt64 := clampAdd x

/-- error: the upper bound of a loop must be a size expression (a numeric literal, a `Nat` constant or variable, the length `s.len` of a slice, or `+ - * / %` of those, `/` and `%` by a positive literal), or `min e N` with a size expression `N`: a loop needs a static bound on its number of iterations -/
#guard_msgs in
mp def bad9 (x : UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...x do
    acc := acc + i
  acc

/-- error: the buffer `buf` of `write` is a string literal or a shared slice `&a[lo:hi]` of a byte array -/
#guard_msgs in
mp def bad10 (x : UInt64) : UInt64 := write 1 x

-- A slice parameter cannot be an extern buffer, which must be a slice of a byte array.
/-- error: a slice view (a slice parameter or borrow) is not an extern buffer yet: Core's extern buffer `Buf.slice` is a slice `a[lo..hi]` of a byte array place -/
#guard_msgs in
mp def bad10b (s : &[UInt8; 4]) : UInt64 := write 1 (&s)

/-- error: unsupported syntax in `mp def` -/
#guard_msgs in
mp def bad11 (x : UInt64) : UInt64 := -x

/-- error: equality is only available on UInt64, UInt8 and Bool, not Result UInt64 UInt64 -/
#guard_msgs in
mp def bad12 (r : Result UInt64 UInt64) : Bool := r == r

-- An unused linear `let`
/-- error: unused linear let `r` of type Result UInt64 UInt64: a linear value must be used exactly once (consume it with `match`) -/
#guard_msgs in
mp def bad13 (x : UInt64) : UInt64 :=
  let r : Result UInt64 UInt64 := ok x
  x

-- An unused linear parameter
/-- error: unused linear parameter `r` of type Result UInt64 UInt64: a linear value must be used exactly once (consume it with `match`) -/
#guard_msgs in
mp def bad14 (r : Result UInt64 UInt64) : UInt64 := 3

/-- Consumes a `Result`. -/
mp def useR (r : Result UInt64 UInt64) : UInt64 :=
  match r with
  | ok a => a
  | err e => e

-- A linear value used twice
/-- error: linear parameter `r` of type Result UInt64 UInt64 is used 2 times; it must be used exactly once -/
#guard_msgs in
mp def bad15 (r : Result UInt64 UInt64) : UInt64 :=
  let a := useR r
  let b := useR r
  a + b

-- Branches that use a linear value differently
/-- error: linear variable `r` is used 1 time(s) in the then-branch but 0 time(s) in the else-branch; a linear value must be used the same number of times on every path -/
#guard_msgs in
mp def bad16 (c : Bool) (r : Result UInt64 UInt64) : Result UInt64 UInt64 :=
  if c then r else ok 1

-- A linear variable from outside a loop, used inside it
/-- error: linear variable `r` is bound outside this loop and used inside it; a loop may run any number of times -/
#guard_msgs in
mp def bad17 (r : Result UInt64 UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...3 do
    match r with
    | ok a => acc := a
    | err e => acc := e
  acc

-- A linear carried variable, used by the loop condition
/-- error: the loop condition must not use the linear variable `acc` -/
#guard_msgs in
mp def bad18 (r : Result UInt64 Bool) : Result UInt64 Bool := do
  let mut acc := r
  for i in 0...3 do
    if !(match acc with | ok _ => true | err _ => false) then break
    acc := acc
  acc

-- A linear `match` payload that is dropped
/-- error: unused linear match payload `inner` of type Result UInt64 UInt64: a linear value must be used exactly once (consume it with `match`) -/
#guard_msgs in
mp def bad19 (r : Result UInt64 (Result UInt64 UInt64)) : UInt64 :=
  match r with
  | ok inner => 0
  | err e => e

/-! ## Ordinary Lean

The name `mp` is not reserved, and Lean's own `for … in` still works outside `mp def`. -/

def mp : Nat := 3

def sumList (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s + mp

example : sumList [1, 2, 3] = 9 := rfl

/-! ## Run-time checks against references

Each function is proved equal to the meaning of its Core term, so these checks test that
meaning, which is trusted, against references written directly on `Nat`. -/

/-- Saturating addition, computed on `Nat`. -/
def clampRef (x y : UInt64) : UInt64 := UInt64.ofNat (min (x.toNat + y.toNat) (2 ^ 64 - 1))

/-- One step of a 64-bit linear congruential generator. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random pairs that mix small and large values. -/
def samples : Nat → UInt64 → List (UInt64 × UInt64)
  | 0, _ => []
  | n + 1, s =>
    let a := lcg s
    let b := lcg a
    let x := if a % 3 == 0 then a % 16 else a
    let y := if b % 5 == 0 then b % 16 else b
    (x, y) :: samples n b

#guard (samples 2000 7).all fun (x, y) => (clampAdd x y).run == clampRef x y

#guard (samples 2000 11).all fun (x, _) =>
  (countBelow x).run == UInt64.ofNat (min x.toNat 100)

#guard (samples 500 13).all fun (x, y) =>
  exceptEq (checkedDiv x y).run (if y == 0 then .error 1 else .ok (x / y))

#guard (samples 500 17).all fun (x, y) =>
  (useDiv x y).run == (if y == 0 then 101 else x / y)

end Millipede.Tests.MpDef
