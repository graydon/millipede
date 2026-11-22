import Millipede.Meta.MpDef
import Std.Tactic.Do
import Std.WP

/-!
# Tests for the statements of `mp def`

`mp def` reads its body in Lean's `do` notation and gives each statement a Millipede meaning.
This suite checks that meaning on sample values with `rfl` and `decide`, for early `return`,
`break` and `continue`, ranges with lower, inclusive, empty and run-time bounds, branches that
shadow a name, and loops over linear variables. It also checks that the size of the Core term
grows linearly with the number of statement `if`s, and that the index obligations of loops with
an offset are still discharged automatically.

Each form that `mp def` refuses has a rejection test that pins its message with `#guard_msgs`.
A loop with jumps is compared with a reference written in plain Lean, so a wrong translation of
`continue` fails the suite.

The statements are described in doc/reference/statements.md.
-/

namespace Millipede.Tests.DoNotation

open Millipede Std.WP

set_option experimental.vcgen true

/-! ## Meaning -/

/-- Returns the position of `c` in a table of three opening brackets, or 3 when it is absent. -/
mp def kindOfR (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3

example : kindOfR 91 = pure 1 := rfl
example : kindOfR 7 = pure 3 := rfl
example := @kindOfR.spec

/-- `break` in the middle of a body and `continue`, with two carried variables. -/
mp def jumps (x : UInt64) : UInt64 := do
  let mut s := 0
  let mut n := 0
  for i in 0...10 do
    if i % 3 == 0 then continue
    s := s + i
    if s > x then break
    n := n + 1
  s * 100 + n

example : (jumps 1000).run = 2706 := by decide
example : (jumps 5).run = 702 := by decide

/-- Loops over a range with a lower bound, an inclusive range, an empty range and a range with
a run-time lower bound. -/
mp def ranges (x : UInt64) : UInt64 := do
  let mut a := 0
  for i in 3...6 do
    a := a * 10 + i
  for i in 1...=2 do
    a := a * 10 + i
  for i in 5...2 do
    a := a + 1000000
  for i in x...4 do
    a := a * 10 + i
  a

example : (ranges 2).run = 3451223 := by decide
example : (ranges 9).run = 34512 := by decide

/-- A run-time bound with a `min` cap is evaluated once, before the body changes `n`. -/
mp def capped (n : UInt64) : UInt64 := do
  let mut n := n
  let mut c := 0
  for i in 0...min n 5 do
    n := n + 1
    c := c + 1
  c * 100 + n

example : (capped 3).run = 306 := by decide
example : (capped 50).run = 555 := by decide

/-- A statement `if` whose branch binds `y` while the rest of the block reads the outer `y`. -/
mp def shadow (c : Bool) : UInt64 := do
  let y := 1
  let mut x := 10
  if c then
    let y := 2
    x := x + y
  x * 10 + y

example : shadow true = pure 121 := rfl
example : shadow false = pure 101 := rfl

/-- A `return` outside a loop makes the rest of the block the other branch of the `if`. -/
mp def early (x : UInt64) : UInt64 := do
  if x == 0 then return 7
  let y := x * 2
  y + 1

example : early 0 = pure 7 := rfl
example : early 3 = pure 7 := rfl

/-- Ten statement `if`s in a row. Each is joined once and the rest of the block follows the
join, so the Core term has ten `ite`s. -/
mp def tenIfs (x : UInt64) : UInt64 := do
  let mut s := x
  let mut n := 0
  if s % 2 == 0 then s := s / 2 else s := s * 3 + 1
  if s % 2 == 0 then
    s := s / 2
  else
    s := s * 3 + 1
    n := n + 1
  if s % 2 == 0 then s := s / 2 else s := s * 3 + 1
  if s % 2 == 0 then
    s := s / 2
  else
    s := s * 3 + 1
    n := n + 1
  if s % 2 == 0 then s := s / 2 else s := s * 3 + 1
  if s % 2 == 0 then
    s := s / 2
  else
    s := s * 3 + 1
    n := n + 1
  if s % 2 == 0 then s := s / 2 else s := s * 3 + 1
  if s % 2 == 0 then
    s := s / 2
  else
    s := s * 3 + 1
    n := n + 1
  if s % 2 == 0 then s := s / 2 else s := s * 3 + 1
  if s % 2 == 0 then
    s := s / 2
  else
    s := s * 3 + 1
    n := n + 1
  s * 100 + n

example : (tenIfs 27).run = 21403 := by decide
example : (tenIfs 1024).run = 100 := by decide

open Lean in
/-- The number of occurrences of the constant `c` in `e`, counted as a tree without sharing. -/
partial def countConst (c : Name) : Expr → Nat
  | .const d _ => if d == c then 1 else 0
  | .app f a => countConst c f + countConst c a
  | .lam _ t b _ | .forallE _ t b _ => countConst c t + countConst c b
  | .letE _ t v b _ => countConst c t + countConst c v + countConst c b
  | .mdata _ e | .proj _ _ e => countConst c e
  | _ => 0

-- `tenIfs.exp` has exactly ten `Exp.ite`s.
open Lean Elab Command in
run_cmd do
  let some v := (Lean.Environment.find? (← Lean.getEnv) ``tenIfs.exp).bind (·.value?) | throwError "no tenIfs.exp"
  let n := countConst ``Exp.ite v
  unless n == 10 do throwError "tenIfs.exp has {n} `Exp.ite`s, expected 10"

/-- Six statement `if`s in a loop, each with two branches that go on and one that jumps with
`continue`. Each is joined once with a flag that records the jump, so the Core term is linear in
the number of statements; copying the rest of the block into the two branches that go on instead
would give 2⁶ copies of the last statement. Six are enough to tell the two apart: the kernel's
check of the normal-form equation `sixJumps.exp_run` grows about as the cube of the number of
statements (doc/phases/auto-speed.md), and twelve took 40 s to several minutes and 8 GB. -/
mp def sixJumps (x : UInt64) : UInt64 := do
  let mut s := 0
  let mut t := 0
  for i in 0...4 do
    if (x >>> 0) % 3 == 0 then s := s + 0 else if (x >>> 0) % 3 == 1 then t := t + 0 else continue
    if (x >>> 1) % 3 == 0 then s := s + 1 else if (x >>> 1) % 3 == 1 then t := t + 1 else continue
    if (x >>> 2) % 3 == 0 then s := s + 2 else if (x >>> 2) % 3 == 1 then t := t + 2 else continue
    if (x >>> 3) % 3 == 0 then s := s + 3 else if (x >>> 3) % 3 == 1 then t := t + 3 else continue
    if (x >>> 4) % 3 == 0 then s := s + 4 else if (x >>> 4) % 3 == 1 then t := t + 4 else continue
    if (x >>> 5) % 3 == 0 then s := s + 5 else if (x >>> 5) % 3 == 1 then t := t + 5 else continue
    s := s + i
  s * 1000 + t

/-- The reference for `sixJumps`, in which an iteration ends at the first `k` with
`(x >>> k) % 3 = 2`. -/
def sixJumpsRef (x : Nat) : Nat := Id.run do
  let mut s := 0
  let mut t := 0
  for i in List.range 4 do
    let mut stop := false
    for k in List.range 6 do
      if !stop then
        if (x >>> k) % 3 == 0 then s := s + k
        else if (x >>> k) % 3 == 1 then t := t + k
        else stop := true
    if !stop then s := s + i
  s * 1000 + t

example : [0, 1, 5, 0x5555, 0xffffff, 123456789].all fun x =>
    (sixJumps (UInt64.ofNat x)).run.toNat == sixJumpsRef x := by decide

open Lean in
/-- The number of Core term constructors in `e`, counted as a tree without sharing. -/
partial def countExp : Expr → Nat
  | .const d _ => if d.getPrefix == ``Exp then 1 else 0
  | .app f a => countExp f + countExp a
  | .lam _ t b _ | .forallE _ t b _ => countExp t + countExp b
  | .letE _ t v b _ => countExp t + countExp v + countExp b
  | .mdata _ e | .proj _ _ e => countExp e
  | _ => 0

-- `sixJumps.exp` has about three `Exp.ite`s per statement, two for its arms and one for the
-- jump flag, and its size is linear in the number of statements.
open Lean Elab Command in
run_cmd do
  let some v := (Lean.Environment.find? (← Lean.getEnv) ``sixJumps.exp).bind (·.value?)
    | throwError "no sixJumps.exp"
  let n := countConst ``Exp.ite v
  unless n == 17 do throwError "sixJumps.exp has {n} `Exp.ite`s, expected 17"
  let m := countExp v
  unless m ≤ 40 * 6 do throwError "sixJumps.exp has {m} Core constructors"

/-- A join keeps what each branch established, so `i < 4` holds after the statement `if`. -/
mp def pickAfterJoin (a : Arr UInt64 4) (c d : Bool) : UInt64 := do
  let mut i := 0
  let mut t := 1
  if c then i := 3; t := 2 else i := 1
  if d then t := t + 1
  a[i]! * t

example := @pickAfterJoin.safe

/-! ## A loop invariant by hand over several carried variables

The loop's state is a nested tuple `(acc, (x₁, (x₂, … ())))`. The accumulator `acc` is the word
variable declared last among those the body ends by assigning, here `m`, and the other variables
the body assigns follow in the order they are declared, here `n`. A pattern in the invariant
names the components. -/

set_option mp.autoSpec false in
mp def countBoth (w : Arr UInt64 4) ensures result ≤ 8 : UInt64 := do
  let mut n := 0
  let mut m := 0
  for i in 0...4 do
    if w[i] == 1 then n := n + 1
    if w[i] == 2 then m := m + 1
  n + m
mp prove countBoth.spec := by
  intro w; vcgen [countBoth] invariants
  · fun done _ (m, n, _) => m.toNat ≤ done.length ∧ n.toNat ≤ done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind

/-! ## Linear variables and loop counters

An assignment `x := e` to a linear `let mut x`, where `e` consumes the old value of `x`, binds
the new value to `x`. The tests do this in straight-line code, in a branch, and in a loop that
assigns other variables too. -/

mp def bumpR (r : Result UInt64 UInt64) : Result UInt64 UInt64 :=
  match r with
  | ok a => ok (a + 1)
  | err e => err e

mp def useR (r : Result UInt64 UInt64) : UInt64 :=
  match r with
  | ok a => a
  | err e => e

mp def linStraight (x : UInt64) : UInt64 := do
  let mut r : Result UInt64 UInt64 := ok x
  r := bumpR r
  r := bumpR r
  useR r

mp def linIf (x : UInt64) (c : Bool) : UInt64 := do
  let mut r : Result UInt64 UInt64 := ok x
  if c then r := bumpR r
  useR r

mp def linLoop (x : UInt64) : UInt64 := do
  let mut r : Result UInt64 UInt64 := ok x
  let mut n := 0
  for i in 0...3 do
    r := bumpR r
    n := n + 1
  useR r * 10 + n

example : (linStraight 5).run = 7 := by decide
example : (linIf 5 true).run = 6 := by decide
example : (linIf 5 false).run = 5 := by decide
example : (linLoop 5).run = 83 := by decide

/-- A counter that shadows a variable the body does not assign is renamed. -/
mp def counterShadow (x : UInt64) : UInt64 := do
  let i := x
  let mut s := 0
  for i in 0...3 do
    s := s + i
  i + s

example : (counterShadow 1000).run = 1003 := by decide

/-- error: the counter `i` shadows the variable `i`, which the loop body assigns: rename the counter -/
#guard_msgs in
mp def counterAssigned (x : UInt64) : UInt64 := do
  let mut i := x
  for i in 0...3 do
    i := i + 10
  i

/-- error: `y` is not mutable: declare it with `let mut` (or take it as `&mut`) to assign it -/
#guard_msgs in
mp def renamedNotMut (c : Bool) : UInt64 := do
  let y := 1
  let mut x := 0
  if c then
    let y := 2
    y := 3
    x := y
  x + y

-- The loop's state is `(m, (n, ()))` as for `countBoth`, although `z`, which the loop does not
-- assign, is declared between them.
set_option mp.autoSpec false in
mp def countBoth2 (w : Arr UInt64 4) ensures result ≤ 8 : UInt64 := do
  let mut n := 0
  let mut z := 7
  let mut m := 0
  for i in 0...4 do
    if w[i] == 1 then n := n + 1
    if w[i] == 2 then m := m + 1
  n + m + (z - 7)
mp prove countBoth2.spec := by
  intro w; vcgen [countBoth2] invariants
  · fun done _ (m, n, _) => m.toNat ≤ done.length ∧ n.toNat ≤ done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind

/-! ## A join writes a large variable in place

A statement `if` that writes one cell of an array borrows the array, so the array is not copied
when the branches join, and the cost charges no words for the join. The words left are copies the
code makes, such as the array's initial value. -/

mp def bigJoin (c : Bool) (x : UInt64) : UInt64 := do
  let mut a : Arr UInt64 512 := Vector.replicate 512 0
  if c then a[0] := x
  let y := a[0] + 1
  let z := y * 2
  let w := z + y
  let v := w * 3
  let u := v + z
  let q := u + w
  let p := q + 1
  if p > 5 then a[1] := p
  a[1]

example : (bigJoin true 3).run = 57 := by decide
example : (bigJoin false 3).run = 15 := by decide

/-- info: cost bigJoin ≤ κ.ctor + 2 * κ.ite + 10 * κ.let_ + κ.mem + κ.place + 8 * κ.prim + κ.ref + 513 * κ.word +
    max (2 * κ.ctor + κ.let_ + κ.mem + κ.place + κ.word) (2 * κ.ctor + κ.let_) +
  max (2 * κ.mem + 2 * κ.place + 2 * κ.word) (κ.mem + κ.place + κ.word) -/
#guard_msgs in
#mp_cost bigJoin

/-! ## A generic slice: `s.len` bounds a loop over `&mut [T; n]` -/

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)
mp def gFill (s : &mut [T; n]) (v : T) : Unit := do
  for i in 0...s.len do
    s[i] := v
end
example := @gFill.safe

/-! ## What stays automatic: obligations through the offset `i = k + lo` -/

mp def sumFrom2 (a : Arr UInt64 8) : UInt64 := do
  let mut s := 0
  for i in 2...8 do
    s := s + a[i]
  s

mp def sumIncl (a : Arr UInt64 8) : UInt64 := do
  let mut s := 0
  for i in 1...=7 do
    s := s + a[i]
  s

mp def sumSliceFrom (s : &[UInt64; 8]) (lo : UInt64) : UInt64 := do
  let mut acc := 0
  for i in lo...s.len do
    acc := acc + s[i]
  acc

example := @sumFrom2.safe
example := @sumIncl.safe
example := @sumSliceFrom.safe

/-! ## Rejections -/

/-- error: unbounded loops (`while`, `repeat`) are not supported in `mp def`: write a bounded loop `for i in lo...hi do` and leave it with `if c then break` -/
#guard_msgs in
mp def noWhile (x : UInt64) : UInt64 := do
  let mut y := x
  while y > 0 do
    y := y - 1
  y

/-- error: unbounded loops (`while`, `repeat`) are not supported in `mp def`: write a bounded loop `for i in lo...hi do` and leave it with `if c then break` -/
#guard_msgs in
mp def noRepeat (x : UInt64) : UInt64 := do
  repeat
    break
  x

/-- error: `try`/`catch`/`finally` is not supported in `mp def`: errors are `Result` values (`match r with | ok a => … | err e => …`) -/
#guard_msgs in
mp def noTry (x : UInt64) : UInt64 := do
  try
    pure x
  catch _ =>
    pure 0

/-- error: `←` is not supported in `mp def`: a call is written directly, `let x := f a` -/
#guard_msgs in
mp def noArrow (x : UInt64) : UInt64 := do
  let y ← pure x
  y

/-- error: a `for` loop in `mp def` runs over a range of words `lo...hi` (upper bound excluded) or `lo...=hi` (included) -/
#guard_msgs in
mp def noList (x : UInt64) : UInt64 := do
  let mut s := x
  for i in [1, 2, 3] do
    s := s + i
  s

/-- error: the upper bound of a loop must be a size expression (a numeric literal, a `Nat` constant or variable, the length `s.len` of a slice, or `+ - * / %` of those, `/` and `%` by a positive literal), or `min e N` with a size expression `N`: a loop needs a static bound on its number of iterations -/
#guard_msgs in
mp def noCap (n : UInt64) : UInt64 := do
  let mut s := 0
  for i in 0...n do
    s := s + i
  s

/-- error: an inclusive upper bound must be below 2^64 - 1 (the counter would wrap around); this one may be 18446744073709551615 -/
#guard_msgs in
mp def noWrap : UInt64 := do
  let mut s := 0
  for i in 0...=18446744073709551615 do
    s := s + i
  s

/-- error: `break` outside a `for` loop -/
#guard_msgs in
mp def noBreak (x : UInt64) : UInt64 := do
  if x == 0 then break
  x

/-- error: `return` is only supported in the body of an `mp def`, not in a nested `do` term -/
#guard_msgs in
mp def noNestedReturn (x : UInt64) : UInt64 := do
  let y := (do return x)
  y

/-- error: unreachable: a statement after `return` in the same block -/
#guard_msgs in
mp def noDead (x : UInt64) : UInt64 := do
  return x
  x + 1

/-- error: the value of this statement (of type UInt64) would be discarded: bind it with `let _ := …`, or make it the last element of the block -/
#guard_msgs in
mp def noDiscard (x : UInt64) : UInt64 := do
  x + 1
  x

/-- error: this statement and the rest of its block translate to 102379 nodes, more than the limit of 100000: split the function into smaller ones -/
#guard_msgs in
set_option mp.autoSafe false in
/-- A statement `if` that writes a reference is copied into its branches instead of being joined,
so twenty of them in a row exceed the size limit, which `mp def` reports as an error. -/
mp def tooLarge (r : &mut UInt64) (x : UInt64) : UInt64 := do
  for i in 0...4 do
    if (x >>> 0) % 3 == 0 then r := r + 0 else if (x >>> 0) % 3 == 1 then r := r * 0 else continue
    if (x >>> 1) % 3 == 0 then r := r + 1 else if (x >>> 1) % 3 == 1 then r := r * 1 else continue
    if (x >>> 2) % 3 == 0 then r := r + 2 else if (x >>> 2) % 3 == 1 then r := r * 2 else continue
    if (x >>> 3) % 3 == 0 then r := r + 3 else if (x >>> 3) % 3 == 1 then r := r * 3 else continue
    if (x >>> 4) % 3 == 0 then r := r + 4 else if (x >>> 4) % 3 == 1 then r := r * 4 else continue
    if (x >>> 5) % 3 == 0 then r := r + 5 else if (x >>> 5) % 3 == 1 then r := r * 5 else continue
    if (x >>> 6) % 3 == 0 then r := r + 6 else if (x >>> 6) % 3 == 1 then r := r * 6 else continue
    if (x >>> 7) % 3 == 0 then r := r + 7 else if (x >>> 7) % 3 == 1 then r := r * 7 else continue
    if (x >>> 8) % 3 == 0 then r := r + 8 else if (x >>> 8) % 3 == 1 then r := r * 8 else continue
    if (x >>> 9) % 3 == 0 then r := r + 9 else if (x >>> 9) % 3 == 1 then r := r * 9 else continue
    if (x >>> 10) % 3 == 0 then r := r + 10 else if (x >>> 10) % 3 == 1 then r := r * 10 else continue
    if (x >>> 11) % 3 == 0 then r := r + 11 else if (x >>> 11) % 3 == 1 then r := r * 11 else continue
    if (x >>> 12) % 3 == 0 then r := r + 12 else if (x >>> 12) % 3 == 1 then r := r * 12 else continue
    if (x >>> 13) % 3 == 0 then r := r + 13 else if (x >>> 13) % 3 == 1 then r := r * 13 else continue
    if (x >>> 14) % 3 == 0 then r := r + 14 else if (x >>> 14) % 3 == 1 then r := r * 14 else continue
    if (x >>> 15) % 3 == 0 then r := r + 15 else if (x >>> 15) % 3 == 1 then r := r * 15 else continue
    if (x >>> 16) % 3 == 0 then r := r + 16 else if (x >>> 16) % 3 == 1 then r := r * 16 else continue
    if (x >>> 17) % 3 == 0 then r := r + 17 else if (x >>> 17) % 3 == 1 then r := r * 17 else continue
    if (x >>> 18) % 3 == 0 then r := r + 18 else if (x >>> 18) % 3 == 1 then r := r * 18 else continue
    if (x >>> 19) % 3 == 0 then r := r + 19 else if (x >>> 19) % 3 == 1 then r := r * 19 else continue
    r := r + i
  0

/-- error: `mp.selftest.doMutant` seeds a bug into the translation of `mp def`: it is allowed only in Tests/Differential/DoFuncs.lean -/
#guard_msgs in
set_option mp.selftest.doMutant "break-ignored" in
mp def seededHere (x : UInt64) : UInt64 := do
  let mut s := 0
  for i in 0...4 do
    if i == x then break
    s := s + i
  s

/-- error: `if let` and `if h : c` are not supported in `mp def` -/
#guard_msgs in
mp def noIfLet (x : UInt64) : UInt64 := do
  if h : x = 0 then return 1
  x

/-! A loop with a run-time lower bound and an inclusive upper bound near `2^64` that stops
early. Its normal form iterates over `upto n`, which compiled code counts lazily, so the
evaluation below does not build a list of `n` elements. -/
set_option mp.autoSafe false in
mp def inclTop (x y : UInt64) : UInt64 := do
  let mut s := 0
  let mut c := 0
  for i in (18446744073709551600 + x % 14)...=18446744073709551613 do
    if c >= y % 9 then break
    s := s + (i - 18446744073709551600)
    c := c + 1
  s * 100 + c

#guard (inclTop 3 5).run == 2505
#guard (inclTop 13 8).run == 1301
#guard (inclTop 0 0).run == 0
/-- info: 5505 -/
#guard_msgs in #eval (inclTop 9 17).run

end Millipede.Tests.DoNotation
