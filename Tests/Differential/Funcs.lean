import Millipede.Meta.MpDef
import Millipede.Top.Sound
import Millipede.Top.Examples

/-!
# Differential tests of scalar functions

Each function here is a pure `U64` function written with `mp def` and paired with a reference
written in plain Lean. The reference uses `Nat` arithmetic and structural loops where that is
easy, so that it does not share the `UInt64` operations of the primitives' denotation.
`Tests.Differential.Main` turns each function into a program that runs it on hundreds of inputs
biased towards edge values and compares each result with the reference's value, compiled in as a
literal. `scripts/differential.sh` runs the program under qemu and requires every case to pass.
Functions over memory are tested instead through a reactor that reads its cases from standard
input, defined in `Harness.lean`. Before generating, the generator also checks that the
reference, the `mp def` function and the denotation of the source term agree on every input.

The suite is shown to catch bugs in three ways. Changing `s < 2 ^ 64` to `s ≤ 2 ^ 64` in
`refAddClamp` makes the generator stop with a disagreement for `addClamp` and `clamp3`; this was
done once by hand and reverted. `scripts/differential.sh --selftest` runs the real passes with
the seeded bugs of `Mutants.lean` between them and requires the affected functions to fail. It
also patches the generated ELFs as a bug in code generation would, turning `setb` into `setbe`,
`div` into `idiv` and `shl` into `shr`, and requires those runs to fail.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

/-- A differential test function of `arity` `U64` arguments, given by its source term, together
with its reference. Both take their arguments in source order, first parameter first. -/
structure TestFn where
  name : String
  arity : Nat
  exp : Exp (List.replicate arity Ty.u64) Ty.u64
  /-- the `mp def` function itself as a Lean function, with its arguments in source order -/
  fn : List UInt64 → UInt64
  /-- the independent reference, with its arguments in source order -/
  ref : List UInt64 → UInt64
  /-- a stateful test, given as a whole program whose root is not `Unit`, the content of its
  standard input and the number of cases it checks; the fields above are then placeholders, and
  no per-case consistency check runs -/
  custom : Option (Program × List UInt8 × Nat) := none

/-! ## The functions -/

mp def addClamp (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then 18446744073709551615 else s

/-- Saturating addition on `Nat`. -/
def refAddClamp (a : List UInt64) : UInt64 :=
  let s := a[0]!.toNat + a[1]!.toNat
  UInt64.ofNat (if s < 2 ^ 64 then s else 2 ^ 64 - 1)

mp def arith (x y : UInt64) : UInt64 :=
  let a := x * y
  let b := x - y
  let c := a ^^^ b
  let d := c ||| (~~~x &&& y)
  d + 4294967295

def refArith (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let p := (x * y) % m
  let b := (x + (m - y)) % m
  let c := p ^^^ b
  let d := c ||| (((m - 1 - x) &&& y))
  UInt64.ofNat ((d + 4294967295) % m)

mp def shifts (x y : UInt64) : UInt64 :=
  let a := x <<< y
  let b := x >>> (y + 1)
  let c := (x >>> y) <<< 63
  a ^^^ b ^^^ c

def refShifts (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let a := (x * 2 ^ (y % 64)) % m
  let b := x / 2 ^ ((y + 1) % 64)
  let c := ((x / 2 ^ (y % 64)) * 2 ^ 63) % m
  UInt64.ofNat (a ^^^ b ^^^ c)

mp def divmod (x y : UInt64) : UInt64 :=
  let q := x / y
  let r := x % y
  let z := if y == 0 then 1000 else 0
  q * 7 + r + z

def refDivmod (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let q := if y = 0 then 0 else x / y
  let r := if y = 0 then x else x % y
  UInt64.ofNat (q * 7 + r + (if y = 0 then 1000 else 0))

mp def divc (x : UInt64) : UInt64 :=
  x / 10 + x % 7 + x / 1 + x % 1 + x / 18446744073709551615

def refDivc (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  UInt64.ofNat (x / 10 + x % 7 + x + 0 + x / 18446744073709551615)

mp def cmps (x y : UInt64) : UInt64 :=
  let a := if x < y then 1 else 0
  let b := if x <= y then 2 else 0
  let c := if x > y then 4 else 0
  let d := if x >= y then 8 else 0
  let e := if x == y then 16 else 0
  let f := if x != y then 32 else 0
  let g := if x < y && y != 0 || !(x == 5) then 64 else 0
  let h := if (x < 9223372036854775808) == (y < 9223372036854775808) then 128 else 0
  a + b + c + d + e + f + g + h

def refCmps (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let t (b : Bool) (n : Nat) : Nat := if b then n else 0
  let h := 2 ^ 63
  UInt64.ofNat (t (x < y) 1 + t (x ≤ y) 2 + t (y < x) 4 + t (y ≤ x) 8 + t (x = y) 16 +
    t (x ≠ y) 32 + t ((x < y && y != 0) || !(x == 5)) 64 + t ((x < h) == (y < h)) 128)

mp def popcount (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := 0
  for i in 0...64 do
    acc := acc + ((x >>> i) &&& 1)
  acc

def refPopcount (a : List UInt64) : UInt64 :=
  let rec go : Nat → Nat → Nat
    | 0, _ => 0
    | k + 1, n => n % 2 + go k (n / 2)
  UInt64.ofNat (go 64 a[0]!.toNat)

mp def collatz (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := x
  for i in 0...200 do
    if acc == 1 then break
    acc := (if acc &&& 1 == 0 then acc >>> 1 else 3 * acc + 1)
  acc

def refCollatz (a : List UInt64) : UInt64 :=
  let rec go : Nat → Nat → Nat
    | 0, n => n
    | k + 1, n => if n = 1 then n else go k (if n % 2 = 0 then n / 2 else (3 * n + 1) % 2 ^ 64)
  UInt64.ofNat (go 200 a[0]!.toNat)

mp def lcg (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := x
  for i in 0...20 do
    acc := acc * 6364136223846793005 + 1442695040888963407 + i
  acc

def refLcg (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) ((acc * 6364136223846793005 + 1442695040888963407 + i) % m)
  UInt64.ofNat (go 20 0 a[0]!.toNat)

mp def sumTo (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := 0
  for i in 0...100 do
    if i ≥ x then break
    acc := acc + i
  acc

def refSumTo (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  UInt64.ofNat (((List.range 100).filter (· < x)).foldl (· + ·) 0)

mp def clamp3 (x y z : UInt64) : UInt64 :=
  let a := addClamp x y
  let b := addClamp a z
  addClamp b (addClamp z x)

def refClamp3 (a : List UInt64) : UInt64 :=
  let s (u v : UInt64) := refAddClamp [u, v]
  s (s (s a[0]! a[1]!) a[2]!) (s a[2]! a[0]!)

mp def checkedDiv (x y : UInt64) : Result UInt64 UInt64 :=
  if y == 0 then err 1 else ok (x / y)

mp def checked (x y : UInt64) : UInt64 :=
  match checkedDiv x y with
  | ok q => q
  | err e => e + 100

def refChecked (a : List UInt64) : UInt64 :=
  if a[1]! = 0 then 101 else UInt64.ofNat (a[0]!.toNat / a[1]!.toNat)

mp def bigImm (x : UInt64) : UInt64 :=
  let a := (x + 4294967295) ^^^ 2147483648
  let b := (x &&& 18446744069414584320) - 9223372036854775808
  let c := x * 4294967296 + 18446744073709551615
  let d := (x ||| 4294967296) - 2147483647 + 2147483648
  a + b + c + d

def refBigImm (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let a := (x + 4294967295) % m ^^^ 2147483648
  let b := ((x &&& 18446744069414584320) + (m - 9223372036854775808)) % m
  let c := (x * 4294967296 + 18446744073709551615) % m
  let d := ((x ||| 4294967296) + (m - 2147483647) + 2147483648) % m
  UInt64.ofNat ((a + b + c + d) % m)

mp def pressure (a b c : UInt64) : UInt64 :=
  let t1 := a + b
  let t2 := b * c
  let t3 := a ^^^ c
  let t4 := t1 + t2
  let t5 := t2 ^^^ t3
  let t6 := t4 - t5
  let t7 := t1 &&& t3
  let t8 := t6 ||| t7
  let t9 := t8 + t1
  let t10 := t9 ^^^ t2
  let t11 := t10 - t3
  let t12 := t11 * 3
  t12 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11

def refPressure (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let z := a[2]!.toNat
  let t1 := (x + y) % m
  let t2 := (y * z) % m
  let t3 := x ^^^ z
  let t4 := (t1 + t2) % m
  let t5 := t2 ^^^ t3
  let t6 := (t4 + (m - t5)) % m
  let t7 := t1 &&& t3
  let t8 := t6 ||| t7
  let t9 := (t8 + t1) % m
  let t10 := t9 ^^^ t2
  let t11 := (t10 + (m - t3)) % m
  let t12 := (t11 * 3) % m
  UInt64.ofNat ((t12 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) % m)

mp def stepMix (acc i : UInt64) : UInt64 :=
  (acc ^^^ (acc >>> 7)) * 3 + i

/-- A loop whose body is a call to a function without a loop. -/
mp def mixLoop (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := x
  for i in 0...8 do
    acc := stepMix acc i
  acc

def refMixLoop (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, i, acc =>
      go k (i + 1) ((((acc ^^^ (acc / 2 ^ 7)) * 3) + i) % m)
  UInt64.ofNat (go 8 0 a[0]!.toNat)

/-- The inner loop of `nest`, which is a call containing a loop. -/
mp def inner (acc j : UInt64) : UInt64 := do
  let mut a : UInt64 := acc
  for k in 0...4 do
    a := (a + j) * 3 + k
  a

mp def nest (x : UInt64) : UInt64 := do
  let mut acc : UInt64 := x
  for i in 0...6 do
    acc := inner acc i
  acc

def refNest (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let rec inn (j : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    -- `inn` counts `k` downward, so `3 - k` is the ascending `k` of `inner`
    | k + 1, acc => inn j k (((acc + j) * 3 + (3 - k)) % m)
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (inn i 4 acc)
  UInt64.ofNat (go 6 0 a[0]!.toNat)

/-- The difference between the largest and the smallest of three words. -/
mp def minmax (x y z : UInt64) : UInt64 :=
  let lo := if x < y then (if x < z then x else z) else (if y < z then y else z)
  let hi := if x > y then (if x > z then x else z) else (if y > z then y else z)
  hi - lo

def refMinmax (a : List UInt64) : UInt64 :=
  let xs := a.map UInt64.toNat
  let hi := xs.foldl max 0
  let lo := xs.foldl min (2 ^ 64)
  UInt64.ofNat (hi - lo)

/-! ## Registry -/

/-- A test function of one argument. `tf2` and `tf3` take two and three. -/
def tf1 (name : String) (e : Exp [Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) : TestFn :=
  { name, arity := 1, exp := e, fn, ref }
def tf2 (name : String) (e : Exp [Ty.u64, Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) :
    TestFn := { name, arity := 2, exp := e, fn, ref }
def tf3 (name : String) (e : Exp [Ty.u64, Ty.u64, Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) :
    TestFn := { name, arity := 3, exp := e, fn, ref }

/-! ### High register pressure

`hpLeaf` is a leaf with twelve values live at once, and `hpCall` keeps eight values live across
three calls while it computes temporaries between them. They measure the register locations
under pressure (doc/measurements.md). -/

mp def hpLeaf (a b c : UInt64) : UInt64 :=
  let v1 := a + b
  let v2 := a ^^^ c
  let v3 := b * 3
  let v4 := c + 7
  let v5 := a - c
  let v6 := b ||| c
  let v7 := a &&& b
  let v8 := c * 5
  let v9 := a + 11
  let v10 := b ^^^ 13
  let v11 := c - b
  let v12 := a * c
  let s1 := (v1 + v12) * (v2 + v11)
  let s2 := (v3 + v10) ^^^ (v4 + v9)
  let s3 := (v5 + v8) * (v6 + v7)
  s1 + s2 + s3 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12

def refHpLeaf (a : List UInt64) : UInt64 :=
  let x := a[0]!; let y := a[1]!; let z := a[2]!
  let v1 := x + y; let v2 := x ^^^ z; let v3 := y * 3; let v4 := z + 7
  let v5 := x - z; let v6 := y ||| z; let v7 := x &&& y; let v8 := z * 5
  let v9 := x + 11; let v10 := y ^^^ 13; let v11 := z - y; let v12 := x * z
  let s1 := (v1 + v12) * (v2 + v11)
  let s2 := (v3 + v10) ^^^ (v4 + v9)
  let s3 := (v5 + v8) * (v6 + v7)
  s1 + s2 + s3 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12

mp def hpCall (a b c : UInt64) : UInt64 :=
  let v1 := a + b
  let v2 := a ^^^ c
  let v3 := b * 3
  let v4 := c + 7
  let v5 := a - c
  let v6 := b ||| c
  let v7 := a &&& b
  let v8 := c * 5
  let w1 := addClamp v1 v2
  let t1 := w1 * 3 + v3
  let t2 := t1 ^^^ v4
  let w2 := addClamp t2 v5
  let t3 := w2 + v6 * 7
  let t4 := t3 ^^^ (t1 + t2)
  let w3 := addClamp t4 v7
  w1 + w2 + w3 + t1 + t2 + t3 + t4 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8

def refHpCall (a : List UInt64) : UInt64 :=
  let x := a[0]!; let y := a[1]!; let z := a[2]!
  let ac (u v : UInt64) := refAddClamp [u, v]
  let v1 := x + y; let v2 := x ^^^ z; let v3 := y * 3; let v4 := z + 7
  let v5 := x - z; let v6 := y ||| z; let v7 := x &&& y; let v8 := z * 5
  let w1 := ac v1 v2
  let t1 := w1 * 3 + v3
  let t2 := t1 ^^^ v4
  let w2 := ac t2 v5
  let t3 := w2 + v6 * 7
  let t4 := t3 ^^^ (t1 + t2)
  let w3 := ac t4 v7
  w1 + w2 + w3 + t1 + t2 + t3 + t4 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8

/-- The scalar differential functions. -/
def funcs : List TestFn :=
  [tf2 "addClamp" addClamp.exp (fun a => (addClamp a[0]! a[1]!).run) refAddClamp,
   tf2 "arith" arith.exp (fun a => (arith a[0]! a[1]!).run) refArith,
   tf2 "shifts" shifts.exp (fun a => (shifts a[0]! a[1]!).run) refShifts,
   tf2 "divmod" divmod.exp (fun a => (divmod a[0]! a[1]!).run) refDivmod,
   tf1 "divc" divc.exp (fun a => (divc a[0]!).run) refDivc,
   tf2 "cmps" cmps.exp (fun a => (cmps a[0]! a[1]!).run) refCmps,
   tf1 "popcount" popcount.exp (fun a => (popcount a[0]!).run) refPopcount,
   tf1 "collatz" collatz.exp (fun a => (collatz a[0]!).run) refCollatz,
   tf1 "lcg" lcg.exp (fun a => (lcg a[0]!).run) refLcg,
   tf1 "sumTo" sumTo.exp (fun a => (sumTo a[0]!).run) refSumTo,
   tf3 "clamp3" clamp3.exp (fun a => (clamp3 a[0]! a[1]! a[2]!).run) refClamp3,
   tf2 "checked" checked.exp (fun a => (checked a[0]! a[1]!).run) refChecked,
   tf1 "bigImm" bigImm.exp (fun a => (bigImm a[0]!).run) refBigImm,
   tf3 "pressure" pressure.exp (fun a => (pressure a[0]! a[1]! a[2]!).run) refPressure,
   tf1 "mixLoop" mixLoop.exp (fun a => (mixLoop a[0]!).run) refMixLoop,
   tf1 "nest" nest.exp (fun a => (nest a[0]!).run) refNest,
   tf3 "minmax" minmax.exp (fun a => (minmax a[0]! a[1]! a[2]!).run) refMinmax,
   tf3 "hpLeaf" hpLeaf.exp (fun a => (hpLeaf a[0]! a[1]! a[2]!).run) refHpLeaf,
   tf3 "hpCall" hpCall.exp (fun a => (hpCall a[0]! a[1]! a[2]!).run) refHpCall]

end Millipede.Tests.Differential
