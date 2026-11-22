import Tests.Differential.DoFuncs
import Millipede.Lib.Pool
import Millipede.Lib.Bump

/-!
# Differential tests of generic definitions, each at two instances

`gTri` loops up to a size variable and is run at `n = 4` and `n = 9`. `gPair` is a client of the
allocator interface and is run over the bitmap pool and over the bump arena. Both run through the
whole pipeline on both targets and are compared with references in plain Lean. Each generic
definition is elaborated once, and an instance is an application at the call, such as
`gTri (n := 4)` or `gPair (A := Pool8.impl)`.
-/

namespace Millipede.Tests.Differential

open Millipede Millipede.Lib

set_option mp.autoSafe false

section
variable (n : Nat)

/-- `s := s * 3 + (y >>> i) % 5` for `i < n`, from `s = x`. -/
mp def gTri (x y : UInt64) : UInt64 := do
  let mut s := x
  for i in 0...n do
    s := s * 3 + (y >>> i) % 5
  s

end

section
variable (A : Alloc UInt64)

/-- Store `x` and `y`, free both, combine the values freed. -/
mp def gPair (a : &mut A.S) (x y : UInt64) : UInt64 := do
  let k1 := A.alloc! (&mut a) x
  let k2 := A.alloc! (&mut a) y
  let v := A.free (&mut a) k1
  let w := A.free (&mut a) k2
  v * 3 + w

end

mp def gTri4 (x y : UInt64) : UInt64 := gTri (n := 4) x y
mp def gTri9 (x y : UInt64) : UInt64 := gTri (n := 9) x y

mp def gPool (x y : UInt64) : UInt64 := do
  let mut a : Pool8 := Pool8.new
  gPair (A := Pool8.impl) (&mut a) x y

mp def gBump (x y : UInt64) : UInt64 := do
  let mut a : Bump8 := Bump8.new
  gPair (A := Bump8.impl) (&mut a) x y

def refTri (n : Nat) (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat ((List.range n).foldl (fun s i => W (s * 3 + (y >>> i) % 5)) x)

def refPair (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (W (W (x * 3) + y))


/-- Generic definitions at two instances each. -/
def genericFuncs : List TestFn :=
  [tfm2 "gTri4" gTri4.exp (fun a => (gTri4 a[0]! a[1]!).run) (refTri 4),
   tfm2 "gTri9" gTri9.exp (fun a => (gTri9 a[0]! a[1]!).run) (refTri 9),
   tfm2 "gPool" gPool.exp (fun a => (gPool a[0]! a[1]!).run) refPair,
   tfm2 "gBump" gBump.exp (fun a => (gBump a[0]! a[1]!).run) refPair]

#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (0xdeadbeef, 0x1234)].all
  fun (x, y) => genericFuncs.all fun f =>
    f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]

-- the two instances of `gTri` differ
#guard !(refTri 4 [5, 3] == refTri 9 [5, 3])

end Millipede.Tests.Differential
