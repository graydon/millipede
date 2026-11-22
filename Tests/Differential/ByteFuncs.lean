import Tests.Differential.SliceFuncs

/-!
# Differential tests of operations on bytes

Each function is an `mp def` over two words that runs through the whole pipeline under qemu and is
compared with a reference in plain Lean over `Nat` and `List`. Bytes are computed on through the
conversions `x.toUInt64` and `x.toUInt8`, which `mp def` inserts around the `U64` operations.
`bTok` writes digits and spaces chosen by the inputs into an owned byte array in a loop, then
finds and parses the space-separated numbers through sub-slices of the array and hashes the
results. `bOps` packs into one word wrapping byte arithmetic, division and remainder, bitwise
operations, the six comparisons and the conversions both ways.

The seeded mutants `flat-trunc8`, which masks a narrowed byte with `0x7F`, and `flat-zext8`, which
sets bit 8 when it widens a byte, must make both functions fail.

`bFill` builds a 100-byte array filled with a literal, which `lower` writes with a store loop, and
`bCopy` puts a 64-byte array into a structure, which `lower` copies with a load and store loop. The
seeded mutants `loop-fill-short` and `loop-copy-short` stop each loop one word early and must make
`bFill` and `bCopy` fail.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

mp def btParse (s : &[UInt8; 32]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc * 10 + (s[i].toUInt64 - 48)
  acc

mp def btEnd (s : &[UInt8; 32]) (lo : UInt64) : UInt64 := do
  let mut e := s.len
  for i in 0...s.len do
    if e != s.len then break
    e := if i ≥ lo && s[i] == 32 then i else e
  e

mp def bTok (x y : UInt64) : UInt64 := do
  let mut a : Arr UInt8 32 := Vector.replicate 32 32
  for i in 0...20 do
    if ((x >>> i) &&& 3) != 0 then
      a[i] := ((y >>> (i * 3)) % 10).toUInt8 + 48
      ()
    else ()
  let mut pos := 0
  let mut sum := 0
  for k in 0...32 do
    if pos ≥ 20 then break
    let e := btEnd (&a[0..20]) pos
    let v := if pos ≤ e && e ≤ 20 then btParse (&a[pos..e]) else 0
    sum := sum * 3 + v
    pos := e + 1
  sum

def btBytes (x y : Nat) : List Nat :=
  (List.range 20).map fun i => if (x >>> i) % 4 = 0 then 32 else 48 + (y >>> (i * 3)) % 10

def parseR (l : List Nat) : Nat := l.foldl (fun acc b => W (acc * 10 + (b - 48))) 0

def refBTok (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := btBytes x y
  let step := fun (st : Nat × Nat) (_ : Nat) =>
    let (pos, sum) := st
    if pos < 20 then
      let e := ((List.range 20).find? fun i => pos ≤ i ∧ l[i]! = 32).getD 20
      (e + 1, W (sum * 3 + parseR ((l.drop pos).take (e - pos))))
    else st
  UInt64.ofNat ((List.range 32).foldl step (0, 0)).2

/-- `k` if `c`, else `0`. It is a call, so that the six tests below do not multiply out in the
normal form. -/
mp def flag (c : Bool) (k : UInt64) : UInt64 := if c then k else 0

mp def bOps (x y : UInt64) : UInt64 :=
  let a := x.toUInt8
  let b := y.toUInt8
  let c := a * b + (a ^^^ 0x5A) - (b ||| 3)
  let d := if b == 0 then c else c / b + c % b
  let e := (d &&& a) ||| (b &&& 0xF0)
  let f1 := flag (a < b) 1
  let f2 := flag (e ≥ 128) 2
  let f3 := flag (a == b) 4
  let f4 := flag (a != c && a ≤ c) 8
  let f5 := flag (200 > d) 16
  let f6 := flag (e > d) 32
  ((c.toUInt64 <<< 24) ||| (d.toUInt64 <<< 16) ||| (e.toUInt64 <<< 8)) + f1 + f2 + f3 + f4 + f5 +
    f6 + ((x >>> 8).toUInt8.toUInt64 <<< 32)

def refBOps (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := x % 256
  let b := y % 256
  let c := ((a * b + (a ^^^ 90)) % 256 + 256 - (b ||| 3)) % 256
  let d := if b = 0 then c else (c / b + c % b) % 256
  let e := (d &&& a) ||| (b &&& 240)
  let fs := (if a < b then 1 else 0) + (if e ≥ 128 then 2 else 0) + (if a = b then 4 else 0) +
    (if a ≠ c ∧ a ≤ c then 8 else 0) + (if 200 > d then 16 else 0) + (if e > d then 32 else 0)
  UInt64.ofNat (W ((c <<< 24 ||| d <<< 16 ||| e <<< 8) + fs + ((x >>> 8) % 256) * 2 ^ 32))

mp def bFill (x y : UInt64) : UInt64 := do
  let mut a : Arr UInt8 100 := Vector.replicate 100 7
  for i in 0...100 do
    if i == x % 100 then
      a[i] := y.toUInt8
      ()
    else ()
  a[90].toUInt64 * 65536 + a[99].toUInt64 * 256 + a[0].toUInt64

def refBFill (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := (List.replicate 100 7).set (x % 100) (y % 256)
  UInt64.ofNat (a[90]! * 65536 + a[99]! * 256 + a[0]!)

structure BigBuf where
  buf : Arr UInt8 64
  n : UInt64
deriving Data

mp def bCopy (x y : UInt64) : UInt64 := do
  let mut b : Arr UInt8 64 := Vector.replicate 64 3
  for i in 0...64 do
    if i == x % 64 then
      b[i] := y.toUInt8
      ()
    else ()
  let s : BigBuf := { buf := b, n := x }
  s.buf[63].toUInt64 * 256 + s.buf[60].toUInt64 + s.n

def refBCopy (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := (List.replicate 64 3).set (x % 64) (y % 256)
  UInt64.ofNat (W (a[63]! * 256 + a[60]! + x))

/-- The byte functions, all of which `compile` accepts. -/
def byteFuncs : List TestFn :=
  [tfm2 "bTok" bTok.exp (fun a => (bTok a[0]! a[1]!).run) refBTok,
   tfm2 "bOps" bOps.exp (fun a => (bOps a[0]! a[1]!).run) refBOps,
   tfm2 "bFill" bFill.exp (fun a => (bFill a[0]! a[1]!).run) refBFill,
   tfm2 "bCopy" bCopy.exp (fun a => (bCopy a[0]! a[1]!).run) refBCopy]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (0xFFFFF, 0x123456789ABCDEF),
    (0xFF, 0xFF), (0x1234, 0x56)].all fun (x, y) =>
  byteFuncs.all fun f => f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]
-- the references are not constant
#guard (refBTok [0xFFFFF, 0x123456789ABCDEF]) != (refBTok [0xFFFFC, 0x123456789ABCDEF])
#guard refBFill [90, 5] != refBFill [91, 5] && refBCopy [63, 5] != refBCopy [62, 5] &&
  refBFill [0, 5] != refBFill [1, 5]

#guard byteFuncs.all fun f => f.exp.memOk

end Millipede.Tests.Differential
