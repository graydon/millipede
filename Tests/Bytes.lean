import Millipede.Meta.MpDef
import Millipede.Top.Sound

/-!
# Operations on bytes

A `UInt8` value is computed on through the conversions `x.toUInt64` and `x.toUInt8`, which
`mp def` inserts around the `U64` operations and which the source may also write itself. These
tests run a tokenizer over a byte slice, whose callers pass sub-slices of an owned byte array, and
byte arithmetic, bitwise operations, comparisons and conversions, whose normal forms read as the
byte operations. They check concrete runs, that the functions are in the fragment the pipeline
accepts, and that a reactor over bytes compiles. Shifts of bytes and conversions from other types
are refused with an error.

The tests then pass pairs of slice cells to a callee, as an insertion sort and a reversal do, and
use size expressions over a slice's length as loop bounds. Each group of runs includes a wrong
expectation that must fail.
-/

namespace Millipede.Tests.Bytes

open Millipede

/-- The number spelled by the decimal digits of a byte slice. -/
mp def parseNum (s : &[UInt8; 64]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc * 10 + (s[i].toUInt64 - 48)
  acc

/-- The index of the first space at or after `lo`, or the length if there is none. -/
mp def tokEnd (s : &[UInt8; 64]) (lo : UInt64) : UInt64 := do
  let mut e := s.len
  for i in 0...s.len do
    if e != s.len then break
    e := if i ≥ lo && 32 == s[i] then i else e
  e

/-- The sum of the space-separated numbers of `a[0..len]`, read through sub-slices of the owned
array. -/
mp def sumToks (a : Arr UInt8 64) (len : UInt64) requires len.toNat ≤ 64 : UInt64 := do
  let mut pos := 0
  let mut sum := 0
  for k in 0...64 do
    if pos ≥ len then break
    let e := tokEnd (&a[0..len]) pos
    let v := if pos ≤ e && e ≤ len then parseNum (&a[pos..e]) else 0
    sum := sum + v
    pos := e + 1
  sum

/-- Byte arithmetic and bitwise operations, which wrap modulo 2^8, comparisons and conversions. -/
mp def bops (a : UInt8) (b : UInt8) : UInt8 :=
  let c := a + b * 3 - 1
  let d := c / b % 7
  let e := (d ^^^ a) &&& (b ||| 1)
  if 200 < e && a != b && e ≤ 250 then e else (e.toUInt64 + 300).toUInt8

mp def bcmp (a : UInt8) (b : UInt8) : UInt64 :=
  let x := if a < b then 1 else 0
  let y := if a ≥ b then 2 else 0
  let z := if a == 255 then 4 else 0
  let w := if b > 127 then 8 else 0
  x + y + z + w + (a - b).toUInt64 * 16

/-- The bytes of a string, padded with spaces to 64. -/
def bytesOf (s : String) : Arr UInt8 64 :=
  Vector.ofFn fun i => (s.toUTF8.toList ++ List.replicate 64 32)[i.val]!

-- concrete runs
#guard (sumToks (bytesOf "12 345 6") 8).run.1 == 363
#guard (sumToks (bytesOf "7") 1).run.1 == 7
#guard (sumToks (bytesOf "") 0).run.1 == 0
#guard (sumToks (bytesOf "1 2 3 4 5 6 7 8 9 10") 20).run.1 == 55
#guard (bops 7 9).run == 44
#guard (bops 250 3).run == (((250 + 3 * 3 - 1 : UInt8) / 3 % 7 ^^^ 250) &&& (3 ||| 1)) + 44
#guard (bops 0 0).run == 44
#guard [(0, 0), (1, 2), (200, 100), (255, 255), (128, 7)].all fun (a, b) =>
  (bcmp (UInt8.ofNat a) (UInt8.ofNat b)).run ==
    UInt64.ofNat ((if a < b then 1 else 0) + (if a ≥ b then 2 else 0) + (if a = 255 then 4 else 0)
      + (if b > 127 then 8 else 0) + ((a + 256 - b) % 256) * 16)
-- a wrong expectation fails
#guard (sumToks (bytesOf "12 345 6") 8).run.1 != 362
#guard (bops 7 9).run != 45

-- the normal forms are the byte operations
example (a b : UInt8) : (bops a b).run =
    let e := ((a + b * 3 - 1) / b % 7 ^^^ a) &&& (b ||| 1)
    if (200 < e ∧ ¬a = b) ∧ e ≤ 250 then e else e + UInt64.toUInt8 300 := rfl
example (a b : UInt8) : Prim.denote .zext8 (.cons a .nil) = a.toUInt64 ∧
    Prim.denote .trunc8 (.cons (a.toUInt64 + b.toUInt64) .nil) = a + b := by
  simp [Prim.denote]

-- the pipeline accepts them
example : parseNum.exp.memOk = true := by decide
example : tokEnd.exp.memOk = true := by decide
example : sumToks.exp.memOk = true := by decide
example : bops.exp.memOk = true := by decide
example : bcmp.exp.memOk = true := by decide

structure T where
  buf : Arr UInt8 64
  len : UInt64
  out : UInt64
deriving Data, Inhabited

mp def tInit : T := { buf := Vector.replicate 64 49, len := 10, out := 0 }
mp def tStep (t : &mut T) : Unit := do
  let l := t.len % 65
  let v := sumToks t.buf l
  let w := bops 3 5
  t.out := v + w.toUInt64
  ()
mp program tProg (root : T) init tInit step tStep
#guard (compile tProg x64Linux).toBool

/-! ## Refusals -/

/-- error: shifts of UInt8 are not in the language (a UInt8 shift takes its amount mod 8): widen with `.toUInt64`, shift, and narrow with `.toUInt8` -/
#guard_msgs in
mp def shift8 (a : UInt8) : UInt8 := a <<< 1

/-- error: `.toUInt64` converts between UInt8 and UInt64, not from Bool -/
#guard_msgs in
mp def convBool (b : Bool) : UInt64 := b.toUInt64

/-- error: `+` needs UInt64 or UInt8 operands, but this has type Bool -/
#guard_msgs in
mp def addBool (b : Bool) : UInt64 := b + 1

/-! ## Pairs of slice cells and size expressions -/

mp def swapP (r : &mut (UInt64 × UInt64)) : Unit := do
  let t := r.fst
  r.fst := r.snd
  r.snd := t
  ()

/-- The pair of two cells of a slice, passed to a callee. -/
mp def pairSlice (s : &mut [UInt64; 8]) : Unit :=
  if 1 < s.len then swapP (&mut (s[0]!, s[1]!)) else ()

/-- Insertion sort over a slice, swapping through the pair of two of its cells. -/
mp def isort (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    let mut j := i
    for k in 0...8 do
      if j ≤ 0 then break
      if j < s.len && s[j - 1]! > s[j]! then
        let _ := swapP (&mut (s[j - 1]!, s[j]!))
        j := j - 1
      else j := 0

/-- Reversal with the loop bound `s.len / 2`, a size expression whose static bound is `4` and
whose run-time condition is `i < s.len / 2`. -/
mp def rev (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len / 2 do
    swapP (&mut (s[i]!, s[s.len - 1 - i]!))

/-- A size parameter as a loop bound. -/
def half : Nat := 4
mp def sumHalf (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...half do
    acc := acc + a[i]
  acc

/-- Size expressions over `s.len` mean what they mean over `Nat`, and a `Nat` constant is its value.
In particular `-` truncates at 0 without wrapping around, so the run-time condition here is
`i < if 1 ≤ s.len then s.len - 1 else 0`. -/
mp def cntM1 (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len - 1 do
    acc := acc + 1
  acc
mp def cntMix (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len + half do
    acc := acc + 1
  acc
mp def cntSub (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...half - s.len do
    acc := acc + 1
  acc
mp def cntStat (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...3 - 5 do
    acc := acc + a[i]
  acc
mp def cnts (n : UInt64) requires n.toNat ≤ 8 : UInt64 :=
  let a : Arr UInt64 8 := Vector.replicate 8 0
  cntM1 (&a[0..n]) * 10000 + cntMix (&a[0..n]) * 100 + cntSub (&a[0..n])

/-- The sum of the space-separated numbers of a byte slice, read through sub-slices of the slice.
A sub-slice is the view's address plus `pos`, and nothing is copied. -/
mp def sumToksS (s : &[UInt8; 64]) : UInt64 := do
  let mut pos := 0
  let mut sum := 0
  for k in 0...64 do
    if pos ≥ s.len then break
    let e := tokEnd (&s) pos
    let v := if pos ≤ e && e ≤ s.len then parseNum (&s[pos..e]) else 0
    sum := sum + v
    pos := e + 1
  sum

mp def sumToks2 (a : Arr UInt8 64) (len : UInt64) requires len.toNat ≤ 64 : UInt64 :=
  sumToksS (&a[0..len])

mp def sortRun (x : UInt64) (n : UInt64) requires n.toNat ≤ 8 : UInt64 := do
  let mut a : Arr UInt64 8 := Vector.replicate 8 0
  for i in 0...8 do
    a[i] := (x >>> (i * 8)) % 16
  let _ := isort (&mut a[0..n])
  let _ := rev (&mut a[0..n])
  let mut h := 0
  for i in 0...8 do
    h := h * 16 + a[i]
  h

#guard (sumToks2 (bytesOf "12 345 6") 8).run.1 == 363
#guard (sumToks2 (bytesOf "1 2 3 4 5 6 7 8 9 10") 20).run.1 == 55
-- sorted descending after `rev` of the sorted prefix
#guard (sortRun 0x0105030702040608 8).run.1 == 0x87654321
#guard (sortRun 0x0105030702040608 3).run.1 == 0x86427351
#guard (sumHalf (Vector.ofFn fun i => UInt64.ofNat i.val)).run == 6
-- the empty slice: `s.len - 1` is 0, `s.len + half` is 4, `half - s.len` is 4
#guard (cnts 0).run.1 == 0 * 10000 + 4 * 100 + 4
#guard (cnts 3).run.1 == 2 * 10000 + 7 * 100 + 1
#guard (cnts 6).run.1 == 5 * 10000 + 10 * 100 + 0
#guard (cntStat (Vector.replicate 8 1)).run == 0
-- a wrong expectation fails
#guard (sortRun 0x0105030702040608 8).run.1 != 0x12345678

example : pairSlice.exp.memOk = true := by decide
example : isort.exp.memOk = true := by decide
example : rev.exp.memOk = true := by decide
example : sumToksS.exp.memOk = true := by decide
example : sumToks2.exp.memOk = true := by decide
example : sortRun.exp.memOk = true := by decide
example : cnts.exp.memOk = true := by decide

end Millipede.Tests.Bytes
