import Tests.Differential.ByteFuncs

/-!
# Differential tests of sub-slices, pairs of slice cells and size-expression bounds

Each function is an `mp def` over two words that runs through the whole pipeline under qemu and is
compared with a reference in plain Lean over `Nat` and `List`. `svTok` is a tokenizer over a byte
slice that takes sub-slices `&s[pos..e]` of the slice and passes them to a parser. A sub-slice is
the view's address plus `pos` with a new length, and nothing is copied. `svSort` is an insertion
sort over a `&mut` slice whose swaps go through the pair `&mut (s[j-1]!, s[j]!)` of two of its
cells. `svRev` reverses a `&mut` slice with the loop bound `s.len / 2`, writes through the
sub-slice borrow `&mut s[1..s.len]`, and counts the iterations of a loop bounded by `s.len - 1`,
which truncates at 0 like `Nat`.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

/-- The space-separated numbers of a byte slice, through sub-slices of the slice. -/
mp def svSum (s : &[UInt8; 32]) : UInt64 := do
  let mut pos := 0
  let mut sum := 0
  for k in 0...32 do
    if pos ≥ s.len then break
    let e := btEnd (&s) pos
    let v := if pos ≤ e && e ≤ s.len then btParse (&s[pos..e]) else 0
    sum := sum * 3 + v
    pos := e + 1
  sum

mp def svTok (x y : UInt64) : UInt64 := do
  let mut a : Arr UInt8 32 := Vector.replicate 32 32
  for i in 0...20 do
    if ((x >>> i) &&& 3) != 0 then
      a[i] := ((y >>> (i * 3)) % 10).toUInt8 + 48
      ()
    else ()
  svSum (&a[0..20])

def refSvTok (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := btBytes x y
  let step := fun (st : Nat × Nat) (_ : Nat) =>
    let (pos, sum) := st
    if pos < 20 then
      let e := ((List.range 20).find? fun i => pos ≤ i ∧ l[i]! = 32).getD 20
      (e + 1, W (sum * 3 + parseR ((l.drop pos).take (e - pos))))
    else st
  UInt64.ofNat ((List.range 32).foldl step (0, 0)).2

mp def svSwap (r : &mut (UInt64 × UInt64)) : Unit := do
  let t := r.fst
  r.fst := r.snd
  r.snd := t
  ()

/-- Insertion sort, swapping through the pair of two cells of the slice. -/
mp def svIsort (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    let mut j := i
    for k in 0...8 do
      if j ≤ 0 then break
      if j < s.len && s[j - 1]! > s[j]! then
        let _ := svSwap (&mut (s[j - 1]!, s[j]!))
        j := j - 1
      else j := 0

/-- A hash of the 8 elements in order. -/
mp def svHash (a : Arr UInt64 8) : UInt64 := do
  let mut h := 0
  for i in 0...8 do
    h := h * 31 + a[i]
  h

mp def svSort (x y : UInt64) : UInt64 := do
  let mut a : Arr UInt64 8 := Vector.replicate 8 0
  for i in 0...8 do
    a[i] := (x >>> (i * 8)) % 16
  let n := y % 9
  let _ := svIsort (&mut a[0..n])
  svHash a

def svElems (x : Nat) : List Nat := (List.range 8).map fun i => (x >>> (i * 8)) % 16


def svHashR (l : List Nat) : Nat := l.foldl (fun h v => W (h * 31 + v)) 0

def refSvSort (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := svElems x
  let n := y % 9
  UInt64.ofNat (svHashR (((l.take n).mergeSort (· ≤ ·)) ++ l.drop n))

/-- Add `100` to every element of a slice. -/
mp def svInc (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    s[i]! := s[i]! + 100

/-- Reversal with the loop bound `s.len / 2`, swapping through pairs of cells. -/
mp def svReverse (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len / 2 do
    svSwap (&mut (s[i]!, s[s.len - 1 - i]!))

/-- The tail `s[1..]` incremented in place, through a sub-slice borrow passed on whole. -/
mp def svTail (s : &mut [UInt64; 8]) : Unit :=
  if 2 ≤ s.len then (let t := &mut s[1..s.len]; svInc (&mut t)) else ()

/-- Double the first element of a slice. -/
mp def svDbl (s : &mut [UInt64; 8]) requires 1 ≤ s.len.toNat : Unit := do
  s[0]! := s[0]! * 2
  ()

/-- Element `1` doubled, through a sub-slice argument. -/
mp def svSecond (s : &mut [UInt64; 8]) : Unit :=
  if 2 ≤ s.len then svDbl (&mut s[1..2]) else ()

/-- The number of iterations of `for i in 0...s.len - 1`, where `s.len - 1` truncates at 0. -/
mp def svCntM1 (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len - 1 do
    acc := acc + 1
  acc

mp def svRev (x y : UInt64) : UInt64 := do
  let mut a : Arr UInt64 8 := Vector.replicate 8 0
  for i in 0...8 do
    a[i] := (x >>> (i * 8)) % 16
  let n := y % 9
  let _ := svReverse (&mut a[0..n])
  let _ := svTail (&mut a[0..n])
  let _ := svSecond (&mut a[0..n])
  svHash a * 16 + svCntM1 (&a[0..n])

def refSvRev (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := svElems x
  let n := y % 9
  let r := (l.take n).reverse
  let r := if 2 ≤ n then r.take 1 ++ ((r.drop 1).map (· + 100)).modifyHead (· * 2) else r
  UInt64.ofNat (svHashR (r ++ l.drop n) * 16 + (n - 1))


/-- The sub-view functions, all of which `compile` accepts. -/
def subViewFuncs : List TestFn :=
  [tfm2 "svTok" svTok.exp (fun a => (svTok a[0]! a[1]!).run) refSvTok,
   tfm2 "svSort" svSort.exp (fun a => (svSort a[0]! a[1]!).run) refSvSort,
   tfm2 "svRev" svRev.exp (fun a => (svRev a[0]! a[1]!).run) refSvRev]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (0xFFFFF, 0x123456789ABCDEF),
    (0xFF, 0xFF), (0x1234, 0x56), (0x0F0E0D0C0B0A0908, 8), (0x08090A0B0C0D0E0F, 8), (0x0F00030E0201050D, 7), (0x0102030405060708, 17)].all fun (x, y) =>
  subViewFuncs.all fun f => f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]
-- the references are not constant
#guard refSvSort [0x08090A0B0C0D0E0F, 8] != refSvSort [0x08090A0B0C0D0E0F, 0]
#guard refSvRev [0x0102030405060708, 8] != refSvRev [0x0102030405060708, 7]

#guard subViewFuncs.all fun f => f.exp.memOk

end Millipede.Tests.Differential
