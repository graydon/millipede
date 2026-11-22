import Tests.Differential.SliceFuncs

/-!
# Differential tests of references to a pair of elements

A reference to two elements `a[i], a[j]` of one array is held as two addresses, and its fields
`r.fst` and `r.snd` are the elements themselves. Each function is an `mp def` over two words that
runs through the whole pipeline under qemu and is compared with a reference in plain Lean. A
callee swaps the pair it gets by `&mut`, twice and the second time with the indices reversed. A
callee updates both elements and returns a value, a callee reads a shared pair, a scoped `&mut`
pair borrow passes its fields on to another callee, and a shared pair borrow is read. Each
harness hashes the whole array afterwards, so a write that is lost or lands in the wrong element
changes the result. Two more functions pass several `&mut` arguments on one root, one of which is
written back through a `Slots` cell.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

mp def ppSwap (r : &mut (UInt64 × UInt64)) : Unit := do
  let t := r.fst
  r.fst := r.snd
  r.snd := t
  ()

mp def ppBump (r : &mut (UInt64 × UInt64)) (d : UInt64) : UInt64 := do
  r.fst := r.fst + d
  r.snd := r.snd * 3 + r.fst
  r.fst ^^^ r.snd

mp def ppSum (r : &(UInt64 × UInt64)) : UInt64 := r.fst * 5 + r.snd

mp def ppSwap2 (a : &mut UInt64) (b : &mut UInt64) : Unit := do
  let t := a
  a := b
  b := t
  ()

/-- One step on two words through `&mut`. -/
mp def psStep (a : &mut UInt64) (b : &mut UInt64) (d : UInt64) : Unit := do
  let t := a * 3 + d
  a := b ^^^ t
  b := t + 1
  ()

/-- The two results of `psStep`, returned exchanged: the words arrive in the registers of the
callee's two results and `ret` moves each into the other's register. -/
mp def psSwapCall (a : &mut UInt64) (b : &mut UInt64) (d : UInt64) : Unit := do
  let _ := psStep (&mut a) (&mut b) d
  let t := a
  a := b
  b := t
  ()

/-! ## Harness functions and references -/

/-- Two results swapped from a callee's two results, twice, the second time into the other
words. -/
mp def pSwapRes (x y : UInt64) : UInt64 := do
  let mut a := x
  let mut b := y
  let _ := psSwapCall (&mut a) (&mut b) 5
  let _ := psSwapCall (&mut b) (&mut a) 9
  a * 7 + b

def refPSwapRes (l : List UInt64) : UInt64 :=
  let step (a b d : UInt64) : UInt64 × UInt64 := let t := a * 3 + d; (b ^^^ t, t + 1)
  let sc (a b d : UInt64) : UInt64 × UInt64 := let (a', b') := step a b d; (b', a')
  let (a, b) := sc l[0]! l[1]! 5
  let (b, a) := sc b a 9
  a * 7 + b

/-- Swap `a[i]` and `a[j]` through a callee that takes the pair, and then `a[k]` and `a[j]`. -/
mp def pSwapArg (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := x % 8
  let j := (x + 1) % 8
  let k := (j + 1 + y % 6) % 8
  let _ := ppSwap (&mut (a[i], a[j]))
  let _ := ppSwap (&mut (a[k], a[j]))
  hash8 a

def swapR (l : List Nat) (i j : Nat) : List Nat :=
  (List.range l.length).map fun t => if t = i then l[j]! else if t = j then l[i]! else l[t]!

def refPSwapArg (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let i := x % 8
  let j := W (x + 1) % 8
  let k := (j + 1 + y % 6) % 8
  let l := swapR (arrR x y) i j
  let l := swapR l k j
  UInt64.ofNat (hashR 7 l)

/-- Update both elements through a callee and use its result. -/
mp def pBumpArg (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := y % 8
  let j := (y + 3) % 8
  let r := ppBump (&mut (a[i], a[j])) x
  hash8 a * 3 + r

def refPBumpArg (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let i := y % 8
  let j := W (y + 3) % 8
  let f := W (l[i]! + x)
  let s := W (W (l[j]! * 3) + f)
  let l := (List.range 8).map fun t => if t = i then f else if t = j then s else l[t]!
  UInt64.ofNat (W (W (hashR 7 l * 3) + (f ^^^ s)))

/-- A shared pair passed to a callee, and the array still read afterwards. -/
mp def pSumArg (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  let i := x % 8
  let j := (x + 5) % 8
  let s := ppSum (&(a[i], a[j]))
  s + hash8 a

def refPSumArg (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let i := x % 8
  let j := W (x + 5) % 8
  UInt64.ofNat (W (W (W (l[i]! * 5) + l[j]!) + hashR 7 l))

/-- A scoped `&mut` pair borrow whose fields go to a callee as two `&mut` arguments. -/
mp def pBorrowFields (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := (x + y) % 8
  let j := (x + y + 1) % 8
  let _ := (let r := &mut (a[i], a[j]); ppSwap2 (&mut r.fst) (&mut r.snd))
  a[i]! := a[i]! + 1
  hash8 a

def refPBorrowFields (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let i := W (x + y) % 8
  let j := W (W (x + y) + 1) % 8
  let l := swapR (arrR x y) i j
  let l := (List.range 8).map fun t => if t = i then W (l[t]! + 1) else l[t]!
  UInt64.ofNat (hashR 7 l)

/-- A scoped shared pair borrow read through its fields. -/
mp def pBorrowShr (x y : UInt64) : UInt64 :=
  let a := mkArr y x
  let i := y % 8
  let j := (y + 7) % 8
  let s := (let r := &(a[i], a[j]); r.fst * 9 + r.snd)
  s ^^^ hash8 a

def refPBorrowShr (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR y x
  let i := y % 8
  let j := W (y + 7) % 8
  UInt64.ofNat (W (W (l[i]! * 9) + l[j]!) ^^^ hashR 7 l)

/-! ## Several `&mut` arguments on one root, a later write-back through a `Slots` cell -/

structure DArena where
  count : UInt64
  cells : Slots UInt64 4
  tag : UInt64
deriving Data

mp def sBump (x : &mut UInt64) (c : &mut UInt64) (d : UInt64) : UInt64 := do
  c := c * 3 + 1
  x := x + d + c
  x ^^^ c

/-- An arena's counter and one of its cells passed together, with the counter written back first. -/
mp def sCellArgs (x y : UInt64) : UInt64 := do
  let mut a := { count := x, cells := (Slots.empty 4 : Slots UInt64 4), tag := y : DArena }
  let k := y % 4
  let _ := a.cells.put! k (x + y)
  let r := sBump (&mut a.cells[k]!) (&mut a.count) x
  let v := a.cells.take! k
  r + v * 7 + a.count * 3 + a.tag

def refSCellArgs (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let c1 := W (W (x * 3) + 1)
  let v1 := W (W (W (x + y) + x) + c1)
  UInt64.ofNat (W (W (W ((v1 ^^^ c1) + W (v1 * 7)) + W (c1 * 3)) + y))

structure DCell where
  v : UInt64
  n : UInt64
deriving Data

instance : Inhabited DCell := ⟨⟨0, 0⟩⟩

/-- Two fields of cells of one `Slots` passed together, first of two cells and then of one cell.
The first write-back goes through a full cell, which keeps every cell's occupancy. -/
mp def sTwoCells (x y : UInt64) : UInt64 := do
  let mut s := (Slots.empty 4 : Slots DCell 4)
  let i := x % 4
  let j := (i + 1 + y % 3) % 4
  let _ := s.put! i { v := x, n := y : DCell }
  let _ := s.put! j { v := y, n := x : DCell }
  let r1 := sBump (&mut s[j]!.n) (&mut s[i]!.v) y
  let r2 := sBump (&mut s[i]!.n) (&mut s[i]!.v) y
  let a := s.take! i
  let b := s.take! j
  r1 + r2 + a.v * 3 + a.n * 5 + b.v * 7 + b.n * 11

def refSTwoCells (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let c1 := W (W (x * 3) + 1)
  let x1 := W (W (x + y) + c1)
  let c2 := W (W (c1 * 3) + 1)
  let x2 := W (W (y + y) + c2)
  UInt64.ofNat (W (W (W (W (W (W (x1 ^^^ c1) + (x2 ^^^ c2)) + W (c2 * 3)) + W (x2 * 5)) +
    W (y * 7)) + W (x1 * 11)))


/-- The functions of this file, all of which `compile` accepts. -/
def pairFuncs : List TestFn :=
  [tfm2 "pSwapRes" pSwapRes.exp (fun a => (pSwapRes a[0]! a[1]!).run) refPSwapRes,
   tfm2 "pSwapArg" pSwapArg.exp (fun a => (pSwapArg a[0]! a[1]!).run) refPSwapArg,
   tfm2 "pBumpArg" pBumpArg.exp (fun a => (pBumpArg a[0]! a[1]!).run) refPBumpArg,
   tfm2 "pSumArg" pSumArg.exp (fun a => (pSumArg a[0]! a[1]!).run) refPSumArg,
   tfm2 "pBorrowFields" pBorrowFields.exp (fun a => (pBorrowFields a[0]! a[1]!).run)
     refPBorrowFields,
   tfm2 "pBorrowShr" pBorrowShr.exp (fun a => (pBorrowShr a[0]! a[1]!).run) refPBorrowShr,
   tfm2 "sCellArgs" sCellArgs.exp (fun a => (sCellArgs a[0]! a[1]!).run) refSCellArgs,
   tfm2 "sTwoCells" sTwoCells.exp (fun a => (sTwoCells a[0]! a[1]!).run) refSTwoCells]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (2 ^ 64 - 1, 2 ^ 64 - 1)].all
  fun (x, y) => pairFuncs.all fun f =>
    f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]

-- all of them are in the fragment the pipeline accepts
#guard pairFuncs.all fun f => f.exp.memOk

end Millipede.Tests.Differential
