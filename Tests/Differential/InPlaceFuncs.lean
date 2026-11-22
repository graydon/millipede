import Tests.Differential.PairFuncs
import Millipede.Lib.Slice

/-!
# Differential tests of in-place loops

Each function is an `mp def` over two words. It runs through the whole pipeline under qemu and is
compared with a reference in plain Lean over `Nat` and `List`. Each harness hashes the lender
after the call, so a write that went to a copy changes the result.

The tests call the slice library of `Millipede/Lib/Slice.lean` on windows with run-time bounds,
including empty and one-cell windows. They run loops that write in place through slices and
`&mut` struct parameters: a bubble pass, updates of the fields of a struct, a find-and-replace
with an early exit and a nested loop that rotates a window. A callee borrows windows of a
struct's array, and a library copy goes between two arrays of one struct. A bubble pass and a
reversal swap elements through a pair borrow, and a callee in a loop receives `&mut
pool.slots[k]!` together with another field. `iRoot` is a program of its own whose step runs a
loop over the root's fields, and one ELF checks many steps.
-/

namespace Millipede.Tests.Differential

open Millipede Millipede.Lib

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

structure IBuf where
  total : UInt64
  data : Arr UInt64 8
  cnt : UInt64
deriving Data, Inhabited

structure ITwo where
  a : Arr UInt64 8
  b : Arr UInt64 8
  n : UInt64
deriving Data, Inhabited

structure IPool where
  used : UInt64
  slots : Slots UInt64 4
  hits : UInt64
deriving Data

/-! ## Reference helpers -/

/-- Replace cell `i` of a list. -/
def setR (l : List Nat) (i v : Nat) : List Nat := patchR l i 1 fun _ => v

/-- Apply `f` to the window of length `len` at `lo` of a list. The window is replaced by the first
component of the result. -/
def segR {α : Type} (l : List Nat) (lo len : Nat) (f : List Nat → List Nat × α) : List Nat × α :=
  let (s, r) := f (sliceR l lo len)
  (patchR l lo len fun k => s[k]!, r)

/-- One bubble pass, which compares and swaps neighbours from left to right, and the number of
swaps. -/
def passR (l : List Nat) : List Nat × Nat :=
  (List.range (l.length - 1)).foldl (fun (st : List Nat × Nat) i =>
    if st.1[i + 1]! < st.1[i]! then (swapR st.1 i (i + 1), st.2 + 1) else st) (l, 0)

/-! ## The library on windows with run-time bounds -/

mp def iLibFill (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 6
  let len := y % 3 + 1
  let _ := Slice.fill (&mut a[lo..lo + len]) (x * 3 + y)
  let _ := Slice.fill (&mut a[0..y % 2]) 7
  hash8 a

def refILibFill (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := patchR (arrR x y) (x % 6) (y % 3 + 1) fun _ => W (x * 3 + y)
  UInt64.ofNat (hashR 7 (patchR l 0 (y % 2) fun _ => 7))

mp def iLibRev (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := y % 5
  let len := x % 4 + 1
  let _ := Slice.reverse (&mut a[lo..lo + len])
  let _ := Slice.reverse (&mut a[0..x % 9])
  hash8 a

def refILibRev (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 (revSub (revSub (arrR x y) (y % 5) (x % 4 + 1)) 0 (x % 9)))

mp def iLibCopy (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let b := mkArr y (x + 1)
  let lo := x % 4
  let n1 := y % 5 + 1
  let _ := Slice.copy (&mut a[lo..lo + n1]) (&b[y % 3..y % 3 + x % 6])
  hash8 a

def refILibCopy (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lb := arrR y (W (x + 1))
  let n := min (y % 5 + 1) (x % 6)
  UInt64.ofNat (hashR 7 (patchR (arrR x y) (x % 4) n fun k => lb[y % 3 + k]!))

/-! ## In-place loops through slices and `&mut` structs -/

/-- A bubble pass over a slice, with the swap count carried next to it. -/
mp def ibPass (s : &mut [UInt64; 8]) : UInt64 := do
  let mut n := 0
  for i in 0...s.len do
    if i + 1 ≥ s.len then break
    let a := s[i]
    let b := s[i + 1]!
    if b < a then
      s[i] := b
      s[i + 1]! := a
      n := n + 1
    else n := n
  n

mp def iBubble (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 3
  let len := y % 5 + 2
  let n1 := ibPass (&mut a[lo..lo + len])
  let n2 := ibPass (&mut a[lo..lo + len])
  let n3 := ibPass (&mut a[0..8])
  hash8 a * 17 + n1 * 5 + n2 * 3 + n3

def refIBubble (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (l, n1) := segR (arrR x y) (x % 3) (y % 5 + 2) passR
  let (l, n2) := segR l (x % 3) (y % 5 + 2) passR
  let (l, n3) := passR l
  UInt64.ofNat (W (hashR 7 l * 17 + n1 * 5 + n2 * 3 + n3))

/-- A loop updating two scalar fields and an array field of a `&mut` struct. -/
mp def ibAcc (b : &mut IBuf) (k : UInt64) : UInt64 := do
  let mut c := 0
  for i in 0...8 do
    if i ≥ k then break
    b.total := b.total + b.data[i]
    b.data[i] := b.data[i] * 2 + b.total
    b.cnt := b.cnt + 1
    c := c + 1
  c

mp def iStruct (x y : UInt64) : UInt64 := do
  let mut b := { total := x, data := mkArr x y, cnt := y : IBuf }
  let c := ibAcc (&mut b) (y % 10)
  let d := ibAcc (&mut b) (x % 4)
  b.total * 7 + hash8 b.data * 3 + c + d + b.cnt

/-- `ibAcc` on a model state `(total, data, cnt)`. -/
def accR (st : Nat × List Nat × Nat) (k : Nat) : (Nat × List Nat × Nat) × Nat :=
  let m := min 8 k
  (((List.range m).foldl (fun (s : Nat × List Nat × Nat) i =>
    let t := W (s.1 + s.2.1[i]!)
    (t, setR s.2.1 i (W (s.2.1[i]! * 2 + t)), s.2.2 + 1)) st), m)

def refIStruct (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (s, c) := accR (x, arrR x y, y) (y % 10)
  let (s, d) := accR s (x % 4)
  UInt64.ofNat (W (s.1 * 7 + hashR 7 s.2.1 * 3 + c + d + s.2.2))

/-- Find the first cell equal to `key`, replace it and count the replacement, leaving the loop
early. -/
mp def ifFind (b : &mut IBuf) (key rep : UInt64) : UInt64 := do
  let mut found := 0
  for i in 0...8 do
    if found != 0 then break
    if b.data[i] == key then
      b.data[i] := rep
      b.cnt := b.cnt + 1
      found := i + 1
    else found := 0
  found

mp def iFindRep (x y : UInt64) : UInt64 := do
  let mut b := { total := 0, data := mkArr x y, cnt := 0 : IBuf }
  let v := if y % 2 == 0 then x else y * 3 + 1
  let r1 := ifFind (&mut b) v (x + y)
  let r2 := ifFind (&mut b) v (x ^^^ y)
  let r3 := ifFind (&mut b) (x + y) 5
  hash8 b.data * 13 + r1 * 7 + r2 * 3 + r3 + b.cnt * 11

def findRepR (st : List Nat × Nat) (key rep : Nat) : (List Nat × Nat) × Nat :=
  match (List.range 8).find? fun i => st.1[i]! == key with
  | some i => ((setR st.1 i rep, st.2 + 1), i + 1)
  | none => (st, 0)

def refIFindRep (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let v := if y % 2 = 0 then x else W (y * 3 + 1)
  let (s, r1) := findRepR (arrR x y, 0) v (W (x + y))
  let (s, r2) := findRepR s v (x ^^^ y)
  let (s, r3) := findRepR s (W (x + y)) 5
  UInt64.ofNat (W (hashR 7 s.1 * 13 + r1 * 7 + r2 * 3 + r3 + s.2 * 11))

set_option mp.autoSafe true in
/-- Rotate a slice left `k` times, by an inner loop inside the outer one that both write the slice.
`s[0]!` reads a full cell only on a nonempty slice, hence the `requires`. -/
mp def irRot (s : &mut [UInt64; 8]) (k : UInt64) requires 1 ≤ s.len.toNat : UInt64 := do
  let mut c := 0
  for r in 0...8 do
    if r ≥ k then break
    let first := s[0]!
    for j in 0...s.len do
      if j + 1 ≥ s.len then break
      s[j] := s[j + 1]!
    s[s.len - 1]! := first
    c := c + first
  c

/-- `mp def` discharges the obligations of the nested in-place loop, because the outer invariant
that the cells are full survives the inner loop. -/
example : ∀ ω w s (len k : UInt64), 1 ≤ len.toNat ∧ len.toNat ≤ 8 ∧
    (∀ i, i < len.toNat → Slots.isFull s i = true) →
    Exp.safe ω irRot.exp (.cons k (.cons len (.cons s .nil))) w := irRot.safe

mp def iRot (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 4
  let len := y % 5 + 1
  let c := irRot (&mut a[lo..lo + len]) (x % 11)
  hash8 a * 3 + c

def rotR (s : List Nat) (k : Nat) : List Nat × Nat :=
  (List.range (min 8 k)).foldl (fun (st : List Nat × Nat) _ =>
    (st.1.drop 1 ++ st.1.take 1, W (st.2 + st.1[0]!))) (s, 0)

def refIRot (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (l, c) := segR (arrR x y) (x % 4) (y % 5 + 1) fun s => rotR s (x % 11)
  UInt64.ofNat (W (hashR 7 l * 3 + c))

/-! ## Sub-slices inside callees, two arrays of one struct -/

/-- The callee borrows windows of the struct's array and hands them to the library. -/
mp def isCallee (b : &mut IBuf) (k : UInt64) : UInt64 := do
  let m := k % 5
  let _ := Slice.reverse (&mut b.data[m..m + 3])
  let _ := Slice.fill (&mut b.data[0..m]) (b.total + 1)
  b.cnt := b.cnt + 1
  slSum (&b.data[1..m + 4])

mp def iSubSlice (x y : UInt64) : UInt64 := do
  let mut b := { total := x, data := mkArr x y, cnt := 0 : IBuf }
  let r1 := isCallee (&mut b) y
  let r2 := isCallee (&mut b) x
  r1 * 5 + r2 * 3 + hash8 b.data + b.cnt

def subR (l : List Nat) (total k : Nat) : List Nat × Nat :=
  let m := k % 5
  let l := patchR (revSub l m 3) 0 m fun _ => W (total + 1)
  (l, sumR (sliceR l 1 (m + 3)))

def refISubSlice (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (l, r1) := subR (arrR x y) x y
  let (l, r2) := subR l x x
  UInt64.ofNat (W (r1 * 5 + r2 * 3 + hashR 7 l + 2))

/-- A library copy from one array of the struct into another, then a loop over both. -/
mp def itMerge (t : &mut ITwo) (k : UInt64) : UInt64 := do
  let lo := k % 4
  let _ := Slice.copy (&mut t.a[lo..lo + 4]) (&t.b[1..1 + k % 6])
  let mut acc := 0
  for i in 0...8 do
    if i ≥ t.n then break
    t.a[i] := t.a[i] + t.b[i]
    acc := acc + t.a[i]
  acc

mp def iTwo (x y : UInt64) : UInt64 := do
  let mut t := { a := mkArr x y, b := mkArr y (x + 1), n := y % 9 : ITwo }
  let r := itMerge (&mut t) x
  hash8 t.a * 3 + hash8 t.b + r + t.n

def refITwo (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lb := arrR y (W (x + 1))
  let la := patchR (arrR x y) (x % 4) (min 4 (x % 6)) fun j => lb[1 + j]!
  let (la, r) := (List.range (min 8 (y % 9))).foldl (fun (st : List Nat × Nat) i =>
    let v := W (st.1[i]! + lb[i]!)
    (setR st.1 i v, W (st.2 + v))) (la, 0)
  UInt64.ofNat (W (hashR 7 la * 3 + hashR 7 lb + r + y % 9))

/-! ## Swaps through a pair borrow inside loops -/

mp def ppOrder (r : &mut (UInt64 × UInt64)) : UInt64 := do
  if r.snd < r.fst then
    let t := r.fst
    r.fst := r.snd
    r.snd := t
    1
  else 0

/-- A bubble pass whose compare-and-swap takes the pair `(a[i], a[i+1])` by `&mut`. -/
mp def ipPass (a : &mut Arr UInt64 8) : UInt64 := do
  let mut n := 0
  for i in 0...7 do
    n := n + ppOrder (&mut (a[i], a[i + 1]))
  n

mp def iPairPass (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let n1 := ipPass (&mut a)
  let n2 := ipPass (&mut a)
  hash8 a * 5 + n1 * 3 + n2

def refIPairPass (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (l, n1) := passR (arrR x y)
  let (l, n2) := passR l
  UInt64.ofNat (W (hashR 7 l * 5 + n1 * 3 + n2))

/-- Swap `a[i]` with `a[7 - i]` for each `i` below `min 4 (x % 5)`, through a pair borrow in the
caller's loop. -/
mp def iPairRev (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  for i in 0...4 do
    if i ≥ x % 5 then break
    let _ := ppSwap (&mut (a[i], a[7 - i]))
  hash8 a

def refIPairRev (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 ((List.range (min 4 (x % 5))).foldl (fun l i => swapR l i (7 - i)) (arrR x y)))

/-! ## A loop in a callee receiving `&mut pool.slots[k]!` and another field -/

mp def ipTouch (c : &mut UInt64) (h : &mut UInt64) (d : UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...3 do
    c := c + d + i
    h := h + c
    acc := acc + c
  acc

mp def iSlotLoop (x y : UInt64) : UInt64 := do
  let mut p := { used := x, slots := (Slots.empty 4 : Slots UInt64 4), hits := y : IPool }
  let k := y % 4
  let _ := p.slots.put! k (x + y)
  let r := ipTouch (&mut p.slots[k]!) (&mut p.hits) x
  let v := p.slots.take! k
  r + v * 7 + p.hits * 3 + p.used

def refISlotLoop (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (c, h, r) := (List.range 3).foldl (fun (st : Nat × Nat × Nat) i =>
    let c := W (st.1 + x + i)
    (c, W (st.2.1 + c), W (st.2.2 + c))) (W (x + y), y, 0)
  UInt64.ofNat (W (r + c * 7 + h * 3 + x))

/-! ## Loops updating root fields across reactor steps -/

structure IRoot where
  n : UInt64
  data : Arr UInt64 8
  total : UInt64
deriving Data, Inhabited

mp def irInit : IRoot := { n := 0, data := Vector.replicate 8 0, total := 0 : IRoot }

-- the program's safety proof cites the step's
set_option mp.autoSafe true in
/-- One step reads a case, which is a word `x` and the expected checksum `e`, and exits at the end of
the input. It runs a loop that updates the root's array and its `total`, and writes `.` when the
checksum equals `e` and `X` otherwise. -/
mp def irStep (r : &mut IRoot) : Unit := do
  let b0 := Examples.sysRead 0
  if b0 < 256 then
    let x := readWord b0
    let e := readWord (Examples.sysRead 0)
    for i in 0...8 do
      if i ≥ x % 9 then break
      r.data[i] := r.data[i] + x + r.total
      r.total := r.total + r.data[i]
    r.n := r.n + 1
    let c := r.total * 3 + r.data[x % 8]! + r.n
    if c == e then
      let _w := Examples.sysWrite 1 "."
      ()
    else
      let _w := Examples.sysWrite 1 "X"
      ()
  else
    let _x := Examples.sysExit 0
    ()

mp program irProg (root : IRoot) init irInit step irStep

/-- The checksums after each step, with the root threaded through as a plain value. -/
def refIRoot (xs : List UInt64) : List UInt64 :=
  let step (st : Nat × List Nat × Nat) (x : UInt64) : (Nat × List Nat × Nat) × UInt64 :=
    let (n, d, t) := st
    let (d, t) := (List.range (min 8 (x.toNat % 9))).foldl (fun (s : List Nat × Nat) i =>
      let v := W (s.1[i]! + x.toNat + s.2)
      (setR s.1 i v, W (s.2 + v))) (d, t)
    let n := W (n + 1)
    ((n, d, t), UInt64.ofNat (W (t * 3 + d[x.toNat % 8]! + n)))
  let rec go (st : Nat × List Nat × Nat) : List UInt64 → List UInt64
    | [] => []
    | x :: rest => let (st', e) := step st x; e :: go st' rest
  go (0, List.replicate 8 0, 0) xs

def rootInput (xs : List UInt64) : List UInt8 :=
  (xs.zip (refIRoot xs)).flatMap fun (x, e) =>
    [x, e].flatMap fun w => (List.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8

/-- The stateful test, one ELF that runs `bigCases.length` steps. -/
def iRoot : TestFn :=
  { name := "iRoot", arity := 0, exp := .atom (.lit (t := Ty.u64) 0), fn := fun _ => 0,
    ref := fun _ => 0, custom := some (irProg, rootInput bigCases, bigCases.length) }

/-! ## Programs that `compile` refuses

`mp def` accepts each of the following and gives it a meaning, which the reference states, but
`compile` refuses it with an error. They copy a pair reference whole or pass it on whole, pass a
`&mut` argument through a `Slots` cell behind an array element after another argument on the
same root, and re-borrow a view or read it whole. A callee that receives a view whole by `&mut`
and writes it through a `&mut s[k]!` argument, as `iViewCellArg` does, is accepted.

doc/open-claims.md lists these refusals. -/

mp def rPairCopy (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := x % 8
  let j := (x + 1) % 8
  let s := (do let r := &mut (a[i], a[j]); let c := r; c.fst * 3 + c.snd)
  s + hash8 a

def refRPairCopy (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  UInt64.ofNat (W (W (l[x % 8]! * 3 + l[W (x + 1) % 8]!) + hashR 7 l))

mp def rpInner (r : &mut (UInt64 × UInt64)) : Unit := do
  r.fst := r.fst + 1
  ()

mp def rpOuter (r : &mut (UInt64 × UInt64)) : Unit :=
  rpInner (&mut r)

mp def rPairPass (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := x % 8
  let j := (x + 1) % 8
  let _ := rpOuter (&mut (a[i], a[j]))
  hash8 a

def refRPairPass (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 (setR (arrR x y) (x % 8) (W ((arrR x y)[x % 8]! + 1))))

structure DOuter where
  xs : Vector DArena 2
deriving Data

instance : Inhabited DArena := ⟨⟨0, Slots.empty 4, 0⟩⟩

mp def rDeepSlots (x y : UInt64) : UInt64 := do
  let i := x % 2
  let k := y % 4
  let mut c := (Slots.empty 4 : Slots UInt64 4)
  let _ := c.put! k (x + y)
  let mut o := { xs := Vector.replicate 2 { count := x, cells := c, tag := y : DArena } : DOuter }
  let _ := sBump (&mut o.xs[i]!.cells[k]!) (&mut o.xs[i]!.count) x
  o.xs[i]!.count + o.xs[i]!.tag

def refRDeepSlots (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (W (W (x * 3 + 1) + y))

mp def rvBorrow (s : &mut [UInt64; 8]) : Unit := do
  let _ := (do let r := &mut s; r[0]! := 5; ())
  ()

mp def rViewReborrow (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let _ := rvBorrow (&mut a[0..1 + y % 7])
  hash8 a

def refRViewReborrow (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 (setR (arrR x y) 0 5))

mp def rvCopy (s : &[UInt64; 8]) : UInt64 :=
  let t := s
  t[0]! + 1

mp def rViewCopy (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  rvCopy (&a[0..1 + y % 7])

def refRViewCopy (a : List UInt64) : UInt64 :=
  let (x, _) := toNat2 a
  UInt64.ofNat (W (x + 1))

mp def rvCell (s : &mut [UInt64; 8]) : Unit :=
  inc (&mut s[0]!) 3

mp def rvCellOuter (s : &mut [UInt64; 8]) : Unit :=
  rvCell (&mut s)

mp def iViewCellArg (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let _ := rvCellOuter (&mut a[0..1 + y % 7])
  hash8 a

def refIViewCellArg (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 (setR (arrR x y) 0 (W (x + 3))))



/-- The in-place loop tests, all of which `compile` accepts. -/
def inPlaceFuncs : List TestFn :=
  [tfm2 "iLibFill" iLibFill.exp (fun a => (iLibFill a[0]! a[1]!).run) refILibFill,
   tfm2 "iLibRev" iLibRev.exp (fun a => (iLibRev a[0]! a[1]!).run) refILibRev,
   tfm2 "iLibCopy" iLibCopy.exp (fun a => (iLibCopy a[0]! a[1]!).run) refILibCopy,
   tfm2 "iBubble" iBubble.exp (fun a => (iBubble a[0]! a[1]!).run) refIBubble,
   tfm2 "iStruct" iStruct.exp (fun a => (iStruct a[0]! a[1]!).run) refIStruct,
   tfm2 "iFindRep" iFindRep.exp (fun a => (iFindRep a[0]! a[1]!).run) refIFindRep,
   tfm2 "iRot" iRot.exp (fun a => (iRot a[0]! a[1]!).run) refIRot,
   tfm2 "iSubSlice" iSubSlice.exp (fun a => (iSubSlice a[0]! a[1]!).run) refISubSlice,
   tfm2 "iTwo" iTwo.exp (fun a => (iTwo a[0]! a[1]!).run) refITwo,
   tfm2 "iPairPass" iPairPass.exp (fun a => (iPairPass a[0]! a[1]!).run) refIPairPass,
   tfm2 "iPairRev" iPairRev.exp (fun a => (iPairRev a[0]! a[1]!).run) refIPairRev,
   tfm2 "iSlotLoop" iSlotLoop.exp (fun a => (iSlotLoop a[0]! a[1]!).run) refISlotLoop,
   tfm2 "iViewCellArg" iViewCellArg.exp (fun a => (iViewCellArg a[0]! a[1]!).run) refIViewCellArg,
   iRoot]

/-- The functions that `compile` must refuse with an error. -/
def refusedInPlaceFuncs : List TestFn :=
  [tfm2 "rPairCopy" rPairCopy.exp (fun a => (rPairCopy a[0]! a[1]!).run) refRPairCopy,
   tfm2 "rPairPass" rPairPass.exp (fun a => (rPairPass a[0]! a[1]!).run) refRPairPass,
   tfm2 "rDeepSlots" rDeepSlots.exp (fun a => (rDeepSlots a[0]! a[1]!).run) refRDeepSlots,
   tfm2 "rViewReborrow" rViewReborrow.exp (fun a => (rViewReborrow a[0]! a[1]!).run)
     refRViewReborrow,
   tfm2 "rViewCopy" rViewCopy.exp (fun a => (rViewCopy a[0]! a[1]!).run) refRViewCopy]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (2 ^ 64 - 1, 2 ^ 64 - 1)].all
  fun (x, y) => ((inPlaceFuncs ++ refusedInPlaceFuncs).filter (·.arity == 2)).all fun f =>
    f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]

-- all of them are in the fragment the pipeline accepts
#guard (inPlaceFuncs.filter (·.arity == 2)).all fun f => f.exp.memOk

end Millipede.Tests.Differential
