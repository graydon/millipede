import Tests.Differential.MemFuncs

/-!
# Differential tests of pointers

On the machine a reference is a pointer. A borrow binder holds the address of the lent place,
reads and writes happen in place, and a reference argument is passed as an address. Each
function below runs through the whole pipeline under qemu and is compared with a reference in
plain Lean over `Nat` and `List`.

The functions take `&mut` to nested struct fields, to array elements at run-time indices and to
elements of an array of structs. Callees reborrow fields of their own reference parameter, pass
it on whole, and return a value computed while they mutate through it. Calls take two and three
`&mut` arguments to disjoint places of one struct, or a `&mut` and a `&` argument of the same
struct. Slices, which are a pointer and a length, are summed, filled at a run-time offset,
reversed in place, taken of a field array, held twice with overlap, and passed as reference
arguments. `pRoot` is a program of its own whose large root every step updates in place.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

structure Tri where
  a : UInt64
  b : UInt64
  c : UInt64
deriving Data, Inhabited

/-! ## Helpers -/

mp def inc (r : &mut UInt64) (d : UInt64) : Unit := do
  r := r + d
  ()

mp def addTo (a : &mut UInt64) (b : &mut UInt64) : Unit := do
  a := a + b * 2
  b := b + 1
  ()

mp def rot3 (a : &mut UInt64) (b : &mut UInt64) (c : &mut UInt64) : Unit := do
  let t := a
  a := b
  b := c
  c := t
  ()

mp def bumpSeg (s : &mut Seg) (d : UInt64) : Unit :=
  let _ := bump (&mut s.hi) d
  let _ := bump (&mut s.lo) (d + 1)
  ()

mp def copyPt (dst : &mut Pt) (src : &Pt) : Unit := do
  dst.x := src.y
  dst.y := src.x + dst.y
  ()

mp def bumpTwice (p : &mut Pt) (d : UInt64) : Unit :=
  let _ := bump (&mut p) d
  bump (&mut p) (d * 2)

mp def bumpRet (p : &mut Pt) : UInt64 := do
  p.x := p.x + 1
  p.x * 2

/-- Reduce a natural number to 64 bits, as the references do after each operation. -/
def W (n : Nat) : Nat := n % 2 ^ 64

def bumpR (s : Nat × Nat) (d : Nat) : Nat × Nat :=
  let x := W (s.1 + d)
  (x, W (s.2 * 3 + x))

def hashR (m : Nat) (l : List Nat) : Nat := l.foldl (fun acc v => W (acc * m + v)) 0

/-! ## 1. `&mut` to nested struct fields -/

mp def pField (x y : UInt64) : UInt64 := do
  let mut s := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt } : Seg }
  let _ := inc (&mut s.lo.y) x
  let _ := inc (&mut s.hi.x) 3
  let _ := inc (&mut s.lo.y) s.hi.x
  s.lo.x + s.lo.y * 3 + s.hi.x * 5 + s.hi.y * 7

def refPField (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let hix := W (y + 3)
  let loy := W (W (y + x) + hix)
  UInt64.ofNat (W (x + loy * 3 + hix * 5 + x * 7))

/-! ## 2. `&mut` to array elements with run-time indices -/

mp def pElem (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[1] := y
  let i := y % 4
  let _ := inc (&mut a[i]!) 5
  let j := (x + y) % 4
  let _ := inc (&mut a[j]!) y
  let mut acc := 0
  for k in 0...4 do
    acc := acc * 7 + a[k]
  acc

def refPElem (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let add (l : List Nat) (k d : Nat) : List Nat :=
    (List.range 4).map fun t => if t = k then W (l[t]! + d) else l[t]!
  let l := add (add [x, y, x, x] (y % 4) 5) (W (x + y) % 4) y
  UInt64.ofNat (hashR 7 l)

/-! ## 3. A callee reborrowing fields of its own `&mut` parameter -/

mp def pNested (x y : UInt64) : UInt64 := do
  let mut s := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt } : Seg }
  let _ := bumpSeg (&mut s) y
  let _ := bumpSeg (&mut s) 1
  s.lo.x + s.lo.y * 3 + s.hi.x * 5 + s.hi.y * 7

def refPNested (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let seg (s : (Nat × Nat) × (Nat × Nat)) (d : Nat) : (Nat × Nat) × (Nat × Nat) :=
    (bumpR s.1 (d + 1), bumpR s.2 d)
  let s := seg (seg ((x, y), (y, x)) y) 1
  UInt64.ofNat (W (s.1.1 + s.1.2 * 3 + s.2.1 * 5 + s.2.2 * 7))

/-! ## 4. `&mut` to elements of an array of structs -/

mp def pPtArr (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 3 ({ x := x, y := y : Pt })
  let _ := bump (&mut a[1]) y
  let _ := bump (&mut a[2]) x
  let _ := bump (&mut a[1]) 2
  a[0].x + a[1].x * 3 + a[1].y * 5 + a[2].x * 7 + a[2].y * 11

def refPPtArr (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let p1 := bumpR (bumpR (x, y) y) 2
  let p2 := bumpR (x, y) x
  UInt64.ofNat (W (x + p1.1 * 3 + p1.2 * 5 + p2.1 * 7 + p2.2 * 11))

/-! ## 5. Two `&mut` arguments -/

mp def pTwo (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let _ := addTo (&mut p.x) (&mut p.y)
  let _ := addTo (&mut p.y) (&mut p.x)
  p.x * 3 + p.y

def refPTwo (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let x1 := W (x + y * 2)
  let y1 := W (y + 1)
  let y2 := W (y1 + x1 * 2)
  let x2 := W (x1 + 1)
  UInt64.ofNat (W (x2 * 3 + y2))

/-! ## 6. Three `&mut` arguments (rotations of the fields of one struct) -/

mp def pThree (x y : UInt64) : UInt64 := do
  let mut t := { a := x, b := y, c := x * 3 + y : Tri }
  let _ := rot3 (&mut t.a) (&mut t.b) (&mut t.c)
  let _ := rot3 (&mut t.c) (&mut t.a) (&mut t.b)
  t.a + t.b * 10 + t.c * 100

def refPThree (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let c0 := W (x * 3 + y)
  -- after both rotations: a = c0, b = x, c = y
  UInt64.ofNat (W (c0 + x * 10 + y * 100))

/-! ## 7. A `&mut` and a `&` argument of one struct -/

mp def pCopy (x y : UInt64) : UInt64 := do
  let mut s := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt } : Seg }
  let _ := copyPt (&mut s.lo) (&s.hi)
  let _ := copyPt (&mut s.hi) (&s.lo)
  s.lo.x + s.lo.y * 3 + s.hi.x * 5 + s.hi.y * 7

def refPCopy (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  -- lo := (hi.y, hi.x + lo.y) = (x, 2y); hi := (lo.y, lo.x + hi.y) = (2y, 2x)
  let lo := (x, W (y + y))
  let hi := (lo.2, W (lo.1 + x))
  UInt64.ofNat (W (lo.1 + lo.2 * 3 + hi.1 * 5 + hi.2 * 7))

/-! ## 8. A callee that reborrows its own reference parameter whole -/

mp def pReborrow (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let _ := bumpTwice (&mut p) x
  let _ := bumpTwice (&mut p) y
  p.x * 5 + p.y

def refPReborrow (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let tw (s : Nat × Nat) (d : Nat) := bumpR (bumpR s d) (W (d * 2))
  let p := tw (tw (x, y) x) y
  UInt64.ofNat (W (p.1 * 5 + p.2))

/-! ## 9. A callee returning a value computed while it mutates through its reference -/

mp def pRet (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let a := bumpRet (&mut p)
  let b := bumpRet (&mut p)
  a + b * 3 + p.x * 5 + p.y * 7

def refPRet (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  UInt64.ofNat (W (W ((x + 1) * 2) + W ((x + 2) * 2) * 3 + W (x + 2) * 5 + y * 7))

/-! ## 10. Slices: sums (fixed and run-time offset) -/

mp def pSliceSum (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 6 x
  a[2] := y
  a[4] := y * 3 + 1
  let s1 := (let r := &a[1:4]; r[0]! + r[1]! + r[2]!)
  let k := y % 5
  let s2 := (let r := &a[k:k+2]; r[0]! * 5 + r[1]!)
  s1 * 3 + s2

def refPSliceSum (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let arr := [x, x, y, x, W (y * 3 + 1), x]
  let s1 := W ((arr.drop 1).take 3 |>.foldl (· + ·) 0)
  let k := y % 5
  let s2 := hashR 5 ((arr.drop k).take 2)
  UInt64.ofNat (W (s1 * 3 + s2))

/-! ## 11. Slices: fill at a run-time offset -/

mp def pSliceFill (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 6 y
  let k := x % 4
  let _ := (do let r := &mut a[k:k+3]; r[0]! := x; r[1]! := x + 1; r[2]! := r[1]! + r[0]!; ())
  let mut acc := 0
  for i in 0...6 do
    acc := acc * 5 + a[i]
  acc

def refPSliceFill (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let k := x % 4
  let vals := [x, W (x + 1), W (x + 1 + x)]
  let l := (List.range 6).map fun i => if k ≤ i ∧ i < k + 3 then vals[i - k]! else y
  UInt64.ofNat (hashR 5 l)

/-! ## 12. Slices: reverse in place, then a sub-range of it -/

mp def pSliceRev (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 6 x
  a[1] := y
  a[2] := x + y
  a[3] := x * y
  a[4] := x ^^^ y
  a[5] := y + 7
  let _ := (do
    let r := &mut a[0:6]
    let t0 := r[0]!
    r[0]! := r[5]!
    r[5]! := t0
    let t1 := r[1]!
    r[1]! := r[4]!
    r[4]! := t1
    let t2 := r[2]!
    r[2]! := r[3]!
    r[3]! := t2
    ())
  let _ := (do
    let q := &mut a[1:4]
    let t := q[0]!
    q[0]! := q[2]!
    q[2]! := t
    ())
  let mut acc := 0
  for i in 0...6 do
    acc := acc * 3 + a[i]
  acc

def refPSliceRev (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let l := [x, y, W (x + y), W (x * y), x ^^^ y, W (y + 7)].reverse
  let l := [l[0]!, l[3]!, l[2]!, l[1]!, l[4]!, l[5]!]
  UInt64.ofNat (hashR 3 l)

/-! ## 13. Slice of a field array -/

mp def pFieldSlice (x y : UInt64) : UInt64 := do
  let mut t := { count := x, items := Vector.replicate 4 y : Table }
  let _ := (do let r := &mut t.items[1:3]; r[0]! := x + 1; r[1]! := r[0]! * 2; ())
  t.count := t.count + 5
  let q := (let q := &t.items[0:2]; q[0]! + q[1]! * 3)
  t.count * 11 + q + t.items[2] * 13 + t.items[3] * 17

def refPFieldSlice (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let i1 := W (x + 1)
  let i2 := W (i1 * 2)
  UInt64.ofNat (W (W (x + 5) * 11 + W (y + i1 * 3) + i2 * 13 + y * 17))

/-! ## 14. Two overlapping shared slices alive together -/

mp def pOverlap (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 6 x
  a[1] := y
  a[3] := y + 1
  a[5] := x + y
  let r := &a[0:4]
  let q := &a[2:6]
  let mut acc := 0
  for i in 0...4 do
    acc := acc + r[i]! * q[i]!
  acc

def refPOverlap (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let arr := [x, y, x, W (y + 1), x, W (x + y)]
  UInt64.ofNat (W ((List.range 4).foldl (fun acc i => acc + arr[i]! * arr[i + 2]!) 0))

/-! ## 15. A shared reference passed in a loop -/

mp def pLoopShr (x y : UInt64) : UInt64 := do
  let s := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt } : Seg }
  let mut acc := x
  for i in 0...5 do
    acc := acc * 3 + sumPt (&s.lo) + sumPt (&s.hi) + i
  acc

def refPLoopShr (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let lo := W (x * 5 + y)
  let hi := W (y * 5 + x)
  UInt64.ofNat ((List.range 5).foldl (fun acc i => W (acc * 3 + lo + hi + i)) x)

/-! ## 16. A big root updated in place by the reactor's step -/

structure Big where
  count : UInt64
  items : Vector UInt64 32
deriving Data, Inhabited

mp def bigInit : Big := { count := 0, items := Vector.replicate 32 0 : Big }

-- the program's safety proof cites the step's
set_option mp.autoSafe true in
/-- One step reads a case, which is a word `x` and the expected checksum `e`, and exits at the end of
the input. It updates the root in place and writes `.` when the checksum of the updated root
equals `e` and `X` otherwise. -/
mp def bigStep (r : &mut Big) : Unit := do
  let b0 := Examples.sysRead 0
  if b0 < 256 then
    let x := readWord b0
    let e := readWord (Examples.sysRead 0)
    let i := x % 32
    r.items[i]! := r.items[i]! + x
    r.count := r.count + 1
    let j := (i + 1) % 32
    let c := r.items[i]! + r.count * 3 + r.items[j]!
    if c == e then
      let _w := Examples.sysWrite 1 "."
      ()
    else
      let _w := Examples.sysWrite 1 "X"
      ()
  else
    let _x := Examples.sysExit 0
    ()

mp program bigProg (root : Big) init bigInit step bigStep

/-- The checksums after each step, with the root threaded through as a plain list. -/
def refBig (xs : List UInt64) : List UInt64 :=
  let step (st : Nat × List Nat) (x : UInt64) : (Nat × List Nat) × UInt64 :=
    let i := x.toNat % 32
    let items := (List.range 32).map fun t => if t = i then W (st.2[t]! + x.toNat) else st.2[t]!
    let count := W (st.1 + 1)
    let j := (i + 1) % 32
    ((count, items), UInt64.ofNat (W (items[i]! + count * 3 + items[j]!)))
  let rec go (st : Nat × List Nat) : List UInt64 → List UInt64
    | [] => []
    | x :: rest => let (st', e) := step st x; e :: go st' rest
  go (0, List.replicate 32 0) xs

/-- The input file of `pRoot`, which holds for each case its word and the expected checksum. -/
def bigInput (xs : List UInt64) : List UInt8 :=
  (xs.zip (refBig xs)).flatMap fun (x, e) =>
    [x, e].flatMap fun w => (List.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8

/-- The words fed to `pRoot`, which are edge values and a linear-congruential stream, so that
indices wrap, repeat and collide. -/
def bigCases : List UInt64 :=
  let edge : List UInt64 := [0, 1, 2, 31, 32, 33, 63, 64, 65, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
    0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xDEADBEEFCAFEBABE]
  let rec lcg (s : UInt64) : Nat → List UInt64
    | 0 => []
    | n + 1 => let s' := s * 6364136223846793005 + 1442695040888963407; (s' >>> 7) :: lcg s' n
  edge ++ (lcg 12345 300).map (· % 40) ++ lcg 99 150 ++ edge

/-- The stateful test, one ELF that updates a large root in place over `bigCases.length` steps,
with the expected values computed by `refBig`. -/
def pRoot : TestFn :=
  { name := "pRoot", arity := 0, exp := .atom (.lit (t := Ty.u64) 0), fn := fun _ => 0,
    ref := fun _ => 0, custom := some (bigProg, bigInput bigCases, bigCases.length) }

/-! ## Slices as reference arguments

A slice argument is passed as the address of its first element and its length, so the callee
works on the caller's elements in place. -/

mp def sumSl (s : &Slice UInt64 4) : UInt64 := s[0]! + s[1]! + s[2]!

/-- A slice borrowed and passed on to a function as a reference argument. -/
mp def rSliceArg (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[2] := y
  sumSl (&a[1:4])

def refRSliceArg (a : List UInt64) : UInt64 := W (a[0]!.toNat * 2 + a[1]!.toNat) |> UInt64.ofNat

/-- The callee writes the caller's elements through a `&mut` slice parameter. -/
mp def bumpSl (s : &mut Slice UInt64 4) (d : UInt64) : Unit := do
  s[0]! := s[0]! + d
  s[1]! := s[1]! * 3
  ()

/-- A `&mut` slice argument (elements `1..3`), and the whole array as a slice. -/
mp def mSliceArg (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[2] := y
  let _ := bumpSl (&mut a[1:3]) 5
  let _ := bumpSl (&mut a[0:4]) y
  a[0] + a[1] * 3 + a[2] * 5 + a[3] * 7

def refMSliceArg (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let a1 := (x + 5) % m
  let a2 := (y * 3) % m
  let a0 := (x + y) % m
  let a1' := (a1 * 3) % m
  UInt64.ofNat ((a0 + a1' * 3 + a2 * 5 + x * 7) % m)

/-- Three reference arguments in one call: a `&mut` slice, a shared slice of another array and a
`&mut` element of a third. -/
mp def mixSl (s : &mut Slice UInt64 4) (t : &Slice UInt64 4) (c : &mut UInt64) : Unit := do
  s[0]! := t[1]! + c
  c := t[0]! * 2
  s[1]! := s[0]! + 1
  ()

mp def mSliceMix (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  let mut b := Vector.replicate 4 y
  b[3] := x + y
  let mut c := Vector.replicate 2 (x * 7)
  let _ := mixSl (&mut a[2:4]) (&b[2:4]) (&mut c[1])
  a[0] + a[1] * 3 + a[2] * 5 + a[3] * 7 + c[0] * 11 + c[1] * 13

def refMSliceMix (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let b3 := (x + y) % m
  let c1 := (x * 7) % m
  let a2 := (b3 + c1) % m
  let c1' := (y * 2) % m
  let a3 := (a2 + 1) % m
  UInt64.ofNat ((x + x * 3 + a2 * 5 + a3 * 7 + c1 * 11 + c1' * 13) % m)

/-- A slice parameter used with its length in a loop `for i in 0...s.len`. Its callers pass slice
arguments `&a[lo..hi]` of run-time length and read the length of a slice borrow. -/
mp def sumLen (s : &[UInt64; 6]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc + s[i] * (i + 1)
  acc

mp def bumpLast (s : &mut [UInt64; 6]) (d : UInt64) : Unit := do
  if 0 < s.len then
    s[s.len - 1] := s[s.len - 1] + d
    ()
  else ()

mp def pSliceLen (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 6 x
  a[1] := y
  let k := y % 5 + 1
  let _ := bumpLast (&mut a[1..k + 1]) 3
  let t := sumLen (&a[0..k])
  t + a[k]! * 100 + (let r := &a[2..6]; r.len)

def refPSliceLen (a : List UInt64) : UInt64 :=
  let x := a[0]!
  let y := a[1]!
  let k := (y % 5 + 1).toNat
  let arr : List UInt64 := [x, y, x, x, x, x]
  let arr := arr.set k (arr[k]! + 3)
  let t := ((List.range k).map fun i => arr[i]! * UInt64.ofNat (i + 1)).foldl (· + ·) 0
  t + arr[k]! * 100 + 4

example : ∀ x y : Fin 7, (pSliceLen x.val.toUInt64 y.val.toUInt64).run =
    refPSliceLen [x.val.toUInt64, y.val.toUInt64] := by decide

/-! ## Harness steps and registry -/

set_option maxHeartbeats 2000000 in

/-- The pointer functions that `compile` must refuse with an error, of which there are none. -/
def refusedPtrFuncs : List TestFn := []

/-- The functions exercising pointers. -/
def ptrFuncs : List TestFn :=
  [tfm2 "pField" pField.exp (fun a => (pField a[0]! a[1]!).run) refPField,
   tfm2 "rSliceArg" rSliceArg.exp (fun a => (rSliceArg a[0]! a[1]!).run) refRSliceArg,
   tfm2 "mSliceArg" mSliceArg.exp (fun a => (mSliceArg a[0]! a[1]!).run) refMSliceArg,
   tfm2 "mSliceMix" mSliceMix.exp (fun a => (mSliceMix a[0]! a[1]!).run) refMSliceMix,
   tfm2 "pSliceLen" pSliceLen.exp (fun a => (pSliceLen a[0]! a[1]!).run) refPSliceLen,
   tfm2 "pElem" pElem.exp (fun a => (pElem a[0]! a[1]!).run) refPElem,
   tfm2 "pNested" pNested.exp (fun a => (pNested a[0]! a[1]!).run) refPNested,
   tfm2 "pPtArr" pPtArr.exp (fun a => (pPtArr a[0]! a[1]!).run) refPPtArr,
   tfm2 "pTwo" pTwo.exp (fun a => (pTwo a[0]! a[1]!).run) refPTwo,
   tfm2 "pThree" pThree.exp (fun a => (pThree a[0]! a[1]!).run) refPThree,
   tfm2 "pCopy" pCopy.exp (fun a => (pCopy a[0]! a[1]!).run) refPCopy,
   tfm2 "pReborrow" pReborrow.exp (fun a => (pReborrow a[0]! a[1]!).run) refPReborrow,
   tfm2 "pRet" pRet.exp (fun a => (pRet a[0]! a[1]!).run) refPRet,
   tfm2 "pSliceSum" pSliceSum.exp (fun a => (pSliceSum a[0]! a[1]!).run) refPSliceSum,
   tfm2 "pSliceFill" pSliceFill.exp (fun a => (pSliceFill a[0]! a[1]!).run) refPSliceFill,
   tfm2 "pSliceRev" pSliceRev.exp (fun a => (pSliceRev a[0]! a[1]!).run) refPSliceRev,
   tfm2 "pFieldSlice" pFieldSlice.exp (fun a => (pFieldSlice a[0]! a[1]!).run) refPFieldSlice,
   tfm2 "pOverlap" pOverlap.exp (fun a => (pOverlap a[0]! a[1]!).run) refPOverlap,
   tfm2 "pLoopShr" pLoopShr.exp (fun a => (pLoopShr a[0]! a[1]!).run) refPLoopShr,
   pRoot]

end Millipede.Tests.Differential
