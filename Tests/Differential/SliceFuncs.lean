import Tests.Differential.PtrFuncs

/-!
# Differential tests of slice parameters and aliasing

Each function is an `mp def` over two words. The harness of `Harness.lean` compiles it through
the whole pipeline, runs the ELF under qemu and compares its output with a reference written in
plain Lean over `Nat` and `List`.

The slice tests pass slices, which are a pointer and a length, as `&[T; n]` and `&mut [T; n]`
parameters. They sum and fill a slice, reverse it in place, find an element, copy between two
slices, pass a slice together with a `&mut` scalar, borrow sub-slices of an array inside a callee,
and pass slices inside a loop body. Other tests pass a slice parameter on whole to another
callee, by `&` and by `&mut`.

The aliasing tests, named `al*`, read the lender after a borrow has ended: after a scoped borrow,
after a callee that wrote through a reference, through a scoped slice borrow and through a slice
argument. A compiler that passed a copy of the lender would lose the writes and still read
correctly, so only a test that reads the lender afterwards sees the bug. The seeded mutants
`copy-borrow`, `copy-ref`, `copy-slice-borrow` and `copy-slice-arg` of `Mutants.lean` do exactly
this, and each must fail every harness of its family, which `aliasFor` lists.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

/-! ## Shared pieces -/

/-- The array under test: `x` with `y`, `x ^^^ y` and `3y+1` at places 1, 3, 6. -/
mp def mkArr (x y : UInt64) : Arr UInt64 8 := do
  let mut a := Vector.replicate 8 x
  a[1] := y
  a[3] := x ^^^ y
  a[6] := y * 3 + 1
  a

def arrR (x y : Nat) : List Nat := [x, y, x, x ^^^ y, x, x, W (y * 3 + 1), x]

/-- A polynomial hash of the 8 elements, which reads every cell of the lender. -/
mp def hash8 (a : Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    acc := acc * 7 + a[i]
  acc

/-- Replace `len` elements from `lo` by `f`. -/
def patchR (l : List Nat) (lo len : Nat) (f : Nat → Nat) : List Nat :=
  (List.range l.length).map fun t => if lo ≤ t ∧ t < lo + len then f (t - lo) else l[t]!

/-- The weighted sum `Σ l[i] * (i + 1)`, the reference for `slSum`. -/
def sumR (l : List Nat) : Nat :=
  W ((List.range l.length).foldl (fun acc i => acc + l[i]! * (i + 1)) 0)

def sliceR (l : List Nat) (lo len : Nat) : List Nat := (l.drop lo).take len

def toNat2 (a : List UInt64) : Nat × Nat := (a[0]!.toNat, a[1]!.toNat)

/-! ## Slice parameters -/

/-- The weighted sum `Σ s[i] * (i + 1)` of a shared slice, by a loop over its length. -/
mp def slSum (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc + s[i] * (i + 1)
  acc

/-- Fill the slice with `v + k` at cell `k`. The cells are unrolled, and each write is guarded
by the length; the guards are nested because each write must be a statement. -/
mp def slFill (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  if 0 < s.len then
    s[0] := v + 0
    if 1 < s.len then
      s[1] := v + 1
      if 2 < s.len then
        s[2] := v + 2
        if 3 < s.len then
          s[3] := v + 3
          if 4 < s.len then
            s[4] := v + 4
            if 5 < s.len then
              s[5] := v + 5
              if 6 < s.len then
                s[6] := v + 6
                if 7 < s.len then
                  s[7] := v + 7
                  ()
                else ()
              else ()
            else ()
          else ()
        else ()
      else ()
    else ()
  else ()

/-- Reverse in place: cell `i` swaps with `len - 1 - i` while `2i + 1 < len`. -/
mp def slRev (s : &mut [UInt64; 8]) : Unit := do
  if 1 < s.len then
    let a := s[0]
    let b := s[s.len - 1]
    s[0] := b
    s[s.len - 1] := a
    if 3 < s.len then
      let a := s[1]
      let b := s[s.len - 2]
      s[1] := b
      s[s.len - 2] := a
      if 5 < s.len then
        let a := s[2]
        let b := s[s.len - 3]
        s[2] := b
        s[s.len - 3] := a
        if 7 < s.len then
          let a := s[3]
          let b := s[s.len - 4]
          s[3] := b
          s[s.len - 4] := a
          ()
        else ()
      else ()
    else ()
  else ()

/-- The index of the first cell equal to `v`, or `99`. -/
mp def slFind (s : &[UInt64; 8]) (v : UInt64) : UInt64 := do
  let mut acc := 99
  for i in 0...s.len do
    let c := s[i]
    acc := if acc == 99 then (if c == v then i else acc) else acc
  acc

/-- Copy the first `min dst.len src.len` (at most 4) cells, plus one, from `src` to `dst`; returns
`min dst.len src.len`. -/
mp def slCopy (dst : &mut [UInt64; 8]) (src : &[UInt64; 8]) : UInt64 := do
  let n := if dst.len < src.len then dst.len else src.len
  if 0 < dst.len then
    if 0 < src.len then
      dst[0] := src[0] + 1
      if 1 < dst.len then
        if 1 < src.len then
          dst[1] := src[1] + 1
          if 2 < dst.len then
            if 2 < src.len then
              dst[2] := src[2] + 1
              if 3 < dst.len then
                if 3 < src.len then
                  dst[3] := src[3] + 1
                  n
                else n
              else n
            else n
          else n
        else n
      else n
    else n
  else n

/-- Take a slice and a `&mut` scalar in one call, and set `c` to `2 * c + 3 * t`, where `t` is
the weighted sum of `s`. -/
mp def slAcc (s : &[UInt64; 8]) (c : &mut UInt64) : Unit := do
  let mut t := 0
  for i in 0...s.len do
    t := t + s[i] * (i + 1)
  c := c * 2 + t * 3
  ()

/-! ## 1. Sum with run-time bounds -/

mp def sSum (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  let lo := x % 5
  let len := y % 4
  slSum (&a[lo..lo + len]) * 3 + slSum (&a[0..8])

def refSSum (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  UInt64.ofNat (W (sumR (sliceR l (x % 5) (y % 4)) * 3 + sumR l))

/-! ## 2. Fill -/

mp def sFill (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := y % 6
  let len := x % 3 + 1
  let _ := slFill (&mut a[lo..lo + len]) y
  hash8 a

def refSFill (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lo := y % 6
  let len := x % 3 + 1
  UInt64.ofNat (hashR 7 (patchR (arrR x y) lo len fun k => W (y + k)))

/-! ## 3. Reverse in place, twice -/

mp def sRev (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 4
  let len := y % 5 + 1
  let _ := slRev (&mut a[lo..lo + len])
  let _ := slRev (&mut a[1..8])
  hash8 a

def revSub (l : List Nat) (lo len : Nat) : List Nat :=
  l.take lo ++ (sliceR l lo len).reverse ++ l.drop (lo + len)

def refSRev (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := revSub (arrR x y) (x % 4) (y % 5 + 1)
  let l := revSub l 1 7
  UInt64.ofNat (hashR 7 l)

/-! ## 4. Find -/

mp def sFind (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  let lo := x % 3
  let len := y % 5 + 2
  let v := if y % 2 == 0 then x else y * 3 + 1
  slFind (&a[lo..lo + len]) v * 100 + slFind (&a[0..8]) (x ^^^ y)

def findR (l : List Nat) (v : Nat) : Nat :=
  match (List.range l.length).find? fun i => l[i]! == v with
  | some i => i
  | none => 99

def refSFind (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let v := if y % 2 = 0 then x else W (y * 3 + 1)
  UInt64.ofNat (W (findR (sliceR l (x % 3) (y % 5 + 2)) v * 100 + findR l (x ^^^ y)))

/-! ## 5. Copy between two slices passed together (two arrays) -/

mp def sCopy (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let b := mkArr y (x + 1)
  let lo := x % 4
  let n1 := y % 4 + 1
  let m := slCopy (&mut a[lo..lo + n1]) (&b[y % 3..y % 3 + 4])
  let m2 := slCopy (&mut a[0..3]) (&b[5..8])
  hash8 a * 11 + m * 3 + m2

def refSCopy (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let la := arrR x y
  let lb := arrR y (W (x + 1))
  let copy (dst src : List Nat) (lo len slo slen : Nat) : List Nat × Nat :=
    let n := min len slen
    (patchR dst lo (min n 4) fun k => W (src[slo + k]! + 1), n)
  let (la, m) := copy la lb (x % 4) (y % 4 + 1) (y % 3) 4
  let (la, m2) := copy la lb 0 3 5 3
  UInt64.ofNat (W (W (hashR 7 la * 11 + m * 3) + m2))

/-! ## 6. A slice and a `&mut` scalar in one call -/

mp def sScalar (x y : UInt64) : UInt64 := do
  let a := mkArr x y
  let mut t := y
  let lo := x % 5
  let _ := slAcc (&a[lo..lo + y % 4]) (&mut t)
  let _ := slAcc (&a[0..8]) (&mut t)
  let _ := slAcc (&a[7..8]) (&mut t)
  t

def refSScalar (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let step (t : Nat) (s : List Nat) := W (t * 2 + W (sumR s * 3))
  let t := step y (sliceR l (x % 5) (y % 4))
  let t := step t l
  let t := step t (sliceR l 7 1)
  UInt64.ofNat t

/-! ## 7. Sub-slices taken inside a callee (from an array reference) -/

/-- The callee borrows sub-slices of the array it was lent. -/
mp def subBump (a : &mut Arr UInt64 8) (k : UInt64) : UInt64 := do
  let m := k % 5
  let _ := (do
    let r := &mut a[m..m + 3]
    r[0]! := r[1]! + r[2]!
    r[2]! := r[0]! * 2
    ())
  let q := (let q := &a[1..m + 2]; q.len + q[0]!)
  q + a[0]

mp def sSub (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let r1 := subBump (&mut a) y
  let r2 := subBump (&mut a) x
  hash8 a + r1 * 3 + r2 * 5

def refSSub (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let bump (l : List Nat) (k : Nat) : List Nat × Nat :=
    let m := k % 5
    let v0 := W (l[m + 1]! + l[m + 2]!)
    let v2 := W (v0 * 2)
    let l := (List.range 8).map fun t =>
      if t = m then v0 else if t = m + 2 then v2 else l[t]!
    (l, W (W ((m + 1) + l[1]!) + l[0]!))
  let (l, r1) := bump (arrR x y) y
  let (l, r2) := bump l x
  UInt64.ofNat (W (hashR 7 l + r1 * 3 + r2 * 5))

/-! ## 8. Slice arguments inside a loop body -/

mp def sLoop (x y : UInt64) : UInt64 := do
  let a := mkArr x y
  let mut acc := x
  for i in 0...5 do
    acc := acc * 5 + slSum (&a[i..i + 3 + y % 2])
  acc

def refSLoop (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  UInt64.ofNat ((List.range 5).foldl (fun acc i => W (acc * 5 + sumR (sliceR l i (3 + y % 2)))) x)

/-! ## Aliasing

Each caller below reads the lender after a borrow has ended or a callee has returned. -/

structure Duo where
  lo : Pt
  hi : Pt
  k : UInt64
deriving Data, Inhabited

/-- Hash of a `Duo`. -/
mp def hashDuo (d : Duo) : UInt64 :=
  d.lo.x + d.lo.y * 3 + d.hi.x * 5 + d.hi.y * 7 + d.k * 11

def hashDuoR (lx ly hx hy k : Nat) : Nat := W (lx + ly * 3 + hx * 5 + hy * 7 + k * 11)

/-! ### Scoped borrows -/

/-- A scoped `&mut` of one element at a run-time index is written through, and the array is read
after. -/
mp def alBElem (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := x % 8
  let _ := (do
    let r := &mut a[i]!
    r := r + y + 1
    ())
  hash8 a

def refAlBElem (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let i := x % 8
  UInt64.ofNat (hashR 7 (patchR (arrR x y) i 1 fun _ => W ((arrR x y)[i]! + y + 1)))

/-- A scoped `&mut` of a struct field that is itself a struct is written through. -/
mp def alBField (x y : UInt64) : UInt64 := do
  let mut d := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt }, k := 3 : Duo }
  let _ := (do
    let r := &mut d.hi
    r.x := r.x + x
    r.y := r.x * 3 + r.y
    ())
  hashDuo d

def refAlBField (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let hx := W (y + x)
  UInt64.ofNat (hashDuoR x y hx (W (hx * 3 + x)) 3)

/-- Two scoped borrows in a row, first of a field and then of the whole struct, with the lender
read after each. -/
mp def alBWhole (x y : UInt64) : UInt64 := do
  let mut d := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt }, k := 3 : Duo }
  let _ := (do
    let r := &mut d.lo
    r.y := r.y + 5
    ())
  let a := d.lo.y
  let _ := (do
    let r := &mut d
    r.k := r.k + a
    r.hi.x := r.lo.y + r.k
    ())
  a + hashDuo d

def refAlBWhole (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let ly := W (y + 5)
  let k := W (3 + ly)
  UInt64.ofNat (W (ly + hashDuoR x ly (W (ly + k)) x k))

/-- A scoped borrow inside another is written through, and the outer borrow then reads the
written value. -/
mp def alBNest (x y : UInt64) : UInt64 := do
  let mut d := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt }, k := 3 : Duo }
  let _ := (do
    let r := &mut d
    let _ := (do
      let q := &mut r.lo
      q.x := q.x + y
      q.y := q.x + 1
      ())
    r.k := r.k + r.lo.x
    ())
  hashDuo d

def refAlBNest (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lx := W (x + y)
  UInt64.ofNat (hashDuoR lx (W (lx + 1)) y x (W (3 + lx)))

/-! ### Reference arguments -/

mp def addK (r : &mut UInt64) (d : UInt64) : Unit := do
  r := r + d + 1
  ()

mp def bumpDuo (d : &mut Duo) (v : UInt64) : UInt64 := do
  d.lo.x := d.lo.x + v
  let _ := addK (&mut d.hi.y) v
  d.k := d.k + 1
  d.k

/-- A callee writes a scalar through its reference; the caller then reads. -/
mp def alRElem (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let i := y % 8
  let _ := addK (&mut a[i]!) x
  let _ := addK (&mut a[(i + 3) % 8]!) y
  hash8 a

def refAlRElem (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let i := y % 8
  let l := patchR (arrR x y) i 1 fun _ => W ((arrR x y)[i]! + x + 1)
  let j := (i + 3) % 8
  UInt64.ofNat (hashR 7 (patchR l j 1 fun _ => W (l[j]! + y + 1)))

/-- A callee takes the whole struct by `&mut` and reborrows fields of it. -/
mp def alRStruct (x y : UInt64) : UInt64 := do
  let mut d := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt }, k := 3 : Duo }
  let r1 := bumpDuo (&mut d) y
  let r2 := bumpDuo (&mut d) x
  hashDuo d + r1 * 13 + r2 * 17

def refAlRStruct (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let step (s : Nat × Nat × Nat × Nat × Nat) (v : Nat) : (Nat × Nat × Nat × Nat × Nat) × Nat :=
    let (lx, ly, hx, hy, k) := s
    ((W (lx + v), ly, hx, W (hy + v + 1), W (k + 1)), W (k + 1))
  let (s1, r1) := step (x, y, y, x, 3) y
  let (s2, r2) := step s1 x
  let (lx, ly, hx, hy, k) := s2
  UInt64.ofNat (W (hashDuoR lx ly hx hy k + r1 * 13 + r2 * 17))

/-- A call with two `&mut` arguments to two fields of a struct, followed by a scoped borrow of the
same struct. -/
mp def alRTwo (x y : UInt64) : UInt64 := do
  let mut d := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt }, k := 3 : Duo }
  let _ := addTo (&mut d.lo.x) (&mut d.hi.y)
  let a := d.lo.x + d.hi.y
  let _ := (do
    let r := &mut d.hi
    r.x := r.x + a
    ())
  hashDuo d + a

def refAlRTwo (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lx := W (x + x * 2)
  let hy := W (x + 1)
  let a := W (lx + hy)
  UInt64.ofNat (W (hashDuoR lx y (W (y + a)) hy 3 + a))

/-! ### Scoped slice borrows -/

/-- A `&mut` slice borrow is written through, and the array is then read through a shared slice
borrow and directly. -/
mp def alSBorrow (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 5
  let _ := (do
    let r := &mut a[lo..lo + 3]
    r[0]! := r[1]! + 1
    r[2]! := r[0]! * 2
    ())
  let t := (let q := &a[lo..lo + 3]; q[0]! + q[1]! * 3 + q[2]! * 5)
  hash8 a + t

def refAlSBorrow (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lo := x % 5
  let l := arrR x y
  let v0 := W (l[lo + 1]! + 1)
  let v2 := W (v0 * 2)
  let l := (List.range 8).map fun t => if t = lo then v0 else if t = lo + 2 then v2 else l[t]!
  UInt64.ofNat (W (hashR 7 l + W (l[lo]! + l[lo + 1]! * 3 + l[lo + 2]! * 5)))

/-- Two slice borrows of two different arrays, each written in turn from the other, with both
arrays read after. -/
mp def alSTwo (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let mut b := mkArr y x
  let v := (let q := &b[2..5]; q[0]! + 1)
  let _ := (do
    let r := &mut a[1..4]
    r[0]! := v
    ())
  let w := (let r := &a[1..4]; r[1]! + 2)
  let _ := (do
    let q := &mut b[2..5]
    q[1]! := w
    ())
  hash8 a * 5 + hash8 b

def refAlSTwo (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let la := arrR x y
  let lb := arrR y x
  let a1 := W (lb[2]! + 1)
  let b3 := W (la[2]! + 2)
  let la := patchR la 1 1 fun _ => a1
  let lb := patchR lb 3 1 fun _ => b3
  UInt64.ofNat (W (hashR 7 la * 5 + hashR 7 lb))

/-! ### Slice arguments -/

/-- A callee writes through a `&mut` slice argument and the array is read after. The second of
the two calls passes the whole array. -/
mp def alAFill (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := y % 5
  let _ := slFill (&mut a[lo..lo + 3]) x
  let mid := hash8 a
  let _ := slFill (&mut a[6..8]) y
  mid * 3 + hash8 a

def refAlAFill (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lo := y % 5
  let l1 := patchR (arrR x y) lo 3 fun k => W (x + k)
  let l2 := patchR l1 6 2 fun k => W (y + k)
  UInt64.ofNat (W (hashR 7 l1 * 3 + hashR 7 l2))

/-- A slice argument and a scalar reference in one call, then the array and the scalar are read. -/
mp def alAScalar (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let mut t := x
  let _ := slAcc (&a[y % 3..y % 3 + 4]) (&mut t)
  let _ := slFill (&mut a[0..2]) t
  t + hash8 a

def refAlAScalar (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let t := W (x * 2 + W (sumR (sliceR l (y % 3) 4) * 3))
  UInt64.ofNat (W (t + hashR 7 (patchR l 0 2 fun k => W (t + k))))

/-- A callee writes through a slice argument, and the same array is then lent whole to another
callee. -/
mp def alAThenRef (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let _ := slFill (&mut a[1..5]) y
  let r := subBump (&mut a) x
  hash8 a + r

def refAlAThenRef (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := patchR (arrR x y) 1 4 fun k => W (y + k)
  let m := x % 5
  let v0 := W (l[m + 1]! + l[m + 2]!)
  let v2 := W (v0 * 2)
  let l := (List.range 8).map fun t => if t = m then v0 else if t = m + 2 then v2 else l[t]!
  UInt64.ofNat (W (hashR 7 l + W (W ((m + 1) + l[1]!) + l[0]!)))

/-! ## A slice parameter passed on whole by `&mut`

The view's address is passed on, and the callee's parameter has the caller's extent. The callee
hands the view back with its occupancy unchanged, so the caller's view is still a view of its
extent. `rPassWhole` passes the slice through one level. `sPassMut` passes it through two, writes
through the view before and after the inner call, and hashes the lender after the calls. -/

mp def passOn (s : &mut [UInt64; 8]) : Unit :=
  slFill (&mut s) 3

mp def rPassWhole (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let _ := passOn (&mut a[0..y % 8])
  hash8 a

def refRPassWhole (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  UInt64.ofNat (hashR 7 (patchR (arrR x y) 0 (y % 8) fun k => W (3 + k)))

mp def passMut (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  let _ := slFill (&mut s) v
  if 1 < s.len then
    s[1] := v * 3
    slRev (&mut s)
  else ()

mp def passMut2 (s : &mut [UInt64; 8]) (v : UInt64) : Unit :=
  passMut (&mut s) (v + 1)

mp def sPassMut (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 5
  let len := y % 4 + 1
  let _ := passMut2 (&mut a[lo..lo + len]) x
  hash8 a

def refSPassMut (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let lo := x % 5
  let len := y % 4 + 1
  let v := W (x + 1)
  let s := (List.range len).map fun k => W (v + k)
  let s := if 1 < len then (s.set 1 (W (v * 3))).reverse else s
  UInt64.ofNat (hashR 7 (patchR (arrR x y) lo len fun k => s[k]!))

/-! ## Loops with tiny bodies -/

/-- A loop whose body only counts. Every path into the body pays the loop's iteration tick, so
the instruction budget accepts it. -/
mp def tinySum (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc + 1
  acc

mp def rTinyLoop (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  tinySum (&a[0..y % 8])

def refRTinyLoop (a : List UInt64) : UInt64 := UInt64.ofNat (a[1]!.toNat % 8)

mp def plainSum (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc + s[i]
  acc

mp def arrSum (a : &Arr UInt64 8) : UInt64 := do
  let mut acc := 0
  for i in 0...8 do
    acc := acc + a[i]
  acc

mp def rPlainSum (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  let u := plainSum (&a[0..y % 8])
  u * 3 + arrSum (&a)

def refRPlainSum (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  UInt64.ofNat ((sliceR l 0 (y % 8)).sum * 3 + l.sum)

/-! ## A slice parameter passed on whole by `&`

A shared slice parameter passed on whole to another callee, as in `slSum (&s)`, passes its address,
and the callee's parameter has the caller's extent. `sPassShr` does this twice, through two
levels. -/

mp def passShr (s : &[UInt64; 8]) : UInt64 :=
  slSum (&s) * 5 + plainSum (&s)

mp def passShr2 (s : &[UInt64; 8]) (k : UInt64) : UInt64 :=
  passShr (&s) + k * s.len

mp def sPassShr (x y : UInt64) : UInt64 :=
  let a := mkArr x y
  let lo := x % 5
  let len := y % 4
  passShr2 (&a[lo..lo + len]) x + passShr (&a[0..8])

def refSPassShr (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let f := fun (s : List Nat) => W (W (sumR s * 5) + s.sum)
  let s := sliceR l (x % 5) (y % 4)
  UInt64.ofNat (W (W (f s + W (x * s.length)) + f l))

/-! ## Harness steps and registry -/


/-- Slice constructs `compile` must refuse with an error. -/
def refusedSliceFuncs : List TestFn := []

/-- The functions of this file that `compile` accepts. -/
def sliceFuncs : List TestFn :=
  [tfm2 "sSum" sSum.exp (fun a => (sSum a[0]! a[1]!).run) refSSum,
   tfm2 "sFill" sFill.exp (fun a => (sFill a[0]! a[1]!).run) refSFill,
   tfm2 "sRev" sRev.exp (fun a => (sRev a[0]! a[1]!).run) refSRev,
   tfm2 "sFind" sFind.exp (fun a => (sFind a[0]! a[1]!).run) refSFind,
   tfm2 "sCopy" sCopy.exp (fun a => (sCopy a[0]! a[1]!).run) refSCopy,
   tfm2 "sScalar" sScalar.exp (fun a => (sScalar a[0]! a[1]!).run) refSScalar,
   tfm2 "sSub" sSub.exp (fun a => (sSub a[0]! a[1]!).run) refSSub,
   tfm2 "sPassShr" sPassShr.exp (fun a => (sPassShr a[0]! a[1]!).run) refSPassShr,
   tfm2 "rPassWhole" rPassWhole.exp (fun a => (rPassWhole a[0]! a[1]!).run) refRPassWhole,
   tfm2 "sPassMut" sPassMut.exp (fun a => (sPassMut a[0]! a[1]!).run) refSPassMut,
   tfm2 "sLoop" sLoop.exp (fun a => (sLoop a[0]! a[1]!).run) refSLoop,
   tfm2 "rTinyLoop" rTinyLoop.exp (fun a => (rTinyLoop a[0]! a[1]!).run) refRTinyLoop,
   tfm2 "rPlainSum" rPlainSum.exp (fun a => (rPlainSum a[0]! a[1]!).run) refRPlainSum,
   tfm2 "alBElem" alBElem.exp (fun a => (alBElem a[0]! a[1]!).run) refAlBElem,
   tfm2 "alBField" alBField.exp (fun a => (alBField a[0]! a[1]!).run) refAlBField,
   tfm2 "alBWhole" alBWhole.exp (fun a => (alBWhole a[0]! a[1]!).run) refAlBWhole,
   tfm2 "alBNest" alBNest.exp (fun a => (alBNest a[0]! a[1]!).run) refAlBNest,
   tfm2 "alRElem" alRElem.exp (fun a => (alRElem a[0]! a[1]!).run) refAlRElem,
   tfm2 "alRStruct" alRStruct.exp (fun a => (alRStruct a[0]! a[1]!).run) refAlRStruct,
   tfm2 "alRTwo" alRTwo.exp (fun a => (alRTwo a[0]! a[1]!).run) refAlRTwo,
   tfm2 "alSBorrow" alSBorrow.exp (fun a => (alSBorrow a[0]! a[1]!).run) refAlSBorrow,
   tfm2 "alSTwo" alSTwo.exp (fun a => (alSTwo a[0]! a[1]!).run) refAlSTwo,
   tfm2 "alAFill" alAFill.exp (fun a => (alAFill a[0]! a[1]!).run) refAlAFill,
   tfm2 "alAScalar" alAScalar.exp (fun a => (alAScalar a[0]! a[1]!).run) refAlAScalar,
   tfm2 "alAThenRef" alAThenRef.exp (fun a => (alAThenRef a[0]! a[1]!).run) refAlAThenRef]

end Millipede.Tests.Differential
