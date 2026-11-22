import Tests.Differential.Harness

/-!
# Differential tests of functions over memory

Each function takes `U64` arguments and uses values held in memory: nested structs and structs
with array fields, enums with payloads, arrays read, written and indexed with `!` and `?`,
`Slots`, `&` and `&mut` parameters, scoped borrows, and copies of whole structs. Each is compiled,
run under qemu on inputs biased towards edge values, and compared with a reference written in
plain Lean over `Nat` and `List`. The references use no `Vector`, `Slots` or `UInt64` operations,
so they do not share the primitives' denotation with the code they check.

Several functions take indices straight from the input, so the checked operations meet in-range,
boundary and out-of-range indices alike.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

structure Pt where
  x : UInt64
  y : UInt64
deriving Data, Inhabited

structure Seg where
  lo : Pt
  hi : Pt
deriving Data, Inhabited

structure Table where
  count : UInt64
  items : Vector UInt64 4
deriving Data, Inhabited

inductive Cmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving Data, Inhabited

/-- A struct with fields of several sizes. -/
structure Mixed where
  a : Bool
  b : UInt64
  c : Bool
  d : UInt64
deriving Data, Inhabited

/-- A payload struct with a byte and a word. -/
structure Span where
  a : Bool
  b : UInt64
deriving Data, Inhabited

/-- An enum with payloads of different sizes. -/
inductive Shape where
  | dot
  | span (s : Span)
  | flag (f : Bool)
  | pair (p : Pt)
deriving Data, Inhabited

/-! ## Helpers called by the functions below -/

mp def bump (p : &mut Pt) (d : UInt64) : Unit := do
  p.x := p.x + d
  p.y := p.y * 3 + p.x
  ()

mp def sumPt (p : &Pt) : UInt64 := p.x * 5 + p.y

mp def addAt (t : &mut Table) (k d : UInt64) : Unit := do
  t.count := t.count + 1
  if k < 4 then
    t.items[k]! := d
    ()
  else ()

/-! ## 1. Struct passed `&mut`, twice -/

mp def mBump (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let _ := bump (&mut p) 5
  let _ := bump (&mut p) x
  p.x * 3 + p.y

def refMBump (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let b (s : Nat × Nat) (d : Nat) : Nat × Nat :=
    let x := (s.1 + d) % m
    (x, (s.2 * 3 + x) % m)
  let s := b (b (a[0]!.toNat, a[1]!.toNat) 5) a[0]!.toNat
  UInt64.ofNat ((s.1 * 3 + s.2) % m)

/-! ## 2. Enum built under conditions, then matched -/

mp def mEnum (x y : UInt64) : UInt64 :=
  let c := if x < 100 then Cmd.add y else if x < 200 then Cmd.mul y else Cmd.stop
  match c with
  | .stop => 7
  | .add n => n + 1
  | .mul n => n * 2

def refMEnum (a : List UInt64) : UInt64 :=
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  UInt64.ofNat (if x < 100 then y + 1 else if x < 200 then y * 2 else 7)

/-! ## 3. Array of enums: written in a loop, read back and evaluated -/

set_option maxHeartbeats 1000000 in
mp def mEnumArr (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 3 Cmd.stop
  a[0] := if x &&& 1 == 0 then Cmd.add (y + 1) else Cmd.mul (y ^^^ 1)
  a[1] := if x &&& 2 == 0 then Cmd.add (y + 2) else Cmd.mul (y ^^^ 2)
  a[2] := if x &&& 4 == 0 then Cmd.add (y + 3) else Cmd.stop
  let r0 := match a[0] with
    | .stop => x
    | .add n => x + n
    | .mul n => x * 3 + n
  let r1 := match a[1] with
    | .stop => r0
    | .add n => r0 + n
    | .mul n => r0 * 3 + n
  match a[2] with
  | .stop => r1
  | .add n => r1 + n
  | .mul n => r1 * 3 + n

def refMEnumArr (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let r0 := if x % 2 = 0 then (x + (y + 1) % m) % m else (x * 3 + (y ^^^ 1)) % m
  let r1 := if (x / 2) % 2 = 0 then (r0 + (y + 2) % m) % m else (r0 * 3 + (y ^^^ 2)) % m
  UInt64.ofNat (if (x / 4) % 2 = 0 then (r1 + (y + 3) % m) % m else r1)

/-! ## 4. Scoped borrow of an array element -/

mp def mBorrow (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  let _ := (do let r := &mut a[2]; r := r + y; ())
  let _ := (do let r := &mut a[0]; r := r * 3; ())
  let mut acc := 0
  for i in 0...4 do
    acc := acc * 7 + a[i]
  acc

def refMBorrow (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let arr := [(x * 3) % m, x, (x + y) % m, x]
  UInt64.ofNat (arr.foldl (fun acc v => (acc * 7 + v) % m) 0)

/-! ## 5. Checked indexing with the raw input as index -/

mp def mChecked (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[1] := y
  match a[x]? with
  | ok v => v + 1000
  | err _ => 99

def refMChecked (a : List UInt64) : UInt64 :=
  let arr := [a[0]!, a[1]!, a[0]!, a[0]!]
  let x := a[0]!
  if x.toNat < 4 then UInt64.ofNat ((arr[x.toNat]!.toNat + 1000) % 2 ^ 64) else 99

/-! ## 6. Nested struct with an array field; scoped borrow into the field -/

mp def mNested (x y : UInt64) : UInt64 := do
  let mut t := { count := x, items := Vector.replicate 4 y : Table }
  let _ := (do let r := &mut t.items[1]; r := r + 10; ())
  t.count := t.count + 1
  t.items[3] := t.count
  t.count + t.items[1] * 2 + t.items[3]

def refMNested (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let count := (x + 1) % m
  let i1 := (y + 10) % m
  UInt64.ofNat ((count + i1 * 2 + count) % m)

/-! ## 7. `put!` and `take!` on `Slots`, which have no checked forms -/

mp def mSlots (x y : UInt64) : UInt64 := do
  let mut s := (Slots.empty 4 : Slots UInt64 4)
  let _ := s.put! 1 y
  let _ := s.put! 3 (x + 1)
  let a := s.take! 1
  let _ := s.put! 1 (a * 2)
  let b := s.take! 3
  let c := s.take! 1
  a + b * 10 + c * 100

def refMSlots (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  UInt64.ofNat ((y + ((x + 1) % m) * 10 + ((y * 2) % m) * 100) % m)

/-! ## 8. Shared reference parameter -/

mp def mShared (x y : UInt64) : UInt64 :=
  let p := { x := x, y := y : Pt }
  sumPt (&p) + sumPt (&p)

def refMShared (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  UInt64.ofNat (2 * ((a[0]!.toNat * 5 + a[1]!.toNat) % m) % m)

/-! ## 9. `a[i]!` under a guard -/

mp def mGuarded (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[3] := y
  if y < 4 then a[y]! else a[3]

def refMGuarded (a : List UInt64) : UInt64 :=
  let arr := [a[0]!, a[0]!, a[0]!, a[1]!]
  if a[1]!.toNat < 4 then arr[a[1]!.toNat]! else a[1]!

/-! ## 10. Prefix sums in place over an array -/

mp def mPrefix (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[0] := a[0] * y
  a[1] := a[1] * (y + 1) + 1
  a[2] := a[2] * (y + 2) + 2
  a[3] := a[3] * (y + 3) + 3
  a[1] := a[1] + a[0]
  a[2] := a[2] + a[1]
  a[3] := a[3] + a[2]
  a[3] ^^^ a[1]

def refMPrefix (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let init := (List.range 4).map fun i => (x * ((y + i) % m) + i) % m
  let init := match init with | [_, a1, a2, a3] => [(x * y) % m, a1, a2, a3] | l => l
  let rec pre : List Nat → Nat → List Nat
    | [], _ => []
    | v :: vs, acc => let s := (v + acc) % m; s :: pre vs s
  let p := match init with | [] => [] | v :: vs => v :: pre vs v
  UInt64.ofNat (p[3]! ^^^ p[1]!)

/-! ## 11. Nested structs, `&mut` of an inner struct, whole-struct copy -/

mp def mSeg (x y : UInt64) : UInt64 := do
  let mut s := { lo := { x := x, y := y : Pt }, hi := { x := y, y := x : Pt } : Seg }
  let before := s
  let _ := bump (&mut s.hi) 1
  s.lo.y := s.hi.x + s.lo.x
  before.hi.x * 2 + before.lo.y + s.lo.y * 3 + s.hi.y

def refMSeg (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  -- hi := (y, x); bump hi 1: hi.x = y+1, hi.y = x*3 + hi.x
  let hix := (y + 1) % m
  let hiy := (x * 3 + hix) % m
  let loy := (hix + x) % m
  UInt64.ofNat ((y * 2 + y + loy * 3 + hiy) % m)

/-! ## 12. A function with `&mut Table` and a checked write, called with raw indices -/

mp def mTable (x y z : UInt64) : UInt64 := do
  let mut t := { count := 0, items := Vector.replicate 4 z : Table }
  let _ := addAt (&mut t) x y
  let _ := addAt (&mut t) y x
  t.count * 100 + t.items[0] + t.items[1] + t.items[2] + t.items[3]

def refMTable (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let set (l : List Nat) (k v : Nat) : List Nat :=
    if k < 4 then (List.range 4).map fun i => if i = k then v else l[i]! else l
  let l0 := [a[2]!.toNat, a[2]!.toNat, a[2]!.toNat, a[2]!.toNat]
  let l1 := set (set l0 a[0]!.toNat a[1]!.toNat) a[1]!.toNat a[0]!.toNat
  UInt64.ofNat ((200 + l1.foldl (· + ·) 0) % m)

/-! ## 13. Struct with fields of several sizes -/

mp def mMixed (x y : UInt64) : UInt64 := do
  let mut v := { a := true, b := x, c := y < x, d := 65535 : Mixed }
  v.a := false
  v.d := 1
  v.b := v.b + y
  let u := v
  v.b := 0
  v.c := !u.c
  u.b + (if u.c then 7 else 0) + (if v.c then 1000 else 0) + v.b

def refMMixed (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  UInt64.ofNat (((x + y) % m + (if y < x then 7 else 1000)) % m)

/-! ## 14. Enum with payloads of different sizes, passed through a call -/

mp def shapeVal (s : Shape) : UInt64 :=
  match s with
  | .dot => 11
  | .span q => q.b + 256
  | .flag f => if f then 1 else 2
  | .pair p => p.x + p.y * 2

mp def mShape (x y : UInt64) : UInt64 :=
  let s := if x % 4 == 0 then Shape.dot
    else if x % 4 == 1 then Shape.span { a := true, b := y : Span }
    else if x % 4 == 2 then Shape.flag (y < x)
    else Shape.pair { x := x, y := y : Pt }
  shapeVal s + shapeVal (Shape.flag (x == y))

def refMShape (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let v :=
    if x % 4 = 0 then 11
    else if x % 4 = 1 then y + 256
    else if x % 4 = 2 then (if y < x then 1 else 2)
    else x + y * 2
  UInt64.ofNat ((v + (if x = y then 1 else 2)) % m)

/-! ## 15. An enum with five variants -/

inductive Op where
  | nop
  | inc (n : UInt64)
  | dbl
  | neg (p : Pt)
  | sel (b : Bool)
deriving Data, Inhabited

mp def applyOp (o : Op) (acc : UInt64) : UInt64 :=
  match o with
  | .nop => acc
  | .inc n => acc + n
  | .dbl => acc * 2
  | .neg p => p.x - acc + p.y
  | .sel b => if b then acc ^^^ 255 else acc + 1

mp def mop (x y : UInt64) : UInt64 :=
  let o := if x % 5 == 0 then Op.nop
    else if x % 5 == 1 then Op.inc y
    else if x % 5 == 2 then Op.dbl
    else if x % 5 == 3 then Op.neg { x := y, y := x : Pt }
    else Op.sel (y < x)
  applyOp o y + applyOp (Op.sel (x == y)) x

def refMOp (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let v :=
    if x % 5 = 0 then y
    else if x % 5 = 1 then (y + y) % m
    else if x % 5 = 2 then (y * 2) % m
    else if x % 5 = 3 then (y + (m - y) + x) % m
    else if y < x then (y ^^^ 255) else (y + 1) % m
  UInt64.ofNat ((v + (if x = y then (x ^^^ 255) else (x + 1) % m)) % m)

/-! ## 16. `Result` from a checked read, matched by the caller -/

mp def lookup (t : &Table) (i : UInt64) : Result UInt64 UInt64 :=
  match t.items[i]? with
  | ok v => ok (v + t.count)
  | err _ => err i

mp def mLookup (x y : UInt64) : UInt64 :=
  let t := { count := x, items := Vector.replicate 4 y : Table }
  match lookup (&t) x with
  | ok v => v
  | err e => e + 1000

def refMLookup (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  UInt64.ofNat (if x < 4 then (y + x) % m else (x + 1000) % m)

/-! ## The pair borrow

`rPair` borrows two elements by a scoped `&mut` and writes through its fields, and the borrow is
held at two addresses. `rPairLoop` writes a field of the pair borrow in a loop, which `compile`
refuses, and `differential refuse` requires an explicit error for it instead of a binary. -/

mp def rPair (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[1] := y
  let i := x % 4
  let j := (x + 1) % 4
  let _ := (do let r := &mut (a.pair! i j); r.fst := r.fst + 10; r.snd := r.snd * 2; ())
  a[0] + a[1] * 3 + a[2] * 5 + a[3] * 7

/-- A loop writing a field of a pair borrow, which is refused because the loop would carry the
pair reference whole. -/
mp def rPairLoop (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[1] := y
  let i := x % 4
  let j := (x + 1) % 4
  let _ := (do
    let r := &mut (a.pair! i j)
    for k in 0...3 do
      r.fst := r.fst + k)
  a[0] + a[1] * 3 + a[2] * 5 + a[3] * 7

def refRPairLoop (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let l := [x, y, x, x]
  let i := x % 4
  let l := (List.range 4).map fun k => if k = i then (l[k]! + 3) % m else l[k]!
  UInt64.ofNat ((l[0]! + l[1]! * 3 + l[2]! * 5 + l[3]! * 7) % m)

mp def swap2 (a : &mut UInt64) (b : &mut UInt64) : Unit := do
  let t := a
  a := b
  b := t
  ()

/-- Two `&mut` arguments of one call, both passed as pointers into `p`. -/
mp def mSwap (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let _ := swap2 (&mut p.x) (&mut p.y)
  p.x * 3 + p.y

def refMSwap (a : List UInt64) : UInt64 :=
  UInt64.ofNat ((a[1]!.toNat * 3 + a[0]!.toNat) % 2 ^ 64)

/-- A slice borrowed and written through, which is lowered as a pointer and a length. -/
mp def rSlice (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  let _ := (do let r := &mut a[1:3]; r[0]! := y; ())
  a[1]

def refRSlice (a : List UInt64) : UInt64 := a[1]!

/-- A shared slice read through, and a mutable one written through twice. -/
mp def mSlice (x y : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  a[2] := y
  let s := (let r := &a[1:3]; r[1]! + r[0]!)
  let _ := (do let r := &mut a[2:4]; r[1]! := r[0]! * 3; r[0]! := s; ())
  a[0] + a[1] * 5 + a[2] * 7 + a[3] * 11

def refMSlice (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let s := (y + x) % m
  let a3 := (y * 3) % m
  UInt64.ofNat ((x + x * 5 + s * 7 + a3 * 11) % m)

def refRPair (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let x := a[0]!.toNat
  let y := a[1]!.toNat
  let l := [x, y, x, x]
  let i := x % 4
  let j := (x + 1) % 4
  let l := (List.range 4).map fun k =>
    if k = i then (l[k]! + 10) % m else if k = j then (l[k]! * 2) % m else l[k]!
  UInt64.ofNat ((l[0]! + l[1]! * 3 + l[2]! * 5 + l[3]! * 7) % m)

/-! ## 18. A call in a loop that takes a loop-carried struct by `&mut` -/

mp def mLoopRef (x y : UInt64) : UInt64 := do
  let mut p := { x := x, y := y : Pt }
  let _ := bump (&mut p) 1
  let _ := bump (&mut p) y
  let _ := bump (&mut p) 3
  p.x + p.y

def refMLoopRef (a : List UInt64) : UInt64 :=
  let m := 2 ^ 64
  let b (s : Nat × Nat) (d : Nat) : Nat × Nat :=
    let x := (s.1 + d) % m
    (x, (s.2 * 3 + x) % m)
  let s := b (b (b (a[0]!.toNat, a[1]!.toNat) 1) a[1]!.toNat) 3
  UInt64.ofNat ((s.1 + s.2) % m)

/-! ## Harness steps -/


/-- A memory test function with its harness step. -/
def tfm1 (name : String) (e : Exp [Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) : TestFn :=
  { name, arity := 1, exp := e, fn, ref }
def tfm2 (name : String) (e : Exp [Ty.u64, Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) : TestFn :=
  { name, arity := 2, exp := e, fn, ref }
def tfm3 (name : String) (e : Exp [Ty.u64, Ty.u64, Ty.u64] Ty.u64) (fn ref : List UInt64 → UInt64) : TestFn :=
  { name, arity := 3, exp := e, fn, ref }

def memFuncs : List TestFn :=
  [tfm2 "mBump" mBump.exp (fun a => (mBump a[0]! a[1]!).run) refMBump,
   tfm2 "mEnum" mEnum.exp (fun a => (mEnum a[0]! a[1]!).run) refMEnum,
   tfm2 "mEnumArr" mEnumArr.exp (fun a => (mEnumArr a[0]! a[1]!).run) refMEnumArr,
   tfm2 "mBorrow" mBorrow.exp (fun a => (mBorrow a[0]! a[1]!).run) refMBorrow,
   tfm2 "mChecked" mChecked.exp (fun a => (mChecked a[0]! a[1]!).run) refMChecked,
   tfm2 "mNested" mNested.exp (fun a => (mNested a[0]! a[1]!).run) refMNested,
   tfm2 "mSlots" mSlots.exp (fun a => (mSlots a[0]! a[1]!).run) refMSlots,
   tfm2 "mShared" mShared.exp (fun a => (mShared a[0]! a[1]!).run) refMShared,
   tfm2 "mGuarded" mGuarded.exp (fun a => (mGuarded a[0]! a[1]!).run) refMGuarded,
   tfm2 "mPrefix" mPrefix.exp (fun a => (mPrefix a[0]! a[1]!).run) refMPrefix,
   tfm2 "mSeg" mSeg.exp (fun a => (mSeg a[0]! a[1]!).run) refMSeg,
   tfm3 "mTable" mTable.exp (fun a => (mTable a[0]! a[1]! a[2]!).run) refMTable,
   tfm2 "mMixed" mMixed.exp (fun a => (mMixed a[0]! a[1]!).run) refMMixed,
   tfm2 "mop" mop.exp (fun a => (mop a[0]! a[1]!).run) refMOp,
   tfm2 "mLookup" mLookup.exp (fun a => (mLookup a[0]! a[1]!).run) refMLookup,
   tfm2 "mLoopRef" mLoopRef.exp (fun a => (mLoopRef a[0]! a[1]!).run) refMLoopRef,
   tfm2 "mShape" mShape.exp (fun a => (mShape a[0]! a[1]!).run) refMShape,
   tfm2 "mSwap" mSwap.exp (fun a => (mSwap a[0]! a[1]!).run) refMSwap,
   tfm2 "rSlice" rSlice.exp (fun a => (rSlice a[0]! a[1]!).run) refRSlice,
   tfm2 "mSlice" mSlice.exp (fun a => (mSlice a[0]! a[1]!).run) refMSlice,
   tfm2 "rPair" rPair.exp (fun a => (rPair a[0]! a[1]!).run) refRPair]

/-- The functions that `compile` must refuse with an error. `rPairLoop` writes a field of a pair
borrow in a loop, which would carry the pair reference whole although it lives at two addresses.
The other refused programs are in `refusedInPlaceFuncs`. -/
def refusedFuncs : List TestFn :=
  [tfm2 "rPairLoop" rPairLoop.exp (fun a => (rPairLoop a[0]! a[1]!).run) refRPairLoop]

end Millipede.Tests.Differential
