import Tests.Differential.SubViewFuncs

/-!
# Differential tests of values in frame slots

A value bound by `let`, a `match` arm or a loop that is never addressed is kept in frame slots
instead of memory. Each function below is an `mp def` over two words whose binders live in
slots. It runs through the whole pipeline and is compared with a reference in plain Lean over
`Nat`.

The functions cover:
* `slMix`, straight-line scalars and `if` expressions;
* `slLoop` and `slBr`, loops whose bodies bind temporaries in slots and read a slot variable of
  the enclosing scope;
* `slAssign`, `let mut` scalars assigned in their slots next to a scalar that a callee updates
  through `&mut`, which therefore stays in memory;
* `slNest`, nested loops whose counters and accumulators are in slots;
* `slRead` and `slFlag`, array elements read straight into slots and a one-byte `Bool`
  accumulator;
* `slCarry`, `let mut` scalars carried by a loop with an early exit and read after the loop;
* `slCall`, call results computed straight into slots;
* `slArm`, `match` arms whose payload binder is in a slot;
* `slArgs`, one-word arguments passed as words into the callee's frame slots;
* `slStruct`, `slRes` and `slSpan`, a two-word struct, a `Result` matched on its tag word and a
  struct with a byte field;
* `slStrOk` and `slStrErr3`, results built into slots that their own payload already occupies, so
  the copy is staged through the scratch slots;
* `slFld`, binders used only through their whole-word fields;
* `slCase`, `case` on enums in slots;
* `slMk`, constructors of several arguments computed straight into their slots;
* `slRet`, results of two and three words returned into the caller's slots.

The slot mutants of `Mutants.lean` each break one of these features, and the self-test of
`scripts/differential.sh` requires every function that `slotFor` lists for a mutant to fail
under it.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

mp def slMix (x y : UInt64) : UInt64 :=
  let a := x * 3 + 1
  let b := y ^^^ a
  let c := if a < b then b - a else a - b
  let d := (c >>> 3) + (b &&& 255)
  let e := if d == c then a else d * 5
  e + (c ^^^ (a <<< 7))

def refSlMix (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := W (x * 3 + 1)
  let b := y ^^^ a
  let c := if a < b then b - a else a - b
  let d := W ((c >>> 3) + b % 256)
  let e := if d = c then a else W (d * 5)
  UInt64.ofNat (W (e + (c ^^^ W (a * 128))))

mp def slLoop (x y : UInt64) : UInt64 := do
  let k := (y &&& 7) + 1
  let mut r := x
  for i in 0...12 do
    let t := (r >>> k) ^^^ i
    let u := if (t &&& 1) == 1 then t * 3 else t + k
    r := r + u
  r ^^^ k

def refSlLoop (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let k := y % 8 + 1
  let r := (List.range 12).foldl (fun acc i =>
    let t := (acc >>> k) ^^^ i
    let u := if t % 2 = 1 then W (t * 3) else W (t + k)
    W (acc + u)) x
  UInt64.ofNat (r ^^^ k)

mp def slAssign (x y : UInt64) : UInt64 := do
  let mut a := x + 5
  let mut m := y
  a := a * 7
  let _ := inc (&mut m) a
  a := a ^^^ m
  let b := if a > m then a - m else m - a
  a := b + (a &&& 1023)
  let _ := inc (&mut m) b
  a ^^^ (m <<< 1)

def refSlAssign (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a1 := W (W (x + 5) * 7)
  let m1 := W (y + a1)
  let a2 := a1 ^^^ m1
  let b := if a2 > m1 then a2 - m1 else m1 - a2
  let a3 := W (b + a2 % 1024)
  let m2 := W (m1 + b)
  UInt64.ofNat (a3 ^^^ W (m2 * 2))

mp def slBr (x y : UInt64) : UInt64 := do
  let mut acc := y
  for i in 0...10 do
    let v := if ((x >>> i) &&& 1) == 1 then
        let p := acc * 3
        p + i
      else
        let q := acc ^^^ x
        q >>> 1
    acc := v + 1
  acc

def refSlBr (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat ((List.range 10).foldl (fun acc i =>
    let v := if (x >>> i) % 2 = 1 then W (W (acc * 3) + i) else (acc ^^^ x) >>> 1
    W (v + 1)) y)

/-! ### Loop counters and accumulators in slots, and places read straight into a slot -/

mp def slNest (x y : UInt64) : UInt64 := do
  let mut acc := x
  for i in 0...6 do
    let mut inner := acc ^^^ i
    for j in 0...5 do
      inner := (inner * 3 + j) ^^^ (y >>> j)
    acc := inner + i
  acc

def refSlNest (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat ((List.range 6).foldl (fun acc i =>
    let inner := (List.range 5).foldl (fun a j => W (a * 3 + j) ^^^ (y >>> j)) (acc ^^^ i)
    W (inner + i)) x)

mp def slRead (x y : UInt64) : UInt64 := do
  let a := mkArr x y
  let mut acc := y
  for i in 0...8 do
    let v := a[i]
    let w := a[7 - i]!
    acc := (acc ^^^ v) * 5 + (w >>> 3)
  acc

def refSlRead (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := arrR x y
  UInt64.ofNat ((List.range 8).foldl (fun acc i =>
    W (W ((acc ^^^ a[i]!) * 5) + (a[7 - i]! >>> 3))) y)

mp def slFlag (x y : UInt64) : UInt64 := do
  let mut f := false
  for i in 0...16 do
    f := if ((x >>> i) &&& 1) == ((y >>> i) &&& 1) then f == false else f
  if f then x + y else x ^^^ y

def refSlFlag (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let f := (List.range 16).foldl (fun b i =>
    if (x >>> i) % 2 = (y >>> i) % 2 then !b else b) false
  UInt64.ofNat (if f then W (x + y) else x ^^^ y)

/-! ### Carried scalars, call results and match arms in slots -/

mp def slCarry (x y : UInt64) : UInt64 := do
  let mut s := x
  let mut t := y ^^^ 3
  for i in 0...9 do
    if (t &&& 1023) == 5 then break
    if ((s >>> i) &&& 1) == 1 then
      s := s * 5 + t
      ()
    else
      t := t + (s >>> 2) + i
      ()
  s ^^^ (t <<< 3)

def refSlCarry (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let rec go : Nat → Nat → Nat → Nat → Nat × Nat
    | 0, _, s, t => (s, t)
    | k + 1, i, s, t =>
      if t % 1024 = 5 then (s, t)
      else if (s >>> i) % 2 = 1 then go k (i + 1) (W (W (s * 5) + t)) t
      else go k (i + 1) s (W (W (t + (s >>> 2)) + i))
  let (s, t) := go 9 0 x (y ^^^ 3)
  UInt64.ofNat (s ^^^ W (t * 8))

mp def slCall (x y : UInt64) : UInt64 := do
  let a := stepMix x y
  let b := if a > y then stepMix a 3 else checked a y
  let mut c := b
  for i in 0...4 do
    c := stepMix c i ^^^ a
  c + (a >>> 5)

def refSlCall (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let sm (acc i : Nat) : Nat := W (W ((acc ^^^ (acc >>> 7)) * 3) + i)
  let a := sm x y
  let b := if a > y then sm a 3 else (if y = 0 then 101 else a / y)
  let c := (List.range 4).foldl (fun acc i => sm acc i ^^^ a) b
  UInt64.ofNat (W (c + (a >>> 5)))

mp def slArm (x y : UInt64) : UInt64 :=
  let r := match checkedDiv x (y &&& 7) with
    | ok q => q * 3 + (q >>> 1)
    | err e => (e + x) ^^^ (e <<< 2)
  r + y

def refSlArm (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let d := y % 8
  let r := if d = 0 then W (1 + x) ^^^ 4 else W (W ((x / d) * 3) + (x / d) / 2)
  UInt64.ofNat (W (r + y))

mp def wsub (a b c : UInt64) : UInt64 := (a * 3 + b) ^^^ (c >>> 1)

mp def wmix (a b : UInt64) : UInt64 := do
  let mut m := b
  let _ := inc (&mut m) a
  m ^^^ (a <<< 2)

mp def slArgs (x y : UInt64) : UInt64 := do
  let mut z := y + 1
  let _ := inc (&mut z) x
  let a := wsub x 7 z
  let b := wsub a y 5
  wmix a b + wsub z b a

def refSlArgs (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let wsub (a b c : Nat) : Nat := W (W (a * 3) + b) ^^^ (c >>> 1)
  let wmix (a b : Nat) : Nat := W (b + a) ^^^ W (a * 4)
  let z := W (W (y + 1) + x)
  let a := wsub x 7 z
  let b := wsub a y 5
  UInt64.ofNat (W (wmix a b + wsub z b a))

/-! ### Multi-word values in slots -/

structure SPt where
  x : UInt64
  y : UInt64
deriving Data, Inhabited

/-- A struct with a byte field, which is a sub-word field. Its values are kept whole in slots. -/
structure SSpan where
  a : Bool
  b : UInt64
deriving Data, Inhabited

mp def spMk (x y : UInt64) : SPt := { x := x ^^^ 5, y := y + 7 : SPt }

mp def spSum (p : SPt) (k : UInt64) : UInt64 := p.x * 3 + p.y + k

mp def slStruct (x y : UInt64) : UInt64 := do
  let mut p := spMk x y
  p.x := p.x * 3 + p.y
  let q := p.y + p.x
  p.y := q ^^^ (p.x >>> 2)
  let s := spSum p 1
  s + p.x + p.y

def refSlStruct (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let px := x ^^^ 5
  let py := W (y + 7)
  let px := W (W (px * 3) + py)
  let q := W (py + px)
  let py := q ^^^ (px >>> 2)
  let s := W (W (W (px * 3) + py) + 1)
  UInt64.ofNat (W (W (s + px) + py))

mp def slRes (x y : UInt64) : UInt64 :=
  let r : Result UInt64 UInt64 := if (y &&& 3) == 0 then err (x + 1) else ok (x / (y &&& 3))
  let t := match r with
    | ok q => q * 5 + 1
    | err e => e ^^^ 77
  t + y

def refSlRes (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let t := if y % 4 = 0 then W (x + 1) ^^^ 77 else W (W ((x / (y % 4)) * 5) + 1)
  UInt64.ofNat (W (t + y))

mp def ssMk (x : UInt64) : SSpan := { a := (x &&& 1) == 1, b := x * 7 : SSpan }

mp def ssUse (s : SSpan) (k : UInt64) : UInt64 := if s.a then s.b + k else s.b ^^^ k

mp def slSpan (x y : UInt64) : UInt64 :=
  let s := ssMk x
  let t := ssMk y
  ssUse s y + ssUse t x

def refSlSpan (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let use (v k : Nat) : Nat := if v % 2 = 1 then W (W (v * 7) + k) else W (v * 7) ^^^ k
  UInt64.ofNat (W (use x y + use y x))


/-! ### Straddling copies and binders used only through fields -/

structure ST3 where
  a : UInt64
  b : UInt64
  c : UInt64
deriving Data, Inhabited

mp def st3Mk (x y : UInt64) : ST3 := { a := x, b := y ^^^ 77, c := x + y : ST3 }

/-- `ok p` computed into the slots of `r`, where `p` is bound inside the bound term of `r` and so
sits at the first slot of `r`. Since `p` straddles the payload's slots, the copy goes through the
scratch slots. -/
mp def slStrOk (x y : UInt64) : UInt64 :=
  let r : Result UInt64 SPt :=
    let p := spMk x y
    ok p
  match r with
    | ok q => q.x * 7 + q.y + (if q.x == 0 then 0 else 1)
    | err e => e

def refSlStrOk (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let px := x ^^^ 5
  let py := W (y + 7)
  UInt64.ofNat (W (W (W (px * 7) + py) + (if px = 0 then 0 else 1)))

/-- `err p` with a three-word payload, which makes a four-word `Result` in slots that is copied
whole and matched. -/
mp def slStrErr3 (x y : UInt64) : UInt64 :=
  let r : Result ST3 UInt64 :=
    let p := st3Mk x y
    err p
  let s := r
  match s with
    | ok q => q
    | err e => e.a * 3 + e.b * 5 + e.c * 7

def refSlStrErr3 (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (W (W (W (x * 3) + W ((y ^^^ 77) * 5)) + W (W (x + y) * 7)))

/-- A `let`-bound struct and a `match` arm's struct payload that are used only through their
whole-word fields. Both stay in slots, and their fields are read as slots. -/
mp def slFld (x y : UInt64) : UInt64 :=
  let p := spMk x y
  let r : Result UInt64 SPt := if (y &&& 1) == 0 then err (x + 9) else ok (spMk y x)
  let t := match r with
    | ok q => q.x * 7 + q.y
    | err e => e ^^^ 1234
  p.x * 7 + p.y + t

def refSlFld (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let t := if y % 2 = 0 then W (x + 9) ^^^ 1234 else W (W ((y ^^^ 5) * 7) + W (x + 7))
  UInt64.ofNat (W (W (W ((x ^^^ 5) * 7) + W (y + 7)) + t))

/-! ### `case` on enums in slots -/

inductive SCmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving Data, Inhabited

inductive SOpt where
  | none
  | some (v : UInt64)
deriving Data, Inhabited

mp def scMk (x y : UInt64) : SCmd :=
  if x % 3 == 0 then SCmd.add y else if x % 3 == 1 then SCmd.mul (y ^^^ 3) else SCmd.stop

/-- `case` on scrutinees in slots, of a three-variant and a two-variant enum. The tag is the low byte
of the first slot and the payload is in the next slot. -/
mp def slCase (x y : UInt64) : UInt64 :=
  let c := scMk x y
  let o := if (y &&& 1) == 0 then SOpt.none else SOpt.some (x + 3)
  let a := match c with
    | .stop => 7
    | .add n => n + 1
    | .mul n => n * 2
  let b := match o with
    | .none => a ^^^ 99
    | .some v => v * 5 + a
  b + a

def refSlCase (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := if x % 3 = 0 then W (y + 1) else if x % 3 = 1 then W ((y ^^^ 3) * 2) else 7
  let b := if y % 2 = 0 then a ^^^ 99 else W (W (W (x + 3) * 5) + a)
  UInt64.ofNat (W (b + a))

/-! ### Constructors computed into slots -/

/-- Constructors of several arguments computed straight into their slots. They build a struct whose
argument temporaries are already in its own slots, a struct from the fields of another, tagged
variants, and a struct whose second argument sits in its first slot, which is staged through the
scratch slots. -/
mp def slMk (x y : UInt64) : UInt64 :=
  let p := { x := x + 1, y := y ^^^ x : SPt }
  let q := { x := p.y, y := p.x : SPt }
  let c := if x % 2 == 0 then SCmd.add q.x else SCmd.mul p.y
  let r := match c with
    | .stop => 0
    | .add n => n
    | .mul n => n * 3
  let s :=
    let a := y * 2
    { x := x, y := a : SPt }
  q.x * 5 + q.y + r + s.x * 7 + s.y

def refSlMk (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let px := W (x + 1)
  let py := y ^^^ x
  let r := if x % 2 = 0 then py else W (py * 3)
  UInt64.ofNat (W (W (W (W (W (py * 5) + px) + r) + W (x * 7)) + W (y * 2)))

/-! ### Multi-word results returned as words -/

mp def rRes (x y : UInt64) : Result UInt64 SPt :=
  if y == 0 then err (x + 17) else ok { x := x / y, y := x % y : SPt }

mp def spBump (p : &mut SPt) (d : UInt64) : Unit := do
  p.x := p.x + d
  ()

/-- A struct, a `Result` with a struct payload and an enum, of two and three words, returned straight
into the caller's slots. One more result goes to a borrowed binder in memory, so its words pass
through the scratch slots and are stored. -/
mp def slRet (x y : UInt64) : UInt64 := do
  let p := spMk x y
  let r := rRes x (y &&& 7)
  let c := scMk y x
  let mut q := spMk y x
  let _ := spBump (&mut q) 3
  let a := match r with
    | ok s => s.x * 3 + s.y
    | err e => e
  let b := match c with
    | .stop => 5
    | .add n => n
    | .mul n => n + 1
  p.x + p.y * 7 + a + b * 11 + q.x * 13 + q.y

def refSlRet (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let d := y % 8
  let a := if d = 0 then W (x + 17) else W (W ((x / d) * 3) + x % d)
  let b := if y % 3 = 0 then x else if y % 3 = 1 then W ((x ^^^ 3) + 1) else 5
  UInt64.ofNat (W (W (W (W (W (x ^^^ 5) + W (W (y + 7) * 7)) + a) + W (b * 11)) +
    W (W ((y ^^^ 5) + 3) * 13)) + W (x + 7))


/-- Whether the binder of a term's first `let` lives in slots. -/
def topSlotBind {Γ : List Ty} {t : Ty} : Exp Γ t → Bool
  | .let_ _ e₂ => e₂.slotBind
  | _ => false

/-- Whether the `err` and `ok` binders of the first `match` along the `let`s live in slots. -/
def firstArms {Γ : List Ty} {t : Ty} : Exp Γ t → Option (Bool × Bool)
  | .match_ _ eE eO => some (eE.slotBind, eO.slotBind)
  | .let_ e₁ e₂ => (firstArms e₁).orElse fun _ => firstArms e₂
  | _ => none

/-- The functions of this file, all of which `compile` accepts. -/
def slotFuncs : List TestFn :=
  [tfm2 "slMix" slMix.exp (fun a => (slMix a[0]! a[1]!).run) refSlMix,
   tfm2 "slLoop" slLoop.exp (fun a => (slLoop a[0]! a[1]!).run) refSlLoop,
   tfm2 "slAssign" slAssign.exp (fun a => (slAssign a[0]! a[1]!).run) refSlAssign,
   tfm2 "slBr" slBr.exp (fun a => (slBr a[0]! a[1]!).run) refSlBr,
   tfm2 "slNest" slNest.exp (fun a => (slNest a[0]! a[1]!).run) refSlNest,
   tfm2 "slRead" slRead.exp (fun a => (slRead a[0]! a[1]!).run) refSlRead,
   tfm2 "slFlag" slFlag.exp (fun a => (slFlag a[0]! a[1]!).run) refSlFlag,
   tfm2 "slCarry" slCarry.exp (fun a => (slCarry a[0]! a[1]!).run) refSlCarry,
   tfm2 "slCall" slCall.exp (fun a => (slCall a[0]! a[1]!).run) refSlCall,
   tfm2 "slArm" slArm.exp (fun a => (slArm a[0]! a[1]!).run) refSlArm,
   tfm2 "slArgs" slArgs.exp (fun a => (slArgs a[0]! a[1]!).run) refSlArgs,
   tfm2 "slStruct" slStruct.exp (fun a => (slStruct a[0]! a[1]!).run) refSlStruct,
   tfm2 "slRes" slRes.exp (fun a => (slRes a[0]! a[1]!).run) refSlRes,
   tfm2 "slSpan" slSpan.exp (fun a => (slSpan a[0]! a[1]!).run) refSlSpan,
   tfm2 "slStrOk" slStrOk.exp (fun a => (slStrOk a[0]! a[1]!).run) refSlStrOk,
   tfm2 "slStrErr3" slStrErr3.exp (fun a => (slStrErr3 a[0]! a[1]!).run) refSlStrErr3,
   tfm2 "slFld" slFld.exp (fun a => (slFld a[0]! a[1]!).run) refSlFld,
   tfm2 "slCase" slCase.exp (fun a => (slCase a[0]! a[1]!).run) refSlCase,
   tfm2 "slMk" slMk.exp (fun a => (slMk a[0]! a[1]!).run) refSlMk,
   tfm2 "slRet" slRet.exp (fun a => (slRet a[0]! a[1]!).run) refSlRet]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (0xFFFFFFFFFFFFFFFF, 0x5555),
    (0x123456789ABCDEF, 0xFFFFFFFFFFFFFFFF)].all fun (x, y) =>
  slotFuncs.all fun f => f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]
-- the references are not constant
#guard refSlAssign [3, 4] != refSlAssign [4, 3]
#guard refSlBr [5, 9] != refSlBr [4, 9]

#guard slotFuncs.all fun f => f.exp.memOk
-- Every function has binders in slots, so its frame grows beyond the scratch slots, and the
-- borrowed `m` of `slAssign` does not push the other binders into memory.
#guard slotFuncs.all fun f => 0 < f.exp.slotNeed
#guard 2 ≤ slAssign.exp.slotNeed
#guard refSlNest [3, 4] != refSlNest [4, 3]
-- the enum scrutinees of `slCase` live in slots
#guard topSlotBind slCase.exp
#guard refSlCase [3, 5] != refSlCase [4, 5]
-- the struct of `slMk` is computed straight into its slots
#guard match slMk.exp with
  | .let_ e₁ e₂ => e₂.slotBind && e₁.Conf (.word Flat.FR)
  | _ => false
#guard refSlMk [3, 5] != refSlMk [5, 3]
#guard refSlRet [3, 5] != refSlRet [5, 3]
#guard refSlRead [3, 4] != refSlRead [4, 3]
#guard refSlFlag [3, 5] != refSlFlag [3, 6]
-- both counters and both accumulators of the nested loops live in slots
#guard 4 ≤ slNest.exp.slotNeed
-- the carried `let mut` scalars and the loop's counter live in slots, the call results go
-- straight to slots, and so does the payload binder of the `ok` arm
#guard 3 ≤ slCarry.exp.slotNeed
#guard 3 ≤ slCall.exp.slotNeed
#guard 2 ≤ slArm.exp.slotNeed
#guard refSlCarry [3, 4] != refSlCarry [4, 3]
#guard refSlCall [3, 4] != refSlCall [4, 3]
#guard refSlArm [3, 4] != refSlArm [3, 5]
-- the three parameters of `wsub` and the two of `wmix` are word parameters; the borrowed `m` of
-- `wmix` is a copy of `b`
#guard (List.range 3).all fun j => wsub.exp.wordParam j
#guard wmix.exp.wordParam 0 && wmix.exp.wordParam 1
#guard refSlArgs [3, 4] != refSlArgs [4, 3]

-- the struct, the `Result` and the struct with a byte field live in slots
#guard (⟨SPt⟩ : Ty).slotTy && (⟨SSpan⟩ : Ty).slotTy && (Ty.result .u64 .u64).slotTy
#guard Ty.slotSum .u64 .u64
#guard topSlotBind slStruct.exp
#guard topSlotBind slRes.exp
#guard 4 ≤ slSpan.exp.slotNeed
#guard refSlStruct [3, 4] != refSlStruct [4, 3]
#guard refSlRes [3, 4] != refSlRes [3, 5]
#guard refSlSpan [3, 4] != refSlSpan [4, 4]
-- the `Result` binders `r` of the straddling copies live in slots, and so do the struct and the
-- arm binders that are used only through their fields
#guard (⟨ST3⟩ : Ty).slotTy && (Ty.result ⟨ST3⟩ .u64).slotTy && Ty.slotSum ⟨ST3⟩ .u64
#guard topSlotBind slStrOk.exp && topSlotBind slStrErr3.exp && topSlotBind slFld.exp
#guard firstArms slFld.exp == some (true, true)
#guard firstArms slStrOk.exp == some (true, true)
#guard refSlStrOk [3, 4] != refSlStrOk [4, 3]
#guard refSlStrErr3 [3, 4] != refSlStrErr3 [4, 3]
#guard refSlFld [3, 4] != refSlFld [3, 5]

end Millipede.Tests.Differential
