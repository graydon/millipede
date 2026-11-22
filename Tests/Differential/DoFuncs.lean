import Tests.Differential.LoopFuncs

/-!
# Differential tests of the `do` notation's jumps and ranges

Each function is an `mp def` over two words. It runs through the whole pipeline on both targets
and is compared with a reference in plain Lean, which folds over `List.range` with an explicit
"stopped" state. The functions use `break`, `continue` and `return` inside and outside loops and
nested loops, lower and inclusive bounds known only at run time, and statement `if`s and `match`
statements that are joined before the rest of the block. Some branches shadow carried variables,
and some joins write fields, elements and fields of elements.

The suite is shown to catch bugs in the translation of the `do` notation. `mp_seeded "bug" fM in
mp def f …` elaborates `f` and also a copy `fM` translated with the named bug seeded. The bugs
ignore a `break`, let a `continue` fall through, lose a `return`'s value or let it fall through,
put an inclusive bound off by one, ignore the lower bound, lose the variables or the jump flag of
a joined statement `if`, leave a shadowing binder unrenamed, leave a leading exit test unnegated,
lose the accumulator's final value, and let an inner `break` leave the outer loop.
`differential domut` evaluates the denotation of each seeded copy on the generated inputs and
checks that it disagrees with the reference.
-/

namespace Millipede.Tests.Differential

open Millipede

set_option mp.autoSafe false

/-- A reference loop, which runs `f` over `lo, …, hi - 1` on a state until `f` answers "stop". -/
def loopR {σ : Type} (lo hi : Nat) (s : σ) (f : Nat → σ → σ × Bool) : σ :=
  (List.range (hi - lo)).foldl (fun (st : σ × Bool) k =>
    if st.2 then st else f (lo + k) st.1) (s, false) |>.1

/-- `mp_seeded "bug" fM, … in mp def f …` defines `f` and, for each seeded bug, a copy `fM`
translated with that bug and without a normal form. -/
syntax "mp_seeded " (str ident),+ " in " command : command

macro_rules
  | `(mp_seeded $[$ms $ids],* in $c:command) => do
    let mut out : Array Lean.Syntax := #[c]
    for (m, id) in ms.zip ids do
      let c' : Lean.TSyntax `command := ⟨c.raw.setArg 3 id⟩
      out := out.push (← `(set_option mp.selftest.doMutant $m in set_option mp.normalForm false in
        $c':command))
    return Lean.mkNullNode out

/-! ## The functions -/

mp_seeded "break-ignored" dBreakM in
/-- A `break` in the middle of the body, with two carried variables. -/
mp def dBreak (x y : UInt64) : UInt64 := do
  let mut s := 0
  let mut c := 0
  for i in 0...20 do
    s := s + (x >>> i) % 7
    if s > y % 50 then break
    c := c + 1
  s * 1000 + c

def refDBreak (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (s, c) := loopR 0 20 (0, 0) fun i (s, c) =>
    let s := s + (x >>> i) % 7
    if s > y % 50 then ((s, c), true) else ((s, c + 1), false)
  UInt64.ofNat (W (s * 1000 + c))

mp_seeded "continue-falls-through" dContM in
/-- Two `continue`s with three carried variables. -/
mp def dCont (x y : UInt64) : UInt64 := do
  let mut a := x
  let mut b := y
  let mut n := 0
  for i in 0...16 do
    if (x >>> i) % 3 == 0 then continue
    a := a * 3 + i
    if (y >>> i) % 2 == 1 then continue
    b := b ^^^ a
    n := n + 1
  a + b * 7 + n

def refDCont (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (a, b, n) := loopR 0 16 (x, y, 0) fun i (a, b, n) =>
    if (x >>> i) % 3 = 0 then ((a, b, n), false) else
    let a := W (a * 3 + i)
    if (y >>> i) % 2 = 1 then ((a, b, n), false) else ((a, b ^^^ a, n + 1), false)
  UInt64.ofNat (W (a + W (b * 7) + n))

mp_seeded "return-lost" dRetM in
/-- A `return` from inside an inner loop, which stops both loops, and then a tail `return`. -/
mp def dRet (x y : UInt64) : UInt64 := do
  for i in 0...8 do
    for j in 0...8 do
      if (x >>> (i * 8 + j)) % 16 == y % 16 then return i * 8 + j + 1
  return 0

def refDRet (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  match (List.range 64).find? fun k => (x >>> k) % 16 == y % 16 with
  | some k => UInt64.ofNat (k + 1)
  | none => 0

mp_seeded "return-falls-through" dRetMidM, "lo-ignored" dRetMidM2 in
/-- A non-zero lower bound and an inclusive bound, `return` in the middle of the body, and
statements after the loop with a `return` that is not in a loop. -/
mp def dRetMid (x y : UInt64) : UInt64 := do
  let mut s := x
  for i in 2...=9 do
    s := s * 5 + i
    if s % 11 == y % 11 then return s + i
  if s > y then return s - y
  s + y

def refDRetMid (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (s, r) := loopR 2 10 (x, none) fun i (s, _) =>
    let s := W (s * 5 + i)
    if s % 11 = y % 11 then ((s, some (W (s + i))), true) else ((s, none), false)
  match r with
  | some v => UInt64.ofNat v
  | none => UInt64.ofNat (if s > y then s - y else W (s + y))

/-- A run-time lower bound and the upper bound `min y 12`, whose static cap is 12. -/
mp def dLo (x y : UInt64) : UInt64 := do
  let lo := x % 10
  let mut s := 1
  for i in lo...min y 12 do
    s := s * 3 + i
  s

def refDLo (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (loopR (x % 10) (min y 12) 1 fun i s => (W (s * 3 + i), false))

mp_seeded "incl-off-by-one" dLoInclM in
/-- An inclusive run-time bound with a run-time lower bound, left by a leading `if … then break`. -/
mp def dLoIncl (x y : UInt64) : UInt64 := do
  let mut s := 0
  for i in x % 7...=min (y % 20) 15 do
    if s > 1000 then break
    s := s * 2 + i
  s

def refDLoIncl (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (loopR (x % 7) (min (y % 20) 15 + 1) 0 fun i s =>
    if s > 1000 then (s, true) else (W (s * 2 + i), false))

/-- The sum of a slice's cells from `lo` up to the slice's length, which is a run-time bound with
a static cap. -/
mp def dSumFrom (s : &[UInt64; 8]) (lo : UInt64) : UInt64 := do
  let mut acc := 0
  for i in lo...s.len do
    acc := acc * 3 + s[i]!
  acc

mp def dSlice (x y : UInt64) : UInt64 := do
  let a := mkArr x y
  let n := y % 9
  dSumFrom (&a[0..n]) (x % 5)

def refDSlice (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := arrR x y
  UInt64.ofNat (loopR (x % 5) (y % 9) 0 fun i acc => (W (acc * 3 + a[i]!), false))

/-- Nested loops with a `continue` in the outer one and a `break` in the inner one that is not at
the start of the body. -/
mp def dNest (x y : UInt64) : UInt64 := do
  let mut t := 0
  for i in 1...6 do
    if (x >>> i) % 2 == 0 then continue
    for j in 0...10 do
      t := t * 3 + j
      if t % 13 == y % 13 then break
      t := t + i
  t

def refDNest (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (loopR 1 6 0 fun i t =>
    if (x >>> i) % 2 = 0 then (t, false) else
    (loopR 0 10 t fun j t =>
      let t := W (t * 3 + j)
      if t % 13 = y % 13 then (t, true) else (W (t + i), false), false))

mp_seeded "join-lost" dJoinM in
/-- Three statement `if`s in a row, which write two variables and are joined before the rest of the
block. One of them has no `else`. -/
mp def dJoin (x y : UInt64) : UInt64 := do
  let mut a := x
  let mut b := y
  if a % 3 == 0 then
    a := a / 3
    b := b + 1
  else
    a := a * 5 + 1
  if b % 2 == 0 then b := b / 2 else b := b * 3 + a
  if a > b then a := a - b
  if a % 7 == b % 7 then a := a + 1
  a * 3 + b

def refDJoin (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (a, b) := if x % 3 = 0 then (x / 3, W (y + 1)) else (W (x * 5 + 1), y)
  let b := if b % 2 = 0 then b / 2 else W (W (b * 3) + a)
  let a := if a > b then a - b else a
  let a := if a % 7 = b % 7 then W (a + 1) else a
  UInt64.ofNat (W (W (a * 3) + b))

mp_seeded "jump-join-lost" dJumpJoinM in
/-- Statement `if`s with two branches that continue and one that jumps by `continue`, `break` or
`return`. They are joined with a jump flag before the rest of the body. -/
mp def dJumpJoin (x y : UInt64) : UInt64 := do
  let mut s := 0
  let mut t := 0
  for i in 0...12 do
    if (x >>> i) % 3 == 0 then s := s + i else if (y >>> i) % 3 == 1 then t := t + i else continue
    if (x >>> (i + 1)) % 5 == 0 then break else if (y >>> i) % 2 == 0 then s := s * 3 else t := t + 1
    if s > y % 1000 + 50 then return s * 2 + t else if t % 2 == 0 then t := t + 3 else s := s + 1
    s := s + t
  s * 7 + t

def refDJumpJoin (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let ((s, t), r) := loopR 0 12 ((0, 0), (none : Option Nat)) fun i ((s, t), _) =>
    if !((x >>> i) % 3 = 0) && !((y >>> i) % 3 = 1) then (((s, t), none), false) else
    let (s, t) := if (x >>> i) % 3 = 0 then (W (s + i), t) else (s, W (t + i))
    if (x >>> (i + 1)) % 5 = 0 then (((s, t), none), true) else
    let (s, t) := if (y >>> i) % 2 = 0 then (W (s * 3), t) else (s, W (t + 1))
    if s > y % 1000 + 50 then (((s, t), some (W (W (s * 2) + t))), true) else
    let (s, t) := if t % 2 = 0 then (s, W (t + 3)) else (W (s + 1), t)
    (((W (s + t), t), none), false)
  match r with
  | some v => UInt64.ofNat v
  | none => UInt64.ofNat (W (W (s * 7) + t))

/-- Statement `if`s outside a loop, with two branches that continue and one that returns. The value
of the `return` is kept in a variable until the join. -/
mp def dRetJoin (x y : UInt64) : UInt64 := do
  let mut a := x
  if a % 3 == 0 then a := a / 3 else if a % 3 == 1 then a := a + y else return 1
  if y % 4 == 0 then return a + 2 else if y % 4 == 1 then a := a * 2 else a := a + 7
  if a > y then a := a - y else return a
  a * 3

def refDRetJoin (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  if x % 3 = 2 then 1 else
  let a := if x % 3 = 0 then x / 3 else W (x + y)
  if y % 4 = 0 then UInt64.ofNat (W (a + 2)) else
  let a := if y % 4 = 1 then W (a * 2) else W (a + 7)
  if a > y then UInt64.ofNat (W ((a - y) * 3)) else UInt64.ofNat a

/-- `n` reduced to a word, since the references compute on naturals. -/
def W' (n : Nat) : Nat := n % 2 ^ 64

/-- An inner loop left by a leading `break`, while the outer loop goes on. -/
mp def dNestBrk (x y : UInt64) : UInt64 := do
  let mut t := y % 3
  for i in 0...5 do
    for j in 0...5 do
      if j == (x + i) % 5 then break
      t := t + 1
    t := t * 2 + i
  t

def refDNestBrk (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  UInt64.ofNat (loopR 0 5 (y % 3) fun i t =>
    let t := loopR 0 5 t fun j t => if j = W' (x + i) % 5 then (t, true) else (W' (t + 1), false)
    (W' (t * 2 + i), false))

/-- A variable assigned in one branch and shadowed by a `let mut` in the other, followed by a long
rest after the join. -/
mp def dShJoin (x y : UInt64) : UInt64 := do
  let mut a := x % 1000
  let mut b := y % 1000
  if x % 2 == 0 then
    a := a + 1
  else
    let mut a := 100
    a := a + 5
    b := b + a
  let c := a + b
  let d := c * 3
  let e := d + a
  let f := e * b
  let g := f + c
  let h := g + d
  if h % 2 == 0 then a := a + 1
  a * 1000000 + b * 1000 + h % 1000

def refDShJoin (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (a, b) := if x % 2 = 0 then (x % 1000 + 1, y % 1000) else (x % 1000, y % 1000 + 105)
  let c := a + b
  let d := c * 3
  let e := d + a
  let f := e * b
  let g := f + c
  let h := g + d
  let a := if h % 2 = 0 then a + 1 else a
  UInt64.ofNat (a * 1000000 + b * 1000 + h % 1000)

mp_seeded "bind-name" dShNestM in
/-- Nested shadowing of a carried variable in branches inside a loop, where the carried `s` must not
be captured. -/
mp def dShNest (x y : UInt64) : UInt64 := do
  let mut s := 1
  let mut t := 0
  for i in 0...6 do
    if (x >>> i) % 2 == 0 then
      let mut s := 50 + i
      if (y >>> i) % 2 == 0 then
        let s := s * 2
        t := t + s
      else
        s := s + 3
        t := t + s
    else
      s := s + i
    t := t + s
  s * 100000 + t

def refDShNest (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (s, t) := loopR 0 6 (1, 0) fun i (s, t) =>
    let t := if (x >>> i) % 2 = 0 then
        (if (y >>> i) % 2 = 0 then t + (50 + i) * 2 else t + (50 + i + 3))
      else t
    let s := if (x >>> i) % 2 = 0 then s else s + i
    ((s, t + s), false)
  UInt64.ofNat (s * 100000 + t)

structure DRP where
  x : UInt64
  y : UInt64
deriving Data, Inhabited

structure DRQ where
  p : DRP
  z : UInt64
deriving Data, Inhabited


/-- A join whose branches write different places: a field, a field of a field, an element, a
variable. -/
mp def dJoinPlaces (x y : UInt64) : UInt64 := do
  let mut q : DRQ := { p := { x := x % 100, y := y % 100 }, z := 7 }
  let mut a : Arr UInt64 4 := #v[1, 2, 3, 4]
  let mut v := 0
  if x % 3 == 0 then
    q.p.x := q.p.x + 11
    a[1] := 50
  else if x % 3 == 1 then
    q.z := q.z + y % 10
    v := 9
  else
    a[(y % 4)]! := a[(y % 4)]! + 100
    q.p.y := 0
  let r1 := q.p.x + q.p.y
  let r2 := r1 + q.z
  let r3 := r2 + a[0] + a[1] + a[2] + a[3]
  let r4 := r3 * 2 + v
  let r5 := r4 + 1
  r5 * 10 + a[(x % 4)]! % 10

def refDJoinPlaces (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (px, py, z, a, v) : Nat × Nat × Nat × List Nat × Nat :=
    if x % 3 = 0 then (x % 100 + 11, y % 100, 7, [1, 50, 3, 4], 0)
    else if x % 3 = 1 then (x % 100, y % 100, 7 + y % 10, [1, 2, 3, 4], 9)
    else (x % 100, 0, 7, ([1, 2, 3, 4] : List Nat).set (y % 4) ([1, 2, 3, 4][y % 4]! + 100), 0)
  let r3 := px + py + z + a.sum
  UInt64.ofNat ((r3 * 2 + v + 1) * 10 + a[x % 4]! % 10)

/-- `a[i].f := e` in a loop, in a statement `if`, then a second loop reading the fields. -/
mp def dElemField (x y : UInt64) : UInt64 := do
  let mut a : Arr DRP 4 := #v[{ x := 1, y := 2 }, { x := 3, y := 4 }, { x := 5, y := 6 }, { x := 7, y := 8 }]
  for i in 0...4 do
    a[i].x := a[i].x * (x % 5) + i
    if (y >>> i) % 2 == 1 then a[i].y := 0
  let mut s := 0
  for i in 0...4 do
    s := s * 100 + a[i].x * 10 + a[i].y
  s

def refDElemField (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a : List (Nat × Nat) := [(1, 2), (3, 4), (5, 6), (7, 8)]
  let a := (List.range 4).map fun i =>
    let (px, py) := a[i]!
    (px * (x % 5) + i, if (y >>> i) % 2 = 1 then 0 else py)
  UInt64.ofNat (W' ((List.range 4).foldl (fun s i => s * 100 + a[i]!.1 * 10 + a[i]!.2) 0))

/-- A `match` statement with binders followed by a long rest, then a loop with a statement `if`
followed by a `break`. -/
mp def dMkR (x : UInt64) : Result UInt64 UInt64 := if x % 2 == 0 then ok (x / 2) else err (x % 9)

mp def dMatchJoin (x y : UInt64) : UInt64 := do
  let mut s := y % 100
  let mut t := 0
  match dMkR x with
  | ok a => s := s + a % 50
  | err e => t := e + 1
  let u := s + t
  let v := u * 3
  let w := v + s
  let z := w * t
  let q := z + u
  let mut c := 0
  for i in 0...10 do
    if i % 3 == 0 then c := c + 1 else c := c + 10
    if c > q % 40 then break
  q * 1000 + c

def refDMatchJoin (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (s, t) := if x % 2 = 0 then (y % 100 + (x / 2) % 50, 0) else (y % 100, x % 9 + 1)
  let u := s + t
  let v := u * 3
  let w := v + s
  let z := w * t
  let q := z + u
  let c := loopR 0 10 0 fun i c =>
    let c := if i % 3 = 0 then c + 1 else c + 10
    (c, c > q % 40)
  UInt64.ofNat (W' (q * 1000 + c))


mp def dMk (x : UInt64) : Result UInt64 UInt64 := if x % 3 == 0 then ok (x / 3) else err (x % 3)

/-- `match` arms that `continue` and `return`, with binders that shadow carried variables. -/
mp def dMatchJump (x y : UInt64) : UInt64 := do
  let mut s := 0
  let mut e := 100
  for i in 0...12 do
    match dMk ((x >>> i) + i) with
    | ok s =>
      if s % 5 == y % 5 then return s * 1000 + i
      e := e + s % 7
    | err e =>
      if e == 2 then continue
      s := s + e
    s := s + 1
  s * 1000 + e

def refDMatchJump (l : List UInt64) : UInt64 := Id.run do
  let (x, y) := toNat2 l
  let mut s := 0
  let mut e := 100
  for i in [0:12] do
    let v := (x >>> i) + i
    let v := v % 2^64
    if v % 3 == 0 then
      let s' := v / 3
      if s' % 5 == y % 5 then return UInt64.ofNat (s' * 1000 + i)
      e := e + s' % 7
    else
      let e' := v % 3
      if e' == 2 then continue
      s := s + e'
    s := s + 1
  return UInt64.ofNat (s * 1000 + e)

mp_seeded "neg-cond" dLeadM in
/-- A leading `if c then break` that reads the accumulator, and a `continue`. -/
mp def dLead (x y : UInt64) : UInt64 := do
  let mut acc := x % 13
  for i in 0...30 do
    if acc > 200 + y % 50 then break
    if i % 4 == 3 then continue
    acc := acc * 2 + i
  acc

def refDLead (l : List UInt64) : UInt64 := Id.run do
  let (x, y) := toNat2 l
  let mut acc := x % 13
  for i in [0:30] do
    if acc > 200 + y % 50 then break
    if i % 4 == 3 then continue
    acc := acc * 2 + i
  return UInt64.ofNat acc

mp_seeded "inner-break-outer" dNestBrk2M in
/-- An inner loop and the loop around it, each left by a `break` that is not at the start of the
body. The inner `break` leaves only the inner loop. -/
mp def dNestBrk2 (x y : UInt64) : UInt64 := do
  let mut t := y % 7
  for i in 0...6 do
    t := t + i
    for j in 0...6 do
      t := t * 2 + j
      if (t + x) % 7 == 0 then break
      t := t + 1
    if t > 100000 + y % 1000 then break
  t

def refDNestBrk2 (l : List UInt64) : UInt64 := Id.run do
  let (x, y) := toNat2 l
  let mut t := y % 7
  for i in [0:6] do
    t := t + i
    for j in [0:6] do
      t := t * 2 + j
      if W' (t + x) % 7 == 0 then break
      t := t + 1
    if t > 100000 + y % 1000 then break
  return UInt64.ofNat t

mp_seeded "acc-lost" dAccM in
/-- An accumulator declared before another statement. The accumulator is `s`, the word variable
declared last that the body assigns, and the loop's final value is assigned back to it. -/
mp def dAcc (x y : UInt64) : UInt64 := do
  let mut s := x % 100
  let c := y % 7
  for i in 0...9 do
    s := s * 3 + i + c
  s * 2 + c

def refDAcc (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let s := loopR 0 9 (x % 100) fun i s => (s * 3 + i + y % 7, false)
  UInt64.ofNat (s * 2 + y % 7)

/-- A loop from a run-time lower bound to an inclusive top bound near `2^64`, left early by a
leading `break` that reads a carried variable. `differential gen` evaluates the normal form
lazily, so the huge range is never built. -/
mp def dInclTop (x y : UInt64) : UInt64 := do
  let mut s := 0
  let mut c := 0
  for i in (18446744073709551600 + x % 14)...=18446744073709551613 do
    if c >= y % 9 then break
    s := s + (i - 18446744073709551600)
    c := c + 1
  s * 100 + c

def refDInclTop (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let (s, c) := loopR (18446744073709551600 + x % 14) 18446744073709551614 (0, 0) fun i (s, c) =>
    if c ≥ y % 9 then ((s, c), true) else ((s + (i - 18446744073709551600), c + 1), false)
  UInt64.ofNat (s * 100 + c)


/-- The `do` notation's jumps and ranges. -/
def doFuncs : List TestFn :=
  [tfm2 "dBreak" dBreak.exp (fun a => (dBreak a[0]! a[1]!).run) refDBreak,
   tfm2 "dCont" dCont.exp (fun a => (dCont a[0]! a[1]!).run) refDCont,
   tfm2 "dRet" dRet.exp (fun a => (dRet a[0]! a[1]!).run) refDRet,
   tfm2 "dRetMid" dRetMid.exp (fun a => (dRetMid a[0]! a[1]!).run) refDRetMid,
   tfm2 "dLo" dLo.exp (fun a => (dLo a[0]! a[1]!).run) refDLo,
   tfm2 "dLoIncl" dLoIncl.exp (fun a => (dLoIncl a[0]! a[1]!).run) refDLoIncl,
   tfm2 "dSlice" dSlice.exp (fun a => (dSlice a[0]! a[1]!).run) refDSlice,
   tfm2 "dNest" dNest.exp (fun a => (dNest a[0]! a[1]!).run) refDNest,
   tfm2 "dJoin" dJoin.exp (fun a => (dJoin a[0]! a[1]!).run) refDJoin,
   tfm2 "dJumpJoin" dJumpJoin.exp (fun a => (dJumpJoin a[0]! a[1]!).run) refDJumpJoin,
   tfm2 "dRetJoin" dRetJoin.exp (fun a => (dRetJoin a[0]! a[1]!).run) refDRetJoin,
   tfm2 "dInclTop" dInclTop.exp (fun a => (dInclTop a[0]! a[1]!).run) refDInclTop,
   tfm2 "dAcc" dAcc.exp (fun a => (dAcc a[0]! a[1]!).run) refDAcc,
   tfm2 "dNestBrk" dNestBrk.exp (fun a => (dNestBrk a[0]! a[1]!).run) refDNestBrk,
   tfm2 "dShJoin" dShJoin.exp (fun a => (dShJoin a[0]! a[1]!).run) refDShJoin,
   tfm2 "dShNest" dShNest.exp (fun a => (dShNest a[0]! a[1]!).run) refDShNest,
   tfm2 "dJoinPlaces" dJoinPlaces.exp (fun a => (dJoinPlaces a[0]! a[1]!).run) refDJoinPlaces,
   tfm2 "dElemField" dElemField.exp (fun a => (dElemField a[0]! a[1]!).run) refDElemField,
   tfm2 "dMatchJoin" dMatchJoin.exp (fun a => (dMatchJoin a[0]! a[1]!).run) refDMatchJoin,
   tfm2 "dMatchJump" dMatchJump.exp (fun a => (dMatchJump a[0]! a[1]!).run) refDMatchJump,
   tfm2 "dLead" dLead.exp (fun a => (dLead a[0]! a[1]!).run) refDLead,
   tfm2 "dNestBrk2" dNestBrk2.exp (fun a => (dNestBrk2 a[0]! a[1]!).run) refDNestBrk2]

#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (0xdeadbeef, 0x1234)].all
  fun (x, y) => doFuncs.all fun f =>
    f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]

/-! ## Seeded translation bugs -/

/-- Each seeded bug with a function translated with it and the reference it must disagree with.
The functions are evaluated through their denotation. -/
def doMutants : List (String × Exp [Ty.u64, Ty.u64] Ty.u64 × (List UInt64 → UInt64)) :=
  [("break-ignored", dBreakM.exp, refDBreak), ("continue-falls-through", dContM.exp, refDCont),
   ("return-lost", dRetM.exp, refDRet), ("return-falls-through", dRetMidM.exp, refDRetMid),
   ("incl-off-by-one", dLoInclM.exp, refDLoIncl), ("lo-ignored", dRetMidM2.exp, refDRetMid),
   ("join-lost", dJoinM.exp, refDJoin), ("jump-join-lost", dJumpJoinM.exp, refDJumpJoin),
   ("bind-name", dShNestM.exp, refDShNest), ("neg-cond", dLeadM.exp, refDLead),
   ("acc-lost", dAccM.exp, refDAcc), ("inner-break-outer", dNestBrk2M.exp, refDNestBrk2)]

end Millipede.Tests.Differential
