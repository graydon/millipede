import Millipede.Meta.MpDef
import Std.Tactic.Do
import Std.WP

/-!
# Tests for `mp def` on structs, enums, arrays, references and slices

This suite defines one small function for each memory construct of the language and checks the
declarations `mp def` generates for it: the normal form, by `rfl`; the obligations, which are
discharged automatically or with `mp prove`; and the result on sample inputs. The constructs are
structs, enums and `match`, arrays, `Slots`, slices with their hidden length, pairs of array
elements, `let mut`, `&` and `&mut` parameters, scoped borrows, `requires` and a small reactor.

A few functions with a `mut` parameter or an array loop also get a `vcgen` specification. Every
checker has a rejection test that pins its message with `#guard_msgs`, and `#guard` compares
three functions with reference definitions, so a wrong translation or a checker that accepts a
bad program makes the suite fail.
-/

namespace Millipede.Tests.MpDef2

open Millipede Std.WP

set_option experimental.vcgen true

/-! ## Data types -/

structure Pt where
  x : UInt64
  y : UInt64
deriving Data, DecidableEq, Repr, Inhabited

/-- A counter and an array of items, the target of the scoped borrow `&mut t.items[i]`. -/
structure Table where
  count : UInt64
  items : Vector UInt64 4
deriving Data, DecidableEq, Repr, Inhabited

inductive Cmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving Data, DecidableEq, Repr, Inhabited

/-- A struct with a linear field. -/
structure Holder where
  r : Except UInt64 UInt64
  n : UInt64
deriving Data

/-! ## Structs -/

mp def mkPt (a b : UInt64) : Pt := { x := a, y := b }
mp def mkPt2 (a b : UInt64) : Pt := Pt.mk b a
mp def mkPt3 (a : UInt64) : Pt := ⟨a, a + 1⟩
mp def norm1 (p : Pt) : UInt64 := p.x + p.y
mp def withX (p : Pt) (v : UInt64) : Pt := { p with x := v }
mp def ascribed (a : UInt64) : UInt64 := let p := { x := a, y := 2 : Pt }; p.y

example : mkPt = fun a b => pure { x := a, y := b } := rfl
example : norm1 = fun p => pure (p.x + p.y) := rfl
example : withX = fun p v => pure { x := v, y := p.y } := rfl
example : (mkPt2 1 2).run = ⟨2, 1⟩ := rfl
example : (mkPt3 1).run = ⟨1, 2⟩ := rfl
example : (ascribed 7).run = 2 := rfl
example (ω : Oracle) (w : World) (p : Pt) :
    norm1.exp.denote ω (.cons p .nil) w = ((norm1 p).run, w) := norm1.exp_denote ω w p
example : norm1.fn.wf = true := norm1.wf

/-- `let mut` and `p := v` on a field. -/
mp def moveRight (p0 : Pt) (d : UInt64) : Pt := do
  let mut p := p0
  p.x := p.x + d
  p

example : moveRight = fun p0 d => pure { x := p0.x + d, y := p0.y } := rfl

/-! ## Enums -/

mp def eval (acc : UInt64) (c : Cmd) : UInt64 :=
  match c with
  | .stop => acc
  | Cmd.add n => acc + n
  | .mul n => acc * n

mp def mkAdd (n : UInt64) : Cmd := Cmd.add n
mp def mkStop : Cmd := Cmd.stop
mp def mkMul (n : UInt64) : Cmd := (.mul n : Cmd)

/-- The normal form of an enum `match` is a Lean `match` on the same constructors. -/
example : eval = fun acc c => match c with
    | .stop => pure acc
    | .add x => pure (acc + x)
    | .mul x => pure (acc * x) := rfl

/-- `vcgen` splits the enum `match` like any Lean `match`. -/
theorem eval_spec (acc : UInt64) (c : Cmd) :
    ⦃True⦄ eval acc c ⦃fun r => r = match c with
      | .stop => acc
      | .add n => acc + n
      | .mul n => acc * n⦄ := by
  cases c <;> (vcgen [eval]; all_goals simp)

example : (eval 5 .stop).run = 5 := rfl
example : (eval 5 (.add 3)).run = 8 := rfl
example : (eval 5 (.mul 3)).run = 15 := rfl
example : (mkAdd 3).run = .add 3 := rfl
example : mkStop.run = .stop := rfl
example : (mkMul 2).run = .mul 2 := rfl
/-- The arms may come in any order. -/
mp def isStop (c : Cmd) : Bool :=
  match c with
  | .mul _ => false
  | .stop => true
  | .add _ => false
example : (isStop .stop).run = true ∧ (isStop (.add 1)).run = false := ⟨rfl, rfl⟩

/-! ## Arrays -/

/-- Indexing with the counter of a loop whose bound is the array's length leaves the user no
obligation. -/
mp def sumArr (a : Arr UInt64 4) : UInt64 := do
  let mut acc := 0
  for i in 0...4 do
    acc := acc + a[i]
  acc

example : sumArr = fun a => forIn (upto 4) (0 : UInt64) (fun i acc =>
    pure (ForInStep.yield (acc + vget a (UInt64.ofNat i).toNat default))) := rfl
example : (sumArr #v[1, 2, 3, 4]).run = 10 := rfl
/-- `mp def` discharged the obligations, because the loop counter stays below 4. -/
example (ω : Oracle) (w : World) (a : Vector UInt64 4) :
    sumArr.exp.safe ω (.cons a .nil) w := sumArr.safe ω w a

/-- The obligation of `a[i]!` is discharged from the `requires` clause. -/
mp def getBang (a : Arr UInt64 4) (i : UInt64) requires i.toNat < 4 : UInt64 := a[i]!

example (ω : Oracle) (w : World) (a : Vector UInt64 4) (i : UInt64) (h : i.toNat < 4) :
    getBang.exp.safe ω (.cons i (.cons a .nil)) w := getBang.safe ω w a i h
/-- A function with `requires` returns its result paired with `()`, the empty tuple of `mut`
values. -/
example : (getBang #v[5, 6, 7, 8] 2).run = (7, ()) := rfl

/-- The checked index `a[i]?` is safe for every `i` and returns an error out of range. -/
mp def getChk (a : Arr UInt64 4) (i : UInt64) : Result Unit UInt64 := a[i]?

example : (getChk #v[5, 6, 7, 8] 2).run = .ok 7 := rfl
example : (getChk #v[5, 6, 7, 8] 9).run = .error () := rfl
example (ω : Oracle) (w : World) (a : Vector UInt64 4) (i : UInt64) :
    getChk.exp.safe ω (.cons i (.cons a .nil)) w := getChk.safe ω w a i

/-- An element assignment to an array that the loop carries. -/
mp def fillArr (a : Arr UInt64 4) (v : UInt64) : Arr UInt64 4 := do
  let mut acc := a
  for i in 0...4 do
    acc[i] := v
    acc := acc
  acc

example : (fillArr #v[1, 2, 3, 4] 9).run = #v[9, 9, 9, 9] := by decide

mp def lit3 : Arr UInt64 3 := #v[1, 2, 3]
mp def rep3 (v : UInt64) : Arr UInt64 3 := Vector.replicate 3 v
example : lit3.run = #v[1, 2, 3] := rfl
example : (rep3 4).run = #v[4, 4, 4] := rfl

/-! ## `mut` parameters, references and calls -/

/-- Increments the field `x` of a point passed by `&mut`. -/
mp def bump (p : &mut Pt) : Unit := do
  p.x := p.x + 1
  ()

/-- A `mut` parameter becomes an extra result, so `bump p` returns `()` and the final `p`. -/
example : bump = fun p => pure ((), { x := p.x + 1, y := p.y }, ()) := rfl
example : bump.fnRef.wf [.mut] = true := bump.wf

-- The cost of a function with a `mut` parameter includes building the tuple that returns it.
/-- info: cost bump ≤ κ.ctor + 2 * κ.let_ + 2 * κ.mem + 2 * κ.place + κ.prim + 2 * κ.word -/
#guard_msgs in
#mp_cost bump

/-- A caller passes `&mut` of a `let mut` binder and sees the update. -/
mp def useBump (q : Pt) : UInt64 := do
  let mut p := q
  let _ := bump (&mut p)
  p.x + p.y

/-- The caller's normal form calls `bump` by name. -/
example : useBump = fun q => (do let x ← bump q; pure (x.2.1.x + x.2.1.y)) := rfl
example : (useBump ⟨1, 2⟩).run = 4 := rfl

/-- A shared reference parameter, and a caller passing `&`. -/
mp def total (p : &Pt) : UInt64 := p.x + p.y
mp def callTotal (q : Pt) : UInt64 := total (&q)
example : (callTotal ⟨3, 4⟩).run = 7 := rfl

/-- Two `&mut` parameters. -/
mp def swap (a : &mut UInt64) (b : &mut UInt64) : Unit := do
  let t := a
  a := b
  b := t
  ()

/-- Two disjoint fields of one struct may be borrowed `&mut` in the same call. -/
mp def swapXY (p0 : Pt) : Pt := do
  let mut p := p0
  let _ := swap (&mut p.x) (&mut p.y)
  p

example : (swapXY ⟨1, 2⟩).run = ⟨2, 1⟩ := rfl

/-- A scoped borrow `let r := &mut t.items[2]` lasts to the end of the enclosing block, so
parenthesising the block ends it before `t` is used again. -/
mp def bumpItem (t0 : Table) : Table := do
  let mut t := t0
  let _ := (do let r := &mut t.items[2]; r := r + 10; ())
  t.count := t.count + 1
  t

example : (bumpItem ⟨0, #v[1, 2, 3, 4]⟩).run = ⟨1, #v[1, 2, 13, 4]⟩ := by decide

/-- `pair!` borrows two elements of one array together, with the obligation `i ≠ j` discharged
from `requires`. -/
mp def swapElems (a0 : Arr UInt64 4) (i j : UInt64)
    requires i.toNat < 4 ∧ j.toNat < 4 ∧ i.toNat ≠ j.toNat : Arr UInt64 4 := do
  let mut a := a0
  let _ := (let r := &mut (a.pair! i j); swap (&mut r.fst) (&mut r.snd))
  a

example : (swapElems #v[1, 2, 3, 4] 0 3).run.1 = #v[4, 2, 3, 1] := by decide

-- A slice of an array, written through.
mp def sliceSet (a0 : Arr UInt64 4) : Arr UInt64 4 := do
  let mut a := a0
  let _ := (do let r := &mut a[1:3]; r[0]! := 9; ())
  a

example : (sliceSet #v[1, 2, 3, 4]).run = #v[1, 9, 3, 4] := by decide

/-- The slice's obligations, that it fits in the array and that its cell 0 is full, are
discharged automatically. -/
example (ω : Oracle) (w : World) (a0 : Vector UInt64 4) :
    sliceSet.exp.safe ω (.cons a0 .nil) w := sliceSet.safe ω w a0

/-- Six `&mut` slice borrows in sequence nest six write-backs in the goal, which is still
discharged automatically. -/
mp def sliceSet6 (a0 : Arr UInt64 64) : UInt64 := do
  let mut a := a0
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  let _ := (do let r := &mut a[1:61]; r[0]! := r[0]! + 1; ())
  a[1]

example (ω : Oracle) (w : World) (a0 : Vector UInt64 64) :
    sliceSet6.exp.safe ω (.cons a0 .nil) w := sliceSet6.safe ω w a0

-- A slice view is never assigned whole, whether it is a borrow or a slice parameter.
/-- error: a slice view is not assigned whole: a view only gives access to its elements `r[i]!` (filling a cell past its length has no storage behind it) -/
#guard_msgs in
mp def sliceWhole (x : UInt64) (b : Slice UInt64 4) : UInt64 := do
  let mut a := Vector.replicate 4 x
  let _ := (do let r := &mut a[0:2]; r := b; ())
  a[1]

/-- error: a slice view is not assigned whole: a view only gives access to its elements `r[i]!` (filling a cell past its length has no storage behind it) -/
#guard_msgs in
mp def sliceParamWhole (s : &mut Slice UInt64 4) (b : Slice UInt64 4) : Unit := do
  s := b
  ()

/-! ## Slice parameters

A slice parameter of type `&[T; n]` or `&mut [T; n]` views part of an array `a : Arr T n`. The
parameter `s` is followed by a hidden `UInt64` parameter `s.len`, which each caller fills in
from the slice it passes. The function's `requires` ends with what every caller guarantees of a
slice argument, `s.len.toNat ≤ n ∧ ∀ k, k < s.len.toNat → s.isFull k = true`, so the obligation
of `s[i]` that cell `i` is full follows from `i < s.len`. That fact may come from a guard, a
`requires` or the loop `for i in 0...s.len`. A slice borrow `let r := &a[lo..hi]` has a length
`r.len` too, and `a[lo..hi]` is the same place as `a[lo:hi]`. -/

/-- Sums a shared slice by a loop over its length, with no `requires` written. -/
mp def sliceSum (s : &[UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    acc := acc + s[i]
  acc

/-- The generated `requires` holds for the view of `a[2..5]` with its length 3, and fails for a
length past the view's full cells. -/
example : sliceSum.req (.cons 3 (.cons (vview #v[1, 2, 3, 4, 5, 6, 7, 8] 2 3) .nil)) := by
  simp only [sliceSum.req, Env.get_here, Env.get_there]; decide
example : ¬ sliceSum.req (.cons 4 (.cons (vview #v[1, 2, 3, 4, 5, 6, 7, 8] 2 3) .nil)) := by
  simp only [sliceSum.req, Env.get_here, Env.get_there]; decide
example (ω : Oracle) (w : World) (s : Slots UInt64 8) (n : UInt64) (h : n.toNat ≤ 8)
    (hf : ∀ k, k < n.toNat → s.isFull k = true) :
    sliceSum.exp.safe ω (.cons n (.cons s .nil)) w := sliceSum.safe ω w s n ⟨h, hf⟩

/-- Adds `d` to the last element of a `&mut` slice, guarded by `0 < s.len`. -/
mp def bumpLast (s : &mut [UInt64; 8]) (d : UInt64) : Unit := do
  if 0 < s.len then
    s[s.len - 1] := s[s.len - 1] + d
    ()
  else ()

/-- A caller passes slices with static and run-time bounds and the length is filled in for it.
The obligations that each slice fits and that each callee's `requires` holds are discharged
automatically. -/
mp def sliceCaller (x k : UInt64) requires k.toNat ≤ 8 : UInt64 := do
  let mut a := Vector.replicate 8 x
  let _ := bumpLast (&mut a[2..5]) 7
  let _ := bumpLast (&mut a[0..k]) 1
  let t := sliceSum (&a[0..8])
  let u := (let r := &a[1..4]; r[0] + r.len)
  t + u

example : (sliceCaller 1 8).run.1 = (8 + 7 + 1) + (1 + 3) := by decide
example : (sliceCaller 1 0).run.1 = (8 + 7) + (1 + 3) := by decide
example (ω : Oracle) (w : World) (x k : UInt64) (h : k.toNat ≤ 8) :
    sliceCaller.exp.safe ω (.cons k (.cons x .nil)) w := sliceCaller.safe ω w x k h

/-- The pair borrow `(a[i], a[j])` is the place `a.pair! i j`, with the obligation `i ≠ j`. -/
mp def pairBorrow (a0 : Arr UInt64 4) (i j : UInt64)
    requires i.toNat < 4 ∧ j.toNat < 4 ∧ i.toNat ≠ j.toNat : Arr UInt64 4 := do
  let mut a := a0
  let _ := (do let r := &mut (a[i], a[j]); r.fst := r.snd + 1; ())
  a

example : (pairBorrow #v[1, 2, 3, 4] 0 3).run.1 = #v[5, 2, 3, 4] := by decide
example (ω : Oracle) (w : World) (a0 : Vector UInt64 4) (i j : UInt64) (h : i.toNat < 4)
    (h' : j.toNat < 4) (hij : i.toNat ≠ j.toNat) :
    pairBorrow.exp.safe ω (.cons j (.cons i (.cons a0 .nil))) w := pairBorrow.safe ω w a0 i j ⟨h, h', hij⟩

-- Without a guard, `mp def` reports the obligation that `s[1]` is full as open, because it
-- fails when `s.len ≤ 1`.
/-- info: the obligations of `unguarded` were not discharged automatically; prove them with `mp prove unguarded.safe := …` (the goal is `unguarded.SafeGoal`); left:
s : Slots UInt64 4
h : s.len.toNat ≤ 4 ∧ ∀ (k : Nat), k < s.len.toNat → s.isFull k = true
⊢ s.isFull 1 = true -/
#guard_msgs in
mp def unguarded (s : &[UInt64; 4]) : UInt64 := s[1]

-- With `requires 2 ≤ s.len.toNat` the same obligation is discharged.
mp def guarded (s : &[UInt64; 4]) requires 2 ≤ s.len.toNat : UInt64 := s[1]
example : guarded.fnRef.Safe := guarded.Safe

-- Rejected slice programs.
/-- error: a slice type needs the length of the arrays it views: `[T; n]` (the view of `a[lo..hi]` for an array `a : Arr T n`; its own length is `s.len`) -/
#guard_msgs in
mp def noBound (s : &[UInt64]) : UInt64 := s[0]

/-- error: parameter `s` of `sliceSum` is a slice of an array of 8 elements (`[T; 8]`), but this is a slice of an array of 4 elements -/
#guard_msgs in
mp def wrongBound (a : Arr UInt64 4) : UInt64 := sliceSum (&a[0..2])

/-- error: cannot assign through the shared reference `s` -/
#guard_msgs in
mp def writeShr (s : &[UInt64; 4]) : Unit := do
  s[0] := 1
  ()

/-- error: `a` is used here while an overlapping place is borrowed with `&mut` by `r`; while `r` is live, no overlapping place may be used except through `r` -/
#guard_msgs in
mp def useWhileSliced (x : UInt64) : UInt64 := do
  let mut a := Vector.replicate 4 x
  let _ := (do let r := &mut a[0..2]; r[0] := a[3]; ())
  a[0]

/-- error: `a` is used here while an overlapping place is borrowed with `&mut` by `r`; while `r` is live, no overlapping place may be used except through `r` -/
#guard_msgs in
mp def pairUseWhile (x i j : UInt64) requires i.toNat < 4 ∧ j.toNat < 4 ∧ i ≠ j : UInt64 := do
  let mut a := Vector.replicate 4 x
  let _ := (do let r := &mut (a[i], a[j]); r.fst := a[0]; ())
  a[0]

/-- error: a pair of places `(a[i], a[j])` needs two elements of the same array -/
#guard_msgs in
mp def pairTwoArrays (a b : Arr UInt64 4) : UInt64 := do
  let mut c := a
  let _ := (let r := &mut (c[0], b[1]); ())
  0

/-- A sub-slice of a slice passed on to a callee, whose obligation `1 ≤ s.len` comes from the
guard. -/
mp def subSlice (s : &mut [UInt64; 8]) : Unit :=
  if 1 ≤ s.len then
    let _ := bumpLast (&mut s[0..1]) 2
    ()
  else ()

/-- info: the obligations of `subSliceNoGuard` were not discharged automatically; prove them with `mp prove subSliceNoGuard.safe := …` (the goal is `subSliceNoGuard.SafeGoal`); left:
s : Slots UInt64 8
h : s.len.toNat ≤ 8 ∧ ∀ (k : Nat), k < s.len.toNat → s.isFull k = true
⊢ s.isFull 0 = true -/
#guard_msgs in
mp def subSliceNoGuard (s : &mut [UInt64; 8]) : Unit :=
  let _ := bumpLast (&mut s[0..1]) 2
  ()

/-- error: the upper bound of a loop must be a size expression (a numeric literal, a `Nat` constant or variable, the length `s.len` of a slice, or `+ - * / %` of those, `/` and `%` by a positive literal), or `min e N` with a size expression `N`: a loop needs a static bound on its number of iterations -/
#guard_msgs in
mp def loopNotLen (s : &[UInt64; 8]) (n : UInt64) : UInt64 := do
  let mut acc := 0
  for i in 0...n do
    acc := acc + s[i]
  acc

/-- The callee's `requires` becomes an obligation of the caller, discharged here from the
caller's own `requires`. -/
mp def twice (a : Arr UInt64 4) (i : UInt64) requires i.toNat < 4 : UInt64 :=
  let x := getBang a i
  x + x

example : (twice #v[5, 6, 7, 8] 1).run = (12, ()) := rfl
example (ω : Oracle) (w : World) (a : Vector UInt64 4) (i : UInt64) (h : i.toNat < 4) :
    twice.exp.safe ω (.cons i (.cons a .nil)) w := twice.safe ω w a i h

/-! ## `Slots` -/

-- `put!` needs the cell empty, which `requires` gives, and `take!` needs it full, which follows
-- from the `put!`; both obligations are discharged automatically.
mp def slotsDemo (s0 : Slots UInt64 2) requires s0.isVacant 0 = true : UInt64 := do
  let mut s := s0
  let _ := s.put! 0 7
  let x := s.take! 0
  x + 1

example : (slotsDemo (Slots.empty 2)).run = (8, ()) := by decide
/-- The bundle's safety, which callers cite. -/
example : slotsDemo.fnRef.Safe := slotsDemo.Safe

-- The checked forms `vacant?` and `full?` are rejected on `Slots`, whose cells carry no tag, so
-- occupancy cannot be observed at run time.
/-- error: `Slots` have no checked forms (doc/design/arenas.md (Slots): cells have no tags, occupancy is known only to proofs); use `put!`/`take!`/`s[i]!` with their obligations, or an arena's checked operations -/
#guard_msgs in
mp def tryPut (s0 : Slots UInt64 4) (i v : UInt64) : Slots UInt64 4 := do
  let mut s := s0
  match s.vacant? i with
  | ok _ =>
    let _ := s.put! i v
    s
  | err _ => s

/-- error: `Slots` have no checked forms (doc/design/arenas.md (Slots): cells have no tags, occupancy is known only to proofs); use `put!`/`take!`/`s[i]!` with their obligations, or an arena's checked operations -/
#guard_msgs in
mp def readCell (s : Slots UInt64 4) (i : UInt64) : UInt64 :=
  match s.full? i with
  | ok _ => s[i]!
  | err _ => 0

/-! ## Reactors -/

mp def initPt : Pt := { x := 0, y := 10 }
mp def stepPt (r : &mut Pt) : Unit := do
  r.x := r.x + 1
  ()

/-- The root is a `Pt`; each step increments `x` through `&mut root`. -/
mp program ptProg (root : Pt) init initPt step stepPt

example : ptProg.wf = true := ptProg.wf_eq
example : ptProg.Safe := ptProg.safe
example (ω : Oracle) : (ptProg.run ω 3).1 = ⟨3, 10⟩ := rfl

/-! ## `vcgen` proofs -/

/-- A specification of a function with a `mut` parameter is stated on its extra result. -/
theorem bump_spec (p : Pt) : ⦃True⦄ bump p ⦃fun r => r.2.1.x = p.x + 1 ∧ r.2.1.y = p.y⦄ := by
  vcgen [bump]
  all_goals simp

/-- A function with a `mut` array parameter and a loop. -/
mp def fill (a : &mut Arr UInt64 4) (v : UInt64) : Unit := do
  for i in 0...4 do
    a[i] := v

theorem fill_spec (a : Vector UInt64 4) (v : UInt64) :
    ⦃True⦄ fill a v ⦃fun r => ∀ k < 4, vget r.2.1 k default = v⦄ := by
  vcgen [fill] invariants
  · fun done _ st => ∀ k < done.length, vget st.2.1 k default = v
  case vc1 => simp at *
  case vc2 ih k hk => simpa using ih k (by simpa using hk)
  case vc3 =>
    rename_i pref cur _ hr _ acc _ ih
    obtain ⟨rfl, hlt⟩ := range_split hr
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hlt (by decide))]
    by_cases h : k = pref.length
    · subst h; exact vget_vset_same _ _ _ _ (by omega)
    · rw [vget_vset_ne _ _ _ _ _ (Ne.symm h)]; exact ih k (by omega)

/-- The maximum of an array, by a loop that reads `a[i]!`. -/
mp def maxArr (a : Arr UInt64 4) : UInt64 := do
  let mut acc := 0
  for i in 0...4 do
    let x := a[i]!
    acc := if acc < x then x else acc
  acc

/-- `mp def` discharged the obligations `i < 4` for the counter. -/
example (ω : Oracle) (w : World) (a : Vector UInt64 4) : maxArr.exp.safe ω (.cons a .nil) w :=
  maxArr.safe ω w a

theorem maxArr_spec (a : Vector UInt64 4) :
    ⦃True⦄ maxArr a ⦃fun r => ∀ k < 4, vget a k default ≤ r⦄ := by
  vcgen [maxArr] invariants
  · fun done _ acc => ∀ k < done.length, vget a k default ≤ acc
  case vc1 => simp at *
  case vc2 _ ih k hk => exact ih k (by simpa using hk)
  case vc3 pref cur suff hr acc ih hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hlt (by decide))] at hc ⊢
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    by_cases h : k = pref.length
    · subst h; exact UInt64.le_refl _
    · have := ih k (by omega)
      simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega
  case vc4 _ pref cur suff hr ih hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hlt (by decide))] at hc
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    by_cases h : k = pref.length
    · subst h; simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega
    · exact ih k (by omega)

/-! ### `mut` parameters in `StateM`

`mut` parameters become extra results. This section writes `bump` and `fill` by hand in
`StateM` to show the alternative, which needs a second normal form and an equation to the
generated one. Its specifications also carry the state through a precondition that every caller
must re-establish, while a specification on extra results is about the returned value, which a
caller's `vcgen` uses as it is. -/

/-- `bump` in `StateM Pt`. -/
def bumpS : StateM Pt Unit := modify fun p => { p with x := p.x + 1 }
theorem bumpS_eq (p : Pt) : (bump p).run = ((bumpS.run p).1, ((bumpS.run p).2, ())) := rfl
theorem bumpS_spec (p₀ : Pt) :
    ⦃fun s => s = p₀⦄ bumpS ⦃fun _ s => s.x = p₀.x + 1 ∧ s.y = p₀.y⦄ := by
  vcgen [bumpS]
  all_goals (rename_i h; subst h; simp)

/-- `fill` in `StateM (Vector UInt64 4)`. -/
def fillS (v : UInt64) : StateM (Vector UInt64 4) Unit := do
  let a ← get
  let a' ← forIn (List.range 4) a fun i acc =>
    pure (ForInStep.yield (vset acc (UInt64.ofNat i).toNat v))
  set a'
theorem fillS_eq (a : Vector UInt64 4) (v : UInt64) :
    (fill a v).run = (((fillS v).run a).1, (((fillS v).run a).2, ())) := rfl

/-! ## Rejections: one per checker -/

-- Types and places
/-- error: `Millipede.Tests.MpDef2.Pt` has no field `z` -/
#guard_msgs in
mp def badField (p : Pt) : UInt64 := p.z

/-- error: missing field `y` -/
#guard_msgs in
mp def badLit (a : UInt64) : Pt := { x := a }

/-- error: type mismatch: expected UInt64, but this has type Bool -/
#guard_msgs in
mp def badLit2 (a : UInt64) : Pt := { x := a, y := true }

/-- error: cannot show that this index is below 4: use a literal below 4 or the counter of a loop `for i in 0...N` with N ≤ 4; otherwise write `a[i]!` (an obligation of `f.safe`) or `a[i]?` (checked, a Result) -/
#guard_msgs in
mp def badIdx (a : Arr UInt64 4) (j : UInt64) : UInt64 := a[j]

/-- error: cannot show that this index is below 4: use a literal below 4 or the counter of a loop `for i in 0...N` with N ≤ 4; otherwise write `a[i]!` (an obligation of `f.safe`) or `a[i]?` (checked, a Result) -/
#guard_msgs in
mp def badIdx2 (a : Arr UInt64 4) : UInt64 := do
  let mut acc := 0
  for i in 0...5 do
    acc := acc + a[i]
  acc

/-- error: `put!` is an operation on `Slots`, but `p` has type Millipede.Tests.MpDef2.Pt -/
#guard_msgs in
mp def badSlots (p : Pt) : Unit := p.put! 0 1

-- Mutability
/-- error: `p` is not mutable: declare it with `let mut` (or take it as `&mut`) to assign it -/
#guard_msgs in
mp def badSet (p : Pt) : Pt := do
  p.x := 1
  p

/-- error: cannot assign through the shared reference `p` -/
#guard_msgs in
mp def badSetShr (p : &Pt) : Unit := do
  p.x := 1
  ()

/-- error: `q` is not mutable: declare it with `let mut` (or take it as `&mut`) to borrow mutably it -/
#guard_msgs in
mp def badBorrowImm (q : Pt) : UInt64 :=
  let _ := bump (&mut q)
  q.x

-- Calls
/-- error: parameter `p` of `bump` is `&mut Millipede.Tests.MpDef2.Pt`: pass `&mut p` for a place `p` -/
#guard_msgs in
mp def badMode (q : Pt) : Unit := bump q

/-- error: `norm1` takes its arguments by value; drop the `&` -/
#guard_msgs in
mp def badMode2 (q : Pt) : UInt64 := norm1 (&q)

-- Borrowing by place
/-- error: `a` is used here while an overlapping place is borrowed with `&mut` by `r`; while `r` is live, no overlapping place may be used except through `r` -/
#guard_msgs in
mp def badLive (a0 : Arr UInt64 4) : Arr UInt64 4 := do
  let mut a := a0
  let r := &mut a[1:3]
  r[0]! := 9
  a

/-- error: `p` is used here while an overlapping place is borrowed with `&mut` for a call's argument; no overlapping place may be used except through that reference -/
#guard_msgs in
mp def badSame (p0 : Pt) : Pt := do
  let mut p := p0
  let _ := swap (&mut p.x) (&mut p.x)
  p

/-- error: `a` is used here while an overlapping place is borrowed with `&mut` for a call's argument; no overlapping place may be used except through that reference -/
#guard_msgs in
mp def badTwoElems (a0 : Arr UInt64 4) : Arr UInt64 4 := do
  let mut a := a0
  let _ := swap (&mut a[0]) (&mut a[1])
  a

/-- error: `p` is written here while an overlapping place is borrowed with `&`; a shared borrow only allows reads -/
#guard_msgs in
mp def badShrWrite (p0 : Pt) : UInt64 := do
  let mut p := p0
  let r := &p
  p.x := 1
  r.x

-- Blocks: a write inside a `let`'s value would not be visible after it.
/-- error: cannot write `x` here: it is bound outside the current block (the value of a `let`, a borrow body, a loop), so the update would not be visible after the block; write it at statement level -/
#guard_msgs in
mp def badBlock (c : Bool) : UInt64 := do
  let mut x := 0
  let _ := if c then (do x := 1) else ()
  x

-- Linearity in places
/-- error: cannot copy the linear value of type Result UInt64 UInt64 out of a place (it would be used twice); move a whole variable, or `take!` it out of a `Slots` -/
#guard_msgs in
mp def badLinRead (h : Holder) : Result UInt64 UInt64 := h.r

/-- error: use of `h` after it was moved (a linear value is used once) -/
#guard_msgs in
mp def badMoved (h : Holder) : Holder :=
  let g := h
  let n := h.n
  g

/-- error: cannot move the linear value out of the shared reference `r` -/
#guard_msgs in
mp def badMoveShr (r : &Result UInt64 UInt64) : Result UInt64 UInt64 := r

-- Enums
/-- error: missing arm for `Millipede.Tests.MpDef2.Cmd.mul` -/
#guard_msgs in
mp def badArms (c : Cmd) : UInt64 :=
  match c with
  | .stop => 0
  | .add n => n

/-- error: duplicate arm for `Millipede.Tests.MpDef2.Cmd.stop` -/
#guard_msgs in
mp def badArms2 (c : Cmd) : UInt64 :=
  match c with
  | .stop => 0
  | .stop => 1
  | .add n => n
  | .mul n => n

/-- error: `Millipede.Tests.MpDef2.Cmd.stop` has no field -/
#guard_msgs in
mp def badArms3 (c : Cmd) : UInt64 :=
  match c with
  | .stop x => x
  | .add n => n
  | .mul n => n

-- A reference may not be shadowed, because the write-back reads it by name.
/-- error: `p` shadows the reference `p`; choose another name -/
#guard_msgs in
mp def badShadow (p : &mut Pt) : Unit :=
  let p := 3
  ()

-- `mp prove` needs a pending goal.
/-- error: `Millipede.Tests.MpDef2.norm1.safe` is already proved -/
#guard_msgs in
mp prove norm1.safe := fun _ _ _ => trivial

/-! ## Run-time checks against references -/

/-- The maximum of four values, the reference for `maxArr`. -/
def maxRef (a : Vector UInt64 4) : UInt64 :=
  [a[0], a[1], a[2], a[3]].foldl max 0

#guard [#v[1, 5, 3, 2], #v[0, 0, 0, 0], #v[9, 8, 7, 6], #v[1, 2, 3, 18446744073709551615]].all
  fun (a : Vector UInt64 4) => (maxArr a).run == maxRef a
#guard [(0, 3), (5, 7), (18446744073709551615, 1)].all fun (x, y) =>
  (swapXY ⟨x, y⟩).run == ⟨y, x⟩
#guard [0, 1, 2, 3].all fun (i : UInt64) =>
  match (getChk #v[10, 11, 12, 13] i).run with | .ok v => v == 10 + i | .error _ => false

end Millipede.Tests.MpDef2
