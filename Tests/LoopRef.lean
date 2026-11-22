import Millipede.Meta.MpDef
import Millipede.Top.Sound
import Std.Tactic.Do
import Std.WP

/-!
# Tests for loops that write through references

A loop body may assign variables bound outside the loop, and after the loop each of them holds
the last value assigned to it. Such a variable may be a `let mut` variable, a `&mut` parameter or
borrow, an element of a `&mut` slice or a field of a reactor's root. The loop carries these
variables, so the value semantics threads them through the iterations while the memory lowering
updates them in place.

This suite runs loops that fill, reverse, scan, copy and search slices, update struct fields and
sort, and checks their results on sample arrays. It checks that their obligations are
discharged automatically, also under nested `if`s, nested loops and short-circuit `&&` and `||`,
and that `compile` accepts them. One loop gets a `vcgen` specification. Core terms check the
loop's meaning and checker directly, and rejection tests pin the messages for what stays illegal.
-/

namespace Millipede.Tests.LoopRef

open Millipede Std.WP

set_option experimental.vcgen true

def ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩

structure Pt where
  x : UInt64
  y : UInt64
deriving Data, DecidableEq, Repr, Inhabited

/-! ## Slices filled, reversed, scanned in place -/

/-- Fills a slice in place, setting cell `i` to `v * 3 + i`. -/
mp def fillS (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  for i in 0...s.len do
    s[i] := v * 3 + i

/-- Reverses a slice in place, leaving the loop at the middle. -/
mp def revS (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    if i ≥ s.len / 2 then break
    let j := s.len - 1 - i
    let a := s[i]
    let b := s[j]!
    s[i] := b
    s[j]! := a

/-- Replaces a slice by its prefix sums in place and returns the total. -/
mp def prefixS (s : &mut [UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    let t := acc + s[i]
    s[i] := t
    acc := t
  acc

/-- Copies `src` into `dst`, as many cells as both have. -/
mp def copyS (dst : &mut [UInt64; 8]) (src : &[UInt64; 8]) : Unit := do
  for i in 0...dst.len do
    if i ≥ src.len then break
    dst[i] := src[i]!

/-- Replaces the first cell equal to `key` by `rep` and returns its position plus one, or 0 when
no cell equals `key`. -/
mp def findRepl (s : &mut [UInt64; 8]) (key rep : UInt64) : UInt64 := do
  let mut found := 0
  for i in 0...s.len do
    if found != 0 then break
    if s[i] == key then
      s[i] := rep
      found := i + 1
    else found := 0
  found

/-- Updates two fields of a `&mut` struct in a loop. -/
mp def bumpPt (p : &mut Pt) (n : UInt64) : Unit := do
  for i in 0...5 do
    p.x := p.x + n
    p.y := p.y * 3 + i

/-- Outer `let mut` variables, one of them written from a nested loop. -/
mp def fibPair (n : UInt64) : UInt64 := do
  let mut a := 0
  let mut b := 1
  let mut c := 0
  for i in 0...12 do
    if i ≥ n then break
    let t := a + b
    a := b
    b := t
    for j in 0...3 do
      c := c + j
  a * 1000 + c

/-! ### Callers and their values -/

/-- The array that the callers below pass slices of. -/
mp def arr8 (x : UInt64) : Arr UInt64 8 := do
  let mut a := Vector.replicate 8 x
  a[2] := x + 5
  a[5] := 7
  a

mp def useFill (x lo len : UInt64) requires lo.toNat + len.toNat ≤ 8 : Arr UInt64 8 := do
  let mut a := arr8 x
  let _ := fillS (&mut a[lo..lo + len]) 10
  a

mp def useRev (x : UInt64) : Arr UInt64 8 := do
  let mut a := arr8 x
  a[0] := 100
  a[7] := 200
  let _ := revS (&mut a[0..8])
  a

mp def usePrefix (x : UInt64) : UInt64 := do
  let mut a := arr8 x
  let t := prefixS (&mut a[1..6])
  t * 1000 + a[5]

mp def useCopy (x y : UInt64) : Arr UInt64 8 := do
  let mut a := arr8 x
  let b := arr8 y
  let _ := copyS (&mut a[1..5]) (&b[0..3])
  a

mp def useFind (x key : UInt64) : UInt64 := do
  let mut a := arr8 x
  let r := findRepl (&mut a[0..8]) key 99
  r * 1000 + a[5]

mp def usePt (x y : UInt64) : Pt := do
  let mut p : Pt := { x := x, y := y }
  let _ := bumpPt (&mut p) 2
  p

example : (useFill 1 2 3).run.1 = #v[1, 1, 30, 31, 32, 7, 1, 1] := by decide
example : (useFill 4 0 8).run.1 = #v[30, 31, 32, 33, 34, 35, 36, 37] := by decide
example : (useRev 1).run = #v[200, 1, 7, 1, 1, 6, 1, 100] := by decide
example : (usePrefix 1).run = 16 * 1000 + 16 := by decide
example : (useCopy 1 2).run = #v[1, 2, 2, 7, 1, 7, 1, 1] := by decide
example : (useFind 1 7).run = 6 * 1000 + 99 := by decide
example : (useFind 1 42).run = 0 * 1000 + 7 := by decide
example : (usePt 1 0).run = ⟨11, 0 * 243 + 0 * 81 + 1 * 27 + 2 * 9 + 3 * 3 + 4⟩ := by decide
example : (fibPair 10).run = 55 * 1000 + 30 := by decide

/-! ## `vcgen`: an in-place loop with an invariant -/

/-- After `fillS`, the cells below the length hold `v * 3 + k`, the others are untouched. -/
theorem fillS_spec (s : Slots UInt64 8) (len v : UInt64) :
    ⦃True⦄ fillS s len v ⦃fun r => ∀ k < 8,
      r.2.1.cell k = if k < len.toNat then some (v * 3 + UInt64.ofNat k) else s.cell k⦄ := by
  vcgen [fillS] invariants
  · fun done _ st => ∀ k < 8, st.2.1.cell k =
      if k < done.length ∧ k < len.toNat then some (v * 3 + UInt64.ofNat k) else s.cell k
  case vc1 => simp
  case vc2 _ _ _ ih k hk =>
    simp only at ih ⊢
    rw [ih k hk]
    by_cases h : k < len.toNat <;> simp [h, hk]
  case vc3 pref cur suff hr _ sv _ ih hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    have hcur : (UInt64.ofNat pref.length).toNat = pref.length :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hlt (by decide))
    simp only [UInt64.lt_iff_toNat_lt, hcur] at hc
    intro k hk
    simp only [List.length_append, List.length_singleton, hcur] at *
    unfold Slots.cell Slots.setCell
    by_cases h : k = pref.length
    · subst h; simp [vget_vset_same _ _ _ _ hk, hc]
    · rw [vget_vset_ne _ _ _ _ _ (Ne.symm h)]
      have := ih k hk; unfold Slots.cell at this; rw [this]
      by_cases h2 : k < len.toNat <;> by_cases h3 : k < pref.length <;> simp [h2, h3] <;> omega
  case vc4 pref cur suff hr _ sv _ ih hc =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    have hcur : (UInt64.ofNat pref.length).toNat = pref.length :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hlt (by decide))
    simp only [UInt64.lt_iff_toNat_lt, hcur, Nat.not_lt] at hc
    intro k hk
    simp only [hcur] at *
    rw [ih k hk]
    by_cases h : k < len.toNat <;> by_cases h3 : k < pref.length <;> simp [h, h3] <;> omega

/-! ## A reactor whose step updates the root's fields in a loop -/

mp def ptInit : Pt := { x := 1, y := 0 }

mp def ptStep (r : &mut Pt) : Unit := do
  for i in 0...3 do
    r.x := r.x * 2
    r.y := r.y + r.x + i

mp program ptProg (root : Pt) init ptInit step ptStep

#guard (fun (p : Pt) => p.x == 64 && p.y == 132) (ptProg.run ω0 2).1

/-- `mp def` discharged the obligations of the step, whose loop writes the root's fields. -/
example : ptProg.Safe := ptProg.safe

/-! ## Compilation

Each loop body hands back its carried variables in place, so the memory lowering accepts every
function above and `compile` accepts the reactor. -/

example : fillS.exp.memOk = true := by decide
example : revS.exp.memOk = true := by decide
example : prefixS.exp.memOk = true := by decide
example : copyS.exp.memOk = true := by decide
example : findRepl.exp.memOk = true := by decide
example : bumpPt.exp.memOk = true := by decide
example : fibPair.exp.memOk = true := by decide
example : ptStep.exp.memOk = true := by decide
#guard (compile ptProg x64Linux).toBool

/-! ## The Core loop's meaning and checker -/

/-- A loop that carries `x` and runs `x := x + i` for `i < 4`, followed by `x`. -/
def coreSum : Exp [Ty.u64] Ty.u64 :=
  .loop 4 (.cons .here .nil) (.lit ()) (.atom (.lit true))
    (.let_ (.prim .add (.cons (.var (.there (.there .here))) (.cons (.var .here) .nil)))
      (.assign (.var (.there (.there (.there .here)))) (.var .here)
        (.mk (Ctor.tupMk .unit [.u64]) (.cons (.lit ()) (.cons (.var (.there (.there (.there .here)))) .nil)))))
    (.atom (.var (.there .here)))

example : coreSum.denote ω0 (.cons 10 .nil) World.init = (16, World.init) := rfl
example : coreSum.wf = true := by decide
example : coreSum.memOk = true := by decide

/-- A loop that carries the same variable twice, which the checker and `compile` both refuse. -/
def coreTwice : Exp [Ty.u64] Ty.u64 :=
  .loop 4 (.cons .here (.cons .here .nil)) (.lit ()) (.atom (.lit true))
    (.mk (Ctor.tupMk .unit [.u64, .u64]) (.cons (.lit ()) (.cons (.var (.there (.there .here)))
      (.cons (.var (.there (.there .here))) .nil))))
    (.atom (.var (.there .here)))

example : coreTwice.wf = false := by decide
example : coreTwice.memOk = false := by decide

/-- A body that hands back a literal instead of the carried variable itself. The checker and the
value semantics accept it, and `compile` refuses it because the update is not in place. -/
def coreNotInPlace : Exp [Ty.u64] Ty.u64 :=
  .loop 4 (.cons .here .nil) (.lit ()) (.atom (.lit true))
    (.mk (Ctor.tupMk .unit [.u64]) (.cons (.lit ()) (.cons (.lit 7) .nil)))
    (.atom (.var (.there .here)))

example : coreNotInPlace.wf = true := by decide
example : coreNotInPlace.memOk = false := by decide
example : coreNotInPlace.denote ω0 (.cons 10 .nil) World.init = (7, World.init) := rfl

/-! ## Obligations discharged automatically

Each `example := @f.safe` fails to elaborate if `mp def` did not discharge `f`'s obligations.
-/

/-- A carried slice written under two nested `if`s. -/
mp def q1 (s : &mut [UInt64; 8]) (t : UInt64) : Unit := do
  for k in 0...s.len do
    if k > t then
      if k > 3 then
        s[k] := 1
        ()
      else ()
    else ()

example := @q1.safe

/-- Insertion sort: the inner `sift` loop compares and swaps under nested `if`s, inside an outer
loop over the same slice. -/
mp def isortS (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    let mut j := i
    for k in 0...8 do
      if j ≤ 0 then break
      if j < s.len then
        let a := s[j - 1]!
        let b := s[j]!
        if a > b then
          s[j - 1]! := b
          s[j]! := a
          j := j - 1
        else j := 0
      else j := 0

example := @isortS.safe

/-- Nested loops whose inner loop writes the carried slice. The outer invariant, that the
slice's cells are full, survives the inner loop. -/
mp def n1 (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    for k in 0...s.len do
      s[k] := s[k] + i

mp def n2 (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...3 do
    for k in 0...s.len do
      s[k] := s[k] + i

mp def n3 (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    for k in 0...3 do
      s[i] := s[i] + k

example := @n1.safe
example := @n2.safe
example := @n3.safe

/-- The exit condition reads `s[i]` only when `i < s.len`, because the loop's condition is
`i < s.len && c` and `&&` short-circuits. -/
mp def ck2 (s : &[UInt64; 32]) : UInt64 := do
  let mut a := 0
  for i in 0...s.len do
    if s[i] == 0 then break
    a := a + s[i]
  a

/-- `j < s.len && s[j]! != 0` reads `s[j]` only when `j` is in range, and `c4` does the same
with `||`. -/
mp def c3 (s : &[UInt64; 32]) (j : UInt64) : Bool :=
  j < s.len && s[j]! != 0

mp def c4 (s : &[UInt64; 32]) (j : UInt64) : Bool :=
  j >= s.len || s[j]! == 0

example := @ck2.safe
example := @c3.safe
example := @c4.safe

mp def arr32 (x : UInt64) : Arr UInt64 32 := do
  let mut a := Vector.replicate 32 x
  a[3] := 0
  a

mp def useSort (x : UInt64) : Arr UInt64 8 := do
  let mut a := arr8 x
  a[0] := 9
  let _ := isortS (&mut a[0..6])
  let _ := n2 (&mut a[6..8])
  a

mp def useCk (x j : UInt64) : UInt64 :=
  let a := arr32 x
  let r := ck2 (&a[1..20])
  let b := c3 (&a[0..2]) j
  let c := c4 (&a[0..2]) j
  r * 100 + (if b then 10 else 0) + (if c then 1 else 0)

example := @useSort.safe
example := @useCk.safe

-- `arr8 2` is `[2,2,7,2,2,7,2,2]`; the caller sets `a[0] := 9`, sorts the first 6 cells and adds
-- 0+1+2 to the last two.
example : (useSort 2).run = #v[2, 2, 2, 7, 7, 9, 5, 5] := by decide
-- In the view `[1..20]` cells 0 and 1 are 5 and cell 2, which is `a[3]`, is 0, so the scan stops
-- there.
example : (useCk 5 0).run = 10 * 100 + 10 := by decide
example : (useCk 5 1).run = 10 * 100 + 10 := by decide
-- `j = 2` is out of the view's range, so `&&` is false and `||` is true without reading `s[2]`.
example : (useCk 5 2).run = 10 * 100 + 1 := by decide

/-! ## What stays illegal -/

/-- error: cannot assign through the shared reference `s` -/
#guard_msgs in
mp def badShr (s : &[UInt64; 8]) : Unit := do
  for i in 0...s.len do
    s[i] := 0

/-- error: `x` is not mutable: declare it with `let mut` (or take it as `&mut`) to assign it -/
#guard_msgs in
mp def badImm (x : UInt64) : UInt64 := do
  for i in 0...3 do
    x := x + i
  x

/-- error: `x` is written here while an overlapping place is borrowed with `&`; a shared borrow only allows reads -/
#guard_msgs in
mp def badBorrowed (x0 : UInt64) : UInt64 := do
  let mut x := x0
  let r := &x
  for i in 0...3 do
    x := x + i
  r + x

/-- error: linear variable `e` is bound outside this loop and used inside it; a loop may run any number of times -/
#guard_msgs in
mp def badLin (e : Result UInt64 UInt64) : Result UInt64 UInt64 := do
  let mut n := 0
  for i in 0...3 do
    let r := e
    n := n + 1
    match r with
    | ok _ => ()
    | err _ => ()
  ok n

/-- error: cannot write `x` here: it is bound outside the current block (the value of a `let`, a borrow body, a loop), so the update would not be visible after the block; write it at statement level -/
#guard_msgs in
mp def badInLet (c : Bool) : UInt64 := do
  let mut x := 0
  let _ := if c then (do for i in 0...3 do x := x + i) else ()
  x

end Millipede.Tests.LoopRef
