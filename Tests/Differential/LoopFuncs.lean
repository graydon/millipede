import Tests.Differential.SliceFuncs

/-!
# Differential tests of loops that write through references

Each function is an `mp def` over two words that runs through the whole pipeline under qemu and is
compared with a reference in plain Lean over `Nat` and `List`. The loops write their carried
variables in place. They fill a `&mut` slice, as `sFill` does without a loop and with the same
reference, reverse it, sum its prefixes, copy into it from another slice, and scan and update it
with an early exit. Other loops update two fields of a `&mut` struct, and nested loops write
outer `let mut` variables. Each harness hashes the lender after the call, so a write lost at the
end of an iteration or at the loop's exit changes the result.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and compared with references, so `mp def` makes no
-- attempt at their obligations.
set_option mp.autoSafe false

structure LPt where
  x : UInt64
  y : UInt64
deriving Data, DecidableEq, Repr, Inhabited

mp def lpFill (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  for i in 0...s.len do
    s[i] := v + i

mp def lpRev (s : &mut [UInt64; 8]) : Unit := do
  for i in 0...s.len do
    if i ≥ s.len / 2 then break
    let j := s.len - 1 - i
    let a := s[i]
    let b := s[j]!
    s[i] := b
    s[j]! := a

mp def lpPrefix (s : &mut [UInt64; 8]) : UInt64 := do
  let mut acc := 0
  for i in 0...s.len do
    let t := acc + s[i]
    s[i] := t
    acc := t
  acc

mp def lpCopy (dst : &mut [UInt64; 8]) (src : &[UInt64; 8]) : UInt64 := do
  let mut n := 0
  for i in 0...dst.len do
    if i ≥ src.len then break
    dst[i] := src[i]! + 1
    n := n + 1
  n

mp def lpFind (s : &mut [UInt64; 8]) (key rep : UInt64) : UInt64 := do
  let mut found := 0
  for i in 0...s.len do
    if found != 0 then break
    if s[i] == key then
      s[i] := rep
      found := i + 1
    else found := 0
  found

mp def lpPt (p : &mut LPt) (n : UInt64) : Unit := do
  for i in 0...6 do
    p.x := p.x * 3 + n
    p.y := p.y + p.x + i

/-! ## Harness functions and references -/

mp def lFill (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := y % 6
  let len := x % 3 + 1
  let _ := lpFill (&mut a[lo..lo + len]) y
  hash8 a

mp def lRev (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 4
  let len := y % 5 + 1
  let _ := lpRev (&mut a[lo..lo + len])
  let _ := lpRev (&mut a[1..8])
  hash8 a

mp def lPrefix (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 5
  let len := y % 4
  let t := lpPrefix (&mut a[lo..lo + len])
  hash8 a * 5 + t

def prefixR (l : List Nat) : List Nat :=
  (List.range l.length).map fun i => W (((l.take (i + 1)).foldl (· + ·) 0))

def refLPrefix (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let lo := x % 5
  let len := y % 4
  let p := prefixR (sliceR l lo len)
  let l' := patchR l lo len fun k => p[k]!
  let t := if len = 0 then 0 else p[len - 1]!
  UInt64.ofNat (W (W (hashR 7 l' * 5) + t))

mp def lCopy (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let b := mkArr y (x + 1)
  let lo := x % 4
  let n1 := y % 4 + 1
  let m := lpCopy (&mut a[lo..lo + n1]) (&b[y % 3..y % 3 + 4])
  hash8 a * 11 + m

def refLCopy (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let la := arrR x y
  let lb := arrR y (W (x + 1))
  let n := min (y % 4 + 1) 4
  let la := patchR la (x % 4) n fun k => W (lb[y % 3 + k]! + 1)
  UInt64.ofNat (W (hashR 7 la * 11 + n))

mp def lFind (x y : UInt64) : UInt64 := do
  let mut a := mkArr x y
  let lo := x % 3
  let len := y % 5 + 2
  let v := if y % 2 == 0 then x else y * 3 + 1
  let r := lpFind (&mut a[lo..lo + len]) v (x + y)
  hash8 a * 13 + r

def refLFind (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let l := arrR x y
  let lo := x % 3
  let len := y % 5 + 2
  let v := if y % 2 = 0 then x else W (y * 3 + 1)
  let s := sliceR l lo len
  let (l', r) := match (List.range s.length).find? fun i => s[i]! == v with
    | some i => (patchR l (lo + i) 1 fun _ => W (x + y), i + 1)
    | none => (l, 0)
  UInt64.ofNat (W (hashR 7 l' * 13 + r))

mp def lPt (x y : UInt64) : UInt64 := do
  let mut p : LPt := { x := x, y := y }
  let _ := lpPt (&mut p) (x ^^^ y)
  p.x * 31 + p.y

def refLPt (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let step := fun (st : Nat × Nat) (i : Nat) =>
    let px := W (st.1 * 3 + (x ^^^ y))
    (px, W (st.2 + px + i))
  let (px, py) := (List.range 6).foldl step (x, y)
  UInt64.ofNat (W (W (px * 31) + py))

mp def lNest (x y : UInt64) : UInt64 := do
  let mut s := x
  let mut t := y
  for i in 0...5 do
    s := s * 7 + i
    for j in 0...3 do
      if j ≥ (x % 4) then break
      t := t + s + j
  s ^^^ t

def refLNest (a : List UInt64) : UInt64 :=
  let (x, y) := toNat2 a
  let (s, t) := (List.range 5).foldl (fun (st : Nat × Nat) i =>
    let s := W (st.1 * 7 + i)
    let t := (List.range (min 3 (x % 4))).foldl (fun t j => W (t + s + j)) st.2
    (s, t)) (x, y)
  UInt64.ofNat (s ^^^ t)


/-- The loops that write through references, all of which `compile` accepts. -/
def loopFuncs : List TestFn :=
  [tfm2 "lFill" lFill.exp (fun a => (lFill a[0]! a[1]!).run) refSFill,
   tfm2 "lRev" lRev.exp (fun a => (lRev a[0]! a[1]!).run) refSRev,
   tfm2 "lPrefix" lPrefix.exp (fun a => (lPrefix a[0]! a[1]!).run) refLPrefix,
   tfm2 "lCopy" lCopy.exp (fun a => (lCopy a[0]! a[1]!).run) refLCopy,
   tfm2 "lFind" lFind.exp (fun a => (lFind a[0]! a[1]!).run) refLFind,
   tfm2 "lPt" lPt.exp (fun a => (lPt a[0]! a[1]!).run) refLPt,
   tfm2 "lNest" lNest.exp (fun a => (lNest a[0]! a[1]!).run) refLNest]

-- The references agree with the functions on a few inputs; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3)].all fun (x, y) =>
  loopFuncs.all fun f => f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]

end Millipede.Tests.Differential
