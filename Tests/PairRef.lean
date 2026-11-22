import Millipede.Meta.MpDef
import Millipede.Top.Sound

/-!
# References to a pair of array elements

`&mut (a[i], a[j])` or `&(a[i], a[j])`, also written `a.pair! i j`, is a reference to two
elements of one array at once, with the obligation `i ≠ j`. `compile` lowers it as two
addresses, so the reference's fields `r.fst` and `r.snd` are the elements themselves, read and
written in place, and the whole array is lent while the borrow lives. This holds for scoped
borrows and for reference arguments, where a callee with a parameter `r : &mut (T × T)` gets the
two addresses.

This suite has a callee that swaps the pair it gets, a callee that updates fields of a pair of
structs and a shared pair. Their obligations are discharged by `mp def`, they run to the expected
values and `compile` accepts them, and a reactor whose step swaps two elements of its root
through a callee compiles. A pair reference used other than through its fields, copied whole or
carried whole by a loop, would live at two addresses, so `compile` refuses it.
-/

namespace Millipede.Tests.PairRef

open Millipede

def ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩

/-- Swaps the two components of the pair it gets by `&mut`. -/
mp def swapPair (r : &mut (UInt64 × UInt64)) : Unit := do
  let t := r.fst
  r.fst := r.snd
  r.snd := t
  ()

/-- Swaps two elements of an array through a callee that takes the pair `&mut (a[i], a[j])`. -/
mp def swapVia (a0 : Arr UInt64 4) (i j : UInt64)
    requires i.toNat < 4 ∧ j.toNat < 4 ∧ i.toNat ≠ j.toNat : Arr UInt64 4 := do
  let mut a := a0
  let _ := swapPair (&mut (a[i], a[j]))
  a

example : (swapVia #v[1, 2, 3, 4] 0 3).run.1 = #v[4, 2, 3, 1] := by decide
example : (swapVia #v[1, 2, 3, 4] 2 1).run.1 = #v[1, 3, 2, 4] := by decide
example : swapVia.exp.memOk = true := by decide

structure Cell where
  v : UInt64
  n : UInt64
deriving Data, DecidableEq, Repr, Inhabited

/-- Updates two cells of a table at once, writing the pair's components, which are structs,
field by field. -/
mp def bumpBoth (r : &mut (Cell × Cell)) (d : UInt64) : UInt64 := do
  r.fst.v := r.fst.v + d
  r.snd.n := r.snd.n + 1
  r.fst.n := r.snd.v
  r.fst.v + r.snd.n

mp def bumpVia (t0 : Arr Cell 3) (i j : UInt64)
    requires i.toNat < 3 ∧ j.toNat < 3 ∧ i.toNat ≠ j.toNat : Arr Cell 3 := do
  let mut t := t0
  let _ := bumpBoth (&mut (t[i], t[j])) 10
  t

example : (bumpVia #v[⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩] 2 0).run.1 = #v[⟨1, 3⟩, ⟨3, 4⟩, ⟨15, 1⟩] := by
  decide
example : bumpVia.exp.memOk = true := by decide

/-- A shared pair, read through its fields, and a shared pair argument. -/
mp def sumPair (r : &(UInt64 × UInt64)) : UInt64 := r.fst * 10 + r.snd

mp def readPairs (a : Arr UInt64 4) : UInt64 :=
  let s := (let r := &(a[0], a[3]); r.fst + r.snd)
  s + sumPair (&(a[2], a[1]))

example : (readPairs #v[1, 2, 3, 4]).run = 5 + 32 := by decide
example : readPairs.exp.memOk = true := by decide

/-! ## A reactor swapping two elements of its root -/

mp def rootInit : Arr UInt64 4 := #v[1, 2, 3, 4]

mp def rootStep (r : &mut Arr UInt64 4) : Unit :=
  let _ := swapPair (&mut (r[0], r[3]))
  let _ := swapPair (&mut (r[1], r[2]))
  ()

mp program swapProg (root : Arr UInt64 4) init rootInit step rootStep

#guard (swapProg.run ω0 1).1.toList == [4, 3, 2, 1]
#guard (swapProg.run ω0 2).1.toList == [1, 2, 3, 4]
example : swapProg.Safe := swapProg.safe
#guard (compile swapProg x64Linux).toBool

/-! ## What stays refused -/

/-- A pair reference copied whole. The checker and the value semantics accept it, and `compile`
refuses it because it lives at two addresses. -/
mp def copyWhole (a0 : Arr UInt64 4) : UInt64 := do
  let mut a := a0
  let s := (do let r := &mut (a[0], a[1]); let c := r; c.fst + c.snd)
  s

example : (copyWhole #v[1, 2, 3, 4]).run = 3 := by decide
example : copyWhole.exp.memOk = false := by decide

/-- A loop that writes a field of a pair borrow, which would carry the reference whole, is
refused. -/
mp def loopField (a0 : Arr UInt64 4) : Arr UInt64 4 := do
  let mut a := a0
  let _ := (do
    let r := &mut (a[0], a[1])
    for k in 0...3 do
      r.fst := r.fst + k)
  a

example : (loopField #v[1, 2, 3, 4]).run = #v[4, 2, 3, 4] := by decide
example : loopField.exp.memOk = false := by decide

end Millipede.Tests.PairRef
