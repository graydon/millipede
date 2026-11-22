import Millipede.Lib.ByteBuf
import Millipede.Top.Sound

/-!
# Tests for the slice helpers and the byte buffer

This suite runs the library's `fill`, `copy` and `reverse` on slices of arrays, with odd and
empty lengths and slices in the middle of an array, and checks that the memory lowering accepts
them and their callers. A caller's contract and obligations are proved from the helpers'
contracts. `ByteBuf.reverse` and `ByteBuf.append` are run on concrete buffers. Negated twins
show that wrong expectations are rejected.
-/

namespace Millipede.Tests.Slice

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-- The bytes `0, 1, …, 15`. -/
def iota16 : Arr UInt8 16 := Vector.ofFn fun i => UInt8.ofNat i.val

mp def fillMid (a0 : Arr UInt8 16) (lo hi : UInt64) (v : UInt8)
    requires lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ 16 : Arr UInt8 16 := do
  let mut a := a0
  let _ := Slice.fill (&mut a[lo..hi]) v
  a

mp def revMid (a0 : Arr UInt8 16) (lo hi : UInt64)
    requires lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ 16 : Arr UInt8 16 := do
  let mut a := a0
  let _ := Slice.reverse (&mut a[lo..hi])
  a

mp def copyMid (a0 b : Arr UInt8 16) (lo hi : UInt64)
    requires lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ 16 : Arr UInt8 16 := do
  let mut a := a0
  let _ := Slice.copy (&mut a[lo..hi]) (&b[0..3])
  a

mp def rev64 (x : UInt64) : Arr UInt64 8 := do
  let mut a := Vector.replicate 8 x
  a[0] := 1
  a[6] := 7
  let _ := Slice.reverse (&mut a[0..7])
  let _ := Slice.fill (&mut a[7..8]) 9
  a

example : (fillMid iota16 3 6 200).run.1 = #v[0, 1, 2, 200, 200, 200, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
  decide
example : (fillMid iota16 5 5 200).run.1 = iota16 := by decide
example : (revMid iota16 0 16).run.1 = #v[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] := by decide
example : (revMid iota16 2 7).run.1 = #v[0, 1, 6, 5, 4, 3, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
example : (revMid iota16 4 4).run.1 = iota16 := by decide
example : (copyMid iota16 (Vector.replicate 16 9) 10 16).run.1 =
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 13, 14, 15] := by decide
example : (copyMid iota16 (Vector.replicate 16 9) 14 16).run.1 =
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 9, 9] := by decide
example : (rev64 3).run = #v[7, 3, 3, 3, 3, 3, 1, 9] := by decide
-- Wrong expectations are rejected.
example : (revMid iota16 0 16).run.1 ≠ iota16 := by decide
example : (copyMid iota16 (Vector.replicate 16 9) 10 16).run.1 ≠ iota16 := by decide

/-! ## The memory lowering accepts them -/

example : (Slice.fill.exp UInt8 16 (by decide)).memOk = true := by decide
example : (Slice.copy.exp UInt8 16 (by decide)).memOk = true := by decide
example : (Slice.reverse.exp UInt8 16 (by decide)).memOk = true := by decide
example : (Slice.fill.exp UInt64 8 (by decide)).memOk = true := by decide
example : (Slice.copy.exp UInt64 8 (by decide)).memOk = true := by decide
example : (Slice.reverse.exp UInt64 8 (by decide)).memOk = true := by decide
example : fillMid.exp.memOk = true := by decide
example : revMid.exp.memOk = true := by decide
example : copyMid.exp.memOk = true := by decide
example : (ByteBuf.reverse.exp 16 (by decide)).memOk = true := by decide
example : (ByteBuf.append.exp 16 (by decide)).memOk = true := by decide

/-! ## A caller's contract from the helpers' contracts -/

/-- Fills a slice twice, passing the view on whole to the helper. The contract and the
obligations follow from the callee's contract, since the first call keeps the cells below the
length full. -/
mp def fillTwice (s : &mut [UInt64; 8]) (v w : UInt64)
    ensures ∀ k < 8, s'.cell k = if k < s.len.toNat then some w else s.cell k : Unit :=
  let _ := Slice.fill (&mut s) v
  let _ := Slice.fill (&mut s) w
  ()

example : fillTwice.exp.memOk = true := by decide

mp prove fillTwice.spec := by mp_auto [Slots.isFull]
mp prove fillTwice.safe := by mp_auto [Slots.isFull]

/-! ## The byte buffer -/

def buf (n : Nat) : ByteBuf 16 := ⟨iota16, UInt64.ofNat n⟩

example : (ByteBuf.reverse 16 (by decide) (buf 5)).run.2.1.bytes =
    #v[4, 3, 2, 1, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
example : (ByteBuf.append 16 (by decide) (buf 3) (vview iota16 8 4) 4).run.1 = 4 := by decide
example : (ByteBuf.append 16 (by decide) (buf 3) (vview iota16 8 4) 4).run.2.1.bytes =
    #v[0, 1, 2, 8, 9, 10, 11, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Only the free space is filled.
example : (ByteBuf.append 16 (by decide) (buf 14) (vview iota16 8 4) 4).run.1 = 2 := by decide
example : (ByteBuf.append 16 (by decide) (buf 14) (vview iota16 8 4) 4).run.2.1.len = 16 := by decide

end Millipede.Tests.Slice
