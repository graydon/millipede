import Tests.Differential.Funcs
import Millipede.Lib.Units

/-!
# Differential tests of unit conversions

These functions over quantities are erased to functions on words, compiled and run under qemu
like the other differential functions. Each is compared with a reference in `Nat` arithmetic
that is written from the meaning of the conversion, the floor or ceiling in base units, and not
from the code that `mp def` emits.

Seeded bugs were tried once by hand and reverted. With the ratio of `.to` inverted, or with
`.toFloor` and `.toCeil` swapped, `lake exe differential gen` stops with the message that the
reference, the `mp def` function and the denotation disagree.
-/

namespace Millipede.Tests.Differential

open Millipede Millipede.Lib

set_option mp.autoSafe false

mp def uRegion (n : Q page) (hdr : Q KiB) (tail : Q byte) : Q byte :=
  n.to byte + hdr.to byte + tail

def refURegion (a : List UInt64) : UInt64 :=
  UInt64.ofNat ((a[0]!.toNat * 4096 + a[1]!.toNat * 1024 + a[2]!.toNat) % 2 ^ 64)

mp def uCeil (b : Q byte) : Q KiB := b.toCeil KiB

def refUCeil (a : List UInt64) : UInt64 := UInt64.ofNat ((a[0]!.toNat + 1023) / 1024)

mp def uFloor (b : Q byte) : Q page := b.toFloor page

def refUFloor (a : List UInt64) : UInt64 := UInt64.ofNat (a[0]!.toNat / 4096)

mp def uCeilSec (t : Q ns) : Q sec := t.toCeil sec

def refUCeilSec (a : List UInt64) : UInt64 :=
  UInt64.ofNat ((a[0]!.toNat + 999999999) / 1000000000)

/-- The checked conversion, which returns `2^64 - 1` on overflow. -/
mp def uChk (m : Q MiB) : UInt64 :=
  match m.to? KiB with
  | ok k => k.val
  | err _ => 18446744073709551615

def refUChk (a : List UInt64) : UInt64 :=
  let k := a[0]!.toNat * 1024
  UInt64.ofNat (if k < 2 ^ 64 then k else 2 ^ 64 - 1)

/-- Scalars, comparisons and a round trip through a coarser unit. -/
mp def uMixed (a b : Q ms) : UInt64 :=
  let c := a * 3 + b / 2
  let s := c.toFloor sec
  let back := s.to ms
  if back <= c && c - back < (sec 1).to ms then s.val else 0

def refUMixed (a : List UInt64) : UInt64 :=
  let c := (a[0]!.toNat * 3 + a[1]!.toNat / 2) % 2 ^ 64
  UInt64.ofNat (c / 1000)

def unitFuncs : List TestFn :=
  [tf3 "uRegion" uRegion.exp (fun a => (uRegion a[0]! a[1]! a[2]!).run) refURegion,
   tf1 "uCeil" uCeil.exp (fun a => (uCeil a[0]!).run) refUCeil,
   tf1 "uFloor" uFloor.exp (fun a => (uFloor a[0]!).run) refUFloor,
   tf1 "uCeilSec" uCeilSec.exp (fun a => (uCeilSec a[0]!).run) refUCeilSec,
   tf1 "uChk" uChk.exp (fun a => (uChk a[0]!).run) refUChk,
   tf2 "uMixed" uMixed.exp (fun a => (uMixed a[0]! a[1]!).run) refUMixed]

-- On edge inputs the reference and the `mp def` function agree, which is the Lean side of the
-- check that `differential gen` runs.
#guard unitFuncs.all fun f => (List.range 40).all fun i =>
  let edge : List UInt64 := [0, 1, 1023, 1024, 1025, 4095, 4096, 999999999, 1000000000,
    18014398509481984, 18014398509481983, 9223372036854775808, 18446744073709551615,
    18446744073709550592]
  let xs := (List.range f.arity).map fun j => edge[(i + 5 * j) % 14]!
  f.fn xs == f.ref xs

end Millipede.Tests.Differential
