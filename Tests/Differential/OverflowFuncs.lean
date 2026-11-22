import Tests.Differential.SlotFuncs

/-!
# Differential tests of checked and wrapping arithmetic

Each function is an `mp def` over two words that runs through the whole pipeline under qemu and is
compared with a reference in plain Lean over `Nat`. `ovWord` matches both outcomes of the checked
forms `+? -? *?` on words and also uses the wrapping forms `+ - *`. `ovByte` does the same on
bytes, where the checked forms test the word result against 255 before narrowing it and the
wrapping forms mask it.

The forms with an obligation compile to the same instruction as the wrapping forms, so they add
no code path to the backend and no mutant. The existing mutants of arithmetic and of bytes apply
to these functions too.
-/

namespace Millipede.Tests.Differential

open Millipede

set_option mp.autoSafe false

mp def ovWord (x y : UInt64) : UInt64 :=
  let s := match x +? y with
    | ok v => v
    | err _ => 1
  let d := match x -? y with
    | ok v => v
    | err _ => 2
  let p := match x *? y with
    | ok v => v
    | err _ => 3
  let q := match (x >>> 33) *? (y >>> 31) with
    | ok v => v
    | err _ => 4
  ((s ^^^ (d <<< 1)) ^^^ ((p <<< 2) ^^^ (q <<< 3))) + (x * y) - (y + 7)

/-- A checked operation's result over `Nat`, which is `none` when it does not fit in `bits` bits. -/
def chkR (bits : Nat) (r : Int) : Option Nat :=
  if 0 ≤ r ∧ r < 2 ^ bits then some r.toNat else none

def refOvWord (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let s := (chkR 64 (x + y)).getD 1
  let d := (chkR 64 ((x : Int) - y)).getD 2
  let p := (chkR 64 (x * y)).getD 3
  let q := (chkR 64 ((x / 2 ^ 33) * (y / 2 ^ 31))).getD 4
  let mix := (s ^^^ W (d * 2)) ^^^ (W (p * 4) ^^^ W (q * 8))
  UInt64.ofNat (W (W (mix + W (x * y)) + 2 ^ 64 - W (y + 7)))

mp def ovByte (x y : UInt64) : UInt64 :=
  let a := x.toUInt8
  let b := y.toUInt8
  let s := match a +? b with
    | ok v => v
    | err _ => 1
  let d := match a -? b with
    | ok v => v
    | err _ => 2
  let p := match a *? b with
    | ok v => v
    | err _ => 3
  let w := (a + b) * (a - b)
  s.toUInt64 ||| (d.toUInt64 <<< 8) ||| (p.toUInt64 <<< 16) ||| (w.toUInt64 <<< 24)

def refOvByte (l : List UInt64) : UInt64 :=
  let (x, y) := toNat2 l
  let a := x % 256
  let b := y % 256
  let s := (chkR 8 (a + b)).getD 1
  let d := (chkR 8 ((a : Int) - b)).getD 2
  let p := (chkR 8 (a * b)).getD 3
  let w := ((a + b) % 256 * ((a + 256 - b) % 256)) % 256
  UInt64.ofNat (s ||| (d <<< 8) ||| (p <<< 16) ||| (w <<< 24))


/-- The checked and wrapping arithmetic functions, all of which `compile` accepts. -/
def overflowFuncs : List TestFn :=
  [tfm2 "ovWord" ovWord.exp (fun a => (ovWord a[0]! a[1]!).run) refOvWord,
   tfm2 "ovByte" ovByte.exp (fun a => (ovByte a[0]! a[1]!).run) refOvByte]

-- The references agree with the functions on a few inputs, which give both outcomes of every
-- check; the generator checks the rest.
#guard [(0, 0), (1, 2), (5, 3), (7, 11), (100, 9), (2 ^ 63, 3), (2 ^ 63, 2 ^ 63),
    (0xFFFFFFFFFFFFFFFF, 1), (0x100000000, 0xFFFFFFFF), (0x100000000, 0x100000000), (200, 55),
    (200, 56), (16, 15), (16, 16), (3, 4), (0x1FF, 0x2FF)].all fun (x, y) =>
  overflowFuncs.all fun f => f.fn [UInt64.ofNat x, UInt64.ofNat y] == f.ref [UInt64.ofNat x, UInt64.ofNat y]
-- the references see the checks
#guard refOvWord [0xFFFFFFFFFFFFFFFF, 1] != refOvWord [0xFFFFFFFFFFFFFFFE, 1]
#guard refOvByte [200, 56] != refOvByte [200, 55]

#guard overflowFuncs.all fun f => f.exp.memOk

end Millipede.Tests.Differential
