# Units

Systems code often mixes magnitudes of one kind, such as bytes and kibibytes or nanoseconds and
milliseconds, and a value in the wrong unit is a common mistake. Millipede lets a program tag a
word with its unit, so that Lean rejects an expression whose units do not agree. The tags exist
only while Lean checks the program, so they cost nothing when it runs. This document builds on
[language.md](language.md) and [obligations.md](obligations.md).

## Dimensions and units

A dimension is a kind of magnitude, such as size or time, and it is declared with
`mp dimension`. A unit belongs to one dimension and has a scale, which is its size in the
dimension's base unit, and it is declared with `mp unit`. The base unit should be the finest one,
so that every scale is a whole number. The library declares the following units:

```lean
mp dimension Size
mp unit byte : Size := 1
mp unit KiB : Size := 1024
mp unit MiB : Size := 1048576
mp unit page : Size := 4096

mp dimension Time
mp unit ns : Time := 1
mp unit us : Time := 1000
mp unit ms : Time := 1000000
mp unit sec : Time := 1000000000
```

## Quantities

A quantity of type `Q u` is a `UInt64` that counts units `u`. The literal `KiB 4` is four
kibibytes, and `q.val` is the count of a quantity `q` as a plain word, for use as an index.

Addition, subtraction and the comparisons need both operands in the same unit. Two units of one
dimension do not mix, because a silent conversion could hide an overflow or a rounding, and the
message says which conversion to write. The following function is rejected for this reason:

```lean
mp def bad1 (a : Q byte) (b : Q KiB) : Q byte := a + b
-- error: `+` needs quantities of the same unit, but the operands are Q byte (dimension Size)
-- and Q KiB (dimension Size): units of one dimension do not mix; convert with `.to byte`
```

There is no arithmetic of dimensions. A quantity is multiplied by a plain `UInt64`, and it is
divided by one with `/` or `%`, but two quantities cannot be multiplied. Bitwise operators and
shifts are not defined on quantities, so such code goes through `.val`.

## Conversions

A conversion changes the unit of a quantity within one dimension. A conversion to a finer unit,
such as `k.to byte` for `k` in KiB, multiplies the count, so it has the three forms of any
multiplication. `.to` wraps around, `.to?` returns a `Result`, and `.to!` carries the obligation
that the product fits in a word. A conversion between units of the same scale emits no code.

A conversion to a coarser unit divides the count, so it must say how to round. `.toFloor` rounds
down and `.toCeil` rounds up, and `.to` to a coarser unit is rejected. The following function
from the tutorial compares a count of bytes with a budget given in kibibytes:

```lean
mp def underBudget (seen : Q byte) (cap : Q KiB) requires cap ≤ 64
    ensures result = true → seen.toNat < cap.toNat * 1024 : Bool :=
  seen < cap.to! byte
```

The obligation of `cap.to! byte` follows from the precondition `cap ≤ 64`, and the analyser
proves such obligations when `requires` bounds the parameters. A bound may also be stated in base
units, as in `requires KiB.inBase off < 16 * 4096`.

## Specifications in base units

A specification is usually simplest in one unit. `u.inBase q` is the amount of a quantity `q` of
unit `u` in base units, a natural number equal to the count times the scale. The lemmas about
`inBase` are known to `simp` and `grind`, so a function that mixes units can be proved against a
specification written in base units. For a quantity `b` of bytes, `b.toFloor KiB` is the largest
whole number of kibibytes whose amount in base units is at most that of `b`.

Units are removed when `mp def` translates a function, so a program with units has the same
compiled code as the same program written with plain words. What is planned for
units and not built is listed in [../open-claims.md](../open-claims.md).
