# Types and expressions

This part of the reference describes the types of Millipede values and the expressions that
compute them. Expressions are written as Lean terms and parsed by Lean, but inside an `mp def`
Millipede gives them their meaning and accepts only the forms described here.

| form | meaning |
|---|---|
| `x`, `p.f`, `a[i]` | a variable, a field, an element |
| `a[i]!`, `a[i]?` | an element with an obligation, or checked |
| `s.put! i v`, `s.take! i` | fills or empties a cell of `Slots` |
| `{ x := a }`, `{ p with x := v }`, `S.mk a b`, `⟨a, b⟩` | structure values |
| `E.c a`, `.c a`, `ok a`, `err e` | enum and `Result` values |
| `#v[a, b]`, `Vector.replicate n a`, `Slots.empty n` | array and `Slots` values |
| `&p`, `&mut p` | a shared or exclusive reference |
| `a[lo..hi]`, `a[lo:hi]` | a slice |
| `&mut (a[i], a[j])`, `a.pair! i j` | two elements borrowed together |
| `a + b`, `a - b`, `a * b` | wrapping arithmetic |
| `a +! b`, `a -! b`, `a *! b` | arithmetic with an obligation |
| `a +? b`, `a -? b`, `a *? b` | checked arithmetic |
| `/ % &&& \|\|\| ^^^ <<< >>>` | other word operations |
| `== != < <= > >=`, `&&`, `\|\|`, `!` | comparisons and logic |
| `x.toUInt64`, `x.toUInt8` | widening and narrowing |
| `KiB e`, `q.val`, `q.to u`, `q.to! u`, `q.to? u`, `q.toFloor u`, `q.toCeil u` | quantities |
| `let x := e; k`, `if c then a else b`, `match` | as in a block |
| `f x (&mut y)` | a call |

## Types

Every value has a type, which fixes its layout in memory and whether it may be copied.

The scalar types are `UInt64`, `UInt8` and `Bool`. A `UInt64` is an unsigned 64-bit word, a
`UInt8` is a byte, and a `Bool` is `true` or `false`. A numeric literal is a word, or a byte
where a byte is expected, and it must fit. The type `Unit` has the single value `()`, and a pair
of an `A` and a `B` has the type `A × B`.

`Arr T n` is an array of `n` elements of type `T`. `Slots T n` is an array of `n` cells, each of
which is either empty or holds a value of type `T`. Whether a cell is full is known only to
proofs, because the cells carry no tag at run time.

A value of type `Result ε α` is either `ok a` with `a : α` or `err e` with `e : ε`. `Result` is
linear, so a result must be taken apart with `match`, and an error cannot be ignored.

Structures and enums declared with `deriving Data` are types, as described in
[definitions.md](definitions.md). A quantity `Q u` is a word tagged with the unit `u`.

A value of a linear type must be used exactly once. Such a value cannot be copied out of a place,
a variable that holds one cannot be used after it was moved, and every path through the function
must use it the same number of times. The rules for linear values are given in
[../design/memory.md](../design/memory.md).

## Places

A place is a part of memory that holds a value: a variable `x`, a field `p.f` of a place, or an
element `a[i]` of an array. Reading a place gives its value.

The plain index `a[i]` is accepted only when `i` is known to be in range. This is the case for a
literal below the array's length, and for the counter of an enclosing loop whose upper bound is
at most the length. Any other index uses one of the two forms that follow.

`a[i]!` reads the element with the obligation that `i` is in range, which must be proved before
the program can be compiled. `a[i]?` tests the index when the program runs and gives a
`Result Unit T`, `ok` with the element or `err ()`:

```lean
mp def getChk (a : Arr UInt64 4) (i : UInt64) : Result Unit UInt64 := a[i]?
```

## Slots

The cells of a `Slots` value are read and written only by forms that carry obligations, since a
cell's state is not known at run time. `s[i]!` reads a cell with the obligation that it is full.
`s.put! i v` fills a cell with the obligation that it is empty, and `s.take! i` empties a full
cell and gives its value. `Slots.empty n` is a value whose cells are all empty. There is no
checked form.

```lean
mp def slotsDemo (s0 : Slots UInt64 2) requires s0.isVacant 0 = true : UInt64 := do
  let mut s := s0
  let _ := s.put! 0 7
  let x := s.take! 0
  x + 1
```

## Constructed values

A structure value is written `{ x := a, y := b }`, `S.mk a b` or `⟨a, b⟩`, and a copy of `p`
with one field changed is written `{ p with x := v }`. An enum value is written `E.c a` or
`.c a`, and a `Result` value `ok a` or `err e`. When the type of a `Result` cannot be inferred,
it is given with an ascription such as `(ok 3 : Result UInt64 UInt64)`.

An array value is written `#v[a, b, c]`, or `Vector.replicate n a` for `n` copies of `a`.
`Tests/Reactor.lean` builds a root from such values:

```lean
mp def rInit ensures RInv result : Ring :=
  { pool := Pool8.new, keys := Slots.empty 8, n := 0, seen := 0, sum := 0 }
```

A sealed structure cannot be built outside its own module, and its fields cannot be written
there. A structure is sealed when its Lean constructor is `private`. The library's arena keys are
sealed, so that client code cannot forge one.

A library may also provide constructors of its own. A Lean constant of type `Ctor ps t` is
applied like a function, and the pool arena makes and consumes its keys this way.

## References and borrows

A reference gives access to a place without copying it. `&p` is a shared reference, through
which the place can only be read, and `&mut p` is an exclusive reference, through which it can
also be written. A reference is passed as the argument of a call whose parameter has the matching
mode:

```lean
mp def rStep (r : &mut Ring) requires RInv r ensures RInv r' : Unit := do
  let c := rRead 0
  if c < 256 && underBudget (byte r.seen) then
    r.seen := r.seen +! 1
    if r.n < 8 then rPush (&mut r) c
```

A reference may also be bound by `let r := &mut p`, which borrows the place until the end of the
block. While an exclusive borrow is live, the place and every place that overlaps it may be used
only through the reference. While a shared borrow is live, the place may be read but not written.
The same rules hold for the duration of a call that takes a reference argument. Nothing can be
assigned through a shared reference, and a linear value cannot be moved out of one.

## Slices

A slice is a run of consecutive elements of an array. `a[lo..hi]` is the slice of the elements
from `lo` up to, but not including, `hi`, and `a[lo:hi]` is the same slice. A slice is only
borrowed or passed by reference, as `&a[lo..hi]` or `&mut a[lo..hi]`.

```lean
mp def sumToks (a : Arr UInt8 64) (len : UInt64) requires len.toNat ≤ 64 : UInt64 := do
  let mut pos := 0
  let mut sum := 0
  for k in 0...64 do
    if pos ≥ len then break
    let e := tokEnd (&a[0..len]) pos
    let v := if pos ≤ e && e ≤ len then parseNum (&a[pos..e]) else 0
    sum := sum + v
    pos := e + 1
  sum
```

A slice parameter or a borrowed slice `s` has the length `s.len`. Its elements are `s[i]` and
`s[i]!`, and the loop `for i in 0...s.len` runs over them. A slice is not assigned whole. The
slice parameters that receive it are described in [definitions.md](definitions.md).

## Pairs of elements

Two elements of one array can be borrowed together with `&mut (a[i], a[j])`, which carries the
obligation `i ≠ j`. The callee receives a reference to a pair and uses its fields `fst` and
`snd`. `a.pair! i j` is the same pair of places.

```lean
mp def swapVia (a0 : Arr UInt64 4) (i j : UInt64)
    requires i.toNat < 4 ∧ j.toNat < 4 ∧ i.toNat ≠ j.toNat : Arr UInt64 4 := do
  let mut a := a0
  let _ := swapPair (&mut (a[i], a[j]))
  a
```

## Arithmetic

Each of `+`, `-` and `*` on words and on bytes has three forms, which differ in what happens when
the result does not fit.

The plain forms `a + b`, `a - b` and `a * b` wrap around, as in C. They carry no obligation.

The forms `a +! b`, `a -! b` and `a *! b` carry the obligation that the mathematical result fits,
which must be proved before the program can be compiled. They compile to the same instruction as
the plain forms, and they suit sizes, indices and budgets, where a result that wrapped would be
wrong.

The forms `a +? b`, `a -? b` and `a *? b` test the result when the program runs and give a
`Result Unit T`, which is `ok` with the result exactly when it fits. `Tests/Overflow.lean` has
one function of each kind:

```lean
mp def addW (x y : UInt64) : UInt64 := x + y
mp def addO (x y : UInt64) : UInt64 := x +! y
mp def addC (x y : UInt64) : Result Unit UInt64 := x +? y
```

## Other operations

`/` and `%` divide words or bytes, and division by zero gives zero while `x % 0` is `x`. The
bitwise operations are `&&&`, `|||` and `^^^`, and the shifts are `<<<` and `>>>`. A byte cannot
be shifted, so a shift of a byte is written by widening it, shifting and narrowing it again.

The comparisons `==`, `!=`, `<`, `<=`, `>` and `>=` give a `Bool`. Equality is defined on words,
bytes and `Bool` only. `a && b` and `a || b` evaluate `b` only when `a` does not decide the
result, so `b` may carry an obligation that holds only when it is evaluated:

```lean
mp def shortInc (i : UInt64) : Bool := i < 100 && i +! 1 < 50
```

`x.toUInt64` widens a byte to a word, and `x.toUInt8` narrows a word to its low byte. Neither
applies to a `Bool`.

## Quantities

A quantity of type `Q u` is a word that counts units `u`. `KiB e` makes a quantity from the word
`e`, and `q.val` gives back the count. Neither costs anything at run time, and a bare numeral is
always a word, never a quantity.

The operations `+`, `-` and the comparisons need quantities of the same unit on both sides. `*`
multiplies a quantity by a `UInt64`, and `/` and `%` divide a quantity by a `UInt64`. The bitwise
operations and shifts are not defined on quantities. A mismatch is reported at the operand, with
both units named.

A quantity is converted to another unit of the same dimension. `q.to u` converts to a finer unit
and wraps around when the result does not fit, `q.to! u` does the same with the obligation that
it fits, and `q.to? u` gives a `Result`. `q.toFloor u` and `q.toCeil u` convert to a coarser unit
and round down or up. Converting to a coarser unit with `to` is rejected, because it would round,
and converting to a finer one with `toFloor` or `toCeil` is rejected, because it is exact.
`Tests/Units.lean` adds sizes given in three units:

```lean
mp def sizeO (n : Q page) (hdr : Q KiB) (tail : Q byte) : Q byte :=
  n.to! byte +! hdr.to! byte +! tail
```

Units and dimensions are declared as described in [definitions.md](definitions.md).

## Calls

A call `f a b` runs an earlier `mp def` or `mp extern` with the given arguments, and its value is
the callee's result. An argument for a value parameter is any expression of the parameter's type.
An argument for a reference parameter is a reference to a place, `&p` or `&mut p`, and a call
that gives a value where a reference is expected, or a reference where a value is expected, is
rejected. A call to a function with a precondition adds the precondition at the arguments to the
caller's obligations.

A call to a generic function infers the function's variables as described in
[definitions.md](definitions.md), and a variable may be given by name, `f (x := e) a b`.
