# Places, linear values and references

This document describes how a Millipede function holds values, moves them and refers to them.
It builds on the types and statements described in [language.md](language.md).

## Places

A place is a variable or a part of one, named by a path such as `p.f` or `a[i]`. Assignment
writes to a place, and a reference refers to one. Reading a place copies its value when the
value's type is not linear, and moves it otherwise. A linear value can be moved out of a whole
variable, or with `take!` out of a cell of a `Slots` value, an array whose cells may be empty, but
it is never copied out of a part of another value.

## Linear types

A type is linear when each of its values must be used exactly once. `Result` is linear, and so
are the keys that name the cells of a pool arena and any structure or enum with a linear field. Using a linear value
moves it out of the variable that held it, after which the variable cannot be used again. A value
of any other type is copied each time it is used.

Before a function is accepted, a checker examines how it uses its variables and references,
and it rejects the function with a message at the position of each violation. For linear
values it enforces the following rules:

- A linear value is used exactly once on every path through the function, so a second use is an
  error, and so is a path on which the value is not used at all.
- The two branches of an `if`, and the arms of a `match`, use the same linear variables.
- The body of a loop does not move a linear variable bound outside the loop, because the body may
  run any number of times. The exception is a variable that the loop assigns, whose value the body
  may use as long as it assigns a new value before the iteration ends.
- A linear value is never copied out of a place, and a place that holds one is never overwritten,
  since either would use the value twice or lose it.

The following function is rejected because it never uses `r`:

```lean
mp def dropsResult (x : UInt64) : UInt64 :=
  let r : Result UInt64 UInt64 := ok x
  x
```

A variable declared with `let mut` may hold a linear value. The assignment `x := e` then gives
`x` a new value, and it is accepted when the old value of `x` is used before or by `e`, so that
no value is lost. In the following function, each call of `bumpR` takes the old value of `r` and
returns the new one:

```lean
mp def linStraight (x : UInt64) : UInt64 := do
  let mut r : Result UInt64 UInt64 := ok x
  r := bumpR r
  r := bumpR r
  useR r
```

## References

A reference gives access to a place without moving the value out of it. A shared reference `&p`
allows reading the place, and an exclusive reference `&mut p` allows reading and writing it. To
borrow a place is to create a reference to it.

A reference is created either by passing `&p` or `&mut p` as the argument of a reference
parameter, or by binding it with `let r := &mut p` or `let r := &p`. A borrow passed to a call
lasts for the call, and one bound by `let` lasts to the end of the block. A parameter is declared
as a reference by giving it the type `&T` or `&mut T`.

Inside a function, a reference is used by its name as if it were the place itself, so reading `a`
reads the place that `a` refers to and assigning to `a` writes that place. The following function
swaps the values of two places:

```lean
mp def swap (a : &mut UInt64) (b : &mut UInt64) : Unit := do
  let t := a
  a := b
  b := t
  ()
```

A reference cannot be stored in a field or an array, and a function cannot return one. A
reference therefore never outlives the call or block that created it, and the language needs no
lifetimes.

## Borrowing

A borrow is live while its reference can still be used. Two places overlap when one contains the
other, as `p` contains `p.f`. While a borrow of `p` is live, the checker restricts the use of every
place that overlaps `p`:

- While `&mut p` is live, an overlapping place is used only through the reference.
- While `&p` is live, overlapping places may be read, but not written, moved or borrowed with
  `&mut`.
- Any number of shared borrows of one place may be live at the same time.

Different fields of a structure do not overlap, so they can be borrowed at the same time. In the
following function, `Pt` is a structure with the fields `x` and `y`:

```lean
mp def swapXY (p0 : Pt) : Pt := do
  let mut p := p0
  let _ := swap (&mut p.x) (&mut p.y)
  p
```

The checker cannot tell whether two indices differ, so it treats any two elements of an array as
overlapping. To borrow two elements at once, a function borrows the pair `&mut (a[i], a[j])`,
which carries the obligation that `i` and `j` are in range and differ, and is used through its
fields `fst` and `snd`. In the
following function, `swapPair` swaps the two fields of the pair it is given:

```lean
mp def swapVia (a0 : Arr UInt64 4) (i j : UInt64)
    requires i.toNat < 4 ∧ j.toNat < 4 ∧ i.toNat ≠ j.toNat : Arr UInt64 4 := do
  let mut a := a0
  let _ := swapPair (&mut (a[i], a[j]))
  a
```

## Slices

A slice is a reference to a run of consecutive elements of an array, written `&a[lo..hi]` or
`&mut a[lo..hi]`. A function that takes a slice declares the parameter with the type `&[T; n]` or
`&mut [T; n]`, where `n` is the length of the array the slice is taken from. The slice itself may
be shorter, and its length is `s.len`. Its elements are read and written as `s[i]`, and the slice
may be passed on whole to another function. The following function fills a slice in place:

```lean
mp def fillS (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  for i in 0...s.len do
    s[i] := v * 3 + i
```

The library provides `Slice.fill`, `Slice.copy` and `Slice.reverse`, which fill, copy and reverse
a slice in place, for any length and any element type that may be copied.

## References in the meaning of a function

In the Lean function that `mp def` defines, an exclusive reference parameter becomes an extra
result, so the function returns its result together with the final value of each such
parameter. A postcondition names the final value of a parameter `d` as `d'`. In the following
function, `Depth` is a structure with the fields `cur` and `max`:

```lean
mp def enter (d : &mut Depth) requires d.cur < 8 ∧ d.max ≤ 8
    ensures d'.cur = d.cur + 1 ∧ d'.max ≤ 8 : Unit := do
  d.cur := d.cur +! 1
  if d.max < d.cur then d.max := d.cur
```

In the meaning of a function, an exclusive borrow reads the place when the borrow begins and
writes it back when the borrow ends. The compiled code passes a pointer instead, and the
compiler's correctness theorem shows that both give the same result.
