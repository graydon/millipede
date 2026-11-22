# Statements

The body of an `mp def` is either an expression or a block of statements introduced by `do`. A
block is written in the notation of Lean's `do` blocks and parsed by Lean, but Millipede gives it
its meaning and accepts only the forms described here.

| form | does |
|---|---|
| `let x := e`, `let x : T := e` | binds `x` for the rest of the block |
| `let mut x := e` | binds a variable that can be assigned |
| `x := e`, `p.f := e`, `a[i] := e`, `a[i]! := e` | assigns a variable or a part of one |
| `if c then … else if c then … else …` | runs one branch |
| `match e with \| … => …` | runs the arm of the value's constructor |
| `for i in lo...hi do …`, `for i in lo...=hi do …` | a bounded loop |
| `break`, `continue` | leaves the loop, or ends the current iteration |
| `return e` | leaves the function |
| `(do …)` | a nested block |
| `e` | a call or other expression |

## Blocks

A block is a sequence of statements that run in order. The value of the last statement is the
value of the block, and every other statement must have the type `Unit`. A value that is not
needed is bound to `_`, as in `let _ := f (&mut a)`, and a statement whose value would be
discarded is rejected.

```lean
mp def jumps (x : UInt64) : UInt64 := do
  let mut s := 0
  let mut n := 0
  for i in 0...10 do
    if i % 3 == 0 then continue
    s := s + i
    if s > x then break
    n := n + 1
  s * 100 + n
```

A statement that follows `break`, `continue` or `return` in the same block can never run, and it
is rejected as unreachable.

## Bindings

`let x := e` evaluates `e` and binds its value to `x` for the rest of the block. The type may be
given, as in `let x : Arr UInt64 3 := #v[40, 91, 123]`. A binding may shadow an earlier variable
of the same name, but not a reference.

`let mut x := e` binds a variable that later statements may assign. Only a variable bound with
`let mut`, or a parameter or borrow of mode `&mut`, can be assigned.

## Assignments

An assignment replaces the value of a variable or of a part of one. `x := e` assigns the
variable `x`, `p.f := e` assigns the field `f` of `p`, and `a[i] := e` assigns an element of an
array or a slice. The index of an assigned element follows the same rules as a read, so
`a[i]! := e` assigns with the obligation that `i` is in range. `Tests/Reactor.lean` assigns
fields through an exclusive reference:

```lean
mp def rPush (r : &mut Ring) (c : UInt64) requires RInv r ∧ r.n.toNat < 8
    ensures RInv r' : Unit := do
  let k := Pool8.alloc! (&mut r.pool) c
  let i := r.n
  let _ := r.keys.put! i k
  r.n := i +! 1
  ()
```

An assignment must be a statement of the block that binds its variable, or of a block nested in
it by `if`, `match` or `for`. An assignment inside the value of a `let`, as in
`let _ := if c then (do x := 1) else ()`, is rejected, because its effect would be lost at the
end of that value.

## Conditionals

`if c then s₁ else s₂` runs `s₁` when the condition `c` is true and `s₂` otherwise. The `else`
part may be another `if`, and as a statement it may be left out, in which case nothing runs when
`c` is false. The rest of the block runs after whichever branch ran.

```lean
mp def enter (d : &mut Depth) requires d.cur < 8 ∧ d.max ≤ 8
    ensures d'.cur = d.cur + 1 ∧ d'.max ≤ 8 : Unit := do
  d.cur := d.cur +! 1
  if d.max < d.cur then d.max := d.cur
```

The forms `if let` and `if h : c` are not supported.

## Match

A `match` takes apart a `Result` or a value of a derived enum. It has exactly one arm for each
constructor, and each arm binds the constructor's field, if it has one. A missing or duplicate
arm is rejected.

```lean
mp def useR (r : Result UInt64 UInt64) : UInt64 :=
  match r with
  | ok a => a
  | err e => e
```

The arms of an enum's `match` name the constructors as `.add n` or `Cmd.add n`. A `match h : e`
form is not supported.

## Loops

The only loop is `for i in lo...hi do body`, which runs the body once for each value of the
counter `i` from `lo` up to, but not including, `hi`. The form `for i in lo...=hi` includes
`hi`. Both bounds are evaluated once, before the first iteration, and when `lo` is greater than
`hi` the body does not run.

```lean
mp def ranges (x : UInt64) : UInt64 := do
  let mut a := 0
  for i in 3...6 do
    a := a * 10 + i
  for i in 1...=2 do
    a := a * 10 + i
  for i in 5...2 do
    a := a + 1000000
  for i in x...4 do
    a := a * 10 + i
  a
```

The lower bound may be any word. The upper bound must be a size expression, so that the number
of iterations has a limit known before the program runs. A size expression is a numeric literal,
a `Nat` constant or variable, the length `s.len` of a slice, or a combination of these by `+`,
`-` and `*`, or by `/` and `%` with a positive literal. These operations have their meaning on
natural numbers, so `-` stops at zero. A bound known only at run time is written `min e N`, where
`N` is a size expression that caps it:

```lean
mp def capped (n : UInt64) : UInt64 := do
  let mut n := n
  let mut c := 0
  for i in 0...min n 5 do
    n := n + 1
    c := c + 1
  c * 100 + n
```

An inclusive upper bound must be below 2^64 − 1, since the counter would otherwise wrap around.
A loop over a list or any other collection is not supported.

A loop body may assign variables bound outside the loop, and after the loop each holds the last
value assigned to it. The counter may not have the name of a variable the body assigns. A linear
variable bound outside the loop cannot be used inside it, because the body may run any number of
times. When `if c then break` is the first statement of the body, `c` must not use a linear
variable.

## Break and continue

`break` leaves the innermost loop, and execution continues after it. `continue` ends the current
iteration, and the loop goes on with the next value of the counter. Either one outside a loop is
rejected. The function `jumps` above uses both.

## Return

`return e` leaves the function at once with the value `e`. Inside a loop it also leaves every
enclosing loop.

```lean
mp def kindOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3
```

The value returned from inside a loop is held in a variable until the loops end, so a function
that returns from inside a loop must have a result type that is not linear and that has a
default value. `return` inside a nested `(do …)` block is not supported.

## Nested blocks

`(do …)` is a block used as an expression, for instance as a branch of an `if` expression. It
follows the rules of a block, except that it cannot contain `return`.

## Forms that are not supported

Some forms of Lean's `do` notation are not part of Millipede, and each is rejected with a message
at its position. They are `while` and `repeat`, `try`, `catch` and `finally`, the arrow `←`,
`unless`, `if let`, `if h : c`, `match h : e`, `for` over anything but a range, and `return` in a
nested block. The message for `unless` suggests `if !c then …`, and the one for `while` suggests
a bounded loop left with `if c then break`.
