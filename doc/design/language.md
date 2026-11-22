# The Millipede language

Millipede is a small imperative language embedded in Lean, so that a program and the proofs
about it are written in the same files. A Millipede function is written with the command
`mp def`. Lean checks the function and gives it a meaning as an ordinary Lean function, which is
what the proofs are about. Millipede's compiler turns the same function into machine code.

The following function returns the position of the character code `c` in a table of three
opening brackets, or 3 when `c` is not one of them:

```lean
mp def kindOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3
```

Its body is a block of statements written in the notation of Lean's `do` blocks. The clause
`ensures result ≤ 3` is a postcondition, a promise about the result which is proved when the
function is defined.

This document describes what a function can compute: its types, expressions, statements and
loops, how errors are handled or proved absent, and how functions make up a program. How values
are held, moved and borrowed is described in [memory.md](memory.md), and the arena library in
[arenas.md](arenas.md). Every form of the language is listed in the
[surface reference](../reference/surface.md).

## Types

Every value has a type, which fixes how the value is laid out in memory and whether it may be
copied.

The scalar types are `UInt64`, `UInt8` and `Bool`. A `UInt64` is an unsigned 64-bit word, a
`UInt8` is a byte, and a `Bool` is either `true` or `false`. The type `Unit` has the single value
`()`, which is the value of a statement that produces nothing. A pair of an `A` and a `B` has
the type `A × B`.

`Arr T n` is an array of `n` elements of type `T`, written as `#v[40, 91, 123]`. The length is
part of the type, so an index can be compared with it when the function is defined.

A value of type `Result ε α` is either `ok a`, a result of type `α`, or `err e`, an error of type
`ε`. `Result` is linear. A linear value must be used exactly once, so an error cannot be ignored.
The rules for linear values are given in [memory.md](memory.md).

A Lean type becomes usable in Millipede when it is declared with `deriving Data`, which fixes its
layout in memory. A structure declared this way keeps its fields in declaration order, laid out
as a C compiler would lay them out. An enum is a Lean `inductive` with at least two
constructors, each of which has at most one field, and it is laid out as a tag followed by that
field. A constructor that needs several fields takes a structure. A structure or enum is linear
when any of its fields is linear.

A type may not contain itself, so a list or a tree cannot be declared directly. Its nodes are kept
instead in an arena, a library value that holds many values of one type, and linked by indices.

A field may hold ghost data, which exists only for proofs, so it takes no space and no code is
compiled for it. A field whose type is a Lean proposition is ghost data, and so is a field of type
`Ghost α` for any Lean type `α`. Millipede code can neither build a structure that has a
proposition field nor read or write that field.

A quantity `Q u` is a `UInt64` tagged with a unit `u`, such as bytes or kibibytes. Lean checks
that the units of an expression agree, and the tag costs nothing at run time. Units are described
in [units.md](units.md).

## Expressions

Expressions are written as in Lean. Arithmetic and comparison work on words and on bytes, and the
operators `+`, `-` and `*` wrap around when the result does not fit. Division by zero gives zero,
and `x % 0` is `x`. Each of the three operators also has a form that does not wrap, given with
the other partial operations at the end of this document.

Bytes may be compared and used in arithmetic but not shifted, and a byte is widened to a word
with `x.toUInt64` and narrowed back with `x.toUInt8`. The operators `&&` and `||`
evaluate their right operand only when the left one does not decide the result.

A field of a structure is read with `p.f`, and an element of an array with `a[i]`. The plain form
`a[i]` is accepted only when the index is known to be in range. That is the case for a literal
below the length, and for the counter `i` of a loop `for i in 0...n` whose bound `n` is at most
the length. Any other index needs one of the two forms that the last section gives.

## Statements

The body of a function is either an expression or a block of statements. A block may contain the
following statements:

- `let x := e` binds `x` for the rest of the block.
- `let mut x := e` binds a variable that can be assigned.
- `x := e` assigns a variable, and `p.f := e` or `a[i] := e` assigns a part of one.
- `if c then … else if c then … else …` runs one of its branches.
- `match r with | ok a => … | err e => …` takes apart a `Result` or an enum, with one arm for
  each constructor.
- A call `f x y` runs another function.
- `return e` leaves the function with the value `e`.
- `for i in lo...hi do …` is a loop, described in the next section.

The statements run in order, and the value of the last one is the value of the block. Every other
statement must have the type `Unit`, and a value that is not needed is bound with `let _ := e`.
After an `if` or a `match` statement, execution continues with the rest of the block.

Some `if` and `match` statements, among them those that assign a linear variable, are
translated with a copy of the rest of the block in each branch. When these copies grow past a
fixed limit, the function is rejected with a message asking for it to be split.

An assignment must appear as a statement of the block that binds its variable, or of a block
nested in it by `if`, `match` or `for`. The following function is rejected because its
assignment sits inside the expression on the right of a `let`, where its effect would be lost:

```lean
mp def badBlock (c : Bool) : UInt64 := do
  let mut x := 0
  let _ := if c then (do x := 1) else ()
  x
```

Some forms of Lean's `do` notation are not part of Millipede, and each is rejected with a message
at its position. They are `while`, `repeat`, `try`, `←`, `unless`, `if let`, `for` over anything
but a range, and `return` inside a nested `(do …)`.

## Loops

The only loop is `for i in lo...hi do body`, which runs the body once for each value of the
counter `i` from `lo` up to, but not including, `hi`. The form `for i in lo...=hi` includes `hi`
as well. Both bounds are evaluated once, before the first iteration, and when `lo` is greater
than `hi` the body does not run at all.

Every loop has a limit on its number of iterations that is known before the program runs, and
for this reason the upper bound must be a size expression. A size expression is a literal, a
`Nat` constant or variable, the length `s.len` of a slice, or a combination of these by `+`, `-`
and `*`, or by `/` and `%` with a positive literal. A bound known only at run time is written
`min e N`, where `N` is a size expression that caps it. The lower bound may be any word.

A loop body may assign variables bound outside the loop, and after the loop each of them holds
the last value assigned to it. The following loop runs at most five times, even though its body
increases `n`:

```lean
mp def capped (n : UInt64) : UInt64 := do
  let mut n := n
  let mut c := 0
  for i in 0...min n 5 do
    n := n + 1
    c := c + 1
  c * 100 + n
```

The counter is a new variable that hides any variable of the same name for the length of the
body. A counter may not take the name of a variable that the body assigns, because inside the
body that name would refer to the counter, which cannot be assigned, and such a loop is rejected
as it is in Lean.

`break` leaves the innermost loop and `continue` ends its current iteration. Statements that
follow `break`, `continue` or `return` in the same block can never run, and they are rejected.

`return e` inside a loop leaves the function at once with the value `e`, as in `kindOf` above.
The value is held in a variable until the loops end, so a function that returns from inside a
loop must have a result type that is not linear and that has a default value.

## Functions

A function is defined with `mp def`, which gives its name, its parameters and their types, its
result type and its body. A parameter is passed either by value or by reference, and references
are described in [memory.md](memory.md).

A function may call only functions defined before it, so no function can call itself, directly
or through another. Every loop has a bound fixed before the program runs, so every function
terminates, and because there is no recursion the compiler can compute how much stack a program
needs.

A function may be generic over types, sizes and implementations of interfaces, which are
declared as Lean `variable` binders before it. A generic function is checked and proved once
for every value of its variables, and a call supplies the variables, usually by inferring them
from the arguments. Generic functions are described in [modules.md](modules.md).

## Errors and obligations

Millipede has no exceptions. A function that can fail returns a `Result`, and because `Result` is
linear the caller must take it apart with a `match` that has one arm for `ok` and one for `err`:

```lean
mp def useR (r : Result UInt64 UInt64) : UInt64 :=
  match r with
  | ok a => a
  | err e => e
```

A partial operation is one that is not defined for every input. Indexing an array is partial,
since the index may be out of range. Arithmetic counts as partial where a wrapped result would
be wrong, as for a size or an index. Each partial operation has two further forms, written with
`?` and with `!`, which differ in when the condition is checked.

The `?` form tests its condition when the program runs and returns a `Result`. `a[i]?` gives
`err` when `i` is out of range, and `a +? b` gives `err` when the sum does not fit in a word.

The `!` form performs no test. Instead it carries an obligation, a statement that the operation
is defined at that point, which must be proved before the program can be compiled. `a[i]!`
carries the obligation that `i` is in range, and `a +! b` the obligation that the sum fits in a
word. The operators `-` and `*` have the same two forms.

A function may state a precondition with `requires`, which every caller must establish, and a
postcondition with `ensures`, which the function guarantees to its callers. Together they are the
function's contract, and a proof about a caller relies on the contract of each callee instead of
its body. A call to a function with a precondition adds that precondition to the caller's
obligations.

The obligations of a function are proved once, for all its calls, and the proof may assume the
function's precondition. In the following function, the obligation `k < 4` of `closers[k]!`
follows from the precondition `k ≤ 3`:

```lean
mp def closerOf (k : UInt64) requires k ≤ 3 : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
```

Most obligations are proved automatically when the function is defined, and a program is
compiled only when every obligation of every function in it has been proved. How obligations and
contracts are proved is described in [obligations.md](obligations.md).

## Programs

A program consists of a value called the root and two functions. The function `init` builds the
root once, and the function `step` is then called again and again with an exclusive reference to
it, each call running to completion before the next begins. A program of this shape is called a
reactor. It is declared with `mp program`, which names the program, the type of the root, the two
functions and an invariant:

```lean
mp program brackets (root : Br) init brInit step brStep invariant BrInv
```

The clause `invariant BrInv` names a property of the root which `init` must establish and every
call of `step` must preserve, so that it holds after any number of steps.

There are no global variables. A value lives either in the frame of a function call, for as long
as the call runs, or inside the root, which is kept in static storage for the life of the program.

A program reaches the outside world through externs. An extern is a function declared with
`mp extern` and implemented outside the program, and the only externs the compiler can call are
the Linux system calls `write`, `read` and `exit`. An `init` may take capability tokens as its
parameters, which are the program's authority to call the externs of their classes.

The command `#mp_compile brackets ".lake/brackets"` compiles a program to an executable for x64
Linux, and a third argument `"arm64-linux"` selects the other target. It also writes a ledger
listing what the executable's correctness rests on. A program whose obligations are not all
proved is refused, with a message that names the missing proofs.

The meaning of a function as a Lean function, and the declarations that `mp def` generates, are
described in [embedding.md](embedding.md), and capability tokens in [world.md](world.md). What is
not yet built is listed in [../open-claims.md](../open-claims.md), and where the code differs
from the agreed design in [deviations.md](deviations.md).
