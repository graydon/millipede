# Resources

Every Millipede program has static bounds on the time and space each reactor step can use. A
bound is computed from the program's syntax before it runs, and a theorem shows that no run
exceeds it, whatever the input. This document describes the quantities that are bounded, how the
bounds are stated, and what kinds of statement a program can make about its resources.

## Quantities

A bound is stated in terms of named quantities, and a number appears only when a closed program
is evaluated for a report. The table lists the quantities.

| quantity | meaning |
|---|---|
| `size T` | the bytes a value of type `T` occupies, from its layout |
| size expression | a capacity or loop bound: a literal, a `Nat` constant, a slice's length `s.len`, or arithmetic of these |
| `Exp.cost κ hb e` | the steps of term `e`, under a cost model `κ`, with its value delivered in mode `hb` |
| `Exp.stackBytes φ e` | the stack used by the calls inside `e`, under a frame model `φ` |
| `Program.footprint` | the bytes of the root plus the values bound at once by `init` or `step` |

A cost model `κ` holds one number for each kind of construct, such as a primitive operation, a
call or a loop iteration. A construct that copies a value also pays a number per 64-bit word of
it, so copying a wide value costs in proportion to its width. Each scalar counts as one word, so a
byte array of 64 elements counts 64. The cost of a term is computed from its syntax. A conditional
costs as much as its more expensive branch, and a loop costs its full number of iterations.

Only copies that the compiled code makes are charged. A conditional, `match` or `case` writes the
value of its arm where its own value goes, so it pays no words for its result; a `match` or `case`
pays for the scrutinee whose payload it copies into the arm. A borrow, and a call with reference
arguments, pass addresses and pay a constant per reference. A function with `&mut` parameters
returns their final values together with its result, a mutable borrow's body returns the borrowed
value, and a loop body returns the variables it writes together with its accumulator. The compiled
code leaves these values where they are, so the constructor at the end of such a body pays only
for its first component. This is the mode `split` of `Exp.cost κ hb e`. The reactor step pays no
words for handing back its root when every tail of the step is the root's variable, which is the
mode `whole`; otherwise it is charged as a copy, mode `copy`, like `init`.

A frame model `φ` gives the bytes of stack that a call with `w` frame slots occupies. The stack
bound of a term is the frame of the term itself plus the deepest chain of calls inside it, which
is finite because there is no recursion. Each frame is charged 16 scratch slots on top of the
slots of its values, because the compiler uses that many in every frame.

Theorems about the source hold for every cost model and every frame model. Each target supplies
its own `κ` and `φ`, which turn steps into machine instructions and frames into bytes. For the
stack, a theorem shows that the compiled code stays within the source bound for every `φ`. The
source bound charges every value of a frame a stack slot, while the compiled code keeps values in a
static data region and in registers, and its frames hold only word slots. The compiler therefore
computes a second, smaller bound from the selected code and asks the kernel for exactly that much
stack; `compile_stack_tight` (Millipede/Top/StackTight.lean) shows that the machine stays within
it and that it is at most the source bound. For
instructions, the compiler checks each program's selected code against the target's `κ` and
refuses a program that exceeds it, as described in [compiler.md](compiler.md).

Each weight of `X64.κ` and `A64.κ` is the most machine instructions that the selected code of its
construct takes, in every register-allocation setting `compile` offers. Allocation off is the
dearest: every value is then in memory, and one load or store of the data region takes 6 or 7
instructions. The weights fitted from the test programs carry a margin of 10%. They pay for the
following, as x64 / arm64 instruction counts before the margin:

| weight | x64 / arm64 | pays for |
|---|---:|---|
| `word` | 32 / 29 | one iteration of the loop that fills or copies a value of 64 bytes or more, 8 bytes per iteration; a straight copy of a word takes at most 14 |
| `iter` | 64 / 59 | a loop's counter step, back jump, counter test, the counter's copy into its variable and the condition's flag and branches, counter and flag in memory |
| `loop` | 14 / 11 | entering a loop: the accumulator and counter set-up and the first test |
| `prim` | 32 / 32 | a primitive, up to two operands read through references (two loads each) |
| `div` | 41 / 33 | a division or remainder with operands as for `prim`; x64's remainder sequence, with its guard against a zero divisor, is 10 instructions, arm64's 2 |
| `mem`, `place` | 25 / 24, 4 / 4 | a read, assignment, `put`, `take` or guard, and each place selector |
| `ref` | 36 / 35 | a borrow or a reference argument: the place's address and its store |
| `call` | 13 / 16 | a call's sequence beyond the words and references it passes |
| `ext` | 16 / 17 | an extern call: argument loads, the system call and the result's store |
| `ite` | 10 / 9 | the condition's load and branch and the join jump |
| `ctor` | 12 / 8 | the tag and payload stores of a constructor that leaves a loop early |
| `atom`, `let_` | 4 / 4, 3 / 2 | an atom beyond its words; a `let` beginning a reactor step pays the step loop's test |
| `match_` | 0 / 0 | its tag test and branch are paid by the words of the scrutinee it copies |

`word` and `iter` are exact counts of fixed instruction sequences and carry no margin. The cost of
a primitive depends on where its operands are: 4 instructions with both in registers, 32 through
references with allocation off, and the weight is the latter.

## Three kinds of statement

The first kind is computed and proved automatically for every term. The cost, the stack bound
and the footprint are computed from syntax. An instrumented semantics follows the path a run
actually takes and counts what it uses, and one theorem for each quantity shows that the amount
used is at most the bound on every run. These theorems are `Exp.exec_sound` for steps,
`Exp.stackUse_le` for the stack and `Exp.footUse_le` for the footprint.

The second kind relates the resources of the operations of an interface, such as a bound on the
cost of `alloc` in terms of the arena's size. These relations are not built. An interface states
only contracts, and a module's hypotheses on its parameters are checked at each instance by
`decide`.

The third kind is a specification of one program, stated as a contract or an invariant over the
state, and proved like any other contract. An allocator's contract can say how many cells are in
use before and after an operation, and a program's root invariant can relate the cells in use to
the capacity of the arena. Such an invariant is what discharges the obligation of each allocation
that must not fail. A function whose signature has no `&mut p` cannot change `p`, so its
contract need not mention it.

## Reports

For a closed program, the command `#mp_report` prints the evaluated figures: the bytes of the
root, the footprint, the static data region, the stack bound and the instructions allowed per
reactor step on each target, and the size of the compiled image. The stack bound is also written
into the image, as the stack size the program asks the kernel for.

## Planned

The design also calls for statements about the step counter of a run, such as a time bound that
depends on the length of the input, and for amortised bounds with a potential function. Neither
is built. See [../open-claims.md](../open-claims.md).

## Where this lives

| item | location |
|---|---|
| `CostModel`, `Exp.cost`, `Exp.exec`, `Exp.exec_sound` | Millipede/Core/Cost.lean |
| `FrameModel`, `Exp.stackBytes`, `Exp.footprint`, their soundness | Millipede/Core/Stack.lean |
| `Program.stackBytes`, `Program.footprint`, `Program.stepCost` | Millipede/Core/Program.lean |
| `#mp_report` | Millipede/Meta/Report.lean |
| figures for the example programs | [../measurements.md](../measurements.md) |
