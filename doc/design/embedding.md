# The embedding

A Millipede function exists in Lean in two forms. The first is a Core term, a value of an
inductive type that the compiler translates and that theorems about cost and memory inspect. The
second is an ordinary Lean function that computes the same result, and proofs about a program are
proofs about it. For each function, a theorem checked by Lean's kernel says that the meaning of
the term is that function. This document builds on [language.md](language.md) and
[obligations.md](obligations.md).

## Why programs are terms

Lean's logic is extensional, so two functions with the same results are equal and no proof can
tell a fast function from a slow one. Cost, memory use and linearity are therefore properties of
the program's text, which only a term records. Lean also has no linear types and its compiler
does not preserve the cost of a function, so Millipede compiles the terms itself.

Lean is good at reasoning about values that have no identity and so cannot alias. Millipede keeps
that for proofs, and uses linearity only to show that the compiled code may update values in
place. A fact about a program's results is proved about the Lean function and carries over to
the term through the kernel-checked equation. A fact about its cost, layout or linearity holds of
the term and of the code compiled from it.

## Terms, types, meaning

A type of Core is a Lean type together with its `Data` instance, which fixes its layout in memory
and whether it is linear. A Core term `Exp Γ t` has a result of type `t`, and `Γ` is the list of
the types of its free variables. A variable is a position in that list, counted from the most
recent binder. A term that is ill-typed or that uses an unbound variable cannot be built, so the
meaning of a term is defined for every term and theorems need no typing hypothesis.

Every operand in a term is an atom, which is a variable or a literal, and a compound operand is
first bound by `let`. Besides `let`, `if` and the application of a primitive, a term may call an
earlier function, build and take apart `Result` values, structures and enums, read and write
places, fill and empty `Slots` cells, borrow a place for the length of a subterm, call an
extern, and run a loop. A call includes the callee's term, which is closed over its parameters,
so a function cannot call itself.

A primitive is an operation on words or Booleans, or a conversion between a byte and a word,
with a meaning that is exactly what the machine does. `+`, `-` and `*` wrap around, `x / 0` is 0, `x % 0` is `x`, and a shift amount is taken
modulo 64. No value of type `Nat` exists at run time.

A loop of Core runs its body at most a fixed number of times, which is part of the term, and
tests a condition before each iteration. Its state is an accumulator together with the variables
from outside the loop that the body assigns, and each iteration hands their new values to the
next one.

The meaning of a term is given by `Exp.denote`, a Lean function defined by structural recursion
on the term. It takes an oracle, the values of the free variables and a world, and it returns the
result and the new world. The world records the extern calls made so far, and the oracle answers
them, so a theorem that holds for every oracle holds whatever the outside world does.

## From syntax to term

The command `mp def` reads the body of a function, translates it into a Core term `f.exp`, and
runs the checker of linearity and borrowing on the term, whose verdict `f.wf` the kernel confirms
by evaluation. It then
simplifies the meaning of the term with a fixed set of lemmas and defines the Lean function `f`
as the result. The equation between the two, `f.exp_denote`, is proved and checked by the
kernel, so the translation does not have to be trusted. The following function and its two forms
are from a test:

```lean
mp def clampAdd (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then 18446744073709551615 else s

example : clampAdd = fun x y => if x + y < x then pure 18446744073709551615 else pure (x + y) :=
  rfl
```

The Lean function is the simplified form, and not the meaning of the term applied to its
arguments, for three reasons. The tactic `vcgen`, which proves the contracts, cannot see through
`Exp.denote` applied to a term. A call
of `g` inside another function simplifies back to `g x`, so a proof about the caller can use the
contract of `g`. And the compiled Lean function runs fast enough to be evaluated on many inputs
in tests.

A function with no externs becomes a function into `Id`. A function that calls an extern takes
the oracle as its first argument and runs in `StateM World`. An exclusive reference parameter
becomes an extra result, so the function returns its result together with the final value of
each such parameter.

Besides `f.exp`, `f`, `f.exp_denote` and `f.wf`, `mp def` generates the statement of the
obligations `f.SafeGoal` and its proof `f.safe`, the contract `f.spec` and `f.post`, and a record
of what the analyser certified. All the generated names are listed in the
[surface reference](../reference/surface.md).

## Proofs about one program

A proof about a Lean function `f` uses `Std.WP` and the tactic `vcgen`. A specification is a
triple `⦃P⦄ f x ⦃Q⦄`, in which `P` is a statement about the state before the call and `Q` one
about the result and the state after it. A triple tagged `@[spec]` is used by `vcgen` in proofs
of callers, and `mp def` tags each contract `f.spec` this way. A loop in `f` is proved with an
invariant given to `vcgen`, as described in [obligations.md](obligations.md).

## Theorems about all programs

Some theorems are proved once, by induction on terms, and hold for every program. The cost of a
term under a cost model, `Exp.cost`, is a bound computed from the term alone. The instrumented
meaning `Exp.exec` follows the branches and iterations actually taken and counts the steps under
the same model. The theorem `Exp.exec_sound` says that `Exp.exec` computes the same result and
world as `Exp.denote` and takes at most `Exp.cost` steps. Cost is charged by the kind of each
construct, so the count does not depend on annotations placed by hand. In the same way
`Exp.stackUse_le` bounds the stack a run uses by `Exp.stack`, computed from the term.

The checker of linearity and borrowing is a function on terms, `Exp.wf`, and each function's
`f.wf` is proved by evaluation in the kernel. The compiler checks it again on the whole program,
and its correctness theorem relies on it, so the theorem holds for every program that the
checker accepts.
