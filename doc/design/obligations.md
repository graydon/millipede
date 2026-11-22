# Obligations and contracts

This document describes how a Millipede function is proved safe and correct. It builds on the
obligations, the `?` and `!` forms and the `requires` and `ensures` clauses introduced in
[language.md](language.md).

## Obligations

An obligation is a statement that a partial operation is defined at the point where it runs. The
following operations carry one:

- `a[i]!` and `s[i]!` on an array or slice, whose index must be in range;
- a slice `&a[lo..hi]`, which must lie within the array;
- `put!`, `take!` and `[i]!` on a `Slots` value, whose cell must be empty or full;
- `+!`, `-!` and `*!`, whose mathematical result must fit in the type;
- a borrow of two elements `&mut (a[i], a[j])`, whose indices must be in range and differ;
- a call of a function with a `requires` clause, whose precondition must hold.

The obligations of a function `f` are collected into one statement, `f.SafeGoal`, which says that
every obligation holds whenever the function's precondition holds. Its proof is `f.safe`, and it
is proved once for all the calls of `f`. A function that uses only the `?` forms and plain
arithmetic has no obligations, so its `f.safe` needs no proof.

In the Lean function that `mp def` defines, an operation whose obligation fails still returns a
value, a default one, so the Lean function is total. The proof of `f.safe` shows that this
never happens in a call that meets the precondition.

## Arithmetic that cannot overflow

Each of `+`, `-` and `*` comes in three forms. The plain form wraps around when the result does
not fit, the `?` form returns `err` instead, and the `!` form carries the obligation that the
result fits and compiles to the same instruction as the plain form. The forms exist for words and
for bytes. The following functions show the three forms:

```lean
mp def nextW (n : UInt64) : UInt64 := n + 1
mp def nextC (n : UInt64) : Result Unit UInt64 := n +? 1
mp def nextO (n : UInt64) : UInt64 := n +! 1
```

`nextW` of the largest word is 0, and `nextC` of it is `err ()`. The obligation of `nextO`, that
`n + 1` is below `2^64`, is false for the largest word, so it cannot be proved until a
precondition bounds `n`.

Wrapping is well defined, but on a size or an index it is usually a mistake. For each function,
`#mp_report` counts the indices and slice bounds that are computed with a wrapping operator.

## Contracts

A contract is the pair of a precondition, written after `requires`, and a postcondition, written
after `ensures`. In the postcondition, `result` stands for the result and `p'` for the final
value of an exclusive reference parameter `p`. In the following functions, the precondition of
the second call of `inc` follows from the postcondition of the first:

```lean
mp def inc (x : UInt64) requires x.toNat < 10 ensures result.toNat = x.toNat + 1 : UInt64 :=
  x + 1

mp def twice (x : UInt64) requires x.toNat < 5 ensures result.toNat = x.toNat + 2 : UInt64 :=
  let y := inc x
  inc y
```

A contract is proved as `f.spec`, a Hoare triple about the Lean function `f`. The triple is
tagged for `vcgen`, so a proof of a caller's contract uses it. The same contract is also stated
as a plain fact, `f.post`, for proofs of a caller's obligations. Proofs about a caller use these
two and do not unfold the body of `f`, so a change to the body that keeps the contract leaves
them intact.

## How proofs are found

When a function is defined, `mp def` first tries to prove its obligations itself. It runs the
analyser, a verified interval analysis, then the tactic `mp_safe`, which splits the obligations by branch and
loop and closes them with `simp`, `omega` and `grind`, and last the tactic `mp_auto`. It tries to
prove the contract with `vcgen` and `grind`, and then with `mp_auto`. These attempts use the
contracts of the callees and unfold the predicates that the contract mentions when they are
defined in the same file.

When an attempt fails, `mp def` reports it with a message that shows the goal left, and the
function is still defined. The programmer then proves the goal with `mp prove f.safe := …` or
`mp prove f.spec := …`, usually by `mp_auto` with extra lemmas. For `nextO` above, `mp def`
gives the following message:

```
info: the obligations of `nextO` were not discharged automatically; prove them with `mp prove nextO.safe := …` (the goal is `nextO.SafeGoal`); left:
n : UInt64
⊢ n.toNat + 1 < 18446744073709551616
```

A program can be compiled only when `f.safe` exists for every function in it. The options
`mp.autoSafe` and `mp.autoSpec` turn the automatic attempts off for a definition, which then has
only `f.SafeGoal` and `f.SpecGoal` until they are proved.

## The analyser

The analyser works on the term that `mp def` builds. For each word and byte variable it computes
a range of values, and it uses the ranges to check indices and arithmetic.
Its soundness is proved once, for every term, so a function that it certifies has its
obligations proved with no further search. The ranges of the parameters come from bounds in the
`requires` clause. In the following function the analyser shows that `m + 48` fits in a word
from the precondition `m ≤ 8`:

```lean
mp def digit (m : UInt64) requires m ≤ 8 : UInt8 := (m +! 48).toUInt8
```

When the analyser certifies only some of the overflow obligations, those are removed and the
remaining ones are left to `mp_safe` and `mp_auto`. The command `#mp_analyse f` reports what the
analyser certified for `f`. The analyser does not read bounds on fields of reference parameters
or on the results of callees, and it does not track the cells of a `Slots` value, so obligations
that depend on them go to the tactics.

## Loop invariants

A proof about a loop needs a loop invariant, a statement about the loop's state that holds before
every iteration. The state of a loop is a tuple of the variables that its body assigns. It begins
with the accumulator, a small variable that is not linear and that the last statement of the body
assigns, and when several qualify the accumulator is the one declared last. The other assigned
variables follow in the order they are declared, and then flags that record a `break` or a
`return`. A loop that assigns a single variable has that variable as its state. In the following
function the state is `(m, (n, ()))`, and the invariant names its components with a pattern:

```lean
mp def countBoth (w : Arr UInt64 4) ensures result ≤ 8 : UInt64 := do
  let mut n := 0
  let mut m := 0
  for i in 0...4 do
    if w[i] == 1 then n := n + 1
    if w[i] == 2 then m := m + 1
  n + m
mp prove countBoth.spec := by
  intro w; vcgen [countBoth] invariants
  · fun done _ (m, n, _) => m.toNat ≤ done.length ∧ n.toNat ≤ done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind
```

An invariant takes the counter values already done, those still to come, and the state, and the
lemma `range_split` gives the fact that the current counter is below the bound. For a contract, the automatic attempt tries the postcondition as the invariant. For obligations it tries
no invariant, then the precondition, then the postcondition, and then both.

An obligation inside a loop may depend on the loop's state, as when an index moves with each
iteration. Such a function is proved with `mp_auto invariants`, which takes one invariant for each
loop in the order the loops appear. In the following function, `j` stays in range because
`j + s = 4` holds before every iteration:

```lean
mp def walk (a : Arr UInt64 4) : UInt64 := do
  let mut j := 0
  let mut s := 4
  let mut t := 0
  for _ in 0...100 do
    if s == 0 then break
    t := t + a[j]!
    j := j + 1
    s := s - 1
  t

mp prove walk.safe := by
  mp_auto invariants
  · fun _ _ (s, j, _) => j.toNat + s.toNat = 4
```

When a proof given by `mp prove f.spec` names loop invariants, the same invariants are also
tried for the obligations, so one invariant often proves both. A goal that is left is
reported at the invariant, with the components of the state named after the source variables.

## Contracts about events

A contract may say which calls a function makes. In the `ensures` of a function that makes calls,
`history` is the list of events before the call, `events` the events that the call appends, and
`exited` whether the call ends by `exit`. The oracle is `ω`, and the answer to a call `c` made
after the events `pre` of this call is `ω.answer (history ++ pre) c`. In the following function
the contract says that the call writes the greeting once, with the answer the oracle gives at
that point, and does not exit:

```lean
mp def greet ensures events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false
    : Unit :=
  let _w := sysWrite 1 "hello, world\n"
  ()
```

The contract is a statement about every run that starts before `exit`. Such a run ends with
the old history followed by a list of events, and the `ensures` holds of that list, of whether
the run exited and of the result, so a function only appends to the history. The `ensures`
fixes the events only as far as it states them: the contract of `greet` gives the one event
exactly, while a contract `events.length = 1` says that there is one event and nothing about
it. A run that starts after `exit` changes nothing, and `f.spec` states that too, so a caller's
proof continues after a callee that may exit and counts no events after it.

A caller's proof uses the callee's contract and not its body, so the events of a function are
proved from the contracts of the functions it calls. The automatic attempt unfolds the calls and
events that the contract names, those of the current file and imported ones. The invariant of a
loop that makes calls states the events so far after `history`. When the contract says
`events = t` and `t` names the loop's bound `N`, the automatic attempt tries as the invariant
that the events so far are `t` with `N` replaced by the number of iterations done; it then tries
the contract itself. Other invariants are given with `mp prove`. A contract that needs a lemma
relating the callees' values to the events is proved with `mp prove`, or automatically when the
lemma is a `@[simp]` lemma in the form that `simp` meets after `vcgen`: the contract of
`revStep`, that the bytes written are the bytes read, reversed, is proved so.

When `step` of a program has a contract about events, and `init` has one or makes no call,
`mp program` proves `p.reach`, which says that for every oracle every run keeps to the contracts
of `init` and `step`, and `p.events_reach`, the same for the trace that the compiler's theorem is
about. When the contract of `step` has a `requires` `R`, a step is related by `R r → E`, and the
proof that `R` holds of each root before `exit` is part of the induction that uses the theorem.
The trace of the program then follows from the two contracts by an induction on the number of
steps, without the body of `step`. The traces of `hello`, `revchunks` and the key-value server
`kvsrv` are proved so. The contract of a step is about runs that start before `exit`, so a root
invariant of a program whose step has such a contract, which must hold after `exit` too, is
proved from the step's body (`kvsrv.inv_step`).

## Root invariants

A program's root invariant is declared by the clause `invariant I` of `mp program`. The command
generates two goals, that `init` establishes `I` and that `step` preserves it, and it tries to
prove them from the contracts of `init` and `step`. The second goal also says that `I` implies the
precondition of `step`. From the two, without further proof, it derives `p.inv`, which says that
`I` holds after any number of steps whatever the outside world answers, and `p.safe`, which says
that every obligation of every step holds. When a goal is not proved automatically, it is proved
with `mp prove p.inv_init := …` or `mp prove p.inv_step := …`.

## Proof burden

The proof burden of a program is the text a programmer writes beyond the program itself, such as
contracts, invariants, lemmas and proofs. The target is about twice the length of the program.
A larger burden is not an error, but it shows where the library's lemmas, the automation or the
types should improve. Current figures are in [../measurements.md](../measurements.md).

The forms of the tactics and options are listed in the
[surface reference](../reference/surface.md), and what the automation cannot yet do in
[../open-claims.md](../open-claims.md).
