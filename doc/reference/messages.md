# Messages

This part of the reference lists the messages a programmer is most likely to meet, by the start of
their text, with what each means and what to do about it. Most of them are checked by a
`#guard_msgs` test in one of the files named before each group's table.

## Proofs left open

These are information messages, not errors. The function is defined, but a proof is missing, so
the program cannot be compiled until it is given with `mp prove`. The tests are in
`Tests/Tutorial.lean`, `Tests/Contracts.lean`, `Tests/LoopSafe.lean`, `Tests/ProgramInv.lean` and
`Tests/Driver.lean`, `Tests/AutoHints.lean`, `Tests/EnsuresEvents.lean`.

| message | meaning |
|---|---|
| ``the obligations of `f` were not discharged automatically; prove them with `mp prove f.safe := …` …; left: …`` | `f.SafeGoal` exists and `f.safe` does not. The goal after `left:` is what could not be shown from the hypotheses above it. Add to the precondition, pass a lemma with `mp_auto [L]`, or write the proof. |
| ``the contract of `f` was not proved automatically; prove it with `mp prove f.spec := …` …`` | the same for the contract, `f.SpecGoal` |
| ``the contract of `f` was not proved automatically: a loop needs an invariant … Prove it with …`` | the postcondition is not kept by an iteration of the loop. Write the invariant in the proof that the message prints. |
| ``the contract of `f` was not proved automatically: a loop needs an invariant (… the carried value and the world …) … `mp_auto invariants` …`` | the same for a contract about events. The invariant is a function of the counters, the loop's state and the world, and states the events so far after `history` (`Tests/EnsuresEvents.lean`). |
| `` `p.reach` is not generated: … `` | `step` has a contract about events, but `init` has a contract that is not about events or a precondition, or `init` returns through a reference; or the contracts did not give it, and the goal left is shown |
| ``hint: a goal about an arena's cells in use usually needs the keys held in the invariant …`` | add `KeyStack` or `Holds` to the invariant, as described in [library.md](library.md) |
| ``hint: the attempt ran out of its budget `mp.autoSafe.maxHeartbeats` …`` | the attempt costs more with each variable in scope and each read of one. Raise the option for this function, or move a loop or a branch into an `mp def` of its own. Lean's `maxHeartbeats` does not apply. |
| ``hint: the pair borrow `(a[i]!, a[j]!)` takes two cells of one array …`` | the goal `False` is left of the obligation that the two indices differ. Require `i ≠ j`, or test it before the borrow. |
| `` `p.inv_init` was not proved automatically ``, `` `p.inv_step` was not proved automatically `` | the program's invariant is not established by `init`, or not kept by `step` |
| `` `p.safe` is not generated: `g.safe` must be proved first `` | a function of the program has open obligations |
| `` `p.safe` is not generated: `g` has a `requires`; give the program an `invariant` under which it holds `` | `step` has a precondition and the program has no invariant |
| `` `f.safe` was proved with the contract's loop invariants `` | the invariants given for the contract also proved the obligations |
| `mp_auto: a goal is left: …` | `mp_auto` did not close the goal. Pass lemmas, or continue by hand. |
| `` `f.spec` is already proved `` | an `mp prove` of something the automatic attempt proved. Delete it. |

## Definitions and calls

The tests are in `Tests/MpDef.lean`, `Tests/MpDef2.lean`, `Tests/Usability.lean` and
`Tests/Contracts.lean`, `Tests/FailedDefs.lean`, `Tests/LoopBounds.lean`.

| message | meaning |
|---|---|
| ``unknown function `g` (not an earlier `mp def` or `mp extern`)`` | a function may call only functions defined before it |
| `` `g` was not defined because of the error above `` | the definition of `g` failed. Fix that error first. |
| `` `g` was not defined because of the error at its `mp def` `` | the same, from `mp program` |
| `` `g`: failed. Its `mp def` stopped with the error reported there … `` | `#mp_report` of a function whose `mp def` failed, for example because the kernel rejected a theorem it generates. Nothing it generated can be cited. |
| `` `f` has no normal form (declared under `set_option mp.normalForm false`), so `g` cannot have one … `` | a caller of such a function must be declared under the same option. Its contract, `g.spec`, needs the normal form too. |
| `` `f` expects 2 argument(s), got 1 `` | a call has the wrong number of arguments |
| ``parameter `p` of `bump` is `&mut Pt`: pass `&mut p` for a place `p` `` | a reference parameter needs a reference argument |
| `` `f` takes its arguments by value; drop the `&` `` | a value parameter got a reference |
| ``a string (`Bytes`) can only be passed to an extern …`` | an `mp def` cannot take or return a string. Choose the string at the extern's call, or pass a byte slice. |
| ``a function with `ensures` cannot have a parameter named `result` …`` | `result` names the returned value in `ensures` |
| ``a function with `ensures` cannot have a parameter named `exited` …`` | `history`, `events` and `exited` name the events of the call in `ensures` |
| `unsupported syntax in `mp def`` | a term that is not a form of the language |
| ``deriving Data: …`` | the type cannot be laid out, for the reason named |

## Types

The tests are in `Tests/MpDef.lean`, `Tests/MpDef2.lean` and `Tests/Bytes.lean`.

| message | meaning |
|---|---|
| `type mismatch: expected Bool, but this has type UInt64` | an expression has the wrong type |
| `equality is only available on UInt64, UInt8 and Bool, not …` | `==` on another type |
| `` `+` needs UInt64 or UInt8 operands, but this has type Bool `` | arithmetic on another type |
| `shifts of UInt8 are not in the language …` | widen with `.toUInt64`, shift, and narrow with `.toUInt8` |
| ``cannot infer the Result type of `ok`; add a type ascription …`` | write `(ok a : Result ε α)` |
| ``missing arm for `E.c` ``, ``duplicate arm for `E.c` `` | a `match` needs exactly one arm per constructor |
| `` `S` has no field `z` ``, ``missing field `y` `` | a field name is wrong, or a structure literal lacks a field |
| `` `S` is sealed (its constructor is private to its module): it cannot be built here `` | a sealed structure, such as an arena key, is built or written outside its module |

## Places, references and linear values

The tests are in `Tests/Tutorial.lean`, `Tests/MpDef.lean`, `Tests/MpDef2.lean`,
`Tests/LoopRef.lean` and `Tests/Lib.lean`.

| message | meaning |
|---|---|
| `cannot show that this index is below n …` | `a[i]` needs a literal or a loop counter. Write `a[i]!` with a precondition, or `a[i]?`. |
| `` `Slots` have no checked forms … `` | use `put!`, `take!` and `s[i]!`, or an arena's checked operations |
| ``use of `k` after it was moved (a linear value is used once)`` | a linear value was used again after it was given away |
| ``linear … `k` … is used 2 times; it must be used exactly once`` | a linear value was used twice |
| ``unused linear … `k` …: a linear value must be used exactly once …`` | a linear value was dropped. Consume it, store it or free it. |
| ``linear variable `r` is used 1 time(s) in the then-branch but 0 time(s) in the else-branch …`` | every path must use a linear value the same number of times |
| ``cannot copy the linear value … out of a place …`` | move a whole variable, or `take!` it out of `Slots` |
| `` `d` is used here while an overlapping place is borrowed with `&mut` by `r` … `` | while an exclusive borrow is live, use the place only through it |
| `` `x` is written here while an overlapping place is borrowed with `&` … `` | a shared borrow allows only reads |
| ``cannot assign through the shared reference `p` `` | the parameter or borrow is `&`, not `&mut` |
| `` `x` is not mutable: declare it with `let mut` … `` | only a `let mut` variable or an `&mut` reference can be assigned |
| ``cannot write `x` here: it is bound outside the current block …`` | write the assignment as a statement, not inside the value of a `let` |
| `` `p` shadows the reference `p`; choose another name `` | a reference cannot be shadowed |

## Capabilities and handles

The tests are in `Tests/Tokens.lean`.

| message | meaning |
|---|---|
| ``…`f` calls the extern symbol "write", which needs the capability `Fs`, but holds no `Fs` token …`` | the function reaches a symbol of a class it holds no token of, perhaps through a callee or an extern declared without a token. Take a token as a parameter. |
| ``the parameter `fs` of `fsWrite` is a token: pass `&t` for a token `t` of the capability `Fs` `` | the extern requires a token of that class at this position |
| `` `Millipede.Lib.Cap` is sealed (its constructor is private to its module): it cannot be built here `` | a token cannot be made in Millipede code. A program receives its tokens at `init`. |
| ``the extern symbol "sym" does not belong to the capability `C`, whose symbols are … `` | an extern may require only a token of a class that governs its symbol |
| ``the symbol "sym" already belongs to the capability `C` `` | a symbol belongs to at most one class |
| ``type mismatch: expected Log clean, but this has type Log dirty`` | an operation of a handle was applied in the wrong state |
| `` `init` must take no parameter, or only tokens of capability classes … `` | the parameters of `init` are the program's grant, so they must be tokens |
| `` `init` takes its tokens by value: `fs` is a reference `` | write `(fs : Fs)`, not `(fs : &Fs)` |

## Blocks and loops

The tests are in `Tests/DoNotation.lean` and `Tests/MpDef.lean`.

| message | meaning |
|---|---|
| `the upper bound of a loop must be a size expression …` | write a literal, a constant, `s.len`, arithmetic of those, or `min e N` |
| `an inclusive upper bound must be below 2^64 - 1 …` | the counter would wrap around |
| ``the counter `i` shadows the variable `i`, which the loop body assigns …`` | rename the counter |
| ``linear variable `e` is bound outside this loop and used inside it …`` | a loop may run any number of times |
| ``the loop condition must not use the linear variable `x` `` | the leading `if c then break` reads a linear variable |
| ``the value of this statement (of type T) would be discarded …`` | bind it with `let _ := …`, or make it the last statement |
| ``unreachable: a statement after `return` in the same block`` | delete the statements after `break`, `continue` or `return` |
| ``… is not supported in `mp def` …`` | a form of Lean's `do` notation outside the language, such as `while`, `try`, `←` or `unless` |
| ``this statement and the rest of its block translate to … nodes, more than the limit of 100000 …`` | split the function into smaller ones |

## Quantities

The tests are in `Tests/Units.lean`.

| message | meaning |
|---|---|
| `` `<` needs quantities of the same unit, but the operands are Q byte … and Q KiB … `` | convert one operand with `.to` |
| `type mismatch: expected Q KiB, but this has type Q byte …` | convert with `.toFloor` or `.toCeil` |
| ``type mismatch: expected UInt64, but this has type Q byte …`` | take the count with `.val` |
| ``cannot convert Q byte (dimension Size) to Q ns (dimension Time) …`` | a conversion stays in one dimension |
| `` `.to KiB` would round … `` | use `.toFloor` or `.toCeil` to go to a coarser unit |

## Generic code

The tests are in `Tests/Generic.lean`, `Tests/Modules.lean` and `Tests/Brands.lean`.

| message | meaning |
|---|---|
| ``cannot infer the variable `A` of the generic `f` …`` | give it by name, `f (A := e) args` |
| ``cannot instantiate `f`: its hypothesis … is neither in the context nor decided`` | the instance violates the function's hypothesis, or the caller must assume it |
| `type mismatch: expected B.K, but this has type A.K` | a key of one arena given to another |

## Compiling

The tests are in `Tests/Driver.lean`.

| message | meaning |
|---|---|
| ``refused: `p.safe` is not proved. … Missing: …`` | prove what the message names |
| ``refused: `p.safe` depends on [sorryAx] …`` | the proof is incomplete or has errors |
| `unknown target 'arm65' (known: x64-linux, arm64-linux)` | the third argument of `#mp_compile` names no target |
| ``compile refused `p`: …`` | the compiler cannot translate a construct of the program, named in the message |
