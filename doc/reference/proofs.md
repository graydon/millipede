# Proofs

A function's obligations and its contract are proved when the function is defined, and most of
them are proved automatically. This part of the reference describes the automatic attempts, the
command that proves what they leave, the tactics such proofs use, and the attributes and options
that affect them.

| form | does |
|---|---|
| `mp prove f.safe := proof` | proves the obligations of `f` |
| `mp prove f.spec := proof` | proves the contract of `f` |
| `mp prove p.inv_init := proof`, `mp prove p.inv_step := proof` | proves a program's invariant |
| `mp_auto`, `mp_auto [lemmas]` | the usual proof of a contract or of obligations |
| `mp_auto invariants · I₁ · I₂` | the same, with an invariant for each loop |
| `mp_safe [lemmas] using closers grind [lemmas] invariants · I₁` | the proof of obligations, step by step |
| `mp_inst_posts [g, …]` | adds each callee's contract at its calls |
| `mp_vcgen_post [f, …]` | `vcgen`, with each loop's invariant guessed from the postcondition |
| `mp_history` | begins a proof of a contract about events from the history `history` |
| `mp_world_branch` | the case of a callee's contract about events for a live or an exited world |
| `mp_safe_setup`, `mp_loop_split`, `mp_loop_inv`, `mp_loop_lift`, `mp_check_terms` | steps of `mp_safe` |
| `@[mp_auto]`, `@[mp_auto_fwd]` | lemmas and predicates for `mp_auto` |
| `@[spec]` | a contract that `vcgen` uses |
| `fmt_close`, `fmt_safe [defs]` and the walks `fmt_parsed`, `fmt_written`, `fmt_checked` | the proofs of generated format code |

## Obligations and contracts

An obligation is a fact that must hold for an operation to be defined, such as an index being in
range or a sum fitting in a word. The obligations of `f`, under its precondition, are stated as
`f.SafeGoal`, and their proof is `f.safe`. A program is compiled only when every obligation of
every function in it has been proved. The obligations are described in
[../design/language.md](../design/language.md).

A function's contract is stated as `f.SpecGoal`, a triple in Lean's `Std.WP` logic, and its proof
is `f.spec`. The same contract as a plain fact about the function's result is `f.post`, which
other proofs cite.

## The automatic attempts

`mp def` first tries to prove the obligations. A function with no partial operation needs no
proof. Otherwise, for a function that is not generic, the verified analyser runs first, which
reads bounds on word parameters from the precondition and proves the obligations it can. What it
leaves goes to the tactic `mp_safe`, then to `mp_auto`, and last to `mp_auto` with loop
invariants taken from the precondition, the postcondition and both. Each attempt has a time
budget, and a proof that is found is checked by Lean's kernel within a budget of its own.

When a function has `ensures`, `mp def` then tries to prove the contract. It runs `vcgen`, which
turns the contract into goals, using each callee's contract instead of its body, and closes the
goals with `grind`. When that fails it tries `mp_auto`, which takes the postcondition at each
loop's state as the loop's invariant.

The attempts unfold the predicates of the contract, such as `BrInv` in `requires BrInv r`, when
they are defined in the current file or tagged `@[mp_auto]`. They use each callee's contract
through `g.post`.

When an attempt fails, `mp def` still defines the function, prints an information message that
says what is left to prove, and leaves the goal for `mp prove`:

```text
the obligations of `closerOf1` were not discharged automatically; prove them with
`mp prove closerOf1.safe := …` (the goal is `closerOf1.SafeGoal`); left:
k : UInt64
⊢ k.toNat < 4
```

The lines after `left:` are the first goal that the attempt could not close, with the hypotheses
it had. A goal that needs the keys of an arena held in an invariant is followed by a hint that
names `KeyStack`, and a goal about a loop's state is followed by the shape of an `mp_auto
invariants` proof for each loop.

## mp prove

`mp prove` proves what the automatic attempt left. Its target is `f.safe`, `f.spec`,
`p.inv_init` or `p.inv_step`, and its proof is a Lean term, usually a tactic block. A target that
is already proved is rejected, as is a name that is not one of these four. `Tests/ByteBuf.lean` proves the
obligations of a step with `mp_auto` and one definition to unfold:

```lean
mp prove catStep.safe := by mp_auto [ByteBuf.Inv]
```

When `f` is generic, `mp prove f.safe` and `mp prove f.spec` are proved once, under the same
variables. `#mp_report` shows for each function whether its obligations and contract were proved
automatically, by a one-line `mp_auto`, or by hand.

## mp_auto

`mp_auto` is the usual proof of a contract or of obligations. On a contract it runs `vcgen` with
the function unfolded, and closes the goals with `grind`. On obligations it runs `mp_safe` set up
as the automatic attempt sets it up. In both cases it passes to `grind` the callees' contracts,
the lemmas tagged `@[mp_auto]`, the contract's predicates and the lemmas or definitions given as
`mp_auto [L, …]`. It also reads word comparisons as comparisons of natural numbers, and it knows
that `x % n < n` when `0 < n`.

`mp_auto` fails when a goal is left, and its message shows the goal. The proof can then pass
more lemmas, or continue by hand with ordinary tactics.

## A loop's invariant by hand

A loop invariant is a fact that holds before and after every iteration of a loop. When the
postcondition is not one, the message of the failed attempt prints the shape of the proof, with
the function's parameters and the callees to unfold. The invariant is a function of the counter
values already done, the values left, both as lists, and the loop's state. `range_split` tells
`grind` that the counter is below the bound. From `Tests/Tutorial.lean`:

```lean
mp def opensIn (w : Arr UInt64 4) ensures result ≤ 4 : UInt64 := do
  let mut n := 0
  for i in 0...4 do
    if isOpen w[i] then n := n + 1
  n
mp prove opensIn.spec := by
  intro w; vcgen [opensIn, isOpen] invariants
  · fun done _ n => n.toNat ≤ done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind
```

The loop's state is the tuple of the values the loop carries from one iteration to the next. Its
first component is the loop's accumulator, a word variable that every path through the body
assigns at its end, and when there are several, the one declared last. When there is none, the
first component is `()`. The other variables that the body assigns or moves follow in the order
of their declaration, then the flags. The state is nested as `(acc, (x₁, (x₂, … ())))`, or is the
accumulator alone when nothing else is carried. A pattern names its components, as in
`fun done _ (acc, x, y, _) => …`.

A loop that contains `break` carries a flag that says it was left. A loop that contains `return`
carries a flag that says it returned and the value it returned, and its invariant must allow the
case where the function has already returned a correct value, as in
`fun done _ (_, f, v, _) => (f = true → v ≤ 3) ∧ …`. For a search loop of the form
`for … do if p i then return v` followed by `return d`, the automatic attempt builds this
invariant itself.

## Contracts about events

A contract about events (see [definitions.md](definitions.md)) is proved like any other: the
automatic attempt runs `vcgen`, uses each callee's contract at its call, unfolds the calls and the
definitions that the contract names (those of the current file, and imported ones that state a
call or an event, or a constant such as a message's bytes), compares the events with `simp_all`,
and closes the rest with `grind`. After a callee that may exit, the proof goes on twice, once for
the world that has exited, where every later call changes nothing, and once for the live world.
`mp_world_branch` takes one such case, and closes it when the callee's contract excludes it. A
fact relating values to events, such as that `Slice.reverse` reverses the bytes a read delivered,
is used when it is a `@[simp]` lemma in the form `simp` meets after `vcgen`; the bytes an extern
delivers appear there as `(fitOut caps r.bytesOut).head?.getD []` (`headD_match`).

`mp_history` begins a proof of a contract about events. It introduces the parameters and the
history before the call as `history`, and leaves a triple about the run from that history. A
loop's invariant then states the events so far with `history`, as a function of the counters
done, the counters left, the loop's state and the world. `mp_auto` begins with it on a contract
about events, and tries the contract as each loop's invariant. When the contract is
`events = t ∧ …` and `t` names the bound `N` of a loop, the automatic attempt of `mp def` first
tries the invariant `fun done _ _ w => w = ⟨history ++ t[N := done.length], false⟩`. From
`Tests/EnsuresEvents.lean`, a function that writes each byte of an array, one write per byte, whose
contract is proved so; the same invariant given by hand is:

```lean
mp def putEach2 (a : Arr UInt8 4) ensures events = byteWrites ω history a 4 ∧ exited = false
    : Unit := do
  for i in 0...4 do
    let _w := sysWriteS 1 (&a[i..i+1])
  ()

mp prove putEach2.spec := by
  intro ω a; mp_auto invariants
  · fun done _ _ w => w = ⟨history ++ byteWrites ω history a done.length, false⟩
```

When `step` of a program has a contract about events, `mp program` derives `p.reach` and
`p.events_reach`; when that contract has a `requires` `R`, `p.stepRel ω r h evs e r'` is
`R r → E` (`Program.reach_of_contracts_req`).

## Loop invariants for obligations

An obligation inside a loop may depend on the loop's state, as when an arena operation needs a
fact about the arena that the loop carries. Such a loop needs an invariant for its obligations,
written in the same form as for a contract, with one `·` for each loop in source order. A
contract proved by `mp prove f.spec` with invariants also offers them to `f.safe` when that was
not proved, so one invariant serves both. From `Tests/LoopSafe.lean`:

```lean
mp prove Store.sum.spec := by
  mp_auto invariants
  · fun _ _ (n, s, _) => A.Inv s ∧ A.used s ≤ n.toNat ∧ n.toNat ≤ 4
```

The command reports that `Store.sum.safe` was proved with the contract's loop invariants. The
obligations alone are proved by `mp prove f.safe := by mp_auto invariants · …`. A goal that is
left names the state's components after the source variables, with `s'` for the current value of
an `&mut` parameter `s`. When an invariant does not prove its loop's obligations, the error is
reported at that invariant.

## mp_safe

`mp_safe` is the tactic that proves obligations step by step. It unfolds the function, splits the
obligations of each loop by its counter, splits branches, and closes the pieces with `simp`,
`omega`, `grind` and `decide`, using the precondition. Its clauses add facts. The lemmas in
brackets are passed to `simp`, the terms after `using` close the obligations of calls, and the
lemmas after `grind` are passed to `grind`, usually the callees' contracts `g.post`. The clause
`invariants · I₁ · …` gives the loops their invariants.

The steps of `mp_safe` are also tactics of their own, for a proof that needs to go between them.
`mp_safe_setup` unfolds `f.SafeGoal` and `f.exp`, names the parameters and takes the invariants.
`mp_loop_split` splits the obligations of the next loop, by its invariant when one was given, by
the invariant that the cells of its slices stay full when it carries a slice, and otherwise for
every state. `mp_loop_inv` is that slice invariant alone, and `mp_loop_lift` carries it through an
inner loop that writes the slice. `mp_check_terms` fails when one of the terms after `using` does
not elaborate.

## Contracts at calls

`mp_inst_posts [g, …]` adds, for every call of each named function in the goal, the callee's
contract `g.post` at the call's arguments as a hypothesis. When the callee's precondition is
closed at the call, the tactic proves it with `decide`, `simp` or `omega`. `mp_inst_posts keep [g, …]`
leaves every precondition as a premise. `mp_auto` runs the first form and `fmt_safe` the second.

`mp_vcgen_post [f, …]` runs `vcgen [f, …]` on a contract and sets each loop invariant it leaves
open to the postcondition at the loop's state. For a search loop it sets the invariant described
above. `mp_auto` and the automatic attempt run it.

## Proofs of generated formats

`mp format` (see [definitions.md](definitions.md)) proves the contracts and obligations of the
functions it generates with the following tactics, which are also usable by hand on code written in
the same calling convention.

| tactic | does |
|---|---|
| `fmt_close` | closes a verification condition: a contract by `fmt_parsed`, `fmt_checked` or `fmt_written`, a bound by `omega`, full cells by `fmt_full`, splitting `∧` and introducing `→` |
| `fmt_parsed` | proves `ParsedT f t B p ok p' v` by walking `f`: `Parsed.pair_cont`, `pair_stop`, `union_cont`, `union_stop`, `array`, `array_stop`, `array_big`, `ParsedT.arm_eq` (the branch the code did not take is closed by `omega`), `ParsedT.unit`, `ParsedT.noArm`, and a leaf's contract from the hypotheses |
| `fmt_checked` | the same for a validator's `CheckedT`, with the `Checked.*` lemmas |
| `fmt_written` | the same for a writer's `WrittenT`, with `Written.pair`, `union`, `array`, `WrittenT.arm_eq`, `unit`, `noArm` |
| `fmt_full` | proves that a buffer's cells are full after writers, through their contracts |
| `fmt_pre` | closes a callee's `requires`: bounds and full cells |
| `fmt_norm` | normalises the hypotheses: tuple projections, literal widths, tested results substituted, word comparisons as comparisons of naturals; splits conjunctions |
| `fmt_split` | splits every hypothesis that is a conjunction |
| `fmt_mp` | replaces each hypothesis `A → B` whose premise `fmt_pre` proves by `B` |
| `fmt_le` | closes `p.toNat ≤ (Slots.bytes s n).length` |
| `fmt_junk` | gives a position or value that no field fixes, such as the end of a union without an arm, any value |
| `fmt_is c` | fails unless the goal is an application of `c`, so that `fmt_close` tries each walk only on its own goals |
| `fmt_safe [defs]` | proves `f.safe`: splits the obligations as `mp_safe` does, adds the callees' contracts with `mp_inst_posts keep`, leaving their premises for `fmt_mp`, then unfolds `defs`, chains through the contracts with `fmt_mp`, and closes with `fmt_close` |

The option `mp.format.seedBug` (default `0`) exists for the generator's own tests: `1` makes the
parser read its first integer in the other byte order, and `2` gives each arm of the first union
the code of the next arm. Either makes the parser's contract proof fail, and the command stops
(`Tests/FormatGenFail.lean`).

## Attributes

`@[mp_auto]` tags a lemma that `mp_auto` passes to `grind`, or a predicate that the automatic
attempts and `mp_auto` unfold wherever it occurs. A predicate defined in another user file needs
this tag to be unfolded. `@[mp_auto_fwd]` tags a lemma that `mp_auto` passes to `grind` for
forward reasoning, which instantiates it from its hypotheses.

`@[spec]` is Lean's attribute for a `Std.WP` specification that `vcgen` uses, and every `f.spec`
carries it.

## Options

The options are set for one definition with `set_option … in`, or for the rest of a file.

| option | default | effect |
|---|---|---|
| `mp.autoSafe` | `true` | try to prove `f.safe`; when false, only `f.SafeGoal` is defined |
| `mp.autoSafe.maxHeartbeats` | `200000` | time budget of the automatic attempt, in thousands of heartbeats |
| `mp.autoSafe.kernelHeartbeats` | `10000` | budget of the kernel's check of an automatic proof, in thousands |
| `mp.autoSpec` | `true` | try to prove `f.spec`; when false, only `f.SpecGoal` is defined |
| `mp.unfoldPreds` | `true` | unfold the contract's predicates in the attempts and in `mp_auto` |
| `mp.analyser` | `true` | run the verified analyser before `mp_safe` |
| `mp.analyser.trace` | `false` | log what the analyser certified at each `mp def` |
| `mp.normalForm` | `true` | define the Lean function `f` and its equations |
| `mp.selftest.doMutant` | `""` | seeds a bug into the translation of blocks, for one self-test |
| `mp.format.seedBug` | `0` | test only: `mp format` emits a wrong parser, so that its proof fails (see Proofs of generated formats) |
| `mp.selftest.badProof` | `""` | gives the generated theorems of one name, such as `exp_run`, a proof the kernel rejects (Tests/FailedDefs.lean) |

With `mp.autoSafe false`, a function without partial operations still gets `f.safe`, and the
analyser does not run. With `mp.normalForm false`, a caller of the function cannot have a normal
form either, so it must be declared under the same option. The kernel checks a normal form with
its loop bounds and callees as variables, so the cost of the check does not depend on the number
of iterations (Tests/LoopBounds.lean). The option
`mp.selftest.doMutant` is refused outside `Tests/Differential/DoFuncs.lean`.
