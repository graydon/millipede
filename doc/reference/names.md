# Generated names

The commands of Millipede add Lean declarations whose names are formed from the name being
defined. This part of the reference lists them. Proofs cite these names, and the messages of the
commands use them.

## Functions

`mp def f` adds the following declarations. A reference function is one that has a reference
parameter or a precondition, and some names exist only for such functions.

| name | what it is |
|---|---|
| `f.exp` | the Core term of the function, of type `Exp Γ t`, which the compiler reads |
| `f` | the normal form, an ordinary Lean function that computes the same result |
| `f.exp_run`, `f.exp_denoteM` | the equation between the monadic meaning of the term and `f`, for a pure and an effectful function |
| `f.exp_denote` | the equation between the meaning of `f.exp` and `f` |
| `f.fn`, `f.fnRef` | the bundle that callers use, for a plain and a reference function |
| `f.req` | the precondition as a predicate on the parameters, for a reference function |
| `f.wf` | the proof that the term passes the checker, by `decide` |
| `f.SafeGoal` | the statement of the obligations under the precondition |
| `f.safe` | the proof of `f.SafeGoal` |
| `f.Safe`, `f.Safe'` | safety of the bundle, and the form that callers' proofs use |
| `f.analysed` | the analyser's certificate that every obligation holds |
| `f.expR`, `f.relaxed` | the term with the obligations the analyser certified removed, and its equation |
| `f.SpecGoal` | the contract as a `Std.WP` triple |
| `f.spec` | the proof of `f.SpecGoal`, tagged `@[spec]`; for a contract about events, `f.SpecGoal` is about a world that has not exited, and `f.spec` also says that from one that has, nothing changes |
| `f.post` | the contract as a fact about the result of `f`; for a contract about events, about the run from a world with any history that has not exited |
| `f.noCalls` | the proof that no run of `f` calls a symbol of a capability class it does not hold, when one is declared |

The normal form `f` returns its value in `Id` when the function calls no extern, directly or
through its callees. Otherwise it takes an oracle, which answers the extern calls, and returns its
value in `StateM World`. The final values of `&mut` parameters are returned as extra results
after the function's own result. `f.safe` exists only once the obligations are proved, and
`f.spec` only once the contract is proved.

## Programs

`mp program p` adds the following declarations.

| name | what it is |
|---|---|
| `p` | the program, of type `Program` |
| `p.wf_eq` | the proof that the program passes the checker, `p.wf = true` |
| `p.invariant` | the invariant `I` |
| `p.InvInitGoal`, `p.inv_init` | the statement that `init` establishes `I`, and its proof |
| `p.InvStepGoal`, `p.inv_step` | the statement that `step` keeps `I`, and its proof |
| `p.inv` | the proof that `I` holds after any number of steps, `∀ ω n, I (p.run ω n).1` |
| `p.safe` | the proof of `p.Safe`, which the compiler needs |
| `p.initRel`, `p.stepRel` | the contracts about events of `init` and `step`, as relations of the oracle, the roots, the history, the events and whether the step exited |
| `p.reach` | the proof that the state after any number of steps is one that `p.initRel` and `p.stepRel` allow, `∀ ω n, p.Reach (p.initRel ω) (p.stepRel ω) n (p.run ω n)` |
| `p.events_reach` | the same for the trace, `∀ ω n, ∃ r, p.Reach … n (r, ⟨p.events ω n, p.halted ω n⟩)` |
| `p.init` | the `init` that mints the tokens, when the given `init` takes tokens |
| `p.noCalls` | the proof that no trace calls a symbol of a capability class `init` is not granted, when one is declared |

`mp capability C` adds the token type `C` and the list `C.syms` of the class's extern symbols.

## Data types

`deriving Data` on a structure `S` adds the instance `S.instData`, which fixes the layout. For
each field `f` it adds the lens `S.f.lens` with the simp lemmas `S.f.lens_get` and
`S.f.lens_set`. It adds the constructor `S.ctor` with the lemma `S.ctor_build`, unless a field is
a proposition.

On an enum `E` it adds the instance `E.instData`, the constructor `E.c.ctor` for each
constructor `c`, and the splits that `match` uses. For two constructors the split is `E.split0`,
and for `k` constructors, when `k` is 3 or more, the splits are `E.split0`, `E.split1` and so on
up to the last constructor's number. It also adds `E.mpMatch`, which is a Lean `match` on the
enum, and the lemma `E.mpMatch_eq`.

## Units

`mp unit u : D := k` adds the simp lemma `u.scale_eq`, which states that the scale of `u` is `k`.

## Interfaces

An interface `I` is a structure, and for each operation `op` it has the fields `opF`, the Core
function, `op`, its normal form, `op_run`, `op_req`, `op_safe`, `op_pure` and, with a contract,
`op_spec`. An `mp implementation` gives these fields from an `mp def`. For each operation,
`mp interface` also adds `I.op.exp`, `I.op.req`, `I.op.exp_run`, `I.op.isPure`,
`I.op.exp_denote`, `I.op.exp_denoteM`, `I.op.Safe'`, `I.op.spec` and `I.op.post`. These are the
declarations `mp def` generates for a callee, stated over the interface's parameters and an
implementation.
