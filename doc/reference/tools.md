# Tools

This part of the reference describes the commands that report on a program, compile it and audit
the proofs it rests on, together with the compiler driver `mpc`.

| form | does |
|---|---|
| `#mp_cost f`, `#mp_cost f with κ` | prints the static cost bound of `f` |
| `#mp_analyse f` | prints what the analyser certified for `f` |
| `#mp_report X` | prints a program's figures and how each proof was made |
| `#mp_compile p "out"`, `#mp_compile p "out" "arm64-linux"` | compiles a program to an ELF file |
| `mp_entry% "name" "desc" p` | a registry entry for `mpc` |
| `#audit`, `#audit X` | checks the axioms that theorems depend on |
| `#audit_ledger` | prints the skeleton of the assumption ledger |
| `lake exe mpc NAME -o FILE` | compiles a program of the registry |

## #mp_cost

`#mp_cost f` prints a bound on the cost of running `f` as a formula over a cost model `κ`, which
gives the cost of each kind of operation. `#mp_cost f with κ` prints the value of the bound under
the given cost model. From `Tests/MpDef.lean`:

```lean
#mp_cost clampAdd                      -- cost clampAdd ≤ κ.atom + κ.ite + 2 * κ.let_ + 2 * κ.prim + 2 * κ.word
#mp_cost clampAdd with CostModel.ones  -- cost clampAdd ≤ 8
```

## #mp_analyse

`#mp_analyse f` prints what the verified analyser certified for the obligations of `f`, counting
overflow obligations and other partial operations, and whether `f.safe` is proved. From
`Tests/Tutorial.lean`:

```lean
#mp_analyse closerOf
-- `Millipede.Tests.Tutorial.closerOf`: the analyser certified all (0 overflow, 1 other partial
-- operations); `safe` proved
```

## #mp_report

`#mp_report X` prints the figures of a program and the status of its proofs. `X` is an
`mp program`, any other constant of type `Program`, or an `mp def`.

For a program, the report gives the size of the root, the static footprint, the data region, the
stack bound and the number of instructions of `init` and of each step, and the size of the
compiled image, first for x64 and then for arm64. The instruction counts are bounds computed from
the cost model, not measurements. The report then lists each function the program calls, with
its stack bound on each target and how its obligations and contract were established. The status
is one of `none`, for a function with nothing to prove, `automatic`, `mp_auto`, `by hand` or
`open`. A generic function is marked as proved once. The report also notes how many
times wrapping arithmetic flows into an index or a slice bound, and what the analyser certified.
When `step` has a contract about events, a line after the figures names the trace theorem
`p.events_reach`, or says that it waits for `mp prove` of the step's contract.

For a generic `mp def`, the report gives the number of variables and how its proofs were
established, and it has no figures, which exist only at a closed instance. From
`Tests/Modules.lean`:

```text
Millipede.Tests.Modules.Echo.echo: generic over 1 variable(s); proved once, for every value of
them (figures: at a closed instance, `#mp_report` of a program)
  obligations automatic; contract automatic
```

## #mp_compile

`#mp_compile p "out"` compiles the program `p` for x64 Linux. It writes the ELF file `out`, and
next to it the assumption ledger, a list of what the binary relies on, in a file whose name ends
in `.ledger.txt`. A third argument names the target, `"x64-linux"` or `"arm64-linux"`, and an
unknown name is refused before anything is written.

The command refuses a program whose `p.safe` is not proved, and its message names what is
missing. It also refuses a `p.safe` that depends on `sorryAx` or on an axiom of the user, which
`#audit` would reject. The compiler itself may refuse a program it cannot translate, with a
message that names the construct. From `Tests/Tutorial.lean`:

```lean
#mp_compile brackets ".lake/brackets"
```

The options `mp.opt.inline`, `mp.opt.fold`, `mp.opt.dce` and `mp.opt.strength` switch the Core
optimisation pass of that name on or off, and all four are on by default. The option
`mp.regalloc`, also on by default, controls register allocation before instruction selection. The
correctness theorem covers every setting of these options.

## mp_entry%

`mp_entry% "name" "description" p` is a term that makes an entry of the registry of `mpc` from the
program `p` and its proof `p.safe`. It refuses a program the way `#mp_compile` does. The registry
is `Examples.registry` in `Millipede/Top/Examples.lean`:

```lean
mp_entry% "exit42" "exit(42)" exit42
```

## mpc

`lake exe mpc NAME -o FILE` compiles the registered program `NAME` and writes the ELF file and its
ledger, and `lake exe mpc --list` lists the registered programs. `--target T` selects the target,
whose default is `x64-linux` or the value of the environment variable `MP_TARGET`.
`--no-opt` switches every Core pass off, `--no-opt-PASS` one of them, and `--no-regalloc` turns
register allocation off. The variable `MP_OPT` also selects passes.

## #audit

`#audit X` collects the axioms the theorem `X` depends on and reports an error when one of them
is `sorryAx`, which an incomplete proof leaves, or an axiom of the user. Lean's standard axioms
propext, Classical.choice and Quot.sound are accepted, and so are the axioms that `bv_decide`
adds in the modules that decode and encode instructions. `#audit` with no argument audits every theorem
and axiom of the `Millipede` modules and the current file, and `#audit Ns` does the same under
the namespace `Ns`.

```lean
#audit Seeded.clean   -- #audit: 1 declarations checked, no incomplete proofs, no user axioms
```

`#audit_ledger` prints the skeleton of the assumption ledger, which names the trusted models and
the theorems that rest on compiled code. `scripts/audit.sh` runs both commands over the whole
library.
