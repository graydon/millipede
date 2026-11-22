# Millipede: a reader's guide

This guide is a map of the Millipede codebase for a programmer who opens it for the first time. It
assumes no background in proofs of compiler correctness. For each part of the system it explains
what is proved or checked, which two things each proof compares, what the argument rests on and
what it assumes. The terms are defined in the [glossary](../reference/glossary.md), and where this
guide and the code disagree, the code is right.

Each section after the first two has a part called "Currently works", on the code as it is, and a
part called "Planned", on what the design asks for and the code does not have yet.

Since the previous revision the guide adds what the theorem does not say (Section 2), capability
tokens and typestate (5, 7), formats and a key-value server (11), new backend code (16, 17), three
object formats (19) and how loose the bounds are (20).

## 1. The system at a glance

Millipede is an experiment in the design of low-level languages for a time when language models
write software and search it for bugs, and [goals.md](../design/goals.md) states its hypotheses.
It consists of a small systems language embedded in Lean 4, a compiler from it to x64 and arm64
Linux executables, and a proof that the compiler is correct. The compiler is an ordinary Lean
function, and Lean checks the theorem that the bytes it produces make the same system calls as the
source, with no C compiler, assembler, linker or runtime library in between. What the source should
do is a separate theorem about each program, which Section 2.3 describes.

### 1.1 The pipeline

A program passes through the following representations on its way to bytes:

```
 mp def / mp program (do notation)
     │ elaborate                 not trusted: the kernel re-checks every output    Meta/
     ▼
 Program   root type, init, step; value and cost semantics                       Core/
     │ optimise                  Core passes, each proved to keep the meaning      Opt/
     │ check, lower              values in byte memory or frame slots    Compile/Lower*.lean
     ▼
 Flat.Prog untyped words and bytes, structured control, cost ticks       Compile/Flat.lean
     │ linearize                 the data region [0, memBytes)       Compile/Linearize*.lean
     ▼
 Lin.Prog  labels and jumps, numbered functions with fixed frames          Compile/Lin.lean
     │ allocate                  register allocation, validated by a checker     RegAlloc/
     │ select                    one driver, one selector per ISA    Target/Sel*.lean, X64/, A64/
     ▼
 Asm.Prog  ISA instructions with symbolic references                       Compile/Asm.lean
     │ budget check, assemble                       Target/Budget.lean, Compile/Assemble*.lean
     ▼
 Obj ──link──▶ Image ──write ELF──▶ bytes                                         Object/
                                      │ load (loader model)                   Object/Elf/Load.lean
                                      ▼
                       machine state ──run (ISA model, oracle)──▶ event trace   Target/
```

A pass that can fail returns an error, and each pass has its own correctness theorem. The theorems
compose into the top-level theorem of Section 2. Everything from register allocation down is done
once for each target, and everything above it is shared.

### 1.2 Where things live

| Directory | Contents |
|---|---|
| `Millipede/Core/` | types, layouts, terms, value and cost semantics, stack bound, borrow checker, obligations, quantities, programs |
| `Millipede/Extern/` | events, oracles, the world |
| `Millipede/Meta/` | `mp def` and the other commands, `deriving Data`, contracts, interfaces, `#audit`, `#mp_report`, `#mp_compile`; the only code that imports Lean's elaborator |
| `Millipede/Analysis/` | the verified interval analyser |
| `Millipede/Opt/` | the Core optimisation passes |
| `Millipede/Compile/` | the simulation framework, Flat, Lin, Asm, `lower`, `linearize`, the generic assembler, and their proofs |
| `Millipede/RegAlloc/` | the register allocator, its checker, the live sets the selectors use, and the arm64 selector with register locations |
| `Millipede/Target/` | the machine, ISA, ABI and target interfaces, the parts of selection shared by both ISAs, and in `X64/` and `A64/` each ISA's model, laws, selector and proof |
| `Millipede/Object/` | `Obj`, `Image`, the linker, the ELF writer and its loader model, and the PE32+, Mach-O and ELF relocatable-object formats, which no target uses yet |
| `Millipede/Lib/` | the allocator interface, arenas, a byte buffer, slice loops and capability tokens written in Millipede, and the standard units |
| `Millipede/Format/` | format descriptions, their parser and writer with theorems, and Millipede code for their leaves |
| `Millipede/Top/` | the statement, `compile` and its backends, the soundness theorems, the driver's entries, examples, the ledger |
| `Mpc.lean`, `Tests/`, `scripts/` | the driver, the Lean tests, and scripts that build and run binaries |

The gate is `scripts/check.sh`, which builds everything, runs every test and runs the audit.
`scripts/quick.sh` builds the library and a cheap subset of the tests while one is working.

## 2. The top-level theorem

### 2.1 What it says

The statement is `CompileSound.Statement compile t`. In plain words, it says the following for
every program `p` and byte string `b`.

> If `compile p t` returns `b` and `p` is `Safe`, then the target's loader model accepts `b` and
> produces an initial machine state `s₀`. For every oracle `ω`, the machine run from `s₀`
>
> 1. never gets stuck, so it meets no fault, undecodable instruction or unsupported system call;
> 2. has the source's event trace, with the same extern calls in the same order with the same
>    data, whether the run is finite or infinite;
> 3. stays within the stack bound, so the stack pointer never goes more than
>    `p.stackBytes t.φ` bytes below where it started, and never above it;
> 4. stays within the instruction bound of each reactor step. There are machine times
>    `marks 0 = 0 ≤ marks 1 ≤ …` such that at `marks (k+1)` the machine's trace is exactly the
>    source's trace after reactor step `k`, and at most `p.stepCost k ω t.κ` instructions run
>    between `marks k` and `marks (k+1)`.

An oracle answers every extern call, given the calls made so far, and the theorem holds for every
oracle, so it covers every input byte and every result. An event records one extern call with its
arguments, the bytes it read and wrote, and its result, never an address. A reactor is the shape
of every program, which runs `init` once and then `step` forever.

Traces are compared as limits of growing prefixes. `κ` is the target's cost model, which gives the
number of instructions each kind of operation may take, and `φ` its frame model, which gives the
stack bytes of a function's frame. The marks tie each instruction budget to a point in the trace,
so a compiler cannot move work or events from one reactor step to another. After `exit`, the
machine steps to itself without counting instructions.

### 2.2 What it assumes

The statement has two hypotheses about the program, that it compiled and that it is `Safe`, which
holds when the condition of every partial operation holds on every run, for every oracle. Nothing
is assumed about the oracle, and everything else is the trusted base of Section 3.

### 2.3 Currently works

There are two targets, `x64Linux` and `arm64Linux`, each an ISA model, Linux's system calls on that
ISA, and static ELF64. `compile p t` runs the shared passes and checks, then the backend of `t`,
which allocates registers, selects, checks the budget, assembles, links and writes the ELF file.

The soundness proof is written once. A backend proves a short list of laws, chiefly that its
writer's output loads back as the image's initial state and that its selected code simulates the
lowered program from that state within the budget. One theorem composes these laws with the shared
passes. The two headline theorems, `Millipede.compile_sound` and `Millipede.compile_sound_arm64`,
are that theorem at the two backends. Both are proved with no hypotheses, so the compiler is correct
on every program it accepts, for both targets, with no assumption beyond `Safe`. The audit checks
that both headlines have exactly the statement as their type. The x64 headline depends only on
Lean's three standard axioms, and the arm64 one also on the axioms that `bv_decide` adds for its
encoding lemmas.

A program's lenses, constructors and splits are records of Lean functions, and nothing in their
types ties them to the byte layouts. Each therefore carries a certificate of its law, and `compile`
refuses a program that uses one without a certificate, so every accepted program is lawful.

The theorem says that the machine's trace is the source's trace, and a theorem about the source
trace is what tells a reader what the bytes do. Two such theorems are proved for every oracle and
carried to the bytes. `hello` writes its greeting and exits with 0, and `revchunks` runs in rounds,
each of which reads up to 16 bytes and writes them reversed, until the input ends. For the other
programs only the classes of system calls they cannot make are proved, as Section 5 describes.
Each of these corollaries keeps the hypothesis that `compile` returned bytes, which is shown by
running `compile` as compiled code. Lean's kernel has evaluated `compile` on `exit42` and `hello`
for both targets, which gives theorems without that hypothesis. For `revchunks` the kernel does not
finish the budget check, so its acceptance is an open claim. A `write` event records the bytes the
program asked to write, so a program that ignores a short write loses output while the theorem
holds.

Where this lives: `Millipede/Top/`: Statement, Compile (`Backend`), Sound
(`compile_sound_of_backend`, `Backend.Laws`, `compile_lawful`), SoundA64, Trace, Behaviour
(`hello_behaviour`, `revProg_behaviour`), Accept (`hello_runs`, `exit42_runs`);
[limits.md](../design/limits.md), which lists what the theorem does not say.

### 2.4 Planned

The same statement for every target in the plan, and theorems beside it about refinement,
noninterference and protocols, which Section 25 describes.

## 3. What is trusted, and the evidence for it

A proof is only as good as the definitions it is about. The following parts are the ones the
theorems cannot check.

### 3.1 Currently works

| Trusted part | Why | Evidence |
|---|---|---|
| The Lean kernel | it checks every proof | none beyond Lean itself |
| `bv_decide` | a bit-vector decision procedure that runs compiled code and adds one axiom per use; allowed only in the arm64 encoding modules `A64/Word` and `A64/Decode`, since the x64 ones are proved in the kernel | `#audit` re-runs each checker and refuses the axiom anywhere else |
| Lean's compiler and runtime | the theorem is about the function `compile`, and the bytes come from running it natively | the differential suites; `Tests/Top.lean` runs the whole pipeline on the machine models and compares with the source |
| The x64 ISA model | it defines what the CPU does | co-simulation against `qemu-x86_64` on random instruction sequences; the encoder against GNU objdump |
| The arm64 ISA model | the same | co-simulation natively on the host CPU; the encoder against `llvm-mc` and objdump |
| The Linux system-call model | it says which registers hold a call's number, arguments and result, and what the kernel may write | every compiled program runs, x64 under qemu and arm64 natively; a lock-step I/O test with short reads |
| The ELF loader model | it defines what `execve` does | x64: `readelf` and qemu on good and corrupted files; arm64: `readelf`, `eu-elflint`, the linkers ld.lld and GNU ld, and the model's initial state against the kernel's under gdb |
| The statement | a wrong statement would make the theorem meaningless | review, and this guide |

The loader model places the stack below a fixed top, because compiled code never observes an address
and address randomisation is not modelled. The oracle is not an assumption, but the kernel's effect
on memory is, so for `read` the model assumes that the kernel writes at most the requested number of
bytes. The x64 evidence comes from qemu, so it is evidence about qemu as much as about the model.
The loader models of PE32+ and Mach-O, and the system linkers that link Millipede's relocatable
objects, are trusted as well, but no theorem about a target rests on them yet. Every other part,
from the elaborator to the ELF writer, is proved, or its output is checked by the kernel or by a
proved checker.

Where this lives: [trust.md](../design/trust.md), [limits.md](../design/limits.md);
`Millipede/Top/Ledger.lean`; Section 24.

### 3.2 Planned

Model-based tests of extern bindings, runs on other hardware, and a red-team loop in which agents
try to produce behaviour that the theorems forbid.

## 4. The core language and its two semantics

### 4.1 Currently works

Everything in this section is proved, for all terms and all oracles. A program is a value of the
Lean type `Exp Γ t`, a term whose result has type `t` and whose free variables have the types
listed in `Γ`. This is a deep embedding, in which the program is data that Lean can inspect, which
matters because cost, layout and linearity are properties of syntax. A variable is a typed
position in `Γ`, so an ill-typed term cannot be built.

The operands of primitives, conditions, constructors and calls are atoms, each a variable or a
literal, so `Exp` is one plain inductive type whose meaning is defined by structural recursion. A
call carries the callee's body as a subterm. A function therefore cannot mention itself, and there
is no recursion. A loop runs a static number of iterations, each of which first tests a condition,
and carries the variables bound outside it that its body writes.

A place is a path into a variable, such as a field, an array element, a `Slots` cell, a slice or a
pair of elements. A slice is a view of a run of array elements. It cannot be stored, and at the
machine it is an address and a length. Primitives mean what the machine does, so arithmetic wraps,
`x / 0 = 0`, `x % 0 = x`, and a shift amount is taken modulo 64.

The value semantics is an ordinary Lean function from an environment and a world, the trace so far,
to a result and a new world, with no memory, no addresses and no cost. A place is a lens, a pair of
functions that read a part of a value and rebuild the value with that part replaced. A `&mut`
borrow reads the place when its scope begins, and the body hands back the updated value. Program
proofs therefore never reason about aliasing, and the memory refinement of Section 14 shows that
updates in place through pointers give the same result.

The cost semantics computes the value and the world again, and also counts the steps of the path
taken under a cost model `κ`, which each target supplies. A reference costs the same whatever the
size of what it points to, because it is an address. The cost theorem says that for every oracle,
cost model and term, the cost semantics returns what the value semantics returns, and takes at most
a static bound computed from the syntax.

A partial operation has a `!` form, such as `a[i]!` or `alloc!`, which compiles to no check and
carries a proof obligation, and many also have a checked form, which returns a `Result`. The safety
predicate collects the obligations along the evaluation, including at each call the callee's
`requires` and its own safety, which is proved once per function. Safety is a hypothesis of the
compiler theorem because the source gives an out-of-range read a default value, while the compiled
code really reads memory.

Where this lives: `Millipede/Core/`: Exp, Denote, Cost (`Exp.exec_sound`), Place, Safe, Checked.

### 4.2 Planned

A single semantics that returns steps, frame depth and events, as the design's `Usage` record does,
and `inline` definitions with block parameters. Neither is started.

## 5. Externs, the oracle and event traces

### 5.1 Currently works

An extern call in the source and a system call on the machine produce the same call record and go
through the same function, which asks the oracle for an answer and appends an event. This shared
path is what makes trace equality a meaningful statement. The world is the list of events and a
flag that says whether the program has halted, and after `exit` the world no longer changes.

There are three externs. `exit` ends the program, and `write` writes constant bytes or a shared
slice of a byte array. `read` reads one byte, whose value is the byte or 2^64 − 1 at the end of the
input, or reads into a mutable slice of a byte array. The oracle chooses every byte of input and
how many bytes each `read` returns.

A capability class is a named set of extern symbols, and an extern of the class can be called only
by a function that holds a token of it. A token takes no space at run time and is linear and
sealed, so code can neither copy nor build one. A program's grant is the classes whose tokens its
`init` takes, and for every other class `mp program` proves that no run calls one of its symbols,
which the equal traces carry to the machine. This proof reads only the symbols that the program's
terms mention, so it would hold without tokens, which make each function's authority visible in
its signature and checked where the function is defined. A class cannot tell one file descriptor
from another, because an event records only its symbol.

Where this lives: `Millipede/Extern/Oracle.lean`, `Millipede/Compile/LowerExt.lean`,
`Millipede/Target/Abi.lean`, `Millipede/Lib/Cap.lean`, `Millipede/Meta/Cap.lean`,
`Millipede/Core/Effects.lean` (`Program.noCalls_of`), `Millipede/Top/NoCalls.lean`
(`Program.NoCalls.machine`); [world.md](../design/world.md).

### 5.2 Planned

Externs with the C calling convention, classes finer than a symbol, extern bindings whose
specifications are assumed as hypotheses, and portable interfaces for files, the network and
clocks, all described in [world.md](../design/world.md).

## 6. Programs: the root and the reactor

### 6.1 Currently works

A `Program` is a root type, a term `init` that builds the root, and a term `step` that takes the
root by `&mut`. There are no global variables, and all state that lasts from one step to the next
is in the root, which lives in static storage. The static cost of each reactor step, the stack
bound and the footprint are computed from the syntax. Every reactor step stays within its cost and
its stack, and the trace only grows and stops growing after `exit`. Each step terminates, because
there is no recursion and every loop is bounded, so the reactor step is the unit of cost.

Where this lives: `Millipede/Core/Program.lean`.

### 6.2 Planned

A blocking wait at the start of each step, and refinement, in which every trace of a program is
proved to be a trace of an abstract machine, described in [protocols.md](../design/protocols.md).

## 7. The checker: linearity and borrowing

### 7.1 Currently works

The checker walks a term in evaluation order, keeping a record of each variable's mode, moves and
borrows. It returns a `Bool`, so a closed term is checked by `decide`. It enforces three rules, of
which the first is linearity. A value of linear type, such as a `Result` or an arena key, is used
exactly once on every path. Both arms of a branch consume the same variables, and a loop body
consumes nothing bound outside it.

The second rule is borrowing by place. While `&mut p` is live, no place that overlaps `p` is used,
and while `&p` is live, overlapping places may be read but not written. Distinct fields are
disjoint. Two elements of an array overlap unless they are borrowed together as a pair, and then
their distinct indices are an obligation.

The third rule is the block rule. A block may write only its own variables, so inside the value of
a `let`, a borrow body or a loop, the variables bound outside are read-only, except those a loop
carries. This makes the value semantics, in which an assignment changes the rest of the block,
match the intuition of imperative code.

The compiler theorem uses two facts about accepted terms, that they obey the block rule and that
they are frozen. A term is frozen when no place lent by a borrow or passed by reference is reached
except through the reference. This is what lets references be pointers, because updating a lent
place in place then cannot be told apart from the semantics of lenses. No compiler theorem depends
on linearity, which the arena library relies on to free each key exactly once.

Linearity also gives handles a typestate, a state carried in the handle's type. A log, for example,
must be synced before it is closed, and the checker rejects a use in the wrong state, a use after
close, a double close and a handle that is never closed. This is tested, and no theorem states it.

Where this lives: `Millipede/Core/`: Wf, WfSound (`Exp.frozen_of_wf`);
`Millipede/Compile/LowerRestr.lean`; `Millipede/Meta/ANF.lean`, which runs the checks with source
positions; `Tests/Log.lean`.

### 7.2 Planned

Transitions of a handle to one of several states, and a separate checker of information flow.

## 8. Types, layouts and quantities

### 8.1 Currently works

An object type is a Lean type, its carrier, together with a `Data` instance. The instance records a
shape, which describes the memory layout, a relation that says which bytes represent a value,
whether values are linear, and the occupancy of the value's `Slots` components. The representation
is a relation because padding bytes and empty cells may hold anything.

Layouts follow the C rules for naturally aligned fields. `deriving Data` on a structure or enum
generates the instance, a lens for each field, the constructors and an exhaustive split, each with
a certificate of its law. Recursive types are rejected, and `scripts/layout-check.sh` compares the
layouts of a dozen types with those gcc gives.

A quantity is a word tagged with a unit, as in `Q KiB`, and a unit is a dimension and a scale. The
elaborator checks that `+`, `-` and comparisons have one unit on both sides, and that conversions
are explicit and name their rounding, and then erases units, so Core never sees a quantity.

Where this lives: `Millipede/Core/`: Ty, Shape, Data, Lawful, Quantity; `Millipede/Meta/`: Derive,
Units.

### 8.2 Planned

Exact conversions across scales, quantity fields in derived structures, and labels for information
flow, described in [security.md](../design/security.md).

## 9. The surface language: `mp def`

### 9.1 Currently works

A function is written with `mp def`. Its body is an expression or a block of statements in the
notation of Lean's `do` blocks:

```lean
mp def kindOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3
```

Lean's parser reads the block, and Millipede translates it into Core. The one loop form is `for i
in lo...hi do`, whose upper bound has a static cap, and a jump out of a loop becomes a flag that
the loop carries. Other forms of Lean's `do` blocks, such as `while`, are refused.

The elaborator converts the body to a named A-normal form, runs the checks of linearity and
borrowing on names so that errors point at the source, and emits the Core term `f.exp`. It then
generates declarations that the kernel checks. `f` is an ordinary Lean function equal to the
meaning of `f.exp`, and `f.exp_denote` is the equation between the two. `f.wf` is the checker's
verdict, `f.safe` the proof of the obligations, and with `ensures`, `f.spec` the proof of the
contract. `mp program` builds a `Program` from two such functions, and `#mp_report` prints its
figures for both targets and how each obligation and contract was proved.

The elaborator need not be trusted, because every theorem about a program is about the term
`f.exp`, which the compiler compiles, and `f.exp_denote` ties that term to the function `f` that
the user reads. The kernel checks each generated theorem before the command ends, so a rejected one
stops the `mp def`. The equation is proved with loop bounds and callees held abstract, so a loop of
any literal bound costs the kernel the same time.

Where this lives: `Millipede/Meta/`: Elab, Syntax, ANF, MpDef. Every form is described in the
[surface reference](../reference/surface.md), and the [tutorial](tutorial.md) builds one program
from nothing to a running binary.

### 9.2 Planned

The commands `#mp_asm` and `#mp_bytes`, and the forms of `do` blocks listed in
[open-claims.md](../open-claims.md).

## 10. Obligations, contracts and the analyser

### 10.1 Currently works

`mp def f … requires P` produces the goal that every obligation of `f.exp` holds whenever `P`
holds. `mp def` tries the verified analyser, then the tactic `mp_safe`, which splits branches and
loops and uses the callees' contracts, then `mp_auto`, which calls `grind`. A goal that is still
open is left for `mp prove f.safe := …`.

A clause `ensures Q` states a postcondition over the result and the final values of the `&mut`
parameters. It is proved as a `Std.WP` triple about `f` and registered for `vcgen`, so a caller's
proof uses the contract at each call and never unfolds the callee. The obligations and the contract
are separate proofs, because the Core term carries the obligations and `f` does not.

`mp program p … invariant I` generates two goals, that `init` establishes `I` and that `step` keeps
it and is safe under it. A library theorem, proved once, turns them into the facts that `I` holds
after every step for every oracle and that `p` is `Safe`. `+` wraps, `+?` returns a `Result` that
is `ok` exactly when the result fits, and `+!` carries the obligation that it fits, and the same
holds for `-` and `*`.

Programs are data, so an interval analysis can run over a term inside the kernel. The analyser
tracks intervals of words and bytes, the comparisons known on the current path, and upper bounds
that grow linearly with a loop counter. When it certifies a term, the term is safe under the input
intervals, which `mp def` reads from `requires`. When it certifies only some overflow obligations,
those operators are relaxed to their wrapping forms, which a second theorem shows mean the same,
and only the rest become goals. Both theorems assume a shape of loop bodies that each definition
proves.

Where this lives: `Millipede/Meta/`: Contracts, Program, Spec (`Program.safe_of_inv`), Auto,
Overflow, Analyse; `Millipede/Analysis/Sound.lean` (`Exp.an_sound`, `Exp.safe_of_relax`);
[obligations.md](../design/obligations.md).

### 10.2 Planned

The obligations and the contract in one proof, contracts about events, and inputs to the analyser
that it does not read yet. The limits of the automation are listed in
[open-claims.md](../open-claims.md).

## 11. Generic code, interfaces and the arena library

### 11.1 Currently works

`mp def`, `mp prove`, contracts, `mp program` and `deriving Data` all work under Lean `variable`
binders, where a variable is a type, a size with hypotheses about it, or an implementation of an
interface. Every theorem about a generic definition is proved once for all values of its
variables, and an instance is an application, so the pool of 8 words is `Pool UInt64 8 1`, and its
safety is the generic theorem applied. `compile` sees only closed programs.

`mp interface` declares a Lean structure of abstract types, an abstract model, and for each
operation its Core function, normal form, safety and contract. `mp implementation` fills such a
structure from `mp def`s. A client written over an implementation variable has its obligations and
contracts proved from the interface's contracts alone, once for every implementation.

There is no heap. Storage whose occupancy changes at run time is built from `Slots`, in library
modules written in Millipede. `Alloc` is the allocator interface, and the bitmap pool `Pool T n W`
and the bump arena `Bump T n` implement it. `ByteBuf cap` is a buffer whose contents are passed in
place as slices to `read` and `write`. A request server written once against `Alloc` is compiled
and run with both arenas.

A key is a linear, sealed structure of 8 bytes that only `alloc` makes and only `free` consumes, so
outside the library a key can be neither forged nor dropped. Its type carries the arena's
parameters, so a key given to an arena of another kind is a type error, and when two arenas share
a key type, access by key carries the obligation that the arena owns the key.

A format description `Fmt` describes a binary message built from integers, byte strings, constants,
pairs, counted repetitions and unions selected by a tag, and the model gives it a parser, a writer
and a validator. For every description the parser reads back what the writer wrote, written bytes
stay within a static size, a canonical description's parse consumes exactly the value's bytes, and
the validator accepts what the parser accepts. Millipede code for the integer and length-prefixed
leaves is proved against the model, and a key-value server `kvsrv` composed from it by hand is
proved to answer each request as the model's parser, the store and the model's writer say. It runs
on both targets against an independent reference, and its event trace is not specified.

Where this lives: `Millipede/Meta/Iface.lean`; `Millipede/Lib/`: Alloc, Pool, Bump, Bitmap,
ByteBuf, Slice; `Millipede/Top/`: Requests, Tally; `Millipede/Format/`: Model, Theorems
(`Fmt.parse_write`, `Fmt.valid_iff`), Code; `Tests/FormatKVSrv.lean` (`srvStep.spec`);
[modules.md](../design/modules.md).

### 11.2 Planned

Brands for each arena value, the analyser and the numeric figures for generic code, which exist
only at closed instances, and relations of cost and size in interfaces. For formats, code and its
proof generated from a description, Millipede code for the other leaves, and the server's trace
against its protocol. These are listed in [open-claims.md](../open-claims.md).

## 12. The simulation framework

### 12.1 Currently works

Every level of the compiler, from the source reactor through Flat, Lin and Asm to the machine, is
presented as a semantics. A semantics has a type of states, a step function from a state to an
optional next state, the events so far, and a work counter called the clock. A step that returns
nothing means that the level is stuck, and a finished program steps to itself.

A pass is shown correct by a forward simulation. It relates source states to target states, and
proves that whenever related states take a source step, the target can take zero or more steps to a
state related to the new one, with equal traces. When the target takes no step a measure must
decrease, so the target cannot stall while the source moves, and the target's clock advances by at
most a fixed factor of the source's. Simulations compose, and the clock bound holds on every
segment between matching times, which gives the marks of clause 4.

A forward simulation shows only that the target can do what the source does. The target is
deterministic, so the run the simulation builds is the only run, and the source never gets stuck,
because there is no undefined behaviour, no recursion, and every loop is bounded.

Where this lives: `Millipede/Compile/Sem.lean` (`FwdSim.comp`, `FwdSim.schedule`).

### 12.2 Planned

Nothing beyond the passes that later sections plan, each of which comes with its own simulation.

## 13. Core optimisation

### 13.1 Currently works

Before lowering, `compile` rewrites the program with four Core passes. `inline` replaces a call
whose body only reads its parameters with the body, the arguments substituted. `fold` evaluates a
`let` of a constant, an `if` on a literal and a `match` on a literal. `dce` removes a `let` whose
variable is unused and whose value has no effect. `strength` replaces division and remainder by a
power of two with a shift and a mask.

Each pass proves two laws for every oracle, environment and world. The rewritten term has the same
meaning as the original, value and world alike, and its obligations follow from the original's, so
a pass may drop an obligation but never add one. A pass's result is kept only when its static cost
and stack bound are no larger than the input's, which is decided when the program is compiled.

A relation between the optimised program and the source transfers the four clauses back, so the
theorem still speaks of the program the user wrote. If the rest of the pipeline refuses the
optimised program, `compile` tries ever shorter prefixes of the list of passes. Over the
differential suite the passes remove about a fifth of the static instructions.

Where this lives: `Millipede/Opt/`: Pass (`Pass.apply`), Rewrite (`Pass.bu`), Subst
(`Exp.subst_denote`), Rules, Config; `Millipede/Top/Sound.lean` (`Program.Sim`); figures in
[measurements.md](../measurements.md).

### 13.2 Planned

Constant propagation and check elimination driven by the analyser, which wait until `compile` can
decide the analyser's hypothesis about loops, and common-subexpression elimination.

## 14. Lowering: Core to Flat

Flat is the first untyped level. Its values are 64-bit words in numbered frame slots or bytes in
memory, its control flow is structured, and it has cost ticks. Lowering places one tick for each
Core construct, where the cost semantics charges it, so the Flat clock equals the step count of the
cost semantics exactly, and later passes must pay for their work out of those ticks.

### 14.1 Currently works

Every Core value lives in byte memory, in the layout of its shape, except the values kept in frame
slots. Each activation owns a region of memory with each variable at a static offset, and since
there is no recursion, a callee's region starts where its caller's ends. The root sits at address
0, and each reactor step updates it in place.

A variable whose address is never formed, and whose type is one byte or one to four words, such as
a scalar, a `Result` or a small structure, is kept in consecutive frame slots instead. Results of
such types are returned as words, and owned parameters of one word are passed as words.

The proof of lowering keeps a relation, the memory refinement, which says that the bytes in memory
and the frame slots represent the source's values. References are pointers, and a slice is an
address and a length, so a borrow's body works on the lender's storage in place. While a `&mut`
borrow is live, the lender's bytes change but its source value does not, so the memory refinement
leaves these bytes out as a hole in the lender. Accepted terms are frozen, as Section 7 describes,
so no access reaches into the hole.

At the end of a `&mut` borrow of a slice, the value semantics writes the view back into the array
from full cells only, while the machine has already written the elements in place, so `compile`
checks a syntactic condition, the hand-back condition, which implies that the cells are still full.

The theorem of lowering covers every cost model, oracle and term that `compile` accepts. From memory
and slots that represent the environment, the lowered code reaches a state with the world of the
cost semantics, the clock advanced by exactly its steps, the destination representing the value, and
everything outside the destination and the term's writable variables unchanged, or else it halts
after `exit`. The proof is by induction on the term, with one lemma for each construct.

`compile` refuses a few constructs rather than make a claim about them, each with a message that
names it, and [open-claims.md](../open-claims.md) lists them.

Where this lives: `Millipede/Compile/`: Flat, Lower (storage, slots, refusals), LowerSim,
LowerSound (`Flat.lowerM_sound`), the other Lower files (one for each group of constructs),
HandBack, BackOk (a counterexample), LowerProg (`Flat.lower_sound`).

### 14.2 Planned

Slots for fields smaller than a word and parameters of several words, and fewer refusals.

## 15. Linearize: Flat to Lin

### 15.1 Currently works

Lin replaces structured control with labels and jumps, and replaces the callee bodies that Flat
keeps inline with numbered functions, each with a frame of fixed size. A callee always has a
smaller number than its caller, so there is no recursion in Lin either. `linearize` is a forward
simulation from Flat to Lin in which related states have equal frames, memories, worlds and clocks,
and the Lin code at the current position is the compiled form of the current Flat statement.

Lin has a data region of the program's static size, and a load or store outside it is stuck, so
that selection can map Lin's memory onto exactly that many machine bytes. The memory refinement
bounds every Flat access to the region, and lowered code provably uses only its declared frames.

Where this lives: `Millipede/Compile/`: Lin, Linearize, LinearizeProof (`Lin.linearize_sound`),
LinearizeLower (`Lin.lowerInBounds`), LowerStack.

### 15.2 Planned

Nothing specific.

## 16. Register allocation: Lin to Lin

### 16.1 Currently works

Register allocation rewrites a Lin program so that each frame slot is replaced by a location.
Locations below a number `k` are machine registers, and the others are words of a smaller frame. The
allocator is ordinary Lean code that is not proved. It joins the uses and definitions of each value
into a web and colours the webs greedily, and a web keeps one location for its whole life, so no
moves are inserted.

Along with the new program, the allocator gives for each code position a map from the source slots
still needed to their locations, and the live locations. A checker looks at one instruction at a
time, and checks that the operands are where the map says and that each entry of the next
position's map is defined by the instruction or carried over unchanged.

When the checker accepts, the new program runs in lock-step with the old one, with the same
function, position, memory, world and clock at every step and every mapped slot's value in its
location. Its stack bound is no larger. When the checker refuses, `compile` keeps the program as it
was, so a bug in the allocator costs speed, never correctness.

The default is six register locations on both targets. Against allocation off, it removes about two
fifths of the static instructions on x64 and a third on arm64, a quarter of the executed
instructions, and two thirds of the stack. On arm64 an option adds up to nine caller-saved
registers as locations for values that are not live across a call, and a check refuses a value
live in a register that an instruction destroys. This is proved and off by default, and the same
for x64 is in progress.

Where this lives: `Millipede/RegAlloc/`: Alloc (the allocator), Check, Sound
(`RegAlloc.lockOfCheck`, `check_stackBytes`), Lock (`Lock.id`); figures in
[measurements.md](../measurements.md).

### 16.2 Planned

Nothing specific beyond the backend work of Section 17.

## 17. Instruction selection: Lin to Asm

### 17.1 Currently works

Each Lin instruction becomes a fixed block of machine instructions. An operand or result in a
register location is used in place, and any other goes through a scratch register to or from its
frame word. Lin's data region becomes a zero-initialised region called `mp_mem`, externs
become Linux system calls, and every reference to code or data is relative to the program counter.

The register locations are `rbx`, `rbp` and `r12` to `r15` on x64, and `x19` onwards on arm64, and
nothing else in the selected code writes them. Before a call, the caller saves each register that
the callee may use and that holds a value live after the call, into the callee's frame word of the
same number, which the callee leaves unused. The callee's return restores them from its own frame.
Every activation therefore sees the registers as Lin sees its slots, and the frames do not grow. A
call writes only the callee's locations that are live at its entry, and a move of a location to
itself selects no code.

On x64, division is guarded without branches, so that `x / 0 = 0` where `div` would fault. On
arm64, frames are rounded to 16 bytes because accesses based on `sp` need that alignment, and data
addresses are formed by `adrp` and `add`, which reach ±4 GiB. arm64 also adds or subtracts a
constant below 4096 as an immediate, and stores a zero from its zero register.

Most of the proof is shared by both ISAs. A frame relation says that the machine's stack holds
Lin's frames and that the bytes at `mp_mem` are Lin's memory, and the simulation reduces to one
fact: from related states, the block of one Lin instruction takes the machine to a state related
to the next Lin state, in exactly the number of instructions the budget counts. Moves, operations,
loads, stores and extern calls are proved once from laws each ISA proves about operands and
results, and each ISA proves its jumps, calls, returns and the entry of `main` for itself.
`select` refuses externs other than the three, frames beyond each ISA's reach, and constant
buffers of 2^32 bytes or more.

Where this lives: `Millipede/Target/`: SelDriver, SelFrame, SelSim (`Sel.selectSim`,
`Sel.select_lower_sound`), SelCases, SelOps, SelExt, SelRun, SelMem; `Millipede/Target/X64/`:
Select, SelectProof, SelectCall; `Millipede/Target/A64/`: Select, SelectProof;
`Millipede/RegAlloc/`: A64Reg, A64RegProof, A64RegCall, A64RegSound.

### 17.2 Planned

Stores of an immediate on x64, compare-and-branch fusion, bit-field forms for fields smaller than a
word, caller-saved locations on x64 and by default, and more sharing of the cases that each ISA
proves for itself.

## 18. The machine models and their laws

### 18.1 Currently works

Memory is a map of bytes with permissions for each page. A read needs `r`, a store needs `w`, and
instruction fetch returns only executable bytes. Permissions never change, so with W^X code is
never modified. The machine's step is the same for every ISA, which is to fetch, decode and
execute, and a decode failure or a fault makes the machine stuck. The system-call instruction calls
a handler supplied by the ABI, which asks the oracle through the same path the source uses.

The x64 model has sixteen registers, four flags and 21 instruction forms. Its memory accesses fault
on non-canonical addresses, and `div` faults on a zero divisor. The arm64 model has thirty-one
registers, `sp` and four flags, and the instructions that selection needs in their 64-bit and
32-bit forms. An access based on `sp` faults when `sp` is not a multiple of 16, as Linux configures
the CPU. The subsets are listed in [targets.md](../design/targets.md).

Each ISA proves the same laws. Decoding an encoded instruction gives it back, the decoder accepts
only canonical encodings, and an instruction other than the system call changes only the registers
and bytes it names. Gaps in a model are not dangerous, because the theorem says that compiled
programs never get stuck, so an instruction the model lacks can only make the proof harder.

Where this lives: `Millipede/Target/`: Machine, Isa, Abi, Target; each ISA's Instr, Encode, Decode,
Exec and Laws in `Millipede/Target/X64/` and `Millipede/Target/A64/`.

### 18.2 Planned

The ABIs of macOS and Windows, in phase 5.

## 19. Assemble, link, write, load

### 19.1 Currently works

The assembler is generic. Functions go into `.text`, constants into `.rodata` and the data region
into `.bss`. Local labels are resolved as distances inside a section, and other symbols become
relocations. An ISA proves four laws about one instruction, chiefly that its bytes, once relocated,
encode the instruction resolved at its address, so decoding at any label gives the intended
instruction wherever the sections are placed. arm64 uses a word assembler with fixups.

The linker merges sections into three page-aligned segments, text at `0x400000`, read-only data
and read-write data, resolves symbols, applies relocations, and asks for the proved stack bound as
the stack size. Its theorems say that every section sits at its address with its relocations
applied, and that the segments are disjoint, below the stack, and never writable and executable.

The writer emits a static ELF executable. The loader model is a Lean function that describes what
`execve` does, and the format law says that loading the written bytes gives exactly the image's
initial state, which a last theorem shows is a correct start for the simulation of selection.

Three more formats have a writer, a model of their loader or reader, and the same kind of law, and
no target uses them yet. PE32+ is the Windows format, and its test files run under wine. Mach-O is
the macOS format, whose loader model recomputes the SHA-256 of each page that the code signature
records, and good files ran on a Mac. ELF relocatable objects, for both ISAs, read back as the
object written, and a program's object links to the same image as its executable. System linkers
link these objects in tests, and no theorem covers a program they link.

Where this lives: `Millipede/Compile/`: Assemble, AssembleLaws (`Asm.assemble_text`),
AssembleProof, AssembleWord; `Millipede/Object/`: Link, LinkProof, `Elf/` (`Elf.load_write`), `Pe/`
(`Pe.load_write`), `MachO/` (`MachO.load_write`), `ElfRel/` (`ElfRel.read_write`,
`Compile.objLink_compileRun`); `Millipede/Target/SelInit.lean`.

### 19.2 Planned

Smaller arm64 images, whose argument is in [targets.md](../design/targets.md), the macOS and
Windows targets that use these writers, and a driver option that writes relocatable objects.

## 20. Cost accounting: instructions per reactor step

### 20.1 Currently works

Clause 4 rests on a chain of facts. The steps of the cost semantics are at most the static cost,
the Flat clock equals those steps, linearize and register allocation keep the clock, and selection
must bound the machine's instructions by the Lin clock. In that last link, a Lin instruction other
than a tick costs nothing on the Lin clock but becomes several machine instructions, and a tick
costs its weight but becomes none, so the argument is an amortised accounting. A certificate gives
every code position a potential, the number of instructions that may still run from there before
later ticks pay for them. The budget check verifies at every position that one Lin step pays for
its instructions out of the potential and the tick's weight, and that the potential is 0 where a
reactor step ends, so a reactor step executes at most its static cost in machine instructions.

An untrusted fixed-point iteration computes the certificate, and `compile` refuses the program if
the check fails, so each target's weights `X64.κ` and `A64.κ` are validated for each program.

The bound is sound but loose, because it charges every construct its most expensive code and every
loop its largest count. Measured under qemu, the step bounds of the registered programs are 3 to 45
times the instructions they run and their stack bounds 5 to 56 times the stack they use, and for
two larger programs the step bound is 154 to 361 times the largest step. Part of the gap is that the
cost semantics charges words that lowering never copies, and a fix of that is in progress.

Where this lives: `Millipede/Target/Budget.lean`, `Millipede/Target/SelSim.lean`
(`Sel.select_lower_cost`); `scripts/bound-check.sh`; [measurements.md](../measurements.md).

### 20.2 Planned

Weights proved valid once for all programs, and a cost semantics that charges only the words that
lowering copies.

## 21. The stack bound

### 21.1 Currently works

A frame model gives the stack bytes of an activation with `w` word slots. x64's is `8(w + 1)`, the
slots and the return address. arm64's is the slots and the saved link register, rounded up to 16
bytes. Core computes from the syntax the slots of each frame, with 16 scratch slots that the
compiler uses besides those of the values, and the deepest chain of callee frames, which is finite
because there is no recursion. The Lin bound is within the source bound for every frame model,
register allocation never enlarges a frame, and the machine's stack pointer stays within the Lin
bound, so no check is run for each program. The linker records the bound in `PT_GNU_STACK`.

Where this lives: `Millipede/Core/Stack.lean` (`Exp.stackUse_le`),
`Millipede/Compile/LowerStack.lean` (`Lin.lower_linearize_stackBytes_le`),
`Millipede/RegAlloc/Sound.lean` (`check_stackBytes`), `Millipede/Target/SelSim.lean`
(`Sel.select_stack`).

### 21.2 Planned

Recording the stack bound in other formats, and guard pages.

## 22. Composition, the driver and the ledger

### 22.1 Currently works

The composition theorem unpacks a successful compilation into the result of each pass and applies
the theorem of each.

The driver compiles only an entry, which is a program together with the proof that it is `Safe`,
checked by the kernel and the audit when the entry is built. `lake exe mpc [--target T] NAME -o
FILE` compiles a registered entry for `x64-linux`, the default, or for `arm64-linux`, and
`#mp_compile p "out"` does the same for any program with a proof of safety. Both write the
executable and an assumption ledger, which names the externs, the target and its trusted models,
the theorems that cover these bytes, the options used, the evaluated bounds and the evidence for
each trusted part.

The registered programs are `exit42`, `hello`, `sum`, `ticks`, `readcount`, `revchunks`,
`pooltally`, `reqspool` and `reqsbump`.

Where this lives: `Millipede/Top/`: Sound, Driver, Examples, Ledger; `Millipede/Meta/Emit.lean`;
`Mpc.lean`.

### 22.2 Planned

Ledger entries for assumed bindings, once bindings exist.

## 23. The audit and the open claims

### 23.1 Currently works

`scripts/check.sh` forbids `sorry`, `axiom` declarations and `native_decide` outside `scratch/`.
`#audit` collects the axioms that each theorem of the library depends on, and fails on `sorryAx` or
on any axiom of the user. The only other axioms allowed are those of `bv_decide`, and each is
accepted only after `#audit` runs its checker again and confirms that it was used in one of the
two arm64 encoding modules. `scripts/audit.sh` also checks the two headline theorems.

An open claim is a statement that cannot be proved yet. It is written as a `Prop` with no proof and
registered in [open-claims.md](../open-claims.md), and the audit fails when such a statement is
neither proved nor registered. One claim is open, that `compile` accepts `revchunks` with the
default options, which the kernel does not finish evaluating.

Where this lives: `Millipede/Meta/Audit.lean`, `scripts/audit.sh`, `Tests/Audit.lean`.

### 23.2 Planned

A check in the gate on wrapping arithmetic used for sizes.

## 24. The test suites and what each is evidence for

The script suites run from `scripts/run-tests.sh`, which the gate calls. Every suite must be shown
to catch a seeded bug, which is what the `--selftest` modes do, and [status.md](../status.md) lists
each suite's seeded bugs. `scripts/differential-srcseed.sh`, which seeds a bug in the compiler's
source, is slow and is not in the gate.

### 24.1 Currently works

| Suite | What it does | Evidence for |
|---|---|---|
| Differential, `scripts/differential.sh`, `scripts/differential-a64.sh` | runs `mp def` functions on inputs biased to edge cases, read at run time, inside a compiled harness that compares each result with a reference in plain Lean; x64 under qemu, arm64 natively; refusals checked; also run with register allocation off and with slot locations only | native execution of `compile` and of the models, as a whole |
| Its self-test | seeded bugs in a pass's output, among them references to a copy of the lender, slot bugs, bugs in the translation of `do` blocks, selection bugs and register-selector bugs | that the suite has teeth |
| Aliasing, I/O and cost harnesses | the caller reads a lender back after a borrow; a buffer program is fed short reads through pipes; passing a reference must cost the same for any size | that writes reach the lender, `read` under short reads, that references are pointers |
| Core passes, `scripts/opt-compare.sh` | a sample of programs compiled with the passes on and off, both targets | that the passes keep behaviour |
| Co-simulation and encoding, `scripts/cosim.sh`, `scripts/a64-cosim.sh`, `scripts/x64-encode-check.sh`, `scripts/a64-encode-check.sh` | random instruction sequences run and the machine state compared with the model; instructions against independent assemblers and disassemblers | each ISA model and encoder |
| ELF and loader checks, `scripts/elf-check.sh`, `scripts/a64-elf-check.sh`, `scripts/loader-a64.sh` | good and corrupted files against the loader model and system tools; arm64's initial state against the kernel's | the loader models |
| Other formats, `scripts/pe-check.sh`, `scripts/macho-check.sh`, `scripts/elfrel-check.sh` | good and corrupted files against system tools and independent readers; runs under wine, links by GNU ld and ld.lld | the writers and reader models of Section 19 |
| Bound check, `scripts/bound-check.sh` | registered programs run under qemu on both ISAs, instructions and stack against the proved bounds | that the bounds hold, and how loose they are |
| Format check, `scripts/format-check.sh` | `kvsrv` on generated request sequences against an independent reference | the formats and the server |
| Layout check, `scripts/layout-check.sh` | Lean layouts against gcc | C-compatible layout |
| Driver check, `scripts/mpc-check.sh` | every registered program compiled for each target and run; output, exit status and ledger checked | the whole system |
| Model runs, `Tests/Top.lean` | programs compiled and run in both targets' Lean models; trace, instructions within `κ`, stack within `φ` | the definitions the theorems are about |
| Rejection tests, `#guard_msgs` in `Tests/` | each checker's errors next to accepted variants; forged, dropped or doubly freed keys | that the checkers reject what they should |
| Ledger test, `Tests/Ledger.lean` | each target's ledger names evidence that exists | the ledger |

### 24.2 Planned

The tests of Section 3.2, and a configuration for continuous integration.

## 25. Later phases

The [roadmap](../roadmap.md) gives the exit criteria of each phase.

Phases 4b, 5 and 6 are partly built, as the Planned parts above describe. Phase 5 still has to add
C externs, the macOS and Windows targets and platform bindings. Phase 6 has proved that the key-value
server refines an abstract store, and still has to derive code from format descriptions, add
information-flow labels with noninterference, and give machines a general type with one refinement
theorem. Phase 7, global types among several processes projected to each role, is not started.

## 26. Limitations of the system as a whole

The theorem covers every program that `compile` accepts, with no hypothesis beyond `Safe`. What it
does not say, such as what a program should do and how close the bounds are, is collected in
[limits.md](../design/limits.md). What `compile` refuses, and what the language lacks, is listed in
[open-claims.md](../open-claims.md). Safety is the user's proof, and `compile` called directly does
not check it, so the theorem then says nothing. The models are tested against qemu, the host CPU
and standard tools, and speculative execution, hardware faults, kernel bugs and time in seconds are
outside them.

Some limits of the language are permanent. There is no heap, no recursion, no unbounded loop but
the reactor, no reference that is stored or returned, no closure, no global variable and no
undefined behaviour, and execution is sequential. These limits make the source total and
deterministic, the stack bound static, and forward simulation sufficient. Other limits are those
of the current code: arithmetic is on words and bytes, the three externs take byte buffers, the
targets are two Linux ones, and brands are per type of arena rather than per arena.
