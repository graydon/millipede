# What the project is

Millipede is an experiment and a proof of concept in the design of low-level programming
languages. It consists of a small language embedded in Lean 4, a compiler from that language to
static x64 and arm64 Linux executables, and a proof in Lean that the compiler is correct.

## Motivation and hypotheses

Automated tools driven by language models may come to find most of the bugs that a program ships
with, which makes it worth having languages that rule out whole classes of bugs before a program
runs. Language models may also do much of the routine work of writing proofs, which would make
verified compilers and proved programs cheaper to build than they have been. The experiment
tests three hypotheses that follow from these two observations:

1. A highly restricted language can eliminate classes of bugs statically, while still expressing
   useful programs.
2. A verified implementation can ensure that a program is compiled as written, down to the bytes
   of the executable.
3. Embedding the language in a proof assistant makes proofs of the functional correctness of
   programs practical.

A second question runs through all three, which is how much of the work an LLM implementor can
do. The code, proofs, tests and documents were written by LLM agents under one person's
direction, in about five days of wall-clock time and about 50 US dollars of usage credits.

## A restricted language

A Millipede program has no heap, no recursion, no unbounded loop other than the reactor's, no
stored references, no closures, no global variables, no exceptions, no undefined behaviour, no
implicit conversions and no dynamic code, and it is sequential. A value of a linear type, such as
an arena key or a `Result`, is used exactly once, and a borrow checker governs references. A
partial operation, such as an array index or an addition that must not overflow, carries an
obligation, a side condition that is proved when the function is defined, and the driver compiles
only a program whose obligations are proved. [language.md](language.md),
[memory.md](memory.md) and [obligations.md](obligations.md) describe these rules.

The design sorts each class of error into one of three kinds: ruled out by the construction of the
language, excluded by a theorem, or named as an assumption in the assumption ledger, a text file
that the compiler driver writes next to each compiled image. The table lists the classes that the
built system handles in the first two ways.

| class of error | how it is excluded | kind |
|---|---|---|
| memory errors: out-of-bounds access, use after free, double free, uninitialised read, type confusion | no heap; linear values and the borrow checker; index obligations; the memory refinement of the compiler; the machine never gets stuck | construction and theorem |
| a jump to an unintended address | follows from the above; code is never writable; the only indirect branch is `ret`; no dynamic loading | theorem |
| running out of time, stack or memory | bounds per reactor step that hold for every input; arenas whose exhaustion is handled or proved impossible | theorem |
| integer overflow and bad indices | wrapping arithmetic with defined results, operators whose overflow is an obligation, and index obligations | construction and theorem |
| unit confusion | quantities tagged with units, checked by Lean | construction |
| ambient authority | no global variables, so a program's state is its root; a theorem, for each program, that it makes no extern call of a class outside its grant; capability tokens that show each function's authority in its signature | construction and theorem |
| data races | programs are sequential | construction |

The restrictions do not remove errors of logic. A program can compute the wrong answer within its
bounds, wrap around where a check was meant, ignore a short write, or leak a secret through its
timing, and a specification that says the wrong thing is caught only by a reader. The price of the
restrictions is the class of programs: filters, decoders of framed input and state machines over a
fixed amount of memory can be written, and a program that needs a heap, threads, files or the
network cannot.

## A verified implementation

The compiler is an ordinary Lean function from a program and a target to the bytes of an ELF
file, and no other compiler, assembler, linker or runtime library sits between the source and the
file. `compile_sound` and `compile_sound_arm64` prove, without hypotheses, that the bytes of a
program whose obligations are proved load under the loader model and, on the model of the
processor, never get stuck, make exactly the source's system calls, keep the stack within a bound
and run each reactor step within an instruction bound. [trust.md](trust.md) quotes the statement.

The statement is about an oracle, a function that supplies every input byte and every answer the
environment gives, and it holds for every oracle. Memory safety, the integrity of control flow and
the resource bounds are consequences of it, so they assume nothing about the input. The theorem
rests on a trusted base, which is the models of the two instruction sets, of the Linux system
calls and of the ELF loader, Lean's kernel, and Lean's compiler, which runs `compile`. Tests compare
each model with qemu, GNU and LLVM tools, and the host's arm64 processor and kernel. No page of
an image is both writable and executable, which the proof uses and the Linux kernel also enforces,
so an error in an instruction-set model cannot make the code change. The images import nothing.

The ledger names the program, the system calls it makes, the trusted models with the evidence
for each, the theorem that covers the bytes, and the stack and instruction bounds. The compiler
favours code that is simple to prove over code that is small or fast. On a small filter its code
is 7 to 12 times the size of the code of `gcc -O2`, and on arm64 it executes 5.6 times as many
instructions.

## Proofs of programs

Each function written with `mp def` is also an ordinary Lean function, so a proof about a program
is a Lean proof about that function. A function states its contract with `requires` and
`ensures`. When the function is defined, `mp def` tries to prove its obligations and its contract
with a verified interval analysis and Lean's tactics, and the programmer proves what is left with
`mp prove`. A program states an invariant over the reactor's steps, which is proved once for
`init` and once for `step`. [obligations.md](obligations.md) and [embedding.md](embedding.md)
describe these.

The compiler theorem says that the machine does what the source does, and a separate theorem
about the source's trace says what that is. Three programs have one, each proved for every oracle
and carried to the compiled bytes: `hello` writes its greeting and exits, `revchunks` writes each
chunk it reads back reversed, and a key-value server answers each request as an abstract
key-value store would and stops at the first malformed request. The other example programs have
no specification of their trace. A contract may state the events that a call appends, and the
trace of `revchunks` follows from such a contract of its step.

## What the experiment does not claim

[limits.md](limits.md) states what the correctness theorem does not cover. The project makes no
claim that Millipede programs withstand attack in general, because the theorems say only that
compiled code behaves as its source does under the trusted models, and what a few programs do.
It makes no claim that the language is practical for real software today, because the class of programs is
small, the generated code is large and slow, and only three programs have a specification of
their behaviour.

## Non-goals

The project leaves these out:

- an optimising compiler beyond a few proved passes, debug information or unwind tables;
- threads or shared-memory concurrency;
- a heap, garbage collection, reference counting, stored references or first-class closures;
- floating point, SIMD, 32-bit targets or big-endian targets;
- changes to Lean's kernel. The project uses only Lean's core library and Std, without Mathlib.

## Planned

The design includes further features that are not built. Information-flow labels with a
noninterference theorem, and a constant-time mode, would control what a program reveals about
secret data. Parsers and writers are written by hand against a format description and proved
to agree with it, and a command would derive them from the description with their proofs. The
key-value server's refinement of an abstract store is proved for that one program, and a general
type of protocol machines, with a refinement theorem proved once for all of them, is planned.
The design also calls for a list of allowed system calls derived from a program's externs, and
for an exercise in which agents given the ledger, the models and the binaries try to produce
behaviour that the theorem forbids. See [world.md](world.md),
[protocols.md](protocols.md), [security.md](security.md) and [../roadmap.md](../roadmap.md).
