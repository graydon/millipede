# The correctness theorem and what it trusts

Millipede's compiler is proved correct by a theorem about the bytes it writes. This document
states the theorem, explains each of its clauses, and says what the proof assumes. Some parts
of the argument are trusted rather than proved, chiefly the models of the machines and of Linux.
The document lists them and names the test that backs each one.

## The statement

The statement is a Lean proposition about a compiler and a target. It is defined in
Millipede/Top/Statement.lean as follows:

```lean
def CompileSound.Statement (compile : Program → Target → Except String ByteArray)
    (t : Target) : Prop :=
  ∀ (p : Program) (b : ByteArray), compile p t = .ok b → p.Safe →
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run t s₀ ω
        m.NeverStuck ∧
        TraceEq m.trace (p.events ω) ∧
        m.StackWithin (p.stackBytes t.φ) ∧
        m.StepsWithin (p.events ω) (fun k => p.stepCost k ω t.κ)
```

Two theorems prove it for Millipede's compiler `compile`. `Millipede.compile_sound` proves
`CompileSound.Statement compile x64Linux`, and `Millipede.compile_sound_arm64` proves
`CompileSound.Statement compile arm64Linux`. Neither has hypotheses. A third theorem,
`Millipede.compileWith_sound`, proves the statement on both targets for every setting of the
compiler's options, so it also covers code compiled with the optimisation passes or register
allocation turned off.

## Programs, oracles and traces

A Millipede program is a reactor. It has one persistent value, the root, and two parts: `init`,
which runs once and builds the root, and `step`, which then runs forever and updates the root
each time. One run of `init` or of `step` is a reactor step, and the reactor steps are numbered
from 0, which is `init`. A program stops only when it calls `exit`.

A program affects the world only through extern calls, which today are the Linux system calls
`read`, `write` and `exit`. An event is the record of one extern call: its name, its word
arguments, the bytes of the buffers it reads, its result word and the bytes it writes. The trace
of a run is the list of its events in order.

An oracle is a function that answers every extern call, given the events that came before it.
It stands for everything outside the program, such as the operating system and the input. The
statement holds for every oracle, so it covers every answer the environment can give. The oracle
can be read as an adversary that chooses each input byte and each result knowing the events so
far, and the theorem holds whatever it chooses. `p.events ω k` is the trace of program `p` under the oracle `ω` after reactor step
`k`.

## Reading the statement

The statement has two premises. The first, `compile p t = .ok b`, says that the compiler
accepted the program `p` for target `t` and produced the bytes `b`. The compiler refuses some
programs with an error message, and nothing is claimed about a refused program. The second,
`p.Safe`, says that every obligation of the program holds on every run under every oracle. An
obligation is a side condition of a partial operation, such as an array index being in range,
and a program's obligations are proved when the program is defined.

The first conclusion is that the bytes load. The target's loader model `t.fmt.load` reads the
ELF file `b` and produces a machine state `s₀`, which is the state of the process just before its
first instruction runs.

The remaining conclusions are about `Machine.run t s₀ ω`, the run of the target's machine model
from `s₀` with the system calls answered by `ω`. Each step of the run executes one instruction.
After the program calls `exit`, the machine stays in its final state, so every run is infinite
unless it gets stuck. The run has four properties, which hold for every oracle:

- `m.NeverStuck` says that the machine never gets stuck. It never faults, never meets an
  instruction it cannot decode, and never makes a system call that the model does not support.
- `TraceEq m.trace (p.events ω)` says that the machine makes the same extern calls as the
  source program, in the same order and with the same data. Both traces grow as their runs
  proceed and may be infinite, so `TraceEq` compares them as limits: every prefix of one is a
  prefix of the other.
- `m.StackWithin (p.stackBytes t.φ)` says that the stack pointer never goes more than
  `p.stackBytes t.φ` bytes below its initial value. The bound is a number computed from the
  program, and `t.φ` is the target's frame model, which gives the bytes of stack that one call
  occupies.
- `m.StepsWithin …` bounds the instructions of each reactor step. `p.stepCost k ω t.κ` is a
  number computed from the source of reactor step `k`, using the target's cost model `t.κ`,
  which gives the instructions each source construct may take. The clause says that the
  machine run can be cut at a sequence of times, one at the end of each reactor step, so that
  at each cut the machine's trace equals the source trace after that reactor step, and the
  instructions executed between two cuts are within the bound for that step. The compiler
  therefore cannot move an event into another reactor step, and it can move work only within
  the bounds. The bound is a worst case, between 3 and 45 times the instructions that the
  registered programs run.

The source trace `p.events ω` comes from the same meaning of the program that its function
contracts describe. A property of the source trace that is proved for every oracle therefore
also holds of the trace of the compiled code. The properties of source traces proved today are
`p.noCalls`, which `mp program` proves for the capability classes a program does not hold, and
the trace specifications of `hello` and `revchunks`, which `hello_behaviour` and
`revProg_behaviour` (Millipede/Top/Behaviour.lean) state for every oracle and carry to the
bytes, and that of the key-value server `kvsrv`, which `kvsrv_answers` (Tests/KVRefine.lean)
states against an abstract key-value store. [limits.md](limits.md) lists them. These theorems hold for any bytes `b` with
`compile p t = .ok b`. That `compile` accepts a program is shown by running it as compiled code.
Lean's kernel checks it only for `exit42` and `hello` (Millipede/Top/Accept.lean), because for
larger programs the instruction-budget check does not evaluate in the kernel in reasonable time.

## What the proof assumes

`compile_sound` depends on Lean's three standard axioms, propext, Classical.choice and
Quot.sound, and on nothing else. `compile_sound_arm64` depends on them and on the axioms that the
tactic `bv_decide` adds for the lemmas it proves. `bv_decide` is used only for lemmas about
encoding and decoding arm64 instructions, in two modules. No other axiom is used, and no proof in the library is left
unfinished with `sorry`. The command `#audit` checks this over the whole library, and
scripts/audit.sh prints the axioms each headline theorem depends on and fails if any other
appears.

The compiler checks some properties of a program before it compiles it, and refuses the
program when one fails. It runs the borrow checker, and it checks that every field accessor,
constructor and variant test of a structure or enum carries a proof that it agrees with the
data layout. After instruction selection it checks that the selected code fits the instruction
budget of each reactor step. These checks run inside
`compile`, so a program that fails one is refused and the theorem needs no hypothesis about it.

## What is trusted

The theorem is about models. It says what the machine model does with the bytes, starting from
the state the loader model gives, with system calls handled by the system-call model. Each model
is a Lean definition written to match the real thing, and the match is not proved. The
following parts of the argument are trusted:

- the statement itself, which a reader must check says what they want;
- Lean's kernel, which checks every proof;
- for arm64, the lemmas proved by `bv_decide`, whose proofs are checked by code that Lean compiles rather
  than by the kernel alone;
- Lean's compiler and runtime, because the bytes come from running `compile` as compiled code,
  while the theorem is about `compile` as a Lean function;
- the models of the two instruction sets, x64 and arm64, each restricted to the instructions
  Millipede emits;
- the loader models, which say what state a Linux process starts in when it is given an ELF
  file. The model puts the stack at a fixed address, while Linux chooses a random one. Compiled
  code never observes an address, so the difference cannot be seen. The model also gives the
  process the stack the image requests, at most 4 MiB, which Linux grows on demand up to
  `RLIMIT_STACK`, so the theorem assumes a limit of at least 4 MiB and the space of the
  arguments and environment;
- the system-call models, which say where the number and the arguments of a Linux system call
  are found, where the kernel writes the bytes it returns, and which registers it changes.

A system linker that links Millipede's relocatable objects is trusted, and no theorem covers the
program it makes; only tests check that such programs behave like those of Millipede's own
linker.

What the kernel returns from a system call is not trusted, because the oracle may answer any
call with any result and any bytes, and the theorem holds for every oracle.

Everything else is proved. The elaborator that turns `mp def` into a Core term is not trusted,
because every theorem about the program is about the term it produces and is checked by the
kernel. The optimisation passes, the lowering, the register allocation check, instruction
selection, the assembler, the linker and the ELF writer are all covered by the proof. The register allocator itself is not trusted
either, because its proposal is checked and is not used when the check fails.

## Evidence beyond proofs

Each trusted model is backed by tests that compare it with the real thing. Each of the scripts
below except scripts/x64-encode-check.sh is shown to catch seeded bugs, either with a
`--selftest` option or with corrupted inputs. The table names the tests for each trusted part.

| trusted part | x64 | arm64 |
|---|---|---|
| instruction-set model | scripts/cosim.sh runs random instruction sequences, with every addressing form the selector emits, under `qemu-x86_64` and compares the registers, flags and memory with the model | scripts/a64-cosim.sh runs random instruction sequences natively on the host, some with system calls, and compares the registers, flags, memory, faults, output and exit code with the model |
| instruction encodings | scripts/x64-encode-check.sh checks that GNU objdump reads the bytes as the model does | scripts/a64-encode-check.sh checks the bytes against `llvm-mc` and objdump |
| loader model | scripts/elf-check.sh checks files with `readelf`, runs them under `qemu-x86_64`, and checks that corrupted files are refused | scripts/a64-elf-check.sh checks files with `readelf`, `eu-elflint`, ld.lld and GNU ld; scripts/loader-a64.sh compares the model's initial state with the kernel's under gdb |
| PE32+ loader model, which no target uses yet | scripts/pe-check.sh compares files with `llvm-readobj` and with files made by `lld-link`, runs them under wine, and checks that corrupted files are refused; no file has run on Windows, and wine accepts files that Windows refuses | none |
| Mach-O loader model, used by no target yet | none | scripts/macho-check.sh checks files with `llvm-readobj`, `llvm-otool`, `llvm-objdump`, an independent Python checker that recomputes the signature, and ld64.lld, and checks that corrupted files are refused; the three good files ran as expected on an arm64 Mac once, by hand |
| system linker on Millipede's relocatable objects, not modelled | scripts/elfrel-check.sh links three programs with `x86_64-linux-gnu-ld` and ld.lld, runs them under `qemu-x86_64` and compares them with Millipede's own executables; the files are checked with `readelf`, `llvm-readobj`, an independent Python reader and the section flags GNU as gives | the same with GNU ld and ld.lld, run natively; a C object calls into Millipede code and a hand-made object calls a C function on both machines |
| system-call model | scripts/mpc-check.sh and scripts/differential.sh run compiled programs under `qemu-x86_64` | `MP_TARGET=arm64-linux scripts/mpc-check.sh` and scripts/differential-a64.sh run compiled programs natively |
| Lean's compiler | the differential suites compare compiled functions with independent reference implementations | the same suites, compiled for arm64 |

The host is an arm64 Linux machine, so x64 code runs under the emulator `qemu-x86_64` rather
than on x64 hardware. The x64 models are therefore compared with qemu, which is itself a model
of the processor and of Linux. The arm64 models are compared with real hardware and a real
kernel.

One further test runs the whole pipeline. Tests/Top.lean compiles a set of example programs for
both targets, loads the bytes with the loader model, runs the machine model, and checks the
trace, the instruction count and the stack depth against the source. The checkers that refuse
programs have negative tests under `#guard_msgs`, which show each refusal and its message.
scripts/bound-check.sh compares the instruction and stack bounds of two registered programs with
their runs under `qemu-x86_64` and `qemu-aarch64`, which execute the bytes independently of the
models.

Every compiled image comes with an assumption ledger, a text file that `mpc` writes next to the
image as `<file>.ledger.txt`. It names the program and its extern calls, the target and its
models, the theorem that covers the bytes, the stack and instruction bounds as numbers, and the
trusted parts with the evidence for each. Tests/Ledger.lean checks that every script and test
file the ledger names exists, and that the ledger of each target names that target's
co-simulation, encoder check and model run.

## Limits

[limits.md](limits.md) states in one place what the theorem does not say, including the class of
programs it covers, how far the bounds are from measured runs, what the tests of the models reach
and what capability tokens add.

## Planned

The design calls for extern bindings, which let a program call C functions whose behaviour is
described by a model, and for tests that run random call sequences against the real functions.
It also calls for a red-team exercise, in which agents given the ledger, the models and the
binaries try to produce behaviour that the theorem forbids. Neither exists yet.
See [../open-claims.md](../open-claims.md) and [deviations.md](deviations.md).

## Where this lives

| item | location |
|---|---|
| `CompileSound.Statement` | Millipede/Top/Statement.lean |
| `compile_sound`, `compile_sound_of_backend` | Millipede/Top/Sound.lean |
| `compile_sound_arm64`, `compileWith_sound` | Millipede/Top/SoundA64.lean |
| `Machine.run`, `NeverStuck`, `StackWithin`, `StepsWithin` | Millipede/Target/Target.lean |
| `TraceEq` | Millipede/Compile/Sem.lean |
| `Oracle`, `Event` | Millipede/Extern/Oracle.lean |
| `Program`, `Program.Safe`, `Program.stackBytes` | Millipede/Core/Program.lean |
| `#audit` | Millipede/Meta/Audit.lean |
| the ledger | Millipede/Top/Ledger.lean |
