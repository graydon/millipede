# The compiler

Millipede's compiler turns a program into an executable file for x64 Linux or arm64 Linux. It
is a Lean function, `compile p t`, which either returns the bytes of the file or refuses the
program with a message. This document describes the stages of the compiler in the order they
run, what each stage is proved to do, and how those proofs combine into the correctness theorem
stated in [trust.md](trust.md).

The compiler sees only closed, first-order terms. Generic code, modules and size parameters are
written in Lean and are applied before the compiler runs, so no stage of the compiler deals with
a type variable, a module or a function value.

## The pipeline

A program passes through the following stages:

```
Program ──checks──▶ Program ──Core passes──▶ Program ──lower──▶ Flat ──linearize──▶ Lin
   ──allocate──▶ Lin ──select──▶ Asm ──budget check──▶ Asm ──assemble──▶ Obj ──link──▶ Image
   ──write──▶ bytes ──load──▶ machine state ──run──▶ events
```

The stages up to `write` are the compiler. The last two, loading and running, are models of
what Linux and the processor do with the file, and they are where the correctness theorem makes
its claims. Every stage that can fail returns an error, and `compile` stops at the first error,
so it never returns bytes that the proofs do not cover.

The stages after `lower` are grouped as a backend, one per target, so that the two targets
share everything before it. The backends of x64 Linux and arm64 Linux differ in the machine
registers that register allocation may use, in instruction selection, the budget check, the
assembler and the linker settings.

## Representations and passes

A program takes the following forms on its way from the source to the linked image. Each form
from Flat down has its own semantics, which the proof of each pass relates to the one above.

| representation | what it holds |
|---|---|
| Core (`Exp`) | typed terms with places, references and obligations; the source |
| Flat | untyped 64-bit words in numbered frame slots, byte-addressed memory, structured control |
| Lin | Flat with labels and jumps, and with numbered functions called by index |
| Asm | the instructions of one target, with symbolic labels and symbol references |
| Obj | sections of bytes, symbols and relocations, independent of the file format |
| Image | loadable segments with addresses and permissions, an entry point and a stack size |

The checks come first. The compiler runs the borrow checker on the program, and it checks that
every field accessor, constructor and variant test of a structure or enum carries a certificate,
a proof that its Lean functions agree with the data layout. A program that fails either check is
refused. The Core optimisation passes
then rewrite the program, as described below.

`lower` translates Core to Flat. It lays out every value in byte memory according to its type,
turns references into pointers, compiles a `match` into a test of the tag, and erases ghost data
and proofs. A small value that is never borrowed is kept in frame slots instead of memory. The
root lives in static storage, and each reactor step runs on it in place. A constructor of at
least 64 bytes that fills an array with a literal, such as `Vector.replicate n 0`, or that takes
a large variable from memory, is written by a loop of 8-byte stores or copies rather than by one
store per word. Each iteration of such a loop charges the tick `words`, and the constructor's own
tick charges the rest of its cost, so the clock still equals Core's step count. `lower` refuses the
constructs it cannot lower, each with a message naming the construct.

`linearize` translates Flat to Lin. Structured control becomes labels and jumps, and the code of
each call becomes a separate function with a fixed frame size. A callee always has a smaller
index than its caller, so a Lin program has no recursion, and its stack depth has a static bound.

Register allocation rewrites a Lin program into another Lin program in which each frame slot is
replaced by a location. The first `k` locations of each frame are machine registers and the rest
are frame slots. An allocator proposes the rewrite, and a checker validates it one instruction at
a time; when the checker refuses, the program is left unchanged. Only the checker is proved, so
the allocator can be ordinary code. Of the register locations, the first `k` are in registers a
call preserves and the next `c` in registers a call destroys (caller-saved); the allocator gives a
caller-saved register only to a value live across no call, and the selector refuses a program in
which a caller-saved location is live after a call that does not define it (`Live.clobOk`). The
allocator first tries, for a value, the register in which its next use or its definition needs
it: the result register of a `ret` or a call, or the argument register of a system call. `k` is 6
on both targets and `c` is 6 on x64 and 14 on arm64 by default (`Compile.Options.regs`, `cregs`);
the option `mpc --no-regalloc` turns the pass off. Before it, `RegAlloc.idOps` rewrites an
operation by a right identity (`bor` by 0, `mul` by 1, …) to a move, which steps exactly alike
(`step_idOps`, `Lock.pre`), so the lowering's `bor x, x, 0` and `mul i, i, 1` select to no code.

`select` translates Lin to Asm. Each Lin instruction becomes a fixed block of machine
instructions. An operand in a register location is used in place, and any other operand is
loaded into a scratch register. If the selector refuses a program with caller-saved locations, it
selects it again with preserved ones only, and then with slot locations only. A load or store of the
data region takes its address code and access form from the ISA (`Sel.Ops.memX`): on x64 the
region's address once by `lea r11, [rip + mp_mem]` and the access `[r11 + a + off]`, with the
Lin address's register as the index and the offset as the displacement, and an immediate stored
or used as an ALU operand directly when it is a sign-extended 32-bit value (`Sel.Ops.stI`,
`Sel.Ops.binI`); on arm64 the address kept in `x29`, which every entry sets, with the Lin
address plus offset as the index (`Options.memBase`; off, every access computes its full address
into a scratch register). The proof carries the base register as an invariant of the relation
(`Conv.regOk` in `MatchAt`), kept by every straight-line instruction (`StraightC`).

The budget check counts the machine instructions that the selected code can execute in each
reactor step and compares them with the cost model of the target. A program whose code would
need more instructions than the cost model allows is refused. The check is described under cost
and stack bounds below.

`assemble` encodes the instructions into a `.text` section and the constant data into a
`.rodata` section, and records the static data region as a `.bss` section. It resolves the jumps
inside a function itself and leaves a relocation for every reference to another function or to
data. `link` places the sections at addresses, resolves the symbols, applies the relocations, and
sets the entry point and the stack size. `write` serialises the image as a static ELF file.

## Proof method

Each representation from Flat down to the machine is given a semantics of one shape, `Sem`. A
`Sem` is a deterministic state machine whose step function takes the oracle as an argument, and
each of its states records the events observed so far and a counter of the work done. A machine
that has called `exit` steps to itself, so a run is infinite unless it gets stuck.

Correctness of a pass is a forward simulation. Every step of the source is matched by zero or
more steps of the target, with a relation between their states preserved, and a decreasing
measure ensures that the target cannot match infinitely many source steps with no steps of its
own. Forward simulations compose, and a forward simulation of a source that never gets stuck
yields a target that never gets stuck and has the same trace. Every semantics here is
deterministic, so the matched run is the target's only run, and no backward simulation is
needed.

Each simulation also relates the work counters, which is how the instruction bound reaches the
machine. Flat and Lin count work in ticks, one per Core construct, weighted by the cost model, so
the Flat counter equals the step count of Core's instrumented semantics exactly. Lin and the
register-allocated Lin run in lock-step, with equal counters at every step.

The proof of each stage is as follows:

- The Core passes preserve the meaning and the safety of the program and never raise its cost or
  stack bound. The relation between the optimised and the source program carries all four
  clauses of the theorem back to the source.
- `lower` is proved by a memory refinement: the Flat run of a lowered term produces the same
  world as Core, advances the counter by exactly Core's steps, leaves the bytes of the result at
  its destination, and leaves untouched every byte the term may not write. The borrow checker's
  guarantees make pointers safe here. While a mutable borrow is live, the bytes of the lender's
  storage may differ from the lender's value in the source, and the checker ensures that nothing
  uses the lender until the borrow ends.
- `linearize` is a forward simulation in which Flat and Lin states have equal frames, memory,
  worlds and counters.
- An allocation that the checker accepts runs in lock-step with the program it came from.
- The same checker validates the live sets of the allocated program: run on the program against
  itself, with each position's map pairing every live location with itself, it accepts exactly
  when the sets are consistent with the code. The accepted check gives a lock-step simulation of
  the program by itself whose states need to agree only on live locations (`RegAlloc.Live.flex`).
  Selection relates the machine to some state related to the Lin state in this way, so a register
  whose value is dead may hold anything.
- `select` is proved once for every instruction set. Each target supplies the relation between
  a Lin state and a machine state and proves that each Lin step is matched by the instructions of
  its block, and the shared proof turns that into a simulation of the whole program.
- The assembler, the linker and the ELF writer are proved by laws rather than simulations.
  Decoding the linked text at a function's address yields that function's instructions, and the
  loader model reads the written file back to the image's initial state.

These pieces are put together once for every backend. A backend proves its laws, which are the
ELF round trip and the simulation, start state and budget of its selected code, and the shared
composition gives the full statement for that backend's target.

## Core optimisation passes

Four passes rewrite Core terms before lowering. They run in a fixed order, and the list is
repeated for two rounds so that a later pass can use what an earlier one exposed.

- `inline` replaces a call by the callee's body, with the arguments substituted, when the callee
  uses its parameters only as plain values and never as places, and when the result needs no
  more frame slots than the call.
- `fold` replaces a `let` of a constant by the constant in the rest of the term, and replaces an
  `if`, `match` or `case` on a literal by the branch it takes.
- `dce` drops a `let` whose variable is unused and whose bound term has no effect, meaning no
  extern call, no write and nothing linear.
- `strength` replaces unsigned division and remainder by a power of two with a shift and a mask.

Each pass is proved to keep the meaning of every term for every oracle, and to keep every
obligation of the result implied by those of the input. The cost and stack bounds are not proved
per pass. Instead, each pass's result is kept only when its bounds are no larger than its
input's, and is discarded otherwise.

The compiler applies the same checks to the optimised program as to the source. If the optimised
program is refused, the compiler tries again with fewer passes, down to none, so an optimisation
never makes an accepted program refused. The test suites turn this fallback off and require that
every program compiles with every pass. The main gain is compile-time evaluation of calls whose
arguments are literals, and the gains are measured in [../measurements.md](../measurements.md).

## Cost and stack bounds

The cost model `κ` of a target gives a number of instructions for each kind of Core construct.
The source program's bound for a reactor step is computed from the syntax of `init` or `step`.
A conditional costs as much as its more expensive branch, and a loop costs its full number of
iterations. The model is described in [resources.md](resources.md).

The budget check ensures that the machine code stays within this bound. It takes a
potential, a number for each code position that says how many instructions may still run from
there before later ticks pay for them. The check confirms, one Lin instruction at a time, that
each step pays for its machine instructions out of the potential and the weight of its tick. The
compiler computes the potential with an untrusted fixed-point iteration, then checks it, and
refuses the program if the check fails. A proof shows that a potential that passes the check
bounds the instructions of every reactor step by that step's share of the source bound.

The stack bound needs no check. The frame model `φ` of a target gives the bytes of stack that a
call with a given number of frame slots occupies. A theorem shows, for every frame model, that
the static stack bound of the Lin program is at most the source bound `p.stackBytes φ`. The
linker asks for exactly the Lin bound as the stack size, which the ELF writer records in the
file. `compile_stack_tight` shows that the machine stays within that size, the bound of the
selected program after register allocation, which is at most the source bound.

## The shape of the generated code

The compiler emits position-independent code only. Every reference from code to code or to data
is relative to the program counter, so a linked image needs no relocation when it is loaded, and
the loader models stay simple.

Internal calls use a convention of Millipede's own, which is described with each target in
[targets.md](targets.md). The registers that hold register locations are saved by the caller
into the callee's frame and restored by the callee's return, so frames do not grow when
registers are used. A caller saves only the registers that are live after the call, that belong
to a deeper activation, or that it reads back as arguments (`RegAlloc.Live.callKeep`), and it
writes only the callee's locations that are live at the callee's entry. A move of a location to
itself is selected as no instructions. On arm64 an addition or subtraction of an immediate below
4096 uses the immediate form of `add`/`sub`, and a zero is stored from `xzr`; the shared
selection layer takes such immediate forms where an ISA has them (the fields `binI` and `stI` of
`Sel.Ops`). No location is placed in a register that a call or a system call destroys, because
giving such registers to values that are not live across a call saved less than half a percent
of the instructions in measurement (decision 30).

Every value that is not kept in frame slots or registers lives in byte memory, and a structure is
never split into separate fields. An operation on a value in memory loads it into a scratch
register, computes, and stores the result back.

## Planned

The following optimisations are designed but not built: constant propagation and check
elimination driven by the verified analyser, common-subexpression elimination, keeping more
values out of memory, and better instruction selection. Constant propagation is blocked because
the analyser's soundness needs a property of loops that the compiler cannot decide. Loop
transformations, vectorisation and profile-guided optimisation are not planned. See
[../open-claims.md](../open-claims.md) and [../roadmap.md](../roadmap.md).

## Where this lives

| item | location |
|---|---|
| `compile`, `compileWith`, `Backend`, the two backends | Millipede/Top/Compile.lean |
| composition, `compile_sound_of_backend`, `Backend.Laws` | Millipede/Top/Sound.lean |
| `Sem`, `FwdSim`, `TraceEq` | Millipede/Compile/Sem.lean |
| Core passes, `Opt.Pass`, `Program.Sim` | Millipede/Opt/ |
| `lower` and `Flat.lowerM_sound` | Millipede/Compile/Lower.lean, LowerSound.lean |
| the loops of large constructors, `Flat.tickLoop_msim` | Millipede/Compile/LowerFill.lean |
| `linearize` and `Lin.linearize_sound` | Millipede/Compile/Linearize.lean, LinearizeProof.lean |
| stack bound, `Lin.lower_linearize_stackBytes_le` | Millipede/Compile/LowerStack.lean |
| register allocation, `RegAlloc.lockOfCheck` | Millipede/RegAlloc/ |
| selection skeleton, `Sel.select_lower_sound`, budget check | Millipede/Target/SelSim.lean, Budget.lean |
| assembler, linker, ELF | Millipede/Compile/Assemble.lean, Millipede/Object/ |
