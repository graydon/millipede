# What the theorem does not say

This document states in one place what the correctness theorem quoted in [trust.md](trust.md)
does not cover, so that a reader can tell what a compiled Millipede program is known to do and
what is only tested or not claimed at all. Each section names the evidence behind its figures.

## The programs it covers

A program is a reactor, which runs `init` once and then `step` until it calls `exit`. Its values
are `UInt64` words, `UInt8` bytes and `Bool`s, and structures, enums and fixed-size arrays of
them, including the arenas of the library. Every loop has a bound known before the program runs,
which is a literal, a constant, the length of a slice or a combination of these, or such a bound
capping a run-time value. No function calls itself, directly or through another, and nothing is
allocated while the program runs. The program reaches the world only through the Linux system
calls `read`, `write` and `exit`, so it cannot open files, use the network, read the clock or
call C. Programs outside this class cannot be written, and the theorem says nothing about them.

## Correctness is refinement of the source trace

The theorem says that the machine makes the same system calls as the source program, with the
same data and in the same order. It does not say what the source program should do. That is a
separate theorem about `p.events`, the source trace, and only such a theorem tells a reader what
the bytes do. Because the traces are equal, a property of the source trace proved for every
oracle holds of every run of the compiled code. The following properties of source traces are
proved today.

| program | property | theorem |
|---|---|---|
| any program declared with `mp program` | no system call of a class outside its grant | `p.noCalls`, carried to the machine by `Program.NoCalls.machine` |
| `hello` of Tests/Core.lean | the trace is exactly one `write` and one `exit` | `Tests.Core.hello_events` |
| `hello` of the registry | for every oracle the trace is one `write` of the greeting and `exit 0` | `Examples.hello_events` from the contract `helloInit.spec`, carried to the bytes by `hello_behaviour` |
| `revchunks` of the registry | for every oracle the trace is rounds of a read and a write of the bytes read, reversed, ending in an exit | `Examples.revProg_events` from the contract `revStep.spec` through `revProg.events_reach`, `Examples.spec_rounds`, carried to the bytes by `revProg_behaviour` and `revProg_rounds` |
| `kvsrv` of Tests/FormatKVSrv.lean | for every oracle the trace is the reads, a write of each response of an abstract key-value store to the requests read, and `exit 0`, or `exit 1` at the first malformed request | `Tests.KV.kvsrv_events` against `kvTrace` (Tests/KVSpec.lean), from the contract `srvStep.spec` through `kvsrv.events_reach`, carried to the bytes by `kvsrv_behaviour`, `kvsrv_answers` and `kvsrv_put_get` |
| `batchEcho` of Tests/FormatGenProg.lean | each batch is checked, read and written by generated functions whose contracts against `batchFmt` are proved; that the trace writes the canonical bytes of each batch is checked by running, not proved | `batchEcho.safe`; scripts/format-check.sh |
| the other registered programs | their traces | not specified |

A contract may also state the events that a call appends, as [obligations.md](obligations.md)
describes. The three traces above that are specified for every oracle follow from such contracts
and not from the bodies of the functions: the contracts of `helloInit` and `revStep` are proved by
the automatic attempt, and the trace theorems cite them. The contracts of `fill` and `srvStep`,
the read and the step of `kvsrv`, are proved by hand with `mp prove`, from the contracts of the
functions they call (`handle` among them, a value contract over `Fmt.parse` and `Fmt.write`).
Still by hand: the induction over the steps that compares the states the contracts allow with the
specification (`revProg_reach`, `kvsrv_reach`), and, for `kvsrv`, the root invariant's step
(`kvsrv.inv_step`), which needs the body because a contract about events says nothing of a run
after `exit`. The contracts of library functions such as `Slice.reverse` and the arenas specify
values, and reach a trace through the contract of a function that calls them.

## Acceptance by `compile`

The theorem holds for every program that `compile` accepts. That `compile` accepts a particular
program is shown by running it as compiled code, in `#guard`s of Tests/Top.lean and by `mpc`, and
the per-program corollaries keep `compile p t = .ok b` as a hypothesis. Lean's kernel has
evaluated the compiler with its default options on two programs, `exit42` and `hello`, on both
targets, which gives `Examples.exit42_runs` and `Examples.hello_runs` without that hypothesis.
For larger programs, `revchunks` among them, the instruction-budget check is too slow in the
kernel.

`compile` itself does not require a proof of the program's obligations, and called directly it
compiles a program whose obligations are unproved. The theorem has the premise `p.Safe`, and the
driver `mpc` and the command `#mp_compile` accept only a program that carries a proof of it.

## What a `write` event records

A `write` event records the bytes the program asked to write and the result the kernel returned.
Linux may write fewer bytes than asked, and the result says how many. A program that ignores the
result, as `hello`, `revchunks` and `kvsrv` do, can lose output on a short write while the theorem still
holds, because the trace records the request. The oracle may return any result, so the theorem
covers short writes and failed reads, but no test makes Linux return a short write.

## How loose the bounds are

The instruction bound of a reactor step is a worst case computed from the source. It charges each
Core construct a weight of the target's cost model, each copy a weight per word copied, each branch
its more expensive arm and each loop its largest iteration count. Values that the compiled code
passes by address or writes in place are not charged as copies: a conditional's result, a borrow's
result, and the `&mut` parameters, borrowed values and loop-carried variables that a body hands
back. Each weight is the most instructions of its construct's selected code in any allocation
setting ([resources.md](resources.md)). Measured under qemu, the step bounds of the registered
programs are 1.7 to 8.6 times the largest step they run, and for two larger programs, the audit's
`upper` and the key-value server of Tests/FormatKVSrv.lean, 11 to 17 times. The reasons are each
loop charged at its full count (`upper`'s write loop 64 times, run once), each branch at its dearer
arm, a byte array charged one word per byte, a copied word charged as one iteration of the fill or
copy loop (32 instructions on x64, against 14 for a straight copy), and each weight at its
construct's worst case: a primitive is charged as if both operands were read through references with
allocation off, 32 instructions on x64, while with registers it takes 4. The tables are in
[../measurements.md](../measurements.md), "Bounds against measured runs".

There are two stack bounds. The clause of `compile_sound` is `p.stackBytes`, computed from the
source, which charges every value of every frame a stack slot, while the compiled code keeps
values in its data region and in registers; it is 2 to 50 times the stack used by the registered
programs and 160 to 1,340 times for the two larger ones. `compile_stack_tight` and
`compile_stack_tight_arm64` (Millipede/Top/StackTight.lean) bound the stack by the size the image
asks the kernel for, which the compiler computes from the selected code after register
allocation; it is at most `p.stackBytes`, and measured it is 1.0 to 1.5 times the stack used.

`compile` checks the instruction budget of each program and refuses one whose selected code
exceeds it, and the proof of the instruction clause uses that check. The weights of `X64.κ` and
`A64.κ` are counts of each target's selected code, with a margin of 10% on those taken from the
test programs; scripts/kappa.lean checks that no test program is refused.
scripts/bound-check.sh compares the bounds of registered programs with runs under qemu-x86_64 and
qemu-aarch64, which execute the bytes independently of the Lean models.

## The stack limit of the process

The loader model gives the process a stack of the size the image requests, at most 4 MiB. ELF
cannot reserve stack, and Linux grows it on demand up to `RLIMIT_STACK`, which is 8 MiB by
default. The theorem therefore assumes that the process can grow its stack to the size the image
requests, which holds for every image when `RLIMIT_STACK` is at least 4 MiB and the space of the
arguments and environment. A process started with a smaller limit may be killed when its stack
grows, which the theorem does not cover.

## Tests of the trusted models

The models of the two instruction sets, of the system calls and of the loaders are trusted, and
tests compare them with the real thing. scripts/cosim.sh runs random instruction sequences under
qemu-x86_64, which is itself a model of x64, since the host is arm64. The sequences use every
addressing form that the selector emits and a new seed on each run, and seeded bugs in the
encoder and in the model's flags, shift counts and division must each be caught.
scripts/a64-cosim.sh runs random sequences on the host's arm64 processor, including `read`,
`write` and `exit` system calls on pipes. The system-call models are also exercised by every
compiled test program, under qemu for x64 and natively for arm64, but Linux was never made to
return a short write or `EINTR` to them.

A system linker that links Millipede's relocatable objects is trusted, and no theorem covers a
program it links. The theorem speaks of the executable that Millipede's own linker makes from the
same object. scripts/elfrel-check.sh links the objects of three programs with GNU ld and ld.lld
and compares the programs' runs with those of Millipede's executables, which is evidence about
those three programs and those linkers.

The differential suites compile 170 test functions for both targets and compare 115,587 results
with independent references. They test Lean's compiler, which runs `compile`, and the models
together, and a passing run is evidence about those, not a proof. The test functions are
compiled with their obligations unproved, so they lie outside the theorem's premise, which a test
of the models allows because the same models run either way.

## Capability tokens

For the capability classes a program does not hold, `mp program` proves `p.noCalls`, which says
that no run calls a symbol of those classes. The proof uses only the extern symbols that the
program's terms mention, so the theorem would hold of the same program written without tokens.
Tokens make the authority of each function visible in its signature and checked as the function
is defined. A class is a set of symbols, so it cannot tell one file descriptor from another. The
states of a handle, such as a log that must be synced before it is closed, are enforced by the
checker and tested, and no theorem states them.

## Code size and speed

The compiler favours code that is simple to prove over code that is small or fast. Against
`gcc -O2` on the audit's filter `upper`, its code is 1.9 KB on x64 and 1.1 KB on arm64 against
gcc's 0.24 KB, and it executes 4.5 (x64) and 3.5 (arm64) times as many instructions, 43 and 34
per byte against gcc's 9.5. The loop's condition, `i < 64 && i < len`, materialises each
comparison as 0 or 1 and tests it again where the two branches join, which a fused
compare-and-branch would not remove. A load or
store of the data region is two instructions on x64, which compute the region's address once
per access (`lea r11, [rip + mp_mem]`, then `[r11 + a + off]` with the Lin address as the index),
and one or two on arm64, which keeps the address in `x29` for the whole run. A constructor of 64 bytes or more that fills an
array with a literal, or takes a large variable from memory, is written by a loop, so the variant
of the filter with a 64 KiB buffer has almost the same code as the 64-byte one (2.9 against
2.8 KB on x64) instead of 3.3 MB. Images pad each segment to a page in the file: arm64 files are
128 or 192 KiB whatever their code, because the loader model takes 64 KiB pages, and x64 files
are a 4 KiB header page plus the code and data rounded up to 4 KiB pages.
