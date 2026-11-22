# Roadmap

This document lists the work that comes next, phase by phase, with the test that ends each
phase. Every phase also ends with `scripts/check.sh` passing and `#audit` clean. What is built is
recorded in [status.md](status.md), and what is unproved or refused in
[open-claims.md](open-claims.md).

## Finished

- Phases 0 and 1 built the scaffold and a thin path to bytes, with `compile_sound` stated and
  proved.
- Phase 2 added memory, slices, loops through references and one lowering for every program.
- Phase 2f kept small values in frame slots. 
- Phase 3 added contracts, the analyser, units, modules and branded keys.
- Phase 4 added the arm64 target and proved `compile_sound_arm64`.

## Phase 4b: optimisation

Phase 4b adds optimisations that keep the correctness theorem unchanged. Its exit test has three
parts. `compile_sound` keeps its statement and stays unconditional on both targets with every
pass enabled. The instruction counts of the differential suite drop by a measured factor. Each
pass can be turned off, so that the differential tests can compare optimised and unoptimised
binaries.

The Core passes and register allocation with six preserved register locations on each target, and
caller-saved ones (3 on x64, 9 on arm64) for values live across no call, are built,
and their gains are recorded in [measurements.md](measurements.md). The following remain:

- on x64, a store of an immediate (`mov qword/byte [m], imm`), which needs two new instruction
  forms and measures 2.9% fewer static instructions and 5.8% fewer executed (`s:ops6`); the other
  immediate and memory-operand forms measure below 2% and are not planned;
- fusing a comparison with the branch that uses it;
- bit-field instructions for fields smaller than a word;
- constant propagation and check elimination driven by the analyser, which wait until the
  analyser's loop condition can be decided ([open-claims.md](open-claims.md)).

## Phase 5: the world

Phase 5 connects programs to the operating system beyond three system calls. Capability tokens,
typestate on handles, the PE32+ and Mach-O writers with their loader models, and ELF relocatable
objects for both Linux targets are built. What remains is externs in the C calling convention
and imports, exports, the macOS and Windows targets that use those writers, a driver option that
writes relocatable objects, and platform bindings with the portable layer of
[design/world.md](design/world.md).

The exit test is one program, a bounded line filter with a specification, that runs from the
same source on x64 Linux, arm64 Linux, arm64 macOS and x64 Windows. A second test is a
crash-recovery invariant proved for a small log.

## Phase 6: untrusted input and specifications

Phase 6 adds format descriptions with derived validators, parsers and serialisers, and their
theorems. It adds information-flow labels with noninterference, `endorse` through parsing, and a
source-level constant-time mode, all as in [design/security.md](design/security.md). It also
adds machines and refinement of a machine by a program, with one-sided protocol conformance, as
in [design/protocols.md](design/protocols.md) (Reactor refinement).

The exit test is a server for a small binary request and response protocol whose messages are
given as formats. The server is proved to refine an abstract machine, such as a key-value store,
for every behaviour of the peer, bytes read from the input reach a sink labelled trusted only
through parsing, and the cost of each step is bounded.

Format descriptions are built as a model with its theorems, Millipede code for every leaf form,
and a command, `mp format`, that generates the parser, writer and validator of a structure from a
description and proves their contracts against it. The key-value request parser and response
writer are generated this way. A key-value server is proved to refine an abstract key-value store for every behaviour of
the peer: its trace is the reads, a write of the store's response to each request decoded by the
model's parser, and the exit, and this is carried to the compiled bytes (Tests/KVRefine.lean).
That part of the exit test is met. Machines as a general Lean type with a refinement theorem
proved once, and information-flow labels, are not built. What remains for formats is a length-prefixed
nested message, a reader of one field in place, constants and ignored runs longer than eight
bytes, a step bound of generated code in terms of the description, and a theorem about the trace
of a program built on generated code.

## Phase 7: global types and relational proofs

Phase 7 adds global types, their projection onto local machines, and the composition theorem
over a model of pipes, as in [design/protocols.md](design/protocols.md) (Global types). It also
adds product programs for proofs about two runs.

The exit test is a program of two or three separate processes. Each is compiled from its own
source and proved to refine its projection, and their composition is proved to follow the global
type. A second test is one noninterference proof by product program for a function that the
checker rejects.

## Standing rules

When a stage makes earlier code, proofs, tests or documentation redundant, that stage deletes or
merges them before its gate. An old path kept alive next to its replacement needs a reason in
[open-claims.md](open-claims.md), and each phase's review checks for leftovers.

Between phases, a pass trims code and redundancy and profiles build and test times, so that the
quick test tier stays cheap.

## Risks and open questions

The following risks remain:

- Vendors underspecify loaders and system calls. The models therefore cover the narrowest shape
  that works, the world models stay weak, and tests include negative cases.
- Kernel evaluation of `decide` on large terms can be slow, and `native_decide` is not allowed
  anywhere in the library.
- `vcgen` may not yet handle several mutable parameters, oracle state and loop counters together
  well enough.

The following questions are open:

- how global types express recursion and choices that depend on data while projection stays
  useful, and what conditions make asynchronous projection sound;
- how receptiveness and bounded response are stated so that refinements of reactors compose,
  with interface automata as the reference point;
- how expressive format descriptions must be for real protocols before derived code stops being
  competitive with hand-written parsers;
- how amortised bounds and statements that are stable under the environment's changes are
  phrased in `Std.WP`;
- whether `inline` definitions with block parameters are expanded on the surface syntax, which
  is simpler, or on terms, which needs one reusable lemma per definition.
