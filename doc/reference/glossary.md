# Glossary

This glossary defines the terms that the design documents, the guides and the reference use, in
alphabetical order. The forms of the language are described in the [surface reference](surface.md).

**A-normal form.** A form of term in which every operand of an operation is a variable or a
literal, so a compound operand is first bound to a variable of its own.

**accumulator.** The first component of a loop's state. It is a word variable that every path
through the loop body assigns at its end.

**analyser.** A verified interval analysis of Core terms. `mp def` runs it before any tactic, and
when it certifies every obligation of a function, those obligations need no other proof.

**arena.** A library type that holds a varying number of values of one type in a fixed number of
cells. The library's arenas are pools and bump arenas.

**assumption ledger.** A text file written next to each compiled binary. It lists what the
binary's correctness relies on and names the proof of the program's safety.

**atom.** A variable or a literal.

**block.** A sequence of statements written after `do`, whose value is the value of its last
statement.

**block rule.** The rule that a block may not write a variable bound outside it. The value of a
`let`, the body of a borrow and the body of a loop are blocks in this sense.

**borrow.** A reference to a place that lasts for a call or until the end of a block. While an
exclusive borrow is live, the place may be used only through it.

**brand.** What ties an arena key to its arena. A key's type carries the arena's type
parameters, so a key of one arena is a type error at an arena of other parameters.

**bump arena.** An arena whose cells are filled in order and emptied all at once by `reset`.

**bundle.** A Lean structure that collects many hypotheses under named fields, so that a lemma
takes one argument instead of many.

**burden.** The lines of contracts and proofs a program needs, measured against its lines of
code.

**canonical.** Said of a format description in which each value has one encoding, so that the
bytes a parse consumes are the bytes of the value it gives. A description with `skip` is not
canonical.

**capability class.** A named set of extern symbols that a function may call only while it holds
a token of the class. It is declared with `mp capability`.

**certificate.** A proof, stored in a lens, constructor or split, that it agrees with the byte
layout of its type. The compiler refuses a program that uses a building block without one.

**checked form.** The form of a partial operation that tests its condition when the program runs
and returns a `Result`, such as `a[i]?` or `a +? b`.

**clock.** A count of the work done by a run of one of the semantics, in Core steps, ticks of the
intermediate languages or machine instructions.

**contract.** A function's precondition and postcondition together. It is proved once, and
callers use it instead of the function's body.

**contract about events.** A contract whose postcondition names `history`, the events before the
call, `events`, the events the call appends, or `exited`, whether the call ends by `exit`.

**Core.** The small typed language that `mp def` translates a function into and that the
compiler reads. A Core term is a Lean value, so Lean can inspect it.

**cost model.** A table of the cost of each kind of Core operation. The compiler checks that the
selected code of each operation stays within its cost.

**de Bruijn index.** A way of naming a variable by the number of binders between it and its use,
with 0 for the innermost.

**deep embedding.** A language whose programs are Lean data values, which can be inspected and
compiled, rather than Lean functions.

**denotation.** The meaning of a term as a Lean function from an environment and a world to a
value and a world.

**dimension.** A kind of quantity, such as `Size` or `Time`. Units of one dimension can be
converted into each other.

**event.** The record of one extern call, with its arguments, the bytes it read and wrote, and its
result.

**history.** The events of a run before a given point, oldest first. In a contract about events,
`history` is the history before the call.

**extent.** The memory that a slice covers, which is the run of array elements it views.

**extern.** A function implemented outside the program, through which the program reaches the
operating system.

**Flat.** The intermediate language after Core. Its values are untyped words and bytes, and its
control flow is still structured.

**footprint.** A static bound on the memory a program uses outside the stack: the root and the
larger of the values of `init` and `step`.

**format description.** A Lean value of type `Fmt` that says how a value is laid out as bytes,
from which a parser, a writer and a validator get their meaning (`Fmt.parse`, `Fmt.write`,
`Fmt.check`) and their theorems. See [library.md](library.md).

**format of a structure.** A format description written next to a Millipede structure with
`mp format`, naming the field each part fills. The command generates the structure's abstraction
into format values, its parser, writer and validator, and proves their contracts. See
[definitions.md](definitions.md).

**format value.** A value of type `Val`, the values of every format description. A Millipede data
type is related to a description through an abstraction function into `Val`.

**forward simulation.** A proof that every step of one program is matched by zero or more steps
of another, while a relation between their states is kept.

**frame.** The memory that one activation of a function uses for its values and temporaries.

**generic.** A definition written under Lean `variable` binders. It is a single Lean term over
its variables, and its proofs are made once for every value of them.

**ghost.** Data that exists only in the meaning of a program and in proofs. It takes no space
and no code is compiled for it.

**grant.** The tokens that a program's `init` receives, one of each class it takes as a parameter.

**hand back.** What a borrow body or a callee with reference parameters does at its end, when it
returns the final values of its references with its result.

**handle.** A sealed linear value that stands for something outside the program, such as an open
file, and whose type carries the handle's state.

**hole.** The part of a place that a live exclusive borrow may have changed, whose bytes are
therefore not related to the stale value of the lender.

**implementation.** A value of an interface, whose operations are `mp def`s and whose contracts
are proved.

**instance.** A generic definition applied to arguments, such as `Pool UInt64 8 1`. Its theorems
are the generic theorems applied to the same arguments.

**interface.** A Lean structure declared with `mp interface`, whose fields are abstract types, a
model of their values, and operations with contracts.

**invariant.** A property that holds at the start and is kept by every step. A program's
invariant is a property of its root, and a loop's invariant a property of its state.

**key.** The linear value that an arena hands out for a stored value, and the only way to reach
that value.

**lawful.** Said of a lens, constructor or split whose Lean functions agree with the byte layout
of its type.

**lens.** A pair of functions, one reading a part of a value and one replacing it. A lens is
Core's model of a place.

**Lin.** The intermediate language after Flat. Its control flow is labels and jumps, and its
functions are numbered and have frames of fixed size.

**linear.** Said of a type whose values must be used exactly once. `Result` and arena keys are
linear.

**loan.** The checker's record that a place is currently borrowed, shared or exclusive.

**location.** Where register allocation keeps a value of a Lin frame: a machine register or a
frame word.

**loop state.** The tuple of values that a loop carries from one iteration to the next.

**lowering.** The translation from Core to Flat, which places every value in memory or in a
frame slot.

**normal form.** The ordinary Lean function `f` that `mp def` defines. It computes the same result
as the Core term, and proofs about the program are about it.

**obligated form.** The form of a partial operation that performs no test and carries an
obligation instead, such as `a[i]!` or `a +! b`.

**obligation.** A fact that must hold for a partial operation to be defined, such as an index
being in range. The obligations of a function are proved as `f.safe`.

**occupancy.** Which cells of a `Slots` value are full. It is known only to proofs.

**open claim.** A statement defined as a `Prop` but not yet proved. Open claims are listed in
[../open-claims.md](../open-claims.md).

**oracle.** A function that answers every extern call. The theorems hold for every oracle, so
the oracle stands for an environment that may answer anything.

**place.** A part of memory that holds a value: a variable, a field of a place, an element of an
array, a cell of `Slots`, a slice or a pair of elements.

**pool.** An arena whose cells are reused after they are freed. A bitmap records which cells are
full.

**postcondition.** A property of a function's result and of the final values of its references,
written with `ensures`.

**potential.** A credit kept per code position in the proof that the selected code stays within
its instruction budget.

**precondition.** A property of a function's parameters, written with `requires`, which every
caller must establish.

**program.** A root type with the two functions `init` and `step`, declared with `mp program`.

**quantity.** A word tagged with a unit, of type `Q u`. The tag costs nothing at run time.

**reactor.** The shape of every program, which runs `init` once and then `step` again and again
with an exclusive reference to the root.

**reference.** Access to a place without copying it. A shared reference `&p` allows reading, and
an exclusive reference `&mut p` also allows writing.

**refinement.** A proof that a lower-level program produces only behaviours that the
higher-level one allows. In this project, a refinement is a forward simulation.

**register allocation.** The pass that moves the values of a Lin program from frame slots to
locations, some of which are machine registers. A checker validates its result, so the allocator
itself is not proved.

**register location.** A location that instruction selection maps to a machine register rather
than to a frame word.

**relaxed term.** The term `f.expR`, in which the overflow obligations that the analyser
certified are replaced by wrapping operations. The remaining obligations are proved on it.

**root.** The one value of a program that lives from step to step, kept in static storage.

**safe.** Said of a program when every obligation of every function holds on every run, for every
oracle.

**scratch slots.** The 16 frame slots that every activation has besides the slots of its values.

**sealed.** Said of a structure whose Lean constructor is private to its module, so that code
elsewhere can neither build it nor write its fields.

**selection.** The translation from Lin to the instructions of a target's ISA, done by a selector
for each ISA.

**size expression.** An expression whose value is known before the program runs, used as the
upper bound of a loop.

**slice.** A run of consecutive elements of an array, used through a reference.

**slot.** A word of a function's frame.

**slot-resident.** Said of a value that is never addressed and is small enough, a byte or one to
four words, to be kept in frame slots instead of in data memory.

**`Slots T n`.** An array of `n` cells, each of which is empty or holds a value of type `T`.

**stuck.** Said of a run that has no next state, because of a fault or an instruction that cannot
be decoded.

**stuttering.** What a halted program does: it steps to itself, unchanged.

**target.** An ISA model, the model of the operating system on that ISA and an executable format.
The targets are x64 Linux and arm64 Linux.

**token.** A value of size zero, linear and sealed, whose type names a capability class. Holding
one gives a function the authority to call the externs of its class.

**trace.** The list of events of a run so far.

**typestate.** A state of a handle kept in its type, so that the checker rejects an operation
applied in the wrong state at no run-time cost.

**unit.** A scale within a dimension, such as `KiB`, which is 1024 bytes.

**view.** The binder that a slice parameter or a slice borrow creates. At run time it is an
address and a length.

**W^X.** The property that no page of memory is both writable and executable.

**world.** The value that records the extern calls a program has made so far.
