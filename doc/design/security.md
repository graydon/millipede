# Information flow and formats

This document describes two parts of the design. Information-flow labels, which would track
which data is secret and which is untrusted, are a plan. Format descriptions, which describe
binary messages as data, are built in part.

## Information flow

A label marks how secret or how trusted a value is, and a value of type `Sec ℓ T` carries the
label `ℓ`. The labels form a lattice that the user chooses, with confidentiality and integrity
as the standard instance. An operation joins the labels of its operands. Branching on a labelled
value raises the label of everything the branches do, and a write is allowed only to a place
whose label is at least as high. Extern signatures carry labels, which mark the sources and
sinks of data.

A checker on terms enforces these rules. A theorem proved once shows noninterference, which
means that two runs whose inputs and oracles agree on everything visible at level `ℓ` produce
results and events that agree at `ℓ`. Programs always terminate, so the theorem also covers
leaks through termination. A program that the checker rejects can still be proved noninterferent
directly, because its meaning is a Lean function and noninterference is a Lean proposition
about it.

Two primitives let data cross labels on purpose. `declassify` releases a secret and `endorse`
trusts an untrusted value, each naming a policy, and the audit lists every use. A validating
parser is the usual `endorse`.

A constant-time mode also forbids branches, array indices, loop conditions and variable-time
operations that depend on secrets. Its theorem says that the steps and the sequence of memory
accesses of a run do not depend on secrets. At first this is a statement about the source only,
and a proof that the compiler preserves it comes later.

## Format descriptions

Many errors in programs that read untrusted input are in hand-written parsers, or in two parsers
that read one message differently, so a binary message is described as data and its parser and
writer are given by the description. A
format description is a Lean value of the inductive type `Fmt`. It is built from unsigned
integers of a fixed width and byte order, byte strings of a fixed length, constants, ignored
bytes, records as nested pairs, byte strings and repetitions with a length or count prefix and a
static bound, and tagged unions. The arms of a union are tried in order, so with two arms of the
same tag the first one is used for parsing and writing alike. The values of every description
are those of one inductive type `Val`, and a Millipede data type is related to a description by an
abstraction function into `Val`.

The meaning of a description is three Lean functions over byte lists, which the kernel reduces. The
parser reads a value from the front of the input and returns it with the bytes left over, the
writer gives the bytes of a value, and the validator returns the bytes the parser would leave
without building the value. Every description has a static bound on the bytes of a value, so an
unbounded format cannot be described. The following theorems are proved once for every
description:

- parsing the bytes of a value, followed by any bytes, gives back the value and those bytes;
- the bytes of a value are within the static bound, and a parse consumes as many bytes as the
  value's bytes;
- when the description is canonical, a parse consumes exactly the bytes of the value it returns,
  so no two byte strings mean the same value;
- the validator accepts exactly the inputs the parser accepts and leaves the same bytes.

A description is canonical unless it contains ignored bytes, which may hold anything when read.

Millipede code over byte slices parses, writes and checks every leaf form: integers of one to
eight bytes, byte strings of a fixed length or with a length prefix, and constants and ignored
bytes of at most eight bytes. A parser takes the position by `&mut` and returns true exactly when
the model's parser accepts the bytes from the position, and then its contract gives the position
after the value and the value. A writer writes exactly the model's bytes at the position and
leaves every other byte of the buffer unchanged. A validator returns true exactly when the model's
validator accepts, without building the value.

The code for a whole message is generated. The programmer writes a Millipede structure and one
description that names the field each part of the message fills, and the command `mp format f
for T := (…)` checks the description against the structure's fields and their types. It then
defines the description `f`, the abstraction `T.toVal` from the structure into `Val`, and the
functions `T.parseAt`, `T.writeAt` and `T.validAt`, each a sequence of calls to the leaves, the
structures nested in it and loops over repetitions. The command proves each function's contract
against `f` and its obligations, by tactics that walk the description and apply lemmas proved once
for every description, and if a proof fails it stops and leaves no declaration behind. The
key-value request, whose three arms share the field `key`, is described this way:

```lean
mp format reqFmt for KReq :=
  (id : uint 2 big,
   op : union 1 big
     | 1 => (key : keyFmt)
     | 2 => (key : keyFmt, val : valFmt)
     | 3 => (key : keyFmt))
```

The contracts prove that the code agrees with the generated description and abstraction, so the
step from the text the programmer wrote to `f` and `T.toVal` is trusted generator code, which the
tests compare with descriptions written out by hand. A writer requires only that each byte string
is within its bound, and it writes `Fmt.write f (T.toVal v)`, so an integer too wide for its bytes
is written truncated and does not parse back; every value a parser returns can be written back
unchanged. The key-value server's request parser and response writer are generated, and the
server is proved to refine an abstract key-value store: for every oracle its trace is the reads, a
write of the store's response to each request that `Fmt.parse` decodes from the input, and the
exit, with status 1 at the first malformed request (Tests/KVRefine.lean).

The parts of the plan that are not built, among them a length-prefixed nested message, a reader
of one field in place, and the labelling of parsed data as trusted, are listed in
[../open-claims.md](../open-claims.md).
