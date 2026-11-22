# Protocols

This document describes how Millipede states and checks that a program follows a protocol, such
as the lifecycle of a file handle or the exchange of messages with a peer. Typestate on handles is
built, and the rest is a plan.

A protocol position can live in a type or in run-time data. A position in a type is checked by
the type checker at each operation, which suits a lifecycle that starts and ends inside one
function or one reactor step. A position in run-time data, such as a state field of the root
that `step` branches on, suits a protocol that spans reactor steps. The legality of each
transition is then a theorem about `step`. A position in a type cannot easily span steps,
because the root's type is fixed while the position's type changes with the state.

## Typestate

A handle is a sealed linear structure whose state is a type parameter, so the type checker
rejects an operation applied in the wrong state, and the state costs nothing at run time. The
log of Tests/Log.lean is a handle whose state says whether its buffer holds bytes not yet
written:

```lean
structure Log (s : LogSt) where
  private mk ::
  fd : UInt64
  buf : ByteBuf 16
  st : LogTok s
deriving Data
```

The field `st` is a zero-size linear value that only the handle's module can make, which makes
the handle linear. An operation that changes the state takes the handle by value and returns it
at the new state, as `Log.sync (fs : &Fs) (h : Log .dirty) : Log .clean` does, and an operation
that keeps the state may take the handle by `&mut`. `Log.close` takes only a clean log and is the
only way to end one outside its module. The checker therefore rejects a use after close, a second
close, a log never closed and an operation in the wrong state.

The state can be any Lean value. A handle kept in the root is in the same state at the end
of every step, because the root's type is fixed. A transition whose outcome
is not known in advance, which would return handles in different states on different arms, is
not built.

## Reactor refinement

A machine is a Lean value with a state type, an initial state and a step relation labelled with
observable actions. A program refines a machine when some relation between the program's root
and the machine's state is established by `init` and preserved by every `step` for every oracle
answer, and the events of each step are actions the machine can take. A theorem proved once
shows that every trace of such a program is a trace of the machine, and with the correctness
theorem this holds of the compiled code.

Trace inclusion alone is weak, since a program that does nothing refines every machine.
Refinement therefore also requires that every reachable state handles every input the machine
may receive. An output that the machine owes after an input must be emitted by the step that
handles that input. Steps are bounded, so this is a property of one step.

The same mechanism states what a program computes, for example that a server behaves as an
abstract key-value store. One such refinement is built: the server `kvsrv` of
Tests/FormatKVSrv.lean against the store of Tests/KVSpec.lean. The relation is between the
server's root and a configuration that holds the rest of the trace, preserved by each step that
the contract of the server's step allows (`kvsrv_reach`, an induction over `Program.Reach`), and
between the server's four slots and the abstract map (`Refines`); the theorem is the equality of
the trace with the machine's (`kvsrv_events`). It is a theorem about one program; no general refinement relation or machine
type exists yet. A protocol is a machine whose actions are sending and receiving
labelled messages. When the peer is a program outside the proof, every receive has an error
transition, and the refinement speaks only of the program's own side, which never leaves the
protocol whatever the peer sends.

## Global types

A global type describes the messages exchanged among several roles, and a Lean function
projects it onto the local machine of each role. Suppose each role's program refines its
projection and the transport between them is reliable and ordered. A theorem proved once then
shows that the composed trace follows the global type, with no role stuck and no message left
unread.

The intended use is privilege separation, in which several processes that we compile, each with
few capabilities, are connected by pipes. Automatic projection covers only finite global types.
A protocol whose structure depends on data needs hand-written local machines and a proof that
they compose.

## Trace predicates

A program's event trace is a Lean value, so any property of the trace can already be stated as
a Lean predicate and proved about the program. Refinement of a machine is a structured form of
such a predicate.
