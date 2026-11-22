# Extern calls and the world

This document describes how a Millipede program calls code outside itself and what is assumed
about the world that code belongs to. The oracle, the event trace, three Linux system calls and
capability tokens are built, and the rest is a plan.

## Extern calls today

A program reaches the outside world only through extern calls, each declared with
`mp extern`. The only externs today are the Linux system calls `read`, `write` and `exit`, which
the compiled code makes directly with the kernel's convention. Two of the declarations in
Millipede/Top/Examples.lean show the form.

```lean
mp extern "write" sysWrite (fd : UInt64) (buf : Bytes) : UInt64
mp extern noreturn "exit" sysExit (code : UInt64) : UInt64
```

An event records one extern call: its symbol, its word arguments, the contents of the buffers it
reads, its result, and the contents of the buffers it writes. An event never contains an address,
so an extern's answer may depend on the contents of a buffer but not on where it lies. Because
the trace holds every byte passed out, two runs with equal traces have sent out exactly the same
bytes, and stale memory cannot leak through an extern.

Both the source semantics and the machine semantics are functions of an oracle, which answers
each call given the events before it. The observable behaviour of a program is its trace under
the oracle. The correctness theorem holds for every oracle and mentions no specification of the
world, so safety never depends on the world behaving well. After `exit`, the trace no longer
changes.

## Capabilities

A capability class is a named set of extern symbols, and a function may call those symbols only
while it holds a token of the class. A token is a value that takes no space at run time, and it
is linear and sealed, so Millipede code can neither copy nor build one. The worked example of
Tests/Log.lean declares a class for writing and an extern that needs its token:

```lean
mp capability Fs for "write"
mp extern "write" fsWrite (fs : &Fs) (fd : UInt64) (buf : &[U8]) : UInt64
```

A program receives its tokens as the parameters of its `init`, which makes one token of each
class that `init` takes before calling it, and these classes are the program's grant. A program
usually keeps its tokens in the root, so that `step` holds them too. A function holds a class
when the type of one of its parameters contains a token of the class, and a call of an extern
that needs a token passes a reference to one that has not been moved.

The guarantee is a theorem about the event trace. For a function that holds no token of some
classes, `mp def` proves that no run of the function calls a symbol of those classes, and it
rejects the function when its body or a callee reaches one, even through an extern declared
without a token. For the classes outside a program's grant, `mp program` proves that no trace
of the program calls their symbols. The compiled code has the same trace as the source, so the
same holds of every run of the executable.

The theorem is proved from the extern symbols that a term and its callees mention, so it would
hold of the same code written without tokens. Tokens make the authority of each function part of
its signature, and the elaborator checks it as each function is defined, so a function that
reaches a symbol of a class it does not hold is rejected where it is written. The kernel checks
the theorem, so for the trace property a reader needs to trust neither that check nor the
sealing of tokens. A symbol that belongs to no class may be called by any function, and a
program that is not declared with `mp program`, or a class declared after it, is covered by no
such theorem. `compile` accepts any program, so the claim is exactly the theorem proved for it.

A class is a set of symbols because an event records only its symbol. Two externs with one
symbol are therefore one class, so a class cannot tell writing a file from writing a socket.
A token stands for all of its class and cannot be split, for example into a token for one
directory. The states of a handle, such as a log whose buffered bytes must be synced before it
is closed, are enforced by the checker and by tests, and no theorem states them.

## Extern bindings

The rest of this document, up to the last section, describes the planned design, and none of
it is built. A program calls C functions as well as system calls, through a binding. A binding
gives each function a symbol, a C signature of at most eight word or reference parameters, and
a specification as a transition on a model state. A program theorem assumes that the oracle
obeys the binding, as a hypothesis of the theorem and never as an axiom, and the ledger lists
the bindings each theorem assumes.

Every extern is assumed to obey a memory contract. It reads and writes only the buffers passed
to it, and only during the call, and its answer depends on the contents of buffers but not on
their addresses. It preserves the registers the C convention preserves, returns exactly once,
and does not call back into Millipede code.

## The world model

A binding for a platform is trusted, so its specification is deliberately weak. It allows
everything the real system can do. Any call may fail with any documented error, reads and writes
may be short, and a blocking call may never return. Tests check that the real behaviour is
included in the model, never that the two are equal. The world can also change between calls,
so a binding states which changes other processes and the clock may make.

Above the bindings, portable interfaces for files, the network, the clock and randomness are
written in Millipede and proved against portable models. They are based on handles with no
ambient names, so a file is opened relative to a directory handle, which removes races on paths.

Each part of the world has a weakest default and stronger assumptions that a program may opt
into, each recorded in the ledger. By default the contents of a file are arbitrary at every
read, the process may die at any event, a peer on a network connection may send anything, and
random bytes are arbitrary. A program asks for no memory after it is loaded, which is already
true of every compiled program.

A reactor begins each step with one blocking wait whose answer, the next event, is chosen by the
environment, and the program must accept any event in any state. Signal handlers, shared
writable mappings and `fork` are excluded and listed as assumptions.

## Exports

An exported function gets a wrapper in the platform's C convention. Its theorem says that a
caller who obeys the convention and the function's precondition sees the events and result of
the source. A library's root lives in static storage behind an `init` that must be called first.

## Where this lives

The oracle and events are in Millipede/Extern/Oracle.lean, and the system-call models are
described in [targets.md](targets.md).
