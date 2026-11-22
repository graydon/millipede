# Definitions

A Millipede program is a sequence of Lean commands, and this part of the reference describes the
commands that define its functions, externs, data types, programs and units. The statements and
expressions that make up a function's body are described in [statements.md](statements.md) and
[expressions.md](expressions.md).

| form | defines |
|---|---|
| `mp def f (x : T) … : R := body` | a function |
| `mp def f … requires P : R := body` | a function with a precondition |
| `mp def f … requires P ensures Q : R := body` | a function with a contract |
| `mp extern [noreturn] "sym" f (x : T) … : UInt64` | an extern |
| `mp capability C for "sym", …` | a capability class and its token type |
| `structure S … deriving Data` | a structure usable in Millipede code |
| `inductive E … deriving Data` | an enum usable in Millipede code |
| `mp format f for T := (x : d, …)` | a binary format of a structure, with its parser, writer and validator |
| `mp program p (root : T) init f step g [invariant I]` | a program |
| `mp dimension D` | a dimension of quantities |
| `mp unit u : D := k` | a unit of a dimension |
| an `mp def` under `variable (…)` | a generic function |
| `mp interface I (params) where items` | an interface |
| `mp implementation n : I args where items` | an implementation of an interface |

The commands are available in a file that imports `Millipede.Meta.MpDef`, and the standard units
are in `Millipede.Lib.Units`. The word `mp` is not reserved, so it remains usable as an ordinary
identifier.

## Functions

An `mp def` command defines a function. It gives the function's name, its parameters with their
types, its result type and its body, which is either an expression or a block of statements:

```lean
mp def clampAdd (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then 18446744073709551615 else s
```

A doc comment may precede the command. `mp def` translates the body into a term of Core, the
small language that the compiler reads, and checks it. It also defines an ordinary Lean function
of the same name that computes the same result, and proofs are about this function. The declarations
the command adds are listed in [names.md](names.md).

A function may call only functions and externs defined before it, so a function cannot call
itself. A call names the callee and gives its arguments, `f x y`. When the definition fails, the
function is not defined, and a later call to it reports that it was not defined because of the
earlier error.

## Parameters

A parameter is passed by value, by shared reference or by exclusive reference, and the form of
its type says which. `(x : T)` passes a value. `(r : &T)` passes a shared reference, through
which the function may read the caller's place but not write it. `(r : &mut T)` passes an
exclusive reference, through which the function may also write the place, and the caller sees
the writes after the call.

The following function takes an exclusive reference to a structure and writes two of its
fields:

```lean
mp def enter (d : &mut Depth) requires d.cur < 8 ∧ d.max ≤ 8
    ensures d'.cur = d.cur + 1 ∧ d'.max ≤ 8 : Unit := do
  d.cur := d.cur +! 1
  if d.max < d.cur then d.max := d.cur
```

A slice parameter has the type `&[T; n]` or `&mut [T; n]`, which is a view of consecutive
elements of an array of `n` elements of type `T`. Each slice parameter `s` comes with a hidden
length `s.len`, which the caller fills in from the slice it passes. The function may assume
`s.len ≤ n` and that every element below `s.len` is present, because every caller guarantees it.
`Tests/LoopRef.lean` has `fillS`, which writes every element of a slice:

```lean
mp def fillS (s : &mut [UInt64; 8]) (v : UInt64) : Unit := do
  for i in 0...s.len do
    s[i] := v * 3 + i
```

How references and slices are borrowed and passed at a call is described in
[expressions.md](expressions.md).

## Preconditions

A precondition is a Lean proposition about the parameters, written after the parameters with
`requires`. The function's obligations are proved under its precondition, and every call of the
function adds the precondition, at the call's arguments, to the caller's obligations. In the
following function the precondition makes the index `k` safe:

```lean
mp def closerOf (k : UInt64) requires k ≤ 3 : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
```

A precondition may use predicates defined in Lean, such as `IsKind k` for `def IsKind (k :
UInt64) : Prop := k ≤ 3`.

## Contracts

A postcondition is a Lean proposition written after the precondition with `ensures`. In it,
`result` names the value the function returns and `p'` names the final value of an `&mut`
parameter `p`, while `p` itself names the value on entry. A precondition and a postcondition
together are the function's contract. `Tests/Contracts.lean` has a function with both:

```lean
mp def inc (x : UInt64) requires x.toNat < 10 ensures result.toNat = x.toNat + 1 : UInt64 :=
  x + 1
```

`mp def` tries to prove the contract when the function is defined, and when it cannot, it says
so and leaves the goal for `mp prove f.spec`, which is described in [proofs.md](proofs.md). A
proof about a caller uses the callee's contract, not its body. A function with `ensures` cannot
have a parameter named `result`, nor one named `p'` when it has an `&mut` parameter `p`.

### Contracts about events

The `ensures` of a function that makes calls may also name three values:

| name | type | meaning |
|---|---|---|
| `history` | `List Event` | the events before the call |
| `events` | `List Event` | the events the call appends, oldest first |
| `exited` | `Bool` | whether the call ends by `exit` |

The oracle is in scope as `ω`. The answer to a call `c` made after the events `pre` of this call
is `ω.answer (history ++ pre) c`, and its event is `c.event` of that answer. A contract that
names one of the three is a contract about events. `Tests/EnsuresEvents.lean` has a function
that writes a greeting:

```lean
mp def greet ensures events = [writeCall.event (ω.answer history writeCall)] ∧ exited = false
    : Unit :=
  let _w := sysWrite 1 "hello, world\n"
  ()
```

The contract holds of every run from a world that has not exited: the run appends a list of
events to the history, and `ensures` holds of that list. It fixes the events only as far as it
states them, so `events.length = 1` says that there is one event and nothing about it. From a
world that has exited, the function changes nothing, and `f.spec` says so too, so that a caller's
proof can go on after a callee that may exit. A parameter cannot be named `history`, `events` or
`exited`. A function without calls has no events, and the three names are not in
scope in its `ensures`.

## Externs

An extern is a function implemented outside the program, which the program calls to reach the
operating system. It is declared with `mp extern`, which gives the symbol, the name used in
Millipede code, the parameters and the result type `UInt64`. `noreturn` marks an extern that
never returns. The externs of `Tests/Reactor.lean` read one byte and exit:

```lean
mp extern "read" rRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern noreturn "exit" rExit (code : UInt64) : UInt64
```

A parameter of an extern is a word or a buffer. A buffer the extern reads has the type `Bytes`,
which takes a string literal, or `&[U8]`, which takes a shared slice `&a[lo..hi]` of a byte
array. `OutByte` is one byte that the extern writes, and the call passes no argument for it.
`&mut [U8]` is a byte slice the extern writes, passed as `&mut a[lo..hi]`. A string literal can
be passed only to an extern, so an `mp def` cannot take or return one.

The compiler translates calls to the Linux system calls `write`, `read` and `exit`, and it
refuses a program that calls any other extern.

An extern may begin with token parameters of the form `(c : &C)`, where `C` is the token type of
a capability class that governs the extern's symbol. A call then passes `&t` for a token `t` of
that class in each such position, which must not have been moved, and the token takes no part
in the call at run time. The
extern of `Tests/Log.lean` writes only for a caller that holds an `Fs` token:

```lean
mp extern "write" fsWrite (fs : &Fs) (fd : UInt64) (buf : &[U8]) : UInt64
```

## Capabilities

A capability class names the extern symbols that a function may call only while it holds a token
of the class. It is declared with `mp capability`, which gives the class's name and its symbols,
as `Tests/Log.lean` does for writing:

```lean
mp capability Fs for "write"
```

The command defines the token type `Fs`, which is `Cap "<full name of Fs>"`, and the list
`Fs.syms` of the symbols. A token takes no space and is linear, and only the program's `init` can
receive one, so Millipede code can neither build nor copy a token. `Cap.drop` consumes a token,
which can then no longer be passed to an extern. A symbol belongs to at most one class.

A function holds a class when one of its parameters has a type that contains a token of the
class, by value, by reference or inside a structure, enum, pair, result, array or `Slots` value.
Each `mp def` after the declaration of a class is checked, and a function whose body or callees
call a symbol of a class it does not hold is rejected, even when the call goes through an extern
declared without a token. For the classes a function does not hold, `mp def` proves
`f.noCalls : f.exp.NoCalls S`, where `S` lists their symbols, which says that no run of the
function calls one of them. A generic function is not checked, and each function that calls it
is. Holding is decided from the parameter types, so a function that has dropped its token still
holds the class, but it cannot pass the token to an extern.

## Handles and their states

A handle is a sealed linear structure with a state as a type parameter, such as the log of
`Tests/Log.lean`, whose state says whether its buffer holds bytes not yet written:

```lean
structure Log (s : LogSt) where
  private mk ::
  fd : UInt64
  buf : ByteBuf 16
  st : LogTok s
deriving Data
```

The state costs nothing at run time, and the field `st`, a sealed zero-size linear value, makes
the handle linear. An operation that changes the state takes the handle by value and returns it
at the new state, as `Log.sync (fs : &Fs) (h : Log .dirty) : Log .clean` does, and an operation
that keeps the state may take `&mut`. The checker then rejects a use after close, a second
close, a handle never closed and an operation applied in the wrong state, the last as a type
mismatch. Only the handle's module can build one, by a private constructor such as `LogTok.mint`,
and end one, by a private constructor of type `Ctor [⟨Log s⟩] Ty.unit`.

## Data types

A Lean structure or enum becomes usable in Millipede code when it is declared with
`deriving Data`, which fixes its layout in memory and generates the declarations Millipede code
needs to build it, read it and take it apart. A structure keeps its fields in declaration order,
laid out as a C compiler lays out the corresponding C struct:

```lean
structure Pt where
  x : UInt64
  y : UInt64
deriving Data
```

An enum is an `inductive` type with at least two constructors, each of which has at most one
field. It is laid out as a tag, the constructor's number, followed by the field. A constructor
that needs several fields takes a structure. `Tests/Derive.lean` has an enum with three
constructors:

```lean
inductive Cmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving Data
```

Every field must itself have a layout, so a type cannot contain itself. A structure or enum is
linear when one of its fields is linear. A field whose type is a proposition takes no space, and
Millipede code cannot build a structure that has one. A structure or enum may have type and size
parameters, such as `structure Log (T : Type) (n : Nat)`, and its declarations are then generated
once, over all values of them.

`deriving Data` rejects a type with indices or universe parameters, an enum constructor with two
or more fields, a single-constructor `inductive` that is not a `structure`, and a field without a
layout. Each is reported with a message that names the field or constructor.

## Formats

`mp format f for T := (…)` gives the structure `T` a binary format, the description `f`, and
generates its parser, writer and validator with their contracts proved. The structure is written
first, with `deriving Data`, and the description names the field that each part of the message
fills. `Tests/FormatKV.lean` has the request of a key-value protocol:

```lean
structure KReq where
  id : UInt64
  op : UInt64
  key : LBytes 16
  val : LBytes 32
deriving Data

mp format reqFmt for KReq :=
  (id : uint 2 big,
   op : union 1 big
     | 1 => (key : keyFmt)
     | 2 => (key : keyFmt, val : valFmt)
     | 3 => (key : keyFmt))
```

A description is a record `(x : d, …)`, its fields in order on the wire, and `()` is the empty
record. The forms of `d` are the following; `big` and `little` are the byte orders.

| form | bytes | field |
|---|---|---|
| `uint k big` | an unsigned integer of `1 ≤ k ≤ 8` bytes | `UInt64` |
| `lbytes k big max` | a length of `k ≤ 8` bytes, at most `max`, then that many bytes | `LBytes M`, `max ≤ M` |
| `bytes n` | `n` bytes | `Arr UInt8 n` |
| `const [b, …]` | the bytes given, 1 to 8 of them | none: `_ : const […]` |
| `skip n` | `n ≤ 8` bytes, ignored when read and written as zeros | none: `_ : skip n` |
| `union k big \| t => (…) \| …` | a tag of `k ≤ 8` bytes, then the record of the arm with that tag | the tag: `UInt64` |
| `array k big max S` | a count of `k ≤ 8` bytes, at most `max`, then that many values of `S` | `Seq S M`, `max ≤ M` |
| `S` | a value of the structure `S`, which has a format | `S` |
| `g` | the leaf description `g : Fmt`, such as `keyFmt := .lbytes 1 .big 16` | as for its form |

The fields after a union are read after the arm that the tag selects. The arms of a union may fill
the same field, as `key` above. The elements of an `array` are a structure that has a format and
an `Inhabited` instance; `Seq S M` holds a count `len` and the array `data`.

The command checks the description against the structure and stops with a message, before
generating anything, when a field it names does not exist or has the wrong type, when a field of
the structure is not filled, when a field is filled twice on one path, when a width is out of
range, when a bound exceeds the field's capacity (`lbytes … 40` into `LBytes 32`), and when a tag
does not fit in its width or appears twice. It then defines, in the current namespace:

| name | what it is |
|---|---|
| `f : Fmt` | the description; `f_maxSize : f.maxSize = n` by `rfl` |
| `T.toVal : T → Val` | the value of `f` a `T` stands for: a record is nested `pair`s, a union `.tag` of its arm's value |
| `T.Bound : T → Prop` | each byte string, count and nested value on the path of the value is within its bound |
| `T.parseAt (s : &[U8; N]) (pos : &mut UInt64) (out : &mut T) : Bool` | `ensures Parsed f B pos result pos' out'.toVal ∧ (result = true → pos' ≤ s.len ∧ T.Bound out')` |
| `T.writeAt (d : &mut [U8; N]) (pos : &mut UInt64) (v : &T)` | `requires pos + f.maxSize ≤ d.len ∧ T.Bound v`, `ensures Written f d d' pos pos' v.toVal ∧ pos' ≤ pos + n` |
| `T.validAt (s : &[U8; N]) (pos : &mut UInt64) : Bool` | `ensures Checked f B pos result pos' ∧ (result = true → pos' ≤ s.len)`, without building a value |
| `S.parseItems`, `S.writeItems`, `S.validItems_max` | the element loops of an `array` of `S`, generated at its first use |

Here `B` is `Slots.bytes s s.len.toNat`. `Parsed`, `Written` and `Checked` are defined in
[library.md](library.md): the parser returns true exactly when `Fmt.parse f` accepts the bytes
from `pos`, with the value and the position after it; the writer writes exactly `Fmt.write f` of
the value and nothing else; the validator returns true exactly when `Fmt.check f` does. Every
function is an ordinary `mp def` with `.spec` and `.safe`. The contracts are proved by the tactic
`fmt_close`, which walks the description in each verification condition and applies the
composition lemmas, and the obligations by `fmt_safe`. If a proof fails, the command stops with a
message that names it, and none of its declarations is left. The step bound of each function is
printed by `#mp_cost`.

A writer requires only `T.Bound`, so an integer too wide for its bytes, or a tag that has no arm,
is written as `Fmt.write f` writes it, truncated or without a body, and those bytes do not parse
back to the value. A value that a parser returned is within `T.Bound` and is a value of `f`, so
writing it gives bytes that parse back to it. The contracts relate the code to the generated `f`
and `T.toVal`; that these are what the description's text says is checked by tests that compare
them with terms written by hand.

## Programs

A program consists of a value called the root and two functions. `init` returns the root, and
`step` takes one parameter, an exclusive reference to the root. The
program runs `init` once and then `step` again and again until a step calls `exit`. A program is
declared with `mp program`:

```lean
mp program brackets (root : Br) init brInit step brStep invariant BrInv
```

The root is kept in static storage for the life of the program. The command checks the program,
and when the obligations of `init` and `step` are proved, it proves that every step of the
program is safe for any input. This proof is named `p.safe`, and the compiler refuses a program
without it.

The clause `invariant I` names a property `I : T → Prop` of the root. `init` must establish it,
and every step may assume it and must keep it, so it holds after any number of steps. The
command tries to prove these two facts from the contracts of `init` and `step`. When `step` has a
precondition, the invariant must imply it, and a program without an invariant gets no `p.safe`.
When a fact is not proved, it is left for `mp prove p.inv_init` or `mp prove p.inv_step`.

When `step` has a contract about events and `init` has one or makes no call, the command states what the contracts allow and proves that the program keeps to it. It
defines `p.initRel ω r evs e`, the contract of `init` from the empty history, and
`p.stepRel ω r h evs e r'`, the contract of `step` from the root `r` and the history `h` to the
root `r'`; when the contract of `step` has a precondition `R`, `p.stepRel` is `R r → E`. It
proves `p.reach`, that the state after `n` steps is one that `Program.Reach` allows
from these two, and `p.events_reach`, the same for the trace. A contract of `step` proved later
by `mp prove` gives them then.

`init` takes no parameters, or only tokens of capability classes, by value, which are the
program's grant. For such an `init` the command defines `p.init`, which calls it with one new
token of each class, and this is the only place where tokens are made. A program usually keeps
its tokens in the root. When some recorded class is not granted, the command proves
`p.noCalls : p.NoCalls S` for the symbols `S` of those classes, which says that no trace of the
program calls them. The program of `Tests/Log.lean` receives the token it writes with:

```lean
mp def logInit (fs : Fs) : LogRoot := { fs := fs, inb := ByteBuf.new }
```

## Units and dimensions

A quantity is a word tagged with a unit, such as a count of bytes or of milliseconds. Units are
grouped into dimensions, and only units of one dimension can be converted into each other. A
dimension is declared with `mp dimension`, and a unit with `mp unit`, which gives the unit's
dimension and its size in base units. `Millipede/Lib/Units.lean` declares the standard ones:

```lean
mp dimension Size
mp unit byte : Size := 1
mp unit KiB : Size := 1024
```

The scale must be positive. How quantities are used in expressions is described in
[expressions.md](expressions.md).

## Generic functions

An `mp def` written under Lean `variable` binders is generic. It takes the variables it uses,
and every declaration it generates is a single Lean term over those variables, which is checked
and proved once. A variable is one of four kinds. A type is `(T : Type) [Data T]`, with
`[Data.Copy T]` when values of `T` are copied, and without it `T` is treated as linear. A size is
`(n : Nat)`, which may be used as a loop bound, as an array length `Arr T n`, and as the word
`UInt64.ofNat n`. A hypothesis is a proposition about the other variables, such as
`(h : n < 2 ^ 64)`. An implementation of an interface is `(A : I …)`.

`Tests/Tutorial.lean` defines a log of any element type and size:

```lean
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)
mp def Log.add (l : &mut Log T n) (v : T) requires l.len.toNat < n
    ensures l'.len = l.len + 1 : Unit := do
  l.items[l.len]! := v
  l.len := l.len + 1
```

A definition takes the variables it mentions and those that the types of these mention. It takes
an instance binder, or a hypothesis made available with `include`, when it takes every variable
that binder's type mentions. A definition that uses none of the variables of `include h` is
therefore not generic over `h`.

At a call of a generic function, each of its variables is inferred. It comes from the expected
type, from the types of the arguments, from instance search, from a hypothesis in the context or
one that `decide` proves, or from the one variable of its type in the caller's context. A
variable that none of these gives is reported by name, and the caller then names it with the form
`f (x := e) args`:

```lean
mp def outside8 (v : UInt64) : UInt64 := Ctx.first (A := Bump8.impl) v
```

## Interfaces

An interface describes what an implementation provides, as a Lean structure whose fields are
abstract types, a model of their values, and operations with contracts stated over that model.
It is declared with `mp interface`, followed by its parameters and its items. An item `x : T` is
a field, and an item `op f (params) requires P ensures Q : R` is an operation with the header of
an `mp def`. `Tests/Tutorial.lean` declares a counter:

```lean
mp interface Counter where
  S : Type
  val : S → UInt64
  op zero ensures val result = 0 : S
  op bump (s : &mut S) requires val s < 1000 ensures val s' = val s + 1 : Unit
  op read (s : &S) ensures result = val s : UInt64
```

An `mp def` under `variable (A : Counter)` calls an operation as `A.bump (&mut s)`. Its
obligations and contract are proved once, from the interface's contracts, and so they hold for
every implementation. Such code treats a value of an abstract type as linear, because the
implementation's type may be, so it passes the counter's state by reference.

## Implementations

An implementation is a value of an interface, declared with `mp implementation`. An item
`op f := g a…` gives the operation `f` as an application of an `mp def`, whose contract becomes
the operation's contract. Any other item `field := term` gives a field directly, and a field
that is a function may name its arguments, as in `val c := c`:

```lean
mp implementation Ctr.impl : Counter where
  S := UInt64
  val c := c
  op zero := Ctr.zero
  op bump := Ctr.bump
  op read := Ctr.read
```

The implementation is a reducible Lean definition, so a client applied to it, such as
`bumpTwice Ctr.impl`, computes with the implementation's functions. The library's arenas are
implementations of the interface `Alloc`, described in [library.md](library.md).
