# Generic code and interfaces

Millipede has no module system of its own. Code that works for many types, sizes or
implementations is written as generic definitions, and an interface is a Lean structure. A
theorem about generic code is then an ordinary Lean theorem quantified over its variables, so
Lean's own records and quantifiers do the work that a module system would do, and the compiler
deals only with closed programs.

## Generic definitions

A generic definition is an `mp def`, `mp program` or `mp implementation` written after Lean
`variable` binders, or a type with parameters declared with `deriving Data`. A variable may stand
for any of the following:

- a type `T`, declared with `(T : Type) [Data T]`, whose values are linear unless the binder
  `[Data.Copy T]` says that they may be copied;
- a size `(n : Nat)`, which may be used as an array length, as a loop bound or as the word
  `UInt64.ofNat n`;
- a hypothesis about the sizes, such as `(h : n < 2 ^ 64)`;
- an implementation `(A : I args)` of an interface `I`, which is a value of the structure `I`.

A definition takes the variables it mentions and those that their types mention. It takes an
instance binder, or a hypothesis named by `include`, when it takes every variable that the
binder's type mentions, which is Lean's own rule for definitions. Every declaration that `mp def`
generates for a generic function is a Lean term over the variables it takes, so its obligations
and contract are proved once for every value of them.

The following structure and function are generic over a type and a size, and `logBoth` uses
`Log.add` at two instances:

```lean
structure Log (T : Type) (n : Nat) where
  items : Arr T n
  len : UInt64
deriving Data
section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)
mp def Log.add (l : &mut Log T n) (v : T) requires l.len.toNat < n
    ensures l'.len = l.len + 1 : Unit := do
  l.items[l.len]! := v
  l.len := l.len + 1
end
mp def logBoth (a : &mut Log UInt64 4) (b : &mut Log UInt8 16) (c : UInt64)
    requires a.len.toNat < 4 ∧ b.len.toNat < 16 : Unit := do
  let _ := Log.add (&mut a) c
  Log.add (&mut b) c.toUInt8
```

## Instances

An instance of a generic definition is the definition applied to arguments, as any Lean
function is. `Pool UInt64 8 1` is a type, and the safety of a generic program at an
implementation is the generic safety theorem applied to that implementation.

At a call of a generic function in an `mp def`, Millipede infers each variable of the callee. It
looks at the expected type and the types of the arguments, synthesises instances, finds a
hypothesis in the caller's context or decides it, and takes the caller's only variable of the
right type. A variable that none of these gives is reported by name, and the call then names it,
as in `Ctx.first (A := Bump8.impl) v`. A hypothesis that is neither in the context nor decided
is also reported, because nothing then shows that the call meets it.

The compiler sees only closed programs, in which every variable has been given. Each instance
is therefore compiled into its own code, and no call is dispatched at run time.

## Interfaces

An interface is a Lean structure declared with `mp interface`. It lists abstract types, a model
of the state that proofs refer to, and operations. Each operation is declared with `op`, its
parameters, its contract and its result type. The following interface describes a counter whose
model is its value:

```lean
mp interface Counter where
  S : Type
  val : S → UInt64
  op zero ensures val result = 0 : S
  op bump (s : &mut S) requires val s < 1000 ensures val s' = val s + 1 : Unit
  op read (s : &S) ensures result = val s : UInt64
```

For each operation the structure holds the implementation's function, the Lean function that
proofs use, the proof that the two agree, and the proofs of its safety and its contract.

## Implementations

An implementation is a value of an interface, declared with `mp implementation`. It gives the
abstract types and the model, and it fills each operation from an `mp def`. The contract that
the interface states for the operation is then proved from the contract of that `mp def`. The
following implementation keeps the counter in a word:

```lean
mp def Ctr.zero ensures result = 0 : UInt64 := 0
mp def Ctr.bump (c : &mut UInt64) requires c < 1000 ensures c' = c + 1 : Unit := do
  c := c + 1
mp def Ctr.read (c : &UInt64) ensures result = c : UInt64 := c
mp implementation Ctr.impl : Counter where
  S := UInt64
  val c := c
  op zero := Ctr.zero
  op bump := Ctr.bump
  op read := Ctr.read
```

An implementation can be generic too. The library's `Pool.impl` and `Bump.impl` implement the
allocator interface `Alloc` for every cell type and capacity.

## Clients

A client is generic code written against an interface, under a variable `(A : I args)`. It calls
the operations as `A.f`, and its proofs use only the contracts that the interface states, so they
hold for every implementation. The following function bumps any counter twice:

```lean
variable (A : Counter)
mp def bumpTwice (s : &mut A.S) requires A.val s < 100 ensures result = A.val s + 2 :
    UInt64 := do
  let _ := A.bump (&mut s)
  let _ := A.bump (&mut s)
  A.read (&s)
```

`bumpTwice Ctr.impl` is the client at the word counter. A whole program may be a client in the
same way. The library's `pooltally` example is a reactor over any allocator that has at least
eight cells and gives cells back, and its root invariant and safety are proved once for every
such allocator.

## Abstract types

Inside a client, the abstract types of an implementation variable are opaque. The key type `A.K`
of an allocator `A` is treated as linear, because its linearity is not known, so a client frees
each key at most once whatever implementation it is given. Two implementation variables `A` and
`B` have different key types, so a key from `A` given to an operation of `B` is a type error:

```lean
variable (A B : Alloc UInt64)
mp def Mix.f (a : &mut A.S) (b : &mut B.S) (v : UInt64) requires A.Inv a ∧ A.used a < A.cap :
    UInt64 := do
  let k := A.alloc! (&mut a) v
  B.free (&mut b) k
-- error: type mismatch: expected B.K, but this has type A.K
```

The command `#mp_report` shows, for a generic function, what is proved once, and for a program,
the figures of each function at the program's arguments. The verified analyser and the figures
for stack, cost and footprint exist only for closed definitions. The limits of generic code are
listed in [../open-claims.md](../open-claims.md).
