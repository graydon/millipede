# Library

The library provides arenas, which hold values whose number varies while a program runs, a byte
buffer for input and output, and functions over slices. Each is written in Millipede, and each
operation's contract is its `requires` and `ensures`. In a contract, `p'` is the arena after the
call.

| module | provides |
|---|---|
| `Millipede.Lib.Pool` | `Pool T n W`, a pool whose cells are reused after `free` |
| `Millipede.Lib.Bump` | `Bump T n`, a bump arena emptied all at once by `reset` |
| `Millipede.Lib.Alloc` | the interface `Alloc` of both arenas, and the invariants `Holds` and `KeyStack` |
| `Millipede.Lib.ByteBuf` | `ByteBuf cap`, a byte buffer for `read` and `write` |
| `Millipede.Lib.Slice` | `Slice.fill`, `Slice.copy` and `Slice.reverse` |
| `Millipede.Lib.Units` | the dimensions `Size` and `Time` and their units |
| `Millipede.Lib.Cap` | `Cap c`, the token of the capability class `c`, and `Cap.drop` |
| `Millipede.Format.Model` | format descriptions `Fmt`, their values `Val`, and `parse`, `write`, `check` |
| `Millipede.Format.Code` | parsers and writers of the leaves of a description, over byte slices |

## Pools

A pool `Pool T n W` has `n` cells that each hold a value of type `T`, and a bitmap of `W` words that
records which cells are full. `Pool8` is a pool of eight words with one bitmap word, and `Pool100`
holds 100 values of a structure `Cell2`. Each is an abbreviation of an instance, such as `Pool
UInt64 8 1`, so in Millipede code `Pool8.alloc!` calls `Pool.alloc!` at that instance. A pool hands
out a key for each value it stores, and the key is the only way to reach the value. Keys are linear
and sealed, so a key cannot be forged, copied, used after its value is freed, or dropped.

| operation | requires | does |
|---|---|---|
| `Pool8.new` | | an empty pool, `Inv` and `live = 0` |
| `Pool8.alloc (&mut p) v` | `p.Inv` | stores `v` and gives `ok` with a new key, or `err` when the pool is full |
| `Pool8.alloc! (&mut p) v` | `p.Inv ∧ p.live < 8` | stores `v` and gives a new key |
| `Pool8.free (&mut p) k` | `p.Inv ∧ p.Owns k` | consumes the key and gives back its value |
| `Pool8.get (&p) (&k)` | `p.Owns k` | reads the key's value |
| `Pool8.set (&mut p) (&k) v` | `p.Owns k` | writes the key's value |

`p.Inv` says that the pool is consistent, which means that its bitmap matches its cells and
`live` counts the full ones. `p.Owns k` says that the key's cell is full. After `alloc!`, the key
is owned and holds `v`, it was not owned before, every key owned before keeps its value, and one
more cell is in use. After `free`, one fewer cell is in use and every other owned key keeps its
value. `Tests/Tutorial.lean` uses both:

```lean
mp def push (r : &mut Br) (e : UInt64) requires BrInv r ∧ r.d.cur < 8 ensures BrInv r' : Unit :=
  let k := Pool8.alloc! (&mut r.pool) e
  let i := r.d.cur
  let _ := r.keys.put! i k
  enter (&mut r.d)
```

## Bump arenas

A bump arena `Bump T n` has `n` cells and a length. The cells below the length are full and the
rest are empty, and `alloc` fills the cell at the length. A value is named by a copyable index,
and no cell is given back before `reset`, which empties every cell. `Bump8` has eight words and
`Buf16` sixteen bytes.

| operation | requires | does |
|---|---|---|
| `Bump8.new` | | an empty arena |
| `Bump8.alloc (&mut b) v` | `b.Inv` | stores `v` and gives `ok` with its index, or `err` when full |
| `Bump8.alloc! (&mut b) v` | `b.Inv ∧ b.len < n` | stores `v` and gives its index |
| `Bump8.get (&b) x` | `b.Inv` | `ok` with the value when `x` is below the length, `err` otherwise |
| `Bump8.get! (&b) (&x)` | `b.Inv ∧ x.idx < b.len` | reads the value |
| `Bump8.reset (&mut b)` | | empties every cell |

## The allocator interface

`Alloc V` is the interface of an arena of values of type `V`. Its abstract types are the state
`S` and the key `K`, and its model is `Inv`, `Owns`, `cell`, `used` and `cap`. Its operations are
`new`, `alloc`, `alloc!`, `get` and `free`, with the contracts of the pool's operations stated
over this model. `free` gives the cell back exactly when the field `reuse` is true, as for a pool,
while a bump arena only forgets the index. `Pool8.impl` and `Bump8.impl` are implementations, so
code written under `variable (A : Alloc UInt64)` runs on either.

## Holding keys

A program that keeps keys of an arena from one step to the next must say in its invariant which
keys it holds, or `alloc!`'s precondition `used < cap` cannot be proved. The library gives two
invariants for this, and both are proved once for every implementation.

`A.Holds s ks` says that the keys of the list `ks` are distinct, each owned by `s`, and as many as
the cells of `s` in use.

`A.KeyStack s keys n` says that cells `0` to `n - 1` of `keys : Slots A.K m` are full and hold
keys that `s` holds. Pushing a new key and popping the top one keep it, and these lemmas are
tagged `@[mp_auto]`. For a pool, the invariant is written `Pool8.impl.KeyStack r.pool r.keys n`,
as in the root invariant of `Tests/Tutorial.lean`:

```lean
def BrInv (r : Br) : Prop :=
  r.pool.Inv ∧ Pool8.impl.KeyStack r.pool r.keys r.d.cur ∧ r.d.max ≤ 8
```

## Byte buffers

`ByteBuf cap` is an array of `cap` bytes and the number of bytes it holds, `len`, and its
invariant `Inv` is `len ≤ cap`. Its bytes are used in place as slices of the array, so the bytes
held are `&b.bytes[0..b.len]` and the free space is `&mut b.bytes[b.len..cap]`.

| operation | does |
|---|---|
| `ByteBuf.new` | an empty buffer |
| `ByteBuf.push! (&mut b) v` | appends a byte, with the obligation `len < cap` |
| `ByteBuf.clear (&mut b)` | empties the buffer |
| `ByteBuf.readFrom (&mut b) fd` | reads into the free space and appends what was read |
| `ByteBuf.writeTo (&b) fd` | writes the bytes held |
| `ByteBuf.reverse (&mut b)` | reverses the bytes held |
| `ByteBuf.append (&mut b) (&s)` | copies as many bytes of a slice as fit into the free space |

Each operation except `writeTo` keeps the invariant, whatever `read` answers.

## Capability tokens

`Cap c` is the type of the tokens of the capability class named `c`, which a declaration
`mp capability C` names `C`. A token takes no space, is linear and cannot be built in Millipede
code, and `Cap.drop c t` consumes the token `t`. Capability classes are described in
[definitions.md](definitions.md).

## Slices

`Slice.fill s v` sets every element of a slice to `v`, `Slice.copy dst src` copies as many
elements as both slices have, and `Slice.reverse s` reverses a slice in place. Each works on
slices `&mut [T; n]` of any element type and any `n < 2 ^ 64`, which are inferred at the call,
as in `Slice.reverse (&mut b.bytes[0..n])`. Each contract says what every element of the result
holds.

## Format descriptions

A format description is a Lean value of type `Fmt`, which says how a value is laid out as bytes.
Its forms are the following.

| form | bytes |
|---|---|
| `uint k e` | an unsigned integer of `k` bytes, in byte order `e` (`.big` or `.little`) |
| `bytes n` | `n` bytes |
| `const l` | the bytes `l` |
| `skip n` | `n` bytes that are ignored when read and written as zeros |
| `unit` | no bytes |
| `pair a b` | `a`, then `b`; a record is a nest of pairs |
| `lbytes k e max` | a length of `k` bytes, at most `max`, then that many bytes |
| `array k e max f` | a count of `k` bytes, at most `max`, then that many values of `f` |
| `union k e arms` | a tag of `k` bytes, then the format of the first arm with that tag |
| `arm t f rest`, `noArm` | the arms of a union: `f` for tag `t`, else `rest` |

A value is a `Val`, and `f.ok v` says that `v` is a value of `f`. `f.parse bs` reads a value from
the front of `bs` and gives it with the bytes left over, or `none`. `f.write v` gives the bytes of
a value, `f.check bs` is the validator, which gives the bytes left over without building the
value, and `f.maxSize` is a static bound on the bytes of every value. A description without
`skip` is canonical (`f.canonical`). `Millipede/Format/Theorems.lean` proves for every
description:

| theorem | says |
|---|---|
| `Fmt.parse_write` | `f.ok v → f.parse (f.write v ++ rest) = some (v, rest)` |
| `Fmt.write_length_le` | `f.ok v → (f.write v).length ≤ f.maxSize` |
| `Fmt.parse_sound` | a parsed value is a value of `f`, after a prefix as long as its bytes |
| `Fmt.parse_consumed` | a parse consumes the length of the value's bytes, at most `f.maxSize` |
| `Fmt.parse_canonical` | when `f` is canonical, `f.parse bs = some (v, r) → bs = f.write v ++ r` |
| `Fmt.parse_injective` | when `f` is canonical, two inputs that parse to the same result are equal |
| `Fmt.check_eq`, `Fmt.valid_iff` | the validator accepts exactly what the parser accepts |

A description's Millipede data type is an ordinary structure, related to the description by an
abstraction function `toVal : T → Val` written next to it. The library's parsers and writers of
the leaves work on byte slices `&[U8; N]` and `&mut [U8; N]` for every `N < 2 ^ 64`. A parser
takes the position by `&mut`, returns whether the bytes from the position parse, and its contract
is `Parsed f (Slots.bytes s s.len.toNat) pos result pos' v`: when `f.parse` of the bytes from `pos`
gives a value, the result is true, `pos'` is the position after the value and `v` is the value,
and otherwise the result is false and the contract says nothing about the position or the output.
A writer requires room and writes exactly `f.write v` at the
position, leaving the other cells unchanged, which its contract states as `Written f d d' pos pos'
v`.

| function | form | contract |
|---|---|---|
| `getU (&s) pos k big` | `uint k _`, `k ≤ 8` | the integer of the `k` bytes at `pos` |
| `putU (&mut d) pos k big v` | `uint k _` | writes `encUint k _ v` at `pos` |
| `getBytes (&s) pos n (&mut a)` | `n` bytes | the first `n` elements of `a` are the bytes at `pos` |
| `putBytes (&mut d) pos (&a) n` | `n` bytes | writes the first `n` elements of `a` at `pos` |
| `parseUint (&s) (&mut pos) k big (&mut x)` | `uint k _` | `Parsed` |
| `writeUint (&mut d) (&mut pos) k big v` | `uint k _` | `Written` |
| `parseLBytes (&s) (&mut pos) k big max (&mut b)` | `lbytes k _ max` into `LBytes M` | `Parsed`, and `b.len ≤ max` when it returns true |
| `writeLBytes (&mut d) (&mut pos) k big (&b)` | `lbytes k _ _` from `LBytes M` | `Written` |

A record or a union is parsed by a sequence of calls, one per field, that stops at the first that
fails, and its contract is proved from the fields' contracts by `Parsed.pair_cont`,
`Parsed.pair_stop`, `Parsed.union_cont`, `Parsed.union_stop` and `ParsedT.arm_eq`, and for writers
by `Written.pair`, `Written.union` and `WrittenT.arm_eq`. `Tests/FormatKV.lean` has the request
parser and the response writer of a key-value protocol written this way. `Tests/FormatKVSrv.lean`
has a server that uses them, and `Tests/KVRefine.lean` proves that its trace is that of the
abstract key-value store of `Tests/KVSpec.lean`, whose requests and responses are decoded and
encoded by `Fmt.parse reqFmt` and `Fmt.write respFmt`.

