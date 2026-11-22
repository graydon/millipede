# Arenas

An arena is a value that holds many values of one type in cells, which it hands out to the
program as it runs. Arenas are library code written in Millipede over the type `Slots`, and a
program usually keeps its arenas in the root. Each arena is generic over the type of its cells,
which may be any type whose values may be copied, and over their number, so its operations and
their contracts are proved once for every such type and capacity. This document builds on
[language.md](language.md) and [memory.md](memory.md).

## Slots

A value of type `Slots T n` is a row of `n` cells, each of which is either empty or holds a value
of type `T`. The running program keeps no record of which cells are full, which is known only to
proofs, so each operation on a cell carries an obligation. `s.put! i v` stores `v` in cell `i`,
which must be empty, and `s.take! i` empties cell `i`, which must be full, and returns its value.
`s[i]!` reads a full cell, and `Slots.empty n` is a value whose cells are all empty.

## Pool arenas

A pool arena hands out cells and takes them back. `alloc` stores a value in a free cell and
returns a key that names the cell, and `free` takes the key back and returns the value. A key is
linear and only `alloc` can create one, so each key is freed at most once, and the checker
rejects a use of a key after `free`.

Access through a key, with `get` or `set`, is not tested when the program runs. Instead it
carries the obligation `p.Owns k`, which says that the cell of key `k` in arena `p` is full. A pool
also gives copyable indices, made from a key with `ix`, and access through an index with `getIx`
is tested when the program runs and returns a `Result`.

The type `Pool T n W` is a pool of `n` cells of type `T`. The pool records which of its cells are
full in a bitmap of `W` words, so `n` may be at most `64 * W`. The library names two pools,
`Pool8 := Pool UInt64 8 1` and `Pool100 := Pool Cell2 100 2`.

## Bump arenas

A bump arena hands out cells in order and takes none back until `reset` empties the whole arena.
Its indices are ordinary copyable values. `get` reads through an index and tests it when the
program runs, and `get!` carries the obligation that the index is below the number of cells
handed out. Right after `reset` that number is zero, so the obligation cannot be proved for any
index. After further allocations an old index may be in range again, and it then reads the new
value in its cell.

The type `Bump T n` is a bump arena of `n` cells of type `T`. The library names `Bump8`, of eight
words, and `Buf16`, of sixteen bytes.

## Running out of space

An arena has a fixed number of cells and can run out of them. `alloc` returns `err` when the arena
is full, and `alloc!` carries the obligation that it is not full, so it makes no such test.

## Keys and their types

The type of a key carries the parameters of its arena, so a pool's key has the type
`Pool.Key T n W` and a bump arena's index the type `Bump.Ix T n`. A key of one arena given to an
arena with other parameters is therefore a type error. In the following function, from a test,
the call to `Pool100.free` is rejected because `k` is a key of a `Pool8`:

```lean
mp def mixInst (a : &mut Pool8) (b : &mut Pool100) (k : Pool8.Key) requires a.Inv ∧ a.Owns k :
    Cell2 :=
  Pool100.free (&mut b) k
```

Two arenas with the same parameters share a key type, so the type does not tell their keys
apart. The obligation `p.Owns k` says only that the key's cell in `p` is full, and a program
shows it from its own record of which keys it holds in which arena.

## Keeping keys

A program that keeps keys from one step to the next stores them in its root, usually as a stack
in a `Slots` value, and states in its root invariant that it holds them. The library states this
once for every arena. `A.Holds s ks` says that the keys in the list `ks` are distinct, are all
owned by the arena `s`, and are as many as the cells in use. `A.KeyStack s keys n` says the same
of the first `n` cells of the `Slots` value `keys`. With either in the invariant, the obligations
of `alloc!` and `free` follow from the contracts of the arena's operations.

Both kinds of arena implement the allocator interface `Alloc`, so a program written against the
interface works with either of them. Interfaces are described in [modules.md](modules.md).

## Byte buffers

A byte buffer `ByteBuf cap` is an array of `cap` bytes together with the number of bytes it
holds, `len`, which is never more than `cap`. Its contents are used in place as slices of the
array. The bytes held are the slice `&b.bytes[0..b.len]`, and the free space is the slice
`&mut b.bytes[b.len..cap]`. `push!` appends a byte and `clear` empties the buffer. `readFrom`
reads from a file into the free space and `writeTo` writes the bytes held to a file, while
`append` copies a slice into the free space and `reverse` reverses the bytes held.
