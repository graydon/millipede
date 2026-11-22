import Millipede.Lib.Pool
import Millipede.Lib.Bump
import Tests.Link
import Tests.Lower

/-!
# Tests for the arena library

Outside the library's own module, the keys of a pool are sealed. This suite shows that `mp def`
rejects a client that forges a key, retargets it, drops it, burns it, frees it twice or uses it
after `free`. A client `roundTrip` allocates, reads through the fresh key and frees it, and all
its obligations, among them that the pool owns the key, follow automatically from the callees'
contracts, which also give it a contract that keeps the live count.

A reactor `poolProg` allocates with `alloc!` and frees in every step, and its root invariant
proves that the pool is never exhausted, with no hand proof. The reactor is lowered and run in
the Flat interpreter, where the root's bytes match the source's. The suite also runs every
operation of `Pool8`, `Pool100`, `Bump8` and `Buf16` against their specifications, and each
`#guard` that checks a specification has a negated twin that must fail.

The arenas are described in doc/design/arenas.md.
-/

namespace Millipede.Lib

-- Short names for the operations of the instances, which are the generic normal forms applied
-- to the instances' arguments, so that a test can write `Pool8.alloc p v`.
abbrev Pool8.new := Pool.new UInt64 8 1 (by decide) (by decide)
abbrev Pool8.alloc := Pool.alloc UInt64 8 1 (by decide) (by decide)
abbrev Pool8.alloc! := Pool.alloc! UInt64 8 1 (by decide) (by decide)
abbrev Pool8.free := Pool.free UInt64 8 1 (by decide) (by decide)
abbrev Pool8.getIx := Pool.getIx UInt64 8 1 (by decide) (by decide)
abbrev Pool100.new := Pool.new Cell2 100 2 (by decide) (by decide)
abbrev Pool100.alloc := Pool.alloc Cell2 100 2 (by decide) (by decide)
abbrev Pool100.findFree := Pool.findFree Cell2 100 2 (by decide) (by decide)
abbrev Bump8.new := Bump.new UInt64 8 (by decide)
abbrev Bump8.alloc := Bump.alloc UInt64 8 (by decide)
abbrev Bump8.get := Bump.get UInt64 8 (by decide)
abbrev Bump8.reset := Bump.reset UInt64 8 (by decide)
abbrev Buf16.new := Bump.new UInt8 16 (by decide)
abbrev Buf16.alloc := Bump.alloc UInt8 16 (by decide)
abbrev Buf16.get := Bump.get UInt8 16 (by decide)

end Millipede.Lib

namespace Millipede.Tests.Lib

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## Keys are sealed, linear and unforgeable outside the library -/

/-- error: unknown function `Pool8.Key.mint` (not an earlier `mp def` or `mp extern`) -/
#guard_msgs in
mp def forge1 (i : UInt64) : Pool8.Key := Pool8.Key.mint i

/-- error: `Millipede.Lib.Pool.Key` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forge2 (t : LinTok) : Pool8.Key := { idx := 3, tok := t }

/-- error: `Millipede.Lib.Pool.Key` is sealed (its constructor is private to its module): it cannot have its fields written here -/
#guard_msgs in
mp def retarget (k : &mut Pool8.Key) : Unit := do
  k.idx := 5
  ()

/-- error: unused linear parameter `k` of type Millipede.Lib.Pool.Key UInt64 8 1: a linear value must be used exactly once (an arena key: free it with the arena's `free`, or store it, e.g. in `Slots` with `put!`) -/
#guard_msgs in
mp def dropKey (k : Pool8.Key) : Unit := ()

/-- error: unknown function `Pool8.Key.burn` (not an earlier `mp def` or `mp extern`) -/
#guard_msgs in
mp def burnKey (k : Pool8.Key) : Unit := Pool8.Key.burn k

/-- error: linear parameter `k` of type Millipede.Lib.Pool.Key UInt64 8 1 is used 2 times; it must be used exactly once -/
#guard_msgs in
mp def doubleFree (p : &mut Pool8) (k : Pool8.Key) requires p.Inv : UInt64 :=
  let a := Pool8.free (&mut p) k
  let b := Pool8.free (&mut p) k
  a + b

/-- error: use of `k` after it was moved (a linear value is used once) -/
#guard_msgs in
mp def useAfterFree (p : &mut Pool8) (k : Pool8.Key) requires p.Inv : UInt64 :=
  let a := Pool8.free (&mut p) k
  Pool8.get (&p) (&k)

/-- error: linear variable `k` is used 1 time(s) in the then-branch but 0 time(s) in the else-branch; a linear value must be used the same number of times on every path -/
#guard_msgs in
mp def leakOnePath (p : &mut Pool8) (k : Pool8.Key) (c : Bool) requires p.Inv : UInt64 :=
  if c then Pool8.free (&mut p) k else 0

/-! ## A client: access by key cannot fail -/

/-- Allocates, reads through the fresh key and frees it, keeping the invariant and the live
count. The obligations that the pool is valid and owns the key, and the contract, follow from
the callees' contracts, since the contract of `alloc` says that the new state owns the fresh
key. -/
mp def roundTrip (p : &mut Pool8) (v : UInt64) requires p.Inv
    ensures p'.Inv ∧ p'.live = p.live : UInt64 :=
  match Pool8.alloc (&mut p) v with
  | ok k =>
    let x := Pool8.get (&p) (&k)
    let y := Pool8.free (&mut p) k
    x + y
  | err _ => 0

example : ∀ ω w (p : Pool8) (v : UInt64), p.Inv → roundTrip.exp.safe ω (.cons v (.cons p .nil)) w :=
  roundTrip.safe

/-- Takes a reference to the key's cell with no run-time check. `p.Owns k` is the obligation of
`p.slots[i]!`, which `mp def` discharges from `requires`. -/
mp def bumpAt (p : &mut Pool8) (k : &Pool8.Key) requires p.Owns k : Unit := do
  let i := k.idx
  let _ := (do let r := &mut p.slots[i]!; r := r + 1; ())
  ()

example (ω : Oracle) (w : World) (p : Pool8) (k : Pool8.Key) (h : p.Owns k) :
    bumpAt.exp.safe ω (.cons k (.cons p .nil)) w := bumpAt.safe ω w p k h

/-! ## A reactor using a pool, proved never to exhaust it

The contract of `stepR` keeps `live = 0`, and `mp program … invariant` generates the induction
over the reactor's steps, so there is no hand proof. -/

/-- The root, a pool and a counter. -/
structure Root where
  pool : Pool8
  total : UInt64
deriving Data

mp def initR : Root := { pool := Pool8.new, total := 0 }

/-- Each step allocates with `alloc!`, which has no run-time check, frees and counts. The
obligation `live < 8` of `alloc!` comes from the step's `requires` that `live = 0`, and the
obligation of `free` that the pool owns the key comes from the contract of `alloc!`. -/
mp def stepR (r : &mut Root) requires r.pool.Inv ∧ r.pool.live.toNat = 0
    ensures r'.pool.Inv ∧ r'.pool.live.toNat = 0 : Unit := do
  let k := Pool8.alloc! (&mut r.pool) r.total
  let v := Pool8.free (&mut r.pool) k
  r.total := v + 1
  ()

/-- The pool is never exhausted. Every obligation of every reactor step holds, among them the
obligation `live < 8` of `alloc!` that replaces the run-time check, because `live = 0` holds
between steps. -/
mp program poolProg (root : Root) init initR step stepR
  invariant fun r => r.pool.Inv ∧ r.pool.live.toNat = 0

example : poolProg.Safe := poolProg.safe

/-- The counter after `n` steps is `n`. -/
example : (poolProg.run Tests.Core.ω0 5).1.total = 5 := by decide +kernel

/-! ### Lowered -/

open Millipede.Flat in
example : (lower poolProg).toBool = true := by decide +kernel

open Millipede.Flat Millipede.Tests.Lower in
/-- The bytes `64…87` of the lowered reactor's root after `fuel` Flat transitions, which hold
the bitmap, the live count and the counter. The cells' bytes are not compared, because a cell
emptied in `Slots` keeps arbitrary bytes. -/
def loweredRootTail (fuel : Nat) : List UInt8 :=
  rd (nextN κ2 Tests.Core.ω0 fuel (lowerProg poolProg).init).mem 64 24

#guard loweredRootTail 2400 == (Data.encodeBytes (poolProg.run Tests.Core.ω0 2).1).drop 64
-- After 2400 transitions the reactor has done two steps, and its root is not that after three.
#guard loweredRootTail 2400 != (Data.encodeBytes (poolProg.run Tests.Core.ω0 3).1).drop 64

/-! ## Runs of the operations -/

/-- Allocates `vs` in order and returns the indices of the keys, with `none` for `Full`, and the
pool. The keys are dropped, which a test driver in Lean may do. -/
def allocAll8 (p : Pool8) : List UInt64 → List (Option UInt64) × Pool8
  | [] => ([], p)
  | v :: vs =>
    let r := (Pool8.alloc p v).run
    let (is, q) := allocAll8 r.2.1 vs
    ((match r.1 with | .ok k => some k.idx | .error _ => none) :: is, q)

/-- Allocates one value and frees its key at once, returning the index and the value read back,
and the pool. -/
def allocFree8 (p : Pool8) (v : UInt64) : Option (UInt64 × UInt64) × Pool8 :=
  match (Pool8.alloc p v).run with
  | (.ok k, q, _) =>
    let i := k.idx
    let r := (Pool8.free q k).run
    (some (i, r.1), r.2.1)
  | (.error _, q, _) => (none, q)

def full8 : Pool8 := (allocAll8 Pool8.new.run [10, 11, 12, 13, 14, 15, 16, 17]).2

-- Filling gives the indices 0…7 in order and then `Full`, and sets the live count and the
-- bitmap.
#guard (allocAll8 Pool8.new.run [10, 11, 12, 13, 14, 15, 16, 17, 18]).1 ==
  [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, none]
#guard full8.live == 8 && full8.bits.toList == [255]
-- There is no ninth key.
#guard (allocAll8 Pool8.new.run [10, 11, 12, 13, 14, 15, 16, 17, 18]).1.getLast? != some (some 8)
-- Checked access by index returns the stored values, and `err` past the live cells.
#guard (List.range 8).all fun i =>
  match (Pool8.getIx full8 ⟨UInt64.ofNat i⟩).run.1 with
  | .ok v => v == 10 + UInt64.ofNat i | .error _ => false
#guard (match (Pool8.getIx full8 ⟨8⟩).run.1 with | .ok _ => false | .error _ => true)
-- In a round trip in a pool with free cells the value comes back and the live count is kept.
#guard (allocFree8 (allocAll8 Pool8.new.run [1, 2, 3]).2 42).1 == some (3, 42)
#guard (allocFree8 (allocAll8 Pool8.new.run [1, 2, 3]).2 42).2.live == 3
-- `alloc!` on the pool with 3 cells live gives the first free cell.
#guard (Pool8.alloc! (allocAll8 Pool8.new.run [1, 2, 3]).2 9).run.1.idx == 3
-- `roundTrip` returns `v + v` and leaves the live count unchanged.
#guard (roundTrip (allocAll8 Pool8.new.run [1, 2]).2 21).run.1 == 42
#guard (roundTrip (allocAll8 Pool8.new.run [1, 2]).2 21).run.2.1.live == 2
#guard (roundTrip full8 21).run.1 == 0

/-- Fills a `Pool100` with the `n` values `0, 1, …`. -/
def fill100 (n : Nat) : List (Option UInt64) × Pool100 :=
  (List.range n).foldl (fun (acc : List (Option UInt64) × Pool100) i =>
    let r := (Pool100.alloc acc.2 ⟨UInt64.ofNat i, 0⟩).run
    (acc.1 ++ [match r.1 with | .ok k => some k.idx | .error _ => none], r.2.1)) ([], Pool100.new.run)

-- 100 cells across two bitmap words, then `Full`.
#guard (fill100 101).1 == (List.range 100).map (fun i => some (UInt64.ofNat i)) ++ [none]
#guard (fill100 100).2.live == 100
#guard (fill100 100).2.bits.toList == [18446744073709551615, 68719476735]
-- The second word holds 36 bits.
#guard (fill100 100).2.bits.toList != [18446744073709551615, 137438953471]
-- The search crosses the word boundary, so with 70 cells live it finds cell 70, which is bit 6
-- of word 1.
#guard (Pool100.findFree (fill100 70).2).run.1 == 70

/-- Allocates `vs` into a `Bump8` and collects the indices. -/
def bumpAll (b : Bump8) : List UInt64 → List (Option UInt64) × Bump8
  | [] => ([], b)
  | v :: vs =>
    let r := (Bump8.alloc b v).run
    let (is, c) := bumpAll r.2.1 vs
    ((match r.1 with | .ok x => some x.idx | .error _ => none) :: is, c)

#guard (bumpAll Bump8.new.run [5, 6, 7, 8, 9, 10, 11, 12, 13]).1 ==
  [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, none]
#guard (match (Bump8.get (bumpAll Bump8.new.run [5, 6, 7]).2 ⟨1⟩).run.1 with
  | .ok v => v == 6 | .error _ => false)
-- A read past the length, or after `reset`, returns `err`.
#guard (match (Bump8.get (bumpAll Bump8.new.run [5, 6, 7]).2 ⟨3⟩).run.1 with
  | .ok _ => false | .error _ => true)
#guard (match (Bump8.get (Bump8.reset (bumpAll Bump8.new.run [5, 6, 7]).2).run.2.1 ⟨1⟩).run.1 with
  | .ok _ => false | .error _ => true)
-- A byte buffer takes 16 bytes and then returns `Full`.
#guard ((List.range 17).foldl (fun (acc : Nat × Buf16) i =>
    match (Buf16.alloc acc.2 (UInt8.ofNat i)).run with
    | (.ok _, b, _) => (acc.1 + 1, b) | (.error _, b, _) => (acc.1, b)) (0, Buf16.new.run)).1 == 16
#guard (match (Buf16.get ((Buf16.alloc Buf16.new.run 65).run.2.1) ⟨0⟩).run.1 with
  | .ok v => v == 65 | .error _ => false)

end Millipede.Tests.Lib
