import Millipede.Meta.MpDef
import Millipede.Top.Sound

/-!
# A ring buffer, generic over its element type and size

`Ring T n` is a structure with a type and a size parameter. `Ring.new`, `Ring.size`,
`Ring.push` and `Ring.pop` are `mp def`s under `variable (T : Type) … (n : Nat)`, each with a
contract proved once for every `T` and `n < 2 ^ 64`. The index arithmetic is modular, as in
`(head + len) % n`. Every obligation and contract is proved by the automatic attempt of
`mp def`, because the default facts of `mp_auto` include `x % n < n` for `0 < n`.

The reactor `rings` holds two instances, `Ring UInt64 4` and `Ring UInt8 3`, in one root. Its
initial root is a struct literal whose fields `Ring.new 0` get their type and size from the
field types. Its obligations are proved, its source trace is checked on two inputs and differs
on a third, and it compiles for x64 and arm64.
-/

namespace Millipede.Tests.Ring

open Millipede Std.WP

set_option experimental.vcgen true

/-- A ring buffer of `n` cells of `T`, with the cells, the first element's cell and the count. -/
structure Ring (T : Type) (n : Nat) where
  buf : Arr T n
  head : UInt64
  len : UInt64
deriving Data

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
include hn

/-- The invariant, that the head is a cell and at most `n` elements are held. -/
def Ring.Inv (r : Ring T n) : Prop := r.head.toNat < n ∧ r.len.toNat ≤ n

/-- The empty ring, with its cells filled with `v`. -/
mp def Ring.new (v : T) ensures result.head = 0 ∧ result.len = 0 : Ring T n :=
  { buf := Vector.replicate n v, head := 0, len := 0 }

/-- The number of elements held. -/
mp def Ring.size (r : &Ring T n) ensures result = r.len : UInt64 := r.len

/-- Appends `v` after the last element. -/
mp def Ring.push (r : &mut Ring T n) (v : T) requires Ring.Inv T n r ∧ r.len.toNat < n
    ensures Ring.Inv T n r' ∧ r'.len.toNat = r.len.toNat + 1 : Unit := do
  let i := (r.head + r.len) % n
  r.buf[i]! := v
  r.len := r.len + 1

/-- Removes and returns the first element. -/
mp def Ring.pop (r : &mut Ring T n) requires Ring.Inv T n r ∧ 0 < r.len.toNat
    ensures Ring.Inv T n r' ∧ r'.len.toNat + 1 = r.len.toNat : T := do
  let v := r.buf[r.head]!
  r.head := (r.head + 1) % n
  r.len := r.len - 1
  v

set_option mp.autoSafe false in
/-- The first element, without removing it. Its obligations are proved below with `mp prove`, for
`Ring.peek` by plain `mp_safe` and for its copy `Ring.peek2` by `mp_auto`. -/
mp def Ring.peek (r : &Ring T n) requires Ring.Inv T n r : T := r.buf[r.head]!

set_option mp.autoSafe false in
mp def Ring.peek2 (r : &Ring T n) requires Ring.Inv T n r : T := r.buf[r.head]!

mp prove Ring.peek.safe := by intros; mp_safe [Ring.Inv]
mp prove Ring.peek2.safe := by mp_auto

-- The automatic attempt of `mp def` proved the obligations and contracts.
example := @Ring.push.safe
example := @Ring.push.spec
example := @Ring.pop.safe
example := @Ring.pop.spec

end

/-! ## A reactor using two instances -/

mp extern "read" rRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern "write" rWrite (fd : UInt64) (buf : &[U8]) : UInt64
mp extern noreturn "exit" rExit (code : UInt64) : UInt64

/-- The root, with a ring of words, a ring of bytes, an output byte and a total. -/
structure Root where
  words : Ring UInt64 4
  bytes : Ring UInt8 3
  out : Arr UInt8 1
  sum : UInt64
deriving Data

/-- Both rings' invariants. -/
def RootInv (r : Root) : Prop := Ring.Inv UInt64 4 r.words ∧ Ring.Inv UInt8 3 r.bytes

/-- The empty root, in which `Ring.new 0` is instantiated at `UInt64, 4` and at `UInt8, 3` from
the field types. -/
mp def rInit ensures RootInv result : Root :=
  { words := Ring.new 0, bytes := Ring.new 0, out := Vector.replicate 1 0, sum := 0 }

/-- Reads one byte and remembers it in both rings, dropping the oldest when a ring is full. At
the end of input it prints the oldest remembered byte and exits with the oldest remembered word. -/
mp def rStep (r : &mut Root) requires RootInv r ensures RootInv r' : Unit := do
  let c := rRead 0
  if c >= 256 then
    if 0 < r.bytes.len then
      r.out[0] := Ring.pop (&mut r.bytes)
      let _w := rWrite 1 (&r.out[0..1])
    let mut s := 0
    if 0 < r.words.len then
      s := Ring.pop (&mut r.words)
    let _x := rExit s
  else
    if r.words.len == 4 then
      let _d := Ring.pop (&mut r.words)
    Ring.push (&mut r.words) c
    if r.bytes.len == 3 then
      let _d := Ring.pop (&mut r.bytes)
    Ring.push (&mut r.bytes) c.toUInt8

mp program rings (root : Root) init rInit step rStep invariant RootInv

example : rings.Safe := rings.safe

/-- The input of `k` bytes `a, b, …`, followed by the end of input. -/
def letters (k : Nat) : Oracle :=
  ⟨fun h c => if c.sym = "read" ∧ h.length < k then ⟨1, [[(97 + h.length).toUInt8]]⟩ else ⟨0, []⟩⟩

-- With six bytes `a … f`, the byte ring keeps `d e f` and prints `d`, and the word ring keeps
-- `c d e f`, so the exit status is `c`, 99.
#guard (rings.events (letters 6) 7).map (·.sym) = ["read", "read", "read", "read", "read", "read",
  "read", "write", "exit"]
#guard (rings.events (letters 6) 7).getLast?.map (·.args) = some [99]
#guard ((rings.events (letters 6) 7).find? (·.sym == "write")).map (·.bytesIn) = some [[100]]
-- With two bytes nothing is dropped.
#guard (rings.events (letters 2) 3).getLast?.map (·.args) = some [97]
-- The reactor compiles for each target.
#guard (compile rings x64Linux).isOk && (compile rings arm64Linux).isOk
-- Another input gives another trace.
#guard (rings.events (letters 6) 7) != rings.events (letters 5) 6

end Millipede.Tests.Ring
