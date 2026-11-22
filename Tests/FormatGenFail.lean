import Millipede.Meta.FormatGen

/-!
# `mp format` rejects what it cannot prove

A description that disagrees with its structure is rejected before anything is generated, and a
generator that emits wrong code (the test-only option `mp.format.seedBug`) makes the contract
proof fail, which stops the command.
-/

namespace Millipede.Tests.FormatGenFail

open Millipede Millipede.Format

structure R where
  id : UInt64
  tag : UInt64
  name : LBytes 8
deriving Data

-- A width out of range.
/-- error: mp format: `uint 9` for `id`: an integer has 1 to 8 bytes -/
#guard_msgs in
mp format r1 for R := (id : uint 9 big, tag : union 1 big | 0 => (name : lbytes 1 big 8))

-- A byte string longer than its field holds.
/--
error: mp format: the field `name` of `Millipede.Tests.FormatGenFail.R` has type `LBytes 8`, but a byte string of at most 9 bytes does not fit in `LBytes 8`
-/
#guard_msgs in
mp format r2 for R := (id : uint 2 big, tag : union 1 big | 0 => (name : lbytes 1 big 9))

-- An integer read into a byte string.
/--
error: mp format: the field `name` of `Millipede.Tests.FormatGenFail.R` has type `LBytes 8`, but `uint 2` needs `UInt64`
-/
#guard_msgs in
mp format r3 for R := (id : uint 2 big, tag : union 1 big | 0 => (name : uint 2 big))

-- A field the structure does not have.
/--
error: mp format: `Millipede.Tests.FormatGenFail.R` has no field `nam` (the description reads `lbytes 1 _ 8` into it)
-/
#guard_msgs in
mp format r4 for R := (id : uint 2 big, tag : union 1 big | 0 => (nam : lbytes 1 big 8))

-- A field of the structure the description does not fill.
/-- error: mp format: the field `name` of `Millipede.Tests.FormatGenFail.R` is not in the description -/
#guard_msgs in
mp format r5 for R := (id : uint 2 big, tag : union 1 big | 0 => ())

-- An arm tag that does not fit in the tag's width.
/-- error: mp format: the arm tag 256 of `tag` does not fit in 1 byte(s) -/
#guard_msgs in
mp format r6 for R := (id : uint 2 big, tag : union 1 big | 256 => (name : lbytes 1 big 8))

-- Two arms with one tag.
/-- error: mp format: the arm tag 0 of `tag` appears twice; the second arm would never be used -/
#guard_msgs in
mp format r7 for R :=
  (id : uint 2 big, tag : union 1 big | 0 => (name : lbytes 1 big 8) | 0 => ())

-- A field filled twice on one path.
/-- error: mp format: the field `id` is filled twice on one path through the description -/
#guard_msgs in
mp format r8 for R :=
  (id : uint 2 big, tag : union 1 big | 0 => (id : uint 1 big, name : lbytes 1 big 8))

-- The seeded bug 1: the first integer is read in the other byte order.
/--
error: mp format: the proof of the parser's contract `Millipede.Tests.FormatGenFail.R.parseAt.spec` failed, so the description is not accepted (no step of the walk over the description proves this goal)
-/
#guard_msgs in
set_option mp.format.seedBug 1 in
mp format r9 for R :=
  (id : uint 2 big, tag : union 1 big | 0 => (name : lbytes 1 big 8) | 1 => ())

-- Nothing of a rejected description is left.
/-- error: Unknown constant `Millipede.Tests.FormatGenFail.R.parseAt` -/
#guard_msgs in
#check R.parseAt
/-- error: Unknown identifier `r9` -/
#guard_msgs in
#check r9

-- The seeded bug 2: each arm of the union has the code of the next arm.
/--
error: mp format: the proof of the parser's contract `Millipede.Tests.FormatGenFail.R.parseAt.spec` failed, so the description is not accepted (no step of the walk over the description proves this goal)
-/
#guard_msgs in
set_option mp.format.seedBug 2 in
mp format r10 for R :=
  (id : uint 2 big, tag : union 1 big | 0 => (name : lbytes 1 big 8) | 1 => ())

-- Without a seeded bug the same description is accepted.
mp format r11 for R :=
  (id : uint 2 big, tag : union 1 big | 0 => (name : lbytes 1 big 8) | 1 => ())

end Millipede.Tests.FormatGenFail
