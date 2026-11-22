import Millipede.Format.Theorems

/-!
# Format descriptions: the model on concrete messages

Runs of `Fmt.parse`, `Fmt.write` and `Fmt.check` (Millipede/Format/Model.lean) on a description
with every form: both byte orders, a fixed array, a constant, ignored bytes, a length-prefixed
string, a bounded repetition and a tagged union. The checks are by `#guard` (compiled evaluation)
and by `decide` (kernel reduction, so the definitions reduce in proofs). Malformed inputs are
rejected: a short input, a length over its bound, a count over its bound, an unknown tag, a wrong
constant.

Teeth: `swapped` is the description with one byte order flipped, a seeded bug, and the checks
show that it reads the sample differently; `lbytesOff` is a parser with an off-by-one length bound
(`n < max` for `n ≤ max`), and the check that it agrees with `Fmt.parse` on the samples fails.
-/

namespace Millipede.Tests.Format

open Millipede.Format

/-- A message with every form. -/
def msg : Fmt :=
  .pair (.const [0x4d, 0x50])                               -- magic "MP"
  (.pair (.uint 2 .big)                                      -- id, big-endian
  (.pair (.uint 4 .little)                                   -- a word, little-endian
  (.pair (.skip 1)                                           -- a padding byte
  (.pair (.bytes 2)                                          -- two raw bytes
  (.pair (.lbytes 1 .big 4)                                  -- a name of at most 4 bytes
  (.pair (.array 1 .big 3 (.uint 1 .big))                    -- at most 3 one-byte numbers
    (.union 1 .big (.arm 1 (.uint 2 .little) (.arm 2 .unit .noArm)))))))))  -- a tagged union

/-- A value of `msg`. -/
def v0 : Val :=
  .pair .unit (.pair (.num 0x0102) (.pair (.num 0x0a0b0c0d) (.pair .unit (.pair (.bytes [7, 8])
    (.pair (.bytes [65, 66]) (.pair (.pair (.num 5) (.pair (.num 6) .unit))
      (.tag 1 (.num 0x3344))))))))

/-- The bytes of `v0`, written out by hand. -/
def b0 : List UInt8 :=
  [0x4d, 0x50, 0x01, 0x02, 0x0d, 0x0c, 0x0b, 0x0a, 0, 7, 8, 2, 65, 66, 2, 5, 6, 1, 0x44, 0x33]

#guard msg.ok v0
#guard msg.write v0 == b0
#guard msg.parse b0 == some (v0, [])
#guard msg.parse (b0 ++ [9, 9]) == some (v0, [9, 9])
#guard msg.check (b0 ++ [9]) == some [9]
#guard msg.maxSize == 2 + 2 + 4 + 1 + 2 + 5 + 4 + 3
#guard (msg.write v0).length ≤ msg.maxSize
-- the kernel reduces the definitions
example : msg.parse b0 = some (v0, []) := by decide
example : msg.write v0 = b0 := by decide
-- `skip` makes `msg` deliberately not canonical: another padding byte parses to the same value
#guard !msg.canonical
#guard msg.parse (b0.set 8 0xff) == some (v0, [])
#guard (Fmt.pair (.uint 2 .big) (.lbytes 1 .big 4)).canonical

/-- Malformed inputs. -/
def bad : List (List UInt8) :=
  [ b0.take 19,                       -- short
    b0.set 0 0x4e,                    -- wrong constant
    b0.set 11 5,                      -- name length 5 > 4
    b0.set 14 4,                      -- count 4 > 3
    b0.set 17 3,                      -- no arm for tag 3
    [] ]

#guard bad.all fun bs => msg.parse bs == none && !msg.valid bs
-- a wrong expectation fails
#guard msg.parse b0 != some (v0, [0])
#guard msg.write v0 != b0.reverse

/-- The tag 2 arm: the union is the last field, so the message is two bytes shorter. -/
def v2 : Val := match v0 with
  | .pair a (.pair b (.pair c (.pair d (.pair e (.pair f (.pair g _)))))) =>
    .pair a (.pair b (.pair c (.pair d (.pair e (.pair f (.pair g (.tag 2 .unit)))))))
  | v => v
#guard msg.parse (msg.write v2) == some (v2, []) && (msg.write v2).length + 2 == b0.length
-- a value that is not a value of `msg`: a name of 5 bytes
#guard !msg.ok (match v0 with
  | .pair a (.pair b (.pair c (.pair d (.pair e (.pair _ r))))) =>
    .pair a (.pair b (.pair c (.pair d (.pair e (.pair (.bytes [1, 2, 3, 4, 5]) r)))))
  | v => v)

/-! ## Seeded bugs -/

/-- `msg` with the id read little-endian. -/
def swapped : Fmt := match msg with
  | .pair m (.pair _ r) => .pair m (.pair (.uint 2 .little) r)
  | f => f
#guard swapped.parse b0 != msg.parse b0

/-- A hand-written parser of `lbytes 1 big max` with an off-by-one bound. -/
def lbytesOff (max : Nat) (bs : List UInt8) : Option (Val × List UInt8) :=
  match bs with
  | n :: r => if n.toNat < max ∧ n.toNat ≤ r.length then some (.bytes (r.take n.toNat), r.drop n.toNat)
    else none
  | [] => none

/-- Samples for the length-prefixed string, every length up to one past the bound. -/
def lsamples : List (List UInt8) := (List.range 6).map fun n => UInt8.ofNat n :: List.replicate n 7

#guard !(lsamples.all fun bs => lbytesOff 4 bs == (Fmt.lbytes 1 .big 4).parse bs)
#guard lsamples.all fun bs => (Fmt.lbytes 1 .big 4).parse bs ==
  (match bs with
   | n :: r => if n.toNat ≤ 4 ∧ n.toNat ≤ r.length then some (.bytes (r.take n.toNat), r.drop n.toNat)
     else none
   | [] => none)

end Millipede.Tests.Format
