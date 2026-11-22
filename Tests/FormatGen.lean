import Millipede.Meta.FormatGen

/-!
# A generated format with every form

A batch message: a constant, a nested header (a version, a skipped byte, four bytes), then an
array of up to three items, each a union of three arms followed by a length-prefixed name. `mp format` generates the parsers, writers and validators of both structures,
with their contracts proved.
-/

namespace Millipede.Tests.FormatGen

open Millipede Millipede.Format Std.WP

/-- An item: a one-byte kind (0 nothing, 1 a four-byte little-endian number, 2 a two-byte code),
then a name of at most 8 bytes. -/
structure Item where
  kind : UInt64
  num : UInt64
  code : UInt64
  name : LBytes 8
deriving Data, Inhabited

mp format itemFmt for Item :=
  (kind : union 1 big
     | 0 => ()
     | 1 => (num : uint 4 little)
     | 2 => (code : uint 2 big),
   name : lbytes 1 big 8)

/-- A header: a one-byte version, a byte of padding and a four-byte sender id. -/
structure Hdr where
  ver : UInt64
  sender : Arr UInt8 4
deriving Data

mp format hdrFmt for Hdr :=
  (ver : uint 1 big,
   _ : skip 1,
   sender : bytes 4)

/-- A batch: the magic bytes `MP`, a header, then at most three items with a one-byte count. -/
structure Batch where
  hdr : Hdr
  items : Seq Item 3
deriving Data

mp format batchFmt for Batch :=
  (_ : const [0x4d, 0x50],
   hdr : Hdr,
   items : array 1 big 3 Item)

/-! ## The generated descriptions and abstractions

The descriptions and abstractions are those written out by hand from the text above, so the
generator put each part of the message in the field the text names. -/

example : itemFmt = .pair
    (.union 1 .big (.arm 0 .unit (.arm 1 (.uint 4 .little) (.arm 2 (.uint 2 .big) .noArm))))
    (.lbytes 1 .big 8) := rfl
example : hdrFmt = .pair (.uint 1 .big) (.pair (.skip 1) (.bytes 4)) := rfl
example : batchFmt = .pair (.const [0x4d, 0x50]) (.pair hdrFmt (.array 1 .big 3 itemFmt)) := rfl
example : Item.toVal = fun r => .pair
    (.tag r.kind.toNat (if r.kind.toNat = 0 then .unit else if r.kind.toNat = 1 then .num r.num.toNat
      else if r.kind.toNat = 2 then .num r.code.toNat else .unit))
    r.name.toVal := rfl
example : Hdr.toVal = fun r => .pair (.num r.ver.toNat) (.pair .unit (.bytes (r.sender.toList.take 4))) :=
  rfl
example : Batch.toVal = fun r => .pair .unit (.pair r.hdr.toVal (Seq.toValWith Item.toVal r.items)) :=
  rfl

/-! ## Round trips by evaluation -/

/-- A batch of three items, with the padding byte 7. -/
def sample : List UInt8 :=
  [0x4d, 0x50, 2, 7, 0, 1, 2, 3, 3,
   0, 1, 0x61,
   1, 0x78, 0x56, 0x34, 0x12, 0,
   2, 0x01, 0x02, 2, 0x68, 0x69]

/-- The same batch with the padding written as zero. -/
def sampleCanon : List UInt8 := sample.set 3 0

#guard (batchFmt.parse (sample ++ [9])).map (fun (v, r) => (batchFmt.write v, r)) ==
  some (sampleCanon, [9])
#guard (batchFmt.parse sampleCanon).map (fun (v, r) => (batchFmt.write v, r)) ==
  some (sampleCanon, [])
#guard batchFmt.check sample == some []
-- A count of four is above the bound, and a kind of 3 has no arm.
#guard batchFmt.parse (sample.set 8 4) == none
#guard batchFmt.parse (sample.set 9 3) == none

end Millipede.Tests.FormatGen
