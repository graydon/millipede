import Millipede.Meta.FormatGen

/-!
# A key-value protocol over format descriptions

The request `reqFmt` is a two-byte id and a one-byte operation followed by its arm: get (1) and
delete (3) carry a key, put (2) a key and a value. The response `respFmt` is the request's id and
a one-byte status followed by its arm: a value (0), nothing (1) or an error code (2). A key is a
byte string of at most 16 bytes with a one-byte length, and a value one of at most 32 bytes with a
two-byte length.

Each message is a Millipede `structure` and one `mp format` command, which defines the description
(`reqFmt`, `respFmt`), the abstraction (`KReq.toVal`, `KResp.toVal`), the bounds of the byte
strings (`KReq.Bound`, `KResp.Bound`), and the parser `KReq.parseAt` and writer `KResp.writeAt`
(with `KReq.writeAt` and `KResp.parseAt`), whose contracts `Parsed reqFmt` and `Written respFmt`
the command proves.
-/

namespace Millipede.Tests.FormatKV

open Millipede Millipede.Format Std.WP

/-! ## The messages -/

/-- A key: a one-byte length, at most 16, then the bytes. -/
def keyFmt : Fmt := .lbytes 1 .big 16
/-- A value: a two-byte big-endian length, at most 32, then the bytes. -/
def valFmt : Fmt := .lbytes 2 .big 32

/-- A request, as Millipede data. -/
structure KReq where
  id : UInt64
  op : UInt64
  key : LBytes 16
  val : LBytes 32
deriving Data

/-- A request: a two-byte id, then a one-byte operation: 1 get a key, 2 put a key and a value,
3 delete a key. -/
mp format reqFmt for KReq :=
  (id : uint 2 big,
   op : union 1 big
     | 1 => (key : keyFmt)
     | 2 => (key : keyFmt, val : valFmt)
     | 3 => (key : keyFmt))

/-- A response, as Millipede data. -/
structure KResp where
  id : UInt64
  status : UInt64
  val : LBytes 32
  code : UInt64
deriving Data

/-- A response: the request's id, then a one-byte status: 0 a value, 1 nothing, 2 an error
code of one byte. -/
mp format respFmt for KResp :=
  (id : uint 2 big,
   status : union 1 big
     | 0 => (val : valFmt)
     | 1 => ()
     | 2 => (code : uint 1 big))

/-- The descriptions are those written out by hand. -/
example : reqFmt = .pair (.uint 2 .big)
    (.union 1 .big (.arm 1 keyFmt (.arm 2 (.pair keyFmt valFmt) (.arm 3 keyFmt .noArm)))) := rfl
example : respFmt =
    .pair (.uint 2 .big) (.union 1 .big (.arm 0 valFmt (.arm 1 .unit (.arm 2 (.uint 1 .big) .noArm)))) :=
  rfl

/-- Both messages are canonical, so no two byte strings parse to the same request or response. -/
theorem reqFmt_canonical : reqFmt.canonical = true := rfl
theorem respFmt_canonical : respFmt.canonical = true := rfl

example {bs bs' : List UInt8} {v : Val} {r : List UInt8} (h : reqFmt.parse bs = some (v, r))
    (h' : reqFmt.parse bs' = some (v, r)) : bs = bs' := Fmt.parse_injective reqFmt_canonical h h'

end Millipede.Tests.FormatKV
