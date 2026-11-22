import Millipede.Top.Examples

/-!
# The program `revchunks` at the source level

`revchunks` reads chunks of bytes and writes each chunk reversed. This suite runs it under an
oracle that answers its `read`s with given chunks, and checks that the trace holds each chunk
read, then the same bytes reversed in a `write`, and `exit 0` at the end of input. The bytes land
in the buffer through the extern, a helper reverses them through a slice, and `write` reads them
from the buffer. Adversarial oracles give counts that disagree with the bytes offered, and a
wrong expectation is rejected.
-/

namespace Millipede.Tests.RevChunks
open Millipede Millipede.Examples

/-- Answers the `k`-th `read` with chunk `k` and its length as the count, with 0 after the last
chunk, and every other call with 0. -/
def chunks (cs : List (List UInt8)) : Oracle :=
  ⟨fun hist c =>
    if c.sym = "read" then
      match cs[(hist.filter (·.sym == "read")).length]? with
      | some bs => ⟨UInt64.ofNat bs.length, [bs]⟩
      | none => ⟨0, []⟩
    else ⟨0, []⟩⟩

/-- The bytes each `write` event carried, in order. -/
def written (es : List Event) : List (List UInt8) :=
  es.filterMap fun e => if e.sym = "write" then e.bytesIn.head? else none

/-- The trace ends with `exit c`. -/
def exited (c : UInt64) (es : List Event) : Bool :=
  match es.getLast? with
  | some e => e.sym == "exit" && e.args == [c]
  | none => false

#guard written (revProg.events (chunks [[1, 2, 3, 4], [5, 6], [7]]) 5) = [[4, 3, 2, 1], [6, 5], [7]]
#guard exited 0 (revProg.events (chunks [[1, 2, 3, 4], [5, 6], [7]]) 5)
#guard written (revProg.events (chunks []) 3) = []
#guard exited 0 (revProg.events (chunks []) 3)
/-- Answers the first `read` with the count `k` and the bytes `bs`, which need not agree with it,
and the other calls with 0. -/
def liar (k : UInt64) (bs : List UInt8) : Oracle :=
  ⟨fun hist c =>
    if c.sym = "read" ∧ (hist.filter (·.sym == "read")).isEmpty then ⟨k, [bs]⟩ else ⟨0, []⟩⟩

-- With more bytes offered than the count, only the counted ones are used.
#guard written (revProg.events (liar 4 [9, 8, 7, 6, 5, 4]) 3) = [[6, 7, 8, 9]]
-- With more bytes offered than the capacity, only 16 land in the buffer.
#guard written (revProg.events (liar 16 ((List.range 20).map UInt8.ofNat)) 3) =
  [(List.range 16).reverse.map UInt8.ofNat]
-- A full chunk of 16 and an odd one of 9, whose middle byte stays.
#guard written (revProg.events (chunks [(List.range 16).map UInt8.ofNat, (List.range 9).map UInt8.ofNat]) 4) =
  [(List.range 16).reverse.map UInt8.ofNat, (List.range 9).reverse.map UInt8.ofNat]
-- With a count below the bytes offered, the program uses the count.
#guard written (revProg.events (liar 3 [9, 8, 7, 6]) 3) = [[7, 8, 9]]
-- With a count above the capacity, nothing is written.
#guard written (revProg.events (chunks [(List.range 17).map UInt8.ofNat]) 3) = []
-- After a failing read, which returns `-errno`, nothing is written.
#guard written (revProg.events ⟨fun _ c => if c.sym = "read" then ⟨UInt64.ofNat (2 ^ 64 - 9), []⟩ else ⟨0, []⟩⟩ 3) = []
-- A wrong expectation is rejected.
#guard written (revProg.events (chunks [[1, 2]]) 3) != [[1, 2]]

end Millipede.Tests.RevChunks
