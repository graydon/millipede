import Millipede.Lib.ByteBuf
import Millipede.Top.Sound
import Tests.RevChunks

/-!
# Tests of the I/O byte buffer

`catProg` is `cat` through a `ByteBuf`. Each step forgets the bytes it holds, reads up to 16 bytes
into the free space through a mutable slice, and writes the bytes it holds through a shared
slice. It exits with 0 at the end of input and with 1 on an error. The tests prove its
obligations and check that `compile` accepts it, so the soundness theorem of `compile` covers its
machine code. They also check its source trace under oracles that answer with given chunks or
adversarially, and that a wrong expectation is rejected.
-/

namespace Millipede.Tests.ByteBuf
open Millipede.Tests.RevChunks (chunks written exited)

open Millipede Millipede.Lib

mp extern noreturn "exit" bbExit (code : UInt64) : UInt64

/-- One step of `cat` through the buffer. -/
mp def catStep (b : &mut ByteBuf 16) : Unit := do
  b.len := 0
  let r := ByteBuf.readFrom (&mut b) 0
  if r == 0 then
    let _x := bbExit 0
    ()
  else if r <= 16 then
    let _w := ByteBuf.writeTo (&b) 1
    ()
  else
    let _x := bbExit 1
    ()

/-- The step's obligations are the precondition of `readFrom`, which holds since `len = 0 ≤ 16`
after the reset, and that of `writeTo`, the invariant, which the contract of `readFrom` keeps
whatever the oracle answers. -/
mp prove catStep.safe := by mp_auto [ByteBuf.Inv]

/-- The empty buffer: the library's `ByteBuf.new` at capacity 16. -/
mp def catInit : ByteBuf 16 := ByteBuf.new

mp program catProg (root : ByteBuf 16) init catInit step catStep

example : catProg.Safe := catProg.safe

#guard (compile catProg x64Linux).toBool

-- the oracle `chunks` and the trace readers `written` and `exited` come from `Tests/RevChunks.lean`

#guard written (catProg.events (chunks [[1, 2, 3], [4], (List.range 16).map (·.toUInt8)]) 5) =
  [[1, 2, 3], [4], (List.range 16).map (·.toUInt8)]
#guard exited 0 (catProg.events (chunks [[1, 2, 3], [4]]) 5)
-- more bytes offered than the free space: only 16 land in the buffer
#guard written (catProg.events ⟨fun hist c => if c.sym = "read" ∧ hist.isEmpty then
    ⟨16, [(List.range 20).map (·.toUInt8)]⟩ else ⟨0, []⟩⟩ 3) = [(List.range 16).map (·.toUInt8)]
-- a count above the free space is an error, so nothing is written and the program exits with 1
#guard exited 1 (catProg.events (chunks [(List.range 17).map (·.toUInt8)]) 3)
#guard written (catProg.events (chunks [(List.range 17).map (·.toUInt8)]) 3) = []
-- a wrong expectation is rejected
#guard written (catProg.events (chunks [[1, 2]]) 3) != [[2, 1]] ∧
  written (catProg.events (chunks [[1, 2]]) 3) == [[1, 2]]

end Millipede.Tests.ByteBuf
