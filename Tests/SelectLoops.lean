import Tests.Select

/-!
# x64 runs of loops

These are term tests in the manner of `Tests/Select.lean`, for loops. Each machine run is slow
even compiled, because a loop runs thousands of instructions in the x64 model, so they sit in a
module of their own that builds in parallel with the suites that import `Tests.Select`.
-/

namespace Millipede.Tests.Select

open Millipede Millipede.Flat Millipede.Lin Millipede.X64 Millipede.Tests.Core
  Millipede.Tests.Lower Millipede.Tests.Lin

-- One machine run serves both checks of `sumTo 10`.
#guard let r := x64Run 0 ω0 (sumTo 10) .nil 30000
  r == linRes ω0 (sumTo 10) .nil 10000 && r.map (·.1) == some (Data.encodeBytes (45 : UInt64))
#guard x64Run 0 ω0 sumWhile .nil 30000 == linRes ω0 sumWhile .nil 10000
#guard x64Run 0 ω0 resLoop .nil 30000 == linRes ω0 resLoop .nil 10000

end Millipede.Tests.Select
