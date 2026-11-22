import Tests.A64Select

/-!
# arm64 runs of loops

These tests select loop terms for arm64 and run them on the arm64 model. Their result bytes and
events agree with the Lin interpreter, and a wrong sum is noticed.
-/

namespace Millipede.Tests.A64Select

open Millipede Millipede.Flat Millipede.Tests.Core Millipede.Tests.Select
  Millipede.Tests.Lower Millipede.Tests.Lin

#guard let r := a64Run ω0 (sumTo 10) .nil 30000
  r == linRes ω0 (sumTo 10) .nil 10000 && r.map (·.1) == some (Data.encodeBytes (45 : UInt64))
#guard (a64Run ω0 (sumTo 10) .nil 30000).map (·.1) != some (Data.encodeBytes (44 : UInt64))
#guard a64Run ω0 sumWhile .nil 30000 == linRes ω0 sumWhile .nil 10000
#guard a64Run ω0 resLoop .nil 30000 == linRes ω0 resLoop .nil 10000

end Millipede.Tests.A64Select
