/-!
# SplitMix64, the pseudo-random generator of the differential and co-simulation drivers
-/

namespace Millipede.Tests

/-- One SplitMix64 step, returning the next state and the output. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

end Millipede.Tests
