import Millipede.Meta.MpDef

/-!
# Standard units

This module declares two dimensions with their usual units, each scale counted in the finest
unit, bytes or nanoseconds. A program may declare its own with `mp dimension` and `mp unit`.
-/

namespace Millipede.Lib

mp dimension Size
mp unit byte : Size := 1
mp unit KiB : Size := 1024
mp unit MiB : Size := 1048576
/-- A 4 KiB page, the base page size of x64 and arm64. -/
mp unit page : Size := 4096

mp dimension Time
mp unit ns : Time := 1
mp unit us : Time := 1000
mp unit ms : Time := 1000000
mp unit sec : Time := 1000000000

end Millipede.Lib
