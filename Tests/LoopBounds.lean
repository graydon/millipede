import Millipede.Meta.MpDef
import Millipede.Meta.Report
import Millipede.Meta.Emit

/-!
# Tests for loops of large literal bounds

`mp def` proves the normal-form equation `f.exp_run` or `f.exp_denoteM` with every loop bound and
every callee abstracted, and applies the proof to them, so the kernel's check of the equation
does not evaluate a loop and its cost does not depend on the bounds (`normalFormOfExp` in
Millipede/Meta/Elab.lean). Before, a loop of 2048 iterations or more failed with
"(kernel) deep recursion detected". Each function below has a loop of a large literal bound or
calls one, and this module builds only if each equation is checked: at 2^20 and 2^32 iterations
an evaluation by the kernel would not finish. The effectful pair `pureL`/`effL` at 2048 and 4096
iterations are the audit's reproductions (scratch/audit/reach/Loop2048.lean, Loop4096.lean).
-/

namespace Millipede.Tests.LoopBounds

open Millipede

mp extern "write" w (fd : UInt64) (buf : Bytes) : UInt64

/-! ## Pure and effectful loops, and a caller of both inside a loop of its own, at each bound -/

namespace L10
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...10 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...10 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...10 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L10

namespace L2048
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...2048 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...2048 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...2048 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L2048

namespace L4096
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...4096 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...4096 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...4096 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L4096

namespace L65536
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...65536 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...65536 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...65536 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L65536

namespace L1M
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...1048576 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...1048576 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...1048576 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L1M

namespace L4G
mp def pureL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...4294967296 do
    a := a * 3 + i
  a
mp def effL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...4294967296 do
    if a == i then
      let _w := w 1 "x"
    a := a + 1
  a
mp def callsL (x : UInt64) : UInt64 := do
  let y := pureL x
  let mut a := y
  for i in 0...4294967296 do
    if i == 5 then break
    a := effL a
  a
example := @callsL.exp_denote
example := @callsL.safe
end L4G

/-! ## A bound that is a size parameter -/
section
variable (n : Nat)
mp def sizeL (x : UInt64) : UInt64 := do
  let mut a := x
  for i in 0...n do
    a := a * 3 + i
  a
end
example := @sizeL.exp_run
example := @sizeL.safe

/-! ## A program whose step runs a loop of 2^20 iterations that stops early, whose
safety proof `#audit` accepts -/
mp extern noreturn "exit" ex (code : UInt64) : UInt64
mp def bInit : UInt64 := 0
mp def bStep (s : &mut UInt64) : Unit := do
  let mut k : UInt64 := 0
  for i in 0...1048576 do
    if i == 3 then break
    k := k + i
  s := s + k
  if s > 9 then
    let _x := ex 0
    ()
mp program big (root : UInt64) init bInit step bStep

/-- info: #audit: 1 declarations checked, no incomplete proofs, no user axioms -/
#guard_msgs in
#audit big.safe

/-! ## Functions without a normal form

`set_option mp.normalForm false` skips `f` and its equations. Such a function is still found by
name, so a caller declared under the same option and a program over it are accepted, and a
caller with a normal form is refused with the reason (scratch/audit/reach/InBug.lean,
InBug2.lean). -/

set_option mp.normalForm false in
mp def noNf (x : UInt64) : UInt64 := x + 1

/-- error: `Millipede.Tests.LoopBounds.noNf` has no normal form (declared under `set_option mp.normalForm false`), so `withNf` cannot have one: set the option for `withNf` too -/
#guard_msgs in
mp def withNf (x : UInt64) : UInt64 := noNf x

section
set_option mp.normalForm false
mp def alsoNoNf (x : UInt64) : UInt64 := noNf x
mp def nInit : Unit := ()
mp def nStep (u : &mut Unit) : Unit := do
  let _x := ex (alsoNoNf 41)
  ()
end
mp program noNfProg (root : Unit) init nInit step nStep
example : noNfProg.Safe := noNfProg.safe

end Millipede.Tests.LoopBounds
