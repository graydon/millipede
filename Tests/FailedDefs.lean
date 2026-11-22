import Millipede.Meta.MpDef
import Millipede.Meta.Report
import Millipede.Meta.Emit

/-!
# Tests for an `mp def` whose generated theorem the kernel rejects

`mp def` waits for the kernel's check of each theorem it generates, so a theorem that the kernel
rejects is an error of the `mp def` itself. The function is then not registered:
a caller, `mp program`, `#mp_report`, `#mp_compile` and `mp_entry%` all refuse it, and `#audit`
rejects the theorem, which Lean keeps as a constant that depends on itself. The test-only option
`mp.selftest.badProof` gives the generated theorems of one name, such as `exp_denoteM`, a proof the
kernel rejects.
-/

namespace Millipede.Tests.FailedDefs

open Millipede

mp extern noreturn "exit" ex (code : UInt64) : UInt64

mp def fInit : UInt64 := 0

/--
error: the kernel rejected the generated theorem `Millipede.Tests.FailedDefs.fStep.exp_denoteM`; its error follows
---
error: (kernel) declaration type mismatch, 'Millipede.Tests.FailedDefs.fStep.exp_denoteM' has type
  true = true
but it is expected to have type
  ∀ (ω : Oracle) (s : UInt64), Exp.denoteM ω fStep.exp (Env.cons s Env.nil) = fStep ω s
-/
#guard_msgs in
set_option mp.selftest.badProof "exp_denoteM" in
mp def fStep (s : &mut UInt64) : Unit := do
  s := s + 1
  let _x := ex s
  ()

/-- error: `fStep` was not defined because of the error above (at its `mp def`) -/
#guard_msgs in
mp def caller (s : &mut UInt64) : Unit := fStep (&mut s)

/-- error: `fStep` was not defined because of the error at its `mp def` -/
#guard_msgs in
mp program fp (root : UInt64) init fInit step fStep

/-- error: `fStep`: failed. Its `mp def` stopped with the error reported there, so it has no proved obligations or contract and cannot be called or compiled -/
#guard_msgs in
#mp_report fStep

/-- error: `fp` is neither a program nor an `mp def` -/
#guard_msgs in
#mp_report fp

/-- error: Unknown constant `fp` -/
#guard_msgs in
#mp_compile fp "unused"

/-- error: Unknown constant `fp` -/
#guard_msgs in
example := mp_entry% "fp" "failed" fp

/--
error: the kernel rejected the generated theorem `Millipede.Tests.FailedDefs.g.safe`; its error follows
---
error: (kernel) declaration type mismatch, 'Millipede.Tests.FailedDefs.g.safe' has type
  true = true
but it is expected to have type
  ∀ (ω : Oracle) (w : World) (x : UInt64), x < 5 → Exp.safe ω g.exp (Env.cons x Env.nil) w
-/
#guard_msgs in
set_option mp.selftest.badProof "safe" in
mp def g (x : UInt64) requires x < 5 : UInt64 := x +! 1

/-- error: `g`: failed. Its `mp def` stopped with the error reported there, so it has no proved obligations or contract and cannot be called or compiled -/
#guard_msgs in
#mp_report g

end Millipede.Tests.FailedDefs
