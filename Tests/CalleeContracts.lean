import Millipede.Meta.MpDef

/-!
# Tests of a caller's obligations when a callee's contract says less than its term

The automatic attempt at a caller's obligations first cites its callees' contracts, and if that
fails, it tries again with the callees' terms. `upper` has `ensures True`. Citing it in `stp`,
`mp_safe` leaves `need`'s `requires` unproved, but with `upper`'s term it proves it, so
`stpAuto.safe` is proved (scratch/audit/reach/Upper.lean, with `ensures True` on its `upcase`). -/

namespace Millipede.Tests.CalleeContracts

open Millipede Std.WP

set_option experimental.vcgen true

mp extern "read" rd (fd : UInt64) (buf : &mut [U8]) : UInt64
structure St2 where
  buf : Arr UInt8 64
  len : UInt64
deriving Data
mp def upper (s : &mut [UInt8; 64]) ensures True : Unit := do
  for i in 0...s.len do
    let c := s[i]
    if c >= 97 then
      s[i] := c - 32
mp def need (s : &St2) (n : UInt64) requires n.toNat ≤ 64 : UInt64 := n
set_option mp.autoSafe false in
mp def stp (s : &mut St2) : Unit := do
  let r := rd 0 (&mut s.buf[0..64])
  if r <= 64 then
    s.len := r
    let n := s.len
    let _ := upper (&mut s.buf[0..n])
    let _b := need (&s) n
    ()
example : stp.SafeGoal := by
  intros
  fail_if_success (mp_safe [stp.exp, upper.Safe', upper.req, need.Safe', need.req,
    upper.exp_denote] using upper.Safe', need.Safe' grind [upper.post]; done)
  mp_safe [stp.exp, upper.Safe', upper.req, need.Safe', need.req] using upper.Safe', need.Safe'
    grind []

-- The same function with the automatic attempt, which falls back to the callees' terms.
mp def stpAuto (s : &mut St2) : Unit := do
  let r := rd 0 (&mut s.buf[0..64])
  if r <= 64 then
    s.len := r
    let n := s.len
    let _ := upper (&mut s.buf[0..n])
    let _b := need (&s) n
    ()

example := @stpAuto.safe

end Millipede.Tests.CalleeContracts
