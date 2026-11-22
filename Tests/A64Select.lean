import Tests.Select
import Millipede.RegAlloc.A64Reg
import Millipede.Target.A64.Select

/-!
# arm64 selection on the Lean model against Lin

These tests select the terms and programs of `Tests/Select.lean` for arm64 with slot locations,
place the data and the data region within the 1 MiB reach of `adr`, and run them on the arm64
model with the arm64 Linux ABI. They run the checks of `Tests/Select.lean` with the arm64 runner.
The result bytes and the events agree with the Lin interpreter, and every Lin binary operation
agrees with its model, including `x / 0 = 0` and `x % 0 = x`, for which `udiv` needs no guard. The
machine trace of a program is its source trace. `scripts/differential-a64.sh` runs the same
selection natively.
-/

namespace Millipede.Tests.A64Select

open Millipede Millipede.Flat Millipede.Tests.Core Millipede.Tests.Select Millipede.Sel
  Millipede.Tests.Lower Millipede.Tests.Lin

def a64Data : Nat := 0x480000
def a64Bss : Nat := 0x490000

/-- Select a Lin program for arm64 and place it. -/
def a64Image (P : Lin.Prog) : Option Image :=
  match RegAlloc.A64Reg.select 0 0 P with
  | .ok A => imageOf A a64Data a64Bss
  | .error _ => none

/-- Run the arm64 code of a Core term with its parameters' bytes in the data region. -/
def a64Run (ω : Oracle) {Γ : List Ty} {t : Ty} (e : Exp Γ t) (env : Env Γ) (fuel : Nat) :
    Option (List UInt8 × List Event) := do
  let img ← a64Image (linOf e)
  let s₀ := img.init A64.linux
  let mem ← s₀.mem.write (UInt64.ofNat a64Bss) (envBytes env)
  let s ← (Asm.msem A64.isa A64.linux).run ω ({ s₀ with mem := mem }, 0) fuel
  pure (bytesFrom s.1.mem (UInt64.ofNat (a64Bss + ctxSize Γ)) t.size, s.1.world.events)

/-- Events of a program compiled for arm64 and run for `fuel` machine steps. -/
def a64Events (ω : Oracle) (p : Program) (fuel : Nat) : Option (List Event) := do
  let img ← a64Image (Lin.linearize (lowerProg p) p.memBytes)
  let s ← (Asm.msem A64.isa A64.linux).run ω (img.init A64.linux, 0) fuel
  pure s.1.world.events

-- the checks of `Tests/Select.lean` for terms, primitives and programs, on arm64
#guard failing ⟨a64Run, a64Events⟩ == []

end Millipede.Tests.A64Select
