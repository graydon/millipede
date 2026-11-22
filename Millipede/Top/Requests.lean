import Millipede.Meta.MpDef
import Millipede.Top.Sound
import Millipede.Lib.Pool
import Millipede.Lib.Bump

/-!
# `reqspool` and `reqsbump`: one client of the allocator interface, two implementations

`Reqs A` is a generic module, a reactor that serves one request per input byte with an arena
scoped to the request, written against the allocator interface `Alloc UInt64` and nothing else.
Each step reads a byte `c`, starts a fresh arena and serves the request `(c, c + 1, c + 2)`. It
stores `x` and `y`, frees `x`'s cell, and stores `z`, which a bitmap pool puts in `x`'s old cell
and a bump arena in a new one. It then reads `y` back, frees every key, and returns the sum of
the three values it read. The root keeps the total, and at the end of input the program exits
with the total's low byte, so its status is `Σ (3c + 3) mod 256` over the input bytes whatever
the implementation.

The contracts of `Reqs.serve`, `Reqs.init` and `Reqs.step` and the safety of `Reqs.prog` are
proved once, for every `A : Alloc UInt64` with `3 ≤ A.cap`, from the interface's contracts alone.
`ReqsPool.prog` applies the module to the bitmap pool and `ReqsBump.prog` to the bump arena, so
their safety is `Reqs.prog.safe` applied, and `compile_sound` covers both.
-/

namespace Millipede.Examples

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

mp extern "read" reqRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern noreturn "exit" reqExit (code : UInt64) : UInt64

section
variable (A : Alloc UInt64) (h3 : 3 ≤ A.cap)
include h3

/-- One request, which uses three cells, freeing one before the third is allocated, and returns
the sum of the values read back. -/
mp def Reqs.serve (a : &mut A.S) (x y z : UInt64) requires A.Inv a ∧ A.used a + 3 ≤ A.cap
    ensures result = x + y + z ∧ A.Inv a' : UInt64 :=
  let k1 := A.alloc! (&mut a) x
  let k2 := A.alloc! (&mut a) y
  let v1 := A.free (&mut a) k1
  let k3 := A.alloc! (&mut a) z
  let v2 := A.get (&a) (&k2)
  let v3 := A.free (&mut a) k3
  let _w := A.free (&mut a) k2
  v1 + v2 + v3

/-- The initial root, a fresh arena and a zero total. -/
mp def Reqs.init ensures A.Inv result.1 : A.S × UInt64 := ⟨A.new, 0⟩

/-- One step, which reads a byte `c`, serves `(c, c + 1, c + 2)` in a fresh arena and adds the
result to the total, and at the end of input exits with the total's low byte. -/
mp def Reqs.step (r : &mut (A.S × UInt64)) requires A.Inv r.fst ensures A.Inv r'.fst :
    Unit := do
  let c := reqRead 0
  if c < 256 then
    let s := A.new
    r.fst := s
    let v := Reqs.serve (&mut r.fst) c (c + 1) (c + 2)
    r.snd := r.snd + v
    ()
  else
    let _x := reqExit (r.snd &&& 255)
    ()

mp program Reqs.prog (root : A.S × UInt64) init Reqs.init step Reqs.step
  invariant (fun r => A.Inv r.1)
end

/-- The client over the bitmap pool. -/
abbrev ReqsPool.prog : Program := Reqs.prog Pool8.impl (by decide)
theorem ReqsPool.prog.safe : ReqsPool.prog.Safe := Reqs.prog.safe _ _

/-- The client over the bump arena. -/
abbrev ReqsBump.prog : Program := Reqs.prog Bump8.impl (by decide)
theorem ReqsBump.prog.safe : ReqsBump.prog.Safe := Reqs.prog.safe _ _

/-- The compiled bytes of both instances are correct, with no hypotheses beyond the compiler's
output. Their obligations hold for every oracle, which `mp program` derives from the contracts
instantiated from the module's generic ones, and `compile_sound` covers every program that
`compile` accepts. -/
theorem reqsPool_sound (b : ByteArray) (hc : compile ReqsPool.prog x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (ReqsPool.prog.events ω) ∧
        m.StackWithin (ReqsPool.prog.stackBytes x64Linux.φ) ∧
        m.StepsWithin (ReqsPool.prog.events ω)
          (fun k => ReqsPool.prog.stepCost k ω x64Linux.κ) :=
  compile_sound ReqsPool.prog b hc ReqsPool.prog.safe

@[inherit_doc reqsPool_sound]
theorem reqsBump_sound (b : ByteArray) (hc : compile ReqsBump.prog x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (ReqsBump.prog.events ω) ∧
        m.StackWithin (ReqsBump.prog.stackBytes x64Linux.φ) ∧
        m.StepsWithin (ReqsBump.prog.events ω)
          (fun k => ReqsBump.prog.stepCost k ω x64Linux.κ) :=
  compile_sound ReqsBump.prog b hc ReqsBump.prog.safe

end Millipede.Examples
