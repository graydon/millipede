import Millipede.Lib.Pool
import Millipede.Lib.Bump
import Millipede.Top.Requests
import Millipede.Meta.Report

/-!
# Tests for generic definitions, interfaces and implementations

An instance of a generic definition is an application, so the library's arenas at a given type
and capacity get their contracts and safety by applying the generic theorems. Instances declared
in this file are filled to capacity and reach `Full`. The hypotheses of a generic definition are
checked at each instance, so a call at a pool too large for one bitmap word, or a client at an
arena with too few cells, is refused with the hypothesis named.

The contract of the generic client `Reqs.serve` is one theorem over every implementation of the
interface `Alloc` with at least three cells, and an instance's contract is that theorem applied.
The compiler's soundness theorem applies to the programs of both instances. A client that looks
through the abstraction is a type error. A test that frees and allocates again tells a pool from
a bump arena, with expectations computed by hand.

Modules are described in doc/design/modules.md.
-/

namespace Millipede.Tests.Modules

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## An instance is an application -/

theorem h100 : 100 ≤ 64 * 2 := by decide
theorem h100n : 100 < 2 ^ 64 := by decide

example : ∀ (p : Pool100) (v : Cell2), p.Inv →
    (Pool.alloc Cell2 100 2 h100 h100n p v).run.2.1.Inv :=
  fun p v h => (Pool.alloc.post Cell2 100 2 h100 h100n p v h).1
example : ∀ (p : Pool100) (v : Cell2), p.Inv ∧ p.live.toNat < 100 →
    (Pool.alloc! Cell2 100 2 h100 h100n p v).run.2.1.live.toNat = p.live.toNat + 1 :=
  fun p v h => (Pool.alloc!.post _ _ _ _ _ p v h).2.2.2.2.1
example : (Pool.alloc!.fnRef Cell2 100 2 h100 h100n).Safe := Pool.alloc!.Safe _ _ _ _ _
example : (Bump.alloc!.fnRef UInt8 16 (by decide)).Safe := Bump.alloc!.Safe _ _ _
/-- At a closed instance the borrow checker is also decided. -/
example : (Pool.alloc.fnRef Cell2 100 2 h100 h100n).wf [.mut, .own] = true := by decide

/-! ## Instances in another file -/

abbrev Pool3 := Pool UInt64 3 1

/-- Allocates `n` times into a fresh `Pool3` and returns the indices, with `none` for `Full`. -/
def fill3 (n : Nat) : List (Option UInt64) :=
  ((List.range n).foldl (fun (acc : List (Option UInt64) × Pool3) i =>
    let r := (Pool.alloc UInt64 3 1 (by decide) (by decide) acc.2 (UInt64.ofNat i)).run
    (acc.1 ++ [match r.1 with | .ok k => some k.idx | .error _ => none], r.2.1))
    ([], (Pool.new UInt64 3 1 (by decide) (by decide)).run)).1

#guard fill3 5 == [some 0, some 1, some 2, none, none]
#guard !(fill3 5 == [some 0, some 1, some 2, some 3, none])

abbrev Bump2 := Bump Cell2 2

#guard ((List.range 3).foldl (fun (acc : Nat × Bump2) i =>
    match (Bump.alloc Cell2 2 (by decide) acc.2 ⟨UInt64.ofNat i, 0⟩).run with
    | (.ok _, b, _) => (acc.1 + 1, b) | (.error _, b, _) => (acc.1, b))
    (0, (Bump.new Cell2 2 (by decide)).run)).1 == 2

/-! ## Hypotheses are checked at the instance -/

/--
error: cannot instantiate `Millipede.Lib.Pool.alloc`: its hypothesis
  100 ≤ 64 * 1
is neither in the context nor decided
-/
#guard_msgs in
mp def badPool (p : &mut Pool UInt64 100 1) (v : UInt64) requires p.Inv :
    Result Full (Pool.Key UInt64 100 1) :=
  Pool.alloc (&mut p) v

/-! ## Interfaces and generic clients -/

open Millipede.Examples

/-- The client's contract, proved once for every implementation. -/
example : ∀ (A : Alloc UInt64) (h : 3 ≤ A.cap) (a : A.S) (x y z : UInt64),
    ⦃A.Inv a ∧ A.used a + 3 ≤ A.cap⦄ Reqs.serve A h a x y z
    ⦃fun r => r.1 = x + y + z ∧ A.Inv r.2.1⦄ := Reqs.serve.spec
example : ∀ (A : Alloc UInt64) (h : 3 ≤ A.cap) (ω : Oracle) (r : A.S × UInt64),
    ⦃fun _ => A.Inv r.1⦄ Reqs.step A h ω r ⦃fun r _ => A.Inv r.2.1.1⦄ := Reqs.step.spec
/-- An instance's contract is the generic theorem applied. -/
example : ∀ (b : Bump8) (x y z : UInt64), ⦃b.Inv ∧ b.used + 3 ≤ 8⦄
    Reqs.serve Bump8.impl (by decide) b x y z ⦃fun r => r.1 = x + y + z ∧ r.2.1.Inv⦄ :=
  Reqs.serve.spec Bump8.impl (by decide)
/-- The soundness theorem for the bump instance, with no hypothesis beyond the compiler's output,
and the safety that it needs for the pool instance. -/
example (b : ByteArray) (hc : compile ReqsBump.prog x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (ReqsBump.prog.events ω) ∧
        m.StackWithin (ReqsBump.prog.stackBytes x64Linux.φ) ∧
        m.StepsWithin (ReqsBump.prog.events ω)
          (fun k => ReqsBump.prog.stepCost k ω x64Linux.κ) :=
  compile_sound ReqsBump.prog b hc ReqsBump.prog.safe
example : ReqsPool.prog.Safe := ReqsPool.prog.safe

/-- A 2-cell arena, which does not meet the hypothesis `3 ≤ A.cap` of `Reqs`, so a call at it is
refused. -/
abbrev BumpW2.impl : Alloc UInt64 := Bump.impl UInt64 2 (by decide)

/--
error: cannot instantiate `Millipede.Examples.Reqs.serve`: its hypothesis
  3 ≤ BumpW2.impl.cap
is neither in the context nor decided
-/
#guard_msgs in
mp def small (a : &mut Bump UInt64 2) requires a.Inv : UInt64 :=
  Reqs.serve (A := BumpW2.impl) (&mut a) 1 2 3

/-! ## A generic client declared here -/

section
variable (A : Alloc UInt64)

/-- Stores `v` and reads it back. The contract is proved once, automatically, for every
implementation, from the interface's contracts. -/
mp def Echo.echo (a : &mut A.S) (v : UInt64) requires A.Inv a ∧ A.used a < A.cap
    ensures result = v ∧ A.Inv a' : UInt64 := do
  let k := A.alloc! (&mut a) v
  let r := A.get (&a) (&k)
  let _w := A.free (&mut a) k
  r

end

example : ∀ (A : Alloc UInt64) (a : A.S) (v : UInt64),
    ⦃A.Inv a ∧ A.used a < A.cap⦄ Echo.echo A a v ⦃fun r => r.1 = v ∧ A.Inv r.2.1⦄ :=
  Echo.echo.spec

/-! ## Reports

`#mp_report` says what is proved once for a generic definition, and gives the figures of a
program at an instance. -/

/--
info: Millipede.Tests.Modules.Echo.echo: generic over 1 variable(s); proved once, for every value of them (figures: at a closed instance, `#mp_report` of a program)
  obligations automatic; contract automatic
-/
#guard_msgs in
#mp_report Echo.echo

/--
info: program Millipede.Examples.ReqsBump.prog
  root            80 bytes (static storage)
  footprint       321 bytes (root + the larger of init's and step's values)
  data region     409 bytes
  stack           ≤ 5792 bytes (X64.φ)
  steps           init ≤ 1217, each step ≤ 4307 instructions (X64.κ)
                  (a bound, not a measurement: the Core term's cost under the cost model X64.κ, which compile checks the selected code against; on the oracle answering 0 the source semantics charges init 1217, step 1 278)
  code            12288 bytes (x64 Linux ELF)
  arm64           stack ≤ 5808 bytes (A64.φ), each step ≤ 3985 instructions (A64.κ); code 131072 bytes (arm64 Linux ELF)
functions (stack ≤ bytes under X64.φ / A64.φ, per target; obligations; contract)
  Millipede.Examples.Reqs.init: stack x64 864, arm64 864; obligations automatic (proved once); contract automatic
  Millipede.Examples.Reqs.serve: stack x64 3160, arm64 3168; obligations automatic (proved once); contract automatic
  Millipede.Examples.Reqs.step: stack x64 5176, arm64 5184; obligations automatic (proved once); contract automatic
  Millipede.Lib.Alloc.alloc!: stack x64 952, arm64 960; obligations the implementation's (`Millipede.Lib.Alloc` field); contract the interface's
  Millipede.Lib.Alloc.free: stack x64 576, arm64 576; obligations the implementation's (`Millipede.Lib.Alloc` field); contract the interface's
  Millipede.Lib.Alloc.get: stack x64 288, arm64 288; obligations the implementation's (`Millipede.Lib.Alloc` field); contract the interface's
  Millipede.Lib.Alloc.new: stack x64 416, arm64 416; obligations the implementation's (`Millipede.Lib.Alloc` field); contract the interface's
-/
#guard_msgs in
#mp_report ReqsBump.prog

/-! ## Rejected: looking through the abstraction -/

section
variable (A : Alloc UInt64)
/-- error: type A.S has no field `live` -/
#guard_msgs in
mp def Peek.count (a : &A.S) : UInt64 := a.live
end

/-! ## Capacity and reuse

The programs of `Reqs` give the same status over both arenas. `Reuse` fills an arena of two
cells, meets `Full`, frees the first key and allocates again. A pool gives the cell back, for
`100 + 10 + 20 + 40`, and a bump arena does not, for `200 + 10 + 20`. The expectations are
computed by hand from the arenas' documented behaviour. -/

section
variable (A : Alloc UInt64) (h2 : A.cap = 2)
include h2

set_option mp.autoSafe false in
mp def Reuse.run (a : &mut A.S) requires A.Inv a ∧ A.used a = 0 : UInt64 := do
  let k1 := A.alloc! (&mut a) 10
  let k2 := A.alloc! (&mut a) 20
  let r3 := A.alloc (&mut a) 30
  match r3 with
  | ok k =>
    let v3 := A.free (&mut a) k
    let v1 := A.free (&mut a) k1
    let v2 := A.free (&mut a) k2
    v1 + v2 + v3
  | err _ =>
    let v1 := A.free (&mut a) k1
    let r4 := A.alloc (&mut a) 40
    match r4 with
    | ok k =>
      let v4 := A.free (&mut a) k
      let v2 := A.free (&mut a) k2
      100 + v1 + v2 + v4
    | err _ =>
      let v2 := A.free (&mut a) k2
      200 + v1 + v2

end

abbrev Pool2.impl : Alloc UInt64 := Pool.impl UInt64 2 1 (by decide) (by decide)

#guard (Reuse.run Pool2.impl rfl (Pool.new UInt64 2 1 (by decide) (by decide)).run).run.1 == 170
#guard (Reuse.run BumpW2.impl rfl (Bump.new UInt64 2 (by decide)).run).run.1 == 230

end Millipede.Tests.Modules
