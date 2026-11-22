import Millipede.Meta.MpDef
import Millipede.Lib.Pool
import Millipede.Lib.Bump

/-!
# `pooltally`: a reactor holding arena keys across steps

`pooltally` is a reactor whose root holds an arena, a stack of up to 8 linear keys that stay live
across steps, and a total, all in static memory. Each step reads one byte of input, which the
oracle chooses. For a byte `c` it allocates a node holding `c` with `alloc!`, which performs no
run-time check, and keeps its key, first freeing the newest key when 8 are held. At the end of its
input it frees one held key per step, adding each freed node's value to the total, and then exits
with the total's low byte, so its status is the sum of the input bytes modulo 256.

The program is a generic client of the allocator interface, proved once. Its accounting of the
keys it holds is the library's `Alloc.KeyStack`, and `mp program … invariant` derives
`Tally.prog.inv` and `Tally.prog.safe` once for every allocator. `PoolTally.prog` applies it to the
bitmap pool, and `compile_sound` covers it with no hypotheses. Every contract and obligation is
proved automatically, by `mp_auto` unfolding `TallyInv` and using the callees' contracts and the
allocator's facts.
-/

namespace Millipede.Examples

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

mp extern "read" tallyRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern noreturn "exit" tallyExit (code : UInt64) : UInt64

/-- The root of `pooltally` over an allocator `A`, which holds the arena, the keys held in cells
`0 … n-1` of `keys`, and the total. -/
structure TallyRoot (A : Alloc UInt64) where
  arena : A.S
  keys : Slots A.K 8
  n : UInt64
  total : UInt64
deriving Data

/-- The root invariant of `pooltally`, which is the arena's invariant together with the keys in
the stack being held. -/
def TallyInv (A : Alloc UInt64) (r : TallyRoot A) : Prop :=
  A.Inv r.arena ∧ A.KeyStack r.arena r.keys r.n

section
variable (A : Alloc UInt64) (h8 : 8 ≤ A.cap) (hr : A.reuse = true)
include h8 hr

/-- The initial root of `pooltally` over an allocator `A` with 8 cells that gives cells back.
`TallyInv`, which includes the library's accounting `A.KeyStack` of the held keys, discharges the
obligation `used < cap` of `alloc!` from the test `n < 8`, and the ownership that `free` needs.
It is proved once, for every such `A`. -/
mp def Tally.init ensures TallyInv A result : TallyRoot A :=
  { arena := A.new, keys := Slots.empty 8, n := 0, total := 0 }

/-- Allocates a node holding `c` with the unchecked `alloc!` and pushes its key. -/
mp def Tally.push (r : &mut TallyRoot A) (c : UInt64)
    requires TallyInv A r ∧ r.n.toNat < 8 ensures TallyInv A r' : Unit := do
  let k := A.alloc! (&mut r.arena) c
  let i := r.n
  let _ := r.keys.put! i k
  r.n := i +! 1
  ()

/-- Pops the newest key, frees its node, and adds the node's value to the total. -/
mp def Tally.pop (r : &mut TallyRoot A)
    requires TallyInv A r ∧ 0 < r.n.toNat
    ensures TallyInv A r' ∧ r'.n.toNat + 1 = r.n.toNat : Unit := do
  let i := r.n -! 1
  let k := r.keys.take! i
  let v := A.free (&mut r.arena) k
  r.n := i
  r.total := r.total + v
  ()

/-- One step, which reads a byte `c`. When fewer than 8 keys are held, it allocates a node holding
`c` and keeps its key, and otherwise it first pops and frees the newest key, adding its value to
the total, and then allocates. At the end of input, when `read` returns `2^64 - 1`, it pops and
frees one held key per step, and exits with the total's low byte once none is left. Every byte is
added exactly once, when its node is freed, so the exit status is the sum of the input bytes
modulo 256. -/
mp def Tally.step (r : &mut TallyRoot A)
    requires TallyInv A r ensures TallyInv A r' : Unit :=
  let c := tallyRead 0
  if c < 256 then
    if r.n < 8 then Tally.push (&mut r) c
    else
      let _ := Tally.pop (&mut r)
      Tally.push (&mut r) c
  else if r.n == 0 then
    let _x := tallyExit (r.total &&& 255)
    ()
  else Tally.pop (&mut r)

/-- The reactor for every such `A`, whose `Tally.prog.safe` and `Tally.prog.inv` are proved
once. -/
mp program Tally.prog (root : TallyRoot A) init Tally.init
  step Tally.step invariant (fun r => TallyInv A r)

end

/-- `pooltally` over the bitmap pool. Its safety, which covers every obligation of every step for
every oracle, among them the bound on live cells that `alloc!` needs in place of a run-time check,
is `Tally.prog.safe` at `Pool8.impl`. -/
abbrev PoolTally.prog : Program := Tally.prog Pool8.impl (by decide) (by decide)

theorem PoolTally.prog.safe : PoolTally.prog.Safe := Tally.prog.safe _ _ _

end Millipede.Examples
