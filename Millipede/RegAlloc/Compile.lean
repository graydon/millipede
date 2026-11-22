import Millipede.Top.Sound
import Millipede.RegAlloc.Alloc
import Millipede.RegAlloc.A64Reg

/-!
# Allocation statistics

The statistics of register allocation that the command `differential ra-stats k` prints.
-/

namespace Millipede.RegAlloc

/-- Statistics of the allocation of a program's Lin image. -/
structure Stats where
  fns : Nat
  /-- The number of functions that kept their slots. -/
  identity : Nat
  websReg : Nat
  websSlot : Nat
  frame0 : Nat
  frame1 : Nat
  /-- The number of Lin `mov`s, while `coalesced` counts those that became `mov l l`, which
  selection leaves empty. -/
  movs : Nat
  coalesced : Nat
  accepted : Bool

def stats (k : Nat) (p : Program) : Except String Stats := do
  let fp ← Flat.lower p
  let P := Lin.linearize fp p.memBytes
  let (P', maps, rs) := Alloc.allocate { k } P
  let pairs := (P.funs.zip P'.funs).flatMap fun (fn, fn') => fn.code.zip fn'.code
  let movs := pairs.filter fun | (.mov _ _, _) => true | _ => false
  let coal := pairs.filter fun | (.mov _ _, .mov x (.slot y)) => x == y | _ => false
  pure ⟨rs.length, (rs.filter (·.fallback)).length, (rs.map (·.inRegs)).sum,
    (rs.map (·.inSlots)).sum, (P.funs.map (·.frame)).sum, (P'.funs.map (·.frame)).sum,
    movs.length, coal.length, check P P' maps⟩

end Millipede.RegAlloc
