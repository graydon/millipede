import Millipede.Meta.MpDef
import Millipede.Top.Sound

/-!
# Several `&mut` arguments on one root, one of them through a `Slots` cell

The value semantics writes a call's `&mut` arguments back one after the other, so the
obligation that a later argument's `Slots` cell is full is about the value after the earlier
write-backs. Cells have no tags, so `compile` decides this on the cells' occupancies, which are
ghost data. Every lens certificate carries a law about occupancy, and a later argument may go
through a cell whose `Slots` is reached from the root by certified fields only, when its
occupancy is apart from what the earlier argument writes.

The write-backs run from the last argument to the first, so in
`bump2 (&mut a.cells[k]!) (&mut a.count) 5` the counter is written back before the cell's
obligation is used. This suite shows that such calls are accepted, with a third field written
back after the cell, through a reference parameter, and for two fields of cells of one `Slots`,
since a write-back through a full cell keeps every cell's occupancy. A cell whose `Slots` lies
behind an array element is still refused, because occupancy is not tracked through elements.
-/

namespace Millipede.Tests.SlotsArgs

open Millipede

structure Arena where
  count : UInt64
  cells : Slots UInt64 4
  tag : UInt64
deriving Data

mp def bump2 (c : &mut UInt64) (x : &mut UInt64) (d : UInt64) : Unit := do
  c := c + 1
  x := x + d
  ()

mp def bump3 (c : &mut UInt64) (x : &mut UInt64) (t : &mut UInt64) : Unit := do
  c := c + 1
  x := x * 2
  t := t + x
  ()

/-- The counter of an arena is written back first, and then one of its cells. -/
mp def addAt (a0 : Arena) (k : UInt64) requires a0.cells.isFull k.toNat = true : Arena := do
  let mut a := a0
  let _ := bump2 (&mut a.cells[k]!) (&mut a.count) 5
  a

def a0 : Arena := ⟨1, (Slots.empty 4).setCell 2 (some 10), 7⟩

example : (addAt a0 2).run.1.count = 6 := by decide
example : (addAt a0 2).run.1.cells.cell 2 = some 11 := by decide
example : addAt.exp.memOk = true := by decide

/-- Three arguments, with a field written back after the cell too. -/
mp def addAt3 (a0 : Arena) (k : UInt64) requires a0.cells.isFull k.toNat = true : Arena := do
  let mut a := a0
  let _ := bump3 (&mut a.tag) (&mut a.cells[k]!) (&mut a.count)
  a

example : (addAt3 a0 2).run.1.tag = 8 := by decide
example : (addAt3 a0 2).run.1.count = 21 := by decide
example : (addAt3 a0 2).run.1.cells.cell 2 = some 20 := by decide
example : addAt3.exp.memOk = true := by decide

/-- Through a reference parameter. -/
mp def addRef (a : &mut Arena) (k : UInt64) requires a.cells.isFull k.toNat = true : Unit :=
  let _ := bump2 (&mut a.cells[k]!) (&mut a.count) 3
  ()

example : addRef.exp.memOk = true := by decide

/-! ## Still refused -/

structure Outer where
  xs : Vector Arena 2
deriving Data

instance : Inhabited Arena := ⟨⟨0, Slots.empty 4, 0⟩⟩

/-- The cell's `Slots` lies behind an array element, where occupancy is not tracked. -/
mp def deepAt (o0 : Outer) (i k : UInt64)
    requires i.toNat < 2 ∧ (o0.xs[i.toNat]!).cells.isFull k.toNat = true : Outer := do
  let mut o := o0
  let _ := bump2 (&mut o.xs[i]!.cells[k]!) (&mut o.xs[i]!.count) 5
  o

example : deepAt.exp.memOk = false := by decide

structure Cell where
  v : UInt64
  n : UInt64
deriving Data

instance : Inhabited Cell := ⟨⟨0, 0⟩⟩

structure Table where
  cells : Slots Cell 4
deriving Data

/-- Two fields of cells of one `Slots`, where `i = j` is allowed because the fields differ. The
first write-back goes through a full cell, which keeps every cell's occupancy. -/
mp def twoCells (t0 : Table) (i j : UInt64)
    requires t0.cells.isFull i.toNat = true ∧ t0.cells.isFull j.toNat = true : Table := do
  let mut t := t0
  let _ := bump2 (&mut t.cells[i]!.v) (&mut t.cells[j]!.n) 5
  t

def t0 : Table := ⟨((Slots.empty 4).setCell 1 (some ⟨1, 2⟩)).setCell 3 (some ⟨3, 4⟩)⟩

example : ((twoCells t0 1 3).run.1.cells.cell 1).map (·.v) = some 2 := by decide
example : ((twoCells t0 1 3).run.1.cells.cell 3).map (·.n) = some 9 := by decide
example : ((twoCells t0 3 3).run.1.cells.cell 3).map (fun c => (c.v, c.n)) = some (4, 9) := by
  decide
example : twoCells.exp.memOk = true := by decide

end Millipede.Tests.SlotsArgs
