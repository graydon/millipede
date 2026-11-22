import Millipede.Lib.Units
import Millipede.Top.Examples
import Millipede.Top.Compile

/-!
# Tests for quantities with units

This suite defines programs with every operation and conversion on quantities and checks their
normal forms by `rfl`. A typed program and its untyped twin have the same Core term and the same
compiled image, compared byte for byte, which shows that units are erased. A size computation
in pages, KiB and bytes drives accesses to a 16 KiB arena, and the verified analyser certifies
all its obligations, while its specifications are stated in base units. Rejection tests pin
the messages for mixing units of one or of two dimensions, passing the wrong unit, using a bare
numeral as a quantity and rounding with `.to`.

Seeded bugs were tried once by hand and reverted. With the ratio of `.to` inverted, the normal
forms and `regionBytes_spec` fail, and with `.toFloor` and `.toCeil` swapped, `ceilK_spec` and
`floorK_spec` fail.

Units are described in doc/design/units.md.
-/

namespace Millipede.Tests.Units

open Millipede Millipede.Lib

/-! ## Operations and their code -/

/-- The wrapping forms `.to` and `+` have no obligation. -/
mp def sizeW (n : Q page) (hdr : Q KiB) (tail : Q byte) : Q byte :=
  n.to byte + hdr.to byte + tail

example : sizeW = fun n hdr tail => pure (n * 4096 + hdr * 1024 + tail) := rfl
example := @sizeW.safe
example : sizeW.exp.total = true := rfl

-- The forms `.to!` and `+!` give the same code with an obligation that the result fits, which
-- is not discharged when the arguments have no bounds.
/-- info: the obligations of `sizeO` were not discharged automatically; prove them with `mp prove sizeO.safe := …` (the goal is `sizeO.SafeGoal`); left:
n : UInt64
⊢ n.toNat * 4096 < 18446744073709551616 -/
#guard_msgs in
mp def sizeO (n : Q page) (hdr : Q KiB) (tail : Q byte) : Q byte :=
  n.to! byte +! hdr.to! byte +! tail

example : sizeO = fun n hdr tail => pure (n * 4096 + hdr * 1024 + tail) := rfl
example : sizeO.exp.total = false := rfl

mp def floorK (b : Q byte) : Q KiB := b.toFloor KiB
mp def ceilK (b : Q byte) : Q KiB := b.toCeil KiB
mp def chkB (p : Q page) : Result Unit (Q byte) := p.to? byte
mp def sameU (b : Q byte) : Q byte := b.to byte

example : floorK = fun b => pure (Qty.floorDiv 1024 b) := rfl
example : ceilK = fun b => pure (Qty.ceilDiv 1024 b) := rfl
example : chkB = fun p => pure (Qty.up? 4096 p) := by
  funext p; simp [chkB, Qty.up?]; rfl
/-- A conversion with ratio 1 emits no code. -/
example : sameU.exp = .atom (.var .here) := rfl

/-- Literals with units, scalars and comparisons, and a quantity's count as an index. -/
mp def mixed (a b : Q ms) (k : UInt64) : Bool :=
  let c := a * 3 + k * b - b / 2 + ms 1 + (sec 2).to ms
  c < b || c == a || c != b && c >= ms 0

mp def idx (tbl : Arr UInt64 8) (i : Q byte) requires i.toNat < 8 : UInt64 := tbl[i.val]!

/-! ## Erasure

A typed program has the same term and the same image as its untyped twin. -/

mp def eraseT : Unit :=
  let n := page 3
  let k := KiB 5
  let t := n.to byte + k.to byte + byte 7
  let b := t.toCeil KiB
  let _x := Examples.sysExit (b.toFloor MiB).val
  ()

mp def eraseU : Unit :=
  let n := 3
  let k := 5
  let t := n * 4096 + k * 1024 + 7
  let b := t / 1024 + (t % 1024 + 1023) / 1024
  let _x := Examples.sysExit (b / 1024)
  ()

example : eraseT.exp = eraseU.exp := rfl

/-- The compiled image of a program whose `init` is the given term. -/
def image (init : Exp [] Ty.unit) : Option (List UInt8) :=
  ((compile ⟨Ty.unit, init, Examples.keepUnit.exp⟩ x64Linux).toOption).map (·.data.toList)

#guard (image eraseT.exp).isSome && image eraseT.exp == image eraseU.exp

/-! ## Conversions in base units -/

theorem floorK_spec (b : UInt64) :
    KiB.inBase (floorK b).run ≤ byte.inBase b ∧ byte.inBase b < KiB.inBase (floorK b).run + 1024 :=
  QUnit.inBase_floorDiv (u := byte) (v := KiB) (r := 1024) (by simp) (by decide)

theorem ceilK_spec (b : UInt64) :
    byte.inBase b ≤ KiB.inBase (ceilK b).run ∧ KiB.inBase (ceilK b).run < byte.inBase b + 1024 :=
  QUnit.inBase_ceilDiv (u := byte) (v := KiB) (r := 1024) (by simp) (by decide)

/-- When the checked conversion returns `ok`, the result is the same amount. -/
theorem chkB_spec (p y : UInt64) (h : (chkB p).run = .ok y) : byte.inBase y = page.inBase p :=
  QUnit.inBase_up? (u := page) (v := byte) (r := 4096) (by simp) (by decide) h

/-! ## A size computation in mixed units

The functions below compute sizes in pages, KiB and bytes and use them to access a 16 KiB arena.
Sizes, offsets and indices use the forms `.to!`, `+!` and `*!`, whose obligations are that the
result fits. The verified analyser certifies every overflow and index obligation from the
bounds in `requires`, and a bound may be stated in base units, as in `KiB.inBase off < …`. The
specifications are stated in base units. -/

/-- The size in bytes of `n` pages, a header of `hdr` KiB and `tail` bytes. -/
mp def regionBytes (n : Q page) (hdr : Q KiB) (tail : Q byte)
    requires n.toNat < 2 ^ 20 ∧ hdr.toNat < 2 ^ 30 ∧ tail.toNat < 2 ^ 40 : Q byte :=
  n.to! byte +! hdr.to! byte +! tail

/-- The same size rounded up to whole pages. -/
mp def regionPages (n : Q page) (hdr : Q KiB) (tail : Q byte)
    requires n.toNat < 2 ^ 20 ∧ hdr.toNat < 2 ^ 30 ∧ tail.toNat < 2 ^ 40 : Q page :=
  (n.to! byte +! hdr.to! byte +! tail).toCeil page

/-- The table slot of an offset in KiB, one slot per page, with the bound stated in base units. -/
mp def slotOf (tbl : Arr UInt64 16) (off : Q KiB) requires KiB.inBase off < 16 * 4096 : UInt64 :=
  tbl[(off.toFloor page).val]!

/-- Zeroes page `pg` of the arena. -/
mp def zeroPage (arena : Arr UInt8 16384) (pg : Q page) requires pg.toNat < 4 :
    Arr UInt8 16384 := do
  let mut a := arena
  let base := pg.to! byte
  for j in 0...4096 do
    a[base.val +! j]! := 0
  a

/-- The byte at page `pg`, KiB `k` of that page, byte `b` of that KiB. -/
mp def byteAt (arena : Arr UInt8 16384) (pg : Q page) (k : Q KiB) (b : Q byte)
    requires pg.toNat < 4 ∧ k.toNat < 4 ∧ b.toNat < 1024 : UInt8 :=
  let off := pg.to! byte +! k.to! byte +! b
  arena[off.val]!

/-- Fills the first `kib` KiB of page `pg` with `v`, one KiB at a time. -/
mp def fillKiB (arena : Arr UInt8 16384) (pg : Q page) (kib : Q KiB) (v : UInt8)
    requires pg.toNat < 4 ∧ kib.toNat ≤ 4 : Arr UInt8 16384 := do
  let mut a := arena
  let base := pg.to! byte
  for k in 0...4 do
    if k ≥ kib.val then break
    let start := base +! (KiB k).to! byte
    for j in 0...1024 do
      a[start.val +! j]! := v
  a

/-- The number of whole KiB in `pages` pages and `b` bytes, counting the pages' KiB in a loop,
whose bound also bounds the count. -/
mp def countKiB (pages : Q page) (b : Q byte) requires pages.toNat ≤ 16 ∧ b.toNat < 4096 :
    Q KiB := do
  let mut n := KiB 0
  for k in 0...64 do
    if k ≥ (pages.to! KiB).val then break
    n := n +! KiB 1
  n +! b.toFloor KiB

-- The analyser certifies all of them.
example := @regionBytes.analysed
example := @regionPages.analysed
example := @slotOf.analysed
example := @zeroPage.analysed
example := @byteAt.analysed
example := @fillKiB.analysed
example := @countKiB.analysed
example : slotOf.fnRef.Safe := slotOf.Safe

/-- Pages, KiB and bytes add up in bytes, with no premise against overflow beyond the bounds of
`requires`. -/
theorem regionBytes_spec (n hdr tail : UInt64)
    (h : n.toNat < 2 ^ 20 ∧ hdr.toNat < 2 ^ 30 ∧ tail.toNat < 2 ^ 40) :
    byte.inBase (regionBytes n hdr tail).run.1 =
      page.inBase n + KiB.inBase hdr + byte.inBase tail := by
  grind [regionBytes]

/-- The region rounded up to whole pages. -/
theorem regionPages_spec (n hdr tail : UInt64)
    (h : n.toNat < 2 ^ 20 ∧ hdr.toNat < 2 ^ 30 ∧ tail.toNat < 2 ^ 40) :
    let total := page.inBase n + KiB.inBase hdr + byte.inBase tail
    total ≤ page.inBase (regionPages n hdr tail).run.1 ∧
      page.inBase (regionPages n hdr tail).run.1 < total + page.scale := by
  grind [regionPages]

-- Some values.
example : (regionBytes 3 2 1).run.1 = 3 * 4096 + 2048 + 1 := rfl
example : (regionPages 1 0 1).run.1 = 2 := rfl
example : (countKiB 3 2048).run.1 = 14 := rfl

/-! ## Rejections -/

/-- error: `+` needs quantities of the same unit, but the operands are Q byte (dimension Size) and Q KiB (dimension Size): units of one dimension do not mix; convert with `.to byte` -/
#guard_msgs in
mp def bad1 (a : Q byte) (b : Q KiB) : Q byte := a + b

/-- error: `+` needs quantities of the same unit, but the operands are Q byte (dimension Size) and Q ns (dimension Time): quantities of different dimensions never mix -/
#guard_msgs in
mp def bad2 (a : Q byte) (b : Q ns) : Q byte := a + b

/-- error: `<` needs quantities of the same unit, but the operands are Q byte (dimension Size) and Q KiB (dimension Size): units of one dimension do not mix; convert with `.to byte` -/
#guard_msgs in
mp def bad3 (a : Q byte) (b : Q KiB) : Bool := a < b

/-- error: type mismatch: expected Q byte, but this has type Q KiB: units of one dimension do not mix; convert with `.to byte` -/
#guard_msgs in
mp def bad4 (a : Q KiB) : Q byte := sizeW (page 1) (KiB 2) a

/-- error: type mismatch: expected Q KiB, but this has type Q byte: units of one dimension do not mix; convert with `.toFloor KiB` or `.toCeil KiB` -/
#guard_msgs in
mp def bad4b (a : Q byte) : Q KiB := a

/-- error: `.to KiB` would round: KiB is coarser than byte; write `.toFloor KiB` or `.toCeil KiB` -/
#guard_msgs in
mp def bad5 (a : Q byte) : Q KiB := a.to KiB

/-- error: cannot convert Q byte (dimension Size) to Q ns (dimension Time): a conversion stays in one dimension -/
#guard_msgs in
mp def bad6 (a : Q byte) : Q ns := a.to ns

/-- error: `+` needs quantities of the same unit, but the operands are Q byte and UInt64: a UInt64 is not a quantity; write `byte n` for a count of byte -/
#guard_msgs in
mp def bad7 (a : Q byte) : Q byte := a + 1

/-- error: `*` multiplies a quantity by a dimensionless UInt64, not Q byte by Q byte (there is no algebra of dimensions; go through `.val`) -/
#guard_msgs in
mp def bad8 (a b : Q byte) : Q byte := a * b

/-- error: type mismatch: expected UInt64, but this has type Q byte: a quantity is not a UInt64; take its count with `.val` -/
#guard_msgs in
mp def bad9 (a : Q byte) : UInt64 := a

/-- error: `.toFloor byte`: byte is finer than KiB, the conversion is exact; write `.to byte` -/
#guard_msgs in
mp def bad10 (a : Q KiB) : Q byte := a.toFloor byte

/-- error: type mismatch: expected UInt64, but this has type Q byte: a quantity is not a UInt64; take its count with `.val` -/
#guard_msgs in
mp def bad11 (tbl : Arr UInt64 8) (i : Q byte) requires i.toNat < 8 : UInt64 := tbl[i]!

/-- error: `==` needs quantities of the same unit, but the operands are Q ms (dimension Time) and Q ns (dimension Time): units of one dimension do not mix; convert with `.to ns` -/
#guard_msgs in
mp def bad12 (a : Q ms) (b : Q ns) : Bool := a == b

/-- error: `<<<` is not defined on quantities (Q byte, UInt64); go through `.val` -/
#guard_msgs in
mp def bad13 (a : Q byte) : Q byte := a <<< 2

end Millipede.Tests.Units
