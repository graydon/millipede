/-!
# Quantities

A unit `QUnit` is a dimension, which is a name, together with a scale, which is the unit's size in
the dimension's base unit, the finest unit of that dimension. Users declare dimensions and units
as follows:

```
mp dimension Size
mp unit byte : Size := 1
mp unit KiB  : Size := 1024
mp unit page : Size := 4096
```

`Q u` is a count of the unit `u`, and it is erased. In `mp def`, a value of type `Q KiB` is a
`UInt64` count of KiB, since only the surface checker keeps the unit, while the Core type is
`Ty.u64`. `Q` exists so that `Q KiB` is a Lean type that the elaborator can recognise, and nothing
has type `Q u` at run time. A count `x` of unit `u` stands for `u.inBase x = x.toNat * u.scale`
base units, a `Nat` that never overflows, and specifications are written over `inBase`.

Two quantities of the same unit can be added, subtracted and compared, and a quantity can be
multiplied or divided by a plain `UInt64`. `q.to v` converts to a finer unit of the same dimension
by multiplying by the ratio of the scales, and wraps like `*`. `q.to! v` does the same with the
obligation that the product does not overflow, and `q.to? v` is the checked form, which returns
`ok` exactly when there is no overflow. `q.toFloor v` and `q.toCeil v` convert to a coarser unit,
rounding down and up, and `q.to v` to a coarser unit is rejected because it would round silently.
`KiB e` makes a count of KiB from a `UInt64`, and `q.val` is the count as a `UInt64`.

The wrapping forms carry no obligation, so their lemmas take the absence of overflow as a
hypothesis, which a function states in its `requires` or a specification premise. The obligated
forms carry it as an obligation, which the analyser discharges when `requires` bounds the
operands, and the same lemmas apply to them, since an obligated primitive denotes the wrapping
operation.

`inBase_def` and each unit's `scale_eq`, which `mp unit` generates, are `simp` and `grind` lemmas.
A specification over `inBase` with concrete units therefore unfolds to arithmetic on `toNat` with
literal ratios, which `grind` decides, floors and ceilings included. The lemmas in this file give
the meaning for any units, for proofs in which the ratio is not a literal. The conversions are the
named functions `Qty.up`, `Qty.up?`, `Qty.floorDiv` and `Qty.ceilDiv`, whose bodies are the
primitives the elaborator emits.

The design is described in doc/design/units.md.
-/

namespace Millipede

/-- A dimension, given by a name such as `Size` or `Time`. Units of different dimensions never
mix. -/
structure Dim where
  name : String
deriving DecidableEq, Repr

/-- A unit, which is a dimension and the unit's size in that dimension's base unit. -/
structure QUnit where
  dim : Dim
  scale : Nat
  scale_pos : 0 < scale := by decide

/-- A count of unit `u`. It is a surface type only, which `mp def` erases to `UInt64`. -/
def Q (_u : QUnit) : Type := UInt64

/-- The meaning of a count of `u`, which is `x.toNat * u.scale` base units. -/
def QUnit.inBase (u : QUnit) (x : UInt64) : Nat := x.toNat * u.scale

/-! ## The conversions that `mp def` emits for `.to`, `.to?`, `.toFloor` and `.toCeil` -/

/-- `q.to v` with the ratio `r = u.scale / v.scale`, which multiplies and wraps. -/
def Qty.up (r : Nat) (x : UInt64) : UInt64 := x * UInt64.ofNat r

/-- `q.to? v`, which is `ok (x * r)` when the product does not overflow and `err ()` otherwise. -/
def Qty.up? (r : Nat) (x : UInt64) : Except Unit UInt64 :=
  if x ≤ UInt64.ofNat ((2 ^ 64 - 1) / r) then .ok (x * UInt64.ofNat r) else .error ()

/-- `q.toFloor v` with ratio `r = v.scale / u.scale`. -/
def Qty.floorDiv (r : Nat) (x : UInt64) : UInt64 := x / UInt64.ofNat r

/-- `q.toCeil v` with ratio `r = v.scale / u.scale`. No intermediate result overflows when
`r ≤ 2^63`. -/
def Qty.ceilDiv (r : Nat) (x : UInt64) : UInt64 :=
  x / UInt64.ofNat r + (x % UInt64.ofNat r + UInt64.ofNat (r - 1)) / UInt64.ofNat r

/-! ## `inBase` lemmas -/

namespace QUnit

variable (u v : QUnit) {x y k : UInt64}

@[simp, grind =] theorem inBase_def : u.inBase x = x.toNat * u.scale := rfl

variable {u v} {r : Nat}

private theorem ofNat_toNat (h : r < 2 ^ 64) : (UInt64.ofNat r).toNat = r :=
  UInt64.toNat_ofNat_of_lt' h

/-- Converting to a finer unit is exact when it does not overflow. -/
theorem inBase_up (hr : u.scale = r * v.scale) (hr64 : r < 2 ^ 64) (h : x.toNat * r < 2 ^ 64) :
    v.inBase (Qty.up r x) = u.inBase x := by
  simp [Qty.up, UInt64.toNat_mul, ofNat_toNat hr64, Nat.mod_eq_of_lt h, hr, Nat.mul_assoc]

private theorem lim_lt (r : Nat) : (2 ^ 64 - 1) / r < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)

/-- The checked conversion succeeds when the plain one does not overflow. -/
theorem up?_ok (hr : 0 < r) (h : x.toNat * r < 2 ^ 64) : Qty.up? r x = .ok (Qty.up r x) := by
  have hx : x.toNat ≤ (2 ^ 64 - 1) / r := (Nat.le_div_iff_mul_le hr).2 (by omega)
  simp [Qty.up?, Qty.up, UInt64.le_iff_toNat_le, ofNat_toNat (lim_lt r), hx]

/-- The checked conversion fails when the plain one overflows. -/
theorem up?_err (hr : 0 < r) (h : 2 ^ 64 ≤ x.toNat * r) : Qty.up? r x = .error () := by
  have hx : ¬ x.toNat ≤ (2 ^ 64 - 1) / r := fun hx =>
    absurd ((Nat.le_div_iff_mul_le hr).1 hx) (by omega)
  simp [Qty.up?, UInt64.le_iff_toNat_le, ofNat_toNat (lim_lt r), hx]

/-- A successful checked conversion returns the same amount in the finer unit. -/
theorem inBase_up? (hr : u.scale = r * v.scale) (hr64 : r < 2 ^ 64) {y : UInt64}
    (h : Qty.up? r x = .ok y) :
    v.inBase y = u.inBase x := by
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right (hr ▸ u.scale_pos)
  by_cases ho : x.toNat * r < 2 ^ 64
  · rw [up?_ok hr0 ho] at h; cases h; exact inBase_up hr hr64 ho
  · rw [up?_err hr0 (by omega)] at h; cases h

/-- Converting to a coarser unit rounds down, so `r.inBase ≤ x.inBase < r.inBase + v.scale`. -/
theorem inBase_floorDiv (hr : v.scale = r * u.scale) (hr64 : r < 2 ^ 64) :
    v.inBase (Qty.floorDiv r x) ≤ u.inBase x ∧ u.inBase x < v.inBase (Qty.floorDiv r x) + v.scale := by
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right (hr ▸ v.scale_pos)
  simp only [Qty.floorDiv, inBase_def, UInt64.toNat_div, ofNat_toNat hr64, hr]
  have h1 := Nat.div_mul_le_self x.toNat r
  have h2 := Nat.lt_div_mul_add (a := x.toNat) hr0
  constructor
  · rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
  · rw [← Nat.mul_assoc, ← Nat.add_mul]; exact Nat.mul_lt_mul_of_pos_right h2 u.scale_pos

/-- The carry `(m + (r - 1)) / r` of `ceilDiv` is 0 when the division is exact and 1
otherwise. -/
private theorem carry_eq (hr0 : 0 < r) (m : Nat) (hm : m < r) :
    (m + (r - 1)) / r = if m = 0 then 0 else 1 := by
  split
  · subst m; exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Converting to a coarser unit with `toCeil` rounds up, so
`x.inBase ≤ r.inBase < x.inBase + v.scale`. -/
theorem inBase_ceilDiv (hr : v.scale = r * u.scale) (hr63 : r ≤ 2 ^ 63) :
    u.inBase x ≤ v.inBase (Qty.ceilDiv r x) ∧
      v.inBase (Qty.ceilDiv r x) < u.inBase x + v.scale := by
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right (hr ▸ v.scale_pos)
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have hdm := Nat.div_add_mod x.toNat r
  have hm : x.toNat % r < r := Nat.mod_lt _ hr0
  have hc := carry_eq hr0 _ hm
  -- the quotient leaves room for the carry
  have hq : x.toNat % r ≠ 0 → x.toNat / r + 1 < 2 ^ 64 := fun h => by
    have : r * (x.toNat / r) < x.toNat := by omega
    have : x.toNat / r < x.toNat := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hr0) this
    omega
  have hd : x.toNat / r ≤ x.toNat := Nat.div_le_self _ _
  have hval : (Qty.ceilDiv r x).toNat = x.toNat / r + (if x.toNat % r = 0 then 0 else 1) := by
    simp only [Qty.ceilDiv, UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
      ofNat_toNat (show r < 2 ^ 64 by omega), ofNat_toNat (show r - 1 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show x.toNat % r + (r - 1) < 2 ^ 64 by omega), hc]
    split <;> rename_i h0 <;> simp [h0] at hq ⊢ <;> omega
  simp only [inBase_def, hval, hr, ← Nat.mul_assoc]
  constructor
  · apply Nat.mul_le_mul_right; split <;> rw [Nat.add_mul] <;> simp [Nat.mul_comm] <;> omega
  · rw [← Nat.add_mul]; apply Nat.mul_lt_mul_of_pos_right _ u.scale_pos
    split <;> rw [Nat.add_mul] <;> simp [Nat.mul_comm] <;> omega

end QUnit

end Millipede
