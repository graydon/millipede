import Lean
import Millipede.Meta.ANF

/-!
# Quantities in `mp def`

Two commands declare dimensions and units. `mp dimension Size` defines `Size : Dim`, and
`mp unit KiB : Size := 1024` defines `KiB : QUnit` of dimension `Size` with a scale of 1024 base
units, together with the simp lemma `KiB.scale_eq : KiB.scale = 1024`.

In `mp def` the type `Q KiB` is the surface type `STy.qty`, which is erased to `Ty.u64`. The
elaborator calls the rules of this module, which are the following.
- `KiB e`, where `e : UInt64` is typically a literal as in `KiB 4`, is a count of KiB, and
  `q.val` is the count. Neither emits code. A bare numeral is a `UInt64` and never a quantity.
- `+ - < <= > >= == !=` need the same unit on both sides. `*` takes a quantity and a `UInt64` in
  either order, and `/` and `%` take a quantity and a `UInt64` divisor. The bitwise operations
  and shifts are not defined on quantities.
- `q.to v` wraps, `q.to! v` carries the obligation that the product fits, `q.to? v` is checked,
  and `q.toFloor v` and `q.toCeil v` round. Each converts within a dimension with the code of
  `Qty.up`, `Qty.up?`, `Qty.floorDiv` or `Qty.ceilDiv`, and a conversion with ratio 1 emits no
  code.
- `+! -! *!` on quantities type like `+ - *` and carry the overflow obligation.

A mismatch is reported at the operand, with the units named. Quantities are described in
doc/design/units.md.
-/

namespace Millipede.Meta

open Lean Elab Command Term Meta

/-! ## Declarations -/

/-- `mp dimension Size` declares a dimension tag `Size : Dim`. -/
syntax (name := mpDimension) (docComment)? mpKw &"dimension " ident : command

/-- `mp unit KiB : Size := 1024` declares a unit of dimension `Size` worth 1024 base units. -/
syntax (name := mpUnit) (docComment)? mpKw &"unit " ident " : " ident " := " num : command

elab_rules : command
  | `(mpDimension| $[$doc?]? mp dimension $d:ident) => do
    let full := (← getCurrNamespace) ++ d.getId
    elabCommand (← `($[$doc?]? def $d : Millipede.Dim := ⟨$(quote full.toString)⟩))
  | `(mpUnit| $[$doc?]? mp unit $u:ident : $d:ident := $s:num) => do
    if s.getNat == 0 then throwErrorAt s "a unit's scale must be positive"
    elabCommand (← `($[$doc?]? def $u : Millipede.QUnit := { dim := $d, scale := $s }))
    let eq := mkIdentFrom u (u.getId ++ `scale_eq)
    elabCommand (← `(@[simp, grind =] theorem $eq : Millipede.QUnit.scale $u = $s := rfl))

/-! ## Typing rules -/

/-- A quantity type. -/
def STy.isQty : STy → Bool
  | .qty .. => true
  | _ => false

/-- The spelling of a quantity type with its dimension, for messages. -/
def qtyFmt : STy → String
  | t@(.qty _ d _) => s!"{t} (dimension {d.splitOn "." |>.getLast!})"
  | t => toString t

/-- A hint for a type mismatch between two surface types, when a quantity is involved. -/
def qtyHint (expected actual : STy) : String :=
  match expected, actual with
  | .qty u d s, .qty _ d' s' =>
    let un := u.componentsRev.head!
    if d != d' then ": quantities of different dimensions never mix"
    else s!": units of one dimension do not mix; convert with " ++
      (if s' % s == 0 then s!"`.to {un}`" else if s % s' == 0 then
        s!"`.toFloor {un}` or `.toCeil {un}`" else "a conversion through a finer common unit")
  | .qty u _ _, .u64 => s!": a UInt64 is not a quantity; write `{u.componentsRev.head!} n` for a \
      count of {u.componentsRev.head!}"
  | .u64, .qty .. => ": a quantity is not a UInt64; take its count with `.val`"
  | _, _ => ""

/-- The result type of `a op b` when one operand is a quantity, or an error. `op` is one of the
binary operators of `binOps`, or `==` or `!=`. -/
def qtyBinOp (op : String) (ta tb : STy) : Except String STy :=
  -- `+! -! *!`, which carry an obligation, type like `+ - *`.
  let op := if op == "+!" then "+" else if op == "-!" then "-" else if op == "*!" then "*" else op
  let isQ : STy → Bool := fun | .qty .. => true | _ => false
  let cmp := ["<", "<=", "≤", ">", ">=", "≥", "==", "!=", "≠"]
  if op == "+" || op == "-" || cmp.contains op then
    if ta == tb then .ok (if cmp.contains op then .bool else ta)
    else if isQ ta && isQ tb then
      -- Suggest converting the coarser operand to the finer unit.
      let (fine, coarse) := match ta, tb with
        | .qty _ _ s, .qty _ _ s' => if s ≤ s' then (ta, tb) else (tb, ta)
        | _, _ => (ta, tb)
      .error s!"`{op}` needs quantities of the same unit, but the operands are {qtyFmt ta} and \
        {qtyFmt tb}{qtyHint fine coarse}"
    else .error s!"`{op}` needs quantities of the same unit, but the operands are {ta} and \
        {tb}{if isQ ta then qtyHint ta tb else qtyHint tb ta}"
  else if op == "*" then
    match ta, tb with
    | .qty .., .u64 => .ok ta
    | .u64, .qty .. => .ok tb
    | _, _ => .error s!"`*` multiplies a quantity by a dimensionless UInt64, not {ta} by {tb} \
        (there is no algebra of dimensions; go through `.val`)"
  else if op == "/" || op == "%" then
    match ta, tb with
    | .qty .., .u64 => .ok ta
    | _, _ => .error s!"`{op}` divides a quantity by a dimensionless UInt64, not {ta} by {tb} \
        (go through `.val`)"
  else .error s!"`{op}` is not defined on quantities ({ta}, {tb}); go through `.val`"

/-- How a conversion between units is computed. -/
inductive QConv where
  /-- The same count, for ratio 1, with no code. -/
  | same
  /-- `x * r` by `Qty.up`, which wraps. -/
  | up (r : Nat)
  /-- `x *! r`, which is `Qty.up` with the obligation that the product fits. -/
  | upNuw (r : Nat)
  /-- `if x ≤ (2^64-1)/r then ok (x * r) else err ()`, as `Qty.up?`. -/
  | upChk (r : Nat)
  /-- `x / r`, as `Qty.floorDiv`. -/
  | floor (r : Nat)
  /-- `x / r + (x % r + (r - 1)) / r`, as `Qty.ceilDiv`. -/
  | ceil (r : Nat)

/-- The conversion methods. -/
def qtyMethods : List Name := [`to, `to!, `to?, `toFloor, `toCeil]

/-- The conversion `q.meth v` from `src` to `tgt`, or an error. -/
def qtyConv (meth : Name) (src tgt : STy) : Except String QConv := do
  let .qty u d s := src | .error s!"`.{meth}` converts quantities, but this has type {src}"
  let .qty v d' s' := tgt | .error s!"`.{meth}` needs a unit as its argument"
  let un := u.componentsRev.head!; let vn := v.componentsRev.head!
  unless d == d' do
    .error s!"cannot convert {qtyFmt src} to {qtyFmt tgt}: a conversion stays in one dimension"
  if meth == `to || meth == `to! || meth == `to? then
    if s % s' == 0 then
      let r := s / s'
      unless r < 2 ^ 64 do .error s!"the ratio {r} of {un} to {vn} does not fit in UInt64"
      return if meth == `to? then .upChk r else if r == 1 then .same
        else if meth == `to! then .upNuw r else .up r
    if s' % s == 0 then
      .error s!"`.{meth} {vn}` would round: {vn} is coarser than {un}; write `.toFloor {vn}` or \
        `.toCeil {vn}`"
    .error s!"{un} and {vn} have no whole ratio; convert through a finer common unit"
  if s' % s == 0 then
    let r := s' / s
    unless r ≤ 2 ^ 63 do .error s!"the ratio {r} of {vn} to {un} exceeds 2^63"
    return if r == 1 then .same else if meth == `toFloor then .floor r else .ceil r
  if s % s' == 0 then
    .error s!"`.{meth} {vn}`: {vn} is finer than {un}, the conversion is exact; write `.to {vn}`"
  .error s!"{un} and {vn} have no whole ratio; convert through a finer common unit"

/-- The result type of a conversion to `tgt`. -/
def qtyConvTy (meth : Name) (tgt : STy) : STy :=
  if meth == `to? then .result .unit tgt else tgt

/-- The code of a conversion of the atom `x`, with fresh names from `fresh`. -/
def qtyConvE {m : Type → Type} [Monad m] (fresh : m Name) (c : QConv) (x : SAtom) (tgt : STy) :
    m AExp := do
  let lit (n : Nat) : SAtom := .lit .u64 (toExpr (UInt64.ofNat n))
  let w (p : Name) : PrimInfo := ⟨p, [.u64, .u64], .u64⟩
  let v (n : Name) : SAtom := .var n .missing
  match c with
  | .same => return .atom x
  | .up r => return .prim (w ``Prim.mul) [x, lit r]
  | .upNuw r => return .prim (w ``Prim.mulNuw) [x, lit r]
  | .floor r => return .prim (w ``Prim.udiv) [x, lit r]
  | .ceil r =>
    -- This is the term that `x / r + (x % r + (r - 1)) / r` elaborates to from source, with the
    -- right operand's temporaries nested in its binding, so that erased code is the untyped
    -- program's.
    let a ← fresh; let b ← fresh; let c ← fresh; let d ← fresh
    return .let_ a .missing .u64 (.prim (w ``Prim.udiv) [x, lit r])
      (.let_ d .missing .u64
        (.let_ c .missing .u64
          (.let_ b .missing .u64 (.prim (w ``Prim.umod) [x, lit r]) (.prim (w ``Prim.add) [v b, lit (r - 1)]))
          (.prim (w ``Prim.udiv) [v c, lit r]))
        (.prim (w ``Prim.add) [v a, v d]))
  | .upChk r =>
    let ok ← fresh; let y ← fresh
    return .let_ ok .missing .bool (.prim ⟨``Prim.ule, [.u64, .u64], .bool⟩ [x, lit ((2 ^ 64 - 1) / r)])
      (.ite .missing (v ok)
        (.let_ y .missing tgt (.prim (w ``Prim.mul) [x, lit r]) (.ok .unit tgt (v y)))
        (.err .unit tgt (.lit .unit (mkConst ``Unit.unit))))

/-- The value of `e`, or its error message at `ref`. -/
def ofExceptAt {α : Type} (ref : Syntax) : Except String α → TermElabM α
  | .ok a => pure a
  | .error m => throwErrorAt ref m

/-- The unit named by a global identifier, a constant of type `QUnit`, as a surface type. -/
def unitSTy? (id : Syntax) : TermElabM (Option STy) := do
  let some c ← (try some <$> realizeGlobalConstNoOverload id catch _ => pure none) | return none
  let some ci := (← getEnv).find? c | return none
  unless ci.type.isConstOf ``QUnit do return none
  exprToSTy (mkApp (mkConst ``Q) (mkConst c))

end Millipede.Meta
