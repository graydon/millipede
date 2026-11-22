import Lean
import Millipede.Meta.ANF

/-!
# The three forms of `+ - *`

Each of `+ - *` on `UInt64` and `UInt8` has three forms in `mp def`.

- `a + b` wraps around. It is always defined and has no obligation. On bytes it is `Prim.trunc8`
  of the word result.
- `a +! b` carries the obligation that the mathematical result fits the width. On words it is
  `Prim.addNuw`, `Prim.subNuw` or `Prim.mulNuw`, whose obligations `x + y < 2^64`, `y ≤ x` and
  `x * y < 2^64` `Exp.safe` collects. On bytes the word operation wraps and the narrowing to a
  byte is `Prim.trunc8Nuw`, whose obligation that the word result is below `2^8` is exactly the
  absence of byte overflow for `+` and `*`. For `-` it is the absence of underflow, since a
  wrapped word is then at least `2^64 - 255`. The compiler emits the plain instruction, because
  the `…Nuw` primitives have the code of the wrapping primitive. Library code and anything that
  computes a size, an index, a count or a budget uses this form or the checked one, and the
  verified analyser discharges most of these obligations.
- `a +? b` is checked. Its type is `Result Unit T`, and it is `ok` of the result exactly when the
  result fits. It is built from the wrapping primitive, a comparison and a branch, has no
  obligation, and means `CheckedArith.addChk`.

The forms `+!`, `-!`, `*!`, `+?`, `-?` and `*?` are tokens of their own, so `a +! b` is not
`a + !b`. Outside `mp def`, in specifications, `+!` means Lean's `+`, which the obligation makes
equal, and `+?` means Lean's checked operation in `CheckedArith`. The choice of forms is recorded
as decision 14 in doc/design/decisions.md.
-/

namespace Millipede

/-- The checked arithmetic of a word type as ordinary Lean functions, which give `a +? b` its
meaning outside `mp def`. -/
class CheckedArith (α : Type) where
  addChk : α → α → Except Unit α
  subChk : α → α → Except Unit α
  mulChk : α → α → Except Unit α

instance : CheckedArith UInt64 where
  addChk a b := if a.toNat + b.toNat < 2 ^ 64 then .ok (a + b) else .error ()
  subChk a b := if b.toNat ≤ a.toNat then .ok (a - b) else .error ()
  mulChk a b := if a.toNat * b.toNat < 2 ^ 64 then .ok (a * b) else .error ()

instance : CheckedArith UInt8 where
  addChk a b := if a.toNat + b.toNat < 2 ^ 8 then .ok (a + b) else .error ()
  subChk a b := if b.toNat ≤ a.toNat then .ok (a - b) else .error ()
  mulChk a b := if a.toNat * b.toNat < 2 ^ 8 then .ok (a * b) else .error ()

end Millipede

namespace Millipede.Meta

open Lean

/-- `a +! b`: addition with the obligation that the sum fits. -/
syntax:65 (name := mpAddO) term:65 " +! " term:66 : term
/-- `a -! b`: subtraction with the obligation `b ≤ a`. -/
syntax:65 (name := mpSubO) term:65 " -! " term:66 : term
/-- `a *! b`: multiplication with the obligation that the product fits. -/
syntax:70 (name := mpMulO) term:70 " *! " term:71 : term
/-- `a +? b`, checked addition with the type `Result Unit T`. -/
syntax:65 (name := mpAddC) term:65 " +? " term:66 : term
/-- `a -? b`, checked subtraction with the type `Result Unit T`. -/
syntax:65 (name := mpSubC) term:65 " -? " term:66 : term
/-- `a *? b`, checked multiplication with the type `Result Unit T`. -/
syntax:70 (name := mpMulC) term:70 " *? " term:71 : term

macro_rules
  | `($a +! $b) => `($a + $b)
  | `($a -! $b) => `($a - $b)
  | `($a *! $b) => `($a * $b)
  | `($a +? $b) => `(Millipede.CheckedArith.addChk $a $b)
  | `($a -? $b) => `(Millipede.CheckedArith.subChk $a $b)
  | `($a *? $b) => `(Millipede.CheckedArith.mulChk $a $b)

/-- The binary arithmetic operators of the wrapping and obligated forms, each with its spelling
and `Prim` constructor. The plain `+ - *` wrap, and `+! -! *!` are the obligated `…Nuw`
primitives. -/
def arithOps : List (String × Name) :=
  [("+", ``Prim.add), ("-", ``Prim.sub), ("*", ``Prim.mul),
   ("+!", ``Prim.addNuw), ("-!", ``Prim.subNuw), ("*!", ``Prim.mulNuw)]

/-- The checked operators and the wrapping primitive each is built from. -/
def checkedOps : List (String × Name) :=
  [("+?", ``Prim.add), ("-?", ``Prim.sub), ("*?", ``Prim.mul)]

/-- The primitives of a byte operation. On bytes the word operation wraps, with no word
obligation because the operands are below `2^8`, and any obligation is on the narrowing. The
result is the word primitive to use and whether the narrowing is the obligated `trunc8Nuw`
instead of `trunc8`. -/
def bytePrim (p : PrimInfo) : PrimInfo × Bool :=
  if p.con == ``Prim.addNuw then ({ p with con := ``Prim.add }, true)
  else if p.con == ``Prim.subNuw then ({ p with con := ``Prim.sub }, true)
  else if p.con == ``Prim.mulNuw then ({ p with con := ``Prim.mul }, true)
  else (p, false)

/-- The checked form `a op? b`, where `op?` is one of `checkedOps`, on operands of type `t`, as
named ANF with result type `Result Unit t`. The operations used inside wrap. On words `+?` is
`let s := a + b; if s < a then err () else ok s`, `-?` is `if a < b then err () else ok (a - b)`,
and `*?` is `if a = 0 then ok 0 else let p := a * b; if p / a = b then ok p else err ()`. On
bytes, when `u8 = some (zext8, trunc8)`, the word result `r` of the widened operands is checked
by `255 < r`, after `a < b` for `-?`, and narrowed. `fresh` makes the temporaries. -/
def checkedAExp {m : Type → Type} [Monad m] (fresh : m Name) (op : String) (t : STy)
    (u8 : Option (PrimInfo × PrimInfo)) (a b : SAtom) : m (Option AExp) := do
  let some wc := checkedOps.lookup op | return none
  let w : PrimInfo := ⟨wc, [.u64, .u64], .u64⟩
  let cmp (c : Name) : PrimInfo := ⟨c, [.u64, .u64], .bool⟩
  let unitLit : SAtom := .lit .unit (mkConst ``Unit.unit)
  let err : AExp := .err .unit t unitLit
  let ok (x : SAtom) : AExp := .ok .unit t x
  let v (n : Name) : SAtom := .var n .missing
  let lit (k : Nat) : SAtom := .lit .u64 (toExpr (UInt64.ofNat k))
  match u8 with
  | none =>
    if op == "+?" then
      let s ← fresh; let c ← fresh
      return some (.let_ s .missing .u64 (.prim w [a, b])
        (.let_ c .missing .bool (.prim (cmp ``Prim.ult) [v s, a]) (.ite .missing (v c) err (ok (v s)))))
    if op == "-?" then
      let c ← fresh; let d ← fresh
      return some (.let_ c .missing .bool (.prim (cmp ``Prim.ult) [a, b])
        (.ite .missing (v c) err (.let_ d .missing .u64 (.prim w [a, b]) (ok (v d)))))
    let z ← fresh; let p ← fresh; let q ← fresh; let c ← fresh
    return some (.let_ z .missing .bool (.prim (cmp ``Prim.eq) [a, lit 0])
      (.ite .missing (v z) (ok (lit 0))
        (.let_ p .missing .u64 (.prim w [a, b])
          (.let_ q .missing .u64 (.prim ⟨``Prim.udiv, [.u64, .u64], .u64⟩ [v p, a])
            (.let_ c .missing .bool (.prim (cmp ``Prim.eq) [v q, b])
              (.ite .missing (v c) (ok (v p)) err))))))
  | some (zext, trunc) =>
    let x ← fresh; let y ← fresh; let r ← fresh; let c ← fresh; let n ← fresh
    let narrow : AExp :=
      .let_ c .missing .bool (.prim (cmp ``Prim.ult) [lit 255, v r])
        (.ite .missing (v c) err (.let_ n .missing t (.prim trunc [v r]) (ok (v n))))
    let body : AExp ← if op == "-?" then do
        let c0 ← fresh
        pure (.let_ c0 .missing .bool (.prim (cmp ``Prim.ult) [v x, v y])
          (.ite .missing (v c0) err (.let_ r .missing .u64 (.prim w [v x, v y]) narrow)))
      else pure (.let_ r .missing .u64 (.prim w [v x, v y]) narrow)
    return some (.let_ x .missing .u64 (.prim zext [a]) (.let_ y .missing .u64 (.prim zext [b]) body))

end Millipede.Meta
