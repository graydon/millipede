import Millipede.Compile.LowerLawful
import Millipede.Core.Wf
import Millipede.Compile.HandBack

/-!
# Why `compile` checks the hand-back condition

When a `&mut` slice borrow ends, the value semantics writes the handed-back view into the array
with `vunview`, which takes element `lo + k` from the view's cell `k` only if that cell is full,
while the machine has written the elements in place. The refinement therefore needs the write-back
condition `Place.backOk`, that the handed-back view still has its cells `0 … len-1` full. This is
not an obligation of `Exp.safe`; it follows from the hand-back condition `Exp.HB`, a syntactic
condition that `compile` checks.

This module shows that the check is needed, because the other checks do not imply the write-back
condition. Those are the lowered fragment's hand-back layout `Exp.Conf` and view discipline
`Exp.VSafe`, the certificates `Exp.certified` and the borrow checker `Exp.wf`. `Exp.Conf` checks
only the tail constructor's placements, and a `Slots` value has no tags, so an empty cell is
represented by any bytes. A constructor `dropCtor` that builds `(a, Slots.empty)`, keeping the
result and dropping the view's cells, therefore has a valid layout certificate and the pair's plan.

A body that writes `r[0]! := 5` and hands back `dropCtor ((), r)` passes all those checks, yet its
handed-back view is empty. The lens write-back leaves the array as it was, while the machine, which
writes through the pointer, holds `5` at element `0`. `dropCtor` has no hand-back certificate,
because its value does not have its arguments' occupancies, so `Exp.HB` fails and `compile`
refuses the term. The same body handing back with the certified pair `goodCtor`, as `mp def` builds
it, is accepted.
-/

namespace Millipede.Flat.BackOk

/-- The pair `(a, ∅)`, which keeps the first component and drops every cell of the view. Its
layout is the pair's, with the same `CtorKind.struct` plan. -/
def dropBuild (env : Env [Ty.unit, Ty.view Ty.u64 2]) : (Ty.pair Ty.unit (Ty.view Ty.u64 2)).carrier :=
  (env.get .here, Slots.empty 2)

/-- `dropBuild` satisfies the layout law of a constructor, because any bytes represent an empty
cell. -/
theorem dropLaw : CtorLaw [Ty.unit, Ty.view Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) .struct
    dropBuild := by
  have hp := CtorLaw.pair Ty.unit (Ty.view Ty.u64 2)
  have hpl : planOf [Ty.unit, Ty.view Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) .struct =
      ([[alignUp 0 Ty.unit.align],
        [alignUp (alignUp 0 Ty.unit.align + Ty.unit.size) (Ty.view Ty.u64 2).align]], none) := rfl
  refine ⟨hp.1, hp.2.1, hp.2.2.1, fun env bs hl ht ha => ?_⟩
  match env with
  | .cons x (.cons _ .nil) =>
    rw [hpl] at ha
    obtain ⟨h1, h2, _⟩ := ha
    refine hp.2.2.2 (.cons x (.cons (Slots.empty 2) .nil)) bs hl ht ?_
    rw [hpl]
    refine ⟨h1, fun o ho => ⟨(h2 o ho).1, fun i h => ?_⟩, trivial⟩
    show Slots.cellRepr (Vector.replicate 2 none)[i] _
    simp [Slots.cellRepr]

/-- The certified constructor that drops the view's cells. -/
def dropCtor : Ctor [Ty.unit, Ty.view Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) :=
  ⟨"pair", .struct, dropBuild, some ⟨dropLaw⟩, none⟩

/-- The slice `a[0..1]` of the array variable. -/
def slice : Place [Ty.arr Ty.u64 2] (Ty.view Ty.u64 2) := .range (.var .here) (.lit 0) (.lit 1)

/-- The borrow body `r[0]! := 5; dropCtor ((), r)`. -/
def body : Exp [Ty.view Ty.u64 2, Ty.arr Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) :=
  .assign (.slot (.var .here) (.lit 0)) (.lit 5)
    (.mk dropCtor (.cons (.lit ()) (.cons (.var .here) .nil)))

/-- `let _ := { let r = &mut a[0..1]; r[0]! := 5; dropCtor ((), r) }; ()`. -/
def badBorrow : Exp [Ty.arr Ty.u64 2] Ty.unit :=
  .borrowMut slice body (.atom (.lit ()))

/-- The term passes the other checks, which are the hand-back layout and the view discipline of
the lowered fragment, the certificates and the borrow checker. -/
theorem badBorrow_checks :
    badBorrow.certified = true ∧ badBorrow.wf = true ∧
      body.Conf (borrowTl Ty.unit (Ty.view Ty.u64 2)) = true ∧
      body.VSafe 0 (borrowTl Ty.unit (Ty.view Ty.u64 2)) = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The hand-back condition fails, so `compile`'s memory checks refuse the term. -/
theorem badBorrow_refused : body.HB 0 = false ∧ badBorrow.memOk = false := by
  refine ⟨by decide, by decide⟩

/-- The pair constructor with the hand-back certificate, built as `Ctor.pairMk` builds it. -/
def goodCtor : Ctor [Ty.unit, Ty.view Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) :=
  ⟨"pair", .struct, fun env => (env.get .here, env.get (.there .here)),
    some ⟨CtorLaw.pair Ty.unit (Ty.view Ty.u64 2)⟩, some ⟨fun | .cons _ (.cons _ .nil) => rfl⟩⟩

/-- The borrow body `r[0]! := 5; goodCtor ((), r)`. -/
def goodBody : Exp [Ty.view Ty.u64 2, Ty.arr Ty.u64 2] (.pair Ty.unit (Ty.view Ty.u64 2)) :=
  .assign (.slot (.var .here) (.lit 0)) (.lit 5)
    (.mk goodCtor (.cons (.lit ()) (.cons (.var .here) .nil)))

/-- With a certified hand-back the term is accepted, and its handed-back view keeps its
element. -/
theorem goodBorrow_accepted :
    goodBody.HB 0 = true ∧
      (Exp.borrowMut (v := Ty.unit) slice goodBody (.atom (.lit ()))).memOk = true := by
  refine ⟨by decide, by decide⟩

/-- The array `[0, 0]`. -/
def env0 : Env [Ty.arr Ty.u64 2] := .cons (Vector.replicate 2 0) .nil

/-- The handed-back view is empty, so the write-back obligation fails. -/
theorem badBorrow_not_backOk (ω : Oracle) (w : World) :
    ¬ slice.backOk env0 (body.denote ω (.cons (slice.get env0) env0) w).1.2 := by
  have he : (body.denote ω (.cons (slice.get env0) env0) w).1.2 = Slots.empty 2 := rfl
  rw [he]
  intro h
  exact absurd (h 0 (by decide)) (by decide)

/-- The lens write-back discards the body's write. After the borrow the source's array is still
`[0, 0]`, while the body wrote `5` to element `0` of the view, which in memory is element `0` of
the array. -/
theorem badBorrow_discards (ω : Oracle) (w : World) :
    slice.set env0 (body.denote ω (.cons (slice.get env0) env0) w).1.2 = env0 ∧
      (body.denote ω (.cons (slice.get env0) env0) w).1.2 = Slots.empty 2 ∧
      (Place.slot (Γ := [Ty.view Ty.u64 2, Ty.arr Ty.u64 2]) (.var .here) (.lit (0 : UInt64))).set
        (.cons (slice.get env0) env0) (5 : UInt64) =
        .cons (Slots.setCell (slice.get env0) 0 (some 5)) env0 := by
  have he : (body.denote ω (.cons (slice.get env0) env0) w).1.2 = Slots.empty 2 := rfl
  rw [he]
  refine ⟨?_, rfl, rfl⟩
  show Env.cons (vunview (Vector.replicate 2 (0 : UInt64)) 0 1 (Slots.empty 2)) .nil = env0
  unfold env0
  congr 1

end Millipede.Flat.BackOk
