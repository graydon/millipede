import Millipede.Core.Lawful

/-!
# Layout laws for every parameter

`deriving Data` certifies a struct constructor with `Flat.CtorLaw.struct`, whose side condition
says that the placements of the fields are inside the value and pairwise disjoint. On a closed
layout it proves the condition by `decide`. For a parameterised struct such as
`structure Bump (T : Type) (n : Nat)` the layout is symbolic, because `Data.shape T` is opaque and
sizes are `n * …`, so `decide` cannot run. The side condition is then the theorem
`CtorLaw.structPlan`, which holds of every C layout.
-/

namespace Millipede.Flat

/-- The placements of a struct constructor are inside the value and disjoint, for every field
list whatever the fields' shapes, given that the arguments' sizes are the fields' sizes. -/
theorem CtorLaw.structPlan {S : Type} [inst : Data S] (fs : List (Field S))
    (hinst : inst = Data.struct fs) (ps : List Ty)
    (hps : ps.map (fun t => t.size) = (Fields.shapes fs).map Shape.size) :
    (∀ q ∈ placements ps (planOf ps ⟨S⟩ .struct).1, q.1 + q.2 ≤ (Data.shape S).size ∧
        ((planOf ps ⟨S⟩ .struct).2.isSome → 1 ≤ q.1)) ∧
      (placements ps (planOf ps ⟨S⟩ .struct).1).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) := by
  subst hinst
  have hlen : ps.length = (Fields.shapes fs).length := by
    simpa using congrArg List.length hps
  have hsz : ∀ j (h1 : j < ps.length) (h2 : j < (Fields.shapes fs).length),
      (ps[j]'h1).size = ((Fields.shapes fs)[j]'h2).size := by
    intro j h1 h2
    have := congrArg (·[j]?) hps
    simpa [List.getElem?_map, h1, h2] using this
  have hplan : (planOf ps (@Ty.mk S (Data.struct fs)) .struct) =
      ((Shape.prodOffsets 0 (Fields.shapes fs)).map fun o => [o], none) := rfl
  rw [hplan, placements_single _ _ (by simp [hlen])]
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    simp only [List.length_zipWith, Shape.prodOffsets_length] at hj
    simp only [List.getElem_zipWith, Option.isSome_none, Bool.false_eq_true, false_implies,
      and_true]
    have h2 : j < (Fields.shapes fs).length := by omega
    rw [hsz j (by omega) h2]
    have := Shape.fieldOffset_add_size_le (Fields.shapes fs) j h2
    rw [Shape.fieldOffset_eq _ _ h2] at this
    exact this
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_zipWith, Shape.prodOffsets_length] at hi hj
    simp only [List.getElem_zipWith]
    have h2 : j < (Fields.shapes fs).length := by omega
    left
    rw [hsz i (by omega) (by omega)]
    exact Shape.prodOffsets_disjoint 0 _ i j hij (by simpa using h2)

end Millipede.Flat
