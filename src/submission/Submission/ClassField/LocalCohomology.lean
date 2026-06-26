import Mathlib.FieldTheory.Galois.Infinite

/-!
# Class Field Theory, Chapter I, Theorem A.4(b)

For a possibly infinite Galois extension, taking a fixed field does not
distinguish a subgroup of the Galois group from its topological closure.  In
particular, the subgroup fixing that field is exactly the closure.
-/

namespace Submission.CField.LocalCohomology

/-- **Theorem I.A.4(b), fixed-field assertion.** A subgroup of an infinite
Galois group and its topological closure have the same fixed field. -/
theorem fixed_topological_closure
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (H : Subgroup Gal(E/K)) :
    IntermediateField.fixedField H.topologicalClosure =
      IntermediateField.fixedField H := by
  apply le_antisymm
  · exact IntermediateField.fixedField_le H.le_topologicalClosure
  · rw [IntermediateField.le_iff_le]
    apply H.topologicalClosure_minimal
    · exact (IntermediateField.le_iff_le H
        (IntermediateField.fixedField H)).mp le_rfl
    · exact InfiniteGalois.fixingSubgroup_isClosed _

/-- **Theorem I.A.4(b), closure assertion.** The subgroup fixing the fixed
field of `H` is the topological closure of `H`. -/
theorem fixing_topological_closure
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (H : Subgroup Gal(E/K)) :
    (IntermediateField.fixedField H).fixingSubgroup =
      H.topologicalClosure := by
  let C : ClosedSubgroup Gal(E/K) :=
    ⟨H.topologicalClosure, H.isClosed_topologicalClosure⟩
  calc
    (IntermediateField.fixedField H).fixingSubgroup =
        (IntermediateField.fixedField H.topologicalClosure).fixingSubgroup := by
      rw [fixed_topological_closure H]
    _ = H.topologicalClosure := InfiniteGalois.fixingSubgroup_fixedField C

end Submission.CField.LocalCohomology
