import Submission.FieldTheory.Blueprint
import Submission.Group.PGroup


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

noncomputable def galoisFixedField
    {F L : Type*} [Field F] [Field L] [Algebra F L] [IsGalois F L]
    (H : ClosedSubgroup Gal(L/F)) [H.Normal] :
    Gal(L/F) ⧸ H.1 ≃* Gal(IntermediateField.fixedField H.1 / F) := by
  simpa using InfiniteGalois.normalAutEquivQuotient H

lemma fixed_galois_p
    {F L : Type*} [Field F] [Field L] [Algebra F L] [IsGalois F L]
    {p : ℕ} (H : ClosedSubgroup Gal(L/F)) [H.Normal]
    (hQuot : IsPGroup p (Gal(L/F) ⧸ H.1)) :
    IsPGroup p (Gal(IntermediateField.fixedField H.1/F)) := by
  exact hQuot.of_equiv (galoisFixedField H)

lemma intermediate_fg_dimensional
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) [FiniteDimensional F L] :
    L.FG := by
  classical
  haveI : Algebra.FiniteType F L := inferInstance
  haveI : Algebra.EssFiniteType F L := inferInstance
  exact IntermediateField.essFiniteType_iff.mp inferInstance

lemma intermediate_field_fg
    {F K K' : Type*} [Field F] [Field K] [Field K']
    [Algebra F K] [Algebra F K']
    (L : IntermediateField F K) (f : K →ₐ[F] K')
    (hL : L.FG) :
    (L.map f).FG := by
  classical
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image f, ?_⟩
  rw [← hs]
  rw [IntermediateField.adjoin_map]
  congr 1
  ext y
  simp

lemma intermediate_fg_i
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (hL : L.FG)
    (t : ι → IntermediateField F K)
    (hLe : L ≤ ⨆ i, t i) :
    ∃ s : Finset ι, L ≤ ⨆ i ∈ s, t i := by
  classical
  obtain ⟨gens, hgens⟩ := hL
  rw [← hgens] at hLe ⊢
  exact
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
      (IntermediateField F K)
      (IntermediateField.adjoin_finset_isCompactElement (F := F) (E := K) gens)
      t hLe

end Submission
