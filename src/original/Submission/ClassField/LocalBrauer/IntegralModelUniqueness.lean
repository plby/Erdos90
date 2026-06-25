import Submission.ClassField.LocalBrauer.CanonicalUnramifiedTower
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Uniqueness from an unramified integral model

This file develops the algebraic bridge needed to identify a finite
unramified local extension with the canonical root-generated level.  The
first step is independent of ramification: if `E = K(e)` and `K` is the
fraction field of `A`, then `E` is the fraction field of `A[e]`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open Polynomial

/-- Clearing coefficients in a polynomial expression shows that adjoining
an element commutes with passage to fraction fields. -/
theorem fraction_adjoin_top
    (A K E : Type u) [CommRing A] [IsDomain A] [Nontrivial A]
    [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] (e : E)
    (hgen : Algebra.adjoin K ({e} : Set E) = ⊤) :
    IsFractionRing (Algebra.adjoin A ({e} : Set E)) E := by
  let U := Algebra.adjoin A ({e} : Set E)
  apply IsFractionRing.of_field U E
  intro z
  have hzK : z ∈ Algebra.adjoin K ({e} : Set E) := by
    rw [hgen]
    trivial
  obtain ⟨t, ht⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin
      (nonZeroDivisors A) K ({e} : Set E) z hzK
  have ht' : algebraMap A E t * z ∈ Algebra.adjoin A ({e} : Set E) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def] using ht
  let y : U := ⟨algebraMap A E t,
    (Algebra.adjoin A ({e} : Set E)).algebraMap_mem t⟩
  let x : U := ⟨algebraMap A E t * z, ht'⟩
  refine ⟨x, y, ?_⟩
  have hy : (algebraMap U E y) ≠ 0 := by
    change algebraMap A E t ≠ 0
    have hAE : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A K E]
      exact (algebraMap K E).injective.comp
        (IsFractionRing.injective A K)
    intro hz
    apply nonZeroDivisors.ne_zero t.property
    apply hAE
    simpa using hz
  apply (eq_div_iff hy).2
  simp [x, y, mul_comm]

/-- Formal unramifiedness of a generated integral model passes to a
separable extension of fraction fields. -/
theorem separable_formally_unramified
    (A K E : Type u) [CommRing A] [IsDomain A] [Nontrivial A]
    [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Module.Finite K E]
    [Algebra A E]
    [IsScalarTower A K E] (e : E)
    (hgen : Algebra.adjoin K ({e} : Set E) = ⊤)
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E))) :
    Algebra.IsSeparable K E := by
  let U := Algebra.adjoin A ({e} : Set E)
  letI : IsFractionRing U E :=
    fraction_adjoin_top A K E e hgen
  letI : Algebra.FormallyUnramified A U := hunramified
  letI : Algebra.FormallyUnramified U E :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors U)
  letI : Algebra.FormallyUnramified A E :=
    Algebra.FormallyUnramified.comp A U E
  letI : Algebra.FormallyUnramified K E :=
    Algebra.FormallyUnramified.of_restrictScalars A K E
  exact Algebra.FormallyUnramified.isSeparable K E

/-- Galoisness is not needed in the canonical comparison: separability and
splitting already identify an extension of the right degree with the
canonical level. -/
theorem alg_separable_splits
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] (n : ℕ) [NeZero n]
    (hdegree : Module.finrank K L = n)
    (hsplit : ((localFrobeniusPolynomial K n).map
      (algebraMap K L)).Splits) :
    Nonempty (L ≃ₐ[K] canonicalUnramifiedLevel K n) := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E : IntermediateField K (SeparableClosure K) := i.fieldRange
  let e : L ≃ₐ[K] E := AlgEquiv.ofInjectiveField i
  letI : Module.Finite K E := Module.Finite.equiv e.toLinearEquiv
  have hdegreeE : Module.finrank K E = n := by
    rw [← e.toLinearEquiv.finrank_eq, hdegree]
  have hsplitE :
      ((localFrobeniusPolynomial K n).map (algebraMap K E)).Splits := by
    have hs := hsplit.map e.toAlgHom.toRingHom
    simpa [localFrobeniusPolynomial, localResidueCard, map_map] using hs
  have hsplitClosure :
      ((localFrobeniusPolynomial K n).map
        (algebraMap K (SeparableClosure K))).Splits := by
    have hs := hsplitE.map E.val.toRingHom
    simpa [map_map] using hs
  let F : IntermediateField K (SeparableClosure K) :=
    IntermediateField.adjoin K
      ((localFrobeniusPolynomial K n).rootSet (SeparableClosure K))
  letI : (localFrobeniusPolynomial K n).IsSplittingField K F :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplitClosure
  letI : Normal K F :=
    Normal.of_isSplittingField (localFrobeniusPolynomial K n)
  have hnormalClosure :
      IntermediateField.normalClosure K F (SeparableClosure K) = F :=
    (IntermediateField.normal_iff_normalClosure_eq (K := F)).mp inferInstance
  have hcanonical_eq :
      (canonicalUnramifiedLevel K n :
        IntermediateField K (SeparableClosure K)) = F := by
    change IntermediateField.normalClosure K
      (IntermediateField.adjoin K
        ((localFrobeniusPolynomial K n).rootSet (SeparableClosure K)))
        (SeparableClosure K) = F
    exact hnormalClosure
  have hF_le_E : F ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    exact (IntermediateField.splits_iff_mem hsplitClosure).mp hsplitE
  have hcanonical_le :
      (canonicalUnramifiedLevel K n :
        IntermediateField K (SeparableClosure K)) ≤ E := by
    rw [hcanonical_eq]
    exact hF_le_E
  have hcanonical_eq_E :
      (canonicalUnramifiedLevel K n :
        IntermediateField K (SeparableClosure K)) = E :=
    IntermediateField.eq_of_le_of_finrank_eq hcanonical_le (by
      rw [unramified_level_finrank K n, hdegreeE])
  exact ⟨e.trans (IntermediateField.equivOfEq hcanonical_eq_E.symm)⟩

end

end Submission.CField.LBrauer
