import Submission.ClassField.Ideles.IdeleNorm
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Continuity of the idèle norm

The idèle norm is assembled from finite-dimensional field norms at the
finite and infinite completions.  This file records the general normed-field
continuity lemma and its archimedean specialization.  The nonarchimedean
specialization additionally requires comparison of the normalized adic
topologies on the two completion models.
-/

namespace Submission.CField.Ideles

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open scoped RestrictedProduct

noncomputable section

universe u

/-- The algebra norm of a finite-dimensional extension of normed fields is
continuous. -/
theorem continuous_algebra_dimensional
    {F E : Type*} [NontriviallyNormedField F] [NormedField E]
    [NormedAlgebra F E] [CompleteSpace F] [FiniteDimensional F E] :
    Continuous (Algebra.norm F : E → F) := by
  let b := Module.Free.chooseBasis F E
  rw [show (Algebra.norm F : E → F) =
      fun x ↦ Matrix.det (Algebra.leftMulMatrix b x) by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  simp_rw [Matrix.det_apply]
  apply continuous_finsetSum
  intro sigma _
  apply Continuous.smul continuous_const
  apply continuous_finsetProd
  intro i _
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  let coord : E →ₗ[F] F :=
    (Finsupp.lapply (sigma i)).comp b.repr.toLinearMap
  exact coord.continuous_of_finiteDimensional.comp
    (continuous_id.mul continuous_const)

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

omit [NumberField K] [NumberField L] in
/-- Each completed norm occurring in an archimedean idèle coordinate is
continuous. -/
theorem continuous_infinite_completion
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    Continuous (infiniteCompletionNorm (K := K) (L := L) v w) := by
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  let hw : AbsoluteValue.LiesOver w.1.1 v.1 :=
    infinite_lies_comap v w.1 w.2
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hw).toAlgebra
  letI : NormedAlgebra v.1.Completion w.1.1.Completion :=
    { toAlgebra := (completionLies v.1 w.1.1 hw).toAlgebra
      norm_smul_le r x := by
        change ‖completionLies v.1 w.1.1 hw r * x‖ ≤ ‖r‖ * ‖x‖
        calc
          _ ≤ ‖completionLies v.1 w.1.1 hw r‖ * ‖x‖ := norm_mul_le _ _
          _ = ‖r‖ * ‖x‖ := by
            congr 1
            simpa only [dist_zero_right, map_zero] using
              (completion_lies_isometry v.1 w.1.1 hw).dist_eq r 0 }
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  exact (continuous_algebra_dimensional
    (F := v.1.Completion) (E := w.1.1.Completion)).units_map _

omit [NumberField L] in
/-- The product of the completed norms above one archimedean place is
continuous. -/
theorem continuous_infinite_norm (v : InfinitePlace K) :
    Continuous (infiniteNorm (K := K) (L := L) v) := by
  classical
  letI : Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
    infiniteCor84ExtensionsFintype v
  have h : Continuous fun x : (InfiniteAdeleRing L)ˣ ↦
      ∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1) := by
    apply continuous_finsetProd
    intro w _
    apply (continuous_infinite_completion (K := K) (L := L) v w).comp
    exact (continuous_apply w.1).comp
      (ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace L ↦
        w.1.Completion)).continuous
  convert h using 1

omit [NumberField L] in
/-- The norm on the archimedean component of the idèles is continuous. -/
theorem continuous_infinite_idele :
    Continuous (infiniteIdeleNorm (K := K) (L := L)) := by
  apply (ContinuousMulEquiv.piUnits (M := fun v : InfinitePlace K ↦
    v.1.Completion)).symm.continuous.comp
  exact continuous_pi fun v ↦ continuous_infinite_norm
    (K := K) (L := L) v

set_option maxHeartbeats 1000000 in
-- Unfolding both dependent restricted-product stages is elaboration-heavy.
omit [FiniteDimensional K L] in
/-- If every completed finite-place norm is continuous, then the assembled
norm on finite idèles is continuous for the restricted-product topologies.

On a principal source stage `S`, the target lies in the principal stage
obtained by deleting the contractions of `Sᶜ`.  Both complements are
finite, and continuity on those stages is coordinatewise continuity of a
finite product. -/
theorem continuous_idele_completion
    (hlocal : ∀
      (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
      (Q : UpperPrimeFactors (K := K) (L := L) P),
      Continuous (finiteCompletionNorm (K := K) (L := L) P Q)) :
    Continuous (finiteIdeleNorm (K := K) (L := L)) := by
  classical
  change @Continuous
    (Πʳ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
      [(Q.adicCompletion L)ˣ,
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q])
    (Πʳ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      [(P.adicCompletion K)ˣ,
        IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P])
    (RestrictedProduct.topologicalSpace
      (fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        (Q.adicCompletion L)ˣ)
      (fun Q ↦ (IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q : Set (Q.adicCompletion L)ˣ))
      Filter.cofinite)
    (RestrictedProduct.topologicalSpace
      (fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
        (P.adicCompletion K)ˣ)
      (fun P ↦ (IdeleUnitSubgroup
        (NumberField.RingOfIntegers K) K P : Set (P.adicCompletion K)ˣ))
      Filter.cofinite)
    (finiteIdeleNorm (K := K) (L := L))
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  let contract : HeightOneSpectrum (NumberField.RingOfIntegers L) →
      HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    fun Q ↦ Q.under (NumberField.RingOfIntegers K)
  let badLower : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    contract '' Sᶜ
  let T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) := badLowerᶜ
  have hSc : Sᶜ.Finite := by
    rwa [Filter.le_principal_iff, Filter.mem_cofinite] at hS
  have hbadLower : badLower.Finite := hSc.image contract
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simpa only [T, compl_compl] using hbadLower
  let g :
      (Πʳ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
        [(Q.adicCompletion L)ˣ,
          IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q]_[Filter.principal S]) →
      (Πʳ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        [(P.adicCompletion K)ˣ,
          IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P]_[Filter.principal T]) :=
    fun x ↦ RestrictedProduct.mk
      (fun P ↦ ∏ Q : UpperPrimeFactors (K := K) (L := L) P,
        finiteCompletionNorm (K := K) (L := L) P Q
          (x (upperPrime (K := K) (L := L) P Q)))
      (by
        rw [Filter.eventually_principal]
        intro P hPT
        change P ∉ badLower at hPT
        apply Subgroup.prod_mem
        intro Q _
        apply completion_unit_subgroup (K := K) (L := L)
        have hxS := x.2
        rw [Filter.eventually_principal] at hxS
        apply hxS
        by_contra hupperS
        apply hPT
        exact ⟨upperPrime (K := K) (L := L) P Q, hupperS,
          upperPrime_under (K := K) (L := L) P Q⟩)
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro P
    have hcoord : Continuous (fun x :
        Πʳ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
          [(Q.adicCompletion L)ˣ,
            IdeleUnitSubgroup
              (NumberField.RingOfIntegers L) L Q]_[Filter.principal S] ↦
        ∏ Q : UpperPrimeFactors (K := K) (L := L) P,
          finiteCompletionNorm (K := K) (L := L) P Q
            (x (upperPrime (K := K) (L := L) P Q))) := by
      apply continuous_finsetProd
      intro Q _
      exact (hlocal P Q).comp
        (RestrictedProduct.continuous_eval
          (R := fun Q : HeightOneSpectrum
            (NumberField.RingOfIntegers L) ↦ (Q.adicCompletion L)ˣ)
          (A := fun Q ↦ (IdeleUnitSubgroup
            (NumberField.RingOfIntegers L) L Q : Set (Q.adicCompletion L)ˣ))
          (upperPrime (K := K) (L := L) P Q))
    simpa only [Function.comp_apply, g, RestrictedProduct.mk_apply] using hcoord
  have hinclusion : Continuous
      (RestrictedProduct.inclusion
        (fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
          (P.adicCompletion K)ˣ)
        (fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
          (IdeleUnitSubgroup
          (NumberField.RingOfIntegers K) K P : Set (P.adicCompletion K)ˣ))
        hT ∘ g) :=
    (RestrictedProduct.continuous_inclusion
      (R := fun P : HeightOneSpectrum
        (NumberField.RingOfIntegers K) ↦ (P.adicCompletion K)ˣ)
      (A := fun P ↦ (IdeleUnitSubgroup
        (NumberField.RingOfIntegers K) K P : Set (P.adicCompletion K)ˣ))
      hT).comp hg
  apply hinclusion.congr
  intro x
  apply RestrictedProduct.ext
  intro P
  rfl

/-- Once continuity of the finite restricted-product norm is known, the
full idèle norm is continuous by the product topology. -/
theorem continuous_idele_norm
    (hfinite : Continuous (finiteIdeleNorm (K := K) (L := L))) :
    Continuous (ideleNorm (K := K) (L := L)) := by
  exact (continuous_infinite_idele (K := K) (L := L)).comp continuous_fst
    |>.prodMk (hfinite.comp continuous_snd)

end

end Submission.CField.Ideles
