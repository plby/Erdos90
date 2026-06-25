import Towers.ClassField.Ideles.IdeleNormContinuity
import Towers.ClassField.NormIndex.CompletionPlaceComparison

/-!
# Continuity of the finite idèle norm

The finite idèle norm is continuous for the restricted-product topologies.
On a principal stage of the source restricted product, only finitely many
upper primes are allowed to be nonunits.  Removing their contractions from
the set of lower primes gives a principal stage in the target.  On these
stages the assertion is coordinatewise continuity of a finite product of
completed field norms.
-/

namespace Towers.CField.NIndex

open Filter Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped RestrictedProduct

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteNormContinuityFinitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteNormContinuityFinitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

private theorem continuous_cast_symm
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun v ↦ v.adicCompletion L) h).symm := by
  subst Q'
  exact continuous_id

/-- The inverse finite completion/adic-completion comparison is continuous. -/
theorem place_symm_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (completionPlaceAdic
      (K := K) (L := L) P w).symm := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q := by
    have hfiber := (upperAboveBase
      (K := K) (L := L) P).apply_symm_apply
        (placeAboveBase (K := K) (L := L) P w)
    exact congrArg Subtype.val hfiber |>.symm
  have hcast : Continuous (RingEquiv.cast
      (R := fun v => v.adicCompletion L) hq).symm :=
    continuous_cast_symm hq
  unfold completionPlaceAdic
  exact (continuous_completion_symm
      (place_centered_prime w.1 hw hwna)).comp
    ((adic_symm_continuous q).comp hcast)

/-- The field norm on the adic completion belonging to a completion place is
continuous. -/
private theorem continuous_completion_attached
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (finiteCompletionNorm (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)) := by
  let v := (FinitePlace.mk P).val
  let Q := placeUpperFactor (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : Module.Finite (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  let hw : AbsoluteValue.LiesOver w.1 v := w.2
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 hw).toAlgebra
  letI : NormedAlgebra v.Completion w.1.Completion :=
    { toAlgebra := (completionLies v w.1 hw).toAlgebra
      norm_smul_le r x := by
        change ‖completionLies v w.1 hw r * x‖ ≤ ‖r‖ * ‖x‖
        calc
          _ ≤ ‖completionLies v w.1 hw r‖ * ‖x‖ := norm_mul_le _ _
          _ = ‖r‖ * ‖x‖ := by
            congr 1
            simpa only [dist_zero_right, map_zero] using
              (completion_lies_isometry v w.1 hw).dist_eq r 0 }
  letI : Module.Finite v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  have hnorm : Continuous
      (Units.map (Algebra.norm v.Completion) :
        w.1.Completionˣ → v.Completionˣ) :=
    (continuous_algebra_dimensional
      (F := v.Completion) (E := w.1.Completion)).units_map _
  have heK : Continuous (Units.map eK.toMonoidHom) :=
    (place_adic_isometry P).continuous.units_map _
  have heL : Continuous (Units.map eL.symm.toMonoidHom) :=
    (place_symm_continuous
      (K := K) (L := L) P w).units_map _
  have htransport : Continuous (fun z =>
      Units.map eK.toMonoidHom
        (Units.map (Algebra.norm v.Completion)
          (Units.map eL.symm.toMonoidHom z))) :=
    heK.comp (hnorm.comp heL)
  apply htransport.congr
  intro z
  apply Units.ext
  change eK (Algebra.norm v.Completion (eL.symm z)) =
    Algebra.norm (P.adicCompletion K)
      (z : (upperPrime (K := K) (L := L) P Q).adicCompletion L)
  simpa only [v, eK, eL, RingEquiv.apply_symm_apply] using
    place_adic_norm
      (K := K) (L := L) P w (eL.symm z)

/-- Every completed finite-place norm occurring in the finite idèle norm is
continuous. -/
theorem continuous_completion_norm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    Continuous (finiteCompletionNorm (K := K) (L := L) P Q) := by
  let w := (placesAboveFactors
    (K := K) (L := L) P).symm Q
  have hQ : placeUpperFactor
      (K := K) (L := L) P w = Q := by
    exact place_upper_symm
      (K := K) (L := L) P Q
  exact Eq.mp (congrArg
    (fun Q' : UpperPrimeFactors (K := K) (L := L) P ↦
      Continuous (finiteCompletionNorm (K := K) (L := L) P Q')) hQ)
    (continuous_completion_attached (K := K) (L := L) P w)

/-- The norm on finite idèles is continuous for the restricted-product
topologies. -/
theorem continuous_finite_norm :
    Continuous (finiteIdeleNorm (K := K) (L := L)) := by
  exact continuous_idele_completion
    (fun P Q ↦ continuous_completion_norm (K := K) (L := L) P Q)

end

end Towers.CField.NIndex
