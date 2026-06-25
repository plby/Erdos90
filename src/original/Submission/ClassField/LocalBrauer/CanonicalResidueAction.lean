import Submission.NumberTheory.Locals.GaloisReductionApply
import Submission.ClassField.LocalBrauer.CanonicalUnramifiedFrobenius

/-!
# Residue action at a canonical unramified level

This is the pointwise form of the canonical reduction equivalence.  Keeping
it separate avoids unfolding the entire decomposition-group construction
whenever Frobenius congruences are used.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev A := Valuation.integer (ValuativeRel.valuation K)

private theorem integer_discrete_valuation
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Valuation.Compatible (NormedField.valuation (K := F))] :
    IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := F))) := by
  letI : IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation F)) :=
    discrete_valuation_ring F
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (valuativeIntegerNorm F)

set_option maxHeartbeats 1000000 in
-- Elaborating the transported integral structure for the canonical level is deep.
@[implicit_reducible]
private noncomputable def canonical_integer_module
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    Module.Finite (A K) N :=
  (level_spectral_data K n).1

set_option maxHeartbeats 1000000 in
-- Elaborating formal unramifiedness through the canonical integral model is deep.
@[implicit_reducible]
private noncomputable def integer_formally_unramified
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    Algebra.FormallyUnramified (A K) N :=
  (level_spectral_data K n).2.1

set_option maxHeartbeats 1000000 in
-- Synthesizing the scalar tower for the transported integral model is deep.
@[implicit_reducible]
private noncomputable def canonical_scalar_tower
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsScalarTower (A K) N E :=
  (level_spectral_data K n).2.2.1

set_option maxHeartbeats 1000000 in
-- Elaborating the integral-closure witness for the canonical level is deep.
@[implicit_reducible]
private noncomputable def integer_integral_closure
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsIntegralClosure N (A K) E :=
  (level_spectral_data K n).2.2.2

set_option maxHeartbeats 1000000 in
-- Synthesizing the local-ring map on the transported integral model is deep.
@[implicit_reducible]
private noncomputable def canonical_integer_hom
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : IsDiscreteValuationRing (A K) :=
      discrete_valuation_ring K
    letI : IsDiscreteValuationRing N :=
      integer_discrete_valuation E
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsLocalHom (algebraMap (A K) N) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : Algebra.IsIntegral (A K) N :=
    Algebra.IsIntegral.of_finite (A K) N
  apply ((IsLocalRing.local_hom_TFAE (algebraMap (A K) N)).out 4 0).mp
  exact ((IsLocalRing.maximal_ideal_unique (A K)).unique
    (inferInstance : (IsLocalRing.maximalIdeal (A K)).IsMaximal)
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal N))).symm

set_option maxHeartbeats 3000000 in
-- The proof reinstalls the integral Galois action used by the reduction equivalence.
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical residue Galois equivalence acts by reducing the action of
the corresponding field automorphism. -/
theorem canonical_unramified_residue
    (n : ℕ) [NeZero n]
    (sigma : Gal(canonicalUnramifiedLevel K n/K)) :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (Valuation.integer (ValuativeRel.valuation K)) N :=
      valuativeSpectralAlgebra K E
    letI : IsLocalHom
        (algebraMap (Valuation.integer (ValuativeRel.valuation K)) N) :=
      canonical_integer_hom K n
    ∀ y : N,
      canonicalUnramifiedResidue K n sigma
          (residue N y) =
        residue N
          ⟨sigma (y : E), by
            rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
            exact_mod_cast
              (spectralNorm_eq_of_equiv sigma (y : E)).ge.trans
                (show ‖(y : E)‖ ≤ 1 by
                  exact_mod_cast y.property)⟩ := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension K E
  let A := Valuation.integer (ValuativeRel.valuation K)
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : IsDiscreteValuationRing N := integer_discrete_valuation E
  letI : IsFractionRing N E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : Algebra A N := valuativeSpectralAlgebra K E
  letI : IsScalarTower A N E := canonical_scalar_tower K n
  letI : Module.Finite A N := canonical_integer_module K n
  letI : Algebra.FormallyUnramified A N :=
    integer_formally_unramified K n
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  letI : IsLocalHom (algebraMap A N) :=
    canonical_integer_hom K n
  letI : (maximalIdeal N).LiesOver (maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (maximalIdeal_comap (algebraMap A N)).symm
  letI : Algebra.IsUnramifiedAt A (maximalIdeal N) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (maximalIdeal N))
    infer_instance
  letI : IsIntegralClosure N A E :=
    integer_integral_closure K n
  letI : FaithfulSMul A N :=
    (faithfulSMul_iff_algebraMap_injective A N).2 <| by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K E).injective
      simpa only [IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap N E) hxy
  let G := Gal(E/K)
  letI : MulSemiringAction G N :=
    IsIntegralClosure.MulSemiringAction A K E N
  letI : IsGaloisGroup G A N :=
    IsGaloisGroup.of_isFractionRing G A N K E
  refine fun z => ?_
  change
    galois_unramified_local
        (R := A) (S := N) (G := G) (maximalIdeal A)
          (IsDiscreteValuationRing.not_a_field A)
          (IsDiscreteValuationRing.not_a_field N) sigma
            (Ideal.Quotient.mk (maximalIdeal N) z) = _
  calc
    _ = residue N (sigma • z) :=
      galois_unramified_mk
        (R := A) (S := N) (G := G) (maximalIdeal A)
        (IsDiscreteValuationRing.not_a_field A)
        (IsDiscreteValuationRing.not_a_field N) sigma z
    _ = _ := by
      congr 1
      apply Subtype.ext
      change algebraMap N E (galRestrict A K E N sigma z) =
        sigma (algebraMap N E z)
      exact algebraMap_galRestrict_apply
        (A := A) (K := K) (L := E) (B := N) sigma z

end

end Submission.CField.LBrauer
