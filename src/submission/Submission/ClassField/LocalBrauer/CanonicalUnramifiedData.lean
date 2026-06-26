import Submission.ClassField.LocalBrauer.CanonicalUnramifiedTower
import Submission.ClassField.LocalBrauer.SpectralNormData

/-!
# Unramified local data for the canonical levels

The explicit Hensel-lifted unramified model is transported across the
splitting-field equivalence to the canonical level in the separable closure.
This supplies the unit norm approximation and normalized-order restriction
without additional hypotheses.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open Polynomial ValuativeRel
open scoped BigOperators

private abbrev A (K : Type u) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

private abbrev A₀ (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] :=
  Valuation.integer (NormedField.valuation (K := K))

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 1000000 in
-- The explicit Galois model has a deeply dependent existential telescope.
/-- Every positive canonical unramified level has the residue algebra, unit
norm data, and order restriction needed for the local invariant. -/
theorem unramified_level_data
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
    ∃ hResidueAlgebra : Algebra 𝓀[K] 𝓀[E],
      letI : Algebra 𝓀[K] 𝓀[E] := hResidueAlgebra
      UnramifiedUnitData K E
          (FLExt.integerUnitNorm K E) ∧
        (∀ x : Kˣ,
          localUnitOrder E
              (Additive.ofMul (Units.map (algebraMap K E) x)) =
            localUnitOrder K (Additive.ofMul x)) ∧
        let N := Valuation.integer (NormedField.valuation (K := E))
        letI : Algebra 𝒪[K] N := valuativeSpectralAlgebra K E
        Module.Finite 𝒪[K] N ∧
          Algebra.FormallyUnramified 𝒪[K] N ∧
          IsScalarTower 𝒪[K] N E ∧
          IsIntegralClosure N 𝒪[K] E := by
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
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  let eA := valuativeIntegerNorm K
  letI : IsDiscreteValuationRing (A₀ K) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA
  obtain ⟨f, h, hfmonic, hhmonic, hfactor, hfdegree, hfred, hfsep,
      hfirr, hfmonic', hlocal, hdvr, hunramified, hunramifiedAt,
      hdegree, hgalois, hcyclic, φ, hφorder, hφgen⟩ :=
    unramified_galois_extension K n
  let U := AdjoinRoot f
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : IsLocalRing U := hlocal
  letI : IsDiscreteValuationRing U := hdvr
  have hAU₀ : Function.Injective (algebraMap (A₀ K) U) := by
    have hdegree_ne : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hfirr.ne_zero, hfdegree]
      exact_mod_cast (NeZero.ne n)
    simpa [AdjoinRoot.algebraMap_eq] using
      AdjoinRoot.of.injective_of_degree_ne_zero hdegree_ne
  letI : FaithfulSMul (A₀ K) U :=
    (faithfulSMul_iff_algebraMap_injective (A₀ K) U).2 hAU₀
  letI : Module.Finite (A₀ K) U := hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral (A₀ K) U :=
    Algebra.IsIntegral.of_finite (A₀ K) U
  letI : Algebra.FormallyUnramified (A₀ K) U := hunramified
  have hmax : IsLocalRing.maximalIdeal (AdjoinRoot f) =
      (IsLocalRing.maximalIdeal (A₀ K)).map
        (algebraMap (A₀ K) (AdjoinRoot f)) :=
    adjoin_irreducible_residue
      (A₀ K) f hfmonic hfred
  letI : IsLocalHom (algebraMap (A₀ K) (AdjoinRoot f)) :=
    ((IsLocalRing.local_hom_TFAE
      (algebraMap (A₀ K) (AdjoinRoot f))).out 2 0).mp (by
      simpa using hmax.symm.le)
  letI : Algebra (A K) (A₀ K) := eA.toRingHom.toAlgebra
  letI : Algebra (A K) U :=
    ((algebraMap (A₀ K) U).comp eA.toRingHom).toAlgebra
  letI : SMul (A K) U := (inferInstance : Algebra (A K) U).toSMul
  letI : FaithfulSMul (A K) U :=
    (faithfulSMul_iff_algebraMap_injective (A K) U).2 <| by
      change Function.Injective
        ((algebraMap (A₀ K) U).comp eA.toRingHom)
      exact hAU₀.comp eA.injective
  letI : IsScalarTower (A K) (A₀ K) U :=
    ⟨fun x y z ↦ by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      change _ = algebraMap (A₀ K) U (eA x) * _
      rfl⟩
  let eAAlg : A K ≃ₐ[A K] A₀ K :=
    AlgEquiv.ofRingEquiv (f := eA) (fun _ ↦ rfl)
  letI : Module.Finite (A K) (A₀ K) :=
    Module.Finite.equiv eAAlg.toLinearEquiv
  letI : Module.Finite (A K) U := Module.Finite.trans (A₀ K) U
  letI : Algebra.FormallyUnramified (A K) (A₀ K) :=
    Algebra.FormallyUnramified.of_equiv eAAlg
  letI : Algebra.FormallyUnramified (A K) U :=
    Algebra.FormallyUnramified.comp (A K) (A₀ K) U
  letI : IsLocalHom (algebraMap (A K) U) :=
    by
      change IsLocalHom
        ((algebraMap (A₀ K) U).comp eA.toRingHom)
      letI : IsLocalHom eA.toRingHom := eA.surjective.isLocalHom
      infer_instance
  let E₀ := FractionRing U
  letI : Algebra U E₀ := OreLocalization.instAlgebra
  letI : Algebra (A₀ K) E₀ :=
    ((algebraMap U E₀).comp (algebraMap (A₀ K) U)).toAlgebra
  have hA₀E₀ : Function.Injective (algebraMap (A₀ K) E₀) := by
    change Function.Injective
      ((algebraMap U E₀).comp (algebraMap (A₀ K) U))
    exact (IsFractionRing.injective U E₀).comp hAU₀
  letI : Algebra K E₀ := (IsFractionRing.lift hA₀E₀).toAlgebra
  letI : Module.Finite K E₀ := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank K (FractionRing (AdjoinRoot f))
    rw [hdegree]
    exact NeZero.pos n)
  letI : IsGalois K E₀ := hgalois
  letI : Algebra (A K) E₀ :=
    ((algebraMap U E₀).comp (algebraMap (A K) U)).toAlgebra
  letI : SMul (A K) E₀ := (inferInstance : Algebra (A K) E₀).toSMul
  letI : IsScalarTower (A K) U E₀ :=
    ⟨fun x y z ↦ by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      change _ = algebraMap U E₀ (algebraMap (A K) U x) * _
      rfl⟩
  letI : FaithfulSMul (A K) E₀ :=
    (faithfulSMul_iff_algebraMap_injective (A K) E₀).2 <| by
      change Function.Injective
        ((algebraMap U E₀).comp (algebraMap (A K) U))
      exact (IsFractionRing.injective U E₀).comp
        (FaithfulSMul.algebraMap_injective (A K) U)
  letI : IsScalarTower (A K) K E₀ :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change algebraMap (A₀ K) E₀ (eA a) =
        algebraMap K E₀ ((eA a : A₀ K) : K)
      exact IsFractionRing.lift_algebraMap
        hA₀E₀ (eA a) |>.symm)
  have hsplit₀ :
      ((localFrobeniusPolynomial K n).map (algebraMap K E₀)).Splits := by
    have hs := frobenius_splits_fraction
      K n f hfmonic hfdegree hfred
    simpa [localFrobeniusPolynomial, localResidueCard] using hs
  let e : E₀ ≃ₐ[K] E := Classical.choice
    (alg_level_splits
      K E₀ n hdegree hsplit₀)
  letI : Algebra U E :=
    (e.toRingEquiv.toRingHom.comp (algebraMap U E₀)).toAlgebra
  have hUE (y : U) : algebraMap U E y = e (algebraMap U E₀ y) := rfl
  have hAE (a : A K) : algebraMap (A K) E a =
      algebraMap U E (algebraMap (A K) U a) := by
    rw [hUE, ← IsScalarTower.algebraMap_apply (A K) U E₀,
      IsScalarTower.algebraMap_apply (A K) K E,
      IsScalarTower.algebraMap_apply (A K) K E₀]
    exact (e.commutes (algebraMap (A K) K a)).symm
  letI : IsScalarTower (A K) U E :=
    IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun a ↦ hAE a
  let eU : E₀ ≃ₐ[U] E :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ ↦ rfl)
  letI : IsFractionRing U E :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors U) eU
  letI : IsIntegralClosure U (A K) E :=
    IsIntegralClosure.of_isIntegrallyClosed U (A K) E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : IsScalarTower (A K) N E :=
    valuativeSpectralTower K E
  letI : IsIntegralClosure N (A K) E :=
    spectral_integer_valuative K E
  letI : Module.Finite (A K) N :=
    spectral_module_model K E U
  letI : Algebra.FormallyUnramified (A K) N :=
    spectral_formally_model K E U
  obtain ⟨hResidueAlgebra, hUnit⟩ :=
    FLExt.residue_unramified_model
      K E U
  refine ⟨hResidueAlgebra, hUnit, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance⟩
  intro x
  exact algebra_integral_model K E U x

set_option maxHeartbeats 1000000 in
-- This is a projection of the deeply dependent canonical local-data package.
/-- The spectral norm integers of a canonical unramified level form a finite
formally unramified algebra over the base valuation integers. -/
theorem level_spectral_data
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra 𝒪[K] N := valuativeSpectralAlgebra K E
    Module.Finite 𝒪[K] N ∧
      Algebra.FormallyUnramified 𝒪[K] N ∧
      IsScalarTower 𝒪[K] N E ∧
      IsIntegralClosure N 𝒪[K] E := by
  obtain ⟨_hResidueAlgebra, _hUnit, _horder, hIntegerData⟩ :=
    unramified_level_data K n
  exact hIntegerData

end

end Submission.CField.LBrauer
