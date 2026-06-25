import Towers.ClassField.LocalBrauer.FiniteExtensionData
import Towers.ClassField.LocalBrauer.SpectralNormData
import Towers.ClassField.LocalBrauer.IntegralModelFrobenius
import Towers.NumberTheory.Locals.UnramifiedExtensions

/-!
# Milne, Class Field Theory, Proposition III.1.2

For a finite unramified extension of local fields, the norm on unit groups is
surjective.  The unramified extension is represented here by a finite local
integral-closure model which is unramified at its maximal ideal; no residue
norm, trace-correction, or continuity data is assumed separately.
-/

namespace Towers.CField.UCohom

noncomputable section

universe u v

open IsLocalRing ValuativeRel
open Towers.CField.LBrauer
open Towers.NumberTheory.Milne

/-- For a local target, being unramified at the maximal ideal is already
formal unramifiedness: localizing a local ring at that ideal changes nothing. -/
theorem formally_unramified_maximal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] [Algebra.IsUnramifiedAt A (maximalIdeal B)] :
    Algebra.FormallyUnramified A B := by
  let M := (maximalIdeal B).primeCompl
  letI : IsLocalization M B :=
    IsLocalization.self fun x hx ↦
      (IsLocalRing.notMem_maximalIdeal (R := B)).mp hx
  let e : B ≃ₐ[B] Localization.AtPrime (maximalIdeal B) :=
    IsLocalization.algEquiv M B _
  exact Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars A)

private abbrev A (K : Type u) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L]

/-- **Proposition III.1.2 (source-facing integral-model form).**

The norm on integer units is onto for a finite local field extension whose
finite local integral-closure model is unramified at its maximal ideal.
Galoisness follows from these hypotheses and is not assumed separately.
All residue-field norm and trace facts, and continuity of the norm, are
derived internally rather than included as hypotheses. -/
theorem unramified_units_model
    (U : Type u) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [IsLocalRing U]
    [Algebra.IsUnramifiedAt (A K) (maximalIdeal U)] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L :=
      LBrauer.FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      LBrauer.FLExt.nonarchimedeanLocalField K L
    ∀ u : 𝒪[K]ˣ, ∃ v : 𝒪[L]ˣ,
      Algebra.norm K (((v : 𝒪[L]) : L)) = ((u : 𝒪[K]) : K) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    LBrauer.FLExt.nonarchimedeanLocalField K L
  letI : Algebra.FormallyUnramified (A K) U :=
    formally_unramified_maximal
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : HenselianLocalRing (A K) :=
    LBrauer.integer_henselian_ring K
  letI : IsDomain U :=
    (IsIntegralClosure.algebraMap_injective U (A K) L).isDomain
      (algebraMap U L)
  letI : FaithfulSMul (A K) U :=
    (faithfulSMul_iff_algebraMap_injective (A K) U).mpr <| by
      intro x y hxy
      have h := congrArg (algebraMap U L) hxy
      simp_rw [← IsScalarTower.algebraMap_apply (A K) U L] at h
      simp_rw [IsScalarTower.algebraMap_apply (A K) K L] at h
      apply Subtype.ext
      exact (algebraMap K L).injective h
  letI : Module.IsTorsionFree (A K) U :=
    IsIntegralClosure.isTorsionFree (A K) L
  letI : Algebra.IsIntegral (A K) U :=
    IsIntegralClosure.isIntegral_algebra (A K) L
  letI : IsLocalHom (algebraMap (A K) U) := inferInstance
  letI : Module.Free (A K) U :=
    Module.free_of_finite_type_torsion_free'
  letI : IsAdicComplete (maximalIdeal (A K)) (A K) :=
    LBrauer.integer_adic_complete K
  letI : HenselianLocalRing U :=
    LBrauer.henselian_formally_unramified
      (A K) U
  letI : Module.Finite (ResidueField (A K)) (ResidueField U) :=
    inferInstance
  letI : Finite (ResidueField (A K)) := local_field_residue K
  letI : Finite (ResidueField U) := Module.finite_of_finite (ResidueField (A K))
  letI : IsGalois (ResidueField (A K)) (ResidueField U) := inferInstance
  letI : IsFractionRing U L :=
    IsIntegralClosure.isFractionRing_of_finite_extension (A K) K L U
  letI : IsGalois K L :=
    fraction_formally_residue
      (A K) U K L
  obtain ⟨hResidueAlgebra, hUnit⟩ :=
    FLExt.residue_unramified_model
      K L U
  letI : Algebra 𝓀[K] 𝓀[L] := hResidueAlgebra
  let hLocal : UnramifiedLocalData K L
      (FLExt.integerUnitNorm K L) :=
    FLExt.unramified_data_unit
      K L hResidueAlgebra hUnit
  exact unramified_integer_norm K L
    (FLExt.integerUnitNorm K L) hLocal

set_option maxHeartbeats 3000000 in
-- Transporting both integer-ring presentations through the integral closure is expensive.
/-- Integral-model form retaining the norm witness in the supplied integral
closure `U`.  This is equivalent to the spectral-integer formulation above,
but is useful when `U` is a concrete completed valuation ring. -/
theorem model_units_surjective
    (U : Type u) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [IsLocalRing U]
    [Algebra.IsUnramifiedAt (A K) (maximalIdeal U)] :
    ∀ u : (A K)ˣ, ∃ v : Uˣ,
      Algebra.norm K (algebraMap U L (v : U)) =
        algebraMap (A K) K (u : A K) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (A K)
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  intro u
  obtain ⟨v, hv⟩ :=
    unramified_units_model K L U u
  let e := valuativeSpectralInteger K L U
  let vNorm : (Valuation.integer (NormedField.valuation (K := L)))ˣ :=
    Units.map (valuativeIntegerNorm L).toMonoidHom v
  let vU : Uˣ := Units.map e.symm.toRingEquiv.toMonoidHom vNorm
  refine ⟨vU, ?_⟩
  have hval : algebraMap U L (vU : U) =
      algebraMap (Valuation.integer (NormedField.valuation (K := L))) L
        (vNorm : Valuation.integer (NormedField.valuation (K := L))) := by
    rw [← valuative_spectral_integer
      K L U (vU : U)]
    change algebraMap _ L (e (e.symm vNorm.val)) = _
    rw [e.apply_symm_apply]
  rw [hval]
  exact hv

end

end Towers.CField.UCohom
