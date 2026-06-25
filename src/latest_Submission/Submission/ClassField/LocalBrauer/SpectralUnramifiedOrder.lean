import Submission.ClassField.LocalBrauer.CanonicalRamification
import Submission.ClassField.LocalBrauer.FieldAdicOrder
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Transporting unramified integral models to spectral integers

An integral-closure model of a finite extension is canonically equivalent to
the spectral valuation integers.  Consequently finiteness and formal
unramifiedness transport to the spectral model, giving ramification index one
and the expected restriction formula for normalized local-field order.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v w

open ValuativeRel

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

private abbrev A := Valuation.integer (ValuativeRel.valuation K)
/-- Finiteness transports from any integral-closure model to the spectral
integer ring. -/
theorem spectral_module_model
    (U : Type w) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : Algebra (A K)
        (Valuation.integer (NormedField.valuation (K := L))) :=
      valuativeSpectralAlgebra K L
    Module.Finite (A K)
      (Valuation.integer (NormedField.valuation (K := L))) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (A K)
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  exact Module.Finite.equiv
    (valuativeSpectralInteger K L U).toLinearEquiv

/-- Formal unramifiedness transports from the integral model to the spectral
integer ring. -/
theorem spectral_formally_model
    (U : Type w) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Algebra.FormallyUnramified (A K) U] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : Algebra (A K)
        (Valuation.integer (NormedField.valuation (K := L))) :=
      valuativeSpectralAlgebra K L
    Algebra.FormallyUnramified (A K)
      (Valuation.integer (NormedField.valuation (K := L))) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (A K)
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  exact Algebra.FormallyUnramified.of_equiv
    (valuativeSpectralInteger K L U)

/-- An unramified finite integral model forces normalized local-field order
on the spectral extension to restrict unchanged to the base field. -/
theorem algebra_integral_model
    (U : Type w) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [Algebra.FormallyUnramified (A K) U]
    [IsLocalRing U] [IsLocalHom (algebraMap (A K) U)]
    (x : Kˣ) :
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
    localUnitOrder L
        (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)) =
      localUnitOrder K (Additive.ofMul x) := by
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
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    constructor
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
      (NormedField.valuation (K := K))).trans
        ((Valuation.HasExtension.val_isEquiv_comap
          (vR := NormedField.valuation (K := K))
          (vA := NormedField.valuation (K := L))).trans
            ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
              (NormedField.valuation (K := L))).symm.comap
                (algebraMap K L)))
  have hOL : 𝒪[L] = Valuation.integer
      (NormedField.valuation (K := L)) := valuative_integer_norm L
  letI : Algebra (A K) (Valuation.integer
      (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  letI : IsScalarTower (A K) (Valuation.integer
      (NormedField.valuation (K := L))) L :=
    valuativeSpectralTower K L
  let eModel := valuativeSpectralInteger K L U
  let eOL : 𝒪[L] ≃+* Valuation.integer
      (NormedField.valuation (K := L)) := RingEquiv.subringCongr hOL
  let eOLAlg : 𝒪[L] ≃ₐ[A K] Valuation.integer
      (NormedField.valuation (K := L)) :=
    AlgEquiv.ofRingEquiv (f := eOL) (fun _ ↦ Subtype.ext rfl)
  let eUO : U ≃ₐ[A K] 𝒪[L] :=
    eModel.trans eOLAlg.symm
  letI : Module.Finite (A K) 𝒪[L] :=
    Module.Finite.equiv eUO.toLinearEquiv
  letI : Algebra.FormallyUnramified (A K) 𝒪[L] :=
    Algebra.FormallyUnramified.of_equiv eUO
  letI : Algebra.IsUnramifiedAt (A K) (IsLocalRing.maximalIdeal 𝒪[L]) := by
    change Algebra.FormallyUnramified (A K)
      (Localization.AtPrime (IsLocalRing.maximalIdeal 𝒪[L]))
    infer_instance
  have hram : (IsLocalRing.maximalIdeal (A K)).ramificationIdx
      (IsLocalRing.maximalIdeal 𝒪[L]) = 1 :=
    ramification_idx_unramified
      (A := A K) (B := 𝒪[L])
  letI : (IsDiscreteValuationRing.maximalIdeal 𝒪[L]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal (A K)).asIdeal := by
    change (IsLocalRing.maximalIdeal 𝒪[L]).LiesOver
      (IsLocalRing.maximalIdeal (A K))
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap (A K) 𝒪[L])).symm
  rw [normalized_adic_hom K,
    normalized_adic_hom L]
  exact normalized_ramification_idx
    (IsDiscreteValuationRing.maximalIdeal (A K))
    (IsDiscreteValuationRing.maximalIdeal 𝒪[L]) hram x

end

end Submission.CField.LBrauer
