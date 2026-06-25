import Submission.ClassField.LocalBrauer.FiniteLocalExtension
import Submission.ClassField.LocalBrauer.FieldAdicOrder
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Ramification scaling in a finite local extension

For the canonical spectral topology on a finite extension of a
nonarchimedean local field, normalized order on base-field units scales by
the ramification index.  This is the valuation input in Remark IV.4.4(c).
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel

namespace FLExt

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The valuation-relation valuation on the spectral extension extends the
valuation-relation valuation on the base field. -/
@[implicit_reducible]
def valuativeValuation :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  constructor
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
    (NormedField.valuation (K := K))).trans
      ((Valuation.HasExtension.val_isEquiv_comap
        (vR := NormedField.valuation (K := K))
        (vA := NormedField.valuation (K := L))).trans
          ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
            (NormedField.valuation (K := L))).symm.comap
              (algebraMap K L)))

/-- In a finite extension equipped with its spectral local-field structure,
the normalized order of a base-field unit is multiplied by the ramification
index. -/
theorem algebra_ramification_idx (x : Kˣ) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : (ValuativeRel.valuation K).HasExtension
        (ValuativeRel.valuation L) := valuativeValuation K L
    letI : IsNonarchimedeanLocalField L :=
      nonarchimedeanLocalField K L
    localUnitOrder L
        (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) *
        localUnitOrder K (Additive.ofMul x) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := valuativeValuation K L
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  letI : (IsDiscreteValuationRing.maximalIdeal 𝒪[L]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal := by
    change (IsLocalRing.maximalIdeal 𝒪[L]).LiesOver
      (IsLocalRing.maximalIdeal 𝒪[K])
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap 𝒪[K] 𝒪[L])).symm
  exact
    Submission.CField.LBrauer.algebra_ramification_idx
      K L x

variable [Algebra.IsSeparable K L]

/-- For the canonical spectral local-field structure on a finite separable extension,
the ramification index times the residue degree is the field degree. -/
theorem ramification_deg_finrank :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : (ValuativeRel.valuation K).HasExtension
        (ValuativeRel.valuation L) := valuativeValuation K L
    letI : IsNonarchimedeanLocalField L :=
      nonarchimedeanLocalField K L
    (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          (IsLocalRing.maximalIdeal 𝒪[L]) *
        (IsLocalRing.maximalIdeal 𝒪[K]).inertiaDeg
          (IsLocalRing.maximalIdeal 𝒪[L]) =
      Module.finrank K L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := valuativeValuation K L
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  let B := Valuation.integer (NormedField.valuation (K := L))
  letI : Algebra 𝒪[K] B := valuativeSpectralAlgebra K L
  letI : IsScalarTower 𝒪[K] B L :=
    valuativeSpectralTower K L
  letI : IsIntegralClosure B 𝒪[K] L :=
    spectral_integer_valuative K L
  letI : Module.Finite 𝒪[K] B :=
    IsIntegralClosure.finite 𝒪[K] K L B
  have hOL : 𝒪[L] = B := valuative_integer_norm L
  let eOL : 𝒪[L] ≃+* B := RingEquiv.subringCongr hOL
  let eOLAlg : 𝒪[L] ≃ₐ[𝒪[K]] B :=
    AlgEquiv.ofRingEquiv (f := eOL) (fun _ ↦ Subtype.ext rfl)
  letI : Module.Finite 𝒪[K] 𝒪[L] :=
    Module.Finite.equiv eOLAlg.symm.toLinearEquiv
  exact Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (R := 𝒪[K]) 𝒪[L] K L (IsDiscreteValuationRing.not_a_field 𝒪[K])

end FLExt

end


end Submission.CField.LBrauer
