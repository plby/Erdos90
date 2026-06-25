import Submission.ClassField.LocalBrauer.CanonicalUnramifiedData
import Submission.NumberTheory.Locals.UnramifiedExtensions

/-!
# Residue cardinality in the canonical unramified tower
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne
open scoped Valued

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 3000000 in
-- Comparing the canonical integral model with its residue field is elaboration-heavy.
set_option synthInstance.maxHeartbeats 300000 in
-- The comparison requires synthesizing the transported local-ring structures.
/-- The residue field of the canonical unramified degree-`n` extension has
cardinality `q_K ^ n`. -/
theorem residue_unramified_level
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    localResidueCard E = (localResidueCard K) ^ n := by
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
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra B E := B.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers
      (ValuativeRel.valuation K)).isFractionRing
  letI : IsFractionRing B E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : Algebra A B := valuativeSpectralAlgebra K E
  obtain ⟨hfinite, hunramified, htower, hclosure⟩ :=
    level_spectral_data K n
  letI : Module.Finite A B := hfinite
  letI : Algebra.FormallyUnramified A B := hunramified
  letI : IsScalarTower A B E := htower
  letI : IsIntegralClosure B A E := hclosure
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : Module.IsTorsionFree A B :=
    IsIntegralClosure.isTorsionFree A E
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (maximalIdeal_comap (algebraMap A B)).symm
  letI : Algebra.IsUnramifiedAt A (maximalIdeal B) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (maximalIdeal B))
    infer_instance
  have hresdegree :
      Module.finrank (ResidueField A) (ResidueField B) = n := by
    rw [← unramified_level_finrank K n]
    exact (finrank_unramified_local
      (R := A) (S := B) (K := K) (L := E) (maximalIdeal A)
      (IsDiscreteValuationRing.not_a_field A)
      (IsDiscreteValuationRing.not_a_field B)).symm
  letI : Module.Finite (ResidueField A) (ResidueField B) :=
    Module.finite_of_finrank_pos (hresdegree.symm ▸ NeZero.pos n)
  letI : Finite (ResidueField A) := local_field_residue K
  letI : Finite (ResidueField B) :=
    Module.finite_of_finite (ResidueField A)
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  letI : Fintype (ResidueField B) := Fintype.ofFinite _
  have hcardA : Nat.card (ResidueField A) = localResidueCard K := by
    simpa [localResidueCard, Valued.ResidueField] using
      Nat.card_congr
        (ResidueField.mapEquiv
          (valuativeIntegerNorm K)).toEquiv
  change Nat.card (ResidueField B) = localResidueCard K ^ n
  calc
    Nat.card (ResidueField B) =
        Nat.card (ResidueField A) ^
          Module.finrank (ResidueField A) (ResidueField B) := by
      simpa [Nat.card_eq_fintype_card] using
        (Module.card_eq_pow_finrank
          (K := ResidueField A) (V := ResidueField B))
    _ = Nat.card (ResidueField A) ^ n := by rw [hresdegree]
    _ = localResidueCard K ^ n := by rw [hcardA]

end

end Submission.CField.LBrauer
