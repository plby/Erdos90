import Towers.ClassField.NormCorrespondence.UnramifiedNormGroups
import Towers.ClassField.LocalBrauer.CanonicalResidueAction

/-!
# Canonical unramified Frobenius in the Chapter I statement

This file connects the residue-field construction of arithmetic Frobenius
with the intrinsic norm-congruence predicate used in Theorem I.1.1.
-/

namespace Towers.CField.LFTheory

noncomputable section

universe u

open LBrauer

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
-- Constructing the spectral integer model unfolds a dependent witness.
@[implicit_reducible]
private noncomputable def canonical_integer_module
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    Module.Finite (A K) N :=
  (level_spectral_data K n).1

set_option maxHeartbeats 1000000 in
-- Constructing the local map witness unfolds the same dependent model.
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

set_option maxHeartbeats 5000000 in
-- The residue congruence uses the dependent spectral integer model above.
set_option synthInstance.maxHeartbeats 300000 in
/-- Arithmetic Frobenius on the canonical unramified level satisfies the
pointwise residue-power characterization used by Theorem I.1.1. -/
theorem subextension_arithmetic_frobenius
    (n : ℕ) [NeZero n] :
    (canonicalUnramifiedSubextension K n).IsArithmeticFrobenius K
      (canonicalArithmeticFrobenius K n) := by
  unfold FASubext.IsArithmeticFrobenius
  dsimp only [canonicalUnramifiedSubextension]
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
  let A0 := Valuation.integer (NormedField.valuation (K := K))
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N := by
    exact integer_discrete_valuation E
  letI : Algebra A N := valuativeSpectralAlgebra K E
  letI : Module.Finite A N :=
    canonical_integer_module K n
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  letI : IsLocalHom (algebraMap A N) :=
    canonical_integer_hom K n
  let k := IsLocalRing.ResidueField A
  let l := IsLocalRing.ResidueField N
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k l := inferInstance
  letI : Finite l := Module.finite_of_finite k
  letI : Fintype l := Fintype.ofFinite l
  have hcardBase : Nat.card k = localResidueCardinality K := by
    change Nat.card (IsLocalRing.ResidueField A) =
      Nat.card (IsLocalRing.ResidueField A0)
    exact Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv
        (valuativeIntegerNorm K)).toEquiv
  intro x hx
  let y : N := ⟨x, by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast hx⟩
  have hres :
      IsLocalRing.residue N
          ⟨canonicalArithmeticFrobenius K n x, by
            change ‖canonicalArithmeticFrobenius K n x‖ ≤ 1
            exact (spectralNorm_eq_of_equiv
              (canonicalArithmeticFrobenius K n) x).ge.trans hx⟩ =
        (IsLocalRing.residue N y) ^
          Nat.card k := by
    have hfrob := canonical_unramified_frobenius K n
    calc
      _ = canonicalUnramifiedResidue K n
            (canonicalArithmeticFrobenius K n)
            (IsLocalRing.residue N y) :=
        (canonical_unramified_residue K n
          (canonicalArithmeticFrobenius K n) y).symm
      _ = FiniteField.frobeniusAlgEquivOfAlgebraic k l
            (IsLocalRing.residue N y) := by rw [hfrob]
      _ = (IsLocalRing.residue N y) ^ Nat.card k := by
        simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
          Nat.card_eq_fintype_card]
  have hmem :
      (⟨canonicalArithmeticFrobenius K n x, by
          change ‖canonicalArithmeticFrobenius K n x‖ ≤ 1
          exact (spectralNorm_eq_of_equiv
            (canonicalArithmeticFrobenius K n) x).ge.trans hx⟩ : N) -
            y ^ Nat.card k ∈
        IsLocalRing.maximalIdeal N := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_pow, hres, sub_self]
  rw [← hcardBase]
  change ‖canonicalArithmeticFrobenius K n x - x ^ Nat.card k‖ < 1
  change (NormedField.valuation (K := E))
      (canonicalArithmeticFrobenius K n x - x ^ Nat.card k) < 1
  have hmem' := (NormedField.valuation (K := E)).mem_maximalIdeal_iff.mp hmem
  change (NormedField.valuation (K := E))
      (canonicalArithmeticFrobenius K n x - x ^ Nat.card k) < 1 at hmem'
  exact hmem'

end

end Towers.CField.LFTheory
