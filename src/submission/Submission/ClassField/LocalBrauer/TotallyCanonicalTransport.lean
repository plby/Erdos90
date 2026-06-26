import Submission.ClassField.LocalBrauer.TotallyTensorField
import Submission.ClassField.LocalBrauer.IntegralModelUniqueness

/-!
# Canonical unramified levels across a totally ramified base change

A totally ramified extension has the same residue field as its base.  Hence
the canonical Frobenius polynomials agree after scalar extension.  Combined
with the field-valued tensor-product theorem, this identifies the scalar
extension of every canonical unramified level with the canonical unramified
level over the larger field.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open Algebra IsLocalRing ValuativeRel
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K F : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [Algebra K F] [FiniteDimensional K F]
  [Algebra 𝒪[K] 𝒪[F]] [Module.Finite 𝒪[K] 𝒪[F]]
  [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
  [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]

set_option synthInstance.maxHeartbeats 100000 in
-- Total ramification unfolds the transported residue-field instances.
omit [FiniteDimensional K F] in
/-- Total ramification identifies the cardinalities of the norm-defined
residue fields. -/
theorem residue_totally_ramified
    (htotal : Submission.NumberTheory.Milne.TotallyRamified
      𝒪[K] 𝒪[F] (maximalIdeal 𝒪[K])) :
    localResidueCard F = localResidueCard K := by
  let p := maximalIdeal 𝒪[K]
  obtain ⟨P, hPprime, hPover, _hmap, hram, hunique⟩ := htotal
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hPmax : P = maximalIdeal 𝒪[F] :=
    IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
  letI : P.IsPrime := hPprime
  letI : P.IsMaximal := hPprime.isMaximal hP0
  letI : P.LiesOver p := hPover
  have hprimes : IsDedekindDomain.primesOverFinset p 𝒪[F] = {P} := by
    ext Q
    rw [Finset.mem_singleton, IsDedekindDomain.mem_primesOverFinset_iff hp0 𝒪[F]]
    constructor
    · rintro ⟨hQprime, hQover⟩
      exact hunique Q hQprime hQover
    · rintro rfl
      exact ⟨hPprime, hPover⟩
  have hbij : Function.Bijective
      (algebraMap (𝒪[K] ⧸ p) (𝒪[F] ⧸ P)) :=
    Submission.NumberTheory.Milne.bijective_full_idx
      𝒪[K] 𝒪[F] K F hp0 hprimes hram
  let e : (𝒪[K] ⧸ p) ≃+* (𝒪[F] ⧸ P) :=
    RingEquiv.ofBijective (algebraMap (𝒪[K] ⧸ p) (𝒪[F] ⧸ P)) hbij
  have hcard : Nat.card (𝒪[K] ⧸ p) = Nat.card (𝒪[F] ⧸ P) :=
    Nat.card_congr e.toEquiv
  have hcard' :
      Nat.card (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation F))) =
        Nat.card (IsLocalRing.ResidueField
          (Valuation.integer (ValuativeRel.valuation K))) := by
    simpa [IsLocalRing.ResidueField, p, hPmax] using hcard.symm
  calc
    localResidueCard F =
        Nat.card (IsLocalRing.ResidueField
          (Valuation.integer (ValuativeRel.valuation F))) := by
      simpa [localResidueCard, Valued.ResidueField] using
        (Nat.card_congr
          (IsLocalRing.ResidueField.mapEquiv
            (valuativeIntegerNorm F)).toEquiv).symm
    _ = Nat.card (IsLocalRing.ResidueField
          (Valuation.integer (ValuativeRel.valuation K))) := hcard'
    _ = localResidueCard K := by
      simpa [localResidueCard, Valued.ResidueField] using
        Nat.card_congr
          (IsLocalRing.ResidueField.mapEquiv
            (valuativeIntegerNorm K)).toEquiv

omit [FiniteDimensional K F] in
/-- Over a totally ramified extension, the canonical Frobenius polynomial
is preserved by scalar extension. -/
theorem frobenius_totally_ramified
    (htotal : Submission.NumberTheory.Milne.TotallyRamified
      𝒪[K] 𝒪[F] (maximalIdeal 𝒪[K]))
    (n : ℕ) :
    (localFrobeniusPolynomial K n).map (algebraMap K F) =
      localFrobeniusPolynomial F n := by
  rw [localFrobeniusPolynomial, localFrobeniusPolynomial,
    residue_totally_ramified K F htotal]
  simp

set_option maxHeartbeats 2000000 in
-- Comparing the two dependent tensor presentations is elaboration-heavy.
set_option synthInstance.maxHeartbeats 150000 in
-- The comparison synthesizes transported structures on both canonical levels.
/-- Scalar extension of a canonical unramified level across a totally
ramified local extension is the canonical unramified level of the same
degree over the larger field. -/
theorem nonempty_totally_ramified
    (n : ℕ) [NeZero n]
    (htotal : Submission.NumberTheory.Milne.TotallyRamified
      𝒪[K] 𝒪[F] (maximalIdeal 𝒪[K])) :
    Nonempty
      ((canonicalUnramifiedLevel K n ⊗[K] F) ≃ₐ[F]
        canonicalUnramifiedLevel F n) := by
  let U := canonicalUnramifiedLevel K n
  let E := U ⊗[K] F
  let hE : IsField E :=
    level_totally_ramified
      K F n htotal
  letI : Field E := hE.toField
  letI : Module.Finite F E := by
    letI : Module.Finite F (F ⊗[K] U) := Module.Finite.base_change K F U
    exact Module.Finite.equiv
      (Algebra.TensorProduct.commRight K F U).toLinearEquiv
  letI : IsGalois F E := tensor_compositum K U F hE
  apply alg_level_splits F E n
  · calc
      Module.finrank F E = Module.finrank F (F ⊗[K] U) :=
        (Algebra.TensorProduct.commRight K F U).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K U :=
        Module.finrank_baseChange (R := F) (S := K) (M' := U)
      _ = n := unramified_level_finrank K n
  · rw [← frobenius_totally_ramified K F htotal]
    rw [Polynomial.map_map]
    have hsplit :
        ((localFrobeniusPolynomial K n).map (algebraMap K U)).Splits := by
      exact unramified_level_splits K n
    have hmapped := hsplit.map
      (Algebra.TensorProduct.includeLeftRingHom
        (R := K) (A := U) (B := F))
    have hbase :
        (Algebra.TensorProduct.includeLeftRingHom
            (R := K) (A := U) (B := F)).comp (algebraMap K U) =
          (algebraMap F E).comp (algebraMap K F) := by
      ext x
      change algebraMap K U x ⊗ₜ[K] (1 : F) =
        (1 : U) ⊗ₜ[K] algebraMap K F x
      rw [← Algebra.TensorProduct.algebraMap_apply,
        ← Algebra.TensorProduct.algebraMap_apply']
    simpa [Polynomial.map_map, hbase] using hmapped

end

end Submission.CField.LBrauer
