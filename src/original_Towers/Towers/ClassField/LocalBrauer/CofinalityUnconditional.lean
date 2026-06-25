import Towers.ClassField.LocalBrauer.GenericFrobeniusSplitting
import Towers.ClassField.LocalBrauer.UnramifiedBrauerCofinality
import Towers.ClassField.LocalBrauer.IntegralModelFrobenius

/-!
# Unconditional cofinality of the unramified tower

The Teichmuller root-count proves that every finite field with the integral
unramified model produced by the division-algebra construction is the
canonical unramified extension of the same degree.  Consequently the
factorial canonical tower splits every Brauer class.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open Polynomial ValuativeRel
open BGroups

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- A finite field with a formally unramified one-generated local integral
model is the canonical root-generated extension of the same degree. -/
theorem alg_formally_model
    (E : Type u) [Field E] [Algebra K E] [Module.Finite K E]
    (hmodel : UnramifiedIntegralGenerator K E) :
    Nonempty
      (E ≃ₐ[K] canonicalUnramifiedLevel K (Module.finrank K E)) := by
  let A := (ValuativeRel.valuation K).integer
  let g : A →+* E := (algebraMap K E).comp A.subtype
  letI : Algebra A E := g.toAlgebra
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    simpa [A] using integer_adic_complete K
  letI : Finite (IsLocalRing.ResidueField A) := by
    simpa [A] using local_field_residue K
  let integerEquiv :
      A ≃+* Valuation.integer (NormedField.valuation (K := K)) := by
    apply RingEquiv.subringCongr
    dsimp [A]
    ext x
    simp only [Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation K).vle_one_iff,
      ← (NormedField.valuation (K := K)).vle_one_iff]
  have hresidueCard :
      Nat.card (IsLocalRing.ResidueField A) = localResidueCard K := by
    rw [localResidueCard]
    exact Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv integerEquiv).toEquiv
  change ∃ e : E,
    let U := Algebra.adjoin A ({e} : Set E)
    Algebra.adjoin K ({e} : Set E) = ⊤ ∧
      IsIntegral A e ∧
      Algebra.FormallyUnramified A U ∧
      IsLocalRing U at hmodel
  obtain ⟨e, hgen, he, hunramified, hlocal⟩ := hmodel
  let n := Module.finrank K E
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
  have hsplit :
      ((localFrobeniusPolynomial K n).map (algebraMap K E)).Splits := by
    have h := frobenius_splits_generator
      A K E e hgen he hlocal hunramified n rfl
    simpa [localFrobeniusPolynomial, hresidueCard] using h
  have hseparable : Algebra.IsSeparable K E :=
    separable_formally_unramified A K E e hgen hunramified
  letI : Algebra.IsSeparable K E := hseparable
  exact alg_separable_splits
    K E n rfl hsplit

/-- Finite unramified extensions in the integral-model sense are uniquely
the canonical root-generated extensions. -/
theorem unramified_uniqueness_unconditional :
    CanonicalUnramifiedUniqueness K := by
  intro E _ _ _ hmodel
  exact alg_formally_model
    K E hmodel

/-- The factorial canonical unramified tower splits every Brauer class. -/
theorem factorial_cofinal_unconditional :
    ∀ x : BrauerGroup K,
      ∃ r, x ∈ relativeBrauerGroup K
        (unramifiedFactorialLevel K r) :=
  factorial_level_cofinal K
    (unramified_uniqueness_unconditional K)

end

end Towers.CField.LBrauer
