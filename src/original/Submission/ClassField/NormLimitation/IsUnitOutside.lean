import Submission.ClassField.KummerNormIndex.NthPowerPlace

/-!
# Chapter VII, Section 9, Proposition 9.2

Milne's local-to-global power criterion is the empty-`T` case of the idèle
factorization proved in Proposition 6.10.  With `T = ∅`, the product of local
unit power-class groups is trivial, so its diagonal map is surjective without
any arithmetic assumption.
-/

namespace Submission.CField.NLimita

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.HQuotie
open Submission.CField.NIndex
open Submission.CField.KNIndex
open Submission.NumberTheory.Milne

noncomputable section

universe u

/-- The unit-outside-`S` condition in Proposition 9.2. -/
def isUnitOutside
    (K : Type u) [Field K] [NumberField K]
    (a : Kˣ) (S : Finset (NumberFieldPlace K)) : Prop :=
  nthPlaceOutside K a S ∅

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating the dependent empty product still unfolds its local-unit family.
/-- The map to the empty product of local power-class groups is
surjective. -/
theorem obvious_empty_surjective
    (n : ℕ) (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) :
    Function.Surjective
      (obviousMap K n S ∅ (by simp)) := by
  intro y
  exact ⟨1, Subsingleton.elim _ _⟩

/-- Proposition 9.2 follows directly from Proposition 6.10 with no auxiliary
finite primes. -/
theorem isUnitOutside_implies_nthPower
    (h610 : (∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
          (primitiveRoots n K).Nonempty →
          ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
            ContainsAllPlaces K S →
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (n : K) ≠ 1 → v ∈ S) →
            CIGenera K S →
            ∀ (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
              (Sum.inl P : NumberFieldPlace K) ∉ S),
            Function.Surjective (obviousMap K n S T hDisjoint) →
            ∀ b : Kˣ,
              (∀ v : NumberFieldPlace K, v ∈ S →
                nthPowerPlace K n b v) →
              nthPlaceOutside K b S T →
              b ∈ (powMonoidHom n : Kˣ →* Kˣ).range)) :
    (∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
          (primitiveRoots n K).Nonempty →
          ∀ S : Finset (NumberFieldPlace K),
            ContainsAllPlaces K S →
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (n : K) ≠ 1 → v ∈ S) →
            CIGenera K S →
            ∀ a : Kˣ,
              (∀ v : NumberFieldPlace K, v ∈ S →
                nthPowerPlace K n a v) →
              isUnitOutside K a S →
              a ∈ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  intro n K _ _ hroots S hInfinite hDividing hClass a hLocal hUnit
  exact h610 n K hroots S ∅ hInfinite hDividing hClass
    (by simp)
    (obvious_empty_surjective n K S) a hLocal hUnit

end

end Submission.CField.NLimita
