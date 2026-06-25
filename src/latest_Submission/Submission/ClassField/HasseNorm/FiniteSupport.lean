import Submission.ClassField.HasseNorm.LocalGlobalCriterion
import Submission.ClassField.HasseNorm.UnramifiedLocal
import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.NumberTheory.Locals.UnramifiedExtensions

/-!
# Finite support of Hasse norm localization

A global element is a unit away from finitely many finite primes.  Outside
the further finite set of ramified primes, Proposition III.1.2 makes that
unit a norm from the chosen upper completion.  Infinite places form a finite
set, so the local norm class has finite support.
-/

namespace Submission.CField.HNorm

open Filter Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

-- The finite-place norm subgroup and ramification data elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
-- Simultaneously elaborating local norm subgroups and ramification data is instance-heavy.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- A global element has nontrivial class in the chosen local norm quotients
at only finitely many places. -/
theorem hasseNonBridge :
    HasseNonBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion x
  let R := RingOfIntegers K
  let S := RingOfIntegers L
  let badUnit : Set (HeightOneSpectrum R) :=
    {P | Units.map (FinitePlace.embedding P).toMonoidHom x ∉
      IdeleUnitSubgroup R K P}
  have hbadUnit : badUnit.Finite := by
    have hrestricted := Filter.eventually_cofinite.mp
      (principalIdele R K x).2.property
    refine hrestricted.subset ?_
    intro P hP
    simpa only [badUnit, Set.mem_setOf_eq, principal_idele_finite] using hP
  let ramifiedIdeals : Set (Ideal R) :=
    {p | ∃ Q : Ideal S, Ideal.IsPrime Q ∧ Q ≠ ⊥ ∧
      Q.under R = p ∧ Ideal.ramificationIdx p Q ≠ 1}
  have hramifiedIdeals : ramifiedIdeals.Finite := by
    exact ramified_base_primes R S
  let badRamified : Set (HeightOneSpectrum R) :=
    {P | P.asIdeal ∈ ramifiedIdeals}
  have hprimeInjective : Function.Injective
      (fun P : HeightOneSpectrum R ↦ P.asIdeal) := by
    intro P Q h
    exact HeightOneSpectrum.ext_iff.mpr h
  have hbadRamified : badRamified.Finite := by
    exact Set.Finite.preimage hprimeInjective.injOn hramifiedIdeals
  let exceptional : Set (NumberFieldPlace K) :=
    Sum.inl '' (badUnit ∪ badRamified) ∪
      Sum.inr '' (Set.univ : Set (InfinitePlace K))
  have hexceptional : exceptional.Finite := by
    exact ((hbadUnit.union hbadRamified).image Sum.inl).union
      ((Set.toFinite (Set.univ : Set (InfinitePlace K))).image Sum.inr)
  refine hexceptional.subset ?_
  intro place hplace
  cases place with
  | inl P =>
      by_cases hunit : P ∈ badUnit
      · exact Set.mem_union_left _ ⟨P, Set.mem_union_left _ hunit, rfl⟩
      by_cases hramified : P ∈ badRamified
      · exact Set.mem_union_left _ ⟨P, Set.mem_union_right _ hramified, rfl⟩
      exfalso
      apply hplace
      change Units.map (FinitePlace.embedding P).toMonoidHom x ∈
        (finiteCompletionNorm (K := K) (L := L) P
          (completion.finiteUpper P)).range
      apply units_range_unramified
      · let Q := completion.finiteUpper P
        let q := upperPrime (K := K) (L := L) P Q
        letI : q.asIdeal.LiesOver P.asIdeal := by
          constructor
          exact (congrArg HeightOneSpectrum.asIdeal
            (upperPrime_under (K := K) (L := L) P Q)).symm
        apply (unramified_ramification_idx
          P.asIdeal q.asIdeal q.ne_bot).2
        by_contra hramificationIdx
        apply hramified
        exact ⟨q.asIdeal, q.isPrime, q.ne_bot,
          congrArg HeightOneSpectrum.asIdeal
            (upperPrime_under (K := K) (L := L) P Q),
          hramificationIdx⟩
      · exact not_not.mp hunit
  | inr v =>
      exact Set.mem_union_right _ ⟨v, Set.mem_univ v, rfl⟩

/-- The two arithmetic inputs now give the literal norm-quotient
localization construction used in the proof of the Hasse norm theorem. -/
theorem hasseConstructionBridge :
    HasseConstructionBridge.{u} :=
  hasse_construction_components
    hasseGlobalBridge
    hasseNonBridge

/-- The first assertion of the Hasse norm theorem: a fixed global element
is a norm from a suitable completion above every place outside a finite
set. -/
theorem hasseAlmostEverywhere :
    HasseAlmostEverywhere.{u} :=
  almost_everywhere_construction
    hasseExistenceBridge
    hasseConstructionBridge

end

end Submission.CField.HNorm
