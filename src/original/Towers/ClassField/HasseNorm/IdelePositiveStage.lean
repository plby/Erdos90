import Towers.ClassField.BrauerLocalization.RestrictedNegOne
import Towers.ClassField.Shifting.SubsingletonLinearEquiv

/-!
# Positive-degree cohomology of finite idèle stages

This file upgrades the degree-one and degree-two finite-stage calculations to
every positive degree.  At a finite prime outside the exceptional set the
decomposition group is cyclic.  Proposition III.1.1 gives vanishing in degree
one, the norm calculation gives vanishing in degree two, and cyclic
periodicity supplies all remaining positive degrees.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.COps
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.BLoc
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Proposition II.1.25 applied to the product of the finite-prime orbit
representations, in an arbitrary degree. -/
noncomputable def resizedIdelePi
    (S : Finset (NumberFieldPlace K)) (n : ℕ) :
    groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) S) n ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        groupCohomology
          (stageOrbitRepresentation
            (K := K) (L := L) S P) n) := by
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
    stageOrbitRepresentation (K := K) (L := L) S P
  let e₁ := ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n).mapIso
    (stageIsoCategorical
      (K := K) (L := L) S)).toLinearEquiv.toAddEquiv
  let e₂ := (groupProductIso
    (ULift.{u} ℤ) Gal(L/K) A n).toLinearEquiv.toAddEquiv
  let e₃ := moduleCatPi
    (fun P ↦ groupCohomology (A P) n)
  exact e₁.trans (e₂.trans e₃)

/-- At an exceptional finite prime, the stage orbit is the unrestricted
completion orbit in every cohomological degree. -/
noncomputable def stageCohomologyFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) (n : ℕ) :
    groupCohomology
        (stageOrbitRepresentation
          (K := K) (L := L) S P) n ≃+
      groupCohomology
        (resizedAboveRepresentation
          (K := K) (L := L) P) n :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n).mapIso
    (stageIsoFull
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

/-- At a nonexceptional finite prime, the stage orbit is the product of
upper local-unit groups in every cohomological degree. -/
noncomputable def resizedStageCohomology
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) (n : ℕ) :
    groupCohomology
        (stageOrbitRepresentation
          (K := K) (L := L) S P) n ≃+
      groupCohomology
        (resizedPrimesRepresentation
          (K := K) (L := L) P) n :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n).mapIso
    (resizedStageIso
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

/-- Restricted Shapiro for the product of local units above a finite base
prime, in every degree. -/
noncomputable def resizedAboveCohomology
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) (n : ℕ) :
    groupCohomology
        (resizedPrimesRepresentation
          (K := K) (L := L) P) n ≃+
      groupCohomology
        (resizedUnitsRepresentation
          (K := K) (L := L) P Q) n :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n).mapIso
      (aboveInducedIso
        (K := K) (L := L) P Q)) ≪≫
    shapiro
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (resizedUnitsRepresentation
        (K := K) (L := L) P Q) n).toLinearEquiv.toAddEquiv

set_option synthInstance.maxHeartbeats 1000000 in
-- Shapiro for the dependent product of local units needs deeper instance search.
set_option maxHeartbeats 6000000 in
-- The positive-degree vanishing proof normalizes the induced representation.
/-- The chosen local-unit factor at an unramified prime has trivial
cohomology in every positive degree. -/
theorem cohomology_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton
      (groupCohomology
        (resizedUnitsRepresentation
          (K := K) (L := L) P Q) n) := by
  let H := primeAboveStabilizer (K := K) (L := L) P Q
  let A := resizedUnitsRepresentation
    (K := K) (L := L) P Q
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H :=
    above_stabilizer_unramified
      (K := K) (L := L) P Q hQ
  letI : CommGroup H := IsCyclic.commGroup
  let g := Classical.choose (IsCyclic.exists_generator (α := H))
  let hg := Classical.choose_spec (IsCyclic.exists_generator (α := H))
  have h₁ : Subsingleton (groupCohomology A 1) := by
    exact resized_1_subsingleton
      (K := K) (L := L) P Q hQ
  have h₂ : Subsingleton (groupCohomology A 2) := by
    letI := unitsStabilizerAction
      (K := K) (L := L) P Q
    letI : Subsingleton
        (H2 (resizedPrimesRepresentation
          (K := K) (L := L) P)) :=
      primes_subsingleton_unramified
      (K := K) (L := L) P Q hQ
    exact (resizedAboveUnits
      (K := K) (L := L) P Q).symm.injective.subsingleton
  exact subsingleton_cohomology_cyclic A g hg h₁ h₂ n hn

/-- At an unramified base prime, the whole orbit of upper local-unit
factors has trivial cohomology in every positive degree. -/
theorem resized_above_subsingleton
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton
      (groupCohomology
        (resizedPrimesRepresentation
          (K := K) (L := L) P) n) := by
  letI : Subsingleton
      (groupCohomology
        (resizedUnitsRepresentation
          (K := K) (L := L) P Q) n) :=
    cohomology_subsingleton_unramified
      (K := K) (L := L) P Q hQ n hn
  exact (resizedAboveCohomology
    (K := K) (L := L) P Q n).injective.subsingleton

/-- Every nonexceptional finite-stage orbit has trivial positive-degree
cohomology when all upper primes outside the stage are unramified. -/
theorem cohomology_subsingleton_outside
    (S : Finset (NumberFieldPlace K))
    (hunramified :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
              (upperPrime (K := K) (L := L) P Q).asIdeal)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton
      (groupCohomology
        (stageOrbitRepresentation
          (K := K) (L := L) S P) n) := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
    Classical.choice (absolute_value_extension
      (K := K) (L := L) (FinitePlace.mk P).val)
  let Q₀ : UpperPrimeFactors (K := K) (L := L) P :=
    placeUpperFactor (K := K) (L := L) P w
  let Q : FinitePrimesAbove (K := K) (L := L) P :=
    upperPrimesAbove (K := K) (L := L) P Q₀
  have hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal := by
    simpa only [Q, upper_primes_above] using
      hunramified P hP Q₀
  letI : Subsingleton
      (groupCohomology
        (resizedPrimesRepresentation
          (K := K) (L := L) P) n) :=
    resized_above_subsingleton
      (K := K) (L := L) P Q hQ n hn
  exact (resizedStageCohomology
    (K := K) (L := L) S P hP n).injective.subsingleton

end

end Towers.CField.HNorm
