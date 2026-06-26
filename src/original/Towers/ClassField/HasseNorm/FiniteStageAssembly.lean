import Towers.ClassField.HasseNorm.FiniteStageCohomology
import Towers.ClassField.HasseNorm.UnramifiedH2

/-!
# Assembly of the finite-place idèle-stage cohomology

This file assembles the finite-place part of the restricted-product argument
in Proposition VII.2.5(b).  Choose a finite stage containing every ramified
finite prime.  Its degree-two cohomology is then the product of the
unrestricted completion-orbit cohomology groups at the exceptional primes:
away from that finite set, the stage uses local units, whose degree-two
cohomology vanishes by unramifiedness.
-/

namespace Towers.CField.HNorm

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.COps
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance numberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) :=
  Classical.decEq _

/-- If every upper prime over a nonexceptional finite base prime is
unramified, then the corresponding finite-stage orbit has trivial
degree-two cohomology. -/
theorem resized_stage_outside
    (S : Finset (NumberFieldPlace K))
    (hunramified :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
              (upperPrime (K := K) (L := L) P Q).asIdeal)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    Subsingleton
      (H2 (stageOrbitRepresentation
        (K := K) (L := L) S P)) := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
    Classical.choice
      (absolute_value_extension
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
      (H2 (resizedPrimesRepresentation
        (K := K) (L := L) P)) :=
    primes_subsingleton_unramified
      (K := K) (L := L) P Q hQ
  exact
    (resizedIdeleStage
      (K := K) (L := L) S P hP).injective.subsingleton

/-- Delete the cohomologically trivial coordinates outside a finite idèle
stage and identify each remaining coordinate with its unrestricted
completion orbit. -/
noncomputable def ideleStageExceptional
    (S : Finset (NumberFieldPlace K))
    (houtside :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          Subsingleton
            (H2 (stageOrbitRepresentation
              (K := K) (L := L) S P))) :
    (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H2 (stageOrbitRepresentation
          (K := K) (L := L) S P)) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H2 (resizedAboveRepresentation
          (K := K) (L := L) P.1)) where
  toFun x P :=
    ideleStageFull
      (K := K) (L := L) S P.1 P.2 (x P.1)
  invFun x P := if hP : (Sum.inl P : NumberFieldPlace K) ∈ S then
    (ideleStageFull
      (K := K) (L := L) S P hP).symm (x ⟨P, hP⟩)
  else
    0
  left_inv x := by
    funext P
    by_cases hP : (Sum.inl P : NumberFieldPlace K) ∈ S
    · change (if hP' : (Sum.inl P : NumberFieldPlace K) ∈ S then
          (ideleStageFull
            (K := K) (L := L) S P hP').symm
            ((ideleStageFull
              (K := K) (L := L) S P hP') (x P))
        else 0) = x P
      simp only [dif_pos hP, AddEquiv.symm_apply_apply]
    · letI := houtside P hP
      exact Subsingleton.elim _ _
  right_inv x := by
    funext P
    change (ideleStageFull
      (K := K) (L := L) S P.1 P.2)
        (if hP' : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
          (ideleStageFull
            (K := K) (L := L) S P.1 hP').symm (x ⟨P.1, hP'⟩)
        else 0) = x P
    simp only [dif_pos P.2, AddEquiv.apply_symm_apply]
  map_add' x y := by
    funext P
    exact
      (ideleStageFull
        (K := K) (L := L) S P.1 P.2).map_add (x P.1) (y P.1)

/-- Finite-place content of Proposition VII.2.5(b): a suitable finite idèle
stage together with the equivalence identifying its degree-two cohomology
with the finite family of unrestricted completion-orbit cohomology groups at
its exceptional finite primes.  No cyclicity hypothesis is needed. -/
noncomputable def resizedStageExceptional :
    Σ S : Finset (NumberFieldPlace K),
      H2 (resizedStageRepresentation
        (K := K) (L := L) S) ≃+
        (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
            (Sum.inl P : NumberFieldPlace K) ∈ S},
          H2 (resizedAboveRepresentation
            (K := K) (L := L) P.1)) := by
  let hexists :=
    stage_unramified_outside (K := K) (L := L)
  let S := Classical.choose hexists
  have hunramified := Classical.choose_spec hexists
  refine ⟨S, (ideleStagePi
    (K := K) (L := L) S).trans ?_⟩
  exact ideleStageExceptional
    (K := K) (L := L) S
      (resized_stage_outside
        (K := K) (L := L) S hunramified)

/-- Propositional packaging of
`resizedStageExceptional`. -/
theorem resized_stage_exceptional :
    Nonempty
      (Σ S : Finset (NumberFieldPlace K),
        H2 (resizedStageRepresentation
          (K := K) (L := L) S) ≃+
          (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
              (Sum.inl P : NumberFieldPlace K) ∈ S},
            H2 (resizedAboveRepresentation
              (K := K) (L := L) P.1))) :=
  ⟨resizedStageExceptional
    (K := K) (L := L)⟩

end

end Towers.CField.HNorm
