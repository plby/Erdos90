import Submission.ClassField.ReciprocityExistence.OrbitEvaluation
import Submission.ClassField.ReciprocityExistence.CupRestriction
import Submission.ClassField.ReciprocityExistence.CoeffNaturality
import Submission.ClassField.ReciprocityExistence.H2Restriction

/-!
# Shapiro evaluation of the finite-orbit character cup

The finite-orbit Shapiro map sends Milne's literal global character cup to
the same literal cup on the selected completed coefficient, with the
character restricted to the chosen-place stabilizer.
-/

namespace Submission.CField.RExist

open CategoryTheory Rep Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm
open scoped IsMulCommutative

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

local instance finiteOrbitCupCompletionPlacesPretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

local instance finiteOrbitCupAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
  aboveUnitsAction (K := K) (L := L) P

local instance finiteOrbitRestrictedCupAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    MulDistribMulAction
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
  MulDistribMulAction.compHom
    (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ)
    (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype

local instance finiteOrbitChosenCupAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    MulDistribMulAction
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
      w.1.Completionˣ :=
  completionDistribAction (FinitePlace.mk P).val w

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent product action needs an enlarged instance search.
omit [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] in
/-- The restricted orbit action is literally restriction of the global
action along the stabilizer inclusion. -/
theorem restricted_cup_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (m : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ) :
    h • m = (CompletionPlaceStabilizer
      (FinitePlace.mk P).val w).subtype h • m :=
  rfl

set_option maxHeartbeats 1000000 in
-- Equivariance is extracted from the already-constructed representation morphism.
set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the dependent stabilizer action needs a larger instance-search budget.
omit [IsMulCommutative Gal(L/K)] in
/-- Concrete chosen-coordinate evaluation is equivariant for the restricted
global action and the completion-place stabilizer action. -/
theorem orbit_chosen_equivariant
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (m : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ) :
    orbitChosenMonoid (K := K) (L := L) P w (h • m) =
      h • orbitChosenMonoid
        (K := K) (L := L) P w m := by
  have he := Rep.hom_comm_apply
    (chosenRepresentationHom
      (K := K) (L := L) P w) h (Additive.ofMul m)
  rw [resized_chosen_hom,
    resized_chosen_hom] at he
  exact congrArg Additive.toMul he

set_option maxHeartbeats 1000000 in
-- The dependent-product coefficient map is compared extensionally.
set_option synthInstance.maxHeartbeats 300000 in
-- The dependent-product coefficient map requires deeper instance search.
omit [IsMulCommutative Gal(L/K)] in
/-- The adjointly defined finite-orbit evaluation morphism is the resized
linearization of the concrete multiplicative coordinate map. -/
theorem orbit_chosen_representation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    chosenRepresentationHom
        (K := K) (L := L) P w =
      uliftRestrictionHom
        (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
        (restricted_cup_smul (K := K) (L := L) P w)
        (orbitChosenMonoid (K := K) (L := L) P w)
        (orbit_chosen_equivariant
          (K := K) (L := L) P w) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change chosenRepresentationHom
      (K := K) (L := L) P w x =
    Additive.ofMul
      (orbitChosenMonoid
        (K := K) (L := L) P w x.toMul)
  rw [resized_chosen_hom]

set_option maxHeartbeats 8000000 in
-- Restriction, coefficient transport, and the literal cup representative
-- are normalized in a single degree-two expression.
set_option synthInstance.maxHeartbeats 300000 in
-- Restriction and coefficient transport require the full stabilizer instance tower.
/-- Shapiro evaluation carries the finite-orbit literal cup to the literal
cup of the evaluated coefficient and restricted character. -/
theorem finite_cup_shapiro
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ)
    (hx : ∀ g : Gal(L/K), g • x = x)
    (chi : CharacterModule (Additive Gal(L/K))) :
    groupCohomology.map
        (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
        (chosenRepresentationHom
          (K := K) (L := L) P w) 2
        (multiplicativeLiftAdditive
          (invariantCharacterCup x hx chi)) =
      multiplicativeLiftAdditive
        (invariantCharacterCup
          (orbitChosenMonoid
            (K := K) (L := L) P w x)
          (fun h => by
            rw [← orbit_chosen_equivariant
                (K := K) (L := L) P w h x,
              restricted_cup_smul,
              hx])
          (chi.comp (CompletionPlaceStabilizer
            (FinitePlace.mk P).val w).subtype.toAdditive)) := by
  rw [orbit_chosen_representation]
  calc
    _ = multiplicativeLiftAdditive
        (MHTwo.mapCoefficientsHom
          (orbitChosenMonoid
            (K := K) (L := L) P w)
          (orbit_chosen_equivariant
            (K := K) (L := L) P w)
          (MHTwo.restrictionHom
            (CompletionPlaceStabilizer
              (FinitePlace.mk P).val w).subtype
            (restricted_cup_smul
              (K := K) (L := L) P w)
            (invariantCharacterCup x hx chi))) :=
      multiplicative_additive_coefficients
        (CompletionPlaceStabilizer
          (FinitePlace.mk P).val w).subtype
        (restricted_cup_smul (K := K) (L := L) P w)
        (orbitChosenMonoid (K := K) (L := L) P w)
        (orbit_chosen_equivariant
          (K := K) (L := L) P w)
        (invariantCharacterCup x hx chi)
    _ = _ := congrArg multiplicativeLiftAdditive (by
      rw [invariant_cup_restriction]
      rw [invariant_cup_coefficients])

set_option maxHeartbeats 2000000 in
-- The orbit reindexing and completion-product Shapiro definitions expose
-- the cohomology map proved above only after their two equivalences reduce.
set_option synthInstance.maxHeartbeats 300000 in
-- The orbit equivalence and Shapiro map share dependent completion instances.
/-- The full finite orbit-to-chosen-completion equivalence has the same cup
formula as its restriction-and-evaluation presentation. -/
theorem orbit_cup_shapiro
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ)
    (hx : ∀ g : Gal(L/K), g • x = x)
    (chi : CharacterModule (Additive Gal(L/K))) :
    uliftUnitsH
        (K := K) (L := L) P w
        (resizedPlaceProduct
          (K := K) (L := L) P
          (multiplicativeLiftAdditive
            (invariantCharacterCup x hx chi))) =
      multiplicativeLiftAdditive
        (invariantCharacterCup
          (orbitChosenMonoid
            (K := K) (L := L) P w x)
          (fun h => by
            rw [← orbit_chosen_equivariant
                (K := K) (L := L) P w h x,
              restricted_cup_smul,
              hx])
          (chi.comp (CompletionPlaceStabilizer
            (FinitePlace.mk P).val w).subtype.toAdditive)) := by
  change (uliftShapiroIso
      (K := K) (L := L) (FinitePlace.mk P).val w 2).hom
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIsoOrbit
          (K := K) (L := L) P).inv 2
        (multiplicativeLiftAdditive
          (invariantCharacterCup x hx chi))) = _
  let cup := multiplicativeLiftAdditive
    (invariantCharacterCup x hx chi)
  have hshapiro := resizedOrbitShapiro
    (K := K) (L := L) P w cup
  have hcup := finite_cup_shapiro
    (K := K) (L := L) P w x hx chi
  exact hshapiro.trans hcup

end

end Submission.CField.RExist
