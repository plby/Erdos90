import Submission.ClassField.ReciprocityExistence.FiniteOrbitShapiro
import Submission.ClassField.ReciprocityExistence.FiniteCoordinates

/-!
# The finite chosen-completion cup coordinate in Theorem VII.8.1

The finite coordinate of the global multiplicative idèle cup, after orbit
reindexing and Shapiro, is the literal character cup of the base idèle
coordinate embedded into the selected upper completion.
-/

namespace Submission.CField.RExist

open scoped IsMulCommutative
open CategoryTheory Rep Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

local instance finiteCupOrbitAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
  aboveUnitsAction (K := K) (L := L) P

local instance finiteCupRestrictedOrbitAction
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

local instance finiteCupChosenAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    MulDistribMulAction
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
      w.1.Completionˣ :=
  completionDistribAction (FinitePlace.mk P).val w

set_option maxHeartbeats 3000000 in
-- The global idèle action, dependent finite orbit, and selected completion
-- are all present in the specialized cup expression.
set_option synthInstance.maxHeartbeats 500000 in
-- The coefficient equality occurs under a cup class with a dependent
-- invariance proof.
set_option maxRecDepth 100000 in
/-- After finite-orbit Shapiro, the global idèle cup is the cup of the
embedded base coordinate with the stabilizer-restricted character. -/
theorem cupStabilizerCoordinate
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    let w := hasseChosenPlace
      (completionChoice K L) (.inl P)
    let x := primesAboveMonoid (K := K) (L := L) P
      (ideleExtensionMonoid (K := K) (L := L) a)
    let hx : ∀ g : Gal(L/K), g • x = x := fun g => by
      rw [← above_monoid_equivariant K L P]
      exact congrArg
        (primesAboveMonoid (K := K) (L := L) P)
        (global_multiplicative_fixed K L a g)
    uliftUnitsH
        (K := K) (L := L) P w
        (resizedPlaceProduct
          (K := K) (L := L) P
          (multiplicativeLiftAdditive
            (invariantCharacterCup x hx chi))) =
      multiplicativeLiftAdditive
        (invariantCharacterCup
          (chosenMonoidHom
            (K := K) (L := L) P w (a.2.1 P))
          (fun h => by
            rw [← orbit_chosen_monoid
                (K := K) (L := L) P w a,
              ← orbit_chosen_equivariant
                (K := K) (L := L) P w h x,
              restricted_cup_smul,
              hx])
          (chi.comp (CompletionPlaceStabilizer
            (FinitePlace.mk P).val w).subtype.toAdditive)) := by
  let w := hasseChosenPlace
    (completionChoice K L) (.inl P)
  let x := primesAboveMonoid (K := K) (L := L) P
    (ideleExtensionMonoid (K := K) (L := L) a)
  let hx : ∀ g : Gal(L/K), g • x = x := fun g => by
    rw [← above_monoid_equivariant K L P]
    exact congrArg
      (primesAboveMonoid (K := K) (L := L) P)
      (global_multiplicative_fixed K L a g)
  dsimp only
  have h := orbit_cup_shapiro P w x hx chi
  calc
    _ = multiplicativeLiftAdditive
        (invariantCharacterCup
          (orbitChosenMonoid
            (K := K) (L := L) P w x)
          (fun h => by
            rw [← orbit_chosen_equivariant
                (K := K) (L := L) P w h x,
              restricted_cup_smul,
              hx])
          (chi.comp (CompletionPlaceStabilizer
            (FinitePlace.mk P).val w).subtype.toAdditive)) := h
    _ = _ := by
      apply congrArg multiplicativeLiftAdditive
      apply invariant_cup_congr
      exact orbit_chosen_monoid
        (K := K) (L := L) P w a

end

end Submission.CField.RExist
