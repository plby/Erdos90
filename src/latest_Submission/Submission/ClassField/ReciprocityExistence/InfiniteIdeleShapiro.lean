import Submission.ClassField.ReciprocityExistence.IdeleCup
import Submission.ClassField.ReciprocityExistence.CupRestriction
import Submission.ClassField.ReciprocityExistence.CoeffNaturality
import Submission.ClassField.ReciprocityExistence.H2Restriction
import Submission.ClassField.ReciprocityExistence.CompletionFormula
import Submission.ClassField.BrauerLocalization.CompletionNaturality

/-!
# Shapiro evaluation of the infinite-place idèle cup

The infinite coordinate of the concrete idèle decomposition is evaluated
at the chosen upper completion.  The resulting class is the literal
invariant-character cup of the embedded base infinite coordinate, with the
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
open Submission.CField.NIndex
open Submission.CField.HNorm
open Submission.CField.BLoc
open scoped IsMulCommutative

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

local instance infiniteCupIdeleAction :
    MulDistribMulAction Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  (concreteActionData (K := K) (L := L)).action

local instance infiniteCupRestrictedIdeleAction
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    MulDistribMulAction
      (CompletionPlaceStabilizer v.1
        ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  MulDistribMulAction.compHom
    (IdeleGroup (NumberField.RingOfIntegers L) L)
    (CompletionPlaceStabilizer v.1
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩).subtype

local instance infiniteCupChosenAction
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    MulDistribMulAction
      (CompletionPlaceStabilizer v.1
        ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩)
      w.1.1.Completionˣ :=
  completionDistribAction v.1
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

/-- Evaluate an idèle first on its infinite component, then at the lower
infinite place `v`, and finally at the selected upper completion `w`. -/
noncomputable def infiniteChosenMonoid
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    IdeleGroup (NumberField.RingOfIntegers L) L →* w.1.1.Completionˣ :=
  let w0 : CompletionPlacesAbove (L := L) v.1 :=
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
  (unitsEvaluationMonoid
      (K := K) (L := L) v.1 w0).comp
    ((Pi.evalMonoidHom
      (fun q : InfinitePlace K ↦
        ((z : CompletionPlacesAbove (L := L) q.1) →
          z.1.Completion)ˣ) v).comp
      ((infiniteIdelesUnits
          (K := K) (L := L)).toMonoidHom.comp
        (MonoidHom.fst
          (InfiniteAdeleRing L)ˣ
          (FiniteIdeles (NumberField.RingOfIntegers L) L))))

set_option maxHeartbeats 2000000 in
-- Evaluating the extended idèle unfolds the dependent infinite completion product.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] in
/-- Evaluating an extended base idèle at the selected upper infinite
completion is the canonical embedding of its lower infinite coordinate. -/
theorem chosen_monoid_extension
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    infiniteChosenMonoid
        (K := K) (L := L) v w
        (ideleExtensionMonoid (K := K) (L := L) a) =
      Units.map
        (completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2)).toMonoidHom
        (MulEquiv.piUnits a.1 v) := by
  rcases w with ⟨w, hw⟩
  subst v
  apply Units.ext
  rfl

/-- The categorical coefficient path used by the infinite coordinate and
Shapiro is exactly projection, regrouping, and the two evaluations. -/
noncomputable def resizedChosenRepresentation
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let w0 : CompletionPlacesAbove (L := L) v.1 :=
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
    Rep.res (CompletionPlaceStabilizer v.1 w0).subtype
        (resizedConcreteRepresentation K L) ⟶
      uliftPlaceRepresentation
        (K := K) (L := L) v.1 w0 := by
  let w0 : CompletionPlacesAbove (L := L) v.1 :=
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
  let H := CompletionPlaceStabilizer v.1 w0
  exact
    (Rep.resFunctor H.subtype).map
        (resizedInfiniteIdeles (K := K) (L := L)) ≫
      (Rep.resFunctor H.subtype).map
        (resizedIsoProducts
          (K := K) (L := L)).hom ≫
      (Rep.resFunctor H.subtype).map
        (resizedProductsEvaluation
          (K := K) (L := L) v) ≫
      uliftIntegralHom
        (completionUnitsEvaluation (K := K) (L := L) v.1 w0)

set_option maxHeartbeats 2000000 in
-- The categorical coefficient path unfolds four dependent representation morphisms.
set_option synthInstance.maxHeartbeats 500000 in
-- The chosen completion action requires deeper instance search.
omit [IsMulCommutative Gal(L/K)] in
/-- Pointwise description of the categorical infinite chosen-coordinate
coefficient path. -/
theorem chosen_representation_hom
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : Rep.res
      (CompletionPlaceStabilizer v.1
        ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩).subtype
      (resizedConcreteRepresentation K L)) :
    resizedChosenRepresentation
        (K := K) (L := L) v w x =
      Additive.ofMul
        (infiniteChosenMonoid
          (K := K) (L := L) v w x.toMul) := by
  rfl

set_option maxHeartbeats 2000000 in
-- Equivariance unfolds the chosen-coordinate representation on both sides.
set_option synthInstance.maxHeartbeats 500000 in
-- The stabilizer action and dependent completion field elaborate together.
omit [IsMulCommutative Gal(L/K)] in
/-- The concrete infinite chosen-coordinate map is equivariant for the
restricted global action. -/
theorem chosen_monoid_equivariant
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (h : CompletionPlaceStabilizer v.1
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩)
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    infiniteChosenMonoid
        (K := K) (L := L) v w (h • x) =
      h • infiniteChosenMonoid
        (K := K) (L := L) v w x := by
  have he := Rep.hom_comm_apply
    (resizedChosenRepresentation
      (K := K) (L := L) v w) h (Additive.ofMul x)
  rw [chosen_representation_hom,
    chosen_representation_hom] at he
  exact congrArg Additive.toMul he

set_option maxHeartbeats 2000000 in
-- Comparing the categorical and multiplicative coefficient paths is definitionally deep.
set_option synthInstance.maxHeartbeats 500000 in
-- The restriction morphism carries a dependent stabilizer action.
omit [IsMulCommutative Gal(L/K)] in
/-- After the harmless idèle representation change, the categorical path
is the linearization of the direct multiplicative chosen-coordinate map. -/
theorem resized_chosen_representation
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let w0 : CompletionPlacesAbove (L := L) v.1 :=
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
    let H := CompletionPlaceStabilizer v.1 w0
    (Rep.resFunctor H.subtype).map
        (multiplicativeIsoConcrete K L).hom ≫
      resizedChosenRepresentation
        (K := K) (L := L) v w =
      uliftRestrictionHom H.subtype
        (fun _ _ ↦ rfl)
        (infiniteChosenMonoid
          (K := K) (L := L) v w)
        (chosen_monoid_equivariant
          (K := K) (L := L) v w) := by
  dsimp only
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change resizedChosenRepresentation
      (K := K) (L := L) v w x =
    Additive.ofMul
      (infiniteChosenMonoid
        (K := K) (L := L) v w x.toMul)
  rw [chosen_representation_hom]
  rfl

set_option maxHeartbeats 30000000 in
-- The full coordinate, Shapiro, and coefficient-naturalness chain normalizes at once.
set_option synthInstance.maxHeartbeats 500000 in
-- The global and local cohomology representations form a deep instance tower.
set_option maxRecDepth 100000 in
/-- The full infinite coordinate and Shapiro path sends the literal global
idèle cup to the literal cup of the selected completed coefficient. -/
theorem global_multiplicative_shapiro
    (v : InfinitePlace K)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    let completion := completionChoice K L
    let w := completion.infiniteUpper v
    let w0 : CompletionPlacesAbove (L := L) v.1 :=
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) v.1) :=
      places_above_pretransitive v
    uliftCompletionUnits
        (K := K) (L := L) v.1 w0
        (resizedHDecomposition
          (K := K) (L := L)
          (globalMultiplicative2 K L a chi) (.inr v)) =
      multiplicativeLiftAdditive
        (invariantCharacterCup
          (infiniteChosenMonoid
            (K := K) (L := L) v w
            (ideleExtensionMonoid (K := K) (L := L) a))
          (fun h => by
            rw [← chosen_monoid_equivariant
              (K := K) (L := L) v w h]
            exact congrArg
              (infiniteChosenMonoid
                (K := K) (L := L) v w)
              (global_multiplicative_fixed K L a h))
          (chi.comp (CompletionPlaceStabilizer v.1 w0).subtype.toAdditive)) := by
  let completion := completionChoice K L
  let w := completion.infiniteUpper v
  let w0 : CompletionPlacesAbove (L := L) v.1 :=
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) :=
    places_above_pretransitive v
  let H := CompletionPlaceStabilizer v.1 w0
  let projection := resizedInfiniteIdeles (K := K) (L := L)
  let regroup := (resizedIsoProducts
    (K := K) (L := L)).hom
  let lowerEval := resizedProductsEvaluation
    (K := K) (L := L) v
  let globalPath :
      (Rep.resFunctor (MonoidHom.id Gal(L/K))).obj
          (resizedConcreteRepresentation K L) ⟶
      uliftUnitsRepresentation
        (K := K) (L := L) v.1 :=
    projection ≫ regroup ≫ lowerEval
  let upperEval := uliftIntegralHom
    (completionUnitsEvaluation (K := K) (L := L) v.1 w0)
  let path := resizedChosenRepresentation
    (K := K) (L := L) v w
  let rawCup := globalMultiplicativeClass K L a chi
  dsimp only
  have hcoord := (resizedIdeleFormula
    (K := K) (L := L)).2
      (globalMultiplicative2 K L a chi) v
  rw [hcoord]
  rw [resized_ideles_direct]
  rw [ulift_completion_units]
  have hG :
      groupCohomology.map (MonoidHom.id Gal(L/K)) projection 2 ≫
          groupCohomology.map (MonoidHom.id Gal(L/K)) regroup 2 ≫
          groupCohomology.map (MonoidHom.id Gal(L/K)) lowerEval 2 =
          groupCohomology.map (MonoidHom.id Gal(L/K))
          globalPath 2 := by
    ext x
    let y := groupCohomology.map (MonoidHom.id Gal(L/K)) projection 2 x
    have hRL := ConcreteCategory.congr_hom
      (groupCohomology.map_id_comp regroup lowerEval 2) y
    have hPRL := ConcreteCategory.congr_hom
      (groupCohomology.map_id_comp projection (regroup ≫ lowerEval) 2) x
    simp only [ConcreteCategory.comp_apply] at hRL hPRL
    dsimp only [y] at hRL
    change groupCohomology.map (MonoidHom.id Gal(L/K)) lowerEval 2
        (groupCohomology.map (MonoidHom.id Gal(L/K)) regroup 2
          (groupCohomology.map (MonoidHom.id Gal(L/K)) projection 2 x)) = _
    rw [← hRL]
    exact hPRL.symm
  have hH :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          globalPath 2 ≫
        groupCohomology.map H.subtype upperEval 2 =
      groupCohomology.map H.subtype path 2 := by
    rw [← groupCohomology.map_comp]
    rfl
  change groupCohomology.map H.subtype upperEval 2
      (groupCohomology.map (MonoidHom.id Gal(L/K)) lowerEval 2
        (groupCohomology.map (MonoidHom.id Gal(L/K)) regroup 2
          (groupCohomology.map (MonoidHom.id Gal(L/K)) projection 2
            (groupCohomology.map (MonoidHom.id Gal(L/K))
              (multiplicativeIsoConcrete K L).hom 2
              (multiplicativeLiftAdditive rawCup))))) = _
  have hpath :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (multiplicativeIsoConcrete K L).hom 2 ≫
        groupCohomology.map H.subtype path 2 =
      groupCohomology.map H.subtype
        ((Rep.resFunctor H.subtype).map
            (multiplicativeIsoConcrete K L).hom ≫ path) 2 := by
    rw [← groupCohomology.map_comp]
    rfl
  calc
    _ = groupCohomology.map H.subtype path 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (multiplicativeIsoConcrete K L).hom 2
          (multiplicativeLiftAdditive rawCup)) := by
      let z := groupCohomology.map (MonoidHom.id Gal(L/K))
        (multiplicativeIsoConcrete K L).hom 2
        (multiplicativeLiftAdditive rawCup)
      have hGz := ConcreteCategory.congr_hom hG z
      have hHz := ConcreteCategory.congr_hom hH z
      simp only [ConcreteCategory.comp_apply] at hGz hHz
      dsimp only [z] at hGz hHz
      rw [hGz]
      exact hHz
    _ = groupCohomology.map H.subtype
          ((Rep.resFunctor H.subtype).map
              (multiplicativeIsoConcrete K L).hom ≫ path) 2
          (multiplicativeLiftAdditive rawCup) := by
      exact ConcreteCategory.congr_hom hpath
        (multiplicativeLiftAdditive rawCup)
    _ = groupCohomology.map H.subtype
          (uliftRestrictionHom H.subtype
            (fun _ _ ↦ rfl)
            (infiniteChosenMonoid
              (K := K) (L := L) v w)
            (chosen_monoid_equivariant
              (K := K) (L := L) v w)) 2
          (multiplicativeLiftAdditive rawCup) := by
      rw [resized_chosen_representation]
      rfl
    _ = multiplicativeLiftAdditive
          (MHTwo.mapCoefficientsHom
            (infiniteChosenMonoid
              (K := K) (L := L) v w)
            (chosen_monoid_equivariant
              (K := K) (L := L) v w)
            (MHTwo.restrictionHom H.subtype
              (fun _ _ ↦ rfl) rawCup)) :=
      multiplicative_additive_coefficients
        H.subtype (fun _ _ ↦ rfl)
        (infiniteChosenMonoid
          (K := K) (L := L) v w)
        (chosen_monoid_equivariant
          (K := K) (L := L) v w) rawCup
    _ = _ := congrArg multiplicativeLiftAdditive (by
      dsimp only [rawCup]
      rw [globalMultiplicativeClass]
      rw [invariant_cup_restriction]
      rw [invariant_cup_coefficients])

set_option synthInstance.maxHeartbeats 500000 in
-- The direct-sum Brauer coordinate carries dependent local coefficient instances.
/-- The infinite coordinate of the final absolute-Brauer-valued idèle cup,
before evaluating the local Shapiro and crossed-product comparison. -/
theorem global_multiplicative_infinite
    (v : InfinitePlace K)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    multiplicativeIdeleCup K L chi
        (Additive.ofMul a) (.inr v) =
      localBrauerInclusion K L
        (completionChoice K L) (.inr v)
        (completionRelativeBrauer
          (K := K) (L := L) (completionChoice K L) (.inr v)
          (resizedHDecomposition
            (K := K) (L := L)
            (globalMultiplicative2 K L a chi) (.inr v))) := by
  change (brauerDirectInclusion K L
      (completionChoice K L)
      (directRelativeBrauer
        K L (completionChoice K L)
        (resizedHDecomposition
          (K := K) (L := L)
          (globalMultiplicative2 K L a chi)))) (.inr v) = _
  change localBrauerInclusion K L
      (completionChoice K L) (.inr v)
      (directRelativeBrauer
        K L (completionChoice K L)
        (resizedHDecomposition
          (K := K) (L := L)
          (globalMultiplicative2 K L a chi)) (.inr v)) = _
  rw [direct_relative_brauer]

end

end Submission.CField.RExist
