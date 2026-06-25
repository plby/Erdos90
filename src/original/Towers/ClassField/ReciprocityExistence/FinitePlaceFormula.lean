import Towers.ClassField.ReciprocityExistence.FiniteOrbitShapiro
import Towers.ClassField.ReciprocityExistence.FiniteCoordinates
import Towers.ClassField.ReciprocityExistence.FiniteNormalization
import Towers.ClassField.ReciprocityExistence.PlaceFormula
import Towers.ClassField.ReciprocityExistence.OrbitNaturality
import Towers.ClassField.ReciprocityExistence.FiniteCupCoordinate
import Towers.ClassField.BrauerLocalization.FiniteNaturality

/-!
# The finite-place cup coordinate in Theorem VII.8.1

The global idèle cup is evaluated at the chosen upper completion, passed
through Shapiro, and compared with the III.3.6 local cup invariant.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open CategoryTheory groupCohomology
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.LClass
open Towers.CField.LRecip
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm
open Towers.CField.BLoc

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 3000000 in
-- Relabelling the completed stabilizer cup unfolds the local Galois action
-- and the chosen prime-adic embedding simultaneously.
set_option synthInstance.maxHeartbeats 500000 in
-- The stabilizer and completed-field actions must be synthesized in the
-- same dependent completion context.
/-- The stabilizer cup obtained from finite-orbit Shapiro is the relabelling
of the literal cup over the chosen completed field extension. -/
theorem stabilizer_cup_local
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (y : (P.adicCompletion K)ˣ)
    (chi : RationalCharacter Gal(L/K)) :
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite (CompletionPlacesAbove (L := L) v) :=
      absolute_extensions_separable v
    letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) v) :=
      completion_above_pretransitive P
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
        w.1.Completionˣ := completionDistribAction v w
    let e := completionStabilizerEquiv
      (K := K) (L := L) v w
    let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
      (CompletionPlaceStabilizer v w).subtype.comp e.symm.toMonoidHom
    let b := Units.map
      (placeCompletionAdic P).symm.toRingHom.toMonoidHom y
    localHStabilizer
        (K := K) (L := L) v w
        (invariantCharacterCup
          (Units.map (algebraMap v.Completion w.1.Completion) b)
          (multiplicative_base_fixed
            v.Completion w.1.Completion b)
          (chi.comp intoGlobal.toAdditive)) =
      invariantCharacterCup
        (chosenMonoidHom
          (K := K) (L := L) P w y)
        (fun h => by
          rw [chosen_monoid_canonical]
          apply Units.ext
          change stabilizerRingHom v w h
              (algebraMap v.Completion w.1.Completion b) =
            algebraMap v.Completion w.1.Completion b
          let eh : Gal(w.1.Completion/v.Completion) := e h
          change eh (algebraMap v.Completion w.1.Completion b) =
            algebraMap v.Completion w.1.Completion b
          exact eh.commutes b)
        (chi.comp (CompletionPlaceStabilizer v w).subtype.toAdditive) := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  let e := completionStabilizerEquiv
    (K := K) (L := L) v w
  let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
    (CompletionPlaceStabilizer v w).subtype.comp e.symm.toMonoidHom
  let b := Units.map
    (placeCompletionAdic P).symm.toRingHom.toMonoidHom y
  dsimp only
  unfold localHStabilizer
  rw [invariant_cup_restriction]
  have hchar :
      (chi.comp intoGlobal.toAdditive).comp e.toMonoidHom.toAdditive =
        chi.comp (CompletionPlaceStabilizer v w).subtype.toAdditive := by
    ext t
    simp [intoGlobal, e]
  change invariantCharacterCup _ _
      ((chi.comp intoGlobal.toAdditive).comp e.toMonoidHom.toAdditive) = _
  rw [hchar]
  apply invariant_cup_congr
    (G := CompletionPlaceStabilizer v w)
    (M := w.1.Completionˣ)
    (hxy := (chosen_monoid_canonical
      (K := K) (L := L) P w y).symm)

set_option maxHeartbeats 20000000 in
-- Comparing the global finite coordinate with the local invariant traverses
-- Shapiro, completion relabelling, and the universe-polymorphic Brauer invariant
-- equivalence, which exceeds the smaller deterministic budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The proof carries the global, orbit, stabilizer, and local Galois actions
-- at once, so instance synthesis needs a larger deterministic budget.
/-- The finite coordinate of the literal global idèle cup has exactly the
local cup invariant used in the transported Proposition III.3.6 formula. -/
theorem finite_cup_invariant
    (data : BData K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : RationalCharacter Gal(L/K)) :
    data.placeInvariant.invariant (.inl P)
        (multiplicativeIdeleCup K L chi
          (Additive.ofMul a) (.inl P)) =
      (characterFormulaData K L P
        (hasseChosenPlace
          (completionChoice K L) (.inl P))).cupInvariant
        (a.2.1 P) chi := by
  let completion := completionChoice K L
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : MulDistribMulAction Gal(L/K)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
    aboveUnitsAction (K := K) (L := L) P
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  let e := completionStabilizerEquiv
    (K := K) (L := L) v w
  let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
    (CompletionPlaceStabilizer v w).subtype.comp e.symm.toMonoidHom
  let b : v.Completionˣ := Units.map
    (placeCompletionAdic P).symm.toRingHom.toMonoidHom
      (a.2.1 P)
  let localCup : MHTwo
      Gal(w.1.Completion/v.Completion) w.1.Completionˣ :=
    invariantCharacterCup
      (Units.map (algebraMap v.Completion w.1.Completion) b)
      (multiplicative_base_fixed
        v.Completion w.1.Completion b)
      (chi.comp intoGlobal.toAdditive)
  let coordinate :=
    resizedPlaceProduct
      (K := K) (L := L) P
      (multiplicativeLiftAdditive
        (invariantCharacterCup
          (primesAboveMonoid (K := K) (L := L) P
            (ideleExtensionMonoid (K := K) (L := L) a))
          (fun g => by
            rw [← above_monoid_equivariant K L P]
            exact congrArg
              (primesAboveMonoid (K := K) (L := L) P)
              (global_multiplicative_fixed K L a g))
          chi))
  have hshapiro := cupStabilizerCoordinate K L P a chi
  have hstabilizer := stabilizer_cup_local
    (K := K) (L := L) P w (a.2.1 P) chi
  have hlocalRelabel :=
    h_stabilizer_multiplicative
      (K := K) (L := L) v
      (fun x y => (FinitePlace.mk P).add_le x y) w localCup
  have hchosen :
      resizedPlaceStabilizer
          (K := K) (L := L) completion (.inl P) coordinate =
        (uliftHasseNorm
          (K := K) (L := L) v w).symm
          ((h2Stabilizer
            (K := K) (L := L) v w
            (fun x y => (FinitePlace.mk P).add_le x y))
            (multiplicativeLiftAdditive localCup)) := by
    change uliftUnitsH
        (K := K) (L := L) P w coordinate = _
    rw [hshapiro]
    apply (uliftHasseNorm
      (K := K) (L := L) v w).injective
    rw [AddEquiv.apply_symm_apply, hlocalRelabel]
    rw [← hstabilizer]
    obtain ⟨c, hc⟩ := MHTwo.exists_mk_eq
      (localHStabilizer
        (K := K) (L := L) v w localCup)
    rw [← hc]
    change groupCohomology.map
        (MonoidHom.id (CompletionPlaceStabilizer v w))
        (uliftIsoHasse
          (K := K) (L := L) v w).hom 2
        (normalizedCocycleU c) =
      normalizedCocycleU c
    rw [normalizedCocycleU,
      groupCohomology.H2π_comp_map_apply]
    congr 1
  have hrelative :
      completionRelativeBrauer
          (K := K) (L := L) completion (.inl P) coordinate =
        (resizedChosen2
            K L completion (.inl P)).symm
          ((uliftHasseNorm
              (K := K) (L := L) v w).symm
            ((h2Stabilizer
                (K := K) (L := L) v w
                (fun x y => (FinitePlace.mk P).add_le x y))
              (multiplicativeLiftAdditive localCup))) := by
    change (resizedChosen2
        K L completion (.inl P)).symm
      (resizedPlaceStabilizer
        (K := K) (L := L) completion (.inl P) coordinate) = _
    rw [hchosen]
  rw [data.placeInvariant.finite_eq P]
  rw [global_multiplicative_finite]
  rw [hrelative]
  rw [multiplicative_h_2 K L P localCup]
  change (carryBrauerInvariant v.Completion
      ((CProduc.hRelativeBrauer
          v.Completion w.1.Completion localCup :
        relativeBrauerGroup v.Completion w.1.Completion) :
        BrauerGroup v.Completion)).toAdd = _
  exact formula_universe_cup
    K L P w (a.2.1 P) chi

end

end Towers.CField.RExist
