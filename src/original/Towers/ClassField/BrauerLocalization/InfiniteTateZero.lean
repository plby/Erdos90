import Towers.ClassField.BrauerLocalization.LocalHilbert90
import Towers.ClassField.BrauerLocalization.Relative2Comparison
import Towers.ClassField.BrauerLocalization.ArchimedeanData
import Towers.ClassField.Shifting.GroupPeriodicityOdd
import Towers.ClassField.CrossedProducts.FiniteExtensionExponent
import Towers.ClassField.GrunwaldWang.PossibleInfiniteDegree

/-!
# Archimedean local Tate-zero cardinality in Proposition VII.2.7

For an infinite completion, the relative Brauer group has cardinality the
local degree.  Both are one for `R/R` and `C/C`, while both are two for
`C/R`.  Cyclic periodicity and the existing completion-place comparison
then identify this cardinality with Tate degree zero for the local unit
representation.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation
open NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Shifting
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.CBrauer
open Towers.CField.GWang
open Towers.CField.HNorm
open groupCohomology

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 500000 in
-- Archimedean completion structures and Brauer-group case splits elaborate together.
set_option maxHeartbeats 5000000 in
/-- At an infinite place, the relative Brauer group of the completed
extension has cardinality its local degree. -/
theorem infinite_relative_finrank
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    Nat.card (relativeBrauerGroup v.1.Completion w.1.1.Completion) =
      Module.finrank v.1.Completion w.1.1.Completion := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : FiniteDimensional v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  have hdegree : Module.finrank v.1.Completion w.1.1.Completion =
      Nat.card (absoluteValueDecomposition v.1 w.1.1) :=
    infiniteDegreeCompatibility K L v w
  have hstabilizer :
      absoluteValueDecomposition v.1 w.1.1 =
        MulAction.stabilizer Gal(L/K) w.1 := by
    rw [absolute_decomposition_stabilizer]
    ext sigma
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply InfinitePlace.ext
      exact fun x ↦ DFunLike.congr_fun h x
    · intro h
      exact congrArg (fun z : InfinitePlace L ↦ z.1) h
  rcases w.1.isReal_or_isComplex with hwreal | hwcomplex
  · have hcardD : Nat.card (absoluteValueDecomposition v.1 w.1.1) = 1 := by
      rw [hstabilizer, InfinitePlace.card_stabilizer, if_pos]
      exact hwreal.isUnramified K
    have hfinrank : Module.finrank v.1.Completion w.1.1.Completion = 1 :=
      hdegree.trans hcardD
    letI : Subsingleton
        (relativeBrauerGroup v.1.Completion w.1.1.Completion) :=
      ⟨fun x y ↦ by
        have hx := relative_brauer_extension
          v.1.Completion w.1.1.Completion x
        have hy := relative_brauer_extension
          v.1.Completion w.1.1.Completion y
        rw [hfinrank, pow_one] at hx hy
        exact hx.trans hy.symm⟩
    exact Nat.card_unique.trans hfinrank.symm
  · rcases v.isReal_or_isComplex with hvreal | hvcomplex
    · have hramified : w.1.IsRamified K := by
        rw [InfinitePlace.isRamified_iff]
        exact ⟨hwcomplex, by
          simpa [InfinitePlace.LiesOver.comap_eq w.1 v] using hvreal⟩
      have hcardD : Nat.card
          (absoluteValueDecomposition v.1 w.1.1) = 2 := by
        rw [hstabilizer, InfinitePlace.card_stabilizer, if_neg hramified]
      have hfinrank : Module.finrank v.1.Completion w.1.1.Completion = 2 :=
        hdegree.trans hcardD
      letI : IsAlgClosed w.1.1.Completion :=
        alg_closed_ring
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwcomplex).symm
      letI : Subsingleton (BrauerGroup w.1.1.Completion) :=
        brauer_subsingleton_closed w.1.1.Completion
      have htop : relativeBrauerGroup v.1.Completion w.1.1.Completion = ⊤ := by
        apply le_antisymm le_top
        intro x _
        rw [relative_brauer_group]
        exact Subsingleton.elim _ _
      let eRelative : relativeBrauerGroup v.1.Completion
          w.1.1.Completion ≃* BrauerGroup v.1.Completion :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      let eReal : Additive (BrauerGroup v.1.Completion) ≃+ ZMod 2 :=
        realZRing v.1.Completion
          (InfinitePlace.Completion.ringEquivRealOfIsReal hvreal)
      calc
        Nat.card (relativeBrauerGroup v.1.Completion w.1.1.Completion) =
            Nat.card (BrauerGroup v.1.Completion) :=
          Nat.card_congr eRelative.toEquiv
        _ = Nat.card (ZMod 2) := Nat.card_congr eReal.toEquiv
        _ = 2 := Nat.card_zmod 2
        _ = Module.finrank v.1.Completion w.1.1.Completion := hfinrank.symm
    · have hwcomplex' : w.1.IsComplex :=
        InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 hvcomplex
      have hunramified : w.1.IsUnramified K :=
        InfinitePlace.isUnramified_iff.mpr (Or.inr (by
          simpa [InfinitePlace.LiesOver.comap_eq w.1 v] using hvcomplex))
      have hcardD : Nat.card
          (absoluteValueDecomposition v.1 w.1.1) = 1 := by
        rw [hstabilizer, InfinitePlace.card_stabilizer, if_pos hunramified]
      have hfinrank : Module.finrank v.1.Completion w.1.1.Completion = 1 :=
        hdegree.trans hcardD
      letI : IsAlgClosed v.1.Completion :=
        alg_closed_ring
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvcomplex).symm
      letI : Subsingleton (BrauerGroup v.1.Completion) :=
        brauer_subsingleton_closed v.1.Completion
      letI : Subsingleton
          (relativeBrauerGroup v.1.Completion w.1.1.Completion) := inferInstance
      exact Nat.card_unique.trans hfinrank.symm

set_option synthInstance.maxHeartbeats 500000 in
-- Tate periodicity and the infinite completion comparison are deeply dependent.
set_option maxHeartbeats 6000000 in
/-- The infinite-place part of the local Tate-zero cardinality bridge. -/
theorem infiniteTateCardinality
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (v : InfinitePlace K)
    (w : CompletionPlacesAbove (L := L) v.1) :
    letI : Fintype (CompletionPlaceStabilizer v.1 w) := Fintype.ofFinite _
    Finite (tateZero
        (placeUnitsRepresentation v.1 w)) ∧
      Nat.card (tateZero
        (placeUnitsRepresentation v.1 w)) =
        Nat.card (CompletionPlaceStabilizer v.1 w) := by
  let w' : InfinitePlacesAbove (K := K) (L := L) v :=
    normalizedPlacesAbove
      (K := K) (L := L) v w
  let H := CompletionPlaceStabilizer v.1 w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  let hwv := infinite_lies_comap v w'.1 w'.2
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact (AbsoluteValue.LiesOver w.1 v.1) := ⟨w.2⟩
  letI : Algebra v.1.Completion w.1.Completion :=
    (completionLies v.1 w.1 w.2).toAlgebra
  letI : FiniteDimensional v.1.Completion w.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w'
  letI : IsGalois v.1.Completion w.1.Completion :=
    infiniteHasseGalois K L v w'
  let A := placeUnitsRepresentation v.1 w
  let eTate : tateZero A ≃+
      H2 (uliftIntegralRepresentation A) :=
    (tateIntLift A).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation A) g hg).toAddEquiv
  let ePresentation : H2 (uliftIntegralRepresentation A) ≃+
      H2 (hasseUnitsRepresentation v.1 w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 2).mapIso
      (uliftIsoHasse
        (K := K) (L := L) v.1 w)).toLinearEquiv.toAddEquiv
  let eLocal : H2 (hasseGlobalRepresentation
      v.1.Completion w.1.Completion) ≃+
      H2 (hasseUnitsRepresentation v.1 w) := by
    simpa [w', hwv] using
      (infiniteHStabilizer
        (K := K) (L := L) v w')
  let eBrauer := relativeBrauer2
    v.1.Completion w.1.Completion
  let e : tateZero A ≃+
      Additive (relativeBrauerGroup v.1.Completion w.1.Completion) :=
    eTate.trans (ePresentation.trans (eLocal.symm.trans eBrauer.symm))
  have hcardRelative : Nat.card
      (relativeBrauerGroup v.1.Completion w.1.Completion) =
        Module.finrank v.1.Completion w.1.Completion := by
    simpa [w'] using
      infinite_relative_finrank
        (K := K) (L := L) v w'
  letI : Finite (relativeBrauerGroup v.1.Completion w.1.Completion) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcardRelative]
      exact Nat.ne_of_gt (Module.finrank_pos (R := v.1.Completion)
        (M := w.1.Completion))
  let hfinite : Finite (tateZero A) :=
    Finite.of_equiv (Additive
      (relativeBrauerGroup v.1.Completion w.1.Completion)) e.symm.toEquiv
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card (tateZero A) =
        Nat.card (relativeBrauerGroup v.1.Completion w.1.Completion) :=
      Nat.card_congr e.toEquiv
    _ = Module.finrank v.1.Completion w.1.Completion := hcardRelative
    _ = Nat.card (absoluteValueDecomposition v.1 w.1) := by
      simpa [w'] using
        infiniteDegreeCompatibility K L v w'
    _ = Nat.card H := by
      change Nat.card (absoluteValueDecomposition v.1 w.1) =
        Nat.card (CompletionPlaceStabilizer v.1 w)
      rw [hasse_stabilizer_decomposition v.1 w]

end

end Towers.CField.BLoc
