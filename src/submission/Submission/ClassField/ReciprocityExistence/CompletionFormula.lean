import Submission.ClassField.HasseNorm.ULiftShapiro
import Submission.ClassField.CohomologyOps.ShapiroCounit

/-!
# The evaluation formula for completion-product Shapiro

The completion-product representation is identified with a coinduced
representation by evaluation at a chosen completion.  Consequently its
Shapiro map is ordinary subgroup restriction followed by that evaluation.
-/

namespace Submission.CField.RExist

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.COps
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

/-- A morphism into a coinduced representation followed by Shapiro is the
single cohomology map obtained from subgroup restriction and the adjoint
coefficient morphism. -/
theorem res_coind_shapiro
    {k G : Type u} [CommRing k] [Group G]
    (H : Subgroup G) [H.FiniteIndex]
    {A : Rep k G} {B : Rep k H} (f : Rep.res H.subtype A ⟶ B)
    (n : ℕ) :
    groupCohomology.map (MonoidHom.id G)
        (Rep.resCoindToHom H.subtype A B f) n ≫
      (groupCohomology.coindIso B n).hom =
    groupCohomology.map H.subtype f n := by
  have hadj :
      Rep.resCoindToHom H.subtype A B f =
        (Rep.resCoindAdjunction k H.subtype).unit.app A ≫
          (Rep.coindFunctor k H.subtype).map f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext g
    rfl
  rw [hadj]
  let unit := (Rep.resCoindAdjunction k H.subtype).unit.app A
  let coindf := (Rep.coindFunctor k H.subtype).map f
  have hmap := groupCohomology.map_id_comp unit coindf n
  have hcoind :=
    Submission.CField.Shifting.coindIso_naturality f n
  calc
    groupCohomology.map (MonoidHom.id G) (unit ≫ coindf) n ≫
          (groupCohomology.coindIso B n).hom =
        (groupCohomology.map (MonoidHom.id G) unit n ≫
          groupCohomology.map (MonoidHom.id G) coindf n) ≫
          (groupCohomology.coindIso B n).hom :=
      congrArg (fun q => q ≫ (groupCohomology.coindIso B n).hom) hmap
    _ = groupCohomology.map (MonoidHom.id G) unit n ≫
        (groupCohomology.map (MonoidHom.id G) coindf n ≫
          (groupCohomology.coindIso B n).hom) := Category.assoc _ _ _
    _ = groupCohomology.map (MonoidHom.id G) unit n ≫
        ((groupCohomology.coindIso (Rep.res H.subtype A) n).hom ≫
          groupCohomology.map (MonoidHom.id H) f n) := by
      simpa [coindf] using congrArg
        (fun q => groupCohomology.map (MonoidHom.id G) unit n ≫ q)
        hcoind.symm
    _ = shapiroRestriction A H n ≫
        groupCohomology.map (MonoidHom.id H) f n := by
      rfl
    _ = restriction A H n ≫
        groupCohomology.map (MonoidHom.id H) f n := by
      rw [restriction_shapiro]
    _ = groupCohomology.map H.subtype f n := by
      rw [restriction, ← groupCohomology.map_comp]
      rfl

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Rescaling the explicit completion-product/coinduced isomorphism does
not change its description as the adjoint of evaluation. -/
theorem ulift_induced_iso
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    (uliftInducedIso
        (K := K) (L := L) v w).hom =
      Rep.resCoindToHom
        (CompletionPlaceStabilizer v w).subtype
        (uliftUnitsRepresentation
          (K := K) (L := L) v)
        (uliftPlaceRepresentation
          (K := K) (L := L) v w)
        (uliftIntegralHom
          (completionUnitsEvaluation
            (K := K) (L := L) v w)) := by
  rfl

set_option maxHeartbeats 2000000 in
-- The resized coinduced representation and its finite-index instance elaborate together.
/-- The degree-two completion-product Shapiro equivalence is subgroup
restriction followed by evaluation at the chosen completion. -/
theorem ulift_completion_units
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [FiniteDimensional K L] [IsGalois K L]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (x : H2 (uliftUnitsRepresentation
      (K := K) (L := L) v)) :
    uliftCompletionUnits
        (K := K) (L := L) v w x =
      groupCohomology.map
        (CompletionPlaceStabilizer v w).subtype
        (uliftIntegralHom
          (completionUnitsEvaluation
            (K := K) (L := L) v w)) 2 x := by
  let H := CompletionPlaceStabilizer v w
  let A := uliftUnitsRepresentation
    (K := K) (L := L) v
  let B := uliftPlaceRepresentation
    (K := K) (L := L) v w
  let f : Rep.res H.subtype A ⟶ B :=
    uliftIntegralHom
      (completionUnitsEvaluation (K := K) (L := L) v w)
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  change ((groupCohomology.map (MonoidHom.id Gal(L/K))
      (uliftInducedIso
        (K := K) (L := L) v w).hom 2) ≫
      (groupCohomology.coindIso
        (uliftPlaceRepresentation
          (K := K) (L := L) v w) 2).hom) x = _
  rw [ulift_induced_iso]
  have h := res_coind_shapiro
    (k := ULift.{u} ℤ) (G := Gal(L/K)) H f 2
  exact ConcreteCategory.congr_hom h x

section FinitePlace

variable [NumberField K] [NumberField L]

set_option maxHeartbeats 2000000 in
-- The finite-place transitivity instance and resized evaluation map elaborate together.
/-- At a finite number-field place, Shapiro is restriction to the selected
decomposition group followed by evaluation at the selected completion. -/
theorem ulift_units_h
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    [FiniteDimensional K L] [IsGalois K L]
    (x : H2 (uliftUnitsRepresentation
      (K := K) (L := L) (FinitePlace.mk P).val)) :
    uliftUnitsH
        (K := K) (L := L) P w x =
      groupCohomology.map
        (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
        (uliftIntegralHom
          (completionUnitsEvaluation
            (K := K) (L := L) (FinitePlace.mk P).val w)) 2 x := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  exact ulift_completion_units
    (K := K) (L := L) (FinitePlace.mk P).val w x

end FinitePlace

end

end Submission.CField.RExist
