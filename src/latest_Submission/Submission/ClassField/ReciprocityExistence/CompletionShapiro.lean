import Submission.ClassField.ReciprocityExistence.CupRestriction
import Submission.ClassField.ReciprocityExistence.CoeffNaturality
import Submission.ClassField.ReciprocityExistence.H2Restriction
import Submission.ClassField.ReciprocityExistence.CompletionFormula
import Submission.ClassField.HasseNorm.HCompletionProduct

/-!
# Shapiro on a multiplicative completion-product class

The explicit completion-product Shapiro equivalence is restriction to the
chosen place stabilizer followed by evaluation at that place.  This file
states the fact in the universe-resized multiplicative `H²` model and then
specializes it to Milne's invariant-character cup.
-/

namespace Submission.CField.RExist

open CategoryTheory Rep Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.COps
open Submission.CField.CProduca
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

/-- Adjoint transposition into a coinduced representation is natural under
precomposition in the source representation. -/
private theorem res_coind_precomp
    {k G : Type u} [CommRing k] [Group G]
    (H : Subgroup G)
    {A A' : Rep k G} {B : Rep k H}
    (q : A' ⟶ A) (f : Rep.res H.subtype A ⟶ B) :
    q ≫ Rep.resCoindToHom H.subtype A B f =
      Rep.resCoindToHom H.subtype A' B
        ((Rep.resFunctor H.subtype).map q ≫ f) := by
  exact ((Rep.resCoindAdjunction k H.subtype).homEquiv_naturality_left q f).symm

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteCupCompletionPlacesPretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

/-- Restrict the prime-adic finite orbit to the chosen place stabilizer,
expressed as the adjoint transpose of the orbit-to-coinduced map.  A later
application theorem identifies its underlying function with evaluation at
the chosen completion. -/
noncomputable def chosenRepresentationHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Rep.res (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
        (resizedAboveRepresentation
          (K := K) (L := L) P) ⟶
      uliftPlaceRepresentation
        (K := K) (L := L) (FinitePlace.mk P).val w :=
  (Rep.resCoindHomEquiv
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
      (resizedAboveRepresentation
        (K := K) (L := L) P)
      (uliftPlaceRepresentation
        (K := K) (L := L) (FinitePlace.mk P).val w)).symm
    ((resizedIsoOrbit
        (K := K) (L := L) P).inv ≫
      (uliftInducedIso
        (K := K) (L := L) (FinitePlace.mk P).val w).hom)

set_option synthInstance.maxHeartbeats 300000 in
-- Both sides traverse the dependent orbit/completion-product equivalence.
/-- The adjointly defined finite-orbit evaluation is literally inverse orbit
reindexing followed by evaluation at the selected completion. -/
theorem resized_representation_hom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    chosenRepresentationHom
        (K := K) (L := L) P w =
      (Rep.resFunctor
        (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype).map
          (resizedIsoOrbit
            (K := K) (L := L) P).inv ≫
        uliftIntegralHom
          (completionUnitsEvaluation
            (K := K) (L := L) (FinitePlace.mk P).val w) := by
  let H := CompletionPlaceStabilizer (FinitePlace.mk P).val w
  let orbit := resizedAboveRepresentation
    (K := K) (L := L) P
  let product := uliftUnitsRepresentation
    (K := K) (L := L) (FinitePlace.mk P).val
  let chosen := uliftPlaceRepresentation
    (K := K) (L := L) (FinitePlace.mk P).val w
  let q : orbit ⟶ product :=
    (resizedIsoOrbit
      (K := K) (L := L) P).inv
  let f : Rep.res H.subtype product ⟶ chosen :=
    uliftIntegralHom
      (completionUnitsEvaluation
        (K := K) (L := L) (FinitePlace.mk P).val w)
  apply (Rep.resCoindHomEquiv H.subtype orbit chosen).injective
  change
    (Rep.resCoindHomEquiv H.subtype orbit chosen)
        ((Rep.resCoindHomEquiv H.subtype orbit chosen).symm
          (q ≫ (uliftInducedIso
            (K := K) (L := L) (FinitePlace.mk P).val w).hom)) =
      Rep.resCoindToHom H.subtype orbit chosen
        ((Rep.resFunctor H.subtype).map q ≫ f)
  rw [(Rep.resCoindHomEquiv H.subtype orbit chosen).apply_symm_apply]
  calc
    q ≫ (uliftInducedIso
          (K := K) (L := L) (FinitePlace.mk P).val w).hom =
        q ≫ Rep.resCoindToHom H.subtype product chosen f := by
      exact congrArg (fun z => q ≫ z)
        (ulift_induced_iso
          (K := K) (L := L) (FinitePlace.mk P).val w)
    _ = _ := res_coind_precomp H q f

set_option maxHeartbeats 1000000 in
-- The orbit equivalence and the coinduced model unfold dependent completion fields.
set_option synthInstance.maxHeartbeats 300000 in
-- The orbit/completion-product isomorphism and coinduced model share a
-- dependent family of completion fields.
/-- After the explicit orbit reindexing, the map into the coinduced module
is the adjoint of the chosen-completion evaluation map. -/
theorem resizedOrbitCoinduced
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (resizedIsoOrbit
        (K := K) (L := L) P).inv ≫
      (uliftInducedIso
        (K := K) (L := L) (FinitePlace.mk P).val w).hom =
    Rep.resCoindToHom
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
      (resizedAboveRepresentation
        (K := K) (L := L) P)
      (uliftPlaceRepresentation
        (K := K) (L := L) (FinitePlace.mk P).val w)
      (chosenRepresentationHom
        (K := K) (L := L) P w) := by
  let H := CompletionPlaceStabilizer (FinitePlace.mk P).val w
  let orbit := resizedAboveRepresentation
    (K := K) (L := L) P
  let chosen := uliftPlaceRepresentation
    (K := K) (L := L) (FinitePlace.mk P).val w
  let q : orbit ⟶ Rep.coind H.subtype chosen :=
    (resizedIsoOrbit
        (K := K) (L := L) P).inv ≫
      (uliftInducedIso
        (K := K) (L := L) (FinitePlace.mk P).val w).hom
  change q = (Rep.resCoindHomEquiv H.subtype orbit chosen)
    ((Rep.resCoindHomEquiv H.subtype orbit chosen).symm q)
  exact (Rep.resCoindHomEquiv H.subtype orbit chosen).apply_symm_apply q |>.symm

set_option maxHeartbeats 1000000 in
-- Comparing the two cohomology maps requires normalizing the dependent orbit model.
set_option synthInstance.maxHeartbeats 300000 in
-- This theorem compares maps before applying them, avoiding expensive
-- equality checking for a specialized dependent cohomology class.
/-- The finite orbit reindexing followed by completion-product Shapiro is
the single cohomology map induced by chosen-completion evaluation. -/
theorem resizedOrbitShapiro
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : OrbitH2 K L P) :
    (uliftShapiroIso
        (K := K) (L := L) (FinitePlace.mk P).val w 2).hom
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIsoOrbit
          (K := K) (L := L) P).inv 2 x) =
    groupCohomology.map
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
      (chosenRepresentationHom
        (K := K) (L := L) P w) 2 x := by
  let H := CompletionPlaceStabilizer (FinitePlace.mk P).val w
  let orbit := resizedAboveRepresentation
    (K := K) (L := L) P
  let chosen := uliftPlaceRepresentation
    (K := K) (L := L) (FinitePlace.mk P).val w
  let induced := uliftInducedIso
    (K := K) (L := L) (FinitePlace.mk P).val w
  let evaluation := chosenRepresentationHom
    (K := K) (L := L) P w
  have hinduced := resizedOrbitCoinduced
    (K := K) (L := L) P w
  have hshapiro := res_coind_shapiro
    H evaluation 2
  have hpath :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIsoOrbit
            (K := K) (L := L) P).inv 2 ≫
        (groupCohomology.map (MonoidHom.id Gal(L/K)) induced.hom 2 ≫
          (groupCohomology.coindIso chosen 2).hom) =
      groupCohomology.map H.subtype evaluation 2 := by
    rw [← Category.assoc]
    rw [← groupCohomology.map_id_comp]
    dsimp only [induced]
    have hmap := congrArg
      (fun q : orbit ⟶ milneInducedModule H chosen =>
        groupCohomology.map
          (A := orbit) (B := milneInducedModule H chosen)
          (MonoidHom.id Gal(L/K)) q 2)
      hinduced
    calc
      _ = groupCohomology.map (MonoidHom.id Gal(L/K))
            (Rep.resCoindToHom H.subtype orbit chosen evaluation) 2 ≫
          (groupCohomology.coindIso chosen 2).hom := by
        exact congrArg
          (fun q => q ≫ (groupCohomology.coindIso chosen 2).hom) hmap
      _ = _ := by simpa only [H, orbit, chosen, evaluation] using hshapiro
  exact ConcreteCategory.congr_hom hpath x

end

end Submission.CField.RExist
