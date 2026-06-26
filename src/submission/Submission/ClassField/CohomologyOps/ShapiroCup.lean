import Submission.ClassField.CohomologyOps.Inflation
import Submission.ClassField.CohomologyOps.ShapiroCounit

namespace Submission.CField.COps.CPFuncto

open CategoryTheory Rep
open Submission.CField.COps.CPBuild
open Submission.CField.COps
open scoped MonoidalCategory TensorProduct

variable {G : Type} [Group G]

noncomputable section

set_option maxHeartbeats 2000000 in
-- Tensoring across restriction requires an expensive definitional equality.
/-- The tensor of the coinduction counit with the identity of the second
coefficient module. -/
def coindTensorCounit (H : Subgroup G) (A : Rep ℤ H) (N : Rep ℤ G) :
    (Rep.res H.subtype (coind H.subtype A) ⊗
      Rep.res H.subtype N : Rep ℤ H) ⟶
      (A ⊗ Rep.res H.subtype N : Rep ℤ H) := by
  let e : Rep.res H.subtype (coind H.subtype A) ⟶ A :=
    (resCoindAdjunction ℤ H.subtype).counit.app A
  exact e ⊗ₘ 𝟙 _

set_option maxHeartbeats 2000000 in
-- The adjunction elaborator unfolds the restricted tensor representation.
/-- The adjoint transpose of `coindTensorCounit`. -/
def coindTensorHom (H : Subgroup G) (A : Rep ℤ H) (N : Rep ℤ G) :
    (coind H.subtype A ⊗ N : Rep ℤ G) ⟶
      coind H.subtype (A ⊗ Rep.res H.subtype N : Rep ℤ H) :=
  Rep.resCoindToHom H.subtype _ _ (coindTensorCounit H A N)

set_option maxHeartbeats 2000000 in
-- The counit identity compares two definitionally equal tensor objects.
theorem res_coind_counit
    (H : Subgroup G) (A : Rep ℤ H) (N : Rep ℤ G) :
    (Rep.resFunctor H.subtype).map (coindTensorHom H A N) ≫
        (resCoindAdjunction ℤ H.subtype).counit.app
          (A ⊗ Rep.res H.subtype N : Rep ℤ H) =
      coindTensorCounit H A N := by
  change (Rep.resCoindHomEquiv H.subtype
      (coind H.subtype A ⊗ N : Rep ℤ G)
      (A ⊗ Rep.res H.subtype N : Rep ℤ H)).symm
        (Rep.resCoindToHom H.subtype _ _ (coindTensorCounit H A N)) = _
  exact (Rep.resCoindHomEquiv H.subtype
    (coind H.subtype A ⊗ N : Rep ℤ G)
    (A ⊗ Rep.res H.subtype N : Rep ℤ H)).symm_apply_apply _

set_option maxHeartbeats 2000000 in
-- Shapiro and tensor functoriality require several large dependent transports.
/-- Shapiro's isomorphism carries the cup product through the canonical
coinduction--tensor morphism to the cup product with the restricted second
class. -/
theorem coind_iso_tensor
    (H : Subgroup G) (A : Rep ℤ H) (N : Rep ℤ G) (r s : ℕ)
    (u : groupCohomology (coind H.subtype A) r)
    (y : groupCohomology N s) :
    (groupCohomology.coindIso
        (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s)).hom
        (groupCohomology.map (MonoidHom.id G)
          (coindTensorHom H A N) (r + s)
          (cupCohomology (coind H.subtype A) N r s u y)) =
      cupCohomology A (Rep.res H.subtype N) r s
        ((groupCohomology.coindIso A r).hom u)
        (restriction N H s y) := by
  let θ := coindTensorHom H A N
  let eT := (resCoindAdjunction ℤ H.subtype).counit.app
    (A ⊗ Rep.res H.subtype N : Rep ℤ H)
  let e := (resCoindAdjunction ℤ H.subtype).counit.app A
  let z := cupCohomology (coind H.subtype A) N r s u y
  let c : Rep.res H.subtype (coind H.subtype A ⊗ N : Rep ℤ G) ⟶
      (A ⊗ Rep.res H.subtype N : Rep ℤ H) :=
    coindTensorCounit H A N
  have hmaps :
      groupCohomology.map (MonoidHom.id G) θ (r + s) ≫
          restriction (coind H.subtype
            (A ⊗ Rep.res H.subtype N : Rep ℤ H)) H (r + s) ≫
          groupCohomology.map (MonoidHom.id H) eT (r + s) =
        groupCohomology.map H.subtype c (r + s) := by
    have hfirst :
        groupCohomology.map (MonoidHom.id G) θ (r + s) ≫
            restriction (coind H.subtype
              (A ⊗ Rep.res H.subtype N : Rep ℤ H)) H (r + s) =
          groupCohomology.map H.subtype
            ((Rep.resFunctor H.subtype).map θ) (r + s) := by
      dsimp only [restriction]
      have hh := (groupCohomology.map_comp
        (A := (coind H.subtype A ⊗ N : Rep ℤ G))
        (B := coind H.subtype
          (A ⊗ Rep.res H.subtype N : Rep ℤ H))
        (C := Rep.res H.subtype (coind H.subtype
          (A ⊗ Rep.res H.subtype N : Rep ℤ H)))
        (MonoidHom.id G) H.subtype θ (𝟙 _) (r + s)).symm
      exact hh
    rw [← Category.assoc, hfirst]
    have hsecond :=
      (groupCohomology.map_comp H.subtype (MonoidHom.id H)
        ((Rep.resFunctor H.subtype).map θ) eT (r + s)).symm
    have hcoeff :
        ((Rep.resFunctor (MonoidHom.id H)).map
            ((Rep.resFunctor H.subtype).map θ)) ≫ eT = c := by
      simpa [resFunctor] using res_coind_counit H A N
    let d : Rep.res H.subtype
          (coind H.subtype A ⊗ N : Rep ℤ G) ⟶
        (A ⊗ Rep.res H.subtype N : Rep ℤ H) :=
      ((Rep.resFunctor (MonoidHom.id H)).map
        ((Rep.resFunctor H.subtype).map θ)) ≫ eT
    have hdc : d = c := hcoeff
    calc
      groupCohomology.map H.subtype ((Rep.resFunctor H.subtype).map θ) (r + s) ≫
          groupCohomology.map (MonoidHom.id H) eT (r + s) =
        groupCohomology.map (H.subtype.comp (MonoidHom.id H))
          (((Rep.resFunctor (MonoidHom.id H)).map
            ((Rep.resFunctor H.subtype).map θ)) ≫ eT) (r + s) := hsecond
      _ = groupCohomology.map H.subtype d (r + s) := by
        congr 1
      _ = groupCohomology.map H.subtype c (r + s) :=
        congrArg (fun q => groupCohomology.map H.subtype q (r + s)) hdc
  have hcup := cupCohomology_map H.subtype
    e (𝟙 (Rep.res H.subtype N)) r s u y
  have hu := congrArg (fun f => f u)
    (coind_iso_counit H A r)
  have hemap :
      groupCohomology.map H.subtype e r =
        restriction (coind H.subtype A) H r ≫
          groupCohomology.map (MonoidHom.id H) e r := by
    have hh := groupCohomology.map_comp H.subtype (MonoidHom.id H)
      (𝟙 (Rep.res H.subtype (coind H.subtype A))) e r
    exact hh
  have hu' : groupCohomology.map H.subtype e r u =
      (groupCohomology.coindIso A r).hom u := by
    rw [hemap]
    exact hu.symm
  have htarget := congrArg (fun f => f
      (groupCohomology.map (MonoidHom.id G) θ (r + s) z))
    (coind_iso_counit H
      (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s))
  have hmaps_z := congrArg (fun f => f z) hmaps
  simp only [ConcreteCategory.comp_apply] at hu htarget hmaps_z
  have hmaps_z' :
      groupCohomology.map (MonoidHom.id H) eT (r + s)
          (restriction (coind H.subtype
            (A ⊗ Rep.res H.subtype N : Rep ℤ H)) H (r + s)
            (groupCohomology.map (MonoidHom.id G) θ (r + s) z)) =
        groupCohomology.map H.subtype c (r + s) z := by
    exact hmaps_z
  let mid : groupCohomology
      (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s) :=
    groupCohomology.map (MonoidHom.id H) eT (r + s)
      (restriction (coind H.subtype
        (A ⊗ Rep.res H.subtype N : Rep ℤ H)) H (r + s)
        (groupCohomology.map (MonoidHom.id G) θ (r + s) z))
  have htarget' :
      (groupCohomology.coindIso
          (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s)).hom
          (groupCohomology.map (MonoidHom.id G) θ (r + s) z) = mid := by
    exact htarget
  have hmaps_z'' : mid = groupCohomology.map H.subtype c (r + s) z := by
    exact hmaps_z'
  let cupL : groupCohomology
      (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s) :=
    groupCohomology.map H.subtype
      (e ⊗ₘ 𝟙 (Rep.res H.subtype N)) (r + s) z
  have hcL : groupCohomology.map H.subtype c (r + s) z = cupL := by
    rfl
  have hcup' : cupL = cupCohomology A (Rep.res H.subtype N) r s
      (groupCohomology.map H.subtype e r u)
      (groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype N)) s y) := by
    simpa only [cupL] using hcup
  calc
    (groupCohomology.coindIso
        (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s)).hom
        (groupCohomology.map (MonoidHom.id G) θ (r + s) z) =
      mid := htarget'
    _ = groupCohomology.map H.subtype c (r + s) z := hmaps_z''
    _ = cupL := hcL
    _ = cupCohomology A (Rep.res H.subtype N) r s
        (groupCohomology.map H.subtype e r u)
        (groupCohomology.map H.subtype
          (𝟙 (Rep.res H.subtype N)) s y) := hcup'
    _ = cupCohomology A (Rep.res H.subtype N) r s
        ((groupCohomology.coindIso A r).hom u)
        (restriction N H s y) := by
      rw [hu']
      rfl

/-- Shapiro compatibility in the form used for corestriction: start with a
subgroup class, transport it by inverse Shapiro, cup upstairs, and transport
the result back by Shapiro. -/
theorem coind_iso_cup
    (H : Subgroup G) (A : Rep ℤ H) (N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology A r) (y : groupCohomology N s) :
    (groupCohomology.coindIso
        (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s)).hom
        (groupCohomology.map (MonoidHom.id G)
          (coindTensorHom H A N) (r + s)
          (cupCohomology (coind H.subtype A) N r s
            ((groupCohomology.coindIso A r).inv x) y)) =
      cupCohomology A (Rep.res H.subtype N) r s x
        (restriction N H s y) := by
  simpa using coind_iso_tensor H A N r s
    ((groupCohomology.coindIso A r).inv x) y

end

end Submission.CField.COps.CPFuncto
