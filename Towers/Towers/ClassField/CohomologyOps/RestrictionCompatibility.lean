import Towers.ClassField.CohomologyOps.BarRestriction
import Towers.ClassField.CohomologyOps.ProjectiveComparison
import Towers.ClassField.CohomologyOps.AllDegrees

/-!
# Compatibility of restriction with the Shapiro model

This file compares the inhomogeneous-cochain definition of restriction with
the map obtained by precomposing bar cochains with the explicit subgroup bar
map from `BarRestriction`.
-/

namespace Towers.CField.COps

open CategoryTheory Rep

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

/-- Restrict a `G`-equivariant bar cochain to an `H`-equivariant cochain on
the restricted ambient bar resolution. -/
def barCochainsRestriction (A : Rep k G) (H : Subgroup G) :
    (barComplex k G).linearYonedaObj k A ⟶
      ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)).complex.linearYonedaObj k (res H.subtype A) where
  f n := ModuleCat.ofHom
    { toFun := fun f => (resFunctor H.subtype).map f
      map_add' := fun f g => by
        apply Rep.hom_ext
        ext x
        rfl
      map_smul' := fun r f => by
        apply Rep.hom_ext
        ext x
        rfl }
  comm' i j hij := by
    subst j
    ext f
    rfl

/-- Contravariant precomposition on cochains internal to `Rep k H`. -/
def barPrecompositionCochains (A : Rep k G) (H : Subgroup G)
    (φ : barComplex k H ⟶
      ((resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (barComplex k G)) :
    ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)).complex.linearYonedaObj k (res H.subtype A) ⟶
      (barComplex k H).linearYonedaObj k (res H.subtype A) where
  f n := ModuleCat.ofHom
    { toFun := fun f => φ.f n ≫ f
      map_add' := fun f g => by
        apply Rep.hom_ext
        ext x
        rfl
      map_smul' := fun r f => by
        apply Rep.hom_ext
        ext x
        rfl }
  comm' i j hij := by
    subst j
    ext f
    simpa only [Category.assoc] using congrArg (fun q => q ≫ f)
      (φ.comm (i + 1) i).symm

/-- A map from the subgroup bar resolution to the restricted ambient bar
resolution acts contravariantly on linear-Yoneda cochains. -/
def precompositionCochains (A : Rep k G) (H : Subgroup G)
    (φ : barComplex k H ⟶
      ((resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (barComplex k G)) :
    (barComplex k G).linearYonedaObj k A ⟶
      (barComplex k H).linearYonedaObj k (res H.subtype A) where
  f n := ModuleCat.ofHom
    { toFun := fun f =>
        φ.f n ≫ (resFunctor H.subtype).map f
      map_add' := fun f g => by
        apply Rep.hom_ext
        ext x
        rfl
      map_smul' := fun r f => by
        apply Rep.hom_ext
        ext x
        rfl }
  comm' i j hij := by
    subst j
    ext f
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun q => q ≫ (resFunctor H.subtype).map f)
      (φ.comm (i + 1) i).symm

/-- Precomposition by the explicit bar-resolution restriction map, with the
coefficient morphism obtained by restricting a `G`-map to `H`. -/
abbrev barRestrictionCochains (A : Rep k G) (H : Subgroup G) :=
  precompositionCochains A H (barRestrictionMap (k := k) H)

/-- Restricting coefficients and then precomposing is the combined explicit
bar restriction map. -/
theorem bar_cochains_precomposition
    (A : Rep k G) (H : Subgroup G) :
    barCochainsRestriction A H ≫
      barPrecompositionCochains A H
        (barRestrictionMap (k := k) H) =
      barRestrictionCochains A H := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext f
  rfl

lemma inhomogeneous_cochains_single
    (A : Rep k G) (n : ℕ) (f : (Fin n → G) → A) (x : Fin n → G) :
    (((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f).hom
        (Finsupp.single x (Finsupp.single 1 1)) = f x := by
  change Representation.freeLift A.ρ f
      (Finsupp.single x (Finsupp.single 1 1)) = f x
  simp

lemma coind_bar_res
    (A : Rep k G) (H : Subgroup G) (n : ℕ)
    (f : (groupCohomology.inhomogeneousCochains A).X n) :
    ((groupCohomology.inhomogeneousCochainsIso
        (coind H.subtype (res H.subtype A))).hom.f n)
        ((groupCohomology.cochainsMap (MonoidHom.id G)
          ((resCoindAdjunction k H.subtype).unit.app A)).f n f) =
      (resCoindHomEquiv H.subtype (Rep.free k G (Fin n → G))
        (res H.subtype A))
        ((resFunctor H.subtype).map
          (((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f)) := by
  apply Rep.free_ext
  intro x
  ext g
  let q : Rep.free k G (Fin n → G) ⟶ A :=
    ((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f
  calc
    _ = ((((groupCohomology.cochainsMap (MonoidHom.id G)
          ((resCoindAdjunction k H.subtype).unit.app A)).f n) f) x :
        coind H.subtype (res H.subtype A)).1 g := congrArg
      (fun z : coind H.subtype (res H.subtype A) => z.1 g)
      (inhomogeneous_cochains_single
        (coind H.subtype (res H.subtype A)) n _ x)
    _ = A.ρ g (f x) := res_coind_unit A H (f x) g
    _ = q.hom ((Rep.free k G (Fin n → G)).ρ g
        (Finsupp.single x (Finsupp.single 1 1))) := by
      rw [hom_comm_apply]
      exact congrArg (A.ρ g)
        (inhomogeneous_cochains_single A n f x).symm
    _ = _ := by
      symm
      exact resCoindToHom_hom_apply_coe
        H.subtype (Rep.free k G (Fin n → G)) (res H.subtype A)
        ((resFunctor H.subtype).map q)
        (Finsupp.single x (Finsupp.single 1 1)) g

/-- The restriction/coinduction unit followed by the inverse Shapiro
adjunction on bar cochains is simply restriction of an equivariant cochain
from `G` to `H`. -/
theorem coind_shapiro_adjunction
    (A : Rep k G) (H : Subgroup G) :
    groupCohomology.cochainsMap (MonoidHom.id G)
        ((resCoindAdjunction k H.subtype).unit.app A) ≫
      (groupCohomology.inhomogeneousCochainsIso
        (coind H.subtype (res H.subtype A))).hom ≫
      (groupCohomology.linearYonedaObjResProjectiveResolutionIso
        (barResolution k G) (res H.subtype A)).inv =
    (groupCohomology.inhomogeneousCochainsIso A).hom ≫
      barCochainsRestriction A H := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext f
  change (resCoindHomEquiv H.subtype (Rep.free k G (Fin n → G))
      (res H.subtype A)).symm _ = _
  let e := resCoindHomEquiv H.subtype (Rep.free k G (Fin n → G))
    (res H.subtype A)
  calc
    e.symm _ = e.symm (e ((resFunctor H.subtype).map
        (((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f))) :=
      congrArg e.symm (coind_bar_res A H n f)
    _ = (resFunctor H.subtype).map
        (((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f) :=
      e.symm_apply_apply _
    _ = _ := rfl

lemma bar_restriction_f (H : Subgroup G) (n : ℕ) (x : Fin n → H) :
    ((barRestrictionMap (k := k) H).f n).hom
        (Finsupp.single x (Finsupp.single 1 1)) =
      Finsupp.single (fun i => (x i : G)) (Finsupp.single 1 1) := by
  change Representation.freeLift
      (Rep.res H.subtype (Rep.free k G (Fin n → G))).ρ
      (fun x : Fin n → H =>
        Finsupp.single (fun i => (x i : G)) (Finsupp.single 1 1))
      (Finsupp.single x (Finsupp.single 1 1)) = _
  simp

/-- Ordinary inhomogeneous restriction is precomposition with the explicit
map from the subgroup bar resolution to the restricted ambient bar
resolution. -/
theorem cochains_inhomogeneous_iso
    (A : Rep k G) (H : Subgroup G) :
    groupCohomology.cochainsMap H.subtype (𝟙 _) ≫
        (groupCohomology.inhomogeneousCochainsIso (res H.subtype A)).hom =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        barRestrictionCochains A H := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext f
  apply Rep.free_ext
  intro x
  change (((groupCohomology.inhomogeneousCochainsIso
      (res H.subtype A)).hom.f n)
      (fun y => f (fun i => (y i : G)))).hom
        (Finsupp.single x (Finsupp.single 1 1)) =
    (((groupCohomology.inhomogeneousCochainsIso A).hom.f n) f).hom
      (((barRestrictionMap (k := k) H).f n).hom
        (Finsupp.single x (Finsupp.single 1 1)))
  rw [inhomogeneous_cochains_single, bar_restriction_f,
    inhomogeneous_cochains_single]

/-- The corresponding equality on cohomology: after transport by the two
inhomogeneous/bar comparison isomorphisms, ordinary restriction is the map
on homology induced by explicit bar precomposition. -/
theorem homology_bar_iso
    (A : Rep k G) (H : Subgroup G) (n : ℕ) :
    HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap H.subtype (𝟙 _)) n ≫
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso
          (res H.subtype A)).hom n =
    HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      HomologicalComplex.homologyMap (barRestrictionCochains A H) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    cochains_inhomogeneous_iso,
    HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The `isoExt` comparison between the restricted ambient bar resolution and
the subgroup bar resolution is the homology map induced by explicit bar
precomposition. -/
theorem ext_bar_homology
    (A : Rep k G) (H : Subgroup G) (n : ℕ) :
    (((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)).isoExt n (res H.subtype A)).inv ≫
      ((barResolution k H).isoExt n (res H.subtype A)).hom =
    HomologicalComplex.homologyMap
      (barPrecompositionCochains A H
        (barRestrictionMap (k := k) H)) n := by
  rw [iso_ext_homology k n
    (barResolution k H)
    ((resFunctor H.subtype).mapProjectiveResolution (barResolution k G))
    (barRestrictionMap (k := k) H)
    (bar_restriction_pi (k := k) H)]
  change HomologicalComplex.homologyMap
      (linearYonedaPrecomposition k (res H.subtype A)
        (barRestrictionMap (k := k) H)) n = _
  congr 1

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
lemma cohomology_bar_resolution
    (A : Rep k G) (n : ℕ) :
    (groupCohomologyIso A n (barResolution k G)).hom =
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso A).hom n := by
  simp [groupCohomologyIso, groupCohomologyIsoExt,
    Rep.barResolution.extIso]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma iso_bar_resolution
    (A : Rep k G) (H : Subgroup G) (n : ℕ) :
    (groupCohomologyIso (res H.subtype A) n
      ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G))).inv ≫
      (groupCohomologyIso (res H.subtype A) n
        (barResolution k H)).hom =
    HomologicalComplex.homologyMap
      (barPrecompositionCochains A H
        (barRestrictionMap (k := k) H)) n := by
  simp only [groupCohomologyIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact ext_bar_homology A H n

set_option backward.isDefEq.respectTransparency false in
/-- **Proposition II.1.30, comparison step.** The restriction map defined on
inhomogeneous cochains agrees in every degree with restriction through the
coinduced module and Shapiro's isomorphism. -/
theorem restriction_shapiro
    (A : Rep k G) (H : Subgroup G) (n : ℕ) :
    restriction A H n = shapiroRestriction A H n := by
  rw [← cancel_mono
    (groupCohomologyIso (res H.subtype A) n (barResolution k H)).hom]
  simp only [restriction, shapiroRestriction, groupCohomology.map,
    groupCohomology.coindIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [iso_bar_resolution]
  rw [cohomology_bar_resolution]
  rw [homology_bar_iso]
  simp only [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
      ((groupCohomology.inhomogeneousCochainsIso A).hom ≫
        barRestrictionCochains A H) n =
    HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap (MonoidHom.id G)
          ((resCoindAdjunction k H.subtype).unit.app A)) n ≫
      HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso
          (coind H.subtype (res H.subtype A))).hom ≫
          (groupCohomology.linearYonedaObjResProjectiveResolutionIso
            (barResolution k G) (res H.subtype A)).inv) n ≫
      HomologicalComplex.homologyMap
        (barPrecompositionCochains A H
          (barRestrictionMap (k := k) H)) n
  slice_rhs 1 2 =>
    rw [← HomologicalComplex.homologyMap_comp,
      coind_shapiro_adjunction]
  rw [← HomologicalComplex.homologyMap_comp,
    Category.assoc, bar_cochains_precomposition]

/-- **Proposition II.1.30.** Restriction followed by corestriction is
multiplication by the subgroup index in every cohomological degree. -/
theorem restriction_corestriction_degrees
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    restriction A H n ≫ corestriction A H n =
      H.index • 𝟙 (groupCohomology A n) := by
  rw [restriction_shapiro,
    shapiro_restriction_corestriction]

end

end Towers.CField.COps
