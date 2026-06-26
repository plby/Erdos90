import Submission.ClassField.CohomologyOps.AllDegrees

/-!
# Naturality of Shapiro restriction in the coefficient module

The restriction map expressed through the restriction/coinduction unit and
Shapiro's isomorphism is natural in morphisms of coefficient modules.
-/

namespace Submission.CField.Shifting

open CategoryTheory Rep

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

private def yonedaObj
    {A B : Rep k G} (P : ChainComplex (Rep k G) ℕ) (f : A ⟶ B) :
    P.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f i := ModuleCat.ofHom (Linear.rightComp k _ f)
  comm' i j hij := by
    ext g
    change (P.d j i ≫ g) ≫ f = P.d j i ≫ (g ≫ f)
    rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem inhomogeneous_cochains_naturality
    {A B : Rep k G} (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) f ≫
        (groupCohomology.inhomogeneousCochainsIso B).hom =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        yonedaObj (barComplex k G) f := by
  ext i g
  apply Rep.free_ext
  intro x
  dsimp [groupCohomology.inhomogeneousCochainsIso,
    yonedaObj, groupCohomology.cochainsMap]
  change B.ρ.freeLift (fun y ↦ f.hom (g y))
      (Finsupp.single x (Finsupp.single 1 1)) =
    f.hom (A.ρ.freeLift g (Finsupp.single x (Finsupp.single 1 1)))
  simp

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
private theorem projective_ext_naturality
    {A B : Rep k G} (P : ProjectiveResolution (Rep.trivial k G k))
    (f : A ⟶ B) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op (Rep.trivial k G k))).map f ≫
        (P.isoExt n B).hom =
      (P.isoExt n A).hom ≫
        HomologicalComplex.homologyMap
          (yonedaObj P.complex f) n := by
  dsimp [ProjectiveResolution.isoExt, Ext, yonedaObj]
  rw [ProjectiveResolution.leftDerived_app_eq
    ((linearYoneda k (Rep k G)).map f).rightOp P n]
  simp
  rw [cancel_epi]
  rw [← cancel_epi (HomologicalComplex.homologyUnop _ n).hom]
  dsimp [HomologicalComplex.homologyUnop]
  have hq :
      (NatTrans.mapHomologicalComplex
          ((linearYoneda k (Rep k G)).map f).rightOp
          (ComplexShape.down ℕ)).app P.complex =
        (HomologicalComplex.opFunctor (ModuleCat k) (ComplexShape.up ℕ)).map
          (yonedaObj P.complex f).op := by
    ext i
    rfl
  rw [hq]
  have h := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality
      (yonedaObj P.complex f) n)
  simp only [unop_comp] at h
  simp at h
  change (HomologicalComplex.homologyOp
      (P.complex.linearYonedaObj k A) n).hom.unop ≫
        ((HomologicalComplex.homologyMap
          ((HomologicalComplex.opFunctor (ModuleCat k)
            (ComplexShape.up ℕ)).map
              (yonedaObj P.complex f).op) n).unop ≫
          (HomologicalComplex.homologyOp
            (P.complex.linearYonedaObj k B) n).inv.unop) =
      (HomologicalComplex.homologyOp
        (P.complex.linearYonedaObj k A) n).hom.unop ≫
        ((HomologicalComplex.homologyOp
          (P.complex.linearYonedaObj k A) n).inv.unop ≫
          HomologicalComplex.homologyMap
            (yonedaObj P.complex f) n)
  rw [← Category.assoc]
  rw [h]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_iso_naturality
    {A B : Rep k G} (P : ProjectiveResolution (Rep.trivial k G k))
    (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (groupCohomologyIso B n P).hom =
      (groupCohomologyIso A n P).hom ≫
        HomologicalComplex.homologyMap
          (yonedaObj P.complex f) n := by
  have hcochains := congrArg
    (fun q ↦ HomologicalComplex.homologyMap q n)
    (inhomogeneous_cochains_naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at hcochains
  have hcochains' :
      groupCohomology.map (MonoidHom.id G) f n ≫
          HomologicalComplex.homologyMap
            (HomotopyEquiv.ofIso
              (groupCohomology.inhomogeneousCochainsIso B)).hom n =
        HomologicalComplex.homologyMap
            (HomotopyEquiv.ofIso
              (groupCohomology.inhomogeneousCochainsIso A)).hom n ≫
          HomologicalComplex.homologyMap
            (yonedaObj (barComplex k G) f) n := by
    exact hcochains
  have hbar := projective_ext_naturality
    (barResolution k G) f n
  have hbar' :
      ((Ext k (Rep k G) n).obj
          (Opposite.op (Rep.trivial k G k))).map f ≫
          (barResolution.extIso k G B n).hom =
        (barResolution.extIso k G A n).hom ≫
          HomologicalComplex.homologyMap
            (yonedaObj (barResolution k G).complex f) n :=
    hbar
  have hbarInv :
      HomologicalComplex.homologyMap
          (yonedaObj (barResolution k G).complex f) n ≫
          (barResolution.extIso k G B n).inv =
        (barResolution.extIso k G A n).inv ≫
          ((Ext k (Rep k G) n).obj
            (Opposite.op (Rep.trivial k G k))).map f := by
    rw [← cancel_epi (barResolution.extIso k G A n).hom]
    slice_lhs 1 2 => rw [← hbar']
    simp
  have hP := projective_ext_naturality P f n
  have hbarInv' :
      HomologicalComplex.homologyMap
          (yonedaObj (barComplex k G) f) n ≫
          (barResolution.extIso k G B n).inv =
        (barResolution.extIso k G A n).inv ≫
          ((Ext k (Rep k G) n).obj
            (Opposite.op (Rep.trivial k G k))).map f :=
    hbarInv
  dsimp [groupCohomologyIso, groupCohomologyIsoExt]
  slice_lhs 1 2 => rw [hcochains']
  slice_lhs 2 3 => rw [hbarInv']
  slice_lhs 3 4 => rw [hP]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem yoneda_obj_projective
    {H : Subgroup G} {A B : Rep k H}
    (P : ProjectiveResolution (Rep.trivial k G k)) (f : A ⟶ B) :
    yonedaObj P.complex ((coindFunctor k H.subtype).map f) ≫
        (groupCohomology.linearYonedaObjResProjectiveResolutionIso P B).inv =
      (groupCohomology.linearYonedaObjResProjectiveResolutionIso P A).inv ≫
        yonedaObj
          ((resFunctor H.subtype).mapProjectiveResolution P).complex f := by
  ext i g
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Shapiro's coinduction isomorphism is natural in the coefficient
representation. -/
theorem coindIso_naturality
    {H : Subgroup G} {A B : Rep k H} (f : A ⟶ B) (n : ℕ) :
    (groupCohomology.coindIso A n).hom ≫
        groupCohomology.map (MonoidHom.id H) f n =
      groupCohomology.map (MonoidHom.id G)
          ((coindFunctor k H.subtype).map f) n ≫
        (groupCohomology.coindIso B n).hom := by
  let P := barResolution k G
  let Q := (resFunctor H.subtype).mapProjectiveResolution P
  have hcochains := congrArg
    (fun q ↦ HomologicalComplex.homologyMap q n)
    (inhomogeneous_cochains_naturality
      ((coindFunctor k H.subtype).map f))
  simp only [HomologicalComplex.homologyMap_comp] at hcochains
  dsimp [coindFunctor] at hcochains
  have hmiddle := congrArg
    (fun q ↦ HomologicalComplex.homologyMap q n)
    (yoneda_obj_projective P f)
  simp only [HomologicalComplex.homologyMap_comp] at hmiddle
  dsimp [P] at hmiddle
  have hGIso := cohomology_iso_naturality Q f n
  have hGIsoInv :
      (groupCohomologyIso A n Q).inv ≫
          groupCohomology.map (MonoidHom.id H) f n =
        HomologicalComplex.homologyMap
            (yonedaObj Q.complex f) n ≫
          (groupCohomologyIso B n Q).inv := by
    rw [← cancel_epi (groupCohomologyIso A n Q).hom]
    rw [Iso.hom_inv_id_assoc]
    slice_rhs 1 2 => rw [← hGIso]
    simp
  dsimp [Q, P] at hGIsoInv
  dsimp [groupCohomology.coindIso]
  simp only [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [hGIsoInv]
  slice_lhs 2 3 => rw [← hmiddle]
  slice_lhs 1 2 => rw [← hcochains]
  simp only [Category.assoc]

/-- Shapiro restriction commutes with morphisms of coefficient modules. -/
theorem shapiroRestriction_naturality
    {A B : Rep k G} (H : Subgroup G) [H.FiniteIndex]
    (f : A ⟶ B) (n : ℕ) :
    COps.shapiroRestriction A H n ≫
        groupCohomology.map (MonoidHom.id H)
          ((resFunctor H.subtype).map f) n =
      groupCohomology.map (MonoidHom.id G) f n ≫
        COps.shapiroRestriction B H n := by
  dsimp only [COps.shapiroRestriction]
  have hcoind := coindIso_naturality
    ((resFunctor H.subtype).map f) n
  dsimp [resFunctor, coindFunctor] at hcoind
  have hunit := (resCoindAdjunction k H.subtype).unit.naturality f
  dsimp [resFunctor, coindFunctor] at hunit
  have hunitMap := congrArg
    (fun q ↦ groupCohomology.map (MonoidHom.id G) q n) hunit
  dsimp only at hunitMap
  have hmap := groupCohomology.map_id_comp f
    ((resCoindAdjunction k H.subtype).unit.app B) n
  dsimp [resFunctor, coindFunctor] at hmap
  dsimp [resFunctor, coindFunctor]
  rw [Category.assoc]
  slice_lhs 2 3 => rw [hcoind]
  rw [← Category.assoc, ← groupCohomology.map_id_comp]
  slice_lhs 1 1 => exact hunitMap.symm
  slice_lhs 1 1 => exact hmap
  simp only [Category.assoc]

end

end Submission.CField.Shifting
