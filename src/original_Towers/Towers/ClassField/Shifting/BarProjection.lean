import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Explicit bar-resolution projection for homological restriction

For a subgroup `H ≤ G`, this constructs the standard right-coset projection
from the restricted bar resolution of `G` to the bar resolution of `H`.  It
also identifies the inverse projective-resolution comparison used by group
homology with the map induced by this explicit projection.  These are the
chain-level ingredients for Proposition II.3.2(b).
-/

open CategoryTheory Finsupp

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

noncomputable def rightCosetRep (H : Subgroup G) (g : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g)

theorem coset_rep_rel (H : Subgroup G) (g : G) :
    QuotientGroup.rightRel H (rightCosetRep H g) g := by
  apply Quotient.exact
  exact Quotient.out_eq _

noncomputable def rightCosetCorrection (H : Subgroup G) (g : G) : H :=
  ⟨g * (rightCosetRep H g)⁻¹,
    QuotientGroup.rightRel_apply.mp (coset_rep_rel H g)⟩

theorem coset_rep_left (H : Subgroup G) (h : H) (g : G) :
    rightCosetRep H (h * g) = rightCosetRep H g := by
  apply congrArg Quotient.out
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa only [mul_inv_rev, mul_inv_cancel_left] using H.inv_mem h.property

theorem right_coset_left (H : Subgroup G) (h : H) (g : G) :
    rightCosetCorrection H (h * g) = h * rightCosetCorrection H g := by
  apply Subtype.ext
  simp [rightCosetCorrection, coset_rep_left, mul_assoc]

noncomputable def standardProjectionMap (H : Subgroup G) (n : ℕ) :
    ((resFunctor H.subtype).obj ((standardComplex k G).X n)) ⟶
      (standardComplex k H).X n := by
  let f :
      (Action.res (Type u) H.subtype).obj
          ((classifyingSpaceUniversalCover G).obj
            (Opposite.op (SimplexCategory.mk n))) ⟶
        (classifyingSpaceUniversalCover H).obj
          (Opposite.op (SimplexCategory.mk n)) :=
    { hom := ↾(fun (x : Fin (n + 1) → G) i => rightCosetCorrection H (x i))
      comm := fun h => by
        ext (x : Fin (n + 1) → G)
        funext i
        exact right_coset_left H h (x i) }
  exact ofHom (Representation.linearizeMap f)

@[simp]
theorem standard_projection_single (H : Subgroup G) (n : ℕ)
    (x : Fin (n + 1) → G) (r : k) :
    (standardProjectionMap (k := k) H n).hom (single x r) =
      single (fun i => rightCosetCorrection H (x i)) r := by
  simp only [standardProjectionMap]
  apply Representation.linearizeMap_single

noncomputable def standardProjection (H : Subgroup G) :
    ((resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (standardComplex k G) ⟶
      standardComplex k H where
  f n := standardProjectionMap (k := k) H n
  comm' i j hij := by
    subst i
    simp only [Functor.mapHomologicalComplex_obj_d]
    apply hom_ext
    apply Representation.IntertwiningMap.ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change
      ((standardComplex k H).d (j + 1) j).hom
          ((standardProjectionMap (k := k) H (j + 1)).hom
            (Finsupp.single x 1)) =
        (standardProjectionMap (k := k) H j).hom
          (((standardComplex k G).d (j + 1) j).hom
            (Finsupp.single x 1))
    rw [standardComplex.d_apply, standardComplex.d_apply]
    rw [standard_projection_single]
    change
      standardComplex.d k H (j + 1)
          (single (fun i : Fin (j + 2) =>
            rightCosetCorrection H (x i)) 1) =
        (standardProjectionMap (k := k) H j).hom
          (standardComplex.d k G (j + 1)
            (single (fun i : Fin (j + 2) => x i) 1))
    rw [standardComplex.d_single
      (k := k) (G := H) (n := j + 1)
      (fun i => rightCosetCorrection H (x i)) 1]
    rw [standardComplex.d_single
      (k := k) (G := G) (n := j + 1) (fun i => x i) 1]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    change
      single (fun q : Fin (j + 1) =>
          rightCosetCorrection H (x (p.succAbove q)))
          (1 * (-1) ^ (p : ℕ)) =
        (standardProjectionMap (k := k) H j).hom
          (single (fun q : Fin (j + 1) => x (p.succAbove q))
            (1 * (-1) ^ (p : ℕ)))
    rw [standard_projection_single]

noncomputable def barProjection (H : Subgroup G) :
    ((resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (barComplex k G) ⟶
      barComplex k H :=
  ((resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (barComplex.isoStandardComplex k G).hom ≫
    standardProjection (k := k) H ≫
    (barComplex.isoStandardComplex k H).inv

theorem standard_projection_f (H : Subgroup G) :
    (standardProjection (k := k) H).f 0 ≫
        (standardComplex.εToSingle₀ k H).f 0 =
      (resFunctor H.subtype).map
        ((standardComplex.εToSingle₀ k G).f 0) := by
  apply hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change
    (standardComplex.ε k H).hom
        ((standardProjectionMap (k := k) H 0).hom (single x 1)) =
      (standardComplex.ε k G).hom (single x 1)
  rw [standard_projection_single]
  simp [standardComplex.ε]

theorem bar_f_pi (H : Subgroup G) :
    (barProjection (k := k) H).f 0 ≫
        (barResolution k H).π.f 0 =
      ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)).π.f 0 := by
  have hc :
      (barComplex.isoStandardComplex k H).inv.f 0 ≫
          (barComplex.isoStandardComplex k H).hom.f 0 =
        𝟙 _ := by
    have h := HomologicalComplex.congr_hom
      (Iso.inv_hom_id (barComplex.isoStandardComplex k H)) 0
    simpa only [HomologicalComplex.comp_f,
      HomologicalComplex.id_f] using h
  simp only [barProjection, barResolution,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  rw [← Category.assoc
    ((barComplex.isoStandardComplex k H).inv.f 0)
    ((barComplex.isoStandardComplex k H).hom.f 0)
    ((standardComplex.εToSingle₀ k H).f 0)]
  rw [hc, Category.id_comp]
  rw [standard_projection_f]
  simp only [Functor.mapHomologicalComplex_obj_X,
    ChainComplex.single₀_obj_zero, Functor.mapProjectiveResolution_complex,
    Functor.mapProjectiveResolution_π, Functor.map_comp, Category.assoc,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, hom_id, Iso.refl_inv,
    Category.comp_id]
  ext x
  rfl

theorem homology_bar_inv
    (H : Subgroup G) [DecidableEq H] (A : Rep k H) (n : ℕ) :
    (groupHomologyIso A n
      ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G))).inv =
      ((((coinvariantsTensor k H).obj A).mapHomologicalComplex
            (ComplexShape.down ℕ)) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k)
            (ComplexShape.down ℕ) n).map
          (barProjection (k := k) H) ≫
        (HomologicalComplex.homologyFunctor (ModuleCat k)
          (ComplexShape.down ℕ) n).map
          (groupHomology.inhomogeneousChainsIso A).inv := by
  classical
  rw [groupHomologyIso]
  dsimp [groupHomologyIsoTor]
  have hinv :
      (isoOfQuasiIsoAt
        (HomotopyEquiv.ofIso
          (groupHomology.inhomogeneousChainsIso A)).hom n).inv =
        HomologicalComplex.homologyMap
          (groupHomology.inhomogeneousChainsIso A).inv n := by
    rw [← cancel_epi (HomologicalComplex.homologyMap
      (groupHomology.inhomogeneousChainsIso A).hom n)]
    calc
      HomologicalComplex.homologyMap
            (groupHomology.inhomogeneousChainsIso A).hom n ≫
          (isoOfQuasiIsoAt
            (HomotopyEquiv.ofIso
              (groupHomology.inhomogeneousChainsIso A)).hom n).inv =
          𝟙 _ := by
        change
          (isoOfQuasiIsoAt
              (HomotopyEquiv.ofIso
                (groupHomology.inhomogeneousChainsIso A)).hom n).hom ≫
            (isoOfQuasiIsoAt
              (HomotopyEquiv.ofIso
                (groupHomology.inhomogeneousChainsIso A)).hom n).inv =
            𝟙 _
        exact (isoOfQuasiIsoAt
          (HomotopyEquiv.ofIso
            (groupHomology.inhomogeneousChainsIso A)).hom n).hom_inv_id
      _ = HomologicalComplex.homologyMap
            (groupHomology.inhomogeneousChainsIso A).hom n ≫
          HomologicalComplex.homologyMap
            (groupHomology.inhomogeneousChainsIso A).inv n := by
        simp [← HomologicalComplex.homologyMap_comp]
  rw [hinv]
  rw [← Category.assoc]
  apply (cancel_mono
    (HomologicalComplex.homologyMap
      (groupHomology.inhomogeneousChainsIso A).inv n)).mpr
  have hnat :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      (𝟙 (trivial k H k))
      ((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G))
      (barResolution k H)
      (barProjection (k := k) H)
      (bar_f_pi (k := k) H)
      ((coinvariantsTensor k H).obj A) n
  have hnat' :
      ((barResolution k H).isoLeftDerivedObj
        ((coinvariantsTensor k H).obj A) n).hom =
        (((resFunctor H.subtype).mapProjectiveResolution
            (barResolution k G)).isoLeftDerivedObj
              ((coinvariantsTensor k H).obj A) n).hom ≫
          ((((coinvariantsTensor k H).obj A).mapHomologicalComplex
              (ComplexShape.down ℕ)) ⋙
            HomologicalComplex.homologyFunctor (ModuleCat k)
              (ComplexShape.down ℕ) n).map
            (barProjection (k := k) H) := by
    simpa using hnat
  rw [hnat']
  change
    (((resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)).isoLeftDerivedObj
          ((coinvariantsTensor k H).obj A) n).inv ≫
      ((((resFunctor H.subtype).mapProjectiveResolution
          (barResolution k G)).isoLeftDerivedObj
            ((coinvariantsTensor k H).obj A) n).hom ≫
        ((((coinvariantsTensor k H).obj A).mapHomologicalComplex
            (ComplexShape.down ℕ)) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k)
            (ComplexShape.down ℕ) n).map
          (barProjection (k := k) H)) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

end Rep
