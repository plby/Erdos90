import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Explicit bar-resolution inclusion for Shapiro's lemma

For a subgroup `H ≤ G`, this constructs the canonical inclusion of the bar
resolution of `H` into the restriction of the bar resolution of `G`, and
identifies its induced homology map with the abstract projective-resolution
comparison.  This complements `Proposition32BarProjection` in the
chain-level proof of Proposition II.3.2(b).
-/

open CategoryTheory Finsupp

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The pointwise subgroup inclusion on homogeneous bar generators. -/
noncomputable def standardInclusionMap (H : Subgroup G) (n : ℕ) :
    (standardComplex k H).X n ⟶
      (resFunctor H.subtype).obj ((standardComplex k G).X n) := by
  let f :
      (classifyingSpaceUniversalCover H).obj
          (Opposite.op (SimplexCategory.mk n)) ⟶
        (Action.res (Type u) H.subtype).obj
          ((classifyingSpaceUniversalCover G).obj
            (Opposite.op (SimplexCategory.mk n))) :=
    { hom := ↾(fun x i => H.subtype (x i))
      comm := fun h => by
        ext (x : Fin (n + 1) → H)
        funext i
        rfl }
  exact ofHom (Representation.linearizeMap f)

@[simp]
theorem standard_inclusion_single (H : Subgroup G) (n : ℕ)
    (x : Fin (n + 1) → H) (r : k) :
    (standardInclusionMap (k := k) H n).hom (single x r) =
      single (fun i => H.subtype (x i)) r := by
  simp only [standardInclusionMap]
  apply Representation.linearizeMap_single

/-- The pointwise inclusion of homogeneous bar resolutions. -/
noncomputable def standardInclusion (H : Subgroup G) :
    standardComplex k H ⟶
      ((resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (standardComplex k G) where
  f n := standardInclusionMap (k := k) H n
  comm' i j hij := by
    subst i
    simp only [Functor.mapHomologicalComplex_obj_d]
    apply hom_ext
    apply Representation.IntertwiningMap.ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change
      ((standardComplex k G).d (j + 1) j).hom
          ((standardInclusionMap (k := k) H (j + 1)).hom
            (single x 1)) =
        (standardInclusionMap (k := k) H j).hom
          (((standardComplex k H).d (j + 1) j).hom
            (single x 1))
    rw [standardComplex.d_apply, standardComplex.d_apply]
    rw [standard_inclusion_single]
    change
      standardComplex.d k G (j + 1)
          (single (fun i : Fin (j + 2) => H.subtype (x i)) 1) =
        (standardInclusionMap (k := k) H j).hom
          (standardComplex.d k H (j + 1)
            (single (fun i : Fin (j + 2) => x i) 1))
    rw [standardComplex.d_single
      (k := k) (G := G) (n := j + 1)
      (fun i => H.subtype (x i)) 1]
    rw [standardComplex.d_single
      (k := k) (G := H) (n := j + 1) (fun i => x i) 1]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact (standard_inclusion_single (k := k) (G := G) H j
      ((fun i => x i) ∘ p.succAbove) (1 * (-1) ^ (p : ℕ))).symm

/-- The homogeneous inclusion commutes with the augmentations. -/
theorem standard_inclusion_f (H : Subgroup G) :
    (standardInclusion (k := k) H).f 0 ≫
        (resFunctor H.subtype).map
          ((standardComplex.εToSingle₀ k G).f 0) =
      (standardComplex.εToSingle₀ k H).f 0 := by
  apply hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change
    (standardComplex.ε k G).hom
        ((standardInclusionMap (k := k) H 0).hom (single x 1)) =
      (standardComplex.ε k H).hom (single x 1)
  rw [standard_inclusion_single]
  simp [standardComplex.ε]

/-- The bar-resolution inclusion induced from the homogeneous model. -/
noncomputable def barInclusion (H : Subgroup G) :
    barComplex k H ⟶
      ((resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (barComplex k G) :=
  (barComplex.isoStandardComplex k H).hom ≫
    standardInclusion (k := k) H ≫
    ((resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (barComplex.isoStandardComplex k G).inv

noncomputable def restrictedBarResolution (H : Subgroup G) :
    ProjectiveResolution (trivial k H k) :=
  (resFunctor H.subtype).mapProjectiveResolution (barResolution k G)

theorem bar_inclusion_f (H : Subgroup G) :
    (barInclusion (k := k) H).f 0 ≫
        (restrictedBarResolution (k := k) H).π.f 0 =
      (barResolution k H).π.f 0 := by
  simp only [barInclusion, restrictedBarResolution, barResolution,
    HomologicalComplex.comp_f, Functor.mapProjectiveResolution_π,
    Functor.map_comp, Category.assoc]
  let i := (((resFunctor H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).map
    (barComplex.isoStandardComplex k G).inv).f 0
  let h := (((resFunctor H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).map
    (barComplex.isoStandardComplex k G).hom).f 0
  let q :=
    (((resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (standardComplex.εToSingle₀ k G)).f 0 ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (resFunctor H.subtype) (ComplexShape.down ℕ) 0).hom.app
        (trivial k G k)).f 0
  have hc : i ≫ h = 𝟙 _ := by
    dsimp only [i, h]
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
    simp
  have hsuffix : i ≫ (h ≫ q) = q := by
    calc
      i ≫ (h ≫ q) = (i ≫ h) ≫ q := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ q := congrArg (fun f => f ≫ q) hc
      _ = q := Category.id_comp _
  have haug : (standardInclusion (k := k) H).f 0 ≫ q =
      (standardComplex.εToSingle₀ k H).f 0 := by
    dsimp only [q]
    rw [← Category.assoc]
    erw [standard_inclusion_f]
  change
    (barComplex.isoStandardComplex k H).hom.f 0 ≫
        ((standardInclusion (k := k) H).f 0 ≫
          (i ≫ (h ≫ q))) =
      (barComplex.isoStandardComplex k H).hom.f 0 ≫
        (standardComplex.εToSingle₀ k H).f 0
  rw [hsuffix, haug]
  rfl

theorem homology_restricted_bar
    (H : Subgroup G) [DecidableEq H] (A : Rep k H) (n : ℕ) :
    (groupHomologyIso A n
      (restrictedBarResolution (k := k) H)).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat k)
        (ComplexShape.down ℕ) n).map
          (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((coinvariantsTensor k H).obj A).mapHomologicalComplex
            (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k)
            (ComplexShape.down ℕ) n).map
          (barInclusion (k := k) H) := by
  classical
  rw [groupHomologyIso]
  dsimp [groupHomologyIsoTor]
  rw [Category.assoc]
  congr 1
  change
    ((barResolution k H).isoLeftDerivedObj
        ((coinvariantsTensor k H).obj A) n).inv ≫
      ((restrictedBarResolution (k := k) H).isoLeftDerivedObj
        ((coinvariantsTensor k H).obj A) n).hom =
      HomologicalComplex.homologyMap
        ((((coinvariantsTensor k H).obj A).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (barInclusion (k := k) H)) n
  have hn :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      (𝟙 (trivial k H k)) (barResolution k H)
      (restrictedBarResolution (k := k) H)
      (barInclusion (k := k) H)
      (bar_inclusion_f (k := k) H)
      ((coinvariantsTensor k H).obj A) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  rw [hn]
  calc
    _ = (((coinvariantsTensor k H).obj A).mapHomologicalComplex
          (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat k)
          (ComplexShape.down ℕ) n).map (barInclusion (k := k) H) :=
      ((barResolution k H).isoLeftDerivedObj
        ((coinvariantsTensor k H).obj A) n).inv_hom_id_assoc _
    _ = _ := rfl

end Rep
