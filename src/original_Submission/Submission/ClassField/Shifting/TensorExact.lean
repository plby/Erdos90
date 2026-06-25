import Submission.ClassField.Shifting.RegularTensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Milne, Class Field Theory, Remark II.3.12: tensor exactness

Both short exact sequences making up Tate's four-term sequence split after
forgetting the group action: their quotients are `I_G` and `Z`.  Consequently
they remain exact after tensoring with an arbitrary representation.  This
file isolates that general argument and applies it to the two concrete
sequences.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep
open scoped TensorProduct
open Submission.CField.TCohomo

noncomputable section

variable {G : Type} [Group G]

/-- Tensoring a short exact sequence on the left remains short exact when
its first map has a retraction after forgetting the group action.  Exactness
at the middle and surjectivity on the right are the usual right exactness of
tensor product; the retraction supplies injectivity on the left. -/
theorem tensor_short_retraction
    (M : Rep ℤ G) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (r : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) X.X₂ X.X₁ _ _
      X.X₂.hV2 X.X₁.hV2)
    (hr : Function.LeftInverse r X.f) :
    (X.map ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact := by
  letI repModule (A : Rep ℤ G) : Module ℤ A := A.hV2
  let F : Functor (Rep ℤ G) (ModuleCat ℤ) :=
    forget₂ (Rep ℤ G) (ModuleCat ℤ)
  let UX := X.map F
  have hUX : UX.ShortExact := hX.map_of_exact F
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact UX).mp
        hUX.exact
  have hsurj : Function.Surjective X.g.hom.toLinearMap := by
    exact (ModuleCat.epi_iff_surjective _).mp hUX.epi_g
  let T := X.map ((tensoringLeft (Rep ℤ G)).obj M)
  refine
    { exact := F.reflects_exact_of_faithful T ?_
      mono_f := (Rep.mono_iff_injective _).2 ?_
      epi_g := (Rep.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff (T.map F)).2
    intro x hx
    change LinearMap.lTensor M X.g.hom.toLinearMap x = 0 at hx
    obtain ⟨y, hy⟩ := (lTensor_exact M hexact hsurj x).mp hx
    refine ⟨y, ?_⟩
    change LinearMap.lTensor M X.f.hom.toLinearMap y = x
    exact hy
  · intro x y hxy
    change LinearMap.lTensor M X.f.hom.toLinearMap x =
      LinearMap.lTensor M X.f.hom.toLinearMap y at hxy
    have hcomp : r.comp X.f.hom.toLinearMap = LinearMap.id :=
      LinearMap.ext fun z ↦ hr z
    apply_fun LinearMap.lTensor M r at hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp,
      LinearMap.lTensor_id_apply] using hxy
  · exact LinearMap.lTensor_surjective M hsurj

/-- Projection onto `C` retracts the inclusion `C → C(φ)` after
forgetting the group action. -/
noncomputable def splittingModuleRetraction
    (C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (hφ : φ (1, 1) = 0) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ)
      (splittingModule C φ hφ) C _ _
      (splittingModule C φ hφ).hV2 C.hV2 :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
    (splittingModule C φ hφ) C _ _
    (splittingModule C φ hφ).hV2 C.hV2
    { toFun := Prod.fst
      map_add' := fun _ _ ↦ rfl }
    (fun n x ↦ by
      change ((splittingModule C φ hφ).hV2.smul n x).1 =
        C.hV2.smul n x.1
      rw [int_smul_eq_zsmul (splittingModule C φ hφ).hV2,
        int_smul_eq_zsmul C.hV2]
      rfl)

@[simp]
theorem splitting_module_retraction
    (C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (hφ : φ (1, 1) = 0) (x : splittingModule C φ hφ) :
    splittingModuleRetraction C φ hφ x = x.1 :=
  by
    change x.1 = x.1
    rfl

/-- The splitting-module sequence stays short exact after tensoring with an
arbitrary representation `M`. -/
theorem splitting_short_exact
    (M C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (hφ : φ (1, 1) = 0) :
    ((splittingModuleSequence C φ hφ).map
      ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact := by
  apply tensor_short_retraction M
    (splitting_sequence_short C φ hφ)
    (splittingModuleRetraction C φ hφ)
  intro c
  change (splittingModuleInclusion C φ hφ c).1 = c
  rw [splitting_module_inclusion]

/-- Projection along the basis vector at `1` retracts the augmentation-ideal
inclusion after forgetting the group action. -/
noncomputable def augmentationIdealRetraction :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ)
      (Rep.leftRegular ℤ G) (augmentationIdealRep (G := G)) _ _
      (Rep.leftRegular ℤ G).hV2 (augmentationIdealRep (G := G)).hV2 := by
  let f : IntegralGroupRing G →+ augmentationIdeal G :=
    { toFun := fun x ↦
        ⟨x - MonoidAlgebra.single 1 (augmentation G x), by
          change augmentation G
            (x - MonoidAlgebra.single 1 (augmentation G x)) = 0
          rw [map_sub, augmentation_single]
          simp⟩
      map_zero' := by
        apply Subtype.ext
        simp
        rfl
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change x + y - MonoidAlgebra.single 1 (augmentation G (x + y)) =
          (x - MonoidAlgebra.single 1 (augmentation G x)) +
            (y - MonoidAlgebra.single 1 (augmentation G y))
        rw [map_add, MonoidAlgebra.single_add]
        abel }
  exact @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
    (Rep.leftRegular ℤ G) (augmentationIdealRep (G := G)) _ _
    (Rep.leftRegular ℤ G).hV2 (augmentationIdealRep (G := G)).hV2
    f.toAddHom
    (fun n x ↦ by
      change
        f ((Rep.leftRegular ℤ G).hV2.smul n x) =
          (augmentationIdealRep (G := G)).hV2.smul n (f x)
      rw [int_smul_eq_zsmul (Rep.leftRegular ℤ G).hV2,
        int_smul_eq_zsmul (augmentationIdealRep (G := G)).hV2]
      exact f.map_zsmul n x)

@[simp]
theorem augmentation_ideal_retraction (x : IntegralGroupRing G) :
    (augmentationIdealRetraction (G := G) x).1 =
      x - MonoidAlgebra.single 1 (augmentation G x) := by
  rfl

/-- The preceding map really retracts the augmentation-ideal inclusion. -/
theorem augmentation_retraction_inverse :
    Function.LeftInverse (augmentationIdealRetraction (G := G))
      (augmentationIdealInclusion (G := G)) := by
  intro x
  apply Subtype.ext
  rw [show augmentationIdealInclusion (G := G) x = x.1 from rfl]
  rw [augmentation_ideal_retraction]
  rw [show augmentation G x.1 = 0 from x.2]
  simp
  rfl

/-- The augmentation sequence stays short exact after tensoring with an
arbitrary representation `M`. -/
theorem tensor_sequence_short (M : Rep ℤ G) :
    ((augmentationSequence (G := G)).map
      ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact := by
  exact tensor_short_retraction M
    augmentation_short_exact augmentationIdealRetraction
    augmentation_retraction_inverse

end

end Submission.CField.Shifting
