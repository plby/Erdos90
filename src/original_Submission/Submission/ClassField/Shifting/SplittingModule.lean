import Submission.ClassField.CohomologyOps.NormalizedRepresentation
import Submission.ClassField.TateCohomology.IntegralGroupRing
import Submission.ClassField.Shifting.AllDegrees
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Milne, Class Field Theory, Theorem II.3.11: the splitting module

Given a normalized two-cocycle `φ` with values in a `G`-module `C`, this file
constructs Tate's splitting module `C(φ)`.  We use the equivalent model

`C(φ) = C ⊕ I_G`,

where `I_G` is the augmentation ideal.  On the standard generator `τ - 1`,
the twisted action is

`σ * (0, τ - 1) = (φ(σ, τ), στ - σ)`.

This is Milne's formula `σ x_τ = x_(στ) - x_σ + φ(σ,τ)`.  We prove directly
from the cocycle identity that it defines a representation, and construct the
short exact sequence `0 -> C -> C(φ) -> I_G -> 0`.
-/

namespace Submission.CField.Shifting

open CategoryTheory Rep
open groupCohomology
open Submission.CField.TCohomo

noncomputable section

variable {G : Type} [Group G]

/-- Left multiplication by `g` preserves the augmentation ideal. -/
noncomputable def augmentationLeftAction (g : G) :
    augmentationIdeal G →ₗ[ℤ] augmentationIdeal G :=
  (LinearMap.mulLeft ℤ (MonoidAlgebra.single g 1)).domRestrict (augmentationIdeal G) |>.codRestrict
    (augmentationIdeal G) fun x ↦ by
      change augmentation G (MonoidAlgebra.single g 1 * x.1) = 0
      rw [augmentation_mul, augmentation_single, LinearMap.mem_ker.mp x.2]
      simp

@[simp]
theorem augmentation_action_coe (g : G) (x : augmentationIdeal G) :
    ((augmentationLeftAction g x : augmentationIdeal G) : IntegralGroupRing G) =
      MonoidAlgebra.single g 1 * x.1 :=
  rfl

@[simp]
theorem augmentation_action_one (x : augmentationIdeal G) :
    augmentationLeftAction (1 : G) x = x := by
  apply Subtype.ext
  change MonoidAlgebra.single 1 1 * x.1 = x.1
  rw [← MonoidAlgebra.one_def, one_mul]

@[simp]
theorem augmentation_action_mul (g h : G) (x : augmentationIdeal G) :
    augmentationLeftAction (g * h) x =
      augmentationLeftAction g (augmentationLeftAction h x) := by
  apply Subtype.ext
  change MonoidAlgebra.single (g * h) 1 * x.1 =
    MonoidAlgebra.single g 1 * (MonoidAlgebra.single h 1 * x.1)
  rw [← mul_assoc, MonoidAlgebra.single_mul_single]
  simp

@[simp]
theorem augmentation_action_class (g t : G) :
    augmentationLeftAction g (augmentationClass G t) =
      augmentationClass G (g * t) - augmentationClass G g := by
  apply Subtype.ext
  change MonoidAlgebra.single g 1 *
      (MonoidAlgebra.single t (1 : ℤ) - MonoidAlgebra.single 1 1) =
    (MonoidAlgebra.single (g * t) (1 : ℤ) - MonoidAlgebra.single 1 1) -
      (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 1)
  rw [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  simp

/-- The coefficient sum `∑ n_τ φ(g,τ)` on the integral group ring. -/
noncomputable def cocycleCoefficientSum (C : Rep ℤ G)
    (φ : cocycles₂ C) (g : G) : IntegralGroupRing G →ₗ[ℤ] C :=
  Finsupp.linearCombination ℤ fun t ↦ φ (g, t)

@[simp]
theorem cocycle_coefficient_single (C : Rep ℤ G)
    (φ : cocycles₂ C) (g t : G) (n : ℤ) :
    cocycleCoefficientSum C φ g (MonoidAlgebra.single t n) = n • φ (g, t) := by
  exact Finsupp.linearCombination_single ℤ n t

/-- The twisting form on `I_G` used in the splitting-module action. -/
noncomputable def splittingTwist (C : Rep ℤ G)
    (φ : cocycles₂ C) (g : G) : augmentationIdeal G →ₗ[ℤ] C :=
  (cocycleCoefficientSum C φ g).domRestrict (augmentationIdeal G)

@[simp]
theorem splittingTwist_class (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) (g t : G) :
    splittingTwist C φ g (augmentationClass G t) = φ (g, t) := by
  change cocycleCoefficientSum C φ g
      (MonoidAlgebra.single t 1 - MonoidAlgebra.single 1 1) = φ (g, t)
  rw [map_sub, cocycle_coefficient_single, cocycle_coefficient_single]
  rw [one_smul, one_smul, cocycles₂_map_one_snd φ g, hφ, map_zero, sub_zero]

/-- The cocycle identity after taking a coefficient-weighted sum in the group
ring.  The final term records the augmentation; it vanishes on `I_G`. -/
theorem cocycle_coefficient_identity (C : Rep ℤ G)
    (φ : cocycles₂ C) (g h : G) (x : IntegralGroupRing G) :
    C.ρ g (cocycleCoefficientSum C φ h x) +
        cocycleCoefficientSum C φ g (MonoidAlgebra.single h 1 * x) =
      cocycleCoefficientSum C φ (g * h) x + augmentation G x • φ (g, h) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      calc
        C.ρ g (cocycleCoefficientSum C φ h (x + y)) +
              cocycleCoefficientSum C φ g (MonoidAlgebra.single h 1 * (x + y)) =
            (C.ρ g (cocycleCoefficientSum C φ h x) +
                cocycleCoefficientSum C φ g (MonoidAlgebra.single h 1 * x)) +
              (C.ρ g (cocycleCoefficientSum C φ h y) +
                cocycleCoefficientSum C φ g (MonoidAlgebra.single h 1 * y)) := by
          simp only [map_add, mul_add]
          abel
        _ = (cocycleCoefficientSum C φ (g * h) x + augmentation G x • φ (g, h)) +
              (cocycleCoefficientSum C φ (g * h) y + augmentation G y • φ (g, h)) := by
          rw [hx, hy]
        _ = cocycleCoefficientSum C φ (g * h) (x + y) +
              augmentation G (x + y) • φ (g, h) := by
          simp only [map_add, add_smul]
          abel
  | single t n =>
      simp only [cocycle_coefficient_single, MonoidAlgebra.single_mul_single,
        one_mul, augmentation_single]
      calc
        C.ρ g (n • φ (h, t)) + n • φ (g, h * t) =
            n • (C.ρ g (φ (h, t)) + φ (g, h * t)) := by
          rw [map_zsmul, smul_add]
        _ = n • (φ (g * h, t) + φ (g, h)) := by
          rw [((mem_cocycles₂_iff φ).1 φ.2 g h t).symm]
        _ = n • φ (g * h, t) + n • φ (g, h) := smul_add n _ _

/-- A normalized cocycle has zero twisting form at the identity. -/
theorem splittingTwist_one (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) (x : augmentationIdeal G) :
    splittingTwist C φ 1 x = 0 := by
  change cocycleCoefficientSum C φ 1 x.1 = 0
  induction x.1 using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single t n =>
      rw [cocycle_coefficient_single, cocycles₂_map_one_fst φ t, hφ, smul_zero]

/-- On the augmentation ideal, the weighted cocycle identity has no error
term. -/
theorem splittingTwist_identity (C : Rep ℤ G)
    (φ : cocycles₂ C) (g h : G) (x : augmentationIdeal G) :
    C.ρ g (splittingTwist C φ h x) +
        splittingTwist C φ g (augmentationLeftAction h x) =
      splittingTwist C φ (g * h) x := by
  have hx := cocycle_coefficient_identity C φ g h x.1
  rw [LinearMap.mem_ker.mp x.2, zero_smul, add_zero] at hx
  exact hx

/-- The linear action of one group element on Tate's splitting module. -/
noncomputable def splittingAction (C : Rep ℤ G)
    (φ : cocycles₂ C) (g : G) :
    (C × augmentationIdeal G) →ₗ[ℤ] (C × augmentationIdeal G) where
  toFun x :=
    (C.ρ g x.1 + splittingTwist C φ g x.2,
      augmentationLeftAction g x.2)
  map_add' x y := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' n x := by
    ext <;> simp [smul_add]

@[simp]
theorem splittingAction_apply (C : Rep ℤ G)
    (φ : cocycles₂ C) (g : G) (x : C × augmentationIdeal G) :
    splittingAction C φ g x =
      (C.ρ g x.1 + splittingTwist C φ g x.2,
        augmentationLeftAction g x.2) :=
  rfl

/-- The representation underlying Tate's splitting module. -/
noncomputable def splittingRepresentation (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    Representation ℤ G (C × augmentationIdeal G) where
  toFun := splittingAction C φ
  map_one' := by
    apply LinearMap.ext
    intro x
    ext
    · simp [splittingAction, splittingTwist_one C φ hφ]
    · simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change splittingAction C φ (g * h) x =
      splittingAction C φ g (splittingAction C φ h x)
    apply Prod.ext
    · simp only [splittingAction_apply, map_add]
      rw [map_mul, ← splittingTwist_identity C φ g h x.2]
      simp [add_assoc]
    · simp

/-- Tate's splitting module `C(φ)`. -/
noncomputable def splittingModule (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) : Rep ℤ G :=
  Rep.of (splittingRepresentation C φ hφ)

@[simp]
theorem splittingModule_action (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0)
    (g : G) (x : splittingModule C φ hφ) :
    (splittingModule C φ hφ).ρ g x =
      (C.ρ g x.1 + splittingTwist C φ g x.2,
        augmentationLeftAction g x.2) :=
  rfl

/-- The augmentation ideal with its left regular action. -/
noncomputable def augmentationIdealRep : Rep ℤ G :=
  Rep.of
    { toFun := augmentationLeftAction
      map_one' := by ext; simp
      map_mul' := by intro g h; ext; simp }

/-- The canonical inclusion `C -> C(φ)`. -/
noncomputable def splittingModuleInclusion (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    C ⟶ splittingModule C φ hφ := by
  let f := @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
    C (C × augmentationIdeal G) _ _ C.hV2 (splittingModule C φ hφ).hV2
    { toFun := fun c ↦ (c, 0)
      map_add' := fun _ _ ↦ rfl }
    (fun n x ↦ by
      change (C.hV2.smul n x, 0) =
        (splittingModule C φ hφ).hV2.smul n (x, 0)
      rw [int_smul_eq_zsmul C.hV2 n x,
        int_smul_eq_zsmul (splittingModule C φ hφ).hV2 n (x, 0)]
      change (n • x, 0) = (n • x, n • (0 : augmentationIdeal G))
      simp)
  let F := @Representation.IntertwiningMap.mk ℤ G C
    (C × augmentationIdeal G) _ _ _ _ C.hV2
    (splittingModule C φ hφ).hV2 C.ρ (splittingModule C φ hφ).ρ f
      (fun g ↦ by
        apply @LinearMap.ext ℤ ℤ C (C × augmentationIdeal G)
          _ _ _ _ C.hV2 (splittingModule C φ hφ).hV2 (RingHom.id ℤ)
        intro x
        change (C.ρ g x, 0) = splittingAction C φ g (x, 0)
        simp [splittingAction])
  exact @Rep.ofHom ℤ G _ _ C (C × augmentationIdeal G) _ _ C.hV2
    (splittingModule C φ hφ).hV2 C.ρ (splittingModule C φ hφ).ρ F

@[simp]
theorem splitting_module_inclusion (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) (c : C) :
    splittingModuleInclusion C φ hφ c = (c, 0) :=
  rfl

/-- The canonical projection `C(φ) -> I_G`. -/
noncomputable def splittingModuleProjection (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    splittingModule C φ hφ ⟶ augmentationIdealRep :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := Prod.snd
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      isIntertwining' := fun _ ↦ rfl }

@[simp]
theorem splitting_module_projection (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0)
    (x : splittingModule C φ hφ) :
    splittingModuleProjection C φ hφ x = x.2 :=
  rfl

/-- The coefficient sequence `0 -> C -> C(φ) -> I_G -> 0`. -/
noncomputable def splittingModuleSequence (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (splittingModuleInclusion C φ hφ)
    (splittingModuleProjection C φ hφ) (by rfl)

/-- Milne's splitting-module sequence is short exact. -/
theorem splitting_sequence_short (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    (splittingModuleSequence C φ hφ).ShortExact := by
  letI repModule (X : Rep.{0} ℤ G) : Module ℤ X := X.hV2
  let F : Functor (Rep.{0} ℤ G) (ModuleCat.{0} ℤ) :=
    forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)
  let S : ShortComplex (ModuleCat.{0} ℤ) := (splittingModuleSequence C φ hφ).map F
  have hS : S.Exact := (ShortComplex.moduleCat_exact_iff S).2 fun x hx ↦ by
      change splittingModuleProjection C φ hφ x = 0 at hx
      change x.2 = 0 at hx
      refine ⟨x.1, ?_⟩
      change splittingModuleInclusion C φ hφ x.1 = x
      rw [splitting_module_inclusion]
      exact Prod.ext rfl hx.symm
  refine
    { exact := F.reflects_exact_of_faithful (splittingModuleSequence C φ hφ) hS
      mono_f := (Rep.mono_iff_injective _).2 fun x y h ↦ by
        change splittingModuleInclusion C φ hφ x =
          splittingModuleInclusion C φ hφ y at h
        rw [splitting_module_inclusion, splitting_module_inclusion] at h
        exact congrArg Prod.fst h
      epi_g := (Rep.epi_iff_surjective _).2 fun x ↦ by
        refine ⟨(0, x), ?_⟩
        rfl }

/-- Milne's cochain `σ ↦ x_σ`, in the `C ⊕ I_G` model. -/
noncomputable def splittingCochain (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    G → splittingModule C φ hφ :=
  fun g ↦ (0, augmentationClass G g)

/-- The chosen cocycle becomes the coboundary of `σ ↦ x_σ` in the
splitting module. -/
theorem splittingCochain_coboundary (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    d₁₂ (splittingModule C φ hφ) (splittingCochain C φ hφ) =
      fun p ↦ splittingModuleInclusion C φ hφ (φ p) := by
  funext p
  rw [splitting_module_inclusion]
  change
    splittingAction C φ p.1 (0, augmentationClass G p.2) -
        (0, augmentationClass G (p.1 * p.2)) +
        (0, augmentationClass G p.1) =
      (φ p, 0)
  apply Prod.ext
  · simp [splittingAction, splittingTwist_class C φ hφ]
  · simp [splittingAction]

/-- The class represented by `φ` maps to zero in `H²(G,C(φ))`. -/
theorem splitting_kills_cocycle (C : Rep ℤ G)
    (φ : cocycles₂ C) (hφ : φ (1, 1) = 0) :
    groupCohomology.map (MonoidHom.id G) (splittingModuleInclusion C φ hφ) 2
        (H2π C φ) = 0 := by
  rw [H2π_comp_map_apply, H2π_eq_zero_iff]
  refine ⟨splittingCochain C φ hφ, ?_⟩
  funext p
  rw [congrFun (splittingCochain_coboundary C φ hφ) p]
  rfl

/-- A normalized cocycle chosen to represent a specified degree-two class. -/
noncomputable def normalizedCocycleClass (C : Rep ℤ G) (gamma : H2 C) :
    cocycles₂ C :=
  (COps.normalized_cocycle_representation C gamma).choose

@[simp]
theorem normalized_cocycle_represents (C : Rep ℤ G) (gamma : H2 C) :
    H2π C (normalizedCocycleClass C gamma) = gamma :=
  (COps.normalized_cocycle_representation C gamma).choose_spec.1

@[simp]
theorem normalized_cocycle_class (C : Rep ℤ G) (gamma : H2 C) :
    normalizedCocycleClass C gamma (1, 1) = 0 :=
  (COps.normalized_cocycle_representation C gamma).choose_spec.2

/-- The splitting module attached to a chosen class `gamma`. -/
noncomputable abbrev splittingModuleClass (C : Rep ℤ G) (gamma : H2 C) :
    Rep ℤ G :=
  splittingModule C (normalizedCocycleClass C gamma)
    (normalized_cocycle_class C gamma)

/-- The chosen class itself maps to zero in its splitting module. -/
theorem splitting_module_kills (C : Rep ℤ G) (gamma : H2 C) :
    groupCohomology.map (MonoidHom.id G)
        (splittingModuleInclusion C (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma)) 2 gamma = 0 := by
  let f := groupCohomology.map (MonoidHom.id G)
    (splittingModuleInclusion C (normalizedCocycleClass C gamma)
      (normalized_cocycle_class C gamma)) 2
  calc
    f gamma = f (H2π C (normalizedCocycleClass C gamma)) := by
      rw [normalized_cocycle_represents]
    _ = 0 := splitting_kills_cocycle C
      (normalizedCocycleClass C gamma)
      (normalized_cocycle_class C gamma)

end

end Submission.CField.Shifting
