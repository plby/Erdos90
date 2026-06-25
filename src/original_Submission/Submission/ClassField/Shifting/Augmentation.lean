import Submission.ClassField.Shifting.SplittingModule
import Submission.ClassField.Shifting.AdditiveHomZero

/-!
# Milne, Class Field Theory, Theorem II.3.11: the augmentation sequence

This file records the augmentation-ideal calculation used in Tate's proof.
The integral group ring, with its left regular action, fits into the short
exact sequence

`0 -> I_G -> Z[G] -> Z -> 0`.

After restriction to a subgroup, the middle term is still coinduced from the
trivial subgroup.  Consequently it is cohomologically acyclic in positive
degrees, and dimension shifting gives `H^2(H, Res I_G) = 0`.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep
open groupCohomology
open Submission.CField.TCohomo

noncomputable section

variable {G : Type} [Group G]

/-- The left regular action is left multiplication in the integral group ring. -/
theorem regular_int_action (g : G) (x : IntegralGroupRing G) :
    (Rep.leftRegular ℤ G).ρ g x = MonoidAlgebra.single g 1 * x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      calc
        (Rep.leftRegular ℤ G).ρ g 0 = 0 := map_zero _
        _ = MonoidAlgebra.single g (1 : ℤ) * 0 :=
          (mul_zero (MonoidAlgebra.single g (1 : ℤ))).symm
  | add x y hx hy =>
      calc
        (Rep.leftRegular ℤ G).ρ g (x + y) =
            (Rep.leftRegular ℤ G).ρ g x +
              (Rep.leftRegular ℤ G).ρ g y := map_add _ _ _
        _ = MonoidAlgebra.single g (1 : ℤ) * x +
              MonoidAlgebra.single g (1 : ℤ) * y := by
          rw [hx, hy]
          rfl
        _ = MonoidAlgebra.single g (1 : ℤ) * (x + y) :=
          (mul_add (MonoidAlgebra.single g (1 : ℤ)) x y).symm
  | single h n =>
      rw [Representation.ofMulAction_single]
      symm
      simpa only [one_mul] using
        (MonoidAlgebra.single_mul_single g h (1 : ℤ) n)

/-- Augmentation is invariant under the left regular action. -/
theorem augmentation_regular_action (g : G)
    (x : IntegralGroupRing G) :
    augmentation G ((Rep.leftRegular ℤ G).ρ g x) = augmentation G x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      exact congrArg (augmentation G)
        (map_zero ((Rep.leftRegular ℤ G).ρ g))
  | add x y hx hy =>
      calc
        augmentation G ((Rep.leftRegular ℤ G).ρ g (x + y)) =
            augmentation G ((Rep.leftRegular ℤ G).ρ g x +
              (Rep.leftRegular ℤ G).ρ g y) :=
          congrArg (augmentation G) (map_add _ x y)
        _ = augmentation G ((Rep.leftRegular ℤ G).ρ g x) +
              augmentation G ((Rep.leftRegular ℤ G).ρ g y) :=
          map_add (augmentation G) _ _
        _ = augmentation G x + augmentation G y :=
          congrArg₂ (fun a b : ℤ ↦ a + b) hx hy
        _ = augmentation G (x + y) := (map_add (augmentation G) x y).symm
  | single h n =>
      rw [Representation.ofMulAction_single, augmentation_single,
        augmentation_single]

/-- The inclusion of the augmentation ideal into the integral regular
representation. -/
noncomputable def augmentationIdealInclusion :
    augmentationIdealRep (G := G) ⟶ Rep.leftRegular ℤ G :=
  Rep.ofHom
    { toLinearMap := (augmentationIdeal G).subtype
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro x
        change
          ((augmentationLeftAction g x : augmentationIdeal G) :
              IntegralGroupRing G) =
            (Rep.leftRegular ℤ G).ρ g x.1
        rw [augmentation_action_coe, regular_int_action]
        rfl }

/-- Augmentation as an equivariant map from the integral regular
representation to the trivial integers. -/
noncomputable def regularAugmentation :
    Rep.leftRegular ℤ G ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom
    { toLinearMap := augmentation G
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro x
        change augmentation G ((Rep.leftRegular ℤ G).ρ g x) =
          augmentation G x
        exact augmentation_regular_action g x }

/-- The equivariant augmentation complex `I_G -> Z[G] -> Z`. -/
noncomputable def augmentationSequence : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (augmentationIdealInclusion (G := G))
    (regularAugmentation (G := G)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact LinearMap.mem_ker.mp x.2)

/-- The augmentation complex is short exact. -/
theorem augmentation_short_exact :
    (augmentationSequence (G := G)).ShortExact := by
  letI repModule (X : Rep.{0} ℤ G) : Module ℤ X := X.hV2
  let F : Functor (Rep.{0} ℤ G) (ModuleCat.{0} ℤ) :=
    forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)
  let S : ShortComplex (ModuleCat.{0} ℤ) :=
    (augmentationSequence (G := G)).map F
  have hS : S.Exact := (ShortComplex.moduleCat_exact_iff S).2 fun x hx ↦ by
    change regularAugmentation (G := G) x = 0 at hx
    refine ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, rfl⟩
  refine
    { exact := F.reflects_exact_of_faithful (augmentationSequence (G := G)) hS
      mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
      epi_g := (Rep.epi_iff_surjective _).2 fun n ↦
        ⟨MonoidAlgebra.single 1 n, augmentation_single G 1 n⟩ }

/-- Restriction preserves the short exact augmentation sequence. -/
theorem restrict_short_exact [Finite G]
    (H : Subgroup G) :
    ((augmentationSequence (G := G)).map
      (Rep.resFunctor H.subtype)).ShortExact :=
  augmentation_short_exact.map_of_exact (Rep.resFunctor H.subtype)

/-- As an `H`-module, the integral regular representation of `G` is
coinduced from the trivial subgroup of `H`, with one coefficient for every
right coset of `H` in `G`. -/
noncomputable def restrictIsoCoind [Finite G]
    (H : Subgroup G) :
    Rep.res H.subtype (Rep.leftRegular ℤ G) ≅
      Rep.coind (⊥ : Subgroup H).subtype
        (Rep.trivial ℤ (⊥ : Subgroup H)
          (↥((default : H.RightTransversal) : Set G) →₀ ℤ)) :=
  (Rep.resFunctor H.subtype).mapIso (ρ_ (Rep.leftRegular ℤ G)).symm ≪≫
    COps.restrictRegularIso H default ℤ ≪≫
    (COps.coindRegularTensor
      (↥((default : H.RightTransversal) : Set G) →₀ ℤ)).symm

/-- The restricted integral regular module has zero positive-degree
cohomology. -/
theorem restrict_int_acyclic [Finite G]
    (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (Rep.leftRegular ℤ G)) n) := by
  let B := Rep.trivial ℤ (⊥ : Subgroup H)
    (↥((default : H.RightTransversal) : Set G) →₀ ℤ)
  have htarget : IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup H).subtype B) n) :=
    COps.zero_cohomology_coinduced B n hn
  exact htarget.of_iso
    ((groupCohomology.functor ℤ H n).mapIso
      (restrictIsoCoind H))

/-- The restricted integral regular module also has zero positive-degree
homology. -/
theorem restrict_regular_acyclic [Finite G]
    (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupHomology
      (Rep.res H.subtype (Rep.leftRegular ℤ G)) n) := by
  let B := Rep.trivial ℤ (⊥ : Subgroup H)
    (↥((default : H.RightTransversal) : Set G) →₀ ℤ)
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup H)) :=
    Classical.decRel _
  let e : Rep.res H.subtype (Rep.leftRegular ℤ G) ≅
      Rep.ind (⊥ : Subgroup H).subtype B :=
    restrictIsoCoind H ≪≫ (Rep.indCoindIso B).symm
  have htarget : IsZero
      (groupHomology (Rep.ind (⊥ : Subgroup H).subtype B) n) :=
    zero_homology_induced B n hn
  exact htarget.of_iso ((groupHomology.functor ℤ H n).mapIso e)

/-- The restricted augmentation ideal has vanishing second cohomology. -/
theorem cohomology_restrict_ideal [Finite G]
    (H : Subgroup G) :
    IsZero (groupCohomology
      (Rep.res H.subtype (augmentationIdealRep (G := G))) 2) := by
  have hshift := COps.dimensionShiftingIso
    (restrict_short_exact H)
    (restrict_int_acyclic H) 1 Nat.zero_lt_one
  have hzero : IsZero
      (groupCohomology (Rep.trivial ℤ H ℤ) 1) :=
    cohomology_trivial_int H
  exact hzero.of_iso hshift.symm

/-- The canonical one-cocycle `h ↦ h - 1` with values in the restricted
augmentation ideal. -/
noncomputable def restrictedAugmentationCocycle (H : Subgroup G) :
    cocycles₁ (Rep.res H.subtype (augmentationIdealRep (G := G))) :=
  ⟨fun h ↦ augmentationClass G (h : G),
    (mem_cocycles₁_iff _).2 fun h j ↦ by
      change augmentationClass G ((h * j : H) : G) =
        augmentationLeftAction (h : G)
            (augmentationClass G (j : G)) +
          augmentationClass G (h : G)
      rw [augmentation_action_class]
      simp⟩

end

end Submission.CField.Shifting
