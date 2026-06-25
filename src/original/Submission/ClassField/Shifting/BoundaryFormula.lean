import Submission.ClassField.Shifting.Augmentation

/-!
# Milne, Class Field Theory, Theorem II.3.11: the boundary cocycle

For the splitting sequence, the connecting map sends the canonical class
represented by `h ↦ h - 1` in the augmentation ideal to the restriction of
the chosen two-cocycle.
-/

namespace Submission.CField.Shifting

open CategoryTheory Rep
open Submission.CField.TCohomo

noncomputable section

variable {G : Type} [Group G]

/-- Restriction of an inhomogeneous two-cocycle to a subgroup. -/
noncomputable def restrictedSplittingCocycle
    (C : Rep ℤ G) (H : Subgroup G) (φ : groupCohomology.cocycles₂ C) :
    groupCohomology.cocycles₂ (Rep.res H.subtype C) :=
  groupCohomology.mapCocycles₂ H.subtype (𝟙 _) φ

@[simp]
theorem restricted_splitting_cocycle
    (C : Rep ℤ G) (H : Subgroup G) (φ : groupCohomology.cocycles₂ C)
    (p : H × H) :
    restrictedSplittingCocycle C H φ p = φ ((p.1 : G), (p.2 : G)) :=
  rfl

/-- The explicit degree-one boundary calculation in Tate's proof. -/
theorem splitting_boundary_class
    (C : Rep ℤ G) (H : Subgroup G)
    (φ : groupCohomology.cocycles₂ C) (hφ : φ (1, 1) = 0) :
    groupCohomology.δ
        ((splitting_sequence_short C φ hφ).map_of_exact
          (Rep.resFunctor H.subtype)) 1 2 rfl
        (groupCohomology.H1π _ (restrictedAugmentationCocycle H)) =
      groupCohomology.H2π _ (restrictedSplittingCocycle C H φ) := by
  let X := (splittingModuleSequence C φ hφ).map
    (Rep.resFunctor H.subtype)
  let hX : X.ShortExact :=
    (splitting_sequence_short C φ hφ).map_of_exact
      (Rep.resFunctor H.subtype)
  let y : H → X.X₂ := fun h ↦ (0, augmentationClass G (h : G))
  let x : H × H → X.X₁ := fun p ↦ φ ((p.1 : G), (p.2 : G))
  have hy : X.g.hom ∘ y = restrictedAugmentationCocycle H := by
    funext h
    rfl
  have hx : X.f.hom ∘ x = groupCohomology.d₁₂ X.X₂ y := by
    funext p
    change (φ ((p.1 : G), (p.2 : G)), 0) = _
    simpa [X, y, x] using (congrFun
      (splittingCochain_coboundary C φ hφ) ((p.1 : G), (p.2 : G))).symm
  simpa [X, hX, x, restrictedSplittingCocycle] using
    groupCohomology.δ₁_apply hX (restrictedAugmentationCocycle H) y hy x hx

end

end Submission.CField.Shifting
