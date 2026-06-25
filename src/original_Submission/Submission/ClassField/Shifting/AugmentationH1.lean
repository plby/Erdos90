import Submission.ClassField.Shifting.Augmentation

/-!
# Milne, Class Field Theory, Theorem II.3.11: the augmentation class in H¹

For a subgroup `H` of a finite group `G`, the class of the cocycle
`h ↦ h - 1` generates `H¹(H, I_G)`.  Its order divides `|H|`.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep
open groupCohomology
open Submission.CField.TCohomo

noncomputable section

variable {G : Type} [Group G]

/-- The augmentation sequence restricted to `H`, with its three carriers
kept definitionally explicit. -/
noncomputable def restrictedAugmentationSequence (H : Subgroup G) :
    ShortComplex (Rep ℤ H) :=
  ShortComplex.mk
    ((Rep.resFunctor H.subtype).map (augmentationIdealInclusion (G := G)))
    ((Rep.resFunctor H.subtype).map (regularAugmentation (G := G)))
    (by
      simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
        using congrArg (Rep.resFunctor H.subtype).map
          (augmentationSequence (G := G)).zero)

/-- The concretely presented restricted augmentation sequence is short
exact. -/
theorem restricted_short_exact [Finite G]
    (H : Subgroup G) :
    (restrictedAugmentationSequence H).ShortExact := by
  simpa only [restrictedAugmentationSequence, augmentationSequence] using
    restrict_short_exact H

/-- The class in `H¹(H, I_G)` represented by the cocycle `h ↦ h - 1`. -/
noncomputable def restrictedAugmentationClass (H : Subgroup G) :
    groupCohomology
      (Rep.res H.subtype (augmentationIdealRep (G := G))) 1 :=
  H1π _ (restrictedAugmentationCocycle H)

/-- The connecting map of the restricted augmentation sequence sends `1`
to the canonical augmentation class. -/
theorem restricted_augmentation_boundary [Finite G] (H : Subgroup G) :
    let X := restrictedAugmentationSequence H
    let z : X.X₃.ρ.invariants := ⟨(1 : ℤ), by
      intro h
      rfl⟩
    groupCohomology.δ (restricted_short_exact H)
        0 1 rfl ((H0Iso X.X₃).inv z) =
      restrictedAugmentationClass H := by
  dsimp only
  let X := restrictedAugmentationSequence H
  let z : X.X₃.ρ.invariants := ⟨(1 : ℤ), by
    intro h
    rfl⟩
  let y : X.X₂ := (MonoidAlgebra.single 1 1 : IntegralGroupRing G)
  let x : H → X.X₁ := fun h ↦ augmentationClass G (h : G)
  have hy : X.g.hom y = z := by
    change augmentation G
      (MonoidAlgebra.single 1 1 : IntegralGroupRing G) = (1 : ℤ)
    exact augmentation_one G
  have hx : X.f.hom ∘ x = d₀₁ X.X₂ y := by
    funext h
    dsimp [X, x, y, restrictedAugmentationSequence, d₀₁,
      augmentationIdealInclusion]
    change
      (augmentationIdeal G).subtype (augmentationClass G (h : G)) =
        (show IntegralGroupRing G from
          (Rep.leftRegular ℤ G).ρ (h : G)
            (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) -
          (MonoidAlgebra.single 1 1 : IntegralGroupRing G)
    rw [Representation.ofMulAction_single]
    simpa only [smul_eq_mul, mul_one] using
      augmentationClass_coe (G := G) (h : G)
  simpa only [restrictedAugmentationClass, X, z, x] using
    (groupCohomology.δ₀_apply
      (restricted_short_exact H) z y hy x hx)

/-- The canonical augmentation class generates `H¹(H, I_G)` as a
`ℤ`-module. -/
theorem restricted_augmentation_generates [Finite G] (H : Subgroup G)
    (c : groupCohomology
      (Rep.res H.subtype (augmentationIdealRep (G := G))) 1) :
    ∃ n : ℤ, c = n • restrictedAugmentationClass H := by
  let X := restrictedAugmentationSequence H
  let hX : X.ShortExact := restricted_short_exact H
  let d := groupCohomology.δ hX 0 1 rfl
  letI : Epi d := groupCohomology.epi_δ_of_isZero hX 0
    (restrict_int_acyclic H 1 Nat.zero_lt_one)
  obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective d).1 inferInstance c
  let one : X.X₃.ρ.invariants := ⟨(1 : ℤ), by
    intro h
    rfl⟩
  let n : ℤ := ((H0Iso X.X₃).hom u).1
  have hu' : u = n • (H0Iso X.X₃).inv one := by
    apply (ModuleCat.mono_iff_injective (H0Iso X.X₃).hom).1 inferInstance
    apply Subtype.ext
    rw [map_zsmul, Iso.inv_hom_id_apply]
    change n = n • (1 : ℤ)
    exact (zsmul_one n).symm
  refine ⟨n, ?_⟩
  rw [← hu, hu']
  change d.hom (n • (H0Iso X.X₃).inv one) = _
  rw [map_zsmul]
  exact congrArg (n • ·) (restricted_augmentation_boundary H)

/-- The order of the canonical augmentation class divides the order of
`H`. -/
theorem card_smul_restricted [Finite G]
    (H : Subgroup G) [Fintype H] :
    (Fintype.card H : ℤ) • restrictedAugmentationClass H = 0 := by
  let X := restrictedAugmentationSequence H
  let hX : X.ShortExact := restricted_short_exact H
  let d := groupCohomology.δ hX 0 1 rfl
  let one : X.X₃.ρ.invariants := ⟨(1 : ℤ), by
    intro h
    rfl⟩
  let m : ℤ := Fintype.card H
  let z : X.X₃.ρ.invariants := ⟨m, by
    intro h
    rfl⟩
  let y : X.X₂ := X.X₂.ρ.norm
    (MonoidAlgebra.single 1 1 : IntegralGroupRing G)
  let x : H → X.X₁ := 0
  have hy : X.g.hom y = z := by
    change augmentation G
      (X.X₂.ρ.norm (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) = m
    rw [Representation.norm, LinearMap.sum_apply]
    have hterm (h : H) : augmentation G
        (X.X₂.ρ h (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) = 1 := by
      change augmentation G
        ((Rep.leftRegular ℤ G).ρ (h : G)
          (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) = 1
      rw [augmentation_regular_action]
      exact augmentation_one G
    calc
      augmentation G
          (∑ h : H, X.X₂.ρ h
            (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) =
          ∑ h : H, augmentation G
            (X.X₂.ρ h
              (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) := by
        exact _root_.map_sum (augmentation G) _ Finset.univ
      _ = ∑ _h : H, (1 : ℤ) := by simp only [hterm]
      _ = m := by simp [m]
  have hx : X.f.hom ∘ x = d₀₁ X.X₂ y := by
    funext h
    change (0 : IntegralGroupRing G) = X.X₂.ρ h y - y
    simp [y]
    rfl
  have hdelta : d.hom ((H0Iso X.X₃).inv z) = 0 := by
    have hcoc :
        (⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ :
          cocycles₁ X.X₁) = 0 := by
      ext h
      rfl
    have hboundary := groupCohomology.δ₀_apply hX z y hy x hx
    change d.hom ((H0Iso X.X₃).inv z) =
      H1π X.X₁
        ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ at hboundary
    rw [hcoc, map_zero] at hboundary
    exact hboundary
  have hz : z = m • one := by
    apply Subtype.ext
    change m = m • (1 : ℤ)
    exact (zsmul_one m).symm
  calc
    (Fintype.card H : ℤ) • restrictedAugmentationClass H =
        m • d.hom ((H0Iso X.X₃).inv one) := by
          exact congrArg (m • ·) (restricted_augmentation_boundary H).symm
    _ = d.hom (m • (H0Iso X.X₃).inv one) := (map_zsmul d.hom m _).symm
    _ = d.hom ((H0Iso X.X₃).inv (m • one)) :=
      congrArg d.hom (map_zsmul (H0Iso X.X₃).inv.hom m one).symm
    _ = d.hom ((H0Iso X.X₃).inv z) := by rw [hz]
    _ = 0 := hdelta

end

end Submission.CField.Shifting
