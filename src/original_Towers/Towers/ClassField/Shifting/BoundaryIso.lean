import Towers.ClassField.Shifting.AugmentationH1
import Towers.ClassField.Shifting.RestrictionGenerator
import Towers.ClassField.Shifting.ShapiroNaturality

/-!
# Milne, Class Field Theory, Theorem II.3.11: the boundary isomorphism

This file completes the arithmetic heart of Tate's proof.  Shapiro
restriction carries the chosen global generator to a generator for every
subgroup, naturality shows that this generator dies in the splitting module,
and the long exact sequence makes the boundary surjective.  The explicit
augmentation class then supplies injectivity.
-/

namespace Towers.CField.Shifting

open AddSubgroup CategoryTheory CategoryTheory.Limits Rep

noncomputable section

variable {G : Type} [Group G] [Finite G]

set_option maxHeartbeats 5000000 in
-- Elaborating the finite cohomology carriers through Shapiro's maps is expensive.
/-- The Shapiro restriction of the chosen global class generates subgroup
cohomology, by `Cor ∘ Res = [G:H]` and the order hypotheses. -/
theorem shapiroRestriction_generates
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (H : Subgroup G) :
    ∀ x : groupCohomology (Rep.res H.subtype C) 2,
      x ∈ zmultiples
        (COps.shapiroRestriction C H 2 gamma) := by
  let r : groupCohomology C 2 →+
      groupCohomology (Rep.res H.subtype C) 2 :=
    (COps.shapiroRestriction C H 2).hom.toAddMonoidHom
  let c : groupCohomology (Rep.res H.subtype C) 2 →+
      groupCohomology C 2 :=
    (COps.corestriction C H 2).hom.toAddMonoidHom
  have hindex : Nat.card (groupCohomology C 2) =
      H.index * Nat.card (groupCohomology (Rep.res H.subtype C) 2) := by
    rw [hcardG, hcardH H, H.index_mul_card]
  have hcorres : c (r gamma) = H.index • gamma := by
    simpa [r, c] using congrArg
      (fun q : groupCohomology C 2 ⟶ groupCohomology C 2 ↦ q gamma)
      (COps.shapiro_restriction_corestriction C H 2)
  letI : Finite (groupCohomology C 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact Nat.card_pos.ne')
  letI : Finite (groupCohomology (Rep.res H.subtype C) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH H]; exact Nat.card_pos.ne')
  exact generator_corestriction_restriction r c H.index
    (Nat.zero_lt_of_ne_zero H.index_ne_zero_of_finite)
    hindex gamma hgamma hcorres

/-- After restriction to a subgroup, the coefficient map from `C` to its
splitting module is zero in degree two. -/
theorem restricted_splitting_inclusion
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (H : Subgroup G) :
    (groupCohomology.functor ℤ H 2).map
        ((Rep.resFunctor H.subtype).map
          (splittingModuleInclusion C (normalizedCocycleClass C gamma)
            (normalized_cocycle_class C gamma))) = 0 := by
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let f := splittingModuleInclusion C φ hφ
  let mH := (groupCohomology.functor ℤ H 2).map
    ((Rep.resFunctor H.subtype).map f)
  let mG := groupCohomology.map (MonoidHom.id G) f 2
  let sC := COps.shapiroRestriction C H 2
  let sE := COps.shapiroRestriction (splittingModule C φ hφ) H 2
  have hnat : sC ≫ mH = mG ≫ sE := by
    simpa [f, mH, mG, sC, sE] using
      shapiroRestriction_naturality H f 2
  have hkill : mG gamma = 0 := by
    simpa [mG, f, φ, hφ] using splitting_module_kills C gamma
  have hgenerator := shapiroRestriction_generates C gamma hgamma hcardG hcardH H
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, hz⟩ := hgenerator x
  change z • sC gamma = x at hz
  have hvalue : mH (sC gamma) = 0 := by
    calc
      mH (sC gamma) = (sC ≫ mH) gamma := rfl
      _ = (mG ≫ sE) gamma := congrArg (fun q ↦ q gamma) hnat
      _ = sE (mG gamma) := rfl
      _ = 0 := by rw [hkill, map_zero]
  let mHa := mH.hom.toAddMonoidHom
  change mHa x = 0
  calc
    mHa x = mHa (z • sC gamma) := congrArg mHa hz.symm
    _ = z • mHa (sC gamma) := map_zsmul mHa z _
    _ = 0 := by rw [show mHa (sC gamma) = 0 from hvalue, zsmul_zero]

set_option maxHeartbeats 5000000 in
-- The boundary type unfolds two restricted short exact sequences.
/-- The restricted splitting boundary `H¹(I_G) → H²(C)` is an
isomorphism under Milne's cyclic-order hypotheses. -/
theorem splitting_boundary_iso
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (H : Subgroup G) :
    IsIso (groupCohomology.δ
      ((splitting_sequence_short C
        (normalizedCocycleClass C gamma)
        (normalized_cocycle_class C gamma)).map_of_exact
          (Rep.resFunctor H.subtype)) 1 2 rfl) := by
  letI : Fintype H := Fintype.ofFinite H
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let X := (splittingModuleSequence C φ hφ).map
    (Rep.resFunctor H.subtype)
  let hX : X.ShortExact :=
    (splitting_sequence_short C φ hφ).map_of_exact
      (Rep.resFunctor H.subtype)
  let d := groupCohomology.δ hX 1 2 rfl
  let S := groupCohomology.mapShortComplex₁ hX (i := 1) (j := 2) rfl
  have hS : S.Exact := groupCohomology.mapShortComplex₁_exact hX rfl
  have hnext : S.g = 0 := by
    change (groupCohomology.functor ℤ H 2).map
      ((Rep.resFunctor H.subtype).map
        (splittingModuleInclusion C φ hφ)) = 0
    simpa [φ, hφ] using
      restricted_splitting_inclusion C gamma hgamma hcardG hcardH H
  letI : Epi d := hS.epi_f hnext
  have hsurj : Function.Surjective d :=
    (ModuleCat.epi_iff_surjective d).1 inferInstance
  have hfinite : Finite (groupCohomology (Rep.res H.subtype C) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH H]; exact Nat.card_pos.ne')
  letI : Finite (groupCohomology (Rep.res H.subtype C) 2) := hfinite
  letI : Finite (groupCohomology X.X₁ 2) := by
    change Finite (groupCohomology (Rep.res H.subtype C) 2)
    infer_instance
  have ha : ∀ x : groupCohomology
      (Rep.res H.subtype (augmentationIdealRep (G := G))) 1,
      x ∈ zmultiples (restrictedAugmentationClass H) := by
    intro x
    obtain ⟨z, hz⟩ := restricted_augmentation_generates H x
    exact ⟨z, hz.symm⟩
  have hb := shapiroRestriction_generates C gamma hgamma hcardG hcardH H
  have hann : Nat.card (groupCohomology (Rep.res H.subtype C) 2) •
      restrictedAugmentationClass H = 0 := by
    rw [hcardH H]
    simpa [Nat.card_eq_fintype_card] using
      card_smul_restricted H
  have hbij : Function.Bijective d :=
    bijective_surjective_annihilated
      d.hom.toAddMonoidHom (restrictedAugmentationClass H)
      (COps.shapiroRestriction C H 2 gamma)
      ha hb hann hsurj
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hbij

end

end Towers.CField.Shifting
