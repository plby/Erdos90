import Submission.ClassField.Shifting.Augmentation
import Submission.ClassField.Shifting.Exceptional

/-!
# Milne, Class Field Theory, Theorem II.3.11: assembling the shifts

This file assembles every Tate range represented in the project.  The only
remaining input is the arithmetic assertion that, after restriction to every
subgroup, the splitting-sequence boundary `H¹(I_G) → H²(C)` is an
isomorphism.
-/

namespace Submission.CField.Shifting

open AddSubgroup CategoryTheory CategoryTheory.Limits Rep

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- The range-wise form of a two-degree Tate shift, using ordinary
cohomology in positive degrees and ordinary homology below degree `-1`. -/
structure TateTwoShift (C : Rep ℤ G) where
  positive : ∀ n : ℕ, 0 < n →
    groupCohomology (Rep.trivial ℤ G ℤ) n ≃+ groupCohomology C (n + 2)
  zero : tateCohomologyZero (Rep.trivial ℤ G ℤ) ≃+
    groupCohomology C 2
  negOne : tateCohomologyOne (Rep.trivial ℤ G ℤ) ≃+
    groupCohomology C 1
  negTwo : groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+
    tateCohomologyZero C
  negThree : groupHomology (Rep.trivial ℤ G ℤ) 2 ≃+
    tateCohomologyOne C
  lower : ∀ n : ℕ, 0 < n →
    groupHomology (Rep.trivial ℤ G ℤ) (n + 2) ≃+ groupHomology C n

/-- Theorem II.3.11 after isolating its one remaining arithmetic boundary
calculation.  All six represented Tate ranges are genuine equivalences. -/
noncomputable def restricted_boundary_iso
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcard : Nat.card (groupCohomology C 2) = Fintype.card G)
    (hC1self : IsZero (groupCohomology C 1))
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        ((splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma)).map_of_exact
            (Rep.resFunctor H.subtype)) 1 2 rfl)) :
    TateTwoShift C := by
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let X := splittingModuleSequence C φ hφ
  let Y := augmentationSequence (G := G)
  have hX : X.ShortExact := splitting_sequence_short C φ hφ
  have hY : Y.ShortExact := augmentation_short_exact
  have hE12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
        IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 2) := by
    apply splitting_12_iso C φ hφ hC1
      cohomology_restrict_ideal
    simpa [φ, hφ] using hboundary
  have hE := allDegrees (splittingModule C φ hφ) hE12
  have hregular12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (Rep.leftRegular ℤ G)) 1) ∧
      IsZero (groupCohomology
          (Rep.res H.subtype (Rep.leftRegular ℤ G)) 2) := fun H ↦
    ⟨restrict_int_acyclic H 1 Nat.zero_lt_one,
      restrict_int_acyclic H 2 (by omega)⟩
  have hregular := allDegrees (Rep.leftRegular ℤ G) hregular12
  have hpositive (n : ℕ) (hn : 0 < n) :
      groupCohomology (Rep.trivial ℤ G ℤ) n ≃+
        groupCohomology C (n + 2) := by
    let e := positiveDoubleShift
        (splitting_sequence_short C φ hφ)
        (augmentation_short_exact (G := G)) (Iso.refl _)
        hE.1 hregular.1 n hn
    simpa [splittingModuleSequence, augmentationSequence] using
      e.toLinearEquiv.toAddEquiv
  have hlower (n : ℕ) (hn : 0 < n) :
      groupHomology (Rep.trivial ℤ G ℤ) (n + 2) ≃+
        groupHomology C n := by
    let e := homologyDoubleShift
        (splitting_sequence_short C φ hφ)
        (augmentation_short_exact (G := G)) (Iso.refl _)
        hE.2.2.2 hregular.2.2.2 n hn
    simpa [splittingModuleSequence, augmentationSequence] using
      e.toLinearEquiv.toAddEquiv
  refine
    { positive := hpositive
      zero := (tateZeroGenerator G C gamma hgamma hcard).toAddEquiv
      negOne := (tateNegEquiv G C hC1self).toAddEquiv
      negTwo := ?_
      negThree := ?_
      lower := hlower }
  · let e1 := homologyNegShort Y hY
      (hregular.2.2.2 1 Nat.zero_lt_one) hregular.2.2.1
    let e2 := isoShortExact X hX hE.2.2.1 hE.2.1
    let e : groupHomology Y.X₃ 1 ≃+ tateCohomologyZero X.X₁ :=
      { toFun := fun x ↦ e2 (e1 x)
        invFun := fun x ↦ e1.symm (e2.symm x)
        left_inv := fun x ↦ by simp
        right_inv := fun x ↦ by simp
        map_add' := fun x y ↦ by
          rw [map_add]
          exact e2.map_add (e1 x) (e1 y) }
    simpa [X, Y, splittingModuleSequence, augmentationSequence] using
      e
  · let e1 := homologyShiftingIso hY hregular.2.2.2 1
      Nat.zero_lt_one
    let e2 := homologyNegShort X hX
      (hE.2.2.2 1 Nat.zero_lt_one) hE.2.2.1
    let e : groupHomology Y.X₃ 2 ≃+ tateCohomologyOne X.X₁ :=
      { toFun := fun x ↦ e2 (e1.hom x)
        invFun := fun x ↦ e1.inv (e2.symm x)
        left_inv := fun x ↦ by simp
        right_inv := fun x ↦ by simp
        map_add' := fun x y ↦ by
          rw [map_add]
          exact e2.map_add (e1.hom x) (e1.hom y) }
    simpa [X, Y, splittingModuleSequence, augmentationSequence] using
      e

end

end Submission.CField.Shifting
