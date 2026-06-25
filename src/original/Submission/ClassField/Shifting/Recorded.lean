import Submission.ClassField.Shifting.AssemblingTensorShift
import Submission.ClassField.Shifting.BoundaryIso

/-!
# Milne, Class Field Theory, Remark II.3.12

Tensoring Tate's four-term sequence with a `G`-module `M` gives a two-degree
Tate shift from `M` to `M ⊗ C`, provided `Tor₁ᶻ(M,C)` vanishes.  The
construction below uses the exact tensorized sequences, the induced-module
description of their regular middle term, and the standard tensor-acyclicity
lemma recorded in `Remark312Acyclic`.
-/

namespace Submission.CField.Shifting

open AddSubgroup CategoryTheory CategoryTheory.Limits MonoidalCategory Rep

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- **Remark II.3.12.** Under Tate's hypotheses on `C`, vanishing of the
underlying integral `Tor₁(M,C)` gives isomorphisms
`H_T^r(G,M) ≅ H_T^(r+2)(G,M ⊗ C)` in every Tate range represented by the
project. -/
noncomputable def dimensionShiftingRecord
    (M C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (hTor : TorOneVanishes M C) :
    TSCoeffi M (M ⊗ C) := by
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let F := (tensoringLeft (Rep ℤ G)).obj M
  let X := (splittingModuleSequence C φ hφ).map F
  let Y := (augmentationSequence (G := G)).map F
  have hX : X.ShortExact := by
    simpa [X, F] using splitting_short_exact M C φ hφ
  have hY : Y.ShortExact := by
    simpa [Y, F] using tensor_sequence_short (G := G) M
  have hE12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
        IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 2) := by
    apply splitting_12_iso C φ hφ
      hC1 cohomology_restrict_ideal
    intro H
    simpa [φ, hφ] using
      (splitting_boundary_iso C gamma hgamma hcardG hcardH H)
  have hXAcyclic : TateAcyclic X.X₂ := by
    simpa [X, F, splittingModuleSequence] using
      (tensorSplittingModule_tateAcyclic_of_torOne M C φ hφ hE12 hTor)
  have hYAcyclic : TateAcyclic Y.X₂ := by
    simpa [Y, F, augmentationSequence] using tensor_regular_acyclic M
  let e : Y.X₁ ≅ X.X₃ := Iso.refl _
  let s := shiftSplicedShort hX hY e hXAcyclic hYAcyclic
  let sourceIso : M ≅ Y.X₃ := by
    simpa [Y, F, augmentationSequence] using (ρ_ M).symm
  simpa [X, splittingModuleSequence] using s.transSource sourceIso

end

end Submission.CField.Shifting
