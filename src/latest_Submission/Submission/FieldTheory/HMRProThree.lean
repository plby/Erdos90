import Submission.FieldTheory.HMRInitialExtension
import Submission.FieldTheory.FiniteGeneration
import Submission.Group.ProPPresentation

/-!
# The initial HMR Galois group is pro-3

This file proves that the initial HMR Galois group is a pro-`3` group.
-/

open scoped Pointwise Topology

noncomputable section

namespace Submission
namespace TBluepr

set_option maxHeartbeats 800000 in
-- Expanding the finite-compositum restriction map and its Galois instances is elaboration-heavy.
set_option synthInstance.maxHeartbeats 100000 in
/-- The initial Galois group is a pro-`3` group. -/
theorem initial_pro_three :
    ProP.ProPGroup 3 initialGaloisGroup := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro N
  let H : ClosedSubgroup initialGaloisGroup :=
    { toSubgroup := N
      isClosed' := N.toOpenSubgroup.isClosed }
  letI : H.toSubgroup.Normal := by
    change (N : Subgroup initialGaloisGroup).Normal
    infer_instance
  let L : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField H.1
  have hfix : L.fixingSubgroup = H.1 := by
    exact InfiniteGalois.fixingSubgroup_fixedField H
  haveI : FiniteDimensional ℚ ↥L := by
    rw [← InfiniteGalois.isOpen_iff_finite L]
    rw [hfix]
    exact N.toOpenSubgroup.isOpen
  letI : IsGalois ℚ ↥L := by
    dsimp [L]
    exact IsGalois.of_fixedField_normal_subgroup H.1
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.lift L
  let eL' : ↥L ≃ₐ[ℚ] ↥L' :=
    IntermediateField.liftAlgEquiv L
  letI : FiniteDimensional ℚ ↥L' :=
    eL'.toLinearEquiv.finiteDimensional
  let 𝓔 :=
    {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
      IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes}
  let t : 𝓔 → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.toIntermediateField
  have hL'le : L' ≤ ⨆ E, t E := by
    simpa [L', t, initialProIntermediate] using
      (IntermediateField.lift_le L)
  obtain ⟨s, hs⟩ :=
    intermediate_fg_i L'
      (intermediate_fg_dimensional L') t hL'le
  let ι := {E : 𝓔 // E ∈ s}
  let u : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => t E.1
  let C : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    ⨆ E, u E
  have hL'C : L' ≤ C := by
    exact hs.trans <| iSup_le fun E => iSup_le fun hEs =>
      le_iSup_of_le (⟨E, hEs⟩ : ι) le_rfl
  letI : ∀ E : ι, FiniteDimensional ℚ ↥(u E) :=
    fun E => E.1.1.finiteDimensional
  letI huGalois : ∀ E : ι, IsGalois ℚ ↥(u E) :=
    fun E => E.1.1.isGalois
  letI : ∀ E : ι, Normal ℚ ↥(u E) :=
    fun E => (huGalois E).to_normal
  letI : ∀ E : ι, Algebra.IsSeparable ℚ ↥(u E) :=
    fun E => (huGalois E).to_isSeparable
  letI : FiniteDimensional ℚ ↥C := by
    dsimp [C]
    infer_instance
  letI : Normal ℚ ↥C := by
    dsimp [C]
    exact
      IntermediateField.normal_iSup ℚ (AlgebraicClosure ℚ) u
        (h := fun E => (huGalois E).to_normal)
  letI : Algebra.IsSeparable ℚ ↥C := by
    dsimp [C]
    exact
      IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := u)
        (h := fun E => IsGalois.to_isSeparable (F := ℚ) (E := ↥(u E)))
  letI : IsGalois ℚ ↥C := by
    exact ⟨⟩
  have hC : IsPGroup 3 (Gal(↥C/ℚ)) := by
    let v : ι → IntermediateField ℚ C :=
      fun E => (u E).restrict (le_iSup u E)
    letI : ∀ E : ι, FiniteDimensional ℚ ↥(v E) := fun E =>
      (IntermediateField.restrict_algEquiv (le_iSup u E)).toLinearEquiv.finiteDimensional
    letI hvGalois : ∀ E : ι, IsGalois ℚ ↥(v E) := fun E =>
      IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv (le_iSup u E))
    let φ : Gal(↥C/ℚ) →* (∀ E : ι, Gal(↥(v E)/ℚ)) :=
      Pi.monoidHom fun E => AlgEquiv.restrictNormalHom (v E)
    have hv : ∀ E : ι, IsPGroup 3 (Gal(↥(v E)/ℚ)) := by
      intro E
      let e : ↥(u E) ≃ₐ[ℚ] ↥(v E) :=
        IntermediateField.restrict_algEquiv (le_iSup u E)
      simpa [u, t] using E.1.2.1.of_equiv (AlgEquiv.autCongr e)
    have hPi : IsPGroup 3 (∀ E : ι, Gal(↥(v E)/ℚ)) :=
      p_pi_fintype hv
    apply hPi.of_injective φ
    refine (injective_iff_map_eq_one φ).mpr ?_
    intro σ hσ
    have htop : ⨆ E, v E = ⊤ := by
      apply (IntermediateField.lift_injective C)
      calc
        IntermediateField.lift (⨆ E, v E)
            = ⨆ E, IntermediateField.lift (v E) := by
                exact IntermediateField.map_iSup C.val v
        _ = C := by
          simp [v, C]
        _ = IntermediateField.lift (⊤ : IntermediateField ℚ C) := by
          exact (IntermediateField.lift_top ℚ C).symm
    have hfixing :
        (⨆ E, v E).fixingSubgroup = ⨅ E, (v E).fixingSubgroup := by
      apply le_antisymm
      · exact le_iInf fun E =>
          IntermediateField.fixingSubgroup_antitone (le_iSup v E)
      · rw [← IntermediateField.le_iff_le]
        exact iSup_le fun E => (IntermediateField.le_iff_le _ _).2 (iInf_le _ E)
    rw [← Subgroup.mem_bot, ← IntermediateField.fixingSubgroup_top, ← htop, hfixing]
    rw [Subgroup.mem_iInf]
    intro E
    letI : Normal ℚ ↥(v E) := (hvGalois E).to_normal
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσE : AlgEquiv.restrictNormalHom (v E) σ = 1 := by
      exact congrFun hσ E
    have hσx :=
      congrArg (fun τ : Gal(↥(v E)/ℚ) => τ ⟨x, hx⟩) hσE
    have hσx' := congrArg Subtype.val hσx
    dsimp [AlgEquiv.restrictNormalHom, AlgEquiv.restrictNormal,
      AlgHom.restrictNormal'] at hσx'
    have hcomm :
        ↑((σ.restrictNormal ↥(v E)) ⟨x, hx⟩) = σ x := by
      exact AlgEquiv.restrictNormal_commutes (χ := σ) (E := v E) ⟨x, hx⟩
    exact hcomm.symm.trans hσx'
  let R : IntermediateField ℚ C :=
    L'.restrict hL'C
  let eL : ↥L ≃ₐ[ℚ] ↥R :=
    eL'.trans (IntermediateField.restrict_algEquiv hL'C)
  letI : IsGalois ℚ ↥R := IsGalois.of_algEquiv eL
  have hR : IsPGroup 3 (Gal(↥R/ℚ)) :=
    hC.of_surjective (AlgEquiv.restrictNormalHom R)
      (AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥R) (E := ↥C))
  have hL : IsPGroup 3 (Gal(↥L/ℚ)) :=
    hR.of_equiv (AlgEquiv.autCongr eL).symm
  simpa [H, L] using
    hL.of_equiv (galoisFixedField H).symm

end TBluepr
end Submission
