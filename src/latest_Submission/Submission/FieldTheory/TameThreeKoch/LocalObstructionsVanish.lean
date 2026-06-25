import Submission.FieldTheory.TameThreeKoch.ObstructionPrimeS


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v w

open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The proof synthesizes several finite-place, residue-field, and cohomological instances.
set_option maxHeartbeats 50000000 in
-- Constructing all global and local tame data remains the expensive part of this declaration.
theorem cft_obstructions_vanish
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (pi : E →* A)
    (hpi : Function.Surjective pi)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : pi.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card pi.ker = 3)
    (alphaE : free.Carrier →* E)
    (halphaE : Continuous alphaE)
    (hkill :
      ∀ i : Fin d,
        alphaE
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE) :
    cft_obstructions_statement
      hsetup pi hpi hE hA hkernel_central hkernel_card
        alphaE halphaE hkill betaA hcompat := by
  unfold cft_obstructions_statement
  have hbetaA : Continuous betaA :=
    rational_compatible_continuous
      hsetup pi alphaE halphaE betaA hcompat
  let N : OpenNormalSubgroup (rationalTameGalois S) :=
    rational_tame_open betaA hbetaA
  let L := rationalTameLayer S N
  let q := centralPreimageProjection pi betaA.range
  let hq : Function.Surjective q :=
    preimage_projection_surjective pi hpi betaA.range
  let hc : q.ker ≤ Subgroup.center (centralExtensionPreimage pi betaA.range) :=
    extension_preimage_projection
      pi betaA.range hkernel_central
  letI : CommGroup q.ker := centralExtensionComm q hc
  let M := rationalTameCompositum S N
  let L0 := rationalLayerClosure S N
  let Lc : IntermediateField ℚ M := L0.restrict le_sup_left
  let Kc : IntermediateField ℚ M :=
    rationalCubeField.restrict le_sup_right
  have hsup : Lc ⊔ Kc = ⊤ := by
    apply (IntermediateField.lift_inj (Lc ⊔ Kc) ⊤).mp
    rw [IntermediateField.lift_sup ℚ M Lc Kc,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top ℚ M]
    rfl
  have hLcGalois : IsGalois ℚ Lc := by
    let hsource : IsGalois ℚ L0 :=
      instGaloisClosure S N
    exact @IsGalois.of_algEquiv ℚ L0 inferInstance inferInstance Lc
      inferInstance inferInstance inferInstance hsource
      (IntermediateField.restrict_algEquiv
        (show L0 ≤ M from le_sup_left))
  let eLc : L0 ≃ₐ[ℚ] Lc :=
    IntermediateField.restrict_algEquiv
      (show L0 ≤ M from le_sup_left)
  let hLcFinite : FiniteDimensional ℚ Lc :=
    Module.Finite.equiv eLc.toLinearEquiv
  letI : FiniteDimensional ℚ Lc := hLcFinite
  letI : IsGalois ℚ Lc := hLcGalois
  letI : Normal ℚ Lc := hLcGalois.to_normal
  letI : Algebra Kc M := Kc.toAlgebra
  let hKcMFinite : FiniteDimensional Kc M :=
    Module.Finite.of_restrictScalars_finite ℚ Kc M
  let hKcMGalois : IsGalois Kc M :=
    @IsGalois.sup_right ℚ inferInstance M inferInstance inferInstance Lc Kc
      hLcGalois hLcFinite hsup
  letI : FiniteDimensional Kc M := hKcMFinite
  letI : IsGalois Kc M := hKcMGalois
  letI : NumberField Kc := NumberField.of_module_finite ℚ Kc
  let galoisEquiv : Gal(M/Kc) ≃* betaA.range :=
    rational_cyclotomic_range
      betaA hbetaA hsetup.target_pro_three
  let hcentralCubic : CCGroups pi :=
    ⟨hpi, hE, hA, hkernel_central, hkernel_card⟩
  let eKernel : q.ker ≃* Multiplicative (ZMod 3) :=
    (extensionPreimageProjection pi betaA.range).symm.trans
      (Classical.choice hcentralCubic.kernel_zmod_three)
  let eCubeRoot : rationalCubeField ≃ₐ[ℚ] Kc :=
    IntermediateField.restrict_algEquiv
      (show rationalCubeField ≤ M from le_sup_right)
  letI : FiniteDimensional ℚ Kc :=
    Module.Finite.equiv eCubeRoot.toLinearEquiv
  letI : IsGalois ℚ Kc :=
    IsGalois.of_algEquiv eCubeRoot
  letI : Normal ℚ Kc :=
    (inferInstance : IsGalois ℚ Kc).to_normal
  let zeta0 : rationalCubeField :=
    Classical.choose rational_cube_primitive
  have hzeta0 : IsPrimitiveRoot zeta0 3 :=
    (mem_primitiveRoots (by norm_num)).1
      (Classical.choose_spec rational_cube_primitive)
  let zeta : Kc := eCubeRoot zeta0
  have hzeta : IsPrimitiveRoot zeta 3 :=
    hzeta0.map_of_injective eCubeRoot.injective
  let kernelToUnits : q.ker →* Mˣ :=
    cubicUnitsFaithful eKernel zeta hzeta
  have hkernelToUnits : Function.Injective kernelToUnits :=
    cubic_faithful_injective eKernel zeta hzeta
  have hfixed : ∀ sigma : Gal(M/Kc), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z := by
    intro sigma z
    exact cubic_faithful_fixed eKernel zeta hzeta sigma z
  have hqKernelCard : Nat.card q.ker = 3 := by
    calc
      Nat.card q.ker = Nat.card (Multiplicative (ZMod 3)) :=
        Nat.card_congr eKernel.toEquiv
      _ = 3 := by norm_num
  have hqKernelCube (z : q.ker) : z ^ 3 = 1 := by
    letI := Fintype.ofFinite q.ker
    have hz := pow_card_eq_one (x := z)
    rw [← Nat.card_eq_fintype_card, hqKernelCard] at hz
    exact hz
  have hfinite :
      ∀ P : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers Kc),
        @Submission.CField.BGroups.brauerBaseChange
            Kc (P.adicCompletion Kc) inferInstance inferInstance
            (FinitePlace.embedding P).toAlgebra
            (extensionRelativeBrauer q hq hc galoisEquiv
              kernelToUnits hfixed : BrauerGroup Kc) = 1 := by
    intro P
    obtain ⟨r, hr, hPover⟩ :=
      number_field_lies Kc P.asIdeal P.ne_bot
    letI : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r) := hPover
    by_cases hrS : r ∈ S
    · exact cft_obstruction_s
        (hsetup := hsetup) (pi := pi) (alphaE := alphaE) (hkill := hkill)
        (betaA := betaA) (hbetaA := hbetaA) (hcompat := hcompat)
        hq hc hsup hLcGalois hLcFinite hKcMFinite hKcMGalois
          eCubeRoot kernelToUnits hkernelToUnits hfixed
          P r hr hPover hrS
    · let v := (FinitePlace.mk P).val
      letI : Fact v.IsNontrivial :=
        ⟨Submission.CField.Ideles.absolute_value_nontrivial
          P⟩
      letI : IsUltrametricDist v.Completion :=
        Submission.CField.Ideles.placeUltrametricDist
          P
      obtain ⟨placeAbove⟩ :=
        Submission.NumberTheory.Milne.absolute_value_extension
          (K := Kc) (L := M) v
      letI : Algebra Kc v.Completion :=
        Submission.NumberTheory.Milne.completionBaseAlgebra v
      letI : Algebra Kc (P.adicCompletion Kc) :=
        (FinitePlace.embedding P).toAlgebra
      have hv :=
        rational_change_not
          S N hsetup.target_pro_three q hq hc galoisEquiv kernelToUnits hfixed
            3 hqKernelCube hr hrS P hPover placeAbove
      apply brauer_change_ring Kc v.Completion
        (P.adicCompletion Kc)
        (Submission.CField.Ideles.placeCompletionAdic P) ?_
        (extensionRelativeBrauer q hq hc galoisEquiv
          kernelToUnits hfixed) hv
      ext x
      exact finite_place_adic P x
  exact hfinite


end TBluepr
end Submission
