import Submission.FieldTheory.TameThreeKoch.LocalObstructionHelpers
import Mathlib.Tactic.ExtractGoal


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

/-!
# Finite local obstruction at a ramified prime

This file isolates the local calculation for rational primes in the prescribed
ramification set.
-/

private abbrev primeInSN
    {S : Finset ℕ} {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA) :
    OpenNormalSubgroup (rationalTameGalois S) :=
  rational_tame_open betaA hbetaA

private abbrev primeInSM
    {S : Finset ℕ} {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA) :=
  rationalTameCompositum S (primeInSN betaA hbetaA)

private abbrev primeSL0
    {S : Finset ℕ} {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA) :=
  rationalLayerClosure S (primeInSN betaA hbetaA)

private abbrev primeSLc
    {S : Finset ℕ} {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA) :
    IntermediateField ℚ (primeInSM betaA hbetaA) :=
  (primeSL0 betaA hbetaA).restrict le_sup_left

private abbrev primeSKc
    {S : Finset ℕ} {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA) :
    IntermediateField ℚ (primeInSM betaA hbetaA) :=
  rationalCubeField.restrict le_sup_right

private abbrev primeInSQ
    {S : Finset ℕ} {A E : Type*} [Group A] [Group E]
    (pi : E →* A) (betaA : rationalTameGalois S →* A) :=
  centralPreimageProjection pi betaA.range

section PrimeInS

variable {d : ℕ} {S : Finset ℕ}
variable {free : ProP.FreeGroup.{u} 3 d}
variable {quotientMap : free.Carrier →* rationalTameGalois S}
variable {prime : Fin d → ℕ} {frobeniusLift : Fin d → free.Carrier}
variable (hsetup :
  RationalKochSetup S free quotientMap prime frobeniusLift)
variable {A E : Type v}
variable [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
variable [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable (pi : E →* A)
variable (alphaE : free.Carrier →* E)
variable (hkill : ∀ i : Fin d,
  alphaE (rationalTameRelator free prime frobeniusLift i) = 1)
variable (betaA : rationalTameGalois S →* A)
variable (hbetaA : Continuous betaA)
variable (hcompat : betaA.comp quotientMap = pi.comp alphaE)

local notation "N" =>
  primeInSN betaA hbetaA
local notation "M" => primeInSM betaA hbetaA
local notation "L0" => primeSL0 betaA hbetaA
local notation "Lc" => primeSLc betaA hbetaA
local notation "Kc" => primeSKc betaA hbetaA
local notation "Lf" => rationalTameLayer S N

include hsetup alphaE hkill hcompat

set_option synthInstance.maxHeartbeats 1000000 in
-- The completed extension algebra is fixed by the finite place.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private abbrev obstructionPlaceGal
    [FiniteDimensional Kc M] [IsGalois Kc M]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers Kc))
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) (FinitePlace.mk P).val) :=
  let v := (FinitePlace.mk P).val
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  Gal(w.1.Completion/v.Completion)

set_option synthInstance.maxHeartbeats 1000000 in
-- Completion and spectral-norm instances have a large telescope.
set_option maxHeartbeats 50000000 in
-- The two valuation comparisons elaborate through the completed extension.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private theorem obstruction_order_smul
    [FiniteDimensional Kc M] [IsGalois Kc M] [NumberField Kc]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers Kc))
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) (FinitePlace.mk P).val)
    [Finite (Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) (FinitePlace.mk P).val)]
    [Nonempty (Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(M/Kc)
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := M) (FinitePlace.mk P).val)]
    [IsUltrametricDist w.1.Completion] [ValuativeRel w.1.Completion]
    [Valuation.Compatible
      (NormedField.valuation (K := w.1.Completion))]
    [IsNonarchimedeanLocalField w.1.Completion]
    (hvle : ∀ x y : w.1.Completion,
      ValuativeRel.vle x y ↔ ‖x‖₊ ≤ ‖y‖₊)
    (sigma : obstructionPlaceGal
      (betaA := betaA) (hbetaA := hbetaA) P w)
    (z : w.1.Completionˣ) :
    localOrderHom w.1.Completion (sigma • z) =
      localOrderHom w.1.Completion z := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨Submission.CField.Ideles.absolute_value_nontrivial
      P⟩
  letI : IsUltrametricDist v.Completion :=
    Submission.CField.Ideles.placeUltrametricDist
      P
  let hw :=
    Submission.NumberTheory.Milne.absolute_extension_nontrivial v w
  let hwna :=
    Submission.NumberTheory.Milne.absolute_extension_nonarchimedean
      v w
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : NontriviallyNormedField v.Completion :=
    Submission.CField.Ideles.placeNontriviallyNormed
      P
  letI : Algebra Kc v.Completion :=
    Submission.NumberTheory.Milne.completionBaseAlgebra v
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap Kc v.Completion).injective).mp
      inferInstance
  letI : IsUltrametricDist w.1.Completion :=
    Submission.NumberTheory.Milne.absoluteUltrametricDist
      w.1 hwna
  letI : ValuativeRel v.Completion :=
    Submission.CField.Ideles.placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    Submission.CField.Ideles.placeNonarchimedeanField
      P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionGalois v w
  letI : Algebra.IsAlgebraic v.Completion w.1.Completion :=
    Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion
  letI : NontriviallyNormedField w.1.Completion :=
    Submission.NumberTheory.Milne.absoluteNontriviallyNormed
      w.1
  apply Multiplicative.toAdd.injective
  change localUnitOrder w.1.Completion
      (Additive.ofMul (sigma • z)) =
    localUnitOrder w.1.Completion (Additive.ofMul z)
  apply le_antisymm
  · rw [local_order_valuation]
    rw [← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation w.1.Completion), hvle]
    change ‖(z : w.1.Completion)‖₊ ≤
      ‖sigma (z : w.1.Completion)‖₊
    have hnorm : ‖(z : w.1.Completion)‖ ≤
        ‖sigma (z : w.1.Completion)‖ := by
      rw [Submission.NumberTheory.Milne.norm_spectral_completion
          v w.1 w.2 inferInstance,
        Submission.NumberTheory.Milne.norm_spectral_completion
          v w.1 w.2 inferInstance]
      exact (spectralNorm_eq_of_equiv sigma
        (z : w.1.Completion)).le
    exact NNReal.coe_le_coe.mp hnorm
  · rw [local_order_valuation]
    rw [← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation w.1.Completion), hvle]
    change ‖sigma (z : w.1.Completion)‖₊ ≤
      ‖(z : w.1.Completion)‖₊
    have hnorm : ‖sigma (z : w.1.Completion)‖ ≤
        ‖(z : w.1.Completion)‖ := by
      rw [Submission.NumberTheory.Milne.norm_spectral_completion
          v w.1 w.2 inferInstance,
        Submission.NumberTheory.Milne.norm_spectral_completion
          v w.1 w.2 inferInstance]
      exact (spectralNorm_eq_of_equiv sigma
        (z : w.1.Completion)).ge
    exact NNReal.coe_le_coe.mp hnorm

set_option synthInstance.maxHeartbeats 1000000 in
-- Comparing the integral actions synthesizes the full number-field module tower.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private theorem obstruction_integers_smul
    [FiniteDimensional Kc M] [IsGalois Kc M] [NumberField Kc]
    (sigma : Gal(M/Kc)) (t : NumberField.RingOfIntegers M) :
    @SMul.smul _ _
        (centralBrauerRingOfIntegersGaloisAction
          (K := Kc) (L := M)).toSMul sigma t =
      @SMul.smul _ _
        (NumberField.RingOfIntegers.instMulSemiringAction M).toSMul
          sigma t := by
  apply NumberField.RingOfIntegers.ext
  have hleft :
      (((@SMul.smul _ _
          (centralBrauerRingOfIntegersGaloisAction
            (K := Kc) (L := M)).toSMul sigma t) :
            NumberField.RingOfIntegers M) : M) = sigma (t : M) := by
    exact algebraMap_galRestrictHom_apply
      (NumberField.RingOfIntegers Kc) Kc M
        (NumberField.RingOfIntegers M) sigma t
  have hright :
      (((@SMul.smul _ _
          (NumberField.RingOfIntegers.instMulSemiringAction M).toSMul
            sigma t) : NumberField.RingOfIntegers M) : M) =
        sigma (t : M) := by
    change _ = sigma • (t : M)
    exact integralClosure.coe_smul sigma t
  exact hleft.trans hright.symm

set_option synthInstance.maxHeartbeats 1000000 in
-- Fixing the inertia action explicitly repeats the full number-field module synthesis.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private theorem obstruction_inertia_action
    [FiniteDimensional Kc M] [IsGalois Kc M] [NumberField Kc]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers M))
    (sigma : Gal(M/Kc))
    (hsigma : ∀ t : NumberField.RingOfIntegers M,
      (@SMul.smul _ _
          (centralBrauerRingOfIntegersGaloisAction
            (K := Kc) (L := M)).toSMul sigma t - t) ∈ Q.asIdeal) :
    sigma ∈ Q.asIdeal.inertia Gal(M/Kc) := by
  intro t
  rw [Submodule.mem_toAddSubgroup]
  change
    (@SMul.smul _ _
        (NumberField.RingOfIntegers.instMulSemiringAction M).toSMul
          sigma t - t) ∈ Q.asIdeal
  rw [← obstruction_integers_smul
    (betaA := betaA) (hbetaA := hbetaA) sigma t]
  exact hsigma t

set_option synthInstance.maxHeartbeats 1000000 in
-- The completed extension algebra is inferred from the chosen place.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private abbrev obstructionCompletionGal
    [FiniteDimensional Kc M] [IsGalois Kc M]
    (v : AbsoluteValue Kc ℝ)
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) v) :=
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  Gal(w.1.Completion/v.Completion)

set_option synthInstance.maxHeartbeats 1000000 in
-- Global-to-local inertia transport uses the full completion instance tower.
set_option maxHeartbeats 50000000 in
-- The proof follows an arbitrary completed inertia element back to the
-- prescribed finite-layer inertia generator.
omit hsetup alphaE hkill hcompat pi [Group E] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
private theorem obstruction_completed_zpowers
    [FiniteDimensional ℚ Lc] [IsGalois ℚ Lc] [Normal ℚ Lc]
    [FiniteDimensional Kc M] [IsGalois Kc M] [NumberField Kc]
    [FiniteDimensional ℚ Kc] [IsGalois ℚ Kc] [Normal ℚ Kc]
    (v : AbsoluteValue Kc ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) v)
    [Fact (AbsoluteValue.LiesOver w.1 v)]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers M))
    (r : ℕ) [Q.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r)]
    (P0 : Ideal (NumberField.RingOfIntegers Lf))
    (eLayer : Lf ≃ₐ[ℚ] Lc)
    (hQunder : Q.asIdeal.under (NumberField.RingOfIntegers Lc) =
      P0.map
        (NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv))
    (eComp : Gal(M/Kc) ≃* Gal(Lc/ℚ))
    (tau0 : P0.inertia Gal(Lf/ℚ))
    (hgen0 : Subgroup.closure ({(tau0 : Gal(Lf/ℚ))} : Set _) =
      P0.inertia Gal(Lf/ℚ))
    (tauD : Submission.NumberTheory.Milne.absoluteValueDecomposition
      v w.1)
    (htauM : eComp tauD.1 = (AlgEquiv.autCongr eLayer) tau0)
    (heComp : ∀ zD :
      Submission.NumberTheory.Milne.absoluteValueDecomposition v w.1,
      eComp zD.1 = AlgEquiv.restrictNormalHom Lc
        (MulSemiringAction.toAlgAut Gal(M/Kc) ℚ M zD.1))
    (ILocal : Subgroup (obstructionCompletionGal
      (betaA := betaA) (hbetaA := hbetaA) (v := v) (w := w)))
    (hILocal : ∀ z : ILocal,
      ((Submission.NumberTheory.Milne.decompositionCompletionExtension
        v w.1).symm z.1).1 ∈ Q.asIdeal.inertia Gal(M/Kc))
    (tauI : ILocal)
    (htauI : tauI.1 =
      Submission.NumberTheory.Milne.decompositionCompletionExtension
        v w.1 tauD) :
    Subgroup.zpowers tauI = ⊤ := by
  let eD :=
    Submission.NumberTheory.Milne.decompositionCompletionExtension
      v w.1
  apply top_unique
  intro z _hz
  let zD := eD.symm z.1
  have hzM : zD.1 ∈ Q.asIdeal.inertia Gal(M/Kc) := hILocal z
  let zGlobal : Gal(M/ℚ) :=
    MulSemiringAction.toAlgAut Gal(M/Kc) ℚ M zD.1
  have hzGlobal : zGlobal ∈ Q.asIdeal.inertia Gal(M/ℚ) := by
    intro t
    have haction : zGlobal • t = zD.1 • t := by
      apply NumberField.RingOfIntegers.ext
      have hring : zGlobal.toRingEquiv = zD.1.toRingEquiv := rfl
      have hfun : zGlobal (t : M) = zD.1 (t : M) :=
        DFunLike.congr_fun hring (t : M)
      simpa only [algebraMap.coe_smul'] using hfun
    rw [haction]
    exact hzM t
  let zL : Gal(Lc/ℚ) :=
    AlgEquiv.restrictNormalHom Lc zGlobal
  have hzL : zL ∈
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)).inertia
        Gal(Lc/ℚ) := by
    exact number_restrict_intermediate
      (q := r) (P := Q.asIdeal) Lc
        (inferInstance : Normal ℚ Lc) zGlobal hzGlobal
  let z0 : Gal(Lf/ℚ) := (AlgEquiv.autCongr eLayer).symm zL
  have hz0 : z0 ∈ P0.inertia Gal(Lf/ℚ) := by
    intro t
    let eO := NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv
    have ht := hzL (eO t)
    rw [hQunder] at ht
    have hcongr : AlgEquiv.autCongr eLayer z0 = zL :=
      (AlgEquiv.autCongr eLayer).apply_symm_apply zL
    have hact := integers_alg_smul eLayer z0 t
    rw [hcongr] at hact
    have ht' : eO (z0 • t - t) ∈ P0.map eO := by
      rw [map_sub, hact]
      exact ht
    obtain ⟨b, hb, hbeq⟩ :=
      (Ideal.mem_map_iff_of_surjective eO eO.surjective).mp ht'
    have hbt : b = z0 • t - t := eO.injective hbeq
    exact hbt ▸ hb
  have hz0Pow : z0 ∈ Subgroup.zpowers (tau0 : Gal(Lf/ℚ)) := by
    rw [Subgroup.zpowers_eq_closure, hgen0]
    exact hz0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz0Pow
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply eD.symm.injective
  apply Subtype.ext
  apply eComp.injective
  have heDtau : eD.symm (tauI ^ k).1 = tauD ^ k := by
    change eD.symm (tauI.1 ^ k) = tauD ^ k
    rw [htauI, ← map_zpow, eD.symm_apply_apply]
  have heDz : eD.symm z.1 = zD := rfl
  have hzComp : eComp zD.1 = zL := by
    rw [heComp zD]
  rw [heDtau, heDz]
  change eComp (tauD.1 ^ k) = eComp zD.1
  rw [map_zpow, htauM, hzComp]
  calc
    (AlgEquiv.autCongr eLayer tau0) ^ k =
        (AlgEquiv.autCongr eLayer) (tau0 ^ k) := by
      rw [map_zpow]
    _ = (AlgEquiv.autCongr eLayer) z0 := congrArg _ hk
    _ = zL := (AlgEquiv.autCongr eLayer).apply_symm_apply zL

set_option synthInstance.maxHeartbeats 1000000 in
-- The local calculation synthesizes completion and residue-field instances.
set_option maxHeartbeats 50000000 in
-- Constructing the tame local data is the expensive part of this declaration.
omit [TopologicalSpace E] [DiscreteTopology E] in
/-- The finite-place obstruction vanishes at a rational prime in the prescribed
ramification set. -/
theorem cft_obstruction_s
    (hq : Function.Surjective (primeInSQ pi betaA))
    (hc : (primeInSQ pi betaA).ker ≤
      Subgroup.center (centralExtensionPreimage pi betaA.range))
    (hsup : Lc ⊔ Kc = ⊤)
    (hLcGalois : IsGalois ℚ Lc)
    (hLcFinite : FiniteDimensional ℚ Lc)
    [FiniteDimensional ℚ Lc] [IsGalois ℚ Lc] [Normal ℚ Lc]
    (hKcMFinite : FiniteDimensional Kc M)
    (hKcMGalois : IsGalois Kc M)
    [FiniteDimensional Kc M] [IsGalois Kc M] [NumberField Kc]
    (eCubeRoot : rationalCubeField ≃ₐ[ℚ] Kc)
    [FiniteDimensional ℚ Kc] [IsGalois ℚ Kc] [Normal ℚ Kc]
    (kernelToUnits : (primeInSQ pi betaA).ker →* Mˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(M/Kc), ∀ z : (primeInSQ pi betaA).ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers Kc))
    (r : ℕ) (hr : Nat.Prime r)
    (hPover : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r))
    (hrS : r ∈ S) :
    @Submission.CField.BGroups.brauerBaseChange
        Kc (P.adicCompletion Kc) inferInstance inferInstance
        (FinitePlace.embedding P).toAlgebra
        (extensionRelativeBrauer (primeInSQ pi betaA) hq hc
          (rational_cyclotomic_range
            betaA hbetaA hsetup.target_pro_three)
          kernelToUnits hfixed : BrauerGroup Kc) = 1 := by
  let L := rationalTameLayer S N
  let q := primeInSQ pi betaA
  let eLc : L0 ≃ₐ[ℚ] Lc :=
    IntermediateField.restrict_algEquiv
      (show L0 ≤ M from le_sup_left)
  let galoisEquiv : Gal(M/Kc) ≃* betaA.range :=
    rational_cyclotomic_range
      betaA hbetaA hsetup.target_pro_three
  letI : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r) := hPover
  have hiMem : r ∈ Finset.univ.image prime := by
    rwa [hsetup.prime_range]
  obtain ⟨i, _hi, hir⟩ := Finset.mem_image.mp hiMem
  have hir' : prime i = r := hir
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨Submission.CField.Ideles.absolute_value_nontrivial
      P⟩
  letI : IsUltrametricDist v.Completion :=
    Submission.CField.Ideles.placeUltrametricDist
      P
  let W := Submission.CField.ICohomo.CompletionPlacesAbove
    (L := M) v
  letI : Finite W :=
    Submission.NumberTheory.Milne.absolute_extensions_separable
      v
  obtain ⟨placeAbove⟩ :=
    Submission.NumberTheory.Milne.absolute_value_extension
      (K := Kc) (L := M) v
  letI : Nonempty W := ⟨placeAbove⟩
  letI : MulAction.IsPretransitive Gal(M/Kc) W :=
    Submission.NumberTheory.Milne.completion_above_pretransitive P
  have hinf : Lc ⊓ Kc = ⊥ := by
    apply (IntermediateField.lift_inj (Lc ⊓ Kc) ⊥).mp
    rw [IntermediateField.lift_inf ℚ M Lc Kc,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_bot ℚ M]
    exact
      (rational_disjoint_cube
        S N hsetup.target_pro_three).inf_eq_bot
  let eLayer : L ≃ₐ[ℚ] Lc :=
    (rationalTameClosure S N).trans eLc
  let P0 :=
    (hsetup.generators_tame_inertia i).primeAbove N
  have hP0 :=
    (hsetup.generators_tame_inertia i).primeAbove_mem N
  letI : P0.IsPrime := hP0.1
  letI : P0.LiesOver (Ideal.rationalPrimeIdeal r) := by
    simpa [P0, hir'] using hP0.2
  let pRat := P0.under (NumberField.RingOfIntegers ℚ)
  letI : P0.LiesOver pRat := inferInstance
  have hbaseUnder : pRat =
      P.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
    exact integers_rat_lies
      (r := r) P0 P.asIdeal
  have hPpRat : P.asIdeal.LiesOver pRat := ⟨hbaseUnder⟩
  letI : P.asIdeal.LiesOver pRat := hPpRat
  obtain ⟨gamma, hgamma⟩ :=
    @compositum_conjugate_completion
      ℚ M L _ _ _ _ _ _ _ _ Lc Kc
      hLcFinite hLcGalois
      (Module.Finite.equiv eCubeRoot.toLinearEquiv)
      (IsGalois.of_algEquiv eCubeRoot)
      hKcMFinite hKcMGalois inferInstance inferInstance
      hsup hinf eLayer pRat P0 inferInstance inferInstance P
      inferInstance inferInstance hPpRat placeAbove
  let w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := M) v := gamma • placeAbove
  have hw : w.1.IsNontrivial :=
    Submission.NumberTheory.Milne.absolute_extension_nontrivial
      v w
  have hwna : IsNonarchimedean w.1 :=
    Submission.NumberTheory.Milne.absolute_extension_nonarchimedean
      v w
  let Q :=
    Submission.NumberTheory.Milne.nonarchimedeanHeightSpectrum
      w.1 hw hwna
  have hQunder : Q.asIdeal.under
      (NumberField.RingOfIntegers Lc) =
        P0.map (NumberField.RingOfIntegers.mapAlgEquiv eLayer) := by
    exact hgamma
  letI : Q.asIdeal.IsPrime := Q.isPrime
  letI : Q.asIdeal.LiesOver P.asIdeal :=
    Submission.NumberTheory.Milne.nonarchimedean_spectrum_lies
      P w.1 w.2 hw hwna
  have hQK : Q.asIdeal.under (NumberField.RingOfIntegers Kc) =
      P.asIdeal :=
    (Q.asIdeal.over_def P.asIdeal).symm
  let eCubeO := NumberField.RingOfIntegers.mapAlgEquiv eCubeRoot
  let Pc : Ideal (NumberField.RingOfIntegers rationalCubeField) :=
    P.asIdeal.comap eCubeO
  have hPcOver : Pc ∈ (Ideal.rationalPrimeIdeal r).primesOver
      (NumberField.RingOfIntegers rationalCubeField) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
    ext z
    change z ∈ Ideal.rationalPrimeIdeal r ↔
      eCubeO.toRingHom
        (algebraMap ℤ
          (NumberField.RingOfIntegers rationalCubeField) z) ∈ P.asIdeal
    simpa using (Ideal.mem_of_liesOver
      (P := P.asIdeal) (p := Ideal.rationalPrimeIdeal r) z)
  letI : Pc.IsPrime := hPcOver.1
  letI : Pc.LiesOver (Ideal.rationalPrimeIdeal r) := hPcOver.2
  have hPcmap : Pc.map eCubeO = P.asIdeal := by
    exact Ideal.map_comap_eq_self_of_equiv eCubeO P.asIdeal
  have hPcBot : MulAction.stabilizer
      Gal(rationalCubeField/ℚ) Pc = ⊥ :=
    cube_stabilizer_bot hr
      (by simpa [← hir'] using hsetup.prime_mod_three i) Pc
  have hKbot : MulAction.stabilizer Gal(Kc/ℚ)
      (Q.asIdeal.under (NumberField.RingOfIntegers Kc)) = ⊥ := by
    rw [hQK]
    exact obstruction_stabilizer_bot
      eCubeRoot P hPcBot
  let tau0 :=
    (hsetup.generators_tame_inertia i).inertiaGenerator N
  let tauL : Gal(Lc/ℚ) := AlgEquiv.autCongr eLayer tau0
  have htauP0 : (tau0 : Gal(L/ℚ)) • P0 = P0 := by
    apply MulAction.mem_stabilizer_iff.mp
    exact Ideal.inertia_le_stabilizer P0 tau0.property
  have htauL : tauL • Q.asIdeal.under
      (NumberField.RingOfIntegers Lc) =
        Q.asIdeal.under (NumberField.RingOfIntegers Lc) := by
    rw [hQunder]
    change tauL • P0.map
        (NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv) =
      P0.map (NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv)
    rw [← ideal_alg_smul]
    rw [htauP0]
  let eLayerO := NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv
  have htauLInertia : tauL ∈
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)).inertia
        Gal(Lc/ℚ) := by
    intro x
    let y : NumberField.RingOfIntegers L := eLayerO.symm x
    have hy := tau0.property y
    have hy' : eLayerO (tau0.1 • y - y) ∈
        P0.map eLayerO := Ideal.mem_map_of_mem eLayerO hy
    rw [hQunder]
    simpa [y, map_sub, integers_alg_smul] using hy'
  letI : Q.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r) :=
    Ideal.LiesOver.trans Q.asIdeal P.asIdeal (Ideal.rationalPrimeIdeal r)
  letI hNormalLc : Normal ℚ Lc := hLcGalois.to_normal
  letI hNormalKc : Normal ℚ Kc :=
    (IsGalois.of_algEquiv eCubeRoot).to_normal
  let eComp : Gal(M/Kc) ≃* Gal(Lc/ℚ) :=
    @galoisCompositumEquiv ℚ M _ _ _ Lc Kc hNormalLc
      hLcFinite hKcMFinite hKcMGalois hsup hinf
  letI hIntegralAction : MulSemiringAction Gal(M/Kc)
      (NumberField.RingOfIntegers M) :=
    Submission.NumberTheory.Milne.ringOfIntegersGaloisAction
  letI : SMulCommClass Gal(M/Kc) (NumberField.RingOfIntegers Kc)
      (NumberField.RingOfIntegers M) := {
    smul_comm := by
        intro sigma a b
        apply Subtype.ext
        have hG (x : NumberField.RingOfIntegers M) :
            ((sigma • x : NumberField.RingOfIntegers M) : M) =
              sigma (x : M) :=
          algebraMap.coe_smul' (B := NumberField.RingOfIntegers M)
            (C := M) sigma x
        have hA (x : NumberField.RingOfIntegers M) :
            ((a • x : NumberField.RingOfIntegers M) : M) =
              (a : Kc) • (x : M) :=
          algebraMap.coe_smul (A := NumberField.RingOfIntegers Kc)
            (B := NumberField.RingOfIntegers M) (C := M) a x
        calc
          ((sigma • (a • b) : NumberField.RingOfIntegers M) : M) =
              sigma (((a • b : NumberField.RingOfIntegers M) : M)) :=
            hG (a • b)
          _ = sigma ((a : Kc) • (b : M)) := congrArg sigma (hA b)
          _ = (a : Kc) • sigma (b : M) :=
            smul_comm sigma (a : Kc) (b : M)
          _ = (a : Kc) •
              ((sigma • b : NumberField.RingOfIntegers M) : M) :=
            congrArg (fun y : M => (a : Kc) • y) (hG b).symm
          _ = ((a • (sigma • b) : NumberField.RingOfIntegers M) : M) :=
            (hA (sigma • b)).symm }
  let tauLSub :
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)).inertia
        Gal(Lc/ℚ) := ⟨tauL, htauLInertia⟩
  obtain ⟨tauGlobal, htauGlobal⟩ :=
    number_restriction_preimage
      Lc (inferInstance : FiniteDimensional ℚ Lc)
      (inferInstance : IsGalois ℚ Lc) hr Q.asIdeal tauLSub
  have htauGlobalStab : tauGlobal.1 • Q.asIdeal = Q.asIdeal :=
    MulAction.mem_stabilizer_iff.mp
      (Ideal.inertia_le_stabilizer Q.asIdeal tauGlobal.property)
  have htauKmem : AlgEquiv.restrictNormalHom Kc tauGlobal.1 ∈
      MulAction.stabilizer Gal(Kc/ℚ)
        (Q.asIdeal.under (NumberField.RingOfIntegers Kc)) := by
    rw [MulAction.mem_stabilizer_iff]
    exact (global_smul_restrict
      tauGlobal.1 Q.asIdeal).symm.trans (by rw [htauGlobalStab])
  have htauK : AlgEquiv.restrictNormalHom Kc tauGlobal.1 = 1 := by
    rw [hKbot] at htauKmem
    exact htauKmem
  let tauM : Gal(M/Kc) :=
    { tauGlobal.1.toRingEquiv with
      commutes' := by
        intro x
        have hx : (AlgEquiv.restrictNormalHom Kc tauGlobal.1) x = x :=
          DFunLike.congr_fun htauK x
        calc
          tauGlobal.1 (algebraMap Kc M x) =
              ((AlgEquiv.restrictNormalHom Kc tauGlobal.1) x : M) :=
            (AlgEquiv.restrictNormal_commutes
              tauGlobal.1 Kc x).symm
          _ = algebraMap Kc M x :=
            congrArg (fun z : Kc => (z : M)) hx }
  have htauMQ : tauM • Q.asIdeal = Q.asIdeal := by
      apply Ideal.ext
      intro x
      have hx := Ideal.ext_iff.mp htauGlobalStab x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      have hsmul : tauM⁻¹ • x = (tauGlobal.1)⁻¹ • x := by
        apply NumberField.RingOfIntegers.ext
        have hring : tauM.toRingEquiv = tauGlobal.1.toRingEquiv := rfl
        have hringInv : tauM.symm.toRingEquiv =
            tauGlobal.1.symm.toRingEquiv :=
          congrArg RingEquiv.symm hring
        have hfun : tauM.symm (x : M) = tauGlobal.1.symm (x : M) :=
          DFunLike.congr_fun hringInv (x : M)
        simpa only [algebraMap.coe_smul'] using hfun
      rw [hsmul]
      simpa [Ideal.mem_pointwise_smul_iff_inv_smul_mem] using hx
  have htauM : eComp tauM = tauL := by
    change AlgEquiv.restrictNormalHom Lc tauGlobal.1 = tauL
    exact congrArg Subtype.val htauGlobal
  let sigma0 : Gal(L/ℚ) :=
    rationalTameEquiv S N
      (rationalTameQuotient S N
        (quotientMap (frobeniusLift i)))
  have hsigma0 : IsArithFrobAt ℤ sigma0 P0 := by
    exact hsetup.frobenius_lift_arithmetic i N
  let sigmaL : Gal(Lc/ℚ) := AlgEquiv.autCongr eLayer sigma0
  have hsigmaL : IsArithFrobAt ℤ sigmaL
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)) := by
    rw [hQunder]
    exact arith_frob_alg (r := r) eLayer P0 sigma0 hsigma0
  let sigmaGlobal : Gal(M/ℚ) :=
    arithFrobAt ℤ Gal(M/ℚ) Q.asIdeal
  have hsigmaGlobal : IsArithFrobAt ℤ sigmaGlobal Q.asIdeal :=
    IsArithFrobAt.arithFrobAt ℤ Gal(M/ℚ) Q.asIdeal
  have hsigmaGlobalStab : sigmaGlobal • Q.asIdeal = Q.asIdeal := by
      rw [← MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      ext x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      have hx := Ideal.ext_iff.mp hsigmaGlobal.comap_eq
        (sigmaGlobal⁻¹ • x)
      rw [Ideal.mem_comap, MulSemiringAction.toAlgHom_apply] at hx
      have hcancel : sigmaGlobal • (sigmaGlobal⁻¹ • x) = x := by simp
      rw [hcancel] at hx
      exact hx.symm
  have hsigmaKmem : AlgEquiv.restrictNormalHom Kc sigmaGlobal ∈
      MulAction.stabilizer Gal(Kc/ℚ)
        (Q.asIdeal.under (NumberField.RingOfIntegers Kc)) := by
    rw [MulAction.mem_stabilizer_iff]
    exact (global_smul_restrict
      sigmaGlobal Q.asIdeal).symm.trans (by rw [hsigmaGlobalStab])
  have hsigmaK : AlgEquiv.restrictNormalHom Kc sigmaGlobal = 1 := by
    rw [hKbot] at hsigmaKmem
    exact hsigmaKmem
  let sigmaM : Gal(M/Kc) :=
    { sigmaGlobal.toRingEquiv with
      commutes' := by
        intro x
        have hx : (AlgEquiv.restrictNormalHom Kc sigmaGlobal) x = x :=
          DFunLike.congr_fun hsigmaK x
        calc
          sigmaGlobal (algebraMap Kc M x) =
              ((AlgEquiv.restrictNormalHom Kc sigmaGlobal) x : M) :=
            (AlgEquiv.restrictNormal_commutes
              sigmaGlobal Kc x).symm
          _ = algebraMap Kc M x :=
            congrArg (fun z : Kc => (z : M)) hx }
  have hsigmaMQ : sigmaM • Q.asIdeal = Q.asIdeal := by
      apply Ideal.ext
      intro x
      have hx := Ideal.ext_iff.mp hsigmaGlobalStab x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      have hsmul : sigmaM⁻¹ • x = sigmaGlobal⁻¹ • x := by
        apply NumberField.RingOfIntegers.ext
        have hring : sigmaM.toRingEquiv = sigmaGlobal.toRingEquiv := rfl
        have hringInv : sigmaM.symm.toRingEquiv =
            sigmaGlobal.symm.toRingEquiv :=
          congrArg RingEquiv.symm hring
        have hfun : sigmaM.symm (x : M) = sigmaGlobal.symm (x : M) :=
          DFunLike.congr_fun hringInv (x : M)
        simpa only [algebraMap.coe_smul'] using hfun
      rw [hsmul]
      simpa [Ideal.mem_pointwise_smul_iff_inv_smul_mem] using hx
  have hsigmaRestr : IsArithFrobAt ℤ
      (AlgEquiv.restrictNormalHom Lc sigmaGlobal)
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)) := by
    exact arith_frob_int
      (E := Lc) (L := M) hsigmaGlobal
  let deltaL : Gal(Lc/ℚ) :=
    AlgEquiv.restrictNormalHom Lc sigmaGlobal * sigmaL⁻¹
  have hdeltaL : deltaL ∈
      (Q.asIdeal.under (NumberField.RingOfIntegers Lc)).inertia
        Gal(Lc/ℚ) := by
    exact hsigmaRestr.mul_inv_mem_inertia hsigmaL
  let delta0 : Gal(L/ℚ) := (AlgEquiv.autCongr eLayer).symm deltaL
  have hdelta0 : delta0 ∈ P0.inertia Gal(L/ℚ) := by
      intro x
      let eO := NumberField.RingOfIntegers.mapRingEquiv eLayer.toRingEquiv
      have hx := hdeltaL (eO x)
      rw [hQunder] at hx
      have hcongr : AlgEquiv.autCongr eLayer delta0 = deltaL :=
        (AlgEquiv.autCongr eLayer).apply_symm_apply deltaL
      have hact := integers_alg_smul eLayer delta0 x
      rw [hcongr] at hact
      have hx' : eO (delta0 • x - x) ∈ P0.map eO := by
        rw [map_sub, hact]
        exact hx
      obtain ⟨y, hy, hyeq⟩ :=
        (Ideal.mem_map_iff_of_surjective eO eO.surjective).mp hx'
      have hyx : y = delta0 • x - x := eO.injective hyeq
      exact hyx ▸ hy
  have hdelta0Pow : delta0 ∈
      Subgroup.zpowers (tau0 : Gal(L/ℚ)) := by
    have hgen0 :=
      (hsetup.generators_tame_inertia i).inertiaGenerator_generates N
    rw [Subgroup.zpowers_eq_closure, hgen0]
    exact hdelta0
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hdelta0Pow
  have hdeltaLPow : tauL ^ a = deltaL := by
    calc
      tauL ^ a =
          (AlgEquiv.autCongr eLayer) ((tau0 : Gal(L/ℚ)) ^ a) := by
        rw [map_zpow]
      _ = (AlgEquiv.autCongr eLayer) delta0 := by rw [ha]
      _ = deltaL := (AlgEquiv.autCongr eLayer).apply_symm_apply deltaL
  have hsigmaRestrEq :
      AlgEquiv.restrictNormalHom Lc sigmaGlobal =
        tauL ^ a * sigmaL := by
    change tauL ^ a =
      AlgEquiv.restrictNormalHom Lc sigmaGlobal * sigmaL⁻¹ at hdeltaLPow
    calc
      AlgEquiv.restrictNormalHom Lc sigmaGlobal =
          (AlgEquiv.restrictNormalHom Lc sigmaGlobal * sigmaL⁻¹) *
            sigmaL := by group
      _ = tauL ^ a * sigmaL := by rw [← hdeltaLPow]
  let lift := tamePreimageLift
    quotientMap pi alphaE betaA hcompat
  let xGlobal := lift (free.generator i)
  let yGlobal0 := lift (frobeniusLift i)
  let yGlobal := xGlobal ^ a * yGlobal0
  have hgaloisEquiv_eComp (s : Gal(M/Kc)) :
      galoisEquiv s =
        rational_tame_range betaA hbetaA
          ((AlgEquiv.autCongr eLayer).symm (eComp s)) := by
    rfl
  have htauBack :
      (AlgEquiv.autCongr eLayer).symm (eComp tauM) = tau0 := by
    rw [htauM]
    exact (AlgEquiv.autCongr eLayer).symm_apply_apply tau0
  have hqxGlobal : q xGlobal = galoisEquiv tauM := by
      rw [preimage_lift_projection]
      apply Subtype.ext
      rw [hgaloisEquiv_eComp, htauBack]
      have hmapTau :=
        (hsetup.generators_tame_inertia i).mapsFiniteLayer N
      rw [← hmapTau]
      change betaA (quotientMap (free.generator i)) =
        ((QuotientGroup.quotientKerEquivRange betaA)
          ((rationalTameEquiv S N).symm
            ((rationalTameEquiv S N)
              (rationalTameQuotient S N
                (quotientMap (free.generator i)))))).1
      rw [MulEquiv.symm_apply_apply]
      rfl
  have hqsigmaM : eComp sigmaM =
      AlgEquiv.restrictNormalHom Lc sigmaGlobal := rfl
  have hqSigmaLayer : q yGlobal0 = galoisEquiv (eComp.symm sigmaL) := by
      have hsigmaBack :
          (AlgEquiv.autCongr eLayer).symm
              (eComp (eComp.symm sigmaL)) = sigma0 := by
        rw [eComp.apply_symm_apply]
        exact (AlgEquiv.autCongr eLayer).symm_apply_apply sigma0
      rw [preimage_lift_projection]
      apply Subtype.ext
      rw [hgaloisEquiv_eComp, hsigmaBack]
      change betaA (quotientMap (frobeniusLift i)) =
        ((QuotientGroup.quotientKerEquivRange betaA)
          ((rationalTameEquiv S N).symm
            ((rationalTameEquiv S N)
              (rationalTameQuotient S N
                (quotientMap (frobeniusLift i)))))).1
      rw [MulEquiv.symm_apply_apply]
      rfl
  have hsigmaMProduct : sigmaM = tauM ^ a * eComp.symm sigmaL := by
    apply eComp.injective
    rw [map_mul, map_zpow, htauM, eComp.apply_symm_apply,
      hqsigmaM, hsigmaRestrEq]
  have hqyGlobal : q yGlobal = galoisEquiv sigmaM := by
    rw [map_mul, map_zpow, hqxGlobal, hqSigmaLayer,
      ← map_zpow, ← map_mul, hsigmaMProduct]
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : NontriviallyNormedField v.Completion :=
    Submission.CField.Ideles.placeNontriviallyNormed P
  letI : Algebra Kc v.Completion :=
    Submission.NumberTheory.Milne.completionBaseAlgebra v
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff
      (algebraMap Kc v.Completion).injective).mp inferInstance
  letI : IsUltrametricDist w.1.Completion :=
    Submission.NumberTheory.Milne.absoluteUltrametricDist w.1 hwna
  letI : ValuativeRel v.Completion :=
    Submission.CField.Ideles.placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    Submission.CField.Ideles.placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionGalois v w
  let Aint :=
    Submission.NumberTheory.Milne.completionIntegerRing v
  let Bint :=
    Submission.NumberTheory.Milne.completionIntegerRing w.1
  letI : Algebra Aint v.Completion := Aint.subtype.toAlgebra
  letI : Algebra Aint Bint :=
    Submission.NumberTheory.Milne.completionIntegerLies v w.1 w.2
  letI : Algebra Bint w.1.Completion := Bint.subtype.toAlgebra
  letI : Algebra Aint w.1.Completion :=
    ((Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).comp Aint.subtype).toAlgebra
  letI : IsScalarTower Aint Bint w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Aint v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Aint v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure Bint Aint w.1.Completion :=
    Submission.NumberTheory.Milne.completion_integer_closure v w.1 w.2
        (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
  letI : MulSemiringAction Gal(w.1.Completion/v.Completion) Bint :=
    IsIntegralClosure.MulSemiringAction
      Aint v.Completion w.1.Completion Bint
  have hAintVal :
      Valuation.integer (ValuativeRel.valuation v.Completion) = Aint := by
    ext x
    simp only [Aint, Submission.NumberTheory.Milne.completionIntegerRing,
      Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation v.Completion).vle_one_iff,
      ← (NormedField.valuation (K := v.Completion)).vle_one_iff]
  letI : IsDiscreteValuationRing Aint :=
    hAintVal ▸ discrete_valuation_ring v.Completion
  letI : IsFractionRing Bint w.1.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := w.1.Completion))).isFractionRing
  letI : Module.Finite Aint Bint :=
    IsIntegralClosure.finite Aint v.Completion w.1.Completion Bint
  letI : Algebra.IsIntegral Aint Bint := Algebra.IsIntegral.of_finite Aint Bint
  letI : FaithfulSMul Aint Bint :=
    (faithfulSMul_iff_algebraMap_injective Aint Bint).2 <| by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective Aint v.Completion
      apply (algebraMap v.Completion w.1.Completion).injective
      rw [← IsScalarTower.algebraMap_apply Aint v.Completion w.1.Completion a,
        ← IsScalarTower.algebraMap_apply Aint v.Completion w.1.Completion b,
        IsScalarTower.algebraMap_apply Aint Bint w.1.Completion a,
        IsScalarTower.algebraMap_apply Aint Bint w.1.Completion b]
      exact congrArg (algebraMap Bint w.1.Completion) hab
  letI : Module.IsTorsionFree Aint Bint :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective Aint Bint)
  letI : IsLocalHom (algebraMap Aint Bint) :=
    Algebra.IsIntegral.isLocalHom Aint Bint
  letI : IsGaloisGroup Gal(w.1.Completion/v.Completion) Aint Bint :=
    IsGaloisGroup.of_isFractionRing
      Gal(w.1.Completion/v.Completion) Aint Bint
        v.Completion w.1.Completion
  let tauD :
      Submission.NumberTheory.Milne.absoluteValueDecomposition v w.1 :=
    ⟨tauM, by
      have hm : tauM ∈ MulAction.stabilizer Gal(M/Kc) Q.asIdeal :=
        MulAction.mem_stabilizer_iff.mpr htauMQ
      change tauM ∈ MulAction.stabilizer Gal(M/Kc)
        (Submission.NumberTheory.Milne.nonarchimedeanHeightSpectrum
          w.1 hw hwna).asIdeal at hm
      rw [absolute_decomposition_stabilizer]
      exact absolute_stabilizer_centered
        w.1 hw hwna tauM hm⟩
  let sigmaD :
      Submission.NumberTheory.Milne.absoluteValueDecomposition v w.1 :=
    ⟨sigmaM, by
      have hm : sigmaM ∈ MulAction.stabilizer Gal(M/Kc) Q.asIdeal :=
        MulAction.mem_stabilizer_iff.mpr hsigmaMQ
      change sigmaM ∈ MulAction.stabilizer Gal(M/Kc)
        (Submission.NumberTheory.Milne.nonarchimedeanHeightSpectrum
          w.1 hw hwna).asIdeal at hm
      rw [absolute_decomposition_stabilizer]
      exact absolute_stabilizer_centered
        w.1 hw hwna sigmaM hm⟩
  let eD := decompositionCompletionExtension v w.1
  let tauLocal : Gal(w.1.Completion/v.Completion) := eD tauD
  let sigmaLocal : Gal(w.1.Completion/v.Completion) := eD sigmaD
  have hvna : IsNonarchimedean v :=
    fun x y ↦ (FinitePlace.mk P).add_le x y
  let f := completionDecomposition v hvna w galoisEquiv
  have hfD (z :
      Submission.NumberTheory.Milne.absoluteValueDecomposition
        v w.1) : f (eD z) = galoisEquiv z.1 := by
    simp only [completionDecomposition,
      MulEquiv.toMonoidHom_eq_coe,
      decompositionGaloisCompletion, MonoidHom.coe_comp,
      MonoidHom.coe_coe, Function.comp_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
      EmbeddingLike.apply_eq_iff_eq, f, eD]
    apply AlgEquiv.ext
    intro x
    rfl
  have hftau : f tauLocal = galoisEquiv tauM := by
    exact hfD tauD
  have hfsigma : f sigmaLocal = galoisEquiv sigmaM := by
    exact hfD sigmaD
  let p := extensionPullbackProjection q f
  let xPull : CentralExtensionPullback q f :=
    ⟨(tauLocal, xGlobal), by
      change f tauLocal = q xGlobal
      rw [hftau, hqxGlobal]⟩
  let yPull : CentralExtensionPullback q f :=
    ⟨(sigmaLocal, yGlobal), by
      change f sigmaLocal = q yGlobal
      rw [hfsigma, hqyGlobal]⟩
  have hrelGlobal0 :
      xGlobal ^ (prime i - 1) * ⁅xGlobal, yGlobal0⁆ = 1 := by
    exact rational_preimage_relation
      quotientMap prime frobeniusLift pi alphaE betaA hcompat hkill i
  have hconjGlobal0 : yGlobal0 * xGlobal * yGlobal0⁻¹ =
      xGlobal ^ prime i :=
    (tame_relation_conjugation xGlobal yGlobal0
      (hsetup.prime_isPrime i).one_le).1 hrelGlobal0
  have hconjGlobal : yGlobal * xGlobal * yGlobal⁻¹ =
      xGlobal ^ r := by
    rw [← hir']
    dsimp only [yGlobal]
    rw [mul_inv_rev]
    calc
      (xGlobal ^ a * yGlobal0) * xGlobal *
          (yGlobal0⁻¹ * (xGlobal ^ a)⁻¹) =
          xGlobal ^ a * (yGlobal0 * xGlobal * yGlobal0⁻¹) *
            (xGlobal ^ a)⁻¹ := by group
      _ = xGlobal ^ a * xGlobal ^ prime i * (xGlobal ^ a)⁻¹ := by
        rw [hconjGlobal0]
      _ = xGlobal ^ prime i := by group
  have hconjM : sigmaM * tauM * sigmaM⁻¹ = tauM ^ r := by
    apply galoisEquiv.injective
    have hmap := congrArg q hconjGlobal
    simpa only [map_mul, map_inv, map_pow, hqxGlobal, hqyGlobal] using hmap
  have hconjLocal : sigmaLocal * tauLocal * sigmaLocal⁻¹ =
      tauLocal ^ r := by
    have hconjD : sigmaD * tauD * sigmaD⁻¹ = tauD ^ r := by
      apply Subtype.ext
      exact hconjM
    change eD sigmaD * eD tauD * (eD sigmaD)⁻¹ = (eD tauD) ^ r
    simpa only [map_mul, map_inv, map_pow] using congrArg eD hconjD
  have hconjPull : yPull * xPull * yPull⁻¹ = xPull ^ r := by
    apply Subtype.ext
    exact Prod.ext hconjLocal hconjGlobal
  let ILocal := (IsLocalRing.maximalIdeal Bint).inertia
    Gal(w.1.Completion/v.Completion)
  have htauMInertia : tauM ∈ Q.asIdeal.inertia Gal(M/Kc) := by
    intro z
    have hz := tauGlobal.property z
    have haction : tauM • z = tauGlobal.1 • z := by
      apply NumberField.RingOfIntegers.ext
      have hring : tauM.toRingEquiv = tauGlobal.1.toRingEquiv := rfl
      have hfun : tauM (z : M) = tauGlobal.1 (z : M) :=
        DFunLike.congr_fun hring (z : M)
      simpa only [algebraMap.coe_smul'] using hfun
    rwa [haction]
  have htauLocalI : tauLocal ∈ ILocal := by
    exact (Submission.TBluepr.decomposition_completion_inertia
      v hvna w tauD).mp htauMInertia
  let tauI : ILocal := ⟨tauLocal, htauLocalI⟩
  have hgen0 :=
    (hsetup.generators_tame_inertia i).inertiaGenerator_generates N
  have hILocal (z : ILocal) :=
    obstruction_inertia_action
      (betaA := betaA) (hbetaA := hbetaA) Q
        ((decompositionCompletionExtension
          v w.1).symm z.1).1
        ((Submission.TBluepr.decomposition_completion_inertia
          v hvna w (eD.symm z.1)).mpr (by
            change eD (eD.symm z.1) ∈ ILocal
            rw [eD.apply_symm_apply]
            exact z.property))
  have htauIGenerates : Subgroup.zpowers tauI = ⊤ :=
    obstruction_completed_zpowers
      (v := v) (w := w) (Q := Q) (r := r) (P0 := P0)
      (eLayer := eLayer) (hQunder := hQunder) (eComp := eComp)
      (tau0 := tau0) (hgen0 := hgen0)
      (tauD := tauD) (htauM := htauM) (heComp := fun _ ↦ rfl)
      (ILocal := ILocal) (tauI := tauI) (hILocal := hILocal)
      (htauI := by rfl)
  let n := Nat.card ILocal
  have hnpos : 0 < n := Nat.card_pos
  letI : NeZero n := ⟨hnpos.ne'⟩
  have htauIall : ∀ z : ILocal, z ∈ Subgroup.zpowers tauI := by
    intro z
    rw [htauIGenerates]
    exact Subgroup.mem_top z
  let eI : Multiplicative (ZMod n) ≃* ILocal :=
    zmodMulEquivOfGenerator htauIall rfl
  have heIgen : eI
      (Submission.CField.LBrauer.CyclicH2.generator
        (n := n)) = tauI := by
    simp [eI,
      Submission.CField.LBrauer.CyclicH2.generator]
  have hpxPull : p xPull =
      ILocal.subtype (eI
        (Submission.CField.LBrauer.CyclicH2.generator
          (n := n))) := by
    change tauLocal = (eI
      (Submission.CField.LBrauer.CyclicH2.generator
        (n := n)) : ILocal)
    rw [heIgen]
  have horderTau : orderOf (p xPull) = n := by
    rw [hpxPull]
    exact obstruction_zmod_generator ILocal n eI
  letI : P.asIdeal.LiesOver
      (Ideal.span ({(r : ℤ)} : Set ℤ)) := by
    simpa [Ideal.rationalPrimeIdeal] using hPover
  have hPInertiaDeg :
      (Ideal.rationalPrimeIdeal r).inertiaDeg P.asIdeal = 1 := by
    let eCubeOZ :
        NumberField.RingOfIntegers rationalCubeField ≃ₐ[ℤ]
          NumberField.RingOfIntegers Kc :=
      { eCubeO.toRingEquiv with
        commutes' := by intro z; simp }
    calc
      (Ideal.rationalPrimeIdeal r).inertiaDeg P.asIdeal =
          (Ideal.rationalPrimeIdeal r).inertiaDeg (Pc.map eCubeO) := by
        rw [hPcmap]
      _ = (Ideal.rationalPrimeIdeal r).inertiaDeg Pc := by
        exact Ideal.inertiaDeg_map_eq
          (Ideal.rationalPrimeIdeal r) Pc eCubeOZ
      _ = 1 := rational_cube_deg hr
        (by simpa [← hir'] using hsetup.prime_mod_three i) Pc
  have hPAbsNorm : Ideal.absNorm P.asIdeal = r :=
    obstruction_abs_deg
      P r hr hPover hPInertiaDeg
  have hbaseResidueCard :
      Nat.card (NumberField.RingOfIntegers Kc ⧸
        Q.asIdeal.under (NumberField.RingOfIntegers Kc)) = r := by
    rw [hQK]
    exact obstruction_abs_norm
      P.asIdeal r hPAbsNorm
  have hglobalResidueCard :
      Nat.card (ℤ ⧸ Q.asIdeal.under ℤ) = r := by
    have hQrat : Q.asIdeal.under ℤ = Ideal.rationalPrimeIdeal r :=
      (Q.asIdeal.over_def (Ideal.rationalPrimeIdeal r)).symm
    exact obstruction_int_prime
      Q.asIdeal r hQrat
  have hsigmaMArith : IsArithFrobAt
      (NumberField.RingOfIntegers Kc) sigmaM Q.asIdeal := by
    intro x
    have hx := hsigmaGlobal x
    have hact : sigmaM • x = sigmaGlobal • x := by
      apply NumberField.RingOfIntegers.ext
      have hring : sigmaM.toRingEquiv = sigmaGlobal.toRingEquiv := rfl
      have hfun : sigmaM (x : M) = sigmaGlobal (x : M) :=
        DFunLike.congr_fun hring (x : M)
      simpa only [algebraMap.coe_smul'] using hfun
    change sigmaM • x - x ^ Nat.card
      (NumberField.RingOfIntegers Kc ⧸
        Q.asIdeal.under (NumberField.RingOfIntegers Kc)) ∈ Q.asIdeal
    rw [hact, hbaseResidueCard]
    simpa [hglobalResidueCard] using hx
  have hsigmaResidue (z : Bint) :
      IsLocalRing.residue Bint (sigmaLocal • z) =
        (IsLocalRing.residue Bint z) ^ r := by
    have hz :=
      Submission.TBluepr.decomposition_arith_frob
        v w sigmaD hsigmaMArith z
    simpa [sigmaLocal, eD, Bint, Q, hbaseResidueCard] using hz
  have hbaseCentered :
      nonarchimedeanHeightSpectrum v
        (absolute_value_nontrivial P) hvna = P :=
    nonarchimedean_height_spectrum P
  let eBaseResidue := centeredCompletionResidue v
    (Submission.CField.Ideles.absolute_value_nontrivial P) hvna
  have hAintResidueCard :
      Nat.card (IsLocalRing.ResidueField Aint) = r := by
    calc
      Nat.card (IsLocalRing.ResidueField Aint) =
          Nat.card (NumberField.RingOfIntegers Kc ⧸ P.asIdeal) := by
        rw [← hbaseCentered]
        exact Nat.card_congr eBaseResidue.symm.toEquiv
      _ = Ideal.absNorm P.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      _ = r := hPAbsNorm
  letI : Finite (IsLocalRing.ResidueField Aint) := by
    exact Finite.of_equiv
      (NumberField.RingOfIntegers Kc ⧸ P.asIdeal)
      (hbaseCentered ▸ eBaseResidue).toEquiv
  let eUpperResidue := centeredCompletionResidue w.1 hw hwna
  letI : Finite (IsLocalRing.ResidueField Bint) := by
    exact Finite.of_equiv
      (NumberField.RingOfIntegers M ⧸ Q.asIdeal)
      eUpperResidue.toEquiv
  let pInt := IsLocalRing.maximalIdeal Aint
  let PInt := IsLocalRing.maximalIdeal Bint
  letI : pInt.IsMaximal := IsLocalRing.maximalIdeal.isMaximal Aint
  letI : PInt.IsMaximal := IsLocalRing.maximalIdeal.isMaximal Bint
  letI : Field (Aint ⧸ pInt) := Ideal.Quotient.field pInt
  letI : Field (Bint ⧸ PInt) := Ideal.Quotient.field PInt
  letI : Fintype (IsLocalRing.ResidueField Aint) := Fintype.ofFinite _
  letI : Fintype (IsLocalRing.ResidueField Bint) := Fintype.ofFinite _
  letI : Finite (Aint ⧸ pInt) := by
    change Finite (IsLocalRing.ResidueField Aint)
    infer_instance
  letI : Finite (Bint ⧸ PInt) := by
    change Finite (IsLocalRing.ResidueField Bint)
    infer_instance
  letI : Fintype (Aint ⧸ pInt) := Fintype.ofFinite _
  letI : Fintype (Bint ⧸ PInt) := Fintype.ofFinite _
  letI : PInt.LiesOver pInt := by
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap Aint Bint)).symm
  have hPIntStable : MulAction.stabilizer
      Gal(w.1.Completion/v.Completion) PInt = ⊤ := by
    simpa [PInt] using
      (obstruction_stabilizer_top
        Gal(w.1.Completion/v.Completion) Bint)
  letI : ILocal.Normal :=
    Submission.NumberTheory.Milne.inertia_forall_smul
      PInt (fun sigma ↦ MulAction.mem_stabilizer_iff.mp
        (hPIntStable.symm ▸ Subgroup.mem_top sigma))
  let eResidue :=
    Submission.NumberTheory.Milne.gal_stabilizer_top
      pInt PInt hPIntStable
  have heResidueApply (sigma : Gal(w.1.Completion/v.Completion))
      (z : Bint) :
      eResidue (QuotientGroup.mk' ILocal sigma)
          (Ideal.Quotient.mk PInt z) =
        Ideal.Quotient.mk PInt (sigma • z) := by
    rfl
  let residueFrob : Gal((Bint ⧸ PInt)/(Aint ⧸ pInt)) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (Aint ⧸ pInt) (Bint ⧸ PInt)
  have hsigmaFrob :
      eResidue (QuotientGroup.mk' ILocal sigmaLocal) = residueFrob := by
    apply AlgEquiv.ext
    rintro ⟨z⟩
    change eResidue (QuotientGroup.mk' ILocal sigmaLocal)
        (Ideal.Quotient.mk PInt z) =
      residueFrob (Ideal.Quotient.mk PInt z)
    rw [heResidueApply]
    change IsLocalRing.residue Bint (sigmaLocal • z) =
      (IsLocalRing.residue Bint z) ^
        Fintype.card (IsLocalRing.ResidueField Aint)
    rw [hsigmaResidue]
    rw [← Nat.card_eq_fintype_card, hAintResidueCard]
  let fLocal := Nat.card
    (Gal(w.1.Completion/v.Completion) ⧸ ILocal)
  have hfLocal : 0 < fLocal := Nat.card_pos
  have horderSigma : orderOf
      (QuotientGroup.mk' ILocal sigmaLocal) = fLocal := by
    exact obstruction_frobenius_card
      eResidue (QuotientGroup.mk' ILocal sigmaLocal) hsigmaFrob
  have hgenSigma : Subgroup.zpowers
      (QuotientGroup.mk' ILocal sigmaLocal) = ⊤ := by
    exact obstruction_zpowers_card
      (QuotientGroup.mk' ILocal sigmaLocal) horderSigma
  have hBintResidueCard :
      Nat.card (IsLocalRing.ResidueField Bint) = r ^ fLocal := by
    change Nat.card (Bint ⧸ PInt) = r ^ fLocal
    have hbaseQuotientCard : Nat.card (Aint ⧸ pInt) = r := by
      simpa [pInt] using hAintResidueCard
    have hcard := obstruction_nat_galois
      eResidue
    rw [hbaseQuotientCard] at hcard
    exact hcard
  have hsigmaPowI : sigmaLocal ^ fLocal ∈ ILocal := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' ILocal sigmaLocal) ^ fLocal = 1
    rw [← horderSigma]
    exact pow_orderOf_eq_one _
  let sigmaPowI : ILocal := ⟨sigmaLocal ^ fLocal, hsigmaPowI⟩
  have hsigmaPowTau : sigmaPowI ∈ Subgroup.zpowers tauI := by
    rw [htauIGenerates]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsigmaPowTau
  have hkLocal : sigmaLocal ^ fLocal = tauLocal ^ k := by
    exact congrArg Subtype.val hk.symm
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hc
  have horderXDiv : orderOf xPull ∣ r ^ fLocal - 1 :=
    obstruction_dvd_projection
      p hpc xPull yPull r fLocal k hr.pos hconjPull (by
        change sigmaLocal ^ fLocal = tauLocal ^ k
        exact hkLocal)
  have horderXResidueDiv : orderOf xPull ∣
      Nat.card (IsLocalRing.ResidueField Bint) - 1 := by
    rw [hBintResidueCard]
    exact horderXDiv
  letI : Algebra.IsAlgebraic v.Completion w.1.Completion :=
    Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion
  letI : NontriviallyNormedField w.1.Completion :=
    Submission.NumberTheory.Milne.absoluteNontriviallyNormed
      w.1
  letI : NormedAlgebra v.Completion w.1.Completion := {
    toAlgebra :=
      (Submission.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    norm_smul_le := by
      intro a x
      change ‖Submission.NumberTheory.Milne.completionLies
        v w.1 w.2 a * x‖ ≤ ‖a‖ * ‖x‖
      calc
        _ ≤ ‖Submission.NumberTheory.Milne.completionLies
            v w.1 w.2 a‖ * ‖x‖ := norm_mul_le _ _
        _ = ‖a‖ * ‖x‖ := by
          congr 1
          simpa only [dist_zero_right, map_zero] using
            (Submission.NumberTheory.Milne.completion_lies_isometry
              v w.1 w.2).dist_eq a 0 }
  letI : NormedSpace v.Completion w.1.Completion := {
    norm_smul_le := by
      intro a x
      change ‖Submission.NumberTheory.Milne.completionLies
        v w.1 w.2 a * x‖ ≤ ‖a‖ * ‖x‖
      calc
        _ ≤ ‖Submission.NumberTheory.Milne.completionLies
            v w.1 w.2 a‖ * ‖x‖ := norm_mul_le _ _
        _ = ‖a‖ * ‖x‖ := by
          congr 1
          simpa only [dist_zero_right, map_zero] using
            (Submission.NumberTheory.Milne.completion_lies_isometry
              v w.1 w.2).dist_eq a 0 }
  letI : ProperSpace w.1.Completion :=
    FiniteDimensional.proper v.Completion w.1.Completion
  haveI : LocallyCompactSpace w.1.Completion := inferInstance
  letI : ValuativeRel w.1.Completion :=
    ValuativeRel.ofValuation
      (NormedField.valuation (K := w.1.Completion))
  letI : Valuation.Compatible
      (NormedField.valuation (K := w.1.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := w.1.Completion))
  letI : IsNonarchimedeanLocalField w.1.Completion :=
    absoluteExtensionNonarchimedean
      w.1
  letI : CharZero w.1.Completion :=
    (RingHom.charZero_iff
      (algebraMap v.Completion w.1.Completion).injective).mp inferInstance
  have hBintVal :
      Valuation.integer (ValuativeRel.valuation w.1.Completion) = Bint := by
    ext x
    simp only [Bint, Submission.NumberTheory.Milne.completionIntegerRing,
      Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation w.1.Completion).vle_one_iff,
      ← (NormedField.valuation (K := w.1.Completion)).vle_one_iff]
  letI : IsDiscreteValuationRing Bint :=
    hBintVal ▸ discrete_valuation_ring w.1.Completion
  letI : HenselianLocalRing Bint :=
    hBintVal ▸ integer_henselian_ring w.1.Completion
  let m := orderOf xPull
  have hmpos : 0 < m := orderOf_pos xPull
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hresidueCardLocal : localResidueCard w.1.Completion =
      Nat.card (IsLocalRing.ResidueField Bint) := by
    rfl
  have hqCoprimeSub : (r ^ fLocal).Coprime (r ^ fLocal - 1) :=
    obstruction_coprime_sub r fLocal hr.ne_zero
  have hqCoprimeM : (r ^ fLocal).Coprime m :=
    Nat.Coprime.coprime_dvd_right horderXDiv hqCoprimeSub
  have hmCoprime : (localResidueCard w.1.Completion).Coprime m := by
    rw [hresidueCardLocal, hBintResidueCard]
    exact hqCoprimeM
  have hmUnit : IsUnit (m : Bint) := by
    have hu := cast_coprime_card
      w.1.Completion m hmCoprime
    rw [hBintVal] at hu
    exact hu
  have hmDiv : m ∣ Nat.card (IsLocalRing.ResidueField Bint) - 1 := by
    exact horderXResidueDiv
  obtain ⟨zetaLocal, hzetaLocal, hzetaLocalI, hzetaLocalSigma⟩ :=
    primitive_inertia_fixed
      (B := Bint) (F := w.1.Completion)
      (G := Gal(w.1.Completion/v.Completion))
      (by
        intro x y hxy
        exact Subtype.ext hxy)
      (fun sigma z ↦ algebraMap.coe_smul'
        (B := Bint) (C := w.1.Completion) sigma z)
      (fun sigma z ↦ Units.coe_smul sigma z)
      m hmUnit sigmaLocal r
      (fun z ↦ hsigmaResidue z) hmDiv
  let pI : CentralExtensionPullback q f →*
      Gal(w.1.Completion/v.Completion) ⧸ ILocal :=
    (QuotientGroup.mk' ILocal).comp p
  have hpI : Function.Surjective pI :=
    (QuotientGroup.mk'_surjective ILocal).comp hp
  have hpIker : pI.ker = ILocal.comap p := by
    ext z
    simp [pI, MonoidHom.mem_ker]
  let ePullQuot :
      (CentralExtensionPullback q f ⧸ ILocal.comap p) ≃*
        (Gal(w.1.Completion/v.Completion) ⧸ ILocal) :=
    (QuotientGroup.quotientMulEquivOfEq hpIker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective pI hpI)
  have hePullY : ePullQuot
      (QuotientGroup.mk' (ILocal.comap p) yPull) =
        QuotientGroup.mk' ILocal sigmaLocal := by
    rfl
  have horderPullY : orderOf
      (QuotientGroup.mk' (ILocal.comap p) yPull) = fLocal := by
    calc
      orderOf (QuotientGroup.mk' (ILocal.comap p) yPull) =
          orderOf (QuotientGroup.mk' ILocal sigmaLocal) := by
        rw [← ePullQuot.orderOf_eq, hePullY]
      _ = fLocal := horderSigma
  have hgenPullY : Subgroup.zpowers
      (QuotientGroup.mk' (ILocal.comap p) yPull) = ⊤ := by
    apply obstruction_zpowers_card
    calc
      orderOf (QuotientGroup.mk' (ILocal.comap p) yPull) =
          fLocal := horderPullY
      _ = Nat.card (CentralExtensionPullback q f ⧸ ILocal.comap p) := by
        exact Nat.card_congr ePullQuot.symm.toEquiv
  let ePullKernel := centralExtensionPullback q f
  let phiLocal := completionKernelUnits v w kernelToUnits
  let phiPull : p.ker →* w.1.Completionˣ :=
    phiLocal.comp ePullKernel.toMonoidHom
  have hphiPull : Function.Injective phiPull := by
    intro z z' hzz'
    apply ePullKernel.injective
    apply hkernelToUnits
    apply Units.map_injective
      (Submission.NumberTheory.Milne.completionEmbedding w.1).injective
    exact hzz'
  have hfixedPull : ∀ sigma : Gal(w.1.Completion/v.Completion),
      ∀ z : p.ker, sigma • phiPull z = phiPull z := by
    intro sigma z
    exact completion_units_fixed v hvna w kernelToUnits hfixed
      sigma (ePullKernel z)
  have hzetaPullY : p yPull • zetaLocal = zetaLocal ^ r := by
    exact hzetaLocalSigma
  have hordLocal : ∀ sigma : Gal(w.1.Completion/v.Completion),
      ∀ z : w.1.Completionˣ,
        localOrderHom w.1.Completion (sigma • z) =
          localOrderHom w.1.Completion z := by
    intro sigma z
    exact obstruction_order_smul
      (betaA := betaA) (hbetaA := hbetaA) (P := P) (w := w)
      (hvle := fun _ _ ↦ Iff.rfl) (sigma := sigma) (z := z)
  let eArel :
      Valuation.integer (ValuativeRel.valuation v.Completion) ≃+*
        Aint :=
    RingEquiv.subringCongr hAintVal
  letI : Algebra
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      v.Completion :=
    (Valuation.integer
      (ValuativeRel.valuation v.Completion)).subtype.toAlgebra
  letI : Algebra
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      Bint :=
    ((algebraMap Aint Bint).comp eArel.toRingHom).toAlgebra
  letI : Algebra
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      w.1.Completion :=
    ((Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).comp
        (Valuation.integer
          (ValuativeRel.valuation v.Completion)).subtype).toAlgebra
  let hscalarB : IsScalarTower
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      Bint w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      rfl
  letI : IsScalarTower
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      Bint w.1.Completion := hscalarB
  letI : IsScalarTower
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hintegralClosureB : IsIntegralClosure Bint
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      w.1.Completion := by
    refine
      { algebraMap_injective := by
          intro x y hxy
          exact Subtype.ext hxy
        isIntegral_iff := ?_ }
    intro x
    exact (RingEquiv.isIntegral_iff eArel (by ext y; rfl) x).trans
      (IsIntegralClosure.isIntegral_iff
        (R := Aint) (A := Bint))
  letI : IsIntegralClosure Bint
      (Valuation.integer (ValuativeRel.valuation v.Completion))
      w.1.Completion := hintegralClosureB
  letI : SMulDistribClass Gal(w.1.Completion/v.Completion)
      Bint w.1.Completion :=
    ⟨fun g b x ↦ by
      change g ((b : w.1.Completion) * x) =
        ((g • b : Bint) : w.1.Completion) * g x
      rw [map_mul]
      congr 1
      exact (algebraMap.coe_smul'
        (B := Bint) (C := w.1.Completion) g b).symm⟩
  have hnormLocal : ∀ c : w.1.Completionˣ,
      (∀ g : Gal(w.1.Completion/v.Completion), g • c = c) →
      localOrderHom w.1.Completion c = 1 →
        ∃ b : w.1.Completionˣ,
          (∀ i : ILocal, i.1 • b = b) ∧
            (∏ j ∈ Finset.range fLocal,
              (p yPull) ^ j • b) = c := by
    exact @inertia_equation_model
      v.Completion w.1.Completion Bint
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      hscalarB inferInstance hintegralClosureB inferInstance inferInstance
      inferInstance sigmaLocal fLocal hfLocal horderSigma hgenSigma
  let tameData : TamePrimitiveData
      q galoisEquiv kernelToUnits P w ILocal n := {
    hphi := hphiPull
    eI := eI
    x := xPull
    hx := hpxPull
    horderX := horderTau
    y := yPull
    r := r
    hconj := hconjPull
    zeta := zetaLocal
    hzeta := hzetaLocal
    hzetaI := hzetaLocalI
    hzetaY := hzetaPullY
    degree := fLocal
    hdegree := hfLocal
    horder := horderPullY
    hgen := hgenPullY
    ord := localOrderHom w.1.Completion
    hord := hordLocal
    hnorm := hnormLocal }
  apply change_tame_primitive
    q hq hc galoisEquiv kernelToUnits hfixed P w ILocal n
  exact tameData

end PrimeInS

end TBluepr
end Submission
