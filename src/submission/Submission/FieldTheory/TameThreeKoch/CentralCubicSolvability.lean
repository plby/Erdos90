import Submission.FieldTheory.TameThreeKoch.FiniteLocalObstructions
import Submission.FieldTheory.TameThreeKoch.AbsoluteLiftTransport
import Submission.FieldTheory.TameThreeKoch.CyclotomicCompatibility
import Submission.FieldTheory.TameThreeKoch.LiftProjectedInertia
import Submission.ClassField.CyclotomicBrauer.LocalizationInjectivity

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v

open NumberField
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.CBrauer
open Submission.CField.RExist
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

/-- Theorem VII.7.1 in the adic-completion presentation used by the tame
embedding argument. -/
private theorem brauer_all_completions
    (K : Type u) [Field K] [NumberField K]
    (beta : BrauerGroup K)
    (hlocal : ∀ place : NumberFieldPlace K,
      Submission.CField.BGroups.brauerBaseChange
        K (Submission.CField.Ideles.placeCompletion K place) beta = 1) :
    beta = 1 := by
  let data := brauerData K
  apply Additive.ofMul.injective
  apply brauerLocalization_injective K
  apply DirectSum.ext
  intro place
  change (DirectSum.component ℤ (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup
        (Submission.CField.RExist.placeCompletion
          K v))) place)
        (data.localization.localization (Additive.ofMul beta)) =
    (DirectSum.component ℤ (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup
        (Submission.CField.RExist.placeCompletion
          K v))) place)
        (data.localization.localization (Additive.ofMul 1))
  rw [data.localization.localization_apply,
    data.localization.localization_apply]
  rw [data.localizeAt_eq, data.localizeAt_eq, map_one]
  cases place with
  | inl P =>
      letI : Algebra K (FinitePlace.mk P).val.Completion :=
        (Submission.NumberTheory.Milne.completionEmbedding
          (FinitePlace.mk P).val).toAlgebra
      letI : Algebra K (P.adicCompletion K) :=
        (FinitePlace.embedding P).toAlgebra
      let e : (FinitePlace.mk P).val.Completion ≃ₐ[K] P.adicCompletion K :=
        AlgEquiv.ofRingEquiv
          (f := placeCompletionAdic P)
          (finite_place_adic P)
      have hnormalized := brauer_change_alg
        K (P.adicCompletion K) (FinitePlace.mk P).val.Completion
          e.symm beta
          (by
            simpa only [Submission.CField.Ideles.placeCompletion] using
              hlocal (.inl P))
      exact congrArg Additive.ofMul hnormalized
  | inr v =>
      exact congrArg Additive.ofMul
        (by
          simpa only [Submission.CField.Ideles.placeCompletion] using
            hlocal (.inr v))

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the finite-field and cohomology tower instances.
set_option maxHeartbeats 60000000 in
-- The proof combines several finite-field towers and cohomology transports.
/--
The central cubic Koch--Shafarevich embedding step.  The global Brauer
obstruction is killed by the injective localization theorem VII.7.1; the full
fundamental exact sequence VIII.4.2 is not needed here.
-/
theorem rational_cft_solvable
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
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧
        pi.comp betaE = betaA ∧
          ∀ i : Fin d,
            betaE (quotientMap (free.generator i)) =
              alphaE (free.generator i) := by
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
  let zetaM : M := algebraMap Kc M zeta
  have hzetaM : IsPrimitiveRoot zetaM 3 :=
    hzeta.map_of_injective (algebraMap Kc M).injective
  apply rational_preliminary_lift
    hsetup pi hpi hE hA hkernel_central hkernel_card
      alphaE halphaE hkill betaA hcompat
  -- Construct the local weak solutions from `hkill`, kill the resulting
  -- global obstruction, descend the weak solution to `ℚ`, and remove its
  -- ramification outside `S`.
  have hfinite :
      ∀ P : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers Kc),
        @Submission.CField.BGroups.brauerBaseChange
            Kc (P.adicCompletion Kc) inferInstance inferInstance
            (FinitePlace.embedding P).toAlgebra
            (extensionRelativeBrauer q hq hc galoisEquiv
              kernelToUnits hfixed : BrauerGroup Kc) = 1 := by
    exact cft_obstructions_vanish
      hsetup pi hpi hE hA hkernel_central hkernel_card
        alphaE halphaE hkill betaA hcompat
  have hzero :
      centralExtensionClass q hq hc galoisEquiv
        kernelToUnits hfixed = 1 := by
    let beta : BrauerGroup Kc :=
      extensionRelativeBrauer q hq hc galoisEquiv
        kernelToUnits hfixed
    have hlocal : ∀ place : NumberFieldPlace Kc,
        Submission.CField.BGroups.brauerBaseChange
          Kc (Submission.CField.Ideles.placeCompletion Kc place) beta = 1 := by
      intro place
      cases place with
      | inl P =>
          exact hfinite P
      | inr v =>
          change @Submission.CField.BGroups.brauerBaseChange
            Kc v.1.Completion inferInstance inferInstance
              (Submission.NumberTheory.Milne.completionEmbedding
                v.1).toAlgebra beta = 1
          rw [completion_embedding_base]
          exact brauer_primitive_cube
            zeta hzeta v beta
    have hbeta : beta = 1 :=
      brauer_all_completions Kc beta hlocal
    apply (extension_relative_brauer
      q hq hc galoisEquiv kernelToUnits hfixed).1
    apply Subtype.ext
    exact hbeta
  let j : M →ₐ[Kc] SeparableClosure Kc := IsSepClosed.lift
  obtain ⟨F, hMF, liftF, hliftF⟩ :=
    cubic_weak_solution j q hq hc hqKernelCard
      galoisEquiv kernelToUnits hkernelToUnits hfixed hqKernelCube
      zetaM hzetaM hzero
  -- Regard the fixed separable closure of `Kc` as an algebraic closure of
  -- `ℚ`.  The subgroup fixing the embedded copy of `Kc` is the index-two
  -- subgroup on which `liftF` gives the cyclotomic weak solution.
  letI : IsScalarTower ℚ Kc (SeparableClosure Kc) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      simp
  letI : Algebra.IsAlgebraic ℚ (SeparableClosure Kc) :=
    Algebra.IsAlgebraic.trans ℚ Kc (SeparableClosure Kc)
  letI : Normal ℚ (SeparableClosure Kc) :=
    normal_iff.mpr fun x =>
      ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  letI : IsGalois ℚ (SeparableClosure Kc) := ⟨⟩
  let iKc : Kc →ₐ[ℚ] SeparableClosure Kc :=
    IsScalarTower.toAlgHom ℚ Kc (SeparableClosure Kc)
  let KcInClosure : IntermediateField ℚ (SeparableClosure Kc) :=
    iKc.fieldRange
  let eKcInClosure : Kc ≃ₐ[ℚ] KcInClosure :=
    algHomRange iKc
  letI : FiniteDimensional ℚ KcInClosure :=
    Module.Finite.equiv eKcInClosure.toLinearEquiv
  let H : Subgroup Gal(SeparableClosure Kc/ℚ) :=
    KcInClosure.fixingSubgroup
  have hindexH : H.index = 2 := by
    change KcInClosure.fixingSubgroup.index = 2
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index KcInClosure]
    calc
      Module.finrank ℚ KcInClosure = Module.finrank ℚ Kc :=
        LinearEquiv.finrank_eq eKcInClosure.symm.toLinearEquiv
      _ = Module.finrank ℚ rationalCubeField :=
        LinearEquiv.finrank_eq eCubeRoot.symm.toLinearEquiv
      _ = 2 := rational_cube_finrank
  letI : H.FiniteIndex := ⟨by rw [hindexH]; norm_num⟩
  have hcoprimeH : Nat.Coprime H.index 3 := by
    rw [hindexH]
    norm_num
  let toCyclotomicAbsolute : H →* Gal(SeparableClosure Kc/Kc) :=
    fixingRelativeAut
  have htoCyclotomicAbsolute_apply (sigma : H) (z : SeparableClosure Kc) :
      toCyclotomicAbsolute sigma z =
        (sigma : Gal(SeparableClosure Kc/ℚ)) z := by
    rfl
  let restrictToF : H →* Gal(F/Kc) :=
    (absoluteRestrictionHom (K := Kc) F).comp
      toCyclotomicAbsolute
  let liftH : H →* centralExtensionPreimage pi betaA.range :=
    liftF.comp restrictToF
  let restrictToM : H →* Gal(M/Kc) :=
    (algFieldRange j).autCongr.symm.toMonoidHom.comp
      ((absoluteRestrictionHom
        (K := Kc) (galoisFieldRange j)).comp
          toCyclotomicAbsolute)
  have hqLiftH : q.comp liftH =
      galoisEquiv.toMonoidHom.comp restrictToM := by
    simpa only [liftH, restrictToF, restrictToM] using
      (restricted_lift_projection
        j F hMF q galoisEquiv liftF hliftF toCyclotomicAbsolute)
  -- The base homomorphism over `ℚ` is restriction to the embedded copy of
  -- the original finite three-extension, followed by its canonical
  -- identification with `betaA.range`.
  let jQ : M →ₐ[ℚ] SeparableClosure Kc := j.restrictScalars ℚ
  let iLc : Lc →ₐ[ℚ] SeparableClosure Kc := jQ.comp Lc.val
  let LcInClosure : IntermediateField ℚ (SeparableClosure Kc) :=
    iLc.fieldRange
  let eLcInClosure : Lc ≃ₐ[ℚ] LcInClosure :=
    algHomRange iLc
  letI : FiniteDimensional ℚ LcInClosure :=
    Module.Finite.equiv eLcInClosure.toLinearEquiv
  letI : IsGalois ℚ LcInClosure :=
    @IsGalois.of_algEquiv ℚ Lc inferInstance inferInstance LcInClosure
      inferInstance inferInstance inferInstance hLcGalois eLcInClosure
  letI : Normal ℚ LcInClosure :=
    (inferInstance : IsGalois ℚ LcInClosure).to_normal
  let layerEquiv : Gal(Lc/ℚ) ≃* betaA.range :=
    (AlgEquiv.autCongr eLc).symm.trans
      ((AlgEquiv.autCongr
        (rationalTameClosure S N)).symm.trans
          (rational_tame_range betaA hbetaA))
  let rangeEquiv : Gal(LcInClosure/ℚ) ≃* betaA.range :=
    (AlgEquiv.autCongr eLcInClosure).symm.trans layerEquiv
  let restrictToLc : Gal(SeparableClosure Kc/ℚ) →* Gal(LcInClosure/ℚ) :=
    AlgEquiv.restrictNormalHom LcInClosure
  let fAbs : Gal(SeparableClosure Kc/ℚ) →* betaA.range :=
    rangeEquiv.toMonoidHom.comp restrictToLc
  -- The finite Kummer field, viewed over `ℚ`, cuts out an open subgroup.
  -- Its normal core is the open normal subgroup through which the eventual
  -- descended lift factors.
  let FoverQ : IntermediateField ℚ (SeparableClosure Kc) :=
    F.toIntermediateField.restrictScalars ℚ
  have hKcF : KcInClosure ≤ FoverQ := by
    intro x hx
    obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange (f := iKc)).1 hx
    rw [← hy]
    exact F.toIntermediateField.algebraMap_mem y
  let iKcF : Kc →ₐ[ℚ] FoverQ :=
    (IntermediateField.inclusion hKcF).comp eKcInClosure.toAlgHom
  letI : Algebra Kc FoverQ := iKcF.toAlgebra
  letI : IsScalarTower ℚ Kc FoverQ :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      rfl
  letI : FiniteDimensional ℚ FoverQ := by
    change FiniteDimensional ℚ F
    exact FiniteDimensional.trans ℚ Kc F
  let J : Subgroup Gal(SeparableClosure Kc/ℚ) :=
    FoverQ.fixingSubgroup
  have hJopen : IsOpen (J : Set Gal(SeparableClosure Kc/ℚ)) := by
    exact IntermediateField.fixingSubgroup_isOpen FoverQ
  have hJclosed : IsClosed (J : Set Gal(SeparableClosure Kc/ℚ)) := by
    exact IntermediateField.fixingSubgroup_isClosed FoverQ
  letI : Finite (Gal(SeparableClosure Kc/ℚ) ⧸ J) :=
    J.quotient_finite_of_isOpen hJopen
  letI : J.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let Nabs : OpenNormalSubgroup Gal(SeparableClosure Kc/ℚ) :=
    { toSubgroup := Subgroup.normalCore J
      isOpen' :=
        Subgroup.isOpen_of_isClosed_of_finiteIndex _
          (Subgroup.normalCore_isClosed J hJclosed)
      isNormal' := Subgroup.normalCore_normal J }
  have hLcF : LcInClosure ≤ FoverQ := by
    intro x hx
    obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange (f := iLc)).1 hx
    rw [← hy]
    apply hMF
    exact (AlgHom.mem_fieldRange (f := j)).2 ⟨(y : M), rfl⟩
  have hJH : J ≤ H := by
    exact IntermediateField.fixingSubgroup_le hKcF
  have hNH : (Nabs : Subgroup Gal(SeparableClosure Kc/ℚ)) ≤ H :=
    le_trans J.normalCore_le hJH
  have hNlift : ∀ x : Nabs, liftH ⟨x, hNH x.2⟩ = 1 := by
    simpa only [liftH, restrictToF] using
      (restricted_lift_fixes
        F H (Nabs : Subgroup Gal(SeparableClosure Kc/ℚ)) hNH
          toCyclotomicAbsolute htoCyclotomicAbsolute_apply liftF
          (fun x y => J.normalCore_le x.2 ⟨y, y.2⟩))
  have hNf :
      (Nabs : Subgroup Gal(SeparableClosure Kc/ℚ)) ≤ fAbs.ker := by
    simpa only [fAbs, restrictToLc] using
      (comp_restrict_fixes
        LcInClosure (inferInstance : Normal ℚ LcInClosure) rangeEquiv
          (Nabs : Subgroup Gal(SeparableClosure Kc/ℚ))
          (le_trans J.normalCore_le
            (IntermediateField.fixingSubgroup_le hLcF)))
  have hrestrictToM_apply (sigma : H) (y : M) :
      j (restrictToM sigma y) =
        (sigma : Gal(SeparableClosure Kc/ℚ)) (j y) := by
    calc
      j (restrictToM sigma y) =
          toCyclotomicAbsolute sigma (j y) := by
        simpa only [restrictToM, MonoidHom.comp_apply] using
          (range_absolute_restriction
            j (toCyclotomicAbsolute sigma) y)
      _ = (sigma : Gal(SeparableClosure Kc/ℚ)) (j y) :=
        htoCyclotomicAbsolute_apply sigma (j y)
  have hrestrictToLc_apply
      (rho : Gal(SeparableClosure Kc/ℚ)) (x : Lc) :
      iLc ((AlgEquiv.autCongr eLcInClosure).symm
        (restrictToLc rho) x) = rho (iLc x) := by
    simpa only [eLcInClosure, LcInClosure, restrictToLc] using
      (alg_restrict_normal iLc
        (by
          change Normal ℚ LcInClosure
          infer_instance)
        rho x)
  letI : Normal ℚ Lc := hLcGalois.to_normal
  have hrestrictionCompatible (sigma : H) :
      rationalTameCyclotomic S N
          hsetup.target_pro_three (restrictToM sigma) =
        (AlgEquiv.autCongr eLcInClosure).symm
          (restrictToLc (sigma : Gal(SeparableClosure Kc/ℚ))) := by
    exact galois_restriction_compatible
      (rationalTameCyclotomic S N
        hsetup.target_pro_three)
      j iLc eLcInClosure H.subtype restrictToM restrictToLc
      (by
        intro tau x
        apply congrArg j
        exact @IntermediateField.restrictRestrictAlgEquivMapHom_apply
          ℚ M inferInstance inferInstance inferInstance Lc Kc
            hLcGalois.to_normal tau x)
      hrestrictToM_apply hrestrictToLc_apply sigma
  have hbaseH :
      galoisEquiv.toMonoidHom.comp restrictToM =
        fAbs.comp H.subtype := by
    apply MonoidHom.ext
    intro sigma
    simp only [MonoidHom.comp_apply]
    change galoisEquiv (restrictToM sigma) =
      rangeEquiv (restrictToLc (sigma : Gal(SeparableClosure Kc/ℚ)))
    change layerEquiv
        (rationalTameCyclotomic S N
          hsetup.target_pro_three (restrictToM sigma)) =
      layerEquiv ((AlgEquiv.autCongr eLcInClosure).symm
        (restrictToLc (sigma : Gal(SeparableClosure Kc/ℚ))))
    exact congrArg layerEquiv (hrestrictionCompatible sigma)
  have hliftHAbs : q.comp liftH = fAbs.comp H.subtype :=
    hqLiftH.trans hbaseH
  obtain ⟨liftAbsQ, hliftAbsQContinuous, hliftAbsQ⟩ :=
    continuous_coprime_index
      q hq hc fAbs H 3 hcoprimeH hqKernelCube liftH hliftHAbs
        Nabs hNH hNf hNlift
  -- Move the preliminary lift to the fixed algebraic closure used to define
  -- `G_S(ℚ)(3)`.  The chosen equivalence extends the already fixed copy of
  -- the finite layer, so the projected homomorphism remains the canonical
  -- restriction of `betaA`.
  letI : IsAlgClosure ℚ (SeparableClosure Kc) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instIsAlgClosure ℚ
  let iStandard : LcInClosure →ₐ[ℚ] AlgebraicClosure ℚ :=
    L0.val.comp (eLc.symm.toAlgHom.comp eLcInClosure.symm.toAlgHom)
  let eOmega : SeparableClosure Kc ≃ₐ[ℚ] AlgebraicClosure ℚ :=
    algClosureExtending iStandard
  let transportAbsolute : Gal(AlgebraicClosure ℚ/ℚ) →*
      Gal(SeparableClosure Kc/ℚ) :=
    (AlgEquiv.autCongr eOmega).symm.toMonoidHom
  let liftStandard : Gal(AlgebraicClosure ℚ/ℚ) →*
      centralExtensionPreimage pi betaA.range :=
    liftAbsQ.comp transportAbsolute
  have heOmega : ∀ x : LcInClosure,
      eOmega x =
        ((eLc.trans eLcInClosure).symm x : AlgebraicClosure ℚ) := by
    intro x
    have h := DFunLike.congr_fun
      (alg_extending_domain
        (K := ℚ) (L := LcInClosure)
        (Omega := SeparableClosure Kc) (Omega' := AlgebraicClosure ℚ)
        iStandard) x
    change eOmega x = iStandard x at h
    exact h
  have hliftStandard : q.comp liftStandard =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S) := by
    exact transport_absolute_projection
      betaA hbetaA Lc eLc LcInClosure eLcInClosure rangeEquiv rfl
        q liftAbsQ hliftAbsQ eOmega heOmega
  have hliftStandardContinuous : Continuous liftStandard :=
    hliftAbsQContinuous.comp (aut_congr_continuous eOmega)
  obtain ⟨D0, liftFinite, hliftStandardKer,
      hliftFinite, hliftFiniteInjective⟩ :=
    intermediate_fixed_faithful
      liftStandard hliftStandardContinuous
  have hPreThree :
      IsPGroup 3 (centralExtensionPreimage pi betaA.range) :=
    hE.to_subgroup (centralExtensionPreimage pi betaA.range)
  have hD0three : IsPGroup 3 Gal(D0/ℚ) :=
    galois_fixed_target
      hPreThree liftStandard D0 hliftStandardKer
  have hD0fixing_le_L0 : D0.toIntermediateField.fixingSubgroup ≤
      L0.fixingSubgroup := by
    exact rational_tame_fixing
      N betaA hbetaA rfl q liftStandard hliftStandard D0
        hliftStandardKer
  have hL0D0 : L0 ≤ D0.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L0,
      ← InfiniteGalois.fixedField_fixingSubgroup D0.toIntermediateField]
    exact IntermediateField.fixedField_le hD0fixing_le_L0
  have hthreeNotMem : 3 ∉ S := by
    intro hthree
    rw [← hsetup.prime_range] at hthree
    obtain ⟨i, _hi, hprime⟩ := Finset.mem_image.mp hthree
    have hmod := hsetup.prime_mod_three i
    rw [hprime] at hmod
    norm_num at hmod
  have hbaseInertia : ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        q (liftFinite
          (tameCyclotomicRestriction
            D0 hD0three S sigma.1)) = 1 := by
    exact rational_tame_projected
      N betaA hbetaA rfl q liftStandard hliftStandard D0 hD0three
        liftFinite hliftFinite hL0D0
  obtain ⟨chiTame, chiTameAbs, hchiTameInflates,
      hchiTameContinuous, hchiTameCancel, hchiTameSupport⟩ :=
    tame_injective_lift
      D0 hD0three S q hc liftFinite hliftFiniteInjective
        hqKernelCube hbaseInertia
  have hchiTameKillAway :=
    kills_inertia_away
      D0 hD0three S q hc liftFinite hbaseInertia chiTame
        hchiTameCancel hchiTameSupport
  let Dthree := nineCorrectionCompositum D0
  let Pthree := rationalNineAbove D0
  have hbaseThree : ∀ sigma : Pthree.inertia Gal(Dthree/ℚ),
      q (liftFinite (nineRestrictionLift D0 sigma.1)) = 1 := by
    simpa only [Dthree, Pthree] using
      (rational_projected_inertia
        N betaA hbetaA rfl q liftStandard hliftStandard D0
          liftFinite hliftFinite hL0D0 hthreeNotMem)
  obtain ⟨chiThree, chiThreeAbs, hchiThreeInflates,
      hchiThreeContinuous, hchiThreeCancel, hchiThreeSupport⟩ :=
    canonical_nine_reciprocity
      D0 q hc liftFinite hqKernelCube hbaseThree
  have hD0leThree : D0.toIntermediateField ≤ Dthree.toIntermediateField :=
    le_sup_left
  have hrestrictThree :
      finiteGaloisRestriction D0 Dthree hD0leThree =
        nineRestrictionLift D0 := by
    apply MonoidHom.ext
    intro rho
    obtain ⟨tau, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := Dthree) (E := AlgebraicClosure ℚ) rho
    rw [restriction_restrict_hom,
      nine_restriction_restrict]
  have hchiTameThree : ∀
      (P : Ideal (NumberField.RingOfIntegers
        (tameCorrectionCompositum D0 hD0three S))),
      P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal 3) →
        ∀ sigma : P.inertia
          Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
            chiTame sigma.1 = 1 := by
    intro P hPprime hPover sigma
    exact hchiTameSupport 3 Nat.prime_three
      (fun i hi => i.prime_ne_three hi.symm) P hPprime hPover sigma
  have hchiThreeCancelE : ∀ sigma : Pthree.inertia Gal(Dthree/ℚ),
      (chiThree sigma.1 : centralExtensionPreimage pi betaA.range) *
        liftFinite
          (finiteGaloisRestriction D0 Dthree hD0leThree sigma.1) = 1 := by
    intro sigma
    have h := congrArg Subtype.val (hchiThreeCancel sigma)
    simpa [rationalNineInertia, hrestrictThree] using h
  have hkillThree := full_compositum_hkill
    D0 hD0three S q hc liftFinite chiTame hchiTameThree
      Dthree hD0leThree chiThree Pthree
      (rational_nine_above D0)
      (nine_above_lies D0)
      hchiThreeCancelE
  have hkillAway := full_hkill_away
    D0 hD0three S q liftFinite chiTame Dthree chiThree
      hchiTameKillAway hchiThreeSupport
  obtain ⟨chiFinite, corrected, hchiValues, hchiInflates,
      hcorrected, hcorrectedKill, hcorrectedUnramified⟩ :=
    full_inflated_corrections
      D0 hD0three S q hc liftFinite chiTame Dthree chiThree
        hkillThree hkillAway
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  let liftFull := liftFinite.comp
    (fullRestrictionLift D0 hD0three S Dthree)
  let correctedAbs : Gal(AlgebraicClosure ℚ/ℚ) →*
      centralExtensionPreimage pi betaA.range :=
    corrected.comp (AlgEquiv.restrictNormalHom Dfull.toIntermediateField)
  have hcorrectedProjection : q.comp corrected = q.comp liftFull := by
    rw [hcorrected]
    exact central_twist_projection liftFull chiFinite hc
  have hcorrectedAbsProjection :
      q.comp correctedAbs = betaA.rangeRestrict.comp
        (rationalAbsoluteRestriction S) := by
    apply MonoidHom.ext
    intro tau
    calc
      q (correctedAbs tau) = q (liftFull
          (AlgEquiv.restrictNormalHom Dfull.toIntermediateField tau)) :=
        DFunLike.congr_fun hcorrectedProjection
          (AlgEquiv.restrictNormalHom Dfull.toIntermediateField tau)
      _ = q (liftFinite
          (AlgEquiv.restrictNormalHom D0.toIntermediateField tau)) := by
        change q (liftFinite
          (fullRestrictionLift D0 hD0three S Dthree
            (AlgEquiv.restrictNormalHom Dfull.toIntermediateField tau))) = _
        rw [show fullRestrictionLift D0 hD0three S Dthree
            (AlgEquiv.restrictNormalHom Dfull.toIntermediateField tau) =
              AlgEquiv.restrictNormalHom D0.toIntermediateField tau from
          restriction_restrict_hom D0 Dfull _ tau]
      _ = q (liftStandard tau) :=
        congrArg q (DFunLike.congr_fun hliftFinite tau)
      _ = betaA.rangeRestrict
          (rationalAbsoluteRestriction S tau) :=
        DFunLike.congr_fun hliftStandard tau
  obtain ⟨betaPre, hbetaPreContinuous, hbetaPre⟩ :=
    rational_preliminary_cleanup
      S hPreThree q betaA.rangeRestrict correctedAbs
        hcorrectedAbsProjection Dfull corrected rfl hcorrectedKill
  let beta0 : rationalTameGalois S →* E :=
    (centralExtensionPreimage pi betaA.range).subtype.comp betaPre
  refine ⟨beta0, ?_, ?_⟩
  · exact (continuous_of_discreteTopology : Continuous
      (centralExtensionPreimage pi betaA.range).subtype).comp
        hbetaPreContinuous
  apply MonoidHom.ext
  intro gamma
  have h := DFunLike.congr_fun hbetaPre gamma
  exact congrArg Subtype.val h

end TBluepr
end Submission
