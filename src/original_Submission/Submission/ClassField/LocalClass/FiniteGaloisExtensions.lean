import Submission.ClassField.LocalClass.CanonicalUnramifiedEquiv
import Submission.ClassField.LocalClass.CentralizerTotallyEmbedding
import Submission.ClassField.LocalClass.IntegralModelTotal
import Submission.ClassField.LocalClass.CanonicalClassReduction
import Submission.ClassField.LocalClass.ResidueSurjectivityTransport
import Submission.ClassField.CrossedProducts.CrossedProductGalois
import Submission.ClassField.LocalBrauer.CanonicalCarryMul
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Lemma III.2.2 for finite Galois extensions

This file proves that the canonical local Brauer class of denominator the
degree of a finite Galois extension belongs to its relative Brauer group.
The proof separates the maximal unramified subextension and embeds the
totally ramified remainder in the centralizer of the unramified field in a
canonical division-algebra representative.
-/

namespace Submission.CField.LClass

noncomputable section

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne
open BGroups CProduca LBrauer
open scoped NormedField Valued

attribute [local instance] NormedField.toValued

private abbrev relInteger (F : Type) [Field F] [ValuativeRel F] :=
  Valuation.integer (ValuativeRel.valuation F)

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance galoisNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance galoisNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

local instance galoisFinrankNeZero :
    NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩

set_option maxHeartbeats 8000000 in
-- Constructing the canonical relative Brauer class requires a large
-- cohomology-instance search and normalization calculation.
set_option synthInstance.maxHeartbeats 500000 in
/-- For a finite Galois extension of nonarchimedean local fields, the
canonical class whose denominator is the extension degree is split by the
extension.  All topology and valuation data on the abstract field `L` are
the canonical spectral ones. -/
theorem brauer_relative_galois :
    canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L := by
  let n := Module.finrank K L
  have hnPos : 0 < n := Module.finrank_pos
  letI : NeZero n := ⟨hnPos.ne'⟩
  by_cases hnOne : n = 1
  · have hclass : canonicalBrauerClass K n = 1 :=
      orderOf_eq_one_iff.mp <| by
        rw [order_brauer_class K n, hnOne]
    change canonicalBrauerClass K n ∈ relativeBrauerGroup K L
    rw [hclass]
    exact (relativeBrauerGroup K L).one_mem
  have hn : 1 < n :=
    (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨hnPos.ne', hnOne⟩
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    ValuativeRel.ofValuation (NormedField.valuation (K := L))
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra K L
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valued.integer L
  letI : IsDiscreteValuationRing A := by
    exact discrete_valuation_ring K
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation L)) :=
      discrete_valuation_ring L
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm L)
  letI : HenselianLocalRing A := integer_henselian_ring K
  letI : HenselianLocalRing B := valued_henselian_ring L
  letI : Algebra B L := B.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers
      (ValuativeRel.valuation K)).isFractionRing
  letI : IsFractionRing B L :=
    (Valuation.integer.integers
      (NormedField.valuation (K := L))).isFractionRing
  letI : Algebra A B := valuativeSpectralAlgebra K L
  letI : IsScalarTower A B L :=
    valuativeSpectralTower K L
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A L :=
    spectral_integer_valuative K L
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  letI : Module.Finite A B := IsIntegralClosure.finite A K L B
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  letI : Finite (ResidueField A) := local_field_residue K
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  letI : Finite (ResidueField B) := by
    letI : Finite (ResidueField
        (Valuation.integer (ValuativeRel.valuation L))) :=
      local_field_residue L
    exact Finite.of_equiv
      (ResidueField (Valuation.integer (ValuativeRel.valuation L)))
      (ResidueField.mapEquiv (valuativeIntegerNorm L)).toEquiv
  letI : Fintype (ResidueField B) := Fintype.ofFinite _
  letI : Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
    infer_instance
  let U := maximalUnramifiedSubalgebra A B
  let F := fractionFieldSubalgebra A B K L U
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : Algebra.FormallyUnramified A U :=
    maximal_subalgebra_formally A B
  letI : IsLocalRing U := maximal_subalgebra_ring A B
  letI : IsDiscreteValuationRing U :=
    subalgebra_discrete_valuation A B
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A U)
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : IsAdicComplete (maximalIdeal A) A :=
    integer_adic_complete K
  letI : HenselianLocalRing U :=
    LBrauer.henselian_formally_unramified A U
  let algUF : Algebra U F :=
    fractionIntermediateSubalgebra A B K L U
  letI : SMul U F := algUF.toSMul
  letI : Algebra U F := algUF
  letI : IsFractionRing U F :=
    fraction_intermediate_subalgebra A B K L U
  letI : IsScalarTower A U F := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro a
    apply F.val.injective
    change algebraMap A L a = algebraMap B L (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B L a
  letI : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    rfl
  letI : Module.Finite K F := by
    apply Module.Finite.of_isLocalization A U (nonZeroDivisors A)
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : Module.IsTorsionFree U B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  letI : Module.Finite U B :=
    Module.Finite.of_restrictScalars_finite A U B
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.of_finite U B
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  let algUL : Algebra U L :=
    ((algebraMap B L).comp (algebraMap U B)).toAlgebra
  letI : SMul U L := algUL.toSMul
  letI : Algebra U L := algUL
  letI : IsScalarTower U B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U F L := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    rfl
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap B L (algebraMap U B (algebraMap A U a)) =
      algebraMap K L (algebraMap A K a)
    calc
      _ = algebraMap B L (algebraMap A B a) := by
        rw [IsScalarTower.algebraMap_apply A U B]
      _ = algebraMap A L a :=
        (IsScalarTower.algebraMap_apply A B L a).symm
      _ = algebraMap K L (algebraMap A K a) :=
        IsScalarTower.algebraMap_apply A K L a
  let towerUBL : IsScalarTower U B L := inferInstance
  let towerUFL : IsScalarTower U F L := by infer_instance
  have htotalU : TotallyRamified U B (maximalIdeal U) :=
    subalgebra_totally_ramified A B F L
      (hUBL := towerUBL) (hUKUL := towerUFL)
  let f := Module.finrank K F
  let m := Module.finrank F L
  have hfPos : 0 < f := Module.finrank_pos
  have hmPos : 0 < m := Module.finrank_pos
  letI : NeZero f := ⟨hfPos.ne'⟩
  letI : NeZero m := ⟨hmPos.ne'⟩
  have hnprod : n = f * m := by
    exact (Module.finrank_mul_finrank K F L).symm
  have hfdvd : f ∣ n := by
    rw [hnprod]
    exact dvd_mul_right f m
  obtain ⟨eFC⟩ :=
    alg_level_model
      K U F f (by rfl)
  let C := canonicalUnramifiedLevel K f
  have hCdegree : Module.finrank K C = f :=
    unramified_level_finrank K f
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  letI : NontriviallyNormedField C :=
    FLExt.nontriviallyNormedField K C
  letI : NormedAlgebra K C := spectralNorm.normedAlgebra K C
  letI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel C :=
    ValuativeRel.ofValuation (NormedField.valuation (K := C))
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  letI : IsNonarchimedeanLocalField C :=
    FLExt.nonarchimedeanLocalField K C
  let algUC : Algebra U C :=
    (eFC.toRingHom.comp (algebraMap U F)).toAlgebra
  letI : SMul U C := algUC.toSMul
  letI : Algebra U C := algUC
  let eUFC : F ≃ₐ[U] C := { eFC with commutes' := fun _ => rfl }
  letI : IsFractionRing U C :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors U) eUFC
  letI : IsScalarTower A U C := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro a
    change algebraMap K C (algebraMap A K a) =
      eFC (algebraMap U F (algebraMap A U a))
    calc
      _ = eFC (algebraMap K F (algebraMap A K a)) :=
        (eFC.commutes (algebraMap A K a)).symm
      _ = eFC (algebraMap A F a) := by
        rw [IsScalarTower.algebraMap_apply A K F]
      _ = eFC (algebraMap U F (algebraMap A U a)) := by
        rw [IsScalarTower.algebraMap_apply A U F]
  let algCL : Algebra C L :=
    ((algebraMap F L).comp eFC.symm.toRingHom).toAlgebra
  letI : SMul C L := algCL.toSMul
  letI : Algebra C L := algCL
  letI : IsScalarTower K C L := IsScalarTower.of_algebraMap_eq' <| by
    ext k
    change algebraMap K L k = algebraMap F L (eFC.symm (algebraMap K C k))
    rw [eFC.symm.commutes]
    rfl
  letI : Module.Finite C L :=
    Module.Finite.of_restrictScalars_finite K C L
  letI : IsGalois C L := IsGalois.tower_top_of_isGalois K C L
  letI : NormedAlgebra C L := spectralNorm.normedAlgebra' K C L
  letI : (NormedField.valuation (K := C)).HasExtension
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra C L
  letI : IsScalarTower U C L := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    change algebraMap B L (algebraMap U B u) =
      algebraMap F L (eFC.symm (eFC (algebraMap U F u)))
    rw [eFC.symm_apply_apply]
    exact IsScalarTower.algebraMap_apply U F L u
  let OC := Valued.integer C
  letI : IsDiscreteValuationRing OC := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation C)) :=
      discrete_valuation_ring C
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm C)
  letI : Algebra OC B := inferInstance
  letI : Module.Finite OC B := valued_integer_module C L
  letI : Module.IsTorsionFree OC B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective OC B)
  letI : IsScalarTower OC B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower OC C L := IsScalarTower.of_algebraMap_eq' rfl
  let A0 := Valued.integer K
  let eA : A ≃+* A0 := valuativeIntegerNorm K
  letI : Algebra A0 A := eA.symm.toRingHom.toAlgebra
  letI : Algebra A0 U :=
    ((algebraMap A U).comp eA.symm.toRingHom).toAlgebra
  letI : IsScalarTower A0 A U := IsScalarTower.of_algebraMap_eq' rfl
  let eA0A : A0 ≃ₐ[A0] A :=
    AlgEquiv.ofRingEquiv (f := eA.symm) (fun _ => rfl)
  letI : Module.Finite A0 A :=
    Module.Finite.equiv eA0A.toLinearEquiv
  letI : Module.Finite A0 U := Module.Finite.trans A U
  letI : Algebra.IsIntegral A0 U := Algebra.IsIntegral.of_finite A0 U
  letI : IsScalarTower A0 U C := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro a
    calc
      algebraMap A0 C a = algebraMap A C (eA.symm a) := by
        apply Subtype.ext
        rfl
      _ = algebraMap U C (algebraMap A U (eA.symm a)) :=
        IsScalarTower.algebraMap_apply A U C (eA.symm a)
      _ = algebraMap U C (algebraMap A0 U a) := by rfl
  have hcompat : (algebraMap OC B).comp
        (dvrValuedInteger K U C).toRingHom =
      algebraMap U B := by
    apply RingHom.ext
    intro u
    apply Subtype.ext
    change algebraMap C L
        ((dvrValuedInteger K U C u : OC) : C) =
      algebraMap B L (algebraMap U B u)
    rw [coe_dvr_valued K U C]
    calc
      algebraMap C L (algebraMap U C u) = algebraMap U L u :=
        (IsScalarTower.algebraMap_apply U C L u).symm
      _ = algebraMap B L (algebraMap U B u) :=
        IsScalarTower.algebraMap_apply U B L u
  have htotalCL : TotallyRamified OC B (maximalIdeal OC) :=
    totally_valued_model K U C L
      hcompat htotalU
  let eC : relInteger C ≃+* OC := valuativeIntegerNorm C
  let eL : relInteger L ≃+* B := valuativeIntegerNorm L
  let algVV : Algebra (relInteger C) (relInteger L) :=
    (eL.symm.toRingHom.comp
      ((algebraMap OC B).comp eC.toRingHom)).toAlgebra
  letI : SMul (relInteger C) (relInteger L) := algVV.toSMul
  letI : Algebra (relInteger C) (relInteger L) := algVV
  letI : Module.Finite (relInteger C) (relInteger L) :=
    Module.Finite.of_equiv_equiv eC.symm eL.symm (by
      apply RingHom.ext
      intro x
      apply eL.injective
      rfl)
  letI : Algebra.IsIntegral (relInteger C) (relInteger L) :=
    Algebra.IsIntegral.of_finite (relInteger C) (relInteger L)
  letI : FaithfulSMul (relInteger C) (relInteger L) :=
    (faithfulSMul_iff_algebraMap_injective
      (relInteger C) (relInteger L)).mpr <| by
      intro x y hxy
      apply eC.injective
      apply FaithfulSMul.algebraMap_injective OC B
      have h := congrArg eL hxy
      exact h
  letI : IsLocalHom
      (algebraMap (relInteger C) (relInteger L)) :=
    Algebra.IsIntegral.isLocalHom (relInteger C) (relInteger L)
  letI : Module.IsTorsionFree (relInteger C) (relInteger L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (relInteger C) (relInteger L))
  letI : IsScalarTower (relInteger C) (relInteger L) L :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      rfl
  letI : IsScalarTower (relInteger C) C L :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      rfl
  let eUC : U ≃+* relInteger C :=
    (dvrValuedInteger K U C).trans eC.symm
  have heUC (u : U) :
      eL (algebraMap (relInteger C) (relInteger L) (eUC u)) =
        algebraMap U B u := by
    change algebraMap OC B (dvrValuedInteger K U C u) =
      algebraMap U B u
    exact DFunLike.congr_fun hcompat u
  have hresU : Function.Surjective
      (algebraMap (ResidueField U) (ResidueField B)) :=
    maximal_subalgebra_surjective A B
  have hresVal : Function.Surjective
      (algebraMap (ResidueField (relInteger C))
        (ResidueField (relInteger L))) := by
    apply residue_surjective_ring
      (relInteger C) (relInteger L) U B eUC.symm eL
    · apply RingHom.ext
      intro x
      have h := (heUC (eUC.symm x)).symm
      rw [eUC.apply_symm_apply] at h
      exact h
    · exact hresU
  have htotalVal : TotallyRamified (relInteger C) (relInteger L)
      (maximalIdeal (relInteger C)) :=
    totally_ramified_surjective
      (relInteger C) (relInteger L) C L hresVal
  have hCLdegree : Module.finrank C L = m := by
    apply Nat.eq_of_mul_eq_mul_left hfPos
    calc
      f * Module.finrank C L = Module.finrank K L := by
        rw [← hCdegree]
        exact Module.finrank_mul_finrank K C L
      _ = f * m := by rw [← hnprod]
  obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hclass, hDdim⟩ :=
    division_brauer_class K n
  letI : DivisionRing D := hDdiv
  letI : Algebra K D := hDalg
  letI : Algebra.IsCentral K D := hDcentral
  letI : Module.Finite K D := hDfinite
  obtain ⟨j, _hj, ⟨eD⟩⟩ :=
    alg_carry_algebra K D <| by
      rw [hDdim]
      simpa using hn
  have hCn : C ≤ canonicalUnramifiedLevel K n :=
    unramified_level K hfPos hnPos hfdvd
  have hsqrtD : Nat.sqrt (Module.finrank K D) = n := by
    rw [hDdim]
    simp
  letI : NeZero (Nat.sqrt (Module.finrank K D)) :=
    ⟨by rw [hsqrtD]; exact hnPos.ne'⟩
  have hCnD : C ≤ canonicalUnramifiedLevel K
      (Nat.sqrt (Module.finrank K D)) := by
    simpa only [hsqrtD] using hCn
  let iCn : C →ₐ[K] canonicalUnramifiedLevel K
      (Nat.sqrt (Module.finrank K D)) :=
    IntermediateField.inclusion hCnD
  let iCarry : canonicalUnramifiedLevel K
      (Nat.sqrt (Module.finrank K D)) →ₐ[K]
      UnramifiedCarryAlgebra K
        (Nat.sqrt (Module.finrank K D)) j :=
    CProduc.fieldEmbedding K
      (canonicalUnramifiedLevel K (Nat.sqrt (Module.finrank K D)))
      ((canonicalCarryCocycle K
        (Nat.sqrt (Module.finrank K D))) ^ j)
  let iCD : C →ₐ[K] D :=
    eD.symm.toAlgHom.comp (iCarry.comp iCn)
  have hDfm : Module.finrank K D = (f * m) ^ 2 := by
    rw [hDdim, ← hnprod]
  obtain ⟨iLD⟩ :=
    totally_ramified_centralizer
      K C L D f m hCdegree hDfm hCLdegree iCD htotalVal
  change canonicalBrauerClass K n ∈ relativeBrauerGroup K L
  exact (brauer_nonempty_alg
    K L n D hclass hDdim rfl).2 ⟨iLD⟩

end

end Submission.CField.LClass
