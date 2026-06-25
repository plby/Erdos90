import Submission.ClassField.LocalClass.CanonicalUnramifiedEquiv
import Submission.ClassField.LocalClass.IntegralModelTotal
import Submission.ClassField.LocalClass.ValuativeIntegerTransport
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure
import Submission.ClassField.LocalBrauer.InvariantTotallyRamified
import Submission.ClassField.LocalBrauer.InvariantBaseUnramified

/-!
# Local invariant base change for finite Galois extensions

The maximal unramified integral model is transported to the canonical
unramified field of the same degree.  The remaining extension is totally
ramified, so the unramified and totally ramified base-change theorems compose.
-/

namespace Submission.CField.LClass

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne
open LBrauer
open scoped NormedField Valued

attribute [local instance] NormedField.toValued

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance scratchNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance scratchNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

section ExistingLocalStructure

variable [Field L] [Algebra K L] [Module.Finite K L]
  [Algebra.IsSeparable K L]

set_option maxHeartbeats 10000000 in
-- Decomposing the abstract extension through its maximal unramified integral
-- model requires a large tower of spectral local-field instances.
set_option synthInstance.maxHeartbeats 500000 in
include K L in
/-- Formula (29) for a finite separable extension, using its canonical
spectral nonarchimedean local-field structure. -/
theorem change_separable_normed :
    SpectralChangeFormula K L := by
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
  change BCForm K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra K L
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valuation.integer (NormedField.valuation (K := L))
  letI : IsDiscreteValuationRing A := by
    change IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation K))
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
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
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
  letI : Finite (ResidueField B) := by
    letI : Finite (ResidueField
        (Valuation.integer (ValuativeRel.valuation L))) :=
      local_field_residue L
    exact Finite.of_equiv
      (ResidueField (Valuation.integer (ValuativeRel.valuation L)))
      (ResidueField.mapEquiv (valuativeIntegerNorm L)).toEquiv
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
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
  let algUL : Algebra U L :=
    ((algebraMap B L).comp (algebraMap U B)).toAlgebra
  letI : SMul U L := algUL.toSMul
  letI : Algebra U L := algUL
  letI : IsScalarTower U B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U F L := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    rfl
  letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    exact IsScalarTower.algebraMap_apply A B L a
  have towerUBL : IsScalarTower U B L := by infer_instance
  have towerUFL : IsScalarTower U F L := by infer_instance
  have hdecomp : TotallyRamified U B (maximalIdeal U) :=
    subalgebra_totally_ramified A B F L
      (hUBL := towerUBL) (hUKUL := towerUFL)
  let f := Module.finrank K F
  have hfPos : 0 < f := Module.finrank_pos
  letI : NeZero f := ⟨hfPos.ne'⟩
  obtain ⟨eFC⟩ :=
    alg_level_model
      K U F f (by rfl)
  let C := canonicalUnramifiedLevel K f
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
      algebraMap K C (algebraMap A K a) =
          eFC (algebraMap K F (algebraMap A K a)) :=
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
  letI : Algebra.IsSeparable C L :=
    Algebra.isSeparable_tower_top_of_isSeparable K C L
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
  letI : IsScalarTower A0 A C := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    rfl
  letI : IsScalarTower A0 U C := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    have h : algebraMap A0 C a =
        algebraMap U C (algebraMap A0 U a) := by
      calc
        algebraMap A0 C a = algebraMap A C (algebraMap A0 A a) :=
          IsScalarTower.algebraMap_apply A0 A C a
        _ = algebraMap U C (algebraMap A U (algebraMap A0 A a)) :=
          IsScalarTower.algebraMap_apply A U C _
        _ = algebraMap U C (algebraMap A0 U a) := by
          rw [IsScalarTower.algebraMap_apply A0 A U]
    exact congrArg (fun x : C => (x : AlgebraicClosure K)) h
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
    exact (IsScalarTower.algebraMap_apply U C L u).symm.trans
      (IsScalarTower.algebraMap_apply U B L u)
  have hresU : Function.Surjective
      (algebraMap (ResidueField U) (ResidueField B)) :=
    maximal_subalgebra_surjective A B
  have hKC : BCForm K C :=
    change_formula_level K f
  have hCL : BCForm C L :=
    change_formula_surjective C L U
      (dvrValuedInteger K U C) hcompat hresU
  exact BCForm.trans K C L hKC hCL

end ExistingLocalStructure

/-- Formula (29) in the Galois form used by the transported local Artin map. -/
theorem change_normed_algebra
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    SpectralChangeFormula K L :=
  change_separable_normed K L

/-- Formula (29) for a finite Galois extension with its canonical spectral
local-field structure installed internally. -/
theorem change_formula_galois
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    SpectralChangeFormula K L :=
  change_normed_algebra K L

variable [Field L] [Algebra K L] [Module.Finite K L]
  [Algebra.IsSeparable K L]

set_option maxHeartbeats 10000000 in
-- Installing the canonical spectral topology and replaying the integral-model
-- decomposition requires a large elaboration budget.
set_option synthInstance.maxHeartbeats 500000 in
include K L in
/-- Formula (29) for every finite separable extension, with the canonical
spectral local-field structure installed on the abstract extension. -/
theorem change_formula_separable :
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
    BCForm K L := by
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
  exact change_separable_normed K L

/-- The spectral packaging of local-invariant base change for finite
separable extensions. -/
theorem spectral_change_separable :
    SpectralChangeFormula K L :=
  change_formula_separable K L

end

end Submission.CField.LClass
