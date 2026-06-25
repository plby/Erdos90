import Submission.ClassField.LocalClass.ResidueSurjectivityTransport
import Submission.ClassField.LocalBrauer.InvariantTotallyRamified
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Transporting a totally ramified local-invariant formula to valuative integers

The integral decomposition of a finite local extension is most naturally
expressed using the norm-defined integer rings.  The local invariant theorem
uses the valuation-relation integer rings.  This file contains the complete
transport between those presentations, so callers do not retain its large
temporary instance context.
-/

namespace Submission.CField.LClass

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer
open scoped NormedField Valued

attribute [local instance] NormedField.toValued

private abbrev relInteger (F : Type u) [Field F] [ValuativeRel F] :=
  Valuation.integer (ValuativeRel.valuation F)

set_option maxHeartbeats 3000000 in
-- The proof installs both integer-ring presentations and their residue fields.
set_option synthInstance.maxHeartbeats 500000 in
/-- A residue-degree-one integral model gives the totally ramified local
invariant formula after transport to valuation-relation integers. -/
theorem change_formula_surjective
    (C L U : Type u)
    [NontriviallyNormedField C] [IsUltrametricDist C] [ValuativeRel C]
    [IsNonarchimedeanLocalField C]
    [Valuation.Compatible (NormedField.valuation (K := C))]
    [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
    [IsNonarchimedeanLocalField L]
    [Valuation.Compatible (NormedField.valuation (K := L))]
    [NormedAlgebra C L] [FiniteDimensional C L]
    [CommRing U] [IsLocalRing U]
    [Algebra U (Valued.integer L)]
    [IsLocalHom (algebraMap U (Valued.integer L))]
    [Algebra (Valued.integer C) (Valued.integer L)]
    [Module.Finite (Valued.integer C) (Valued.integer L)]
    [FaithfulSMul (Valued.integer C) (Valued.integer L)]
    [IsScalarTower (Valued.integer C) (Valued.integer L) L]
    [IsScalarTower (Valued.integer C) C L]
    (eU : U ≃+* Valued.integer C)
    (hcompat : (algebraMap (Valued.integer C) (Valued.integer L)).comp
        eU.toRingHom = algebraMap U (Valued.integer L))
    (hresU : Function.Surjective
      (algebraMap (ResidueField U)
        (ResidueField (Valued.integer L)))) :
    BCForm C L := by
  let OC := Valued.integer C
  let B := Valued.integer L
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
      exact congrArg eL hxy
  letI : IsLocalHom (algebraMap (relInteger C) (relInteger L)) :=
    Algebra.IsIntegral.isLocalHom (relInteger C) (relInteger L)
  letI : Module.IsTorsionFree (relInteger C) (relInteger L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (relInteger C) (relInteger L))
  letI : IsScalarTower (relInteger C) (relInteger L) L :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      change algebraMap C L ((eC x : OC) : C) =
        algebraMap B L (algebraMap OC B (eC x))
      exact (IsScalarTower.algebraMap_apply OC C L (eC x)).symm.trans
        (IsScalarTower.algebraMap_apply OC B L (eC x))
  letI : IsScalarTower (relInteger C) C L :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      rfl
  let eUC : U ≃+* relInteger C := eU.trans eC.symm
  have heUC (u : U) :
      eL (algebraMap (relInteger C) (relInteger L) (eUC u)) =
        algebraMap U B u := by
    change algebraMap OC B (eU u) = algebraMap U B u
    exact DFunLike.congr_fun hcompat u
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
  have htotal : TotallyRamified (relInteger C) (relInteger L)
      (maximalIdeal (relInteger C)) :=
    totally_ramified_surjective
      (relInteger C) (relInteger L) C L hresVal
  exact formula_totally_ramified C L htotal

end

end Submission.CField.LClass
