import Submission.ClassField.LocalReciprocity.CupPairing
import Submission.ClassField.BrauerLocalization.Relative2Comparison

/-!
# Finite local invariant normalization for the resized Brauer comparison

This file records the normalization statement at the endpoint of the finite
place branch of Theorem VII.8.1.  The universe-resized categorical `H²`
comparison does not alter the canonical local invariant of the represented
multiplicative class.
-/

namespace Submission.CField.RExist

open Submission.CField.LClass
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.HNorm
open Submission.CField.BLoc

noncomputable section

universe u

/-- The inverse resized relative-Brauer comparison is the crossed-product
class represented by the original multiplicative `H²` class. -/
theorem resized_multiplicative_2
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : MHTwo Gal(L/K) Lˣ) :
    ((relativeBrauer2 K L).symm
        (multiplicativeLiftAdditive x)).toMul =
      CProduc.hRelativeBrauer K L x := by
  have hclass :
      (relativeBrauer2 K L).symm
          (multiplicativeLiftAdditive x) =
        Additive.ofMul (CProduc.hRelativeBrauer K L x) := by
    apply (relativeBrauer2 K L).injective
    rw [AddEquiv.apply_symm_apply]
    change multiplicativeLiftAdditive x =
      multiplicativeLiftAdditive
        ((CProduc.hRelativeBrauer K L).symm
          (CProduc.hRelativeBrauer K L x))
    rw [MulEquiv.symm_apply_apply]
  exact congrArg Additive.toMul hclass

variable (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteNormalizationValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteNormalizationValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The inverse resized relative-Brauer comparison represents exactly the
same multiplicative `H²` class for purposes of the canonical local invariant. -/
theorem carry_resized_symm
    (x : MHTwo Gal(L/K) Lˣ) :
    carryBrauerInvariant K
        (((relativeBrauer2 K L).symm
          (multiplicativeLiftAdditive x)).toMul : BrauerGroup K) =
      ((relativeHTorsion K L x :
          invariantPowTorsion (Module.finrank K L)) :
        Multiplicative LocalInvariant) := by
  rw [invariant_torsion_coe]
  rw [resized_multiplicative_2]

end

end Submission.CField.RExist
