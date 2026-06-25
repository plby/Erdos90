import Submission.ClassField.LocalClass.Inflation
import Submission.ClassField.LocalClass.ScratchTransportSetup
import Submission.ClassField.CrossedProducts.BrauerRestriction
import Submission.ClassField.LocalBrauer.InvariantBaseChange

/-!
# Restriction of the finite local fundamental class

This file isolates formula (31), the arithmetic normalization input in
Lemma III.3.2.  The proof only needs the local-invariant base-change formula
for the intermediate extension; all cohomological transport is unconditional.
-/

namespace Submission.CField.LRecip

open Submission.CField.LClass
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K F L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance fundamentalValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance fundamentalValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional K F] [FiniteDimensional F L] [FiniteDimensional K L]
  [IsGalois K L] [IsGalois F L]

attribute [local instance] Units.mulDistribMulActionRight

local instance fundamentalDegreeKNeZero :
    NeZero (Module.finrank K F) :=
  ⟨Module.finrank_pos.ne'⟩

local instance fundamentalDegreeFNeZero :
    NeZero (Module.finrank F L) :=
  ⟨Module.finrank_pos.ne'⟩

set_option maxHeartbeats 2000000 in
-- Transporting the fundamental cocycle through the intermediate-field tower is normalization-heavy.
set_option synthInstance.maxHeartbeats 500000 in
/-- Formula (31) in multiplicative Galois `H²`: restriction of the local
fundamental class for `L/K` is the local fundamental class for `L/F`. -/
theorem multiplicative_fundamental_change
    (hbase : SpectralChangeFormula K F) :
    galoisHRestriction K F L
        (multiplicativeFundamentalClass K L) =
      letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
      letI : NontriviallyNormedField F :=
        FLExt.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := FLExt.valuativeRel K F
      letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
        Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
      letI : IsNonarchimedeanLocalField F :=
        FLExt.nonarchimedeanLocalField K F
      multiplicativeFundamentalClass F L := by
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  change BCForm K F at hbase
  apply (CProduc.hRelativeBrauer F L).injective
  rw [GaloisRestrictionCompatibility,
    h_brauer_restriction,
    h_brauer_fundamental,
    h_brauer_fundamental]
  apply Subtype.ext
  apply (carryBrauerInvariant F).injective
  change carryBrauerInvariant F
      (brauerBaseChange K F
        (canonicalBrauerClass K (Module.finrank K L))) =
    carryBrauerInvariant F
      (canonicalBrauerClass F (Module.finrank F L))
  rw [hbase,
    canonical_carry_brauer,
    canonical_carry_brauer]
  apply Multiplicative.ext
  change Module.finrank K F •
      ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) =
    ((1 : ℚ) / (Module.finrank F L : ℚ) : LocalInvariant)
  rw [← Module.finrank_mul_finrank K F L]
  exact invariant_nsmul_div
    (Module.finrank K F) (Module.finrank F L)

set_option maxHeartbeats 3000000 in
-- Identifying the restricted class with the intrinsic fixed-field class needs extended normalization.
set_option synthInstance.maxHeartbeats 500000 in
/-- Formula (31): restriction of the finite local fundamental class through
any intermediate field is the intrinsic fundamental class over that field. -/
theorem h_fundamental_restriction :
    galoisHRestriction K F L
        (multiplicativeFundamentalClass K L) =
      letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
      letI : NontriviallyNormedField F :=
        FLExt.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := FLExt.valuativeRel K F
      letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
        Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
      letI : IsNonarchimedeanLocalField F :=
        FLExt.nonarchimedeanLocalField K F
      multiplicativeFundamentalClass F L := by
  letI : Algebra.IsSeparable K F :=
    Algebra.isSeparable_tower_bot_of_isSeparable K F L
  exact multiplicative_fundamental_change
    K F L (spectral_change_separable K F)

end

end Submission.CField.LRecip
