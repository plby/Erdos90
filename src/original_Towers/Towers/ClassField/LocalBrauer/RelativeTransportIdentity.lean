import Towers.ClassField.NormCorrespondence.CanonicalNormalization
import Towers.ClassField.NormCorrespondence.LocalStatement
import Towers.ClassField.LocalBrauer.RelativeTransportNorm

/-!
# Difference identity for transported relative arithmetic Frobenius

The transported difference is the image of the corresponding Frobenius-power
difference on the source canonical level.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open Towers.CField.LFTheory

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev F (n : ℕ) := canonicalRelativeLevel K n
private abbrev E (m n : ℕ) := canonicalUpperLevel K m n
private abbrev C (m n : ℕ) [NeZero m] [NeZero n] :=
  relativeTargetLevel K m n

set_option maxHeartbeats 4000000 in
-- Unfolding the conjugated automorphism crosses both canonical tower levels.
set_option synthInstance.maxHeartbeats 500000 in
theorem transported_arithmetic_pow
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : E K m n ≃ₐ[F K n] C K m n) (y : C K m n) :
    transportedArithmeticFrobenius (K := K) m n e y -
        y ^ (localResidueCardinality K ^ n) =
      e (((canonicalArithmeticFrobenius K (m * n)) ^ n) (e.symm y) -
        (e.symm y) ^ (localResidueCardinality K ^ n)) := by
  rw [transported_relative_frobenius K m n e y,
    relative_arithmetic_frobenius K m n,
    map_sub, map_pow]
  simp

end

end Towers.CField.LBrauer
