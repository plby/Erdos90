import Towers.ClassField.LocalBrauer.FrobeniusPowerResidue
import Towers.ClassField.LocalBrauer.RelativeTransportIdentity

/-!
# Source estimate for transported relative arithmetic Frobenius

This file isolates the spectral-norm comparison and the source-field residue
estimate.  Keeping these declarations in their own module gives Lean a cache
boundary before the target-field comparison.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Towers.CField.LFTheory

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev F (n : ℕ) := canonicalRelativeLevel K n
private abbrev E (m n : ℕ) := canonicalUpperLevel K m n
private abbrev C (m n : ℕ) [NeZero m] [NeZero n] :=
  relativeTargetLevel K m n

set_option maxHeartbeats 1000000 in
-- Transport the source Frobenius-power estimate across the algebra equivalence.
set_option synthInstance.maxHeartbeats 500000 in
theorem transported_arithmetic_frobenius
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : E K m n ≃ₐ[F K n] C K m n)
    (y : C K m n) (hy : ‖y‖ ≤ 1) :
    ‖transportedArithmeticFrobenius (K := K) m n e y -
        y ^ (localResidueCardinality K ^ n)‖ < 1 := by
  have hx : ‖e.symm y‖ ≤ 1 := by
    rw [← canonical_relative_alg K m n e]
    simp only [AlgEquiv.apply_symm_apply,
      FLExt.norm_eq_spectral]
    exact hy
  have hsrc := arithmetic_frobenius_residue K m n
    (e.symm y) hx
  rw [transported_arithmetic_pow K m n e y,
    canonical_relative_alg K m n e]
  exact hsrc

end

end Towers.CField.LBrauer
