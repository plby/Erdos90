import Submission.ClassField.LocalBrauer.RelativeFrobeniusEstimate

/-!
# Target comparison for transported relative arithmetic Frobenius

This file combines the cached source estimate with the defining target-field
estimate by the ultrametric triangle inequality.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Submission.CField.LFTheory

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev F (n : ℕ) := canonicalRelativeLevel K n
private abbrev C (m n : ℕ) [NeZero m] [NeZero n] :=
  relativeTargetLevel K m n

set_option maxHeartbeats 4000000 in
-- The source and target Frobenius estimates use different spectral norms.
set_option synthInstance.maxHeartbeats 500000 in
theorem transported_relative_arithmetic
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : canonicalUpperLevel K m n ≃ₐ[F K n] C K m n)
    (y : C K m n) (hy : ‖y‖ ≤ 1) :
    ‖transportedArithmeticFrobenius (K := K) m n e y -
        canonicalArithmeticFrobenius (F K n) m y‖ < 1 := by
  have hcardF : localResidueCardinality (F K n) =
      localResidueCardinality K ^ n :=
    residue_unramified_level K n
  have hsrc := transported_arithmetic_frobenius
    K m n e y hy
  have htgt := subextension_arithmetic_frobenius (F K n) m
    y hy
  rw [hcardF] at htgt
  have htgt' :
      ‖y ^ (localResidueCardinality K ^ n) -
        canonicalArithmeticFrobenius (F K n) m y‖ < 1 := by
    rw [norm_sub_rev, NormedAlgebra.norm_eq_spectralNorm (F K n)]
    change spectralNorm (F K n) (canonicalUnramifiedLevel (F K n) m)
      (canonicalArithmeticFrobenius (F K n) m y -
        y ^ (localResidueCardinality K ^ n)) < 1 at htgt
    exact htgt
  have htriangle := IsUltrametricDist.norm_add_le_max
    (transportedArithmeticFrobenius (K := K) m n e y -
      y ^ (localResidueCardinality K ^ n))
    (y ^ (localResidueCardinality K ^ n) -
      canonicalArithmeticFrobenius (F K n) m y)
  have hadd :
      (transportedArithmeticFrobenius (K := K) m n e y -
        y ^ (localResidueCardinality K ^ n)) +
          (y ^ (localResidueCardinality K ^ n) -
            canonicalArithmeticFrobenius (F K n) m y) =
        transportedArithmeticFrobenius (K := K) m n e y -
          canonicalArithmeticFrobenius (F K n) m y := by ring
  rw [hadd] at htriangle
  exact htriangle.trans_lt
    (max_lt hsrc htgt')

end

end Submission.CField.LBrauer
