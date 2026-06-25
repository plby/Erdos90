import Submission.ClassField.LocalBrauer.CanonicalAutomorphismExt
import Submission.ClassField.LocalBrauer.RelativeTransportEstimate

/-!
# Transport of relative arithmetic Frobenius
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

set_option maxHeartbeats 2000000 in
-- The proof compares residue actions through two spectral norm models.
set_option synthInstance.maxHeartbeats 500000 in
/-- Every equivalence from `U_{m*n}/U_n` to the canonical degree-`m`
unramified extension over `U_n` carries relative arithmetic Frobenius to
arithmetic Frobenius. -/
theorem arithmetic_aut_congr
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : canonicalUpperLevel K m n ≃ₐ[F K n] C K m n) :
    e.autCongr (relativeArithmeticFrobenius K m n) =
      canonicalArithmeticFrobenius (F K n) m := by
  change transportedArithmeticFrobenius (K := K) m n e = _
  apply canonical_unramified_ext (F K n) m
  intro y hy
  exact transported_relative_arithmetic K m n e y hy

end

end Submission.CField.LBrauer
