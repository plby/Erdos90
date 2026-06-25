import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Milne, Algebraic Number Theory, the topology defined by an absolute value

This records the two elementary topological observations immediately before
Proposition 7.8: the induced distance is `|x - y|`, and the powers of `x`
converge to zero exactly when `|x| < 1`.
-/

namespace Submission.NumberTheory.Milne

open Filter Topology

variable {K : Type*} [Field K]

/-- The metric on the copy of `K` carrying the topology defined by `v` has
distance `v (x - y)`. -/
theorem with_dist_eq (v : AbsoluteValue K ℝ) (x y : K) :
    dist (WithAbs.toAbs v x) (WithAbs.toAbs v y) = v (x - y) := by
  rw [dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.ofAbs_toAbs]

/-- For the topology defined by an absolute value, `x ^ n` tends to zero if
and only if `v x < 1`.  This is the observation used in Milne's proof of
Proposition 7.8(a) implies (b). -/
theorem tendsto_absolute_value
    (v : AbsoluteValue K ℝ) (x : K) :
    Tendsto (fun n : ℕ ↦ WithAbs.toAbs v (x ^ n)) atTop (𝓝 0) ↔ v x < 1 := by
  rw [show (fun n : ℕ ↦ WithAbs.toAbs v (x ^ n)) =
      fun n : ℕ ↦ (WithAbs.toAbs v x) ^ n by
        funext n
        exact WithAbs.toAbs_pow v x n]
  simpa only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs] using
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
      (x := WithAbs.toAbs v x))

end Submission.NumberTheory.Milne
