import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Milne, Chapter 7, Exercise 7-2

Open balls in an ultrametric space have every one of their points as a
centre.  Consequently, two intersecting balls are nested.  In a complete
nonarchimedean additive group, a series converges exactly when its terms tend
to zero.
-/

namespace Towers.NumberTheory.Milne

open Filter Metric Topology

section Balls

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- Milne, Exercise 7-2(a): every point of an open ultrametric ball is a
centre of the same ball. -/
theorem ultrametric_ball {a b : X} {r : ℝ}
    (hb : b ∈ ball a r) :
    ball a r = ball b r :=
  IsUltrametricDist.ball_eq_of_mem hb

/-- Milne, Exercise 7-2(a): when two open balls meet, the ball with the
smaller radius is contained in the one with the larger radius. -/
theorem ultrametric_ball_both
    {a b x : X} {r s : ℝ}
    (hxa : x ∈ ball a r) (hxb : x ∈ ball b s) (hrs : r ≤ s) :
    ball a r ⊆ ball b s := by
  rw [IsUltrametricDist.ball_eq_of_mem hxa,
    IsUltrametricDist.ball_eq_of_mem hxb]
  exact ball_subset_ball hrs

end Balls

section Series

variable {G : Type*} [NormedAddCommGroup G] [IsUltrametricDist G]
  [CompleteSpace G]

/-- Milne, Exercise 7-2(b): over a complete nonarchimedean additive group, a
series converges if and only if its terms tend to zero. -/
theorem ultrametric_summable_tendsto (a : ℕ → G) :
    Summable a ↔ Tendsto a atTop (𝓝 0) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    Nat.cofinite_eq_atTop]

end Series

end Towers.NumberTheory.Milne
