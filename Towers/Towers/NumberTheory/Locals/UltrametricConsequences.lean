import Towers.NumberTheory.Locals.EquivalentAbsoluteValues
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Elementary consequences of the ultrametric inequality

This file formalizes Milne 7.9--7.11.
-/

namespace Towers.NumberTheory.Milne

section

variable {K : Type*} [Field K]

/-- Milne 7.9: if two summands have different absolute values, the absolute
value of their sum is the larger one. -/
theorem nonarchimedean_max_ne (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {x y : K} (hxy : v x ≠ v y) :
    v (x + y) = max (v x) (v y) :=
  IsNonarchimedean.add_eq_max_of_ne hv hxy

/-- Milne 7.10: if `x` is closer to `b` than to `a`, then its distance from
`a` equals the distance between `a` and `b`. -/
theorem nonarchimedean_distance (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {a b x : K}
    (h : v (x - b) < v (x - a)) :
    v (a - x) = v (a - b) := by
  have h' : v (x - b) < v (a - x) := by
    calc
      v (x - b) < v (x - a) := h
      _ = v (a - x) := by
        rw [show x - a = -(a - x) by ring, v.map_neg]
  calc
    v (a - x) = v ((a - x) + (x - b)) :=
      (IsNonarchimedean.add_eq_left_of_lt hv h').symm
    _ = v (a - b) := by ring_nf

/-- Milne 7.11: in a vanishing finite sum, a nonzero summand of maximal
absolute value cannot be the unique summand with that value. -/
theorem second_maximal_summand
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {ι : Type*} {s : Finset ι} {a : ι → K} {k : ι}
    (hk : k ∈ s) (hk0 : a k ≠ 0)
    (hmax : ∀ j ∈ s, v (a j) ≤ v (a k))
    (hsum : ∑ j ∈ s, a j = 0) :
    ∃ j ∈ s, j ≠ k ∧ v (a j) = v (a k) := by
  classical
  by_contra h
  push Not at h
  have hstrict : ∀ j ∈ s, j ≠ k → v (a j) < v (a k) := by
    intro j hj hjk
    exact lt_of_le_of_ne (hmax j hj) (h j hj hjk)
  have heq := IsNonarchimedean.apply_sum_eq_of_lt hv hk hstrict
  rw [hsum, v.map_zero] at heq
  exact (v.pos hk0).ne' heq.symm

end

end Towers.NumberTheory.Milne
