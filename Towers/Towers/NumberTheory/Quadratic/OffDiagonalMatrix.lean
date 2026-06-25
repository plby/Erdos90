import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Milne, Algebraic Number Theory, Lemma 5.10

A real square matrix with negative off-diagonal entries and positive row sums is invertible.
-/

namespace Towers.NumberTheory.Milne

open scoped BigOperators

/-- **Milne, Lemma 5.10.** If every off-diagonal entry of a real square matrix is
negative and every row sum is positive, then the matrix is invertible. -/
theorem off_row_pos
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hoff : ∀ i j, i ≠ j → A i j < 0)
    (hrow : ∀ i, 0 < ∑ j, A i j) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  suffices x - y = 0 by
    exact sub_eq_zero.mp this
  let z := x - y
  have hz : A.mulVec z = 0 := by
    rw [show z = x - y by rfl, Matrix.mulVec_sub, hxy, sub_self]
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.elim _ _
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j ↦ |z j|)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)))
  by_cases hzi : z i = 0
  · funext j
    have hj := hi j (Finset.mem_univ j)
    rw [hzi, abs_zero] at hj
    exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
  exfalso
  have hnormalized : (∑ j, A i j * (z j / z i)) = 0 := by
    calc
      (∑ j, A i j * (z j / z i)) = (∑ j, A i j * z j) / z i := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [show (∑ j, A i j * z j) = 0 by exact congrFun hz i, zero_div]
  have hterm (j : Fin n) : A i j ≤ A i j * (z j / z i) := by
    by_cases hji : j = i
    · subst j
      simp [hzi]
    · have habs : |z j| ≤ |z i| := hi j (Finset.mem_univ j)
      have habsdiv : |z j / z i| ≤ 1 := by
        rw [abs_div, div_le_one (abs_pos.mpr hzi)]
        exact habs
      have hquot : z j / z i ≤ 1 := (le_abs_self _).trans habsdiv
      simpa using mul_le_mul_of_nonpos_left hquot (hoff i j (Ne.symm hji)).le
  have hsum : (∑ j, A i j) ≤ ∑ j, A i j * (z j / z i) :=
    Finset.sum_le_sum fun j _ ↦ hterm j
  rw [hnormalized] at hsum
  exact (not_lt_of_ge hsum) (hrow i)

end Towers.NumberTheory.Milne
