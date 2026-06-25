import Mathlib
import Towers.Group.GolodShafarevichCore


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

namespace GShafar

/-- Above the truncation range itself, the zero-extended sequence vanishes. -/
lemma truncated_sequence_zero
    {a : ℕ → ℝ} {N n : ℕ} (hn : N < n) :
    truncatedSequence a N n = 0 := by
  rw [truncatedSequence]
  exact if_neg (Nat.not_le.mpr hn)
/--
The shifted linear contribution vanishes above the finite coefficient window.
-/
lemma sequence_pred_window
    {a : ℕ → ℝ} {N n : ℕ} {r : ℕ} {depth : Fin r → ℕ}
    (hn : truncationWindow N depth < n) :
    (if 1 ≤ n then truncatedSequence a N (n - 1) else 0) = 0 := by
  have hn_pos : 1 ≤ n := by
    have hN_nonneg : 0 ≤ N + max 1 (Finset.univ.sup depth) := Nat.zero_le _
    have hzero_lt : 0 < n := lt_of_le_of_lt hN_nonneg hn
    exact Nat.succ_le_of_lt hzero_lt
  have hN_lt_pred : N < n - 1 := by
    dsimp [truncationWindow] at hn
    have hN_plus_one_lt : N + 1 < n := by
      exact lt_of_le_of_lt
        (Nat.add_le_add_left (le_max_left 1 (Finset.univ.sup depth)) N) hn
    omega
  simp [hn_pos, truncated_sequence_zero (a := a) hN_lt_pred]
/--
Each shifted relator contribution vanishes above the finite coefficient window.
-/
lemma truncated_sequence_window
    {a : ℕ → ℝ} {N n : ℕ} {r : ℕ} {depth : Fin r → ℕ}
    (hn : truncationWindow N depth < n) (i : Fin r) :
    (if depth i ≤ n then truncatedSequence a N (n - depth i) else 0) = 0 := by
  by_cases hle : depth i ≤ n
  · have hdepth_le_sup : depth i ≤ Finset.univ.sup depth := by
      exact Finset.le_sup (by simp)
    have hN_lt_sub : N < n - depth i := by
      dsimp [truncationWindow] at hn
      have hN_plus_depth_lt : N + depth i < n := by
        exact lt_of_le_of_lt
          (Nat.add_le_add_left
            (le_trans hdepth_le_sup (le_max_right 1 (Finset.univ.sup depth))) N)
          hn
      omega
    simp [hle, truncated_sequence_zero (a := a) hN_lt_sub]
  · simp [hle]

end GShafar

end Towers
