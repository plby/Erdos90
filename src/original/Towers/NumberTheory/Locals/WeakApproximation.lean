import Towers.NumberTheory.Locals.EquivalentAbsoluteValues
import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# Weak approximation

This file formalizes Milne's Lemma 7.18 and Theorem 7.20.  The theorem is first
stated as density of the diagonal embedding in the finite product of the
topologies defined by the absolute values, then in Milne's epsilon form.
-/

namespace Towers.NumberTheory.Milne

open Filter Fintype
open scoped Topology

section

variable {K : Type*} [Field K]
variable {ι : Type*} [Finite ι]
variable (v : ι → AbsoluteValue K ℝ)

/-- Milne, Lemma 7.18: one member of a finite pairwise inequivalent family can
be made larger than one while all the others are smaller than one. -/
theorem place_separating_element
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (i : ι) :
    ∃ a : K, 1 < v i a ∧ ∀ j ≠ i, v j a < 1 :=
  AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hnt hpair i

/-- The diagonal map from `K` to the finite product of the metric fields
defined by pairwise inequivalent absolute values has dense range.  This is the
topological form of Milne's Weak Approximation Theorem 7.20. -/
theorem weak_approximation_dense
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) :
    DenseRange (fun x : K ↦ fun i ↦ (WithAbs.equiv (v i)).symm x) := by
  classical
  letI := Fintype.ofFinite ι
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a ha using place_separating_element v hnt hpair
  let y : ℕ → K := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (v i) (z i)
  have hy : Tendsto
      (fun n i ↦ (WithAbs.equiv (v i)).symm (y n)) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun i ↦ ?_
    simp_rw [← Fintype.sum_pi_single i z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun j _ ↦ ?_
    by_cases hij : i = j
    · rw [← hij, Pi.single_eq_same]
      have hai : a i ≠ 0 := by
        exact (v i).pos_iff.mp (zero_lt_one.trans (ha i).1)
      have hinv : v i (a i)⁻¹ < 1 := by
        rw [map_inv₀, inv_lt_one_iff₀]
        exact Or.inr (ha i).1
      simp only [RingEquiv.symm_apply_apply]
      convert
        (WithAbs.tendsto_one_div_one_add_pow_nhds_one hinv).mul_const (z i) using 1
      exact congrArg (fun x ↦ 𝓝 x) (one_mul (z i)).symm
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (v i)) hij (z j)]
      have haj : a j ≠ 0 :=
        (v j).pos_iff.mp (zero_lt_one.trans (ha j).1)
      have hother : 1 < v i (a j)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(v i).pos haj, (ha j).2 i hij⟩
      have hzero := (v i).tendsto_div_one_add_pow_nhds_zero hother
      simp_rw [← WithAbs.norm_toAbs_eq] at hzero
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 hzero).mul_const
        ((WithAbs.equiv (v i)).symm (WithAbs.equiv (v j) (z j)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hy r hr
  exact ⟨y N, dist_comm z _ ▸ hN N le_rfl⟩

/-- Milne, Theorem 7.20: simultaneous approximation with respect to finitely
many nontrivial pairwise inequivalent absolute values. -/
theorem weakApproximation
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (target : ι → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, ∀ i, v i (x - target i) < ε := by
  classical
  letI := Fintype.ofFinite ι
  let z : (i : ι) → WithAbs (v i) := fun i ↦ (WithAbs.equiv (v i)).symm (target i)
  obtain ⟨x, hx⟩ :=
    (Metric.denseRange_iff.mp (weak_approximation_dense v hnt hpair)) z ε hε
  refine ⟨x, fun i ↦ ?_⟩
  have hi := (dist_pi_lt_iff hε).mp hx i
  simpa [z, dist_comm, dist_eq_norm, ← WithAbs.norm_toAbs_eq] using hi

/-- Milne, Lemma 7.19: there is an element simultaneously close to one at a
chosen place and close to zero at all the other places. -/
theorem close_place_elsewhere
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (i : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, v i (x - 1) < ε ∧ ∀ j ≠ i, v j x < ε := by
  classical
  obtain ⟨x, hx⟩ :=
    weakApproximation v hnt hpair (fun j ↦ if j = i then 1 else 0) hε
  refine ⟨x, ?_, fun j hji ↦ ?_⟩
  · simpa using hx i
  · simpa [hji] using hx j

end

end Towers.NumberTheory.Milne
