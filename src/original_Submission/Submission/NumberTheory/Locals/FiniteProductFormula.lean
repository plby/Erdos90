import Submission.NumberTheory.Locals.WeakApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# No finite product formula

Milne's Corollary 7.21 is a direct consequence of weak approximation: a
finite multiplicative relation among pairwise inequivalent absolute values
has only zero exponents.
-/

namespace Submission.NumberTheory.Milne

open Filter Fintype
open scoped Topology

section

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι]
variable (v : ι → AbsoluteValue K ℝ)

/-- Milne, Corollary 7.21: nontrivial pairwise inequivalent absolute values
cannot satisfy a nontrivial finite product formula. -/
theorem formula_exponents_zero
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (r : ι → ℝ)
    (hprod : ∀ a : K, a ≠ 0 → ∏ i, (v i a) ^ r i = 1) :
    ∀ i, r i = 0 := by
  classical
  let diagonal : K → (i : ι) → WithAbs (v i) :=
    fun x i ↦ (WithAbs.equiv (v i)).symm x
  have hdense : DenseRange diagonal := by
    simpa [diagonal] using weak_approximation_dense v hnt hpair
  intro i
  obtain ⟨b, hb⟩ := (hnt i).exists_abv_gt_one
  let z : (j : ι) → WithAbs (v j) :=
    fun j ↦ (WithAbs.equiv (v j)).symm (if j = i then b else 1)
  let productMap : ((j : ι) → WithAbs (v j)) → ℝ :=
    fun y ↦ ∏ j, ‖y j‖ ^ r j
  have hz_ne_zero (j : ι) : ‖z j‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    simp only [z]
    split_ifs with h
    · subst j
      exact (map_ne_zero (WithAbs.equiv (v i)).symm).mpr
        ((v i).pos_iff.mp (zero_lt_one.trans hb))
    · exact (map_ne_zero (WithAbs.equiv (v j)).symm).mpr one_ne_zero
  have hcontinuous : ContinuousAt productMap z := by
    change Tendsto (fun y ↦ ∏ j, ‖y j‖ ^ r j) (𝓝 z)
      (𝓝 (∏ j, ‖z j‖ ^ r j))
    exact tendsto_finsetProd Finset.univ fun j _ ↦
      (continuousAt_apply j z).norm.rpow_const (Or.inl (hz_ne_zero j))
  have hproduct_z : productMap z = 1 := by
    by_contra hne
    have hnear_product : ∀ᶠ y in 𝓝 z, productMap y ≠ 1 :=
      hcontinuous.eventually_ne hne
    have hz_ne_diagonal_zero : z ≠ diagonal 0 := by
      intro h
      have hi := congr_fun h i
      have hnorm : v i b = v i 0 := by
        simpa only [z, diagonal, if_pos, WithAbs.norm_toAbs_eq] using congrArg norm hi
      rw [map_zero] at hnorm
      exact (ne_of_gt (zero_lt_one.trans hb)) hnorm
    have hnear_nonzero : ∀ᶠ y in 𝓝 z, y ≠ diagonal 0 :=
      eventually_ne_nhds hz_ne_diagonal_zero
    obtain ⟨a, ha_product, ha_nonzero⟩ :=
      hdense.mem_nhds (hnear_product.and hnear_nonzero)
    have ha0 : a ≠ 0 := by
      intro ha
      exact ha_nonzero (congrArg diagonal ha)
    apply ha_product
    simpa [productMap, diagonal, WithAbs.norm_toAbs_eq] using hprod a ha0
  have hri : (v i b) ^ r i = 1 := by
    rw [show productMap z = ∏ j, (v j (if j = i then b else 1)) ^ r j by
      simp [productMap, z, WithAbs.norm_toAbs_eq]] at hproduct_z
    rw [Finset.prod_eq_single i] at hproduct_z
    · simpa using hproduct_z
    · intro j _ hji
      simp [hji]
    · simp
  have hpow : (v i b) ^ r i = (v i b) ^ (0 : ℝ) := by
    simpa using hri
  exact (Real.rpow_right_inj (zero_lt_one.trans hb) (ne_of_gt hb)).mp hpow

end

end Submission.NumberTheory.Milne
