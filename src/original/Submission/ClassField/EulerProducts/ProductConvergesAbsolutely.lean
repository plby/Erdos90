import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter VI, Section 2, Lemma 2.6

The book defines absolute convergence of `∏ (1 + bₙ)` to mean convergence
of `∏ (1 + |bₙ|)` to a nonzero value.  We encode exactly that definition
using Mathlib's unconditional infinite product and prove its equivalence
with absolute convergence of `∑ bₙ`.
-/

namespace Submission.CField.EProduc

open scoped BigOperators

/-- Literal absolute convergence of the product `∏ (1 + b i)`: the product
of the positive real factors `1 + ‖b i‖` exists and has nonzero value. -/
def ProductConvergesAbsolutely {ι : Type*} (b : ι → ℂ) : Prop :=
  Multipliable (fun i ↦ 1 + ‖b i‖) ∧
    ∏' i, (1 + ‖b i‖) ≠ 0

private theorem add_sum_prod
    {ι : Type*} (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (s : Finset ι) :
    1 + ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 + b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsum : 0 ≤ ∑ i ∈ s, b i :=
        Finset.sum_nonneg fun i _ ↦ hb i
      calc
        1 + (b a + ∑ i ∈ s, b i) ≤
            (1 + b a) * (1 + ∑ i ∈ s, b i) := by
          nlinarith [hb a]
        _ ≤ (1 + b a) * ∏ i ∈ s, (1 + b i) :=
          mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one (hb a))

/-- If the positive product is multipliable, its finite products are
bounded; the elementary inequality `1 + ∑ |bᵢ| ≤ ∏ (1 + |bᵢ|)` then bounds
all finite subsums. -/
private theorem summable_multipliable_add
    {ι : Type*} {b : ι → ℂ}
    (hprod : Multipliable (fun i ↦ 1 + ‖b i‖)) :
    Summable fun i ↦ ‖b i‖ := by
  classical
  obtain ⟨r, hr, s, hs⟩ := hprod.eventually_bounded_finsetProd
  refine summable_of_sum_le (c := r) (fun i ↦ norm_nonneg (b i)) ?_
  intro u
  let t := s ∪ u
  have hut : u ⊆ t := Finset.subset_union_right
  have hst : s ⊆ t := Finset.subset_union_left
  calc
    ∑ i ∈ u, ‖b i‖ ≤ ∑ i ∈ t, ‖b i‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hut
        (fun _ _ _ ↦ norm_nonneg _)
    _ ≤ 1 + ∑ i ∈ t, ‖b i‖ := le_add_of_nonneg_left zero_le_one
    _ ≤ ∏ i ∈ t, (1 + ‖b i‖) :=
      add_sum_prod (fun i ↦ ‖b i‖)
        (fun i ↦ norm_nonneg _) t
    _ ≤ r := hs t hst

/-- **Lemma VI.2.6.**  The product `∏ (1 + bₙ)` converges absolutely if
and only if the series `∑ bₙ` converges absolutely. -/
theorem converges_absolutely_summable
    {ι : Type*} (b : ι → ℂ) :
    ProductConvergesAbsolutely b ↔ Summable fun i ↦ ‖b i‖ := by
  constructor
  · exact fun h ↦ summable_multipliable_add h.1
  · intro h
    refine ⟨Real.multipliable_one_add_of_summable h, ?_⟩
    have h' : Summable fun i ↦ ‖‖b i‖‖ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg] using h
    exact tprod_one_add_ne_zero_of_summable
      (fun i ↦ by positivity) h'

end Submission.CField.EProduc
