import Towers.Group.Zassenhaus.Normalization

/-!
# Partial sums of integer-valued power-collection polynomials

Triangular symbolic collection recurrences accumulate lower-weight
coordinates one repeated block at a time.  This file packages the discrete
antidifference step in the Newton-binomial basis: taking partial sums raises
the degree bound by one.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace IVMost

/-- Differences preserve a common integer-valued polynomial degree bound. -/
lemma sub
    {f g : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (hg : IVMost g degreeBound) :
    IVMost (f - g) degreeBound := by
  simpa [sub_eq_add_neg] using
    hf.add
      (TCTex.IVMost.smul
        (-1) hg)

/-- Hockey-stick identity in the exact range form needed by partial sums. -/
lemma range_nat_choose
    (steps k : ℕ) :
    ∑ j ∈ Finset.range steps, j.choose k =
      steps.choose (k + 1) := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ']
      simp [Nat.add_comm]

lemma sum_choose_int
    (steps k : ℕ) :
    ∑ j ∈ Finset.range steps, (j.choose k : ℤ) =
      (steps.choose (k + 1) : ℤ) := by
  exact_mod_cast range_nat_choose steps k

/-- The shifted Newton-binomial expansion representing the partial sums of
an integer-valued polynomial. -/
noncomputable def partialSumPolynomial
    (f : ℕ → ℤ)
    (degreeBound : ℕ) :
    Polynomial ℚ :=
  ∑ k ∈ Finset.range (degreeBound + 1),
    Polynomial.C (natBinomialCoefficient f k : ℚ) *
      natChoosePolynomial (k + 1)

lemma nat_degree_partial
    (f : ℕ → ℤ)
    (degreeBound : ℕ) :
    (partialSumPolynomial f degreeBound).natDegree ≤ degreeBound + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkdegree : k + 1 ≤ degreeBound + 1 := by
    exact Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  calc
    (Polynomial.C (natBinomialCoefficient f k : ℚ) *
        natChoosePolynomial (k + 1)).natDegree ≤
        (Polynomial.C (natBinomialCoefficient f k : ℚ)).natDegree +
          (natChoosePolynomial (k + 1)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + (k + 1) := by
      gcongr
      · simp
      · exact degree_choose_polynomial (k + 1)
    _ ≤ degreeBound + 1 := by simpa using hkdegree

lemma partial_sum_polynomial
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (steps : ℕ) :
    (partialSumPolynomial f degreeBound).eval (steps : ℚ) =
      ((∑ j ∈ Finset.range steps, f j : ℤ) : ℚ) := by
  rw [partialSumPolynomial, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_C_mul, eval_nat_choose]
  norm_cast
  calc
    ∑ k ∈ Finset.range (degreeBound + 1),
        natBinomialCoefficient f k * (steps.choose (k + 1) : ℤ) =
        ∑ k ∈ Finset.range (degreeBound + 1),
          natBinomialCoefficient f k *
            (∑ j ∈ Finset.range steps, (j.choose k : ℤ)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [sum_choose_int]
    _ = ∑ j ∈ Finset.range steps,
          ∑ k ∈ Finset.range (degreeBound + 1),
            natBinomialCoefficient f k * (j.choose k : ℤ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range steps, f j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (hf.nat_binomial_basisexpansion j).symm

/-- Partial sums raise the degree bound of an integer-valued polynomial by
one. -/
lemma partialSum
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound) :
    IVMost
      (fun steps : ℕ => ∑ j ∈ Finset.range steps, f j)
      (degreeBound + 1) := by
  exact
    ⟨partialSumPolynomial f degreeBound,
      nat_degree_partial f degreeBound,
      partial_sum_polynomial hf⟩

end IVMost
end TCTex
end Towers
