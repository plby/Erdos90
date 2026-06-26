import Submission.Group.Zassenhaus.ChooseNormalization

/-!
# Newton expansion values at negative one

The predecessor-origin boundary for symbolic collection polynomials is most
transparent in the Newton basis. Evaluate the canonical truncated Newton
polynomial on signed integer inputs and specialize at `-1`, where generalized
binomial coefficients become alternating signs.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

/-- The canonical truncated Newton polynomial evaluates on signed integer
inputs by replacing ordinary natural binomial coefficients with generalized
ring binomial coefficients. -/
lemma binomial_expansion_int
    (f : ℕ → ℤ)
    (m : ℕ)
    (z : ℤ) :
    (natBinomialExpansion f m).eval (z : ℚ) =
      ((∑ k ∈ Finset.range (m + 1),
        natBinomialCoefficient f k * Ring.choose z k : ℤ) : ℚ) := by
  rw [natBinomialExpansion, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_C_mul, nat_choose_int]
  norm_cast

/-- Generalized binomial coefficients at `-1` are alternating signs. -/
lemma ring_choose_neg
    (k : ℕ) :
    Ring.choose (-1 : ℤ) k = (-1 : ℤ) ^ k := by
  rw [Ring.choose_neg']
  simp [Units.smul_def, Int.coe_negOnePow_natCast]

/-- Evaluation of the canonical truncated Newton polynomial at `-1` is the
alternating sum of its Newton coefficients. -/
lemma binomial_expansion_neg
    (f : ℕ → ℤ)
    (m : ℕ) :
    (natBinomialExpansion f m).eval (-1) =
      ((∑ k ∈ Finset.range (m + 1),
        natBinomialCoefficient f k * (-1 : ℤ) ^ k : ℤ) : ℚ) := by
  rw [show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num,
    binomial_expansion_int]
  apply congrArg
  apply Finset.sum_congr rfl
  intro k _hk
  rw [ring_choose_neg]

/-- Any degree-bounded natural polynomial witness is the canonical truncated
Newton polynomial selected by its natural values. -/
lemma polynomial_binomial_expansion
    {f : ℕ → ℤ}
    {m : ℕ}
    (P : Polynomial ℚ)
    (hPdegree : P.natDegree ≤ m)
    (hPeval : ∀ q : ℕ, P.eval (q : ℚ) = (f q : ℚ)) :
    P = natBinomialExpansion f m := by
  let hf : IVMost f m :=
    ⟨P, hPdegree, hPeval⟩
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem
    (Nat.cast_injective :
      Function.Injective (fun q : ℕ => (q : ℚ)))
  intro q
  change
    P.eval (q : ℚ) =
      (natBinomialExpansion f m).eval (q : ℚ)
  rw [hPeval q, binomial_expansion_polynomial]
  norm_cast
  exact hf.nat_binomial_basisexpansion q

end TCTex
end Submission
