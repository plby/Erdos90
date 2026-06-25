import Submission.Group.Zassenhaus.Expansions

/-!
# Normalizing power-collection polynomials back to recipes

Higher Hall corrections are formed by polynomial operations on previously
collected exponents.  The collector still needs finite repeated-block recipes
as output.  This file closes that loop: every integer-valued polynomial with
the required degree bound has an explicit bounded Newton-binomial recipe
expansion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

namespace IVMost

/-- A polynomial degree bound may be enlarged. -/
lemma mono
    {f : ℕ → ℤ}
    {degreeBound largerBound : ℕ}
    (hdegree : degreeBound ≤ largerBound)
    (hf : IVMost f degreeBound) :
    IVMost f largerBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  exact ⟨P, hPdegree.trans hdegree, hPeval⟩

/-- Products add degree bounds. -/
lemma mul
    {f g : ℕ → ℤ}
    {leftDegree rightDegree : ℕ}
    (hf : IVMost f leftDegree)
    (hg : IVMost g rightDegree) :
    IVMost
      (f * g) (leftDegree + rightDegree) := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  rcases hg with ⟨Q, hQdegree, hQeval⟩
  refine ⟨P * Q, Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add hPdegree hQdegree), ?_⟩
  intro q
  simp [Polynomial.eval_mul, hPeval q, hQeval q]

end IVMost

namespace BBRecipe

/--
The bounded recipe representing the Newton basis function `q ↦ choose q k`.
-/
def binomialBasis
    (inputWeight targetWeight k : ℕ)
    (hinputWeight : 0 < inputWeight)
    (hk : k ≤ targetWeight / inputWeight) :
    BBRecipe inputWeight targetWeight :=
  if hkZero : k = 0 then
    BBRecipe.empty inputWeight targetWeight
  else
    BBRecipe.select inputWeight targetWeight k
      (Nat.pos_of_ne_zero hkZero)
      (by
        rw [Nat.le_div_iff_mul_le hinputWeight] at hk
        simpa [Nat.mul_comm] using hk)

@[simp]
lemma eval_binomialBasis
    (inputWeight targetWeight k : ℕ)
    (hinputWeight : 0 < inputWeight)
    (hk : k ≤ targetWeight / inputWeight) :
    (binomialBasis inputWeight targetWeight k hinputWeight hk).eval =
      fun q : ℕ => (Nat.choose q k : ℤ) := by
  ext q
  by_cases hkZero : k = 0
  · subst k
    simp only [binomialBasis, dif_pos]
    simpa [BBRecipe.eval, BBRecipe.empty] using
      PBRecipe.eval_empty inputWeight q
  · simp only [binomialBasis, dif_neg hkZero]
    simpa [BBRecipe.eval, BBRecipe.select] using
      PBRecipe.eval_select inputWeight k q (Nat.pos_of_ne_zero hkZero)

end BBRecipe

namespace BCExp

/--
The explicit Newton-binomial recipe expansion associated to a function with
the target weight's maximal allowed degree.
-/
noncomputable def binomialBasis
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ) :
    BCExp inputWeight targetWeight where
  terms :=
    List.ofFn fun k : Fin (targetWeight / inputWeight + 1) =>
      (natBinomialCoefficient f k,
        BBRecipe.binomialBasis inputWeight targetWeight k
          hinputWeight (Nat.lt_succ_iff.mp k.isLt))

/--
Newton normalization evaluates to the original integer-valued polynomial.
-/
lemma eval_binomialBasis
    {inputWeight targetWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      IVMost
        f (targetWeight / inputWeight)) :
    (binomialBasis inputWeight targetWeight hinputWeight f).eval = f := by
  ext q
  rw [BCExp.eval]
  simp only [binomialBasis, List.map_ofFn, Function.comp_apply,
    BRTerm.eval, List.sum_ofFn, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, BBRecipe.eval_binomialBasis]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => natBinomialCoefficient f k * (Nat.choose q k : ℤ))]
  exact (hf.nat_binomial_basisexpansion q).symm

end BCExp

/--
Every bounded integer-valued polynomial belongs to the span of bounded
repeated-block recipes.
-/
theorem int_combination_recipes
    {inputWeight targetWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      IVMost
        f (targetWeight / inputWeight)) :
    IntCombinationRecipes
      inputWeight targetWeight f := by
  rw [← BCExp.eval_binomialBasis hinputWeight hf]
  exact
    (BCExp.binomialBasis
      inputWeight targetWeight hinputWeight f).eval_recipe_span

end TCTex
end Submission
