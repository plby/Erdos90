import Submission.Group.Zassenhaus.PolynomialNegOne
import Submission.Group.Zassenhaus.Normalization


/-!
# Signed evaluation of repeated-block recipes

Repeated-block recipes are naturally evaluated on natural multiplicities.
Their binomial basis also has a canonical signed extension through generalized
binomial coefficients.  Define that extension and identify evaluation at `-1`
with the alternating Newton-coefficient sum.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

namespace PBRecipe

/-- Signed evaluation of a repeated-block recipe through generalized binomial
coefficients. -/
def evalInt
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight)
    (z : ℤ) :
    ℤ :=
  (recipe.indices.map fun k => Ring.choose z k).prod

@[simp]
lemma evalInt_empty
    (inputWeight : ℕ)
    (z : ℤ) :
    (empty inputWeight).evalInt z = 1 := by
  simp [evalInt, empty]

@[simp]
lemma evalInt_select
    (inputWeight k : ℕ)
    (hk : 0 < k)
    (z : ℤ) :
    (select inputWeight k hk).evalInt z = Ring.choose z k := by
  simp [evalInt, select]

/-- Signed recipe evaluation restricts to the original evaluation on natural
inputs. -/
lemma evalInt_nat
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight)
    (q : ℕ) :
    recipe.evalInt (q : ℤ) = recipe.eval q := by
  simp [evalInt, eval, Ring.choose_natCast]

end PBRecipe

namespace BBRecipe

/-- Signed evaluation of a bounded repeated-block recipe. -/
def evalInt
    {inputWeight targetWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight)
    (z : ℤ) :
    ℤ :=
  recipe.toPBRecipe.evalInt z

@[simp]
lemma evalInt_empty
    (inputWeight targetWeight : ℕ)
    (z : ℤ) :
    (empty inputWeight targetWeight).evalInt z = 1 :=
  PBRecipe.evalInt_empty inputWeight z

@[simp]
lemma evalInt_select
    (inputWeight targetWeight k : ℕ)
    (hk : 0 < k)
    (hweight : inputWeight * k ≤ targetWeight)
    (z : ℤ) :
    (select inputWeight targetWeight k hk hweight).evalInt z =
      Ring.choose z k :=
  PBRecipe.evalInt_select inputWeight k hk z

@[simp]
lemma eval_binomial_basis
    (inputWeight targetWeight k : ℕ)
    (hinputWeight : 0 < inputWeight)
    (hk : k ≤ targetWeight / inputWeight)
    (z : ℤ) :
    (binomialBasis inputWeight targetWeight k hinputWeight hk).evalInt z =
      Ring.choose z k := by
  by_cases hkZero : k = 0
  · subst k
    rw [binomialBasis, dif_pos rfl]
    simp
  · rw [binomialBasis, dif_neg hkZero]
    exact evalInt_select inputWeight targetWeight k _ _ z

end BBRecipe

namespace BRTerm

/-- Signed evaluation of one integer-weighted repeated-block recipe term. -/
def evalInt
    {inputWeight targetWeight : ℕ}
    (term : BRTerm inputWeight targetWeight)
    (z : ℤ) :
    ℤ :=
  term.1 * term.2.evalInt z

end BRTerm

namespace BCExp

/-- Signed evaluation of a finite repeated-block coordinate expansion. -/
def evalInt
    {inputWeight targetWeight : ℕ}
    (expansion : BCExp inputWeight targetWeight)
    (z : ℤ) :
    ℤ :=
  (expansion.terms.map fun term => term.evalInt z).sum

/-- The Newton-normalized recipe expansion evaluates on signed integer inputs
as the corresponding generalized-binomial sum. -/
lemma eval_binomial_basis
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ)
    (z : ℤ) :
    (binomialBasis inputWeight targetWeight hinputWeight f).evalInt z =
      ∑ k ∈ Finset.range (targetWeight / inputWeight + 1),
        natBinomialCoefficient f k * Ring.choose z k := by
  rw [evalInt, binomialBasis]
  simp only [List.map_ofFn, Function.comp_apply, BRTerm.evalInt,
    List.sum_ofFn, BBRecipe.eval_binomial_basis]
  exact
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ => natBinomialCoefficient f k * Ring.choose z k)
      (targetWeight / inputWeight + 1)

/-- At `-1`, the signed Newton-normalized recipe expansion is the alternating
sum of its Newton coefficients. -/
lemma eval_int_binomial
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ) :
    (binomialBasis inputWeight targetWeight hinputWeight f).evalInt (-1) =
      ∑ k ∈ Finset.range (targetWeight / inputWeight + 1),
        natBinomialCoefficient f k * (-1 : ℤ) ^ k := by
  rw [eval_binomial_basis]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [ring_choose_neg]

end BCExp

end TCTex
end Submission
