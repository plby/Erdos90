import Towers.Group.Zassenhaus.Normalization

/-!
# Normalizing generalized binomial coefficients of power exponents

Recursive Hall collection does not only multiply previously collected
exponents.  Higher corrections contain generalized binomial coefficients
`Ring.choose (f q) k`, where `f q` may be a signed integer exponent produced by
an earlier collection step.  This file proves the corresponding polynomial
closure theorem and normalizes those functions back to explicit repeated-block
recipes.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

/--
The rational Newton basis polynomial also evaluates to generalized binomial
coefficients on signed integer inputs.
-/
lemma nat_choose_int
    (z : ℤ)
    (k : ℕ) :
    (natChoosePolynomial k).eval (z : ℚ) =
      ((Ring.choose z k : ℤ) : ℚ) := by
  rw [natChoosePolynomial, Polynomial.eval_smul, Polynomial.eval_map,
    int_cast_smul, Polynomial.eval₂_smulOneHom_eq_smeval]
  rw [← Ring.choose_eq_smul]
  exact (Ring.map_choose (Int.castRingHom ℚ) z k).symm

namespace IVMost

/--
Taking a generalized binomial coefficient of a signed integer-valued
polynomial multiplies its degree bound by the binomial index.
-/
lemma ringChoose
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (k : ℕ) :
    IVMost
      (fun q : ℕ => Ring.choose (f q) k)
      (k * degreeBound) := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  refine ⟨(natChoosePolynomial k).comp P, ?_, ?_⟩
  · exact Polynomial.natDegree_comp_le.trans
      (Nat.mul_le_mul
        (degree_choose_polynomial k)
        hPdegree)
  · intro q
    rw [Polynomial.eval_comp, hPeval q, nat_choose_int]

end IVMost

/--
Scaling a target weight by `k` leaves room for a degree bound scaled by `k`.
-/
lemma le_div_left
    (k targetWeight inputWeight : ℕ) :
    k * (targetWeight / inputWeight) ≤
      (k * targetWeight) / inputWeight := by
  by_cases hinputWeight : inputWeight = 0
  · simp [hinputWeight]
  · rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hinputWeight)]
    calc
      k * (targetWeight / inputWeight) * inputWeight =
          k * ((targetWeight / inputWeight) * inputWeight) := by
            rw [Nat.mul_assoc]
      _ ≤ k * targetWeight :=
        Nat.mul_le_mul_left k (Nat.div_mul_le_self targetWeight inputWeight)

namespace BCExp

/--
Normalize a generalized binomial coefficient of a signed exponent into the
Newton repeated-block basis at a scaled target weight.
-/
noncomputable def ringChoose
    (inputWeight targetWeight k : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ) :
    BCExp inputWeight (k * targetWeight) :=
  binomialBasis inputWeight (k * targetWeight) hinputWeight
    (fun q : ℕ => Ring.choose (f q) k)

/--
The explicit scaled-weight expansion evaluates to the generalized binomial
coefficient of the original exponent.
-/
lemma eval_ringChoose
    {inputWeight targetWeight k : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      IVMost
        f (targetWeight / inputWeight)) :
    (ringChoose inputWeight targetWeight k hinputWeight f).eval =
      fun q : ℕ => Ring.choose (f q) k := by
  exact eval_binomialBasis hinputWeight
    ((hf.ringChoose k).mono
      (le_div_left k targetWeight inputWeight))

end BCExp

/--
Generalized binomial coefficients of bounded signed exponents belong to the
span of bounded repeated-block recipes at the corresponding scaled weight.
-/
theorem combination_recipes_choose
    {inputWeight targetWeight k : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      IVMost
        f (targetWeight / inputWeight)) :
    IntCombinationRecipes
      inputWeight (k * targetWeight)
      (fun q : ℕ => Ring.choose (f q) k) := by
  rw [← BCExp.eval_ringChoose hinputWeight hf]
  exact
    (BCExp.ringChoose
      inputWeight targetWeight k hinputWeight f).eval_recipe_span

end TCTex
end Towers
