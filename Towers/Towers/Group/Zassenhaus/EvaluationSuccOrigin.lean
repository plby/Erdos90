import Towers.Group.Zassenhaus.PolynomialSucc
import Towers.Group.Zassenhaus.SignedRecipeEvaluation

namespace Towers
namespace TCTex
namespace BCExp

lemma binomial_basis_succ
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ)
    (hf :
      IVMost
        f (targetWeight / inputWeight)) :
    (binomialBasis inputWeight targetWeight hinputWeight
      (fun steps : ℕ => f (steps + 1))).evalInt (-1) =
        f 0 := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  let shift : Polynomial ℚ := Polynomial.X + Polynomial.C 1
  have hshift : shift.natDegree ≤ 1 := by
    dsimp [shift]
    rw [Polynomial.natDegree_X_add_C]
  have hPsuccDegree :
      (P.comp shift).natDegree ≤ targetWeight / inputWeight := by
    apply Polynomial.natDegree_comp_le.trans
    calc
      P.natDegree * shift.natDegree ≤ P.natDegree * 1 :=
        Nat.mul_le_mul_left P.natDegree hshift
      _ = P.natDegree := Nat.mul_one _
      _ ≤ targetWeight / inputWeight := hPdegree
  have hPsuccEval :
      ∀ steps : ℕ,
        (P.comp shift).eval (steps : ℚ) = (f (steps + 1) : ℚ) := by
    intro steps
    rw [Polynomial.eval_comp]
    simp only [shift, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    simpa using hPeval (steps + 1)
  have hcanonical :
      P.comp shift =
        natBinomialExpansion
          (fun steps : ℕ => f (steps + 1))
          (targetWeight / inputWeight) :=
    polynomial_binomial_expansion
      (P.comp shift) hPsuccDegree hPsuccEval
  have hneg :=
    congrArg (fun Q : Polynomial ℚ => Q.eval (-1)) hcanonical
  change
    (P.comp shift).eval (-1) =
      (natBinomialExpansion
        (fun steps : ℕ => f (steps + 1))
        (targetWeight / inputWeight)).eval (-1) at hneg
  rw [Polynomial.eval_comp] at hneg
  simp only [shift, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] at hneg
  norm_num at hneg
  have hPzero : P.eval (0 : ℚ) = (f 0 : ℚ) := by
    simpa using hPeval 0
  rw [hPzero, binomial_expansion_neg] at hneg
  rw [eval_int_binomial]
  exact_mod_cast hneg.symm

lemma binomial_basis_neg
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (f : ℕ → ℤ)
    (hf :
      IVMost
        f (targetWeight / inputWeight))
    (hzero : f 0 = 0) :
    (binomialBasis inputWeight targetWeight hinputWeight
      (fun steps : ℕ => f (steps + 1))).evalInt (-1) = 0 := by
  rw [binomial_basis_succ
    inputWeight targetWeight hinputWeight f hf, hzero]

lemma int_binomial_neg
    {ι : Type*}
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (slots : List ι)
    (f : ι → ℕ → ℤ)
    (hf :
      ∀ slot ∈ slots,
        IVMost
          (f slot) (targetWeight / inputWeight)) :
    (slots.map fun slot =>
      binomialBasis inputWeight targetWeight hinputWeight
        (fun steps : ℕ => f slot (steps + 1))).map
          (fun expansion => expansion.evalInt (-1)) =
      slots.map fun slot => f slot 0 := by
  rw [List.map_map]
  apply List.map_congr_left
  intro slot hslot
  exact
    binomial_basis_succ
      inputWeight targetWeight hinputWeight (f slot) (hf slot hslot)

lemma int_binomial_basis
    {ι : Type*}
    (inputWeight targetWeight : ℕ)
    (hinputWeight : 0 < inputWeight)
    (slots : List ι)
    (f : ι → ℕ → ℤ)
    (hf :
      ∀ slot ∈ slots,
        IVMost
          (f slot) (targetWeight / inputWeight))
    (hzero : ∀ slot ∈ slots, f slot 0 = 0) :
    (slots.map fun slot =>
      binomialBasis inputWeight targetWeight hinputWeight
        (fun steps : ℕ => f slot (steps + 1))).map
          (fun expansion => expansion.evalInt (-1)) =
      slots.map fun _slot => 0 := by
  rw [int_binomial_neg
    inputWeight targetWeight hinputWeight slots f hf]
  apply List.map_congr_left
  intro slot hslot
  exact hzero slot hslot

end BCExp
end TCTex
end Towers
