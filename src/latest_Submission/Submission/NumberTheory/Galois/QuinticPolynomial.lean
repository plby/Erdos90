import Submission.NumberTheory.Discriminant.PolynomialExamples
import Submission.NumberTheory.Galois.PermutationGroupCriterion

/-!
# Milne, Chapter 8, Example 8.25

The polynomial `X^5 - X - 1` factors modulo `2` as a product of irreducible
polynomials of degrees two and three, and its reduction modulo `3` is
irreducible.  For the latter claim, the degree-one case is excluded by
checking roots; a hypothetical monic quadratic divisor is then ruled out by
comparing coefficients with its monic cubic quotient.

The final theorem records the group-theoretic step: a subgroup of `S₅`
containing a full cycle and an element whose cube is a transposition is all
of `S₅`.  Turning the finite-field factorizations into elements of the
Galois group is the content of the Frobenius-cycle form of Dedekind's theorem
formalized in `DedekindTheorem`.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset Polynomial

/-- The rational irreducibility assertion recalled in Example 8.25. -/
theorem irreducible_over_rat :
    Irreducible (X ^ 5 - X - 1 : ℚ[X]) :=
  irreducible_x_five

/-- The displayed factorization of `X^5 - X - 1` modulo `2`. -/
theorem factorization_mod_two :
    (X ^ 5 - X - 1 : (ZMod 2)[X]) =
      (X ^ 2 + X + 1) * (X ^ 3 + X ^ 2 + 1) := by
  ring_nf
  reduce_mod_char

/-- The quadratic factor in the mod-`2` factorization is irreducible. -/
theorem quadratic_factor_irreducible :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
      rw [show (X ^ 2 + X + 1 : (ZMod 2)[X]) = X ^ 2 + (X + 1) by ring]
      exact ((isMonicOfDegree_X_pow (ZMod 2) 2).add_right (by
        compute_degree
        norm_num)).natDegree_eq
    simp [hdeg]
  · intro x hx
    fin_cases x <;>
      exact one_ne_zero (by simpa [IsRoot.def] using hx)

/-- The cubic factor in the mod-`2` factorization is irreducible. -/
theorem cubic_factor_irreducible :
    Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by
      rw [show (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) = X ^ 3 + (X ^ 2 + 1) by ring]
      exact ((isMonicOfDegree_X_pow (ZMod 2) 3).add_right (by
        compute_degree
        norm_num)).natDegree_eq
    simp [hdeg]
  · intro x hx
    fin_cases x <;>
      exact one_ne_zero (by simpa [IsRoot.def] using hx)

/-- A directly checked part of the mod-`3` computation: the polynomial has
no linear factor.  This statement intentionally does not claim that it has
no quadratic factor. -/
theorem no_mod_three (x : ZMod 3) :
    ¬(X ^ 5 - X - 1 : (ZMod 3)[X]).IsRoot x := by
  fin_cases x <;> norm_num [IsRoot.def] <;> reduce_mod_char <;> decide

/-- The reduction of `X^5 - X - 1` modulo `3` is irreducible, as asserted in
Milne's Example 8.25. -/
theorem irreducible_mod_three :
    Irreducible (X ^ 5 - X - 1 : (ZMod 3)[X]) := by
  let p : (ZMod 3)[X] := X ^ 5 - X - 1
  have hpmonic : p.Monic := by
    rw [show p = X ^ 5 + (-X - 1) by simp only [p]; ring]
    exact ((isMonicOfDegree_X_pow (ZMod 3) 5).add_right (by
      compute_degree
      norm_num)).monic
  have hpne : p ≠ 1 := by
    intro hp
    have hdegree := congrArg natDegree hp
    have : p.natDegree = 5 := by
      simp only [p]
      compute_degree
      norm_num
    simp [this] at hdegree
  rw [hpmonic.irreducible_iff_lt_natDegree_lt hpne]
  intro q hqmonic hqdegree hqdvd
  have hpdegree : p.natDegree = 5 := by
    simp only [p]
    compute_degree
    norm_num
  rw [hpdegree] at hqdegree
  have hqcases : q.natDegree = 1 ∨ q.natDegree = 2 := by
    simp only [mem_Ioc] at hqdegree
    omega
  rcases hqcases with hqdegree | hqdegree
  · have hdegree : q.degree = 1 :=
      (degree_eq_iff_natDegree_eq hqmonic.ne_zero).2 hqdegree
    have hq : q = X - C (-q.coeff 0) := by
      simpa [hqmonic.leadingCoeff] using
        eq_X_add_C_of_degree_eq_one hdegree
    rw [hq] at hqdvd
    exact no_mod_three (-q.coeff 0)
      (dvd_iff_isRoot.mp hqdvd)
  · have hq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      ext n
      by_cases hn : n ≤ 2
      · interval_cases n
        · simp
        · simp
        · simpa [hqdegree] using hqmonic.coeff_natDegree
      · have hlt : q.natDegree < n := by omega
        simp [coeff_eq_zero_of_natDegree_lt hlt, coeff_X, coeff_C,
          show n ≠ 0 by omega, show 1 ≠ n by omega,
          show n ≠ 2 by omega]
    let a : ZMod 3 := q.coeff 1
    let b : ZMod 3 := q.coeff 0
    rcases hqdvd with ⟨r, hr⟩
    have hrmonic : r.Monic := by
      apply hqmonic.of_mul_monic_left
      rwa [← hr]
    have hrdegree : r.natDegree = 3 := by
      have hdegree := congrArg natDegree hr
      rw [hqmonic.natDegree_mul hrmonic, hpdegree, hqdegree] at hdegree
      omega
    have hrform :
        r = X ^ 3 + C (r.coeff 2) * X ^ 2 + C (r.coeff 1) * X + C (r.coeff 0) := by
      ext n
      by_cases hn : n ≤ 3
      · interval_cases n
        · simp
        · simp
        · simp
        · simpa [hrdegree] using hrmonic.coeff_natDegree
      · have hlt : r.natDegree < n := by omega
        simp [coeff_eq_zero_of_natDegree_lt hlt, coeff_X, coeff_C,
          show n ≠ 0 by omega, show 1 ≠ n by omega,
          show n ≠ 2 by omega, show n ≠ 3 by omega]
    let c : ZMod 3 := r.coeff 2
    let d : ZMod 3 := r.coeff 1
    let e : ZMod 3 := r.coeff 0
    have hprod :
        p = (X ^ 2 + C a * X + C b) *
          (X ^ 3 + C c * X ^ 2 + C d * X + C e) := by
      simpa only [a, b, c, d, e, ← hq, ← hrform] using hr
    have h0 := congrArg (fun f : (ZMod 3)[X] ↦ f.coeff 0) hprod
    have h1 := congrArg (fun f : (ZMod 3)[X] ↦ f.coeff 1) hprod
    have h2 := congrArg (fun f : (ZMod 3)[X] ↦ f.coeff 2) hprod
    have h3 := congrArg (fun f : (ZMod 3)[X] ↦ f.coeff 3) hprod
    have h4 := congrArg (fun f : (ZMod 3)[X] ↦ f.coeff 4) hprod
    simp only [p, coeff_sub, coeff_add, coeff_mul, coeff_X_pow, coeff_X, coeff_C] at h0 h1 h2 h3 h4
    norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_one] at h0 h1 h2 h3 h4
    clear_value a b c d e
    have hc : c = -a := by linear_combination -h4
    subst c
    have hd : d = -b - a * -a := by linear_combination -h3
    subst d
    have he : e = -(b * -a) - a * (-b - a * -a) := by
      linear_combination -h2
    subst e
    fin_cases a <;> fin_cases b <;>
      norm_num at h0 h1 <;> reduce_mod_char at h0 h1 <;> contradiction

/-- The group-theoretic conclusion of Example 8.25.  Milne obtains `rho`
from the mod-`2` factorization: it is a product of disjoint cycles of lengths
two and three, so its cube is a transposition. -/
theorem quintic_x_5
    (H : Subgroup (Equiv.Perm (Fin 5))) {sigma rho : Equiv.Perm (Fin 5)}
    (hsigmaCycle : sigma.IsCycle) (hsigmaSupport : sigma.support = univ)
    (hrhoCube : (rho ^ 3).IsSwap) (hsigma : sigma ∈ H) (hrho : rho ∈ H) :
    H = ⊤ := by
  apply perm_cycle_swap H
      (sigma := sigma) (tau := rho ^ 3)
  · norm_num
  · exact hsigmaCycle
  · exact hsigmaSupport
  · exact hrhoCube
  · exact hsigma
  · exact H.pow_mem hrho 3

end Submission.NumberTheory.Milne
