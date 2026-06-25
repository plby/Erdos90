import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree

/-!
# Milne, Chapter 7, Exercise 7-8(a)

The two cubics `X³ + X² + X + 1` and `X³ + X² + X - 1` have the same
coefficient norms over `ℚ_[5]`, hence the same Newton polygon.  The first is
reducible, while the second is irreducible.

Milne's printed solution names `X - 1` as a factor of the first cubic; this is
a typo.  The factor is `X + 1`.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

noncomputable section

local instance fivePrimeFact_8a : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The reducible cubic in Exercise 7-8(a). -/
def Reducible : ℚ_[5][X] :=
  X ^ 3 + X ^ 2 + X + 1

/-- The irreducible cubic in Exercise 7-8(a). -/
def locallyReducibleIrreducible : ℚ_[5][X] :=
  X ^ 3 + X ^ 2 + X - 1

/-- The first example is a monic cubic. -/
theorem reducible_monic_degree :
    Reducible.Monic ∧ Reducible.natDegree = 3 := by
  constructor
  · rw [show Reducible = X ^ 3 + (X ^ 2 + X + 1) by
        simp only [Reducible]
        ring]
    apply monic_X_pow_add
    compute_degree
    norm_num
  · dsimp [Reducible]
    compute_degree
    all_goals norm_num

/-- The second example is a monic cubic. -/
theorem irreducible_monic_degree :
    locallyReducibleIrreducible.Monic ∧ locallyReducibleIrreducible.natDegree = 3 := by
  constructor
  · rw [show locallyReducibleIrreducible = X ^ 3 + (X ^ 2 + X - 1) by
        simp only [locallyReducibleIrreducible]
        ring]
    apply monic_X_pow_add
    compute_degree
    norm_num
  · dsimp [locallyReducibleIrreducible]
    compute_degree
    all_goals norm_num

/-- The first cubic has the explicit factorization
`(X + 1)(X² + 1)`. -/
theorem Reducible_factorization :
    Reducible = (X + 1) * (X ^ 2 + 1) := by
  simp [Reducible]
  ring

/-- Consequently the first cubic is reducible. -/
theorem Reducible_not_irreducible :
    ¬ Irreducible Reducible := by
  intro hirr
  rw [Reducible_factorization] at hirr
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · have hdeg := natDegree_eq_zero_of_isUnit h
    have hnat : (X + 1 : ℚ_[5][X]).natDegree = 1 := by
      compute_degree
      norm_num
    omega
  · have hdeg := natDegree_eq_zero_of_isUnit h
    have hnat : (X ^ 2 + 1 : ℚ_[5][X]).natDegree = 2 := by
      compute_degree
      norm_num
    omega

private def IrreduciblePadicInt : ℤ_[5][X] :=
  X ^ 3 + X ^ 2 + X - 1

private theorem irreducible_int_monic :
    IrreduciblePadicInt.Monic := by
  rw [show IrreduciblePadicInt =
      X ^ 3 + (X ^ 2 + X - 1) by
      simp only [IrreduciblePadicInt]
      ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

private theorem Irreducible_zmod_five :
    Irreducible
      (IrreduciblePadicInt.map (PadicInt.toZMod : ℤ_[5] →+* ZMod 5)) := by
  let f : (ZMod 5)[X] := X ^ 3 + X ^ 2 + X - 1
  have hf :
      IrreduciblePadicInt.map (PadicInt.toZMod : ℤ_[5] →+* ZMod 5) = f := by
    simp [IrreduciblePadicInt, f]
  rw [hf]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : f.natDegree = 3 := by
      dsimp [f]
      compute_degree
      all_goals norm_num
    simp [hdeg]
  · intro x
    fin_cases x <;> norm_num [f, IsRoot.def] <;> decide

private theorem Irreducible_padicInt :
    Irreducible IrreduciblePadicInt := by
  apply Monic.irreducible_of_irreducible_map
    (PadicInt.toZMod : ℤ_[5] →+* ZMod 5) IrreduciblePadicInt
  · exact irreducible_int_monic
  · exact Irreducible_zmod_five

/-- The second cubic is irreducible over `ℚ_[5]`, by irreducibility of its
reduction modulo `5`. -/
theorem Irreducible_irreducible :
    Irreducible locallyReducibleIrreducible := by
  have hmap : Irreducible
      (IrreduciblePadicInt.map (algebraMap ℤ_[5] ℚ_[5])) :=
    (irreducible_int_monic.irreducible_iff_irreducible_map_fraction_map).1
      Irreducible_padicInt
  simpa [locallyReducibleIrreducible, IrreduciblePadicInt] using hmap

/-- The coefficient norms of the two cubics agree at every index.  This is
the data defining their common Newton polygon. -/
theorem coefficient_norms_eq (n : ℕ) :
    ‖Reducible.coeff n‖ = ‖locallyReducibleIrreducible.coeff n‖ := by
  by_cases hn0 : n = 0
  · subst n
    norm_num [Reducible, locallyReducibleIrreducible, coeff_add, coeff_sub]
  by_cases hn1 : n = 1
  · subst n
    norm_num [Reducible, locallyReducibleIrreducible, coeff_add, coeff_sub,
      coeff_X, coeff_one]
  by_cases hn2 : n = 2
  · subst n
    norm_num [Reducible, locallyReducibleIrreducible, coeff_add, coeff_sub,
      coeff_X, coeff_one]
  by_cases hn3 : n = 3
  · subst n
    norm_num [Reducible, locallyReducibleIrreducible, coeff_add, coeff_sub,
      coeff_X, coeff_one]
  have hn4 : 4 ≤ n := by omega
  have hirrDegree : locallyReducibleIrreducible.natDegree = 3 := by
    exact irreducible_monic_degree.2
  have hredDegree : Reducible.natDegree = 3 := by
    exact reducible_monic_degree.2
  have hirrCoeff : locallyReducibleIrreducible.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hredCoeff : Reducible.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hirrCoeff, hredCoeff]

end

end Submission.NumberTheory.Milne
