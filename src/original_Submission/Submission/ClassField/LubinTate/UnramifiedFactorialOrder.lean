import Submission.ClassField.LubinTate.UnramifiedFrobeniusBase

/-! # Order reflection for canonical factorial unramified levels -/

namespace Submission.CField.LTate

noncomputable section

open Submission.CField.LBrauer

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Because the degree of level `r` is `(r+2)!`, inclusion of two canonical
factorial levels reflects the order of their indices. -/
theorem canonical_factorial_subalgebra
    {r s : ℕ}
    (h : (unramifiedFactorialLevel K r).toIntermediateField.toSubalgebra ≤
      (unramifiedFactorialLevel K s).toIntermediateField.toSubalgebra) :
    r ≤ s := by
  have hfield :
      (unramifiedFactorialLevel K r).toIntermediateField ≤
        (unramifiedFactorialLevel K s).toIntermediateField := h
  have hdegree : invariantLevelDegree r ≤
      invariantLevelDegree s := by
    rw [← factorial_level_finrank K r,
      ← factorial_level_finrank K s]
    exact IntermediateField.finrank_le_of_le_right hfield
  by_contra hrs
  have hsr : s < r := Nat.lt_of_not_ge hrs
  have hfac : Nat.factorial (s + 2) < Nat.factorial (r + 2) :=
    Nat.factorial_lt_of_lt (by omega) (by omega)
  change Nat.factorial (r + 2) ≤ Nat.factorial (s + 2) at hdegree
  omega

end

end Submission.CField.LTate
