import Submission.Group.Zassenhaus.Normalization

/-!
# Successor shifts of integer-valued collection polynomials

Precomposing an integer-valued polynomial on natural inputs with successor
preserves its degree bound. This is the small arithmetic adapter needed by
successor-skew symbolic collection schedules.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace IVMost

/-- Precomposition with `steps ↦ steps + 1` preserves the degree bound. -/
lemma succ
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound) :
    IVMost
      (fun steps : ℕ => f (steps + 1)) degreeBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  let shift : Polynomial ℚ := Polynomial.X + Polynomial.C 1
  refine ⟨P.comp shift, Polynomial.natDegree_comp_le.trans ?_, ?_⟩
  · have hshift : shift.natDegree ≤ 1 := by
      dsimp [shift]
      rw [Polynomial.natDegree_X_add_C]
    calc
      P.natDegree * shift.natDegree ≤ P.natDegree * 1 :=
        Nat.mul_le_mul_left P.natDegree hshift
      _ = P.natDegree := Nat.mul_one _
      _ ≤ degreeBound := hPdegree
  · intro steps
    rw [Polynomial.eval_comp,
      show shift.eval (steps : ℚ) = (steps : ℚ) + 1 by simp [shift]]
    simpa using hPeval (steps + 1)

end IVMost
end TCTex
end Submission
