import Towers.Group.Zassenhaus.Normalization

/-!
# Predecessor shifts of origin-compatible collection polynomials

A polynomial family known only after precomposition with successor does not
automa extend across natural input zero.  The exact missing datum is
the value of its successor witness at `-1`.  Package that compatibility
condition and the valid predecessor-shift adapter.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

/-- Every polynomial witness for the successor-precomposed family evaluates
at `-1` to the actual value of the original family at natural input zero. -/
def SuccessorPolynomialsOrigin
    (f : ℕ → ℤ) :
    Prop :=
  ∀ P : Polynomial ℚ,
    (∀ steps : ℕ, P.eval (steps : ℚ) = (f (steps + 1) : ℚ)) →
      P.eval (-1) = (f 0 : ℚ)

namespace IVMost

/-- Remove a successor precomposition when its polynomial witness is
compatible with the missing origin value. -/
lemma pred_match_origin
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hsucc :
      IVMost
        (fun steps : ℕ => f (steps + 1)) degreeBound)
    (horigin : SuccessorPolynomialsOrigin f) :
    IVMost f degreeBound := by
  rcases hsucc with ⟨P, hPdegree, hPeval⟩
  let shift : Polynomial ℚ := Polynomial.X - Polynomial.C 1
  refine ⟨P.comp shift, Polynomial.natDegree_comp_le.trans ?_, ?_⟩
  · have hshift : shift.natDegree ≤ 1 := by
      dsimp [shift]
      exact Polynomial.natDegree_X_sub_C_le 1
    calc
      P.natDegree * shift.natDegree ≤ P.natDegree * 1 :=
        Nat.mul_le_mul_left P.natDegree hshift
      _ = P.natDegree := Nat.mul_one _
      _ ≤ degreeBound := hPdegree
  · intro steps
    rw [Polynomial.eval_comp]
    cases steps with
    | zero =>
        simpa [shift] using horigin P hPeval
    | succ steps =>
        simpa [shift] using hPeval steps

end IVMost
end TCTex
end Towers
