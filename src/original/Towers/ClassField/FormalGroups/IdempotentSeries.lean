import Towers.ClassField.FormalGroups.CompositionalInverse

/-!
# Class Field Theory, Chapter I, Remark 2.4(b)

Milne derives the identity axiom of a formal group law from its linear term
and associativity.  The essential unary statement is that a substitution-
idempotent series with invertible linear coefficient is the identity series.
-/

namespace Towers.CField.FGroups

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The power-series argument in Remark 2.4(b): if `f ∘ f = f` and the
linear coefficient of `f` is a unit, then `f = X`. -/
theorem x_subst {f : R⟦X⟧}
    (hf0 : f.constantCoeff = 0) (hf1 : IsUnit (coeff 1 f))
    (hidem : f.subst f = f) : f = X := by
  apply subst_injective_coeff hf1 hf0 constantCoeff_X
  rw [hidem]
  exact map_algebraMap_eq_subst_X (R := R) (S := R) f

/-- The form used for the linear term `f(X) = X +` terms of degree at least
two in Remark 2.4(b). -/
theorem x_subst_self {f : R⟦X⟧}
    (hf0 : f.constantCoeff = 0) (hf1 : coeff 1 f = 1)
    (hidem : f.subst f = f) : f = X := by
  apply x_subst hf0
  · rw [hf1]
    exact isUnit_one
  · exact hidem

end Towers.CField.FGroups
