import Mathlib

namespace Submission.NumberTheory

namespace GSchnei

/-- A complex number is rational when it is the image of an element of `ℚ`. -/
def IsRational (z : ℂ) : Prop := ∃ q : ℚ, (q : ℂ) = z

/-- A value of `alpha ^ beta`, allowing every choice of a logarithm of `alpha`. -/
def IPValue (alpha beta z : ℂ) : Prop :=
  ∃ w : ℂ, Complex.exp w = alpha ∧ Complex.exp (w * beta) = z

theorem principal_cpow_value {alpha beta : ℂ} (halpha : alpha ≠ 0) :
    IPValue alpha beta (alpha ^ beta) := by
  refine ⟨Complex.log alpha, Complex.exp_log halpha, ?_⟩
  rw [Complex.cpow_def_of_ne_zero halpha]

theorem IPValue.ne_zero {alpha beta z : ℂ} (hz : IPValue alpha beta z) :
    z ≠ 0 := by
  obtain ⟨w, -, rfl⟩ := hz
  exact Complex.exp_ne_zero _

/-- The full, branch-independent statement of Theorem 9. -/
def FullStatement : Prop :=
  ∀ alpha beta z : ℂ,
    IsAlgebraic ℚ alpha → IsAlgebraic ℚ beta →
    alpha ≠ 0 → alpha ≠ 1 → ¬IsRational beta →
    IPValue alpha beta z → Transcendental ℚ z

/-- The principal-branch consequence of Theorem 9, using Mathlib's `Complex.cpow`. -/
def PrincipalStatement : Prop :=
  ∀ alpha beta : ℂ,
    IsAlgebraic ℚ alpha → IsAlgebraic ℚ beta →
    alpha ≠ 0 → alpha ≠ 1 → ¬IsRational beta →
    Transcendental ℚ (alpha ^ beta)

theorem full_implies_principal : FullStatement → PrincipalStatement := by
  intro h alpha beta halpha hbeta halpha0 halpha1 hbetaRat
  exact h alpha beta (alpha ^ beta) halpha hbeta halpha0 halpha1 hbetaRat
    (principal_cpow_value halpha0)

end GSchnei

end Submission.NumberTheory
