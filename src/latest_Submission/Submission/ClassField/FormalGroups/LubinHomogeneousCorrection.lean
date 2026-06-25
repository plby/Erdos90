import Submission.ClassField.FormalGroups.LubinCorrectionUnits

/-!
# Class Field Theory, Chapter I, Lemma 2.11: coefficientwise correction

The Frobenius congruence says that every coefficient of the intertwining
error is divisible by `pi`.  This file assembles those coefficientwise
divisibilities into a power-series factorization and proves that multiplying
the divisor by an additional unit still gives a unique quotient.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- Coefficientwise divisibility by `pi` is equivalent to a global scalar
factorization of a multivariable power series. -/
theorem smul_coeff_span (pi : R) (H : MvPowerSeries σ R)
    (hH : ∀ d, coeff d H ∈ Ideal.span {pi}) :
    ∃ P : MvPowerSeries σ R, pi • P = H := by
  choose c hc using fun d ↦ (Ideal.mem_span_singleton.mp (hH d))
  refine ⟨c, ?_⟩
  apply MvPowerSeries.ext
  intro d
  simpa only [coeff_smul] using (hc d).symm

/-- Dividing a coefficientwise-`pi`-divisible series by `u*pi`, where `u` is
a unit, has a unique solution over a domain.  This is the algebraic quotient
used for each homogeneous correction in Lemma 2.11. -/
theorem unique_coeff_span
    [IsDomain R] {pi : R} (hpi : pi ≠ 0) (u : Rˣ)
    (H : MvPowerSeries σ R)
    (hH : ∀ d, coeff d H ∈ Ideal.span {pi}) :
    ∃! Q : MvPowerSeries σ R, ((u : R) * pi) • Q = H := by
  obtain ⟨P, hP⟩ := smul_coeff_span pi H hH
  have hcandidate : ((u : R) * pi) • ((↑u⁻¹ : R) • P) = H := by
    rw [smul_smul]
    have hu : ((u : R) * pi) * (↑u⁻¹ : R) = pi := by
      rw [mul_assoc, mul_comm pi, ← mul_assoc]
      simp
    rw [hu, hP]
  refine ⟨(↑u⁻¹ : R) • P, hcandidate, ?_⟩
  intro Q hQ
  apply MvPowerSeries.ext
  intro d
  have hc := congrArg (coeff d) (hQ.trans hcandidate.symm)
  simp only [coeff_smul] at hc
  exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero u) hpi) hc

/-- The canonical quotient by a unit times `pi`. -/
noncomputable def correctionQuotient [IsDomain R] {pi : R}
    (hpi : pi ≠ 0) (u : Rˣ) (H : MvPowerSeries σ R)
    (hH : ∀ d, coeff d H ∈ Ideal.span {pi}) : MvPowerSeries σ R :=
  Classical.choose (unique_coeff_span hpi u H hH)

theorem correctionQuotient_spec [IsDomain R] {pi : R}
    (hpi : pi ≠ 0) (u : Rˣ) (H : MvPowerSeries σ R)
    (hH : ∀ d, coeff d H ∈ Ideal.span {pi}) :
    ((u : R) * pi) • correctionQuotient hpi u H hH = H :=
  (Classical.choose_spec
    (unique_coeff_span hpi u H hH)).1

/-- Division by a nonzero scalar preserves homogeneity. -/
theorem correction_quotient_homogeneous [IsDomain R] {pi : R}
    (hpi : pi ≠ 0) (u : Rˣ) (H : MvPowerSeries σ R)
    (hH : ∀ d, coeff d H ∈ Ideal.span {pi}) {n : ℕ}
    (hhom : H.IsHomogeneous n) :
    (correctionQuotient hpi u H hH).IsHomogeneous n := by
  intro d hd
  have hcoeff := congrArg (coeff d)
    (correctionQuotient_spec hpi u H hH)
  simp only [coeff_smul] at hcoeff
  apply hhom
  rw [← hcoeff]
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero u) hpi) hd

end

end Submission.CField.FGroups
