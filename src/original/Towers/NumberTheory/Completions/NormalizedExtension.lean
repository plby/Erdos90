import Towers.NumberTheory.Locals.CompleteDiscreteExtension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional


/-!
# Milne, Chapter 8, Lemma 8.6

For a finite extension of a complete nonarchimedean field, the normalized
value on the extension is the `n`th power of the uniquely extended absolute
value, where `n` is the extension degree.  It is also the absolute value of
the field norm.  The three archimedean extension types are recorded
separately at the end of the file.
-/

namespace Towers.NumberTheory.Milne

open Module

noncomputable section

variable (K L : Type*) [NontriviallyNormedField K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsUltrametricDist K] [CompleteSpace K]
  [FiniteDimensional K L]

/-- The normalized value attached to the unique extension of the absolute
value from `K` to `L`. -/
def normalizedExtensionValue (x : L) : ℝ :=
  completeAbsoluteValue K L x ^ finrank K L

omit [FiniteDimensional K L] in
/-- Milne's Lemma 8.6: on the base field, normalized values are raised to the
extension degree. -/
@[simp]
theorem normalized_value_algebra (x : K) :
    normalizedExtensionValue K L (algebraMap K L x) =
      ‖x‖ ^ finrank K L := by
  rw [normalizedExtensionValue, complete_absolute_algebra]

/-- The normalized value is the absolute value of the algebra norm. -/
theorem normalized_extension_norm (x : L) :
    normalizedExtensionValue K L x = ‖Algebra.norm K x‖ := by
  rw [normalizedExtensionValue,
    complete_extension_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg (Algebra.norm K x))]
  have hn : (finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast finrank_pos.ne'
  field_simp
  rw [Real.rpow_one]

end

section Archimedean

/-- The real-to-real archimedean case of Milne's Lemma 8.6. -/
theorem normalized_real_finrank (x : ℝ) :
    ‖x‖ = ‖x‖ ^ finrank ℝ ℝ := by
  simp

/-- The real-to-complex archimedean case of Milne's Lemma 8.6.  The
normalized value on `ℂ` is the square of its usual absolute value. -/
theorem normalized_complex_real (z : ℂ) :
    Complex.normSq z = ‖z‖ ^ finrank ℝ ℂ := by
  rw [Complex.finrank_real_complex, Complex.normSq_eq_norm_sq]

/-- The complex-to-complex archimedean case of Milne's Lemma 8.6. -/
theorem normalized_complex_finrank (z : ℂ) :
    Complex.normSq z = Complex.normSq z ^ finrank ℂ ℂ := by
  simp

end Archimedean

end Towers.NumberTheory.Milne
