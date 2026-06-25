import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Milne, Algebraic Number Theory, Example 4.7

A cubic number field of negative discriminant has one complex place. If the absolute value of
its discriminant is at most `49`, Minkowski's bound forces its class number to be one.
-/

namespace Towers.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace
open scoped NumberField Real

variable (K : Type*) [Field K] [NumberField K]

/-- A cubic number field with negative discriminant has signature `(1, 1)`. -/
theorem discr_nr_complex
    (hdegree : finrank ℚ K = 3) (hdiscr : NumberField.discr K < 0) :
    nrComplexPlaces K = 1 := by
  have hcard := card_add_two_mul_card_eq_rank K
  have hcard3 : nrRealPlaces K + 2 * nrComplexPlaces K = 3 :=
    hcard.trans hdegree
  have hcomplex_le : nrComplexPlaces K ≤ 1 := by omega
  interval_cases hcomplex : nrComplexPlaces K
  · have hsign := NumberField.sign_discr (K := K)
    have hsign_neg : (NumberField.discr K).sign = -1 :=
      Int.sign_eq_neg_one_of_neg hdiscr
    rw [hsign_neg, hcomplex] at hsign
    norm_num at hsign
  · rfl

/-- The noncomputational first part of Example 4.7: a cubic field with negative discriminant
of absolute value at most `49` has principal ring of integers. -/
theorem discr_abs_49
    (hdegree : finrank ℚ K = 3) (hdiscr : NumberField.discr K < 0)
    (habs : (NumberField.discr K).natAbs ≤ 49) :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  have hcomplex := discr_nr_complex K hdegree hdiscr
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt (K := K)
  rw [hdegree, hcomplex]
  norm_num
  have habs_real : (|(NumberField.discr K : ℝ)| : ℝ) ≤ 49 := by
    calc
      |(NumberField.discr K : ℝ)| = ((|(NumberField.discr K)| : ℤ) : ℝ) :=
        Int.cast_abs.symm
      _ = ((NumberField.discr K).natAbs : ℝ) := by
        rw [Int.abs_eq_natAbs, Int.cast_natCast]
      _ ≤ 49 := by exact_mod_cast habs
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  nlinarith [sq_nonneg (Real.pi - 3.14)]

/-- Consequently, such a cubic field has class number one. -/
theorem cubic_abs_49
    (hdegree : finrank ℚ K = 3) (hdiscr : NumberField.discr K < 0)
    (habs : (NumberField.discr K).natAbs ≤ 49) :
    NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  exact discr_abs_49 K hdegree hdiscr habs

end Towers.NumberTheory.Milne
