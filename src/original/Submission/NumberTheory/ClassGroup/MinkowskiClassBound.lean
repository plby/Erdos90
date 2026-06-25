import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Milne, Algebraic Number Theory, Theorem 4.3

Every ideal class of a number field has an integral representative whose numerical norm is
at most the Minkowski bound.  Here `Ideal.absNorm` is the numerical norm and
`NumberField.InfinitePlace.nrComplexPlaces K` is Milne's number `s` of conjugate pairs of
nonreal embeddings.
-/

namespace Submission.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace Ideal Nat
open scoped nonZeroDivisors Real

/-- Milne's Minkowski constant
`(n! / n^n) * (4 / pi)^s`, for `n = [K : Q]` and `s` complex places. -/
noncomputable def milneMinkowskiConstant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) *
    (4 / Real.pi) ^ nrComplexPlaces K

/-- Milne's Minkowski bound `C_K * sqrt |Delta_K|`. -/
noncomputable def milneMinkowskiBound
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  milneMinkowskiConstant K * Real.sqrt |NumberField.discr K|

/-- The constant used by mathlib's class-number theorem is Milne's Minkowski bound. -/
theorem milne_minkowski
    (K : Type*) [Field K] [NumberField K] :
    milneMinkowskiBound K =
      (4 / Real.pi) ^ nrComplexPlaces K *
        ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |NumberField.discr K|) := by
  simp only [milneMinkowskiBound, milneMinkowskiConstant]
  ring

/-- Theorem 4.3, pointwise form: every ideal class contains a nonzero integral ideal of
numerical norm at most the Minkowski bound. -/
theorem integral_milne_minkowski
    {K : Type*} [Field K] [NumberField K] (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ milneMinkowskiBound K := by
  simpa only [milne_minkowski] using
    (NumberField.exists_ideal_in_class_of_norm_le C)

/-- Theorem 4.3 in representative-system form: one may choose, simultaneously for every
ideal class, an integral representative satisfying the Minkowski bound. -/
theorem representatives_milne_minkowski
    (K : Type*) [Field K] [NumberField K] :
    ∃ rep : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰,
      ∀ C, ClassGroup.mk0 (rep C) = C ∧
        Ideal.absNorm (rep C : Ideal (𝓞 K)) ≤ milneMinkowskiBound K := by
  choose rep hrep using
    (fun C : ClassGroup (𝓞 K) ↦
      integral_milne_minkowski C)
  exact ⟨rep, hrep⟩

end Submission.NumberTheory.Milne
