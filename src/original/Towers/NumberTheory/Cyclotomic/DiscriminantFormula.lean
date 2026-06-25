import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Milne, Algebraic Number Theory, Remark 6.6(c)

The exact discriminant formula for a general cyclotomic field.
-/

namespace Towers.NumberTheory.Milne

open NumberField

/-- **Milne, Remark 6.6(c).** The signed discriminant of the `n`th cyclotomic
field. -/
theorem cyclotomic_discriminant_formula (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    NumberField.discr K =
      (-1) ^ (n.totient / 2) *
        (n ^ n.totient /
          ∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1))) :=
  IsCyclotomicExtension.Rat.discr n K

/-- The absolute-value form of the cyclotomic discriminant formula. -/
theorem discriminant_abs_formula (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    (NumberField.discr K).natAbs =
      n ^ n.totient /
        ∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) :=
  IsCyclotomicExtension.Rat.natAbs_discr n K

/-- **Milne, Remark 6.6(b).** The roots of unity in the `n`th cyclotomic field
have order `n` for even `n`, and order `2n` for odd `n`. -/
theorem cyclotomic_torsion_order (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    NumberField.Units.torsionOrder K = if Even n then n else 2 * n :=
  IsCyclotomicExtension.Rat.torsionOrder_eq

end Towers.NumberTheory.Milne
