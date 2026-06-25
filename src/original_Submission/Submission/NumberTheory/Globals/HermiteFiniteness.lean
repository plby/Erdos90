import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Milne, Chapter 8, Theorem 8.43 (Hermite)

Inside a fixed characteristic-zero ambient field, there are only finitely many
number fields whose absolute discriminant is bounded by a prescribed natural
number.  In particular this contains Milne's fixed-discriminant statement.
-/

namespace Submission.NumberTheory.Milne

open NumberField
open scoped IntermediateField

variable (A : Type*) [Field A] [CharZero A]

/-- Milne's Theorem 8.43, in Mathlib's stronger bounded-discriminant form. -/
theorem fields_discriminant_bounded (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ N}.Finite :=
  NumberField.finite_of_discr_bdd A N

/-- For a fixed integer discriminant, only finitely many number fields inside
the ambient field realize it. -/
theorem number_fields_discriminant (d : ℤ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      discr K = d}.Finite := by
  apply (fields_discriminant_bounded A d.natAbs).subset
  intro K hK
  letI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
  change discr K = d at hK
  simp [hK]

end Submission.NumberTheory.Milne
