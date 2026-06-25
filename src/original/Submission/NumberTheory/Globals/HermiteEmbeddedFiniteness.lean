import Submission.NumberTheory.Globals.UnramifiedExtensionFiniteness

/-!
# Milne, Chapter 8, Theorem 8.43: embedded number fields

Hermite's theorem is restated using the `EmbeddedNumberField` representation
used by the Chapter 8 finiteness arguments.  The canonical specialization to
subfields of an algebraic closure of `ℚ` gives a single ambient field in which
to represent all number fields.
-/

namespace Submission.NumberTheory.Milne

open NumberField
open scoped IntermediateField

universe u

/-- Hermite's Theorem 8.43 in the `EmbeddedNumberField` representation:
inside any fixed characteristic-zero ambient field, only finitely many
embedded number fields have a prescribed signed discriminant. -/
theorem embedded_fields_discriminant
    (A : Type u) [Field A] [CharZero A] (d : ℤ) :
    {K : EmbeddedNumberField A |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      discr K = d}.Finite :=
  number_fields_discriminant A d

/-- In a fixed algebraic closure of `ℚ`, the embedded copies of number fields
with prescribed signed discriminant form a finite set. -/
theorem algebraic_fields_discriminant (d : ℤ) :
    {K : EmbeddedNumberField (AlgebraicClosure ℚ) |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      discr K = d}.Finite :=
  embedded_fields_discriminant (AlgebraicClosure ℚ) d

end Submission.NumberTheory.Milne
