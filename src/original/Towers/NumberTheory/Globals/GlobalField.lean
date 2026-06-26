import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Milne, Chapter 8: global fields

Milne begins the chapter by defining a global field to be either a number
field or a finite extension of a rational function field over a finite field.
The structure below packages the constant field and the required algebra
structure in the function-field case.
-/

namespace Towers.NumberTheory.Milne

noncomputable section

universe u

/-- A presentation of `K` as a one-variable function field over a finite
constant field. -/
structure FFPres (K : Type u) [Field K] where
  /-- The finite constant field. -/
  constants : Type u
  [constantsField : Field constants]
  [constantsFinite : Finite constants]
  [functionFieldAlgebra : Algebra (RatFunc constants) K]
  [finiteDimensional : FiniteDimensional (RatFunc constants) K]

namespace FFPres

attribute [instance] constantsField constantsFinite functionFieldAlgebra finiteDimensional

end FFPres

/-- Milne's definition: a global field is a number field or a function field
in one variable over a finite field. -/
def IsGlobalField (K : Type u) [Field K] : Prop :=
  NumberField K ∨ Nonempty (FFPres K)

/-- Every number field is a global field. -/
theorem global_field_number (K : Type u) [Field K] [NumberField K] :
    IsGlobalField K :=
  Or.inl inferInstance

/-- Every finite extension of `Fq(t)`, for `Fq` finite, is a global field. -/
theorem global_field_function
    (Fq K : Type u) [Field Fq] [Finite Fq] [Field K]
    [Algebra (RatFunc Fq) K] [FiniteDimensional (RatFunc Fq) K] :
    IsGlobalField K :=
  Or.inr ⟨{ constants := Fq }⟩

/-- The rational numbers are a global field. -/
theorem rat_global_field : IsGlobalField ℚ :=
  global_field_number ℚ

/-- The rational function field over a finite field is a global field. -/
theorem rat_func_global (Fq : Type u) [Field Fq] [Finite Fq] :
    IsGlobalField (RatFunc Fq) :=
  global_field_function Fq (RatFunc Fq)

end

end Towers.NumberTheory.Milne
