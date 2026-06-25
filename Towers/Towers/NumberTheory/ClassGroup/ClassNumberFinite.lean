import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Milne, Algebraic Number Theory, Theorem 4.4

The class group of a number field is finite.  Mathlib constructs its canonical finite type
from the admissible archimedean absolute value.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField

/-- **Milne, Theorem 4.4.** The ideal class group of a number field is finite. -/
theorem classGroup_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) := by
  infer_instance

/-- The class number is the cardinality of the finite ideal class group. -/
theorem number_card_group
    (K : Type*) [Field K] [NumberField K] :
    NumberField.classNumber K = Fintype.card (ClassGroup (𝓞 K)) :=
  rfl

end Towers.NumberTheory.Milne
