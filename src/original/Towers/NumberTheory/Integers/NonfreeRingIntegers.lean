import Mathlib.NumberTheory.NumberField.Basic

/-!
# Nonfree relative rings of integers

Milne, Remark 2.31(b), notes without proof that there are finite extensions
of number fields `L / K` for which `𝓞 L` is not a free `𝓞 K`-module.  This
file records the literal existence statement as a proposition.  No axiom is
introduced.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField

universe u

/-- **Milne, Remark 2.31(b).** There exists a finite extension of number
fields whose relative ring of integers is not free over the base ring of
integers.  The source supplies no construction or proof. -/
def NonfreeIntegersTheorem : Prop :=
  ∃ (K L : Type u) (fieldK : Field K) (fieldL : Field L),
    letI : Field K := fieldK
    letI : Field L := fieldL
    ∃ (numberFieldK : NumberField K) (numberFieldL : NumberField L),
      letI : NumberField K := numberFieldK
      letI : NumberField L := numberFieldL
      ∃ algebraKL : Algebra K L,
        letI : Algebra K L := algebraKL
        ∃ tower : IsScalarTower ℚ K L,
          letI : IsScalarTower ℚ K L := tower
          ∃ finite : FiniteDimensional K L,
            letI : FiniteDimensional K L := finite
            ¬ Module.Free (𝓞 K) (𝓞 L)

end Towers.NumberTheory.Milne
