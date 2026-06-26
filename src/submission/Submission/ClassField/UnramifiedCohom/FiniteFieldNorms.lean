import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Milne, Class Field Theory, Lemma III.1.4: finite-field norms

The all-degree Tate-cohomology formulation of Lemma III.1.4 requires a
uniform integer-indexed Tate-cohomology theory, which is not currently
available in Mathlib.  This file records the exact norm-surjectivity
consequence used in the proof of Proposition III.1.2.
-/

namespace Submission.CField.UCohom

variable (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l]

/-- **Lemma III.1.4, norm-surjectivity assertion.** The norm on unit groups
of a finite extension of finite fields is surjective. -/
theorem units_norm_surjective :
    Function.Surjective (Units.map <| Algebra.norm k (S := l)) :=
  FiniteField.unitsMap_norm_surjective k l

/-- The field norm of a finite extension of finite fields is surjective. -/
theorem field_norm_surjective :
    Function.Surjective (Algebra.norm k (S := l)) :=
  FiniteField.norm_surjective k l

end Submission.CField.UCohom
