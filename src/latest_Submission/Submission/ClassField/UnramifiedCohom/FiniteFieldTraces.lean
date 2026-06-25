import Mathlib.FieldTheory.Finite.Trace
import Submission.ClassField.CohomologyOps.AdditiveRepresentation

/-!
# Milne, Class Field Theory, Lemma III.1.5: finite-field traces

The positive-degree cohomology of the additive Galois module of a finite
field extension vanishes, and the field trace is surjective.  The uniform
all-degree Tate-cohomology formulation is not included because Mathlib does
not currently provide an integer-indexed Tate-cohomology theory.
-/

namespace Submission.CField.UCohom

open CategoryTheory

universe u

variable (k l : Type u) [Field k] [Field l] [Algebra k l] [Finite l]

/-- **Lemma III.1.5, positive-degree assertion.** Positive-degree group
cohomology of the additive Galois module of a finite extension of finite
fields vanishes. -/
theorem cohomology_additive_extension
    (r : ℕ) (hr : 0 < r) :
    Limits.IsZero
      (groupCohomology
        (COps.additiveGaloisRepresentation k l) r) :=
  COps.cohomology_additive_representation
    k l r hr

/-- **Lemma III.1.5, trace-surjectivity assertion.** The trace of a finite
extension of finite fields is surjective. -/
theorem field_trace_surjective :
    Function.Surjective (Algebra.trace k l) :=
  Algebra.trace_surjective k l

end Submission.CField.UCohom
