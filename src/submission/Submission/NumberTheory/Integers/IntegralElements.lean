import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Milne, Chapter 2, Theorem 2.1

The elements of an algebra integral over the base ring form a subring.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Theorem 2.1: the integral elements are precisely the elements of
the integral-closure subring. -/
theorem elements_form_subring
    (A L : Type*) [CommRing A] [CommRing L] [Algebra A L] :
    ∃ S : Subring L, ∀ x : L, x ∈ S ↔ IsIntegral A x := by
  refine ⟨(integralClosure A L).toSubring, fun x ↦ ?_⟩
  change x ∈ integralClosure A L ↔ IsIntegral A x
  exact mem_integralClosure_iff A L

end Submission.NumberTheory.Milne
