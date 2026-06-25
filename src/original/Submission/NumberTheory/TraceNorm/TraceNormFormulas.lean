import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

/-!
# Milne, Chapter 2, Propositions 2.19 and 2.20

Trace and norm as sums and products of roots or embeddings.
-/

namespace Submission.NumberTheory.Milne

open scoped IntermediateField

/-- Milne, Proposition 2.19: trace and norm are respectively the sum and
product of the roots of the minimal polynomial, counted with relative-degree
multiplicity. -/
theorem trace_norm_roots
    (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [FiniteDimensional K L]
    (x : L) (hsplit : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.trace K L x) =
        Module.finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum ∧
      algebraMap K F (Algebra.norm K x) =
        ((minpoly K x).aroots F).prod ^ Module.finrank K⟮x⟯ L := by
  exact ⟨trace_eq_sum_roots hsplit,
    Algebra.norm_eq_prod_roots F hsplit⟩

/-- Milne, Proposition 2.20: for a finite separable extension, trace and norm
are the sum and product over all embeddings into an algebraically closed
overfield.  This also records Aside 2.22. -/
theorem trace_norm_embeddings
    (K L E : Type*) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed E] (x : L) :
    algebraMap K E (Algebra.trace K L x) =
        ∑ σ : L →ₐ[K] E, σ x ∧
      algebraMap K E (Algebra.norm K x) =
        ∏ σ : L →ₐ[K] E, σ x := by
  exact ⟨trace_eq_sum_embeddings E,
    Algebra.norm_eq_prod_embeddings K E x⟩

end Submission.NumberTheory.Milne
