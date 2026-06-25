import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Milne, Chapter 2, Theorem 2.2

The fundamental theorem of symmetric polynomials.
-/

namespace Submission.NumberTheory.Milne

open MvPolynomial

/-- Milne, Theorem 2.2: every symmetric polynomial in `r` variables is a
polynomial in the first `r` elementary symmetric polynomials. -/
theorem aeval_esymm_symmetric
    (A : Type*) [CommRing A] (r : ℕ)
    (P : MvPolynomial (Fin r) A) (hP : P.IsSymmetric) :
    ∃ Q : MvPolynomial (Fin r) A,
      MvPolynomial.aeval
        (fun i : Fin r ↦ MvPolynomial.esymm (Fin r) A (i + 1)) Q = P := by
  let p : MvPolynomial.symmetricSubalgebra (Fin r) A := ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ :=
    MvPolynomial.esymmAlgHom_fin_surjective
      (m := r) (n := r) A le_rfl p
  refine ⟨Q, ?_⟩
  simpa [p, MvPolynomial.esymmAlgHom_apply] using
    congrArg Subtype.val hQ

end Submission.NumberTheory.Milne
