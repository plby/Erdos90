import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Chapter IV, Section 5, Theorem 5.4

This is the finite-dimensional algebra form of the Artin-Wedderburn theorem,
already available in Mathlib.
-/

namespace Submission.CField.BDim

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSemisimpleRing A] [Module.Finite k A]

/-- Milne, Theorem IV.5.4, with each simple factor displayed as a full matrix
algebra over a finite-dimensional division algebra. -/
theorem semisimple_matrix_division :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ)
      (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra k (D i))
      (_ : ∀ i, Module.Finite k (D i)),
      (∀ i, NeZero (d i)) ∧
        Nonempty (A ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k A

end Submission.CField.BDim
