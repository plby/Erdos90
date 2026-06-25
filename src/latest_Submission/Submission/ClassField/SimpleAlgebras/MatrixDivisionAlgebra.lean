import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Milne, Class Field Theory, Theorem IV.1.17

The finite-dimensional form of the Wedderburn--Artin theorem follows from its
Artinian form because a finite algebra over a field is Artinian.
-/

namespace Submission.CField.SAlgebr

universe u v

/-- **Theorem IV.1.17.** Every finite-dimensional simple `k`-algebra is a
matrix algebra over a finite-dimensional division `k`-algebra. -/
theorem alg_matrix_division
    (k : Type u) (A : Type v)
    [Field k] [Ring A] [Algebra k A]
    [Module.Finite k A] [IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type v)
      (_ : DivisionRing D) (_ : Algebra k D)
      (_ : Module.Finite k D),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A

end Submission.CField.SAlgebr
