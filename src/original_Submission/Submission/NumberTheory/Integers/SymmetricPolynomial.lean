import Mathlib

/-!
# Milne, Algebraic Number Theory, Example 2.10(c)

The multivariable polynomial ring is integral over its symmetric subring. Consequently, over a
field, it is the integral closure of the symmetric subring in its fraction field.
-/

namespace Submission.NumberTheory.Milne

open MvPolynomial

noncomputable section

@[implicit_reducible] private def permRenameAction (R σ : Type*) [CommRing R] :
    MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ R) where
  smul e p := rename e p
  one_smul p := rename_id_apply p
  mul_smul e f p := by
    change rename (e * f) p = rename e (rename f p)
    rw [rename_rename]
    congr 1
  smul_zero e := map_zero (rename e)
  smul_add e p q := map_add (rename e) p q
  smul_one e := map_one (rename e)
  smul_mul e p q := map_mul (rename e) p q

/-- Every polynomial is integral over the subring of symmetric polynomials. The annihilating
polynomial is the product of `X - e • p` over all permutations `e` of the variables. -/
theorem mv_integral_symmetric
    (R σ : Type*) [CommRing R] [Finite σ] :
    Algebra.IsIntegral (symmetricSubalgebra σ R) (MvPolynomial σ R) := by
  letI : MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ R) := permRenameAction R σ
  letI : Algebra.IsInvariant (symmetricSubalgebra σ R) (MvPolynomial σ R) (Equiv.Perm σ) :=
    ⟨fun p hp ↦ ⟨⟨p, hp⟩, rfl⟩⟩
  exact Algebra.IsInvariant.isIntegral
    (symmetricSubalgebra σ R) (MvPolynomial σ R) (Equiv.Perm σ)

/-- Over a field, the polynomial ring is the integral closure of its symmetric subring in the
polynomial ring's fraction field. -/
theorem mv_symmetric_subalgebra
    (k σ : Type*) [Field k] [Finite σ] :
    IsIntegralClosure (MvPolynomial σ k) (symmetricSubalgebra σ k)
      (FractionRing (MvPolynomial σ k)) := by
  letI : Algebra.IsIntegral (symmetricSubalgebra σ k) (MvPolynomial σ k) :=
    mv_integral_symmetric k σ
  infer_instance

end

end Submission.NumberTheory.Milne
