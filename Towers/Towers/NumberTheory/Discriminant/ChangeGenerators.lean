import Mathlib

/-!
# Milne, Algebraic Number Theory, Lemma 2.23

The discriminant of a family transformed by a coefficient matrix is multiplied by the
square of that matrix's determinant.
-/

namespace Towers.NumberTheory.Milne

open scoped Matrix

/-- If `γ j = ∑ i, a j i • β i`, then the discriminant of `γ` is the discriminant of
`β` multiplied by `det(a)²`. This is Lemma 2.23. -/
theorem discr_linear_combination
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] [DecidableEq ι]
    (β γ : ι → B) (a : Matrix ι ι A)
    (hγ : ∀ j, γ j = ∑ i, algebraMap A B (a j i) * β i) :
    Algebra.discr A γ = a.det ^ 2 * Algebra.discr A β := by
  have hγ' : γ = a.map (algebraMap A B) *ᵥ β := by
    funext j
    simpa [Matrix.mulVec] using hγ j
  rw [hγ', Algebra.discr_of_matrix_mulVec]

end Towers.NumberTheory.Milne
