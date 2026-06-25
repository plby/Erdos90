import Towers.ClassField.HilbertSymbols.QuadraticHilbert

/-!
# Milne, Class Field Theory, Proposition III.4.1: pairing-theoretic core

Milne deduces Proposition III.4.1 from two properties of the Hilbert symbol:
it detects norms from Kummer extensions, and its right kernel is trivial.
The first theorem below records exactly that implication abstractly. The
second specializes the same argument to the elementary quadratic conic from
the preceding special case.
-/

namespace Towers.CField.HSymbol

universe u v

/-- An element of a monoid is an `n`th power. -/
def IsNthPower {A : Type u} [Monoid A] (n : ℕ) (a : A) : Prop :=
  ∃ x : A, x ^ n = a

/-- **Proposition III.4.1, abstract final step.** If a pairing detects the
relevant norm condition and has trivial right kernel modulo `n`th powers,
then an element which is a norm for every parameter is an `n`th power. -/
theorem nth_forall_nondegenerate
    {A : Type u} [Monoid A] {C : Type v} [One C]
    (n : ℕ) (pairing : A → A → C) (IsNormFrom : A → A → Prop)
    (norm_iff : ∀ a b, IsNormFrom a b ↔ pairing a b = 1)
    (right_nondegenerate : ∀ b,
      (∀ a, pairing a b = 1) → IsNthPower n b)
    {b : A} (hNorm : ∀ a, IsNormFrom a b) :
    IsNthPower n b := by
  apply right_nondegenerate b
  intro a
  exact (norm_iff a b).mp (hNorm a)

/-- The square-coefficient branch of Milne's quadratic conic argument is
automatic, independently of the second coefficient. -/
theorem nontrivial_conic_square
    {K : Type*} [Field K] {a b : K} (ha : IsSquare a) :
    NontrivialQuadraticConic a b := by
  rcases ha with ⟨c, rfl⟩
  refine ⟨1, 0, c, Or.inl one_ne_zero, ?_⟩
  ring

/-- **Proposition III.4.1, quadratic special-case conclusion.** Assuming the
right-nondegeneracy assertion for Milne's conic pairing, an element satisfying
every quadratic norm equation is a square. -/
theorem square_forall_nondegenerate
    {K : Type*} [Field K] {b : K}
    (right_nondegenerate :
      (∀ a, NontrivialQuadraticConic a b) → IsSquare b)
    (hNorm : ∀ a, QuadraticValue a b) :
    IsSquare b := by
  apply right_nondegenerate
  intro a
  by_cases ha : IsSquare a
  · exact nontrivial_conic_square ha
  · exact (nontrivial_conic_solution ha).mp
      (hNorm a)

end Towers.CField.HSymbol
