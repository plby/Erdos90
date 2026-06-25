import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chapter VI, Section 4, Lemma 4.7: character orthogonality

The displayed formula in the source omits the necessary hypothesis `a ≠ 1`:
at the identity every character has value one, so the sum is the number of
characters.  The two declarations below record both cases exactly.

The analytic comparison of polar, Dirichlet, and natural densities, the
Euler-product logarithm estimate, Theorem 4.8, and the second inequality are
not currently available in Mathlib's analytic-number-theory library.
-/

namespace Towers.CField.DDensit

open scoped BigOperators

noncomputable section

variable {A : Type*} [CommGroup A] [Finite A]

local instance : Fintype (MulChar A ℂ) := Fintype.ofFinite _
local instance : DecidableEq A := Classical.decEq A

/-- **Lemma VI.4.7, nonidentity case.** The sum of all complex-valued
characters at a nonidentity element of a finite abelian group is zero. -/
theorem character_sum_zero {a : A} (ha : a ≠ 1) :
    ∑ χ : MulChar A ℂ, χ a = 0 := by
  obtain ⟨χ, hχ⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun _ ↦ rfl

/-- At the identity, the character sum is the number of characters rather
than zero. -/
theorem sum_characters_one :
    ∑ χ : MulChar A ℂ, χ 1 = (Fintype.card (MulChar A ℂ) : ℂ) := by
  simp

/-- Piecewise form of character orthogonality. -/
theorem sum_characters_eq (a : A) :
    ∑ χ : MulChar A ℂ, χ a =
      if a = 1 then (Fintype.card (MulChar A ℂ) : ℂ) else 0 := by
  classical
  by_cases ha : a = 1
  · subst a
    rw [if_pos rfl]
    exact sum_characters_one (A := A)
  · rw [if_neg ha]
    exact character_sum_zero (A := A) ha

end

end Towers.CField.DDensit
