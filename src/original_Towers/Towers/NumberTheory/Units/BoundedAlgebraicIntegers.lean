import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Milne, Algebraic Number Theory, Proposition 5.5 (global form)

The existing fixed-number-field finiteness theorem is strengthened here to Milne's literal
statement: the ambient set consists of all complex algebraic integers, rather than the integers
of one fixed number field.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- **Milne, Proposition 5.5.** For fixed `m` and `M`, there are only finitely many complex
algebraic integers of degree at most `m` all of whose conjugates have norm less than `M`.

Here `IsConjRoot ℚ x y` says precisely that `x` and `y` have the same rational minimal
polynomial. Thus the last condition quantifies over all complex conjugates of `x`. -/
theorem degree_all_conjugates (m : ℕ) (M : ℝ) :
    {x : ℂ | IsIntegral ℤ x ∧ (minpoly ℚ x).natDegree ≤ m ∧
      ∀ y : ℂ, IsConjRoot ℚ x y → ‖y‖ < M}.Finite := by
  classical
  let C := Nat.ceil (max M 1 ^ m * m.choose (m / 2))
  refine (bUnion_roots_finite (algebraMap ℤ ℂ) m (Set.finite_Icc (-C : ℤ) C)).subset ?_
  rintro x ⟨hxi, hdegree, hconj⟩
  simp_rw [Set.mem_iUnion]
  have hxq : IsIntegral ℚ x := hxi.tower_top
  have hminpoly : minpoly ℚ x = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hxi
  refine ⟨minpoly ℤ x, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · rw [← (minpoly.monic hxi).natDegree_map (algebraMap ℤ ℚ), ← hminpoly]
    exact hdegree
  · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
    refine (Eq.trans_le ?_ <| coeff_bdd_of_roots_le (algebraMap ℚ ℂ)
      (minpoly.monic hxq) (IsAlgClosed.splits _) hdegree ?_ i).trans (Nat.le_ceil _)
    · rw [coeff_map, norm_algebraMap' ℂ, hminpoly, coeff_map, eq_intCast, Int.norm_cast_rat,
        Int.norm_eq_abs,
        Int.cast_abs]
    · intro z hz
      apply (hconj z ?_).le
      apply (isConjRoot_iff_aeval_eq_zero hxq).2
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots ((minpoly.monic hxq).map _).ne_zero).mp hz
  · exact Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hxi, minpoly.aeval ℤ x⟩

/-- Equivalent root-set presentation of Proposition 5.5. This is often convenient when applying
the result, because the complex roots of the rational minimal polynomial are displayed directly. -/
theorem integral_minpoly_roots (m : ℕ) (M : ℝ) :
    {x : ℂ | IsIntegral ℤ x ∧ (minpoly ℚ x).natDegree ≤ m ∧
      ∀ y ∈ (minpoly ℚ x).rootSet ℂ, ‖y‖ < M}.Finite := by
  refine (degree_all_conjugates m M).subset ?_
  rintro x ⟨hxi, hdegree, hroots⟩
  refine ⟨hxi, hdegree, fun y hy ↦ ?_⟩
  exact hroots y ((isConjRoot_iff_mem_minpoly_rootSet hxi.tower_top).mp hy)

end Towers.NumberTheory.Milne
