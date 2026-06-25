import Mathlib
import Towers.NumberTheory.Discriminant.PolynomialExamples

/-!
# Milne, Algebraic Number Theory, Exercise 6-1

The elementary polynomial, real-root, discriminant, and unit computations from the exercise.
The later assertions about the full ring of integers, prime ideals, and the class group require the
number-field argument that follows these computations in Milne's solution.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- The cubic polynomial in Exercise 6-1. -/
noncomputable def exerciseSixPolynomial (R : Type*) [Ring R] : R[X] :=
  X ^ 3 - 3 * X + 1

/-- The polynomial in Exercise 6-1 is irreducible over `ℚ`. -/
theorem exercise_polynomial_irreducible :
    Irreducible (exerciseSixPolynomial ℚ) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (exerciseSixPolynomial ℚ).natDegree = 3 := by
      rw [show exerciseSixPolynomial ℚ = X ^ 3 + (-3 * X + 1) by
        simp only [exerciseSixPolynomial]
        ring]
      exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
        compute_degree
        norm_num)).natDegree_eq
    simp [hnat]
  · intro x hx
    let f : ℤ[X] := exerciseSixPolynomial ℤ
    have hf : f.Monic := by
      rw [show f = X ^ 3 + (-3 * X + 1) by
        simp only [f, exerciseSixPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    have hroot : Polynomial.aeval x f = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      simpa [f, exerciseSixPolynomial, IsRoot.def, aeval_def] using hx
    obtain ⟨z, hxz, hz⟩ := exists_integer_of_is_root_of_monic hf hroot
    have hzunit : IsUnit z := by
      rw [isUnit_iff_dvd_one]
      simpa [f, exerciseSixPolynomial] using hz
    rcases Int.isUnit_eq_one_or hzunit with hz | hz
    · subst z
      have : x = 1 := by simpa using hxz
      subst x
      norm_num [exerciseSixPolynomial, IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow] at hx
    · subst z
      have : x = -1 := by simpa using hxz
      subst x
      norm_num [exerciseSixPolynomial, IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow] at hx

/-- The polynomial in Exercise 6-1 has a real root in each of the three displayed disjoint
intervals. In particular it has three distinct real roots. -/
theorem exercise_six_roots :
    ∃ a b c : ℝ,
      a ∈ Set.Icc (-2 : ℝ) (-1) ∧
      b ∈ Set.Icc (0 : ℝ) 1 ∧
      c ∈ Set.Icc (1 : ℝ) 2 ∧
      (exerciseSixPolynomial ℝ).IsRoot a ∧
      (exerciseSixPolynomial ℝ).IsRoot b ∧
      (exerciseSixPolynomial ℝ).IsRoot c ∧
      a < b ∧ b < c := by
  let g : ℝ → ℝ := fun x => x ^ 3 - 3 * x + 1
  have hg : Continuous g := by
    fun_prop
  have haSigns : g (-2) ≤ 0 ∧ 0 ≤ g (-1) := by
    norm_num [g]
  have hbSigns : 0 ≤ g 0 ∧ g 1 ≤ 0 := by
    norm_num [g]
  have hcSigns : g 1 ≤ 0 ∧ 0 ≤ g 2 := by
    norm_num [g]
  obtain ⟨a, haIcc, ha⟩ := (intermediate_value_Icc
    (f := g) (a := (-2 : ℝ)) (b := -1) (by norm_num) hg.continuousOn)
    (show 0 ∈ Set.Icc (g (-2)) (g (-1)) by exact haSigns)
  obtain ⟨b, hbIcc, hb⟩ := (intermediate_value_Icc'
    (f := g) (a := (0 : ℝ)) (b := 1) (by norm_num) hg.continuousOn)
    (show 0 ∈ Set.Icc (g 1) (g 0) by exact ⟨hbSigns.2, hbSigns.1⟩)
  obtain ⟨c, hcIcc, hc⟩ := (intermediate_value_Icc
    (f := g) (a := (1 : ℝ)) (b := 2) (by norm_num) hg.continuousOn)
    (show 0 ∈ Set.Icc (g 1) (g 2) by exact hcSigns)
  refine ⟨a, b, c, haIcc, hbIcc, hcIcc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [exerciseSixPolynomial, IsRoot.def, g] using ha
  · simpa [exerciseSixPolynomial, IsRoot.def, g] using hb
  · simpa [exerciseSixPolynomial, IsRoot.def, g] using hc
  · have haNeg : a < 0 := lt_of_le_of_lt haIcc.2 (by norm_num)
    exact haNeg.trans_le hbIcc.1
  · have hbLe : b ≤ 1 := hbIcc.2
    have hcPos : 1 < c := by
      apply lt_of_le_of_ne hcIcc.1
      intro h
      subst c
      norm_num [g] at hc
    exact lt_of_le_of_lt hbLe hcPos

/-- Equivalently, the cubic has exactly three distinct real roots. -/
theorem exercise_six_real :
    (exerciseSixPolynomial ℝ).roots.toFinset.card = 3 := by
  classical
  obtain ⟨a, b, c, _, _, _, ha, hb, hc, hab, hbc⟩ :=
    exercise_six_roots
  let p : ℝ[X] := exerciseSixPolynomial ℝ
  have hpdeg : p.natDegree = 3 := by
    rw [show p = X ^ 3 + (-3 * X + 1) by
      simp only [p, exerciseSixPolynomial]
      ring]
    exact ((isMonicOfDegree_X_pow ℝ 3).add_right (by
      compute_degree
      norm_num)).natDegree_eq
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp, natDegree_zero] at hpdeg
    norm_num at hpdeg
  have haMem : a ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hp0]
    exact ha
  have hbMem : b ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hp0]
    exact hb
  have hcMem : c ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hp0]
    exact hc
  have hsub : ({a, b, c} : Finset ℝ) ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haMem
    · exact hbMem
    · exact hcMem
  have hthree : ({a, b, c} : Finset ℝ).card = 3 := by
    simp [hab.ne, hbc.ne, (hab.trans hbc).ne]
  apply le_antisymm
  · calc
      p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
      _ = 3 := hpdeg
  · rw [← hthree]
    exact Finset.card_le_card hsub

/-- The order discriminant computed in Exercise 6-1 is `81`. -/
theorem exercise_polynomial_discr :
    discr (exerciseSixPolynomial ℤ) = 81 := by
  simpa [exerciseSixPolynomial, sub_eq_add_neg] using
    (discr_cube_b (-3 : ℤ) (1 : ℤ))

section UnitIdentities

variable {R : Type*} [CommRing R] (α : R)

/-- A root of `X³ - 3X + 1` is a unit, with inverse `3 - α²`. -/
theorem exercise_six_one (hα : α ^ 3 - 3 * α + 1 = 0) : IsUnit α := by
  apply IsUnit.of_mul_eq_one (b := 3 - α ^ 2)
  linear_combination -hα

/-- If `α` is a root, then `α + 2` is a unit, with inverse `(α - 1)²`. -/
theorem exercise_six_unit (hα : α ^ 3 - 3 * α + 1 = 0) :
    IsUnit (α + 2) := by
  apply IsUnit.of_mul_eq_one (b := (α - 1) ^ 2)
  linear_combination hα

/-- The identity `(α + 1)³ = 3α(α + 2)` from Exercise 6-1. -/
theorem exercise_six_cube (hα : α ^ 3 - 3 * α + 1 = 0) :
    (α + 1) ^ 3 = 3 * α * (α + 2) := by
  linear_combination hα

end UnitIdentities

end Towers.NumberTheory.Milne
