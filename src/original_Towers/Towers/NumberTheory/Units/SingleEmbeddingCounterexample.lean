import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Milne, Algebraic Number Theory, Exercise 5-1

Bounding only one chosen complex absolute value does not give a finite set of algebraic
integers of bounded degree.  Milne suggests the powers of `√2 - 1` as a counterexample.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable def exerciseFiveBase : ℝ :=
  Real.sqrt 2 - 1

noncomputable def exerciseFiveFamily (n : ℕ) : ℝ :=
  exerciseFiveBase ^ (n + 1)

theorem exercise_five_pos : 0 < exerciseFiveBase := by
  dsimp [exerciseFiveBase]
  exact sub_pos.mpr Real.one_lt_sqrt_two

theorem exercise_five_base : exerciseFiveBase < 1 := by
  dsimp [exerciseFiveBase]
  nlinarith [Real.sqrt_two_lt_three_halves]

theorem exercise_base_integral : IsIntegral ℤ exerciseFiveBase := by
  let p : ℤ[X] := X ^ 2 + C 2 * X + C (-1)
  refine ⟨p, ?_, ?_⟩
  · exact (isMonicOfDegree_add_add_two (2 : ℤ) (-1)).monic
  · rw [← aeval_def]
    simp only [p, map_add, map_mul, map_pow, aeval_X, map_ofNat, map_neg, map_one]
    dsimp [exerciseFiveBase]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith

theorem exercise_five_integral (n : ℕ) :
    IsIntegral ℤ (exerciseFiveFamily n) :=
  exercise_base_integral.pow (n + 1)

theorem exercise_five_abs (n : ℕ) :
    |exerciseFiveFamily n| < 1 := by
  rw [exerciseFiveFamily]
  rw [abs_of_pos (pow_pos exercise_five_pos _)]
  exact pow_lt_one₀ exercise_five_pos.le exercise_five_base (Nat.succ_ne_zero n)

theorem exercise_five_injective : Function.Injective exerciseFiveFamily := by
  exact (pow_right_strictAnti₀ exercise_five_pos exercise_five_base).injective.comp
    Nat.succ_injective

theorem exercise_five_minpoly (n : ℕ) :
    (minpoly ℚ (exerciseFiveFamily n)).natDegree ≤ 2 := by
  let α : ℝ := exerciseFiveBase
  let K : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {α}
  have hαZ : IsIntegral ℤ α := exercise_base_integral
  have hαQ : IsIntegral ℚ α := hαZ.tower_top
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hαQ
  let xK : K :=
    ⟨exerciseFiveFamily n, by
      change α ^ (n + 1) ∈ IntermediateField.adjoin ℚ {α}
      exact (IntermediateField.adjoin ℚ {α}).pow_mem
        (IntermediateField.subset_adjoin ℚ {α} (Set.mem_singleton α)) (n + 1)⟩
  let p : ℚ[X] := X ^ 2 + C 2 * X + C (-1)
  have hp : IsMonicOfDegree p 2 := isMonicOfDegree_add_add_two (2 : ℚ) (-1)
  have hαroot : Polynomial.aeval α p = 0 := by
    simp only [p, map_add, map_mul, map_pow, aeval_X, map_ofNat, map_neg, map_one]
    dsimp [α, exerciseFiveBase]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith
  have hαdegree : (minpoly ℚ α).natDegree ≤ 2 := by
    calc
      (minpoly ℚ α).natDegree ≤ p.natDegree :=
        natDegree_le_of_dvd (minpoly.dvd ℚ α hαroot) hp.monic.ne_zero
      _ = 2 := hp.natDegree_eq
  have hmin : minpoly ℚ (exerciseFiveFamily n) = minpoly ℚ xK := by
    simpa only [xK] using
      minpoly.algHom_eq (IntermediateField.val K) Subtype.val_injective xK
  calc
    (minpoly ℚ (exerciseFiveFamily n)).natDegree = (minpoly ℚ xK).natDegree := by
      rw [hmin]
    _ ≤ Module.finrank ℚ K := minpoly.natDegree_le xK
    _ = (minpoly ℚ α).natDegree := by
      simpa only [K] using IntermediateField.adjoin.finrank hαQ
    _ ≤ 2 := hαdegree

/-- **Milne, Exercise 5-1.** There are infinitely many real algebraic integers of degree
less than `3` and absolute value less than `1`. -/
theorem infinite_minpoly_abs :
    {x : ℝ | IsIntegral ℤ x ∧ (minpoly ℚ x).natDegree < 3 ∧ |x| < 1}.Infinite := by
  apply (Set.infinite_range_of_injective exercise_five_injective).mono
  rintro x ⟨n, rfl⟩
  exact ⟨exercise_five_integral n,
    Nat.lt_succ_iff.mpr (exercise_five_minpoly n),
    exercise_five_abs n⟩

end Towers.NumberTheory.Milne
