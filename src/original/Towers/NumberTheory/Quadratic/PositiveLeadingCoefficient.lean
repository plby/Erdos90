import Towers.NumberTheory.Quadratic.ProperPrimitiveClasses

/-!
# A positive leading coefficient in a proper form class

For a nonsquare discriminant, every form in the corrected target of Theorem 4.29 is properly
equivalent to one with positive leading coefficient.  In the indefinite case the vector
`(-b, 2a)` has value `-aD`; after dividing its coordinates by their gcd it extends to the first
column of a matrix in `SL(2, Z)`.
-/

namespace Towers.NumberTheory.Milne

open scoped MatrixGroups

namespace BQForm

private theorem neg_b_two (Q : BQForm) :
    Q.eval (-Q.b) (2 * Q.a) = -Q.a * Q.discriminant := by
  simp only [eval, discriminant]
  ring

private theorem eval_mul (Q : BQForm) (x y g : ℤ) :
    Q.eval (x * g) (y * g) = g ^ 2 * Q.eval x y := by
  simp only [eval]
  ring

/-- A form in the corrected target of Theorem 4.29 with nonsquare discriminant has a properly
equivalent representative with positive leading coefficient. -/
theorem transform_proper_square
    (D : ℤ) (Q : BQForm)
    (hQ : ProperDiscriminant D Q) (hD : ¬ IsSquare D) :
    ∃ g : SL(2, ℤ), 0 < (Q.transform g).a := by
  by_cases hDneg : D < 0
  · refine ⟨1, ?_⟩
    rw [transform_one]
    exact (hQ.2.2 hDneg).1
  have hDne : D ≠ 0 := by
    intro h
    apply hD
    exact ⟨0, by simp [h]⟩
  have hDpos : 0 < D := lt_of_le_of_ne (le_of_not_gt hDneg) (Ne.symm hDne)
  have ha_ne : Q.a ≠ 0 := by
    intro ha
    apply hD
    refine ⟨Q.b, ?_⟩
    rw [← hQ.1]
    simp [discriminant, ha, pow_two]
  by_cases ha_pos : 0 < Q.a
  · refine ⟨1, ?_⟩
    rw [transform_one]
    exact ha_pos
  have ha_neg : Q.a < 0 := lt_of_le_of_ne (le_of_not_gt ha_pos) ha_ne
  let x : ℤ := -Q.b
  let y : ℤ := 2 * Q.a
  have hy_ne : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (by norm_num) ha_ne
  have hgcd_pos : 0 < Int.gcd x y :=
    Int.gcd_pos_of_ne_zero_right x hy_ne
  obtain ⟨x', y', hgcd, hx, hy⟩ := Int.exists_gcd_one hgcd_pos
  have hxy_coprime : IsCoprime x' y' :=
    Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  obtain ⟨g, hg0, hg1⟩ := hxy_coprime.exists_SL2_col 0
  refine ⟨g, ?_⟩
  have hvalue : 0 < Q.eval x y := by
    change 0 < Q.eval (-Q.b) (2 * Q.a)
    rw [neg_b_two]
    rw [hQ.1]
    exact mul_pos (neg_pos.mpr ha_neg) hDpos
  have hscaled : Q.eval x y = (Int.gcd x y : ℤ) ^ 2 * Q.eval x' y' := by
    calc
      Q.eval x y =
          Q.eval (x' * (Int.gcd x y : ℤ)) (y' * (Int.gcd x y : ℤ)) :=
        congrArg₂ Q.eval hx hy
      _ = (Int.gcd x y : ℤ) ^ 2 * Q.eval x' y' := eval_mul Q x' y' _
  have hgcd_sq_pos : 0 < (Int.gcd x y : ℤ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hgcd_pos)
  have hprimitive_value : 0 < Q.eval x' y' := by
    nlinarith
  simpa [transform, hg0, hg1, eval] using hprimitive_value

end BQForm

end Towers.NumberTheory.Milne
