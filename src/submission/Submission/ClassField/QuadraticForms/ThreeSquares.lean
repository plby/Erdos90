import Mathlib.Tactic

/-!
# Chapter VIII, Section 6: the three-squares obstruction

Milne's Proposition 6.14 is the Gauss--Legendre three-squares theorem.  The converse direction
is not currently available in Mathlib.  This file proves the elementary obstruction direction:
no natural number of the form `4^a * (8*b + 7)` is a sum of three squares.
-/

namespace Submission.CField.QForms

/-- A natural number is a sum of three natural-number squares. -/
def SumThreeSquares (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2

/-- A square modulo eight is `0`, `1`, or `4`. -/
theorem square_mod_eight (x : ℕ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have hreduce : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by
    simpa using (Nat.pow_mod x 2 8)
  rw [hreduce]
  have hx : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : x % 8 <;> norm_num

/-- A sum of three squares is never congruent to seven modulo eight. -/
theorem squares_ne_seven (x y z : ℕ) :
    (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  rcases square_mod_eight x with hx | hx | hx <;>
    rcases square_mod_eight y with hy | hy | hy <;>
      rcases square_mod_eight z with hz | hz | hz <;> omega

/-- The immediate mod-eight obstruction to being a sum of three squares. -/
theorem squares_eight_seven {n : ℕ} (hn : n % 8 = 7) :
    ¬ SumThreeSquares n := by
  rintro ⟨x, y, z, rfl⟩
  exact squares_ne_seven x y z hn

/-- A square modulo four is zero or one. -/
theorem square_mod_four (x : ℕ) :
    x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hreduce : x ^ 2 % 4 = (x % 4) ^ 2 % 4 := by
    simpa using (Nat.pow_mod x 2 4)
  rw [hreduce]
  have hx : x % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : x % 4 <;> norm_num

/-- If four divides a sum of three squares, all three variables are even. -/
theorem even_variables_squares
    {x y z : ℕ} (hfour : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  have hsum : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hfour
  rcases square_mod_four x with hx | hx <;>
    rcases square_mod_four y with hy | hy <;>
      rcases square_mod_four z with hz | hz
  all_goals
    have hx0 : x ^ 2 % 4 = 0 := by omega
    have hy0 : y ^ 2 % 4 = 0 := by omega
    have hz0 : z ^ 2 % 4 = 0 := by omega
    have h4x : 4 ∣ x ^ 2 := Nat.dvd_iff_mod_eq_zero.mpr hx0
    have h4y : 4 ∣ y ^ 2 := Nat.dvd_iff_mod_eq_zero.mpr hy0
    have h4z : 4 ∣ z ^ 2 := Nat.dvd_iff_mod_eq_zero.mpr hz0
    exact ⟨Nat.prime_two.dvd_of_dvd_pow ((show 2 ∣ 4 from by norm_num).trans h4x),
      Nat.prime_two.dvd_of_dvd_pow ((show 2 ∣ 4 from by norm_num).trans h4y),
      Nat.prime_two.dvd_of_dvd_pow ((show 2 ∣ 4 from by norm_num).trans h4z)⟩

/-- Dividing a represented number by four preserves representation by three squares. -/
theorem squares_four_mul {n : ℕ} :
    SumThreeSquares (4 * n) → SumThreeSquares n := by
  rintro ⟨x, y, z, hxyz⟩
  have hfour : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [← hxyz]
    exact dvd_mul_right 4 n
  obtain ⟨hx, hy, hz⟩ := even_variables_squares hfour
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  obtain ⟨z', rfl⟩ := hz
  refine ⟨x', y', z', ?_⟩
  nlinarith

/-- Repeatedly divide a represented number by a power of four. -/
theorem sum_squares_four {a n : ℕ} :
    SumThreeSquares (4 ^ a * n) → SumThreeSquares n := by
  induction a with
  | zero => simp
  | succ a ih =>
      intro h
      apply ih
      apply squares_four_mul
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- **Proposition 6.14, obstruction direction.** A number of the form
`4^a * (8*b + 7)` is not a sum of three squares. -/
theorem not_sum_squares (a b : ℕ) :
    ¬ SumThreeSquares (4 ^ a * (8 * b + 7)) := by
  intro h
  have hbase : SumThreeSquares (8 * b + 7) :=
    sum_squares_four h
  exact squares_eight_seven (by omega) hbase

/-- Natural-number form of the forbidden shape `4^a(8b-1)` in the source.
For a positive integer, this is equivalently `4^a(8b+7)` with `a,b : ℕ`. -/
def ThreeSquaresForbidden (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

/-- The only unformalized direction of the Gauss--Legendre theorem. -/
def ExistenceBridge : Prop :=
  ∀ n : ℕ, 0 < n → ¬ ThreeSquaresForbidden n → SumThreeSquares n

/-- The full source biconditional follows from the already-proved congruence
obstruction and the isolated existence direction. -/
theorem of_existence
    (hExistence : ExistenceBridge) :
    ∀ n : ℕ, 0 < n → (SumThreeSquares n ↔ ¬ ThreeSquaresForbidden n)
  := by
  intro n hn
  constructor
  · intro hsum hforbidden
    obtain ⟨a, b, rfl⟩ := hforbidden
    exact not_sum_squares a b hsum
  · exact hExistence n hn

end Submission.CField.QForms
