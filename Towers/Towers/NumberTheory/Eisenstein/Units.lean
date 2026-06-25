import Mathlib

namespace Towers.NumberTheory

/-- The integral model `Z[omega]`, where `omega^2 = omega - 1`, for the ring of integers of
`Q(sqrt(-3))`. -/
abbrev EInts := QuadraticAlgebra ℤ (-1) 1

namespace EInts

/-- The element corresponding to `(1 + sqrt(-3)) / 2`. -/
def omega : EInts := ⟨0, 1⟩

@[simp] theorem omega_sq : omega ^ 2 = omega - 1 := by
  simp [QuadraticAlgebra.ext_iff, omega, pow_two,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private lemma norm_formula (x : EInts) :
    x.norm = x.re ^ 2 + x.re * x.im + x.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

private lemma norm_nonnegative (x : EInts) : 0 ≤ x.norm := by
  have hfour : 4 * x.norm = (2 * x.re + x.im) ^ 2 + 3 * x.im ^ 2 := by
    rw [norm_formula]
    ring
  nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg x.im]

/-- Proposition 96 for the exceptional imaginary quadratic ring of discriminant `-3`:
its units are the six sixth roots of unity. -/
theorem isUnit_iff (x : EInts) :
    IsUnit x ↔
      x = 1 ∨ x = -1 ∨ x = omega ∨ x = -omega ∨
        x = 1 - omega ∨ x = omega - 1 := by
  constructor
  · intro hx
    have hnormUnit : IsUnit x.norm :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hx
    have hnorm : x.norm = 1 := by
      rcases Int.isUnit_iff.mp hnormUnit with hnorm | hnorm
      · exact hnorm
      · have := norm_nonnegative x
        omega
    rw [norm_formula] at hnorm
    have hfour_y : (2 * x.re + x.im) ^ 2 + 3 * x.im ^ 2 = 4 := by
      nlinarith
    have hfour_x : (2 * x.im + x.re) ^ 2 + 3 * x.re ^ 2 = 4 := by
      nlinarith
    have hre_lower : -2 < x.re := by
      nlinarith [sq_nonneg (2 * x.im + x.re)]
    have hre_upper : x.re < 2 := by
      nlinarith [sq_nonneg (2 * x.im + x.re)]
    have him_lower : -2 < x.im := by
      nlinarith [sq_nonneg (2 * x.re + x.im)]
    have him_upper : x.im < 2 := by
      nlinarith [sq_nonneg (2 * x.re + x.im)]
    interval_cases hre : x.re <;> interval_cases him : x.im <;>
      simp [hre, him, QuadraticAlgebra.ext_iff, omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hnorm ⊢
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit] <;>
      norm_num [norm_formula, omega, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]

/-- The primitive sixth root of unity `omega`, bundled as a unit. -/
def omegaUnit : EIntsˣ where
  val := omega
  inv := 1 - omega
  val_inv := by
    ext <;> norm_num [omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  inv_val := by
    ext <;> norm_num [omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[simp] theorem omegaUnit_val :
    ((omegaUnit : EIntsˣ) : EInts) = omega := rfl

@[simp] theorem omega_unit_six : omegaUnit ^ 6 = 1 := by
  ext <;> norm_num [omegaUnit, omega, pow_succ,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Proposition 99(i): every unit in the Eisenstein integers is one of the six powers of
`omegaUnit`. -/
theorem unit_omega_pow (u : EIntsˣ) :
    ∃ k : Fin 6, u = omegaUnit ^ (k : ℕ) := by
  have hu : IsUnit (u : EInts) := u.isUnit
  rw [isUnit_iff] at hu
  rcases hu with h | h | h | h | h | h
  · refine ⟨0, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · refine ⟨3, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · refine ⟨1, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · refine ⟨4, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · refine ⟨5, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · refine ⟨2, Units.ext ?_⟩
    rw [h]
    ext <;> norm_num [omegaUnit, omega, pow_succ,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem omegaUnit_order : orderOf omegaUnit = 6 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 6)]
  refine ⟨omega_unit_six, ?_⟩
  intro m hm hpos
  interval_cases m <;>
    simp_all [omegaUnit, omega, pow_succ, Units.ext_iff,
      QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The unique-exponent form of Proposition 99(i). -/
theorem unit_omega_unique (u : EIntsˣ) :
    ∃! k : Fin 6, u = omegaUnit ^ (k : ℕ) := by
  obtain ⟨k, hk⟩ := unit_omega_pow u
  refine ⟨k, hk, ?_⟩
  intro l hl
  have hpow : omegaUnit ^ (k : ℕ) = omegaUnit ^ (l : ℕ) := hk.symm.trans hl
  have hmod := pow_eq_pow_iff_modEq.mp hpow
  rw [omegaUnit_order] at hmod
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt hmod.symm l.isLt k.isLt

end EInts

end Towers.NumberTheory
