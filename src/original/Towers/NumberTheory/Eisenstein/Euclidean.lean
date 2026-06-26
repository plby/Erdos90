import Towers.NumberTheory.Eisenstein.Units
import Mathlib.Algebra.Order.Round

/-!
# The Eisenstein integers are Euclidean

For Milne's Example 2.10(b), we prove that
`ℤ[(1 + √-3) / 2]` is a Euclidean domain for the norm
`N(a + bω) = a² + ab + b²`.  The quotient rounds the two rational
coordinates of the field quotient independently.  The resulting error lies
in the square `[-1/2, 1/2]²`, on which the norm is strictly less than one.
-/

namespace Towers.NumberTheory

namespace EInts

/-- The positive-definite norm form on the Eisenstein integers. -/
theorem norm_formula (x : EInts) :
    x.norm = x.re ^ 2 + x.re * x.im + x.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

/-- The Eisenstein norm is nonnegative. -/
theorem norm_nonnegative (x : EInts) : 0 ≤ x.norm := by
  have hfour : 4 * x.norm = (2 * x.re + x.im) ^ 2 + 3 * x.im ^ 2 := by
    rw [norm_formula]
    ring
  nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg x.im]

/-- The Eisenstein norm is positive precisely away from zero. -/
theorem norm_pos_iff (x : EInts) : 0 < x.norm ↔ x ≠ 0 := by
  constructor
  · intro h hzero
    subst x
    norm_num [norm_formula] at h
  · intro hx
    have hne : x.norm ≠ 0 := by
      rw [norm_formula]
      intro h
      have him : x.im = 0 := by
        nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg x.im]
      have hre : x.re = 0 := by
        rw [him] at h
        norm_num at h ⊢
        nlinarith
      apply hx
      ext <;> simp [hre, him]
    exact lt_of_le_of_ne (norm_nonnegative x) (Ne.symm hne)

private noncomputable def quotient (x y : EInts) :
    EInts :=
  ⟨round
      (((x.re * (y.re + y.im) + x.im * y.im : ℤ) : ℚ) /
        (y.norm : ℚ)),
    round
      (((x.im * y.re - x.re * y.im : ℤ) : ℚ) /
        (y.norm : ℚ))⟩

private noncomputable def remainder (x y : EInts) :
    EInts := x - y * quotient x y

private theorem quotient_zero (x : EInts) :
    quotient x 0 = 0 := by
  ext <;> simp [quotient]

private theorem quotient_remainder_eq (x y : EInts) :
    y * quotient x y + remainder x y = x := by
  simp [remainder]

private theorem norm_remainder_lt (x : EInts)
    {y : EInts} (hy : y ≠ 0) :
    (remainder x y).norm < y.norm := by
  let A : ℤ := x.re * (y.re + y.im) + x.im * y.im
  let B : ℤ := x.im * y.re - x.re * y.im
  let m : ℤ := round ((A : ℚ) / (y.norm : ℚ))
  let n : ℤ := round ((B : ℚ) / (y.norm : ℚ))
  let u : ℚ := (A : ℚ) / (y.norm : ℚ) - m
  let v : ℚ := (B : ℚ) / (y.norm : ℚ) - n
  have hquot : quotient x y = (⟨m, n⟩ : EInts) := by
    ext <;> simp [quotient, m, n, A, B]
  have hN : 0 < y.norm := (norm_pos_iff y).2 hy
  have hN0 : (y.norm : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have huabs : |u| ≤ (1 : ℚ) / 2 := by
    simpa [u, m] using
      (abs_sub_round ((A : ℚ) / (y.norm : ℚ)))
  have hvabs : |v| ≤ (1 : ℚ) / 2 := by
    simpa [v, n] using
      (abs_sub_round ((B : ℚ) / (y.norm : ℚ)))
  have hu := (abs_le.mp huabs)
  have hv := (abs_le.mp hvabs)
  have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by
    have hprod : 0 ≤ (u + 1 / 2) * (1 / 2 - u) :=
      mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
    nlinarith
  have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by
    have hprod : 0 ≤ (v + 1 / 2) * (1 / 2 - v) :=
      mul_nonneg (by linarith [hv.1]) (by linarith [hv.2])
    nlinarith
  have huv : u ^ 2 + u * v + v ^ 2 < (1 : ℚ) := by
    nlinarith [sq_nonneg (u - v)]
  have hnorm :
      ((remainder x y).norm : ℚ) =
        (y.norm : ℚ) * (u ^ 2 + u * v + v ^ 2) := by
    rw [norm_formula (remainder x y)]
    simp only [remainder, hquot,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    dsimp only [u, v, A, B]
    push_cast
    field_simp [hN0]
    rw [norm_formula y]
    push_cast
    ring
  have hcast : ((remainder x y).norm : ℚ) < (y.norm : ℚ) := by
    rw [hnorm]
    have hNq : 0 < (y.norm : ℚ) := by exact_mod_cast hN
    calc
      (y.norm : ℚ) * (u ^ 2 + u * v + v ^ 2) <
          (y.norm : ℚ) * 1 := mul_lt_mul_of_pos_left huv hNq
      _ = (y.norm : ℚ) := mul_one _
  exact_mod_cast hcast

private theorem nat_abs_remainder (x : EInts)
    {y : EInts} (hy : y ≠ 0) :
    (remainder x y).norm.natAbs < y.norm.natAbs := by
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt
    (norm_nonnegative (remainder x y)) (norm_remainder_lt x hy)

private theorem norm_mul_left (x : EInts)
    {y : EInts} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [map_mul, Int.natAbs_mul]
  have hyNorm : 1 ≤ y.norm.natAbs := by
    have : 0 < y.norm.natAbs :=
      Int.natAbs_pos.mpr ((norm_pos_iff y).2 hy).ne'
    omega
  exact le_mul_of_one_le_right (Nat.zero_le _) hyNorm

/-- **Milne, Example 2.10(b).** The Eisenstein integers are Euclidean for
their positive-definite norm. -/
noncomputable instance instEuclideanDomain : EuclideanDomain EInts :=
  { (inferInstance : CommRing EInts),
    (inferInstance : Nontrivial EInts) with
    quotient := quotient
    quotient_zero := quotient_zero
    remainder := remainder
    quotient_mul_add_remainder_eq := quotient_remainder_eq
    r := InvImage (· < ·) (Int.natAbs ∘ QuadraticAlgebra.norm)
    r_wellFounded := (measure (Int.natAbs ∘ QuadraticAlgebra.norm)).wf
    remainder_lt := nat_abs_remainder
    mul_left_not_lt := fun a _ hb0 ↦
      not_lt_of_ge (norm_mul_left a hb0) }

/-- **Milne, Example 2.10(b).** Consequently the Eisenstein integers form a
principal ideal ring. -/
theorem principalIdealRing : IsPrincipalIdealRing EInts := by
  infer_instance

/-- The Eisenstein integers are integrally closed. -/
theorem isIntegrallyClosed : IsIntegrallyClosed EInts := by
  infer_instance

/-- In their fraction field, the Eisenstein integers are exactly the
integral closure of `ℤ`. -/
theorem integral_fraction_ring :
    IsIntegralClosure EInts ℤ
      (FractionRing EInts) := by
  infer_instance

end EInts

end Towers.NumberTheory
