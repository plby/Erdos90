import Mathlib

/-!
# Milne, Algebraic Number Theory, Example 2.35

The first two small instances of the discriminant formula for `X^n + aX + b`.
The general resultant computation, and the larger computer-algebra examples in the text, are
computational rather than structural.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- The resultant of a linear polynomial and a binomial. This is the algebraic calculation
used in the proof of Example 2.35. -/
theorem resultant_x_c
    {K : Type*} [Field K] {m : ℕ} (hm : 0 < m) (c b d e : K) :
    resultant (C c * X + C b) (C d * X ^ m + C e) 1 m =
      d * (-b) ^ m + e * c ^ m := by
  by_cases hc : c = 0
  · subst c
    have hz : C (0 : K) * X + C b = C b := by simp
    rw [hz, zero_pow hm.ne']
    simp only [mul_zero, add_zero]
    rw [resultant_C_left]
    simp only [one_mul, coeff_add, coeff_C_mul, coeff_X_pow, if_pos, pow_one,
      coeff_C, if_neg hm.ne', add_zero]
    rw [neg_pow]
    ring
  · have hpoly : C c * X + C b = C c * (X + C (b / c)) := by
      rw [mul_add, ← C_mul]
      congr 1
      apply C_injective
      field_simp [hc]
    rw [hpoly, resultant_C_mul_left, resultant_X_add_C_left]
    · simp only [eval_add, eval_mul, eval_X, eval_C, eval_pow]
      rw [mul_add, neg_pow, div_pow]
      field_simp [pow_ne_zero _ hc]
      ring
    · calc
        (C d * X ^ m + C e).natDegree ≤
            max (C d * X ^ m).natDegree (C e).natDegree := natDegree_add_le _ _
        _ ≤ m := by
          apply max_le
          · exact natDegree_C_mul_X_pow_le d m
          · simp

/-- Example 2.35: the discriminant of `X^n + aX + b`. -/
theorem discr_add_b
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : 2 ≤ n) (a b : K) :
    discr (X ^ n + C a * X + C b) =
      (-1) ^ (n * (n - 1) / 2) *
        ((n : K) ^ n * b ^ (n - 1) +
          (-1) ^ (n - 1) * ((n - 1 : ℕ) : K) ^ (n - 1) * a ^ n) := by
  let f : K[X] := X ^ n + C a * X + C b
  let g : K[X] := C (n : K) * X ^ (n - 1) + C a
  have hn0 : (n : K) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hlow : (C a * X + C b).natDegree < n := by
    calc
      (C a * X + C b).natDegree ≤ max (C a * X).natDegree (C b).natDegree :=
        natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simpa using natDegree_C_mul_X_pow_le a 1
        · simp
      _ < n := by omega
  have hfdegree : f.IsMonicOfDegree n := by
    simpa [f, add_assoc] using (isMonicOfDegree_X_pow K n).add_right hlow
  have hfdeg : f.natDegree = n := hfdegree.natDegree_eq
  have hfmonic : f.Monic := hfdegree.monic
  have hg : f.derivative = g := by
    simp [f, g, derivative_add, derivative_mul, derivative_X_pow]
  have hgdeg : g.natDegree = n - 1 := by
    have hlead : (C (n : K) * X ^ (n - 1)).natDegree = n - 1 := by
      exact natDegree_C_mul_X_pow (n - 1) (n : K) hn0
    have hconstlt : (C a : K[X]).natDegree <
        (C (n : K) * X ^ (n - 1)).natDegree := by
      rw [hlead]
      simp [show 0 < n - 1 by omega]
    dsimp [g]
    rw [natDegree_add_eq_left_of_natDegree_lt hconstlt, hlead]
  have hres : resultant f g n (n - 1) =
      (n : K) ^ n * b ^ (n - 1) +
        (-1) ^ (n - 1) * ((n - 1 : ℕ) : K) ^ (n - 1) * a ^ n := by
    let c : K := ((n - 1 : ℕ) : K) / (n : K) * a
    let h : K[X] := C c * X + C b
    let p : K[X] := C ((n : K)⁻¹) * X
    have hpdeg : p.natDegree = 1 := by simp [p, hn0]
    have hreduce : f = h + g * p := by
      dsimp [f, h, g, p, c]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      have hX : (X : K[X]) ^ n = X ^ (n - 1) * X := by
        calc
          X ^ n = X ^ (n - 1 + 1) := by (congr 1; omega)
          _ = X ^ (n - 1) * X := pow_succ X (n - 1)
      rw [hX]
      simp only [div_eq_mul_inv, map_sub, map_mul]
      ring_nf
      have hCinv : C (n : K) * C ((n : K)⁻¹) = (1 : K[X]) := by
        rw [← C_mul, mul_inv_cancel₀ hn0, map_one]
      calc
        X * X ^ (n - 1) + X * C a + C b =
            X * X ^ (n - 1) * (C (n : K) * C ((n : K)⁻¹)) +
              X * C a * (C (n : K) * C ((n : K)⁻¹)) + C b := by
          rw [hCinv]
          ring
        _ = _ := by
          rw [map_one]
          ring
    rw [hreduce, resultant_add_mul_left]
    · have hhdeg : h.natDegree ≤ 1 := by
        dsimp [h]
        calc
          (C c * X + C b).natDegree ≤
              max (C c * X).natDegree (C b).natDegree := natDegree_add_le _ _
          _ ≤ 1 := by
            apply max_le
            · simpa using natDegree_C_mul_X_pow_le c 1
            · simp
      have hpad := resultant_add_left_deg h g 1 (n - 1) (n - 1) hhdeg
      rw [show 1 + (n - 1) = n by omega] at hpad
      rw [hpad]
      rw [show g.coeff (n - 1) = (n : K) by
        dsimp [g]
        rw [coeff_add, coeff_C_mul, coeff_X_pow]
        simp only [if_pos, mul_one]
        rw [coeff_C]
        simp [show n - 1 ≠ 0 by omega]]
      rw [resultant_x_c (m := n - 1) (by omega)]
      dsimp only [c]
      rw [neg_pow b]
      have hsign : (-1 : K) ^ ((n - 1) * (n - 1)) = (-1) ^ (n - 1) := by
        apply neg_one_pow_congr
        simp [Nat.even_mul]
      rw [hsign, mul_pow, div_pow]
      field_simp [pow_ne_zero _ hn0]
      have hsign2 : (-1 : K) ^ ((n - 1) * 2) = 1 := by
        calc
          (-1 : K) ^ ((n - 1) * 2) = (-1) ^ (2 * (n - 1)) := by
            rw [Nat.mul_comm]
          _ = ((-1) ^ 2) ^ (n - 1) := pow_mul _ _ _
          _ = 1 := by norm_num
      have hsquares : (-1 : K) ^ (n - 1) * (-1) ^ (n - 1) = 1 := by
        rw [← pow_add, show n - 1 + (n - 1) = (n - 1) * 2 by omega, hsign2]
      rw [mul_add]
      have hnpow : (n : K) ^ n = (n : K) ^ (n - 1) * (n : K) := by
        calc
          (n : K) ^ n = (n : K) ^ ((n - 1) + 1) := by (congr 1; omega)
          _ = (n : K) ^ (n - 1) * (n : K) := pow_succ _ _
      have hapow : a ^ n = a ^ (n - 1) * a := by
        calc
          a ^ n = a ^ ((n - 1) + 1) := by (congr 1; omega)
          _ = a ^ (n - 1) * a := pow_succ _ _
      rw [hnpow, hapow]
      ring_nf at hsquares ⊢
      rw [hsquares]
      simp
    · rw [hpdeg]
      omega
    · rw [hgdeg]
  change f.discr = _
  have hpos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos, hfdeg]
    omega
  have hresultant := resultant_deriv (f := f) hpos
  rw [hg, hfdeg, hfmonic.leadingCoeff, mul_one, hres] at hresultant
  let s : K := (-1) ^ (n * (n - 1) / 2)
  have hs : s * s = 1 := by
    dsimp [s]
    calc
      (-1 : K) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 1) / 2) =
          (-1) ^ (n * (n - 1) / 2 + n * (n - 1) / 2) := by rw [pow_add]
      _ = ((-1 : K) ^ 2) ^ (n * (n - 1) / 2) := by
        rw [show n * (n - 1) / 2 + n * (n - 1) / 2 =
          2 * (n * (n - 1) / 2) by omega, pow_mul]
      _ = 1 := by norm_num
  change f.discr = s * _
  calc
    f.discr = 1 * f.discr := by rw [one_mul]
    _ = (s * s) * f.discr := by rw [hs]
    _ = s * (s * f.discr) := by ring
    _ = s * _ := by rw [← hresultant]

/-- The quadratic instance of Example 2.35. -/
theorem discr_sq_b
    {K : Type*} [CommRing K] [Nontrivial K] (a b : K) :
    discr (X ^ 2 + C a * X + C b) = a ^ 2 - 4 * b := by
  rw [discr_of_degree_eq_two]
  · simp
  · simpa using
      (degree_quadratic (R := K) (a := 1) (b := a) (c := b) one_ne_zero)

/-- The cubic instance of Example 2.35. -/
theorem discr_cube_b
    {K : Type*} [CommRing K] [Nontrivial K] (a b : K) :
    discr (X ^ 3 + C a * X + C b) = -27 * b ^ 2 - 4 * a ^ 3 := by
  rw [discr_of_degree_eq_three]
  · simp
    ring
  · simpa using
      (degree_cubic (R := K) (a := 1) (b := 0) (c := a) (d := b) one_ne_zero)

/-- The quartic instance displayed in Example 2.35. -/
theorem discr_four_b
    {K : Type*} [Field K] [CharZero K] (a b : K) :
    discr (X ^ 4 + C a * X + C b) = 256 * b ^ 3 - 27 * a ^ 4 := by
  rw [discr_add_b 4 (by norm_num) a b]
  norm_num
  ring

/-- The quintic instance displayed in Example 2.35. -/
theorem discr_x_b
    {K : Type*} [Field K] [CharZero K] (a b : K) :
    discr (X ^ 5 + C a * X + C b) = 5 ^ 5 * b ^ 4 + 4 ^ 4 * a ^ 5 := by
  rw [discr_add_b 5 (by norm_num) a b]
  norm_num

/-- The discriminant computation in Example 2.36. -/
theorem discr_cube_sub :
    discr (X ^ 3 - X - 1 : ℤ[X]) = -23 := by
  simpa [sub_eq_add_neg] using
    (discr_cube_b (-1 : ℤ) (-1 : ℤ))

/-- The irreducibility assertion in Example 2.36. This is the degree-three case of
Selmer's theorem on `X^n - X - 1`. -/
theorem irreducible_cube_sub :
    Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  simpa using (X_pow_sub_X_sub_one_irreducible_rat (n := 3) (by norm_num))

/-- The discriminant computation in Example 2.37. -/
theorem discr_x_cube :
    discr (X ^ 3 + X + 1 : ℤ[X]) = -31 := by
  simpa using (discr_cube_b (1 : ℤ) (1 : ℤ))

/-- The irreducibility assertion in Example 2.37. -/
theorem irreducible_cube_add :
    Irreducible (X ^ 3 + X + 1 : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (X ^ 3 + X + 1 : ℚ[X]).natDegree = 3 := by
      have hlow : (X + 1 : ℚ[X]).natDegree < 3 := by
        calc
          (X + 1 : ℚ[X]).natDegree ≤ max X.natDegree (1 : ℚ[X]).natDegree :=
            natDegree_add_le _ _
          _ = 1 := by simp
          _ < 3 := by norm_num
      simpa [add_assoc] using
        ((isMonicOfDegree_X_pow ℚ 3).add_right hlow).natDegree_eq
    simp [hnat]
  · intro x hx
    let f : ℤ[X] := X ^ 3 + X + 1
    have hlow : (X + 1 : ℤ[X]).natDegree < 3 := by
      calc
        (X + 1 : ℤ[X]).natDegree ≤ max X.natDegree (1 : ℤ[X]).natDegree :=
          natDegree_add_le _ _
        _ = 1 := by simp
        _ < 3 := by norm_num
    have hf : f.Monic := by
      simpa [f, add_assoc] using
        ((isMonicOfDegree_X_pow ℤ 3).add_right hlow).monic
    have hroot : Polynomial.aeval x f = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      simpa [f, IsRoot.def, aeval_def] using hx
    obtain ⟨z, hxz, hz⟩ := exists_integer_of_is_root_of_monic hf hroot
    have hzunit : IsUnit z := by
      rw [isUnit_iff_dvd_one]
      simpa [f] using hz
    rcases Int.isUnit_eq_one_or hzunit with hz | hz
    · subst z
      have : x = 1 := by simpa using hxz
      subst x
      norm_num [f, IsRoot.def] at hx
    · subst z
      have : x = -1 := by simpa using hxz
      subst x
      norm_num [f, IsRoot.def] at hx

/-- The polynomial discriminant computation in Example 2.38. -/
theorem discr_cube_eight :
    discr (X ^ 3 + X ^ 2 - 2 * X + 8 : ℤ[X]) = -2012 := by
  rw [discr_of_degree_eq_three]
  · norm_num [coeff_add, coeff_sub, coeff_mul, coeff_X]
  · simpa using
      (degree_cubic (R := ℤ) (a := 1) (b := 1) (c := -2) (d := 8) one_ne_zero)

/-- The polynomial discriminant computation in Example 2.39. -/
theorem discr_x_five :
    discr (X ^ 5 - X - 1 : ℚ[X]) = 2869 := by
  convert discr_x_b (-1 : ℚ) (-1 : ℚ) using 1 <;>
    norm_num [sub_eq_add_neg]

/-- The irreducibility assertion in Example 2.39. This is another specialization of
Selmer's theorem. -/
theorem irreducible_x_five :
    Irreducible (X ^ 5 - X - 1 : ℚ[X]) := by
  simpa using (X_pow_sub_X_sub_one_irreducible_rat (n := 5) (by norm_num))

end Towers.NumberTheory.Milne
