import Towers.ClassField.ArtinLSeries.GaussSplitCount
import Mathlib.Data.Real.Sqrt

/-!
# Chapter VIII, Section 10: the numerical consequence of Gauss's formula

The source prints `N_p = A` in the split case.  That formula is false (already
for `p = 7`); with its sign convention the intended point-count formula is
`N_p = p + 1 + A`.  The preceding files now prove that corrected point count;
this file records its elementary Weil-bound consequence.
-/

namespace Towers.CField.ALSeries

/-- If the corrected Gauss point-count formula and the accompanying
representation `4p = A² + 27B²` hold, with a nonzero second coefficient, then
the strict Weil bound follows. -/
theorem weil_corrected_point
    {p A B N : ℝ} (hp : 0 ≤ p) (hB : B ≠ 0)
    (hrep : 4 * p = A ^ 2 + 27 * B ^ 2)
    (hcount : N = p + 1 + A) :
    |N - p - 1| < 2 * Real.sqrt p := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hAsq : A ^ 2 < 4 * p := by nlinarith
  have hsqrt : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
  have hdiff : N - p - 1 = A := by linarith
  rw [hdiff]
  apply (sq_lt_sq₀ (abs_nonneg A) (by positivity)).mp
  rw [sq_abs]
  nlinarith

/-- In the split-prime representation `4p = A² + 27B²`, the coefficient
`B` cannot vanish.  Thus the strictness hypothesis in the real inequality
above is a consequence of the source hypotheses, not an extra assumption. -/
theorem gauss_split_ne
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    {A B : ℤ} (hrep : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) :
    B ≠ 0 := by
  intro hB
  subst B
  have hpA2 : (p : ℤ) ∣ A ^ 2 := by
    refine ⟨4, ?_⟩
    nlinarith
  have hpA : (p : ℤ) ∣ A :=
    Int.Prime.dvd_pow' (Fact.out : p.Prime) hpA2
  obtain ⟨k, hk⟩ := hpA
  rw [hk] at hrep
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hfactor : (p : ℤ) * (4 - (p : ℤ) * k ^ 2) = 0 := by
    nlinarith
  have hfour : (4 : ℤ) = (p : ℤ) * k ^ 2 := by
    have := (mul_eq_zero.mp hfactor).resolve_left hp0
    nlinarith
  have hp4int : (p : ℤ) ∣ 4 := ⟨k ^ 2, hfour⟩
  have hp4 : p ∣ 4 := by exact_mod_cast hp4int
  have hp2dvd : p ∣ 2 := by
    apply (Fact.out : p.Prime).dvd_of_dvd_pow (m := 2) (n := 2)
    norm_num [pow_two]
    exact hp4
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp2dvd
  subst p
  norm_num at hpmod

/-- Integer form of the strict Weil-bound calculation at a split prime. -/
theorem gauss_weil_corrected
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    {A B N : ℤ}
    (hrep : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2)
    (hcount : N = (p : ℤ) + 1 + A) :
    |(N : ℝ) - p - 1| < 2 * Real.sqrt p := by
  apply weil_corrected_point
    (p := (p : ℝ)) (A := (A : ℝ)) (B := (B : ℝ)) (N := (N : ℝ))
  · positivity
  · exact_mod_cast gauss_split_ne p hpmod hrep
  · exact_mod_cast hrep
  · exact_mod_cast hcount

/-- Gauss's corrected point-count theorem implies the strict Weil bound for
the Fermat cubic at every prime, with no additional hypotheses. -/
theorem fermat_point_weil
    (hGauss : (∀ (p : ℕ) [Fact p.Prime],
          (p % 3 ≠ 1 →
            (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
          (p % 3 = 1 →
            (∃! A : ℤ, GaussNormalizedCoefficient p A) ∧
            ∀ A : ℤ, GaussNormalizedCoefficient p A →
              (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)))
    (p : ℕ) [Fact p.Prime] :
    |(gaussFermatCount p : ℝ) - p - 1| <
      2 * Real.sqrt p := by
  by_cases hpmod : p % 3 = 1
  · obtain ⟨hexists, hcount⟩ := (hGauss p).2 hpmod
    obtain ⟨A, hA, _⟩ := hexists
    obtain ⟨hAmod, B, hrep⟩ := hA
    exact gauss_weil_corrected p hpmod hrep
      (hcount A ⟨hAmod, B, hrep⟩)
  · have hcount := (hGauss p).1 hpmod
    have hp : (0 : ℝ) < p := by
      exact_mod_cast (Fact.out : p.Prime).pos
    have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    have hzero : (gaussFermatCount p : ℝ) - p - 1 = 0 := by
      have hcountR : (gaussFermatCount p : ℝ) = (p : ℝ) + 1 := by
        exact_mod_cast hcount
      linarith
    rw [hzero, abs_zero]
    positivity

/-- The strict Weil bound for the Fermat cubic, with no bridge hypotheses. -/
theorem gauss_fermat_weil
    (p : ℕ) [Fact p.Prime] :
    |(gaussFermatCount p : ℝ) - p - 1| <
      2 * Real.sqrt p :=
  fermat_point_weil fermatPointCount p

end Towers.CField.ALSeries
