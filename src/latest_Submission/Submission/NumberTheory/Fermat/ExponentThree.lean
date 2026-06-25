import Mathlib

namespace Submission.NumberTheory

private lemma cube_or_dvd
    (x : ℤ) (hx : ¬ (3 : ℤ) ∣ x) :
    x ^ 3 ≡ 1 [ZMOD 9] ∨ x ^ 3 ≡ -1 [ZMOD 9] := by
  have hmod : x % 9 ≡ x [ZMOD 9] := Int.mod_modEq x 9
  have hmod3 : x % 9 ≡ x [ZMOD 3] :=
    hmod.of_dvd (by norm_num)
  have hnonneg : 0 ≤ x % 9 := Int.emod_nonneg x (by norm_num)
  have hlt : x % 9 < 9 := Int.emod_lt_of_pos x (by norm_num)
  have hxrem : x % 3 ≠ 0 := by
    intro h
    exact hx (Int.dvd_iff_emod_eq_zero.mpr h)
  have hpow : (x % 9) ^ 3 ≡ x ^ 3 [ZMOD 9] := hmod.pow 3
  have hcases :
      x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨
        x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
    omega
  rcases hcases with hres | hres | hres | hres | hres | hres | hres | hres | hres
  · exact (hxrem (by simpa [Int.ModEq, hres] using hmod3.symm)).elim
  · exact Or.inl (by simpa [Int.ModEq, hres] using hpow.symm)
  · exact Or.inr (by simpa [Int.ModEq, hres] using hpow.symm)
  · exact (hxrem (by simpa [Int.ModEq, hres] using hmod3.symm)).elim
  · exact Or.inl (by simpa [Int.ModEq, hres] using hpow.symm)
  · exact Or.inr (by simpa [Int.ModEq, hres] using hpow.symm)
  · exact (hxrem (by simpa [Int.ModEq, hres] using hmod3.symm)).elim
  · exact Or.inl (by simpa [Int.ModEq, hres] using hpow.symm)
  · exact Or.inr (by simpa [Int.ModEq, hres] using hpow.symm)

/-- The elementary `p = 3` argument in the opening chapter of Wright's notes:
if none of `x`, `y`, and `z` is divisible by `3`, then `x³ + y³ = z³` is impossible. -/
theorem fermat_case_three
    {x y z : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) (hy : ¬ (3 : ℤ) ∣ y) (hz : ¬ (3 : ℤ) ∣ z) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  intro hxyz
  rcases cube_or_dvd x hx with hx3 | hx3 <;>
    rcases cube_or_dvd y hy with hy3 | hy3 <;>
      rcases cube_or_dvd z hz with hz3 | hz3
  all_goals
    have heq : x ^ 3 + y ^ 3 ≡ z ^ 3 [ZMOD 9] := by rw [hxyz]
    have hbad := (hx3.add hy3).symm.trans (heq.trans hz3)
    norm_num [Int.ModEq] at hbad

end Submission.NumberTheory
