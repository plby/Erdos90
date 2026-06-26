import Towers.ClassField.HigherReciprocity.FurtwanglerConclusion

/-! # Chapter VIII, Section 5, Corollary 5.15 -/

namespace Towers.CField.HRecip

/-- Dividing a positive Fermat solution by the common gcd produces the
relatively-prime solution to which Theorem 5.14 applies. -/
theorem primitive_fermat_solution
    {p x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hpxyz : ¬ p ∣ x * y * z) (hFermat : x ^ p + y ^ p = z ^ p) :
    ∃ x₀ y₀ z₀ : ℕ,
      0 < x₀ ∧ 0 < y₀ ∧ 0 < z₀ ∧
      Nat.gcd (Nat.gcd x₀ y₀) z₀ = 1 ∧
      (¬ p ∣ x₀ * y₀ * z₀) ∧
      x₀ ^ p + y₀ ^ p = z₀ ^ p := by
  let d := Nat.gcd (Nat.gcd x y) z
  have hdxy : d ∣ Nat.gcd x y := Nat.gcd_dvd_left _ _
  have hdz : d ∣ z := Nat.gcd_dvd_right _ _
  have hdx : d ∣ x := hdxy.trans (Nat.gcd_dvd_left _ _)
  have hdy : d ∣ y := hdxy.trans (Nat.gcd_dvd_right _ _)
  have hdpos : 0 < d :=
    Nat.gcd_pos_of_pos_left z (Nat.gcd_pos_of_pos_left y hx)
  refine ⟨x / d, y / d, z / d,
    Nat.div_pos (Nat.le_of_dvd hx hdx) hdpos,
    Nat.div_pos (Nat.le_of_dvd hy hdy) hdpos,
    Nat.div_pos (Nat.le_of_dvd hz hdz) hdpos, ?_, ?_, ?_⟩
  · rw [Nat.gcd_div hdx hdy, Nat.gcd_div hdxy hdz]
    exact Nat.div_self hdpos
  · intro hpReduced
    apply hpxyz
    apply hpReduced.trans
    exact mul_dvd_mul
      (mul_dvd_mul (Nat.div_dvd_of_dvd hdx) (Nat.div_dvd_of_dvd hdy))
      (Nat.div_dvd_of_dvd hdz)
  · have hscaled :
        (d * (x / d)) ^ p + (d * (y / d)) ^ p =
          (d * (z / d)) ^ p := by
      simpa [Nat.mul_div_cancel' hdx, Nat.mul_div_cancel' hdy,
        Nat.mul_div_cancel' hdz] using hFermat
    rw [mul_pow, mul_pow, mul_pow, ← Nat.mul_add] at hscaled
    exact Nat.mul_left_cancel (Nat.pow_pos hdpos) hscaled

/-- Theorem 5.14 implies the unconditional source formulation of
Wieferich's condition. -/
theorem primitive_fermat_absurd
    (h514 : (∀ (p x y z : ℕ),
          p.Prime → p ≠ 2 → 0 < x → 0 < y → 0 < z →
          Nat.gcd (Nat.gcd x y) z = 1 → (¬ p ∣ x * y * z) →
          x ^ p + y ^ p = z ^ p →
          ∀ q : ℕ, q.Prime → q ∣ x * y * z →
            q ^ (p - 1) ≡ 1 [MOD p ^ 2])) :
    (∀ (p x y z : ℕ),
          p.Prime → p ≠ 2 → 0 < x → 0 < y → 0 < z →
          (¬ p ∣ x * y * z) → x ^ p + y ^ p = z ^ p →
          2 ^ (p - 1) ≡ 1 [MOD p ^ 2]) := by
  intro p x y z hp hp2 hx hy hz hpxyz hFermat
  obtain ⟨x₀, y₀, z₀, hx₀, hy₀, hz₀, hcoprime, hpReduced, hFermat₀⟩ :=
    primitive_fermat_solution hx hy hz hpxyz hFermat
  exact h514 p x₀ y₀ z₀ hp hp2 hx₀ hy₀ hz₀ hcoprime hpReduced hFermat₀
    2 Nat.prime_two (two_dvd_add hFermat₀)

end Towers.CField.HRecip
