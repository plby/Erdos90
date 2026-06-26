import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Chapter VIII, Section 5: the elementary Wieferich consequence

Theorem 5.14 is the deep power-reciprocity input: every prime divisor `q` of
a first-case Fermat solution satisfies `q^(p-1) ≡ 1 (mod p²)`.  Its proof in
the source uses the explicit cyclotomic Hilbert symbol, which is not currently
available in Mathlib or this project.

Corollary 5.15 has a separate elementary final step: some member of a Fermat
triple is even, so Theorem 5.14 can be applied with `q = 2`.  We formalize
that step exactly here.
-/

namespace Submission.CField.HRecip

/-- In any natural-number solution of `x^p + y^p = z^p`, at least one of
`x`, `y`, and `z` is even.  This is the parity observation used in the proof
of Corollary 5.15. -/
theorem two_dvd_add
    {p x y z : ℕ} (hFermat : x ^ p + y ^ p = z ^ p) :
    2 ∣ x * y * z := by
  by_contra htwo
  have hx : Odd x := Nat.not_even_iff_odd.mp fun heven =>
    htwo (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left heven.two_dvd y) z)
  have hy : Odd y := Nat.not_even_iff_odd.mp fun heven =>
    htwo (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right heven.two_dvd x) z)
  have hz : Odd z := Nat.not_even_iff_odd.mp fun heven =>
    htwo (dvd_mul_of_dvd_right heven.two_dvd (x * y))
  have heven : Even (z ^ p) := by
    rw [← hFermat]
    exact hx.pow.add_odd hy.pow
  exact (Nat.not_even_iff_odd.mpr hz.pow) heven

/-- **Corollary VIII.5.15 (Wieferich's condition), conditional on Theorem
VIII.5.14.** If every prime divisor of a Fermat triple satisfies the
Furtwängler congruence, then `2` satisfies it. -/
theorem wieferich_of_furtwangler
    {p x y z : ℕ} (hFermat : x ^ p + y ^ p = z ^ p)
    (hFurtwangler : ∀ q : ℕ, q.Prime → q ∣ x * y * z →
      q ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  hFurtwangler 2 Nat.prime_two
    (two_dvd_add hFermat)

end Submission.CField.HRecip
