import Towers.NumberTheory.Quadratic.PrimeFactorization
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Class Field Theory, Introduction: quadratic extensions of Q

Milne writes `p* = (-1)^((p - 1) / 2) p` for an odd prime `p`.  Since
`(p - 1) / 2 = p / 2`, `primeStar` is the same integer.  The main result below
is the quadratic-reciprocity identity `(p* / q) = (q / p)` used to describe
the primes splitting in `Q(sqrt(p*))` by congruence conditions modulo `p`.
-/

namespace Towers.CField.Examples

open Ideal
open Towers.NumberTheory

/-- Milne's signed prime `p* = (-1)^((p - 1) / 2) p` for an odd prime `p`. -/
def primeStar (p : ℕ) : ℤ := (-1) ^ (p / 2) * p

/-- For an odd prime, `primeStar` is Milne's displayed formula
`(-1)^((p - 1) / 2) p`. -/
theorem star_book_formula {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    primeStar p = (-1) ^ ((p - 1) / 2) * p := by
  have hodd := Nat.Prime.odd_of_ne_two Fact.out hp
  rcases hodd with ⟨k, hk⟩
  have hexponent : p / 2 = (p - 1) / 2 := by omega
  simp only [primeStar, hexponent]

theorem star_mod_four {p : ℕ} (hp : p % 4 = 1) :
    primeStar p = p := by
  rw [primeStar, ZMod.neg_one_pow_div_two_of_one_mod_four hp]
  simp

theorem star_neg_four {p : ℕ} (hp : p % 4 = 3) :
    primeStar p = -(p : ℤ) := by
  rw [primeStar, ZMod.neg_one_pow_div_two_of_three_mod_four hp]
  simp

/-- For an odd prime `p`, Milne's `p*` is congruent to one modulo four. -/
theorem prime_star_mod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    primeStar p ≡ 1 [ZMOD 4] := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp
  rcases Nat.odd_mod_four_iff.mp hodd with hp1 | hp3
  · rw [star_mod_four hp1]
    exact Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using hp1)
  · rw [star_neg_four hp3]
    have hp3' : (p : ℤ) ≡ 3 [ZMOD 4] :=
      Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using hp3)
    exact hp3'.neg.trans (by norm_num)

/-- Milne's signed prime `p*` is squarefree. -/
theorem primeStar_squarefree {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Squarefree (primeStar p) := by
  rw [← Int.squarefree_natAbs]
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp
  rcases Nat.odd_mod_four_iff.mp hodd with hp1 | hp3
  · rw [star_mod_four hp1]
    simpa using (Fact.out : Nat.Prime p).squarefree
  · rw [star_neg_four hp3]
    simpa using (Fact.out : Nat.Prime p).squarefree

/-- The reciprocity identity `(p* / q) = (q / p)` from the introduction. -/
theorem legendre_sym_star {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q (primeStar p) = legendreSym p q := by
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp
  rcases Nat.odd_mod_four_iff.mp hpodd with hp1 | hp3
  · rw [star_mod_four hp1]
    exact legendreSym.quadratic_reciprocity_one_mod_four hp1 hq
  · have hqodd : q % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hq
    rcases Nat.odd_mod_four_iff.mp hqodd with hq1 | hq3
    · rw [star_neg_four hp3,
        show -(p : ℤ) = (-1) * p by ring, legendreSym.mul,
        legendreSym.at_neg_one hq, ZMod.χ₄_nat_one_mod_four hq1,
        one_mul, legendreSym.quadratic_reciprocity_one_mod_four hq1 hp]
    · rw [star_neg_four hp3,
        show -(p : ℤ) = (-1) * p by ring, legendreSym.mul,
        legendreSym.at_neg_one hq, ZMod.χ₄_nat_three_mod_four hq3,
        neg_one_mul, legendreSym.quadratic_reciprocity_three_mod_four hp3 hq3]
      simp

/-- The prime `p` ramifies in the integral-coordinate quadratic order for
`p*`. -/
theorem prime_ramifies_star {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (QOrd.rootIdeal (primeStar p) 0 p 0).IsPrime ∧
      QOrd.rootIdeal (primeStar p) 0 p 0 *
          QOrd.rootIdeal (primeStar p) 0 p 0 =
        span {(p : QOrd (primeStar p) 0)} := by
  apply
    Towers.NumberTheory.Milne.ramifies_quadratic_radical
      (primeStar p) (primeStar_squarefree hp) p
  refine ⟨(-1 : ℤ) ^ (p / 2), ?_⟩
  simp [primeStar, mul_comm]

/-- If `q` is a quadratic residue modulo `p`, then `(q)` splits into two distinct
prime ideals in the integral-coordinate quadratic order for `p*`. -/
theorem star_legendre_sym
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hleg : legendreSym p q = 1) :
    ∃ a : ℤ,
      (QOrd.rootIdeal (primeStar p) 0 q a).IsPrime ∧
      (QOrd.rootIdeal (primeStar p) 0 q (-a)).IsPrime ∧
      QOrd.rootIdeal (primeStar p) 0 q a ≠
        QOrd.rootIdeal (primeStar p) 0 q (-a) ∧
      QOrd.rootIdeal (primeStar p) 0 q a *
          QOrd.rootIdeal (primeStar p) 0 q (-a) =
        span {(q : QOrd (primeStar p) 0)} := by
  have hstar : legendreSym q (primeStar p) = 1 :=
    (legendre_sym_star hp hq).trans hleg
  have hqstar : ¬(q : ℤ) ∣ primeStar p := by
    intro hdiv
    have hz : legendreSym q (primeStar p) = 0 :=
      (legendreSym.eq_zero_iff q (primeStar p)).2
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (primeStar p) q).2 hdiv)
    omega
  exact
    Towers.NumberTheory.Milne.splits_legendre_sym
      (primeStar p) q hq hqstar hstar

/-- If `q` is a quadratic nonresidue modulo `p`, then `(q)` remains prime in the
integral-coordinate quadratic order for `p*`. -/
theorem inert_star_legendre
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hleg : legendreSym p q = -1) :
    (span {(q : QOrd (primeStar p) 0)}).IsPrime := by
  apply
    Towers.NumberTheory.Milne.odd_inert_legendre
  rw [legendre_sym_star hp hq]
  exact hleg

end Towers.CField.Examples
