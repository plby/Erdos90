import Towers.ClassField.LocalGlobalPowers.Counterexample
import Towers.NumberTheory.Locals.NewtonRootLifting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Appendix, Exercise A-11: the exceptional eighth power

The real and rational parts of the exercise were already needed in Chapter
VIII, Section 1, and are re-exported here with the appendix numbering.  The
three elementary identities below isolate the last algebraic step in Milne's
local argument: if one of `-1`, `2`, or `-2` is a square, then `16` is an
eighth power.

The finite-field quadratic-character trichotomy and Hensel lifting are also
carried out below, completing the odd `p`-adic assertion.
-/

namespace Towers.CField.LGPowers.EEPower

open Towers.CField.LGPowers
open Towers.NumberTheory.Milne
open Polynomial

noncomputable section

/-- If `x^2 = 2`, then `x` is an eighth root of `16`. -/
theorem eighth_power_sq
    {R : Type*} [CommRing R] (x : R) (hx : x ^ 2 = 2) :
    x ^ 8 = 16 := by
  rw [show 8 = 2 * 4 by norm_num, pow_mul, hx]
  norm_num

/-- If `x^2 = -2`, then `x` is an eighth root of `16`. -/
theorem eighth_sq_two
    {R : Type*} [CommRing R] (x : R) (hx : x ^ 2 = -2) :
    x ^ 8 = 16 := by
  rw [show 8 = 2 * 4 by norm_num, pow_mul, hx]
  norm_num

/-- If `i^2 = -1`, then `(1+i)^8 = 16`. -/
theorem eighth_sq_neg
    {R : Type*} [CommRing R] (i : R) (hi : i ^ 2 = -1) :
    (1 + i) ^ 8 = 16 := by
  have hsquare : (1 + i) ^ 2 = 2 * i := by
    calc
      (1 + i) ^ 2 = 1 + 2 * i + i ^ 2 := by ring
      _ = 2 * i := by rw [hi]; ring
  have hiFourth : i ^ 4 = 1 := by
    calc
      i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hi]
      _ = 1 := by ring
  calc
    (1 + i) ^ 8 = ((1 + i) ^ 2) ^ 4 := by ring
    _ = (2 * i) ^ 4 := by rw [hsquare]
    _ = 16 := by rw [mul_pow, hiFourth]; ring

/-- **Exercise A-11, real part.** `16` is an eighth power in `R`. -/
theorem sixteen_eighth_real :
    ∃ x : ℝ, x ^ 8 = 16 :=
  Towers.CField.LGPowers.sixteen_eighth_real

/-- **Exercise A-11, rational obstruction.** `16` is not an eighth power in
`Q`. -/
theorem sixteen_eighth_rational :
    ¬∃ x : ℚ, x ^ 8 = 16 :=
  Towers.CField.LGPowers.sixteen_eighth_rational

/-- For an odd prime, one of `-1`, `2`, or `-2` is a square in the residue
field.  The four odd residue classes modulo eight give the four cases. -/
theorem zmod_square_or
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    IsSquare (-1 : ZMod p) ∨ IsSquare (2 : ZMod p) ∨
      IsSquare (-2 : ZMod p) := by
  have hpodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp2
  have hpmodlt : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hpmododd : p % 8 % 2 = 1 := by omega
  have hcases : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  rcases hcases with h1 | h3 | h5 | h7
  · exact Or.inr <| Or.inl <|
      (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl h1)
  · exact Or.inr <| Or.inr <|
      (ZMod.exists_sq_eq_neg_two_iff hp2).2 (Or.inr h3)
  · exact Or.inl <| ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  · exact Or.inr <| Or.inl <|
      (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inr h7)

/-- A nonzero square modulo an odd prime lifts to a square in the `p`-adic
integers.  This is the simple-root Hensel step used in Exercise A-11. -/
private theorem sq_square_mod
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) (ha : IsSquare (a : ZMod p)) :
    ∃ y : ℤ_[p], y ^ 2 = a := by
  let F : ℤ[X] := X ^ 2 - C a
  obtain ⟨c, hc⟩ := ha
  let r : ℤ := c.val
  have hcr : (r : ZMod p) = c := by simp [r]
  have hz : ((r ^ 2 : ℤ) : ZMod p) = (a : ZMod p) := by
    rw [Int.cast_pow, hcr]
    simpa [pow_two] using hc.symm
  have hdiv : (p : ℤ) ∣ r ^ 2 - a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by simpa using sub_eq_zero.mpr hz)
  have hrp : ¬ (p : ℤ) ∣ r := by
    intro hr
    have hczero : c = 0 := by
      exact hcr.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 hr)
    apply hpa
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1
      (by simpa [hczero] using hc)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2
      ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpdiv)
  have hrzero : (r : ZMod p) ≠ 0 := by
    intro h
    exact hrp ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).1 h)
  have h2r : ¬ (p : ℤ) ∣ 2 * r := by
    intro h
    have hzero : ((2 * r : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * r) p).2 h
    push_cast at hzero
    exact mul_ne_zero htwo hrzero hzero
  have hF : F.aeval (r : ℤ_[p]) = ((r ^ 2 - a : ℤ) : ℤ_[p]) := by
    simp [F, aeval_def]
  have hFd : F.derivative.aeval (r : ℤ_[p]) = ((2 * r : ℤ) : ℤ_[p]) := by
    simp [F, aeval_def]
  have hderiv : ‖F.derivative.aeval (r : ℤ_[p])‖ = 1 := by
    rw [hFd, PadicInt.norm_intCast_eq_one_iff]
    rw [Int.isCoprime_iff_nat_coprime]
    have hpNat : ¬ p ∣ (2 * r).natAbs := by
      rwa [← Int.natCast_dvd]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpNat).symm
  have hvalue : ‖F.aeval (r : ℤ_[p])‖ < 1 := by
    rw [hF, PadicInt.norm_intCast_lt_one_iff]
    exact hdiv
  have hnewton :
      ‖F.aeval (r : ℤ_[p])‖ < ‖F.derivative.aeval (r : ℤ_[p])‖ ^ 2 := by
    simpa [hderiv] using hvalue
  obtain ⟨y, hy, -, -⟩ := padic_newton_root F r hnewton
  refine ⟨y, ?_⟩
  have hy' : y ^ 2 - (a : ℤ_[p]) = 0 := by simpa [F] using hy
  exact sub_eq_zero.mp hy'

/-- **Exercise A-11, odd `p`-adic part.** For every odd prime `p`, `16` is
an eighth power in `Q_p`. -/
theorem sixteen_eighth_padic
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ x : ℚ_[p], x ^ 8 = 16 := by
  have hpNotDvdTwo : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hpdiv : p ∣ 2 := by exact_mod_cast h
    exact hp2
      ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpdiv)
  rcases zmod_square_or p hp2 with hneg | htwo | hnegTwo
  · have hneg' : IsSquare (((-1 : ℤ) : ZMod p)) := by simpa using hneg
    have hpNotDvdNegOne : ¬ (p : ℤ) ∣ -1 := by
      intro h
      exact (Fact.out : p.Prime).ne_one
        (Nat.dvd_one.mp (Int.natCast_dvd.mp h))
    obtain ⟨i, hi⟩ := sq_square_mod p hp2 (a := -1)
        hpNotDvdNegOne hneg'
    refine ⟨(1 + (i : ℚ_[p])), ?_⟩
    apply eighth_sq_neg
    simpa using congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hi
  · have htwo' : IsSquare (((2 : ℤ) : ZMod p)) := by simpa using htwo
    obtain ⟨x, hx⟩ := sq_square_mod p hp2 (a := 2)
        hpNotDvdTwo htwo'
    refine ⟨(x : ℚ_[p]), eighth_power_sq _ ?_⟩
    simpa using congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hx
  · have hnegTwo' : IsSquare (((-2 : ℤ) : ZMod p)) := by simpa using hnegTwo
    obtain ⟨x, hx⟩ := sq_square_mod p hp2 (a := -2)
        (by simpa using hpNotDvdTwo) hnegTwo'
    refine ⟨(x : ℚ_[p]), eighth_sq_two _ ?_⟩
    simpa using congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hx

end

end Towers.CField.LGPowers.EEPower
