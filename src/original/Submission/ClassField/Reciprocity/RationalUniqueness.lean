import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Chapter V, Section 5, Lemma 5.9: the rational uniqueness step

The proof of the idèle decomposition for `ℚ` uses the fact that the only
positive rational number which is a unit at every finite prime is `1`.  The
lemma below records the elementary reduced-fraction core of that assertion:
neither the numerator nor the denominator has a prime divisor.

Turning this into the full topological-group equivalence of Lemma 5.9 also
requires a product formula assembling the finitely many nonzero valuations of
a finite idèle into a rational number.  That compatibility is not currently
packaged for Mathlib's restricted-product finite adeles.
-/

namespace Submission.CField.Recip

/-- **Lemma V.5.9, arithmetic uniqueness step.** A positive rational whose
reduced numerator and denominator are divisible by no prime is `1`. -/
theorem positive_rational_units
    (q : ℚ) (hq : 0 < q)
    (hunit : ∀ p : ℕ, p.Prime →
      ¬p ∣ q.num.natAbs ∧ ¬p ∣ q.den) :
    q = 1 := by
  have hnumAbs : q.num.natAbs = 1 :=
    Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp ↦ (hunit p hp).1
  have hden : q.den = 1 :=
    Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp ↦ (hunit p hp).2
  have hnumPos : 0 < q.num := Rat.num_pos.mpr hq
  have hnum : q.num = 1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hnumAbs
    simpa [Int.natAbs_of_nonneg hnumPos.le] using hcast
  rw [← q.num_divInt_den, hnum, hden]
  exact Rat.divInt_one_one

/-- **Lemma V.5.9, p-adic uniqueness form.** A positive rational number whose
valuation at every finite prime is zero is `1`. -/
theorem positive_val_rat
    (q : ℚ) (hq : 0 < q)
    (hval : ∀ p : Nat.Primes, padicValRat p q = 0) :
    q = 1 := by
  apply positive_rational_units q hq
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hqnum : q.num ≠ 0 := Rat.num_ne_zero.mpr (ne_of_gt hq)
  have hv :
      (padicValInt p q.num : ℤ) = (padicValNat p q.den : ℤ) := by
    exact sub_eq_zero.mp (hval ⟨p, hp⟩)
  constructor
  · intro hpnum
    have hcop : p.Coprime q.den := q.reduced.of_dvd_left hpnum
    have hpden : ¬p ∣ q.den := hp.coprime_iff_not_dvd.mp hcop
    have hdenval : padicValNat p q.den = 0 :=
      padicValNat.eq_zero_of_not_dvd hpden
    have hnumval : padicValInt p q.num ≠ 0 := by
      intro hzero
      have hpnumInt : (p : ℤ) ∣ q.num := Int.natCast_dvd.mpr hpnum
      rcases padicValInt.eq_zero_iff.mp hzero with hpone | hnumzero | hpnot
      · exact hp.ne_one hpone
      · exact hqnum hnumzero
      · exact hpnot hpnumInt
    apply hnumval
    apply Int.ofNat_injective
    simpa [hdenval] using hv
  · intro hpden
    have hcop : q.num.natAbs.Coprime p := q.reduced.of_dvd_right hpden
    have hpnum : ¬p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop.symm
    have hnumval : padicValInt p q.num = 0 :=
      padicValInt.eq_zero_of_not_dvd (by simpa [Int.natCast_dvd] using hpnum)
    have hdenval : padicValNat p q.den ≠ 0 := by
      intro hzero
      rcases padicValNat.eq_zero_iff.mp hzero with hpone | hdenzero | hpnot
      · exact hp.ne_one hpone
      · exact q.den_nz hdenzero
      · exact hpnot hpden
    apply hdenval
    apply Int.ofNat_injective
    simpa [hnumval] using hv.symm

end Submission.CField.Recip
