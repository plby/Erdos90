import Submission.ClassField.FormalGroups.LubinTateExamples

/-!
# Class Field Theory, Chapter I, Definition 2.9

This file packages the elementary defining conditions for Milne's set
`\mathcal F_\pi` of Lubin--Tate power series and verifies Examples 2.10(a,b).
-/

namespace Submission.CField.FGroups

open Polynomial

noncomputable section

/-- Milne's set `\mathcal F_\pi` from Definition 2.9.  The first two
coefficient equations express `f(X) = \pi X +` terms of degree at least two;
the final equation expresses reduction to `X^q` modulo `\pi`. -/
def LubinSeries {R : Type*} [CommRing R]
    (pi : R) (q : ℕ) (f : PowerSeries R) : Prop :=
  PowerSeries.coeff 0 f = 0 ∧
    PowerSeries.coeff 1 f = pi ∧
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {pi})) f =
        PowerSeries.X ^ q

/-- Example 2.10(a): `\pi X + X^q` is a Lubin--Tate series when `q > 1`. -/
theorem lubin_tate_basic
    {R : Type*} [CommRing R] [Nontrivial R]
    (pi : R) {q : ℕ} (hq : 1 < q) :
    LubinSeries pi q
      (basicLubinTate pi q : PowerSeries R) := by
  constructor
  · simp [basicLubinTate, Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)]
  constructor
  · simpa using basic_lubin_tate pi hq
  · rw [← Polynomial.polynomial_map_coe]
    rw [basic_lubin_span]
    simp

/-- Example 2.10(b): `(1+X)^p-1` belongs to `\mathcal F_p`. -/
theorem lubin_series_cyclotomic
    (p : ℕ) [Fact p.Prime] :
    LubinSeries (p : ℤ) p
      (cyclotomicLubinTate p : PowerSeries ℤ) := by
  constructor
  · simp
  constructor
  · simp
  · apply PowerSeries.map_injective
      (Int.quotientSpanNatEquivZMod p).toRingHom
      (Int.quotientSpanNatEquivZMod p).injective
    change
      ((PowerSeries.map (Int.quotientSpanNatEquivZMod p).toRingHom).comp
          (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))))
            (cyclotomicLubinTate p : PowerSeries ℤ) =
        PowerSeries.map (Int.quotientSpanNatEquivZMod p).toRingHom
          (PowerSeries.X ^ p)
    rw [← PowerSeries.map_comp]
    have hcomp :
        (Int.quotientSpanNatEquivZMod p).toRingHom.comp
            (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) =
          Int.castRingHom (ZMod p) :=
      Int.quotientSpanNatEquivZMod_comp_Quotient_mk p
    rw [hcomp]
    rw [map_pow, PowerSeries.map_X]
    rw [← Polynomial.polynomial_map_coe]
    rw [cyclotomic_lubin_prime]
    simp

end

end Submission.CField.FGroups
