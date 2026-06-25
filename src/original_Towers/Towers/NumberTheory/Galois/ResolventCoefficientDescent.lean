import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Coefficient descent for Galois resolvents

This file isolates the elementary descent step in Milne's Theorem 8.20.
If a multivariate polynomial over a Galois extension is fixed by the
coefficientwise Galois action, then all of its coefficients come from the
base field.  The same statement is then applied coefficientwise to a
univariate polynomial whose coefficients are multivariate polynomials.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable {G K L ι : Type*} [Group G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The coefficientwise action on a multivariate polynomial, with all
variables fixed. -/
def mvCoefficientwiseS
    (g : G) (q : MvPolynomial ι L) : MvPolynomial ι L :=
  MvPolynomial.map (MulSemiringAction.toRingHom G L g) q

@[simp]
theorem mv_coefficientwise_s
    (g : G) (q : MvPolynomial ι L) (d : ι →₀ ℕ) :
    MvPolynomial.coeff d (mvCoefficientwiseS g q) =
      g • MvPolynomial.coeff d q := by
  simp [mvCoefficientwiseS, MvPolynomial.coeff_map]

/-- A coefficientwise Galois-fixed multivariate polynomial descends to the
base field. -/
theorem mv_polynomial_coefficientwise
    (q : MvPolynomial ι L)
    (hfixed : ∀ g : G, mvCoefficientwiseS g q = q) :
    ∃ q₀ : MvPolynomial ι K,
      MvPolynomial.map (algebraMap K L) q₀ = q := by
  rw [← Set.mem_range, MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨d, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  have hcoeff : ∀ g : G, g • MvPolynomial.coeff d q =
      MvPolynomial.coeff d q := by
    intro g
    have h := congrArg (MvPolynomial.coeff d) (hfixed g)
    simpa using h
  exact Algebra.IsInvariant.isInvariant
    (A := K) (B := L) (G := G) (MvPolynomial.coeff d q) hcoeff

/-- A univariate polynomial with coefficientwise Galois-fixed multivariate
coefficients descends to the corresponding polynomial ring over the base
field. -/
theorem mv_coefficientwise_fixed
    (F : (MvPolynomial ι L)[X])
    (hfixed : ∀ g : G,
      F.map (MvPolynomial.map (MulSemiringAction.toRingHom G L g)) = F) :
    ∃ F₀ : (MvPolynomial ι K)[X],
      F₀.map (MvPolynomial.map (algebraMap K L)) = F := by
  rw [← Polynomial.mem_lifts]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  obtain ⟨q₀, hq₀⟩ :=
    mv_polynomial_coefficientwise
      (G := G) (K := K) (L := L) (ι := ι) (F.coeff n) (by
      intro g
      have h := congrArg (Polynomial.coeff · n) (hfixed g)
      simpa only [Polynomial.coeff_map] using h)
  exact ⟨q₀, hq₀⟩

end

end Towers.NumberTheory.Milne
