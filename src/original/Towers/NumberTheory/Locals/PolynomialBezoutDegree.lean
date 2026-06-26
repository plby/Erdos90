import Towers.NumberTheory.Locals.LocalPolynomialCoprime

/-!
# Degree-bounded Bezout identities over a local ring

This completes the degree-bounded form of Milne's Lemma 7.34.  The
Sylvester-matrix identity expresses the resultant as a polynomial linear
combination with the required degree bounds; coprimality makes the resultant
a unit, so the identity can be normalized to equal one.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

section


variable {A : Type*} [CommRing A] [Nontrivial A]

/-- Monic coprime polynomials, not both constant, have a Bezout identity
whose coefficients have the standard strict degree bounds. -/
theorem bezout_degree_monic
    {f g : A[X]} (hf : f.Monic) (hg : g.Monic)
    (hcoprime : IsCoprime f g)
    (hdegree : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    ∃ a b : A[X],
      a.degree < g.degree ∧ b.degree < f.degree ∧
        a * f + b * g = 1 := by
  have hresultant : IsUnit (resultant f g) :=
    (isUnit_resultant_iff_isCoprime hf).2 hcoprime
  obtain ⟨p, q, hp, hq, heq⟩ :=
    exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hdegree
  refine ⟨C (hresultant.unit⁻¹).1 * p, C (hresultant.unit⁻¹).1 * q, ?_, ?_, ?_⟩
  · rw [degree_C_mul_of_isUnit (hresultant.unit⁻¹).isUnit]
    simpa [degree_eq_natDegree hg.ne_zero] using hp
  · rw [degree_C_mul_of_isUnit (hresultant.unit⁻¹).isUnit]
    simpa [degree_eq_natDegree hf.ne_zero] using hq
  · simp only [mul_assoc, ← mul_add, mul_comm p, mul_comm q, heq, ← map_mul,
      IsUnit.val_inv_mul, map_one]

variable [IsLocalRing A]

/-- Milne, Lemma 7.34: a coprime factorization over the residue field lifts
to a degree-bounded Bezout identity over the local ring. -/
theorem bezout_monic_coprime
    {f g : A[X]} (hf : f.Monic) (hg : g.Monic)
    (hcoprime : IsCoprime
      (f.map (IsLocalRing.residue A)) (g.map (IsLocalRing.residue A)))
    (hdegree : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    ∃ a b : A[X],
      a.degree < g.degree ∧ b.degree < f.degree ∧
        a * f + b * g = 1 := by
  exact bezout_degree_monic hf hg
    (coprime_monic_residue hf hg hcoprime) hdegree

end


end Towers.NumberTheory.Milne
