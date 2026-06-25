import Submission.NumberTheory.Dedekind.DedekindLocalizations

/-!
# Milne, Algebraic Number Theory, Remark 3.25

For a noetherian domain, the local-DVR condition, invertibility of every nonzero
fractional ideal, and the Dedekind condition are equivalent.
-/

namespace Submission.NumberTheory.Milne

open scoped nonZeroDivisors

/-- Remark 3.25(a),(b): for a noetherian domain, being Dedekind is equivalent to all
localizations at nonzero prime ideals being discrete valuation rings. -/
theorem dedekind_localizations_dvr
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    IsDedekindDomain A ↔
      ∀ (P : Ideal A) (_ : P ≠ ⊥) [P.IsPrime],
        IsDiscreteValuationRing (Localization.AtPrime P) := by
  constructor
  · intro hDedekind
    exact
      (dedekind_domain_discrete A).mp hDedekind |>.2
  · intro hLocal
    exact
      (dedekind_domain_discrete A).mpr
        ⟨inferInstance, hLocal⟩

/-- Remark 3.25(a),(c): a domain is Dedekind exactly when every nonzero fractional
ideal satisfies the inverse identity. This includes Noether's converse. -/
theorem dedekind_ideals_invertible
    (A K : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      ∀ I : FractionalIdeal A⁰ K, I ≠ 0 → I * I⁻¹ = 1 := by
  rw [isDedekindDomain_iff_isDedekindDomainInv,
    isDedekindDomainInv_iff (K := K)]
  rfl

/-- Remark 3.25(a),(d): a domain is Dedekind exactly when every nonzero fractional
ideal admits a multiplicative inverse. -/
theorem dedekind_every_fractional
    (A K : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      ∀ I : FractionalIdeal A⁰ K, I ≠ 0 → ∃ J, I * J = 1 := by
  constructor
  · intro hDedekind
    letI : IsDedekindDomain A := hDedekind
    intro I hI
    exact ⟨I⁻¹, mul_inv_cancel₀ hI⟩
  · intro h
    rw [isDedekindDomain_iff_isDedekindDomainInv,
      isDedekindDomainInv_iff (K := K)]
    intro I hI
    exact (FractionalIdeal.mul_inv_cancel_iff K).mpr (h I hI)

end Submission.NumberTheory.Milne
