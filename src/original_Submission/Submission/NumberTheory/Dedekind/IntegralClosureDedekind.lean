import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Milne, Algebraic Number Theory, Theorem 3.29 and Lemma 3.30

The integral closure of a Dedekind domain in a finite separable extension of its fraction
field is again Dedekind. We also record the field criterion used in Milne's proof.
-/

namespace Submission.NumberTheory.Milne

universe u v w

/-- Theorem 3.29: the integral closure of a Dedekind domain in a finite separable
extension of its fraction field is a Dedekind domain. -/
theorem integral_dedekind_domain
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] :
    IsDedekindDomain B := by
  exact IsIntegralClosure.isDedekindDomain A K L B

/-- Lemma 3.30: an integral domain algebraic over a field is itself a field. -/
theorem field_domain_algebraic
    (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.IsAlgebraic k B] :
    IsField B := by
  exact (Algebra.IsIntegral.isField_iff_isField
    (FaithfulSMul.algebraMap_injective k B)).mp (Field.toIsField k)

/-- The source-delegated strengthening immediately after Theorem 3.29: separability can be
dropped.  Milne cites Janusz, I.6.1, and does not give the substantially harder noetherianity
argument. -/
def IntegralDedekindTheorem : Prop :=
  ∀ (A : Type u) (K : Type v) (L : Type w) (B : Type w)
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L],
    IsDedekindDomain B

/-- Fieldwise access to the arbitrary finite-extension strengthening of Theorem 3.29. -/
theorem dedekind_domain_extension
    (hgeneral : IntegralDedekindTheorem.{u, v, w})
    (A : Type u) (K : Type v) (L B : Type w)
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] :
    IsDedekindDomain B :=
  hgeneral A K L B

end Submission.NumberTheory.Milne
