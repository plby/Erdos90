import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral

/-!
# Milne, Chapter 2, integral-closure facts

This file records Propositions 2.6--2.9 and 2.13--2.17 in the notation of
Mathlib's integral-closure API.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Proposition 2.6: an element algebraic over the fraction field has
a nonzero multiple integral over the original domain. -/
theorem nonzero_integral_multiple
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L] (x : L) :
    ∃ d : A, d ≠ 0 ∧ IsIntegral A (algebraMap A L d * x) := by
  letI : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := K) (C := L)).mpr inferInstance
  obtain ⟨d, hd, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := A) x).exists_integral_multiple
  exact ⟨d, hd, by simpa only [Algebra.smul_def] using hint⟩

/-- Milne, Corollary 2.7: in an algebraic field extension, the ambient field
is the fraction field of the integral closure. -/
theorem integral_fraction_algebraic
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L] :
    IsFractionRing (integralClosure A L) L := by
  letI : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := K) (C := L)).mpr inferInstance
  have hinj : ∀ x, algebraMap A L x = 0 → x = 0 := by
    intro x hx
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [map_zero, IsScalarTower.algebraMap_apply A K L] using hx
  exact integralClosure.isFractionRing_of_algebraic
    (A := A) (L := L) hinj

/-- Milne, Proposition 2.9: every unique factorization domain is integrally
closed. -/
theorem integrally_unique_monoid
    (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] :
    IsIntegrallyClosed A := by
  infer_instance

/-- **Milne, Example 2.10(a).** The rational integers form a principal ideal
ring. -/
theorem integers_principal_ring :
    IsPrincipalIdealRing ℤ := by
  infer_instance

/-- **Milne, Example 2.10(a).** The rational integers are integrally closed,
as a consequence of unique factorization. -/
theorem integers_integrally :
    IsIntegrallyClosed ℤ :=
  integrally_unique_monoid ℤ

/-- **Milne, Example 2.10(a).** The Gaussian integers form a principal ideal
ring. -/
theorem integral_factsgaussian_ring :
    IsPrincipalIdealRing GaussianInt := by
  infer_instance

/-- **Milne, Example 2.10(a).** The Gaussian integers are integrally closed,
as a consequence of their Euclidean-domain structure. -/
theorem gaussian_integrally_closed :
    IsIntegrallyClosed GaussianInt :=
  integrally_unique_monoid GaussianInt

/-- Milne, Proposition 2.13: an integral algebra of finite type is finite as
a module. -/
theorem module_integral_type
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Algebra.FiniteType A B] :
    Module.Finite A B :=
  Algebra.IsIntegral.finite

/-- Milne, Lemma 2.14: module-finiteness is transitive in an algebra tower. -/
theorem moduleFinite_trans
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] :
    Module.Finite A C :=
  Module.Finite.trans B C

/-- Milne, Proposition 2.15: integrality is transitive in an algebra tower. -/
theorem algebra_integral_trans
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] :
    Algebra.IsIntegral A C :=
  Algebra.IsIntegral.trans B

/-- Milne, Corollary 2.16: the integral closure in an algebraic extension of
the fraction field is integrally closed. -/
theorem integrally_closed_algebraic
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L] :
    IsIntegrallyClosed (integralClosure A L) := by
  letI : IsFractionRing (integralClosure A L) L :=
    integral_fraction_algebraic A K L
  exact (IsIntegrallyClosed.integralClosure_eq_bot_iff L).mp
    integralClosure_idem

/-- Milne, Remark 2.17: the ring of integers of a number field is
integrally closed. -/
theorem integers_integrally_closed
    (K : Type*) [Field K] [NumberField K] :
    IsIntegrallyClosed (NumberField.RingOfIntegers K) := by
  infer_instance

/-- Exercise 2-7: taking integral closure commutes with localization.  Here `Rf` is the
localization of `R` at `M`, and `Sf` is the corresponding localization of `S`; consequently
the integral closure of `Rf` in `Sf` is the localization of the integral closure of `R` in
`S`. -/
theorem integral_closure_localization
    {R S Rf Sf : Type*} [CommRing R] [CommRing S]
    [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf]
    [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R)
    [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) :=
  IsLocalization.integralClosure M

end Submission.NumberTheory.Milne
