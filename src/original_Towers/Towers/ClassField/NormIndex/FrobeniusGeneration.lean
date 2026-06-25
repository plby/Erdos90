import Towers.ClassField.PrimeDensities.Density

/-!
# Chapter VII, Section 4: Frobenius generation

The faithful algebraic proofs of Theorem 4.3 through Corollary 4.8 are in the
neighboring source-statement files.  This file records a complementary,
stronger consequence of Chapter VI's conditional Chebotarev interface in the
abelian case: every element occurs at infinitely many primes, hence still
occurs after any finite exceptional set is removed.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable {G : Type*} [CommGroup G] [Finite G]

/-- The Galois elements represented by Frobenius classes outside a prescribed
exceptional set of primes.  For an abelian group a conjugacy class determines
its unique element. -/
def FrobeniusElementsOutside
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (T : Set (HeightOneSpectrum (𝓞 K))) : Set G :=
  {sigma | ∃ p, p ∉ T ∧ frobeniusClass p = some (ConjClasses.mk sigma)}

/-- **Proposition VII.4.6, Chebotarev abelian form.** A nonidentity
Frobenius class occurs at infinitely many primes. -/
theorem nonidentity_primes_infinite
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (sigma : G) (_hsigma : sigma ≠ 1) :
    (primesFrobeniusClass K frobeniusClass
      (ConjClasses.mk sigma)).Infinite := by
  apply Set.Infinite.prime_ideal_densi K
    (abelian_density_chebotarev K hcheb sigma)
  exact one_div_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)

/-- Every abelian Frobenius element occurs outside any finite exceptional set.
This is the finite-set refinement used in Proposition 4.7 and Corollary 4.8. -/
theorem frobenius_occurs_outside
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (sigma : G) :
    sigma ∈ FrobeniusElementsOutside K frobeniusClass T := by
  have hinfinite :
      (primesFrobeniusClass K frobeniusClass
        (ConjClasses.mk sigma)).Infinite := by
    apply Set.Infinite.prime_ideal_densi K
      (abelian_density_chebotarev K hcheb sigma)
    exact one_div_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  rcases (hinfinite.diff hT).nonempty with ⟨p, hp, hpT⟩
  exact ⟨p, hpT, hp⟩

/-- Under Chebotarev, the Frobenius elements outside a finite set exhaust the
abelian Galois group. -/
theorem elements_outside_univ
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    FrobeniusElementsOutside K frobeniusClass T = Set.univ := by
  apply Set.eq_univ_of_forall
  exact frobenius_occurs_outside K hcheb hT

/-- **Proposition VII.4.7 and Corollary VII.4.8, Chebotarev abelian form.**
The Frobenius elements away from a finite exceptional set generate the whole
Galois group. -/
theorem elements_outside_top
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    Subgroup.closure (FrobeniusElementsOutside K frobeniusClass T) = ⊤ := by
  rw [elements_outside_univ K hcheb hT]
  exact Subgroup.closure_univ

end

end Towers.CField.NIndex
