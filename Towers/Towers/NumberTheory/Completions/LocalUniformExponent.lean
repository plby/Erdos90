import Towers.NumberTheory.Completions.TotallyRamifiedBound
import Towers.NumberTheory.Completions.AdicLocalRing
import Towers.NumberTheory.Completions.LocalTowerBound
import Mathlib.RingTheory.DedekindDomain.Dvr


/-!
# One local-different exponent for a finite set of primes

The explicit local different bound depends on the normalized valuation of
`N!` at the base prime.  For a finite ramification set, taking the finite
supremum gives the single exponent required by the global Hermite argument.
-/

namespace Towers.NumberTheory.Milne

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero R]

/-- The explicit local exponent at one nonzero prime of a Dedekind domain. -/
noncomputable def differentExponentIdeal
    (p : Ideal R) (hp : p.IsPrime) (hp0 : p ≠ ⊥) (N : ℕ) : ℕ := by
  letI : p.IsPrime := hp
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R hp0 (Localization.AtPrime p)
  letI : CharZero (Localization.AtPrime p) :=
    CharZero.of_addMonoidHom
      (algebraMap R (Localization.AtPrime p)).toAddMonoidHom
      (by simp)
      (IsLocalization.injective (Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  exact N *
    (dvrCastValuation (Localization.AtPrime p) N.factorial + 1)

/-- A single exponent dominating the explicit local exponents at every
prime in a finite set. -/
noncomputable def differentExponentBound
    (S : Finset (Ideal R))
    (hprime : ∀ p ∈ S, p.IsPrime) (hne : ∀ p ∈ S, p ≠ ⊥)
    (N : ℕ) : ℕ :=
  S.attach.sup fun p => differentExponentIdeal (R := R) (p : Ideal R)
    (hprime p p.2) (hne p p.2) N

theorem different_exponent_bound
    (S : Finset (Ideal R))
    (hprime : ∀ p ∈ S, p.IsPrime) (hne : ∀ p ∈ S, p ≠ ⊥)
    (N : ℕ) {p : Ideal R} (hp : p ∈ S) :
    differentExponentIdeal (R := R) p (hprime p hp) (hne p hp) N ≤
      differentExponentBound S hprime hne N := by
  classical
  unfold differentExponentBound
  have hle := Finset.le_sup (f := fun q : S =>
      differentExponentIdeal (R := R) (q : Ideal R)
        (hprime q q.2) (hne q q.2) N)
    (S.mem_attach ⟨p, hp⟩)
  simpa only [Subtype.coe_mk] using hle

set_option synthInstance.maxHeartbeats 200000 in
-- The completed valuation-ring DVR and torsion-free instances unfold deeply.
omit [CharZero R] in
/-- Completing the local ring at a height-one prime does not change the
normalized valuation of a natural number. -/
theorem dvr_valuation_integers
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (v : IsDedekindDomain.HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)]
    [CharZero (Localization.AtPrime v.asIdeal)]
    [CharZero (v.adicCompletionIntegers K)] (n : ℕ) :
    dvrCastValuation (v.adicCompletionIntegers K) n =
      dvrCastValuation (Localization.AtPrime v.asIdeal) n := by
  let A := Localization.AtPrime v.asIdeal
  let B := v.adicCompletionIntegers K
  let f : A →+* B := primeAdicIntegers (K := K) v
  letI : Algebra A B := f.toAlgebra
  letI : Module.IsTorsionFree A B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact adic_integers_injective (K := K) v
  apply dvr_valuation_maximal A B
  exact maximal_completion_integers (K := K) v

end

end Towers.NumberTheory.Milne
