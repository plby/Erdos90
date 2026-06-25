import Towers.NumberTheory.Density.ConjugacyInvariantDensity
import Towers.NumberTheory.Galois.DedekindDegreePartition
import Towers.NumberTheory.Ramification.KummerFactorization
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Densities of polynomial factorization patterns

This file joins the full-partition form of Dedekind's theorem to the
conjugacy-invariant form of Chebotarev.  The resulting prime sets are defined
by the literal multiset of degrees of the irreducible factors of a reduced
polynomial.
-/

namespace Towers.NumberTheory.Milne

open Equiv IsDedekindDomain NumberField Polynomial

noncomputable section

variable (K L : Type*) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

noncomputable local instance integralClosureDecidableEq :
    DecidableEq (𝓞 L) :=
  Classical.decEq _

/-- The natural action of `Gal(L/K)` on the integral roots of an integral
polynomial that splits in `L`. -/
noncomputable def integralRootAction (f : (𝓞 K)[X]) :
    Gal(L/K) →* Equiv.Perm (f.rootSet (𝓞 L)) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  exact MulAction.toPermHom Gal(L/K) (f.rootSet (𝓞 L))

/-- The literal multiset of degrees of the irreducible factors of `f`
modulo the finite prime `v`. -/
noncomputable def reductionDegrees
    (f : (𝓞 K)[X]) (v : HeightOneSpectrum (𝓞 K)) : Multiset ℕ :=
  reductionFactorDegrees f v.asIdeal

/-- The finite primes where the reduction of `f` has irreducible-factor
degree multiset `parts`. -/
def primesReductionDegrees
    (f : (𝓞 K)[X]) (parts : Multiset ℕ) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {v | reductionDegrees K f v = parts}

/-- The finite primes where the reduction of `f` is inseparable. -/
def inseparableReductionPrimes (f : (𝓞 K)[X]) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ¬(f.map (Ideal.Quotient.mk v.asIdeal)).Separable}

/-- The finite primes dividing the polynomial discriminant. -/
def polynomialDiscriminantPrimes (f : (𝓞 K)[X]) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {v | f.discr ∈ v.asIdeal}

/-- Every prime of inseparable reduction divides the polynomial
discriminant. -/
theorem inseparable_subset_discriminant
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree) :
    inseparableReductionPrimes K f ⊆ polynomialDiscriminantPrimes K f := by
  intro v hv
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  apply (discr_not_squarefree f hf hdegree).2
  have hv' : ¬(f.map (Ideal.Quotient.mk v.asIdeal)).Separable := by
    simpa only [inseparableReductionPrimes, Set.mem_setOf_eq] using hv
  simpa only [PerfectField.separable_iff_squarefree] using hv'

/-- A nonzero polynomial discriminant has only finitely many prime
divisors. -/
theorem polynomial_discriminant_primes
    (f : (𝓞 K)[X]) (hdisc : f.discr ≠ 0) :
    (polynomialDiscriminantPrimes K f).Finite := by
  apply (Ideal.finite_factors
    (I := Ideal.span {f.discr})
    (Ideal.span_singleton_eq_bot.not.mpr hdisc)).subset
  intro v hv
  apply Ideal.dvd_iff_le.mpr
  rw [Ideal.span_singleton_le_iff_mem]
  exact hv

/-- A monic separable polynomial has inseparable reduction at only finitely
many finite primes: every such prime divides its nonzero discriminant. -/
theorem inseparable_reduction_primes
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0) :
    (inseparableReductionPrimes K f).Finite := by
  exact (polynomial_discriminant_primes K f hdisc).subset
    (inseparable_subset_discriminant
      K f hf hdegree)

/-- At a prime of separable reduction, Dedekind identifies the literal
factor-degree multiset with the full partition of arithmetic Frobenius on
the integral roots. -/
theorem degrees_frobenius_partition
    (f : (𝓞 K)[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (v : HeightOneSpectrum (𝓞 K))
    (hsep : (f.map (Ideal.Quotient.mk v.asIdeal)).Separable) :
    reductionDegrees K f v =
      (conjugacyActionPartition
        (integralRootAction K L f)
        (arithmeticFrobeniusClass K L v)).parts := by
  classical
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  let P := arithmeticFrobeniusAbove K L v
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : P.1.IsPrime := P.2.1
  letI : P.1.IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance
      (Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2)
  letI : P.1.LiesOver v.asIdeal := P.2.2
  letI : Finite (𝓞 L ⧸ P.1) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2)
  letI : Algebra.IsAlgebraic (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ P.1) :=
    Algebra.IsAlgebraic.of_finite (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ P.1)
  have hpartition :=
    arithmetic_partition_degrees
      (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K))
      (p := v.asIdeal) (Q := P.1) f hf hsplits hsep
  change reductionFactorDegrees f v.asIdeal = _
  rw [← hpartition]
  have hclass : arithmeticFrobeniusClass K L v =
      ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) P.1) := by
    rfl
  rw [hclass, conjugacy_partition_mk]
  rfl

/-- Away from inseparable reductions, the literal factor-degree prime set is
exactly the corresponding arithmetic-Frobenius partition prime set. -/
theorem primes_diff_inseparable
    (f : (𝓞 K)[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (parts : Multiset ℕ) :
    primesReductionDegrees K f parts \
        inseparableReductionPrimes K f =
      primesFrobeniusPartition K
          (fun v => some (arithmeticFrobeniusClass K L v))
          (integralRootAction K L f) parts \
        inseparableReductionPrimes K f := by
  classical
  ext v
  by_cases hsep : (f.map (Ideal.Quotient.mk v.asIdeal)).Separable
  · have hbridge := degrees_frobenius_partition
      K L f hf hsplits v hsep
    simp [primesReductionDegrees, inseparableReductionPrimes,
      hsep, hbridge]
  · simp [primesReductionDegrees, inseparableReductionPrimes, hsep]

/-- Chebotarev's density formula for a literal irreducible-factor degree
pattern of a monic integral polynomial.  The only excluded local hypotheses
are the finite inseparable-reduction set and Chebotarev itself. -/
theorem primes_density_chebotarev
    (f : (𝓞 K)[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (parts : Multiset ℕ)
    (hbad : (inseparableReductionPrimes K f).Finite)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f parts)
      (((∑ C ∈ conjugacyClassesSatisfying
          (fun C : ConjClasses Gal(L/K) =>
            (conjugacyActionPartition
              (integralRootAction K L f) C).parts = parts),
        C.carrier.ncard : ℕ) : ℝ) / Nat.card Gal(L/K)) := by
  classical
  let frobeniusPrimes := primesFrobeniusPartition K
    (fun v => some (arithmeticFrobeniusClass K L v))
    (integralRootAction K L f) parts
  have hfrob : PNDensit K frobeniusPrimes
      (((∑ C ∈ conjugacyClassesSatisfying
          (fun C : ConjClasses Gal(L/K) =>
            (conjugacyActionPartition
              (integralRootAction K L f) C).parts = parts),
        C.carrier.ncard : ℕ) : ℝ) / Nat.card Gal(L/K)) := by
    exact partition_ratio_chebotarev
      K hcheb (integralRootAction K L f) parts
  have heq := primes_diff_inseparable
    K L f hf hsplits parts
  have hleft :
      (frobeniusPrimes \ primesReductionDegrees K f parts).Finite := by
    apply hbad.subset
    intro v hv
    by_contra hvbad
    have hvf : v ∈ frobeniusPrimes \ inseparableReductionPrimes K f :=
      ⟨hv.1, hvbad⟩
    rw [← heq] at hvf
    exact hv.2 hvf.1
  have hright :
      (primesReductionDegrees K f parts \ frobeniusPrimes).Finite := by
    apply hbad.subset
    intro v hv
    by_contra hvbad
    have hvr : v ∈ primesReductionDegrees K f parts \
        inseparableReductionPrimes K f := ⟨hv.1, hvbad⟩
    rw [heq] at hvr
    exact hv.2 hvr.1
  exact hfrob.congr_fin_diff K hleft hright

/-- Chebotarev's factorization-pattern formula with the finite exceptional
set discharged by the nonvanishing of the polynomial discriminant. -/
theorem primes_degrees_chebotarev
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (parts : Multiset ℕ)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f parts)
      (((∑ C ∈ conjugacyClassesSatisfying
          (fun C : ConjClasses Gal(L/K) =>
            (conjugacyActionPartition
              (integralRootAction K L f) C).parts = parts),
        C.carrier.ncard : ℕ) : ℝ) / Nat.card Gal(L/K)) :=
  primes_density_chebotarev
    K L f hf hsplits parts
      (inseparable_reduction_primes K f hf hdegree hdisc) hcheb

/-- The same factorization-pattern formula, written as the proportion of
individual Galois elements having the requested full root partition. -/
theorem degrees_density_chebotarev
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (parts : Multiset ℕ)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f parts)
      ((Nat.card {sigma : Gal(L/K) //
          ((integralRootAction K L f sigma).partition).parts = parts} : ℝ) /
        Nat.card Gal(L/K)) := by
  have h :=
    primes_degrees_chebotarev
      K L f hf hdegree hdisc hsplits parts hcheb
  rw [conjugacy_satisfying_ncard] at h
  simpa only [conjugacy_partition_mk] using h

/-- A permutation-representation model for the polynomial Galois action may
be used directly in the density formula.  Both the group equivalence and the
pointwise equality of full action partitions are recorded, since the abstract
group alone does not determine a root action. -/
theorem degrees_equivalent_action
    {G : Type*} [Group G] [Finite G]
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (rho : G →* Equiv.Perm alpha) (e : Gal(L/K) ≃* G)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((rho (e sigma)).partition).parts)
    (parts : Multiset ℕ)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f parts)
      ((Nat.card {g : G // ((rho g).partition).parts = parts} : ℝ) /
        Nat.card G) := by
  have h := degrees_density_chebotarev
    K L f hf hdegree hdisc hsplits parts hcheb
  have hnum := nat_action_partition
    (integralRootAction K L f) rho e hparts parts
  have hden : Nat.card Gal(L/K) = Nat.card G := Nat.card_congr e.toEquiv
  rw [hnum, hden] at h
  exact h

/-- Numerical form of the equivalent-action formula, after supplying the
order of the model group and the number of elements of the selected full
partition type. -/
theorem degrees_density_equivalent
    {G : Type*} [Group G] [Finite G]
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (f : (𝓞 K)[X]) (hf : f.Monic) (hdegree : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0)
    (hsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (rho : G →* Equiv.Perm alpha) (e : Gal(L/K) ≃* G)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((rho (e sigma)).partition).parts)
    (parts : Multiset ℕ) (count order : ℕ)
    (hcount : Nat.card {g : G //
      ((rho g).partition).parts = parts} = count)
    (horder : Nat.card G = order)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f parts)
      ((count : ℝ) / order) := by
  simpa only [hcount, horder] using
    (degrees_equivalent_action
      K L f hf hdegree hdisc hsplits rho e hparts parts hcheb)

end

end Towers.NumberTheory.Milne
