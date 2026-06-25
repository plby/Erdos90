import Towers.NumberTheory.Ramification.DiscriminantModIdeal
import Towers.NumberTheory.Ramification.ReducedDiscriminant
import Towers.NumberTheory.Dedekind.NumberFieldOverrings
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Milne, Algebraic Number Theory, Theorem 3.35: ramification and discriminants

We prove Milne's discriminant criterion by reducing a basis modulo a prime. The reduced algebra
has nonzero discriminant exactly when it is reduced, and its defining ideal is radical exactly
when every prime above the base prime occurs with ramification index one. We also record the
corresponding local criterion in terms of the different ideal.
-/

namespace Towers.NumberTheory.Milne

open nonZeroDivisors
open Module
open UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra

/-- In a Dedekind domain, an ideal is radical in the ideal-theoretic sense exactly when it is a
radical element of the unique-factorization monoid of ideals. -/
theorem ideal_radical_monoid
    {R : Type*} [CommRing R] [IsDedekindDomain R] (I : Ideal R) :
    I.IsRadical ↔ IsRadical I := by
  constructor
  · intro hI n J hIJ
    rw [Ideal.dvd_iff_le] at hIJ ⊢
    intro x hx
    apply hI
    exact ⟨n, hIJ (Ideal.pow_mem_pow hx n)⟩
  · intro hI x hx
    rcases hx with ⟨n, hxn⟩
    have hpow : I ∣ (Ideal.span {x}) ^ n := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow,
        Ideal.span_le, Set.singleton_subset_iff]
      exact hxn
    have hspan : I ∣ Ideal.span {x} := hI n _ hpow
    exact (Ideal.span_singleton_le_iff_mem I).mp (Ideal.dvd_iff_le.mp hspan)

/-- The extension of a nonzero prime is radical exactly when every prime above it has
ramification index one. -/
theorem radical_ramification_idx
    {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    (p.map (algebraMap A B)).IsRadical ↔
      ∀ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P = 1 := by
  classical
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  have hmap : p.map (algebraMap A B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp
  rw [ideal_radical_monoid,
    isRadical_iff_squarefree_of_ne_zero hmap,
    UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap,
    Multiset.nodup_iff_count_le_one]
  constructor
  · intro h P hP
    have hPmem : P ∈ normalizedFactors (p.map (algebraMap A B)) :=
      (Ideal.mem_primesOver_iff_mem_normalizedFactors B hp).mp hP
    have hPfacts := (Ideal.mem_normalizedFactors_iff hmap).mp hPmem
    have hPprime : P.IsPrime := hPfacts.1
    have hP0 : P ≠ ⊥ := by
      intro hbot
      subst P
      exact hmap (eq_bot_iff.mpr hPfacts.2)
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      hmap hPprime hP0]
    exact Nat.le_antisymm (h P) (Multiset.count_pos.mpr hPmem)
  · intro h P
    by_cases hPmem : P ∈ normalizedFactors (p.map (algebraMap A B))
    · have hPfacts := (Ideal.mem_normalizedFactors_iff hmap).mp hPmem
      have hPprime : P.IsPrime := hPfacts.1
      have hP0 : P ≠ ⊥ := by
        intro hbot
        subst P
        exact hmap (eq_bot_iff.mpr hPfacts.2)
      have hPO : P ∈ Ideal.primesOver p B :=
        (Ideal.mem_primesOver_iff_mem_normalizedFactors B hp).mpr hPmem
      rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        hmap hPprime hP0]
      exact (h P hPO).le
    · simp [Multiset.count_eq_zero.mpr hPmem]

/-- **Theorem 3.35.** A nonzero prime with finite residue field divides the discriminant of a
finite free Dedekind extension exactly when some prime above it has nontrivial ramification
index. -/
theorem discr_ramification_ne
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsPrime] [Finite (A ⧸ p)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B) (hp : p ≠ ⊥) :
    Algebra.discr A b ∈ p ↔
      ∃ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P ≠ 1 := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  letI : Module.Free A B := Module.Free.of_basis b
  letI : Module.Finite A B := Module.Finite.of_basis b
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : PerfectField (A ⧸ p) := inferInstance
  letI : Module.Free (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
    Module.Free.of_basis (basisModIdeal A b p)
  letI : Module.Finite (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
    Module.Finite.of_basis (basisModIdeal A b p)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [← discr_modIdeal A B b p]
  rw [← not_iff_not]
  simp only [not_exists, not_and, not_not]
  change Algebra.discr (A ⧸ p) (basisModIdeal A b p) ≠ 0 ↔
    ∀ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P = 1
  rw [← reduced_discr_ne (A ⧸ p)
    (B ⧸ p.map (algebraMap A B)) (basisModIdeal A b p)]
  rw [← Ideal.isRadical_iff_quotient_reduced]
  rw [radical_ramification_idx hp]

/-- The arithmetic-order specialization of Theorem 3.35. Finiteness over `ℤ` supplies the
finite residue field used in the proof. -/
theorem discr_ramification_idx
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite ℤ A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B)
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.discr A b ∈ p ↔
      ∃ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P ≠ 1 := by
  letI : AddGroup.FG A := Module.Finite.iff_addGroup_fg.mp inferInstance
  letI : Ring.HasFiniteQuotients A := inferInstance
  letI : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  exact discr_ramification_ne A B b hp

/-- **Theorem 3.35, number-field form.** For an arbitrary Dedekind domain in a number field
having that number field as its fraction field, a nonzero prime divides the discriminant exactly
when some prime above it has nontrivial ramification index.  This includes infinite localizations
of the ring of integers. -/
theorem discr_ramification_fraction
    (A K B : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [NumberField K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B)
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.discr A b ∈ p ↔
      ∃ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P ≠ 1 := by
  letI : Finite (A ⧸ p) :=
    fraction_number_field (K := K) p hp
  exact discr_ramification_ne A B b hp

/-- The local lower-bound ingredient in Remark 3.39(a): at a prime upstairs, the different
contains the `(e - 1)`st power of that prime, where `e` is its ramification index. -/
theorem ramification_different_ideal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) (P : Ideal B) :
    P ^ (Ideal.ramificationIdx p P - 1) ∣ differentIdeal A B := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  apply pow_sub_one_dvd_differentIdeal A P (Ideal.ramificationIdx p P) hp
  exact Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx

/-- Remark 3.39(a), locally at a prime upstairs: the exponent of the different is at least
`e - 1`. -/
theorem ramification_idx_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) (P : Ideal B) (hP : P.IsPrime) :
    Ideal.ramificationIdx p P - 1 ≤ multiplicity P (differentIdeal A B) := by
  have hfin : FiniteMultiplicity P (differentIdeal A B) :=
    FiniteMultiplicity.of_not_isUnit
      (by simpa only [Ideal.isUnit_iff] using hP.ne_top)
      differentIdeal_ne_bot
  exact hfin.le_multiplicity_of_pow_dvd
    (ramification_different_ideal A B hp P)

/-- The contribution `f(P/p) * (e(P/p) - 1)` in Remark 3.39(a) occurs in the relative
norm of the different. This is the prime-by-prime input to Milne's displayed sum. -/
theorem contribution_rel_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [PerfectField (FractionRing A)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    p ^ ((Ideal.ramificationIdx p P - 1) * Ideal.inertiaDeg p P) ∣
      Ideal.relNorm A (differentIdeal A B) := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP0
  have h := map_dvd (Ideal.relNorm A)
    (ramification_different_ideal A B hp P)
  rw [map_pow, Ideal.relNorm_eq_pow_of_isMaximal P p] at h
  simpa only [pow_mul, Nat.mul_comm] using h

/-- Remark 3.39(a): the exponent of a prime in the relative norm of the different is at
least the sum of the tame lower bounds `f(P/p) * (e(P/p) - 1)` over the primes above it. -/
theorem contributions_rel_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [PerfectField (FractionRing A)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    (∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        Ideal.inertiaDeg p P * (Ideal.ramificationIdx p P - 1)) ≤
      multiplicity p (Ideal.relNorm A (differentIdeal A B)) := by
  classical
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  let s := IsDedekindDomain.primesOverFinset p B
  let D := differentIdeal A B
  have hprod :
      (∏ P ∈ s, P ^ (Ideal.ramificationIdx p P - 1)) ∣ D := by
    apply Finset.prod_dvd_of_coprime
    · intro P hPs Q hQs hPQ
      have hPover : P ∈ Ideal.primesOver p B :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp B).mp hPs
      have hQover : Q ∈ Ideal.primesOver p B :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp B).mp hQs
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPover
      have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hQover
      letI : P.IsMaximal := hPover.1.isMaximal hP0
      letI : Q.IsMaximal := hQover.1.isMaximal hQ0
      exact (Ideal.isCoprime_of_isMaximal hPQ).pow
    · intro P hPs
      exact ramification_different_ideal A B hp P
  have hnorm :
      p ^ (∑ P ∈ s,
          Ideal.inertiaDeg p P * (Ideal.ramificationIdx p P - 1)) ∣
        Ideal.relNorm A D := by
    have h := map_dvd (Ideal.relNorm A) hprod
    have hnormPrime : ∀ P ∈ s,
        Ideal.relNorm A P = p ^ Ideal.inertiaDeg p P := by
      intro P hPs
      have hPover : P ∈ Ideal.primesOver p B :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp B).mp hPs
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPover
      letI : P.IsMaximal := hPover.1.isMaximal hP0
      letI : P.LiesOver p := hPover.2
      exact Ideal.relNorm_eq_pow_of_isMaximal P p
    rw [map_prod] at h
    have hprodNorm :
        (∏ P ∈ s, Ideal.relNorm A (P ^ (Ideal.ramificationIdx p P - 1))) =
          p ^ (∑ P ∈ s,
            Ideal.inertiaDeg p P * (Ideal.ramificationIdx p P - 1)) := by
      calc
        _ = ∏ P ∈ s,
              (Ideal.relNorm A P) ^ (Ideal.ramificationIdx p P - 1) := by
            apply Finset.prod_congr rfl
            intro P hPs
            rw [map_pow]
        _ = ∏ P ∈ s,
              (p ^ Ideal.inertiaDeg p P) ^ (Ideal.ramificationIdx p P - 1) := by
            apply Finset.prod_congr rfl
            intro P hPs
            rw [hnormPrime P hPs]
        _ = ∏ P ∈ s,
              p ^ (Ideal.inertiaDeg p P * (Ideal.ramificationIdx p P - 1)) := by
            simp only [pow_mul]
        _ = _ := Finset.prod_pow_eq_pow_sum s _ p
    rwa [hprodNorm] at h
  have hfinite : FiniteMultiplicity p (Ideal.relNorm A D) :=
    FiniteMultiplicity.of_not_isUnit
      (by simpa only [Ideal.isUnit_iff] using
        (inferInstance : p.IsPrime).ne_top)
      (Ideal.relNorm_eq_bot_iff.not.mpr (by
        simpa only [D] using (differentIdeal_ne_bot : differentIdeal A B ≠ ⊥)))
  simpa only [s, D] using hfinite.le_multiplicity_of_pow_dvd hnorm

/-- A prime divides the relative norm of a nonzero ideal exactly when some prime above it
divides the original ideal. -/
theorem dvd_rel_norm
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [PerfectField (FractionRing A)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) {I : Ideal B} (hI : I ≠ ⊥) :
    p ∣ Ideal.relNorm A I ↔
      ∃ P ∈ Ideal.primesOver p B, P ∣ I := by
  classical
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  have hpPrime : Prime p := Ideal.prime_of_isPrime hp inferInstance
  constructor
  · intro hpNorm
    have hnormFactors :
        Ideal.relNorm A I =
          ((normalizedFactors I).map (Ideal.relNorm A)).prod := by
      rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    rw [hnormFactors] at hpNorm
    obtain ⟨P, hPfactor, hpNormP⟩ :=
      hpPrime.exists_mem_multiset_map_dvd hpNorm
    have hPdata := (Ideal.mem_normalizedFactors_iff hI).mp hPfactor
    have hP0 : P ≠ ⊥ := by
      intro hPbot
      subst P
      exact hI (eq_bot_iff.mpr hPdata.2)
    letI : P.IsPrime := hPdata.1
    letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP0
    let q := P.under A
    have hq0 : q ≠ ⊥ := Ideal.under_ne_bot A hP0
    have hqPrime : q.IsPrime := (inferInstance : P.IsPrime).under A
    letI : q.IsPrime := hqPrime
    letI : q.IsMaximal := hqPrime.isMaximal hq0
    have hPoverQ : P.LiesOver q := by
      simp [Ideal.liesOver_iff, q]
    letI : P.LiesOver q := hPoverQ
    have hnormP : Ideal.relNorm A P = q ^ Ideal.inertiaDeg q P :=
      Ideal.relNorm_eq_pow_of_isMaximal P q
    rw [hnormP] at hpNormP
    have hf0 : Ideal.inertiaDeg q P ≠ 0 :=
      Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos q P)
    have hpq : p ∣ q := (hpPrime.dvd_pow_iff_dvd hf0).mp hpNormP
    have hqPrimeMonoid : Prime q := Ideal.prime_of_isPrime hq0 hqPrime
    have hpqEq : p = q := by
      rw [← associated_iff_eq]
      exact hpPrime.associated_of_dvd hqPrimeMonoid hpq
    have hPover : P.LiesOver p := by
      simpa only [hpqEq] using hPoverQ
    exact ⟨P, ⟨hPdata.1, hPover⟩, Ideal.dvd_iff_le.mpr hPdata.2⟩
  · rintro ⟨P, hPover, hPI⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPover
    letI : P.IsPrime := hPover.1
    letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP0
    letI : P.LiesOver p := hPover.2
    have hnormPI : Ideal.relNorm A P ∣ Ideal.relNorm A I :=
      map_dvd (Ideal.relNorm A) hPI
    rw [Ideal.relNorm_eq_pow_of_isMaximal P p] at hnormPI
    exact (dvd_pow_self p
      (Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos p P))).trans hnormPI

/-- The relative discriminant ideal of a finite Dedekind extension, defined without a freeness
assumption as the relative norm of the different. -/
noncomputable def relativeDiscriminantIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] : Ideal A :=
  Ideal.relNorm A (differentIdeal A B)

/-- Remark 3.39(b): a nonzero prime divides the relative discriminant ideal exactly when a
prime above it divides the different. -/
theorem relative_discriminant_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [PerfectField (FractionRing A)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    p ∣ relativeDiscriminantIdeal A B ↔
      ∃ P ∈ Ideal.primesOver p B, P ∣ differentIdeal A B := by
  exact dvd_rel_norm A B hp differentIdeal_ne_bot

/-- A prime of a finite Dedekind extension divides the different exactly when it is ramified. -/
theorem dvd_different_ramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (P : Ideal B) [P.IsPrime] :
    P ∣ differentIdeal A B ↔ ¬ Algebra.IsUnramifiedAt A P := by
  exact dvd_differentIdeal_iff (A := A) (B := B)

/-- For an arithmetic Dedekind extension, divisibility of the different is equivalent to a
nontrivial ramification index. -/
theorem different_ramification_idx
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Module.Finite ℤ A] [CharZero A] [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    P ∣ differentIdeal A B ↔ Ideal.ramificationIdx (P.under A) P ≠ 1 := by
  rw [dvd_different_ramified A B P,
    Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP]

/-- The ramification-index formulation in the orientation used in Milne's statement. -/
theorem ramifies_dvd_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Module.Finite ℤ A] [CharZero A] [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (P.under A) P ≠ 1 ↔ P ∣ differentIdeal A B := by
  exact (different_ramification_idx A B P hP).symm

/-- Remark 3.39(b), in ramification-index form: a nonzero prime divides the relative
discriminant ideal exactly when some prime above it ramifies. -/
theorem discriminant_ramification_idx
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Module.Finite ℤ A] [CharZero A] [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    p ∣ relativeDiscriminantIdeal A B ↔
      ∃ P ∈ Ideal.primesOver p B, Ideal.ramificationIdx p P ≠ 1 := by
  rw [relative_discriminant_different A B hp]
  constructor
  · rintro ⟨P, hPover, hPdifferent⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPover
    letI : P.IsPrime := hPover.1
    have hramUnder : Ideal.ramificationIdx (P.under A) P ≠ 1 :=
      (different_ramification_idx A B P hP0).mp hPdifferent
    have hpUnder : p = P.under A := hPover.2.over
    exact ⟨P, hPover, by simpa only [hpUnder] using hramUnder⟩
  · rintro ⟨P, hPover, hram⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPover
    letI : P.IsPrime := hPover.1
    have hpUnder : p = P.under A := hPover.2.over
    have hramUnder : Ideal.ramificationIdx (P.under A) P ≠ 1 := by
      simpa only [← hpUnder] using hram
    exact ⟨P, hPover,
      (different_ramification_idx A B P hP0).mpr hramUnder⟩

/-- The set of prime divisors of the different is finite.  By
`dvd_different_ramified`, this is the finite support of ramification. -/
theorem set_dvd_different
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    Set.Finite {P : Ideal B | Ideal.IsPrime P ∧ P ∣ differentIdeal A B} := by
  let D := differentIdeal A B
  have hD : D ≠ ⊥ := differentIdeal_ne_bot
  refine ((normalizedFactors D).toFinset.finite_toSet).subset ?_
  intro P hP
  simpa using (Ideal.mem_normalizedFactors_iff hD).2
    ⟨hP.1, Ideal.dvd_iff_le.mp (by simpa [D] using hP.2)⟩

/-- Only finitely many primes of the base have a ramified prime above them. -/
theorem ramified_base_primes
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B] [Module.Finite ℤ A] [CharZero A] [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    Set.Finite {p : Ideal A | ∃ P : Ideal B,
      Ideal.IsPrime P ∧ P ≠ ⊥ ∧ P.under A = p ∧ Ideal.ramificationIdx p P ≠ 1} := by
  refine ((set_dvd_different A B).image fun P ↦ P.under A).subset ?_
  intro p hp
  rcases hp with ⟨P, hP, hP0, rfl, hram⟩
  letI : P.IsPrime := hP
  refine ⟨P, ?_, rfl⟩
  exact ⟨hP, (ramifies_dvd_different A B P hP0).mp hram⟩

end Towers.NumberTheory.Milne
