import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

/-!
# Pairwise-coprime factors of a power

The ideal-factor extraction used in Milne's proof of Theorem 6.8.
-/

namespace Towers.NumberTheory.Milne

open Function
open scoped BigOperators

/-- In a Dedekind domain, each member of a pairwise-coprime family of nonzero ideals whose
product is a `k`th power is itself a `k`th power. -/
theorem pairwise_coprime_prod
    {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (F : ι → Ideal R) (hF0 : ∀ i, F i ≠ 0) (hpair : Pairwise (IsCoprime on F))
    {J : Ideal R} {k : ℕ} (hprod : ∏ i, F i = J ^ k) (i : ι) :
    ∃ I : Ideal R, F i = I ^ k := by
  classical
  let B : Ideal R := ∏ j ∈ Finset.univ.erase i, F j
  have hB0 : B ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hF0 j
  have hsplit : F i * B = J ^ k := by
    rw [← hprod]
    exact Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i)
  have hcop : IsCoprime (F i) B := by
    apply IsCoprime.prod_right
    intro j hj
    exact hpair (Ne.symm (Finset.mem_erase.mp hj).1)
  have hassoc : Associates.mk (F i) * Associates.mk B = Associates.mk J ^ k := by
    simpa only [Associates.mk_mul_mk, Associates.mk_pow] using congrArg Associates.mk hsplit
  obtain ⟨d, hd⟩ := Associates.eq_pow_of_mul_eq_pow
    (Associates.mk_ne_zero.mpr (hF0 i)) (Associates.mk_ne_zero.mpr hB0) (c := Associates.mk J)
    (k := k) (by
      intro q hqi hqB hqprime
      have hqi' : q.out ∣ F i := (Associates.out_dvd_iff (F i) q).mpr hqi
      have hqB' : q.out ∣ B := (Associates.out_dvd_iff B q).mpr hqB
      have hqunit : IsUnit q.out := hcop.isUnit_of_dvd' hqi' hqB'
      apply hqprime.not_unit
      rw [← Associates.mk_out q, Associates.isUnit_mk]
      exact hqunit) hassoc
  refine ⟨d.out, ?_⟩
  apply associated_iff_eq.mp
  rw [← Associates.mk_eq_mk_iff_associated]
  simpa only [Associates.mk_pow, Associates.mk_out] using hd

/-- A convenient form where nonvanishing of the product follows from nonvanishing of the ideal
whose power it is. -/
theorem pairwise_coprime_ne
    {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (F : ι → Ideal R) (hpair : Pairwise (IsCoprime on F))
    {J : Ideal R} (hJ0 : J ≠ 0) {k : ℕ} (hprod : ∏ i, F i = J ^ k) (i : ι) :
    ∃ I : Ideal R, F i = I ^ k := by
  classical
  apply pairwise_coprime_prod F _ hpair hprod i
  intro j hj0
  have hz : ∏ i, F i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj0
  rw [hprod] at hz
  exact (pow_ne_zero k hJ0) hz

end Towers.NumberTheory.Milne
