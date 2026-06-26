import Towers.ClassField.CyclotomicBrauer.PrimePowerBlocks
import Mathlib.GroupTheory.Exponent

/-!
# Lemma VII.7.3: arithmetic for the coprime compositum

The prime-power targets indexed by `N.primeFactors` are pairwise coprime
and multiply to `N`.  Consequently a finite product of cyclic groups with
those cardinalities is cyclic.  These are the finite-product facts used by
the Galois restriction map for the rational compositum.
-/

namespace Towers.CField.CBrauer

noncomputable section

/-- The product of the prime-power targets in Lemma VII.7.3 is the original
integer `N`. -/
theorem prod_prime_targets
    (N : ℕ) (hN : N ≠ 0) :
    (∏ ell : N.primeFactors,
      (ell : ℕ) ^ N.factorization ell) = N := by
  exact (Nat.prod_pow_primeFactors_factorization hN).symm

/-- Distinct prime factors of `N` give pairwise coprime target powers. -/
theorem targets_pairwise_coprime (N : ℕ) :
    Set.Pairwise (Set.univ : Set N.primeFactors)
      (Function.onFun Nat.Coprime fun ell : N.primeFactors ↦
        (ell : ℕ) ^ N.factorization ell) := by
  simpa only [Set.pairwise_univ] using
    Nat.pairwise_coprime_pow_primeFactors_factorization (n := N)

/-- Pairwise coprime divisors of one natural number have product dividing
that number.  This is the local-degree assembly used after every
prime-power completion degree has been embedded into the compositum degree. -/
theorem dvd_pairwise_coprime
    {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℕ)
    (hcoprime : Set.Pairwise (s : Set ι) (Function.onFun Nat.Coprime f))
    (hdvd : ∀ i ∈ s, f i ∣ d) :
    (∏ i ∈ s, f i) ∣ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have haDvd : f a ∣ d := hdvd a (Finset.mem_insert_self a s)
      have hsDvd : (∏ i ∈ s, f i) ∣ d := by
        apply ih
        · exact hcoprime.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
        · intro i hi
          exact hdvd i (Finset.mem_insert_of_mem hi)
      have hcop : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcoprime (Finset.mem_insert_self a s)
          (Finset.mem_insert_of_mem hi) (by
            intro hai
            apply ha
            rwa [hai])
      exact hcop.mul_dvd_of_dvd_of_dvd haDvd hsDvd

/-- If every prime-power target divides one local degree, then `N` itself
divides that degree. -/
theorem dvd_prime_targets
    (N d : ℕ) (hN : N ≠ 0)
    (hdvd : ∀ ell : N.primeFactors,
      (ell : ℕ) ^ N.factorization ell ∣ d) :
    N ∣ d := by
  rw [← prod_prime_targets N hN]
  apply dvd_pairwise_coprime Finset.univ
    (fun ell : N.primeFactors ↦ (ell : ℕ) ^ N.factorization ell) d
  · simpa only [Finset.coe_univ] using
      targets_pairwise_coprime N
  · intro ell _
    exact hdvd ell

/-- A finite product of finite cyclic groups of pairwise coprime orders is
cyclic.  Mathlib provides the binary result; the exponent computation gives
the dependent finite-product form needed for all prime factors at once. -/
theorem pi_pairwise_coprime
    {ι : Type*} [Finite ι]
    (G : ι → Type*) [∀ i, Group (G i)] [∀ i, Finite (G i)]
    [∀ i, IsCyclic (G i)]
    (hcoprime : Set.Pairwise (Set.univ : Set ι)
      (Function.onFun Nat.Coprime fun i ↦ Nat.card (G i))) :
    IsCyclic (∀ i, G i) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI (i : ι) : CommGroup (G i) := IsCyclic.commGroup
  rw [IsCyclic.iff_exponent_eq_card, Monoid.exponent_pi, Nat.card_pi]
  have hexponent : ∀ i, Monoid.exponent (G i) = Nat.card (G i) := fun i ↦
    IsCyclic.iff_exponent_eq_card.mp (inferInstance : IsCyclic (G i))
  simp_rw [hexponent]
  apply Finset.lcm_eq_prod
  simpa only [Finset.coe_univ] using hcoprime

/-- Specialized form for groups whose orders are the prime-power factors of
`N`. -/
theorem cyclic_pi_factors
    (N : ℕ) (G : N.primeFactors → Type*)
    [∀ ell, Group (G ell)] [∀ ell, Finite (G ell)]
    [∀ ell, IsCyclic (G ell)]
    (hcard : ∀ ell, Nat.card (G ell) =
      (ell : ℕ) ^ N.factorization ell) :
    IsCyclic (∀ ell, G ell) := by
  apply pi_pairwise_coprime G
  intro ell₁ _ ell₂ _ hne
  change Nat.Coprime (Nat.card (G ell₁)) (Nat.card (G ell₂))
  rw [hcard ell₁, hcard ell₂]
  exact Nat.pairwise_coprime_pow_primeFactors_factorization hne

end

end Towers.CField.CBrauer
