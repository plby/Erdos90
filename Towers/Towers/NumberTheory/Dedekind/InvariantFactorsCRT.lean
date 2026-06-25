import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Milne, Algebraic Number Theory, CRT packaging for invariant factors

The primary cyclic factors in the invariant-factor theorem are indexed by distinct prime ideals.
This file packages the Chinese remainder step that combines one cyclic factor at each prime into
a single quotient by the product ideal.
-/

namespace Towers.NumberTheory.Milne

open Function
open scoped DirectSum

/-- A finite product of pairwise coprime ideals gives, linearly over the original ring, the
product of the corresponding quotient rings. -/
noncomputable def prodLinearPi
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    (A ⧸ ∏ i, I i) ≃ₗ[A] ∀ i, A ⧸ I i := by
  classical
  let F : A →ₗ[A] ∀ i, A ⧸ I i := LinearMap.pi fun i => (I i).mkQ
  have hprod : ∏ i, I i = ⨅ i, I i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := I) (by
        intro i _ j _ hij
        exact hI hij)
  have hker : LinearMap.ker F = ∏ i, I i := by
    change LinearMap.ker (LinearMap.pi fun i => (I i).mkQ) = _
    rw [LinearMap.ker_pi]
    simp only [Submodule.ker_mkQ]
    exact hprod.symm
  let f : (A ⧸ ∏ i, I i) →ₗ[A] ∀ i, A ⧸ I i :=
    (∏ i, I i).liftQ F hker.ge
  apply LinearEquiv.ofBijective f
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact (∏ i, I i).ker_liftQ_eq_bot' F hker.symm
  · intro y
    obtain ⟨x, hx⟩ := Ideal.pi_mkQ_surjective hI y
    refine ⟨Ideal.Quotient.mk (∏ i, I i) x, ?_⟩
    simpa [f, F, Submodule.liftQ_apply] using hx

@[simp]
theorem linear_pi_mk
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) (x : A) :
    prodLinearPi A ι I hI (Ideal.Quotient.mk (∏ i, I i) x) =
      fun i => Ideal.Quotient.mk (I i) x := by
  classical
  rfl

/-- Powers of pairwise distinct maximal ideals are pairwise coprime. -/
theorem pairwise_coprime_powers
    (A : Type*) [CommRing A]
    (ι : Type*) (P : ι → Ideal A)
    (hP : ∀ i, (P i).IsMaximal) (hP_inj : Function.Injective P)
    (e : ι → ℕ) :
    Pairwise (IsCoprime on fun i => P i ^ e i) := by
  intro i j hij
  letI : (P i).IsMaximal := hP i
  letI : (P j).IsMaximal := hP j
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.pow_sup_pow_eq_top
    (Ideal.isCoprime_iff_sup_eq.mp
      (Ideal.isCoprime_of_isMaximal (fun h => hij (hP_inj h))))

/-- The CRT equivalence for powers of a finite family of distinct maximal ideals. -/
noncomputable def maximalPowersPi
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι]
    (P : ι → Ideal A) (hP : ∀ i, (P i).IsMaximal)
    (hP_inj : Function.Injective P) (e : ι → ℕ) :
    (A ⧸ ∏ i, P i ^ e i) ≃ₗ[A] ∀ i, A ⧸ P i ^ e i :=
  prodLinearPi A ι (fun i => P i ^ e i)
    (pairwise_coprime_powers A ι P hP hP_inj e)

/-- The increasing rearrangement of a finite tuple of exponents. -/
noncomputable def sortedExponents {n : ℕ} (e : Fin n → ℕ) : Fin n → ℕ :=
  e ∘ Tuple.sort e

theorem sortedExponents_monotone {n : ℕ} (e : Fin n → ℕ) :
    Monotone (sortedExponents e) :=
  Tuple.monotone_sort e

/-- Reindexing by the sorting permutation puts the exponents of a prime-primary cyclic
decomposition in increasing order. -/
noncomputable def sortDirectLinear
    (A : Type*) [CommRing A] (P : Ideal A)
    (n : ℕ) (e : Fin n → ℕ) :
    (⨁ j, A ⧸ P ^ e j) ≃ₗ[A]
      ⨁ j, A ⧸ P ^ sortedExponents e j :=
  DirectSum.lequivCongrLeft A (Tuple.sort e).symm

/-- Multiplying the sorted prime-power columns produces the nested ideals in the global
invariant-factor theorem. -/
noncomputable def invariantFactorIdeal
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι] (P : ι → Ideal A)
    (n : ℕ) (e : ι → Fin n → ℕ) (j : Fin n) : Ideal A :=
  ∏ i, P i ^ sortedExponents (e i) j

/-- The ideals obtained by multiplying increasing prime-power exponents form the required
descending chain under inclusion. -/
theorem invariant_factor_antitone
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι] (P : ι → Ideal A)
    (n : ℕ) (e : ι → Fin n → ℕ) :
    Antitone (invariantFactorIdeal A ι P n e) := by
  classical
  intro j k hjk
  apply Finset.prod_le_prod'
  intro i _
  exact Ideal.pow_le_pow_right (sortedExponents_monotone (e i) hjk)

/-- A rectangular collection of prime-power cyclic factors can be read either by prime columns
or by invariant-factor rows.  The row ideals are the products of the entries in each row. -/
noncomputable def quotientsPrimaryColumns
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι]
    (P : ι → Ideal A) (hP : ∀ i, (P i).IsMaximal)
    (hP_inj : Function.Injective P)
    (n : ℕ) (e : ι → Fin n → ℕ) :
    (⨁ j, A ⧸ invariantFactorIdeal A ι P n e j) ≃ₗ[A]
      ⨁ i, ⨁ j, A ⧸ P i ^ sortedExponents (e i) j := by
  classical
  let C : Fin n → ι → Type _ := fun j i =>
    A ⧸ P i ^ sortedExponents (e i) j
  let idxSwap : (Σ _ : Fin n, ι) ≃ (Σ _ : ι, Fin n) :=
    (Equiv.sigmaEquivProd (Fin n) ι).trans <|
      (Equiv.prodComm (Fin n) ι).trans <|
        (Equiv.sigmaEquivProd ι (Fin n)).symm
  let eSwap :
      (⨁ p : Σ _ : Fin n, ι, C p.1 p.2) ≃ₗ[A]
        ⨁ p : Σ _ : ι, Fin n, C p.2 p.1 := by
    simpa [idxSwap, Equiv.prodComm_symm] using
      (DirectSum.lequivCongrLeft A idxSwap :
        (⨁ p : Σ _ : Fin n, ι, C p.1 p.2) ≃ₗ[A]
          ⨁ p : Σ _ : ι, Fin n,
            C (idxSwap.symm p).1 (idxSwap.symm p).2)
  let eRows :
      (⨁ j, A ⧸ invariantFactorIdeal A ι P n e j) ≃ₗ[A]
        ⨁ j, ⨁ i, C j i :=
    DFinsupp.mapRange.linearEquiv fun j =>
      (maximalPowersPi A ι P hP hP_inj
        (fun i => sortedExponents (e i) j)) ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype A ι (C j)).symm
  let eFlatten :
      (⨁ j, ⨁ i, C j i) ≃ₗ[A]
        ⨁ p : Σ _ : Fin n, ι, C p.1 p.2 :=
    (DirectSum.sigmaLcurryEquiv (δ := C) A).symm
  let eCurry :
      (⨁ p : Σ _ : ι, Fin n, C p.2 p.1) ≃ₗ[A]
        ⨁ i, ⨁ j, C j i :=
    DirectSum.sigmaLcurryEquiv (δ := fun i j => C j i) A
  exact eRows ≪≫ₗ eFlatten ≪≫ₗ eSwap ≪≫ₗ eCurry

/-- The same row-versus-column equivalence, with the prime-primary columns left in their
original (possibly unsorted) order. -/
noncomputable def primaryColumnsUnsorted
    (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι]
    (P : ι → Ideal A) (hP : ∀ i, (P i).IsMaximal)
    (hP_inj : Function.Injective P)
    (n : ℕ) (e : ι → Fin n → ℕ) :
    (⨁ j, A ⧸ invariantFactorIdeal A ι P n e j) ≃ₗ[A]
      ⨁ i, ⨁ j, A ⧸ P i ^ e i j :=
  quotientsPrimaryColumns A ι P hP hP_inj n e ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun i =>
      (sortDirectLinear A (P i) n (e i)).symm

end Towers.NumberTheory.Milne
