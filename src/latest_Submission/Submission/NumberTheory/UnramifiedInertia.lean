import Submission.NumberTheory.LocalInertia


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

lemma number_bot_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hUnramified :
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.inertia (Gal(L/ℚ)) = ⊥ := by
  classical
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  have hP_mem :
      P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q)
        (NumberField.RingOfIntegers L) :=
    ⟨inferInstance, inferInstance⟩
  have hRamification :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P = 1 :=
    hUnramified P hP_mem
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    inertia_ramification_idx (L := L) hq P
  have hCardOne :
      Nat.card (P.inertia (Gal(L/ℚ))) = 1 := by
    rw [hCard, hRamification]
  exact (P.inertia (Gal(L/ℚ))).eq_bot_of_card_eq hCardOne

lemma ramification_idx_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hInertia :
      P.inertia (Gal(L/ℚ)) = ⊥) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P = 1 := by
  classical
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    inertia_ramification_idx (L := L) hq P
  have hCardOne :
      Nat.card (P.inertia (Gal(L/ℚ))) = 1 := by
    rw [hInertia, Subgroup.card_bot]
  rw [← hCard]
  exact hCardOne

noncomputable def ringIntegersRat
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) :
    NumberField.RingOfIntegers K ≃ₐ[ℤ] NumberField.RingOfIntegers L :=
  AlgEquiv.ofRingEquiv
    (f := NumberField.RingOfIntegers.mapRingEquiv (e : K ≃+* L))
    (by
      intro z
      ext
      simp)

lemma rational_rat_alg
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L)
    {q : ℕ}
    (hUnramified :
      RationalPrimeUnramified
        (S := NumberField.RingOfIntegers K) q) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers L) q := by
  classical
  let eO : NumberField.RingOfIntegers K ≃ₐ[ℤ]
      NumberField.RingOfIntegers L :=
    ringIntegersRat e
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
  have hUnder :
      (P.comap eO).under ℤ = P.under ℤ := by
    ext z
    change
      eO (algebraMap ℤ (NumberField.RingOfIntegers K) z) ∈ P ↔
        algebraMap ℤ (NumberField.RingOfIntegers L) z ∈ P
    rw [eO.commutes]
  have hP_comap_mem :
      P.comap eO ∈
        Ideal.primesOver (Ideal.rationalPrimeIdeal q)
          (NumberField.RingOfIntegers K) := by
    refine ⟨inferInstance, ?_⟩
    exact ⟨by simpa [hUnder] using
      (P.over_def (Ideal.rationalPrimeIdeal q) :
        Ideal.rationalPrimeIdeal q = P.under ℤ)⟩
  have hRamificationComap :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) (P.comap eO) = 1 :=
    hUnramified (P.comap eO) hP_comap_mem
  have hRamificationEq :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) (P.comap eO) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    Ideal.ramificationIdx_comap_eq
      (p := Ideal.rationalPrimeIdeal q) eO P
  simpa [hRamificationEq] using hRamificationComap

end Submission
