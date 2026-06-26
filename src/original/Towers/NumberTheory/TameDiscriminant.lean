import Towers.NumberTheory.Splitting


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

theorem totally_gal_rat
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ_ne_two : ℓ ≠ 2)
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (hG : IsPGroup ℓ (Gal(L/ℚ))) :
    NumberField.IsTotallyReal L := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard_odd : Odd (Nat.card (Gal(L/ℚ))) := by
    have hℓ_odd : Odd ℓ := hℓ.odd_of_ne_two hℓ_ne_two
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    rw [hn]
    simpa using hℓ_odd.pow (n := n)
  letI : IsUnramifiedAtInfinitePlaces ℚ L :=
    IsUnramifiedAtInfinitePlaces_of_odd_card_aut (k := ℚ) (K := L) hcard_odd
  refine (NumberField.isTotallyReal_iff L).2 ?_
  intro w
  have hw_unram : w.IsUnramified ℚ := NumberField.InfinitePlace.isUnramified (k := ℚ) w
  have hbase_real : (w.comap (algebraMap ℚ L)).IsReal := by
    exact NumberField.IsTotallyReal.isReal _
  exact ((NumberField.InfinitePlace.isUnramified_iff (k := ℚ) (w := w)).1 hw_unram).resolve_right
    ((NumberField.InfinitePlace.not_isComplex_iff_isReal).2 hbase_real)

-- Lemma 7

/--
Weak tame discriminant bound, sufficient for the tower construction.

If `L/ℚ` is finite and ramified only at the finite set `S`,
and all ramification at primes in `S` is tame, then the root discriminant
is bounded by the product of the primes in `S`.
-/
lemma ramification_hypothesis_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r := by
  intro r hr hrS
  exact hram r hr hrS

/-- Compatibility name used by the original `Erdos90/I.lean` development. -/
lemma hypothesis_erdos_90
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r :=
  ramification_hypothesis_unramified L S hram

/--
A rational prime `r` is tame at the prime ideals above `(r)` in a `ℤ`-algebra
`S` if every prime ideal above `(r)` has ramification index coprime to `r`.

This is the exact local hypothesis used in the root-discriminant argument.
-/
noncomputable def RationalTamePrimes
    {S : Type*} [CommRing S] [Algebra ℤ S]
    (r : ℕ) : Prop :=
  ∀ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r) S,
    Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)

lemma tame_hypothesis_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    (htame : ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r := by
  intro r hrS
  exact htame r hrS

/-- Compatibility name used by the original `Erdos90/I.lean` development. -/
lemma tame_hypothesis_erdos
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    (htame : ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r :=
  tame_hypothesis_primes L S htame

/-- The local factor contributed by a rational prime with tame ramification index `e`. -/
def tameDiscriminantFactor (r e : ℕ) : ℝ :=
  Real.rpow (r : ℝ) (1 - 1 / (e : ℝ))

lemma sub_inv_cast (e : ℕ) :
    1 - 1 / (e : ℝ) ≤ (1 : ℝ) := by
  have hdiv_nonneg : 0 ≤ 1 / (e : ℝ) := by
    positivity
  linarith

lemma tame_discriminant_nonneg (r e : ℕ) :
    0 ≤ tameDiscriminantFactor r e := by
  unfold tameDiscriminantFactor
  exact Real.rpow_nonneg (by positivity) _

lemma tame_discriminant_prime
    {r e : ℕ} (hr : Nat.Prime r) :
    tameDiscriminantFactor r e ≤ r := by
  unfold tameDiscriminantFactor
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hr.one_lt.le
  have hexp : 1 - 1 / (e : ℝ) ≤ (1 : ℝ) := sub_inv_cast e
  simpa using Real.rpow_le_rpow_of_exponent_le hr1 hexp

lemma tame_discriminant_factor
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r) :
    (∏ r ∈ S, tameDiscriminantFactor r (e r)) ≤ ∏ r ∈ S, (r : ℝ) := by
  classical
  revert hSprime
  refine Finset.induction_on S ?_ ?_
  · intro hSprime
    simp [tameDiscriminantFactor]
  · intro r S hrS ih hSprime
    have hrprime : Nat.Prime r := hSprime r (by simp [hrS])
    have hSprime' : ∀ q ∈ S, Nat.Prime q := by
      intro q hq
      exact hSprime q (by simp [hq])
    have hnonneg_tame :
        0 ≤ ∏ q ∈ S, tameDiscriminantFactor q (e q) := by
      refine Finset.prod_nonneg ?_
      intro q hq
      exact tame_discriminant_nonneg q (e q)
    have hstep₁ :
        tameDiscriminantFactor r (e r) *
            ∏ q ∈ S, tameDiscriminantFactor q (e q)
          ≤ (r : ℝ) * ∏ q ∈ S, tameDiscriminantFactor q (e q) := by
      exact mul_le_mul_of_nonneg_right
        (tame_discriminant_prime hrprime) hnonneg_tame
    have hstep₂ :
        (r : ℝ) * ∏ q ∈ S, tameDiscriminantFactor q (e q)
          ≤ (r : ℝ) * ∏ q ∈ S, (q : ℝ) := by
      exact mul_le_mul_of_nonneg_left (ih hSprime') (by positivity)
    calc
      (∏ q ∈ insert r S, tameDiscriminantFactor q (e q))
          =
            tameDiscriminantFactor r (e r) *
              ∏ q ∈ S, tameDiscriminantFactor q (e q) := by
              simp [hrS]
      _ ≤ (r : ℝ) * ∏ q ∈ S, tameDiscriminantFactor q (e q) := hstep₁
      _ ≤ (r : ℝ) * ∏ q ∈ S, (q : ℝ) := hstep₂
      _ = ∏ q ∈ insert r S, (q : ℝ) := by
              simp [hrS]

lemma nonempty_primes_integers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r) :
    Nonempty ↑((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) := by
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  letI : qI.IsPrime := rational_prime_ideal hr
  simpa [qI] using
    (Ideal.nonempty_primesOver (R := ℤ) (S := NumberField.RingOfIntegers L) qI)

noncomputable def chosenPrimeRational
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r) :
    {P : Ideal (NumberField.RingOfIntegers L) //
      P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)} :=
  Classical.choice (nonempty_primes_integers (L := L) hr)

lemma chosen_prime_rational
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r) :
    (chosenPrimeRational (L := L) hr).1 ∈
      (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) :=
  (chosenPrimeRational (L := L) hr).2

lemma rational_ramification_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hQ : Q ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) Q := by
  let _ := hr
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := by simpa [qI] using hP.2
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver qI := by simpa [qI] using hQ.2
  simpa [qI] using
    (Ideal.ramificationIdx_eq_of_isGaloisGroup
      (p := qI) (P := P) (Q := Q) (G := Gal(L/ℚ)))

lemma chosen_coprime_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (htame : RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r)
        (chosenPrimeRational (L := L) hr).1) := by
  exact htame _ (chosen_prime_rational (L := L) hr)

lemma tame_ramification_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (htame : RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    ∃ e : ℕ,
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r e ∧
        Nat.Coprime r e := by
  let P0 : Ideal (NumberField.RingOfIntegers L) := (chosenPrimeRational (L := L) hr).1
  let e : ℕ :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P0
  refine ⟨e, ?_, ?_⟩
  · intro P hP
    dsimp [e, P0]
    exact rational_ramification_primes
      (L := L) (hr := hr) hP (chosen_prime_rational (L := L) hr)
  · dsimp [e, P0]
    exact chosen_coprime_idx (L := L) hr htame

lemma tame_ramification_function
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (htame : ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    ∃ e : ℕ → ℕ,
      ∀ r ∈ S,
        RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r) ∧
          Nat.Coprime r (e r) := by
  classical
  choose e he using fun r (hrS : r ∈ S) =>
    tame_ramification_prime
      (L := L) (hr := hSprime r hrS) (htame := htame r hrS)
  refine ⟨fun r => if hrS : r ∈ S then e r hrS else 1, ?_⟩
  intro r hrS
  simpa [hrS] using he r hrS

lemma tame_index_function
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    {e : ℕ → ℕ}
    (he : ∀ r ∈ S,
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r) ∧
        Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r) :=
  (he r hrS).1

lemma tame_function_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ)
    {e : ℕ → ℕ}
    (he : ∀ r ∈ S,
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r) ∧
        Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    Nat.Coprime r (e r) :=
  (he r hrS).2

def tameRamificationExtension
    (S : Finset ℕ) (e : ℕ → ℕ) (r : ℕ) : ℕ :=
  if _hrS : r ∈ S then e r else 1

lemma tame_ramification_extension
    (S : Finset ℕ) (e : ℕ → ℕ)
    {r : ℕ} (hrS : r ∈ S) :
    tameRamificationExtension S e r = e r := by
  simp [tameRamificationExtension, hrS]

lemma tame_ramification_not
    (S : Finset ℕ) (e : ℕ → ℕ)
    {r : ℕ} (hrS : r ∉ S) :
    tameRamificationExtension S e r = 1 := by
  simp [tameRamificationExtension, hrS]

lemma tame_ramification_spec
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_idx : ∀ r ∈ S,
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    ∀ r, Nat.Prime r →
      RationalRamificationIdx
        (S := NumberField.RingOfIntegers L) r (tameRamificationExtension S e r) := by
  intro r hr
  by_cases hrS : r ∈ S
  · simpa [tame_ramification_extension S e hrS] using he_idx r hrS
  · simpa
      [RationalPrimeUnramified, tame_ramification_not S e hrS]
      using
      hram r hr hrS

lemma tame_ramification_coprime
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r)) :
    ∀ r ∈ S, Nat.Coprime r (tameRamificationExtension S e r) := by
  intro r hrS
  simpa [tame_ramification_extension S e hrS] using he_coprime r hrS

lemma discriminant_factor_pos
    {r e : ℕ} (hr : Nat.Prime r) :
    0 < tameDiscriminantFactor r e := by
  unfold tameDiscriminantFactor
  exact Real.rpow_pos_of_pos (by exact_mod_cast hr.pos) _

lemma tame_discriminant_pos
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r) :
    0 < ∏ r ∈ S, tameDiscriminantFactor r (e r) := by
  refine Finset.prod_pos ?_
  intro r hrS
  exact discriminant_factor_pos (hSprime r hrS)

lemma discriminant_abs_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hdisc : absDiscriminant L = x ^ Module.finrank ℚ L) :
    rootDiscriminant L = x := by
  set currentAlg : Algebra ℚ L := inferInstance
  letI : Algebra ℚ L := currentAlg
  set n : ℕ := Module.finrank ℚ L
  have hdisc_n : absDiscriminant L = x ^ n := by
    simpa [currentAlg, n] using hdisc
  have halg : currentAlg = DivisionRing.toRatAlgebra := by
    exact Subsingleton.elim _ _
  subst currentAlg
  letI : Algebra ℚ L := DivisionRing.toRatAlgebra
  set m : ℕ := Module.finrank ℚ L
  have hnm : n = m := by
    cases halg
    rfl
  have hdisc_m : absDiscriminant L = x ^ m := by
    simpa [hnm] using hdisc_n
  have hm_pos : 0 < m := by
    simpa [m] using (show 0 < Module.finrank ℚ L from Module.finrank_pos)
  have hm_ne_zero : (m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hm_pos
  have hroot_m : Real.rpow (x ^ m) (1 / (m : ℝ)) = x := by
    have hpow : x ^ m = Real.rpow x (m : ℝ) := by
      symm
      exact Real.rpow_natCast x m
    have hrpow :
        Real.rpow (Real.rpow x (m : ℝ)) (1 / (m : ℝ)) =
          Real.rpow x ((m : ℝ) * (1 / (m : ℝ))) := by
      symm
      exact Real.rpow_mul hx_nonneg _ _
    have hmul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
      field_simp [hm_ne_zero]
    have hstart :
        Real.rpow (x ^ m) (1 / (m : ℝ)) =
          Real.rpow (Real.rpow x (m : ℝ)) (1 / (m : ℝ)) := by
      rw [hpow]
    have hlast : Real.rpow x ((m : ℝ) * (1 / (m : ℝ))) = x := by
      rw [hmul]
      exact Real.rpow_one x
    exact hstart.trans (hrpow.trans hlast)
  unfold rootDiscriminant
  rw [hdisc_m]
  simpa [m] using hroot_m

lemma ramification_global_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (e : ℕ → ℕ)
    {r : ℕ} (hr : Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r)) :
    e r = (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  let P0 : Ideal (NumberField.RingOfIntegers L) := (chosenPrimeRational (L := L) hr).1
  have hP0 :
      P0 ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) := by
    dsimp [P0]
    exact chosen_prime_rational (L := L) hr
  letI : P0.IsPrime := hP0.1
  letI : P0.LiesOver (Ideal.rationalPrimeIdeal r) := hP0.2
  calc
    e r
      = Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P0 := by
            symm
            exact he_idx r hr P0 hP0
    _ = (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
          symm
          exact Ideal.ramificationIdxIn_eq_ramificationIdx
            (p := Ideal.rationalPrimeIdeal r) (P := P0) (G := Gal(L/ℚ))

lemma ramification_dvd_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (e : ℕ → ℕ)
    {r : ℕ} (hr : Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r)) :
    e r ∣ Module.finrank ℚ L := by
  rw [ramification_global_indices
    (L := L) (e := e) hr he_idx]
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := rational_ideal_maximal hr
  have hmain :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := qI) hqI0 (NumberField.RingOfIntegers L) (Gal(L/ℚ))
  refine ⟨(qI.primesOver (NumberField.RingOfIntegers L)).ncard *
      qI.inertiaDegIn (NumberField.RingOfIntegers L), ?_⟩
  calc
    Module.finrank ℚ L
      = Nat.card (Gal(L/ℚ)) := by
          symm
          exact IsGalois.card_aut_eq_finrank ℚ L
    _ = (qI.primesOver (NumberField.RingOfIntegers L)).ncard *
          (qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
            qI.inertiaDegIn (NumberField.RingOfIntegers L)) := by
              simpa using hmain.symm
    _ = qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
          ((qI.primesOver (NumberField.RingOfIntegers L)).ncard *
            qI.inertiaDegIn (NumberField.RingOfIntegers L)) := by
              ac_rfl

lemma tame_root_discriminant
    {r e k : ℕ} (he_pos : 0 < e) :
    tameDiscriminantFactor r e ^ (e * k) =
      (r : ℝ) ^ (e * k - (e * k) / e) := by
  have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
  have he_ne_zero : (e : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt he_pos
  have hkdiv : (e * k) / e = k := by
    exact Nat.mul_div_right k he_pos
  have hinv :
      (1 / (e : ℝ)) * ((e : ℝ) * (k : ℝ)) = (k : ℝ) := by
    have hmul : (1 / (e : ℝ)) * (e : ℝ) = 1 := by
      field_simp [he_ne_zero]
    calc
      (1 / (e : ℝ)) * ((e : ℝ) * (k : ℝ))
          = ((1 / (e : ℝ)) * (e : ℝ)) * (k : ℝ) := by ring
      _ = k := by rw [hmul, one_mul]
  have hexp :
      (1 - 1 / (e : ℝ)) * ((e * k : ℕ) : ℝ) =
        (((e * k - (e * k) / e : ℕ)) : ℝ) := by
    rw [Nat.cast_mul]
    calc
      (1 - 1 / (e : ℝ)) * ((e : ℝ) * (k : ℝ))
          = 1 * ((e : ℝ) * (k : ℝ)) - (1 / (e : ℝ)) * ((e : ℝ) * (k : ℝ)) := by
              ring
      _ = (e : ℝ) * (k : ℝ) - (k : ℝ) := by rw [one_mul, hinv]
      _ = (((e * k : ℕ)) : ℝ) - (((e * k) / e : ℕ) : ℝ) := by
            rw [hkdiv, Nat.cast_mul]
      _ = (((e * k - (e * k) / e : ℕ)) : ℝ) := by
            symm
            rw [Nat.cast_sub (Nat.div_le_self (e * k) e)]
  unfold tameDiscriminantFactor
  calc
    Real.rpow (r : ℝ) (1 - 1 / (e : ℝ)) ^ (e * k)
      = Real.rpow (Real.rpow (r : ℝ) (1 - 1 / (e : ℝ))) ((e * k : ℕ) : ℝ) := by
          symm
          exact Real.rpow_natCast _ (e * k)
    _ = Real.rpow (r : ℝ) ((1 - 1 / (e : ℝ)) * ((e * k : ℕ) : ℝ)) := by
          symm
          exact Real.rpow_mul hr_nonneg _ _
    _ = Real.rpow (r : ℝ) (((e * k - (e * k) / e : ℕ)) : ℝ) := by rw [hexp]
    _ = (r : ℝ) ^ (e * k - (e * k) / e) := Real.rpow_natCast _ _

lemma tame_discriminant_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    tameDiscriminantFactor r (e r) ^ Module.finrank ℚ L =
      (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
  have hr : Nat.Prime r := hSprime r hrS
  have hcop : Nat.Coprime r (e r) := he_coprime r hrS
  have hdiv : e r ∣ Module.finrank ℚ L := by
    exact ramification_dvd_indices
      (L := L) (e := e) hr he_idx
  have he_ne_zero : e r ≠ 0 := by
    intro he0
    have hcop0 : Nat.Coprime r 0 := by
      simpa [he0] using hcop
    simp [Nat.Prime.ne_one hr] at hcop0
  rcases hdiv with ⟨k, hk⟩
  rw [hk]
  exact tame_root_discriminant
    (r := r) (e := e r) (k := k) (Nat.pos_of_ne_zero he_ne_zero)

lemma tame_discriminant_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r)) :
    (∏ r ∈ S, tameDiscriminantFactor r (e r)) ^ Module.finrank ℚ L =
      ∏ r ∈ S, (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
  classical
  revert hSprime he_coprime
  refine Finset.induction_on S ?_ ?_
  · intro hSprime he_coprime
    simp
  · intro r S hrS ih hSprime he_coprime
    have hfactor :
        tameDiscriminantFactor r (e r) ^ Module.finrank ℚ L =
          (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
      exact tame_discriminant_finrank
        (L := L) (S := insert r S) (e := e) hSprime he_idx he_coprime (by simp)
    have hSprime' : ∀ q ∈ S, Nat.Prime q := by
      intro q hq
      exact hSprime q (by simp [hq])
    have he_coprime' : ∀ q ∈ S, Nat.Coprime q (e q) := by
      intro q hq
      exact he_coprime q (by simp [hq])
    calc
      (∏ q ∈ insert r S, tameDiscriminantFactor q (e q)) ^ Module.finrank ℚ L
        =
          (tameDiscriminantFactor r (e r) *
            ∏ q ∈ S, tameDiscriminantFactor q (e q)) ^ Module.finrank ℚ L := by
              simp [hrS]
      _ = tameDiscriminantFactor r (e r) ^ Module.finrank ℚ L *
            (∏ q ∈ S, tameDiscriminantFactor q (e q)) ^ Module.finrank ℚ L := by
              rw [mul_pow]
      _ = (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) *
            ∏ q ∈ S, (q : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e q) := by
              rw [hfactor, ih hSprime' he_coprime']
      _ =
          ∏ q ∈ insert r S,
            (q : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e q) := by
            simp [hrS]

lemma ramification_dvd_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r e : ℕ} (hr : Nat.Prime r)
    (hidx : RationalRamificationIdx (S := NumberField.RingOfIntegers L) r e)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    P ^ e ∣
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L)) (Ideal.rationalPrimeIdeal r) := by
  let _ := hr
  rw [Ideal.dvd_iff_le]
  calc
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L)) (Ideal.rationalPrimeIdeal r)
      ≤ P ^ Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P := Ideal.le_pow_ramificationIdx
    _ = P ^ e := by rw [hidx P hP]

lemma pred_different_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r e : ℕ} (hr : Nat.Prime r)
    (hidx : RationalRamificationIdx (S := NumberField.RingOfIntegers L) r e)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    P ^ (e - 1) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  exact pow_sub_one_dvd_differentIdeal ℤ P e (rational_ne_bot hr)
    (ramification_dvd_idx
      (L := L) (hr := hr) hidx hP)

lemma abs_inertia_deg
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)] :
    Ideal.absNorm P = r ^ Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P := by
  letI : P.LiesOver (Ideal.span ({(r : ℤ)} : Set ℤ)) := by
    simpa using (show P.LiesOver (Ideal.rationalPrimeIdeal r) from inferInstance)
  have hprimeInt : Prime (r : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa
  simpa using
    (Ideal.absNorm_eq_pow_inertiaDeg
      (R := NumberField.RingOfIntegers L) (P := P) (p := (r : ℤ)) hprimeInt)

lemma abs_different_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r e : ℕ} (hr : Nat.Prime r)
    (hidx : RationalRamificationIdx (S := NumberField.RingOfIntegers L) r e)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    r ^ (Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P * (e - 1)) ∣
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  have hdiv : P ^ (e - 1) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    exact pred_different_idx
      (L := L) (hr := hr) hidx hP
  have hnorm : Ideal.absNorm (P ^ (e - 1)) ∣
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
    rcases hdiv with ⟨J, hJ⟩
    refine ⟨Ideal.absNorm J, ?_⟩
    rw [hJ, Ideal.absNorm.map_mul]
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r) := hP.2
  rw [show Ideal.absNorm (P ^ (e - 1)) = Ideal.absNorm P ^ (e - 1) by simp] at hnorm
  rw [abs_inertia_deg (L := L) (hr := hr) (P := P)] at hnorm
  simpa [pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnorm

lemma abs_different_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    r ^ (Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P * (e r - 1)) ∣
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  exact abs_different_idx
    (L := L) (r := r) (e := e r) (hSprime r hrS) (he_idx r (hSprime r hrS)) hP

lemma abs_discriminant_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] :
    absDiscriminant L =
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  calc
    absDiscriminant L = |(NumberField.discr L : ℝ)| := by
      rfl
    _ = ((NumberField.discr L).natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
    _ = Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
      rw [NumberField.absNorm_differentIdeal (K := L) (𝒪 := NumberField.RingOfIntegers L)]

lemma abs_different_ne
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] :
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) ≠ 0 := by
  rw [NumberField.absNorm_differentIdeal (K := L) (𝒪 := NumberField.RingOfIntegers L)]
  exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (K := L))

lemma factorization_support_subset
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hsupp : ∀ r ∉ S, n.factorization r = 0) :
    n = Finset.prod S (fun r => r ^ n.factorization r) := by
  have hsupp' : n.factorization.support ⊆ S := by
    intro r hr
    by_contra hrS
    have hz : n.factorization r = 0 := hsupp r hrS
    exact (Finsupp.mem_support_iff.mp hr) hz
  calc
    n = n.factorization.prod (fun r k => r ^ k) := by
      symm
      exact Nat.prod_factorization_pow_eq_self hn
    _ = Finset.prod n.factorization.support (fun r => r ^ n.factorization r) := by
      rfl
    _ = Finset.prod S (fun r => r ^ n.factorization r) := by
      exact Finset.prod_subset hsupp' (by
        intro r hrS hrnot
        have hz : n.factorization r = 0 := by
          exact not_not.mp (fun hne => hrnot (Finsupp.mem_support_iff.mpr hne))
        simp [hz])

lemma rational_deg_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) =
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P := by
  let _ := hr
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r) := hP.2
  exact Ideal.inertiaDegIn_eq_inertiaDeg
    (p := Ideal.rationalPrimeIdeal r) (P := P) (G := Gal(L/ℚ))

lemma factorization_abs_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) * (e r - 1) ≤
      (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r := by
  let P : Ideal (NumberField.RingOfIntegers L) :=
    (chosenPrimeRational (L := L) (hSprime r hrS)).1
  have hP :
      P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) := by
    dsimp [P]
    exact chosen_prime_rational (L := L) (hSprime r hrS)
  have hdiv :
      r ^ (Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P * (e r - 1)) ∣
        Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
    exact abs_different_indices
      (L := L) (S := S) (e := e) hSprime he_idx hrS hP
  have hle :
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P * (e r - 1) ≤
        (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization
      (hSprime r hrS) (abs_different_ne (L := L))).mp hdiv
  have hinertia :
      (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) =
        Ideal.inertiaDeg (Ideal.rationalPrimeIdeal r) P := by
    exact rational_deg_primes
      (L := L) (hr := hSprime r hrS) hP
  simpa [hinertia] using hle

lemma primes_deg_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    Module.finrank ℚ L - Module.finrank ℚ L / e r =
      ((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)).ncard *
        (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
          (e r - 1) := by
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  let g : ℕ := (qI.primesOver (NumberField.RingOfIntegers L)).ncard
  let f : ℕ := qI.inertiaDegIn (NumberField.RingOfIntegers L)
  have hr : Nat.Prime r := hSprime r hrS
  have heq_ram :
      e r = qI.ramificationIdxIn (NumberField.RingOfIntegers L) := by
    simpa [qI] using ramification_global_indices
      (L := L) (e := e) hr he_idx
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := rational_ideal_maximal hr
  have hmain :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := qI) hqI0 (NumberField.RingOfIntegers L) (Gal(L/ℚ))
  have hfin :
      Module.finrank ℚ L = g * (e r * f) := by
    calc
      Module.finrank ℚ L = Nat.card (Gal(L/ℚ)) := by
        symm
        exact IsGalois.card_aut_eq_finrank ℚ L
      _ = (qI.primesOver (NumberField.RingOfIntegers L)).ncard *
            (qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
              qI.inertiaDegIn (NumberField.RingOfIntegers L)) := by
              simpa using hmain.symm
      _ = g * (e r * f) := by
            simp [g, f, heq_ram]
  have he_ne_zero : e r ≠ 0 := by
    intro he0
    have hcop0 : Nat.Coprime r 0 := by
      simpa [he0] using he_coprime r hrS
    simp [Nat.Prime.ne_one hr] at hcop0
  have he_pos : 0 < e r := Nat.pos_of_ne_zero he_ne_zero
  have hdiv :
      (g * (e r * f)) / e r = g * f := by
    rw [show g * (e r * f) = e r * (g * f) by ac_rfl]
    exact Nat.mul_div_right _ he_pos
  calc
    Module.finrank ℚ L - Module.finrank ℚ L / e r
      = g * (e r * f) - (g * (e r * f)) / e r := by
          rw [hfin]
    _ = g * (e r * f) - g * f := by rw [hdiv]
    _ = g * (e r * f - f) := by
          rw [Nat.mul_sub_left_distrib]
    _ = g * ((e r - 1) * f) := by
          rw [show e r * f - f = e r * f - 1 * f by simp, ← Nat.sub_mul]
    _ = g * f * (e r - 1) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

lemma primes_finset_ncard
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [IsDomain A] [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p B).card = (p.primesOver B).ncard := by
  let hs : (p.primesOver B).Finite :=
    Set.Finite.ofFinset (IsDedekindDomain.primesOverFinset p B) (fun P =>
      IsDedekindDomain.mem_primesOverFinset_iff hp B)
  rw [Set.ncard_eq_toFinset_card (p.primesOver B) hs]
  congr
  ext P
  rw [hs.mem_toFinset]
  exact IsDedekindDomain.mem_primesOverFinset_iff hp B

lemma coprime_ne
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hQ : Q ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hPQ : P ≠ Q) :
    IsCoprime P Q := by
  letI : P.IsPrime := hP.1
  letI : Q.IsPrime := hQ.1
  have hP0 : P ≠ ⊥ := by
    intro hP0
    subst hP0
    exact (rational_ne_bot hr)
      (hP.2.over.trans (Ideal.under_bot ℤ (NumberField.RingOfIntegers L)))
  have hQ0 : Q ≠ ⊥ := by
    intro hQ0
    subst hQ0
    exact (rational_ne_bot hr)
      (hQ.2.over.trans (Ideal.under_bot ℤ (NumberField.RingOfIntegers L)))
  have hsup : P ⊔ Q = ⊤ := by
    by_contra hsup
    have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    have hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
    have hEqP : P = P ⊔ Q := hPmax.eq_of_le hsup le_sup_left
    have hEqQ : Q = P ⊔ Q := hQmax.eq_of_le hsup le_sup_right
    exact hPQ (hEqP.trans hEqQ.symm)
  exact (Ideal.isCoprime_iff_sup_eq).2 hsup

lemma powers_different_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L),
        P ^ (e r - 1) ∣
      differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  classical
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  have hr : Nat.Prime r := hSprime r hrS
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := by simpa [qI] using rational_ideal_maximal hr
  let T : Finset (Ideal (NumberField.RingOfIntegers L)) :=
    IsDedekindDomain.primesOverFinset qI (NumberField.RingOfIntegers L)
  have hmain :
      ∀ U : Finset (Ideal (NumberField.RingOfIntegers L)),
        U ⊆ T →
          ∏ P ∈ U, P ^ (e r - 1) ∣
            differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    intro U
    refine Finset.induction_on U ?_ ?_
    · intro hU
      rw [Ideal.dvd_iff_le]
      simp
    · intro P s hPs ih hU
      have hs_sub : s ⊆ T := by
        intro Q hQ
        exact hU (Finset.mem_insert_of_mem hQ)
      have ih' := ih hs_sub
      have hPmem_finset : P ∈ T := hU (Finset.mem_insert_self P s)
      have hPmem :
          P ∈ qI.primesOver (NumberField.RingOfIntegers L) := by
        exact (IsDedekindDomain.mem_primesOverFinset_iff hqI0 (NumberField.RingOfIntegers L)).1
          (by simpa [T] using hPmem_finset)
      have hPdiv :
          P ^ (e r - 1) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
        simpa [qI] using
        pred_different_idx
          (L := L) (r := r) (e := e r) hr (he_idx r hr) hPmem
      have hcop :
          IsCoprime (P ^ (e r - 1)) (∏ Q ∈ s, Q ^ (e r - 1)) := by
        apply IsCoprime.prod_right
        intro Q hQ
        apply IsCoprime.pow
        have hQmem_finset : Q ∈ T := hs_sub hQ
        have hQmem :
            Q ∈ qI.primesOver (NumberField.RingOfIntegers L) := by
          exact (IsDedekindDomain.mem_primesOverFinset_iff hqI0 (NumberField.RingOfIntegers L)).1
            (by simpa [T] using hQmem_finset)
        have hPQ : P ≠ Q := by
          intro hEq
          subst hEq
          exact hPs hQ
        simpa [qI] using coprime_ne
          (L := L) (hr := hr) hPmem hQmem hPQ
      rw [Ideal.dvd_iff_le] at hPdiv ih' ⊢
      rw [Finset.prod_insert hPs]
      rw [Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_iff_sup_eq).1 hcop)]
      exact le_inf hPdiv ih'
  simpa [T] using hmain T (by intro P hP; exact hP)

lemma pred_abs_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    r ^
        ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1))) ∣
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  classical
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  let T : Finset (Ideal (NumberField.RingOfIntegers L)) :=
    IsDedekindDomain.primesOverFinset qI (NumberField.RingOfIntegers L)
  have hr : Nat.Prime r := hSprime r hrS
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := by simpa [qI] using rational_ideal_maximal hr
  have hprod_div :
      ∏ P ∈ T, P ^ (e r - 1) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    simpa [T] using
      powers_different_indices
        (L := L) (S := S) (e := e) hSprime he_idx hrS
  have hnorm_div :
      Ideal.absNorm (∏ P ∈ T, P ^ (e r - 1)) ∣
        Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
    rcases hprod_div with ⟨J, hJ⟩
    refine ⟨Ideal.absNorm J, ?_⟩
    rw [hJ, Ideal.absNorm.map_mul]
  have hnorm_left :
      Ideal.absNorm (∏ P ∈ T, P ^ (e r - 1)) =
        r ^ (T.card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1))) := by
    calc
      Ideal.absNorm (∏ P ∈ T, P ^ (e r - 1))
        = ∏ P ∈ T, Ideal.absNorm (P ^ (e r - 1)) := by
            simp
      _ = ∏ P ∈ T, r ^
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1)) := by
            refine Finset.prod_congr rfl ?_
            intro P hP
            have hP' :
                P ∈ qI.primesOver (NumberField.RingOfIntegers L) := by
              exact (IsDedekindDomain.mem_primesOverFinset_iff hqI0 (NumberField.RingOfIntegers
                L)).1
                (by simpa [T] using hP)
            letI : P.LiesOver qI := hP'.2
            have hinertia :
                (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) =
                  Ideal.inertiaDeg qI P := by
              simpa [qI] using
                rational_deg_primes
                  (L := L) (hr := hr) hP'
            have habs :
                Ideal.absNorm P = r ^ Ideal.inertiaDeg qI P := by
              simpa [qI] using
                abs_inertia_deg
                  (L := L) (hr := hr) (P := P)
            rw [show Ideal.absNorm (P ^ (e r - 1)) = Ideal.absNorm P ^ (e r - 1) by simp]
            rw [habs]
            simp [hinertia, pow_mul]
      _ = r ^ (T.card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1))) := by
            simp [Finset.prod_const, pow_mul, Nat.mul_assoc, Nat.mul_comm]
  simpa [hnorm_left] using hnorm_div

lemma factorization_zero_dvd
    {n r : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0) (hndvd : ¬ r ∣ n) :
    n.factorization r = 0 := by
  by_contra hfac
  have hle : 1 ≤ n.factorization r := Nat.one_le_iff_ne_zero.mpr hfac
  exact hndvd ((Nat.Prime.dvd_iff_one_le_factorization hr hn).2 hle)

lemma rational_ideal_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) ≤ P := by
  rw [Ideal.map_le_iff_le_comap]
  simpa [Ideal.under] using le_of_eq hP.2.over

lemma ramification_idx_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1)
    {r : ℕ} (hr : Nat.Prime r) (hrS : r ∉ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = 1 := by
  simpa [he_one hrS] using he_idx r hr P hP

lemma prime_ne_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    P ≠ ⊥ := by
  intro hP0
  subst hP0
  exact (rational_ne_bot hr)
    (hP.2.over.trans (Ideal.under_bot ℤ (NumberField.RingOfIntegers L)))

lemma rational_prime_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)} [P.IsPrime]
    (hmap_le :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≤ P) :
    P.LiesOver (Ideal.rationalPrimeIdeal r) := by
  have hunder_le : Ideal.rationalPrimeIdeal r ≤ Ideal.under ℤ P := by
    rw [Ideal.map_le_iff_le_comap] at hmap_le
    simpa [Ideal.under] using hmap_le
  have hunder_ne_top : Ideal.under ℤ P ≠ ⊤ := by
    intro htop
    have h1 : (1 : ℤ) ∈ Ideal.under ℤ P := by simp [htop]
    have h1' : (1 : NumberField.RingOfIntegers L) ∈ P := by
      simpa [Ideal.under] using h1
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem P h1' (by
        simp))
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  exact Ideal.LiesOver.mk
    ((rational_ideal_maximal hr).eq_of_le hunder_ne_top hunder_le)

lemma rational_maximal_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1)
    {r : ℕ} (hr : Nat.Prime r) (hrS : r ∉ S)
    {P : Ideal (NumberField.RingOfIntegers L)} [P.IsPrime]
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.map
        (algebraMap ℤ (Localization.AtPrime P))
        (Ideal.rationalPrimeIdeal r) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hmap_le :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) ≤ P :=
    rational_ideal_primes (L := L) hP
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  exact
    (Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff
      (p := Ideal.rationalPrimeIdeal r) (P := P)
      hP0 hmap_le).1
      (ramification_idx_not
        (L := L) (S := S) (e := e) he_idx he_one hr hrS hP)

lemma dvd_different_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1)
    {r : ℕ} (hr : Nat.Prime r) (hrS : r ∉ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    ¬ P ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  letI : P.IsPrime := hP.1
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  have hunram : Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ)
      (S := NumberField.RingOfIntegers L) (p := P) hP0]
    have hover :
        Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers L)) P =
          Ideal.rationalPrimeIdeal r := by
      simpa [Ideal.under] using hP.2.over.symm
    have hram :
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = 1 :=
      ramification_idx_not
        (L := L) (S := S) (e := e) he_idx he_one hr hrS hP
    rw [← hP.2.over]
    exact hram
  exact (not_dvd_differentIdeal_iff.2 hunram)

lemma sup_different_dvd
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (hnot : ∀ P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L),
      ¬ P ∣ differentIdeal ℤ (NumberField.RingOfIntegers L)) :
    Ideal.map
        (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) ⊔
      differentIdeal ℤ (NumberField.RingOfIntegers L) = ⊤ := by
  by_contra hsup
  rcases Ideal.exists_le_maximal
      (Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        differentIdeal ℤ (NumberField.RingOfIntegers L)) hsup with
    ⟨P, hPmax, hPle⟩
  letI : P.IsPrime := hPmax.isPrime
  have hmap_le :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≤ P :=
    le_trans le_sup_left hPle
  have hD_le : differentIdeal ℤ (NumberField.RingOfIntegers L) ≤ P :=
    le_trans le_sup_right hPle
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r) :=
    rational_prime_lies (L := L) hr hmap_le
  have hPmem : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) :=
    ⟨inferInstance, inferInstance⟩
  exact hnot P hPmem ((Ideal.dvd_iff_le).2 hD_le)

lemma rational_span_cast
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (r : ℕ) :
    Ideal.map
        (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) =
      Ideal.span ({(r : NumberField.RingOfIntegers L)} : Set (NumberField.RingOfIntegers L)) := by
  simpa [Ideal.rationalPrimeIdeal] using
    (Ideal.map_span
      (algebraMap ℤ (NumberField.RingOfIntegers L))
      ({(r : ℤ)} : Set ℤ))

lemma r_different_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    (hsup :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        differentIdeal ℤ (NumberField.RingOfIntegers L) = ⊤) :
    IsUnit
      ((Ideal.Quotient.mk (differentIdeal ℤ (NumberField.RingOfIntegers L)))
        (r : NumberField.RingOfIntegers L)) := by
  have h1_mem :
      (1 : NumberField.RingOfIntegers L) ∈
        Ideal.map
            (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.rationalPrimeIdeal r) ⊔
          differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    rw [hsup]
    simp
  rcases (Submodule.mem_sup).1 h1_mem with ⟨a, ha, b, hb, hab⟩
  rw [rational_span_cast (L := L) r] at ha
  rcases (Ideal.mem_span_singleton').1 ha with ⟨c, hc⟩
  let q := Ideal.Quotient.mk (differentIdeal ℤ (NumberField.RingOfIntegers L))
  have hq_b : q b = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hb
  have hmul :
      q c * q (r : NumberField.RingOfIntegers L) = 1 := by
    have hqab : q a + q b = 1 := by
      simpa using congrArg q hab
    have hqa : q a = q c * q (r : NumberField.RingOfIntegers L) := by
      rw [← hc]
      simp [q]
    calc
      q c * q (r : NumberField.RingOfIntegers L) = q a := hqa.symm
      _ = q a + q b := by
            rw [hq_b]
            symm
            exact add_zero (q a)
      _ = 1 := hqab
  exact (isUnit_iff_exists_inv).2 ⟨q c, by
    simpa [mul_comm] using hmul⟩

lemma abs_norm_ne
    (O : Type*) [CommRing O] [Nontrivial O] [IsDedekindDomain O] [Module.Free ℤ O]
    {I : Ideal O} (hI0 : Ideal.absNorm I ≠ 0) :
    Finite (O ⧸ I) := by
  have hpos : 0 < Nat.card (O ⧸ I) := by
    simpa [Ideal.absNorm] using Nat.pos_of_ne_zero hI0
  exact (Nat.card_pos_iff.mp hpos).2

lemma not_abs_r
    (O : Type*) [CommRing O] [Nontrivial O] [IsDedekindDomain O]
    [Module.Free ℤ O] [Module.Finite ℤ O]
    {I : Ideal O} (hI0 : Ideal.absNorm I ≠ 0)
    {r : ℕ} (hr : Nat.Prime r)
    (hunit : IsUnit ((Ideal.Quotient.mk I) (r : O))) :
    ¬ r ∣ Ideal.absNorm I := by
  intro hdvd
  let G := O ⧸ I.toAddSubgroup
  have hGpos : 0 < Nat.card G := by
    simpa [G, Ideal.absNorm, Submodule.cardQuot, AddSubgroup.index_eq_card] using
      Nat.pos_of_ne_zero hI0
  letI : Finite G := (Nat.card_pos_iff.mp hGpos).2
  letI : Fintype G := Fintype.ofFinite G
  have hdvd_card : r ∣ Fintype.card G := by
    simpa [G, Ideal.absNorm, Submodule.cardQuot, AddSubgroup.index_eq_card,
      Nat.card_eq_fintype_card] using hdvd
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  let q := Ideal.Quotient.mk I
  let g : G →+ O ⧸ I :=
    QuotientAddGroup.lift I.toAddSubgroup q.toAddMonoidHom (by
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hx)
  have hg_zero : ∀ x : G, g x = 0 → x = 0 := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a ha
    dsimp [g] at ha ⊢
    apply (QuotientAddGroup.eq).2
    simpa using I.neg_mem ((Ideal.Quotient.eq_zero_iff_mem).1 ha)
  rcases exists_prime_addOrderOf_dvd_card r hdvd_card with ⟨x, hx⟩
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    rw [hx0, addOrderOf_zero] at hx
    have : r = 1 := hx.symm
    exact hr.ne_one this
  have hsmul_zero : r • x = 0 := by
    simpa [hx] using addOrderOf_nsmul_eq_zero x
  have hmul_zero : q (r : O) * g x = 0 := by
    have hmap_zero : r • g x = 0 := by
      simpa [g] using congrArg g hsmul_zero
    simpa [q, nsmul_eq_mul] using hmap_zero
  rcases (isUnit_iff_exists_inv).1 hunit with ⟨u, hu⟩
  have hgx_zero : g x = 0 := by
    calc
      g x = (1 : O ⧸ I) * g x := by simp
      _ = (q (r : O) * u) * g x := by rw [hu]
      _ = q (r : O) * (u * g x) := by simp [mul_assoc]
      _ = (q (r : O) * g x) * u := by ac_rfl
      _ = 0 := by
            calc
              (q (r : O) * g x) * u = 0 * u := by rw [hmul_zero]
              _ = 0 := zero_mul u
  exact hx_ne_zero (hg_zero x hgx_zero)

lemma not_abs_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1)
    {r : ℕ} (hr : Nat.Prime r) (hrS : r ∉ S) :
    ¬ r ∣ Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  have hsup :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        differentIdeal ℤ (NumberField.RingOfIntegers L) = ⊤ := by
    exact sup_different_dvd
      (L := L) hr
      (fun P hP =>
        dvd_different_ideal
          (L := L) (S := S) (e := e) he_idx he_one hr hrS hP)
  have hunit :
      IsUnit
        ((Ideal.Quotient.mk (differentIdeal ℤ (NumberField.RingOfIntegers L)))
          (r : NumberField.RingOfIntegers L)) := by
    exact r_different_top
      (L := L) hsup
  exact not_abs_r
    (O := NumberField.RingOfIntegers L)
    (I := differentIdeal ℤ (NumberField.RingOfIntegers L))
    (abs_different_ne (L := L)) hr hunit

lemma abs_different_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1)
    {r : ℕ} (hrS : r ∉ S) :
    (Ideal.absNorm
      (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r = 0 := by
  let _ := hSprime
  by_cases hr : Nat.Prime r
  · exact factorization_zero_dvd hr
      (abs_different_ne (L := L))
      (not_abs_different
        (L := L) (S := S) (e := e) he_idx he_one hr hrS)
  · exact Nat.factorization_eq_zero_of_not_prime
      (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))) hr

lemma abs_different_s
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1) :
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) =
      Finset.prod S (fun r =>
        r ^
          (Ideal.absNorm
            (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r) := by
  exact factorization_support_subset
    (n := Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)))
    (abs_different_ne (L := L)) S
    (fun r hrS =>
      abs_different_not
        (L := L) (S := S) (e := e) hSprime he_idx he_one hrS)

lemma factorization_abs_target
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    Module.finrank ℚ L - Module.finrank ℚ L / e r ≤
      (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r := by
  have hr : Nat.Prime r := hSprime r hrS
  have hdiv :
      r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1))) ∣
        Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
    exact pred_abs_different
      (L := L) (S := S) (e := e) hSprime he_idx hrS
  have hle :
      (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) ≤
        (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization
      hr (abs_different_ne (L := L))).mp hdiv
  have hcard :
      (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card =
        ((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)).ncard := by
    letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
    exact primes_finset_ncard
      (p := Ideal.rationalPrimeIdeal r) (B := NumberField.RingOfIntegers L)
      (rational_ne_bot hr)
  have htarget :
      Module.finrank ℚ L - Module.finrank ℚ L / e r =
        (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) := by
    calc
      Module.finrank ℚ L - Module.finrank ℚ L / e r
        = ((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)).ncard *
            (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1) := by
                exact primes_deg_pred
                  (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS
      _ = (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
            (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1) := by
                rw [← hcard]
      _ = (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1)) := by
                rw [Nat.mul_assoc]
  simpa [htarget] using hle

lemma factorization_not_dvd
    {n r k : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0)
    (hnot : ¬ r ^ (k + 1) ∣ n) :
    n.factorization r ≤ k := by
  by_contra hle
  have hgt : k < n.factorization r := Nat.not_le.mp hle
  have hk : k + 1 ≤ n.factorization r := Nat.succ_le_of_lt hgt
  exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization hr hn).2 hk)

lemma target_deg_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    Module.finrank ℚ L - Module.finrank ℚ L / e r =
      (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
        ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
          (e r - 1)) := by
  have hr : Nat.Prime r := hSprime r hrS
  have hcard :
      (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card =
        ((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)).ncard := by
    letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
    exact primes_finset_ncard
      (p := Ideal.rationalPrimeIdeal r) (B := NumberField.RingOfIntegers L)
      (rational_ne_bot hr)
  calc
    Module.finrank ℚ L - Module.finrank ℚ L / e r
      = ((Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)).ncard *
          (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1) := by
              exact primes_deg_pred
                (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS
    _ = (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L)).card *
          (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1) := by
              rw [← hcard]
    _ = (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) := by
              rw [Nat.mul_assoc]

lemma ramification_idx_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
      e r := by
  exact he_idx r (hSprime r hrS) P hP

lemma idx_coprime_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) := by
  have hram :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
        e r := by
    exact ramification_idx_indices
      (L := L) (S := S) (e := e) hSprime he_idx hrS hP
  simpa [← hram] using he_coprime r hrS

lemma ramification_different_witness
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r e : ℕ}
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hPQ :
      P ^ e * Q =
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r))
    {x : NumberField.RingOfIntegers L}
    (hxQ : x ∈ Q)
    (htrace : Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∉
      Ideal.rationalPrimeIdeal r) :
    ¬ P ^ e ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  exact not_dvd_differentIdeal_of_intTrace_not_mem
    (A := ℤ) (B := NumberField.RingOfIntegers L) (p := Ideal.rationalPrimeIdeal r)
    (P := P ^ e) (Q := Q) hPQ x hxQ htrace

lemma ramification_idx_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P ≠ 0 := by
  intro hzero
  have hcop0 := hcop
  rw [hzero] at hcop0
  simp [Nat.Prime.ne_one hr] at hcop0

lemma idx_pos_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    0 <
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P := by
  exact Nat.pos_of_ne_zero
    (ramification_idx_coprime (L := L) (hr := hr) hcop)

lemma ramification_idx_mapped
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    P ^
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ∣
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) := by
  let _ := hr
  let _ := hP
  rw [Ideal.dvd_iff_le]
  exact Ideal.le_pow_ramificationIdx

lemma factor_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L),
      P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q =
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) := by
  rcases ramification_idx_mapped
      (L := L) (hr := hr) hP with ⟨Q, hQ⟩
  exact ⟨Q, hQ.symm⟩

lemma mapped_ne_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) ≠ ⊥ := by
  intro hbot
  have hr_mem :
      (r : NumberField.RingOfIntegers L) ∈
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) := by
    rw [rational_span_cast (L := L) r]
    exact Ideal.subset_span (by simp)
  rw [hbot] at hr_mem
  have hr_zero : (r : NumberField.RingOfIntegers L) = 0 := by
    simpa using hr_mem
  exact (Nat.cast_ne_zero.mpr hr.ne_zero) hr_zero

lemma count_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Multiset.count P
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.rationalPrimeIdeal r))) =
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P := by
  have hmap0 :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≠ ⊥ := by
    exact mapped_ne_bot (L := L) (hr := hr)
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  letI : P.IsPrime := hP.1
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal hP.1 hP0
  let c :=
    Multiset.count P
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r)))
  rcases Ideal.eq_prime_pow_mul_coprime hmap0 P with ⟨Q, hsup, hfac⟩
  have hle :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≤
        P ^ c := by
    rw [hfac]
    exact Ideal.mul_le_right
  have hgt :
      ¬ Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.rationalPrimeIdeal r) ≤
          P ^ (c + 1) := by
    intro hnext
    have hnext' : P ^ c * Q ≤ P ^ (c + 1) := by
      rw [hfac] at hnext
      exact hnext
    have hpowEq : P ^ c = P ^ (c + 1) := by
      calc
        P ^ c = P ^ c * ⊤ := by rw [Ideal.mul_top]
        _ = P ^ c * (P ⊔ Q) := by rw [hsup]
        _ = P ^ c * P ⊔ P ^ c * Q := by rw [Ideal.mul_sup]
        _ = P ^ (c + 1) ⊔ P ^ c * Q := by rw [pow_succ]
        _ = P ^ (c + 1) := by
          apply sup_eq_left.mpr
          exact hnext'
    have hstrict :=
      Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top hP.1)
    exact (ne_of_lt (hstrict (Nat.lt_succ_self c))) hpowEq.symm
  have hram :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = c := by
    exact Ideal.ramificationIdx_spec hle hgt
  simpa [c] using hram.symm

lemma coprime_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L),
      P ⊔ Q = ⊤ ∧
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q := by
  have hmap0 :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≠ ⊥ := by
    exact mapped_ne_bot (L := L) (hr := hr)
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal hP.1 hP0
  rcases Ideal.eq_prime_pow_mul_coprime hmap0 P with ⟨Q, hsup, hfac⟩
  have hcount :
      Multiset.count P
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
              (Ideal.rationalPrimeIdeal r))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P := by
    exact count_ramification_idx
      (L := L) (hr := hr) hP
  refine ⟨Q, hsup, ?_⟩
  rw [hfac, hcount]

lemma int_dvd_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {I Q : Ideal (NumberField.RingOfIntegers L)}
    (hIQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        I * Q)
    (hI : I ∣ differentIdeal ℤ (NumberField.RingOfIntegers L))
    {x : NumberField.RingOfIntegers L}
    (hxQ : x ∈ Q) :
    Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∈
      Ideal.rationalPrimeIdeal r := by
  let _ := hr
  by_contra htrace
  exact
    (not_dvd_differentIdeal_of_intTrace_not_mem
      (A := ℤ) (B := NumberField.RingOfIntegers L)
      (p := Ideal.rationalPrimeIdeal r) (P := I) (Q := Q)
      hIQ.symm x hxQ htrace) hI

lemma forall_dvd_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {I Q : Ideal (NumberField.RingOfIntegers L)}
    (hIQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        I * Q)
    (hI : I ∣ differentIdeal ℤ (NumberField.RingOfIntegers L)) :
    ∀ x : NumberField.RingOfIntegers L,
      x ∈ Q →
      Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∈
        Ideal.rationalPrimeIdeal r := by
  intro x hxQ
  exact int_dvd_different
    (L := L) (hr := hr) hIQ hI hxQ

lemma factorization_different_forall
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {I Q : Ideal (NumberField.RingOfIntegers L)}
    (hIQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        I * Q)
    (hall :
      ∀ x : NumberField.RingOfIntegers L,
        x ∈ Q →
        Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∈
          Ideal.rationalPrimeIdeal r) :
    I ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  let O := NumberField.RingOfIntegers L
  let F := FractionalIdeal (nonZeroDivisors O) L
  rw [Ideal.dvd_iff_le]
  have hmap0 :
      Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) ≠ ⊥ := by
    exact mapped_ne_bot (L := L) (hr := hr)
  have hI0 : I ≠ ⊥ := by
    intro hIbot
    apply hmap0
    simpa [hIbot] using hIQ
  have hI0F : ((I : Ideal O) : F) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).2 hI0
  rw [differentialIdeal_le_iff (A := ℤ) (K := ℚ) (L := L) (B := O) hI0]
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_one]
  have hIQF :
      ((Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) : Ideal O) : F) =
        (I : F) * (Q : F) := by
    simpa [F, FractionalIdeal.coeIdeal_mul] using
      congrArg (fun J : Ideal O => (J : F)) hIQ
  have hQeq :
      ((Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) : Ideal O) : F) *
          ((I : F)⁻¹) =
        (Q : F) := by
    calc
      ((Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) : Ideal O) : F) *
            ((I : F)⁻¹)
          = ((I : F) * (Q : F)) * ((I : F)⁻¹) := by rw [hIQF]
      _ = (Q : F) * ((I : F) * ((I : F)⁻¹)) := by
            ac_rfl
      _ = (Q : F) * 1 := by rw [mul_inv_cancel₀ hI0F]
      _ = (Q : F) := by rw [mul_one]
  have hr_mem_map :
      (algebraMap O L (r : O)) ∈
        ((Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) : Ideal O) : F) := by
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨(r : O), ?_, rfl⟩
    rw [rational_span_cast (L := L) r]
    exact Ideal.subset_span (by simp)
  have hrx_mem_Q :
      (algebraMap O L (r : O)) * x ∈ (Q : F) := by
    have hmem :
        (algebraMap O L (r : O)) * x ∈
          ((Ideal.map (algebraMap ℤ O) (Ideal.rationalPrimeIdeal r) : Ideal O) : F) *
            ((I : F)⁻¹) := by
      exact FractionalIdeal.mul_mem_mul hr_mem_map hx
    rw [hQeq] at hmem
    exact hmem
  rw [FractionalIdeal.mem_coeIdeal] at hrx_mem_Q
  rcases hrx_mem_Q with ⟨q, hqQ, hqeq⟩
  have hqtrace : Algebra.intTrace ℤ O q ∈ Ideal.rationalPrimeIdeal r := hall q hqQ
  rw [Ideal.rationalPrimeIdeal, Ideal.mem_span_singleton] at hqtrace
  rcases hqtrace with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have htrace_eq :
      (algebraMap ℤ ℚ) (Algebra.intTrace ℤ O q) =
        (r : ℚ) * Algebra.trace ℚ L x := by
    calc
      (algebraMap ℤ ℚ) (Algebra.intTrace ℤ O q)
          = Algebra.trace ℚ L (algebraMap O L q) := by
              simpa [O] using
                (Algebra.algebraMap_intTrace
                  (A := ℤ) (K := ℚ) (L := L) (B := O) q)
      _ = Algebra.trace ℚ L ((algebraMap O L (r : O)) * x) := by rw [hqeq]
      _ = Algebra.trace ℚ L ((r : ℚ) • x) := by simp [Algebra.smul_def, O]
      _ = (r : ℚ) * Algebra.trace ℚ L x := by
            simpa [Algebra.smul_def] using (Algebra.trace ℚ L).map_smul (r : ℚ) x
  have hmul_eq :
      (r : ℚ) * Algebra.trace ℚ L x = (r : ℚ) * (algebraMap ℤ ℚ n) := by
    calc
      (r : ℚ) * Algebra.trace ℚ L x
          = (algebraMap ℤ ℚ) (Algebra.intTrace ℤ O q) := by
              symm
              exact htrace_eq
      _ = (algebraMap ℤ ℚ) ((r : ℤ) * n) := by rw [hn]
      _ = (r : ℚ) * (algebraMap ℤ ℚ n) := by simp
  have hr0Q : (r : ℚ) ≠ 0 := by
    exact_mod_cast hr.ne_zero
  have hcancel :=
    congrArg (fun t : ℚ => (r : ℚ)⁻¹ * t) hmul_eq
  simpa [mul_assoc, hr0Q] using hcancel.symm

lemma witness_factorization_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {I Q : Ideal (NumberField.RingOfIntegers L)}
    (hIQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        I * Q)
    (hnot : ¬ I ∣ differentIdeal ℤ (NumberField.RingOfIntegers L)) :
    ∃ x : NumberField.RingOfIntegers L,
      x ∈ Q ∧
      Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∉
        Ideal.rationalPrimeIdeal r := by
  by_contra hcontra
  have hall :
      ∀ x : NumberField.RingOfIntegers L,
        x ∈ Q →
        Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∈
          Ideal.rationalPrimeIdeal r := by
    intro x hxQ
    by_contra htrace
    exact hcontra ⟨x, hxQ, htrace⟩
  exact hnot <|
    factorization_different_forall
      (L := L) (hr := hr) hIQ hall

lemma trace_restrict_maps
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Module.Free K V]
    {p : Submodule K V} {f : V →ₗ[K] V}
    (hf : ∀ x, f x ∈ p) :
    LinearMap.trace K V f =
      LinearMap.trace K p (f.restrict (fun x _ => hf x)) := by
  symm
  exact LinearMap.trace_restrict_eq_of_forall_mem p f hf

lemma quotientEquiv_apply
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : Submodule K V} (hpq : IsCompl p q) (x : V) :
    Submodule.quotientEquivOfIsCompl p q hpq (Submodule.Quotient.mk x) =
      q.projectionOnto p hpq.symm x := by
  exact Submodule.quotientEquivOfIsCompl_apply_mk hpq x

lemma compl_conj_q
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    {p q : Submodule K V} (hpq : IsCompl p q)
    {f : V →ₗ[K] V}
    (hf : p ≤ p.comap f) :
    (Submodule.quotientEquivOfIsCompl p q hpq).conj (p.mapQ p f hf) =
      (q.projectionOnto p hpq.symm).comp (f.comp q.subtype) := by
  ext x
  rw [LinearEquiv.conj_apply]
  simp [Submodule.mapQ_apply]

noncomputable def submoduleQuotientEquiv
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : p = q) :
    (M ⧸ p) ≃ₗ[R] (M ⧸ q) := by
  cases h
  exact LinearEquiv.refl R (M ⧸ p)

@[simp] lemma submodule_quotient_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : p = q) (x : M) :
    submoduleQuotientEquiv h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  cases h
  rfl

lemma trace_restrict_q
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Module.Free K V]
    {p : Submodule K V} {f : V →ₗ[K] V}
    (hf : p ≤ p.comap f) :
    LinearMap.trace K V f =
      LinearMap.trace K p (f.restrict (fun _ hx => hf hx)) +
      LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by
  classical
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  let fp : V →ₗ[K] V := (p.projection q hpq).comp f
  let fq : V →ₗ[K] V := (q.projection p hpq.symm).comp f
  have hsplit :
      f = fp + fq := by
    ext x
    change f x =
      p.projection q hpq (f x) + q.projection p hpq.symm (f x)
    symm
    exact Submodule.projection_add_projection_eq_self hpq (f x)
  have hfp_map : ∀ x, fp x ∈ p := by
    intro x
    exact Submodule.projection_apply_mem hpq (f x)
  have hfp_trace :
      LinearMap.trace K V fp =
        LinearMap.trace K p (f.restrict (fun _ hx => hf hx)) := by
    calc
      LinearMap.trace K V fp =
          LinearMap.trace K p (fp.restrict (fun x _ => hfp_map x)) := by
            exact trace_restrict_maps hfp_map
      _ = LinearMap.trace K p (f.restrict (fun _ hx => hf hx)) := by
            congr 1
            ext x
            change fp x = f x
            simpa [fp, hf x.2] using
              Submodule.projection_apply_left hpq ⟨f x, hf x.2⟩
  have hfq_map : ∀ x, fq x ∈ q := by
    intro x
    exact Submodule.projection_apply_mem hpq.symm (f x)
  have hfq_trace :
      LinearMap.trace K V fq =
        LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by
    calc
      LinearMap.trace K V fq =
          LinearMap.trace K q (fq.restrict (fun x _ => hfq_map x)) := by
            exact trace_restrict_maps hfq_map
      _ = LinearMap.trace K q
            ((q.projectionOnto p hpq.symm).comp (f.comp q.subtype)) := by
            rfl
      _ = LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by
            rw [← LinearMap.trace_conj'
              (p.mapQ p f hf) (Submodule.quotientEquivOfIsCompl p q hpq)]
            simp [compl_conj_q]
  calc
    LinearMap.trace K V f = LinearMap.trace K V (fp + fq) := by rw [hsplit]
    _ = LinearMap.trace K V fp + LinearMap.trace K V fq := by
          simp
    _ = LinearMap.trace K p (f.restrict (fun _ hx => hf hx)) +
          LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by
          rw [hfp_trace, hfq_trace]

noncomputable def powQuotImage
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x :
      NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    (i : ℕ) :
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) := by
  refine
    { toFun := fun z => ⟨x * z, ?_⟩
      map_add' := by
        intro z w
        apply Subtype.ext
        simpa using mul_add x (z : _) (w : _)
      map_smul' := by
        intro c z
        apply Subtype.ext
        change x * (c • (z : _)) = c • (x * (z : _))
        rw [Algebra.smul_def, Algebra.smul_def]
        ac_rfl }
  rcases (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 z.2 with
    ⟨y, hy, hyz⟩
  rcases Ideal.Quotient.mk_surjective x with ⟨x0, hx0⟩
  rw [← hyz, ← hx0]
  have hmem :
      (Ideal.Quotient.mk
        (P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) (x0 * y) ∈
        Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ i) := by
    simpa using
      (Ideal.mem_map_of_mem
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (Ideal.mul_mem_left (P ^ i) x0 hy))
  change
    (Ideal.Quotient.mk
      (P ^
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) (x0 * y) ∈
      Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)
  exact hmem

noncomputable def primePowImage
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) := by
  let O := NumberField.RingOfIntegers L
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let μ : O ⧸ P ^ e →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r] O ⧸ P ^ e :=
    (Algebra.lmul (ℤ ⧸ Ideal.rationalPrimeIdeal r) (O ⧸ P ^ e))
      (Ideal.Quotient.mk (P ^ e) x)
  refine
    { toFun := fun z => ⟨μ z, ?_⟩
      map_add' := by
        intro z w
        ext
        exact μ.map_add z w
      map_smul' := by
        intro c z
        ext
        exact μ.map_smul c z }
  rcases (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 z.2 with
    ⟨y, hy, hyz⟩
  rw [← hyz]
  exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hy)

lemma quot_image_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    powQuotImage (L := L) (r := r) (P := P)
        ((Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) x)
        i =
      primePowImage (L := L) (r := r) (P := P) x i := by
  ext z
  rfl

lemma quot_comp_inclusion
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x :
      NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    (i : ℕ) :
    (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i ∘ₗ
        powQuotImage (L := L) (r := r) (P := P) x (i + 1) =
      powQuotImage (L := L) (r := r) (P := P) x i ∘ₗ
        (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i := by
  ext z
  rfl

lemma quot_image_range
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x :
      NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    (i : ℕ) :
    LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) ≤
      Submodule.comap
        (powQuotImage (L := L) (r := r) (P := P) x i)
        (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) := by
  rintro z ⟨y, rfl⟩
  refine ⟨powQuotImage (L := L) (r := r) (P := P) x (i + 1) y, ?_⟩
  exact congrArg (fun f => f y)
    (quot_comp_inclusion
      (L := L) (r := r) (P := P) x i)

lemma pow_not_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    {i : ℕ}
    (_hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    ∃ a : NumberField.RingOfIntegers L,
      a ∈ P ^ i ∧
      a ∉
        P ^ (i + 1) := by
  classical
  have hstrict :=
    Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  have hnotle : ¬ P ^ i ≤ P ^ (i + 1) := by
    exact not_le_of_gt (hstrict (Nat.lt_succ_self i))
  by_contra h
  apply hnotle
  intro a ha
  by_contra hnext
  exact h ⟨a, ha, hnext⟩

noncomputable def quotSuccGenerator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    NumberField.RingOfIntegers L :=
  Classical.choose
    (pow_not_succ
      (L := L) (r := r) (P := P) hP0 hi)

lemma quot_succ_generator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi ∈
      P ^ i := by
  exact
    (Classical.choose_spec
      (pow_not_succ
        (L := L) (r := r) (P := P) hP0 hi)).1

lemma pow_quot_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi ∉
      P ^ (i + 1) := by
  exact
    (Classical.choose_spec
      (pow_not_succ
        (L := L) (r := r) (P := P) hP0 hi)).2

lemma pow_quot_span
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Ideal.span
        ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
          Set (NumberField.RingOfIntegers L)) ≤
      P ^ i := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi

lemma quot_span_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    ¬ Ideal.span
          ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
            Set (NumberField.RingOfIntegers L)) ≤
        P ^ (i + 1) := by
  intro hle
  exact
    pow_quot_not (L := L) (r := r) (P := P) hP0 i hi
      (hle (Ideal.subset_span (by simp)))

lemma not_succ_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (hsup : P ⊔ Q = ⊤)
    (i : ℕ) :
    ¬ P ^ i * Q ≤ P ^ (i + 1) := by
  intro hnext
  have hpowEq : P ^ i = P ^ (i + 1) := by
    calc
      P ^ i = P ^ i * ⊤ := by rw [Ideal.mul_top]
      _ = P ^ i * (P ⊔ Q) := by rw [hsup]
      _ = P ^ i * P ⊔ P ^ i * Q := by rw [Ideal.mul_sup]
      _ = P ^ (i + 1) ⊔ P ^ i * Q := by rw [pow_succ]
      _ = P ^ (i + 1) := by
        apply sup_eq_left.mpr
        exact hnext
  have hstrict :=
    Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top inferInstance)
  exact (ne_of_lt (hstrict (Nat.lt_succ_self i))) hpowEq.symm

lemma coprime_not_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {P I : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (hI0 : I ≠ ⊥)
    {i : ℕ}
    (hIle : I ≤ P ^ i)
    (hInle : ¬ I ≤ P ^ (i + 1)) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L), P ⊔ Q = ⊤ ∧ I = P ^ i * Q := by
  let c :=
    Multiset.count P
      (UniqueFactorizationMonoid.normalizedFactors I)
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  rcases Ideal.eq_prime_pow_mul_coprime hI0 P with ⟨Q, hsup, hfac⟩
  have hnot_lt_ci : ¬ c < i := by
    intro hci
    have hpow : P ^ i ≤ P ^ (c + 1) := by
      exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hci)
    have hIc1 : I ≤ P ^ (c + 1) := by
      exact le_trans hIle hpow
    have hPc1 : P ^ c * Q ≤ P ^ (c + 1) := by
      rw [← hfac]
      exact hIc1
    exact
      (not_succ_coprime
        (L := L) (P := P) (Q := Q) hP0 hsup c) hPc1
  have hnot_lt_ic : ¬ i < c := by
    intro hic
    have hpow : P ^ c ≤ P ^ (i + 1) := by
      exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hic)
    have hIc : I ≤ P ^ c := by
      rw [hfac]
      exact Ideal.mul_le_right
    exact hInle (le_trans hIc hpow)
  have hci : c = i := by
    exact Nat.le_antisymm (Nat.le_of_not_lt hnot_lt_ic) (Nat.le_of_not_lt hnot_lt_ci)
  have hfac' : I = P ^ c * Q := by
    simpa [c] using hfac
  rw [hci] at hfac'
  exact ⟨Q, hsup, hfac'⟩

lemma pow_quot_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L),
      P ⊔ Q = ⊤ ∧
      Ideal.span
          ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
            Set (NumberField.RingOfIntegers L)) =
        P ^ i * Q := by
  let I :=
    Ideal.span
      ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
        Set (NumberField.RingOfIntegers L))
  have hIle : I ≤ P ^ i := by
    exact pow_quot_span (L := L) (r := r) (P := P) hP0 i hi
  have hInle : ¬ I ≤ P ^ (i + 1) := by
    exact quot_span_not (L := L) (r := r) (P := P) hP0 i hi
  have hI0 : I ≠ ⊥ := by
    intro hbot
    exact hInle (by simp [I, hbot])
  exact
    coprime_not_succ
      (L := L) (P := P) (I := I) hP0 hI0 hIle hInle

lemma quot_span_sup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Ideal.span
        ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
          Set (NumberField.RingOfIntegers L)) ⊔
      P ^ (i + 1) =
        P ^ i := by
  rcases pow_quot_coprime
      (L := L) (r := r) (P := P) hP0 i hi with ⟨Q, hsup, hfac⟩
  calc
    Ideal.span
        ({quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi} :
          Set (NumberField.RingOfIntegers L)) ⊔
      P ^ (i + 1)
        = P ^ i * Q ⊔ P ^ i * P := by
            rw [hfac, pow_succ]
    _ = P ^ i * (Q ⊔ P) := by rw [Ideal.mul_sup]
    _ = P ^ i * ⊤ := by rw [sup_comm, hsup]
    _ = P ^ i := by rw [Ideal.mul_top]

lemma singleton_sup_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    {x : NumberField.RingOfIntegers L}
    (hx : x ∉ P) :
    Ideal.span ({x} : Set (NumberField.RingOfIntegers L)) ⊔ P = ⊤ := by
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  by_contra hsup
  have hEq : P = Ideal.span ({x} : Set (NumberField.RingOfIntegers L)) ⊔ P := by
    exact (Ideal.IsPrime.isMaximal inferInstance hP0).eq_of_le hsup le_sup_right
  have hx' : x ∈ P := by
    have hxSup : x ∈ Ideal.span ({x} : Set (NumberField.RingOfIntegers L)) ⊔ P := by
      exact
        (show Ideal.span ({x} : Set (NumberField.RingOfIntegers L)) ≤
            Ideal.span ({x} : Set (NumberField.RingOfIntegers L)) ⊔ P from le_sup_left)
          (Ideal.subset_span (by simp))
    rw [← hEq] at hxSup
    exact hxSup
  exact hx hx'

lemma comp_quot_inclusion
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i ∘ₗ
        primePowImage (L := L) (r := r) (P := P) x (i + 1) =
      primePowImage (L := L) (r := r) (P := P) x i ∘ₗ
        (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i := by
  ext z
  rfl

lemma prime_image_range
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) ≤
      Submodule.comap
        (primePowImage (L := L) (r := r) (P := P) x i)
        (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) := by
  rintro z ⟨y, rfl⟩
  refine ⟨primePowImage (L := L) (r := r) (P := P) x (i + 1) y, ?_⟩
  exact congrArg (fun f => f y)
    (comp_quot_inclusion
      (L := L) (r := r) (P := P) x i)

lemma powInclusion_injective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (i : ℕ) :
    Function.Injective ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun t =>
      ((t :
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ i))) :
        NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) h

noncomputable def quot_inclusion_range
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (i : ℕ) :
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ (i + 1))) ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) :=
  LinearEquiv.ofInjective
    ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
    (powInclusion_injective (L := L) (r := r) (P := P) i)

lemma quot_restrict_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x :
      NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    (i : ℕ) :
    let e := quot_inclusion_range (L := L) (r := r) (P := P) i
    let fRange :
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
          →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) :=
      LinearMap.restrict
        (powQuotImage (L := L) (r := r) (P := P) x i)
        (fun _ hx => quot_image_range (L := L) (r := r) (P := P) x i hx)
    e.conj (powQuotImage (L := L) (r := r) (P := P) x (i + 1)) = fRange := by
  dsimp
  apply DFunLike.ext
  intro z
  apply Subtype.ext
  change
    ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
        (powQuotImage (L := L) (r := r) (P := P) x (i + 1)
          ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z)) =
      powQuotImage (L := L) (r := r) (P := P) x i z.1
  have hz :
      ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
          ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z) = z.1 := by
    exact congrArg Subtype.val
      ((quot_inclusion_range (L := L) (r := r) (P := P) i).apply_symm_apply z)
  rw [← hz]
  exact congrArg
    (fun f =>
      f ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z))
    (quot_comp_inclusion
      (L := L) (r := r) (P := P) x i)

lemma image_restrict_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    let e := quot_inclusion_range (L := L) (r := r) (P := P) i
    let fRange :
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
          →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) :=
      LinearMap.restrict
        (primePowImage (L := L) (r := r) (P := P) x i)
        (fun _ hx => prime_image_range (L := L) (r := r) (P := P) x i hx)
    e.conj (primePowImage (L := L) (r := r) (P := P) x (i + 1)) = fRange := by
  dsimp
  apply DFunLike.ext
  intro z
  apply Subtype.ext
  change
    ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
        (primePowImage (L := L) (r := r) (P := P) x (i + 1)
          ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z)) =
      primePowImage (L := L) (r := r) (P := P) x i z.1
  have hz :
      ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
          ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z) = z.1 := by
    exact congrArg Subtype.val
      ((quot_inclusion_range (L := L) (r := r) (P := P) i).apply_symm_apply z)
  rw [← hz]
  exact congrArg
    (fun f =>
      f ((quot_inclusion_range (L := L) (r := r) (P := P) i).symm z))
    (comp_quot_inclusion
      (L := L) (r := r) (P := P) x i)

noncomputable def primeImageBetween
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    {i j : ℕ}
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P ^ i) :
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ j)) →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ (i + j))) := by
  let xbar :=
    Ideal.Quotient.mk
      (P ^
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) x
  refine
    { toFun := fun z => ⟨xbar * (z : _), ?_⟩
      map_add' := by
        intro z w
        apply Subtype.ext
        simpa [xbar] using mul_add xbar (z : _) (w : _)
      map_smul' := by
        intro c z
        apply Subtype.ext
        change xbar * (c • (z : _)) = c • (xbar * (z : _))
        rw [Algebra.smul_def, Algebra.smul_def]
        ac_rfl }
  rcases (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 z.2 with
    ⟨y, hy, hyz⟩
  rw [← hyz]
  have hxy : x * y ∈ P ^ (i + j) := by
    simpa [pow_add, Ideal.mul_comm] using Ideal.mul_mem_mul hx hy
  simpa using Ideal.mem_map_of_mem _ hxy

lemma between_quot_inclusion
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    {i j : ℕ}
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P ^ i) :
    (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P (i + j) ∘ₗ
        primeImageBetween (L := L) (r := r) (P := P) (i := i) (j := j + 1) x hx =
      primeImageBetween (L := L) (r := r) (P := P) (i := i) (j := j) x hx ∘ₗ
        (Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P j := by
  ext z
  rfl

lemma image_between_range
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    {i j : ℕ}
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P ^ i) :
    LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P j) ≤
      Submodule.comap
        (primeImageBetween (L := L) (r := r) (P := P) (i := i) (j := j) x hx)
        (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P (i + j))) := by
  rintro z ⟨y, rfl⟩
  refine ⟨primeImageBetween
      (L := L) (r := r) (P := P) (i := i) (j := j + 1) x hx y, ?_⟩
  exact congrArg (fun f => f y)
    (between_quot_inclusion
      (L := L) (r := r) (P := P) (i := i) (j := j) x hx)

noncomputable def primeStepQ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
        →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) :=
  (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)).mapQ
    (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
    (primePowImage (L := L) (r := r) (P := P) x i)
    (prime_image_range (L := L) (r := r) (P := P) x i)

@[simp] lemma prime_q_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ)
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))) :
    primeStepQ (L := L) (r := r) (P := P) x i (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (primePowImage (L := L) (r := r) (P := P) x i z) := by
  rfl

noncomputable def primeBetweenQ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    {i j : ℕ}
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P ^ i) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ j)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P j))
        →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ (i + j))) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P (i + j))) :=
  (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P j)).mapQ
    (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P (i + j)))
    (primeImageBetween
      (L := L) (r := r) (P := P) (i := i) (j := j) x hx)
    (image_between_range
      (L := L) (r := r) (P := P) (i := i) (j := j) x hx)

@[simp] lemma between_q_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    {i j : ℕ}
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P ^ i)
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ j))) :
    primeBetweenQ
        (L := L) (r := r) (P := P) (i := i) (j := j) x hx
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := j) x hx z) := by
  rfl

noncomputable def powGeneratorStep
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) := by
  simpa [Nat.add_zero] using
    (primeBetweenQ
      (L := L) (r := r) (P := P) (i := i) (j := 0)
      (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
      (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi))

@[simp] lemma generator_step_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))) :
    powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0)
          (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          z) := by
  simpa [powGeneratorStep, Nat.add_zero] using
    (between_q_mk
      (L := L) (r := r) (P := P) (i := i) (j := 0)
      (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
      (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
      z)

lemma generator_step_surjective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Function.Surjective
      (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi) := by
  classical
  intro zq
  refine Quotient.inductionOn zq ?_
  intro z
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let g := quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).1 z.2 with
    ⟨a, haPi, haz⟩
  have hspan :
      a ∈ Ideal.span ({g} : Set (NumberField.RingOfIntegers L)) ⊔ P ^ (i + 1) := by
    rw [quot_span_sup
      (L := L) (r := r) (P := P) hP0 i hi]
    exact haPi
  rcases Submodule.mem_sup.1 hspan with ⟨u, huSpan, v, hvPow, huv⟩
  rcases (Ideal.mem_span_singleton.mp huSpan) with ⟨c, huc⟩
  rw [huc] at huv
  refine ⟨Submodule.Quotient.mk ⟨Ideal.Quotient.mk (P ^ e) c, ?_⟩, ?_⟩
  · exact
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
        ⟨c, by simp [pow_zero], rfl⟩
  · rw [generator_step_mk]
    apply (Submodule.Quotient.eq _).2
    refine ⟨⟨Ideal.Quotient.mk (P ^ e) (-v), ?_⟩, ?_⟩
    · exact
        (Ideal.mem_map_iff_of_surjective
          (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
          ⟨-v, (P ^ (i + 1)).neg_mem hvPow, rfl⟩
    · apply Subtype.ext
      have hmul :
          (primeImageBetween
              (L := L) (r := r) (P := P) (i := i) (j := 0) g
              (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
              ⟨Ideal.Quotient.mk (P ^ e) c, by
                exact
                    (Ideal.mem_map_iff_of_surjective
                      (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
                    ⟨c, by simp [pow_zero], rfl⟩⟩).1 =
            Ideal.Quotient.mk (P ^ e) (g * c) := by
        change
          Ideal.Quotient.mk (P ^ e) g * Ideal.Quotient.mk (P ^ e) c =
            Ideal.Quotient.mk (P ^ e) (g * c)
        rw [← map_mul]
      change
        Ideal.Quotient.mk (P ^ e) (-v) =
          (primeImageBetween
              (L := L) (r := r) (P := P) (i := i) (j := 0) g
              (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
              ⟨Ideal.Quotient.mk (P ^ e) c, by
                exact
                  (Ideal.mem_map_iff_of_surjective
                    (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
                    ⟨c, by simp [pow_zero], rfl⟩⟩).1 - z.1
      rw [hmul]
      rw [← haz]
      apply eq_sub_iff_add_eq.mpr
      rw [← huv]
      simp [add_comm, add_assoc]

lemma generator_step_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    {zq :
      (↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ 0)) ⧸
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))}
    (hz :
      powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi zq = 0) :
    zq = 0 := by
  classical
  revert hz
  refine Quotient.inductionOn zq ?_
  intro z hz
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let g := quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).1 z.2 with
    ⟨a, haTop, haz⟩
  let za :
      ↥(Ideal.map
        (Ideal.Quotient.mk (P ^ e))
        (P ^ 0)) := by
    refine ⟨Ideal.Quotient.mk (P ^ e) a, ?_⟩
    exact
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
        ⟨a, by simp [pow_zero], rfl⟩
  have hza : za = z := by
    apply Subtype.ext
    exact haz
  have hz0 :
      powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
          (Submodule.Quotient.mk za) = 0 := by
    have hz' := hz
    rwa [← hza] at hz'
  have hzImg :
      Submodule.Quotient.mk
          (primeImageBetween
            (L := L) (r := r) (P := P) (i := i) (j := 0) g
            (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
            za) =
        (0 :
          (↥(Ideal.map
              (Ideal.Quotient.mk (P ^ e))
              (P ^ i)) ⧸
            LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))) := by
    simpa [generator_step_mk] using hz0
  have hmemRange' :
      primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0) g
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          za -
        0 ∈
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) := by
    exact (Submodule.Quotient.eq _).1 hzImg
  have hmemRange :
      primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0) g
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          za ∈
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) := by
    rw [sub_zero] at hmemRange'
    exact hmemRange'
  rcases hmemRange with ⟨y, hy⟩
  have hwy :
      (((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i y :
          ↥(Ideal.map
            (Ideal.Quotient.mk (P ^ e))
            (P ^ i)))).1 =
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0) g
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          za).1 := by
    simpa using congrArg Subtype.val hy
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).1 y.2 with
    ⟨b, hbPow, hyb⟩
  have hyb' :
      (((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i y :
          ↥(Ideal.map
            (Ideal.Quotient.mk (P ^ e))
            (P ^ i)))).1 =
        Ideal.Quotient.mk (P ^ e) b := by
    simpa using hyb.symm
  have hmulga :
      (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0) g
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          za).1 =
        Ideal.Quotient.mk (P ^ e) (g * a) := by
    change
      Ideal.Quotient.mk (P ^ e) g * Ideal.Quotient.mk (P ^ e) a =
        Ideal.Quotient.mk (P ^ e) (g * a)
    rw [← map_mul]
  have hquot : Ideal.Quotient.mk (P ^ e) (g * a) = Ideal.Quotient.mk (P ^ e) b := by
    calc
      Ideal.Quotient.mk (P ^ e) (g * a)
          = (primeImageBetween
              (L := L) (r := r) (P := P) (i := i) (j := 0) g
              (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
              za).1 := hmulga.symm
      _ = (((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i y :
            ↥(Ideal.map
              (Ideal.Quotient.mk (P ^ e))
              (P ^ i)))).1 := hwy.symm
      _ = Ideal.Quotient.mk (P ^ e) b := hyb'
  have hdiff0 : Ideal.Quotient.mk (P ^ e) (g * a - b) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hquot
  have hdiffmem : g * a - b ∈ P ^ e := by
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hdiff0
  have hpowle : P ^ e ≤ P ^ (i + 1) := by
    exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hi)
  have hga : g * a ∈ P ^ (i + 1) := by
    have hdiffmem' : g * a - b ∈ P ^ (i + 1) := hpowle hdiffmem
    have hsum := Ideal.add_mem (P ^ (i + 1)) hdiffmem' hbPow
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  have haP : a ∈ P := by
    by_contra hnaP
    have hsup :
        Ideal.span ({a} : Set (NumberField.RingOfIntegers L)) ⊔ P = ⊤ := by
      exact singleton_sup_not (L := L) hP0 hnaP
    have hOne :
        (1 : NumberField.RingOfIntegers L) ∈
          Ideal.span ({a} : Set (NumberField.RingOfIntegers L)) ⊔ P := by
      simp [hsup]
    rcases Submodule.mem_sup.1 hOne with ⟨u, huSpan, v, hvP, huv⟩
    rcases (Ideal.mem_span_singleton.mp huSpan) with ⟨d, hud⟩
    have hgu : g * u ∈ P ^ (i + 1) := by
      rw [hud]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Ideal.mul_mem_left (P ^ (i + 1)) d hga)
    have hgv : g * v ∈ P ^ (i + 1) := by
      have hmul := Ideal.mul_mem_mul
        (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi) hvP
      simpa [pow_succ, Ideal.mul_comm, Ideal.mul_assoc] using hmul
    have hgmem : g ∈ P ^ (i + 1) := by
      have hEq : g = g * u + g * v := by
        calc
          g = g * 1 := by simp
          _ = g * (u + v) := by rw [← huv]
          _ = g * u + g * v := by rw [mul_add]
      rw [hEq]
      exact Ideal.add_mem _ hgu hgv
    exact
      pow_quot_not (L := L) (r := r) (P := P) hP0 i hi hgmem
  let ya :
      ↥(Ideal.map
        (Ideal.Quotient.mk (P ^ e))
        (P ^ 1)) := by
    refine ⟨Ideal.Quotient.mk (P ^ e) a, ?_⟩
    exact
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
        ⟨a, by simpa [pow_one] using haP, rfl⟩
  have hzq0 :
      (Submodule.Quotient.mk za :
        (↥(Ideal.map
            (Ideal.Quotient.mk (P ^ e))
            (P ^ 0)) ⧸
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))) = 0 := by
    apply (Submodule.Quotient.eq _).2
    refine ⟨ya, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (P ^ e) a = Ideal.Quotient.mk (P ^ e) a - 0
    exact (sub_zero _).symm
  have hzmk :
      (Submodule.Quotient.mk z :
        (↥(Ideal.map
            (Ideal.Quotient.mk (P ^ e))
            (P ^ 0)) ⧸
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))) =
        Submodule.Quotient.mk za := by
    simp [hza]
  exact hzmk.trans hzq0

set_option synthInstance.maxHeartbeats 400000 in
-- The same wrapper also needs extra instance-search budget on those quotient types.
-- The quotient-subtraction elaboration in the injectivity wrapper needs extra
-- instance-search budget.
lemma generator_step_injective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Function.Injective
      (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi) := by
  let f := powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
  intro z w hzw
  have hsub0 : f z - f w = 0 := by
    exact sub_eq_zero.mpr hzw
  have hsub : f (z - w) = 0 := by
    calc
      f (z - w) = f z - f w := by rw [map_sub]
      _ = 0 := hsub0
  have hz0 : z - w = 0 := by
    exact generator_step_zero
      (L := L) (r := r) (P := P) hP0 i hi (zq := z - w) hsub
  exact sub_eq_zero.mp hz0

lemma generator_step_bijective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Function.Bijective
      (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi) := by
  exact ⟨generator_step_injective (L := L) (r := r) (P := P) hP0 i hi,
    generator_step_surjective (L := L) (r := r) (P := P) hP0 i hi⟩

set_option maxHeartbeats 800000 in
-- Packaging the unconditional stage-shift quotient equivalence needs extra elaboration budget.
noncomputable def primeStageShift
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) :=
  LinearEquiv.ofBijective
    (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi)
    (generator_step_bijective (L := L) (r := r) (P := P) hP0 i hi)

@[simp] lemma stage_shift_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))) :
    primeStageShift
        (L := L) (r := r) (P := P) hP0 i hi
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0)
          (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          z) := by
  simp [primeStageShift]

set_option maxHeartbeats 800000 in
-- Packaging the large quotient map into a linear equivalence needs extra elaboration budget.
noncomputable def primeGeneratorStep
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (hbij :
      Function.Bijective
        ⇑(powGeneratorStep
          (L := L) (r := r) (P := P) hP0 i hi)) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)) :=
  let f := powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
  LinearEquiv.ofBijective f hbij

@[simp] lemma prime_generator_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (hbij :
      Function.Bijective
        ⇑(powGeneratorStep
          (L := L) (r := r) (P := P) hP0 i hi))
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))) :
    primeGeneratorStep
        (L := L) (r := r) (P := P) hP0 i hi hbij
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0)
          (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          z) := by
  simp [primeGeneratorStep]

noncomputable def primePowResidue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸ P) := by
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let f : NumberField.RingOfIntegers L ⧸ P ^ e →+* NumberField.RingOfIntegers L ⧸ P :=
    Ideal.Quotient.factor
      (show P ^ e ≤ P by
        exact Ideal.pow_le_self (Nat.ne_of_gt hepos))
  refine
    { toFun := fun z => f z.1
      map_add' := by
        intro z w
        exact map_add f z.1 w.1
      map_smul' := by
        intro c z
        refine Quotient.inductionOn c ?_
        intro n
        change
          f (((Ideal.Quotient.mk (Ideal.rationalPrimeIdeal r) n :
              ℤ ⧸ Ideal.rationalPrimeIdeal r)) • z.1) =
            ((Ideal.Quotient.mk (Ideal.rationalPrimeIdeal r) n :
              ℤ ⧸ Ideal.rationalPrimeIdeal r)) • f z.1
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }

lemma prime_residue_surjective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    Function.Surjective
      (primePowResidue (L := L) (r := r) (P := P) hepos) := by
  intro z
  rcases Ideal.Quotient.mk_surjective z with ⟨x, rfl⟩
  refine ⟨⟨Ideal.Quotient.mk _ x, ?_⟩, rfl⟩
  have hx : x ∈ (P ^ 0 : Ideal (NumberField.RingOfIntegers L)) := by
    simp [pow_zero]
  exact Ideal.mem_map_of_mem
    (Ideal.Quotient.mk
      (P ^
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    hx

lemma prime_residue_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    (primePowResidue (L := L) (r := r) (P := P) hepos).ker =
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0) := by
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let f : NumberField.RingOfIntegers L ⧸ P ^ e →+* NumberField.RingOfIntegers L ⧸ P :=
    Ideal.Quotient.factor
      (show P ^ e ≤ P by
        exact Ideal.pow_le_self (Nat.ne_of_gt hepos))
  ext z
  constructor
  · intro hz
    rcases Ideal.Quotient.mk_surjective z.1 with ⟨x, hx⟩
    have hxP : x ∈ P := by
      have hz0 :
          primePowResidue (L := L) (r := r) (P := P) hepos z =
            (0 : NumberField.RingOfIntegers L ⧸ P) := hz
      have hz' : f ((Ideal.Quotient.mk (P ^ e)) x) = (0 : NumberField.RingOfIntegers L ⧸ P) := by
        have hz1 := hz0
        change f z.1 = (0 : NumberField.RingOfIntegers L ⧸ P) at hz1
        rwa [← hx] at hz1
      change (Ideal.Quotient.mk P) x = 0 at hz'
      exact (Ideal.Quotient.eq_zero_iff_mem).1 hz'
    refine ⟨⟨Ideal.Quotient.mk (P ^ e) x, ?_⟩, ?_⟩
    · exact
        (Ideal.mem_map_iff_of_surjective
          (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).2
          ⟨x, by simpa [pow_one] using hxP, rfl⟩
    · apply Subtype.ext
      exact hx
  · rintro ⟨y, rfl⟩
    rcases (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (P ^ e)) Ideal.Quotient.mk_surjective).1 y.2 with
      ⟨x, hxP, hxy⟩
    change f y.1 = 0
    rw [← hxy]
    change (Ideal.Quotient.mk P) x = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (by simpa [pow_one] using hxP)

set_option maxHeartbeats 800000 in
-- The quotient-kernel equivalence on this large subtype/quotient expression
-- needs extra elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
noncomputable def primeQuotKer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      (primePowResidue (L := L) (r := r) (P := P) hepos).ker) := by
  let φ := primePowResidue (L := L) (r := r) (P := P) hepos
  have hker : φ.ker = LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0) := by
    simpa [φ] using
      prime_residue_ker (L := L) (r := r) (P := P) hepos
  exact submoduleQuotientEquiv hker.symm

set_option maxHeartbeats 800000 in
-- The quotient-kernel equivalence on this large subtype/quotient expression
-- needs extra elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
noncomputable def primeStepResidue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸ P) := by
  let φ := primePowResidue (L := L) (r := r) (P := P) hepos
  let e₁ := LinearMap.quotKerEquivRange φ
  let e₂ : ↥φ.range ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸ P) :=
    LinearEquiv.ofBijective φ.range.subtype <| by
      constructor
      · intro x y hxy
        exact Subtype.ext hxy
      · intro z
        rcases prime_residue_surjective
            (L := L) (r := r) (P := P) hepos z with ⟨x, rfl⟩
        exact ⟨⟨φ x, ⟨x, rfl⟩⟩, rfl⟩
  exact
    (primeQuotKer (L := L) (r := r) (P := P) hepos).trans
      (e₁.trans e₂)

@[simp] lemma prime_residue_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (z :
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))) :
    primeStepResidue (L := L) (r := r) (P := P) hepos
        (Submodule.Quotient.mk z) =
      primePowResidue (L := L) (r := r) (P := P) hepos z := by
  let φ := primePowResidue (L := L) (r := r) (P := P) hepos
  let e₀ := primeQuotKer (L := L) (r := r) (P := P) hepos
  let e₁ := LinearMap.quotKerEquivRange φ
  let e₂ : ↥φ.range ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸ P) :=
    LinearEquiv.ofBijective φ.range.subtype <| by
      constructor
      · intro x y hxy
        exact Subtype.ext hxy
      · intro z
        rcases prime_residue_surjective
            (L := L) (r := r) (P := P) hepos z with ⟨x, rfl⟩
        exact ⟨⟨φ x, ⟨x, rfl⟩⟩, rfl⟩
  have haux : (e₁.trans e₂) (Submodule.Quotient.mk z) = φ z := by
    rfl
  have h0 : e₀ (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := by
    have hker :
        φ.ker =
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0) := by
      simpa [φ] using
        prime_residue_ker (L := L) (r := r) (P := P) hepos
    simp [e₀, primeQuotKer]
  change (e₂ (e₁ (e₀ (Submodule.Quotient.mk z)))) = φ z
  rw [h0]
  exact haux

set_option maxHeartbeats 800000 in
-- Composing the stage-shift and residue-step equivalences needs extra elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
noncomputable def powStepResidue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (hbij :
      Function.Bijective
        ⇑(powGeneratorStep
          (L := L) (r := r) (P := P) hP0 i hi)) :
    (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
        ≃ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸ P) := by
  let e₀ := primeStepResidue (L := L) (r := r) (P := P) hepos
  let eᵢ := primeGeneratorStep
    (L := L) (r := r) (P := P) hP0 i hi hbij
  exact eᵢ.symm.trans e₀

lemma residue_commutes_q
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (x : NumberField.RingOfIntegers L)
    (z :
      (↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0)) ⧸
      LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))) :
    primeStepResidue (L := L) (r := r) (P := P) hepos
        (primeStepQ (L := L) (r := r) (P := P) x 0 z) =
      ((Algebra.lmul
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P))
        ((Ideal.Quotient.mk P) x))
        (primeStepResidue
          (L := L) (r := r) (P := P) hepos z) := by
  refine Quotient.inductionOn z ?_
  intro y
  change
    primeStepResidue (L := L) (r := r) (P := P) hepos
        (Submodule.Quotient.mk (primePowImage (L := L) (r := r) (P := P) x 0 y)) =
      ((Ideal.Quotient.mk P) x) *
        primeStepResidue (L := L) (r := r) (P := P) hepos
          (Submodule.Quotient.mk y)
  rw [prime_residue_mk, prime_residue_mk]
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  let f : NumberField.RingOfIntegers L ⧸ P ^ e →+* NumberField.RingOfIntegers L ⧸ P :=
    Ideal.Quotient.factor
      (show P ^ e ≤ P by
        exact Ideal.pow_le_self (Nat.ne_of_gt hepos))
  change f ((primePowImage (L := L) (r := r) (P := P) x 0 y).1) =
    ((Ideal.Quotient.mk P) x) * f y.1
  change f (((Ideal.Quotient.mk (P ^ e)) x) * y.1) = ((Ideal.Quotient.mk P) x) * f y.1
  rw [map_mul]
  rfl

set_option maxHeartbeats 800000 in
-- The specialization has a large definitional equality problem on the quotient/range types.
lemma restrict_q_quot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x :
      NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
    (i : ℕ)
    [Module.Finite (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))]
    [Module.Free (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))] :
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ i))
        (powQuotImage (L := L) (r := r) (P := P) x i) =
      LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
          ((powQuotImage (L := L) (r := r) (P := P) x i).restrict
            (fun _ hx => quot_image_range (L := L) (r := r) (P := P) x i hx)) +
        LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (↥(Ideal.map
              (Ideal.Quotient.mk
                (P ^
                  (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
              (P ^ i)) ⧸
            LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
          ((LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)).mapQ
            (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
            (powQuotImage (L := L) (r := r) (P := P) x i)
            (quot_image_range (L := L) (r := r) (P := P) x i)) := by
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  letI : Field (ℤ ⧸ Ideal.rationalPrimeIdeal r) := Ideal.Quotient.field _
  let p := LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
  let f := powQuotImage (L := L) (r := r) (P := P) x i
  have hstable : p ≤ Submodule.comap f p := by
    simpa [p, f] using
      (quot_image_range (L := L) (r := r) (P := P) x i)
  simpa [p, f] using
    (@trace_restrict_q
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))
      _ _ _ _ _ p f hstable)

set_option maxHeartbeats 800000 in
-- The same quotient/range normalization issue appears for the lifted multiplication map.
lemma restrict_q_image
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L) (i : ℕ)
    [Module.Finite (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))]
    [Module.Free (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))] :
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ i))
        (primePowImage (L := L) (r := r) (P := P) x i) =
      LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
          ((primePowImage (L := L) (r := r) (P := P) x i).restrict
            (fun _ hx =>
              prime_image_range (L := L) (r := r) (P := P) x i hx)) +
        LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (↥(Ideal.map
              (Ideal.Quotient.mk
                (P ^
                  (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
              (P ^ i)) ⧸
            LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
          ((LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)).mapQ
            (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
            (primePowImage (L := L) (r := r) (P := P) x i)
            (prime_image_range (L := L) (r := r) (P := P) x i)) := by
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  letI : Field (ℤ ⧸ Ideal.rationalPrimeIdeal r) := Ideal.Quotient.field _
  let p := LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
  let f := primePowImage (L := L) (r := r) (P := P) x i
  have hstable : p ≤ Submodule.comap f p := by
    simpa [p, f] using
      (prime_image_range (L := L) (r := r) (P := P) x i)
  simpa [p, f] using
    (@trace_restrict_q
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))
      _ _ _ _ _ p f hstable)

lemma sup_idx_factorization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hPQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q) :
    P ⊔ Q = ⊤ := by
  rcases coprime_ramification_idx
      (L := L) (hr := hr) hP with ⟨Q', hsup', hPQ'⟩
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  have hpow0 :
      P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ≠
        ⊥ := by
    exact pow_ne_zero _ hP0
  have hQQ' : Q = Q' := by
    apply mul_left_cancel₀ hpow0
    calc
      P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q
          =
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) := hPQ.symm
      _ =
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q' := hPQ'
  simpa [hQQ'] using hsup'

lemma mk_sup_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    [P.IsPrime]
    (hP0 : P ≠ ⊥)
    (hsup : P ⊔ Q = ⊤) :
    Function.Surjective
      (fun x : Q => (Ideal.Quotient.mk P) x.1) := by
  let _ := r
  let _ := hP0
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal ‹P.IsPrime› hP0
  intro z
  rcases Ideal.Quotient.mk_surjective z with ⟨y, rfl⟩
  have hOne :
      (1 : NumberField.RingOfIntegers L) ∈ P ⊔ Q := by
    simp [hsup]
  rcases Submodule.mem_sup.1 hOne with ⟨u, huP, v, hvQ, huv⟩
  refine ⟨⟨v * y, by
    simpa [mul_comm] using (Ideal.mul_mem_left Q y hvQ)⟩, ?_⟩
  change (Ideal.Quotient.mk P) (v * y) = (Ideal.Quotient.mk P) y
  have huv' : (u + v) * y = y := by
    calc
      (u + v) * y = 1 * y := by rw [huv]
      _ = y := by simp
  have huPy : u * y ∈ P := by
    simpa [mul_comm] using (Ideal.mul_mem_left P y huP)
  have huy0 : (Ideal.Quotient.mk P) (u * y) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem).2 huPy
  have huvq :
      (Ideal.Quotient.mk P) ((u + v) * y) =
        (Ideal.Quotient.mk P) (u * y) + (Ideal.Quotient.mk P) (v * y) := by
    rw [add_mul, map_add]
  have hqeq :
      (Ideal.Quotient.mk P) ((u + v) * y) =
        (Ideal.Quotient.mk P) (v * y) := by
    calc
      (Ideal.Quotient.mk P) ((u + v) * y)
          = (Ideal.Quotient.mk P) (u * y) + (Ideal.Quotient.mk P) (v * y) := huvq
      _ = 0 + (Ideal.Quotient.mk P) (v * y) := by rw [huy0]
      _ = (Ideal.Quotient.mk P) (v * y) := zero_add _
  calc
    (Ideal.Quotient.mk P) (v * y)
        = (Ideal.Quotient.mk P) ((u + v) * y) := by exact hqeq.symm
    _ = (Ideal.Quotient.mk P) y := by simp [huv']

lemma factor_nonzero_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hP0 : P ≠ ⊥)
    (hsup : P ⊔ Q = ⊤) :
    ∃ x : NumberField.RingOfIntegers L,
      x ∈ Q ∧
      Algebra.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P)
          ((Ideal.Quotient.mk P) x) ≠
        0 := by
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal ‹P.IsPrime› hP0
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  letI : Field (ℤ ⧸ Ideal.rationalPrimeIdeal r) := Ideal.Quotient.field _
  letI : Field (NumberField.RingOfIntegers L ⧸ P) := Ideal.Quotient.field P
  letI :
      Algebra (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap (by
      simpa [Ideal.under] using (show
        Ideal.rationalPrimeIdeal r =
          Ideal.comap (algebraMap (ℤ) (NumberField.RingOfIntegers L)) P from
            ‹P.LiesOver (Ideal.rationalPrimeIdeal r)›.over).le)
  have hsurjTrace :=
    Algebra.trace_surjective
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L ⧸ P)
  rcases hsurjTrace 1 with ⟨z, hz⟩
  rcases mk_sup_top
      (L := L) (r := r) (P := P) (Q := Q) hP0 hsup z with ⟨xQ, hxQ⟩
  have hxQ' : (Ideal.Quotient.mk P) xQ.1 = z := hxQ
  refine ⟨xQ.1, xQ.2, ?_⟩
  rw [hxQ', hz]
  intro h10
  have h01 : (0 : ℤ ⧸ Ideal.rationalPrimeIdeal r) = 1 := h10.symm
  have h10' : (1 : ℤ ⧸ Ideal.rationalPrimeIdeal r) = 0 := h01.symm
  have h1mem : (1 : ℤ) ∈ Ideal.rationalPrimeIdeal r := by
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h10'
  have htop : Ideal.rationalPrimeIdeal r = ⊤ := (Ideal.eq_top_iff_one _).2 h1mem
  exact (rational_ideal_maximal hr).ne_top htop

lemma generator_commutes_q
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    (x : NumberField.RingOfIntegers L)
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (z :
      (↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ 0)) ⧸
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))) :
    powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
        (primeStepQ (L := L) (r := r) (P := P) x 0 z) =
      primeStepQ (L := L) (r := r) (P := P) x i
        (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi z) := by
  refine Quotient.inductionOn z ?_
  intro y
  calc
    powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
        (primeStepQ (L := L) (r := r) (P := P) x 0 (Submodule.Quotient.mk y))
        =
      powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
        (Submodule.Quotient.mk
          (primePowImage (L := L) (r := r) (P := P) x 0 y)) := by
            rfl
    _ =
      Submodule.Quotient.mk
        (primeImageBetween
          (L := L) (r := r) (P := P) (i := i) (j := 0)
          (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
          (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
          (primePowImage (L := L) (r := r) (P := P) x 0 y)) := by
            exact
              generator_step_mk
                (L := L) (r := r) (P := P) hP0 i hi
                (primePowImage (L := L) (r := r) (P := P) x 0 y)
    _ =
      Submodule.Quotient.mk
        (primePowImage (L := L) (r := r) (P := P) x i
          (primeImageBetween
            (L := L) (r := r) (P := P) (i := i) (j := 0)
            (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
            (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
            y)) := by
              apply congrArg Submodule.Quotient.mk
              apply Subtype.ext
              change
                (Ideal.Quotient.mk
                    (P ^
                      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
                    (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)) *
                    ((Ideal.Quotient.mk
                        (P ^
                          Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) x) *
                      y.1)
                  =
                (Ideal.Quotient.mk
                    (P ^
                      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) x) *
                  ((Ideal.Quotient.mk
                      (P ^
                        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
                      (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)) *
                    y.1)
              ac_rfl
    _ =
      primeStepQ (L := L) (r := r) (P := P) x i
        (Submodule.Quotient.mk
          (primeImageBetween
            (L := L) (r := r) (P := P) (i := i) (j := 0)
            (quotSuccGenerator (L := L) (r := r) (P := P) hP0 i hi)
            (quot_succ_generator (L := L) (r := r) (P := P) hP0 i hi)
            y)) := by
              rfl
    _ =
      primeStepQ (L := L) (r := r) (P := P) x i
        (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
          (Submodule.Quotient.mk y)) := by
            rw [generator_step_mk]

set_option maxHeartbeats 800000 in
-- These quotient-trace conjugation proofs need more heartbeats for normalization and trace goals.
set_option synthInstance.maxHeartbeats 200000 in
lemma step_trace_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (x : NumberField.RingOfIntegers L)
    (i : ℕ)
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (↥(Ideal.map
            (Ideal.Quotient.mk
              (P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
            (P ^ i)) ⧸
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
        (primeStepQ (L := L) (r := r) (P := P) x i) =
      Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P)
        ((Ideal.Quotient.mk P) x) := by
  let e0 := primeStepResidue (L := L) (r := r) (P := P) hepos
  let ei := primeGeneratorStep
    (L := L) (r := r) (P := P) hP0 i hi
    (generator_step_bijective (L := L) (r := r) (P := P) hP0 i hi)
  have hcommi :
      ei.conj (primeStepQ (L := L) (r := r) (P := P) x 0) =
        primeStepQ (L := L) (r := r) (P := P) x i := by
    apply DFunLike.ext
    intro z
    change
      powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
          (primeStepQ (L := L) (r := r) (P := P) x 0
            (ei.symm z)) =
        primeStepQ (L := L) (r := r) (P := P) x i z
    have hz' :
        powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
            (ei.symm z) = z := by
      simp [ei, primeGeneratorStep]
    calc
      powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
          (primeStepQ (L := L) (r := r) (P := P) x 0
            (ei.symm z))
        =
      primeStepQ (L := L) (r := r) (P := P) x i
          (powGeneratorStep (L := L) (r := r) (P := P) hP0 i hi
            (ei.symm z)) :=
          generator_commutes_q
            (L := L) (r := r) (P := P) hP0 x i hi (ei.symm z)
      _ = primeStepQ (L := L) (r := r) (P := P) x i z := by rw [hz']
  have hcomm0 :
      e0.conj (primeStepQ (L := L) (r := r) (P := P) x 0) =
        (Algebra.lmul
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P))
          ((Ideal.Quotient.mk P) x) := by
    apply DFunLike.ext
    intro z
    change
      primeStepResidue (L := L) (r := r) (P := P) hepos
          (primeStepQ (L := L) (r := r) (P := P) x 0
            (e0.symm z)) =
        ((Ideal.Quotient.mk P) x) * z
    have hz' :
        primeStepResidue (L := L) (r := r) (P := P) hepos
            (e0.symm z) = z := by
      simp [e0, primeStepResidue]
    calc
      primeStepResidue (L := L) (r := r) (P := P) hepos
          (primeStepQ (L := L) (r := r) (P := P) x 0
            (e0.symm z))
        =
      ((Ideal.Quotient.mk P) x) *
          (primeStepResidue (L := L) (r := r) (P := P) hepos
            (e0.symm z)) :=
          residue_commutes_q
            (L := L) (r := r) (P := P) hepos x (e0.symm z)
      _ = ((Ideal.Quotient.mk P) x) * z := by rw [hz']
  calc
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (↥(Ideal.map
            (Ideal.Quotient.mk
              (P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
            (P ^ i)) ⧸
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
        (primeStepQ (L := L) (r := r) (P := P) x i)
      =
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (↥(Ideal.map
            (Ideal.Quotient.mk
              (P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
            (P ^ 0)) ⧸
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P 0))
        (primeStepQ (L := L) (r := r) (P := P) x 0) := by
          rw [← LinearMap.trace_conj'
            (primeStepQ (L := L) (r := r) (P := P) x 0) ei, hcommi]
    _ =
      LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P)
        ((Algebra.lmul
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P))
          ((Ideal.Quotient.mk P) x)) := by
            rw [← LinearMap.trace_conj'
              (primeStepQ (L := L) (r := r) (P := P) x 0) e0, hcomm0]
    _ =
      Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P)
        ((Ideal.Quotient.mk P) x) := by
            simp [Algebra.trace_apply]

set_option maxHeartbeats 800000 in
-- The filtration-step trace decomposition triggers expensive finite-module instance search.
set_option synthInstance.maxHeartbeats 200000 in
lemma image_succ_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (x : NumberField.RingOfIntegers L)
    (i : ℕ)
    [Module.Finite (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))]
    [Module.Free (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ i))]
    (hi :
      i <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) :
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ i))
        (primePowImage (L := L) (r := r) (P := P) x i) =
      LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ (i + 1)))
        (primePowImage (L := L) (r := r) (P := P) x (i + 1)) +
      Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P)
        ((Ideal.Quotient.mk P) x) := by
  have hrestrict :
      LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i))
          ((primePowImage (L := L) (r := r) (P := P) x i).restrict
            (fun _ hx =>
              prime_image_range (L := L) (r := r) (P := P) x i hx)) =
        LinearMap.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          ↥(Ideal.map
            (Ideal.Quotient.mk
              (P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
            (P ^ (i + 1)))
          (primePowImage (L := L) (r := r) (P := P) x (i + 1)) := by
    let e := quot_inclusion_range (L := L) (r := r) (P := P) i
    let fRange :
        LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i)
          →ₗ[ℤ ⧸ Ideal.rationalPrimeIdeal r]
          LinearMap.range ((Ideal.rationalPrimeIdeal r).powQuotSuccInclusion P i) :=
      LinearMap.restrict
        (primePowImage (L := L) (r := r) (P := P) x i)
        (fun _ hx => prime_image_range (L := L) (r := r) (P := P) x i hx)
    have hconj :
        e.conj (primePowImage (L := L) (r := r) (P := P) x (i + 1)) = fRange := by
      simpa [e, fRange] using
        image_restrict_succ
          (L := L) (r := r) (P := P) x i
    rw [← LinearMap.trace_conj'
      (primePowImage (L := L) (r := r) (P := P) x (i + 1)) e, hconj]
  rw [restrict_q_image
    (L := L) (r := r) (hr := hr) (P := P) x i]
  rw [hrestrict]
  simpa [primeStepQ] using
    (step_trace_residue
      (L := L) (r := r) (P := P) hP0 hepos x i hi)

set_option maxHeartbeats 800000 in
-- Identifying the stage-zero trace with the quotient trace needs extra elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
lemma trace_image_quotient
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (x : NumberField.RingOfIntegers L)
    [Module.Finite (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))]
    [Module.Free (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0))] :
    LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        ↥(Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (P ^ 0))
        (primePowImage (L := L) (r := r) (P := P) x 0) =
      Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
        ((Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) x) := by
  have hI_ideal :
      (Ideal.map
        (Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
        (P ^ 0) : Ideal _) = ⊤ := by
    simpa [pow_zero] using
      (show
        (Ideal.map
          (Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
          (⊤ : Ideal (NumberField.RingOfIntegers L))) = ⊤ by
            simpa using
              (Ideal.map_top
                (Ideal.Quotient.mk
                  (P ^
                    (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))))
  let I : Ideal
      (NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :=
    Ideal.map
      (Ideal.Quotient.mk
        (P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)))
      (P ^ 0)
  have hI_big :
      ((I : Ideal
        (NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) :
          Submodule
            (NumberField.RingOfIntegers L ⧸
              P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
            (NumberField.RingOfIntegers L ⧸
              P ^
                (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) = ⊤ := by
    simpa [I] using hI_ideal
  have hI :
      I.restrictScalars (ℤ ⧸ Ideal.rationalPrimeIdeal r) = ⊤ := by
    exact
      (Submodule.restrictScalars_eq_top_iff
        (S := ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (R := NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
        (M := NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
        (p := (I : Submodule _ _))).2 hI_big
  let eTop :
      ↥(I.restrictScalars (ℤ ⧸ Ideal.rationalPrimeIdeal r)) ≃ₗ[
        ℤ ⧸ Ideal.rationalPrimeIdeal r]
      (NumberField.RingOfIntegers L ⧸
        P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :=
    LinearEquiv.ofTop
      (p := I.restrictScalars (ℤ ⧸ Ideal.rationalPrimeIdeal r)) hI
  have hconj :
      eTop.conj (primePowImage (L := L) (r := r) (P := P) x 0) =
        Algebra.lmul
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸
            P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
          ((Ideal.Quotient.mk
            (P ^
              (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) x) := by
    apply DFunLike.ext
    intro z
    change
      eTop
          (primePowImage (L := L) (r := r) (P := P) x 0
            (eTop.symm z)) =
        ((Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) x) * z
    rfl
  rw [← LinearMap.trace_conj'
    (primePowImage (L := L) (r := r) (P := P) x 0) eTop]
  simpa [Algebra.trace_apply] using
    congrArg
      (LinearMap.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) hconj

set_option maxHeartbeats 800000 in
-- Iterating the filtration trace identity requires more heartbeats for the recursive trace algebra.
set_option synthInstance.maxHeartbeats 200000 in
lemma ramification_idx_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP0 : P ≠ ⊥)
    [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (hepos :
      0 <
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)
    (x : NumberField.RingOfIntegers L) :
    Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸
          P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))
        ((Ideal.Quotient.mk
          (P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P))) x) =
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P :
            ℤ ⧸ Ideal.rationalPrimeIdeal r) *
        Algebra.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P)
          ((Ideal.Quotient.mk P) x) := by
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal hr
  letI : Field (ℤ ⧸ Ideal.rationalPrimeIdeal r) := Ideal.Quotient.field _
  let e :=
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
  have hle :
      Ideal.rationalPrimeIdeal r ≤
        Ideal.comap
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (P ^ e) := by
    exact Ideal.map_le_iff_le_comap.mp (show
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≤
        P ^ e from Ideal.le_pow_ramificationIdx)
  letI :
      Algebra
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P ^ e) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  have htower :
      IsScalarTower
        ℤ
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P ^ e) := .of_algebraMap_eq' rfl
  letI :
      IsScalarTower
        ℤ
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P ^ e) := htower
  have hfinZ :
      Module.Finite
        ℤ
        (NumberField.RingOfIntegers L ⧸ P ^ e) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℤ (P ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI :
      Module.Finite
        ℤ
        (NumberField.RingOfIntegers L ⧸ P ^ e) := hfinZ
  letI :
      Module.Finite
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P ^ e) :=
    @Module.Finite.of_restrictScalars_finite
      ℤ
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L ⧸ P ^ e)
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      htower
      hfinZ
  let τ :
      ℤ ⧸ Ideal.rationalPrimeIdeal r :=
    Algebra.trace
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L ⧸ P)
      ((Ideal.Quotient.mk P) x)
  let tr : ℕ → ℤ ⧸ Ideal.rationalPrimeIdeal r := fun i =>
    LinearMap.trace
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)
      ↥(Ideal.map
        (Ideal.Quotient.mk
          (P ^ e))
        (P ^ i))
      (primePowImage (L := L) (r := r) (P := P) x i)
  have hstep : ∀ i, i < e → tr i = tr (i + 1) + τ := by
    intro i hi
    simpa [tr, τ, e] using
      image_succ_residue
        (L := L) (r := r) (hr := hr) (P := P) hP0 hepos x i hi
  have htop :
      Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e) = (⊥ : Ideal _) := by
    simp [e]
  have htr_e : tr e = 0 := by
    unfold tr
    have hzero_map :
        primePowImage (L := L) (r := r) (P := P) x e = 0 := by
      ext z
      have hzmem : ((z : NumberField.RingOfIntegers L ⧸ P ^ e) ∈ (⊥ : Ideal _)) := by
        rw [← htop]
        exact z.2
      have hz : (z : NumberField.RingOfIntegers L ⧸ P ^ e) = 0 := by
        simpa using hzmem
      have hz' : z = 0 := Subtype.ext hz
      rw [hz']
      simp
    rw [hzero_map]
    simp
  have hrec : ∀ k, k ≤ e → tr (e - k) = (k : ℤ ⧸ Ideal.rationalPrimeIdeal r) * τ := by
    intro k hk
    induction k with
    | zero =>
        simpa [tr, τ, e] using htr_e
    | succ k ih =>
        have hk' : k ≤ e := Nat.le_of_succ_le hk
        have hlt : e - Nat.succ k < e := by
          omega
        have hsub : e - Nat.succ k + 1 = e - k := by
          omega
        calc
          tr (e - Nat.succ k)
              = tr (e - Nat.succ k + 1) + τ := hstep _ hlt
          _ = tr (e - k) + τ := by rw [hsub]
          _ = (k : ℤ ⧸ Ideal.rationalPrimeIdeal r) * τ + τ := by rw [ih hk']
          _ = ((Nat.succ k : ℤ ⧸ Ideal.rationalPrimeIdeal r)) * τ := by
                simp [Nat.succ_eq_add_one, add_mul]
  have htr0 : tr 0 = (e : ℤ ⧸ Ideal.rationalPrimeIdeal r) * τ := by
    simpa [e] using hrec e le_rfl
  calc
    Algebra.trace
        (ℤ ⧸ Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L ⧸ P ^ e)
        ((Ideal.Quotient.mk (P ^ e)) x)
      =
    tr 0 := by
      symm
      simpa [tr, e] using
        trace_image_quotient
          (L := L) (r := r) (P := P) x
    _ = (e : ℤ ⧸ Ideal.rationalPrimeIdeal r) * τ := htr0
    _ =
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P :
            ℤ ⧸ Ideal.rationalPrimeIdeal r) *
        Algebra.trace
          (ℤ ⧸ Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L ⧸ P)
          ((Ideal.Quotient.mk P) x) := by
            rfl

set_option maxHeartbeats 800000 in
-- The final contradiction combines CRT, quotient traces, and the iterated filtration trace formula.
set_option synthInstance.maxHeartbeats 200000 in
lemma different_coprime_factorization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hPQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q)
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    ¬ P ^
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ∣
      differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  let O := NumberField.RingOfIntegers L
  let p := Ideal.rationalPrimeIdeal r
  let e :=
    Ideal.ramificationIdx p
      P
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal hP.1 hP0
  letI : p.IsMaximal := rational_ideal_maximal hr
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field _
  have hepos : 0 < e := idx_pos_coprime (L := L) (hr := hr) hcop
  have hsup : P ⊔ Q = ⊤ := by
    simpa [O, p, e] using
      sup_idx_factorization
        (L := L) (hr := hr) (P := P) (Q := Q) hP hPQ
  rcases factor_nonzero_residue
      (L := L) (hr := hr) (P := P) (Q := Q) hP0 hsup with
    ⟨x, hxQ, hresnz⟩
  intro hdiv
  have hintmem :
      Algebra.intTrace ℤ O x ∈ p := by
    simpa [O, p, e] using
      int_dvd_different
        (L := L) (hr := hr) (I := P ^ e) (Q := Q) hPQ hdiv hxQ
  have hlePow :
      p ≤ Ideal.comap (algebraMap ℤ O) (P ^ e) := by
    exact Ideal.map_le_iff_le_comap.mp (show
      Ideal.map (algebraMap ℤ O) p ≤ P ^ e from Ideal.le_pow_ramificationIdx)
  letI : Algebra (ℤ ⧸ p) (O ⧸ P ^ e) :=
    Ideal.Quotient.algebraQuotientOfLEComap hlePow
  have htowerPow : IsScalarTower ℤ (ℤ ⧸ p) (O ⧸ P ^ e) := .of_algebraMap_eq' rfl
  letI : IsScalarTower ℤ (ℤ ⧸ p) (O ⧸ P ^ e) := htowerPow
  have hfinPowZ : Module.Finite ℤ (O ⧸ P ^ e) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℤ (P ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite ℤ (O ⧸ P ^ e) := hfinPowZ
  letI : Module.Finite (ℤ ⧸ p) (O ⧸ P ^ e) :=
    @Module.Finite.of_restrictScalars_finite
      ℤ (ℤ ⧸ p) (O ⧸ P ^ e)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      htowerPow hfinPowZ
  have hleQmap :
      Ideal.map (algebraMap ℤ O) p ≤ Q := by
    rw [hPQ]
    exact (Ideal.mul_le_left : P ^ e * Q ≤ Q)
  have hleQ :
      p ≤ Ideal.comap (algebraMap ℤ O) Q := by
    exact Ideal.map_le_iff_le_comap.mp hleQmap
  letI : Algebra (ℤ ⧸ p) (O ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap hleQ
  have htowerQ : IsScalarTower ℤ (ℤ ⧸ p) (O ⧸ Q) := .of_algebraMap_eq' rfl
  letI : IsScalarTower ℤ (ℤ ⧸ p) (O ⧸ Q) := htowerQ
  have hfinQZ : Module.Finite ℤ (O ⧸ Q) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℤ Q).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite ℤ (O ⧸ Q) := hfinQZ
  letI : Module.Finite (ℤ ⧸ p) (O ⧸ Q) :=
    @Module.Finite.of_restrictScalars_finite
      ℤ (ℤ ⧸ p) (O ⧸ Q)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      htowerQ hfinQZ
  have hcopPQ : IsCoprime (P ^ e) Q := by
    exact (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  let eTotal :
      (O ⧸ Ideal.map (algebraMap ℤ O) p) ≃ₐ[ℤ ⧸ p]
        ((O ⧸ P ^ e) × O ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hPQ).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hcopPQ)
      commutes' := Quotient.ind fun _ => rfl }
  have htrace_map :
      Algebra.trace
          (ℤ ⧸ p)
          (O ⧸ Ideal.map (algebraMap ℤ O) p)
          ((Ideal.Quotient.mk (Ideal.map (algebraMap ℤ O) p)) x) =
        0 := by
    rw [Algebra.trace_quotient_eq_of_isDedekindDomain]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hintmem
  have htrace_prod :
      Algebra.trace
          (ℤ ⧸ p)
          (O ⧸ P ^ e)
          ((Ideal.Quotient.mk (P ^ e)) x) =
        0 := by
    have htmp :
        Algebra.trace
            (ℤ ⧸ p)
            ((O ⧸ P ^ e) × O ⧸ Q)
            (eTotal ((Ideal.Quotient.mk (Ideal.map (algebraMap ℤ O) p)) x)) =
          0 := by
      exact (Algebra.trace_eq_of_algEquiv eTotal _).trans htrace_map
    have hcomp :
        eTotal ((Ideal.Quotient.mk (Ideal.map (algebraMap ℤ O) p)) x) =
          ((Ideal.Quotient.mk (P ^ e)) x, 0) := by
      ext
      · change
          Ideal.Quotient.factor (Ideal.mul_le_right : P ^ e * Q ≤ P ^ e)
              ((Ideal.quotEquivOfEq hPQ)
                ((Ideal.Quotient.mk (Ideal.map (algebraMap ℤ O) p)) x)) =
            (Ideal.Quotient.mk (P ^ e)) x
        rfl
      · change
          (Ideal.Quotient.mk Q) x = 0
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hxQ
    rw [Algebra.trace_prod_apply] at htmp
    rw [hcomp] at htmp
    simpa using htmp
  have hformula :
      (e : ℤ ⧸ p) *
          Algebra.trace
            (ℤ ⧸ p)
            (O ⧸ P)
            ((Ideal.Quotient.mk P) x) =
        0 := by
    rw [← ramification_idx_residue
      (L := L) (r := r) (hr := hr) (P := P) hP0 hepos x]
    exact htrace_prod
  have he_ne0 : (e : ℤ ⧸ p) ≠ 0 := by
    intro hzero
    have hmem : (e : ℤ) ∈ p := by
      exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa [p] using hzero)
    have hmem' : (e : ℤ) ∈ Ideal.span ({(r : ℤ)} : Set ℤ) := by
      simpa [Ideal.rationalPrimeIdeal] using hmem
    rw [Ideal.mem_span_singleton] at hmem'
    rcases hmem' with ⟨n, hn⟩
    have hrdvd_int : (r : ℤ) ∣ (e : ℤ) := ⟨n, by simpa [mul_comm] using hn⟩
    have hrdvd : r ∣ e := Int.natCast_dvd_natCast.mp hrdvd_int
    exact ((Nat.Prime.coprime_iff_not_dvd hr).1 hcop) hrdvd
  have hres0 :
      Algebra.trace
          (ℤ ⧸ p)
          (O ⧸ P)
          ((Ideal.Quotient.mk P) x) = 0 := by
    exact (mul_eq_zero.mp hformula).resolve_left he_ne0
  exact hresnz hres0

lemma witness_coprime_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P Q : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hsup : P ⊔ Q = ⊤)
    (hPQ :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) =
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q)
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    ∃ x : NumberField.RingOfIntegers L,
      x ∈ Q ∧
      Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∉
        Ideal.rationalPrimeIdeal r := by
  let _ := hsup
  exact witness_factorization_different
    (L := L) (hr := hr) (I := P ^
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) (Q := Q) hPQ
    (different_coprime_factorization
      (L := L) (hr := hr) (P := P) (Q := Q) hP hPQ hcop)

lemma witness_idx_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L),
      ∃ x : NumberField.RingOfIntegers L,
        P ^
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) * Q =
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.rationalPrimeIdeal r) ∧
        x ∈ Q ∧
        Algebra.intTrace ℤ (NumberField.RingOfIntegers L) x ∉
          Ideal.rationalPrimeIdeal r := by
  rcases coprime_ramification_idx
      (L := L) (hr := hr) hP with ⟨Q, hsup, hPQ⟩
  rcases witness_coprime_idx
      (L := L) (hr := hr) (P := P) (Q := Q) hP hsup hPQ hcop with
    ⟨x, hxQ, htrace⟩
  refine ⟨Q, x, ?_, hxQ, htrace⟩
  simpa [mul_comm] using hPQ.symm

lemma ramification_different_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hcop : Nat.Coprime r
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    ¬ P ^
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ∣
      differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  rcases coprime_ramification_idx
      (L := L) (hr := hr) hP with ⟨Q, hsup, hPQ⟩
  let _ := hsup
  exact different_coprime_factorization
    (L := L) (hr := hr) (P := P) (Q := Q) hP hPQ hcop

lemma ramification_different_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} {e : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hram :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = e)
    (hnot :
      ¬ P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ∣
        differentIdeal ℤ (NumberField.RingOfIntegers L)) :
    ¬ P ^ e ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  simpa [← hram] using hnot

lemma ramification_different_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    ¬ P ^ (e r) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  have hr : Nat.Prime r := hSprime r hrS
  have hram :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
        e r := by
    exact ramification_idx_indices
      (L := L) (S := S) (e := e) hSprime he_idx hrS hP
  have hcop :
      Nat.Coprime r
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) := by
    exact idx_coprime_indices
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS hP
  have hnot :
      ¬ P ^
          (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) ∣
        differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    exact ramification_different_coprime
      (L := L) (hr := hr) hP hcop
  exact ramification_different_idx
    (L := L) (r := r) (e := e r) hram hnot

lemma sup_forall_dvd
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {I : Ideal (NumberField.RingOfIntegers L)}
    {r : ℕ} (hr : Nat.Prime r)
    (hnot : ∀ P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L),
      ¬ P ∣ I) :
    Ideal.map
        (algebraMap ℤ (NumberField.RingOfIntegers L))
        (Ideal.rationalPrimeIdeal r) ⊔
      I = ⊤ := by
  by_contra hsup
  rcases Ideal.exists_le_maximal
      (Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        I) hsup with
    ⟨P, hPmax, hPle⟩
  letI : P.IsPrime := hPmax.isPrime
  have hmap_le :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ≤ P :=
    le_trans le_sup_left hPle
  have hI_le : I ≤ P := le_trans le_sup_right hPle
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r) :=
    rational_prime_lies (L := L) hr hmap_le
  have hPmem : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) :=
    ⟨inferInstance, inferInstance⟩
  exact hnot P hPmem ((Ideal.dvd_iff_le).2 hI_le)

lemma r_sup_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {I : Ideal (NumberField.RingOfIntegers L)}
    {r : ℕ}
    (hsup :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        I = ⊤) :
    IsUnit
      ((Ideal.Quotient.mk I) (r : NumberField.RingOfIntegers L)) := by
  have h1_mem :
      (1 : NumberField.RingOfIntegers L) ∈
        Ideal.map
            (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.rationalPrimeIdeal r) ⊔
          I := by
    rw [hsup]
    simp
  rcases (Submodule.mem_sup).1 h1_mem with ⟨a, ha, b, hb, hab⟩
  rw [rational_span_cast (L := L) r] at ha
  rcases (Ideal.mem_span_singleton').1 ha with ⟨c, hc⟩
  let q := Ideal.Quotient.mk I
  have hq_b : q b = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hb
  have hmul :
      q c * q (r : NumberField.RingOfIntegers L) = 1 := by
    have hqab : q a + q b = 1 := by
      simpa using congrArg q hab
    have hqa : q a = q c * q (r : NumberField.RingOfIntegers L) := by
      rw [← hc]
      simp [q]
    calc
      q c * q (r : NumberField.RingOfIntegers L) = q a := hqa.symm
      _ = q a + q b := by
            rw [hq_b]
            symm
            exact add_zero (q a)
      _ = 1 := hqab
  exact (isUnit_iff_exists_inv).2 ⟨q c, by
    simpa [mul_comm] using hmul⟩

lemma not_abs_forall
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {I : Ideal (NumberField.RingOfIntegers L)}
    (hI0 : Ideal.absNorm I ≠ 0)
    {r : ℕ} (hr : Nat.Prime r)
    (hnot : ∀ P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L),
      ¬ P ∣ I) :
    ¬ r ∣ Ideal.absNorm I := by
  have hsup :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        I = ⊤ := by
    exact sup_forall_dvd
      (L := L) hr hnot
  have hunit :
      IsUnit ((Ideal.Quotient.mk I) (r : NumberField.RingOfIntegers L)) := by
    exact r_sup_top
      (L := L) hsup
  exact not_abs_r
    (O := NumberField.RingOfIntegers L) (I := I) hI0 hr hunit

lemma dvd_abs_norm
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {I : Ideal (NumberField.RingOfIntegers L)}
    (hI0 : Ideal.absNorm I ≠ 0)
    {r : ℕ} (hr : Nat.Prime r)
    (hdvd : r ∣ Ideal.absNorm I) :
    ∃ P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L), P ∣ I := by
  by_contra hcontra
  have hnot : ∀ P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L),
      ¬ P ∣ I := by
    intro P hP hPI
    exact hcontra ⟨P, hP, hPI⟩
  exact (not_abs_forall
    (L := L) (I := I) hI0 hr hnot) hdvd

lemma abs_powers_power
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    {r : ℕ} (hrS : r ∈ S) :
    Ideal.absNorm
        (∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          P ^ (e r - 1)) =
      r ^
        ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1))) := by
  classical
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  let T : Finset (Ideal (NumberField.RingOfIntegers L)) :=
    IsDedekindDomain.primesOverFinset qI (NumberField.RingOfIntegers L)
  have hr : Nat.Prime r := hSprime r hrS
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := by simpa [qI] using rational_ideal_maximal hr
  calc
    Ideal.absNorm (∏ P ∈ T, P ^ (e r - 1))
      = ∏ P ∈ T, Ideal.absNorm (P ^ (e r - 1)) := by
          simp
    _ = ∏ P ∈ T, r ^
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) := by
          refine Finset.prod_congr rfl ?_
          intro P hP
          have hP' :
              P ∈ qI.primesOver (NumberField.RingOfIntegers L) := by
            exact (IsDedekindDomain.mem_primesOverFinset_iff hqI0 (NumberField.RingOfIntegers L)).1
              (by simpa [T] using hP)
          letI : P.LiesOver qI := hP'.2
          have hinertia :
              (Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) =
                Ideal.inertiaDeg qI P := by
            simpa [qI] using
              rational_deg_primes
                (L := L) (hr := hr) hP'
          have habs :
              Ideal.absNorm P = r ^ Ideal.inertiaDeg qI P := by
            simpa [qI] using
              abs_inertia_deg
                (L := L) (hr := hr) (P := P)
          rw [show Ideal.absNorm (P ^ (e r - 1)) = Ideal.absNorm P ^ (e r - 1) by simp]
          rw [habs]
          simp [hinertia, pow_mul]
      _ = r ^
        (T.card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1))) := by
          simp [Finset.prod_const, pow_mul, Nat.mul_assoc, Nat.mul_comm]
      _ = r ^
        ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1))) := by
          simp [T, qI]

lemma abs_powers_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    {r : ℕ} (hrS : r ∈ S)
    {J : Ideal (NumberField.RingOfIntegers L)}
    (hJ :
      differentIdeal ℤ (NumberField.RingOfIntegers L) =
        (∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          P ^ (e r - 1)) * J) :
    Ideal.absNorm J ≠ 0 := by
  let _ := hSprime
  let _ := hrS
  intro hJ0
  have hzero :
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) = 0 := by
    rw [hJ, Ideal.absNorm.map_mul, hJ0]
    simp
  exact abs_different_ne (L := L) hzero

lemma abs_powers_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    {r : ℕ} (hrS : r ∈ S)
    {J : Ideal (NumberField.RingOfIntegers L)}
    (hJ :
      differentIdeal ℤ (NumberField.RingOfIntegers L) =
        (∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          P ^ (e r - 1)) * J)
    (hdvd :
      r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1)) + 1) ∣
        Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))) :
    r ∣ Ideal.absNorm J := by
  have hr : Nat.Prime r := hSprime r hrS
  have hdvd' :
      r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1)) + 1) ∣
        r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1))) * Ideal.absNorm J := by
    simpa [hJ, Ideal.absNorm.map_mul,
      abs_powers_power
        (L := L) (S := S) (e := e) hSprime hrS] using hdvd
  have hdvd'' :
      r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1))) * r ∣
        r ^
          ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
            (NumberField.RingOfIntegers L)).card *
            ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
              (e r - 1))) * Ideal.absNorm J := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdvd'
  exact Nat.dvd_of_mul_dvd_mul_left
    (pow_pos hr.pos
      ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
        ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
          (e r - 1)))) hdvd''

lemma global_ramification_pos
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    0 < e r := by
  by_contra hpos
  have hzero : e r = 0 := Nat.eq_zero_of_not_pos hpos
  have hnot :
      ¬ P ^ (e r) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    exact ramification_different_indices
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS hP
  have htriv : P ^ (e r) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    rw [hzero]
    simp
  exact hnot htriv

lemma pred_dvd_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (e : ℕ → ℕ)
    {r : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
      (NumberField.RingOfIntegers L)) :
    P ^ (e r - 1) ∣
      ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L),
        Q ^ (e r - 1) := by
  simpa using
    (Finset.dvd_prod_of_mem
      (s := IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L))
      (f := fun Q : Ideal (NumberField.RingOfIntegers L) => Q ^ (e r - 1))
      hP)

lemma ramification_dvd_different
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S)
    {P J : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L))
    (hPJ : P ∣ J)
    (hJ :
      differentIdeal ℤ (NumberField.RingOfIntegers L) =
        (∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          Q ^ (e r - 1)) * J) :
    P ^ (e r) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  have hPprod :
      P ^ (e r - 1) ∣
        ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          Q ^ (e r - 1) := by
    letI : (Ideal.rationalPrimeIdeal r).IsMaximal := rational_ideal_maximal (hSprime r hrS)
    exact pred_dvd_powers
      (L := L) (e := e) (by
        simpa using
          (IsDedekindDomain.mem_primesOverFinset_iff
            (rational_ne_bot (hSprime r hrS))
            (NumberField.RingOfIntegers L)).2 hP)
  have hmul :
      P ^ (e r - 1) * P ∣
        (∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L),
          Q ^ (e r - 1)) * J := by
    exact mul_dvd_mul hPprod hPJ
  have hpos : 0 < e r := by
    exact global_ramification_pos
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS hP
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨n, hn⟩
  have hJ' := hJ
  have hmul' := hmul
  rw [hn] at hJ'
  rw [hn] at hmul' ⊢
  simpa [hJ', pow_succ, Nat.succ_sub_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    using hmul'

lemma abs_different_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    ¬ r ^
        ((IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) + 1) ∣
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  classical
  have hprod_div :
      ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L),
          P ^ (e r - 1) ∣
        differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    exact powers_different_indices
      (L := L) (S := S) (e := e) hSprime he_idx hrS
  rcases hprod_div with ⟨J, hJ⟩
  intro hdvd
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    exact abs_powers_ideal
      (L := L) (S := S) (e := e) hSprime hrS hJ
  have hJdvd : r ∣ Ideal.absNorm J := by
    exact abs_powers_different
      (L := L) (S := S) (e := e) hSprime hrS hJ hdvd
  rcases dvd_abs_norm
      (L := L) (I := J) hJ0 (hSprime r hrS) hJdvd with
    ⟨P, hP, hPJ⟩
  have hPow :
      P ^ (e r) ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
    exact ramification_dvd_different
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS hP hPJ hJ
  exact
    (ramification_different_indices
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS hP) hPow

lemma abs_different_target
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r ≤
      (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
        (NumberField.RingOfIntegers L)).card *
        ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
          (e r - 1)) := by
  have hr : Nat.Prime r := hSprime r hrS
  exact factorization_not_dvd hr
    (abs_different_ne (L := L))
    (abs_different_succ
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS)

lemma different_ideal_target
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r ≤
      Module.finrank ℚ L - Module.finrank ℚ L / e r := by
  have htarget :
      Module.finrank ℚ L - Module.finrank ℚ L / e r =
        (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) := by
    exact target_deg_pred
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS
  have hle :
      (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r ≤
        (IsDedekindDomain.primesOverFinset (Ideal.rationalPrimeIdeal r)
          (NumberField.RingOfIntegers L)).card *
          ((Ideal.rationalPrimeIdeal r).inertiaDegIn (NumberField.RingOfIntegers L) *
            (e r - 1)) := by
    exact abs_different_target
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS
  simpa [htarget] using hle

lemma factorization_different_target
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    {r : ℕ} (hrS : r ∈ S) :
    (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r =
      Module.finrank ℚ L - Module.finrank ℚ L / e r := by
  exact le_antisymm
    (different_ideal_target
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS)
    (factorization_abs_target
      (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS)

lemma abs_powers_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1) :
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) =
      ∏ r ∈ S, r ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
  calc
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))
      = Finset.prod S (fun r =>
          r ^
            (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization
              r) := by
            exact abs_different_s
              (L := L) (S := S) (e := e) hSprime he_idx he_one
    _ = ∏ r ∈ S, r ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
          refine Finset.prod_congr rfl ?_
          intro r hrS
          rw [factorization_different_target
            (L := L) (S := S) (e := e) hSprime he_idx he_coprime hrS]

lemma discriminant_powers_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1) :
    absDiscriminant L =
      ∏ r ∈ S, (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
  calc
    absDiscriminant L
      = Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
          exact abs_discriminant_different (L := L)
    _ = ((∏ r ∈ S, r ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) : ℕ) : ℝ) := by
          exact_mod_cast
            (abs_powers_indices
              (L := L) (S := S) e hSprime he_idx he_coprime he_one)
    _ = ∏ r ∈ S, (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
          exact_mod_cast rfl

lemma abs_discriminant_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1) :
    absDiscriminant L =
      (∏ r ∈ S, tameDiscriminantFactor r (e r)) ^ Module.finrank ℚ L := by
  calc
    absDiscriminant L
      = ∏ r ∈ S, (r : ℝ) ^ (Module.finrank ℚ L - Module.finrank ℚ L / e r) := by
          exact discriminant_powers_indices
            (L := L) (S := S) e hSprime he_idx he_coprime he_one
    _ = (∏ r ∈ S, tameDiscriminantFactor r (e r)) ^ Module.finrank ℚ L := by
          symm
          exact tame_discriminant_powers
            (L := L) (S := S) e hSprime he_idx he_coprime

lemma discriminant_global_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ) (e : ℕ → ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (he_idx : ∀ r, Nat.Prime r →
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    (he_one : ∀ {r : ℕ}, r ∉ S → e r = 1) :
    rootDiscriminant L = ∏ r ∈ S, tameDiscriminantFactor r (e r) := by
  let x : ℝ := ∏ r ∈ S, tameDiscriminantFactor r (e r)
  have hx_nonneg : 0 ≤ x := by
    exact le_of_lt (tame_discriminant_pos S e hSprime)
  have hdisc : absDiscriminant L = x ^ Module.finrank ℚ L := by
    dsimp [x]
    exact abs_discriminant_indices
      (L := L) (S := S) e hSprime he_idx he_coprime he_one
  have hdisc' : absDiscriminant L = x ^ Module.finrank ℚ L := by
    simpa using hdisc
  exact discriminant_abs_finrank
    (L := L) hx_nonneg hdisc'

lemma discriminant_tame_indices
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (e : ℕ → ℕ)
    (he_idx : ∀ r ∈ S,
      RationalRamificationIdx (S := NumberField.RingOfIntegers L) r (e r))
    (he_coprime : ∀ r ∈ S, Nat.Coprime r (e r))
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    rootDiscriminant L = ∏ r ∈ S, tameDiscriminantFactor r (e r) := by
  calc
    rootDiscriminant L =
        ∏ r ∈ S, tameDiscriminantFactor r (tameRamificationExtension S e r) := by
          exact discriminant_global_indices
            (L := L) (S := S) (tameRamificationExtension S e) hSprime
            (tame_ramification_spec
              (L := L) (S := S) e he_idx hram)
            (tame_ramification_coprime
              (S := S) e he_coprime)
            (tame_ramification_not (S := S) e)
    _ = ∏ r ∈ S, tameDiscriminantFactor r (e r) := by
          refine Finset.prod_congr rfl ?_
          intro r hrS
          simp [tame_ramification_extension S e hrS]

lemma tame_discriminant_factorization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r)
    (htame : ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    ∃ e : ℕ → ℕ,
      rootDiscriminant L = ∏ r ∈ S, tameDiscriminantFactor r (e r) := by
  obtain ⟨e, he⟩ :=
    tame_ramification_function
      (L := L) (S := S) hSprime htame
  refine ⟨e, ?_⟩
  exact discriminant_tame_indices
    (L := L) (S := S) hSprime e
    (fun r hrS => tame_index_function (L := L) (S := S) he hrS)
    (fun r hrS => tame_function_coprime (L := L) (S := S) he hrS)
    hram

/--
Weak tame discriminant bound, sufficient for the tower construction.

If `L/ℚ` is finite and ramified only at the finite set `S`,
and all ramification at primes in `S` is tame, then the root discriminant
is bounded by the product of the primes in `S`.
-/
theorem discriminant_ramified_tame
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r)
    (htame : ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r) :
    rootDiscriminant L ≤ ∏ r ∈ S, (r : ℝ) := by
  obtain ⟨e, hfactorization⟩ :=
    tame_discriminant_factorization
      (L := L) (S := S) hSprime
      (ramification_hypothesis_unramified (L := L) (S := S) hram)
      (tame_hypothesis_primes (L := L) (S := S) htame)
  calc
    rootDiscriminant L = ∏ r ∈ S, tameDiscriminantFactor r (e r) := hfactorization
    _ ≤ ∏ r ∈ S, (r : ℝ) := tame_discriminant_factor S e hSprime

/--
A finite Galois `ℓ`-extension of `ℚ`, ramified only at primes in `S`
with `ℓ ∉ S`, has root discriminant at most the product of the primes in `S`.
-/
lemma ne_finset_not
    {ℓ : ℕ} {S : Finset ℕ} {r : ℕ}
    (hrS : r ∈ S)
    (hSaway : ℓ ∉ S) :
    r ≠ ℓ := by
  intro hEq
  apply hSaway
  simpa [hEq] using hrS

lemma prime_coprime_ne
    {r ℓ n : ℕ}
    (hr : Nat.Prime r)
    (hℓ : Nat.Prime ℓ)
    (hr_ne_ℓ : r ≠ ℓ) :
    Nat.Coprime r (ℓ ^ n) := by
  have hr_coprime_ℓ : Nat.Coprime r ℓ := (Nat.coprime_primes hr hℓ).2 hr_ne_ℓ
  exact hr_coprime_ℓ.pow_right n

lemma coprime_card_p
    {r ℓ : ℕ} (hr : Nat.Prime r) (hℓ : Nat.Prime ℓ)
    {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup ℓ G) (hr_ne_ℓ : r ≠ ℓ) :
    Nat.Coprime r (Nat.card G) := by
  letI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn]
  exact prime_coprime_ne hr hℓ hr_ne_ℓ

lemma coprime_gal_finset
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (hGal : IsPGroup ℓ (Gal(L/ℚ)))
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (hSaway : ℓ ∉ S)
    {r : ℕ} (hrS : r ∈ S) :
    Nat.Coprime r (Nat.card (Gal(L/ℚ))) := by
  have hr : Nat.Prime r := hSprime r hrS
  have hr_ne_ℓ : r ≠ ℓ := ne_finset_not hrS hSaway
  exact coprime_card_p hr hℓ hGal hr_ne_ℓ

lemma tamely_ramified_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ}
    (hcop :
      ∀ P : Ideal (NumberField.RingOfIntegers L),
        P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) →
          Nat.Coprime r
            (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P)) :
    RationalTamePrimes (S := NumberField.RingOfIntegers L) r := by
  intro P hP
  exact hcop P hP

lemma ramification_idx_gal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r) :
    (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) ∣
      Nat.card (Gal(L/ℚ)) := by
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hr
  letI : qI.IsMaximal := rational_ideal_maximal hr
  have hmain :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := qI) hqI0 (NumberField.RingOfIntegers L) (Gal(L/ℚ))
  refine ⟨(qI.primesOver (NumberField.RingOfIntegers L)).ncard *
      qI.inertiaDegIn (NumberField.RingOfIntegers L), ?_⟩
  calc
    Nat.card (Gal(L/ℚ))
      = (qI.primesOver (NumberField.RingOfIntegers L)).ncard *
          (qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
            qI.inertiaDegIn (NumberField.RingOfIntegers L)) := by
              simpa using hmain.symm
    _ = qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
          ((qI.primesOver (NumberField.RingOfIntegers L)).ncard *
            qI.inertiaDegIn (NumberField.RingOfIntegers L)) := by
              ac_rfl

lemma idx_coprime_gal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hcop : Nat.Coprime r (Nat.card (Gal(L/ℚ))))
    {e : ℕ} (hdiv : e ∣ Nat.card (Gal(L/ℚ))) :
    Nat.Coprime r e := by
  exact Nat.Coprime.coprime_dvd_right hdiv hcop

lemma rational_idx_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
      (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
  let _ := hr
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r) := hP.2
  symm
  exact Ideal.ramificationIdxIn_eq_ramificationIdx
    (p := Ideal.rationalPrimeIdeal r) (P := P) (G := Gal(L/ℚ))

lemma ramification_idx_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
      ∣ (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
  rw [rational_idx_primes
    (L := L) (hr := hr) hP]

lemma ramification_idx_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (hP : P.LiesOver (Ideal.rationalPrimeIdeal r)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
      ∣ (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
  exact ramification_idx_primes
    (L := L) (hr := hr) ⟨inferInstance, hP⟩

lemma ramification_idx_multiple
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (hP : P.LiesOver (Ideal.rationalPrimeIdeal r)) :
    ∃ Q : Ideal (NumberField.RingOfIntegers L),
      Q ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L) ∧
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
          ∣ Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) Q := by
  refine ⟨P, ?_, dvd_rfl⟩
  exact ⟨inferInstance, hP⟩

lemma rational_ramification_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (hP : P.LiesOver (Ideal.rationalPrimeIdeal r)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
      ∣ (Ideal.rationalPrimeIdeal r).ramificationIdxIn (NumberField.RingOfIntegers L) := by
  obtain ⟨Q, hQ, hdiv⟩ :=
    ramification_idx_multiple (L := L) (r := r) P hP
  exact dvd_trans hdiv
    (ramification_idx_primes
      (L := L) (hr := hr) hQ)

lemma rational_gal_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (hP : P.LiesOver (Ideal.rationalPrimeIdeal r)) :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P
      ∣ Nat.card (Gal(L/ℚ)) := by
  exact dvd_trans
    (rational_ramification_lies
      (L := L) (hr := hr) P hP)
    (ramification_idx_gal (L := L) (hr := hr))

lemma tamely_ramified_gal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (hcop : Nat.Coprime r (Nat.card (Gal(L/ℚ)))) :
    RationalTamePrimes (S := NumberField.RingOfIntegers L) r := by
  exact tamely_ramified_coprime
    (L := L) (r := r) fun P hP =>
      idx_coprime_gal
        (L := L) (r := r) (hcop := hcop)
        (dvd_trans
          (ramification_idx_primes
            (L := L) (hr := hr) hP)
          (ramification_idx_gal
            (L := L) (hr := hr)))

lemma tame_hypothesis_away
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (hGal : IsPGroup ℓ (Gal(L/ℚ)))
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (hSaway : ℓ ∉ S) :
    ∀ r ∈ S,
      RationalTamePrimes (S := NumberField.RingOfIntegers L) r := by
  intro r hrS
  have hr : Nat.Prime r := hSprime r hrS
  have hcop : Nat.Coprime r (Nat.card (Gal(L/ℚ))) :=
    coprime_gal_finset
      (ℓ := ℓ) hℓ (L := L) hGal S hSprime hSaway hrS
  exact tamely_ramified_gal (L := L) hr hcop

theorem discriminant_ramified_ell
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L]
    (hGal : IsPGroup ℓ (Gal(L/ℚ)))
    (S : Finset ℕ)
    (hSprime : ∀ r ∈ S, Nat.Prime r)
    (hSaway : ℓ ∉ S)
    (hram : ∀ r, Nat.Prime r → r ∉ S →
      RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    rootDiscriminant L ≤ ∏ r ∈ S, (r : ℝ) := by
  exact discriminant_ramified_tame
    (L := L) (S := S) hSprime hram
    (tame_hypothesis_away
      (ℓ := ℓ) hℓ (L := L) hGal S hSprime hSaway)

/-- If `K` has signature `(r₁,r₂)` and `S ≠ ∅`, the HMR constant is
`α_{K,S} := 2 + 2 * sqrt (r₁ + r₂)`. Here `r₁` and `r₂` are supplied by Mathlib as
`NumberField.InfinitePlace.nrRealPlaces K` and
`NumberField.InfinitePlace.nrComplexPlaces K`. -/
def hmrAlpha (K : Type*) [Field K] [NumberField K] : ℝ :=
  2 + 2 * Real.sqrt
    (NumberField.InfinitePlace.nrRealPlaces K +
      NumberField.InfinitePlace.nrComplexPlaces K)

end Towers
