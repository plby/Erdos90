import Submission.NumberTheory.Locals.TotallyRamifiedEisenstein

/-!
# The local different bound used in Milne, Theorem 8.42

This file develops the classical degree-dependent bound for the different of
a totally ramified extension of discrete valuation rings.  The first step is
the restriction formula for normalized additive valuations: if the maximal
ideal downstairs extends to the `e`-th power of the maximal ideal upstairs,
then restriction multiplies valuations by `e`.
-/

namespace Submission.NumberTheory.Milne

open scoped BigOperators

/-- The finite normalized DVR valuation of a nonzero natural number viewed
in a characteristic-zero discrete valuation ring. -/
noncomputable def dvrCastValuation
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] (n : ℕ) : ℕ :=
  (IsDiscreteValuationRing.addVal R (n : R)).toNat

theorem val_dvr_valuation
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] (n : ℕ) (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal R (n : R) = dvrCastValuation R n := by
  apply (ENat.coe_toNat_eq_self.mpr ?_).symm
  rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact Nat.cast_ne_zero.mpr hn

/-- A finite sum of nonzero elements with pairwise distinct DVR valuations
has the valuation of its unique term of smallest valuation. -/
theorem val_pairwise_ne
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ι : Type*} (s : Finset ι) (f : ι → R)
    (hs : s.Nonempty)
    (hpair : (s : Set ι).Pairwise fun i j ↦
      IsDiscreteValuationRing.addVal R (f i) ≠
        IsDiscreteValuationRing.addVal R (f j)) :
    ∃ j ∈ s,
      IsDiscreteValuationRing.addVal R (s.sum f) =
          IsDiscreteValuationRing.addVal R (f j) ∧
        ∀ i ∈ s,
          IsDiscreteValuationRing.addVal R (f j) ≤
            IsDiscreteValuationRing.addVal R (f i) := by
  classical
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image
    (fun i ↦ IsDiscreteValuationRing.addVal R (f i)) hs
  refine ⟨j, hj, ?_, hmin⟩
  let v := AddValuation.toValuation (IsDiscreteValuationRing.addVal R)
  have hv : v (s.sum f) = v (f j) := by
    apply Valuation.map_sum_eq_of_lt v hj
    intro i hi
    have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
    have hij : i ≠ j := by
      simpa using (Finset.mem_sdiff.mp hi).2
    have hne : IsDiscreteValuationRing.addVal R (f i) ≠
        IsDiscreteValuationRing.addVal R (f j) :=
      hpair his hj hij
    have hlt : IsDiscreteValuationRing.addVal R (f j) <
        IsDiscreteValuationRing.addVal R (f i) :=
      lt_of_le_of_ne (hmin i his) hne.symm
    exact hlt
  simpa [v] using hv

/-- Restriction of the normalized additive valuation through a totally
ramified extension multiplies values by the ramification index. -/
theorem val_nsmul_maximal
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (Pi : B) (hPi : Irreducible Pi) (e : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (x : A) :
    IsDiscreteValuationRing.addVal B (algebraMap A B x) =
      e • IsDiscreteValuationRing.addVal A x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨k, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hpi
  have hspan :
      Ideal.span ({algebraMap A B pi} : Set B) =
        Ideal.span ({Pi ^ e} : Set B) := by
    calc
      Ideal.span ({algebraMap A B pi} : Set B) =
          Ideal.map (algebraMap A B) (Ideal.span ({pi} : Set A)) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) := by
        rw [hpi.maximalIdeal_eq]
      _ = Ideal.span ({Pi} : Set B) ^ e := hmap
      _ = Ideal.span ({Pi ^ e} : Set B) := Ideal.span_singleton_pow Pi e
  have hassociated : Associated (algebraMap A B pi) (Pi ^ e) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  have hvalPi :
      IsDiscreteValuationRing.addVal B (algebraMap A B pi) = e := by
    calc
      IsDiscreteValuationRing.addVal B (algebraMap A B pi) =
          IsDiscreteValuationRing.addVal B (Pi ^ e) := by
        apply le_antisymm
        · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hassociated.dvd
        · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hassociated.symm.dvd
      _ = e := hPi.addVal_pow e
  have hvalUnitA : IsDiscreteValuationRing.addVal A (u : A) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit
  have hvalUnitB :
      IsDiscreteValuationRing.addVal B (algebraMap A B (u : A)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap A B))
  rw [hu, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hvalUnitB, hvalPi,
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hvalUnitA,
    IsDiscreteValuationRing.addVal_uniformizer hpi]
  simp [nsmul_eq_mul, mul_comm]

/-- Under total ramification, two nonzero polynomial terms of exponents
strictly below the ramification index have distinct valuations.  Their
valuations are congruent to their exponents modulo `e`. -/
theorem val_terms_ne
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (Pi : B) (hPi : Irreducible Pi) (e : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    {a b : A} {i j : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hi : i < e) (hj : j < e) (hij : i ≠ j) :
    IsDiscreteValuationRing.addVal B (algebraMap A B a * Pi ^ i) ≠
      IsDiscreteValuationRing.addVal B (algebraMap A B b * Pi ^ j) := by
  have hva : IsDiscreteValuationRing.addVal A a ≠ ⊤ := by
    intro hva
    exact ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp hva)
  have hvb : IsDiscreteValuationRing.addVal A b ≠ ⊤ := by
    intro hvb
    exact hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp hvb)
  obtain ⟨ka, hka⟩ := ENat.ne_top_iff_exists.mp hva
  obtain ⟨kb, hkb⟩ := ENat.ne_top_iff_exists.mp hvb
  have htermA :
      IsDiscreteValuationRing.addVal B (algebraMap A B a * Pi ^ i) =
        (e * ka + i : ℕ) := by
    rw [IsDiscreteValuationRing.addVal_mul,
      val_nsmul_maximal
        A B Pi hPi e he hmap,
      IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hPi, ← hka]
    simp [nsmul_eq_mul]
  have htermB :
      IsDiscreteValuationRing.addVal B (algebraMap A B b * Pi ^ j) =
        (e * kb + j : ℕ) := by
    rw [IsDiscreteValuationRing.addVal_mul,
      val_nsmul_maximal
        A B Pi hPi e he hmap,
      IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hPi, ← hkb]
    simp [nsmul_eq_mul]
  rw [htermA, htermB]
  norm_cast
  intro h
  have hmod := congrArg (fun n : ℕ ↦ n % e) h
  have hmodA : (e * ka + i) % e = i := by
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hi]
  have hmodB : (e * kb + j) % e = j := by
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hj]
  change (e * ka + i) % e = (e * kb + j) % e at hmod
  rw [hmodA, hmodB] at hmod
  exact hij hmod

/-- The classical derivative estimate for a totally ramified uniformizer.
For a monic polynomial `f` of degree `e`, the nonzero terms of `f'(Pi)`
have pairwise distinct valuations modulo `e`.  Hence no cancellation occurs,
and its valuation is at most the valuation of the leading derivative term. -/
theorem val_aeval_leading
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (Pi : B) (hPi : Irreducible Pi) (e : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (f : Polynomial A) (hf : f.Monic) (hdegree : f.natDegree = e) :
    IsDiscreteValuationRing.addVal B
        (Polynomial.aeval Pi (Polynomial.derivative f)) ≤
      IsDiscreteValuationRing.addVal B
        (algebraMap A B (e : A) * Pi ^ (e - 1)) := by
  classical
  let term : ℕ → B := fun i ↦
    algebraMap A B ((Polynomial.derivative f).coeff i) * Pi ^ i
  let support : Finset ℕ :=
    (Finset.range e).filter fun i ↦ (Polynomial.derivative f).coeff i ≠ 0
  have hepos : 0 < e := Nat.pos_of_ne_zero he
  have helead : e - 1 < e := by omega
  have hleadcoeff : (Polynomial.derivative f).coeff (e - 1) = (e : A) := by
    have hidx : e - 1 + 1 = e := Nat.sub_add_cancel hepos
    have hcastidx : ((e - 1 : ℕ) : A) + 1 = (e : A) := by
      exact_mod_cast hidx
    rw [Polynomial.coeff_derivative, hcastidx, hidx,
      ← hdegree, hf.coeff_natDegree, one_mul]
  have hcast : (e : A) ≠ 0 := Nat.cast_ne_zero.mpr he
  have hleadsupport : e - 1 ∈ support := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr helead, ?_⟩
    rw [hleadcoeff]
    exact hcast
  have hsupport : support.Nonempty := ⟨e - 1, hleadsupport⟩
  have hpair : (support : Set ℕ).Pairwise fun i j ↦
      IsDiscreteValuationRing.addVal B (term i) ≠
        IsDiscreteValuationRing.addVal B (term j) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    exact val_terms_ne A B Pi hPi e he hmap
      hi'.2 hj'.2 (Finset.mem_range.mp hi'.1) (Finset.mem_range.mp hj'.1) hij
  obtain ⟨j, hj, hsum, hmin⟩ :=
    val_pairwise_ne B support term hsupport hpair
  have hsumSupport :
      support.sum term = (Finset.range e).sum term := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hcoeff : (Polynomial.derivative f).coeff i = 0 := by
      by_contra hcoeff
      exact hnot (Finset.mem_filter.mpr ⟨hi, hcoeff⟩)
    simp [hcoeff]
  have haeval :
      Polynomial.aeval Pi (Polynomial.derivative f) =
        (Finset.range e).sum term := by
    have hderivlt : (Polynomial.derivative f).natDegree < e := by
      rw [← hdegree]
      exact Polynomial.natDegree_derivative_lt (hdegree.trans_ne he)
    rw [Polynomial.aeval_eq_sum_range' hderivlt Pi]
    simp only [term, Algebra.smul_def]
  calc
    IsDiscreteValuationRing.addVal B
        (Polynomial.aeval Pi (Polynomial.derivative f)) =
        IsDiscreteValuationRing.addVal B (support.sum term) := by
      rw [haeval, hsumSupport]
    _ = IsDiscreteValuationRing.addVal B (term j) := hsum
    _ ≤ IsDiscreteValuationRing.addVal B (term (e - 1)) :=
      hmin (e - 1) hleadsupport
    _ = IsDiscreteValuationRing.addVal B
        (algebraMap A B (e : A) * Pi ^ (e - 1)) := by
      change IsDiscreteValuationRing.addVal B
        (algebraMap A B ((Polynomial.derivative f).coeff (e - 1)) * Pi ^ (e - 1)) = _
      rw [hleadcoeff]

/-- Numerical form of the totally ramified derivative estimate:
`v_B(f'(Pi)) ≤ e * v_A(e) + e - 1`. -/
theorem val_aeval_derivative
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (Pi : B) (hPi : Irreducible Pi) (e : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (f : Polynomial A) (hf : f.Monic) (hdegree : f.natDegree = e) :
    IsDiscreteValuationRing.addVal B
        (Polynomial.aeval Pi (Polynomial.derivative f)) ≤
      e • IsDiscreteValuationRing.addVal A (e : A) + (e - 1 : ℕ) := by
  refine (val_aeval_leading
    A B Pi hPi e he hmap f hf hdegree).trans_eq ?_
  rw [IsDiscreteValuationRing.addVal_mul,
    val_nsmul_maximal
      A B Pi hPi e he hmap,
    IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hPi]
  simp [nsmul_eq_mul]

/-- For an integral generator of the upper ring, the conductor is the unit
ideal, so the different is generated by the derivative of its minimal
polynomial. -/
theorem different_aeval_derivative
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    (Pi : B) (hadjoin : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (hfield : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤) :
    differentIdeal A B =
      Ideal.span {Polynomial.aeval Pi
        (Polynomial.derivative (minpoly A Pi))} := by
  have hconductor : conductor A Pi = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top hadjoin
  have hformula := conductor_mul_differentIdeal A K L Pi hfield
  rw [hconductor, ← Ideal.one_eq_top, one_mul] at hformula
  exact hformula

/-- The local wild different bound for a totally ramified monogenic DVR
extension.  If `e` is the degree and `r = v_A(e)`, then
`D_{B/A}` divides the `(e * r + e - 1)`-st power of the maximal ideal of
`B`. -/
theorem different_totally_generator
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    (Pi : B) (hPi : Irreducible Pi) (e r : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (hdegree : (minpoly A Pi).natDegree = e)
    (hadjoin : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (hfield : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤)
    (hr : IsDiscreteValuationRing.addVal A (e : A) = r) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^ (e * r + (e - 1)) := by
  rw [different_aeval_derivative
      A B K L Pi hadjoin hfield,
    hPi.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd]
  calc
    IsDiscreteValuationRing.addVal B
        (Polynomial.aeval Pi (Polynomial.derivative (minpoly A Pi))) ≤
        e • IsDiscreteValuationRing.addVal A (e : A) + (e - 1 : ℕ) :=
      val_aeval_derivative A B Pi hPi e he hmap
        (minpoly A Pi) (minpoly.monic (Algebra.IsIntegral.isIntegral Pi)) hdegree
    _ = (e * r + (e - 1) : ℕ) := by rw [hr]; simp [nsmul_eq_mul]
    _ = IsDiscreteValuationRing.addVal B (Pi ^ (e * r + (e - 1))) := by
      rw [hPi.addVal_pow]

/-- The tame equality for a totally ramified monogenic extension of DVRs.  If the
ramification degree `e` is a unit in the base DVR, the lower bound
`maximalIdeal B ^ (e - 1) ∣ differentIdeal A B` and the derivative upper bound coincide. -/
theorem different_maximal_totally
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    (Pi : B) (hPi : Irreducible Pi) (e : ℕ) (he : e ≠ 0)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (hdegree : (minpoly A Pi).natDegree = e)
    (hadjoin : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (hfield : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤)
    (heunit : IsUnit (e : A)) :
    differentIdeal A B = (IsLocalRing.maximalIdeal B) ^ (e - 1) := by
  have hupper : differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^ (e - 1) := by
    have hval : IsDiscreteValuationRing.addVal A (e : A) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr heunit
    simpa using
      (different_totally_generator
        A B K L Pi hPi e 0 he hmap hdegree hadjoin hfield hval)
  have hp : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field A
  have hlower : (IsLocalRing.maximalIdeal B) ^ (e - 1) ∣
      differentIdeal A B := by
    rw [hPi.maximalIdeal_eq]
    exact pow_sub_one_dvd_differentIdeal A (Ideal.span ({Pi} : Set B)) e hp
      (Ideal.dvd_iff_le.mpr hmap.le)
  exact le_antisymm (Ideal.dvd_iff_le.mp hlower) (Ideal.dvd_iff_le.mp hupper)

/-- Degree-uniform form of the totally ramified local different bound.  For
`e ≤ N`, the valuation of `e` is bounded by the valuation of `N!`, so an
exponent depending only on `A` and `N` suffices. -/
theorem different_uniform_totally
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    (Pi : B) (hPi : Irreducible Pi) (e N : ℕ) (he : e ≠ 0)
    (heN : e ≤ N)
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (hdegree : (minpoly A Pi).natDegree = e)
    (hadjoin : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (hfield : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^
        (N * (dvrCastValuation A N.factorial + 1)) := by
  let r := dvrCastValuation A e
  let c := dvrCastValuation A N.factorial
  have hr : IsDiscreteValuationRing.addVal A (e : A) = r :=
    val_dvr_valuation A e he
  have hc : IsDiscreteValuationRing.addVal A (N.factorial : A) = c :=
    val_dvr_valuation A N.factorial
      (Nat.factorial_ne_zero N)
  have hdvdNat : e ∣ N.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero he) heN
  have hdvdA : (e : A) ∣ (N.factorial : A) := by
    rcases hdvdNat with ⟨k, hk⟩
    refine ⟨(k : A), ?_⟩
    exact_mod_cast hk
  have hvaluation :
      IsDiscreteValuationRing.addVal A (e : A) ≤
        IsDiscreteValuationRing.addVal A (N.factorial : A) :=
    IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hdvdA
  have hrc : r ≤ c := by
    rw [hr, hc] at hvaluation
    exact_mod_cast hvaluation
  have hexponent : e * r + (e - 1) ≤ N * (c + 1) := by
    calc
      e * r + (e - 1) ≤ e * c + e :=
        Nat.add_le_add (Nat.mul_le_mul_left e hrc) (Nat.sub_le e 1)
      _ = e * (c + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ N * (c + 1) := Nat.mul_le_mul_right (c + 1) heN
  exact dvd_trans
    (different_totally_generator
      A B K L Pi hPi e r he hmap hdegree hadjoin hfield hr)
    (pow_dvd_pow (IsLocalRing.maximalIdeal B) hexponent)

/-- The intrinsic tame different formula for a totally ramified extension of DVRs.
No uniformizer or monogenicity hypothesis is exported: an upstairs uniformizer is
automa an Eisenstein generator. -/
theorem different_maximal_ramified
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [PerfectField (FractionRing A)]
    [IsIntegralClosure B A L]
    (htr : TotallyRamified A B (IsLocalRing.maximalIdeal A))
    (htame : IsUnit ((Module.finrank A B : ℕ) : A)) :
    differentIdeal A B =
      (IsLocalRing.maximalIdeal B) ^ (Module.finrank A B - 1) := by
  obtain ⟨Pi, hPi⟩ := IsDiscreteValuationRing.exists_irreducible B
  have heis : (minpoly A Pi).IsEisensteinAt
      (IsLocalRing.maximalIdeal A) :=
    minpoly_eisenstein_ramified A B K L htr Pi hPi
  have hfixed :=
    eisenstein_ramified_weakly
      A B K L htr Pi hPi heis.isWeaklyEisensteinAt
  have hfield :=
    fraction_weakly_eisenstein
      A B K L htr Pi hPi heis.isWeaklyEisensteinAt
  have hfieldAlg : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (algebraMap B L Pi)),
      hfield]
    rfl
  have hdegree : (minpoly A Pi).natDegree = Module.finrank A B := by
    apply minpoly_weakly_uniformizer
      A B K L Pi hPi
    · rcases htr with ⟨P, hPprime, hPover, hmap, _hram, _hunique⟩
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field A) P
      have hPmax : P = IsLocalRing.maximalIdeal B :=
        IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
      simpa [hPmax] using hmap
    · exact heis.isWeaklyEisensteinAt
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ Module.finrank A B := by
    rcases htr with ⟨P, hPprime, hPover, hmap, _hram, _hunique⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field A) P
    have hPmax : P = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
    simpa [hPmax, hPi.maximalIdeal_eq] using hmap
  exact
    different_maximal_totally
      A B K L Pi hPi (Module.finrank A B) Module.finrank_pos.ne'
        hmap hdegree hfixed.2.1 hfieldAlg htame

/-- Intrinsic form of the degree-uniform local different bound.  A totally
ramified finite extension of DVRs has an upstairs uniformizer that generates
the integral extension and its fraction field, so the generator hypotheses
of the preceding theorem follow from total ramification itself. -/
theorem different_uniform_ramified
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [PerfectField (FractionRing A)]
    [IsIntegralClosure B A L]
    (htr : TotallyRamified A B (IsLocalRing.maximalIdeal A))
    (N : ℕ) (hN : Module.finrank A B ≤ N) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^
        (N * (dvrCastValuation A N.factorial + 1)) := by
  obtain ⟨Pi, hPi⟩ := IsDiscreteValuationRing.exists_irreducible B
  have heis : (minpoly A Pi).IsEisensteinAt
      (IsLocalRing.maximalIdeal A) :=
    minpoly_eisenstein_ramified A B K L htr Pi hPi
  have hfixed :=
    eisenstein_ramified_weakly
      A B K L htr Pi hPi heis.isWeaklyEisensteinAt
  have hfield :=
    fraction_weakly_eisenstein
      A B K L htr Pi hPi heis.isWeaklyEisensteinAt
  have hfieldAlg : Algebra.adjoin K ({algebraMap B L Pi} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (algebraMap B L Pi)),
      hfield]
    rfl
  have hdegree : (minpoly A Pi).natDegree = Module.finrank A B := by
    apply minpoly_weakly_uniformizer
      A B K L Pi hPi
    · rcases htr with ⟨P, hPprime, hPover, hmap, _hram, _hunique⟩
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field A) P
      have hPmax : P = IsLocalRing.maximalIdeal B :=
        IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
      simpa [hPmax] using hmap
    · exact heis.isWeaklyEisensteinAt
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ Module.finrank A B := by
    rcases htr with ⟨P, hPprime, hPover, hmap, _hram, _hunique⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field A) P
    have hPmax : P = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
    simpa [hPmax, hPi.maximalIdeal_eq] using hmap
  exact
    different_uniform_totally
      A B K L Pi hPi (Module.finrank A B) N Module.finrank_pos.ne'
        hN hmap hdegree hfixed.2.1 hfieldAlg

end Submission.NumberTheory.Milne
