import Towers.FieldTheory.TameThreeKoch.CyclotomicCubicSubfields
import Towers.FieldTheory.RationalRamificationCleanup
import Towers.NumberTheory.Galois.TrivialExtensionInertia

open scoped Pointwise Topology

noncomputable section

namespace Towers
namespace TBluepr

local instance cyclotomicCleanupFiniteDimensional
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ D :=
  D.finiteDimensional

local instance cyclotomicCleanupIsGalois
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ D :=
  D.isGalois

/-- If a rational prime distinct from `3` has nontrivial inertia in a finite
Galois `3`-extension of `ℚ`, then it is congruent to `1` modulo `3`.

This is the numerical input needed to use the cubic subfield of the
`q`-th cyclotomic field as the ramification-cleanup character at `q`. -/
theorem rational_inertia_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hG : IsPGroup 3 Gal(L/ℚ))
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hIne : P.inertia Gal(L/ℚ) ≠ ⊥) :
    q ≡ 1 [MOD 3] := by
  classical
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  let I : Subgroup Gal(L/ℚ) := P.inertia Gal(L/ℚ)
  letI : Finite Gal(L/ℚ) :=
    IsGaloisGroup.finite Gal(L/ℚ) ℚ L
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hcardG⟩ := IsPGroup.iff_card.mp hG
  have hqcardG : Nat.Coprime q (Nat.card Gal(L/ℚ)) := by
    have hcop : Nat.Coprime (q ^ 1) (3 ^ n) :=
      Nat.coprime_pow_primes 1 n hq Nat.prime_three hqne
    rw [hcardG]
    simpa using hcop
  have hcardIdvdG : Nat.card I ∣ Nat.card Gal(L/ℚ) :=
    Subgroup.card_subgroup_dvd_card I
  have hqcardI : Nat.Coprime q (Nat.card I) :=
    hqcardG.coprime_dvd_right hcardIdvdG
  obtain ⟨chi, hchi⟩ :=
    tame_units_embedding
      (L := L) hq P hqcardI
  have hIp : IsPGroup 3 I := hG.to_subgroup I
  obtain ⟨m, hcardI⟩ := IsPGroup.iff_card.mp hIp
  have hm : m ≠ 0 := by
    intro hm0
    have hcardOne : Nat.card I = 1 := by simpa [hm0] using hcardI
    have honeLt : 1 < Nat.card I :=
      (Subgroup.one_lt_card_iff_ne_bot I).2 hIne
    omega
  have hthreeI : 3 ∣ Nat.card I := by
    rw [hcardI]
    exact dvd_pow_self 3 hm
  have hthreeUnits :
      3 ∣ Nat.card (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    hthreeI.trans (Subgroup.card_dvd_of_injective chi hchi)
  have hp_ne_bot : p ≠ ⊥ := by
    simpa [p] using rational_ne_bot hq
  letI : p.IsPrime := by
    simpa [p] using rational_prime_ideal hq
  letI : p.IsMaximal := by
    simpa [p] using rational_ideal_maximal hq
  letI : P.LiesOver p := by
    simpa [p] using
      (inferInstance : P.LiesOver (Ideal.rationalPrimeIdeal q))
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (ℤ ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp_ne_bot
  letI : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) := inferInstance
  letI : Module.Finite (ℤ ⧸ p)
      (NumberField.RingOfIntegers L ⧸ P) :=
    Module.Finite.of_finite
  letI : Algebra.IsSeparable (ℤ ⧸ p)
      (NumberField.RingOfIntegers L ⧸ P) := inferInstance
  letI : IsGaloisGroup Gal(L/ℚ) ℤ
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ) ℤ
      (NumberField.RingOfIntegers L) ℚ L
  have hthreeNorm : 3 ∣ Ideal.absNorm P - 1 := by
    simpa [Nat.card_units, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using hthreeUnits
  have hnorm : Ideal.absNorm P = q ^ p.inertiaDeg P := by
    letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
      simpa [p, Ideal.rationalPrimeIdeal] using
        (inferInstance : P.LiesOver p)
    exact Ideal.absNorm_eq_pow_inertiaDeg' P hq
  have hthreePow : 3 ∣ q ^ p.inertiaDeg P - 1 := by
    rwa [hnorm] at hthreeNorm
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) hp_ne_bot (NumberField.RingOfIntegers L) Gal(L/ℚ)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg
      (p := p) (P := P) (B := NumberField.RingOfIntegers L)
      (G := Gal(L/ℚ))] at hfund
  have hfdvd : p.inertiaDeg P ∣ Nat.card Gal(L/ℚ) := by
    refine ⟨(p.primesOver (NumberField.RingOfIntegers L)).ncard *
      p.ramificationIdxIn (NumberField.RingOfIntegers L), ?_⟩
    calc
      Nat.card Gal(L/ℚ) =
          (p.primesOver (NumberField.RingOfIntegers L)).ncard *
            (p.ramificationIdxIn (NumberField.RingOfIntegers L) *
              p.inertiaDeg P) := hfund.symm
      _ = p.inertiaDeg P *
          ((p.primesOver (NumberField.RingOfIntegers L)).ncard *
            p.ramificationIdxIn (NumberField.RingOfIntegers L)) := by
        ac_rfl
  rw [hcardG] at hfdvd
  obtain ⟨k, _hk, hfk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hfdvd
  have hfodd : Odd (p.inertiaDeg P) := by
    rw [hfk]
    exact (show Odd 3 by norm_num).pow
  have hpowZ : (q : ZMod 3) ^ p.inertiaDeg P = 1 := by
    have honele : 1 ≤ q ^ p.inertiaDeg P :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq.ne_zero)
    have hmod : 1 ≡ q ^ p.inertiaDeg P [MOD 3] :=
      (Nat.modEq_iff_dvd' honele).2 hthreePow
    have hcast :=
      (ZMod.natCast_eq_natCast_iff 1 (q ^ p.inertiaDeg P) 3).2 hmod
    simpa using hcast.symm
  have hqZ : (q : ZMod 3) = 1 := by
    let z : ZMod 3 := q
    have hz0 : z ≠ 0 := by
      intro hz
      have hthreeq : 3 ∣ q :=
        (ZMod.natCast_eq_zero_iff q 3).1 hz
      rcases (Nat.dvd_prime hq).1 hthreeq with hthreeone | hthreeq
      · norm_num at hthreeone
      · exact hqne hthreeq.symm
    have hzpow : z ^ p.inertiaDeg P = 1 := hpowZ
    have hzsq : z ^ 2 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one hz0
    obtain ⟨k, hk⟩ := hfodd
    calc
      z = z ^ (2 * k + 1) := by rw [pow_add, pow_mul, hzsq]; simp
      _ = z ^ p.inertiaDeg P := by rw [hk]
      _ = 1 := hzpow
  exact (ZMod.natCast_eq_natCast_iff q 1 3).1 hqZ

set_option maxHeartbeats 2000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The tame-pair construction unfolds finite restriction and inertia instances.
/-- The finite tame-pair cancellation character, inflated to the absolute
Galois group.  This packages the form used by the global cleanup: whenever
an absolute automorphism restricts to the selected upper inertia subgroup,
the inflated cubic character cancels the finite lift there. -/
theorem absolute_character_cancels
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ D)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers D))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A G : Type*} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [Group G]
    (liftFinite : Gal(D/ℚ) →* A)
    (otherFinite : Gal(D/ℚ) →* G)
    (hother : ∀ sigma : P.inertia Gal(D/ℚ),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair :
      letI : Algebra ℚ C := C.algebra'
      Function.Injective
        (((otherFinite.comp (P.inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction C hCgal.to_normal q P)))) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        ∀ sigma : Gal(AlgebraicClosure ℚ/ℚ),
          AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
              P.inertia Gal(D/ℚ) →
            chi sigma *
              liftFinite
                (AlgEquiv.restrictNormalHom D.toIntermediateField sigma) = 1 := by
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let liftI : P.inertia Gal(D/ℚ) →* A :=
    liftFinite.comp (P.inertia Gal(D/ℚ)).subtype
  let otherI : P.inertia Gal(D/ℚ) →* G :=
    otherFinite.comp (P.inertia Gal(D/ℚ)).subtype
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_pair
      C hCfin hCgal hq hqne P hram hcard liftI otherI
        (by simpa [otherI] using hother) (by simpa [otherI] using hpair)
  let chi : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    absoluteThroughIntermediate D C hCgal.to_normal chiC
  refine ⟨chi,
    absolute_through_continuous
      D C hCgal.to_normal chiC, ?_⟩
  intro sigma hsigma
  let tau : P.inertia Gal(D/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma, hsigma⟩
  change chiC (finiteIntermediateRestriction D C hCgal.to_normal tau.1) *
      liftFinite tau.1 = 1
  exact hcancel tau

set_option maxHeartbeats 2000000 in
-- The inertia-hom variant repeats the finite restriction instance search.
/-- A version of `absolute_character_cancels`
whose character to be cancelled is only defined on the chosen inertia
subgroup.  This is the form needed for a lift of an unramified base map: the
lift is kernel-valued on inertia outside the prescribed ramification set,
but need not be kernel-valued on the whole finite Galois group. -/
theorem absolute_cancels_pair
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ D)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers D))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A G : Type*} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [Group G]
    (liftI : P.inertia Gal(D/ℚ) →* A)
    (otherFinite : Gal(D/ℚ) →* G)
    (hother : ∀ sigma : P.inertia Gal(D/ℚ),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair :
      letI : Algebra ℚ C := C.algebra'
      Function.Injective
        (((otherFinite.comp (P.inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction C hCgal.to_normal q P)))) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma : AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
              P.inertia Gal(D/ℚ)),
            chi sigma * liftI
              ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
                hsigma⟩ = 1 := by
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let otherI : P.inertia Gal(D/ℚ) →* G :=
    otherFinite.comp (P.inertia Gal(D/ℚ)).subtype
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_pair
      C hCfin hCgal hq hqne P hram hcard liftI otherI
        (by
          intro sigma
          exact hother sigma)
        (by
          change Function.Injective
            (((otherFinite.comp (P.inertia Gal(D/ℚ)).subtype).prod
              (numberInertiaRestriction C hCgal.to_normal q P)))
          exact hpair)
  let chi : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    absoluteThroughIntermediate D C hCgal.to_normal chiC
  refine ⟨chi,
    absolute_through_continuous
      D C hCgal.to_normal chiC, ?_⟩
  intro sigma hsigma
  let tau : P.inertia Gal(D/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma, hsigma⟩
  change chiC (finiteIntermediateRestriction D C hCgal.to_normal tau.1) *
      liftI tau = 1
  exact hcancel tau

/-- If a normal subgroup contains every upper inertia group outside `S`, its
fixed field is unramified outside `S`.  This is the finite-level descent used
after multiplying the explicit cubic correction characters. -/
theorem fixed_outside_inertia
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset ℕ) (H : Subgroup Gal(K/ℚ)) [H.Normal]
    (hinertia :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers K)),
          P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
            P.inertia Gal(K/ℚ) ≤ H) :
    let E := IntermediateField.fixedField H
    letI : Algebra ℚ E := E.algebra'
    letI : FiniteDimensional ℚ E := inferInstance
    letI : NumberField E := NumberField.of_module_finite ℚ E
    UnramifiedOutside E S := by
  let E : IntermediateField ℚ K := IntermediateField.fixedField H
  letI : Algebra ℚ E := E.algebra'
  letI : FiniteDimensional ℚ E := inferInstance
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois ℚ E := IsGalois.of_fixedField_normal_subgroup H
  rw [UnramifiedOutside, RamifiedOnlyAt]
  intro q hq hqS Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := hQ.2
  have hQ0 : Q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) Q
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q
      (S := NumberField.RingOfIntegers K)
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver Q := hPlies
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ0 P
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : Q.LiesOver p := by simpa [p] using hQ.2
  letI : P.LiesOver p := Ideal.LiesOver.trans P Q p
  have hp0 : p ≠ ⊥ := by simpa [p] using rational_ne_bot hq
  letI : p.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (ℤ ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp0
  letI : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  letI : Finite (NumberField.RingOfIntegers K ⧸ P) := inferInstance
  letI : Module.Finite (ℤ ⧸ p)
      (NumberField.RingOfIntegers K ⧸ P) := Module.Finite.of_finite
  letI : Algebra.IsSeparable (ℤ ⧸ p)
      (NumberField.RingOfIntegers K ⧸ P) := inferInstance
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing
      Gal(K/ℚ) ℤ (NumberField.RingOfIntegers K) ℚ K
  letI : IsGaloisGroup E.fixingSubgroup E K :=
    IsGaloisGroup.intermediateField Gal(K/ℚ) ℚ K E
  letI := IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers E) E K (NumberField.RingOfIntegers K)
  letI : IsGaloisGroup E.fixingSubgroup
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing E.fixingSubgroup
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) E K
  letI : Field (NumberField.RingOfIntegers E ⧸ Q) :=
    Ideal.Quotient.field Q
  letI : IsGalois (NumberField.RingOfIntegers E ⧸ Q)
      (NumberField.RingOfIntegers K ⧸ P) :=
    { __ := Ideal.Quotient.normal
        (A := NumberField.RingOfIntegers E)
        (G := E.fixingSubgroup) Q P }
  letI : Algebra.IsSeparable (NumberField.RingOfIntegers E ⧸ Q)
      (NumberField.RingOfIntegers K ⧸ P) := inferInstance
  have hIleH : P.inertia Gal(K/ℚ) ≤ H :=
    hinertia q hq hqS P inferInstance inferInstance
  have hIleFix : P.inertia Gal(K/ℚ) ≤ E.fixingSubgroup := by
    change P.inertia Gal(K/ℚ) ≤
      (IntermediateField.fixedField H).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField H]
    exact hIleH
  let inertiaEquiv : P.inertia Gal(K/ℚ) ≃
      P.inertia E.fixingSubgroup :=
    { toFun := fun sigma ↦ ⟨⟨sigma.1, hIleFix sigma.2⟩, sigma.2⟩
      invFun := fun sigma ↦ ⟨sigma.1.1, sigma.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcard : Nat.card (P.inertia Gal(K/ℚ)) =
      Nat.card (P.inertia E.fixingSubgroup) :=
    Nat.card_congr inertiaEquiv
  have habsolute : Nat.card (P.inertia Gal(K/ℚ)) =
      p.ramificationIdx P := by
    calc
      Nat.card (P.inertia Gal(K/ℚ)) =
          p.ramificationIdxIn (NumberField.RingOfIntegers K) :=
        Ideal.card_inertia_eq_ramificationIdxIn p hp0 P
      _ = p.ramificationIdx P :=
        Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(K/ℚ)
  have hrelative : Nat.card (P.inertia E.fixingSubgroup) =
      Q.ramificationIdx P := by
    calc
      Nat.card (P.inertia E.fixingSubgroup) =
          Q.ramificationIdxIn (NumberField.RingOfIntegers K) :=
        Ideal.card_inertia_eq_ramificationIdxIn Q hQ0 P
      _ = Q.ramificationIdx P :=
        Ideal.ramificationIdxIn_eq_ramificationIdx Q P E.fixingSubgroup
  have hequal : p.ramificationIdx P = Q.ramificationIdx P := by
    rw [← habsolute, hcard, hrelative]
  have htower := Ideal.ramificationIdx_algebra_tower' p Q P
  rw [hequal] at htower
  have hrelative0 : Q.ramificationIdx P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hQ0
  have hcancel : 1 * Q.ramificationIdx P =
      p.ramificationIdx Q * Q.ramificationIdx P := by
    simpa using htower
  exact (Nat.mul_right_cancel (Nat.pos_of_ne_zero hrelative0) hcancel).symm

end TBluepr
end Towers
