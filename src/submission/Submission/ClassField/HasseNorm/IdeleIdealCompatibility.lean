import Submission.ClassField.ArtinReciprocity.NormLimitation
import Submission.ClassField.CyclicIdeles.FiniteGalois
import Submission.ClassField.HasseNorm.WeakApproximation
import Submission.ClassField.HasseNorm.ModulusContainedSubgroup

/-!
# Compatibility of idèle and ideal norms

The ideal norm used in the global second inequality is presented by its
effect on prime generators.  This file first packages that presentation as
an honest homomorphism on nonzero fractional ideals.  The remaining local
calculation is then exactly the assertion that the idèle norm has the same
prime-exponent map.
-/

namespace Submission.CField.HNorm

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.Ideles
open Submission.CField.CIdeles
open scoped nonZeroDivisors WithZero

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

private abbrev finiteExtension : NFExt K where
  carrier := L

/-- The contraction of an upper finite prime. -/
def lowerPrime
    (Q : HeightOneSpectrum (OK L)) : HeightOneSpectrum (OK K) :=
  Q.under (OK K)

private abbrev PrimesAbove
    (P : HeightOneSpectrum (OK K)) :=
  {Q : HeightOneSpectrum (OK L) // lowerPrime (K := K) Q = P}

private noncomputable def upperPrimeAbove
    (P : HeightOneSpectrum (OK K)) :
    UpperPrimeFactors (K := K) (L := L) P → PrimesAbove (K := K) (L := L) P :=
  fun Q ↦ ⟨upperPrime (K := K) (L := L) P Q,
    upperPrime_under (K := K) (L := L) P Q⟩

omit [FiniteDimensional K L] in
private theorem factor_above_injective
    (P : HeightOneSpectrum (OK K)) :
    Function.Injective
      (upperPrimeAbove (K := K) (L := L) P) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  have h' := congrArg
    (fun Q : PrimesAbove (K := K) (L := L) P ↦ Q.1.asIdeal) h
  exact h'

omit [FiniteDimensional K L] in
private theorem upper_factor_above
    (P : HeightOneSpectrum (OK K)) :
    Function.Surjective
      (upperPrimeAbove (K := K) (L := L) P) := by
  intro Q
  let I : Ideal (OK L) :=
    P.asIdeal.map (algebraMap (OK K) (OK L))
  have hI : I ≠ 0 := Ideal.map_ne_bot_of_ne_bot P.ne_bot
  have hQtop : Q.1.asIdeal ≠ ⊤ := Q.1.isPrime.ne_top
  letI : P.asIdeal.IsMaximal := P.isMaximal
  have hlies : Q.1.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal Q.2).symm
  have hdiv : Q.1.asIdeal ∣ I :=
    (Ideal.liesOver_iff_dvd_map hQtop).mp hlies
  have hirr : Irreducible Q.1.asIdeal :=
    (Ideal.prime_of_isPrime Q.1.ne_bot Q.1.isPrime).irreducible
  obtain ⟨q, hqmem, hQq⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI hirr hdiv
  let q' : UpperPrimeFactors (K := K) (L := L) P :=
    ⟨q, Multiset.mem_toFinset.mpr hqmem⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  exact associated_iff_eq.mp hQq.symm

private noncomputable def upperFactorsAbove
    (P : HeightOneSpectrum (OK K)) :
    UpperPrimeFactors (K := K) (L := L) P ≃ PrimesAbove (K := K) (L := L) P :=
  Equiv.ofBijective
    (upperPrimeAbove (K := K) (L := L) P)
    ⟨factor_above_injective (K := K) (L := L) P,
      upper_factor_above (K := K) (L := L) P⟩

private noncomputable def upperPrimeFactor
    (Q : HeightOneSpectrum (OK L)) :
    UpperPrimeFactors (K := K) (L := L) (lowerPrime (K := K) Q) :=
  (upperFactorsAbove
    (K := K) (L := L) (lowerPrime (K := K) Q)).symm ⟨Q, rfl⟩

omit [FiniteDimensional K L] in
@[simp]
private theorem upper_prime_factor
    (Q : HeightOneSpectrum (OK L)) :
    upperPrime (K := K) (L := L) (lowerPrime (K := K) Q)
      (upperPrimeFactor (K := K) (L := L) Q) = Q := by
  have h := (upperFactorsAbove
    (K := K) (L := L) (lowerPrime (K := K) Q)).apply_symm_apply ⟨Q, rfl⟩
  exact congrArg Subtype.val h

/-- The residue degree attached to an upper prime, regarded as an integer
coefficient in a prime-exponent vector. -/
def primeNormWeight
    (Q : HeightOneSpectrum (OK L)) : ℤ :=
  ((lowerPrime (K := K) Q).asIdeal.inertiaDeg Q.asIdeal : ℤ)

/-- Push a finite upper-prime exponent vector to the lower field, weighting
an upper prime by its residue degree. -/
noncomputable def idealExponentHom :
    (HeightOneSpectrum (OK L) →₀ ℤ) →+
      (HeightOneSpectrum (OK K) →₀ ℤ) :=
  Finsupp.liftAddHom fun Q ↦
    (Finsupp.singleAddHom (lowerPrime (K := K) Q)).comp
      (AddMonoidHom.mulLeft (primeNormWeight (K := K) Q))

omit [FiniteDimensional K L] in
@[simp]
theorem ideal_exponent_single
    (Q : HeightOneSpectrum (OK L)) (n : ℤ) :
    idealExponentHom (K := K) (L := L) (Finsupp.single Q n) =
      Finsupp.single (lowerPrime (K := K) Q)
        (primeNormWeight (K := K) Q * n) := by
  simp [idealExponentHom]

omit [FiniteDimensional K L] in
open Classical in
theorem ideal_exponent_hom
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (P : HeightOneSpectrum (OK K)) :
    idealExponentHom (K := K) (L := L) e P =
      e.sum fun Q n ↦
        if lowerPrime (K := K) Q = P then
          primeNormWeight (K := K) Q * n
        else 0 := by
  classical
  rw [idealExponentHom, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro Q hQ
  by_cases hQP : lowerPrime (K := K) Q = P
  · simp [hQP]
  · simp [hQP]

omit [FiniteDimensional K L] in
theorem ideal_exponent_fiber
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (P : HeightOneSpectrum (OK K))
    (hzero : ∀ Q, lowerPrime (K := K) Q = P → e Q = 0) :
    idealExponentHom (K := K) (L := L) e P = 0 := by
  rw [ideal_exponent_hom]
  classical
  change ∑ Q ∈ e.support,
      (if lowerPrime (K := K) Q = P then
        primeNormWeight (K := K) Q * e Q else 0) = 0
  apply Finset.sum_eq_zero
  intro Q hQ
  by_cases hQP : lowerPrime (K := K) Q = P
  · simp [hQP, hzero Q hQP]
  · simp [hQP]

private theorem fractional_factorization_single
    {F : Type u} [Field F] [NumberField F]
    (Q : HeightOneSpectrum (OK F)) (n : ℤ) :
    fractionalIdealFactorization (OK F) F
        (Multiplicative.ofAdd (Finsupp.single Q n)) =
      ANExt.primeFractionalIdeal Q ^ n := by
  apply Units.ext
  simpa [ANExt.primeFractionalIdeal] using
    fractional_ideal_single (OK F) F Q n

private def integralIdealUnit
    {F : Type u} [Field F] [NumberField F]
    (I : Ideal (OK F)) (hI : I ≠ ⊥) :
    (FractionalIdeal (OK F)⁰ F)ˣ :=
  FractionalIdeal.mk0 F
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩

@[simp]
private theorem integral_unit_top
    {F : Type u} [Field F] [NumberField F] :
    integralIdealUnit (F := F) ⊤ (by simp) = 1 := by
  apply Units.ext
  rfl

private theorem integral_unit_mul
    {F : Type u} [Field F] [NumberField F]
    (I J : Ideal (OK F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    integralIdealUnit (F := F) (I * J) (mul_ne_zero hI hJ) =
      integralIdealUnit (F := F) I hI * integralIdealUnit (F := F) J hJ := by
  apply Units.ext
  simp only [integralIdealUnit, Units.val_mul, FractionalIdeal.coe_mk0]
  exact FractionalIdeal.coeIdeal_mul I J

/-- The prime-generator presentation of the norm, as a homomorphism on
nonzero fractional ideals. -/
noncomputable def fractionalIdealHom :
    (FractionalIdeal (OK L)⁰ L)ˣ →* (FractionalIdeal (OK K)⁰ K)ˣ :=
  (fractionalIdealFactorization (OK K) K).toMonoidHom.comp <|
    (idealExponentHom (K := K) (L := L)).toMultiplicative.comp <|
      (fractionalIdealFactorization (OK L) L).symm.toMonoidHom

omit [FiniteDimensional K L] in
/-- The norm homomorphism has the defining value `p ^ f(Q/p)` on an upper
prime. -/
theorem fractional_hom_prime
    (Q : HeightOneSpectrum (OK L)) :
    fractionalIdealHom (K := K) (L := L)
        (ANExt.primeFractionalIdeal Q) =
      ANExt.primeFractionalIdeal
        (lowerPrime (K := K) Q) ^
        (lowerPrime (K := K) Q).asIdeal.inertiaDeg Q.asIdeal := by
  have hQ :
      ANExt.primeFractionalIdeal Q =
        fractionalIdealFactorization (OK L) L
          (Multiplicative.ofAdd (Finsupp.single Q 1)) := by
    simpa using
      (fractional_factorization_single Q (1 : ℤ)).symm
  rw [hQ]
  unfold fractionalIdealHom
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  change fractionalIdealFactorization (OK K) K
      ((idealExponentHom (K := K) (L := L)).toMultiplicative
        (Multiplicative.ofAdd (Finsupp.single Q 1))) = _
  apply Units.ext
  change
    (fractionalIdealFactorization (OK K) K
      (Multiplicative.ofAdd
        (idealExponentHom (K := K) (L := L)
          (Finsupp.single Q 1))) : FractionalIdeal (OK K)⁰ K) = _
  rw [ideal_exponent_single]
  simp only [mul_one]
  rw [fractional_ideal_single]
  simp [ANExt.primeFractionalIdeal,
    primeNormWeight]

omit [FiniteDimensional K L] in
private theorem fractional_ideal_integral
    (I : Ideal (OK L)) (hI : I ≠ ⊥) :
    fractionalIdealHom (K := K) (L := L)
        (integralIdealUnit (F := L) I hI) =
      integralIdealUnit (F := K) (Ideal.relNorm (OK K) I)
        ((Ideal.relNorm_eq_bot_iff).not.mpr hI) := by
  classical
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro hI
      exact (hI rfl).elim
  | h₂ I hunit =>
      intro hI
      have htop : I = ⊤ := Ideal.isUnit_iff.mp hunit
      subst I
      simp
  | h₃ I Q hI0 hQ ih =>
      intro hQI
      let q : HeightOneSpectrum (OK L) := HeightOneSpectrum.ofPrime hQ
      have hQ0 : Q ≠ ⊥ := hQ.ne_zero
      have hrelQ : Ideal.relNorm (OK K) Q ≠ ⊥ :=
        (Ideal.relNorm_eq_bot_iff).not.mpr hQ0
      have hrelI : Ideal.relNorm (OK K) I ≠ ⊥ :=
        (Ideal.relNorm_eq_bot_iff).not.mpr hI0
      have hqIdeal : q.asIdeal = Q := rfl
      have hprime := fractional_hom_prime (K := K) (L := L) q
      have hlies : q.asIdeal.LiesOver
          (lowerPrime (K := K) q).asIdeal := ⟨rfl⟩
      letI : q.asIdeal.LiesOver (lowerPrime (K := K) q).asIdeal := hlies
      have hrel : Ideal.relNorm (OK K) q.asIdeal =
          (lowerPrime (K := K) q).asIdeal ^
            (lowerPrime (K := K) q).asIdeal.inertiaDeg q.asIdeal :=
        rel_contraction_deg
          (OK K) (OK L) q.asIdeal (lowerPrime (K := K) q).asIdeal
      have hrel' : Ideal.relNorm (OK K) Q =
          (lowerPrime (K := K) q).asIdeal ^
            (lowerPrime (K := K) q).asIdeal.inertiaDeg q.asIdeal := by
        simpa only [hqIdeal] using hrel
      have hprimeUnit : fractionalIdealHom (K := K) (L := L)
          (integralIdealUnit (F := L) Q hQ0) =
        integralIdealUnit (F := K) (Ideal.relNorm (OK K) Q) hrelQ := by
        apply Units.ext
        simp only [integralIdealUnit, FractionalIdeal.coe_mk0]
        rw [hrel']
        simpa [ANExt.primeFractionalIdeal,
          FractionalIdeal.coeIdeal_pow,
          hqIdeal] using congrArg Units.val hprime
      rw [integral_unit_mul Q I hQ0 hI0, map_mul,
        hprimeUnit, ih hI0]
      calc
        integralIdealUnit (F := K) (Ideal.relNorm (OK K) Q) hrelQ *
            integralIdealUnit (F := K) (Ideal.relNorm (OK K) I) hrelI =
          integralIdealUnit (F := K)
            (Ideal.relNorm (OK K) Q * Ideal.relNorm (OK K) I)
            (mul_ne_zero hrelQ hrelI) :=
          (integral_unit_mul _ _ hrelQ hrelI).symm
        _ = integralIdealUnit (F := K)
            (Ideal.relNorm (OK K) (Q * I))
            ((Ideal.relNorm_eq_bot_iff).not.mpr hQI) := by
          apply Units.ext
          simp only [integralIdealUnit, FractionalIdeal.coe_mk0]
          rw [map_mul]

/-- Compatibility with principal fractional ideals, proved from the
integral principal-ideal norm formula after clearing a denominator. -/
theorem fractional_ideal_principal (x : Lˣ) :
    fractionalIdealHom (K := K) (L := L)
        (toPrincipalIdeal (OK L) L x) =
      toPrincipalIdeal (OK K) K (Units.map (Algebra.norm K) x) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (OK L)⁰ (x : L)
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, IsLocalization.mk'_zero] at hnd
    exact x.ne_zero hnd.symm
  have hd : (d : OK L) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  let I : Ideal (OK L) := Ideal.span {n}
  let J : Ideal (OK L) := Ideal.span {(d : OK L)}
  have hI : I ≠ ⊥ := by
    simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hn
  have hJ : J ≠ ⊥ := by
    simpa only [J, ne_eq, Ideal.span_singleton_eq_bot] using hd
  have hxIdeal :
      toPrincipalIdeal (OK L) L x =
        integralIdealUnit (F := L) I hI /
          integralIdealUnit (F := L) J hJ := by
    apply Units.ext
    simp only [coe_toPrincipalIdeal, div_eq_mul_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
    change FractionalIdeal.spanSingleton (OK L)⁰ (x : L) =
      (I : FractionalIdeal (OK L)⁰ L) *
        (J : FractionalIdeal (OK L)⁰ L)⁻¹
    rw [← hnd, IsFractionRing.mk'_eq_div,
      ← FractionalIdeal.spanSingleton_div_spanSingleton,
      div_eq_mul_inv,
      ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_span_singleton]
  rw [hxIdeal, map_div,
    fractional_ideal_integral (K := K) (L := L) I hI,
    fractional_ideal_integral (K := K) (L := L) J hJ]
  apply Units.ext
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    coe_toPrincipalIdeal, Units.coe_map]
  change
    (Ideal.relNorm (OK K) I : FractionalIdeal (OK K)⁰ K) *
        (Ideal.relNorm (OK K) J : FractionalIdeal (OK K)⁰ K)⁻¹ =
      FractionalIdeal.spanSingleton (OK K)⁰
        (Algebra.norm K (x : L))
  rw [show Ideal.relNorm (OK K) I =
      Ideal.span {Algebra.intNorm (OK K) (OK L) n} by
        simpa only [I] using Ideal.relNorm_singleton (OK K) n,
    show Ideal.relNorm (OK K) J =
      Ideal.span {Algebra.intNorm (OK K) (OK L) (d : OK L)} by
        simpa only [J] using Ideal.relNorm_singleton (OK K) (d : OK L),
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    ← div_eq_mul_inv,
    FractionalIdeal.spanSingleton_div_spanSingleton]
  congr 1
  rw [← hnd, IsFractionRing.mk'_eq_div]
  have hnormDiv :
      Algebra.norm K
          ((algebraMap (OK L) L) n / (algebraMap (OK L) L) (d : OK L)) =
        Algebra.norm K ((algebraMap (OK L) L) n) *
          (Algebra.norm K ((algebraMap (OK L) L) (d : OK L)))⁻¹ := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [hnormDiv,
    ← Algebra.algebraMap_intNorm (A := OK K) (B := OK L)
      (K := K) (L := L) n,
    ← Algebra.algebraMap_intNorm (A := OK K) (B := OK L)
      (K := K) (L := L) (d : OK L)]
  simp only [div_eq_mul_inv]

theorem principalExponentCompatible (x : Lˣ) :
    (idealExponentHom (K := K) (L := L)).toMultiplicative
        (ideleExponentHom (OK L) L
          (principalIdele (OK L) L x).2) =
      ideleExponentHom (OK K) K
        (principalIdele (OK K) K (Units.map (Algebra.norm K) x)).2 := by
  have hnorm := fractional_ideal_principal (K := K) (L := L) x
  rw [← idele_ideal_principal (K := L) x,
    ← idele_ideal_principal (K := K)
      (Units.map (Algebra.norm K) x)] at hnorm
  change fractionalIdealHom (K := K) (L := L)
      (finiteIdeleIdeal (OK L) L (principalIdele (OK L) L x).2) =
    finiteIdeleIdeal (OK K) K
      (principalIdele (OK K) K (Units.map (Algebra.norm K) x)).2 at hnorm
  unfold finiteIdeleIdeal fractionalIdealHom at hnorm
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] at hnorm
  exact (fractionalIdealFactorization (OK K) K).injective hnorm

private theorem fractional_total_subgroup
    (e : HeightOneSpectrum (OK L) →₀ ℤ) :
    fractionalIdealHom (K := K) (L := L)
        (fractionalIdealFactorization (OK L) L
          (Multiplicative.ofAdd e)) ∈
      (finiteExtension (K := K) (L := L)).totalIdealSubgroup := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add Q n e hQ hn ih =>
      rw [show Multiplicative.ofAdd (Finsupp.single Q n + e) =
          Multiplicative.ofAdd (Finsupp.single Q n) *
            Multiplicative.ofAdd e by rfl,
        map_mul, map_mul]
      apply Subgroup.mul_mem _
      · rw [fractional_factorization_single,
          map_zpow, fractional_hom_prime]
        let P : (finiteExtension (K := K) (L := L)).PAbove :=
          { downstairs := lowerPrime (K := K) Q
            upstairs := Q
            liesOver := ⟨rfl⟩ }
        change P.normGenerator
            (finiteExtension (K := K) (L := L)) ^ n ∈ _
        exact Subgroup.zpow_mem _
          (Subgroup.subset_closure (Set.mem_range_self P)) n
      · exact ih

/-- The range of the explicitly packaged fractional-ideal norm is precisely
the total ideal norm subgroup used in Theorem VI.4.9. -/
theorem fractional_ideal_range :
    (fractionalIdealHom (K := K) (L := L)).range =
      (finiteExtension (K := K) (L := L)).totalIdealSubgroup := by
  apply le_antisymm
  · rintro I ⟨J, rfl⟩
    let e := (fractionalIdealFactorization (OK L) L).symm J
    rw [show J = fractionalIdealFactorization (OK L) L e by
      exact ((fractionalIdealFactorization (OK L) L).apply_symm_apply J).symm]
    exact fractional_total_subgroup e.toAdd
  · rw [NFExt.totalIdealSubgroup,
      Subgroup.closure_le]
    rintro I ⟨P, rfl⟩
    let Qideal :=
      ANExt.primeFractionalIdeal P.upstairs
    refine ⟨Qideal, ?_⟩
    dsimp only [Qideal]
    change fractionalIdealHom (K := K) (L := L)
        (ANExt.primeFractionalIdeal P.upstairs) =
      ANExt.primeFractionalIdeal P.downstairs ^
        P.downstairs.asIdeal.inertiaDeg P.upstairs.asIdeal
    have hlower : lowerPrime (K := K) P.upstairs = P.downstairs := by
      apply HeightOneSpectrum.ext
      exact P.liesOver.over.symm
    simpa only [hlower] using
      (fractional_hom_prime (K := K) (L := L) P.upstairs)

/-- Pointwise compatibility still to be established locally: applying the
idèle ideal map after the idèle norm agrees with the prime-generator ideal
norm above.  Its subgroup consequence is proved immediately below. -/
def IdeleIdealCompatible : Prop :=
  ∀ x : IdeleGroup (OK L) L,
    ideleIdealMap (OK K) K (ideleNorm (K := K) (L := L) x) =
      fractionalIdealHom (K := K) (L := L)
        (ideleIdealMap (OK L) L x)

/-- The exact finite-coordinate calculation underlying
`IdeleIdealCompatible`: the lower exponent vector of the idèle norm is
the residue-degree pushforward of the upper exponent vector. -/
def IdeleExponentCompatible : Prop :=
  ∀ x : FiniteIdeles (OK L) L,
    (idealExponentHom (K := K) (L := L)).toMultiplicative
        (ideleExponentHom (OK L) L x) =
      ideleExponentHom (OK K) K
        (finiteIdeleNorm (K := K) (L := L) x)

/-- Coordinate form of the compatibility calculation.  The right side is
definitionally the finite sum of `f(Q/P) * ord_Q(x_Q)` over upper primes
whose contraction is `P`. -/
def IdeleOrderFormula : Prop :=
  ∀ (x : FiniteIdeles (OK L) L) (P : HeightOneSpectrum (OK K)),
    -WithZero.log
        (Valued.v
          (((finiteIdeleNorm (K := K) (L := L) x).1 P :
              (P.adicCompletion K)ˣ) : P.adicCompletion K)) =
      (idealExponentHom (K := K) (L := L)
        (ideleExponentHom (OK L) L x).toAdd) P

/-- The one-completed-factor norm/order identity.  This is the sole local
arithmetic assertion in the global compatibility theorem: a local norm
multiplies normalized order by the residue degree. -/
def CompletionOrderFormula : Prop :=
  ∀ (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ),
    -WithZero.log
        (Valued.v
          ((finiteCompletionNorm (K := K) (L := L) P Q z :
              (P.adicCompletion K)ˣ) : P.adicCompletion K)) =
      (P.asIdeal.inertiaDeg
          (upperPrime (K := K) (L := L) P Q).asIdeal : ℤ) *
        -WithZero.log
          (Valued.v
            (z : (upperPrime (K := K) (L := L) P Q).adicCompletion L))

private theorem ray_units_norm
    {F : Type u} [Field F] [NumberField F]
    (P : HeightOneSpectrum (OK F)) (n : ℕ) :
    rayLocalSubgroup (K := F) P n ≤
      IdeleUnitSubgroup (OK F) F P := by
  exact ray_idele_unit P n

private theorem idele_exponent_modulus
    {F : Type u} [Field F] [NumberField F]
    (m : Modulus F) (a : modulusIdeles m)
    (P : HeightOneSpectrum (OK F)) (hP : P ∈ m.finiteSupport) :
    (ideleExponentHom (OK F) F a.1.2).toAdd P = 0 := by
  rw [idele_exponent_hom]
  have hunit : a.1.2.1 P ∈ IdeleUnitSubgroup (OK F) F P :=
    ray_units_norm P (m.finite P)
      (a.2.1 P hP)
  change a.1.2.1 P ∈ (P.adicCompletionIntegers F).units at hunit
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    at hunit
  simp [hunit]

omit [FiniteDimensional K L] in
private theorem idele_fiber_units
    (P : HeightOneSpectrum (OK K))
    (x : FiniteIdeles (OK L) L)
    (hunit : ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
      x.1 (upperPrime (K := K) (L := L) P Q) ∈
        IdeleUnitSubgroup (OK L) L
          (upperPrime (K := K) (L := L) P Q)) :
    finiteNorm (K := K) (L := L) P x ∈
      IdeleUnitSubgroup (OK K) K P := by
  classical
  change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
    finiteCompletionNorm (K := K) (L := L) P Q
      (x.1 (upperPrime (K := K) (L := L) P Q))) ∈ _
  apply Subgroup.prod_mem
  intro Q hQ
  exact completion_unit_subgroup (K := K) (L := L) P Q _
    (hunit Q)

private theorem idele_exponent_embedding
    {F : Type u} [Field F] [NumberField F]
    (Q : HeightOneSpectrum (OK F)) (z : (Q.adicCompletion F)ˣ) :
    (ideleExponentHom (OK F) F
        (finiteLocalEmbedding (OK F) F Q z)).toAdd =
      Finsupp.single Q
        (-WithZero.log (Valued.v (z : Q.adicCompletion F))) := by
  classical
  apply Finsupp.ext
  intro R
  rw [idele_exponent_hom]
  by_cases hRQ : R = Q
  · subst R
    rw [show (finiteLocalEmbedding (OK F) F Q z).1 Q = z by
      exact RestrictedProduct.mulSingle_eq_same
        (IdeleUnitSubgroup (OK F) F) Q z]
    simp
  · rw [show (finiteLocalEmbedding (OK F) F Q z).1 R = 1 by
      exact RestrictedProduct.mulSingle_eq_of_ne
        (IdeleUnitSubgroup (OK F) F) z hRQ]
    simp [Finsupp.single_eq_of_ne hRQ]

omit [FiniteDimensional K L] in
private theorem idele_local_embedding
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ) :
    finiteNorm (K := K) (L := L) P
        (finiteLocalEmbedding (OK L) L
          (upperPrime (K := K) (L := L) P Q) z) =
      finiteCompletionNorm (K := K) (L := L) P Q z := by
  classical
  let q := fun Q' : UpperPrimeFactors (K := K) (L := L) P ↦
    upperPrime (K := K) (L := L) P Q'
  change (∏ Q' : UpperPrimeFactors (K := K) (L := L) P,
    finiteCompletionNorm (K := K) (L := L) P Q'
      ((finiteLocalEmbedding (OK L) L (q Q) z).1 (q Q'))) = _
  rw [Fintype.prod_eq_single Q]
  · rw [show (finiteLocalEmbedding (OK L) L (q Q) z).1 (q Q) = z by
      exact RestrictedProduct.mulSingle_eq_same
        (IdeleUnitSubgroup (OK L) L) (q Q) z]
  · intro Q' hQ'
    have hprime : q Q' ≠ q Q := by
      intro h
      exact hQ' (factor_above_injective
        (K := K) (L := L) P (Subtype.ext h))
    rw [show (finiteLocalEmbedding (OK L) L (q Q) z).1 (q Q') = 1 by
      exact RestrictedProduct.mulSingle_eq_of_ne
        (IdeleUnitSubgroup (OK L) L) z hprime,
      map_one]

/-- A convenient representative form of Proposition V.4.6(b): after
multiplication by a principal idèle, any idèle satisfies the ray conditions
of a prescribed modulus. -/
private theorem multiplier_modulus_ideles
    {F : Type u} [Field F] [NumberField F]
    (m : Modulus F) (a : IdeleGroup (OK F) F) :
    ∃ b : Fˣ,
      a * principalIdele (OK F) F b ∈ modulusIdeles m := by
  obtain ⟨c, hc⟩ := weakApproximation m
    (QuotientGroup.mk' (principalIdeles (OK F) F) a)
  change QuotientGroup.mk' (principalIdeles (OK F) F) c.1 =
    QuotientGroup.mk' (principalIdeles (OK F) F) a at hc
  have hdiv : c.1 / a ∈ principalIdeles (OK F) F :=
    QuotientGroup.eq_iff_div_mem.mp hc
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  have heq : a * principalIdele (OK F) F b = c.1 := by
    rw [hb]
    simp [div_eq_mul_inv]
  rw [heq]
  exact c.2

private noncomputable def primesAboveFinset
    (P : HeightOneSpectrum (OK K)) :
    Finset (HeightOneSpectrum (OK L)) := by
  classical
  exact Finset.univ.image
    (fun Q : UpperPrimeFactors (K := K) (L := L) P ↦
      upperPrime (K := K) (L := L) P Q)

private noncomputable def primesAboveModulus
    (P : HeightOneSpectrum (OK K)) : Modulus L := by
  classical
  let S := primesAboveFinset (K := K) (L := L) P
  let finitePart : HeightOneSpectrum (OK L) →₀ ℕ :=
    Finsupp.onFinset S (fun Q ↦ if Q ∈ S then 1 else 0) (by
      intro Q hQ
      by_contra hQS
      simp [hQS] at hQ)
  exact
    { finite := finitePart
      infinite := ∅ }

omit [FiniteDimensional K L] in
private theorem upper_modulus_support
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    upperPrime (K := K) (L := L) P Q ∈
      (primesAboveModulus (K := K) (L := L) P).finiteSupport := by
  classical
  have hmem : upperPrime (K := K) (L := L) P Q ∈
      primesAboveFinset (K := K) (L := L) P := by
    unfold primesAboveFinset
    apply Finset.mem_image.mpr
    exact ⟨Q, Finset.mem_univ Q, rfl⟩
  rw [Modulus.finite_support_iff]
  change (if upperPrime (K := K) (L := L) P Q ∈
    primesAboveFinset (K := K) (L := L) P then 1 else 0) ≠ 0
  rw [if_pos hmem]
  exact one_ne_zero

omit [FiniteDimensional K L] in
private theorem primes_above_modulus
    (P : HeightOneSpectrum (OK K)) (Q : HeightOneSpectrum (OK L))
    (hQ : lowerPrime (K := K) Q = P) :
    Q ∈ (primesAboveModulus (K := K) (L := L) P).finiteSupport := by
  subst P
  simpa only [upper_prime_factor] using
    upper_modulus_support
      (K := K) (L := L) (lowerPrime (K := K) Q)
      (upperPrimeFactor (K := K) (L := L) Q)

/-- A local completed norm multiplies normalized order by the residue
degree.  Weak approximation reduces the assertion to the already-proved
compatibility of the global norm with principal idèles. -/
theorem completionOrderFormula :
    CompletionOrderFormula (K := K) (L := L) := by
  classical
  intro P Q z
  let q := upperPrime (K := K) (L := L) P Q
  let a : IdeleGroup (OK L) L := finitePlaceEmbedding (OK L) L q z
  let m := primesAboveModulus (K := K) (L := L) P
  obtain ⟨b, hb⟩ :=
    multiplier_modulus_ideles m a
  let c : modulusIdeles m :=
    ⟨a * principalIdele (OK L) L b, hb⟩
  let ea := (ideleExponentHom (OK L) L a.2).toAdd
  let eb := (ideleExponentHom (OK L) L
    (principalIdele (OK L) L b).2).toAdd
  let ec := (ideleExponentHom (OK L) L c.1.2).toAdd
  let ena := (ideleExponentHom (OK K) K
    (finiteIdeleNorm (K := K) (L := L) a.2)).toAdd
  let enb := (ideleExponentHom (OK K) K
    (principalIdele (OK K) K (Units.map (Algebra.norm K) b)).2).toAdd
  let enc := (ideleExponentHom (OK K) K
    (finiteIdeleNorm (K := K) (L := L) c.1.2)).toAdd
  have hec : ec = ea + eb := by
    change (ideleExponentHom (OK L) L
        (a.2 * (principalIdele (OK L) L b).2)).toAdd =
      (ideleExponentHom (OK L) L a.2).toAdd +
        (ideleExponentHom (OK L) L
          (principalIdele (OK L) L b).2).toAdd
    rw [map_mul]
    rfl
  have hecP : idealExponentHom (K := K) (L := L) ec P = 0 := by
    apply ideal_exponent_fiber
    intro R hRP
    exact idele_exponent_modulus m c R
      (primes_above_modulus
        (K := K) (L := L) P R hRP)
  have hcNormUnit :
      finiteNorm (K := K) (L := L) P c.1.2 ∈
        IdeleUnitSubgroup (OK K) K P := by
    apply idele_fiber_units
    intro Q'
    exact ray_units_norm
      (upperPrime (K := K) (L := L) P Q')
      (m.finite (upperPrime (K := K) (L := L) P Q'))
      (c.2.1 (upperPrime (K := K) (L := L) P Q')
        (upper_modulus_support
          (K := K) (L := L) P Q'))
  have hencP : enc P = 0 := by
    rw [show enc P = -WithZero.log
        (Valued.v
          (((finiteIdeleNorm (K := K) (L := L) c.1.2).1 P :
            (P.adicCompletion K)ˣ) : P.adicCompletion K)) by
      exact idele_exponent_hom (OK K) K
        (finiteIdeleNorm (K := K) (L := L) c.1.2) P]
    change finiteNorm (K := K) (L := L) P c.1.2 ∈
      (P.adicCompletionIntegers K).units at hcNormUnit
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      at hcNormUnit
    simp [hcNormUnit]
  have henc : enc = ena + enb := by
    have hnorm : finiteIdeleNorm (K := K) (L := L) c.1.2 =
        finiteIdeleNorm (K := K) (L := L) a.2 *
          finiteIdeleNorm (K := K) (L := L)
            (principalIdele (OK L) L b).2 := by
      exact map_mul (finiteIdeleNorm (K := K) (L := L)) a.2
        (principalIdele (OK L) L b).2
    rw [principalIdeleCompatibility (K := K) (L := L) b] at hnorm
    change (ideleExponentHom (OK K) K
        (finiteIdeleNorm (K := K) (L := L) c.1.2)).toAdd =
      (ideleExponentHom (OK K) K
        (finiteIdeleNorm (K := K) (L := L) a.2)).toAdd +
      (ideleExponentHom (OK K) K
        (principalIdele (OK K) K (Units.map (Algebra.norm K) b)).2).toAdd
    rw [hnorm, map_mul]
    rfl
  have hprincipal :
      idealExponentHom (K := K) (L := L) eb P = enb P := by
    have h := congrArg (fun e : Multiplicative
        (HeightOneSpectrum (OK K) →₀ ℤ) ↦ e.toAdd P)
      (principalExponentCompatible
        (K := K) (L := L) b)
    simpa only [eb, enb] using h
  have horders : ena P =
      idealExponentHom (K := K) (L := L) ea P := by
    have hidealAdd := congrArg
      (fun e : HeightOneSpectrum (OK L) →₀ ℤ ↦
        idealExponentHom (K := K) (L := L) e P) hec
    have hnormAdd := congrArg
      (fun e : HeightOneSpectrum (OK K) →₀ ℤ ↦ e P) henc
    simp only [map_add, Finsupp.add_apply] at hidealAdd hnormAdd
    rw [hecP] at hidealAdd
    rw [hencP] at hnormAdd
    omega
  have hea : ea = Finsupp.single q
      (-WithZero.log (Valued.v (z : q.adicCompletion L))) := by
    exact idele_exponent_embedding q z
  have hnormAt := idele_local_embedding
    (K := K) (L := L) P Q z
  rw [← hnormAt]
  change ena P = _
  rw [horders, hea, ideal_exponent_single]
  simp [q, lowerPrime, primeNormWeight,
    upperPrime_under (K := K) (L := L) P Q]

omit [FiniteDimensional K L] in
private theorem ideal_exponent_upper
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (P : HeightOneSpectrum (OK K)) :
    idealExponentHom (K := K) (L := L) e P =
      ∑ Q : UpperPrimeFactors (K := K) (L := L) P,
        primeNormWeight (K := K)
            (upperPrime (K := K) (L := L) P Q) *
          e (upperPrime (K := K) (L := L) P Q) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add R n e hR hn ih =>
      rw [map_add, Finsupp.add_apply, ih]
      simp_rw [Finsupp.add_apply, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [ideal_exponent_single]
      by_cases hRP : lowerPrime (K := K) R = P
      · subst P
        rw [Finsupp.single_eq_same]
        rw [Fintype.sum_eq_single
          (upperPrimeFactor (K := K) (L := L) R)]
        · simp [upper_prime_factor]
        · intro Q hQ
          have hne : upperPrime (K := K) (L := L)
              (lowerPrime (K := K) R) Q ≠ R := by
            intro heq
            apply hQ
            apply factor_above_injective
              (K := K) (L := L) (lowerPrime (K := K) R)
            apply Subtype.ext
            simpa only [upperPrimeAbove,
              upper_prime_factor] using heq
          simp [Finsupp.single_eq_of_ne hne]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hRP)]
        symm
        apply Finset.sum_eq_zero
        intro Q hQ
        have hne : upperPrime (K := K) (L := L) P Q ≠ R := by
          intro heq
          apply hRP
          rw [← heq]
          exact upperPrime_under (K := K) (L := L) P Q
        simp [Finsupp.single_eq_of_ne hne]

private theorem order_finset_prod
    (P : HeightOneSpectrum (OK K))
    {I : Type*} (s : Finset I)
    (f : I → (P.adicCompletion K)ˣ) :
    -WithZero.log
        (Valued.v
          (((∏ i ∈ s, f i) : (P.adicCompletion K)ˣ) :
            P.adicCompletion K)) =
      ∑ i ∈ s,
        -WithZero.log (Valued.v ((f i : (P.adicCompletion K)ˣ) :
          P.adicCompletion K)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hfi : Valued.v ((f i : (P.adicCompletion K)ˣ) :
          P.adicCompletion K) ≠ 0 := by simp
      have hfs : Valued.v
          (((∏ j ∈ s, f j) : (P.adicCompletion K)ˣ) :
            P.adicCompletion K) ≠ 0 := by
        let u : (P.adicCompletion K)ˣ := ∏ j ∈ s, f j
        have hu : Valued.v ((u : (P.adicCompletion K)ˣ) :
            P.adicCompletion K) ≠ 0 := by simp
        exact hu
      rw [Units.val_mul, map_mul, WithZero.log_mul hfi hfs]
      rw [neg_add_rev, ih]
      omega

/-- The finite idèle norm has at each lower prime the residue-degree
weighted sum of the normalized orders at all upper primes. -/
theorem ideleOrderFormula :
    IdeleOrderFormula (K := K) (L := L) := by
  classical
  intro x P
  rw [ideal_exponent_upper]
  change
    (-WithZero.log
      (Valued.v
        (((∏ Q : UpperPrimeFactors (K := K) (L := L) P,
            finiteCompletionNorm (K := K) (L := L) P Q
              (x.1 (upperPrime (K := K) (L := L) P Q))) :
            (P.adicCompletion K)ˣ) : P.adicCompletion K))) = _
  rw [order_finset_prod]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [idele_exponent_hom]
  have hweight : primeNormWeight (K := K)
      (upperPrime (K := K) (L := L) P Q) =
      (P.asIdeal.inertiaDeg
        (upperPrime (K := K) (L := L) P Q).asIdeal : ℤ) := by
    simp [primeNormWeight, lowerPrime,
      upperPrime_under (K := K) (L := L) P Q]
  rw [hweight]
  exact completionOrderFormula (K := K) (L := L) P Q
    (x.1 (upperPrime (K := K) (L := L) P Q))

omit [FiniteDimensional K L] in
theorem exponent_compatible_formula :
    IdeleExponentCompatible (K := K) (L := L) ↔
      IdeleOrderFormula (K := K) (L := L) := by
  constructor
  · intro h x P
    have hP := congrArg (fun e : Multiplicative
        (HeightOneSpectrum (OK K) →₀ ℤ) ↦ e.toAdd P) (h x)
    simpa only [idele_exponent_hom] using hP.symm
  · intro h x
    apply Multiplicative.toAdd.injective
    apply Finsupp.ext
    intro P
    simpa only [idele_exponent_hom] using (h x P).symm

theorem ideleExponentCompatible :
    IdeleExponentCompatible (K := K) (L := L) :=
  exponent_compatible_formula.mpr
    (ideleOrderFormula (K := K) (L := L))

/-- The exponent-vector identity is exactly the desired pointwise
idèle/ideal norm identity. -/
theorem idele_compatible_exponent
    (h : IdeleExponentCompatible (K := K) (L := L)) :
    IdeleIdealCompatible (K := K) (L := L) := by
  intro x
  change finiteIdeleIdeal (OK K) K
      (finiteIdeleNorm (K := K) (L := L) x.2) =
    fractionalIdealHom (K := K) (L := L)
      (finiteIdeleIdeal (OK L) L x.2)
  unfold finiteIdeleIdeal fractionalIdealHom
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  change fractionalIdealFactorization (OK K) K
      (ideleExponentHom (OK K) K
        (finiteIdeleNorm (K := K) (L := L) x.2)) =
    fractionalIdealFactorization (OK K) K
      ((idealExponentHom (K := K) (L := L)).toMultiplicative
        (ideleExponentHom (OK L) L x.2))
  exact congrArg (fractionalIdealFactorization (OK K) K) (h x.2).symm

theorem ideleIdealCompatible :
    IdeleIdealCompatible (K := K) (L := L) :=
  idele_compatible_exponent
    (ideleExponentCompatible (K := K) (L := L))

/-- Pointwise compatibility implies the exact subgroup equality needed for
the idealic/idèlic index comparison. -/
theorem idele_total_compatible
    (hcompat : IdeleIdealCompatible (K := K) (L := L)) :
    Subgroup.map (ideleIdealMap (OK K) K)
        (ideleNormSubgroup (K := K) (L := L)) =
      (finiteExtension (K := K) (L := L)).totalIdealSubgroup := by
  rw [← fractional_ideal_range (K := K) (L := L)]
  ext I
  constructor
  · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
    exact ⟨ideleIdealMap (OK L) L x, (hcompat x).symm⟩
  · rintro ⟨J, rfl⟩
    obtain ⟨x, rfl⟩ := idele_surjective (OK L) L J
    refine ⟨ideleNorm (K := K) (L := L) x, ⟨x, rfl⟩, ?_⟩
    exact hcompat x

theorem idele_ideal_total :
    Subgroup.map (ideleIdealMap (OK K) K)
        (ideleNormSubgroup (K := K) (L := L)) =
      (finiteExtension (K := K) (L := L)).totalIdealSubgroup :=
  idele_total_compatible
    (ideleIdealCompatible (K := K) (L := L))

/-! ### Prime-to-modulus norm lifts -/

local instance lowerPrimeOutsideDecidable
    (S : Finset (HeightOneSpectrum (OK K))) :
    DecidablePred (fun Q : HeightOneSpectrum (OK L) ↦
      lowerPrime (K := K) Q ∉ S) :=
  Classical.decPred _

omit [FiniteDimensional K L] in
/-- Removing all upper-prime exponents over a finite set does not change a
lower norm exponent vector which already vanishes on that set. -/
private theorem exponent_filter_outside
    (S : Finset (HeightOneSpectrum (OK K)))
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (hzero : ∀ P ∈ S,
      idealExponentHom (K := K) (L := L) e P = 0) :
    idealExponentHom (K := K) (L := L)
        (e.filter fun Q ↦ lowerPrime (K := K) Q ∉ S) =
      idealExponentHom (K := K) (L := L) e := by
  classical
  let good := e.filter fun Q ↦ lowerPrime (K := K) Q ∉ S
  let bad := e.filter fun Q ↦ lowerPrime (K := K) Q ∈ S
  have he : e = good + bad := by
    apply Finsupp.ext
    intro Q
    by_cases hQ : lowerPrime (K := K) Q ∈ S
    · simp [good, bad, hQ]
    · simp [good, bad, hQ]
  have hbad : idealExponentHom (K := K) (L := L) bad = 0 := by
    apply Finsupp.ext
    intro P
    by_cases hP : P ∈ S
    · have hgoodP :
      idealExponentHom (K := K) (L := L) good P = 0 := by
        apply ideal_exponent_fiber
        intro Q hQP
        simp [good, hQP, hP]
      have heP := congrArg
        (fun z : HeightOneSpectrum (OK L) →₀ ℤ ↦
          idealExponentHom (K := K) (L := L) z P) he
      simp only [map_add, Finsupp.add_apply, hgoodP, zero_add] at heP
      rw [← heP, hzero P hP]
      rfl
    · apply ideal_exponent_fiber
      intro Q hQP
      simp [bad, hQP, hP]
  rw [show e.filter (fun Q ↦ lowerPrime (K := K) Q ∉ S) = good from rfl]
  rw [he, map_add, hbad, add_zero]

/-- A local unit of any prescribed normalized order. -/
private theorem local_order_lift
    {F : Type u} [Field F] [NumberField F]
    (Q : HeightOneSpectrum (OK F)) (n : ℤ) :
    ∃ z : (Q.adicCompletion F)ˣ,
      -WithZero.log (Valued.v (z : Q.adicCompletion F)) = n := by
  obtain ⟨z, hz⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      (K := F) Q (WithZero.exp (-n))
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have : (0 : ℤᵐ⁰) = WithZero.exp (-n) := by simpa using hz
    exact WithZero.exp_ne_zero this.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  simp only [Units.val_mk0, hz, WithZero.log_exp]
  omega

private noncomputable def controlledLocalLift
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (Q : HeightOneSpectrum (OK L)) : (Q.adicCompletion L)ˣ :=
  if e Q = 0 then 1
  else Classical.choose (local_order_lift Q (e Q))

private theorem controlled_lift_order
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (Q : HeightOneSpectrum (OK L)) :
    -WithZero.log (Valued.v
      (controlledLocalLift (L := L) e Q :
        Q.adicCompletion L)) = e Q := by
  by_cases hQ : e Q = 0
  · simp [controlledLocalLift, hQ]
  · simpa only [controlledLocalLift, if_neg hQ] using
      Classical.choose_spec
        (local_order_lift Q (e Q))

private theorem controlled_lift_one
    (e : HeightOneSpectrum (OK L) →₀ ℤ)
    (Q : HeightOneSpectrum (OK L)) (hQ : e Q = 0) :
    controlledLocalLift (L := L) e Q = 1 := by
  simp [controlledLocalLift, hQ]

/-- Realize an exponent vector by a finite idèle which is literally `1`
outside its support. -/
private theorem exponents_off_support
    (e : HeightOneSpectrum (OK L) →₀ ℤ) :
    ∃ x : FiniteIdeles (OK L) L,
      (ideleExponentHom (OK L) L x).toAdd = e ∧
      ∀ Q, e Q = 0 → x.1 Q = 1 := by
  classical
  let z : ∀ Q : HeightOneSpectrum (OK L), (Q.adicCompletion L)ˣ :=
    fun Q ↦ controlledLocalLift (L := L) e Q
  have hzRestricted : ∀ᶠ Q in Filter.cofinite,
      z Q ∈ IdeleUnitSubgroup (OK L) L Q := by
    filter_upwards [e.support.finite_toSet.compl_mem_cofinite] with Q hQ
    have heQ : e Q = 0 := by simpa using hQ
    rw [show z Q = 1 by
      exact controlled_lift_one
        (L := L) e Q heQ]
    exact (IdeleUnitSubgroup (OK L) L Q).one_mem
  let x : FiniteIdeles (OK L) L := RestrictedProduct.mk z hzRestricted
  refine ⟨x, ?_, ?_⟩
  · apply Finsupp.ext
    intro Q
    rw [idele_exponent_hom]
    change -WithZero.log (Valued.v (z Q : Q.adicCompletion L)) = e Q
    exact controlled_lift_order (L := L) e Q
  · intro Q hQ
    change z Q = 1
    exact controlled_lift_one (L := L) e Q hQ

/-- Every prime-to-`m` ideal norm is the ideal of an actual idèle norm
which already lies in `I_m`. -/
theorem modulus_idele_image
    (m : Modulus K) :
    let B := idealMapBridge (K := K) m
    (finiteExtension (K := K) (L := L)).idealNormSubgroup m.finiteSupport ≤
      Subgroup.map (modulusIdeleIdeal m B.landsPrimeTo)
        ((ideleNormSubgroup (K := K) (L := L)).comap
          (modulusIdeles m).subtype) := by
  classical
  dsimp only
  let B := idealMapBridge (K := K) m
  intro J hJ
  have hJtotal : (J.1 : (FractionalIdeal (OK K)⁰ K)ˣ) ∈
      (finiteExtension (K := K) (L := L)).totalIdealSubgroup := hJ
  rw [← fractional_ideal_range (K := K) (L := L)] at hJtotal
  obtain ⟨A, hA⟩ := hJtotal
  let e := ((fractionalIdealFactorization (OK L) L).symm A).toAdd
  have hnormA :
      fractionalIdealHom (K := K) (L := L)
          (fractionalIdealFactorization (OK L) L
            (Multiplicative.ofAdd e)) = J.1 := by
    rw [show fractionalIdealFactorization (OK L) L
        (Multiplicative.ofAdd e) = A by
      exact (fractionalIdealFactorization (OK L) L).apply_symm_apply A]
    exact hA
  have hzero : ∀ P ∈ m.finiteSupport,
      idealExponentHom (K := K) (L := L) e P = 0 := by
    intro P hP
    have hcount := J.2 P hP
    have hfac := congrArg
      (fun z : Multiplicative (HeightOneSpectrum (OK K) →₀ ℤ) ↦ z.toAdd P)
      ((fractionalIdealFactorization (OK K) K).symm_apply_apply
        ((idealExponentHom (K := K) (L := L)).toMultiplicative
          (Multiplicative.ofAdd e)))
    change FractionalIdeal.count K P
        (((fractionalIdealFactorization (OK K) K
          ((idealExponentHom (K := K) (L := L)).toMultiplicative
            (Multiplicative.ofAdd e)) :
              (FractionalIdeal (OK K)⁰ K)ˣ) :
            FractionalIdeal (OK K)⁰ K)) =
      idealExponentHom (K := K) (L := L) e P at hfac
    have hfactorization : fractionalIdealFactorization (OK K) K
          ((idealExponentHom (K := K) (L := L)).toMultiplicative
            (Multiplicative.ofAdd e)) = J.1 := by
      simpa only [fractionalIdealHom, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hnormA
    rw [hfactorization] at hfac
    exact hfac.symm.trans hcount
  let e' := e.filter fun Q ↦ lowerPrime (K := K) Q ∉ m.finiteSupport
  have hnormE : idealExponentHom (K := K) (L := L) e' =
      idealExponentHom (K := K) (L := L) e :=
    exponent_filter_outside m.finiteSupport e hzero
  obtain ⟨x, hxexp, hxone⟩ :=
    exponents_off_support
      (L := L) e'
  let a : IdeleGroup (OK L) L := (1, x)
  let n : IdeleGroup (OK K) K := ideleNorm (K := K) (L := L) a
  have hnmod : n ∈ modulusIdeles m := by
    constructor
    · intro P hP
      change finiteNorm (K := K) (L := L) P x ∈
        rayLocalSubgroup (K := K) P (m.finite P)
      have hnP : finiteNorm (K := K) (L := L) P x = 1 := by
        change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
          finiteCompletionNorm (K := K) (L := L) P Q
            (x.1 (upperPrime (K := K) (L := L) P Q))) = 1
        apply Finset.prod_eq_one
        intro Q _
        have heQ : e' (upperPrime (K := K) (L := L) P Q) = 0 := by
          simp only [e', Finsupp.filter_apply]
          rw [if_neg]
          exact not_not_intro <| by
            simpa only [lowerPrime, upperPrime_under] using hP
        rw [hxone _ heQ, map_one]
      rw [hnP]
      exact (rayLocalSubgroup (K := K) P (m.finite P)).one_mem
    · intro w hw
      have hnInfinite : n.1 = 1 := by
        change infiniteIdeleNorm (K := K) (L := L)
            (1 : (InfiniteAdeleRing L)ˣ) = 1
        exact map_one _
      rw [hnInfinite]
      change MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ) w.1 ∈
        positiveRealSubgroup w
      have hone := congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ))) w.1
      exact hone.symm ▸ (positiveRealSubgroup w).one_mem
  let nm : modulusIdeles m := ⟨n, hnmod⟩
  refine ⟨nm, ?_, ?_⟩
  · exact ⟨a, rfl⟩
  · apply Subtype.ext
    change ideleIdealMap (OK K) K n = J.1
    rw [ideleIdealCompatible (K := K) (L := L) a]
    change fractionalIdealHom (K := K) (L := L)
      (fractionalIdealFactorization (OK L) L
        (ideleExponentHom (OK L) L x)) = J.1
    rw [show ideleExponentHom (OK L) L x =
        Multiplicative.ofAdd e' by
      exact Multiplicative.toAdd.injective hxexp]
    unfold fractionalIdealHom
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    change fractionalIdealFactorization (OK K) K
      (Multiplicative.ofAdd
        (idealExponentHom (K := K) (L := L) e')) = J.1
    rw [hnormE]
    simpa only [fractionalIdealHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hnormA

/-- The faithful idealic-to-idèlic comparison used in Theorem VII.5.1.
For a suitable modulus, the idèlic norm index is bounded above by the
ray-ideal norm index. -/
theorem idele_extension_ray :
    ∃ m : Modulus K,
      Finite (IdealsPrimeTo (OK K) K m.finiteSupport ⧸
        extensionRaySubgroup
          (finiteExtension (K := K) (L := L)) m) →
        (principalIdeles (OK K) K ⊔
            ideleNormSubgroup (K := K) (L := L)).index ≤
          (extensionRaySubgroup
            (finiteExtension (K := K) (L := L)) m).index := by
  classical
  obtain ⟨m, hmNorm⟩ := modulusContainedSubgroup (K := K) (L := L)
  let P := principalIdeles (OK K) K
  let N := ideleNormSubgroup (K := K) (L := L)
  let H := P ⊔ N
  let M := modulusIdeles m
  let i : M →* IdeleGroup (OK K) K := (modulusIdeles m).subtype
  let C : Subgroup M := H.comap i
  let B := idealMapBridge (K := K) m
  let f := modulusIdeleIdeal m B.landsPrimeTo
  let D : Subgroup (IdealsPrimeTo (OK K) K m.finiteSupport) :=
    Subgroup.map f C
  let R := extensionRaySubgroup
    (finiteExtension (K := K) (L := L)) m
  let qI : M →* (IdeleGroup (OK K) K ⧸ H) :=
    (QuotientGroup.mk' H).comp i
  have hqI : Function.Surjective qI := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H z
    obtain ⟨b, hb⟩ := weakApproximation m
      (QuotientGroup.mk' P a)
    refine ⟨b, ?_⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact (show P ≤ H from le_sup_left)
      (QuotientGroup.eq_iff_div_mem.mp hb)
  have hqIker : qI.ker = C := by
    ext a
    change QuotientGroup.mk' H (i a) = 1 ↔ i a ∈ H
    exact QuotientGroup.eq_one_iff (N := H) (i a)
  let eI : (M ⧸ C) ≃* (IdeleGroup (OK K) K ⧸ H) :=
    (QuotientGroup.quotientMulEquivOfEq hqIker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qI hqI)
  have hfker : f.ker ≤ C := by
    intro a ha
    have haUnit : a ∈ modulusUnitIdeles m := by
      rw [← modulus_ideal_ker m B.landsPrimeTo]
      exact ha
    change i a ∈ H
    exact (show N ≤ H from le_sup_right) (hmNorm ⟨a, haUnit, rfl⟩)
  let qJ : M →* (IdealsPrimeTo (OK K) K m.finiteSupport ⧸ D) :=
    (QuotientGroup.mk' D).comp f
  have hqJ : Function.Surjective qJ :=
    (QuotientGroup.mk'_surjective D).comp B.idealMap_surjective
  have hqJker : qJ.ker = C := by
    ext a
    change QuotientGroup.mk' D (f a) = 1 ↔ a ∈ C
    have hquot : QuotientGroup.mk' D (f a) = 1 ↔ f a ∈ D :=
      QuotientGroup.eq_one_iff (N := D) (f a)
    rw [hquot]
    change a ∈ Subgroup.comap f (Subgroup.map f C) ↔ a ∈ C
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hfker]
  let eJ : (M ⧸ C) ≃*
      (IdealsPrimeTo (OK K) K m.finiteSupport ⧸ D) :=
    (QuotientGroup.quotientMulEquivOfEq hqJker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qJ hqJ)
  have hRleD : R ≤ D := by
    change (rayPrincipalSubgroup K m ⊔
      (finiteExtension (K := K) (L := L)).idealNormSubgroup
        m.finiteSupport) ≤ D
    apply sup_le
    · rw [← B.principal_image]
      apply Subgroup.map_mono
      intro a ha
      change i a ∈ H
      exact (show P ≤ H from le_sup_left) ha
    · refine (modulus_idele_image
          (K := K) (L := L) m).trans ?_
      apply Subgroup.map_mono
      intro a ha
      change i a ∈ H
      exact (show N ≤ H from le_sup_right) ha
  have hindexIC : H.index = C.index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact (Nat.card_congr eI.toEquiv).symm
  have hindexCD : C.index = D.index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr eJ.toEquiv
  refine ⟨m, fun hfinite ↦ ?_⟩
  letI : Finite (IdealsPrimeTo (OK K) K m.finiteSupport ⧸ R) := hfinite
  letI : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact hindexIC.trans_le <|
    hindexCD.trans_le (Subgroup.index_antitone hRleD)

/-- The unconditional, universe-polymorphic idealic-to-idèlic inequality
bridge consumed by the Chapter VII, Theorem 5.1 reduction. -/
theorem idealInequalityBridge :
    IdealInequalityBridge.{u} := by
  intro F E _ _ _ _ _ _
  exact idele_extension_ray
    (K := F) (L := E)

end

end Submission.CField.HNorm
