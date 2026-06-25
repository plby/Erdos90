import Towers.NumberTheory.Ramification.EisensteinRamification

/-!
# Milne, Algebraic Number Theory, Proposition 3.53: unconditional total ramification

This file proves the full ramification assertion for an Eisenstein root without assuming that
the integral closure is monogenic or imposing a conductor-coprimality hypothesis. The valuation
argument is expressed through multiplicities of prime ideals in principal ideals.
-/

namespace Towers.NumberTheory.Milne

open Algebra Ideal Polynomial UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

/-- The local valuation estimate in Proposition 3.53: the degree of an Eisenstein minimal
polynomial is at most the ramification index of every prime above the Eisenstein prime. -/
theorem minpoly_idx_eisenstein
    {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsPrime] (hp0 : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    {alpha : B} (halpha : IsIntegral A alpha)
    (hf : (minpoly A alpha).IsEisensteinAt p) :
    (minpoly A alpha).natDegree ≤ Ideal.ramificationIdx p P := by
  classical
  let F := minpoly A alpha
  let e := Ideal.ramificationIdx p P
  let m := F.natDegree
  have he0 : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  have halphaP : alpha ∈ P :=
    lies_eisenstein hf (minpoly.monic halpha)
      (minpoly.aeval A alpha)
  by_contra hme
  have hem : e < m := Nat.lt_of_not_ge hme
  have hmap_le : p.map (algebraMap A B) ≤ P ^ e :=
    Ideal.le_pow_ramificationIdx
  have hterms : ∀ i < m,
      algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈ P ^ (e + 1) := by
    intro i hi
    by_cases him : i + 1 = m
    · rw [him, (minpoly.monic halpha).coeff_natDegree, map_one, one_mul]
      exact (Ideal.pow_le_pow_right (by omega))
        (Ideal.pow_mem_pow halphaP m)
    · have hcoeff : F.coeff (i + 1) ∈ p := hf.coeff_mem him
      have hcoeff' : algebraMap A B (F.coeff (i + 1)) ∈ P ^ e :=
        hmap_le (Ideal.mem_map_of_mem (algebraMap A B) hcoeff)
      have hpow : alpha ^ (i + 1) ∈ P ^ (i + 1) :=
        Ideal.pow_mem_pow halphaP (i + 1)
      have hmul : algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈
          P ^ e * P ^ (i + 1) := Ideal.mul_mem_mul hcoeff' hpow
      rw [← pow_add] at hmul
      exact (Ideal.pow_le_pow_right (by omega)) hmul
  have hsum : ∑ i ∈ Finset.range m,
      algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈ P ^ (e + 1) :=
    Ideal.sum_mem _ fun i hi ↦ hterms i (Finset.mem_range.mp hi)
  have heval : algebraMap A B (F.coeff 0) +
      ∑ i ∈ Finset.range m,
        algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) = 0 := by
    have hroot := minpoly.aeval A alpha
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at hroot
    simpa [F, m, Algebra.smul_def, add_comm] using hroot
  have hconst_up : algebraMap A B (F.coeff 0) ∈ P ^ (e + 1) := by
    rw [eq_neg_of_add_eq_zero_left heval]
    simpa only [Ideal.neg_mem_iff] using hsum
  have hc0 : F.coeff 0 ≠ 0 := by
    intro hc
    apply hf.notMem
    rw [hc]
    exact Ideal.zero_mem _
  have hspan0 : Ideal.span ({F.coeff 0} : Set A) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hc0
  have hpirr : Irreducible p :=
    (Ideal.prime_of_isPrime hp0 (inferInstance : p.IsPrime)).irreducible
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hPirr : Irreducible P :=
    (Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)).irreducible
  have hbase : emultiplicity p (Ideal.span ({F.coeff 0} : Set A)) = 1 := by
    apply emultiplicity_eq_of_dvd_of_not_dvd
    · rw [pow_one, Ideal.dvd_span_singleton]
      exact hf.mem (minpoly.natDegree_pos halpha)
    · simpa only [Ideal.dvd_span_singleton] using hf.notMem
  have hmapem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    (S := B) hspan0 hpirr hPirr hP0
  have hmapem' :
      emultiplicity P (Ideal.span ({algebraMap A B (F.coeff 0)} : Set B)) = e := by
    simpa [Ideal.map_span, hbase, e] using hmapem
  have hdivup : P ^ (e + 1) ∣
      Ideal.span ({algebraMap A B (F.coeff 0)} : Set B) :=
    Ideal.dvd_span_singleton.mpr hconst_up
  have hle := le_emultiplicity_of_pow_dvd hdivup
  rw [hmapem'] at hle
  exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self e))) hle

/-- Proposition 3.53 for an integral generator of the fraction-field extension. This is the
book's setting `L = K(alpha)` and imposes no monogenicity condition on `B`. -/
theorem eisenstein_total_top
    (A B K L : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    {p : Ideal A} [p.IsPrime] (hp0 : p ≠ ⊥)
    {alpha : B} (halpha : IsIntegral A alpha)
    (hf : (minpoly A alpha).IsEisensteinAt p)
    (hgen : IntermediateField.adjoin K ({algebraMap B L alpha} : Set L) = ⊤) :
    let P := p.map (algebraMap A B) ⊔ Ideal.span {alpha}
    P.IsPrime ∧
      p.map (algebraMap A B) = P ^ (minpoly A alpha).natDegree ∧
      Ideal.ramificationIdx p P = (minpoly A alpha).natDegree ∧
      ∀ Q : Ideal B, Q.IsPrime → Q.LiesOver p → Q = P := by
  classical
  letI : NoZeroSMulDivisors A B := ⟨fun h ↦ smul_eq_zero.mp h⟩
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp0
  let F := minpoly A alpha
  let m := F.natDegree
  let I := p.map (algebraMap A B) ⊔ Ideal.span {alpha}
  have hm0 : 0 < m := minpoly.natDegree_pos halpha
  have hfieldDegree : Module.finrank K L = m := by
    have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq K
      (algebraMap B L alpha)).mp hgen
    rw [minpoly.isIntegrallyClosed_eq_field_fractions K L halpha,
      (minpoly.monic halpha).natDegree_map] at hdeg
    exact hdeg.symm
  let Q0 : Ideal.primesOver p B := Classical.choice inferInstance
  let Q : Ideal B := Q0.1
  have hQprime : Q.IsPrime := Q0.2.1
  have hQover : Q.LiesOver p := Q0.2.2
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver p := hQover
  have hramQ : Ideal.ramificationIdx p Q = m := by
    apply Nat.le_antisymm
    · simpa [hfieldDegree] using Ideal.ramificationIdx_le_finrank B K L Q
    · exact minpoly_idx_eisenstein hp0 halpha hf
  have hQmem : Q ∈ IsDedekindDomain.primesOverFinset p B :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mpr ⟨hQprime, hQover⟩
  have hsum : ∑ Q' ∈ IsDedekindDomain.primesOverFinset p B,
      Ideal.ramificationIdx p Q' * Ideal.inertiaDeg p Q' = m := by
    rw [Ideal.sum_ramification_inertia B K L hp0, hfieldDegree]
  have hrest : ∑ Q' ∈ (IsDedekindDomain.primesOverFinset p B).erase Q,
      Ideal.ramificationIdx p Q' * Ideal.inertiaDeg p Q' = 0 := by
    rw [← Finset.add_sum_erase _ _ hQmem] at hsum
    have hfQ : 0 < Ideal.inertiaDeg p Q := Ideal.inertiaDeg_pos p Q
    have hmle : m ≤ m * Ideal.inertiaDeg p Q := Nat.le_mul_of_pos_right m hfQ
    rw [hramQ] at hsum
    omega
  have hunique : ∀ Q' : Ideal B, Q'.IsPrime → Q'.LiesOver p → Q' = Q := by
    intro Q' hQ'prime hQ'over
    by_contra hne
    have hmem : Q' ∈ (IsDedekindDomain.primesOverFinset p B).erase Q := by
      rw [Finset.mem_erase]
      exact ⟨hne, (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mpr ⟨hQ'prime, hQ'over⟩⟩
    have hterm : Ideal.ramificationIdx p Q' * Ideal.inertiaDeg p Q' ≤
        ∑ R ∈ (IsDedekindDomain.primesOverFinset p B).erase Q,
          Ideal.ramificationIdx p R * Ideal.inertiaDeg p R := by
      exact Finset.single_le_sum
        (s := (IsDedekindDomain.primesOverFinset p B).erase Q)
        (f := fun R ↦ Ideal.ramificationIdx p R * Ideal.inertiaDeg p R)
        (fun _ _ ↦ Nat.zero_le _) hmem
    have hramQ'0 : Ideal.ramificationIdx p Q' ≠ 0 := by
      letI : Q'.IsPrime := hQ'prime
      letI : Q'.LiesOver p := hQ'over
      exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q' hp0
    have hinertiaQ'0 : Ideal.inertiaDeg p Q' ≠ 0 := by
      letI : Q'.IsPrime := hQ'prime
      letI : Q'.LiesOver p := hQ'over
      exact Ideal.inertiaDeg_ne_zero p Q'
    rw [hrest] at hterm
    exact (Nat.mul_ne_zero hramQ'0 hinertiaQ'0) (Nat.eq_zero_of_le_zero hterm)
  have hmap0 : p.map (algebraMap A B) ≠ ⊥ := map_ne_bot_of_ne_bot hp0
  have hall : ∀ R ∈ normalizedFactors (p.map (algebraMap A B)), R = Q := by
    intro R hR
    have hRdata := (Ideal.mem_normalizedFactors_iff hmap0).mp hR
    have hRover : R.LiesOver p :=
      (Ideal.mem_primesOver_iff_mem_normalizedFactors B hp0).mpr hR |>.2
    exact hunique R hRdata.1 hRover
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  have hcount : (normalizedFactors (p.map (algebraMap A B))).count Q = m := by
    simpa [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      hmap0 hQprime hQ0] using hramQ
  have hfac : normalizedFactors (p.map (algebraMap A B)) =
      Multiset.replicate m Q := by
    have hcardForm := Multiset.eq_replicate_card.mpr hall
    have hcard : (normalizedFactors (p.map (algebraMap A B))).card = m := by
      rw [hcardForm, Multiset.count_replicate_self] at hcount
      exact hcount
    exact Multiset.eq_replicate.mpr ⟨hcard, hall⟩
  have hpowQ : p.map (algebraMap A B) = Q ^ m := by
    rw [← Ideal.prod_normalizedFactors_eq_self hmap0, hfac, Multiset.prod_replicate]
  have halphaQ : alpha ∈ Q :=
    lies_eisenstein hf (minpoly.monic halpha)
      (minpoly.aeval A alpha)
  have halpha_not_mem_sq : alpha ∉ Q ^ 2 := by
    intro halpha2
    have hterms2 : ∀ i < m,
        algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈ Q ^ (m + 1) := by
      intro i hi
      by_cases him : i + 1 = m
      · rw [him, (minpoly.monic halpha).coeff_natDegree, map_one, one_mul]
        have ha : alpha ^ m ∈ (Q ^ 2) ^ m := Ideal.pow_mem_pow halpha2 m
        rw [← pow_mul] at ha
        exact (Ideal.pow_le_pow_right (by omega)) ha
      · have hcoeff : F.coeff (i + 1) ∈ p := hf.coeff_mem him
        have hcoeff' : algebraMap A B (F.coeff (i + 1)) ∈ Q ^ m := by
          rw [← hpowQ]
          exact Ideal.mem_map_of_mem (algebraMap A B) hcoeff
        have hpow : alpha ^ (i + 1) ∈ Q ^ (i + 1) :=
          Ideal.pow_mem_pow halphaQ (i + 1)
        have hmul : algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈
            Q ^ m * Q ^ (i + 1) := Ideal.mul_mem_mul hcoeff' hpow
        rw [← pow_add] at hmul
        exact (Ideal.pow_le_pow_right (by omega)) hmul
    have hsum2 : ∑ i ∈ Finset.range m,
        algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) ∈ Q ^ (m + 1) :=
      Ideal.sum_mem _ fun i hi ↦ hterms2 i (Finset.mem_range.mp hi)
    have heval2 : algebraMap A B (F.coeff 0) +
        ∑ i ∈ Finset.range m,
          algebraMap A B (F.coeff (i + 1)) * alpha ^ (i + 1) = 0 := by
      have hroot := minpoly.aeval A alpha
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at hroot
      simpa [F, m, Algebra.smul_def, add_comm] using hroot
    have hconst2 : algebraMap A B (F.coeff 0) ∈ Q ^ (m + 1) := by
      rw [eq_neg_of_add_eq_zero_left heval2]
      simpa only [Ideal.neg_mem_iff] using hsum2
    have hc0 : F.coeff 0 ≠ 0 := by
      intro hc
      apply hf.notMem
      rw [hc]
      exact Ideal.zero_mem _
    have hspan0 : Ideal.span ({F.coeff 0} : Set A) ≠ ⊥ :=
      mt Ideal.span_singleton_eq_bot.mp hc0
    have hpirr : Irreducible p :=
      (Ideal.prime_of_isPrime hp0 (inferInstance : p.IsPrime)).irreducible
    have hQirr : Irreducible Q :=
      (Ideal.prime_of_isPrime hQ0 hQprime).irreducible
    have hbase : emultiplicity p (Ideal.span ({F.coeff 0} : Set A)) = 1 := by
      apply emultiplicity_eq_of_dvd_of_not_dvd
      · rw [pow_one, Ideal.dvd_span_singleton]
        exact hf.mem hm0
      · simpa only [Ideal.dvd_span_singleton] using hf.notMem
    have hmapem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
      (S := B) hspan0 hpirr hQirr hQ0
    have hmapem' :
        emultiplicity Q (Ideal.span ({algebraMap A B (F.coeff 0)} : Set B)) = m := by
      simpa [Ideal.map_span, hbase, hramQ] using hmapem
    have hdiv : Q ^ (m + 1) ∣
        Ideal.span ({algebraMap A B (F.coeff 0)} : Set B) :=
      Ideal.dvd_span_singleton.mpr hconst2
    have hle := le_emultiplicity_of_pow_dvd hdiv
    rw [hmapem'] at hle
    exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m))) hle
  have hIQ : I ≤ Q := root_lies_eisenstein
    hf (minpoly.monic halpha) (minpoly.aeval A alpha)
  have hIeq : I = Q := by
    have hmapI : p.map (algebraMap A B) ≤ I := le_sup_left
    have hI0 : I ≠ ⊥ := by
      intro hI
      apply hmap0
      exact le_bot_iff.mp (hmapI.trans (le_of_eq hI))
    have hInot2 : ¬I ≤ Q ^ 2 := by
      intro hle
      apply halpha_not_mem_sq
      exact hle ((show Ideal.span ({alpha} : Set B) ≤ I from le_sup_right)
        (Ideal.mem_span_singleton_self alpha))
    have hcountI : (normalizedFactors I).count Q = 1 := by
      apply Ideal.count_normalizedFactors_eq
      · simpa only [pow_one] using hIQ
      · simpa only [Nat.reduceAdd] using hInot2
    have hallI : ∀ R ∈ normalizedFactors I, R = Q := by
      intro R hR
      have hRdata := (Ideal.mem_normalizedFactors_iff hI0).mp hR
      have hmapR : p.map (algebraMap A B) ≤ R := hmapI.trans hRdata.2
      have hRover : R.LiesOver p :=
        (Ideal.liesOver_iff_dvd_map hRdata.1.ne_top).mpr
          (Ideal.dvd_iff_le.mpr hmapR)
      exact hunique R hRdata.1 hRover
    have hfacI : normalizedFactors I = Multiset.replicate 1 Q := by
      have hcardForm := Multiset.eq_replicate_card.mpr hallI
      have hcard : (normalizedFactors I).card = 1 := by
        rw [hcardForm, Multiset.count_replicate_self] at hcountI
        exact hcountI
      exact Multiset.eq_replicate.mpr ⟨hcard, hallI⟩
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, hfacI, Multiset.prod_replicate, pow_one]
  have hIprime : I.IsPrime := hIeq.symm ▸ hQprime
  have hpowI : p.map (algebraMap A B) = I ^ m := hIeq ▸ hpowQ
  have hramI : Ideal.ramificationIdx p I = m := hIeq ▸ hramQ
  have huniqueI : ∀ Q' : Ideal B, Q'.IsPrime → Q'.LiesOver p → Q' = I := by
    intro Q' hQ'prime hQ'over
    exact (hunique Q' hQ'prime hQ'over).trans hIeq.symm
  exact ⟨by simpa [I] using hIprime, by simpa [I, F, m] using hpowI,
    by simpa [I, F, m] using hramI,
    fun Q' hQ'prime hQ'over ↦ by simpa [I] using huniqueI Q' hQ'prime hQ'over⟩

/-- **Proposition 3.53.** An Eisenstein polynomial is irreducible and its root generates a
totally ramified field extension. The field-generation hypothesis says precisely that
`L = K(alpha)`; it imposes no monogenicity condition on the integral closure `B`. -/
theorem eisenstein_total_ramification
    (A B K L : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    {p : Ideal A} [p.IsPrime] (hp0 : p ≠ ⊥)
    {f : A[X]} (hf : f.IsEisensteinAt p) (hmonic : f.Monic)
    (hdeg : 0 < f.natDegree)
    {alpha : B} (halpha : aeval alpha f = 0)
    (hgen : IntermediateField.adjoin K ({algebraMap B L alpha} : Set L) = ⊤) :
    let P := p.map (algebraMap A B) ⊔ Ideal.span {alpha}
    P.IsPrime ∧
      p.map (algebraMap A B) = P ^ f.natDegree ∧
      Ideal.ramificationIdx p P = f.natDegree ∧
      ∀ Q : Ideal B, Q.IsPrime → Q.LiesOver p → Q = P := by
  have halpha_int : IsIntegral A alpha := ⟨f, hmonic, halpha⟩
  have hirr : Irreducible f := eisenstein_irreducible (inferInstance : p.IsPrime)
    hf hmonic hdeg
  have hdvd : minpoly A alpha ∣ f :=
    minpoly.isIntegrallyClosed_dvd halpha_int halpha
  have hmin : minpoly A alpha = f :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic halpha_int) hmonic
      ((minpoly.irreducible halpha_int).associated_of_dvd hirr hdvd)
  simpa [hmin] using
    eisenstein_total_top
      A B K L hp0 halpha_int (hmin.symm ▸ hf) hgen

end Towers.NumberTheory.Milne
