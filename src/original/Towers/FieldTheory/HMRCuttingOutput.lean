import Towers.FieldTheory.HMRInitialCutting


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers
namespace TBluepr
namespace STBuild

/- Compatibility name from the original `Erdos90/I.lean` construction. -/
theorem initial_rank_alpha :
    (initialGeneratorRank : ℝ) > initialAlpha := by
  rw [initial_alpha_four]
  have h5 : (5 : ℝ) ≤ initialGeneratorRank := by
    exact_mod_cast initial_rank_five
  linarith

theorem hmr_cutting_criterion
    (c : HParame)
    (hCrit : HMRGSCuttingCriterion c)
    {k : ℕ}
    (hk : 2 ≤ k)
    (hkTail : HMRCuttingBound c k)
    (x : HMRCutSequence)
    (hAdm : HMRCutAdmissible k x) :
    Infinite (hmrCutQuotient (K := ℚ) (KS := initialProExtension) x) := by
  exact hCrit hk hkTail x hAdm

/- Combining the depth choice and the cutting criterion upgrades the numerical GS data to the
packaged predicate `HMRCuttingLevel k`. This is the exact interface the later theorems
use, so the remaining development no longer needs to talk about `t₀` or `ε` explicitly. -/
theorem hmr_cutting_level
    (c : HParame)
    (hCrit : HMRGSCuttingCriterion c)
    {k : ℕ}
    (hk : 2 ≤ k)
    (hkTail : HMRCuttingBound c k) :
    HMRCuttingLevel k := by
  refine ⟨hk, ?_⟩
  intro x hZas
  exact
    hmr_cutting_criterion
      c
      hCrit
      hk
      hkTail
      x
      hZas

/- It is convenient to package the previous two existential steps together: the initial tower has
some strict GS witness together with a depth at which the geometric tail is already small. This
keeps the final existence proof short and exposes a clean intermediate target for later passes. -/
theorem initial_hmr_cutting :
    ∃ (c : HParame) (k : ℕ),
      2 ≤ k ∧ HMRCuttingBound c k := by
  let c : HParame :=
    Classical.choice hmr_gs_parameters
  rcases hmr_cutting_bound c with ⟨k, hk, hkTail⟩
  exact ⟨c, k, hk, hkTail⟩

/- Choose a level `k ≥ 2` for which the HMR depth argument applies uniformly to every later
sequence of Frobenius elements. This is the `k` singled out at the beginning of the TeX proof. -/
theorem initial_cutting_level :
    ∃ k : ℕ, HMRCuttingLevel k := by
  rcases initial_hmr_cutting with ⟨c, k, hk, hkTail⟩
  have hCrit : HMRGSCuttingCriterion c :=
    cutting_criterion_parameters c
  exact
    ⟨k, hmr_cutting_level c hCrit hk hkTail⟩

/- A named witness for the cutting level chosen for the initial tower. Keeping it explicit makes
later lemmas easier to state without repeatedly unpacking the existential witness above. -/
noncomputable def hmrCuttingLevel : ℕ :=
  Classical.choose initial_cutting_level

/- The named cutting level satisfies the full depth-choice package. -/
theorem hmr_cutting_spec :
    HMRCuttingLevel hmrCuttingLevel := by
  exact Classical.choose_spec initial_cutting_level

/- In particular, the chosen cutting level is at least `2`. -/
theorem hmr_cutting_two :
    2 ≤ hmrCuttingLevel := by
  exact hmr_cutting_spec.1

/- Once the cutting level is fixed, the infinitude statement is exactly the depth-choice
conclusion applied to the sequence `x`. This isolates the first half of the final theorem
from the later local splitting argument. -/
theorem hmr_cut_infinite
    {k : ℕ} (hk : HMRCuttingLevel k)
    (x : ℕ → initialGaloisGroup)
    (hZas : ∀ i, x i ∈ initialZassenhausFiltration (k + i)) :
    Infinite (hmrCutQuotient (K := ℚ) (KS := initialProExtension) x) := by
  exact hk.2 x hZas

/- Fixing one index `i`, the local part of the TeX proof runs as follows:
1. descend unramifiedness from `Q_S^(3)/ℚ` to the fixed field `L^N/ℚ`,
2. push Frobenius from `Gal(L/ℚ)` to the quotient `Gal(L^N/ℚ)`,
3. use `x i ∈ N` to see that the quotient Frobenius is trivial,
4. conclude that `𝔮_i` splits completely in `L^N/ℚ`.

We isolate that entire fixed-index argument here so the main theorem only has to combine it
with the separate infinitude input. -/
abbrev InitialHMRSplitting (x : ℕ → initialGaloisGroup) :=
  FiniteGaloisIntermediateField ℚ
    (hmrFixedField (K := ℚ) (KS := initialProExtension) x)

/- The finite-level splitting criterion we need later is exactly the finite-place version of
“unramified plus trivial Frobenius implies complete splitting”. Isolating it here keeps the
subextension-level HMR argument from having to reopen the arithmetic criterion each time. -/
theorem splits_completely_frobenius
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E]
    (v : FinitePlace K)
    (hUnr : UnramifiedPlaceField (K := K) (E := E) v)
    (hFrob :
      FrobeniusPlaceField (K := K) (E := E) v (1 : Gal(E/K))) :
    SplitsCompletelyField (K := K) (E := E) v := by
  letI : IsGaloisGroup Gal(E / K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E / K))
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers E)
      (K := K) (L := E)
  let pI : Ideal (NumberField.RingOfIntegers K) := v.maximalIdeal.asIdeal
  have hpI0 : pI ≠ ⊥ := by
    simpa [pI] using v.maximalIdeal.ne_bot
  letI : pI.IsMaximal := by
    simpa [pI] using v.maximalIdeal.isMaximal
  rcases hFrob with ⟨Q, hQFrob⟩
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver pI := Q.2.2
  have hQunr : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.1 := hUnr Q.1
  have hQ0 : Q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpI0 Q.1
  letI : Q.1.IsMaximal := Ideal.IsPrime.isMaximal (show Q.1.IsPrime by infer_instance) hQ0
  let p : Ideal (NumberField.RingOfIntegers K) := Q.1.under (NumberField.RingOfIntegers K)
  have hp0 : p ≠ ⊥ := by
    exact mt Ideal.eq_bot_of_comap_eq_bot hQ0
  have hp_eq : pI = p := by
    exact Ideal.LiesOver.over (P := Q.1) (p := pI)
  have hpprime : p.IsPrime := inferInstance
  letI : p.IsMaximal := hpprime.isMaximal hp0
  letI : Field ((NumberField.RingOfIntegers K) ⧸ p) := Ideal.Quotient.field p
  haveI : Finite ((NumberField.RingOfIntegers K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI : Fintype ((NumberField.RingOfIntegers K) ⧸ p) :=
    Fintype.ofFinite ((NumberField.RingOfIntegers K) ⧸ p)
  letI : Field ((NumberField.RingOfIntegers E) ⧸ Q.1) := Ideal.Quotient.field Q.1
  haveI : Finite ((NumberField.RingOfIntegers E) ⧸ Q.1) :=
    Ideal.finiteQuotientOfFreeOfNeBot Q.1 hQ0
  have hPe : Ideal.ramificationIdx pI Q.1 = 1 := by
    have hPe' : Ideal.ramificationIdx p Q.1 = 1 := by
      simpa [p] using
        (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
          (R := NumberField.RingOfIntegers K) (p := Q.1) hQ0)
    simpa [hp_eq] using hPe'
  have hrestrict_id : hQFrob.restrict = 1 := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgHom.IsArithFrobAt.restrict_mk]
    have h1 :
        (MulSemiringAction.toAlgHom
          (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers E)
          (1 : Gal(E / K))) x = x := by
      simp
    simp
  have hrestrict_frob :
      hQFrob.restrict =
        FiniteField.frobeniusAlgHom
          ((NumberField.RingOfIntegers K) ⧸ p)
          ((NumberField.RingOfIntegers E) ⧸ Q.1) := by
    ext x
    simp [p, AlgHom.IsArithFrobAt.restrict_apply, Nat.card_eq_fintype_card]
  have hfinrank :
      Module.finrank ((NumberField.RingOfIntegers K) ⧸ p)
        ((NumberField.RingOfIntegers E) ⧸ Q.1) = 1 := by
    have horder :
        orderOf
            (FiniteField.frobeniusAlgHom
              ((NumberField.RingOfIntegers K) ⧸ p)
              ((NumberField.RingOfIntegers E) ⧸ Q.1)) = 1 := by
      rw [← hrestrict_frob, hrestrict_id]
      exact orderOf_one
    rw [FiniteField.orderOf_frobeniusAlgHom] at horder
    exact horder
  have hPf : Ideal.inertiaDeg pI Q.1 = 1 := by
    calc
      Ideal.inertiaDeg pI Q.1 = Ideal.inertiaDeg p Q.1 := by
        simp [hp_eq]
      _ = Module.finrank ((NumberField.RingOfIntegers K) ⧸ p)
            ((NumberField.RingOfIntegers E) ⧸ Q.1) := by
          exact Ideal.inertiaDeg_algebraMap (p := p) (P := Q.1)
      _ = 1 := hfinrank
  have hramIn : pI.ramificationIdxIn (NumberField.RingOfIntegers E) = 1 := by
    calc
      pI.ramificationIdxIn (NumberField.RingOfIntegers E)
        = Ideal.ramificationIdx pI Q.1 := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := pI) (P := Q.1) (G := Gal(E / K))
      _ = 1 := hPe
  have hinIn : pI.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    calc
      pI.inertiaDegIn (NumberField.RingOfIntegers E)
        = Ideal.inertiaDeg pI Q.1 := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := pI) (P := Q.1) (G := Gal(E / K))
      _ = 1 := hPf
  refine ⟨?_, ?_⟩
  · have hcount :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        (p := pI) hpI0 (NumberField.RingOfIntegers E) (Gal(E / K))
    have hcardG : Nat.card Gal(E / K) = Module.finrank K E := by
      simpa using IsGaloisGroup.card_eq_finrank (G := Gal(E / K)) (K := K) (L := E)
    rw [hcardG, hramIn, hinIn] at hcount
    simpa [pI] using hcount
  · intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver pI := hP.2
    constructor
    · calc
        Ideal.ramificationIdx pI P
          = Ideal.ramificationIdx pI Q.1 := by
              exact Ideal.ramificationIdx_eq_of_isGaloisGroup
                (p := pI) (P := P) (Q := Q.1) (G := Gal(E / K))
        _ = 1 := hPe
    · calc
        Ideal.inertiaDeg pI P
          = Ideal.inertiaDeg pI Q.1 := by
              exact Ideal.inertiaDeg_eq_of_isGaloisGroup
                (p := pI) (P := P) (Q := Q.1) (G := Gal(E / K))
        _ = 1 := hPf

/- Every chosen cut generator belongs to the closed normal subgroup generated by the entire
sequence. This is the group-theoretic core of the TeX line “`x_i ∈ N`”. -/
theorem initial_hmr_cut
    (x : ℕ → initialGaloisGroup) (i : ℕ) :
    x i ∈ hmrCutSubgroup (K := ℚ) (KS := initialProExtension) x := by
  change x i ∈ (Subgroup.normalClosure (Set.range x)).topologicalClosure
  exact subset_closure (Subgroup.subset_normalClosure ⟨i, rfl⟩)

/- Since the fixed field is defined from that closed normal subgroup, every chosen generator lies
in its fixing subgroup. This is the precise formal content of the TeX step “`x_i` dies in the
quotient `Gal(L^N/ℚ)`”. -/
theorem hmr_cut_fixing
    (x : ℕ → initialGaloisGroup) (i : ℕ) :
    x i ∈
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).fixingSubgroup := by
  have hxcut :
      x i ∈ hmrCutSubgroup (K := ℚ) (KS := initialProExtension) x :=
    initial_hmr_cut x i
  have hfixEq :
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).fixingSubgroup =
        hmrCutSubgroup (K := ℚ) (KS := initialProExtension) x := by
    simpa [hmrFixedField, hmrCutClosed] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (hmrCutClosed (K := ℚ) (KS := initialProExtension) x))
  have hfix :
      x i ∈
        (hmrFixedField (K := ℚ) (KS := initialProExtension) x).fixingSubgroup := by
    rw [hfixEq]
    exact hxcut
  exact hfix

/- Therefore every chosen generator fixes every element of every finite Galois layer inside the
cut fixed field. This packages the pointwise triviality information needed later when converting
descended Frobenius elements into the identity. -/
theorem hmr_cut_fixes
    (x : ℕ → initialGaloisGroup) (i : ℕ)
    (E : @FiniteGaloisIntermediateField ℚ
      (↥(hmrFixedField (K := ℚ) (KS := initialProExtension) x))
      Rat.instField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).toField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).algebra') :
    ∀ y : E, x i y.1.1 = y.1.1 := by
  have hfix :
      x i ∈
        (hmrFixedField (K := ℚ) (KS := initialProExtension) x).fixingSubgroup :=
    hmr_cut_fixing x i
  intro y
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (K := hmrFixedField (K := ℚ) (KS := initialProExtension) x)
      (σ := x i)).1 hfix y.1.1 y.1.2

theorem initial_hmr_norm (v : FinitePlace ℚ) :
    Rat.HeightOneSpectrum.natGenerator v.maximalIdeal = finitePlaceNorm v := by
  let I : Ideal (𝓞 ℚ) := v.maximalIdeal.asIdeal
  let J : Ideal ℤ := I.map Rat.ringOfIntegersEquiv
  have hint : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hcard :
      Ideal.absNorm J = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
    let e : (𝓞 ℚ) ⧸ I ≃+* ℤ ⧸ J :=
      Ideal.quotientEquiv I J Rat.ringOfIntegersEquiv rfl
    exact Nat.card_congr e.toEquiv.symm
  have hspan :
      J = Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v.maximalIdeal : ℤ)} : Set ℤ) := by
    simpa [I, J, hint] using
      (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v.maximalIdeal).symm
  calc
    Rat.HeightOneSpectrum.natGenerator v.maximalIdeal = Ideal.absNorm J := by
      rw [hspan, Ideal.absNorm_apply]
      simpa [Submodule.cardQuot_apply] using
        (Int.card_ideal_quot (Rat.HeightOneSpectrum.natGenerator v.maximalIdeal)).symm
    _ = Ideal.absNorm I := hcard
    _ = finitePlaceNorm v := by
      rfl

theorem initial_hmr_integers (v : FinitePlace ℚ) :
    v.maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv =
      Ideal.rationalPrimeIdeal (finitePlaceNorm v) := by
  have hint : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  calc
    v.maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv
      = Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v.maximalIdeal : ℤ)} : Set ℤ) := by
          simpa [hint] using
            (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v.maximalIdeal).symm
    _ = Ideal.rationalPrimeIdeal (finitePlaceNorm v) := by
          rw [initial_hmr_norm v]
          rfl

theorem initial_hmr_prime (v : FinitePlace ℚ) :
    Nat.Prime (finitePlaceNorm v) := by
  rw [← initial_hmr_norm v]
  exact Rat.HeightOneSpectrum.prime_natGenerator v.maximalIdeal

attribute [-instance] DivisionRing.toRatAlgebra in
theorem initial_hmr_rational
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (v : FinitePlace ℚ)
    (hUnr : UnramifiedPlaceField (K := ℚ) (E := E) v) :
    RationalPrimeUnramified (S := 𝓞 E) (finitePlaceNorm v) := by
  letI : IsScalarTower ℤ ℚ E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ E (𝓞 E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ℚ (𝓞 ℚ)
  letI : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := ℤ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  letI : IsGaloisGroup Gal(ℚ/ℚ) ℤ (𝓞 ℚ) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(ℚ/ℚ)) (A := ℤ)
      (B := 𝓞 ℚ) (K := ℚ) (L := ℚ)
  letI : IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := 𝓞 ℚ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  let pI : Ideal (𝓞 ℚ) := v.maximalIdeal.asIdeal
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal (finitePlaceNorm v)
  have hq : Nat.Prime (finitePlaceNorm v) := initial_hmr_prime v
  have hpI0 : pI ≠ ⊥ := by
    simpa [pI] using v.maximalIdeal.ne_bot
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have hpmap : pI.map e0 = qI := by
    simpa [pI, qI] using initial_hmr_integers v
  have hqover : qI.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    rfl
  letI : qI.LiesOver qI := hqover
  have hpover : pI.LiesOver qI := by
    have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
      Subsingleton.elim _ _
    rw [Ideal.liesOver_iff]
    change qI = pI.comap (algebraMap ℤ (𝓞 ℚ))
    rw [halg]
    calc
      qI = pI.map e0.toRingHom := by
        simpa using hpmap.symm
      _ = pI.comap e0.symm.toRingHom := by
        exact (Ideal.comap_symm (I := pI) e0.toRingEquiv).symm
  letI : pI.LiesOver qI := hpover
  letI : pI.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := pI)
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := pI.nonempty_primesOver (S := 𝓞 E)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver pI := hPover
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpI0 P
  have hramP : Ideal.ramificationIdx pI P = 1 := by
    have hramP' :
        Ideal.ramificationIdx (Ideal.under (𝓞 ℚ) P) P = 1 :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
        (R := 𝓞 ℚ) (S := 𝓞 E) (p := P) hP0).1 (hUnr P)
    simpa [Ideal.LiesOver.over (P := P) (p := pI)] using hramP'
  have hramPIn : pI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      pI.ramificationIdxIn (𝓞 E)
        = Ideal.ramificationIdx pI P := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := pI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hramP
  have hramSelf : Ideal.ramificationIdx qI qI = 1 := by
    have hqItop' : qI ≠ ⊤ := Ideal.IsPrime.ne_top (show qI.IsPrime by infer_instance)
    have hqItop : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊤ := by
      simpa using hqItop'
    have hqI0' : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊥ := by
      simpa using hqI0
    simpa using
      (Ideal.ramificationIdx_map_self_eq_one (R := ℤ) (S := ℤ)
        (p := qI) hqItop hqI0')
  have hramBaseIn : qI.ramificationIdxIn (𝓞 ℚ) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 ℚ)
        = Ideal.ramificationIdx qI pI := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := pI) (G := Gal(ℚ/ℚ))
      _ = Ideal.ramificationIdx qI (pI.map e0) := by
            symm
            exact Ideal.ramificationIdx_map_eq (p := qI) (P := pI) e0
      _ = Ideal.ramificationIdx qI qI := by
            rw [hpmap]
      _ = 1 := hramSelf
  have hramEIn : qI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 E)
        = qI.ramificationIdxIn (𝓞 ℚ) * pI.ramificationIdxIn (𝓞 E) := by
            symm
            exact Ideal.ramificationIdxIn_mul_ramificationIdxIn'
              (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
      _ = 1 := by rw [hramBaseIn, hramPIn]
  intro Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver qI := hQ.2
  calc
    Ideal.ramificationIdx qI Q
      = qI.ramificationIdxIn (𝓞 E) := by
          symm
          exact Ideal.ramificationIdxIn_eq_ramificationIdx
            (p := qI) (P := Q) (G := Gal(E/ℚ))
    _ = 1 := hramEIn

attribute [-instance] DivisionRing.toRatAlgebra in
theorem initial_hmr_unramified
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (v : FinitePlace ℚ)
    (hUnr : RationalPrimeUnramified (S := 𝓞 E) (finitePlaceNorm v)) :
    UnramifiedPlaceField (K := ℚ) (E := E) v := by
  letI : IsScalarTower ℤ ℚ E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ E (𝓞 E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ℚ (𝓞 ℚ)
  letI : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := ℤ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  letI : IsGaloisGroup Gal(ℚ/ℚ) ℤ (𝓞 ℚ) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(ℚ/ℚ)) (A := ℤ)
      (B := 𝓞 ℚ) (K := ℚ) (L := ℚ)
  letI : IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := 𝓞 ℚ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  let pI : Ideal (𝓞 ℚ) := v.maximalIdeal.asIdeal
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal (finitePlaceNorm v)
  have hq : Nat.Prime (finitePlaceNorm v) := initial_hmr_prime v
  have hpI0 : pI ≠ ⊥ := by
    simpa [pI] using v.maximalIdeal.ne_bot
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have hpmap : pI.map e0 = qI := by
    simpa [pI, qI] using initial_hmr_integers v
  have hqover : qI.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    rfl
  letI : qI.LiesOver qI := hqover
  have hpover : pI.LiesOver qI := by
    have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
      Subsingleton.elim _ _
    rw [Ideal.liesOver_iff]
    change qI = pI.comap (algebraMap ℤ (𝓞 ℚ))
    rw [halg]
    calc
      qI = pI.map e0.toRingHom := by
        simpa using hpmap.symm
      _ = pI.comap e0.symm.toRingHom := by
        exact (Ideal.comap_symm (I := pI) e0.toRingEquiv).symm
  letI : pI.LiesOver qI := hpover
  letI : pI.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := pI)
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ := qI.nonempty_primesOver (S := 𝓞 E)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver qI := hQover
  have hQmem : Q ∈ Ideal.primesOver qI (𝓞 E) := ⟨hQprime, hQover⟩
  have hramQ : Ideal.ramificationIdx qI Q = 1 := hUnr Q hQmem
  have hramEIn : qI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 E)
        = Ideal.ramificationIdx qI Q := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := Q) (G := Gal(E/ℚ))
      _ = 1 := hramQ
  have hramSelf : Ideal.ramificationIdx qI qI = 1 := by
    have hqItop' : qI ≠ ⊤ := Ideal.IsPrime.ne_top (show qI.IsPrime by infer_instance)
    have hqItop : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊤ := by
      simpa using hqItop'
    have hqI0' : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊥ := by
      simpa using hqI0
    simpa using
      (Ideal.ramificationIdx_map_self_eq_one (R := ℤ) (S := ℤ)
        (p := qI) hqItop hqI0')
  have hramBaseIn : qI.ramificationIdxIn (𝓞 ℚ) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 ℚ)
        = Ideal.ramificationIdx qI pI := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := pI) (G := Gal(ℚ/ℚ))
      _ = Ideal.ramificationIdx qI (pI.map e0) := by
            symm
            exact Ideal.ramificationIdx_map_eq (p := qI) (P := pI) e0
      _ = Ideal.ramificationIdx qI qI := by
            rw [hpmap]
      _ = 1 := hramSelf
  have hramPIn : pI.ramificationIdxIn (𝓞 E) = 1 := by
    have hmul :
        qI.ramificationIdxIn (𝓞 E) =
          qI.ramificationIdxIn (𝓞 ℚ) * pI.ramificationIdxIn (𝓞 E) := by
      symm
      exact Ideal.ramificationIdxIn_mul_ramificationIdxIn'
        (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
    rw [hramEIn, hramBaseIn] at hmul
    simpa using hmul.symm
  intro P _ _
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpI0 P
  have hramP : Ideal.ramificationIdx (Ideal.under (𝓞 ℚ) P) P = 1 := by
    have hramP' : Ideal.ramificationIdx pI P = 1 := by
      calc
        Ideal.ramificationIdx pI P
          = pI.ramificationIdxIn (𝓞 E) := by
              symm
              exact Ideal.ramificationIdxIn_eq_ramificationIdx
                (p := pI) (P := P) (G := Gal(E/ℚ))
        _ = 1 := hramPIn
    simpa [Ideal.LiesOver.over (P := P) (p := pI)] using hramP'
  exact
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := 𝓞 ℚ) (S := 𝓞 E) (p := P) hP0).2 hramP

/- Unramifiedness of `𝔮_i` in the ambient extension descends to every finite Galois layer of the
cut fixed field. This isolates the first local arithmetic bridge from the Frobenius argument. -/
attribute [-instance] DivisionRing.toRatAlgebra in
theorem initial_hmr_split
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (i : ℕ) (E : @FiniteGaloisIntermediateField ℚ
      (↥(hmrFixedField (K := ℚ) (KS := initialProExtension) x))
      Rat.instField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).toField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).algebra') :
    UnramifiedPlaceField (K := ℚ) (E := E) (𝔮 i) := by
  let E' : IntermediateField ℚ initialProExtension :=
    IntermediateField.lift E.toIntermediateField
  let eE : E ≃ₐ[ℚ] ↥E' := IntermediateField.liftAlgEquiv E.toIntermediateField
  letI : FiniteDimensional ℚ ↥E' :=
    FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.surjective
  letI : NumberField ↥E' := NumberField.of_module_finite ℚ ↥E'
  have hE'_gal : IsGalois ℚ ↥E' := IsGalois.of_algEquiv eE
  let Efg : FiniteGaloisIntermediateField ℚ initialProExtension :=
    @FiniteGaloisIntermediateField.mk ℚ initialProExtension _ _ _ E' inferInstance hE'_gal
  have hE'_unr : UnramifiedPlaceField (K := ℚ) (E := ↥E') (𝔮 i) :=
    hUnr i Efg
  have hE'_rat :
      RationalPrimeUnramified (S := 𝓞 ↥E') (finitePlaceNorm (𝔮 i)) :=
    initial_hmr_rational
      (v := 𝔮 i) hE'_unr
  have hE_rat :
      RationalPrimeUnramified (S := 𝓞 E) (finitePlaceNorm (𝔮 i)) :=
    rational_unramified_alg eE.symm hE'_rat
  exact
    initial_hmr_unramified
      (v := 𝔮 i) hE_rat

/- For one fixed finite layer of the cut field, the local HMR argument is now completely broken
into three inputs: unramified descent, Frobenius descent, and the fact that the chosen cut
generator fixes the layer pointwise. We package those ingredients into the finite-level
splitting conclusion needed by the ambient theorem. -/
set_option maxHeartbeats 800000 in
-- Transporting splitting across the lifted finite layer and its integer-ring equivalence
-- requires more reduction than the default budget.
set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing the transported scalar towers also exceeds the default instance budget.
attribute [-instance] DivisionRing.toRatAlgebra in
theorem hmr_split_layer
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (hFrob : ∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i))
    (i : ℕ) (E : @FiniteGaloisIntermediateField ℚ
      (↥(hmrFixedField (K := ℚ) (KS := initialProExtension) x))
      Rat.instField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).toField
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x).algebra') :
    SplitsCompletelyField (K := ℚ) (E := E) (𝔮 i) := by
  let e : E ≃ₐ[ℚ]
      IntermediateField.lift
        (F := hmrFixedField (K := ℚ) (KS := initialProExtension) x) E :=
    IntermediateField.liftAlgEquiv
      (E := hmrFixedField (K := ℚ) (KS := initialProExtension) x) E
  letI :
      FiniteDimensional ℚ
        ↥(IntermediateField.lift
          (F := hmrFixedField (K := ℚ) (KS := initialProExtension) x) E) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  letI :
      IsGalois ℚ
        ↥(IntermediateField.lift
          (F := hmrFixedField (K := ℚ) (KS := initialProExtension) x) E) :=
    IsGalois.of_algEquiv e
  let E' : FiniteGaloisIntermediateField ℚ initialProExtension :=
    .mk (IntermediateField.lift
      (F := hmrFixedField (K := ℚ) (KS := initialProExtension) x) E)
  letI : NumberField E' := instNumberIntermediate E'
  let eInt :
      NumberField.RingOfIntegers E ≃ₐ[NumberField.RingOfIntegers ℚ]
        NumberField.RingOfIntegers E' :=
    NumberField.RingOfIntegers.mapAlgEquiv e
  have hsplit' : SplitsCompletelyField (K := ℚ) (E := E') (𝔮 i) := by
    refine
      splits_completely_frobenius
        (K := ℚ) (E := E') (v := 𝔮 i)
        ?_ ?_
    · exact hUnr i E'
    · have hx_fixed :
          x i ∈
            ((E' : IntermediateField ℚ initialProExtension).fixingSubgroup) := by
        refine IntermediateField.fixingSubgroup_antitone ?_
          (hmr_cut_fixing (x := x) i)
        simpa using
          (IntermediateField.lift_le
            (F := hmrFixedField (K := ℚ) (KS := initialProExtension) x)
            E.toIntermediateField)
      have hx_ker :
          x i ∈
            (AlgEquiv.restrictNormalHom
              (E' : IntermediateField ℚ initialProExtension)).ker := by
        rw [IntermediateField.restrictNormalHom_ker
          (E := (E' : IntermediateField ℚ initialProExtension))]
        exact hx_fixed
      have htriv :
          AlgEquiv.restrictNormalHom
              (E' : IntermediateField ℚ initialProExtension) (x i) =
            (1 : Gal(E'/ℚ)) := by
        simpa using hx_ker
      simpa [htriv] using hFrob i E'
  let primeEquiv :
      Ideal.primesOver (𝔮 i).maximalIdeal.asIdeal (NumberField.RingOfIntegers E) ≃
        Ideal.primesOver (𝔮 i).maximalIdeal.asIdeal (NumberField.RingOfIntegers E') :=
    { toFun := fun P => Ideal.primesOver.mk _ (P.1.map eInt)
      invFun := fun P => Ideal.primesOver.mk _ (P.1.comap eInt)
      left_inv := by
        intro P
        apply Subtype.ext
        change
          Ideal.comap
              (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                NumberField.RingOfIntegers E')
              (Ideal.map
                (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                  NumberField.RingOfIntegers E') ↑P) =
            ↑P
        convert
          (Ideal.comap_of_equiv
            (I := (P : Ideal (NumberField.RingOfIntegers E)))
            (f := eInt.toRingEquiv)) using 1
        · exact congrArg
            (Ideal.comap
              (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                NumberField.RingOfIntegers E'))
            (Ideal.map_comap_of_equiv
              (I := (P : Ideal (NumberField.RingOfIntegers E)))
              (f := eInt.toRingEquiv))
      right_inv := by
        intro P
        apply Subtype.ext
        change
          Ideal.map
              (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                NumberField.RingOfIntegers E')
              (Ideal.comap
                (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                  NumberField.RingOfIntegers E') ↑P) =
            ↑P
        convert
          (Ideal.map_of_equiv
            (I := (P : Ideal (NumberField.RingOfIntegers E')))
            (f := eInt.toRingEquiv.symm)) using 1
        · exact congrArg
            (Ideal.map
              (eInt.toRingEquiv : NumberField.RingOfIntegers E →+*
                NumberField.RingOfIntegers E'))
            ((Ideal.map_symm
              (I := (P : Ideal (NumberField.RingOfIntegers E')))
              (f := eInt.toRingEquiv)).symm)
        }
  rcases hsplit' with ⟨hsplit'_card, hsplit'_data⟩
  refine ⟨?_, ?_⟩
  · calc
      (Ideal.primesOver (𝔮 i).maximalIdeal.asIdeal
          (NumberField.RingOfIntegers E)).ncard
        =
          (Ideal.primesOver (𝔮 i).maximalIdeal.asIdeal
            (NumberField.RingOfIntegers E')).ncard := by
              simpa using Set.ncard_congr' primeEquiv
      _ = Module.finrank ℚ E' := hsplit'_card
      _ = Module.finrank ℚ E := by
            simpa using e.toLinearEquiv.finrank_eq.symm
  · intro P hP
    have hP' :=
      hsplit'_data (primeEquiv ⟨P, hP⟩) (primeEquiv ⟨P, hP⟩).2
    constructor
    · have hram_map :
          Ideal.ramificationIdx (𝔮 i).maximalIdeal.asIdeal (P.map eInt) =
            Ideal.ramificationIdx (𝔮 i).maximalIdeal.asIdeal P := by
        simpa using
          (Ideal.ramificationIdx_map_eq
            (p := (𝔮 i).maximalIdeal.asIdeal) (P := P) eInt)
      rw [← hram_map]
      simpa [primeEquiv, eInt] using hP'.1
    · have hinertia_map :
          Ideal.inertiaDeg (𝔮 i).maximalIdeal.asIdeal (P.map eInt) =
            Ideal.inertiaDeg (𝔮 i).maximalIdeal.asIdeal P := by
        simpa using
          (Ideal.inertiaDeg_map_eq
            (p := (𝔮 i).maximalIdeal.asIdeal) (P := P) eInt)
      rw [← hinertia_map]
      simpa [primeEquiv, eInt] using hP'.2

attribute [-instance] DivisionRing.toRatAlgebra in
theorem hmr_split_index
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (hFrob : ∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i))
    (i : ℕ) :
    SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension) (𝔮 i)
      (hmrFixedField (K := ℚ) (KS := initialProExtension) x) := by
  intro E
  exact hmr_split_layer 𝔮 x hUnr hFrob i E

/- The fixed-index splitting lemma packages immediately into the pointwise statement needed in
the theorem. Keeping this wrapper separate makes the final assembly proof read like the TeX
argument: infinitude first, then local splitting for each `i`. -/
theorem hmr_all_indices
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (hFrob : ∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i)) :
    ∀ i,
      SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension) (𝔮 i)
        (hmrFixedField (K := ℚ) (KS := initialProExtension) x) := by
  intro i
  exact hmr_split_index 𝔮 x hUnr hFrob i

/- Putting the two independent halves of the TeX proof together:
the depth-choice lemma gives infinitude of the quotient, and the fixed-index splitting lemma
gives complete splitting in the fixed field for every prescribed place. -/
theorem hmr_cutting_output
    {k : ℕ} (hk : HMRCuttingLevel k)
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (h𝔮S : ∀ i, finitePlaceNorm (𝔮 i) ∉ initialRamifiedPrimes)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (hFrob : ∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i))
    (hZas : ∀ i, x i ∈ initialZassenhausFiltration (k + i)) :
    Infinite (hmrCutQuotient (K := ℚ) (KS := initialProExtension) x) ∧
      ∀ i,
        SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension) (𝔮 i)
          (hmrFixedField (K := ℚ) (KS := initialProExtension) x) := by
  let _ := h𝔮S
  refine ⟨hmr_cut_infinite hk x hZas, ?_⟩
  exact hmr_all_indices 𝔮 x hUnr hFrob

/-
The HMR Frobenius-cutting theorem in the concrete `Q_S^(3)/ℚ` setting. Since finite places of
`ℚ` correspond to rational primes, we express the condition `q_i ∉ S` by requiring the norm of
the finite place `𝔮_i` to avoid `initialRamifiedPrimes`.
-/
theorem hmr_tame_cutting :
    ∃ k : ℕ, 2 ≤ k ∧
      ∀ (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup),
        (∀ i, finitePlaceNorm (𝔮 i) ∉ initialRamifiedPrimes) →
        (∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i)) →
        (∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i)) →
        (∀ i, x i ∈ initialZassenhausFiltration (k + i)) →
        Infinite (hmrCutQuotient (K := ℚ) (KS := initialProExtension) x) ∧
          ∀ i,
            SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension) (𝔮 i)
              (hmrFixedField (K := ℚ) (KS := initialProExtension) x) := by
  refine ⟨hmrCuttingLevel, hmr_cutting_two, ?_⟩
  intro 𝔮 x h𝔮S hUnr hFrob hZas
  exact hmr_cutting_output hmr_cutting_spec 𝔮 x h𝔮S hUnr hFrob hZas

/- So the HMR tame Frobenius-cutting theorem applies to `G = Gal(Q_S^(3)/ℚ)`. -/
theorem initialHMRApplicable :
    ∃ k : ℕ, 2 ≤ k := by
  rcases hmr_tame_cutting with ⟨k, hk, _⟩
  exact ⟨k, hk⟩

/- Adding the congruence condition `q ≡ 1 mod 4`. -/
noncomputable def cuttingLevel : ℕ :=
  Classical.choose hmr_tame_cutting

theorem cutting_level_two : 2 ≤ cuttingLevel := by
  exact (Classical.choose_spec hmr_tame_cutting).1

theorem cutting_level_output
    (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup)
    (h𝔮S : ∀ i, finitePlaceNorm (𝔮 i) ∉ initialRamifiedPrimes)
    (hUnr : ∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i))
    (hFrob : ∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i))
    (hZas : ∀ i, x i ∈ initialZassenhausFiltration (cuttingLevel + i)) :
    Infinite (hmrCutQuotient (K := ℚ) (KS := initialProExtension) x) ∧
      ∀ i,
        SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension) (𝔮 i)
          (hmrFixedField (K := ℚ) (KS := initialProExtension) x) := by
  exact (Classical.choose_spec hmr_tame_cutting).2 𝔮 x h𝔮S hUnr hFrob hZas

end STBuild
end TBluepr
end Towers
