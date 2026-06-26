import Towers.FieldTheory.Blueprint


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

namespace TBluepr

theorem rational_unramified_alg
    {K L : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    [Field L] [NumberField L] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) {q : ℕ}
    (hK : RationalPrimeUnramified (S := 𝓞 K) q) :
    RationalPrimeUnramified (S := 𝓞 L) q := by
  have h_algK : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  have h_algL : (DivisionRing.toRatAlgebra : Algebra ℚ L) = ‹Algebra ℚ L› :=
    Subsingleton.elim _ _
  cases h_algK
  cases h_algL
  let e0 : 𝓞 K ≃ₐ[ℤ] 𝓞 L := (e.restrictScalars ℤ).mapIntegralClosure
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  intro Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver qI := hQ.2
  let P : Ideal (𝓞 K) := Ideal.comap e0.toRingHom Q
  have hP :
      P ∈ Ideal.primesOver qI (𝓞 K) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
    ext z
    change z ∈ qI ↔ algebraMap ℤ (𝓞 K) z ∈ P
    change z ∈ qI ↔ e0.toRingHom (algebraMap ℤ (𝓞 K) z) ∈ Q
    simpa using (Ideal.mem_of_liesOver (P := Q) (p := qI) z)
  have hPe :
      Ideal.ramificationIdx qI P = 1 := hK P hP
  calc
    Ideal.ramificationIdx qI Q
      = Ideal.ramificationIdx qI (Ideal.map e0 P) := by
          congr 1
          simpa [P] using
            (Ideal.map_comap_of_surjective (f := e0.toRingHom) e0.surjective Q).symm
    _ = Ideal.ramificationIdx qI P := by
          exact Ideal.ramificationIdx_map_eq (p := qI) (P := P) e0
    _ = 1 := hPe

/--
An unramified finite-place Frobenius equal to the identity forces complete
splitting at that place.
-/
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

/-- Compose a finite-level embedding with an ambient extension embedding. -/
theorem embeds_extension_trans
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K]
    {L M : Type} [Field L] [Algebra ℚ L] [Field M] [Algebra ℚ M]
    (hKL : EmbedsIntoExtension K L)
    (hLM : ExtensionEmbeds L M) :
    EmbedsIntoExtension K M := by
  rcases hKL with ⟨f⟩
  rcases hLM with ⟨g⟩
  exact ⟨g.comp f⟩

instance ring_scalar_tower
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] :
    IsScalarTower ℤ (𝓞 K) K := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  simp

theorem abs_rational_ideal (q : ℕ) :
    Ideal.absNorm (Ideal.rationalPrimeIdeal q) = q := by
  rw [Ideal.rationalPrimeIdeal, Ideal.absNorm_apply]
  simpa [Submodule.cardQuot_apply] using Int.card_ideal_quot q

theorem arith_frob_rat
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)]
    {Q : Ideal (𝓞 E)} {σ : Gal(E/ℚ)} :
    IsArithFrobAt (𝓞 ℚ) σ Q ↔ IsArithFrobAt ℤ σ Q := by
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
    Subsingleton.elim _ _
  have hmap :
      Q.under ℤ = (Q.under (𝓞 ℚ)).map e0 := by
    have hcomp :
        (algebraMap ℤ (𝓞 E)) =
          (algebraMap (𝓞 ℚ) (𝓞 E)).comp e0.symm.toRingHom :=
      Subsingleton.elim _ _
    calc
      Q.under ℤ = (Q.under (𝓞 ℚ)).comap e0.symm.toRingHom := by
        rw [Ideal.under, hcomp, Ideal.under, Ideal.comap_comap]
      _ = (Q.under (𝓞 ℚ)).map e0.toRingHom := by
        symm
        exact Ideal.map_comap_of_equiv (I := Q.under (𝓞 ℚ)) e0.toRingEquiv
  have hcard :
      Nat.card ((𝓞 ℚ) ⧸ Q.under (𝓞 ℚ)) =
        Nat.card (ℤ ⧸ Q.under ℤ) := by
    let e :
        (𝓞 ℚ) ⧸ Q.under (𝓞 ℚ) ≃+*
          ℤ ⧸ Q.under ℤ :=
      Ideal.quotientEquiv (Q.under (𝓞 ℚ)) (Q.under ℤ) Rat.ringOfIntegersEquiv hmap
    exact Nat.card_congr e.toEquiv
  constructor <;> intro hσ <;>
    simpa [IsArithFrobAt, AlgHom.IsArithFrobAt, hcard] using hσ

theorem arith_rat_restrict
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    {P : Ideal (𝓞 L)} [P.IsPrime]
    {σ : Gal(L/ℚ)}
    (hσ : IsArithFrobAt (𝓞 ℚ) σ P) :
    IsArithFrobAt (𝓞 ℚ) (σ.restrictNormalHom E)
      (P.under (𝓞 E)) := by
  intro x
  rw [Ideal.mem_of_liesOver
    (A := 𝓞 E) (B := 𝓞 L) (p := P.under (𝓞 E)) (P := P)]
  have hmap :
      algebraMap (𝓞 E) (𝓞 L)
        (MulSemiringAction.toAlgHom (𝓞 ℚ)
          (𝓞 E) (σ.restrictNormalHom E) x) =
      MulSemiringAction.toAlgHom (𝓞 ℚ)
        (𝓞 L) σ (algebraMap (𝓞 E) (𝓞 L) x) := by
    apply Subtype.ext
    calc
      algebraMap (𝓞 L) L
          (algebraMap (𝓞 E) (𝓞 L)
            (MulSemiringAction.toAlgHom (𝓞 ℚ)
              (𝓞 E) (σ.restrictNormalHom E) x))
        =
          algebraMap E L
            (algebraMap (𝓞 E) E
              (MulSemiringAction.toAlgHom (𝓞 ℚ)
                (𝓞 E) (σ.restrictNormalHom E) x)) := by
            rfl
      _ =
          algebraMap E L
            ((σ.restrictNormalHom E)
              (algebraMap (𝓞 E) E x)) := by
            rw [alg_gal_restrict
              (K := ℚ) (E := E) (σ := σ.restrictNormalHom E) x]
            exact congrArg (algebraMap E L)
              (algebraMap_galRestrict_apply
                (A := 𝓞 ℚ) (K := ℚ) (L := E)
                (B := 𝓞 E) (σ := σ.restrictNormalHom E) x)
      _ = σ (algebraMap E L (algebraMap (𝓞 E) E x)) := by
            exact AlgEquiv.restrictNormal_commutes σ E (algebraMap (𝓞 E) E x)
      _ = σ
          (algebraMap (𝓞 L) L
            (algebraMap (𝓞 E) (𝓞 L) x)) := by
            rfl
      _ =
          algebraMap (𝓞 L) L
            (MulSemiringAction.toAlgHom (𝓞 ℚ)
              (𝓞 L) σ (algebraMap (𝓞 E) (𝓞 L) x)) := by
            rw [alg_gal_restrict
              (K := ℚ) (E := L) (σ := σ)
              (x := algebraMap (𝓞 E) (𝓞 L) x)]
            exact
              (algebraMap_galRestrict_apply
                (A := 𝓞 ℚ) (K := ℚ) (L := L)
                (B := 𝓞 L) σ
                (algebraMap (𝓞 E) (𝓞 L) x)).symm
  have hσx :
      MulSemiringAction.toAlgHom (𝓞 ℚ)
          (𝓞 L) σ
          (algebraMap (𝓞 E) (𝓞 L) x) -
        (algebraMap (𝓞 E)
          (𝓞 L) x) ^
          Nat.card ((𝓞 ℚ) ⧸ P.under (𝓞 ℚ)) ∈
        P := by
    exact hσ (algebraMap (𝓞 E) (𝓞 L) x)
  rw [← hmap] at hσx
  simpa [AlgHom.IsArithFrobAt, Ideal.under_under, map_sub, map_pow] using hσx

theorem arith_frob_int
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    [IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L)]
    {P : Ideal (𝓞 L)} [P.IsPrime]
    {σ : Gal(L/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) :
    IsArithFrobAt ℤ (σ.restrictNormalHom E)
      (P.under (𝓞 E)) := by
  have hσ' : IsArithFrobAt (𝓞 ℚ) σ P :=
    (arith_frob_rat (E := L)).2 hσ
  have h' :
      IsArithFrobAt (𝓞 ℚ) (σ.restrictNormalHom E)
        (P.under (𝓞 E)) :=
    arith_rat_restrict (E := E) (L := L) hσ'
  exact (arith_frob_rat (E := E)).1 h'

theorem frobenius_restrict_hom
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    {v : FinitePlace ℚ} {σ : Gal(L/ℚ)}
    (hσ : FrobeniusPlaceField (K := ℚ) (E := L) v σ) :
    FrobeniusPlaceField (K := ℚ) (E := E) v (σ.restrictNormalHom E) := by
  rcases hσ with ⟨Q, hQFrob⟩
  refine ⟨⟨Q.1.under (𝓞 E), inferInstance, inferInstance⟩, ?_⟩
  exact arith_rat_restrict (E := E) (L := L) hQFrob

theorem place_nat_norm (v : FinitePlace ℚ) :
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

theorem place_ring_integers (v : FinitePlace ℚ) :
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
          rw [place_nat_norm v]
          rfl

theorem splits_completely_split
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (v : FinitePlace ℚ)
    (hq : Nat.Prime (finitePlaceNorm v))
    (hsplit : SplitsCompletelyField (K := ℚ) (E := E) v) :
    splitsCompletely E (finitePlaceNorm v) := by
  letI : IsScalarTower ℤ ℚ E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ E (𝓞 E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ℚ (𝓞 ℚ)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 ℚ) ℚ E (𝓞 E)
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
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have hpmap : pI.map e0 = qI := by
    simpa [pI, qI] using place_ring_integers v
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
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := pI) (P := P)
  have hPmem : P ∈ Ideal.primesOver pI (𝓞 E) := ⟨hPprime, hPover⟩
  have hPoverq : P.LiesOver qI := Ideal.LiesOver.trans P pI qI
  letI : P.LiesOver qI := hPoverq
  have hramP : Ideal.ramificationIdx pI P = 1 := (hsplit.2 P hPmem).1
  have hinP : Ideal.inertiaDeg pI P = 1 := (hsplit.2 P hPmem).2
  have hramPIn : pI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      pI.ramificationIdxIn (𝓞 E)
        = Ideal.ramificationIdx pI P := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := pI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hramP
  have hinPIn : pI.inertiaDegIn (𝓞 E) = 1 := by
    calc
      pI.inertiaDegIn (𝓞 E)
        = Ideal.inertiaDeg pI P := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := pI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hinP
  have hramSelf : Ideal.ramificationIdx qI qI = 1 := by
    have hqItop' : qI ≠ ⊤ := Ideal.IsPrime.ne_top (show qI.IsPrime by infer_instance)
    have hqItop : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊤ := by
      simpa using hqItop'
    have hqI0' : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊥ := by
      simpa using hqI0
    simpa using
      (Ideal.ramificationIdx_map_self_eq_one (R := ℤ) (S := ℤ)
        (p := qI) hqItop hqI0')
  have hinSelf : Ideal.inertiaDeg qI qI = 1 := by
    rw [Ideal.inertiaDeg_algebraMap (p := qI) (P := qI)]
    exact Module.finrank_self (ℤ ⧸ qI)
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
  have hinBaseIn : qI.inertiaDegIn (𝓞 ℚ) = 1 := by
    calc
      qI.inertiaDegIn (𝓞 ℚ)
        = Ideal.inertiaDeg qI pI := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := pI) (G := Gal(ℚ/ℚ))
      _ = Ideal.inertiaDeg qI (pI.map e0) := by
            symm
            exact Ideal.inertiaDeg_map_eq (p := qI) (P := pI) e0
      _ = Ideal.inertiaDeg qI qI := by
            rw [hpmap]
      _ = 1 := hinSelf
  have hramEIn : qI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 E)
        = qI.ramificationIdxIn (𝓞 ℚ) * pI.ramificationIdxIn (𝓞 E) := by
            symm
            exact Ideal.ramificationIdxIn_mul_ramificationIdxIn'
              (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
      _ = 1 := by rw [hramBaseIn, hramPIn]
  have hinEIn : qI.inertiaDegIn (𝓞 E) = 1 := by
    calc
      qI.inertiaDegIn (𝓞 E)
        = qI.inertiaDegIn (𝓞 ℚ) * pI.inertiaDegIn (𝓞 E) := by
            symm
            exact Ideal.inertiaDegIn_mul_inertiaDegIn
              (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
      _ = 1 := by rw [hinBaseIn, hinPIn]
  have hPe : Ideal.ramificationIdx qI P = 1 := by
    calc
      Ideal.ramificationIdx qI P
        = qI.ramificationIdxIn (𝓞 E) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hramEIn
  have hPf : Ideal.inertiaDeg qI P = 1 := by
    calc
      Ideal.inertiaDeg qI P
        = qI.inertiaDegIn (𝓞 E) := by
            symm
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hinEIn
  have h_algE : (DivisionRing.toRatAlgebra : Algebra ℚ E) = ‹Algebra ℚ E› :=
    Subsingleton.elim _ _
  cases h_algE
  exact splits_completely_conditions E hq P hPe hPf

end TBluepr

end Towers
