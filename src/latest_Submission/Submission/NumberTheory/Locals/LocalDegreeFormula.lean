import Submission.NumberTheory.Ramification.FactorizationInExtensions
import Submission.NumberTheory.Valuations.DiscreteValuations
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# The local degree formula

Milne's Corollary 7.42 is the one-prime specialization of the global
ramification-inertia degree formula from Theorem 3.34.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Corollary 7.42: if `P` is the unique prime above `p`, then the
extension degree is the ramification index times the inertia degree. -/
theorem ramification_deg_unique
    (A B K L : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    (hunique : IsDedekindDomain.primesOverFinset p B = {P}) :
    Ideal.ramificationIdx p P * Ideal.inertiaDeg p P =
      Module.finrank K L := by
  have h := deg_fraction_rings
    A B K L hp
  rw [hunique] at h
  simpa only [Finset.sum_singleton] using h

/-- The ideal-factorization assertion in Milne's Remark 7.43: if `P` is the
unique prime above `p`, then the extension of `p` is the `e`th power of `P`,
where `e` is the ramification index. -/
theorem ramification_idx_unique
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    (hunique : IsDedekindDomain.primesOverFinset p B = {P}) :
    p.map (algebraMap A B) = P ^ Ideal.ramificationIdx p P := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  classical
  have hfin : (p.primesOver B).toFinset = {P} := by
    ext Q
    rw [Finset.mem_singleton]
    rw [Set.mem_toFinset, ← IsDedekindDomain.mem_primesOverFinset_iff hp B, hunique]
    simp
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp, hfin]
  simp

/-- The uniformizer relation in Milne's Remark 7.43.  If `pi` generates `p`
and `Pi` generates the unique prime `P` above it, then the image of `pi` is a
unit times `Pi ^ e`. -/
theorem algebra_uniformizer_unique
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    (hunique : IsDedekindDomain.primesOverFinset p B = {P})
    {pi : A} (hpi : p = Ideal.span {pi})
    {Pi : B} (hPi : P = Ideal.span {Pi}) :
    ∃ u : Bˣ,
      algebraMap A B pi = (u : B) * Pi ^ Ideal.ramificationIdx p P := by
  have hfactor :=
    ramification_idx_unique A B hp hunique
  have hspan :
      Ideal.span ({algebraMap A B pi} : Set B) =
        Ideal.span ({Pi ^ Ideal.ramificationIdx p P} : Set B) := by
    calc
      Ideal.span ({algebraMap A B pi} : Set B) =
          p.map (algebraMap A B) := by
            rw [hpi, Ideal.map_span, Set.image_singleton]
      _ = P ^ Ideal.ramificationIdx p P := hfactor
      _ = (Ideal.span ({Pi} : Set B)) ^ Ideal.ramificationIdx p P := by
        rw [← hPi]
      _ = Ideal.span ({Pi ^ Ideal.ramificationIdx p P} : Set B) :=
        Ideal.span_singleton_pow Pi _
  obtain ⟨u, hu⟩ :=
    (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

open WithZero Multiplicative IsDedekindDomain

noncomputable section

private theorem count_factors_emultiplicity
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk P.asIdeal).count (Associates.mk I).factors =
      (emultiplicity P.asIdeal I).toNat := by
  have hcount := Ideal.count_associates_factors_eq hI P.isPrime P.ne_bot
  have hem := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
    P.irreducible hI
  calc
    _ = Multiset.count P.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors I) := hcount
    _ = (emultiplicity P.asIdeal I).toNat := by
      have h := congrArg ENat.toNat hem
      simpa [normalize_eq] using h.symm

/-- The normalized multiplicative valuation at `P`, restricted to the base
Dedekind domain, is the `e(P/p)`th power of the normalized valuation at `p`.
This is Equation (13) preceding Proposition 3.53 and the integral-element
form of Remark 7.43. -/
theorem int_valuation_idx
    {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] (a : A) :
    P.intValuation (algebraMap A B a) =
      (p.intValuation a) ^ Ideal.ramificationIdx p.asIdeal P.asIdeal := by
  by_cases ha : a = 0
  · subst a
    have he : Ideal.ramificationIdx p.asIdeal P.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
        P.asIdeal p.ne_bot
    simp [he]
  have hmapa : algebraMap A B a ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective A B).ne ha
  rw [P.intValuation_if_neg hmapa, p.intValuation_if_neg ha]
  have hspanA : (Ideal.span {a} : Ideal A) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  have hspanB : (Ideal.span {algebraMap A B a} : Ideal B) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hmapa
  rw [count_factors_emultiplicity P hspanB,
    count_factors_emultiplicity p hspanA]
  have hem := emultiplicity_ramification_idx p P a ha
  have hemNat :
      (emultiplicity P.asIdeal
          (Ideal.span {algebraMap A B a})).toNat =
        Ideal.ramificationIdx p.asIdeal P.asIdeal *
          (emultiplicity p.asIdeal (Ideal.span {a})).toNat := by
    have h := congrArg ENat.toNat hem
    simpa using h
  rw [hemNat, ← WithZero.exp_nsmul]
  congr 1
  simp only [nsmul_eq_mul, Int.natCast_mul]
  ring

/-- Remark 7.43 in multiplicative form, for arbitrary elements of the
fraction field: restricting the normalized valuation at `P` to `K` raises
the normalized valuation at `p` to the ramification index. -/
theorem valuation_ramification_idx
    {A B K L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] (x : K) :
    P.valuation L (algebraMap K L x) =
      (p.valuation K x) ^ Ideal.ramificationIdx p.asIdeal P.asIdeal := by
  obtain ⟨⟨a, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors A) x
  obtain rfl : x = IsLocalization.mk' K a ⟨d, hd⟩ :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  have hdA : d ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨d, hd⟩
  have hdB : algebraMap A B d ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective A B).ne hdA
  let dB : nonZeroDivisors B := ⟨algebraMap A B d,
    mem_nonZeroDivisors_iff_ne_zero.mpr hdB⟩
  have hmk :
      algebraMap K L (IsLocalization.mk' K a ⟨d, hd⟩) =
        IsLocalization.mk' L (algebraMap A B a) dB := by
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    have hx' := IsLocalization.eq_mk'_iff_mul_eq.mp
      (rfl : IsLocalization.mk' K a ⟨d, hd⟩ =
        IsLocalization.mk' K a ⟨d, hd⟩)
    have hxL := congrArg (algebraMap K L) hx'
    rw [map_mul, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L] at hxL
    dsimp [dB]
    simpa only [IsScalarTower.algebraMap_apply A B L] using hxL
  rw [hmk, P.valuation_of_mk', p.valuation_of_mk']
  rw [int_valuation_idx p P,
    int_valuation_idx p P]
  exact (div_pow _ _ _).symm

/-- The additive normalization of a Dedekind-prime valuation, restricted to
the multiplicative group of the fraction field. Mathlib's multiplicative
value `exp (-n)` corresponds to additive order `n`. -/
def normalizedAdicOrder
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : HeightOneSpectrum A) (x : Kˣ) : ℤ :=
  -(p.valuation K (x : K)).log

/-- A normalized adic order assumes every integer value. -/
theorem normalized_order_surjective
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : HeightOneSpectrum A) :
    Function.Surjective (normalizedAdicOrder p (K := K)) := by
  intro z
  obtain ⟨x, hx⟩ := p.valuation_surjective K (WithZero.exp (-z : ℤ))
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    rw [map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  simp [normalizedAdicOrder, hx]

/-- Remark 7.43 in additive normalized form:
`ord_P(algebraMap x) = e(P/p) * ord_p(x)`. -/
theorem normalized_adic_ramification
    {A B K L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] (x : Kˣ) :
    normalizedAdicOrder P
        (Units.map (algebraMap K L).toMonoidHom x) =
      Ideal.ramificationIdx p.asIdeal P.asIdeal * normalizedAdicOrder p x := by
  unfold normalizedAdicOrder
  change -(P.valuation L (algebraMap K L (x : K))).log = _
  rw [valuation_ramification_idx p P,
    WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/-- The extension of `ord_p` to `L`, normalized so that it agrees with
`ord_p` on `K`. -/
def extendedAdicOrder
    {A B L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B) (x : Lˣ) : ℚ :=
  (normalizedAdicOrder P x : ℚ) /
    (Ideal.ramificationIdx p.asIdeal P.asIdeal : ℚ)

/-- The rescaled order on `L` really extends the normalized order on `K`. -/
theorem extended_adic_algebra
    {A B K L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] (x : Kˣ) :
    extendedAdicOrder p P
        (Units.map (algebraMap K L).toMonoidHom x) =
      normalizedAdicOrder p x := by
  rw [extendedAdicOrder,
    normalized_adic_ramification p P]
  have he : (Ideal.ramificationIdx p.asIdeal P.asIdeal : ℚ) ≠ 0 := by
    exact_mod_cast
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
        P.asIdeal p.ne_bot)
  push_cast
  field_simp

/-- The final assertion of Remark 7.43: the value group of the extension of
`ord_p` to `L` is exactly `e(P/p)⁻¹ ℤ`. -/
theorem extended_smul_int
    {A B L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] :
    Set.range (extendedAdicOrder p P (L := L)) =
      Set.range (fun z : ℤ =>
        (z : ℚ) / (Ideal.ramificationIdx p.asIdeal P.asIdeal : ℚ)) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨normalizedAdicOrder P x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := normalized_order_surjective P (K := L) z
    refine ⟨x, ?_⟩
    simp [extendedAdicOrder, hx]

end

end Submission.NumberTheory.Milne
