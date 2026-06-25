import Submission.NumberTheory.Locals.PlacesClassification
import Submission.NumberTheory.Locals.RestrictionNontrivial


/-!
# Classification of nonarchimedean absolute values on number fields

This file proves the finite-place half of Milne's Theorem 7.14 for an
arbitrary nontrivial absolute value.  The prime ideal associated to `w` is
the set of algebraic integers whose value is strictly less than one.
-/

namespace Submission.NumberTheory.Milne

open scoped BigOperators NNReal
open Polynomial IsDedekindDomain NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A nonarchimedean absolute value is at most one on every algebraic
integer. -/
theorem nonarchimedean_ring_integers
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) (x : 𝓞 K) :
    w (algebraMap (𝓞 K) K x) ≤ 1 := by
  let xK : K := algebraMap (𝓞 K) K x
  by_contra hx
  have hx1 : 1 < w xK := lt_of_not_ge hx
  let p : ℤ[X] := minpoly ℤ xK
  have hxi : IsIntegral ℤ xK := by
    simpa [xK] using x.isIntegral_coe
  have hpmonic : p.Monic := minpoly.monic hxi
  have hd : 0 < p.natDegree :=
    natDegree_pos_of_monic_of_aeval_eq_zero hpmonic (minpoly.aeval ℤ xK)
  let lower : K := ∑ i ∈ Finset.range p.natDegree,
    algebraMap ℤ K (p.coeff i) * xK ^ i
  have hroot : lower + xK ^ p.natDegree = 0 := by
    have h := minpoly.aeval ℤ xK
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range,
      Finset.sum_range_succ] at h
    simpa only [lower, p, hpmonic.coeff_natDegree, map_one, one_mul] using h
  obtain ⟨i, hi_mem, hi_sum⟩ :=
    hna.finset_image_add
      (fun i : ℕ => algebraMap ℤ K (p.coeff i) * xK ^ i)
      (Finset.range p.natDegree)
  have hi : i < p.natDegree :=
    Finset.mem_range.mp (hi_mem ⟨0, Finset.mem_range.mpr hd⟩)
  have hcoeff : w (algebraMap ℤ K (p.coeff i)) ≤ 1 := by
    simpa using hna.apply_intCast_le_one
      (f := w) (n := p.coeff i)
  have hterm :
      w (algebraMap ℤ K (p.coeff i) * xK ^ i) <
        w (xK ^ p.natDegree) := by
    rw [w.map_mul, w.map_pow, w.map_pow]
    calc
      w (algebraMap ℤ K (p.coeff i)) * w xK ^ i ≤ 1 * w xK ^ i := by
        gcongr
      _ = w xK ^ i := one_mul _
      _ < w xK ^ p.natDegree := pow_lt_pow_right₀ hx1 hi
  have hlower : w lower < w (xK ^ p.natDegree) := hi_sum.trans_lt hterm
  have hz := hna.add_eq_right_of_lt hlower
  rw [hroot, w.map_zero] at hz
  have hx0 : xK ≠ 0 := w.ne_zero_iff.mp (zero_lt_one.trans hx1).ne'
  exact (w.pos (pow_ne_zero _ hx0)).ne' hz.symm

/-- The ideal of algebraic integers having value strictly less than one. -/
def nonarchimedeanPrimeIdeal
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) : Ideal (𝓞 K) where
  carrier := {x | w (algebraMap (𝓞 K) K x) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change w (algebraMap (𝓞 K) K (x + y)) < 1
    rw [map_add]
    exact (hna _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro a x hx
    change w (algebraMap (𝓞 K) K (a * x)) < 1
    rw [map_mul, w.map_mul]
    exact (mul_le_mul_of_nonneg_right
      (nonarchimedean_ring_integers w hna a)
      (w.nonneg _)).trans_lt (by simpa using hx)

@[simp]
theorem nonarchimedean_prime_ideal
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) (x : 𝓞 K) :
    x ∈ nonarchimedeanPrimeIdeal w hna ↔
      w (algebraMap (𝓞 K) K x) < 1 :=
  Iff.rfl

/-- The strict unit-ball ideal of a nonarchimedean absolute value is prime. -/
theorem nonarchimedean_ideal
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) :
    (nonarchimedeanPrimeIdeal w hna).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have hone : (1 : 𝓞 K) ∈ nonarchimedeanPrimeIdeal w hna := by
      rw [htop]
      simp
    simp at hone
  · intro x y hxy
    change w (algebraMap (𝓞 K) K (x * y)) < 1 at hxy
    rw [map_mul, w.map_mul] at hxy
    by_cases hx : w (algebraMap (𝓞 K) K x) < 1
    · exact Or.inl hx
    · right
      have hx1 : 1 ≤ w (algebraMap (𝓞 K) K x) := le_of_not_gt hx
      by_contra hy
      have hy1 : 1 ≤ w (algebraMap (𝓞 K) K y) := le_of_not_gt hy
      exact (not_le_of_gt hxy)
        (one_le_mul_of_one_le_of_one_le hx1 hy1)

/-- Nontriviality forces the centered prime ideal to be nonzero. -/
theorem nonarchimedean_ne_bot
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    nonarchimedeanPrimeIdeal w hna ≠ ⊥ := by
  let v := w.comp (algebraMap ℚ K).injective
  have hv : v.IsNontrivial := number_restriction_nontrivial w hw
  have hvna : IsNonarchimedean v := by
    intro x y
    change w (algebraMap ℚ K (x + y)) ≤
      max (w (algebraMap ℚ K x)) (w (algebraMap ℚ K y))
    simpa only [map_add] using hna (algebraMap ℚ K x) (algebraMap ℚ K y)
  obtain ⟨p, hp, _⟩ := ostrowski_nonarchimedean v hv hvna
  obtain ⟨hpFact, hvp⟩ := hp
  letI : Fact p.Prime := hpFact
  have hpadic : Rat.AbsoluteValue.padic p (p : ℚ) < 1 := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm]
    exact_mod_cast (padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  have hvplt : v (p : ℚ) < 1 := hvp.lt_one_iff.mpr hpadic
  apply (nonarchimedeanPrimeIdeal w hna).ne_bot_iff.mpr
  refine ⟨(p : 𝓞 K), ?_, ?_⟩
  · change w (algebraMap (𝓞 K) K (p : 𝓞 K)) < 1
    change w (algebraMap ℚ K (p : ℚ)) < 1 at hvplt
    simpa using hvplt
  · exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The height-one prime associated to a nontrivial nonarchimedean absolute
value. -/
def nonarchimedeanHeightSpectrum
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) : HeightOneSpectrum (𝓞 K) where
  asIdeal := nonarchimedeanPrimeIdeal w hna
  isPrime := nonarchimedean_ideal w hna
  ne_bot := nonarchimedean_ne_bot w hw hna

/-- Regard a nonarchimedean real-valued absolute value as an `ℝ≥0`-valued
valuation. -/
def nonarchimedeanValuation
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) : Valuation K ℝ≥0 where
  toFun x := ⟨w x, w.nonneg x⟩
  map_one' := by apply NNReal.eq; exact w.map_one
  map_zero' := by apply NNReal.eq; exact w.map_zero
  map_mul' x y := by apply NNReal.eq; exact w.map_mul x y
  map_add_le_max' x y := by
    rw [← NNReal.coe_le_coe]
    simpa using hna x y

omit [NumberField K] in
@[simp]
theorem nonarchimedeanValuation_apply
    (w : AbsoluteValue K ℝ) (hna : IsNonarchimedean w) (x : K) :
    (nonarchimedeanValuation w hna x : ℝ) = w x :=
  rfl

/-- The valuation induced by `w` is equivalent to the normalized valuation
at its centered height-one prime.  The proof uses the fact that the
localization of a Dedekind domain at a nonzero prime is a valuation ring. -/
theorem nonarchimedean_valuation_adic
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    (nonarchimedeanValuation w hna).IsEquiv
      ((nonarchimedeanHeightSpectrum w hw hna).valuation K) := by
  let P := nonarchimedeanHeightSpectrum w hw hna
  have hwle (a : 𝓞 K) : w (algebraMap (𝓞 K) K a) ≤ 1 :=
    nonarchimedean_ring_integers w hna a
  have hweq (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
      w (algebraMap (𝓞 K) K a) = 1 := by
    apply le_antisymm (hwle a)
    exact le_of_not_gt (by
      intro hlt
      exact ha hlt)
  apply Valuation.isEquiv_of_val_le_one
  intro x
  change w x ≤ 1 ↔ P.valuation K x ≤ 1
  constructor
  · intro hx
    obtain ⟨n, d, hnd | hnd⟩ := P.exists_primeCompl_mul_eq_or_mul_eq x
    · have hdv : P.valuation K (algebraMap (𝓞 K) K d) = 1 := by
        rw [P.valuation_of_algebraMap,
          P.intValuation_eq_one_iff_mem_primeCompl]
        exact d.prop
      have hnv : P.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := by
        rw [P.valuation_of_algebraMap]
        exact P.intValuation_le_one n
      have heq := congrArg (P.valuation K) hnd
      rw [map_mul, hdv, mul_one] at heq
      exact heq.symm ▸ hnv
    · have hdw : w (algebraMap (𝓞 K) K d) = 1 := hweq d d.prop
      have hnnot : n ∉ P.asIdeal := by
        intro hn
        have hnlt : w (algebraMap (𝓞 K) K n) < 1 := hn
        have hprod :
            w x * w (algebraMap (𝓞 K) K n) < 1 :=
          (mul_le_mul_of_nonneg_right hx (w.nonneg _)).trans_lt
            (by simpa using hnlt)
        have heq := congrArg w hnd
        rw [w.map_mul, hdw] at heq
        rw [heq] at hprod
        exact (lt_irrefl 1 hprod)
      have hnv : P.valuation K (algebraMap (𝓞 K) K n) = 1 := by
        rw [P.valuation_of_algebraMap,
          P.intValuation_eq_one_iff_mem_primeCompl]
        exact hnnot
      have hdv : P.valuation K (algebraMap (𝓞 K) K d) = 1 := by
        rw [P.valuation_of_algebraMap,
          P.intValuation_eq_one_iff_mem_primeCompl]
        exact d.prop
      have heq := congrArg (P.valuation K) hnd
      rw [map_mul, hnv, hdv, mul_one] at heq
      exact heq.le
  · intro hx
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
    have hdw : w (algebraMap (𝓞 K) K d) = 1 := hweq d d.prop
    have hnle := hwle n
    have heq := congrArg w hnd
    rw [w.map_mul, hdw, mul_one] at heq
    exact heq.symm ▸ hnle

/-- Milne, Theorem 7.14(a), arbitrary-value form: every nontrivial
nonarchimedean absolute value on a number field is equivalent to the finite
place attached to its centered prime ideal. -/
theorem finite_place_nonarchimedean
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    ∃ v : FinitePlace K, w.IsEquiv v.1 := by
  let P := nonarchimedeanHeightSpectrum w hw hna
  refine ⟨FinitePlace.mk P, ?_⟩
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.2
  intro x
  have hval :=
    (nonarchimedean_valuation_adic w hw hna).lt_one_iff_lt_one
      (x := x)
  have hval' : w x < 1 ↔ P.valuation K x < 1 := by
    exact_mod_cast hval
  change w x < 1 ↔ ‖FinitePlace.embedding P x‖ < 1
  rw [FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def]
  have hto :
      ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero P)
          (P.valuation K x) : ℝ≥0) : ℝ) < 1 ↔ P.valuation K x < 1 := by
    exact_mod_cast WithZeroMulInt.toNNReal_lt_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal P)
  rw [hto]
  exact hval'

/-- The finite place in the nonarchimedean classification can be chosen to
be the centered height-one prime itself. -/
theorem place_centered_prime
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    w.IsEquiv
      (FinitePlace.mk (nonarchimedeanHeightSpectrum w hw hna)).val := by
  obtain ⟨v, hv⟩ :=
    finite_place_nonarchimedean w hw hna
  let P := nonarchimedeanHeightSpectrum w hw hna
  have hmax : v.maximalIdeal = P := by
    apply HeightOneSpectrum.ext
    ext x
    rw [← FinitePlace.norm_lt_one_iff_mem K v.maximalIdeal x]
    rw [FinitePlace.norm_embedding_eq]
    change v.val (algebraMap (RingOfIntegers K) K x) < 1 ↔
      w (algebraMap (RingOfIntegers K) K x) < 1
    exact hv.lt_one_iff.symm
  have hvP : v = FinitePlace.mk P := by
    rw [← FinitePlace.mk_maximalIdeal v, hmax]
  simpa [P, ← hvP] using hv

/-- The centered prime of an extending nonarchimedean absolute value lies
over the centered finite prime of the base absolute value. -/
theorem nonarchimedean_spectrum_lies
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (RingOfIntegers K))
    (w : AbsoluteValue L ℝ)
    (hwv : AbsoluteValue.LiesOver w (FinitePlace.mk p).val)
    (hw : w.IsNontrivial) (hna : IsNonarchimedean w) :
    (nonarchimedeanHeightSpectrum w hw hna).asIdeal.LiesOver
      p.asIdeal := by
  constructor
  ext x
  change
    x ∈ p.asIdeal ↔
      w (algebraMap (RingOfIntegers L) L
        (algebraMap (RingOfIntegers K) (RingOfIntegers L) x)) < 1
  rw [show algebraMap (RingOfIntegers L) L
      (algebraMap (RingOfIntegers K) (RingOfIntegers L) x) =
      algebraMap K L (algebraMap (RingOfIntegers K) K x) by
        exact IsScalarTower.algebraMap_apply
          (RingOfIntegers K) (RingOfIntegers L) L x]
  have heq := DFunLike.congr_fun hwv.comp_eq
    (algebraMap (RingOfIntegers K) K x)
  change w (algebraMap K L (algebraMap (RingOfIntegers K) K x)) =
    (FinitePlace.mk p).val (algebraMap (RingOfIntegers K) K x) at heq
  rw [heq]
  exact (FinitePlace.norm_lt_one_iff_mem K p x).symm

/-- Centered primes are compatible with restriction of arbitrary normalized
nonarchimedean absolute values. -/
theorem nonarchimedean_spectrum_centered
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hwv : AbsoluteValue.LiesOver w v)
    (hv : v.IsNontrivial) (hvna : IsNonarchimedean v)
    (hw : w.IsNontrivial) (hwna : IsNonarchimedean w) :
    (nonarchimedeanHeightSpectrum w hw hwna).asIdeal.LiesOver
      (nonarchimedeanHeightSpectrum v hv hvna).asIdeal := by
  constructor
  ext x
  change
    v (algebraMap (RingOfIntegers K) K x) < 1 ↔
      w (algebraMap (RingOfIntegers L) L
        (algebraMap (RingOfIntegers K) (RingOfIntegers L) x)) < 1
  rw [show algebraMap (RingOfIntegers L) L
      (algebraMap (RingOfIntegers K) (RingOfIntegers L) x) =
      algebraMap K L (algebraMap (RingOfIntegers K) K x) by
        exact IsScalarTower.algebraMap_apply
          (RingOfIntegers K) (RingOfIntegers L) L x]
  have heq := DFunLike.congr_fun hwv.comp_eq
    (algebraMap (RingOfIntegers K) K x)
  change w (algebraMap K L (algebraMap (RingOfIntegers K) K x)) =
    v (algebraMap (RingOfIntegers K) K x) at heq
  rw [heq]

end

end Submission.NumberTheory.Milne
