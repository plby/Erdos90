import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Milne, Algebraic Number Theory, Example 7.1

The standard archimedean, nonarchimedean, and trivial absolute values.
-/

namespace Towers.NumberTheory.Milne

open scoped NNReal WithZero

/-- Milne, Example 7.1(a): an embedding into `ℂ` defines an absolute value. -/
noncomputable def embeddingAbsoluteValue {K : Type*} [Field K] (sigma : K →+* ℂ) :
    AbsoluteValue K ℝ :=
  NumberField.place sigma

@[simp]
theorem embedding_absolute_value {K : Type*} [Field K] (sigma : K →+* ℂ) (x : K) :
    embeddingAbsoluteValue sigma x = ‖sigma x‖ :=
  rfl

/-- The nonnegative-real function obtained by exponentiating a multiplicative
integer-valued valuation with a base greater than one. -/
noncomputable def discreteAbvDef {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) (e : ℝ≥0) (he : 1 < e) (x : K) : ℝ≥0 :=
  WithZeroMulInt.toNNReal (ne_zero_of_lt he) (v x)

/-- Milne, Example 7.1(b): exponentiating an additive discrete valuation by
`e⁻¹`, for `e > 1`, satisfies the ultrametric inequality.  In multiplicative
notation `v x = exp (-ord x)`, so this function is `e ^ (-ord x)`. -/
theorem abv_def_nonarchimedean {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) (e : ℝ≥0) (he : 1 < e) :
    IsNonarchimedean (discreteAbvDef v e he) := by
  intro x y
  simp only [discreteAbvDef]
  have hmono := (WithZeroMulInt.toNNReal_strictMono he).monotone
  rw [← hmono.map_max]
  exact hmono (v.map_add x y)

/-- Milne, Example 7.1(b), in Mathlib's multiplicative valuation convention:
every `ℤᵐ⁰`-valued valuation and every base `e > 1` define an absolute value. -/
noncomputable def discreteValuationAbsolute {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) (e : ℝ≥0) (he : 1 < e) : AbsoluteValue K ℝ where
  toFun x := discreteAbvDef v e he x
  map_mul' x y := by simp [discreteAbvDef]
  nonneg' _ := by positivity
  eq_zero' x := by simp [discreteAbvDef]
  add_le' x y :=
    (abv_def_nonarchimedean v e he).add_le fun _ ↦ bot_le

@[simp]
theorem discrete_valuation_absolute {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) (e : ℝ≥0) (he : 1 < e) (x : K) :
    discreteValuationAbsolute v e he x =
      WithZeroMulInt.toNNReal (ne_zero_of_lt he) (v x) :=
  rfl

/-- Evaluation in additive notation: `v x = exp n` gives absolute value
`e ^ n`.  Taking `n = -ord x` is Milne's displayed `(1 / e) ^ ord x`. -/
theorem discrete_valuation_exp
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (e : ℝ≥0) (he : 1 < e) {x : K} {n : ℤ}
    (hx : v x = WithZero.exp n) :
    discreteValuationAbsolute v e he x = (e : ℝ) ^ n := by
  rw [discrete_valuation_absolute, hx]
  simp [WithZeroMulInt.toNNReal, WithZero.exp]

/-- The absolute value constructed from a discrete valuation is
nonarchimedean. -/
theorem discrete_valuation_nonarchimedean
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (e : ℝ≥0) (he : 1 < e) :
    IsNonarchimedean (discreteValuationAbsolute v e he) :=
  abv_def_nonarchimedean v e he

/-- The normalized rational `p`-adic absolute value obtained from the general
discrete-valuation construction by choosing the base `e = p`. -/
noncomputable def rationalAbsoluteValue (p : ℕ) [hp : Fact p.Prime] :
    AbsoluteValue ℚ ℝ :=
  discreteValuationAbsolute (Rat.padicValuation p) (p : ℝ≥0)
    (by exact_mod_cast hp.out.one_lt)

/-- Milne's normalized formula `|x|ₚ = p ^ (-ordₚ x)` for nonzero rationals. -/
theorem rational_padic_absolute
    (p : ℕ) [hp : Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    rationalAbsoluteValue p x =
      (p : ℝ) ^ (-padicValRat p x) := by
  unfold rationalAbsoluteValue
  apply discrete_valuation_exp
  simp [Rat.padicValuation, hx]

/-- The normalized rational `p`-adic absolute value is nonarchimedean. -/
theorem rational_absolute_nonarchimedean
    (p : ℕ) [hp : Fact p.Prime] :
    IsNonarchimedean (rationalAbsoluteValue p) :=
  discrete_valuation_nonarchimedean
    (Rat.padicValuation p) (p : ℝ≥0) (by exact_mod_cast hp.out.one_lt)

/-- Milne, Example 7.1(b): the normalized absolute value attached to a prime ideal of a
number field. -/
noncomputable def primeAbsoluteValue {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AbsoluteValue K ℝ :=
  NumberField.HeightOneSpectrum.adicAbv K v

/-- The normalized prime-ideal absolute value is nonarchimedean. -/
theorem absolute_value_nonarchimedean {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsNonarchimedean (primeAbsoluteValue v) :=
  NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v

/-- The normalized prime-ideal value is the absolute norm of the prime raised
to its multiplicative integer valuation. -/
theorem prime_absolute_value {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : K) :
    primeAbsoluteValue v x =
      WithZeroMulInt.toNNReal
        (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
        (v.valuation K x) :=
  rfl

/-- Milne's normalized finite-place formula for a nonzero algebraic integer:
its prime-ideal absolute value is the reciprocal of the norm of the largest
power of the prime dividing its principal ideal. -/
theorem absolute_abs_norm {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {x : NumberField.RingOfIntegers K} (hx : x ≠ 0) :
    primeAbsoluteValue v (algebraMap _ K x) *
        Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) = 1 := by
  change NumberField.HeightOneSpectrum.adicAbv K v (algebraMap _ K x) *
      Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) = 1
  rw [← NumberField.FinitePlace.norm_embedding]
  exact NumberField.HeightOneSpectrum.embedding_mul_absNorm K v hx

/-- Milne, Example 7.1(c): the trivial absolute value. -/
noncomputable def trivialAbsoluteValue (K : Type*) [Field K] : AbsoluteValue K ℝ := by
  letI := Classical.decEq K
  exact AbsoluteValue.trivial

@[simp]
theorem trivial_absolute_value {K : Type*} [Field K] {x : K}
    (hx : x ≠ 0) : trivialAbsoluteValue K x = 1 := by
  classical
  exact AbsoluteValue.trivial_apply hx

/-- Every absolute value on a finite field is trivial. -/
theorem absolute_value_trivial {K : Type*} [Field K] [Finite K]
    (v : AbsoluteValue K ℝ) : v = trivialAbsoluteValue K := by
  letI := Fintype.ofFinite K
  ext x
  by_cases hx : x = 0
  · subst x
    simp [trivialAbsoluteValue]
  · rw [trivial_absolute_value hx]
    have hpow : v x ^ (Fintype.card K - 1) = 1 := by
      rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one]
    exact (pow_eq_one_iff_of_nonneg (v.nonneg x)
      (Nat.sub_ne_zero_iff_lt.mpr Fintype.one_lt_card)).mp hpow

end Towers.NumberTheory.Milne
