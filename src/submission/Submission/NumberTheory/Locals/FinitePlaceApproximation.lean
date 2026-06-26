import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Milne, Chapter 7, Exercise 7-1

The Chinese remainder construction behind the finite-place approximation
theorem, including its common-denominator control.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped NNReal WithZero

section PrimePowerEstimate

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Membership in the `n`th power of a finite prime gives the expected
geometric bound for its adic absolute value. -/
theorem adic_abv_pow (v : HeightOneSpectrum R)
    {b : ℝ≥0} (hb : 1 < b) {r : R} {n : ℕ} (hr : r ∈ v.asIdeal ^ n) :
    v.adicAbv hb (algebraMap R K r) ≤ (b : ℝ)⁻¹ ^ n := by
  rw [v.adicAbv_of_algebraMap]
  have hval := (v.intValuation_le_pow_iff_mem r n).2 hr
  have hmap := (WithZeroMulInt.toNNReal_strictMono hb).monotone hval
  norm_cast
  simpa [HeightOneSpectrum.intAdicAbv, HeightOneSpectrum.intAdicAbvDef,
    WithZeroMulInt.toNNReal] using hmap

end PrimePowerEstimate

section Exercise

variable {R K ι : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Finite ι]

/-- Milne, Exercise 7-1, in its finite-place form.  Starting from a common
denominator `d` for finitely many targets, CRT produces an approximation which
is arbitrarily close at the selected finite places.  At every finite place
(hence in particular at every unselected one), its size is at most
`1 / |d|`.

The positive parameters `q i` choose the usual rank-one normalization of the
selected adic absolute values. -/
theorem finite_place_approximation
    (v : ι → HeightOneSpectrum R) (hv : Function.Injective v)
    (q : ι → ℝ≥0) (hq : ∀ i, 1 < q i)
    (target : ι → K) (d : R) (hd : d ≠ 0)
    (numerator : ι → R)
    (hden : ∀ i, algebraMap R K d * target i = algebraMap R K (numerator i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K,
      (∀ i, (v i).adicAbv (hq i) (x - target i) < ε) ∧
      ∀ (w : HeightOneSpectrum R) (c : ℝ≥0) (hc : 1 < c),
        w.adicAbv hc x ≤ 1 / w.adicAbv hc (algebraMap R K d) := by
  classical
  letI := Fintype.ofFinite ι
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne hd
  choose e he using fun i ↦
    exists_pow_lt_of_lt_one
      (mul_pos hε (((v i).adicAbv (hq i)).pos hdK))
      (show (q i : ℝ)⁻¹ < 1 by
        have hqreal : (1 : ℝ) < q i := by exact_mod_cast hq i
        exact (inv_lt_one₀ (zero_lt_one.trans hqreal)).2 hqreal)
  have hprime : ∀ i : ι, Prime (v i).asIdeal := fun i ↦
    Ideal.prime_of_isPrime (v i).ne_bot (v i).isPrime
  have hcoprime : Pairwise fun i j ↦ (v i).asIdeal ≠ (v j).asIdeal := by
    intro i j hij hEq
    apply hij
    apply hv
    exact HeightOneSpectrum.ext hEq
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := Finset.univ) (fun i ↦ (v i).asIdeal) e
    (fun i _ ↦ hprime i)
    (fun i _ j _ hij ↦ hcoprime hij) (fun i ↦ numerator i)
  refine ⟨algebraMap R K b / algebraMap R K d, ?_, ?_⟩
  · intro i
    have hsub :
        algebraMap R K b / algebraMap R K d - target i =
          algebraMap R K (b - numerator i) / algebraMap R K d := by
      field_simp [hdK]
      rw [hden i, map_sub]
    rw [hsub, map_div₀]
    have hnum := adic_abv_pow (K := K) (v i) (hq i)
      (hb i (Finset.mem_univ i))
    apply (div_lt_iff₀ ((v i).adicAbv (hq i) |>.pos hdK)).2
    exact hnum.trans_lt (he i)
  · intro w c hc
    rw [map_div₀]
    exact (div_le_div_iff_of_pos_right (w.adicAbv hc |>.pos hdK)).2
      (w.adicAbv_coe_le_one hc b)

/-- The literal number-field specialization of Exercise 7-1, using the
standard normalization `|x|_𝔭 = N(𝔭)^{-v_𝔭(x)}`. -/
theorem placeApproximationnumberField
    {F ι : Type*} [Field F] [NumberField F] [Finite ι]
    (v : ι → HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hv : Function.Injective v)
    (target : ι → F) (d : NumberField.RingOfIntegers F) (hd : d ≠ 0)
    (numerator : ι → NumberField.RingOfIntegers F)
    (hden : ∀ i, algebraMap (NumberField.RingOfIntegers F) F d * target i =
      algebraMap (NumberField.RingOfIntegers F) F (numerator i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F,
      (∀ i, NumberField.HeightOneSpectrum.adicAbv F (v i) (x - target i) < ε) ∧
      ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        NumberField.HeightOneSpectrum.adicAbv F w x ≤
          1 / NumberField.HeightOneSpectrum.adicAbv F w
            (algebraMap (NumberField.RingOfIntegers F) F d) := by
  let q : ι → ℝ≥0 := fun i ↦ Ideal.absNorm (v i).asIdeal
  have hq : ∀ i, 1 < q i := fun i ↦
    NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v i)
  obtain ⟨x, hx, hbound⟩ :=
    finite_place_approximation v hv q hq target d hd numerator hden hε
  refine ⟨x, ?_, ?_⟩
  · exact hx
  · intro w
    exact hbound w (Ideal.absNorm w.asIdeal)
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)

end Exercise

end Submission.NumberTheory.Milne
