import Mathlib
import Submission.NumberTheory.ClassGroup.CubicNumberExample
import Submission.NumberTheory.ClassGroup.NoExtensionQ
import Submission.NumberTheory.Units.UnitTheorem

/-!
# Milne, Algebraic Number Theory, Lemma 5.13

The analytic estimate for the discriminant of a cubic unit having one real conjugate and a
complex-conjugate pair.  We also record the integral-basis divisibility step used to pass from the
discriminant of the power basis to the discriminant of the number field.
-/

namespace Submission.NumberTheory.Milne

open Set
open scoped NumberField

private noncomputable def cubicVandermondeFactor (a x : ℝ) : ℝ :=
  (a - x) ^ 2 * (1 - x ^ 2)

private lemma cubic_vandermonde_continuous (a : ℝ) :
    Continuous (cubicVandermondeFactor a) := by
  unfold cubicVandermondeFactor
  fun_prop

private lemma deriv_cubic_vandermonde (a x : ℝ) :
    HasDerivAt (cubicVandermondeFactor a)
      (-2 * (a - x) * (1 + a * x - 2 * x ^ 2)) x := by
  unfold cubicVandermondeFactor
  convert (((hasDerivAt_const x a).sub (hasDerivAt_id x)).pow 2).mul
    ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)) using 1
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  ring

private lemma cubic_vandermonde_aux
    {t v x : ℝ} (ht : 1 < t) (hv : 0 < v) (htv : t * v = 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    16 * cubicVandermondeFactor ((t + v) / 2) x < 4 * t ^ 2 + 24 := by
  let a := (t + v) / 2
  let f := cubicVandermondeFactor a
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
      (cubic_vandermonde_continuous a).continuousOn
  have hle : f x ≤ f x₀ := hmax hx
  have hv_lt_one : v < 1 := by
    nlinarith [mul_pos (sub_pos.mpr ht) hv]
  have ht_pos : 0 < t := lt_trans zero_lt_one ht
  have ha_gt_one : 1 < a := by
    dsimp [a]
    have hsquare : 0 ≤ (t - 1) ^ 2 := sq_nonneg (t - 1)
    nlinarith [htv]
  by_cases hleft : x₀ = -1
  · subst x₀
    have hf_nonpos : f x ≤ 0 := by simpa [f, cubicVandermondeFactor] using hle
    have hrhs : 0 < 4 * t ^ 2 + 24 := by positivity
    nlinarith
  by_cases hright : x₀ = 1
  · subst x₀
    have hf_nonpos : f x ≤ 0 := by simpa [f, cubicVandermondeFactor] using hle
    have hrhs : 0 < 4 * t ^ 2 + 24 := by positivity
    nlinarith
  have hx₀int : x₀ ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx₀.1 (Ne.symm hleft), lt_of_le_of_ne hx₀.2 hright⟩
  have hderiv : deriv f x₀ = 0 :=
    (hmax.isLocalMax (Filter.mem_of_superset (Ioo_mem_nhds hx₀int.1 hx₀int.2)
      (fun _ hy ↦ ⟨hy.1.le, hy.2.le⟩))).deriv_eq_zero
  have hcritical_product :
      -2 * (a - x₀) * (1 + a * x₀ - 2 * x₀ ^ 2) = 0 := by
    rw [← (deriv_cubic_vandermonde a x₀).deriv]
    exact hderiv
  have hax_ne : a - x₀ ≠ 0 := by
    nlinarith [hx₀.2]
  have hcritical : a * x₀ - 2 * x₀ ^ 2 + 1 = 0 := by
    rcases mul_eq_zero.mp hcritical_product with htwo | hrest
    · exact (hax_ne (by nlinarith [htwo])).elim
    · nlinarith [hrest]
  have hx₀neg : x₀ < 0 := by
    by_contra h
    have hx₀nonneg : 0 ≤ x₀ := le_of_not_gt h
    have hx₀pos : 0 < x₀ := by
      apply lt_of_le_of_ne hx₀nonneg
      intro hxzero
      subst x₀
      norm_num at hcritical
    have hmul_strict : x₀ < a * x₀ := by
      nlinarith [mul_pos (sub_pos.mpr ha_gt_one) hx₀pos]
    have hfactor : (2 * x₀ + 1) * (x₀ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hx₀.2)
    nlinarith [hfactor]
  have hx₀_lt : x₀ < -v / 2 := by
    by_contra h
    have hlower : -v / 2 ≤ x₀ := le_of_not_gt h
    have hxsq : x₀ ^ 2 ≤ v ^ 2 / 4 := by
      have habs : |x₀| ≤ v / 2 := by
        rw [abs_of_neg hx₀neg]
        nlinarith
      have habs' : |x₀| ≤ |v / 2| := by
        simpa [abs_of_nonneg (by nlinarith [hv] : 0 ≤ v / 2)] using habs
      have hsquare := sq_le_sq.mpr habs'
      nlinarith
    have hminusax : -a * x₀ ≤ a * v / 2 := by
      have ha_pos : 0 < a := lt_trans zero_lt_one ha_gt_one
      nlinarith
    have hav : a * v = (v ^ 2 + 1) / 2 := by
      dsimp [a]
      nlinarith [htv]
    have hv_sq_lt : v ^ 2 < 1 := by nlinarith
    nlinarith
  have hx₀sq : v ^ 2 / 4 < x₀ ^ 2 := by
    have hnegv : -v / 2 < 0 := by nlinarith
    have habs : |(-v / 2)| < |x₀| := by
      rw [abs_of_neg hnegv, abs_of_neg hx₀neg]
      nlinarith
    have hsquare := sq_lt_sq.mpr habs
    nlinarith
  have hfactor_value :
      cubicVandermondeFactor a x₀ = a ^ 2 + 1 - x₀ ^ 2 - x₀ ^ 4 := by
    unfold cubicVandermondeFactor
    nlinarith [sq_nonneg (a - x₀), sq_nonneg x₀]
  have ha_sq : 4 * a ^ 2 = t ^ 2 + 2 + v ^ 2 := by
    dsimp [a]
    nlinarith [htv]
  have hstrict :
      16 * cubicVandermondeFactor a x₀ < 4 * t ^ 2 + 24 := by
    rw [hfactor_value]
    nlinarith [sq_nonneg (x₀ ^ 2)]
  exact (mul_le_mul_of_nonneg_left hle (by norm_num)).trans_lt hstrict

/-- The analytic inequality at the heart of Milne's Lemma 5.13.  If the real conjugate is
`ε = u²`, put `t = u³`; the other two conjugates have modulus `t⁻¹` after taking the
Vandermonde product.  Writing `x = cos θ` gives exactly the expression on the left. -/
theorem cubic_vandermonde_factor {u x : ℝ} (hu : 1 < u)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2)) <
      4 * u ^ 6 + 24 := by
  have ht : 1 < u ^ 3 := one_lt_pow₀ hu (by norm_num)
  have hupos : 0 < u ^ 3 := lt_trans zero_lt_one ht
  have hinvpos : 0 < (u ^ 3)⁻¹ := inv_pos.mpr hupos
  have hmul : u ^ 3 * (u ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hupos)
  convert cubic_vandermonde_aux ht hinvpos hmul hx using 1
  all_goals ring

/-- **Milne, Lemma 5.13 (field-discriminant form).**

This formulation exposes precisely the conjugate calculation in the printed proof.  The basis is
the power basis `(1, ε, ε²)`; `hdisc` is the Vandermonde calculation after writing the two
nonreal conjugates as `u⁻¹ exp(± iθ)` and putting `x = cos θ`.  The hypotheses `hepsilon` and
`hu` say `ε = u² > 1`.  The conclusion is the literal bound
`|Δ_K| < 4 ε³ + 24`.

The integral-basis index formula supplies the last step of Milne's proof: the field discriminant
divides the power-basis discriminant with square quotient. -/
theorem cubic_field_discr
    (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin 3) ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    {epsilon u x : ℝ} (hepsilon : epsilon = u ^ 2) (hu : 1 < u)
    (hx : x ∈ Icc (-1 : ℝ) 1)
    (hdisc : abs ((Algebra.discr ℚ b : ℚ) : ℝ) =
      16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2))) :
    abs (NumberField.discr K : ℝ) < 4 * epsilon ^ 3 + 24 := by
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K b hb
  have hd_ne : d ≠ 0 := by
    intro hd_zero
    subst d
    norm_num at hd
    exact (Algebra.discr_not_zero_of_basis ℚ b) hd
  have hd_real :
      (↑(Algebra.discr ℚ b) : ℝ) =
        (↑d : ℝ) ^ 2 * ↑(NumberField.discr K) := by
    exact_mod_cast hd
  have hd_abs : 1 ≤ |(↑d : ℝ)| := by
    exact_mod_cast Int.one_le_abs hd_ne
  have hfield_le_basis :
      abs (NumberField.discr K : ℝ) ≤ abs ((Algebra.discr ℚ b : ℚ) : ℝ) := by
    rw [hd_real, abs_mul, abs_pow]
    exact le_mul_of_one_le_left (abs_nonneg (↑(NumberField.discr K) : ℝ))
      (by nlinarith [sq_nonneg |(↑d : ℝ)|])
  calc
    abs (NumberField.discr K : ℝ) ≤ abs ((Algebra.discr ℚ b : ℚ) : ℝ) := hfield_le_basis
    _ = 16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2)) := hdisc
    _ < 4 * u ^ 6 + 24 := cubic_vandermonde_factor hu hx
    _ = 4 * epsilon ^ 3 + 24 := by rw [hepsilon]; ring

/-- The discriminant of the power basis `(1, ε, ε²)` is the square of the
Vandermonde product of the three conjugates. -/
theorem cubic_discr_vandermonde
    (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin 3) ℚ K) (epsilonK : K)
    (hb : ∀ i, b i = epsilonK ^ (i : ℕ))
    (e : Fin 3 ≃ (K →ₐ[ℚ] ℂ)) {a z w : ℂ}
    (ha : e 0 epsilonK = a) (hz : e 1 epsilonK = z)
    (hw : e 2 epsilonK = w) :
    algebraMap ℚ ℂ (Algebra.discr ℚ b) =
      ((z - a) * (w - a) * (w - z)) ^ 2 := by
  rw [Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e]
  congr 1
  rw [Matrix.det_fin_three]
  simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
    Matrix.reindex_apply, hb]
  norm_num [ha, hz, hw]
  ring

/-- The squared norm of the cubic Vandermonde product in Milne's trigonometric
parameterization. -/
theorem sq_vandermonde_parameterization
    {u x y : ℝ} (hu : u ≠ 0) (hcircle : x ^ 2 + y ^ 2 = 1) :
    Complex.normSq
        ((((u ^ 2 : ℝ) : ℂ) - ⟨u⁻¹ * x, u⁻¹ * y⟩) *
          ((((u ^ 2 : ℝ) : ℂ) - starRingEnd ℂ ⟨u⁻¹ * x, u⁻¹ * y⟩) *
            (⟨u⁻¹ * x, u⁻¹ * y⟩ - starRingEnd ℂ ⟨u⁻¹ * x, u⁻¹ * y⟩))) =
      16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2)) := by
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.ofReal_re,
    Complex.conj_re, Complex.sub_im, Complex.ofReal_im, Complex.conj_im, zero_sub]
  field_simp [hu]
  ring_nf at hcircle ⊢
  have hy : y ^ 2 = 1 - x ^ 2 := by nlinarith
  rw [show y ^ 4 = (y ^ 2) ^ 2 by ring,
    show y ^ 6 = (y ^ 2) ^ 3 by ring, hy]
  ring

/-- Lemma 5.13 after the three embeddings have been parameterized by a point on
the unit circle.  Unlike `cubic_field_discr`, this derives the power-basis
discriminant identity. -/
theorem discr_parameterized_embeddings
    (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin 3) ℚ K) (epsilonK : K)
    (hb : ∀ i, b i = epsilonK ^ (i : ℕ))
    (hintegral : IsIntegral ℤ epsilonK)
    (e : Fin 3 ≃ (K →ₐ[ℚ] ℂ))
    {u x y : ℝ} (hu : 1 < u) (hcircle : x ^ 2 + y ^ 2 = 1)
    (he0 : e 0 epsilonK = ((u ^ 2 : ℝ) : ℂ))
    (he1 : e 1 epsilonK = (⟨u⁻¹ * x, u⁻¹ * y⟩ : ℂ))
    (he2 : e 2 epsilonK = starRingEnd ℂ (⟨u⁻¹ * x, u⁻¹ * y⟩ : ℂ)) :
    abs (NumberField.discr K : ℝ) < 4 * (u ^ 2) ^ 3 + 24 := by
  let z : ℂ := ⟨u⁻¹ * x, u⁻¹ * y⟩
  let a : ℂ := ((u ^ 2 : ℝ) : ℂ)
  let p : ℂ := (a - z) * ((a - starRingEnd ℂ z) * (z - starRingEnd ℂ z))
  have hdiscComplex :
      algebraMap ℚ ℂ (Algebra.discr ℚ b) =
        ((z - a) * (starRingEnd ℂ z - a) * (starRingEnd ℂ z - z)) ^ 2 :=
    cubic_discr_vandermonde K b epsilonK hb e he0 he1 he2
  have hproduct :
      (z - a) * (starRingEnd ℂ z - a) * (starRingEnd ℂ z - z) = -p := by
    dsimp [p]
    ring
  have hdisc : abs ((Algebra.discr ℚ b : ℚ) : ℝ) =
      16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2)) := by
    calc
      abs ((Algebra.discr ℚ b : ℚ) : ℝ) =
          ‖(algebraMap ℚ ℂ (Algebra.discr ℚ b))‖ := by
        rw [← Real.norm_eq_abs]
        change ‖((Algebra.discr ℚ b : ℚ) : ℝ)‖ =
          ‖((Algebra.discr ℚ b : ℚ) : ℂ)‖
        rw [← Complex.ofReal_ratCast, Complex.norm_real]
      _ = ‖((z - a) * (starRingEnd ℂ z - a) *
          (starRingEnd ℂ z - z)) ^ 2‖ := by rw [hdiscComplex]
      _ = Complex.normSq ((z - a) * (starRingEnd ℂ z - a) *
          (starRingEnd ℂ z - z)) := by
        rw [norm_pow, Complex.sq_norm]
      _ = Complex.normSq p := by rw [hproduct, Complex.normSq_neg]
      _ = 16 * (((u ^ 3 + (u ^ 3)⁻¹) / 2 - x) ^ 2 * (1 - x ^ 2)) := by
        dsimp [p, a, z]
        exact sq_vandermonde_parameterization
          (ne_of_gt (lt_trans zero_lt_one hu)) hcircle
  have hx : x ∈ Icc (-1 : ℝ) 1 := by
    have hxSq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
    constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  apply cubic_field_discr K b (epsilon := u ^ 2) (u := u) (x := x)
    ?_ rfl hu hx hdisc
  intro i
  rw [hb]
  exact hintegral.pow _

/-- Lemma 5.13 assuming the two nonreal conjugates are complex conjugates and
their product with the real conjugate is one. -/
theorem discr_conjugate_embeddings
    (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin 3) ℚ K) (epsilonK : K)
    (hb : ∀ i, b i = epsilonK ^ (i : ℕ))
    (hintegral : IsIntegral ℤ epsilonK)
    (e : Fin 3 ≃ (K →ₐ[ℚ] ℂ))
    {u : ℝ} (hu : 1 < u) {z : ℂ}
    (he0 : e 0 epsilonK = ((u ^ 2 : ℝ) : ℂ))
    (he1 : e 1 epsilonK = z)
    (he2 : e 2 epsilonK = starRingEnd ℂ z)
    (hnorm : u ^ 2 * Complex.normSq z = 1) :
    abs (NumberField.discr K : ℝ) < 4 * (u ^ 2) ^ 3 + 24 := by
  let x := u * z.re
  let y := u * z.im
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one hu)
  have hcircle : x ^ 2 + y ^ 2 = 1 := by
    dsimp [x, y]
    calc
      (u * z.re) ^ 2 + (u * z.im) ^ 2 =
          u ^ 2 * (z.re * z.re + z.im * z.im) := by ring
      _ = 1 := by rw [← Complex.normSq_apply, hnorm]
  have hz : (⟨u⁻¹ * x, u⁻¹ * y⟩ : ℂ) = z := by
    apply Complex.ext <;> dsimp [x, y] <;> field_simp
  apply discr_parameterized_embeddings K b epsilonK hb hintegral e
      hu hcircle he0
  · simpa [hz] using he1
  · simpa [hz] using he2

/-- The unit norm condition in Lemma 5.13 forces norm `+1`: norm `-1` is
impossible because the real conjugate and the squared modulus are positive. -/
theorem cubic_discr_conjugates
    (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin 3) ℚ K) (epsilonK : K)
    (hb : ∀ i, b i = epsilonK ^ (i : ℕ))
    (hintegral : IsIntegral ℤ epsilonK)
    (hnormUnit : Algebra.norm ℚ epsilonK = 1 ∨ Algebra.norm ℚ epsilonK = -1)
    (e : Fin 3 ≃ (K →ₐ[ℚ] ℂ))
    {u : ℝ} (hu : 1 < u) {z : ℂ}
    (he0 : e 0 epsilonK = ((u ^ 2 : ℝ) : ℂ))
    (he1 : e 1 epsilonK = z)
    (he2 : e 2 epsilonK = starRingEnd ℂ z) :
    abs (NumberField.discr K : ℝ) < 4 * (u ^ 2) ^ 3 + 24 := by
  have hnormEmb := Algebra.norm_eq_prod_embeddings ℚ ℂ epsilonK
  rw [← e.prod_comp] at hnormEmb
  rw [Fin.prod_univ_three, he0, he1, he2] at hnormEmb
  have hnormReal : (Algebra.norm ℚ epsilonK : ℝ) =
      u ^ 2 * Complex.normSq z := by
    have hre := congrArg Complex.re hnormEmb
    norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre
    rw [Complex.normSq_apply]
    linear_combination hre
  have hnorm : u ^ 2 * Complex.normSq z = 1 := by
    rcases hnormUnit with hplus | hminus
    · rw [hplus] at hnormReal
      norm_num at hnormReal ⊢
      exact hnormReal.symm
    · rw [hminus] at hnormReal
      have hnonneg : 0 ≤ u ^ 2 * Complex.normSq z :=
        mul_nonneg (sq_nonneg u) (Complex.normSq_nonneg z)
      norm_num at hnormReal
      nlinarith
  exact discr_conjugate_embeddings K b epsilonK hb hintegral e
    hu he0 he1 he2 hnorm

/-- **Milne, Lemma 5.13 (unit-conjugate form).** For an actual ring-of-integers
unit, the norm and integrality hypotheses used in the printed proof are automatic. -/
theorem discr_integers_conjugates
    (K : Type*) [Field K] [NumberField K]
    (epsilon : (𝓞 K)ˣ) (b : Module.Basis (Fin 3) ℚ K)
    (hb : ∀ i, b i = (epsilon : K) ^ (i : ℕ))
    (e : Fin 3 ≃ (K →ₐ[ℚ] ℂ))
    {u : ℝ} (hu : 1 < u) {z : ℂ}
    (he0 : e 0 (epsilon : K) = ((u ^ 2 : ℝ) : ℂ))
    (he1 : e 1 (epsilon : K) = z)
    (he2 : e 2 (epsilon : K) = starRingEnd ℂ z) :
    abs (NumberField.discr K : ℝ) < 4 * (u ^ 2) ^ 3 + 24 := by
  exact cubic_discr_conjugates K b (epsilon : K) hb
    epsilon.val.isIntegral_coe
    ((integers_or_neg K epsilon.val).mp epsilon.isUnit)
    e hu he0 he1 he2

private def cubicAlgHom {K : Type*} [Field K] [NumberField K]
    (phi : K →ₐ[ℚ] ℂ) : K →ₐ[ℚ] ℂ where
  __ := (starRingEnd ℂ).comp phi.toRingHom
  commutes' q := by simp

@[simp] private theorem cubic_alg_hom
    {K : Type*} [Field K] [NumberField K]
    (phi : K →ₐ[ℚ] ℂ) (x : K) :
    cubicAlgHom phi x = starRingEnd ℂ (phi x) := rfl

private theorem cubic_alg_involutive
    {K : Type*} [Field K] [NumberField K] :
    Function.Involutive (cubicAlgHom : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ)) := by
  intro phi
  ext x
  simp [cubicAlgHom]

/-- A unit of a cubic number field that lies in the rational subfield is torsion. -/
theorem cubic_rational_torsion
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) (epsilon : (𝓞 K)ˣ)
    (hrat : (epsilon : K) ∈ (algebraMap ℚ K).range) :
    epsilon ∈ NumberField.Units.torsion K := by
  obtain ⟨q, hq⟩ := hrat
  have hnorm :=
    (integers_or_neg K epsilon.val).mp epsilon.isUnit
  have hqcube : q ^ 3 = 1 ∨ q ^ 3 = -1 := by
    simpa only [← hdegree, ← Algebra.norm_algebraMap, hq] using hnorm
  have hqpm : q = 1 ∨ q = -1 := by
    rcases hqcube with hplus | hminus
    · left
      have hfac : (q - 1) * (q ^ 2 + q + 1) = 0 := by nlinarith
      have hpos : 0 < q ^ 2 + q + 1 := by
        nlinarith [sq_nonneg (q + 1 / 2)]
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · exact (ne_of_gt hpos h).elim
    · right
      have hfac : (q + 1) * (q ^ 2 - q + 1) = 0 := by nlinarith
      have hpos : 0 < q ^ 2 - q + 1 := by
        nlinarith [sq_nonneg (q - 1 / 2)]
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · exact (ne_of_gt hpos h).elim
  rcases hqpm with rfl | rfl
  · have he : epsilon = 1 := by
      apply NumberField.Units.coe_injective
      simpa using hq.symm
    rw [he]
    exact (NumberField.Units.torsion K).one_mem
  · have he : epsilon = -1 := by
      apply NumberField.Units.coe_injective
      simpa using hq.symm
    rw [he]
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by simp⟩

/-- Every member of Mathlib's chosen fundamental system represents a nonzero
class modulo the torsion subgroup. -/
theorem fundamental_system_not
    (K : Type*) [Field K] [NumberField K]
    (i : Fin (NumberField.Units.rank K)) :
    NumberField.Units.fundSystem K i ∉ NumberField.Units.torsion K := by
  intro hi
  have hmk : QuotientGroup.mk (NumberField.Units.fundSystem K i) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hi
  have hfund := NumberField.Units.fundSystem_mk K i
  rw [hmk] at hfund
  have hbzero : NumberField.Units.basisModTorsion K i = 0 := by
    simpa using hfund.symm
  have hrepr := (NumberField.Units.basisModTorsion K).repr_self i
  rw [hbzero, map_zero] at hrepr
  have hcoord := congrArg (fun f ↦ f i) hrepr
  simp at hcoord

/-- **Milne, Lemma 5.13.** Let `K` be a cubic number field of negative
discriminant.  Every nontorsion integral unit whose value at a real embedding is
greater than one satisfies Milne's discriminant bound.  In particular this
applies to the positive fundamental unit used in the text. -/
theorem cubic_discr_nontorsion
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) (hdiscr : NumberField.discr K < 0)
    (epsilon : (𝓞 K)ˣ) (hnontorsion : epsilon ∉ NumberField.Units.torsion K)
    (sigma : K →ₐ[ℚ] ℝ) (hepsilon : 1 < sigma (epsilon : K)) :
    abs (NumberField.discr K : ℝ) < 4 * (sigma (epsilon : K)) ^ 3 + 24 := by
  classical
  let epsilonK : K := (epsilon : K)
  have hnotrat : epsilonK ∉ (algebraMap ℚ K).range := by
    intro hrat
    exact hnontorsion (cubic_rational_torsion K hdegree epsilon hrat)
  have hintQ : IsIntegral ℚ epsilonK := IsIntegral.of_finite ℚ epsilonK
  have hdegdvd : (minpoly ℚ epsilonK).natDegree ∣ 3 := by
    rw [← hdegree]
    exact minpoly.degree_dvd hintQ
  have hdeg2 : 2 ≤ (minpoly ℚ epsilonK).natDegree :=
    (minpoly.two_le_natDegree_iff hintQ).2 hnotrat
  have hdeg : (minpoly ℚ epsilonK).natDegree = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdegdvd with h | h
    · omega
    · exact h
  have hprimIF : IntermediateField.adjoin ℚ {epsilonK} = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq ℚ epsilonK).2
      (hdeg.trans hdegree.symm)
  have hprim : Algebra.adjoin ℚ {epsilonK} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hintQ.isAlgebraic hprimIF
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hintQ hprim
  have hpgen : pb.gen = epsilonK := PowerBasis.ofAdjoinEqTop_gen hintQ hprim
  have hpdim : pb.dim = 3 := by
    rw [PowerBasis.ofAdjoinEqTop_dim, hdeg]
  let b : Module.Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr hpdim)
  have hb : ∀ i, b i = epsilonK ^ (i : ℕ) := by
    intro i
    simp [b, hpgen]
  have hc : NumberField.InfinitePlace.nrComplexPlaces K = 1 :=
    discr_nr_complex K hdegree hdiscr
  have hr : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
    have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hc, hdegree] at hsig
    omega
  let sigmaC : K →ₐ[ℚ] ℂ := (Complex.ofRealAm.restrictScalars ℚ).comp sigma
  have hsigmaReal : NumberField.ComplexEmbedding.IsReal sigmaC.toRingHom := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [sigmaC, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hrealSub :
      Subsingleton {phi : K →+* ℂ // NumberField.ComplexEmbedding.IsReal phi} :=
    letI : Fintype {phi : K →+* ℂ // NumberField.ComplexEmbedding.IsReal phi} :=
      Subtype.fintype _
    Fintype.card_le_one_iff_subsingleton.mp (by
      have hcard : Fintype.card
          {phi : K →+* ℂ // NumberField.ComplexEmbedding.IsReal phi} = 1 := by
        simpa only [hr] using NumberField.InfinitePlace.card_real_embeddings K
      exact hcard.le)
  have realAlgHom_eq (phi psi : K →ₐ[ℚ] ℂ)
      (hphi : NumberField.ComplexEmbedding.IsReal phi.toRingHom)
      (hpsi : NumberField.ComplexEmbedding.IsReal psi.toRingHom) : phi = psi := by
    have hsub :
        (⟨phi.toRingHom, hphi⟩ :
            {f : K →+* ℂ // NumberField.ComplexEmbedding.IsReal f}) =
          ⟨psi.toRingHom, hpsi⟩ := @Subsingleton.elim _ hrealSub _ _
    ext x
    exact DFunLike.congr_fun (congrArg Subtype.val hsub) x
  have hcardEmb : Fintype.card (K →ₐ[ℚ] ℂ) = 3 := by
    rw [AlgHom.card ℚ K ℂ, hdegree]
  let eBase : Fin 3 ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by simp [hcardEmb])
  let e : Fin 3 ≃ (K →ₐ[ℚ] ℂ) := eBase.setValue 0 sigmaC
  have he0map : e 0 = sigmaC := Equiv.setValue_eq eBase 0 sigmaC
  have he10 : e 1 ≠ sigmaC := by
    rw [← he0map]
    intro h
    have := e.injective h
    norm_num at this
  have he1notReal : ¬ NumberField.ComplexEmbedding.IsReal (e 1).toRingHom := by
    intro hreal
    exact he10 (realAlgHom_eq (e 1) sigmaC hreal hsigmaReal)
  have hconj1 : cubicAlgHom (e 1) = e 2 := by
    obtain ⟨i, hi⟩ := e.surjective (cubicAlgHom (e 1))
    fin_cases i
    · exfalso
      apply he10
      calc
        e 1 = cubicAlgHom (cubicAlgHom (e 1)) :=
          (cubic_alg_involutive (e 1)).symm
        _ = cubicAlgHom (e 0) := congrArg cubicAlgHom hi.symm
        _ = cubicAlgHom sigmaC := congrArg cubicAlgHom he0map
        _ = sigmaC := by ext x; simp [cubicAlgHom, sigmaC]
    · exfalso
      apply he1notReal
      rw [NumberField.ComplexEmbedding.isReal_iff]
      exact congrArg AlgHom.toRingHom hi.symm
    · exact hi.symm
  let u : ℝ := Real.sqrt (sigma epsilonK)
  have heps0 : 0 ≤ sigma epsilonK := le_trans (by norm_num) hepsilon.le
  have hu : 1 < u := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by positivity) hepsilon
  have hu2 : u ^ 2 = sigma epsilonK := Real.sq_sqrt heps0
  let z : ℂ := e 1 epsilonK
  have hres :=
    discr_integers_conjugates
      K epsilon b hb e (u := u) (z := z) hu (by
        rw [he0map]
        simp only [sigmaC, AlgHom.coe_comp, Function.comp_apply,
          AlgHom.restrictScalars_apply, Complex.ofRealAm_coe]
        rw [hu2]) rfl (by
        rw [← hconj1]
        change cubicAlgHom (e 1) epsilonK = starRingEnd ℂ z
        simp [z, cubicAlgHom])
  change abs (NumberField.discr K : ℝ) < 4 * (sigma epsilonK) ^ 3 + 24
  simpa only [hu2] using hres

/-- Lemma 5.13 specialized to one of Mathlib's chosen fundamental units.  The
positivity hypothesis selects its sign and inverse exactly as in Milne's text. -/
theorem discr_fundamental_system
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) (hdiscr : NumberField.discr K < 0)
    (i : Fin (NumberField.Units.rank K)) (sigma : K →ₐ[ℚ] ℝ)
    (hepsilon : 1 < sigma (NumberField.Units.fundSystem K i : K)) :
    abs (NumberField.discr K : ℝ) <
      4 * (sigma (NumberField.Units.fundSystem K i : K)) ^ 3 + 24 :=
  cubic_discr_nontorsion K hdegree hdiscr
    (NumberField.Units.fundSystem K i) (fundamental_system_not K i)
    sigma hepsilon

end Submission.NumberTheory.Milne
