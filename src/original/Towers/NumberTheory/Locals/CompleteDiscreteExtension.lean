import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Norm.Transitivity
import Towers.NumberTheory.Locals.LogarithmicValuation

/-!
# Extension of a complete nonarchimedean absolute value

This file records the spectral-norm form of Milne's Theorem 7.38.  Mathlib's
result is stronger in one direction: discreteness and separability are not
needed for existence, uniqueness, or completeness of a finite extension.  We
express discreteness through the logarithmic value group introduced in
`LogarithmicValuation` and prove that this property is preserved by a finite
extension.
-/

namespace Towers.NumberTheory.Milne

noncomputable section

open Module IntermediateField

private theorem discrete_topology_singleton
    (M : Submodule ℤ ℝ) {c : ℝ} (hc : c ≠ 0)
    (hM : M ≤ Submodule.span ℤ ({c} : Set ℝ)) :
    DiscreteTopology M := by
  apply DiscreteTopology.of_forall_le_norm (r := |c|) (abs_pos.mpr hc)
  intro x hx
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp (hM x.property)
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hx
    apply Subtype.ext
    simpa [hn0] using hn.symm
  have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn0
  change |c| ≤ |(x : ℝ)|
  rw [← hn]
  simp only [zsmul_eq_mul, abs_mul]
  nlinarith [abs_nonneg c]

section

variable (K L : Type*) [NontriviallyNormedField K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsUltrametricDist K] [CompleteSpace K]

/-- The canonical extension to `L` of the absolute value defined by the norm on `K`.

It is obtained from the spectral norm.  Completeness of `K` makes the spectral
norm multiplicative. -/
def completeAbsoluteValue : AbsoluteValue L ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue
    (spectralMulAlgNorm K L).toMulRingNorm

@[simp]
theorem complete_absolute_value (x : L) :
    completeAbsoluteValue K L x = spectralNorm K L x :=
  rfl

/-- The spectral absolute value extends the given norm on `K`. -/
@[simp]
theorem complete_absolute_algebra (x : K) :
    completeAbsoluteValue K L (algebraMap K L x) = ‖x‖ := by
  exact spectralNorm_extends x

/-- The extended absolute value remains nonarchimedean. -/
theorem complete_absolute_nonarchimedean :
    IsNonarchimedean (completeAbsoluteValue K L) :=
  isNonarchimedean_spectralNorm

/-- Uniqueness in Milne's Theorem 7.38: every real-valued absolute value on
`L` extending the norm on complete `K` equals the spectral absolute value. -/
theorem complete_absolute_unique
    (f : AbsoluteValue L ℝ)
    (hf : ∀ x : K, f (algebraMap K L x) = ‖x‖) :
    f = completeAbsoluteValue K L := by
  ext x
  exact spectralNorm_unique_field_norm_ext hf x

/-- **Milne, Corollary 7.40.** The absolute value of a complete
nonarchimedean field extends uniquely to every algebraic extension.

Milne assumes the extension is separable and the base absolute value is
discrete.  The spectral-norm theorem used here gives the stronger statement
without either assumption. -/
theorem unique_complete_absolute :
    ∃! f : AbsoluteValue L ℝ,
      ∀ x : K, f (algebraMap K L x) = ‖x‖ := by
  refine ⟨completeAbsoluteValue K L,
    complete_absolute_algebra K L, ?_⟩
  intro f hf
  exact complete_absolute_unique K L f hf

/-- The value of the unique extension can be read from the constant
coefficient of the minimal polynomial. -/
theorem complete_absolute_rpow (x : L) :
    completeAbsoluteValue K L x =
      ‖(minpoly K x).coeff 0‖ ^ (1 / (minpoly K x).natDegree : ℝ) := by
  exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x

/-- Milne's norm formula for the unique extension. -/
theorem complete_extension_rpow
    [FiniteDimensional K L] (x : L) :
    completeAbsoluteValue K L x =
      ‖Algebra.norm K x‖ ^ (1 / (finrank K L : ℝ)) := by
  rw [complete_absolute_rpow]
  rw [Algebra.norm_eq_norm_adjoin K x, norm_pow]
  rw [← IntermediateField.adjoin.powerBasis_gen
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, norm_mul, norm_pow]
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg ((minpoly K x).coeff 0))]
  congr 1
  rw [← Module.finrank_mul_finrank K K⟮x⟯ L, Nat.cast_mul]
  rw [IntermediateField.adjoin.finrank
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral]
  have hm : (minpoly K x).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsAlgebraic.isAlgebraic x).isIntegral).ne'
  have hd : finrank K⟮x⟯ L ≠ 0 := finrank_pos.ne'
  field_simp [hm, hd]

/-- The discreteness clause of Milne's Theorem 7.38.  If the logarithmic
value group of the absolute value on `K` is discrete, then the logarithmic
value group of its unique extension to a finite extension `L` is discrete as
well. -/
theorem complete_negative_discrete
    [FiniteDimensional K L]
    (hdiscrete : DiscreteTopology
      (negativeLogRange (NormedField.toAbsoluteValue K))) :
    DiscreteTopology
      (negativeLogRange (completeAbsoluteValue K L)) := by
  have hnontrivial :
      ∃ x : Kˣ, NormedField.toAbsoluteValue K x ≠ 1 := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      norm_num at hx
    refine ⟨Units.mk0 x hx0, ?_⟩
    exact ne_of_gt hx
  obtain ⟨c, hc, ord, -, hord⟩ :=
    discrete_negative_log
      (NormedField.toAbsoluteValue K) hnontrivial hdiscrete
  let d : ℝ := finrank K L
  have hd : d ≠ 0 := by
    have hdpos : 0 < d := by
      dsimp [d]
      exact_mod_cast (finrank_pos : 0 < finrank K L)
    exact hdpos.ne'
  apply discrete_topology_singleton
    (negativeLogRange (completeAbsoluteValue K L))
    (c := c / d) (div_ne_zero hc hd)
  intro r hr
  obtain ⟨x, rfl⟩ := hr
  let nx : Kˣ := Units.map (Algebra.norm K) x.toMul
  have hnorm_ne : Algebra.norm K (x.toMul : L) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr x.toMul.ne_zero
  have hlog :
      negativeLogHom (completeAbsoluteValue K L) x =
        (1 / d) * negativeLogHom (NormedField.toAbsoluteValue K)
          (Additive.ofMul nx) := by
    change -Real.log (completeAbsoluteValue K L (x.toMul : L)) =
      (1 / d) * (-Real.log ‖Algebra.norm K (x.toMul : L)‖)
    rw [complete_extension_rpow,
      Real.log_rpow (norm_pos_iff.mpr hnorm_ne)]
    dsimp [d]
    ring
  have hmem :
      negativeLogHom (completeAbsoluteValue K L) x ∈
        Submodule.span ℤ ({c / d} : Set ℝ) := by
    rw [hlog, hord]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨ord (Additive.ofMul nx), ?_⟩
    simp only [zsmul_eq_mul]
    field_simp [hd]
  simpa only [AddMonoidHom.coe_toIntLinearMap] using hmem

/-- The discreteness assertion in Milne's Remark 7.39: the canonical absolute
value on a finite extension has discrete logarithmic value group exactly when
the original absolute value does. -/
theorem complete_log_discrete
    [FiniteDimensional K L] :
    DiscreteTopology
        (negativeLogRange (completeAbsoluteValue K L)) ↔
      DiscreteTopology
        (negativeLogRange (NormedField.toAbsoluteValue K)) := by
  constructor
  · intro hL
    have hsubset :
        negativeLogRange (NormedField.toAbsoluteValue K) ≤
          negativeLogRange (completeAbsoluteValue K L) := by
      intro r hr
      obtain ⟨x, rfl⟩ := hr
      refine ⟨Additive.ofMul (Units.map (algebraMap K L) x.toMul), ?_⟩
      change -Real.log
          (completeAbsoluteValue K L
            (algebraMap K L (x.toMul : K))) =
        -Real.log (NormedField.toAbsoluteValue K (x.toMul : K))
      rw [complete_absolute_algebra]
      rfl
    exact DiscreteTopology.of_subset hL hsubset
  · exact complete_negative_discrete K L

/-- A finite extension is complete for the metric induced by the canonical
extended absolute value. -/
theorem complete_extension [FiniteDimensional K L] :
    @CompleteSpace L (spectralNorm.uniformSpace K L) := by
  infer_instance

end

end


end Towers.NumberTheory.Milne
