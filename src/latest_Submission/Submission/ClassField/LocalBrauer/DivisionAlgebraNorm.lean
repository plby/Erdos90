import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Norm.Transitivity
import Submission.ClassField.CrossedProducts.SubalgebraField


/-!
# Chapter IV, Section 4: the regular norm on a division algebra

For a finite-dimensional division algebra `D` over a complete valued field
`K`, Milne's absolute value can be recovered from the determinant of left
multiplication.  This file establishes the algebraic part of that
construction.  In particular, it proves the determinant tower formula when
an element belongs to a finite commutative subfield of `D`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

variable (K D : Type u) [NormedField K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]

/-- The real-valued candidate obtained from the determinant of left
multiplication on `D`. -/
def regularValueCandidate (x : D) : ℝ :=
  ‖Algebra.norm K x‖ ^ (1 / (Module.finrank K D : ℝ))

omit [Module.Finite K D] in
theorem regular_candidate_nonneg (x : D) :
    0 ≤ regularValueCandidate K D x := by
  exact Real.rpow_nonneg (norm_nonneg _) _

@[simp]
theorem regular_candidate_zero :
    regularValueCandidate K D 0 = 0 := by
  have hdim : (Module.finrank K D : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos.ne' : Module.finrank K D ≠ 0)
  simp [regularValueCandidate, one_div, hdim]

omit [Module.Finite K D] in
@[simp]
theorem regular_value_candidate :
    regularValueCandidate K D 1 = 1 := by
  simp [regularValueCandidate]

omit [Module.Finite K D] in
theorem regular_candidate_mul (x y : D) :
    regularValueCandidate K D (x * y) =
      regularValueCandidate K D x * regularValueCandidate K D y := by
  simp only [regularValueCandidate, map_mul, norm_mul]
  exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem regular_absolute_candidate (x : D) :
    regularValueCandidate K D x = 0 ↔ x = 0 := by
  have hdim : (1 / (Module.finrank K D : ℝ)) ≠ 0 := by
    exact one_div_ne_zero (by
      exact_mod_cast (Module.finrank_pos.ne' : Module.finrank K D ≠ 0))
  rw [regularValueCandidate,
    Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)]
  constructor
  · rintro ⟨hnorm, _⟩
    exact Algebra.norm_eq_zero_iff.mp (norm_eq_zero.mp hnorm)
  · rintro rfl
    exact ⟨by simp, hdim⟩

@[simp]
theorem regular_candidate_algebra (x : K) :
    regularValueCandidate K D (algebraMap K D x) = ‖x‖ := by
  have hdim : Module.finrank K D ≠ 0 := Module.finrank_pos.ne'
  rw [regularValueCandidate, Algebra.norm_algebraMap, norm_pow]
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (norm_nonneg x) hdim)

@[simp]
theorem regular_candidate_neg (x : D) :
    regularValueCandidate K D (-x) =
      regularValueCandidate K D x := by
  rw [show -x = algebraMap K D (-1) * x by simp,
    regular_candidate_mul,
    regular_candidate_algebra]
  simp

/-- The regular absolute-value candidate, packaged with the multiplicative
and zero-preserving laws that do not use the triangle inequality. -/
def regularAbsoluteCandidate : D →*₀ ℝ where
  toFun := regularValueCandidate K D
  map_zero' := regular_candidate_zero K D
  map_one' := regular_value_candidate K D
  map_mul' := regular_candidate_mul K D

@[simp]
theorem regular_candidate_hom (x : D) :
    regularAbsoluteCandidate K D x =
      regularValueCandidate K D x :=
  rfl

omit [Module.Finite K D] in
/-- Left multiplication by an element of a commutative subalgebra, regarded
as a linear map over that subalgebra, restricts to the usual `K`-linear left
multiplication map. -/
private theorem restrict_scalars_lmul
    (E : Subalgebra K D) (hcomm : ∀ x y : E, x * y = y * x) (e : E) :
    letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
    (DistribSMul.toLinearMap E D e).restrictScalars K = Algebra.lmul K D (e : D) := by
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  ext x
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing the scalar action on `E`-linear endomorphisms traverses the
-- subalgebra, field, and restricted-scalar module diamonds below.
/-- The determinant of left multiplication on `D`, restricted to an element
of a finite commutative subfield `E`, is the field norm raised to `[D:E]`.
This is the ordinary-left-norm version of the reduced-norm restriction
formula needed in Milne's construction. -/
theorem regular_coe_pow
    (E : Subalgebra K D) (hcomm : ∀ x y : E, x * y = y * x) (e : E) :
    letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
    letI : Module.Finite K E :=
      Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
    letI : IsDomain E :=
      Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
    letI : Field E := fieldOfFiniteDimensional K E
    Algebra.norm K (e : D) =
      (Algebra.norm K e) ^ Module.finrank E D := by
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  letI : Module.Finite E D :=
    Module.Finite.of_restrictScalars_finite K E D
  let f : D →ₗ[E] D := DistribSMul.toLinearMap E D e
  have hf : f.restrictScalars K = Algebra.lmul K D (e : D) := by
    exact restrict_scalars_lmul K D E hcomm e
  have hdet : LinearMap.det f = e ^ Module.finrank E D := by
    have hf_smul : f = e • (LinearMap.id : D →ₗ[E] D) := by
      ext x
      rfl
    rw [hf_smul, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [Algebra.norm_apply, ← hf, LinearMap.det_restrictScalars, hdet, map_pow]

end

end Submission.CField.LBrauer
