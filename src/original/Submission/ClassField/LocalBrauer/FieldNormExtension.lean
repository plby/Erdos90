import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Chapter IV, Section 4: extension of the local absolute value

Milne begins the nonarchimedean local-field calculation by using the unique
extension of the absolute value from the base field to every finite
commutative subfield of a central division algebra.  Mathlib's spectral norm
theorem proves the stronger statement for arbitrary algebraic field
extensions of a complete nontrivially normed nonarchimedean field.

This file packages the spectral norm as an `AbsoluteValue` and records both
its extension property and its uniqueness.  The later passage from these
commutative extensions to a single absolute value on a noncommutative
division algebra is a separate theorem.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The spectral norm, regarded as the multiplicative absolute value on an
algebraic extension of a complete nonarchimedean field. -/
def spectralAbsoluteValue : AbsoluteValue L ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue
    (spectralMulAlgNorm K L).toMulRingNorm

@[simp]
theorem spectral_absolute_value (x : L) :
    spectralAbsoluteValue K L x = spectralNorm K L x :=
  rfl

/-- The spectral absolute value restricts to the given absolute value on the
base field. -/
@[simp]
theorem spectral_absolute_algebra (x : K) :
    spectralAbsoluteValue K L (algebraMap K L x) = ‖x‖ := by
  exact spectralNorm_extends x

/-- The spectral absolute value is nonarchimedean. -/
theorem spectral_absolute_nonarchimedean :
    IsNonarchimedean (spectralAbsoluteValue K L) :=
  isNonarchimedean_spectralNorm

/-- The absolute value of a complete nonarchimedean field extends uniquely
to every algebraic commutative field extension. -/
theorem unique_extending_norm :
    ∃! f : AbsoluteValue L ℝ,
      ∀ x : K, f (algebraMap K L x) = ‖x‖ := by
  refine ⟨spectralAbsoluteValue K L, spectral_absolute_algebra K L, ?_⟩
  intro f hf
  ext x
  exact (spectralNorm_unique_field_norm_ext hf x).trans
    (spectral_absolute_value K L x).symm

/-- Finite-extension form of the unique extension theorem used in Milne's
local division-algebra argument. -/
theorem unique_absolute_extending
    (E : Type v) [Field E] [Algebra K E] [FiniteDimensional K E] :
    ∃! f : AbsoluteValue E ℝ,
      ∀ x : K, f (algebraMap K E x) = ‖x‖ := by
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact unique_extending_norm K E

section LocalField

open ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [UniformSpace F]
  [IsUniformAddGroup F] [IsNonarchimedeanLocalField F]

/-- The real-valued norm associated to the canonical rank-one valuation of a
nonarchimedean local field. -/
noncomputable def localAbsoluteNorm (x : F) : ℝ :=
  (ValuativeRel.valuation F).norm x

/-- Local-field specialization: the absolute value associated to the local
valuation extends uniquely to every finite commutative field extension. -/
theorem unique_absolute_value
    (E : Type v) [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃! f : AbsoluteValue E ℝ,
      ∀ x : F, f (algebraMap F E x) = localAbsoluteNorm F x := by
  letI : Valuation.RankOne
      (Valued.v (R := F) (Γ₀ := ValueGroupWithZero F)) := by
    change Valuation.RankOne (valuation F)
    infer_instance
  letI : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  simpa only [localAbsoluteNorm] using
    (unique_absolute_extending F E)

end LocalField

end

end Submission.CField.LBrauer
