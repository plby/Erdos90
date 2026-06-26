import Towers.ClassField.LocalBrauer.DivisionAbsoluteValue
import Towers.ClassField.LocalBrauer.FieldNormExtension

/-!
# Chapter IV, Section 4: the absolute value on a local division algebra

This file specializes the determinant construction to Mathlib's
`IsNonarchimedeanLocalField` interface.  It gives Milne's unique extension of
the local absolute value to every finite-dimensional division algebra and
includes the nonarchimedean triangle inequality in the characterization.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]

/-- **Milne IV.4, local division-algebra absolute value.** The absolute value
of a nonarchimedean local field has a unique extension to a
finite-dimensional division algebra, and that extension is
nonarchimedean. -/
theorem unique_nonarchimedean_division :
    ∃! f : AbsoluteValue D ℝ,
      IsNonarchimedean f ∧
        ∀ x : K, f (algebraMap K D x) = (valuation K).norm x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  refine ⟨divisionAbsoluteValue K D, ?_, ?_⟩
  · exact ⟨division_absolute_nonarchimedean K D, by
      intro x
      change divisionAbsoluteValue K D (algebraMap K D x) = ‖x‖
      simpa only using
        division_absolute_value K D x⟩
  · intro f hf
    apply division_absolute_unique K D f
    intro x
    change f (algebraMap K D x) = ‖x‖
    simpa only using hf.2 x

/-- Forgetting the ultrametric clause gives the literal uniqueness statement
for extensions of the local absolute value. -/
theorem unique_division_absolute :
    ∃! f : AbsoluteValue D ℝ,
      ∀ x : K, f (algebraMap K D x) = (valuation K).norm x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  change ∃! f : AbsoluteValue D ℝ,
    ∀ x : K, f (algebraMap K D x) = ‖x‖
  simpa only using
    (unique_division_value K D)

end

end Towers.CField.LBrauer
