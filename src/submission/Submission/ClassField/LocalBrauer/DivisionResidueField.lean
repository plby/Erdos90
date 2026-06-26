import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.LittleWedderburn
import Submission.ClassField.LocalBrauer.DivisionAlgebraIntegers
import Submission.ClassField.LocalBrauer.AlgebraAbsoluteValue

/-!
# Chapter IV, Section 4: the residue field of a local division algebra

The canonical absolute value makes a finite-dimensional division algebra over
a nonarchimedean local field into a finite-dimensional normed space.  Its
closed unit ball is therefore compact.  A finite cover by open unit balls
gives finitely many representatives modulo the strict-valuation ideal, so the
residue division ring is finite.  Little Wedderburn then makes it a field.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Algebra K D] [Module.Finite K D]

@[implicit_reducible]
private def divisionAlgebraNorm : Norm D :=
  ⟨divisionAbsoluteValue K D⟩

private def divisionSpaceCore :
    @NormedSpace.Core K D _ _ _ (divisionAlgebraNorm K D) := by
  letI : Norm D := divisionAlgebraNorm K D
  refine
    { norm_nonneg := fun x ↦ (divisionAbsoluteValue K D).nonneg x
      norm_smul := fun c x ↦ by
        change divisionAbsoluteValue K D (c • x) =
          ‖c‖ * divisionAbsoluteValue K D x
        rw [Algebra.smul_def, map_mul,
          division_absolute_value]
      norm_triangle := fun x y ↦ (divisionAbsoluteValue K D).add_le x y
      norm_eq_zero_iff := fun x ↦ by
        change divisionAbsoluteValue K D x = 0 ↔ x = 0
        exact (divisionAbsoluteValue K D).eq_zero }

/-- The residue division ring of a finite-dimensional division algebra over a
nonarchimedean local field is finite. -/
theorem division_residue_ring : Finite (divisionResidueRing K D) := by
  letI : Norm D := divisionAlgebraNorm K D
  let core := divisionSpaceCore K D
  letI : NormedAddCommGroup D := NormedAddCommGroup.ofCore core
  letI : NormedSpace K D := NormedSpace.ofCore core
  letI : ProperSpace D := FiniteDimensional.proper K D
  have hcompact : IsCompact (Metric.closedBall (0 : D) 1) :=
    isCompact_closedBall 0 1
  obtain ⟨t, htball, htfinite, htcover⟩ :=
    hcompact.finite_cover_balls (show (0 : ℝ) < 1 by positivity)
  let reps : t → divisionResidueRing K D := fun y ↦
    (divisionMaximalIdeal K D).ringCon.mk'
      ⟨y.1, by
        rw [division_subring]
        exact (mem_closedBall_zero_iff.mp (htball y.2))⟩
  letI : Finite t := htfinite
  apply Finite.of_surjective reps
  intro q
  obtain ⟨x, rfl⟩ := (divisionMaximalIdeal K D).ringCon.mk'_surjective q
  have hxball : (x : D) ∈ Metric.closedBall (0 : D) 1 := by
    exact mem_closedBall_zero_iff.mpr x.2
  have hcover := htcover hxball
  simp only [Set.mem_iUnion] at hcover
  obtain ⟨y, hyt, hxy⟩ := hcover
  refine ⟨⟨y, hyt⟩, ?_⟩
  apply (RingCon.eq (c := (divisionMaximalIdeal K D).ringCon)).mpr
  rw [(divisionMaximalIdeal K D).rel_iff]
  rw [division_maximal]
  simpa only [reps, dist_eq_norm, norm_sub_rev] using
    (Metric.mem_ball.mp hxy)

/-- Milne's finite residue division ring `O_D / P` is commutative, by the
little Wedderburn theorem, and hence is a field. -/
@[implicit_reducible]
noncomputable def divisionResidueField : Field (divisionResidueRing K D) := by
  letI : DivisionRing (divisionResidueRing K D) :=
    divisionResidue K D
  letI : Finite (divisionResidueRing K D) := division_residue_ring K D
  exact littleWedderburn (divisionResidueRing K D)

end

end Submission.CField.LBrauer
