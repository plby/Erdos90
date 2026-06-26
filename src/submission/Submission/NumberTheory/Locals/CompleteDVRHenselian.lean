import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Complete discretely valued fields have Henselian integer rings

For an ultrametric field whose integer ring is a discrete valuation ring,
the powers of the maximal ideal are exactly a family of shrinking closed
balls.  Thus the valuation topology on the integer ring is adic.  Completeness
of the field then makes the integer ring complete for that topology, hence
Henselian.
-/

namespace Submission.NumberTheory.Milne

open IsLocalRing
open scoped NormedField Valued

/-- The topology on the integer ring of an ultrametric discretely valued
field is the topology defined by powers of its maximal ideal. -/
theorem valued_integer_adic
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Valued.integer K)] :
    IsAdic (maximalIdeal (Valued.integer K)) := by
  rw [isAdic_iff]
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Valued.integer K)
  constructor
  · intro n
    rw [hπ.maximalIdeal_pow_eq_closedBall_pow]
    exact IsUltrametricDist.isOpen_closedBall _
      (pow_ne_zero n (norm_ne_zero_iff.mpr hπ.ne_zero))
  · intro s hs
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hs⟩ := hs
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖π‖ ^ n < ε :=
      exists_pow_lt_of_lt_one hε (Valued.integer.norm_irreducible_lt_one hπ)
    refine ⟨n, ?_⟩
    rw [hπ.maximalIdeal_pow_eq_closedBall_pow]
    exact (Metric.closedBall_subset_ball hn).trans hs

/-- The valuation integer ring of a complete ultrametric discretely valued
field is complete for its maximal-ideal-adic filtration. -/
theorem valued_integer_complete
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)] :
    IsAdicComplete (maximalIdeal (Valued.integer K))
      (Valued.integer K) := by
  have hclosed : IsClosed (Valued.integer K : Set K) := by
    rw [show (Valued.integer K : Set K) = Metric.closedBall 0 1 by
      ext x
      simp [Valued.integer.mem_iff]]
    exact Metric.isClosed_closedBall
  letI : IsUniformAddGroup (Valued.integer K) :=
    (Valued.integer K).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (Valued.integer K) := hclosed.completeSpace_coe
  exact (valued_integer_adic K).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- The integer ring of a complete ultrametric discretely valued field is
Henselian. -/
theorem valued_henselian_ring
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)] :
    HenselianLocalRing (Valued.integer K) := by
  letI : IsAdicComplete (maximalIdeal (Valued.integer K))
      (Valued.integer K) :=
    valued_integer_complete K
  exact {
    toIsLocalRing := inferInstance
    is_henselian := by
      intro p hp a ha hpa
      exact @HenselianRing.is_henselian (Valued.integer K) _
        (maximalIdeal (Valued.integer K))
        (IsAdicComplete.henselianRing (Valued.integer K)
          (maximalIdeal (Valued.integer K)))
        p hp a ha
          (hpa.map (Ideal.Quotient.mk (maximalIdeal (Valued.integer K)))) }

end Submission.NumberTheory.Milne
