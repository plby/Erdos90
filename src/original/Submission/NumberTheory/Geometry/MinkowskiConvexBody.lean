import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Milne, Algebraic Number Theory, Theorem 4.19

Minkowski's convex-body theorem in the compact form used by Milne.
-/

namespace Submission.NumberTheory.Milne

open MeasureTheory MeasureTheory.Measure Module Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {μ : Measure E} [IsAddHaarMeasure μ]
  {L : AddSubgroup E} [Countable L] [DiscreteTopology L]
  {D T : Set E}

/-- **Milne, Theorem 4.19 (Minkowski).** Let `D` be a fundamental domain for a
discrete lattice `L` in a finite-dimensional real vector space. If `T` is compact,
convex, symmetric about the origin, and has volume at least `2^n` times the volume
of `D`, then `T` contains a nonzero point of `L`. -/
theorem point_convex_symmetric
    (fund : IsAddFundamentalDomain L D μ)
    (hT_symm : ∀ x ∈ T, -x ∈ T)
    (hT_convex : Convex ℝ T)
    (hT_compact : IsCompact T)
    (hvolume : μ D * 2 ^ finrank ℝ E ≤ μ T) :
    ∃ x : L, x ≠ 0 ∧ (x : E) ∈ T := by
  obtain ⟨x, hx0, hxT⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      fund hT_symm hT_convex hT_compact hvolume
  exact ⟨x, hx0, hxT⟩

end Submission.NumberTheory.Milne
