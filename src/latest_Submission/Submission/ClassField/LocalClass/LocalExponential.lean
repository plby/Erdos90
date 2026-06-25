import Submission.ClassField.LocalClass.ExponentialRadius
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# The local exponential equivalence in characteristic zero

The positive-radius theorem makes the inverse function theorem applicable to
the local exponential.  Restricting its source to the convergence ball gives
an honest local exponential/logarithm equivalence with all algebraic
identities available on its source.
-/

namespace Submission.CField.LClass

open scoped ENNReal NormedField Topology

noncomputable section

/-- The exponential as an open partial homeomorphism around zero, restricted
to its disk of convergence.  Its inverse is the local logarithm needed in
Lemma III.2.4. -/
noncomputable def localExpHomeomorph
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K] :
    OpenPartialHomeomorph K K := by
  let hder : HasStrictFDerivAt NormedSpace.exp
      (ContinuousLinearEquiv.refl K K : K →L[K] K) 0 := by
    simpa using hasStrictFDerivAt_exp_zero_of_radius_pos
      (exp_radius_pos K)
  exact (hder.toOpenPartialHomeomorph NormedSpace.exp).restrOpen
    (Metric.eball 0 (NormedSpace.expSeries K K).radius)
    Metric.isOpen_eball

@[simp]
theorem exp_homeomorph_coe
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K] :
    (localExpHomeomorph K : K → K) = NormedSpace.exp := rfl

theorem exp_partial_homeomorph
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K] :
    (0 : K) ∈ (localExpHomeomorph K).source := by
  let hder : HasStrictFDerivAt NormedSpace.exp
      (ContinuousLinearEquiv.refl K K : K →L[K] K) 0 := by
    simpa using hasStrictFDerivAt_exp_zero_of_radius_pos
      (exp_radius_pos K)
  rw [localExpHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨hder.mem_toOpenPartialHomeomorph_source,
    Metric.mem_eball_self (exp_radius_pos K)⟩

theorem exp_homeomorph_ball
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K]
    {x : K} (hx : x ∈ (localExpHomeomorph K).source) :
    x ∈ Metric.eball 0 (NormedSpace.expSeries K K).radius := by
  simpa [localExpHomeomorph,
    OpenPartialHomeomorph.restrOpen_source] using hx.2

/-- Exponential is injective on the canonical local source. -/
theorem exp_injective_source
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K] :
    Set.InjOn NormedSpace.exp (localExpHomeomorph K).source :=
  (localExpHomeomorph K).injOn

/-- The additive-to-multiplicative identity on the canonical local source. -/
theorem local_exp_add
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K]
    {x y : K}
    (hx : x ∈ (localExpHomeomorph K).source)
    (hy : y ∈ (localExpHomeomorph K).source) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_mem_ball
    (exp_homeomorph_ball K hx)
    (exp_homeomorph_ball K hy)

end

end Submission.CField.LClass
