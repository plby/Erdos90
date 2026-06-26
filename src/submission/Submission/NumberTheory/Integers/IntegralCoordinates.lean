import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.43

Coordinates of an integral element in an integral field basis have denominators dividing the
discriminant.  This is the Cramer-rule calculation underlying the lattice bound in the proposition.
-/

namespace Submission.NumberTheory.Milne

open scoped Matrix

/-- If `b` is a field basis consisting of elements integral over `A`, then the discriminant times
every `b`-coordinate of an integral element is integral over `A`. -/
theorem discr_repr_integral
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (hb : ∀ i, IsIntegral A (b i))
    {z : L} (hz : IsIntegral A z) (i : ι) :
    IsIntegral A (Algebra.discr K b * b.repr z i) := by
  let t : ι → K := fun j => Algebra.trace K L (z * b j)
  have hcramer := Matrix.mulVec_cramer (Algebra.traceMatrix K b) t
  have hinjective : Function.Injective (Algebra.traceMatrix K b).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    simpa [← Algebra.discr_def] using Algebra.discr_isUnit_of_basis K b
  dsimp [t] at hcramer
  rw [← Algebra.traceMatrix_of_basis_mulVec, ← Matrix.mulVec_smul,
    hinjective.eq_iff, Algebra.traceMatrix_of_basis_mulVec] at hcramer
  have hi :
      Algebra.discr K b * b.repr z i =
        Matrix.cramer (Algebra.traceMatrix K b) t i := by
    simpa [Algebra.discr_def, Algebra.smul_def, mul_comm] using
      congrFun hcramer.symm i
  rw [hi, Matrix.cramer_apply]
  apply IsIntegral.det
  intro j k
  rw [Matrix.updateCol_apply]
  split
  · exact Algebra.isIntegral_trace (hz.mul (hb j))
  · exact Algebra.isIntegral_trace ((hb j).mul (hb k))

/-- In the fraction-field situation of Proposition 2.43, the discriminant times every coordinate
actually comes from the integrally closed base ring. -/
theorem base_discr_repr
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (hb : ∀ i, IsIntegral A (b i))
    {z : L} (hz : IsIntegral A z) (i : ι) :
    ∃ a : A, algebraMap A K a = Algebra.discr K b * b.repr z i := by
  exact IsIntegrallyClosed.isIntegral_iff.mp
    (discr_repr_integral A K L b hb hz i)

/-- Every integral element belongs to the `A`-span of the basis vectors divided by their
discriminant. This is the upper inclusion in Proposition 2.43. -/
theorem discr_smul_basis
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (hb : ∀ i, IsIntegral A (b i))
    {z : L} (hz : IsIntegral A z) :
    z ∈ Submodule.span A
      (Set.range fun i => (Algebra.discr K b)⁻¹ • b i) := by
  classical
  choose a ha using fun i => base_discr_repr A K L b hb hz i
  rw [← b.sum_repr z]
  apply Submodule.sum_mem
  intro i _
  have hcoeff :
      (algebraMap A K (a i)) * (Algebra.discr K b)⁻¹ = b.repr z i := by
    rw [ha]
    field_simp [Algebra.discr_not_zero_of_basis K b]
  rw [← hcoeff, mul_smul, IsScalarTower.algebraMap_smul]
  exact Submodule.smul_mem _ (a i)
    (Submodule.subset_span (Set.mem_range_self i))

/-- The full pair of lattice inclusions in Proposition 2.43. -/
theorem inv_discr_smul
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (hb : ∀ i, IsIntegral A (b i)) :
    Submodule.span A (Set.range b) ≤
        Subalgebra.toSubmodule (integralClosure A L) ∧
      Subalgebra.toSubmodule (integralClosure A L) ≤
        Submodule.span A
          (Set.range fun i => (Algebra.discr K b)⁻¹ • b i) := by
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_integralClosure_iff A L).2 (hb i)
  · intro z hz
    exact discr_smul_basis A K L b hb
      ((mem_integralClosure_iff A L).1 hz)

end Submission.NumberTheory.Milne
