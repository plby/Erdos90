import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.29 and Corollary 2.30

The integral closure in a finite separable field extension lies between the span of an
integral basis and the span of its trace-dual basis. Consequently it is finite over a
Noetherian base, and over a principal ideal ring it is free of the expected rank.
-/

namespace Towers.NumberTheory.Milne

/-- Let `K` be the fraction field of an integrally closed domain `A`, and let `L / K` be
finite separable. There is a `K`-basis of integral elements whose `A`-span is contained in
the integral closure, while the integral closure is contained in the `A`-span of the
trace-dual basis. This is the pair of inclusions in Proposition 2.29. -/
theorem integral_basis_dual
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (s : Finset L) (b b' : Module.Basis s K L),
      (∀ i, IsIntegral A (b i)) ∧
      Submodule.span A (Set.range b) ≤
        Subalgebra.toSubmodule (integralClosure A L) ∧
      Subalgebra.toSubmodule (integralClosure A L) ≤
        Submodule.span A (Set.range b') ∧
      Module.Free A (Submodule.span A (Set.range b)) ∧
      Module.Free A (Submodule.span A (Set.range b')) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  refine ⟨s, b, b.traceDual, hb, ?_, integralClosure_le_span_dualBasis b hb, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (mem_integralClosure_iff A L).2 (hb i)
  · exact Module.Free.of_basis (b.restrictScalars A)
  · exact Module.Free.of_basis (b.traceDual.restrictScalars A)

/-- The finite-generation conclusion of Proposition 2.29. -/
theorem integral_module_noetherian
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- Over a principal ideal ring, the integral closure is free and has rank `[L : K]`, as in
the final assertion of Proposition 2.29. -/
theorem integral_finrank_principal
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsPrincipalIdealRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Free A (integralClosure A L) ∧
      Module.finrank A (integralClosure A L) = Module.finrank K L := by
  letI : Module.IsTorsionFree A L :=
    Module.IsTorsionFree.trans_faithfulSMul A K L
  letI : Module.Free A (integralClosure A L) :=
    IsIntegralClosure.module_free A K L (integralClosure A L)
  exact ⟨inferInstance,
    IsIntegralClosure.rank A K L (integralClosure A L)⟩

/-- Any subalgebra that is finite as an `A`-module consists of integral elements, hence lies
in the integral closure. Together with Proposition 2.29 this is Corollary 2.30. -/
theorem subalgebra_closure_module
    (A L : Type*) [CommRing A] [CommRing L] [Algebra A L]
    (S : Subalgebra A L) [Module.Finite A S] :
    S ≤ integralClosure A L := by
  intro x hx
  rw [mem_integralClosure_iff]
  exact (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : S)).map S.val

end Towers.NumberTheory.Milne
