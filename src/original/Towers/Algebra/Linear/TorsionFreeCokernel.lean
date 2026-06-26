import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Torsion-free cokernels from an exact sequence

This file packages the module-theoretic argument used in Lemma 2.3 and
Corollary 2.4 of Efrat--Chapman.
-/

namespace EChapma

variable {R M N P : Type*}
  [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/--
If `range f = ker g` and the target of `g` is torsion-free, then the
cokernel of `f` is torsion-free.
-/
theorem cokernel_torsion_ker
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    [Module.IsTorsionFree R P]
    (hexact : LinearMap.range f = LinearMap.ker g) :
    Module.IsTorsionFree R (N ⧸ LinearMap.range f) := by
  rw [hexact]
  let e :
      (N ⧸ LinearMap.ker g) ≃ₗ[R] LinearMap.range g :=
    g.quotKerEquivRange
  exact e.injective.moduleIsTorsionFree _ (by simp)

/-- Project to the coordinates outside a chosen subset of a basis. -/
noncomputable def basisComplementCoordinates
    {ι : Type*}
    (b : Module.Basis ι R N)
    (s : Set ι) :
    N →ₗ[R] (sᶜ : Set ι) →₀ R :=
  (Finsupp.lsubtypeDomain (sᶜ : Set ι)).comp b.repr.toLinearMap

/-- The kernel of complementary basis coordinates is the span of the
selected basis vectors. -/
theorem basis_complement_coordinates
    {ι : Type*}
    (b : Module.Basis ι R N)
    (s : Set ι) :
    LinearMap.ker (basisComplementCoordinates b s) =
      Submodule.span R (b '' s) := by
  ext x
  rw [LinearMap.mem_ker, Module.Basis.mem_span_image]
  constructor
  · intro hx i hi
    by_contra his
    have hzero :
        b.repr x i = 0 := by
      have hcoord :=
        DFunLike.congr_fun hx
          (⟨i, his⟩ : (sᶜ : Set ι))
      simpa [basisComplementCoordinates,
        Finsupp.lsubtypeDomain_apply] using hcoord
    exact (Finsupp.mem_support_iff.mp hi) hzero
  · intro hx
    rw [basisComplementCoordinates, LinearMap.comp_apply,
      Finsupp.lsubtypeDomain_apply,
      Finsupp.subtypeDomain_eq_zero_iff']
    intro i hi
    rw [← Finsupp.notMem_support_iff]
    exact fun his => hi (hx his)

/-- The range of a linear map is spanned by the images of any basis of its
domain. -/
theorem linear_basis_image
    {ι : Type*}
    (f : M →ₗ[R] N)
    (b : Module.Basis ι R M) :
    LinearMap.range f =
      Submodule.span R (Set.range fun i => f (b i)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [← b.linearCombination_repr x,
      Finsupp.linearCombination_apply, map_finsuppSum]
    apply Submodule.sum_mem
    intro i _hi
    have hfi :
        f (b i) ∈
          Submodule.span R (Set.range fun j => f (b j)) :=
      Submodule.subset_span (Set.mem_range_self i)
    simpa using Submodule.smul_mem _ _ hfi
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨b i, rfl⟩

/-- A quotient by the span of a subset of a basis is torsion-free. -/
theorem cokernel_torsion_basis
    {ι : Type*}
    (f : M →ₗ[R] N)
    (b : Module.Basis ι R N)
    (s : Set ι)
    (hrange : LinearMap.range f = Submodule.span R (b '' s)) :
    Module.IsTorsionFree R (N ⧸ LinearMap.range f) := by
  apply cokernel_torsion_ker
    f (basisComplementCoordinates b s)
  rw [basis_complement_coordinates, hrange]

/-- Torsion-free cokernels let one cancel a regular scalar modulo the range. -/
theorem cokernel_torsion_free
    (f : M →ₗ[R] N)
    (htf : Module.IsTorsionFree R (N ⧸ LinearMap.range f))
    {a : R} (ha : IsRegular a)
    {y : N}
    (hy : a • y ∈ LinearMap.range f) :
    y ∈ LinearMap.range f := by
  letI := htf
  have hquot :
      a •
          (Submodule.Quotient.mk y :
            N ⧸ LinearMap.range f) =
        0 := by
    change
      (Submodule.Quotient.mk (a • y) :
          N ⧸ LinearMap.range f) =
        0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hy
  have hyzero :
      (Submodule.Quotient.mk y :
          N ⧸ LinearMap.range f) =
        0 :=
    ha.smul_eq_zero_iff_right.mp hquot
  rw [Submodule.Quotient.mk_eq_zero] at hyzero
  exact hyzero

/-- Every cokernel of a linear map over a field is torsion-free. -/
theorem cokernel_torsion_field
    {K V W : Type*}
    [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (f : V →ₗ[K] W) :
    Module.IsTorsionFree K (W ⧸ LinearMap.range f) :=
  inferInstance

end EChapma
