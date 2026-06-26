import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Small linear-algebra utilities

Reusable finite-rank consequences of surjective linear maps, kept here to avoid
reproving the same rank inequality in the degree-one and graded-layer files.
-/

namespace Towers


/-- A bijective linear map preserves finite rank. -/
theorem eq_of_bijective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Bijective f) :
    Module.finrank K V = Module.finrank K W :=
  LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf)

/-- Symmetric orientation of `eq_of_bijective`. -/
theorem finrank_bijective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Bijective f) :
    Module.finrank K W = Module.finrank K V :=
  (eq_of_bijective f hf).symm

/-- An injective linear map into a finite module cannot decrease finite rank. -/
theorem finrank_injective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W] (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Module.finrank K V ≤ Module.finrank K W := by
  have e : V ≃ₗ[K] LinearMap.range f := LinearEquiv.ofInjective f hf
  rw [e.finrank_eq]
  exact Submodule.finrank_le (LinearMap.range f)

/-- Kernel-trivial form of the injective finite-rank inequality. -/
theorem finrank_ker_bot {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W] (f : V →ₗ[K] W) (hker : LinearMap.ker f = ⊥) :
    Module.finrank K V ≤ Module.finrank K W := by
  exact finrank_injective f (LinearMap.ker_eq_bot.mp hker)

/-- A surjective linear map from a finite module cannot increase finite rank. -/
theorem finrank_surjective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K V] (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Module.finrank K W ≤ Module.finrank K V := by
  have hr : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  calc
    Module.finrank K W = Module.finrank K (LinearMap.range f) := by
      rw [hr]
      simp
    _ ≤ Module.finrank K V := LinearMap.finrank_range_le f

end Towers

namespace Towers

/-- Finite-dimensional rank-nullity in `finrank` form for a linear map out of a finite module. -/
theorem rank_nullity {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K V] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

/-- Rank-nullity for a surjective linear map, oriented as source rank equals target
rank plus kernel rank. -/
theorem finrank_ker_surjective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K V] (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Module.finrank K V = Module.finrank K W + Module.finrank K (LinearMap.ker f) := by
  have h := rank_nullity f
  have hr : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [hr] at h
  simpa [add_comm] using h.symm

end Towers
