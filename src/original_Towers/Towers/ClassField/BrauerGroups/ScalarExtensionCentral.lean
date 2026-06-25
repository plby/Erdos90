import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Towers.ClassField.BrauerGroups.CentralMatrix

/-!
# Chapter IV, Proposition 2.15

Extending the base field of a finite-dimensional central simple algebra
produces a central simple algebra over the larger field.
-/

namespace Towers.CField.BGroups

open scoped TensorProduct

universe u v w

variable (k : Type v) (K : Type u) (A : Type w)
  [Field k] [Field K] [Algebra k K]
  [Ring A] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The centrality part of Milne's Proposition IV.2.15. -/
theorem scalar_extension_central [Algebra.IsCentral k A] :
    Algebra.IsCentral K (A ⊗[k] K) := by
  letI : Module.Free k K := Module.Free.of_divisionRing k K
  constructor
  intro x hx
  have hxleft : x ∈ Subalgebra.centralizer k
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] K).range := by
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Subalgebra.mem_center_iff] at hx
    exact hx y
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct,
    Algebra.IsCentral.center_eq_bot] at hxleft
  rcases hxleft with ⟨y, rfl⟩
  clear hx
  induction y using TensorProduct.induction_on with
  | zero =>
      exact Algebra.mem_bot.mpr ⟨0, by simp⟩
  | tmul a b =>
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp a.2
      exact Algebra.mem_bot.mpr ⟨algebraMap k K c * b, by
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        change 1 ⊗ₜ[k] ((algebraMap k K) c * b) =
          Algebra.TensorProduct.map (⊥ : Subalgebra k A).val (AlgHom.id k K) (a ⊗ₜ[k] b)
        rw [Algebra.TensorProduct.map_tmul]
        change 1 ⊗ₜ[k] ((algebraMap k K) c * b) = (a : A) ⊗ₜ[k] b
        rw [← hc]
        calc
          1 ⊗ₜ[k] ((algebraMap k K) c * b) = 1 ⊗ₜ[k] (c • b) := by
            rw [Algebra.smul_def]
          _ = (c • (1 : A)) ⊗ₜ[k] b := (TensorProduct.smul_tmul c (1 : A) b).symm
          _ = (algebraMap k A) c ⊗ₜ[k] b := by
            rw [Algebra.algebraMap_eq_smul_one]⟩
  | add y z hy hz =>
      rw [Algebra.mem_bot] at hy hz ⊢
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      refine ⟨a + b, ?_⟩
      simp only [map_add]
      rw [ha, hb]

/-- Milne, Proposition IV.2.15: scalar extension preserves central
simplicity. -/
theorem scalar_extension_simple
    [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A] :
    IsSimpleRing (A ⊗[k] K) ∧ Algebra.IsCentral K (A ⊗[k] K) := by
  letI : IsSimpleRing (A ⊗[k] K) :=
    tensor_simple_ring k A K
  letI : Algebra.IsCentral K (A ⊗[k] K) := scalar_extension_central k K A
  exact ⟨inferInstance, inferInstance⟩

end Towers.CField.BGroups
