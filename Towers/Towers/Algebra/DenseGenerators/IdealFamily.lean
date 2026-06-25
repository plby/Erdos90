import Mathlib
import Towers.Algebra.CompletedGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

noncomputable def DGFam.of_fintype
    {R : Type u} [Ring R] [Fintype R]
    (I : Ideal R) :
    DGFam I := by
  classical
  refine
    { index := I
      finite_index := inferInstance
      generator := fun x => x.1
      generator_mem := fun x => x.2
      spans := ?_ }
  intro x
  constructor
  · intro hx
    refine ⟨fun y : I => if y = ⟨x, hx⟩ then 1 else 0, ?_⟩
    rw [Fintype.sum_eq_single (⟨x, hx⟩ : I)]
    · simp
    · intro y hy
      simp [hy]
  · rintro ⟨coeff, hcoeff⟩
    rw [← hcoeff]
    exact Ideal.sum_mem I fun y _hy =>
      I.mul_mem_left (coeff y) y.2

end Towers
