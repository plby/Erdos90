import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

section GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/--
In a finite cyclic group whose order is divisible by `3`, there is a unique subgroup of index `3`.

We realize it concretely as the image of the cube map.
-/
theorem unique_index_three
    (h3 : 3 ∣ Nat.card G) :
    ∃! H : Subgroup G, H.index = 3 := by
  letI : CommGroup G := IsCyclic.commGroup
  let H0 : Subgroup G := (powMonoidHom 3 : G →* G).range
  have hH0_index : H0.index = 3 := by
    rw [IsCyclic.index_powMonoidHom_range (G := G) 3, Nat.gcd_eq_right h3]
  refine ⟨H0, hH0_index, ?_⟩
  intro H hH
  have hle : H0 ≤ H := by
    rintro _ ⟨g, rfl⟩
    simpa [hH] using (Subgroup.pow_index_mem H g : g ^ H.index ∈ H)
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have hcard_H0 : 3 * Nat.card H0 = Nat.card G := by
    simpa [hH0_index] using H0.index_mul_card
  have hcard_H : 3 * Nat.card H = Nat.card G := by
    simpa [hH] using H.index_mul_card
  omega

end GroupTheory

end Submission
