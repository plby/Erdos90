import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Class Field Theory, Chapter II, Remark 1.19

Every degree-two cohomology class has a normalized cocycle representative.
For a cocycle `x`, subtract the coboundary of the constant one-cochain with
value `x (1, 1)`.
-/

namespace Submission.CField.COps

open groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The coboundary of the constant cochain with value `m` takes the value
`m` at `(1, 1)`, as computed in Remark II.1.19. -/
theorem d₁₂_const_apply_one_one (A : Rep k G) (m : A) :
    d₁₂ A (fun _ ↦ m) (1, 1) = m := by
  change A.ρ 1 m - m + m = m
  simp

/-- **Remark II.1.19.** Every class in `H²(G,A)` is represented by a
normalized cocycle, meaning one whose value at `(1,1)` is zero. -/
theorem normalized_cocycle_representation
    (A : Rep k G) (z : H2 A) :
    ∃ x : cocycles₂ A, H2π A x = z ∧ x (1, 1) = 0 := by
  induction z using H2_induction_on with
  | h x =>
      let c : G → A := fun _ ↦ x (1, 1)
      let dc : cocycles₂ A := ⟨d₁₂ A c, d₁₂_apply_mem_cocycles₂ c⟩
      let y : cocycles₂ A := x - dc
      refine ⟨y, ?_, ?_⟩
      · change H2π A (x - dc) = H2π A x
        rw [map_sub]
        have hdc : H2π A dc = 0 := by
          rw [H2π_eq_zero_iff]
          exact ⟨c, rfl⟩
        rw [hdc, sub_zero]
      · change x (1, 1) - d₁₂ A c (1, 1) = 0
        rw [d₁₂_const_apply_one_one]
        exact sub_self _

end Submission.CField.COps
