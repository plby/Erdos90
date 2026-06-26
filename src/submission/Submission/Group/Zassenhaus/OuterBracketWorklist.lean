import Submission.Group.LowerCentralStrong

/-!
# Exact worklists for brackets with finite left products

The class-three collector can distribute an outer bracket across a finite
product because the resulting triple commutators are central.  At arbitrary
nilpotency cutoff the exact product identity retains conjugations instead.

This file packages the unrestricted finite recursion.  For a left product
`x * tail`, the worklist emits `x`, recursively expands the tail bracket,
emits `x⁻¹`, and finally emits `[x, right]`.  Its product is exactly the
original bracket with the full left product.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission

universe u

open scoped commutatorElement

namespace LPComm

/--
Exact finite worklist for a commutator whose left input is a list product.
The conjugating copies are retained instead of discarded by a centrality
assumption.
-/
def factors
    {G : Type u}
    [Group G]
    (right : G) :
    List G → List G
  | [] => []
  | left :: tail =>
      [left] ++ factors right tail ++ [left⁻¹, ⁅left, right⁆]

@[simp]
theorem factors_nil
    {G : Type u}
    [Group G]
    (right : G) :
    factors right [] = [] :=
  rfl

@[simp]
theorem factors_cons
    {G : Type u}
    [Group G]
    (right left : G)
    (tail : List G) :
    factors right (left :: tail) =
      [left] ++ factors right tail ++ [left⁻¹, ⁅left, right⁆] :=
  rfl

/-- The worklist has three emitted entries for every left-product entry. -/
@[simp]
theorem length_factors
    {G : Type u}
    [Group G]
    (right : G) :
    ∀ left : List G,
      (factors right left).length = 3 * left.length := by
  intro left
  induction left with
  | nil =>
      simp
  | cons head tail ih =>
      simp [ih]
      omega

/--
The unrestricted worklist evaluates exactly to the bracket with the full
left product.
-/
theorem prod_factors
    {G : Type u}
    [Group G]
    (right : G) :
    ∀ left : List G,
      (factors right left).prod = ⁅left.prod, right⁆ := by
  intro left
  induction left with
  | nil =>
      simp
  | cons head tail ih =>
      simp only [factors_cons, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, ih, List.prod_cons]
      rw [element_mul_left]
      group

/--
Every emitted entry is either a conjugating copy of an original left factor,
its inverse, or its bracket with the fixed right input.
-/
theorem exists_of_factors
    {G : Type u}
    [Group G]
    (right : G) :
    ∀ {left : List G} {x : G},
      x ∈ factors right left →
        ∃ y ∈ left, x = y ∨ x = y⁻¹ ∨ x = ⁅y, right⁆ := by
  intro left
  induction left with
  | nil =>
      intro x hx
      simp at hx
  | cons head tail ih =>
      intro x hx
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | hx | hx
      · exact ⟨head, by simp, Or.inl hx⟩
      · rcases ih hx with ⟨y, hy, hxy⟩
        exact ⟨y, by simp [hy], hxy⟩
      · exact ⟨head, by simp, Or.inr (Or.inl hx)⟩
      · exact ⟨head, by simp, Or.inr (Or.inr hx)⟩

end LPComm
end Submission
