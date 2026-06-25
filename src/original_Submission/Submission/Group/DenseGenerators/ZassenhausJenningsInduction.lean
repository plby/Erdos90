import Submission.Group.DenseGenerators.ZassenhausJenningsReduction

open scoped commutatorElement

/-!
# Strong-induction reduction for the Jennings commutator laws

Interior commutator bounds follow from lower-degree reverse dimension-subgroup
inclusions.  Consequently the remaining independent group-theoretic input is confined
to exact-generator commutators whose summed weights reach a killed cutoff.
-/

namespace Submission

noncomputable section

universe u

/-- The boundary commutator statement left for Hall collection: on a killed layer,
exact generators whose summed weights reach the cutoff commute. -/
def KilledBoundaryTrivial
    (p : ℕ)
    (Q : Type u) [Group Q]
    (n : ℕ) :
    Prop :=
  ∀ {r s : ℕ} {x y : Q},
    r < n →
    s < n →
    n ≤ r + s →
    x ∈ exactGeneratorSet p Q r →
    y ∈ exactGeneratorSet p Q s →
      ⁅x, y⁆ = 1

/-- Boundary triviality on finite killed layers implies the full reverse mod-`p`
dimension-subgroup inclusion.  The proof uses strong induction on the cutoff:
lower sums are transferred through the already-established lower-degree reverse
inclusions, while sums reaching the cutoff are exactly the boundary hypothesis. -/
lemma zmod_boundary_trivial
    {p : ℕ} [Fact p.Prime]
    (hboundary :
      ∀ {n : ℕ},
        1 < n →
          ∀ {Q : Type u} [Group Q] [Finite Q],
            zassenhausFiltration p Q n = ⊥ →
              KilledBoundaryTrivial p Q n) :
    ∀ {n : ℕ},
      0 < n →
        ∀ {G : Type u} [Group G],
          GroupAlgebra.dSubgro (ZMod p) G n ≤
            zassenhausFiltration p G n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn G _
      by_cases hn_one : n = 1
      · subst n
        rw [GroupAlgebra.dimension_one_top, zassenhausFiltration_one]
      · have hn_two : 1 < n := by omega
        apply
          zmod_filtration_law
            hn_two
        · intro Q _ _ hbot r x hr hx y
          have hr_pos : 0 < r :=
            exact_set_pos (p := p) hx
          by_cases hinterior : r + 1 < n
          · apply (ih (r + 1) hinterior (by omega))
            exact
              GroupAlgebra.commutator_dimension_any
                (ZMod p)
                Q
                (filtration_dimension_zmod r
                  (exact_subset_filtration hx))
                (by
                  rw [GroupAlgebra.dimension_one_top]
                  exact Subgroup.mem_top y)
          · have hcomm :
                ⁅x, y⁆ = 1 :=
              hboundary
                hn_two
                hbot
                hr
                (by omega)
                (Nat.le_of_not_gt hinterior)
                hx
                (zassenhaus_exact_set y)
            rw [hcomm]
            exact Subgroup.one_mem _
        · intro Q _ _ hbot r s x y hr hs hx hy
          have hr_pos : 0 < r :=
            exact_set_pos (p := p) hx
          have hs_pos : 0 < s :=
            exact_set_pos (p := p) hy
          by_cases hinterior : r + s < n
          · apply (ih (r + s) hinterior (by omega))
            exact
              GroupAlgebra.commutator_dimension_any
                (ZMod p)
                Q
                (filtration_dimension_zmod r
                  (exact_subset_filtration hx))
                (filtration_dimension_zmod s
                  (exact_subset_filtration hy))
          · have hcomm :
                ⁅x, y⁆ = 1 :=
              hboundary
                hn_two
                hbot
                hr
                hs
                (Nat.le_of_not_gt hinterior)
                hx
                hy
            rw [hcomm]
            exact Subgroup.one_mem _

end

end Submission
