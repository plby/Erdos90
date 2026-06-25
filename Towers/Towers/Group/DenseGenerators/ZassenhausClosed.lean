import Mathlib
import Towers.Group.DenseGenerators.ZassenhausCompact


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

/-- Zassenhaus filtrations pull back along the quotient by an open normal subgroup. -/
lemma zassenhaus_filtration_comap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ)
    (n : ℕ) :
    zassenhausFiltration p Γ n ≤
      (zassenhausFiltration p (Γ ⧸ N.toSubgroup) n).comap
        (QuotientGroup.mk' N.toSubgroup) := by
  exact
    filtration_comap
      (p := p)
      (Γ := Γ)
      (Λ := Γ ⧸ N.toSubgroup)
      n
      (QuotientGroup.mk' N.toSubgroup)

/-- The preimage of a Zassenhaus subgroup in an open-normal finite quotient is closed. -/
lemma filtration_comap_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ)
    (n : ℕ) :
    IsClosed
      (((zassenhausFiltration p (Γ ⧸ N.toSubgroup) n).comap
        (QuotientGroup.mk' N.toSubgroup) : Subgroup Γ) : Set Γ) := by
  let Q : Type u := Γ ⧸ N.toSubgroup
  let π : Γ →* Q := QuotientGroup.mk' N.toSubgroup
  haveI : DiscreteTopology Q := by
    dsimp [Q]
    exact QuotientGroup.discreteTopology N.isOpen
  have hπ_cont : Continuous (fun x : Γ => π x) := by
    dsimp [π, Q]
    change Continuous (QuotientGroup.mk : Γ → Γ ⧸ N.toSubgroup)
    exact QuotientGroup.continuous_mk
  have hclosed_target :
      IsClosed ((zassenhausFiltration p Q n : Subgroup Q) : Set Q) := by
    exact isClosed_discrete _
  change
    IsClosed
      (π ⁻¹'
        ((zassenhausFiltration p Q n : Subgroup Q) : Set Q))
  exact hclosed_target.preimage hπ_cont

/-- Closed-overgroup separation is a point-set criterion for closedness of a subgroup.

If every point outside `K` can be excluded by some closed subgroup containing `K`, then `K` is
itself closed: the closure of `K` lies in every such closed overgroup. -/
lemma overgroup_separation
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : Subgroup G}
    (hsep :
      ∀ g : G, g ∉ K →
        ∃ H : Subgroup G,
          K ≤ H ∧ IsClosed ((H : Subgroup G) : Set G) ∧ g ∉ H) :
    IsClosed ((K : Subgroup G) : Set G) := by
  refine isClosed_of_closure_subset ?_
  intro g hgclosure
  by_contra hgK
  rcases hsep g hgK with ⟨H, hKH, hHclosed, hgH⟩
  have hclosure_le_H :
      closure ((K : Subgroup G) : Set G) ⊆ (H : Set G) := by
    exact (hHclosed.closure_subset_iff).mpr hKH
  exact hgH (hclosure_le_H hgclosure)

/-- Zassenhaus closedness reduced to closed-overgroup separation.

This isolates the precise finite-quotient input still needed for closedness: every element outside
`D_n(Γ)` must be separated from `D_n(Γ)` by a closed overgroup. -/
lemma closed_overgroup_separation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (_s : Fin d → Γ)
    (_hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range _s)) = ⊤)
    {n : ℕ}
    (_hn : 1 < n)
    (hsep :
      ∀ g : Γ, g ∉ zassenhausFiltration p Γ n →
        ∃ H : Subgroup Γ,
          zassenhausFiltration p Γ n ≤ H ∧
            IsClosed ((H : Subgroup Γ) : Set Γ) ∧
            g ∉ H) :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  exact overgroup_separation hsep

end Towers
