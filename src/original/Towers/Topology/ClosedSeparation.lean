import Mathlib.Topology.Algebra.Group.Basic


noncomputable section

namespace Towers
namespace TBluepr

structure CQSep
    (G : Type*) [Group G] [TopologicalSpace G]
    (K : Subgroup G) (g : G) : Type _ where
  target : Type
  [targetGroup : Group target]
  quotientMap : G →* target
  kernel_closed : IsClosed ((quotientMap.ker : Subgroup G) : Set G)
  K_le_ker : K ≤ quotientMap.ker
  separates : quotientMap g ≠ 1

attribute [instance] CQSep.targetGroup

/- A closed quotient separation witness gives a closed overgroup of `K` that omits the chosen
element.  This is the exact point-set step used when profinite quotients separate points. -/

theorem CQSep.exists_closed_overgroomittin
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Subgroup G} {g : G}
    (D : CQSep G K g) :
    ∃ H : Subgroup G,
      K ≤ H ∧ IsClosed ((H : Subgroup G) : Set G) ∧ g ∉ H := by
  refine ⟨D.quotientMap.ker, ?_, ?_, ?_⟩
  · exact D.K_le_ker
  · exact D.kernel_closed
  · intro hg
    have hg_eq : D.quotientMap g = 1 := by
      exact MonoidHom.mem_ker.mp hg
    exact D.separates hg_eq

/- A subgroup has closed-overgroup separation if every exterior point can be excluded by some
closed subgroup still containing the original subgroup. -/

structure COSep
    (G : Type*) [Group G] [TopologicalSpace G]
    (K : Subgroup G) : Prop where
  separate :
    ∀ g : G, g ∉ K →
      ∃ H : Subgroup G,
        K ≤ H ∧ IsClosed ((H : Subgroup G) : Set G) ∧ g ∉ H

/- Closed quotient separation is a concrete way to build closed-overgroup separation. -/

theorem overgroup_separation_quotient
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Subgroup G}
    (h :
      ∀ g : G, g ∉ K →
        Nonempty (CQSep G K g)) :
    COSep G K := by
  refine ⟨?_⟩
  intro g hg
  rcases h g hg with ⟨D⟩
  exact
    D.exists_closed_overgroomittin

/- Closed-overgroup separation forces every point in the closure of `K` to lie back in `K`.
Indeed, a closed overgroup containing `K` must contain the closure of `K`. -/

theorem COSep.closure_subset
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Subgroup G}
    (D : COSep G K) :
    closure ((K : Subgroup G) : Set G) ⊆ (K : Set G) := by
  intro g hgclosure
  by_contra hgK
  rcases D.separate g hgK with ⟨H, hKH, hH_closed, hgH⟩
  have hclosure_le_H :
      closure ((K : Subgroup G) : Set G) ⊆ (H : Set G) := by
    exact (hH_closed.closure_subset_iff).mpr hKH
  exact hgH (hclosure_le_H hgclosure)

/- Hence closed-overgroup separation is a standalone closedness criterion for subgroups. -/

theorem COSep.isClosed
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Subgroup G}
    (D : COSep G K) :
    IsClosed ((K : Subgroup G) : Set G) := by
  exact
    isClosed_of_closure_subset D.closure_subset

/- The previous criterion can be applied directly from closed quotient separations. -/

theorem closed_quotient_separation
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Subgroup G}
    (h :
      ∀ g : G, g ∉ K →
        Nonempty (CQSep G K g)) :
    IsClosed ((K : Subgroup G) : Set G) := by
  have hsep : COSep G K := by
    exact overgroup_separation_quotient h
  exact
    hsep.isClosed

/- A finite-level quotient that separates an element from the second Zassenhaus subgroup.  This
is the arithmetic form of the profinite separation statement: the quotient comes from a finite
Galois subextension in the defining pro-`3` tower, its kernel contains `D₂`, and the chosen
element remains nontrivial. -/

theorem topological_closure_closed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {S H : Subgroup G}
    (hSH : S ≤ H)
    (hH : IsClosed ((H : Subgroup G) : Set G)) :
    S.topologicalClosure ≤ H := by
  intro g hg
  change g ∈ closure ((S : Subgroup G) : Set G) at hg
  exact ((hH.closure_subset_iff).mpr hSH) hg

/- If the ordinary normal closure of the cut sequence lies in a closed subgroup, then the HMR
topological cut subgroup lies there as well.  This specializes the topological-closure step to
the depth-two Zassenhaus subgroup, using the closedness isolated above. -/

end TBluepr
end Towers
