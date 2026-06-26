import Mathlib
import Towers.Algebra.DenseGenerators.FiniteGroupAlgebra
import Towers.Topology.ClosedSeparation


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z


namespace DGTest

variable {p : ℕ}
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable {n : ℕ}

/-- The pullback to `Γ` of the target Zassenhaus subgroup in a finite quotient test. -/
def targetZassenhausComap
    (T : DGTest Γ)
    (p n : ℕ) :
    Subgroup Γ := by
  letI : Group T.quotientGroup := T.instGroup
  exact (targetZassenhaus T p n).comap T.quotientMap

/-- The inverse image of the target Zassenhaus subgroup under a finite quotient test is closed.

This is the formal version of the finite-quotient separation move used after the TeX proof has
converted Zassenhaus-depth information into congruences in finite augmentation quotients: once the
test quotient is finite and discrete, every subgroup of the target is closed, and continuity pulls
that closed set back to the profinite group. -/
lemma target_comap_closed
    (T : DGTest Γ) :
    IsClosed ((targetZassenhausComap T p n : Subgroup Γ) : Set Γ) := by
  letI : Group T.quotientGroup := T.instGroup
  letI : TopologicalSpace T.quotientGroup := T.instTopologicalSpace
  letI : DiscreteTopology T.quotientGroup := T.instDiscreteTopology
  let K : Subgroup T.quotientGroup := targetZassenhaus T p n
  have hK_closed : IsClosed (K : Set T.quotientGroup) := by
    exact isClosed_discrete _
  dsimp [targetZassenhausComap]
  change IsClosed ((fun x : Γ => T.quotientMap x) ⁻¹' (K : Set T.quotientGroup))
  exact hK_closed.preimage T.quotientMap_continuous

/-- Elements already in `D_n(Γ)` land in the target `D_n` of every finite quotient test.

This packages the functoriality of the Zassenhaus filtration in the subgroup language required by
the closed-overgroup criterion: `D_n(Γ)` is contained in the pullback of the target subgroup in the
finite quotient. -/
lemma zassenhaus_target_comap
    (T : DGTest Γ) :
    zassenhausFiltration p Γ n ≤
      targetZassenhausComap T p n := by
  letI : Group T.quotientGroup := T.instGroup
  intro g hg
  dsimp [targetZassenhausComap]
  change T.quotientMap g ∈ targetZassenhaus T p n
  have hg_target :
      T.quotientMap g ∈ targetZassenhaus T p n := by
    exact
      filtration_comap
        (p := p) (Γ := Γ) (Λ := T.quotientGroup) n T.quotientMap hg
  exact hg_target

/-- A quotient test that detects `g` outside the target Zassenhaus subgroup produces the closed
overgroup needed to separate `g` from `D_n(Γ)`.

The overgroup is the pullback of the finite quotient's target Zassenhaus subgroup.  It contains
`D_n(Γ)` by functoriality, is closed because the quotient is discrete, and excludes `g` by the
chosen test. -/
lemma closed_overgroup_target
    (T : DGTest Γ)
    {g : Γ}
    (hgT : g ∉ targetZassenhausComap T p n) :
    ∃ H : Subgroup Γ,
      zassenhausFiltration p Γ n ≤ H ∧
        IsClosed ((H : Subgroup Γ) : Set Γ) ∧
        g ∉ H := by
  let H : Subgroup Γ := targetZassenhausComap T p n
  refine ⟨H, ?_, ?_, ?_⟩
  · exact T.zassenhaus_target_comap (p := p) (n := n)
  · dsimp [H]
    exact T.target_comap_closed (p := p) (n := n)
  · intro hgH
    exact hgT (by simpa [H] using hgH)


end DGTest

end Towers
