import Submission.Group.FiniteContinuousShadows
import Submission.Group.ProPTopology
import Submission.Group.ProPClosed


open scoped Topology

noncomputable section

namespace Submission
namespace PCShadow

universe u

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [TotallyDisconnectedSpace F]

/--
The finite `p`-shadow attached to one open-normal quotient of a pro-`p`
profinite group.
-/
def openNormalShadow
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F) :
    Shadow p F := by
  letI : DiscreteTopology (F ⧸ (N : Subgroup F)) :=
    pro_discrete_topology N
  letI : Finite (F ⧸ (N : Subgroup F)) :=
    pro_p_open N
  exact {
    Target := F ⧸ (N : Subgroup F)
    map := QuotientGroup.mk' (N : Subgroup F)
    map_continuous := pro_open_continuous N
    target_p_group := hProP N
  }

omit [TotallyDisconnectedSpace F] in
@[simp] lemma open_shadow_kernel
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F) :
    (openNormalShadow hProP N).map.ker =
      (N : Subgroup F) := by
  change (QuotientGroup.mk' (N : Subgroup F)).ker =
    (N : Subgroup F)
  exact QuotientGroup.ker_mk' (N : Subgroup F)

/--
Open-normal finite `p`-quotients separate every nonidentity element in a
pro-`p` profinite group.
-/
lemma open_shadow_ne
    (hProP : ProP.ProPGroup p F)
    {x : F}
    (hx : x ≠ 1) :
    ∃ S : Shadow p F, S.map x ≠ 1 := by
  rcases open_normal_not hx with
    ⟨N, hxN⟩
  refine ⟨openNormalShadow hProP N, ?_⟩
  intro hxone
  apply hxN
  change QuotientGroup.mk' (N : Subgroup F) x = 1 at hxone
  exact (QuotientGroup.eq_one_iff x).mp hxone

/--
Every pro-`p` profinite group is residually finite `p` for the continuous finite
discrete `p`-group shadow theory.
-/
lemma residually_pro_group
    (hProP : ProP.ProPGroup p F) :
    RFP p F := by
  rw [residually_separates_nontrivial]
  intro x hx
  exact open_shadow_ne hProP hx

end PCShadow
end Submission
