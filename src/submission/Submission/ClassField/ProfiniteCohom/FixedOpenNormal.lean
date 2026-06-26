import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.MulAction

/-!
# Milne, Class Field Theory, Section II.4: discrete profinite actions

An element of a discrete set with a continuous profinite group action is
fixed by an open normal subgroup.
-/

namespace Submission.CField.PCohom

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [MulAction G X] [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]

/-- Every element of a discrete continuous profinite `G`-set is fixed by
some open normal subgroup of `G`. -/
theorem open_normal_stabilizer (x : X) :
    ∃ N : OpenNormalSubgroup G,
      (N : Subgroup G) ≤ MulAction.stabilizer G x := by
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem (MulAction.stabilizer G x))
  exact ⟨N, hN⟩

end Submission.CField.PCohom
