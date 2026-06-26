import Submission.Group.PresentationData


namespace Submission

/--
A homomorphism kernel is the preimage of the identity singleton.
-/
theorem monoid_preimage_one
    {G H : Type*}
    [Group G] [Group H]
    (φ : G →* H) :
    ((φ.ker : Subgroup G) : Set G) = φ ⁻¹' ({1} : Set H) := by
  ext g
  constructor
  · intro hg
    have hφ : φ g = 1 := MonoidHom.mem_ker.mp hg
    exact Set.mem_singleton_iff.mpr hφ
  · intro hg
    have hφ : φ g = 1 := Set.mem_singleton_iff.mp hg
    exact MonoidHom.mem_ker.mpr hφ

end Submission
