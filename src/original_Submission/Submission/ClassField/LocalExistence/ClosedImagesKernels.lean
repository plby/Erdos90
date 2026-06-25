import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact

/-!
# Milne, Class Field Theory, Section III.5, Step 1

Milne begins the proof of the local existence theorem by showing that a norm
map has closed image and compact kernel.  Once the local-field calculations
have supplied openness of the image and containment of the kernel in the
compact unit group, the remainder is a general topological-group argument.
This file records that argument.
-/

namespace Submission.CField.LExist

universe u v

/-- **Step III.5.1, topological core.** A continuous group homomorphism has
closed image when its image is open.  If its kernel is contained in a compact
set, then its kernel is compact as well.

For a local norm map, openness of the image follows from finite index and the
local-field open-subgroup theorem, while the valuation formula places the
kernel inside the compact unit group. -/
theorem image_closed_compact
    {G : Type u} {H : Type v}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space H]
    (f : G →* H) (hf : Continuous f)
    (hopen : IsOpen (f.range : Set H))
    {U : Set G} (hU : IsCompact U) (hker : (f.ker : Set G) ⊆ U) :
    IsClosed (f.range : Set H) ∧ IsCompact (f.ker : Set G) := by
  constructor
  · exact f.range.isClosed_of_isOpen hopen
  · apply hU.of_isClosed_subset _ hker
    have hpreimage : IsClosed (f ⁻¹' ({1} : Set H)) :=
      isClosed_singleton.preimage hf
    convert hpreimage using 1

end Submission.CField.LExist
