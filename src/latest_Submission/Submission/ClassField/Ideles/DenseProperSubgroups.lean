import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Appendix exercise A-4: finite-index subgroups need not be open

Milne constructs a proper dense finite-index subgroup of a product of copies
of `F_2`, then pulls it back to the idele class group of `Q`.  The product and
idele-class constructions are not currently connected in the available idele
API.  The topological-group obstruction used at the end of the argument is
general and is recorded below: a proper dense subgroup cannot be open.
-/

namespace Submission.CField.Ideles.DPSubgro

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A proper dense subgroup of a topological group is not open. -/
theorem dense_proper_open (H : Subgroup G)
    (hdense : Dense (H : Set G)) (hproper : H ≠ ⊤) :
    ¬ IsOpen (H : Set G) := by
  intro hopen
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact dense_iff_closure_eq.mp hdense
  apply hproper
  apply SetLike.ext'
  simpa only [Subgroup.coe_top] using huniv

end Submission.CField.Ideles.DPSubgro
