import Submission.ClassField.Homological.RepresentationsProjectives

/-!
# Milne, Class Field Theory, Remark II.A.15

Formula (25), computing group cohomology from any projective resolution of the
trivial representation, can equivalently be taken as its definition.
-/

open CategoryTheory

universe u

namespace Submission.CField.Homological

variable (k G : Type u) [CommRing k] [Group G]

/-- The projective-resolution presentation highlighted in Remark A.15. -/
noncomputable def cohomologyProjectivePresentation
    (A : Rep.{u} k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  cohomologyProjectiveResolution k G A n P

end Submission.CField.Homological
