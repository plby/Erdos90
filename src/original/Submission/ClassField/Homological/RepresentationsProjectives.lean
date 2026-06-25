import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.ClassField.Homological.EnoughInjectives

/-!
# Milne, Class Field Theory, Example II.A.14

Group cohomology is Ext from the trivial representation.  Representations
have enough projective and injective objects, so either kind of resolution may
be used.
-/

open CategoryTheory

universe u

namespace Submission.CField.Homological

variable (k G : Type u) [CommRing k] [Group G]

/-- The category of `G`-modules has enough projectives. -/
theorem repres_enoug_proje :
    EnoughProjectives (Rep.{u} k G) :=
  inferInstance

/-- The category of `G`-modules has enough injectives. -/
theorem representations_enough_injectives :
    EnoughInjectives (Rep.{u} k G) :=
  inferInstance

/-- Example A.14: group cohomology is Ext from the trivial representation. -/
noncomputable def groupCohomologyExt (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology A n ≅
      ((Ext k (Rep.{u} k G) n).obj
        (Opposite.op (Rep.trivial k G k))).obj A :=
  groupCohomologyIsoExt A n

/-- Formula (25): any projective resolution of the trivial representation
computes group cohomology. -/
noncomputable def cohomologyProjectiveResolution
    (A : Rep.{u} k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  groupCohomologyIso A n P

end Submission.CField.Homological
