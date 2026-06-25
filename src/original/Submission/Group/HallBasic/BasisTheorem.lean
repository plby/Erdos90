import Submission.Group.HallBasic.AssociatedGradedSpanning
import Submission.Group.HallBasic.ConcreteBasisBridge
import Submission.Group.HallBasic.Indexed
import Submission.Group.HallBasic.Weight

open Submission.TCTex

/-!
# All-weight concrete Hall basis from the two classical reduction inputs

The canonical finite Hall families are already constructed.  This file
packages the exact remaining inputs for the free-group graded Hall basis
theorem:

* Jacobi-driven reduction of non-admissible ordered brackets of basic trees;
* signed standard-word triangularity for the recursive Hall polynomials.

The first input gives spanning in every positive lower-central layer.  The
second gives Magnus-side linear independence.  Together they construct the
concrete collection-layer Hall basis in every positive weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open TBluepr

universe u

/--
Non-admissible Hall reduction and signed standard-word triangularity construct
the concrete free-group associated-graded Hall basis in one positive weight.
-/
theorem forms_nonadmissible_system
    {d r : ℕ}
    (reduction :
      HallTree.NBRed
        (α := FreeGenerator.{u} d))
    (pivots :
      HallTree.SSSystem
        (α := FreeGenerator.{u} d) ℤ)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    { pivots := pivots.pivots r
      span_eq_top := reduction.tree_span_top hr }
    hr

/--
The same two classical inputs provide concrete free-group graded Hall bases in
every positive ordinary weight.
-/
theorem forms_associated_pivots
    (d : ℕ)
    (reduction :
      HallTree.NBRed
        (α := FreeGenerator.{u} d))
    (pivots :
      HallTree.SSSystem
        (α := FreeGenerator.{u} d) ℤ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  fun _r hr =>
    forms_nonadmissible_system
      reduction pivots hr

end TCTex
end Submission



noncomputable section

namespace Submission
namespace TCTex

open TBluepr

universe u

/--
Through weight three, signed standard-word independence is formalized.  Thus
lower-central spanning is the only remaining input needed to construct the
exact free-group associated-graded Hall basis consumed by collection.
-/
theorem forms_associated_pos
    {d r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3)
    (hspan :
      Submodule.span ℤ
          (Set.range fun i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r =>
            (HallTree.indexedBasicTree i).freeLowerWeight
              (HallTree.indexed_tree_weight i)) =
        ⊤) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    { pivots := (HallTree.standardSystemUp ℤ).pivots r hr
      span_eq_top := hspan }
    hrPos

end TCTex
end Submission
