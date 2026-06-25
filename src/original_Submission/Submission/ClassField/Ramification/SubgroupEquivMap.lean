import Submission.ClassField.Ramification.LubinLowerBreak

/-!
# Class Field Theory, Chapter I, Proposition 4.3

Proposition 4.3 is the restriction of the Lubin--Tate reciprocity isomorphism
to a principal-unit quotient.  Proposition 4.1 identifies its image with a
lower ramification group, and Example 4.2 identifies that group with the
corresponding upper ramification group.  The theorem below packages this
immediate restriction step independently of the not-yet-constructed concrete
Lubin--Tate field tower.
-/

namespace Submission.CField.Ramification

noncomputable section

/-- An equivalence restricts to an equivalence between a subgroup and any
subgroup identified with its image. -/
def subgroupEquiv
    {U G : Type*} [Group U] [Group G]
    (e : U ≃* G) (H : Subgroup U) (J : Subgroup G)
    (h : H.map e.toMonoidHom = J) : H ≃* J :=
  (e.subgroupMap H).trans (MulEquiv.subgroupCongr h)

@[simp]
theorem subgroup_equiv
    {U G : Type*} [Group U] [Group G]
    (e : U ≃* G) (H : Subgroup U) (J : Subgroup G)
    (h : H.map e.toMonoidHom = J) (u : H) :
    (subgroupEquiv e H J h u : G) = e u := by
  rfl

/-- Proposition 4.3: if Proposition 4.1 identifies the image of the
`i`th principal-unit subgroup with the relevant lower ramification group and
Example 4.2 identifies that lower group with `G^i`, reciprocity restricts to
an isomorphism onto `G^i`. -/
def principalUpperRamification
    {U G : Type*} [Group U] [Group G]
    (reciprocity : U ≃* G)
    (principalUnits : Subgroup U)
    (lowerRamification upperRamification : Subgroup G)
    (h41 : principalUnits.map reciprocity.toMonoidHom = lowerRamification)
    (h42 : lowerRamification = upperRamification) :
    principalUnits ≃* upperRamification :=
  subgroupEquiv reciprocity principalUnits upperRamification
    (h41.trans h42)

@[simp]
theorem principal_upper_ramification
    {U G : Type*} [Group U] [Group G]
    (reciprocity : U ≃* G)
    (principalUnits : Subgroup U)
    (lowerRamification upperRamification : Subgroup G)
    (h41 : principalUnits.map reciprocity.toMonoidHom = lowerRamification)
    (h42 : lowerRamification = upperRamification)
    (u : principalUnits) :
    (principalUpperRamification reciprocity principalUnits
      lowerRamification upperRamification h41 h42 u : G) = reciprocity u := by
  rfl

end

end Submission.CField.Ramification
