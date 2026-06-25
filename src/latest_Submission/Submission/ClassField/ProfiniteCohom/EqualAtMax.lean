import Submission.ClassField.ProfiniteCohom.CochainLift

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {J : Type} [SmallCategory J] [IsFiltered J]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Two stage cochains with the same image in the union become equal after
passing to a common filtered stage. -/
theorem cochains_equal_max
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (c : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom.hom.hom.hom)
    (r : ℕ) {i j : J}
    (f : continuousInhomogeneousCochains (F.obj i) r)
    (g : continuousInhomogeneousCochains (F.obj j) r)
    (h : continuousCochainMap (c.ι.app i) r f =
      continuousCochainMap (c.ι.app j) r g) :
    continuousCochainMap (F.map (IsFiltered.leftToMax i j)) r f =
      continuousCochainMap (F.map (IsFiltered.rightToMax i j)) r g := by
  let k := IsFiltered.max i j
  let fi : i ⟶ k := IsFiltered.leftToMax i j
  let fj : j ⟶ k := IsFiltered.rightToMax i j
  apply ContinuousMap.ext
  intro x
  apply hinj k
  rw [continuous_cochain, continuous_cochain]
  have hi := c.w fi
  have hi' := congrArg (fun q ↦ q.hom.hom.hom.hom (f x)) hi
  have hj := c.w fj
  have hj' := congrArg (fun q ↦ q.hom.hom.hom.hom (g x)) hj
  have hx := congrArg (fun q : continuousInhomogeneousCochains c.pt r ↦ q x) h
  change continuousCochainMap (c.ι.app i) r f x =
    continuousCochainMap (c.ι.app j) r g x at hx
  rw [continuous_cochain, continuous_cochain] at hx
  have hx' : (c.ι.app i).hom.hom.hom.hom (f x) =
      (c.ι.app j).hom.hom.hom.hom (g x) := hx
  have hleft : (c.ι.app k).hom.hom.hom.hom
        ((F.map fi).hom.hom.hom.hom (f x)) =
      (c.ι.app i).hom.hom.hom.hom (f x) := by
    simpa only [Action.comp_hom, TopModuleCat.hom_comp,
      ContinuousLinearMap.coe_comp', Function.comp_apply] using hi'
  have hright : (c.ι.app j).hom.hom.hom.hom (g x) =
      (c.ι.app k).hom.hom.hom.hom
        ((F.map fj).hom.hom.hom.hom (g x)) := by
    simpa only [Action.comp_hom, TopModuleCat.hom_comp,
      ContinuousLinearMap.coe_comp', Function.comp_apply] using hj'.symm
  exact hleft.trans (hx'.trans hright)

end
end Submission.CField.PCohom
