import Towers.ClassField.ProfiniteCohom.ContinuousFunctor

namespace Towers.CField.PCohom

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {J : Type} [SmallCategory J] [IsFiltered J]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A finite subset of a filtered union of coefficient modules lifts to one
common stage. -/
theorem subset_lifts_stage
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (c : Cocone F)
    (hcover : ∀ x : c.pt.obj.obj.V, ∃ j, ∃ y : (F.obj j).obj.obj.V,
      (c.ι.app j).hom.hom.hom.hom y = x)
    (s : Set c.pt.obj.obj.V) (hs : s.Finite) :
    ∃ j, ∀ x ∈ s, ∃ y : (F.obj j).obj.obj.V,
      (c.ι.app j).hom.hom.hom.hom y = x := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | @insert x s hxs hs ih =>
      obtain ⟨i, y, hy⟩ := hcover x
      obtain ⟨j, hj⟩ := ih
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, ?_⟩
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · refine ⟨(F.map fi).hom.hom.hom.hom y, ?_⟩
        have hw := c.w fi
        have hw' := congrArg (fun q ↦ q.hom.hom.hom.hom y) hw
        simpa only [Category.comp_id, Action.comp_hom, TopModuleCat.hom_comp,
          ContinuousLinearMap.coe_comp', Function.comp_apply] using hw'.trans hy
      · obtain ⟨w, hw⟩ := hj z hz
        refine ⟨(F.map fj).hom.hom.hom.hom w, ?_⟩
        have hc := c.w fj
        have hc' := congrArg (fun q ↦ q.hom.hom.hom.hom w) hc
        simpa only [Category.comp_id, Action.comp_hom, TopModuleCat.hom_comp,
          ContinuousLinearMap.coe_comp', Function.comp_apply] using hc'.trans hw

end
end Towers.CField.PCohom
