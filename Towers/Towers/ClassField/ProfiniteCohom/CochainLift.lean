import Towers.ClassField.ProfiniteCohom.FiniteStage

namespace Towers.CField.PCohom

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {J : Type} [SmallCategory J] [IsFiltered J]

omit [IsTopologicalGroup G] [TotallyDisconnectedSpace G] in
/-- Every continuous cochain into a filtered union of discrete coefficient
modules already has values in one stage. -/
theorem lifts_filtered_stage
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (c : Cocone F)
    (hcover : ∀ x : c.pt.obj.obj.V, ∃ j, ∃ y : (F.obj j).obj.obj.V,
      (c.ι.app j).hom.hom.hom.hom y = x)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom.hom.hom.hom)
    (r : ℕ) (f : continuousInhomogeneousCochains c.pt r) :
    ∃ j, ∃ g : continuousInhomogeneousCochains (F.obj j) r,
      continuousCochainMap (c.ι.app j) r g = f := by
  letI : DiscreteTopology c.pt.obj.obj.V := c.pt.property
  letI (j : J) : DiscreteTopology (F.obj j).obj.obj.V := (F.obj j).property
  have hrange : (Set.range f).Finite :=
    continuous_compact_discrete f.continuous
  obtain ⟨j, hj⟩ := subset_lifts_stage
    F c hcover (Set.range f) hrange
  let lift : (Fin r → G) → (F.obj j).obj.obj.V := fun x ↦
    Classical.choose (hj (f x) ⟨x, rfl⟩)
  have hlift (x : Fin r → G) :
      (c.ι.app j).hom.hom.hom.hom (lift x) = f x :=
    Classical.choose_spec (hj (f x) ⟨x, rfl⟩)
  have hcont : Continuous lift := by
    rw [continuous_discrete_rng]
    intro y
    have hpre : lift ⁻¹' ({y} : Set (F.obj j).obj.obj.V) =
        f ⁻¹' ({(c.ι.app j).hom.hom.hom.hom y} : Set c.pt.obj.obj.V) := by
      ext x
      change lift x = y ↔ f x = (c.ι.app j).hom.hom.hom.hom y
      constructor
      · intro h
        rw [← hlift x, h]
      · intro h
        apply hinj j
        rw [hlift x, h]
    rw [hpre]
    exact (isOpen_discrete _).preimage f.continuous
  let g : continuousInhomogeneousCochains (F.obj j) r :=
    { toFun := lift
      continuous_toFun := hcont }
  refine ⟨j, g, ?_⟩
  apply ContinuousMap.ext
  intro x
  rw [continuous_cochain]
  exact hlift x

end
end Towers.CField.PCohom
