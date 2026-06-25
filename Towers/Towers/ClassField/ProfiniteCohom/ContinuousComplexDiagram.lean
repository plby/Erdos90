import Towers.ClassField.ProfiniteCohom.FilteredColimitExact
import Towers.ClassField.ProfiniteCohom.ContinuousModuleDiagram

namespace Towers.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {J : Type} [SmallCategory J] [IsFiltered J]

abbrev cochainComplexDiagram
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) :
    J ⥤ CochainComplex (ModuleCat ℤ) ℕ :=
  F ⋙ inhomogeneousCochainFunctor

abbrev continuousColimitComplex
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.coconeOfHasColimitEval
    (cochainComplexDiagram F)).pt

def cochainSystemDifferential
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    continuousCochainDiagram F n ⟶
      continuousCochainDiagram F (n + 1) where
  app j := ((cochainComplexDiagram F).obj j).d n (n + 1)
  naturality _ _ f := ((cochainComplexDiagram F).map f).comm n (n + 1)

noncomputable def continuousCochainSystem
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) :
    CochainComplex (J ⥤ ModuleCat.{0, 0} ℤ) ℕ :=
  CochainComplex.of (continuousCochainDiagram F)
    (cochainSystemDifferential F) fun n ↦ by
      apply NatTrans.ext
      funext j
      exact ((cochainComplexDiagram F).obj j).d_comp_d
        n (n + 1) (n + 1 + 1)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [IsFiltered J] in
theorem cochain_d_app
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (i j : ℕ) (k : J) :
    ((continuousCochainSystem F).d i j).app k =
      ((cochainComplexDiagram F).obj k).d i j := by
  by_cases h : i + 1 = j
  · subst j
    have hd : (continuousCochainSystem F).d i (i + 1) =
        cochainSystemDifferential F i := CochainComplex.of_d _ _ i
    exact congrArg (fun φ ↦ φ.app k) hd
  · have hrel : ¬ (ComplexShape.up ℕ).Rel i j := by
      simpa only [ComplexShape.up_Rel] using h
    rw [(continuousCochainSystem F).shape i j hrel,
      ((cochainComplexDiagram F).obj k).shape i j hrel]
    rfl

def continuousCochainChain
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) :
    continuousColimitComplex F ⟶
      continuousInhomogeneousComplex c.pt :=
  (HomologicalComplex.isColimitCoconeOfHasColimitEval
    (cochainComplexDiagram F)).desc
      (inhomogeneousCochainFunctor.mapCocone c)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [IsFiltered J] in
theorem cochain_chain_f
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (n : ℕ) :
    (continuousCochainChain c).f n = continuousCochainUnion c n := by
  rfl

noncomputable instance cochain_chain_iso
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x) :
    IsIso (continuousCochainChain c) := by
  letI (n : ℕ) : IsIso ((continuousCochainChain c).f n) := by
    rw [cochain_chain_f]
    exact continuous_cochain_iso c n hinj hcover
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def cochainComplexIso
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x) :
    continuousColimitComplex F ≅
      continuousInhomogeneousComplex c.pt := by
  letI := cochain_chain_iso c hinj hcover
  exact asIso (continuousCochainChain c)

noncomputable def systemPointwiseHomology
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((continuousCochainSystem F).sc r).homology ≅
      (continuousCochainSystem F).asFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r :=
  NatIso.ofComponents (fun j ↦
    (((continuousCochainSystem F).sc r).mapHomologyIso
      ((evaluation J (ModuleCat.{0, 0} ℤ)).obj j)).symm)
    (by
      intro i j f
      let S := (continuousCochainSystem F).sc r
      let τ := (evaluation J (ModuleCat.{0, 0} ℤ)).map f
      change S.homology.map f ≫
          (S.mapHomologyIso ((evaluation J (ModuleCat.{0, 0} ℤ)).obj j)).inv =
        (S.mapHomologyIso ((evaluation J (ModuleCat.{0, 0} ℤ)).obj i)).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans τ)
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp
      rfl)

noncomputable def cochainSystemFunctor
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) :
    (continuousCochainSystem F).asFunctor ≅ cochainComplexDiagram F :=
  NatIso.ofComponents (fun j ↦
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by
        intro i k _
        simpa using (cochain_d_app F i k j).symm))
    (by
      intro i j f
      ext n
      simp
      rfl)

abbrev continuousCohomologyDiagram
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    J ⥤ ModuleCat ℤ :=
  cochainComplexDiagram F ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r

noncomputable def cochainDiagramIso
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((continuousCochainSystem F).sc r).homology ≅
      continuousCohomologyDiagram F r :=
  systemPointwiseHomology F r ≪≫
    Functor.isoWhiskerRight (cochainSystemFunctor F)
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [IsFiltered J] in
theorem colim_cochain_d
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (i j : ℕ) :
    colimMap ((continuousCochainSystem F).d i j) =
      (continuousColimitComplex F).d i j := by
  dsimp [continuousColimitComplex,
    HomologicalComplex.coconeOfHasColimitEval]
  apply congrArg colimMap
  apply NatTrans.ext
  funext k
  exact cochain_d_app F i j k

noncomputable def systemColimitShort
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((continuousCochainSystem F).sc r).map
        (colim : (J ⥤ ModuleCat.{0, 0} ℤ) ⥤ ModuleCat.{0, 0} ℤ) ≅
      (continuousColimitComplex F).sc r := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simpa using (colim_cochain_d F
      ((ComplexShape.up ℕ).prev r) r).symm
  · simpa using (colim_cochain_d F r
      ((ComplexShape.up ℕ).next r)).symm

noncomputable def systemColimitHomology
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    (((continuousCochainSystem F).sc r).map
      (colim : (J ⥤ ModuleCat.{0, 0} ℤ) ⥤ ModuleCat.{0, 0} ℤ)).homology ≅
      (continuousColimitComplex F).homology r :=
  ShortComplex.homologyMapIso
    (systemColimitShort F r)

/-- Filtered unions of discrete continuous coefficient modules commute with
continuous cohomology. -/
noncomputable def filteredUnionIso
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x)
    (r : ℕ) :
    colimit (continuousCohomologyDiagram F r) ≅
      (continuousInhomogeneousComplex c.pt).homology r :=
  (colim.mapIso (cochainDiagramIso F r)).symm ≪≫
    (filteredColimitHomology (continuousCochainSystem F) r).symm ≪≫
      systemColimitHomology F r ≪≫
        HomologicalComplex.homologyMapIso
          (cochainComplexIso c hinj hcover) r

end
end Towers.CField.PCohom
