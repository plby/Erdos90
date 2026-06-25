import Towers.ClassField.ProfiniteCohom.FilteredColimitExact
import Towers.ClassField.ProfiniteCohom.ContinuousComplex

namespace Towers.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

abbrev cochainColimitComplex
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.coconeOfHasColimitEval
    (finiteCochainDiagram (underlyingRep M))).pt

example (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    (cochainColimitComplex M).X n =
      colimit (cochainModuleDiagram M n) := by
  rfl

def finiteCochainDifferential
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    cochainModuleDiagram M n ⟶
      cochainModuleDiagram M (n + 1) where
  app N := ((finiteCochainDiagram (underlyingRep M)).obj N).d n (n + 1)
  naturality _ _ f :=
    ((finiteCochainDiagram (underlyingRep M)).map f).comm n (n + 1)

/-- The finite-quotient cochains as one cochain complex in the functor
category.  This is the input to filtered-colimit exactness. -/
noncomputable def finiteCochainSystem
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    CochainComplex
      (OpenInflationIndex G ⥤ ModuleCat.{0, 0} ℤ) ℕ :=
  CochainComplex.of (cochainModuleDiagram M)
    (finiteCochainDifferential M) fun n ↦ by
      apply NatTrans.ext
      funext N
      change ((finiteCochainDiagram (underlyingRep M)).obj N).d n (n + 1) ≫
          ((finiteCochainDiagram (underlyingRep M)).obj N).d
            (n + 1) (n + 1 + 1) = 0
      exact ((finiteCochainDiagram (underlyingRep M)).obj N).d_comp_d
        n (n + 1) (n + 1 + 1)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem system_d_app
    (M : DiscreteContAction (TopModuleCat ℤ) G) (i j : ℕ)
    (N : OpenInflationIndex G) :
    ((finiteCochainSystem M).d i j).app N =
      ((finiteCochainDiagram (underlyingRep M)).obj N).d i j := by
  by_cases h : i + 1 = j
  · subst j
    have hd : (finiteCochainSystem M).d i (i + 1) =
        finiteCochainDifferential M i := by
      exact CochainComplex.of_d _ _ i
    exact congrArg (fun φ ↦ φ.app N) hd
  · have hrel : ¬ (ComplexShape.up ℕ).Rel i j := by
      simpa only [ComplexShape.up_Rel] using h
    rw [(finiteCochainSystem M).shape i j hrel,
      ((finiteCochainDiagram (underlyingRep M)).obj N).shape i j hrel]
    rfl

def levelColimitChain
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    cochainColimitComplex M ⟶
      continuousInhomogeneousComplex M where
  f n := levelColimitContinuous M n
  comm' i j hij := by
    subst j
    apply colimit.hom_ext
    intro N
    change colimit.ι (cochainModuleDiagram M i) N ≫
        levelColimitContinuous M i ≫
          (continuousInhomogeneousComplex M).d i (i + 1) =
      colimit.ι (cochainModuleDiagram M i) N ≫
        (cochainColimitComplex M).d i (i + 1) ≫
          levelColimitContinuous M (i + 1)
    dsimp [levelColimitContinuous]
    have hι := colimit.ι_desc (levelContinuousCocone M i) N
    rw [← Category.assoc]
    refine (congrArg
      (fun k ↦ k ≫ (continuousInhomogeneousComplex M).d i (i + 1)) hι).trans ?_
    dsimp [cochainColimitComplex,
      HomologicalComplex.coconeOfHasColimitEval]
    change (levelContinuousCocone M i).ι.app N ≫
        (continuousInhomogeneousComplex M).d i (i + 1) =
      (colimit.ι (cochainModuleDiagram M i) N ≫
          colimMap (finiteCochainDifferential M i)) ≫
        colimit.desc (cochainModuleDiagram M (i + 1))
          (levelContinuousCocone M (i + 1))
    rw [ι_colimMap]
    rw [Category.assoc, colimit.ι_desc]
    dsimp [levelContinuousCocone, finiteCochainDifferential]
    have hcont : (continuousInhomogeneousComplex M).d i (i + 1) =
        continuousCochainDifferential M i :=
      CochainComplex.of_d _ _ i
    have hfinite :
        ((finiteCochainDiagram (underlyingRep M)).obj N).d i (i + 1) =
          inhomogeneousCochains.d
            ((underlyingRep M).quotientToInvariants
              ((OrderDual.ofDual N : OpenNormalSubgroup G) : Subgroup G)) i := by
      exact groupCohomology.inhomogeneousCochains.d_def _ i
    rw [hcont, hfinite]
    exact (level_continuous_d M (OrderDual.ofDual N) i).symm

noncomputable instance colimit_chain_iso
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    IsIso (levelColimitChain M) := by
  letI (n : ℕ) : IsIso ((levelColimitChain M).f n) :=
    level_colimit_iso M n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The degreewise finite-level colimit is the complex of continuous
inhomogeneous cochains. -/
noncomputable def colimitComplexIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    cochainColimitComplex M ≅
      continuousInhomogeneousComplex M :=
  asIso (levelColimitChain M)

noncomputable def systemEvaluationIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ)
    (N : OpenInflationIndex G) :
    ((finiteCochainSystem M).sc r).map
        ((evaluation (OpenInflationIndex G) (ModuleCat.{0, 0} ℤ)).obj N) ≅
      ((finiteCochainDiagram (underlyingRep M)).obj N).sc r := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simpa using (system_d_app M
      ((ComplexShape.up ℕ).prev r) r N).symm
  · simpa using (system_d_app M r
      ((ComplexShape.up ℕ).next r) N).symm

noncomputable def pointwiseHomologyIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((finiteCochainSystem M).sc r).homology ≅
      (finiteCochainSystem M).asFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r :=
  NatIso.ofComponents (fun N ↦
    (((finiteCochainSystem M).sc r).mapHomologyIso
      ((evaluation (OpenInflationIndex G) (ModuleCat.{0, 0} ℤ)).obj N)).symm)
    (by
      intro N K f
      let S := (finiteCochainSystem M).sc r
      let τ := (evaluation (OpenInflationIndex G) (ModuleCat.{0, 0} ℤ)).map f
      change S.homology.map f ≫
          (S.mapHomologyIso
            ((evaluation (OpenInflationIndex G) (ModuleCat.{0, 0} ℤ)).obj K)).inv =
        (S.mapHomologyIso
            ((evaluation (OpenInflationIndex G) (ModuleCat.{0, 0} ℤ)).obj N)).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans τ)
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp
      rfl)

noncomputable def systemFunctorIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    (finiteCochainSystem M).asFunctor ≅
      finiteCochainDiagram (underlyingRep M) :=
  NatIso.ofComponents (fun N ↦
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by
        intro i j _
        simpa using (system_d_app M i j N).symm))
    (by
      intro N K f
      ext n
      simp
      rfl)

noncomputable def systemDiagramIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((finiteCochainSystem M).sc r).homology ≅
      finiteCohomologyDiagram M r :=
  pointwiseHomologyIso M r ≪≫
    Functor.isoWhiskerRight (systemFunctorIso M)
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem colim_system_d
    (M : DiscreteContAction (TopModuleCat ℤ) G) (i j : ℕ) :
    colimMap ((finiteCochainSystem M).d i j) =
      (cochainColimitComplex M).d i j := by
  dsimp [cochainColimitComplex,
    HomologicalComplex.coconeOfHasColimitEval]
  apply congrArg colimMap
  apply NatTrans.ext
  funext N
  exact system_d_app M i j N

noncomputable def systemColimitIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    ((finiteCochainSystem M).sc r).map
        (colim : (OpenInflationIndex G ⥤ ModuleCat.{0, 0} ℤ) ⥤
          ModuleCat.{0, 0} ℤ) ≅
      (cochainColimitComplex M).sc r := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simpa using (colim_system_d M
      ((ComplexShape.up ℕ).prev r) r).symm
  · simpa using (colim_system_d M r
      ((ComplexShape.up ℕ).next r)).symm

noncomputable def colimitHomologyIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    (((finiteCochainSystem M).sc r).map
        (colim : (OpenInflationIndex G ⥤ ModuleCat.{0, 0} ℤ) ⥤
          ModuleCat.{0, 0} ℤ)).homology ≅
      (cochainColimitComplex M).homology r :=
  ShortComplex.homologyMapIso
    (systemColimitIso M r)

/-- **Milne II.4.2.** Continuous cohomology is the filtered colimit of the
cohomology of the finite quotients `G/N` with coefficients in `M^N`. -/
noncomputable def cohomologyColimitIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    colimit (finiteCohomologyDiagram M r) ≅
      (continuousInhomogeneousComplex M).homology r :=
  (colim.mapIso (systemDiagramIso M r)).symm ≪≫
    (filteredColimitHomology (finiteCochainSystem M) r).symm ≪≫
      colimitHomologyIso M r ≪≫
        HomologicalComplex.homologyMapIso
          (colimitComplexIso M) r

end
end Towers.CField.PCohom
