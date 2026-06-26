import Submission.ClassField.ProfiniteCohom.ContinuousFunctor

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {J : Type} [SmallCategory J] [IsFiltered J]

abbrev continuousCochainDiagram
    (F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    J ⥤ ModuleCat ℤ :=
  F ⋙ inhomogeneousCochainFunctor ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) r

def continuousCochainCocone
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (r : ℕ) :
    Cocone (continuousCochainDiagram F r) :=
  (inhomogeneousCochainFunctor ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) r).mapCocone c

def continuousCochainUnion
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (r : ℕ) :
    colimit (continuousCochainDiagram F r) ⟶
      continuousInhomogeneousCochains c.pt r :=
  colimit.desc _ (continuousCochainCocone c r)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem lifts_filtered_union
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F)
    (s : Set c.pt.obj.obj.V) (hs : s.Finite)
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x) :
    ∃ j, ∀ x ∈ s, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | @insert x s hxs hs ih =>
      obtain ⟨i, yi, hyi⟩ := hcover x
      obtain ⟨j, hj⟩ := ih
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, ?_⟩
      intro z hz
      rcases mem_insert_iff.mp hz with rfl | hz
      · refine ⟨F.map fi yi, ?_⟩
        have hw := congrArg (fun φ ↦ φ yi) (c.w fi)
        simpa only [ConcreteCategory.comp_apply] using hw.trans hyi
      · obtain ⟨yj, hyj⟩ := hj z hz
        refine ⟨F.map fj yj, ?_⟩
        have hw := congrArg (fun φ ↦ φ yj) (c.w fj)
        simpa only [ConcreteCategory.comp_apply] using hw.trans hyj

omit [TotallyDisconnectedSpace G] in
theorem continuous_cochain_union
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (r : ℕ)
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x) :
    Function.Surjective (continuousCochainUnion c r) := by
  classical
  letI : DiscreteTopology c.pt.obj.obj.V := c.pt.property
  intro f
  obtain ⟨j, hj⟩ := lifts_filtered_union c (range f)
    (continuous_compact_discrete f.continuous) hcover
  let q : c.pt.obj.obj.V → (F.obj j).obj.obj.V := fun x ↦
    if hx : x ∈ range f then Classical.choose (hj x hx) else 0
  have hq : Continuous q := continuous_of_discreteTopology
  let fj : C(Fin r → G, (F.obj j).obj.obj.V) :=
    ⟨q ∘ f, hq.comp f.continuous⟩
  refine ⟨colimit.ι (continuousCochainDiagram F r) j fj, ?_⟩
  let D := continuousCochainDiagram F r
  have hleg : colimit.ι D j ≫ continuousCochainUnion c r =
      continuousCochainMap (c.ι.app j) r := by
    exact colimit.ι_desc (continuousCochainCocone c r) j
  rw [← ConcreteCategory.comp_apply, hleg]
  apply ContinuousMap.ext
  intro x
  change continuousCochainMap (c.ι.app j) r fj x = f x
  rw [continuous_cochain]
  change c.ι.app j (q (f x)) = f x
  dsimp [q]
  rw [dif_pos ⟨x, rfl⟩]
  exact Classical.choose_spec (hj (f x) ⟨x, rfl⟩)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem continuous_cochain_injective
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (r : ℕ)
    (hinj : ∀ j, Function.Injective (c.ι.app j)) :
    Function.Injective (continuousCochainUnion c r) := by
  intro x y hxy
  let D := continuousCochainDiagram F r
  let U := forget (ModuleCat ℤ)
  have hc : IsColimit (U.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves U (colimit.isColimit D)
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit hc y
  subst x
  subst y
  let k := IsFiltered.max i j
  let fi : i ⟶ k := IsFiltered.leftToMax i j
  let fj : j ⟶ k := IsFiltered.rightToMax i j
  let xi' : continuousInhomogeneousCochains (F.obj i) r := xi
  let yj' : continuousInhomogeneousCochains (F.obj j) r := yj
  have hstage : D.map fi xi = D.map fj yj := by
    change continuousCochainMap (F.map fi) r xi' =
      continuousCochainMap (F.map fj) r yj'
    apply ContinuousMap.ext
    intro z
    apply hinj k
    have hxy' : continuousCochainMap (c.ι.app i) r xi =
        continuousCochainMap (c.ι.app j) r yj := by
      have hi0 : colimit.ι D i ≫ continuousCochainUnion c r =
          continuousCochainMap (c.ι.app i) r := by
        exact colimit.ι_desc (continuousCochainCocone c r) i
      have hj0 : colimit.ι D j ≫ continuousCochainUnion c r =
          continuousCochainMap (c.ι.app j) r := by
        exact colimit.ι_desc (continuousCochainCocone c r) j
      have hi := congrArg (fun φ ↦ φ xi) hi0
      have hj := congrArg (fun φ ↦ φ yj) hj0
      exact hi.symm.trans (hxy.trans hj)
    have hz := congrArg (fun t : C(Fin r → G, c.pt.obj.obj.V) ↦ t z) hxy'
    have hz' : c.ι.app i (xi' z) = c.ι.app j (yj' z) := by
      change continuousCochainMap (c.ι.app i) r xi' z =
        continuousCochainMap (c.ι.app j) r yj' z at hz
      rw [continuous_cochain, continuous_cochain] at hz
      exact hz
    have hwi := congrArg (fun φ ↦ φ (xi' z)) (c.w fi)
    have hwj := congrArg (fun φ ↦ φ (yj' z)) (c.w fj)
    rw [continuous_cochain, continuous_cochain]
    exact hwi.trans (hz'.trans hwj.symm)
  have hfi : colimit.ι D i xi = colimit.ι D k (D.map fi xi) := by
    have hw := congrArg (fun φ ↦ φ xi) ((colimit.cocone D).w fi)
    simpa only [ConcreteCategory.comp_apply] using hw.symm
  have hfj : colimit.ι D j yj = colimit.ι D k (D.map fj yj) := by
    have hw := congrArg (fun φ ↦ φ yj) ((colimit.cocone D).w fj)
    simpa only [ConcreteCategory.comp_apply] using hw.symm
  exact hfi.trans ((congrArg (fun z ↦ colimit.ι D k z) hstage).trans hfj.symm)

noncomputable instance continuous_cochain_iso
    {F : J ⥤ DiscreteContAction (TopModuleCat ℤ) G} (c : Cocone F) (r : ℕ)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ x : c.pt.obj.obj.V,
      ∃ j, ∃ y : (F.obj j).obj.obj.V, c.ι.app j y = x) :
    IsIso (continuousCochainUnion c r) :=
  (ConcreteCategory.isIso_iff_bijective (continuousCochainUnion c r)).2
    ⟨continuous_cochain_injective c r hinj,
      continuous_cochain_union c r hcover⟩

end
end Submission.CField.PCohom
