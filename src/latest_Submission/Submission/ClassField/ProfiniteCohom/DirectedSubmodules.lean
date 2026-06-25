import Submission.ClassField.ProfiniteCohom.ContinuousComplexDiagram

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {M : DiscreteContAction (TopModuleCat ℤ) G}
  {I : Type}

abbrev DirectedSubmoduleIndex
    (S : I → Submodule ℤ M.obj.obj.V) := Set.range S

def directedSubmoduleStable
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) (g : G) (x : M.obj.obj.V)
    (hx : x ∈ T.1) : (M.obj.obj.ρ g).hom x ∈ T.1 := by
  obtain ⟨i, hi⟩ := T.2
  rw [← hi] at hx ⊢
  exact hstable i g x hx

set_option maxHeartbeats 1000000 in
-- Unfolding the nested topological-action and subtype-module structures is expensive.
noncomputable def directedSubmoduleStage
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) :
    DiscreteContAction (TopModuleCat ℤ) G := by
  letI : DiscreteTopology M.obj.obj.V := M.property
  letI : Module ℤ T.1 := Submodule.module T.1
  let act (g : G) : T.1 →L[ℤ] T.1 :=
    { toLinearMap := ((M.obj.obj.ρ g).hom.toLinearMap.domRestrict T.1).codRestrict T.1
        (fun x ↦ directedSubmoduleStable S hstable T g x.1 x.2)
      cont := continuous_of_discreteTopology }
  let A : Action (TopModuleCat ℤ) G :=
    { V := TopModuleCat.of ℤ T.1
      ρ :=
        { toFun := fun g ↦ TopModuleCat.ofHom (act g)
          map_one' := by
            apply ConcreteCategory.ext
            ext x
            dsimp [act]
            change (M.obj.obj.ρ 1).hom x.1 = x.1
            simp
          map_mul' := fun g h ↦ by
            apply ConcreteCategory.ext
            ext x
            dsimp [act]
            change (M.obj.obj.ρ (g * h)).hom x.1 =
              (M.obj.obj.ρ g * M.obj.obj.ρ h).hom x.1
            exact congrArg (fun φ : End M.obj.obj.V ↦ φ.hom x.1)
              (M.obj.obj.ρ.map_mul g h) } }
  have hact_cont : Continuous (fun p : G × T.1 ↦
      (⟨(M.obj.obj.ρ p.1).hom p.2.1,
        directedSubmoduleStable S hstable T p.1 p.2.1 p.2.2⟩ : T.1)) := by
    exact Continuous.subtype_mk
      (M.obj.property.1.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  have hA : A.IsContinuous := by
    rw [Action.isContinuous_def]
    change Continuous (fun p : G × T.1 ↦
      (⟨(M.obj.obj.ρ p.1).hom p.2.1,
        directedSubmoduleStable S hstable T p.1 p.2.1 p.2.2⟩ : T.1))
    exact hact_cont
  exact ⟨⟨A, hA⟩, by
    change DiscreteTopology T.1
    infer_instance⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem directed_stage_rho
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) (g : G)
    (x : (directedSubmoduleStage S hstable T).obj.obj.V) :
    ((directedSubmoduleStage S hstable T).obj.obj.ρ g).hom x =
      ⟨(M.obj.obj.ρ g).hom x.1,
        directedSubmoduleStable S hstable T g x.1 x.2⟩ := by
  rfl

def directedSubmoduleMap
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    {T U : DirectedSubmoduleIndex S} (hTU : T ≤ U) :
    directedSubmoduleStage S hstable T ⟶ directedSubmoduleStage S hstable U := by
  letI : DiscreteTopology M.obj.obj.V := M.property
  letI : Module ℤ T.1 := Submodule.module T.1
  letI : Module ℤ U.1 := Submodule.module U.1
  let f : T.1 →L[ℤ] U.1 :=
    { toLinearMap := T.1.subtype.codRestrict U.1 (fun x ↦ hTU x.2)
      cont := continuous_of_discreteTopology }
  apply ObjectProperty.homMk
  apply ObjectProperty.homMk
  exact
    { hom := TopModuleCat.ofHom f
      comm := fun g ↦ by
        ext x
        apply Subtype.ext
        rfl }

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem directed_submodule
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    {T U : DirectedSubmoduleIndex S} (hTU : T ≤ U) (x : T.1) :
    (directedSubmoduleMap S hstable hTU).hom.hom.hom.hom x =
      (⟨x.1, hTU x.2⟩ : U.1) := by
  rfl

def directedSubmoduleDiagram
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i) :
    DirectedSubmoduleIndex S ⥤ DiscreteContAction (TopModuleCat ℤ) G where
  obj T := directedSubmoduleStage S hstable T
  map f := directedSubmoduleMap S hstable (leOfHom f)
  map_id T := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

def directedSubmoduleInclusion
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) :
    directedSubmoduleStage S hstable T ⟶ M := by
  letI : DiscreteTopology M.obj.obj.V := M.property
  letI : Module ℤ T.1 := Submodule.module T.1
  let f : T.1 →L[ℤ] M.obj.obj.V :=
    ⟨T.1.subtype, continuous_subtype_val⟩
  apply ObjectProperty.homMk
  apply ObjectProperty.homMk
  exact
    { hom := TopModuleCat.ofHom f
      comm := fun g ↦ by
        ext x
        rfl }

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem directed_submodule_inclusion
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) (x : T.1) :
    (directedSubmoduleInclusion S hstable T).hom.hom.hom.hom x = x.1 := by
  rfl

def directedSubmoduleCocone
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i) :
    Cocone (directedSubmoduleDiagram S hstable) where
  pt := M
  ι :=
    { app := directedSubmoduleInclusion S hstable
      naturality := fun T U f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        let x' : T.1 := x
        change ((⟨x'.1, (leOfHom f) x'.2⟩ : U.1) : M.obj.obj.V) = x'.1
        rfl }

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem directed_submodule_cocone
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (T : DirectedSubmoduleIndex S) :
    Function.Injective ((directedSubmoduleCocone S hstable).ι.app T) := by
  intro x y h
  change (show T.1 from x) = (show T.1 from y)
  apply Subtype.ext
  change x.1 = y.1
  change x.1 = y.1 at h
  exact h

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem directed_cocone_cover
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (hcover : ∀ x, ∃ i, x ∈ S i) (x : M.obj.obj.V) :
    ∃ T, ∃ y : ((directedSubmoduleDiagram S hstable).obj T).obj.obj.V,
      (directedSubmoduleCocone S hstable).ι.app T y = x := by
  obtain ⟨i, hxi⟩ := hcover x
  let T : DirectedSubmoduleIndex S := ⟨S i, ⟨i, rfl⟩⟩
  let y : ((directedSubmoduleDiagram S hstable).obj T).obj.obj.V :=
    (⟨x, hxi⟩ : T.1)
  refine ⟨T, y, ?_⟩
  change x = x
  rfl

/-- **Milne II.4.4.** If a discrete `G`-module is the directed union of
`G`-stable submodules `S i`, continuous cohomology commutes with this union. -/
noncomputable def directedColimitIso
    (S : I → Submodule ℤ M.obj.obj.V)
    (hstable : ∀ i g x, x ∈ S i → (M.obj.obj.ρ g).hom x ∈ S i)
    (hdir : Directed (· ≤ ·) S)
    (hcover : ∀ x, ∃ i, x ∈ S i) (r : ℕ) :
    colimit (continuousCohomologyDiagram
      (directedSubmoduleDiagram S hstable) r) ≅
      (continuousInhomogeneousComplex M).homology r := by
  letI : IsDirectedOrder (DirectedSubmoduleIndex S) :=
    hdir.directedOn_range.isDirectedOrder
  let i₀ := Classical.choose (hcover (0 : M.obj.obj.V))
  letI : Nonempty (DirectedSubmoduleIndex S) :=
    ⟨⟨S i₀, ⟨i₀, rfl⟩⟩⟩
  letI : IsFiltered (DirectedSubmoduleIndex S) := inferInstance
  exact filteredUnionIso
    (directedSubmoduleCocone S hstable)
    (directed_submodule_cocone S hstable)
    (directed_cocone_cover S hstable hcover) r

end
end Submission.CField.PCohom

