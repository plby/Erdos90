import Submission.FieldTheory.HMRZassenhausOpen.BeforeJenningsLazard
import Submission.Group.ZassenhausFiniteQuotient.ResidualSeparation


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission
namespace TBluepr
namespace STBuild

section InitialZassenhausOpen

local notation "G" => initialGaloisGroup

universe u

open DGSep

noncomputable def DCModel.ofTowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : Submission.DCModel
      (p := p) (Γ := Γ) s hs n) :
    DCModel
      (p := p) (Γ := Γ) s hs n where
  completedGroupAlgebra := M.completedGroupAlgebra
  instRing := M.instRing
  instAlgebra := M.instAlgebra
  instUniformSpace := M.instUniformSpace
  topologicalRing := M.topologicalRing
  instCompleteSpace := M.instCompleteSpace
  t2Space := M.t2Space
  instCompactSpace := M.instCompactSpace
  totallyDisconnected := M.totallyDisconnected
  augmentationMap := M.augmentationMap
  augmentationMap_continuous := M.augmentationMap_continuous
  augmentationIdeal := M.augmentationIdeal
  augmentation_ideal_ker := M.augmentation_ideal_ker
  augmentationQuotient := M.augmentationQuotient
  instQuotientRing := M.instQuotientRing
  instQuotientAlgebra := M.instQuotientAlgebra
  quotientTopology := M.quotientTopology
  quotientTopologicalRing := M.quotientTopologicalRing
  quotientMap := M.quotientMap
  quotientMap_continuous := M.quotientMap_continuous
  quotientMap_surjective := M.quotientMap_surjective
  quotientMap_ker := M.quotientMap_ker
  canonicalUnit := M.canonicalUnit
  canonicalUnit_continuous := M.canonicalUnit_continuous
  canonicalUnit_augmentation := M.canonicalUnit_augmentation
  unitReduction := M.unitReduction
  unitReduction_continuous := M.unitReduction_continuous
  unitReduction_apply := M.unitReduction_apply
  quotientUnitMap := M.quotientUnitMap
  quotient_unit_continuous := M.quotient_unit_continuous
  quotient_unit_map := M.quotient_unit_map
  quotientEquiv := by
    simpa [
      generators_jennings_approx,
      Submission.generators_jennings_approx
    ] using M.quotientEquiv
  quotientEquiv_apply := by
    intro g
    simpa [
      dense_jennings_approx,
      Submission.dense_jennings_approx,
      generators_jennings_approx,
      Submission.generators_jennings_approx
    ] using M.quotientEquiv_apply g
  unit_map_ker := M.unit_map_ker

lemma model_discrete_towers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (h :
      ∃ M : Submission.DCModel
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          DiscreteTopology M.quotientUnitMap.range)) :
    ∃ M : DCModel
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  rcases h with ⟨M, hfinite, hdiscrete⟩
  let M' := DCModel.ofTowers M
  refine ⟨M', ?_, ?_⟩
  · simpa [M', DCModel.ofTowers] using hfinite
  · simpa [M', DCModel.ofTowers] using hdiscrete

/-- A finite Hausdorff augmentation quotient is enough to construct the dense-generators
Jennings witness. -/
lemma jennings_witness_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (h :
      ∃ M : DCModel
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          T2Space M.augmentationQuotient)) :
    Nonempty (TFWitnes p Γ n) := by
  rcases jennings_approx_t
      (p := p) (Γ := Γ) s hs n h with ⟨A⟩
  exact ⟨A.toJenningsWitness⟩

lemma nhds_topologically_fg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hpro : ProP.ProPGroup p Γ)
    (hfg : ∃ d : ℕ, ∃ s : Fin d → Γ,
      Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ((zassenhausFiltration p Γ n : Set Γ)) ∈ 𝓝 (1 : Γ) := by
  rcases hfg with ⟨d, s, hs⟩
  exact
    (ProP.filtration_topologically_generates
      p hpro s hs n).mem_nhds (by simp)

/-- Once the pro-`p` openness theorem gives openness of `Dₙ(Γ)`, the intrinsic quotient
`Γ ⧸ Dₙ(Γ)` is automa discrete. -/
noncomputable instance instTopologyApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hpro : ProP.ProPGroup p Γ)
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    DiscreteTopology
      (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  have hnhds :
      ((zassenhausFiltration p Γ n : Set Γ)) ∈ 𝓝 (1 : Γ) := by
    exact
      nhds_topologically_fg
        (p := p) (Γ := Γ) hpro ⟨d, s, hs⟩ n
  have hOpen : IsOpen ((zassenhausFiltration p Γ n : Set Γ)) := by
    exact Subgroup.isOpen_of_mem_nhds _ hnhds
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  dsimp [generators_jennings_approx]
  exact QuotientGroup.discreteTopology hOpen

/-- The intrinsic quotient `Γ ⧸ Dₙ(Γ)` is finite because it is compact and, by the pro-`p`
openness theorem above, discrete. -/
noncomputable instance instJenningsApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hpro : ProP.ProPGroup p Γ)
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Finite (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  have hnhds :
      ((zassenhausFiltration p Γ n : Set Γ)) ∈ 𝓝 (1 : Γ) := by
    exact
      nhds_topologically_fg
        (p := p) (Γ := Γ) hpro ⟨d, s, hs⟩ n
  have hOpen : IsOpen ((zassenhausFiltration p Γ n : Set Γ)) := by
    exact Subgroup.isOpen_of_mem_nhds _ hnhds
  unfold generators_jennings_approx
  letI : CompactSpace (Γ ⧸ zassenhausFiltration p Γ n) := by
    infer_instance
  letI : DiscreteTopology (Γ ⧸ zassenhausFiltration p Γ n) := by
    exact QuotientGroup.discreteTopology hOpen
  exact finite_of_compact_of_discrete

lemma jennings_datum (n : ℕ) :
    Nonempty (InitialJenningsDatum n) := by
  let _ : Fact initialPrimeParameter.Prime := by
    dsimp [initialPrimeParameter]
    infer_instance
  have hnhds :
      ((initialZassenhausFiltration n : Set G)) ∈ 𝓝 (1 : G) := by
    simpa [initialZassenhausFiltration] using
      nhds_topologically_fg
        (p := initialPrimeParameter) (Γ := G)
        initial_pro_three initial_topologically_fg n
  have hOpen : IsOpen ((initialZassenhausFiltration n : Set G)) := by
    exact Subgroup.isOpen_of_mem_nhds _ hnhds
  let _ := hOpen
  exact jennings_datum_nhds n hnhds

noncomputable def initialJenningsDatum (n : ℕ) : InitialJenningsDatum n :=
  Classical.choice (jennings_datum n)

abbrev initialJenningsQuotient (n : ℕ) : Type :=
  (initialJenningsDatum n).quotient

noncomputable instance instJenningsQuotient (n : ℕ) :
    Group (initialJenningsQuotient n) :=
  (initialJenningsDatum n).instGroup

noncomputable instance instSpaceJennings (n : ℕ) :
    TopologicalSpace (initialJenningsQuotient n) :=
  (initialJenningsDatum n).instTopologicalSpace

noncomputable instance instInitialJennings (n : ℕ) :
    Finite (initialJenningsQuotient n) :=
  (initialJenningsDatum n).instFinite

noncomputable instance instTopologyJennings (n : ℕ) :
    DiscreteTopology (initialJenningsQuotient n) :=
  (initialJenningsDatum n).instDiscreteTopology

noncomputable def initialJenningsMap (n : ℕ) :
    G →* initialJenningsQuotient n :=
  (initialJenningsDatum n).map

lemma initial_jennings_continuous (n : ℕ) :
    Continuous (initialJenningsMap n) :=
  (initialJenningsDatum n).continuous_map

lemma initial_jennings_ker (n : ℕ) :
    (initialJenningsMap n).ker ≤ initialZassenhausFiltration n :=
  (initialJenningsDatum n).ker_le

lemma initial_jennings_open (n : ℕ) :
    IsOpen (((initialJenningsMap n).ker : Set G)) := by
  simpa [MonoidHom.ker] using
    (isOpen_discrete ({1} : Set (initialJenningsQuotient n))).preimage
      (initial_jennings_continuous n)

end InitialZassenhausOpen

end STBuild
end TBluepr
end Submission
