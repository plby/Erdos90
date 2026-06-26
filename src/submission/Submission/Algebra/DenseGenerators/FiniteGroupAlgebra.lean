import Mathlib
import Submission.Algebra.DenseGenerators.IdealQuotient


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

lemma
    dense_gens_topological
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        ∃ Q :
          GAAug
            (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
          Finite Q.augmentationQuotient ∧
            Nonempty
              (GTAug
                (p := p) (Γ := Γ) (s := s) (hs := hs) Q) := by
  rcases
      dense_gens_closed
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, hdata⟩
  rcases A.existsfin_topoaug_quotfinclosed hdata with
    ⟨Q, hfiniteQ, hTop⟩
  exact ⟨A, hdense, Q, hfiniteQ, hTop⟩

lemma
    gens_completed_open
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
  rcases
      dense_gens_topological
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, Q, hfiniteQ, hTop⟩
  have hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    A.openaug_powerfin_topoaugquot
      ⟨Q, hfiniteQ, hTop⟩
  exact ⟨A, hdense, hopen⟩

lemma
    gens_completed_algebraic
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        ∃ Q :
          GAAug
            (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
          Finite Q.augmentationQuotient ∧
            IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
              Set A.completedGroupAlgebra) := by
  rcases
      gens_completed_open
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, hopen⟩
  rcases A.existsfin_algaug_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs) hopen with
    ⟨Q, hfiniteQ⟩
  exact ⟨A, hdense, Q, hfiniteQ, hopen⟩

lemma
    gens_completed_fin
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        ∃ T : A.FAAugtru n,
          IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
            Set A.completedGroupAlgebra) := by
  rcases
      gens_completed_algebraic
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, Q, hfiniteQ, hopen⟩
  letI : Finite Q.augmentationQuotient := hfiniteQ
  let T : A.FAAugtru n :=
    Q.fin_alg_augtrunc
  have hker_open :
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    simpa [T] using
      Q.open_keropen_augpower
        hopen
  exact ⟨A, hdense, T, hker_open⟩

lemma
    gens_completed_topology
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        ∃ T : A.FAAugtru n,
          Nonempty T.DiscreteContTopo := by
  rcases
      gens_completed_fin
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, T, hker_open⟩
  exact
    ⟨A, hdense, T,
      ⟨T.discrete_conttopo_openker hker_open⟩⟩

lemma
    gens_completed_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.FCAugtru n) := by
  rcases
      gens_completed_topology
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, T, hTtop⟩
  rcases hTtop with ⟨HTop⟩
  exact
    ⟨A, hdense,
      ⟨T.fin_cont_augtrunc HTop⟩⟩

lemma
    gens_completed_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.ContAugPowerkernel n) := by
  rcases
      gens_completed_trunc
        (p := p) (Γ := Γ) s hs hn with
    ⟨A, hdense, hT⟩
  rcases hT with ⟨T⟩
  refine ⟨A, hdense, ?_⟩
  exact ⟨T.cont_aug_powerkernel⟩

lemma
    gens_completed_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower n := by
  rcases
      gens_completed_ambient
        (p := p) (Γ := Γ) s hs hn with
    ⟨A, hdense, hK⟩
  rcases hK with ⟨K⟩
  exact
    ⟨A, hdense,
      A.closed_augpower_contkernel K⟩

lemma
    completed_aug_pos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 0 < n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower n := by
  rcases nat_or_pos _hn with hOne | htwo
  · subst n
    exact
      gens_closed_aug
        (p := p) (Γ := Γ) s hs
  · exact
      gens_completed_closed
        (p := p) (Γ := Γ) s hs htwo

lemma
    gens_aug_pos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 0 < n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.TopoAugQuot n := by
  rcases
      completed_aug_pos
        (p := p) (Γ := Γ) s hs hn with
    ⟨A, hdense, hclosed⟩
  exact
    ⟨A, hdense,
      A.topoaug_quotclosed_augpower hclosed⟩

lemma
    gens_topological_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.TopoAugQuot n := by
  rcases n with _ | n
  · exact
      completed_topological_aug
        (p := p) (Γ := Γ) s hs
  · exact
      gens_aug_pos
        (p := p) (Γ := Γ) s hs (Nat.succ_pos n)

lemma
    dense_gens_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty
          (DCAlg
            (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  rcases
      gens_topological_aug
        (p := p) (Γ := Γ) s hs n with
    ⟨A, hdense, htop⟩
  rcases htop with ⟨Qalg, hT⟩
  rcases hT with ⟨T⟩
  exact
    ⟨A, hdense,
      dense_topological_aug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Qalg T⟩

lemma dense_completed_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      Nonempty
        (DCAlg
          (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  rcases
      dense_gens_aug
        (p := p) (Γ := Γ) s hs n with
    ⟨A, _hdense, hQ⟩
  exact ⟨A, hQ⟩

lemma dense_completed_reduction
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg (p := p) (Γ := Γ)
      (s := s) (hs := hs) n A) :
    Nonempty (DenseCompletedReduction Q) := by
  let unitReduction : Units A.completedGroupAlgebra →* Units Q.augmentationQuotient :=
    Units.map Q.quotientMap.toRingHom.toMonoidHom
  have happly :
      ∀ x : Units A.completedGroupAlgebra,
        (unitReduction x : Q.augmentationQuotient) =
          Q.quotientMap (x : A.completedGroupAlgebra) := by
    intro x
    rfl
  have hcontinuous : Continuous unitReduction := by
    exact Continuous.units_map
      Q.quotientMap.toRingHom.toMonoidHom Q.quotientMap_continuous
  refine ⟨?_⟩
  exact
    { unitReduction := unitReduction
      unitReduction_continuous := hcontinuous
      unitReduction_apply := happly }

lemma dense_generators_completed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    {Q : DCAlg (p := p) (Γ := Γ)
      (s := s) (hs := hs) n A}
    (R : DenseCompletedReduction Q) :
    Nonempty (DenseGeneratorsCompleted R) := by
  let quotientUnitMap : Γ →* Units Q.augmentationQuotient :=
    R.unitReduction.comp A.canonicalUnit
  have hcontinuous : Continuous quotientUnitMap := by
    have hunit : Continuous R.unitReduction := R.unitReduction_continuous
    have hcanonical : Continuous A.canonicalUnit := A.canonicalUnit_continuous
    exact hunit.comp hcanonical
  refine ⟨?_⟩
  exact
    { quotientUnitMap := quotientUnitMap
      quotient_unit_continuous := hcontinuous
      quotient_unit_map := rfl }

lemma generators_completed_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      Nonempty
        (DCLayer
          (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  rcases dense_completed_ambient
      (p := p) (Γ := Γ) s hs n with ⟨A, hQ⟩
  rcases hQ with ⟨Q⟩
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  exact ⟨A, ⟨Q.toQuotientLayer R U⟩⟩

lemma
    gens_completed_layer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty
          (DCLayer
            (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  rcases
      dense_gens_aug
        (p := p) (Γ := Γ) s hs n with
    ⟨A, hdense, hQ⟩
  rcases hQ with ⟨Q⟩
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  exact ⟨A, hdense, ⟨Q.toQuotientLayer R U⟩⟩

lemma dense_algebra_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Nonempty
      (DCCore
        (p := p) (Γ := Γ) s hs n) := by
  rcases generators_completed_ambient
      (p := p) (Γ := Γ) s hs n with ⟨A, hquotient⟩
  rcases hquotient with ⟨Q⟩
  exact ⟨A.toCore Q⟩

def generators_lazard_subgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (m : ℕ) : Subgroup Γ where
  carrier :=
    { x | (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ m }
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    have hmul :
        (C.canonicalUnit (x * y) : C.completedGroupAlgebra) - 1 =
          (C.canonicalUnit x : C.completedGroupAlgebra) *
              ((C.canonicalUnit y : C.completedGroupAlgebra) - 1) +
            ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) := by
      simp only [map_mul, Units.val_mul]
      noncomm_ring
    change
      (C.canonicalUnit (x * y) : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ m
    rw [hmul]
    exact
      (C.augmentationIdeal ^ m).add_mem
        ((C.augmentationIdeal ^ m).mul_mem_left
          (C.canonicalUnit x : C.completedGroupAlgebra) hy)
        hx
  inv_mem' := by
    intro x hx
    have hinv :
        (C.canonicalUnit x⁻¹ : C.completedGroupAlgebra) - 1 =
          -((C.canonicalUnit x⁻¹ : C.completedGroupAlgebra) *
            ((C.canonicalUnit x : C.completedGroupAlgebra) - 1)) := by
      simp only [map_inv]
      noncomm_ring [Units.inv_mul]
    change
      (C.canonicalUnit x⁻¹ : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ m
    rw [hinv]
    exact
      (C.augmentationIdeal ^ m).neg_mem
        ((C.augmentationIdeal ^ m).mul_mem_left
          (C.canonicalUnit x⁻¹ : C.completedGroupAlgebra) hx)

lemma jennings_lazard_augmentation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n m : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (g : Γ) :
    g ∈ generators_lazard_subgroup C m ↔
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ m := by
  rfl

structure JLBound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  augmentation_subgroup_zassenhaus :
    generators_lazard_subgroup C n ≤
      zassenhausFiltration p Γ n

lemma JLBound.mem_zassenhaus
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : JLBound C)
    {g : Γ}
    (hg : (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n) :
    g ∈ zassenhausFiltration p Γ n := by
  have hsubgroup :
      g ∈ generators_lazard_subgroup C n := by
    exact
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C g).2 hg
  exact H.augmentation_subgroup_zassenhaus hsubgroup

lemma dense_lazard_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Nonempty (JLBound C) ↔
      ∀ g : Γ,
        (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
          g ∈ zassenhausFiltration p Γ n := by
  constructor
  · rintro ⟨H⟩ g hg
    exact H.mem_zassenhaus (p := p) (Γ := Γ) (s := s) (hs := hs) (g := g) hg
  · intro H
    refine ⟨?_⟩
    refine
      { augmentation_subgroup_zassenhaus := ?_ }
    intro g hg
    exact H g
      ((jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C g).1 hg)

structure JLInput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  positive_bound :
    1 < n →
      Nonempty (JLBound C)

lemma jennings_lazard_positive
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (H : JLInput C)
    (hn : 1 < n) :
    Nonempty (JLBound C) := by
  exact H.positive_bound hn

lemma
    dense_jennings_lazard
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (_C : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≤ 1) :
    ∀ g : Γ,
      (_C.canonicalUnit g : _C.completedGroupAlgebra) - 1 ∈ _C.augmentationIdeal ^ n →
        g ∈ zassenhausFiltration p Γ n := by
  intro g _hmem
  exact zassenhaus_filtration_one p Γ hn g

lemma
    generators_jennings_lazard
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C)
    (hn : 1 < n) :
    ∀ g : Γ,
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
        g ∈ zassenhausFiltration p Γ n := by
  rcases
      jennings_lazard_positive
        (p := p) (Γ := Γ) (s := s) (hs := hs) C Hinput hn with
    ⟨H⟩
  exact
    (dense_lazard_bound
      (p := p) (Γ := Γ) (s := s) (hs := hs) C).1 ⟨H⟩

lemma dense_generators_lazard
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C) :
    ∀ g : Γ,
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
        g ∈ zassenhausFiltration p Γ n := by
  by_cases hn : n ≤ 1
  · exact
      dense_jennings_lazard
        (p := p) (Γ := Γ) (s := s) (hs := hs) C hn
  · have hpos : 1 < n := Nat.lt_of_not_ge hn
    exact
      generators_jennings_lazard
        (p := p) (Γ := Γ) (s := s) (hs := hs) C Hinput hpos

lemma jennings_lazard_sub
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {g : Γ}
    (hmem : (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n) :
    g ∈ C.quotientUnitMap.ker := by
  letI := C.instRing
  letI := C.instQuotientRing
  have hker :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈
        RingHom.ker C.quotientMap.toRingHom := by
    rw [C.quotientMap_ker]
    exact hmem
  have hquotient_sub :
      C.quotientMap.toRingHom
          ((C.canonicalUnit g : C.completedGroupAlgebra) - 1) = 0 := by
    simpa [RingHom.mem_ker] using hker
  have hquotient_one :
      C.quotientMap (C.canonicalUnit g : C.completedGroupAlgebra) =
        (1 : C.augmentationQuotient) := by
    change C.quotientMap.toRingHom (C.canonicalUnit g : C.completedGroupAlgebra) =
      (1 : C.augmentationQuotient)
    rw [← sub_eq_zero]
    simpa [map_sub, map_one] using hquotient_sub
  have hunit_reduced :
      C.unitReduction (C.canonicalUnit g) = (1 : Units C.augmentationQuotient) := by
    apply Units.ext
    simpa [C.unitReduction_apply] using hquotient_one
  rw [MonoidHom.mem_ker]
  simpa [C.quotient_unit_map] using hunit_reduced

lemma jennings_lazard_subgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    C.quotientUnitMap.ker =
      generators_lazard_subgroup C n := by
  ext g
  constructor
  · intro hg
    exact
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C g).2
        (jennings_lazard_ker
          (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hg)
  · intro hg
    exact
      jennings_lazard_sub
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C
        ((jennings_lazard_augmentation
          (p := p) (Γ := Γ) (s := s) (hs := hs) C g).1 hg)

def JLBound.kernel_upper_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : JLBound C) :
    LUBound C := by
  refine
    { quotient_unit_ker := ?_ }
  intro g hg
  have hcongruence :
      g ∈ generators_lazard_subgroup C n := by
    rw [← jennings_lazard_subgroup
      (p := p) (Γ := Γ) (s := s) (hs := hs) C]
    exact hg
  exact H.augmentation_subgroup_zassenhaus hcongruence

def LUBound.pos_dim_subgroupbound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (U : LUBound C) :
    JLBound C := by
  refine
    { augmentation_subgroup_zassenhaus := ?_ }
  intro g hg
  have hker : g ∈ C.quotientUnitMap.ker := by
    rw [jennings_lazard_subgroup
      (p := p) (Γ := Γ) (s := s) (hs := hs) C]
    exact hg
  exact U.quotient_unit_ker hker

lemma jennings_lazard_upper
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Nonempty (LUBound C) ↔
      Nonempty (JLBound C) := by
  constructor
  · rintro ⟨U⟩
    exact ⟨U.pos_dim_subgroupbound (p := p) (Γ := Γ) (s := s) (hs := hs)⟩
  · rintro ⟨H⟩
    exact ⟨H.kernel_upper_bound (p := p) (Γ := Γ) (s := s) (hs := hs)⟩

structure GCAmbien.JLDiminp
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 1) where
  positiveDimensionInput :
    ∀ {n : ℕ}
      (Q : DCAlg
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
      (R : DenseCompletedReduction Q)
      (U : DenseGeneratorsCompleted R),
      JLInput
        (A.toCore (Q.toQuotientLayer R U))

def GCAmbien.JLDiminp.toCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (H : A.JLDiminp)
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    JLInput
      (A.toCore (Q.toQuotientLayer R U)) := by
  exact H.positiveDimensionInput Q R U

structure GCPackag.PDUpperb
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  pointwise_mem_zassenhaus :
    ∀ g : Γ,
      ((P.toAmbient.toCore (Q.toQuotientLayer R U)).canonicalUnit g :
          (P.toAmbient.toCore (Q.toQuotientLayer R U)).completedGroupAlgebra) - 1 ∈
        (P.toAmbient.toCore (Q.toQuotientLayer R U)).augmentationIdeal ^ n →
      g ∈ zassenhausFiltration p Γ n

abbrev denseGroupAlgebra
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ] :=
  MonoidAlgebra (ZMod p) Λ

def denseGeneratorsElement
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (x : Λ) :
    denseGroupAlgebra p Λ :=
  MonoidAlgebra.single x 1

noncomputable def denseGeneratorsAugmentation
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ] :
    denseGroupAlgebra p Λ →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p)

@[simp]
lemma dense_algebra_element
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsAugmentation p Λ
        (denseGeneratorsElement p Λ x) =
      1 := by
  simp [
    denseGeneratorsAugmentation,
    denseGeneratorsElement,
    MonoidAlgebra.lift_single
  ]

@[simp]
lemma dense_algebra_single
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) (c : ZMod p) :
    denseGeneratorsAugmentation p Λ
        (MonoidAlgebra.single x c : denseGroupAlgebra p Λ) =
      c := by
  simp [
    denseGeneratorsAugmentation,
    MonoidAlgebra.lift_single
  ]

def denseGeneratorsIdeal
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ] :
    Ideal (denseGroupAlgebra p Λ) :=
  Ideal.span
    { y : denseGroupAlgebra p Λ |
      ∃ x : Λ,
        denseGeneratorsElement p Λ x - 1 = y }

lemma dense_algebra_ker
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    denseGeneratorsIdeal p Λ ≤
      RingHom.ker (denseGeneratorsAugmentation p Λ).toRingHom := by
  rw [denseGeneratorsIdeal]
  refine Ideal.span_le.mpr ?_
  rintro y ⟨x, rfl⟩
  change
    denseGeneratorsAugmentation p Λ
          (denseGeneratorsElement p Λ x - 1) =
        0
  simp

lemma dense_smul_element
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : denseGroupAlgebra p Λ) :
    x.sum
        (fun g c =>
          c • (denseGeneratorsElement p Λ g - 1)) =
      x -
        algebraMap (ZMod p) (denseGroupAlgebra p Λ)
          (denseGeneratorsAugmentation p Λ x) := by
  refine MonoidAlgebra.induction_linear x ?zero ?add ?single
  · change
      (0 : denseGroupAlgebra p Λ) =
        0 -
          algebraMap (ZMod p) (denseGroupAlgebra p Λ)
            (denseGeneratorsAugmentation p Λ 0)
    simp [denseGeneratorsAugmentation]
    rfl
  · intro x y hx hy
    let f : Λ → ZMod p → denseGroupAlgebra p Λ :=
      fun g c =>
        c • (denseGeneratorsElement p Λ g - 1)
    change Finsupp.sum (x + y) f =
      x + y -
        algebraMap (ZMod p) (denseGroupAlgebra p Λ)
          (denseGeneratorsAugmentation p Λ (x + y))
    have hsum_add :
        Finsupp.sum (x + y) f = Finsupp.sum x f + Finsupp.sum y f :=
      Finsupp.sum_add_index'
        (f := x)
        (g := y)
        (h := f)
        (by
          intro g
          simp [f])
        (by
          intro g a b
          simp [f, add_smul])
    rw [hsum_add, map_add]
    rw [map_add]
    rw [hx, hy]
    abel
  · intro g c
    let f : Λ → ZMod p → denseGroupAlgebra p Λ :=
      fun g c =>
        c • (denseGeneratorsElement p Λ g - 1)
    change Finsupp.sum (MonoidAlgebra.single g c) f =
      MonoidAlgebra.single g c -
        algebraMap (ZMod p) (denseGroupAlgebra p Λ)
          (denseGeneratorsAugmentation p Λ
            (MonoidAlgebra.single g c))
    have hsingle : Finsupp.sum (MonoidAlgebra.single g c) f = f g c :=
      Finsupp.sum_single_index (by simp [f])
    rw [hsingle]
    simp [
      f,
      denseGeneratorsElement,
      denseGeneratorsAugmentation,
      MonoidAlgebra.lift_single,
      Algebra.smul_def,
      mul_sub
    ]

lemma dense_generators_ideal
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    RingHom.ker (denseGeneratorsAugmentation p Λ).toRingHom ≤
      denseGeneratorsIdeal p Λ := by
  intro x hx
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hterm :
      ∀ (g : Λ) (c : ZMod p),
        c • (denseGeneratorsElement p Λ g - 1) ∈ I := by
    intro g c
    have hgen : denseGeneratorsElement p Λ g - 1 ∈ I := by
      dsimp [I, denseGeneratorsIdeal]
      exact Ideal.subset_span ⟨g, rfl⟩
    have hmul :
        algebraMap (ZMod p) (denseGroupAlgebra p Λ) c *
            (denseGeneratorsElement p Λ g - 1) ∈ I :=
      I.mul_mem_left _ hgen
    simpa [Algebra.smul_def] using hmul
  have hsum :
      x.sum
          (fun g c =>
            c • (denseGeneratorsElement p Λ g - 1)) ∈ I := by
    change
      (∑ g ∈ x.support,
        x g • (denseGeneratorsElement p Λ g - 1)) ∈ I
    exact I.sum_mem fun g _hg => hterm g (x g)
  have haug_zero :
      denseGeneratorsAugmentation p Λ x = 0 := by
    simpa [RingHom.mem_ker] using hx
  have hdecomp :
      x.sum
          (fun g c =>
            c • (denseGeneratorsElement p Λ g - 1)) =
        x := by
    have hdecomp_zero :
        x.sum
            (fun g c =>
              c • (denseGeneratorsElement p Λ g - 1)) =
          x -
            algebraMap (ZMod p) (denseGroupAlgebra p Λ) (0 : ZMod p) := by
      rw [← haug_zero]
      exact
        dense_smul_element
          (p := p) (Λ := Λ) x
    have htail :
        x - algebraMap (ZMod p) (denseGroupAlgebra p Λ) (0 : ZMod p) =
          x := by
      rw [map_zero, sub_zero]
    exact hdecomp_zero.trans htail
  simpa [I, hdecomp] using hsum

lemma dense_generators_ker
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    denseGeneratorsIdeal p Λ =
      RingHom.ker (denseGeneratorsAugmentation p Λ).toRingHom := by
  exact le_antisymm
    dense_algebra_ker
    dense_generators_ideal

lemma dense_element_ideal
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsElement p Λ x - 1 ∈
      denseGeneratorsIdeal p Λ := by
  have hgenerator :
      denseGeneratorsElement p Λ x - 1 ∈
        { y : denseGroupAlgebra p Λ |
          ∃ z : Λ,
            denseGeneratorsElement p Λ z - 1 = y } := by
    exact ⟨x, rfl⟩
  exact Ideal.subset_span hgenerator

def denseLetterSpan
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ] :
    Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
  Submodule.span (ZMod p)
    { y : denseGroupAlgebra p Λ |
      ∃ x : Λ,
        denseGeneratorsElement p Λ x - 1 = y }

lemma element_letter_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsElement p Λ x - 1 ∈
      denseLetterSpan p Λ := by
  dsimp [denseLetterSpan]
  exact Submodule.subset_span ⟨x, rfl⟩

lemma dense_letter_ideal
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    (denseLetterSpan p Λ :
      Set (denseGroupAlgebra p Λ)) ⊆
      (denseGeneratorsIdeal p Λ :
        Set (denseGroupAlgebra p Λ)) := by
  let S : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ x : Λ,
        denseGeneratorsElement p Λ x - 1 = y }
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) S := by
    simpa [denseLetterSpan, S] using hy
  refine Submodule.span_induction
    (s := S)
    (p := fun z _ => z ∈ I)
    ?mem ?zero ?add ?smul hyspan
  · rintro z ⟨x, rfl⟩
    exact
      dense_element_ideal
        (p := p) (Λ := Λ) x
  · exact I.zero_mem
  · intro x y _hx _hy hx_mem hy_mem
    exact I.add_mem hx_mem hy_mem
  · intro c x _hx hx_mem
    have hmul : algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * x ∈ I :=
      I.mul_mem_left _ hx_mem
    simpa [I, Algebra.smul_def] using hmul

lemma generators_letter_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    (denseGeneratorsIdeal p Λ :
      Set (denseGroupAlgebra p Λ)) ⊆
      (denseLetterSpan p Λ :
        Set (denseGroupAlgebra p Λ)) := by
  intro x hx
  let L : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseLetterSpan p Λ
  have hxker :
      x ∈ RingHom.ker
          (denseGeneratorsAugmentation p Λ).toRingHom := by
    simpa [dense_generators_ker]
      using hx
  have haug_zero :
      denseGeneratorsAugmentation p Λ x = 0 := by
    simpa [RingHom.mem_ker] using hxker
  have hterm :
      ∀ (g : Λ) (c : ZMod p),
        c • (denseGeneratorsElement p Λ g - 1) ∈ L := by
    intro g c
    exact
      L.smul_mem c
        (element_letter_span
          (p := p) (Λ := Λ) g)
  have hsum :
      x.sum
          (fun g c =>
            c • (denseGeneratorsElement p Λ g - 1)) ∈ L := by
    change
      (∑ g ∈ x.support,
        x g • (denseGeneratorsElement p Λ g - 1)) ∈ L
    exact L.sum_mem fun g _hg => hterm g (x g)
  have hdecomp :
      x.sum
          (fun g c =>
            c • (denseGeneratorsElement p Λ g - 1)) =
        x := by
    have hdecomp_zero :
        x.sum
            (fun g c =>
              c • (denseGeneratorsElement p Λ g - 1)) =
          x -
            algebraMap (ZMod p) (denseGroupAlgebra p Λ) (0 : ZMod p) := by
      rw [← haug_zero]
      exact
        dense_smul_element
          (p := p) (Λ := Λ) x
    have htail :
        x - algebraMap (ZMod p) (denseGroupAlgebra p Λ) (0 : ZMod p) =
          x := by
      rw [map_zero, sub_zero]
    exact hdecomp_zero.trans htail
  simpa [L, hdecomp] using hsum

lemma dense_letter_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {x : denseGroupAlgebra p Λ} :
    x ∈ denseGeneratorsIdeal p Λ ↔
      x ∈ denseLetterSpan p Λ := by
  constructor
  · intro hx
    exact
      generators_letter_span
        (p := p) (Λ := Λ) hx
  · intro hx
    exact
      dense_letter_ideal
        (p := p) (Λ := Λ) hx

lemma dense_generators_factors
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (w : List Λ) :
    (w.map fun x =>
        denseGeneratorsElement p Λ x - 1).prod ∈
      denseGeneratorsIdeal p Λ ^ w.length := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.length_nil]
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | cons x w ih =>
      let head : denseGroupAlgebra p Λ :=
        denseGeneratorsElement p Λ x - 1
      let tail : denseGroupAlgebra p Λ :=
        (w.map fun y =>
          denseGeneratorsElement p Λ y - 1).prod
      have hhead_one : head ∈ I ^ 1 := by
        have hhead : head ∈ I := by
          dsimp [head, I]
          exact
            dense_element_ideal
              (p := p) (Λ := Λ) x
        simpa [Submodule.pow_one] using hhead
      have htail : tail ∈ I ^ w.length := by
        dsimp [tail]
        exact ih
      have hmul :
          head * tail ∈ I ^ (1 + w.length) := by
        rw [Ideal.IsTwoSided.pow_add (I := I) 1 w.length]
        exact Ideal.mul_mem_mul hhead_one htail
      simpa [I, head, tail, Nat.add_comm] using hmul

noncomputable def denseGeneratorsGenerator
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    {n : ℕ}
    (w : List.Vector Λ n) :
    denseGroupAlgebra p Λ :=
  (w.toList.map fun x =>
    denseGeneratorsElement p Λ x - 1).prod

lemma dense_generators_generator
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    (w : List.Vector Λ n) :
    denseGeneratorsGenerator p Λ w ∈
      denseGeneratorsIdeal p Λ ^ n := by
  have hmem :
      (w.toList.map fun x =>
          denseGeneratorsElement p Λ x - 1).prod ∈
        denseGeneratorsIdeal p Λ ^ w.toList.length :=
    dense_generators_factors
      (p := p) (Λ := Λ) w.toList
  simpa [denseGeneratorsGenerator] using hmem

lemma dense_generators_cons
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    (x : Λ)
    (w : List.Vector Λ n) :
    denseGeneratorsGenerator p Λ (List.Vector.cons x w) =
      (denseGeneratorsElement p Λ x - 1) *
        denseGeneratorsGenerator p Λ w := by
  simp [
    denseGeneratorsGenerator,
    List.Vector.toList_cons
  ]

def denseGeneratorsSpan
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
  Submodule.span (ZMod p)
    { y : denseGroupAlgebra p Λ |
      ∃ w : List.Vector Λ n,
        denseGeneratorsGenerator p Λ w = y }

lemma dense_generator_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    (w : List.Vector Λ n) :
    denseGeneratorsGenerator p Λ w ∈
      denseGeneratorsSpan p Λ n := by
  dsimp [denseGeneratorsSpan]
  exact Submodule.subset_span ⟨w, rfl⟩

lemma dense_span_pow
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (n : ℕ) :
    (denseGeneratorsSpan p Λ n :
      Set (denseGroupAlgebra p Λ)) ⊆
      (((denseGeneratorsIdeal p Λ) ^ n :
          Ideal (denseGroupAlgebra p Λ)) :
        Set (denseGroupAlgebra p Λ)) := by
  let T : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ w : List.Vector Λ n,
        denseGeneratorsGenerator p Λ w = y }
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) T := by
    simpa [denseGeneratorsSpan, T] using hy
  refine Submodule.span_induction
    (s := T)
    (p := fun z _ => z ∈ I ^ n)
    ?mem ?zero ?add ?smul hyspan
  · rintro z ⟨w, rfl⟩
    exact
      dense_generators_generator
        (p := p) (Λ := Λ) w
  · exact (I ^ n).zero_mem
  · intro x y _hx _hy hx_mem hy_mem
    exact (I ^ n).add_mem hx_mem hy_mem
  · intro c x _hx hx_mem
    have hmul : algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * x ∈
        I ^ n :=
      (I ^ n).mul_mem_left _ hx_mem
    simpa [I, Algebra.smul_def] using hmul

lemma dense_element_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsElement p Λ x - 1 ∈
      denseGeneratorsSpan p Λ 1 := by
  let w : List.Vector Λ 1 := List.Vector.cons x List.Vector.nil
  have hword :
      denseGeneratorsGenerator p Λ w =
        denseGeneratorsElement p Λ x - 1 := by
    simp [
      w,
      denseGeneratorsGenerator,
      List.Vector.nil
    ]
  rw [← hword]
  exact
    dense_generator_span
      (p := p) (Λ := Λ) w

lemma dense_generators_letter
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    (denseLetterSpan p Λ :
      Set (denseGroupAlgebra p Λ)) ⊆
      (denseGeneratorsSpan p Λ 1 :
        Set (denseGroupAlgebra p Λ)) := by
  let S : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ x : Λ,
        denseGeneratorsElement p Λ x - 1 = y }
  let W : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseGeneratorsSpan p Λ 1
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) S := by
    simpa [denseLetterSpan, S] using hy
  refine Submodule.span_induction
    (s := S)
    (p := fun z _ => z ∈ W)
    ?mem ?zero ?add ?smul hyspan
  · rintro z ⟨x, rfl⟩
    exact
      dense_element_span
        (p := p) (Λ := Λ) x
  · exact W.zero_mem
  · intro x y _hx _hy hx_mem hy_mem
    exact W.add_mem hx_mem hy_mem
  · intro c x _hx hx_mem
    exact W.smul_mem c hx_mem

lemma dense_generators_one
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    (denseGeneratorsIdeal p Λ :
      Set (denseGroupAlgebra p Λ)) ⊆
      (denseGeneratorsSpan p Λ 1 :
        Set (denseGroupAlgebra p Λ)) := by
  intro x hx
  exact
    dense_generators_letter
      (p := p) (Λ := Λ)
      (generators_letter_span
        (p := p) (Λ := Λ) hx)

lemma dense_letter_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    {a b : denseGroupAlgebra p Λ}
    (ha : a ∈ denseLetterSpan p Λ)
    (hb : b ∈ denseGeneratorsSpan p Λ n) :
    a * b ∈ denseGeneratorsSpan p Λ (n + 1) := by
  let S : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ x : Λ,
        denseGeneratorsElement p Λ x - 1 = y }
  let T : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ w : List.Vector Λ n,
        denseGeneratorsGenerator p Λ w = y }
  let L : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseLetterSpan p Λ
  let Wn : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseGeneratorsSpan p Λ n
  let Wsucc : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseGeneratorsSpan p Λ (n + 1)
  have hscalar_mul_right :
      ∀ (c : ZMod p) (x y : denseGroupAlgebra p Λ),
        x * (c • y) = c • (x * y) := by
    intro c x y
    calc
      x * (c • y) =
          x * (algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * y) := by
            rw [Algebra.smul_def]
      _ = (x * algebraMap (ZMod p) (denseGroupAlgebra p Λ) c) * y := by
            rw [mul_assoc]
      _ = (algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * x) * y := by
            rw [Algebra.commutes]
      _ = algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * (x * y) := by
            rw [mul_assoc]
      _ = c • (x * y) := by
            rw [Algebra.smul_def]
  have hscalar_mul_left :
      ∀ (c : ZMod p) (x y : denseGroupAlgebra p Λ),
        (c • x) * y = c • (x * y) := by
    intro c x y
    calc
      (c • x) * y =
          (algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * x) * y := by
            rw [Algebra.smul_def]
      _ = algebraMap (ZMod p) (denseGroupAlgebra p Λ) c * (x * y) := by
            rw [mul_assoc]
      _ = c • (x * y) := by
            rw [Algebra.smul_def]
  have hletter_mul :
      ∀ x : Λ,
        ∀ y ∈ Wn,
          (denseGeneratorsElement p Λ x - 1) * y ∈ Wsucc := by
    intro x y hy
    have hyspan : y ∈ Submodule.span (ZMod p) T := by
      simpa [Wn, denseGeneratorsSpan, T] using hy
    refine Submodule.span_induction
      (s := T)
      (p := fun z _ =>
        (denseGeneratorsElement p Λ x - 1) * z ∈ Wsucc)
      ?_ ?_ ?_ ?_ hyspan
    · rintro z ⟨w, rfl⟩
      rw [
        ← dense_generators_cons
          (p := p) (Λ := Λ) x w
      ]
      exact
        dense_generator_span
          (p := p) (Λ := Λ) (List.Vector.cons x w)
    · change
        (denseGeneratorsElement p Λ x - 1) *
            (0 : denseGroupAlgebra p Λ) ∈ Wsucc
      rw [mul_zero]
      exact Wsucc.zero_mem
    · intro y z _hy _hz hy_mem hz_mem
      rw [mul_add]
      exact Wsucc.add_mem hy_mem hz_mem
    · intro c z _hz hz_mem
      rw [hscalar_mul_right]
      exact Wsucc.smul_mem c hz_mem
  have hmul_all :
      ∀ x ∈ L, ∀ y ∈ Wn, x * y ∈ Wsucc := by
    intro x hx
    have hxspan : x ∈ Submodule.span (ZMod p) S := by
      simpa [L, denseLetterSpan, S] using hx
    refine Submodule.span_induction
      (s := S)
      (p := fun z _ => ∀ y ∈ Wn, z * y ∈ Wsucc)
      ?_ ?_ ?_ ?_ hxspan
    · rintro z ⟨g, rfl⟩ y hy
      exact hletter_mul g y hy
    · intro y _hy
      change (0 : denseGroupAlgebra p Λ) * y ∈ Wsucc
      rw [zero_mul]
      exact Wsucc.zero_mem
    · intro x y _hx _hy hx_mem hy_mem z hz
      rw [add_mul]
      exact Wsucc.add_mem (hx_mem z hz) (hy_mem z hz)
    · intro c x _hx hx_mem y hy
      rw [hscalar_mul_left]
      exact Wsucc.smul_mem c (hx_mem y hy)
  exact hmul_all a (by simpa [L] using ha) b (by simpa [Wn] using hb)

lemma dense_succ_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (n : ℕ) :
    (((denseGeneratorsIdeal p Λ) ^ (n + 1) :
        Ideal (denseGroupAlgebra p Λ)) :
      Set (denseGroupAlgebra p Λ)) ⊆
      (denseGeneratorsSpan p Λ (n + 1) :
        Set (denseGroupAlgebra p Λ)) := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  induction n with
  | zero =>
      intro x hx
      have hxI : x ∈ I := by
        simpa [I, Submodule.pow_one] using hx
      exact
        dense_generators_one
          (p := p) (Λ := Λ) hxI
  | succ n ih =>
      intro x hx
      let Wsucc : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
        denseGeneratorsSpan p Λ (n + 2)
      have hprod_eq : I ^ (n + 2) = I * I ^ (n + 1) := by
        have hpow :
            I ^ (1 + (n + 1)) = I ^ 1 * I ^ (n + 1) :=
          Ideal.IsTwoSided.pow_add (I := I) 1 (n + 1)
        simpa [Submodule.pow_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpow
      have hxprod : x ∈ I * I ^ (n + 1) := by
        simpa [I, hprod_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx
      refine Submodule.mul_induction_on hxprod ?mul ?add
      · intro a ha b hb
        have ha_letter :
            a ∈ denseLetterSpan p Λ :=
          generators_letter_span
            (p := p) (Λ := Λ) ha
        have hb_word :
            b ∈ denseGeneratorsSpan p Λ (n + 1) :=
          ih hb
        exact
          dense_letter_succ
            (p := p) (Λ := Λ) (n := n + 1) ha_letter hb_word
      · intro y z hy hz
        exact Wsucc.add_mem hy hz

lemma dense_algebra_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    {x : denseGroupAlgebra p Λ} :
    x ∈ (denseGeneratorsIdeal p Λ) ^ (n + 1) ↔
      x ∈ denseGeneratorsSpan p Λ (n + 1) := by
  constructor
  · intro hx
    exact
      dense_succ_span
        (p := p) (Λ := Λ) n hx
  · intro hx
    exact
      dense_span_pow
        (p := p) (Λ := Λ) (n + 1) hx

def denseGeneratorsAlgebra
    (p : ℕ) [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω) :
    denseGroupAlgebra p Λ →ₐ[ZMod p]
      denseGroupAlgebra p Ω :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) ψ

@[simp]
lemma generators_algebra_element
    {p : ℕ} [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω)
    (x : Λ) :
    denseGeneratorsAlgebra (p := p) ψ
        (denseGeneratorsElement p Λ x) =
      denseGeneratorsElement p Ω (ψ x) := by
  simp [
    denseGeneratorsAlgebra,
    denseGeneratorsElement
  ]

lemma dense_generators_augmentation
    {p : ℕ} [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω)
    (x : denseGroupAlgebra p Λ) :
    denseGeneratorsAugmentation p Ω
        (denseGeneratorsAlgebra (p := p) ψ x) =
      denseGeneratorsAugmentation p Λ x := by
  refine MonoidAlgebra.induction_linear x ?zero ?add ?single
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro g c
    simp [
      denseGeneratorsAlgebra,
      denseGeneratorsAugmentation,
      MonoidAlgebra.lift_single
    ]

lemma dense_augmentation_ideal
    {p : ℕ} [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω)
    {x : denseGroupAlgebra p Λ}
    (hx : x ∈ denseGeneratorsIdeal p Λ) :
    denseGeneratorsAlgebra (p := p) ψ x ∈
      denseGeneratorsIdeal p Ω := by
  rw [dense_generators_ker] at hx
  rw [dense_generators_ker]
  rw [RingHom.mem_ker] at hx
  rw [RingHom.mem_ker]
  simpa [dense_generators_augmentation, hx]

def dDCongru
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (n : ℕ)
    (x : Λ) : Prop :=
  denseGeneratorsElement p Λ x - 1 ∈
    denseGeneratorsIdeal p Λ ^ n

lemma dense_alg_maps
    {𝕜 : Type v} {R : Type w} {S : Type z}
    [CommSemiring 𝕜] [Semiring R] [Semiring S]
    [Algebra 𝕜 R] [Algebra 𝕜 S]
    (f : R →ₐ[𝕜] S)
    {I : Ideal R} {J : Ideal S}
    (hI : ∀ {x : R}, x ∈ I → f x ∈ J)
    {n : ℕ} {x : R}
    (hx : x ∈ I ^ n) :
    f x ∈ J ^ n := by
  induction n generalizing x with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ n ih =>
      rw [Submodule.pow_succ] at hx
      rw [Submodule.pow_succ]
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Ideal.mul_mem_mul (ih ha) (hI hb)
      · intro y z hy hz
        rw [map_add]
        exact Ideal.add_mem _ hy hz

lemma dense_algebra_pow
    {p : ℕ} [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω)
    {n : ℕ}
    {x : denseGroupAlgebra p Λ}
    (hx : x ∈ denseGeneratorsIdeal p Λ ^ n) :
    denseGeneratorsAlgebra (p := p) ψ x ∈
      denseGeneratorsIdeal p Ω ^ n := by
  exact
    dense_alg_maps
      (denseGeneratorsAlgebra (p := p) ψ)
      (by
        intro x hx
        exact
          dense_augmentation_ideal
            (p := p) ψ hx)
      hx

lemma dDCongru.map
    {p : ℕ} [Fact p.Prime]
    {Λ Ω : Type u} [Group Λ] [Group Ω]
    (ψ : Λ →* Ω)
    {n : ℕ}
    {x : Λ}
    (hx : dDCongru p Λ n x) :
    dDCongru p Ω n (ψ x) := by
  dsimp [dDCongru] at hx ⊢
  have hmapped :
      denseGeneratorsAlgebra (p := p) ψ
          (denseGeneratorsElement p Λ x - 1) ∈
        denseGeneratorsIdeal p Ω ^ n :=
    dense_algebra_pow
      (p := p) ψ hx
  simpa [map_sub] using hmapped

def zassenhausSelfQuotient
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    Type u :=
  Λ ⧸ zassenhausFiltration p Λ n

instance instSelfQuotient
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    Group (zassenhausSelfQuotient p Λ n) := by
  letI : (zassenhausFiltration p Λ n).Normal :=
    zassenhausFiltration_normal p Λ n
  dsimp [zassenhausSelfQuotient]
  infer_instance

def zassenhausSelf
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    Λ →* zassenhausSelfQuotient p Λ n := by
  letI : (zassenhausFiltration p Λ n).Normal :=
    zassenhausFiltration_normal p Λ n
  dsimp [zassenhausSelfQuotient]
  exact QuotientGroup.mk' (zassenhausFiltration p Λ n)

lemma zassenhaus_self_quotient
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ)
    (x : Λ) :
    zassenhausSelf p Λ n x = 1 ↔
      x ∈ zassenhausFiltration p Λ n := by
  letI : (zassenhausFiltration p Λ n).Normal :=
    zassenhausFiltration_normal p Λ n
  dsimp [zassenhausSelf, zassenhausSelfQuotient]
  exact QuotientGroup.eq_one_iff x

lemma dDCongru.map_zass_selfquot
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    {x : Λ}
    (hx : dDCongru p Λ n x) :
    dDCongru p
      (zassenhausSelfQuotient p Λ n) n
      (zassenhausSelf p Λ n x) := by
  exact
      dDCongru.map
        (p := p)
        (Λ := Λ)
        (Ω := zassenhausSelfQuotient p Λ n)
        (zassenhausSelf p Λ n)
      hx

lemma lower_central_surjective
    {G H : Type u} [Group G] [Group H]
    (f : G →* H)
    (hf : Function.Surjective f)
    (i : ℕ) :
    Subgroup.lowerCentralSeries H i ≤
      Subgroup.map f (Subgroup.lowerCentralSeries G i) := by
  induction i with
  | zero =>
      rw [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_zero]
      exact (Subgroup.map_top_of_surjective f hf).ge
  | succ i ih =>
      change
        ⁅Subgroup.lowerCentralSeries H i, (⊤ : Subgroup H)⁆ ≤
          Subgroup.map f ⁅Subgroup.lowerCentralSeries G i, (⊤ : Subgroup G)⁆
      exact
        Subgroup.commutator_le_map_commutator ih
          ((Subgroup.map_top_of_surjective f hf).ge)

lemma set_subset_surjective
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H)
    (hf : Function.Surjective f) :
    zassenhausGeneratorSet p H n ⊆
      (fun y : G => f y) '' zassenhausGeneratorSet p G n := by
  intro y hy
  rcases hy with ⟨i, j, x, hx, hbound, rfl⟩
  have hx_lift :
      x ∈ Subgroup.map f (Subgroup.lowerCentralSeries G i) :=
    lower_central_surjective f hf i hx
  rcases hx_lift with ⟨x₀, hx₀, rfl⟩
  refine ⟨x₀ ^ (p ^ j), ?_, by simp⟩
  exact ⟨i, j, x₀, hx₀, hbound, rfl⟩

lemma image_set_subset
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H) :
    (fun y : G => f y) '' zassenhausGeneratorSet p G n ⊆
      zassenhausGeneratorSet p H n := by
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with ⟨i, j, x, hx, hbound, rfl⟩
  refine ⟨i, j, f x, ?_, hbound, ?_⟩
  · exact Subgroup.lowerCentralSeries.map f i (Subgroup.mem_map_of_mem f hx)
  · simp

lemma image_set_surjective
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H)
    (hf : Function.Surjective f) :
    (fun y : G => f y) '' zassenhausGeneratorSet p G n =
      zassenhausGeneratorSet p H n := by
  apply Set.Subset.antisymm
  · exact image_set_subset p n f
  · exact set_subset_surjective p n f hf

lemma self_subset_singleton
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    zassenhausGeneratorSet p (zassenhausSelfQuotient p Λ n) n ⊆
      ({1} : Set (zassenhausSelfQuotient p Λ n)) := by
  intro y hy
  let q : Λ →* zassenhausSelfQuotient p Λ n :=
    zassenhausSelf p Λ n
  have hq_surjective : Function.Surjective q := by
    letI : (zassenhausFiltration p Λ n).Normal :=
      zassenhausFiltration_normal p Λ n
    dsimp [q, zassenhausSelf, zassenhausSelfQuotient]
    exact QuotientGroup.mk'_surjective (zassenhausFiltration p Λ n)
  have hy_lift :
      y ∈ (fun x : Λ => q x) '' zassenhausGeneratorSet p Λ n :=
    set_subset_surjective
      (p := p) (n := n) q hq_surjective hy
  rcases hy_lift with ⟨x, hx, rfl⟩
  have hx_mem : x ∈ zassenhausFiltration p Λ n := by
    exact Subgroup.subset_closure hx
  change q x = 1
  exact (zassenhaus_self_quotient p Λ n x).mpr hx_mem

lemma filtration_self_bot
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ) :
    zassenhausFiltration p (zassenhausSelfQuotient p Λ n) n = ⊥ := by
  rw [zassenhausFiltration, Subgroup.closure_eq_bot_iff]
  exact self_subset_singleton p Λ n

structure TUBound
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) :
    Type (u + 1) where
  one_trivial_zassenhaus :
    ∀ {Λ : Type u} [Group Λ] [Finite Λ],
      zassenhausFiltration p Λ n = ⊥ →
      ∀ x : Λ,
        dDCongru p Λ n x →
        x = 1

lemma zassenhaus_filtration_succ
    (p : ℕ)
    (G : Type*) [Group G]
    (m : ℕ) :
    zassenhausFiltration p G (m + 1) ≤ zassenhausFiltration p G m := by
  have hindex : m ≤ m + 1 := by
    exact Nat.le_succ m
  have hanti :
      zassenhausFiltration p G (m + 1) ≤ zassenhausFiltration p G m :=
    zassenhausFiltration_antitone p G hindex
  exact hanti

lemma dDCongru.of_le
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m n : ℕ}
    (hmn : m ≤ n)
    {x : Λ}
    (hx : dDCongru p Λ n x) :
    dDCongru p Λ m x := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hle : I ^ n ≤ I ^ m := by
    exact Ideal.pow_le_pow_right hmn
  have hxI :
      denseGeneratorsElement p Λ x - 1 ∈ I ^ n := by
    simpa [I, dDCongru] using hx
  have hxlower :
      denseGeneratorsElement p Λ x - 1 ∈ I ^ m :=
    hle hxI
  simpa [I, dDCongru] using hxlower

@[simp]
lemma dense_canonical_element
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    denseGeneratorsElement p Λ (1 : Λ) =
      (1 : denseGroupAlgebra p Λ) := by
  change
    MonoidAlgebra.single (1 : Λ) (1 : ZMod p) =
      (1 : denseGroupAlgebra p Λ)
  rw [MonoidAlgebra.one_def]

@[simp]
lemma dense_element_mul
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x y : Λ) :
    denseGeneratorsElement p Λ (x * y) =
      denseGeneratorsElement p Λ x *
        denseGeneratorsElement p Λ y := by
  change
    MonoidAlgebra.single (x * y) (1 : ZMod p) =
      MonoidAlgebra.single x (1 : ZMod p) *
        MonoidAlgebra.single y (1 : ZMod p)
  simp [MonoidAlgebra.single_mul_single]

@[simp]
lemma dense_element_pow
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) (k : ℕ) :
    denseGeneratorsElement p Λ (x ^ k) =
      denseGeneratorsElement p Λ x ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      rw [dense_element_mul]
      rw [ih]

def denseGeneratorsUnit
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (x : Λ) :
    Units (denseGroupAlgebra p Λ) where
  val := denseGeneratorsElement p Λ x
  inv := denseGeneratorsElement p Λ x⁻¹
  val_inv := by
    rw [← dense_element_mul]
    simp
  inv_val := by
    rw [← dense_element_mul]
    simp

@[simp]
lemma dense_generators_coe
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    ((denseGeneratorsUnit p Λ x :
        Units (denseGroupAlgebra p Λ)) :
      denseGroupAlgebra p Λ) =
      denseGeneratorsElement p Λ x := by
  rfl

@[simp]
lemma dense_generators_canonical
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x y : Λ) :
    denseGeneratorsUnit p Λ (x * y) =
      denseGeneratorsUnit p Λ x *
        denseGeneratorsUnit p Λ y := by
  ext
  simp [
    denseGeneratorsUnit,
    dense_element_mul
  ]

@[simp]
lemma dense_generators_inv
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsUnit p Λ x⁻¹ =
      (denseGeneratorsUnit p Λ x)⁻¹ := by
  ext
  rfl

def denseGeneratorsSubgroup
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (m : ℕ) : Subgroup Λ where
  carrier :=
    { x |
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsIdeal p Λ ^ m }
  one_mem' := by
    change
      denseGeneratorsElement p Λ (1 : Λ) - 1 ∈
        denseGeneratorsIdeal p Λ ^ m
    rw [dense_canonical_element]
    rw [sub_self]
    exact (denseGeneratorsIdeal p Λ ^ m).zero_mem
  mul_mem' := by
    intro x y hx hy
    let I : Ideal (denseGroupAlgebra p Λ) :=
      denseGeneratorsIdeal p Λ
    have hmul :
        denseGeneratorsElement p Λ (x * y) - 1 =
          denseGeneratorsElement p Λ x *
              (denseGeneratorsElement p Λ y - 1) +
            (denseGeneratorsElement p Λ x - 1) := by
      rw [dense_element_mul]
      noncomm_ring
    change
      denseGeneratorsElement p Λ (x * y) - 1 ∈ I ^ m
    rw [hmul]
    exact
      (I ^ m).add_mem
        ((I ^ m).mul_mem_left
          (denseGeneratorsElement p Λ x) hy)
        hx
  inv_mem' := by
    intro x hx
    let I : Ideal (denseGroupAlgebra p Λ) :=
      denseGeneratorsIdeal p Λ
    have hleft_inverse :
        denseGeneratorsElement p Λ x⁻¹ *
            denseGeneratorsElement p Λ x =
          (1 : denseGroupAlgebra p Λ) := by
      rw [← dense_element_mul]
      simp
    have hinv :
        denseGeneratorsElement p Λ x⁻¹ - 1 =
          -((denseGeneratorsElement p Λ x⁻¹) *
            (denseGeneratorsElement p Λ x - 1)) := by
      noncomm_ring [hleft_inverse]
    change
      denseGeneratorsElement p Λ x⁻¹ - 1 ∈ I ^ m
    rw [hinv]
    exact
      (I ^ m).neg_mem
        ((I ^ m).mul_mem_left
          (denseGeneratorsElement p Λ x⁻¹) hx)

lemma dense_generators_subgroup
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (m : ℕ)
    (x : Λ) :
    x ∈ denseGeneratorsSubgroup p Λ m ↔
      dDCongru p Λ m x := by
  rfl

lemma dense_generators_top
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    denseGeneratorsSubgroup p Λ 0 = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Subgroup.mem_top x
  · intro _hx
    change
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsIdeal p Λ ^ 0
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

lemma dense_dimension_congruence
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    dDCongru p Λ 1 x := by
  change
    denseGeneratorsElement p Λ x - 1 ∈
      denseGeneratorsIdeal p Λ ^ 1
  rw [Submodule.pow_one]
  exact
    dense_element_ideal
      (p := p) (Λ := Λ) x

lemma dense_algebra_top
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    denseGeneratorsSubgroup p Λ 1 = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Subgroup.mem_top x
  · intro _hx
    exact dense_dimension_congruence
      (p := p) (Λ := Λ) x

lemma dense_algebra_sub
    {R : Type u} [Ring R]
    (u v : Units R) :
    ((u * v * u⁻¹ * v⁻¹ : Units R) : R) - 1 =
      ((((u : R) - 1) * ((v : R) - 1) -
          (((v : R) - 1) * ((u : R) - 1))) *
        ((u⁻¹ : Units R) : R)) * ((v⁻¹ : Units R) : R) := by
  simp only [Units.val_mul]
  noncomm_ring [Units.mul_inv, Units.inv_mul]

lemma dense_sub_add
    {R : Type u} [Ring R]
    (I : Ideal R)
    [I.IsTwoSided]
    {m n : ℕ}
    {u v : Units R}
    (hu : (u : R) - 1 ∈ I ^ m)
    (hv : (v : R) - 1 ∈ I ^ n) :
    ((u * v * u⁻¹ * v⁻¹ : Units R) : R) - 1 ∈ I ^ (m + n) := by
  have hleft :
      ((u : R) - 1) * ((v : R) - 1) ∈ I ^ (m + n) := by
    rw [Ideal.IsTwoSided.pow_add (I := I) m n]
    exact Ideal.mul_mem_mul hu hv
  have hright :
      ((v : R) - 1) * ((u : R) - 1) ∈ I ^ (m + n) := by
    have hright' :
        ((v : R) - 1) * ((u : R) - 1) ∈ I ^ (n + m) := by
      rw [Ideal.IsTwoSided.pow_add (I := I) n m]
      exact Ideal.mul_mem_mul hv hu
    simpa [Nat.add_comm] using hright'
  have hdiff :
      ((u : R) - 1) * ((v : R) - 1) -
          (((v : R) - 1) * ((u : R) - 1)) ∈ I ^ (m + n) :=
    (I ^ (m + n)).sub_mem hleft hright
  rw [dense_algebra_sub]
  exact
    (I ^ (m + n)).mul_mem_right ((v⁻¹ : Units R) : R)
      ((I ^ (m + n)).mul_mem_right ((u⁻¹ : Units R) : R) hdiff)

lemma dense_generators_add
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m n : ℕ}
    {x y : Λ}
    (hx : dDCongru p Λ m x)
    (hy : dDCongru p Λ n y) :
    dDCongru p Λ (m + n)
      (x * y * x⁻¹ * y⁻¹) := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  let u : Units (denseGroupAlgebra p Λ) :=
    denseGeneratorsUnit p Λ x
  let v : Units (denseGroupAlgebra p Λ) :=
    denseGeneratorsUnit p Λ y
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  have hu : (u : denseGroupAlgebra p Λ) - 1 ∈ I ^ m := by
    simpa [u, I, dDCongru] using hx
  have hv : (v : denseGroupAlgebra p Λ) - 1 ∈ I ^ n := by
    simpa [v, I, dDCongru] using hy
  have hunit :
      ((u * v * u⁻¹ * v⁻¹ : Units (denseGroupAlgebra p Λ)) :
          denseGroupAlgebra p Λ) - 1 ∈ I ^ (m + n) :=
    dense_sub_add
      (I := I) (m := m) (n := n) (u := u) (v := v) hu hv
  change
    denseGeneratorsElement p Λ (x * y * x⁻¹ * y⁻¹) - 1 ∈
      I ^ (m + n)
  simpa [
    u,
    v,
    denseGeneratorsUnit,
    dense_element_mul,
    mul_assoc
  ] using hunit

lemma dense_generators_pow
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {i : ℕ}
    {x : Λ}
    (hx : x ∈ Subgroup.lowerCentralSeries Λ i) :
    dDCongru p Λ (i + 1) x := by
  induction i generalizing x with
  | zero =>
      exact dense_dimension_congruence
        (p := p) (Λ := Λ) x
  | succ i ih =>
      rw [Subgroup.lowerCentralSeries_succ] at hx
      let P : Subgroup Λ :=
        denseGeneratorsSubgroup p Λ (i + 2)
      have hclosure :
          Subgroup.closure
              { g : Λ | ∃ a ∈ Subgroup.lowerCentralSeries Λ i,
                  ∃ b ∈ (⊤ : Subgroup Λ), a * b * a⁻¹ * b⁻¹ = g } ≤ P := by
        rw [Subgroup.closure_le]
        rintro g ⟨a, ha, b, _hb, rfl⟩
        have haI :
            dDCongru p Λ (i + 1) a :=
          ih ha
        have hbI :
            dDCongru p Λ 1 b :=
          dense_dimension_congruence
            (p := p) (Λ := Λ) b
        have hcomm :
            dDCongru p Λ ((i + 1) + 1)
              (a * b * a⁻¹ * b⁻¹) :=
          dense_generators_add
            (p := p) (Λ := Λ) (m := i + 1) (n := 1) haI hbI
        change
          dDCongru p Λ (i + 2)
            (a * b * a⁻¹ * b⁻¹)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomm
      exact hclosure hx

lemma dense_generators_mul
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m k : ℕ}
    {a : denseGroupAlgebra p Λ}
    (ha : a ∈ denseGeneratorsIdeal p Λ ^ m) :
    a ^ k ∈ denseGeneratorsIdeal p Λ ^ (m * k) := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  have haI : a ∈ I ^ m := by
    simpa [I] using ha
  have hpowers : (I ^ m) ^ k = I ^ (m * k) := by
    induction k with
    | zero =>
        rw [mul_zero, Submodule.pow_zero, Submodule.pow_zero]
    | succ k ih =>
        calc
          (I ^ m) ^ (k + 1) = (I ^ m) ^ k * I ^ m := by
            rw [Ideal.IsTwoSided.pow_add, Submodule.pow_one]
          _ = I ^ (m * k) * I ^ m := by
            rw [ih]
          _ = I ^ (m * k + m) := by
            exact (Ideal.IsTwoSided.pow_add (I := I) (m * k) m).symm
          _ = I ^ (m * (k + 1)) := by
            rw [Nat.mul_succ]
  have hpow : a ^ k ∈ (I ^ m) ^ k :=
    Ideal.pow_mem_pow haI k
  simpa [I, hpowers] using hpow

lemma generators_char_p
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] :
    CharP (denseGroupAlgebra p Λ) p := by
  exact
    charP_of_injective_algebraMap'
      (R := ZMod p) (A := denseGroupAlgebra p Λ) p

lemma dense_char_p
    {R : Type u} [Ring R]
    {p j : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) :
    a ^ (p ^ j) - 1 = (a - 1) ^ (p ^ j) := by
  have hsub :
      (a - 1) ^ (p ^ j) = a ^ (p ^ j) - (1 : R) ^ (p ^ j) := by
    simpa only [one_pow] using
      (sub_pow_char_pow_of_commute (R := R) (p := p) (n := j)
        (x := a) (y := 1) (Commute.one_right a))
  calc
    a ^ (p ^ j) - 1 = a ^ (p ^ j) - (1 : R) ^ (p ^ j) := by
      rw [one_pow]
    _ = (a - 1) ^ (p ^ j) := hsub.symm

lemma dense_generators_element
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {j : ℕ}
    {x : Λ} :
    denseGeneratorsElement p Λ (x ^ (p ^ j)) - 1 =
      (denseGeneratorsElement p Λ x - 1) ^ (p ^ j) := by
  letI : CharP (denseGroupAlgebra p Λ) p :=
    generators_char_p (p := p) (Λ := Λ)
  have hcanonical :
      denseGeneratorsElement p Λ (x ^ (p ^ j)) =
        denseGeneratorsElement p Λ x ^ (p ^ j) := by
    simp
  calc
    denseGeneratorsElement p Λ (x ^ (p ^ j)) - 1 =
        denseGeneratorsElement p Λ x ^ (p ^ j) - 1 := by
      rw [hcanonical]
    _ = (denseGeneratorsElement p Λ x - 1) ^ (p ^ j) :=
      dense_char_p
        (p := p) (j := j)
        (denseGeneratorsElement p Λ x)

lemma dDCongru.pow_prime_power
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {r j : ℕ}
    {x : Λ}
    (hx : dDCongru p Λ r x) :
    dDCongru p Λ (r * p ^ j) (x ^ (p ^ j)) := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hxI :
      denseGeneratorsElement p Λ x - 1 ∈ I ^ r := by
    simpa [I, dDCongru] using hx
  have hpow :
      (denseGeneratorsElement p Λ x - 1) ^ (p ^ j) ∈
        I ^ (r * p ^ j) :=
    dense_generators_mul
      (p := p) (Λ := Λ) (m := r) (k := p ^ j) hxI
  have hidentity :
      denseGeneratorsElement p Λ (x ^ (p ^ j)) - 1 =
        (denseGeneratorsElement p Λ x - 1) ^ (p ^ j) :=
    dense_generators_element
      (p := p) (Λ := Λ) (j := j) (x := x)
  change
    denseGeneratorsElement p Λ (x ^ (p ^ j)) - 1 ∈
      I ^ (r * p ^ j)
  rw [hidentity]
  exact hpow

lemma dense_congruence_generator
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    {g : Λ}
    (hg : g ∈ zassenhausGeneratorSet p Λ n) :
    dDCongru p Λ n g := by
  rcases hg with ⟨i, j, x, hx_lower, hbound, rfl⟩
  have hx_congruence :
      dDCongru p Λ (i + 1) x :=
    dense_generators_pow
      (p := p) (Λ := Λ) hx_lower
  have hx_power_congruence :
      dDCongru p Λ ((i + 1) * p ^ j)
        (x ^ (p ^ j)) :=
    dDCongru.pow_prime_power
      (p := p) (Λ := Λ) (r := i + 1) (j := j) hx_congruence
  exact
    dDCongru.of_le
      (p := p) (Λ := Λ) hbound hx_power_congruence

lemma filtration_dense_generators
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (n : ℕ) :
    zassenhausFiltration p Λ n ≤
      denseGeneratorsSubgroup p Λ n := by
  rw [zassenhausFiltration]
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  exact
    (dense_generators_subgroup
      (p := p) (Λ := Λ) n g).2
      (dense_congruence_generator
        (p := p) (Λ := Λ) hg)

lemma filtration_drop_bot
    (p : ℕ)
    (G : Type*) [Group G]
    {n : ℕ}
    (_hn : 1 < n)
    (hbot : zassenhausFiltration p G n = ⊥)
    {x : G}
    (hxne : x ≠ 1) :
    ∃ m : ℕ,
      m < n ∧
        x ∈ zassenhausFiltration p G m ∧
          x ∉ zassenhausFiltration p G (m + 1) := by
  classical
  have hxmem0 : x ∈ zassenhausFiltration p G 0 := by
    rw [filtration_zero_top]
    exact Subgroup.mem_top x
  have hxnotn : x ∉ zassenhausFiltration p G n := by
    intro hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hx
    exact hxne (Subgroup.mem_bot.mp hxbot)
  let P : ℕ → Prop := fun k => x ∉ zassenhausFiltration p G k
  have hP : ∃ k : ℕ, P k := ⟨n, hxnotn⟩
  let k : ℕ := Nat.find hP
  have hknot : P k := Nat.find_spec hP
  have hkpos : 0 < k := by
    have hnotP0 : ¬ P 0 := by
      intro h
      exact h hxmem0
    exact (Nat.find_pos hP).2 hnotP0
  have hkle : k ≤ n := Nat.find_min' hP hxnotn
  have hpred_lt : k - 1 < k := Nat.pred_lt (Nat.ne_of_gt hkpos)
  have hpred_mem : x ∈ zassenhausFiltration p G (k - 1) := by
    have hnotPpred : ¬ P (k - 1) := Nat.find_min hP hpred_lt
    exact not_not.mp hnotPpred
  refine ⟨k - 1, ?_, hpred_mem, ?_⟩
  · omega
  · have hpred_succ : k - 1 + 1 = k := by
      omega
    simpa [P, hpred_succ] using hknot

lemma dense_generators_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (n : ℕ)
    (x : Λ) :
    x ∈ denseGeneratorsSubgroup p Λ (n + 1) ↔
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsSpan p Λ (n + 1) := by
  have hcongruence :
      x ∈ denseGeneratorsSubgroup p Λ (n + 1) ↔
        dDCongru p Λ (n + 1) x :=
    dense_generators_subgroup
      (p := p) (Λ := Λ) (n + 1) x
  have hpower :
      dDCongru p Λ (n + 1) x ↔
        denseGeneratorsElement p Λ x - 1 ∈
          denseGeneratorsSpan p Λ (n + 1) := by
    change
      denseGeneratorsElement p Λ x - 1 ∈
          (denseGeneratorsIdeal p Λ) ^ (n + 1) ↔
        denseGeneratorsElement p Λ x - 1 ∈
          denseGeneratorsSpan p Λ (n + 1)
    exact
      dense_algebra_span
        (p := p) (Λ := Λ) (n := n)
        (x := denseGeneratorsElement p Λ x - 1)
  exact hcongruence.trans hpower

lemma dense_sub_span
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    (hm : 0 < m)
    {x : Λ}
    (hxmem : x ∈ zassenhausFiltration p Λ m) :
    denseGeneratorsElement p Λ x - 1 ∈
      denseGeneratorsSpan p Λ m := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨n, rfl⟩
  have hle :
      zassenhausFiltration p Λ (n + 1) ≤
        denseGeneratorsSubgroup p Λ (n + 1) :=
    filtration_dense_generators
      (p := p) (Λ := Λ) (n + 1)
  have hxpower :
      x ∈ denseGeneratorsSubgroup p Λ (n + 1) :=
    hle hxmem
  exact
    (dense_generators_span
      (p := p) (Λ := Λ) n x).1 hxpower

lemma dense_generators_left
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {n : ℕ}
    (a : denseGroupAlgebra p Λ)
    {z : denseGroupAlgebra p Λ}
    (hz : z ∈ denseGeneratorsSpan p Λ (n + 1)) :
    a * z ∈ denseGeneratorsSpan p Λ (n + 1) := by
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hzI : z ∈ I ^ (n + 1) := by
    exact
      (dense_algebra_span
        (p := p) (Λ := Λ) (n := n) (x := z)).2 hz
  have hmulI : a * z ∈ I ^ (n + 1) :=
    (I ^ (n + 1)).mul_mem_left a hzI
  exact
    (dense_algebra_span
      (p := p) (Λ := Λ) (n := n) (x := a * z)).1 hmulI

lemma dense_element_sub
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x y : Λ) :
    denseGeneratorsElement p Λ (x * y) - 1 =
      denseGeneratorsElement p Λ x *
          (denseGeneratorsElement p Λ y - 1) +
        (denseGeneratorsElement p Λ x - 1) := by
  rw [dense_element_mul]
  noncomm_ring

lemma dense_element_inv
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (x : Λ) :
    denseGeneratorsElement p Λ x⁻¹ - 1 =
      -((denseGeneratorsElement p Λ x⁻¹) *
        (denseGeneratorsElement p Λ x - 1)) := by
  have hleft_inverse :
      denseGeneratorsElement p Λ x⁻¹ *
          denseGeneratorsElement p Λ x =
        (1 : denseGroupAlgebra p Λ) := by
    rw [← dense_element_mul]
    simp
  noncomm_ring [hleft_inverse]

def dGKern
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (m : ℕ) :
    Subgroup Λ :=
  zassenhausFiltration p Λ m ⊓
    denseGeneratorsSubgroup p Λ (m + 1)

lemma dense_algebra_kernel
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ} :
    x ∈ dGKern p Λ m ↔
      x ∈ zassenhausFiltration p Λ m ∧
        x ∈ denseGeneratorsSubgroup p Λ (m + 1) := by
  rfl

lemma dense_generators_kernel
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (m : ℕ) :
    dGKern p Λ m ≤
      zassenhausFiltration p Λ m := by
  intro x hx
  exact
    (dense_algebra_kernel
      (p := p) (Λ := Λ) (m := m) (x := x)).1 hx |>.1

lemma dense_generators_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    (m : ℕ) :
    dGKern p Λ m ≤
      denseGeneratorsSubgroup p Λ (m + 1) := by
  intro x hx
  exact
    (dense_algebra_kernel
      (p := p) (Λ := Λ) (m := m) (x := x)).1 hx |>.2

lemma filtration_map_le
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H) :
    Subgroup.map f (zassenhausFiltration p G n) ≤
      zassenhausFiltration p H n := by
  rw [zassenhausFiltration, zassenhausFiltration, MonoidHom.map_closure]
  exact Subgroup.closure_mono (image_set_subset p n f)

lemma filtration_map_mem
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H)
    {x : G}
    (hx : x ∈ zassenhausFiltration p G n) :
    f x ∈ zassenhausFiltration p H n := by
  have hxmap :
      f x ∈ Subgroup.map f (zassenhausFiltration p G n) :=
    Subgroup.mem_map_of_mem f hx
  exact filtration_map_le p n f hxmap

lemma zassenhaus_self_filtration
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (m n : ℕ)
    {x : Λ}
    (hx : x ∈ zassenhausFiltration p Λ m) :
    zassenhausSelf p Λ n x ∈
      zassenhausFiltration p (zassenhausSelfQuotient p Λ n) m := by
  exact
    filtration_map_mem
      (p := p)
      (n := m)
      (f := zassenhausSelf p Λ n)
      hx

lemma zassenhaus_self_not
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (n : ℕ)
    {x : Λ}
    (hxnot : x ∉ zassenhausFiltration p Λ n) :
    zassenhausSelf p Λ n x ≠ 1 := by
  intro hxone
  exact hxnot
    ((zassenhaus_self_quotient p Λ n x).mp hxone)

lemma dDCongru.subone_memword_spansucc
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hx : dDCongru p Λ (m + 1) x) :
    denseGeneratorsElement p Λ x - 1 ∈
      denseGeneratorsSpan p Λ (m + 1) := by
  have hxI :
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsIdeal p Λ ^ (m + 1) := by
    simpa [dDCongru] using hx
  exact
    (dense_algebra_span
      (p := p)
      (Λ := Λ)
      (n := m)
      (x := denseGeneratorsElement p Λ x - 1)).1 hxI

lemma
  dense_generators_core
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] [Finite Λ]
    {x : Λ}
    (_hxmem : x ∈ zassenhausFiltration p Λ 0)
    (_hxword :
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsSpan p Λ (0 + 1)) :
    x ∈ zassenhausFiltration p Λ (0 + 1) := by
  rw [filtration_one_top]
  exact Subgroup.mem_top x

structure DSFunc
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (m : ℕ)
    (x : Λ) :
    Type (u + 1) where
  linearFunctional :
    denseGroupAlgebra p Λ →ₗ[ZMod p] ZMod p
  annihilates_span_succ :
    ∀ {z : denseGroupAlgebra p Λ},
      z ∈ denseGeneratorsSpan p Λ (m + 1) →
        linearFunctional z = 0
  detects_sub_one :
    linearFunctional (denseGeneratorsElement p Λ x - 1) ≠ 0

namespace DSFunc

lemma linear_functional
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (f : denseGroupAlgebra p Λ →ₗ[ZMod p] ZMod p)
    (hfW :
      ∀ {z : denseGroupAlgebra p Λ},
        z ∈ denseGeneratorsSpan p Λ (m + 1) →
          f z = 0)
    (hfx :
      f (denseGeneratorsElement p Λ x - 1) ≠ 0) :
    Nonempty
      (DSFunc
        (p := p) Λ m x) := by
  refine
    ⟨{ linearFunctional := f
       annihilates_span_succ := ?_
       detects_sub_one := ?_ }⟩
  · intro z hz
    exact hfW hz
  · exact hfx

lemma sub_span_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (Φ :
      DSFunc
        (p := p) Λ m x) :
    denseGeneratorsElement p Λ x - 1 ∉
      denseGeneratorsSpan p Λ (m + 1) := by
  intro hxword
  have hzero :
      Φ.linearFunctional
          (denseGeneratorsElement p Λ x - 1) = 0 :=
    Φ.annihilates_span_succ hxword
  exact Φ.detects_sub_one hzero

lemma false_sub_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (Φ :
      DSFunc
        (p := p) Λ m x)
    (hxword :
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsSpan p Λ (m + 1)) :
    False := by
  have hxnot :
      denseGeneratorsElement p Λ x - 1 ∉
        denseGeneratorsSpan p Λ (m + 1) :=
    Φ.sub_span_succ
  exact hxnot hxword

end DSFunc

lemma mk_q_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hxnotword :
      denseGeneratorsElement p Λ x - 1 ∉
        denseGeneratorsSpan p Λ (m + 1)) :
    (denseGeneratorsSpan p Λ (m + 1)).mkQ
        (denseGeneratorsElement p Λ x - 1) ≠ 0 := by
  intro hzero
  apply hxnotword
  have hmk :
      Submodule.Quotient.mk
          (denseGeneratorsElement p Λ x - 1) =
        (0 :
          denseGroupAlgebra p Λ ⧸
            denseGeneratorsSpan p Λ (m + 1)) := by
    simpa [Submodule.mkQ_apply] using hzero
  exact
    (Submodule.Quotient.mk_eq_zero
      (p := denseGeneratorsSpan p Λ (m + 1))
      (x := denseGeneratorsElement p Λ x - 1)).1 hmk

lemma dense_functional_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hxnotword :
      denseGeneratorsElement p Λ x - 1 ∉
        denseGeneratorsSpan p Λ (m + 1)) :
    ∃ f : denseGroupAlgebra p Λ →ₗ[ZMod p] ZMod p,
      (∀ {z : denseGroupAlgebra p Λ},
        z ∈ denseGeneratorsSpan p Λ (m + 1) →
          f z = 0) ∧
      f (denseGeneratorsElement p Λ x - 1) ≠ 0 := by
  classical
  let W : Submodule (ZMod p) (denseGroupAlgebra p Λ) :=
    denseGeneratorsSpan p Λ (m + 1)
  let y : denseGroupAlgebra p Λ :=
    denseGeneratorsElement p Λ x - 1
  let q : denseGroupAlgebra p Λ ⧸ W :=
    W.mkQ y
  have hq : q ≠ 0 := by
    dsimp [q, W, y]
    exact
      mk_q_succ
        (p := p) (Λ := Λ) (m := m) (x := x) hxnotword
  obtain ⟨⟨ι, b⟩⟩ :=
    Module.Free.exists_basis
      (R := ZMod p)
      (M := denseGroupAlgebra p Λ ⧸ W)
  have hcoord_exists : ∃ i : ι, b.coord i q ≠ 0 := by
    by_contra hnone
    apply hq
    have hall : ∀ i : ι, b.coord i q = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact (b.forall_coord_eq_zero_iff).mp hall
  rcases hcoord_exists with ⟨i, hi⟩
  let f : denseGroupAlgebra p Λ →ₗ[ZMod p] ZMod p :=
    (b.coord i).comp W.mkQ
  refine ⟨f, ?_, ?_⟩
  · intro z hz
    have hzq : W.mkQ z = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero (p := W) (x := z)).2 hz
    simp [f, hzq]
  · simpa [f, q, y] using hi

lemma gens_fin_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hxnotword :
      denseGeneratorsElement p Λ x - 1 ∉
        denseGeneratorsSpan p Λ (m + 1)) :
    Nonempty
      (DSFunc
        (p := p) Λ m x) := by
  rcases
      dense_functional_succ
        (p := p) (Λ := Λ) (m := m) (x := x) hxnotword with
    ⟨f, hfW, hfx⟩
  exact
    DSFunc.linear_functional
      (p := p) (Λ := Λ) (m := m) (x := x) f hfW hfx

lemma dense_generators_pos
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    (hm : 0 < m) :
    denseGeneratorsSpan p Λ (m + 1) ≤
      denseGeneratorsSpan p Λ m := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨n, rfl⟩
  intro z hz
  let I : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hzI_succ : z ∈ I ^ ((n + 1) + 1) := by
    exact
      (dense_algebra_span
        (p := p) (Λ := Λ) (n := n + 1) (x := z)).2 hz
  have hle : n + 1 ≤ (n + 1) + 1 := Nat.le_succ (n + 1)
  have hzI : z ∈ I ^ (n + 1) := by
    exact Ideal.pow_le_pow_right hle hzI_succ
  exact
    (dense_algebra_span
      (p := p) (Λ := Λ) (n := n) (x := z)).1 hzI

abbrev denseGeneratorsPositive
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (m : ℕ) :
    Type u :=
  (denseGeneratorsSpan p Λ m) ⧸
    (Submodule.comap
      (denseGeneratorsSpan p Λ m).subtype
      (denseGeneratorsSpan p Λ (m + 1)))

structure DDBound
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (m : ℕ) :
    Type (u + 1) where
  augmentation_kernel_succ :
    dGKern p Λ m ≤
      zassenhausFiltration p Λ (m + 1)

namespace DDBound

lemma mem_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    (H :
      DDBound
        (p := p) Λ m)
    {x : Λ}
    (hx : x ∈ dGKern p Λ m) :
    x ∈ zassenhausFiltration p Λ (m + 1) := by
  have hle :
      dGKern p Λ m ≤
        zassenhausFiltration p Λ (m + 1) :=
    H.augmentation_kernel_succ
  exact hle hx

end DDBound

lemma dGKern.dimensionCongruence
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hx : x ∈ dGKern p Λ m) :
    dDCongru p Λ (m + 1) x := by
  have hxpair :
      x ∈ zassenhausFiltration p Λ m ∧
        x ∈ denseGeneratorsSubgroup p Λ (m + 1) :=
    (dense_algebra_kernel
      (p := p) (Λ := Λ) (m := m) (x := x)).1 hx
  exact
    (dense_generators_subgroup
      (p := p) (Λ := Λ) (m + 1) x).1 hxpair.2

lemma dGKern.map_selfquot_memzass
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hx : x ∈ dGKern p Λ m) :
    zassenhausSelf p Λ (m + 1) x ∈
      zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) m := by
  have hxpair :
      x ∈ zassenhausFiltration p Λ m ∧
        x ∈ denseGeneratorsSubgroup p Λ (m + 1) :=
    (dense_algebra_kernel
      (p := p) (Λ := Λ) (m := m) (x := x)).1 hx
  exact
    zassenhaus_self_filtration
      (p := p)
      (Λ := Λ)
      (m := m)
      (n := m + 1)
      hxpair.1

lemma dGKern.map_selfquot_dimcongruence
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ}
    (hx : x ∈ dGKern p Λ m) :
    dDCongru p
      (zassenhausSelfQuotient p Λ (m + 1)) (m + 1)
      (zassenhausSelf p Λ (m + 1) x) := by
  have hxcongruence :
      dDCongru p Λ (m + 1) x :=
    dGKern.dimensionCongruence
      (p := p) (Λ := Λ) (m := m) hx
  exact
    dDCongru.map_zass_selfquot
      (p := p) hxcongruence

lemma zassenhaus_self_succ
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (m : ℕ)
    {y : zassenhausSelfQuotient p Λ (m + 1)}
    (hy : y ∈ zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1)) :
    y = 1 := by
  have hbot :
      zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) = ⊥ :=
    filtration_self_bot p Λ (m + 1)
  have hybot : y ∈ (⊥ : Subgroup (zassenhausSelfQuotient p Λ (m + 1))) := by
    simpa [hbot] using hy
  exact Subgroup.mem_bot.mp hybot

lemma
    dense_self_congruence
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {y : zassenhausSelfQuotient p Λ (m + 1)}
    (hycongruence :
      dDCongru p
        (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) y) :
    denseGeneratorsElement p
        (zassenhausSelfQuotient p Λ (m + 1)) y - 1 ∈
      denseGeneratorsSpan p
        (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) := by
  exact
    dDCongru.subone_memword_spansucc
      (p := p)
      (Λ := zassenhausSelfQuotient p Λ (m + 1))
      (m := m)
      (x := y)
      hycongruence

lemma zassenhaus_self_commutator
    {p : ℕ} [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (a b : zassenhausSelfQuotient p Λ (1 + 1)) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  let Ω : Type u := zassenhausSelfQuotient p Λ (1 + 1)
  let c : Ω := a * b * a⁻¹ * b⁻¹
  have hc_lower : c ∈ Subgroup.lowerCentralSeries Ω 1 := by
    rw [Subgroup.lowerCentralSeries_succ]
    refine Subgroup.subset_closure ?_
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [Subgroup.lowerCentralSeries_zero]
      exact Subgroup.mem_top a
    · exact Subgroup.mem_top b
    · rfl
  have hc_generator : c ∈ zassenhausGeneratorSet p Ω (1 + 1) := by
    refine ⟨1, 0, c, hc_lower, ?_, ?_⟩
    · norm_num
    · simp [c]
  have hc_filtration : c ∈ zassenhausFiltration p Ω (1 + 1) :=
    Subgroup.subset_closure hc_generator
  have hbot : zassenhausFiltration p Ω (1 + 1) = ⊥ := by
    simpa [Ω] using filtration_self_bot p Λ (1 + 1)
  have hc_bot : c ∈ (⊥ : Subgroup Ω) := by
    rw [hbot] at hc_filtration
    exact hc_filtration
  exact Subgroup.mem_bot.mp hc_bot

lemma zassenhaus_self_one
    {p : ℕ} [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    (a : zassenhausSelfQuotient p Λ (1 + 1)) :
    a ^ p = 1 := by
  let Ω : Type u := zassenhausSelfQuotient p Λ (1 + 1)
  have ha_lower : a ∈ Subgroup.lowerCentralSeries Ω 0 := by
    rw [Subgroup.lowerCentralSeries_zero]
    exact Subgroup.mem_top a
  have hp_two : 2 ≤ p := by
    exact (Fact.out : Nat.Prime p).two_le
  have ha_generator : a ^ p ∈ zassenhausGeneratorSet p Ω (1 + 1) := by
    refine ⟨0, 1, a, ha_lower, ?_, ?_⟩
    · simpa [pow_one] using hp_two
    · simp
  have ha_filtration : a ^ p ∈ zassenhausFiltration p Ω (1 + 1) :=
    Subgroup.subset_closure ha_generator
  have hbot : zassenhausFiltration p Ω (1 + 1) = ⊥ := by
    simpa [Ω] using filtration_self_bot p Λ (1 + 1)
  have ha_bot : a ^ p ∈ (⊥ : Subgroup Ω) := by
    rw [hbot] at ha_filtration
    exact ha_filtration
  exact Subgroup.mem_bot.mp ha_bot

lemma self_not_ne
    {p : ℕ} [Fact p.Prime]
    (Λ : Type u) [Group Λ]
    {a : zassenhausSelfQuotient p Λ (1 + 1)} :
    a ∉ zassenhausFiltration p (zassenhausSelfQuotient p Λ (1 + 1)) (1 + 1) ↔
      a ≠ 1 := by
  let Ω : Type u := zassenhausSelfQuotient p Λ (1 + 1)
  have hbot : zassenhausFiltration p Ω (1 + 1) = ⊥ := by
    simpa [Ω] using filtration_self_bot p Λ (1 + 1)
  constructor
  · intro ha_not ha_one
    apply ha_not
    rw [ha_one]
    exact (zassenhausFiltration p Ω (1 + 1)).one_mem
  · intro ha_ne ha_mem
    have ha_bot : a ∈ (⊥ : Subgroup Ω) := by
      simpa [Ω, hbot] using ha_mem
    exact ha_ne (Subgroup.mem_bot.mp ha_bot)

structure DACharac
    (p : ℕ) [Fact p.Prime]
    (E : Type u) [Group E]
    (y : E) :
    Type u where
  toFun : E → ZMod p
  map_one : toFun 1 = 0
  map_mul : ∀ a b : E, toFun (a * b) = toFun a + toFun b
  detects : toFun y ≠ 0

namespace DACharac

noncomputable def linearFunctional
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    denseGroupAlgebra p E →ₗ[ZMod p] ZMod p :=
  Finsupp.linearCombination (ZMod p) χ.toFun

lemma linearFunctional_single
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (g : E)
    (c : ZMod p) :
    χ.linearFunctional
        (MonoidAlgebra.single g c : denseGroupAlgebra p E) =
      c * χ.toFun g := by
  change
    Finsupp.sum (MonoidAlgebra.single g c)
        (fun i d => d * χ.toFun i) =
      c * χ.toFun g
  rw [Finsupp.sum_single_index (by simp)]

lemma functional_canonical_element
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (g : E) :
    χ.linearFunctional (denseGeneratorsElement p E g) =
      χ.toFun g := by
  simpa [denseGeneratorsElement] using
    χ.linearFunctional_single g (1 : ZMod p)

lemma linearFunctional_one
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    χ.linearFunctional (1 : denseGroupAlgebra p E) = 0 := by
  rw [MonoidAlgebra.one_def]
  simp [χ.linearFunctional_single, χ.map_one]

lemma linear_functional_element
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (g : E) :
    χ.linearFunctional (denseGeneratorsElement p E g - 1) =
      χ.toFun g := by
  calc
    χ.linearFunctional (denseGeneratorsElement p E g - 1) =
        χ.linearFunctional (denseGeneratorsElement p E g) -
          χ.linearFunctional (1 : denseGroupAlgebra p E) := by
            exact LinearMap.map_sub χ.linearFunctional _ _
    _ = χ.toFun g := by
      rw [χ.functional_canonical_element, χ.linearFunctional_one, sub_zero]

lemma linear_functional_letter
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (a b : E) :
    χ.linearFunctional
        ((denseGeneratorsElement p E a - 1) *
          (denseGeneratorsElement p E b - 1)) =
      0 := by
  let A : denseGroupAlgebra p E :=
    denseGeneratorsElement p E a
  let B : denseGroupAlgebra p E :=
    denseGeneratorsElement p E b
  have hword :
      (A - 1) * (B - 1) =
        denseGeneratorsElement p E (a * b) -
          denseGeneratorsElement p E a -
            denseGeneratorsElement p E b +
              (1 : denseGroupAlgebra p E) := by
    simp [
      A,
      B,
      denseGeneratorsElement,
      sub_mul,
      mul_sub,
      MonoidAlgebra.single_mul_single
    ]
    abel
  change χ.linearFunctional ((A - 1) * (B - 1)) = 0
  rw [hword]
  rw [map_add, map_sub, map_sub]
  rw [
    χ.functional_canonical_element,
    χ.functional_canonical_element,
    χ.functional_canonical_element,
    χ.linearFunctional_one,
    χ.map_mul a b
  ]
  abel

lemma linear_functional_generator
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (w : List.Vector E (1 + 1)) :
    χ.linearFunctional
        (denseGeneratorsGenerator p E w) =
      0 := by
  cases w using List.Vector.casesOn with
  | cons a t =>
      cases t using List.Vector.casesOn with
      | cons b u =>
          cases u using List.Vector.casesOn with
          | nil =>
              simpa [
                denseGeneratorsGenerator,
                List.Vector.toList_cons,
                List.Vector.toList_nil
              ] using χ.linear_functional_letter a b

lemma linear_functional_two
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    {z : denseGroupAlgebra p E}
    (hz :
      z ∈ denseGeneratorsSpan p E (1 + 1)) :
    χ.linearFunctional z = 0 := by
  let T : Set (denseGroupAlgebra p E) :=
    { z | ∃ w : List.Vector E (1 + 1),
        denseGeneratorsGenerator p E w = z }
  have hzspan : z ∈ Submodule.span (ZMod p) T := by
    simpa [denseGeneratorsSpan, T] using hz
  refine Submodule.span_induction
    (s := T)
    (p := fun z _ => χ.linearFunctional z = 0)
    ?_ ?_ ?_ ?_ hzspan
  · rintro z ⟨w, rfl⟩
    exact χ.linear_functional_generator w
  · exact map_zero χ.linearFunctional
  · intro x z _hx _hz hx_zero hz_zero
    rw [map_add, hx_zero, hz_zero, add_zero]
  · intro c z _hz hz_zero
    rw [map_smul, hz_zero, smul_zero]

lemma linear_functional_detects
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    χ.linearFunctional (denseGeneratorsElement p E y - 1) ≠ 0 := by
  intro hzero
  have hvalue :
      χ.linearFunctional (denseGeneratorsElement p E y - 1) =
        χ.toFun y :=
    χ.linear_functional_element y
  exact χ.detects (hvalue ▸ hzero)

lemma detects_ne_zero
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    χ.toFun y ≠ 0 := by
  have hdetect : χ.toFun y ≠ 0 := χ.detects
  exact hdetect

lemma map_mul_apply
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y)
    (a b : E) :
    χ.toFun (a * b) = χ.toFun a + χ.toFun b := by
  have hmul : χ.toFun (a * b) = χ.toFun a + χ.toFun b :=
    χ.map_mul a b
  exact hmul

end DACharac

lemma comm_trivial_commutators
    {E : Type u} [Group E]
    (hcomm :
      ∀ a b : E,
        a * b * a⁻¹ * b⁻¹ = 1)
    (a b : E) :
    a * b = b * a := by
  have hcancel_right : a * b * a⁻¹ = b := by
    have hmul := congrArg (fun x => x * b) (hcomm a b)
    simpa [mul_assoc] using hmul
  have hcancel_left := congrArg (fun x => x * a) hcancel_right
  simpa [mul_assoc] using hcancel_left

lemma dense_additive_torsion
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    (hpowers : ∀ a : E, a ^ p = 1) :
    ∀ x : Additive E, p • x = 0 := by
  intro x
  cases x using Additive.rec with
  | ofMul a =>
      rw [← ofMul_pow]
      simp [hpowers a]

lemma linear_ne
    {K : Type v}
    {V : Type u}
    [DivisionRing K]
    [AddCommGroup V]
    [Module K V]
    {v : V}
    (hv : v ≠ 0) :
    ∃ φ : V →ₗ[K] K, φ v ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K V
  have hrepr_ne_zero : b.repr v ≠ 0 := by
    intro hrepr_zero
    apply hv
    have hpreimage := congrArg (fun f => b.repr.symm f) hrepr_zero
    simpa using hpreimage
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr_ne_zero
  exact ⟨b.coord i, by simpa [Module.Basis.coord_apply] using hi⟩

lemma additive_character_comm
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [CommGroup E]
    {y : E}
    (hy_ne : y ≠ 1)
    (hpowers : ∀ a : E, a ^ p = 1) :
    Nonempty
      (DACharac
        (p := p) E y) := by
  classical
  letI : Module (ZMod p) (Additive E) :=
    AddCommGroup.zmodModule
      (dense_additive_torsion
        (p := p) (E := E) hpowers)
  have hy_add_ne : Additive.ofMul y ≠ (0 : Additive E) := by
    intro hy_add_zero
    apply hy_ne
    have hy_mul_zero := congrArg Additive.toMul hy_add_zero
    simpa using hy_mul_zero
  obtain ⟨φ, hφy⟩ :=
    linear_ne
      (K := ZMod p)
      (V := Additive E)
      hy_add_ne
  refine
    ⟨{
      toFun := fun a => φ.toFun (Additive.ofMul a)
      map_one := ?_
      map_mul := ?_
      detects := ?_
    }⟩
  · simpa using φ.map_zero
  · intro a b
    rw [ofMul_mul]
    exact φ.map_add (Additive.ofMul a) (Additive.ofMul b)
  · exact hφy

lemma
    dense_additive_character
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    denseGeneratorsElement p E y - 1 ∉
      denseGeneratorsSpan p E (1 + 1) := by
  classical
  have hdetect : χ.toFun y ≠ 0 :=
    DACharac.detects_ne_zero χ
  have hone : χ.toFun (1 : E) = 0 := χ.map_one
  have hmul :
      ∀ a b : E, χ.toFun (a * b) = χ.toFun a + χ.toFun b := by
    intro a b
    exact
      DACharac.map_mul_apply
        χ a b
  intro hyword
  have hzero :
      χ.linearFunctional (denseGeneratorsElement p E y - 1) = 0 :=
    χ.linear_functional_two hyword
  exact χ.linear_functional_detects hzero

lemma
    separating_functional_character
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E]
    {y : E}
    (χ :
      DACharac
        (p := p) E y) :
    Nonempty
      (DSFunc
        (p := p) (Λ := E) (m := 1) (x := y)) := by
  have hy_not_word :
      denseGeneratorsElement p E y - 1 ∉
        denseGeneratorsSpan p E (1 + 1) :=
    dense_additive_character
      (p := p) (E := E) (y := y) χ
  exact
    gens_fin_succ
      (p := p)
      (Λ := E)
      (m := 1)
      (x := y)
      (by simpa using hy_not_word)

lemma elementary_abelian_character
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E] [Finite E]
    {y : E}
    (hy_ne : y ≠ 1)
    (hpowers : ∀ a : E, a ^ p = 1)
    (hcomm :
      ∀ a b : E,
        a * b * a⁻¹ * b⁻¹ = 1) :
    Nonempty
      (DACharac
        (p := p) E y) := by
  classical
  letI : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm :=
        comm_trivial_commutators hcomm }
  exact
    additive_character_comm
      (p := p)
      (E := E)
      (y := y)
      hy_ne
      hpowers

lemma elementary_separating_functional
    {p : ℕ} [Fact p.Prime]
    {E : Type u} [Group E] [Finite E]
    {y : E}
    (hy_ne : y ≠ 1)
    (hpowers : ∀ a : E, a ^ p = 1)
    (hcomm :
      ∀ a b : E,
        a * b * a⁻¹ * b⁻¹ = 1) :
    Nonempty
      (DSFunc
        (p := p) (Λ := E) (m := 1) (x := y)) := by
  rcases
      elementary_abelian_character
        (p := p) (E := E) (y := y) hy_ne hpowers hcomm with
    ⟨χ⟩
  exact
    separating_functional_character
      (p := p) (E := E) (y := y) χ

lemma self_separating_functional
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] [Finite Λ]
    {y : zassenhausSelfQuotient p Λ (1 + 1)}
    (hy_ne : y ≠ 1)
    (hpowers :
      ∀ a : zassenhausSelfQuotient p Λ (1 + 1), a ^ p = 1)
    (hcomm :
      ∀ a b : zassenhausSelfQuotient p Λ (1 + 1),
        a * b * a⁻¹ * b⁻¹ = 1) :
    Nonempty
      (DSFunc
        (p := p)
        (Λ := zassenhausSelfQuotient p Λ (1 + 1))
        (m := 1)
        (x := y)) := by
  haveI : Finite (zassenhausSelfQuotient p Λ (1 + 1)) := by
    dsimp [zassenhausSelfQuotient]
    infer_instance
  exact
    elementary_separating_functional
      (p := p)
      (E := zassenhausSelfQuotient p Λ (1 + 1))
      (y := y)
      hy_ne
      hpowers
      hcomm

lemma
    dense_gens_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    {x : Λ} :
    Nonempty
        (DSFunc
          (p := p) Λ m x) ↔
      denseGeneratorsElement p Λ x - 1 ∉
        denseGeneratorsSpan p Λ (m + 1) := by
  constructor
  · rintro ⟨Φ⟩
    exact Φ.sub_span_succ
  · intro hxnot
    exact
      gens_fin_succ
        (p := p) (Λ := Λ) (m := m) (x := x) hxnot

lemma
    gens_pbw_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] [Finite Λ]
    {m : ℕ}
    (_hm : 1 < m)
    {y : zassenhausSelfQuotient p Λ (m + 1)}
    (_hymem :
      y ∈ zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) m)
    (_hynot :
      y ∉ zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1)) :
    Nonempty
        (DSFunc
          (p := p)
          (Λ := zassenhausSelfQuotient p Λ (m + 1))
          (m := m)
          (x := y)) ↔
      denseGeneratorsElement p
          (zassenhausSelfQuotient p Λ (m + 1)) y - 1 ∉
        denseGeneratorsSpan p
          (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) := by
  exact
    dense_gens_succ
      (p := p)
      (Λ := zassenhausSelfQuotient p Λ (m + 1))
      (m := m)
      (x := y)

lemma
    self_higher_succ
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {m : ℕ}
    (_hm : 1 < m)
    {y : zassenhausSelfQuotient p Λ (m + 1)}
    (Φ :
      DSFunc
        (p := p)
        (Λ := zassenhausSelfQuotient p Λ (m + 1))
        (m := m)
        (x := y)) :
    denseGeneratorsElement p
        (zassenhausSelfQuotient p Λ (m + 1)) y - 1 ∉
      denseGeneratorsSpan p
        (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) := by
  intro hyword
  have hzero :
      Φ.linearFunctional
          (denseGeneratorsElement p
              (zassenhausSelfQuotient p Λ (m + 1)) y - 1) = 0 := by
    exact Φ.annihilates_span_succ hyword
  have hdetect :
      Φ.linearFunctional
          (denseGeneratorsElement p
              (zassenhausSelfQuotient p Λ (m + 1)) y - 1) ≠ 0 := by
    exact Φ.detects_sub_one
  exact hdetect hzero

lemma self_succ_bot
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (m : ℕ) :
    zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) = ⊥ := by
  exact filtration_self_bot p Λ (m + 1)

lemma self_filtration_succ
    (p : ℕ)
    (Λ : Type u) [Group Λ]
    (m : ℕ)
    {y : zassenhausSelfQuotient p Λ (m + 1)}
    (hy : y ∈ zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1)) :
    y = 1 := by
  have hbot :
      zassenhausFiltration p (zassenhausSelfQuotient p Λ (m + 1)) (m + 1) = ⊥ :=
    self_succ_bot p Λ m
  have hybot : y ∈ (⊥ : Subgroup (zassenhausSelfQuotient p Λ (m + 1))) := by
    simpa [hbot] using hy
  exact Subgroup.mem_bot.mp hybot

structure
    GCPackag.PFUpperb
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  finite_quotient_zassenhaus :
    ∀ g : Γ,
      ((P.toAmbient.toCore (Q.toQuotientLayer R U)).canonicalUnit g :
          (P.toAmbient.toCore (Q.toQuotientLayer R U)).completedGroupAlgebra) - 1 ∈
        (P.toAmbient.toCore (Q.toQuotientLayer R U)).augmentationIdeal ^ n →
      ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
        (φ : Γ →* Λ),
        Continuous (fun x : Γ => φ x) →
        φ g ∈ zassenhausFiltration p Λ n

structure
    GCPackag.PFCongru
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  finite_quotient_congruence :
    ∀ g : Γ,
      ((P.toAmbient.toCore (Q.toQuotientLayer R U)).canonicalUnit g :
          (P.toAmbient.toCore (Q.toQuotientLayer R U)).completedGroupAlgebra) - 1 ∈
        (P.toAmbient.toCore (Q.toQuotientLayer R U)).augmentationIdeal ^ n →
      ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
        (φ : Γ →* Λ),
        Continuous (fun x : Γ => φ x) →
        dDCongru p Λ n (φ g)

structure
    GCPackag.PosdimFinquotAlgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) :
    Type (u + 1) where
  toAlgHom :
    P.toAmbient.completedGroupAlgebra →ₐ[ZMod p] denseGroupAlgebra p Λ
  map_canonicalUnit :
    ∀ g : Γ,
      toAlgHom (P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) =
        denseGeneratorsElement p Λ (φ g)
  map_augmentation :
    ∀ x : P.toAmbient.completedGroupAlgebra,
      MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p) (toAlgHom x) =
        P.toAmbient.augmentationMap x

structure
    GCPackag.PFRawalg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) :
    Type (u + 1) where
  toAlgHom :
    P.toAmbient.completedGroupAlgebra →ₐ[ZMod p] denseGroupAlgebra p Λ
  map_canonicalUnit :
    ∀ g : Γ,
      toAlgHom (P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) =
        denseGeneratorsElement p Λ (φ g)
  map_augmentation :
    ∀ x : P.toAmbient.completedGroupAlgebra,
      MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p) (toAlgHom x) =
        P.toAmbient.augmentationMap x

structure
    GCPackag.PosDimfinQuotform
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    {φ : Γ →* Λ}
    (M : P.PFRawalg Q R U φ) :
    Type (u + 1) where
  map_canonicalUnit :
    ∀ g : Γ,
      M.toAlgHom (P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) =
        denseGeneratorsElement p Λ (φ g)

def
    GCPackag.fin_quotraw_algmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ)
    (hφ : Continuous (fun x : Γ => φ x)) :
    P.PFRawalg Q R U φ where
  toAlgHom :=
    P.algebraMapExtension.quotient_alg_hom φ hφ
  map_canonicalUnit := by
    intro g
    simpa [
      GCPackag.toAmbient,
      DCObject.toAmbient,
      denseGeneratorsElement
    ] using
      P.algebraMapExtension.alg_hom_unit
        φ hφ g
  map_augmentation := by
    intro x
    simpa [
      GCPackag.toAmbient,
      DCObject.toAmbient
    ] using
      P.algebraMapExtension.finite_alg_hom
        φ hφ x

def
    GCPackag.PFRawalg.toCanonicalFormula
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    {φ : Γ →* Λ}
    (M : P.PFRawalg Q R U φ) :
    P.PosDimfinQuotform M where
  map_canonicalUnit := M.map_canonicalUnit

def
    GCPackag.PFRawalg.toAlgebraMap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    {φ : Γ →* Λ}
    (M : P.PFRawalg Q R U φ)
    (H : P.PosDimfinQuotform M) :
    P.PosdimFinquotAlgmap Q R U φ where
  toAlgHom := M.toAlgHom
  map_canonicalUnit := H.map_canonicalUnit
  map_augmentation := M.map_augmentation

structure
    GCPackag.PFRawalga
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  raw_algebra_map :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      (φ : Γ →* Λ),
      Continuous (fun x : Γ => φ x) →
      Nonempty (P.PFRawalg Q R U φ)

structure
    GCPackag.PosDimfinQuotformulas
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  finite_canonical_formula :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      {φ : Γ →* Λ},
      Continuous (fun x : Γ => φ x) →
      ∀ M : P.PFRawalg Q R U φ,
        Nonempty (P.PosDimfinQuotform M)

structure
    GCPackag.PFAlgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  finite_algebra_map :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      (φ : Γ →* Λ),
      Continuous (fun x : Γ => φ x) →
      Nonempty (P.PosdimFinquotAlgmap Q R U φ)

def
    GCPackag.PFRawalga.toAlgebraMaps
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    (Hraw : P.PFRawalga Q R U)
    (Hformula : P.PosDimfinQuotformulas Q R U) :
    P.PFAlgmap Q R U := by
  refine
    { finite_algebra_map := ?_ }
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
  rcases Hraw.raw_algebra_map φ hφ with ⟨Mraw⟩
  rcases Hformula.finite_canonical_formula hφ Mraw with ⟨Hcanon⟩
  exact ⟨Mraw.toAlgebraMap Hcanon⟩

structure
    GCPackag.PosdimFinquotAugtransport
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  unit_sub_one :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      {φ : Γ →* Λ},
      Continuous (fun x : Γ => φ x) →
      ∀ (M : P.PosdimFinquotAlgmap Q R U φ)
        (g : Γ),
        M.toAlgHom
            ((P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) - 1) ∈
          denseGeneratorsIdeal p Λ

def
    GCPackag.posdim_finquot_augtransport
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    P.PosdimFinquotAugtransport Q R U := by
  refine
    { unit_sub_one := ?_ }
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ _hφ M g
  have hmap_sub :
      M.toAlgHom
          ((P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) - 1) =
        denseGeneratorsElement p Λ (φ g) - 1 := by
    simp [map_sub, M.map_canonicalUnit g]
  simpa [hmap_sub] using
    dense_element_ideal
      (p := p) (Λ := Λ) (φ g)

lemma
    GCPackag.existspos_dimfinaug_transportonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PosdimFinquotAugtransport Q R U) := by
  exact
    ⟨P.posdim_finquot_augtransport Q R U⟩

structure
    GCPackag.PFAugide
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  map_augmentation_ideal :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      {φ : Γ →* Λ},
      Continuous (fun x : Γ => φ x) →
      ∀ (M : P.PosdimFinquotAlgmap Q R U φ)
        {x : P.toAmbient.completedGroupAlgebra},
        x ∈ P.toAmbient.augmentationIdeal →
        M.toAlgHom x ∈ denseGeneratorsIdeal p Λ

structure
    GCPackag.PosdimFinquotPowertransport
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Type (u + 1) where
  map_augmentation_power :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      {φ : Γ →* Λ},
      Continuous (fun x : Γ => φ x) →
      ∀ (M : P.PosdimFinquotAlgmap Q R U φ)
        {x : P.toAmbient.completedGroupAlgebra},
        x ∈ P.toAmbient.augmentationIdeal ^ n →
        M.toAlgHom x ∈ denseGeneratorsIdeal p Λ ^ n

def
    GCPackag.PFAugide.toPowerTransport
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    (Hideal : P.PFAugide Q R U) :
    P.PosdimFinquotPowertransport Q R U := by
  refine
    { map_augmentation_power := ?_ }
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ M x hx
  let I : Ideal P.toAmbient.completedGroupAlgebra := P.toAmbient.augmentationIdeal
  let J : Ideal (denseGroupAlgebra p Λ) :=
    denseGeneratorsIdeal p Λ
  have hI :
      ∀ {y : P.toAmbient.completedGroupAlgebra}, y ∈ I → M.toAlgHom y ∈ J := by
    intro y hy
    exact
      Hideal.map_augmentation_ideal hφ M (x := y)
        (by simpa [I] using hy)
  have hxI : x ∈ I ^ n := by
    simpa [I] using hx
  have hxJ : M.toAlgHom x ∈ J ^ n :=
    dense_alg_maps
      (𝕜 := ZMod p)
      (R := P.toAmbient.completedGroupAlgebra)
      (S := denseGroupAlgebra p Λ)
      (f := M.toAlgHom)
      (I := I)
      (J := J)
      (n := n)
      (x := x)
      hI
      hxI
  simpa [J] using hxJ

def
    GCPackag.PFAlgmap.toCongruenceTransport
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    (Hmaps : P.PFAlgmap Q R U)
    (Hpower : P.PosdimFinquotPowertransport Q R U) :
    P.PFCongru Q R U := by
  refine
    { finite_quotient_congruence := ?_ }
  intro g hcongruence Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
  rcases Hmaps.finite_algebra_map φ hφ with ⟨M⟩
  have hambient :
      (P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) - 1 ∈
        P.toAmbient.augmentationIdeal ^ n := by
    simpa [GCAmbien.toCore] using hcongruence
  have hmapped :
      M.toAlgHom
          ((P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) - 1) ∈
        denseGeneratorsIdeal p Λ ^ n :=
    Hpower.map_augmentation_power hφ M hambient
  have hmap_sub :
      M.toAlgHom
          ((P.toAmbient.canonicalUnit g : P.toAmbient.completedGroupAlgebra) - 1) =
        denseGeneratorsElement p Λ (φ g) - 1 := by
    simp [map_sub, M.map_canonicalUnit g]
  exact
    show dDCongru p Λ n (φ g) from
      by
        simpa [dDCongru, hmap_sub] using hmapped

lemma
    GCPackag.existsposdim_finquotraw_algmapsonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PFRawalga Q R U) := by
  refine
    ⟨{ raw_algebra_map := ?_ }⟩
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
  exact
    ⟨P.fin_quotraw_algmap Q R U φ hφ⟩

lemma
    GCPackag.existspos_dimfin_formulasonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PosDimfinQuotformulas Q R U) := by
  refine
    ⟨{ finite_canonical_formula := ?_ }⟩
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ _hφ M
  exact
    ⟨M.toCanonicalFormula⟩

lemma
    GCPackag.existsposdim_finquotalg_mapsonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PFAlgmap Q R U) := by
  rcases
      P.existsposdim_finquotraw_algmapsonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U _hn with
    ⟨Hraw⟩
  rcases
      P.existspos_dimfin_formulasonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U _hn with
    ⟨Hformula⟩
  exact
    ⟨Hraw.toAlgebraMaps Hformula⟩

lemma
    GCPackag.existspos_dimfinideal_transportonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PFAugide Q R U) := by
  refine
    ⟨{ map_augmentation_ideal := ?_ }⟩
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ _hφ M x hx
  have hxker :
      x ∈ RingHom.ker P.toAmbient.augmentationMap.toRingHom := by
    simpa [P.toAmbient.augmentation_ideal_ker] using hx
  have hxzero : P.toAmbient.augmentationMap x = 0 := by
    simpa [RingHom.mem_ker] using hxker
  have hfinite_zero :
      denseGeneratorsAugmentation p Λ (M.toAlgHom x) = 0 := by
    simpa [denseGeneratorsAugmentation, hxzero] using
      M.map_augmentation x
  rw [dense_generators_ker]
  rw [RingHom.mem_ker]
  exact hfinite_zero

lemma
    GCPackag.existspos_dimfinpower_transportonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PosdimFinquotPowertransport Q R U) := by
  rcases
      P.existspos_dimfinideal_transportonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U _hn with
    ⟨Hideal⟩
  exact
    ⟨Hideal.toPowerTransport⟩

structure DenseUpperBound
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) :
    Type (u + 1) where
  finite_group_zassenhaus :
    ∀ {Λ : Type u} [Group Λ] [Finite Λ] (x : Λ),
      dDCongru p Λ n x →
      x ∈ zassenhausFiltration p Λ n

def TUBound.pos_dim_upperbound
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (H : TUBound (p := p) n) :
    DenseUpperBound (p := p) n := by
  refine
    { finite_group_zassenhaus := ?_ }
  intro Λ _instGroupΛ _instFiniteΛ x hx
  let Ω : Type u := zassenhausSelfQuotient p Λ n
  letI : Group Ω := instSelfQuotient p Λ n
  haveI : Finite Ω := by
    dsimp [Ω, zassenhausSelfQuotient]
    infer_instance
  let q : Λ →* Ω := zassenhausSelf p Λ n
  have hxq :
      dDCongru p Ω n (q x) := by
    dsimp [q, Ω]
    exact
      dDCongru.map_zass_selfquot
        (p := p) hx
  have hΩ :
      zassenhausFiltration p Ω n = ⊥ := by
    dsimp [Ω]
    exact filtration_self_bot p Λ n
  have hq_one : q x = 1 :=
    H.one_trivial_zassenhaus hΩ (q x) hxq
  dsimp [q, Ω] at hq_one
  exact
    (zassenhaus_self_quotient p Λ n x).mp hq_one

def
    GCPackag.PFCongru.fin_quot_upperbound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    (Htransport : P.PFCongru Q R U)
    (Hfinite : DenseUpperBound (p := p) n) :
    P.PFUpperb Q R U := by
  refine
    { finite_quotient_zassenhaus := ?_ }
  intro g hcongruence Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
  have hfinite_congruence :
      dDCongru p Λ n (φ g) :=
    Htransport.finite_quotient_congruence g hcongruence φ hφ
  exact
    Hfinite.finite_group_zassenhaus (φ g) hfinite_congruence

lemma
    GCPackag.existspos_dimfincong_transportonelt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (_hn : 1 < n) :
    Nonempty (P.PFCongru Q R U) := by
  rcases
      P.existsposdim_finquotalg_mapsonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U _hn with
    ⟨Hmaps⟩
  rcases
      P.existspos_dimfinpower_transportonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U _hn with
    ⟨Hpower⟩
  exact
    ⟨Hmaps.toCongruenceTransport Hpower⟩

lemma filtration_comap
    {p : ℕ}
    {Γ Λ : Type u} [Group Γ] [Group Λ]
    (n : ℕ)
    (φ : Γ →* Λ) :
    zassenhausFiltration p Γ n ≤
      Subgroup.comap φ (zassenhausFiltration p Λ n) := by
  intro g hg
  exact
    filtration_map_mem
      (p := p)
      (n := n)
      (f := φ)
      hg

structure DGTest
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instTopologicalSpace : TopologicalSpace quotientGroup]
  [instDiscreteTopology : DiscreteTopology quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap : Γ →* quotientGroup
  quotientMap_continuous : Continuous (fun x : Γ => quotientMap x)

namespace DGTest

def ofHom
    {Γ Λ : Type u} [Group Γ] [TopologicalSpace Γ]
    [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ)
    (hφ : Continuous (fun x : Γ => φ x)) :
    DGTest Γ where
  quotientGroup := Λ
  instGroup := inferInstance
  instTopologicalSpace := inferInstance
  instDiscreteTopology := inferInstance
  instFinite := inferInstance
  quotientMap := φ
  quotientMap_continuous := hφ

def targetZassenhaus
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (T : DGTest Γ)
    (p n : ℕ) :
    @Subgroup T.quotientGroup T.instGroup :=
  @zassenhausFiltration p T.quotientGroup T.instGroup n

end DGTest

end Submission
