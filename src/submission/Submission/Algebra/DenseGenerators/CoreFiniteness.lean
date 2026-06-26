import Mathlib
import Submission.Algebra.DenseGenerators.Jennings


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

namespace GCAmbien

def CompletedAlgebra
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  ∀ (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
      [CompactSpace B] [TotallyDisconnectedSpace B],
    ∀ v : Γ →* Units B,
      Continuous v →
        ∃! Φ : A.completedGroupAlgebra →ₐ[ZMod p] B,
          Continuous Φ ∧
            ∀ g : Γ,
              Φ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B)

end GCAmbien

namespace DCCore

lemma augmentation_t_2
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := C.quotientTopology
    T2Space C.augmentationQuotient := by
  letI := C.quotientTopology
  have hT2 : T2Space C.augmentationQuotient := C.quotientT2
  exact hT2

end DCCore

lemma completed_core_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite C.augmentationQuotient) :
    Finite C.quotientUnitMap.range := by
  letI := C.instQuotientRing
  letI := C.quotientTopology
  letI : Finite C.augmentationQuotient := hfinite
  have hfinite_units : Finite (Units C.augmentationQuotient) := inferInstance
  exact inferInstance

lemma completed_core_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hT2 :
      letI := C.quotientTopology
      T2Space C.augmentationQuotient) :
    letI := C.quotientTopology
    T2Space C.quotientUnitMap.range := by
  letI := C.instQuotientRing
  letI := C.quotientTopology
  letI : T2Space C.augmentationQuotient := hT2
  have hT2_units : T2Space (Units C.augmentationQuotient) := inferInstance
  exact inferInstance

lemma discrete_t_2
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite C.augmentationQuotient)
    (hT2 :
      letI := C.quotientTopology
      T2Space C.augmentationQuotient) :
    letI := C.quotientTopology
    DiscreteTopology C.quotientUnitMap.range := by
  letI := C.instQuotientRing
  letI := C.quotientTopology
  have hfinite_range : Finite C.quotientUnitMap.range :=
    completed_core_range
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hfinite
  have hT2_range : T2Space C.quotientUnitMap.range :=
    completed_core_t
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hT2
  letI : Finite C.quotientUnitMap.range := hfinite_range
  letI : T2Space C.quotientUnitMap.range := hT2_range
  infer_instance

lemma DCAlg.fin_core_fintrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient := by
  have hfiniteQ : Finite Q.augmentationQuotient :=
    Q.fin_fin_trunc T
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  simpa [GCAmbien.toCore] using hfiniteLayer

lemma
    DCAlg.fin_corefin_algtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient := by
  have hfiniteQ : Finite Q.augmentationQuotient :=
    Q.fin_fin_algtrunc T
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  simpa [GCAmbien.toCore] using hfiniteLayer

lemma gens_core_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (T : A.FCAugtru n) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc T
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  refine ⟨C, ?_⟩
  have hfinite :
      Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    Q.fin_core_fintrunc T R U
  simpa [C] using hfinite

lemma
    core_algebraic_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (T : A.FAAugtru n)
    (HTop : T.DiscreteContTopo) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  let Tcont : A.FCAugtru n :=
    T.fin_cont_augtrunc HTop
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc Tcont
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  refine ⟨C, ?_⟩
  have hfinite :
      Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    Q.fin_corefin_algtrunc T R U
  simpa [C] using hfinite

lemma dense_gens_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  rcases
      gens_completed_topology
        (p := p) (Γ := Γ) s hs hn with
    ⟨A, _hdense, T, hTtop⟩
  rcases hTtop with ⟨HTop⟩
  exact
    core_algebraic_trunc
      (p := p) (Γ := Γ) (s := s) (hs := hs) A T HTop

lemma dense_completed_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs 0,
      Finite M.augmentationQuotient := by
  rcases completed_algebra_ambient
      (p := p) (Γ := Γ) s hs with ⟨A⟩
  rcases A.topo_aug_quotzero with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs 0 :=
    A.toCore (Q.toQuotientLayer R U)
  refine ⟨C, ?_⟩
  have hfiniteQ : Finite Q.augmentationQuotient :=
    Q.fin_level_zero
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  have hfiniteCore : Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    (by simpa [GCAmbien.toCore] using hfiniteLayer)
  simpa [C] using hfiniteCore

lemma generators_completed_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs 1,
      Finite M.augmentationQuotient := by
  rcases completed_algebra_ambient
      (p := p) (Γ := Γ) s hs with ⟨A⟩
  exact
    gens_core_ambient
      (p := p) (Γ := Γ) (s := s) (hs := hs) A
      A.fin_contaug_truncone

lemma gens_completed_cases
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  cases n with
  | zero =>
      exact
        dense_completed_core
          (p := p) (Γ := Γ) s hs
  | succ n =>
      cases n with
      | zero =>
          exact
            generators_completed_core
              (p := p) (Γ := Γ) s hs
      | succ n =>
          have htwo : 2 ≤ Nat.succ (Nat.succ n) :=
            Nat.succ_le_succ (Nat.succ_pos n)
          exact
            dense_gens_core
              (p := p) (Γ := Γ) s hs htwo

def DCCore.FinDenseWordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  ∃ ι : Type u, Finite ι ∧
    ∃ w : ι → M.augmentationQuotient,
      Submodule.span (ZMod p) (Set.range w) = ⊤

noncomputable def DCCore.signedAugmentationLetter
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d) : M.augmentationQuotient := by
  letI := M.instRing
  letI := M.instQuotientRing
  exact
    M.quotientMap
      ((M.canonicalUnit (generatorsLetterElement s a) :
        M.completedGroupAlgebra) - 1)

noncomputable def DCCore.boundedAugmentationWord
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) : M.augmentationQuotient := by
  letI := M.instQuotientRing
  exact
    (w.2.toList.map fun a =>
      M.signedAugmentationLetter (s := s) a).prod

noncomputable def DCCore.bounded_aug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Submodule (ZMod p) M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact
    Submodule.span (ZMod p)
      (Set.range fun w : ULift.{u} (denseBoundedIndex d n) =>
        M.boundedAugmentationWord (s := s) (n := n) w.down)

lemma DCCore.bounded_augword_memspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.boundedAugmentationWord (s := s) (n := n) w ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact Submodule.subset_span ⟨ULift.up w, rfl⟩

@[simp]
lemma DCCore.bounded_aug_wordempty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseEmptyBounded d n) = 1 := by
  letI := M.instQuotientRing
  simp [DCCore.boundedAugmentationWord,
    denseEmptyBounded]

lemma DCCore.onemem_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    (1 : M.augmentationQuotient) ∈ M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa using
    M.bounded_augword_memspan
      (s := s) (n := n) (denseEmptyBounded d n)

@[simp]
lemma DCCore.bounded_aug_wordsingleton
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : 0 < n)
    (a : denseSignedLetter d) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseSingletonBounded hn a) =
      M.signedAugmentationLetter (s := s) a := by
  letI := M.instQuotientRing
  simp [DCCore.boundedAugmentationWord,
    denseSingletonBounded]

@[simp]
lemma DCCore.boundedaug_wordcons_boundedword
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : v.1.1 < n) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseConsBounded a v hv) =
      M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v := by
  letI := M.instQuotientRing
  simp [DCCore.boundedAugmentationWord,
    denseConsBounded]

lemma DCCore.signedaug_lettermem_boundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : 0 < n)
    (a : denseSignedLetter d) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a ∈ M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa using
    M.bounded_augword_memspan
      (s := s) (n := n) (denseSingletonBounded hn a)

def DCCore.BoundedAugWordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  M.bounded_aug_wordspan = ⊤

lemma DCCore.fg_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.bounded_aug_wordspan.FG := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rw [DCCore.bounded_aug_wordspan]
  exact
    Submodule.fg_span
      (Set.finite_range fun w : ULift.{u} (denseBoundedIndex d n) =>
        M.boundedAugmentationWord (s := s) (n := n) w.down)

lemma DCCore.modulefin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Module.Finite (ZMod p) M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact
    Module.Finite.of_fg
      (M.fg_boundedaug_wordspan (s := s) (n := n))

lemma DCCore.fin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Finite M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Module.Finite (ZMod p) M.bounded_aug_wordspan :=
    M.modulefin_boundedaug_wordspan (s := s) (n := n)
  haveI : Finite (ZMod p) :=
    dense_generators_zmod p
  exact Module.finite_of_finite (ZMod p)

lemma DCCore.setfin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    (M.bounded_aug_wordspan : Set M.augmentationQuotient).Finite := by
  classical
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Finite M.bounded_aug_wordspan :=
    M.fin_boundedaug_wordspan (s := s) (n := n)
  haveI : Fintype M.bounded_aug_wordspan :=
    Fintype.ofFinite M.bounded_aug_wordspan
  exact Set.toFinite (M.bounded_aug_wordspan : Set M.augmentationQuotient)

lemma DCCore.closed_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    letI := M.quotientTopology
    IsClosed (M.bounded_aug_wordspan : Set M.augmentationQuotient) := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  letI := M.quotientT2
  exact
    (M.setfin_boundedaug_wordspan (s := s) (n := n)).isClosed

def DCCore.DenseCanonunitQuotspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra)) :
        Set M.augmentationQuotient)) = Set.univ

def DCCore.DenseAlgebraSpan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (M.canonicalUnit g : M.completedGroupAlgebra)) :
        Set M.completedGroupAlgebra)) = Set.univ

lemma GCAmbien.densecanon_unitalg_spancore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hdense : A.DenseAlgebraSpan) :
    (A.toCore Q).DenseAlgebraSpan := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  simpa [GCAmbien.DenseAlgebraSpan,
    DCCore.DenseAlgebraSpan,
    GCAmbien.toCore] using hdense

def DCCore.CanonunitSuboneBoundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  ∀ g : Γ,
    M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan

def DCCore.PoscanonUnitsubOneboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  n ≠ 0 →
    ∀ g : Γ,
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan

def DCCore.PosdenseSubgroupsubOneboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  n ≠ 0 →
    ∀ g : Γ,
      g ∈ Subgroup.closure (Set.range s) →
        M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
          M.bounded_aug_wordspan

lemma DCCore.quotmapsigned_wordelementnil_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s []) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hzero :
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s []) :
            M.completedGroupAlgebra) - 1) = 0 := by
    simp [generatorsSignedElement]
  rw [hzero]
  exact M.bounded_aug_wordspan.zero_mem

lemma DCCore.quotmapsigned_wordelemsing_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s [a]) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      M.signedAugmentationLetter (s := s) a ∈
        M.bounded_aug_wordspan :=
    M.signedaug_lettermem_boundedspan (s := s) (n := n) hnpos a
  simpa [generatorsSignedElement,
    DCCore.signedAugmentationLetter] using hletter

lemma DCCore.signedaug_lettermul_memspanlt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : v.1.1 < n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hmem :
      M.boundedAugmentationWord (s := s) (n := n)
          (denseConsBounded a v hv) ∈
        M.bounded_aug_wordspan :=
    M.bounded_augword_memspan
      (s := s) (n := n) (denseConsBounded a v hv)
  simpa using hmem

lemma DCCore.quotmap_signedaug_factorsprodlist
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((w.map fun a =>
          (M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1).prod) =
      (w.map fun a => M.signedAugmentationLetter (s := s) a).prod := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  induction w with
  | nil =>
      simp [DCCore.signedAugmentationLetter]
  | cons a w ih =>
      simp [DCCore.signedAugmentationLetter,
        map_mul, ih]

lemma DCCore.quotmap_signedaug_factorsprod
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) :
    letI := M.instRing
    letI := M.instQuotientRing
    M.quotientMap
        ((w.2.toList.map fun a =>
          (M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1).prod) =
      M.boundedAugmentationWord (s := s) (n := n) w := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa [DCCore.boundedAugmentationWord] using
    M.quotmap_signedaug_factorsprodlist (s := s) (n := n) w.2.toList

lemma DCCore.signedaug_lettermuleq_quotmapcons
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v =
      M.quotientMap
        (((a :: v.2.toList).map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod) := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hlist :
      M.quotientMap
          (((a :: v.2.toList).map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) =
        ((a :: v.2.toList).map fun b =>
          M.signedAugmentationLetter (s := s) b).prod :=
    M.quotmap_signedaug_factorsprodlist
      (s := s) (n := n) (a :: v.2.toList)
  simpa [DCCore.boundedAugmentationWord] using hlist.symm

lemma DCCore.quotmap_signwordelem_consproducteq
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instQuotientRing
    M.quotientMap
        (((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1)) =
      M.signedAugmentationLetter (s := s) a *
        M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) := by
  letI := M.instRing
  letI := M.instQuotientRing
  rw [map_mul]
  rfl

def DCCore.BoundedWordspanRawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  M.DenseAlgebraSpan ∧ M.CanonunitSuboneBoundedspan

def DCCore.BoundedwordSpanposRawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  M.DenseAlgebraSpan ∧
    M.PosdenseSubgroupsubOneboundedspan

def DCCore.BoundedWordspanProofinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) : Prop :=
  M.DenseCanonunitQuotspan ∧
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    ∀ g : Γ,
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan

lemma DCCore.quotmap_canonunit_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (g : Γ)
    (hsub :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hone : (1 : M.augmentationQuotient) ∈ M.bounded_aug_wordspan :=
    M.onemem_boundedaug_wordspan (s := s) (n := n)
  have hsum :
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) + 1 ∈
        M.bounded_aug_wordspan :=
    M.bounded_aug_wordspan.add_mem hsub hone
  simpa using hsum

lemma DCCore.bounded_wordspan_proofinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedWordspanProofinputs) :
    M.BoundedAugWordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  let canonicalSpan : Submodule (ZMod p) M.augmentationQuotient :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra))
  have hcanonical_le : canonicalSpan ≤ M.bounded_aug_wordspan := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, rfl⟩
    exact
      M.quotmap_canonunit_memboundedspan
        (s := s) (n := n) g (H.2 g)
  have hclosure_subset :
      closure (canonicalSpan : Set M.augmentationQuotient) ⊆
        (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    closure_minimal hcanonical_le
      (M.closed_boundedaug_wordspan (s := s) (n := n))
  refine le_antisymm le_top ?_
  intro x _hx
  have hxclosure : x ∈ closure (canonicalSpan : Set M.augmentationQuotient) := by
    rw [H.1]
    exact Set.mem_univ x
  exact hclosure_subset hxclosure

lemma DCCore.findense_wordspan_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hspan : M.BoundedAugWordspan) :
    M.FinDenseWordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let ι : Type u := ULift.{u} (denseBoundedIndex d n)
  have hι : Finite ι := by
    dsimp [ι]
    exact dense_bounded_index d n
  let w : ι → M.augmentationQuotient :=
    fun x => M.boundedAugmentationWord (s := s) (n := n) x.down
  have hw : Submodule.span (ZMod p) (Set.range w) = ⊤ := by
    simpa [DCCore.BoundedAugWordspan, ι, w]
      using hspan
  exact ⟨ι, hι, w, hw⟩

lemma DCCore.modulefin_findense_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hspan : M.FinDenseWordspan) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Module.Finite (ZMod p) M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rcases hspan with ⟨ι, hι, w, hw⟩
  letI : Finite ι := hι
  exact
    dense_spanning_family
      (R := ZMod p) (M := M.augmentationQuotient) w hw

lemma DCCore.finaug_quotfin_densewordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hspan : M.FinDenseWordspan) :
    Finite M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Module.Finite (ZMod p) M.augmentationQuotient :=
    M.modulefin_findense_wordspan hspan
  haveI : Finite (ZMod p) :=
    dense_generators_zmod p
  exact Module.finite_of_finite (ZMod p)

lemma dense_core_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.DenseAlgebraSpan := by
  rcases
      gens_completed_layer
        (p := p) (Γ := Γ) s hs n with
    ⟨A, hdense, hQ⟩
  rcases hQ with ⟨Q⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore Q
  refine ⟨C, ?_⟩
  simpa [C] using
    A.densecanon_unitalg_spancore
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q hdense

lemma completed_algebra_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  exact
    gens_completed_cases
      (p := p) (Γ := Γ) s hs n

lemma dense_core_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        T2Space M.augmentationQuotient) := by
  rcases completed_algebra_core
      (p := p) (Γ := Γ) s hs n with ⟨M, hfinite⟩
  refine ⟨M, hfinite, ?_⟩
  exact M.augmentation_t_2

lemma core_discrete_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (h :
      ∃ M : DCCore
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          T2Space M.augmentationQuotient)) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  rcases h with ⟨M, hfinite, hT2⟩
  refine ⟨M, hfinite, ?_⟩
  exact
    discrete_t_2
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite hT2

lemma core_discrete_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  exact
    core_discrete_t
      (p := p) (Γ := Γ) s hs n
      (dense_core_t
        (p := p) (Γ := Γ) s hs n)

end Submission
