import Mathlib
import Submission.Algebra.DenseGenerators.PositiveAugmentation


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

def DCCore.PosJenningsInput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Prop :=
  ∀ g : Γ,
    (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
      g ∈ zassenhausFiltration p Γ n

lemma DCCore.posjennings_inputiffpos_dimsubgboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    C.PosJenningsInput ↔
      Nonempty (JLBound C) := by
  constructor
  · intro H
    exact
      (dense_lazard_bound
        (p := p) (Γ := Γ) (s := s) (hs := hs) C).2 H
  · intro H
    exact
      (dense_lazard_bound
        (p := p) (Γ := Γ) (s := s) (hs := hs) C).1 H

def DCCore.PosjenningsBoundedwordRawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Prop :=
  C.BoundedwordSpanposRawinputs ∧ C.PosJenningsInput

def DCCore.DenseSpanposJenningsinput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Prop :=
  C.DenseAlgebraSpan ∧ C.PosJenningsInput

lemma DCCore.denseunit_algspan_posjenninpu
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : C.DenseSpanposJenningsinput) :
    C.DenseAlgebraSpan := by
  exact H.1

lemma DCCore.posjennings_inputspan_posjenninpu
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : C.DenseSpanposJenningsinput) :
    C.PosJenningsInput := by
  exact H.2

def GCAmbien.PosJenningsinputQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  (A.toCore Q).PosJenningsInput

def GCAmbien.DensespanPosjenningsQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  A.DenseAlgebraSpan ∧
    A.PosJenningsinputQuotlayer Q

lemma GCAmbien.densespan_posjenncomp_densequotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.CompleteDenseQuotlayer Q)
    (hJL : A.PosJenningsinputQuotlayer Q) :
    A.DensespanPosjenningsQuotlayer Q := by
  rcases H with ⟨hcomplete, hdense⟩
  have _hcomplete : A.CompletedAlgebra := hcomplete
  have hdense' : A.DenseAlgebraSpan := hdense
  have hJL' : A.PosJenningsinputQuotlayer Q := hJL
  exact ⟨hdense', hJL'⟩

def GCAmbien.PosdimSubgroupboundQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  Nonempty (JLBound (A.toCore Q))

def GCAmbien.PointwiseposDimboundQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  ∀ g : Γ,
    ((A.toCore Q).canonicalUnit g : (A.toCore Q).completedGroupAlgebra) - 1 ∈
        (A.toCore Q).augmentationIdeal ^ n →
      g ∈ zassenhausFiltration p Γ n

def GCAmbien.JenningskernelUpperboundQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  (A.toCore Q).quotientUnitMap.ker ≤ zassenhausFiltration p Γ n

lemma GCAmbien.nonemptjenning_kernelupper_boundquotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.JenningskernelUpperboundQuotlayer Q) :
    Nonempty (LUBound (A.toCore Q)) := by
  dsimp [
    GCAmbien.JenningskernelUpperboundQuotlayer,
    LUBound
  ] at H ⊢
  exact ⟨⟨H⟩⟩

lemma GCAmbien.pointwisepos_dimiffjennings_kernuppeboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    A.PointwiseposDimboundQuotlayer Q ↔
      A.JenningskernelUpperboundQuotlayer Q := by
  constructor
  · intro Hpoint g hgker
    have hpow :
        ((A.toCore Q).canonicalUnit g : (A.toCore Q).completedGroupAlgebra) - 1 ∈
          (A.toCore Q).augmentationIdeal ^ n :=
      jennings_lazard_ker
        (p := p) (Γ := Γ) (s := s) (hs := hs) (A.toCore Q) hgker
    exact Hpoint g hpow
  · intro Hker g hpow
    have hgker :
        g ∈ (A.toCore Q).quotientUnitMap.ker :=
      jennings_lazard_sub
        (p := p) (Γ := Γ) (s := s) (hs := hs) (A.toCore Q) hpow
    exact Hker hgker

lemma GCAmbien.pointwisepos_dimjennings_kernuppeboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.JenningskernelUpperboundQuotlayer Q) :
    A.PointwiseposDimboundQuotlayer Q := by
  exact
    (A.pointwisepos_dimiffjennings_kernuppeboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q).2 H

lemma GCAmbien.jenningskernel_upperpos_dimsubgboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.PointwiseposDimboundQuotlayer Q) :
    A.JenningskernelUpperboundQuotlayer Q := by
  exact
    (A.pointwisepos_dimiffjennings_kernuppeboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q).1 H

lemma GCAmbien.pointwisepos_dimpos_dimsubgboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.PosdimSubgroupboundQuotlayer Q) :
    A.PointwiseposDimboundQuotlayer Q := by
  dsimp [
    GCAmbien.PosdimSubgroupboundQuotlayer,
    GCAmbien.PointwiseposDimboundQuotlayer
  ] at H ⊢
  exact
    (dense_lazard_bound
      (p := p) (Γ := Γ) (s := s) (hs := hs) (A.toCore Q)).1 H

def DCCore.PackagedCompleteGroupalg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Prop :=
  ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
    ∃ Q : DCLayer
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      A.CompletedAlgebra ∧ C = A.toCore Q

lemma DCCore.packaged_completegroup_algcore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hcomplete : A.CompletedAlgebra) :
    (A.toCore Q).PackagedCompleteGroupalg := by
  refine ⟨A, Q, ?_, ?_⟩
  · exact hcomplete
  · rfl

lemma GCAmbien.jenningskernel_upperpos_dimsubgbouna
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.PosdimSubgroupboundQuotlayer Q) :
    A.JenningskernelUpperboundQuotlayer Q := by
  have Hpoint : A.PointwiseposDimboundQuotlayer Q :=
    A.pointwisepos_dimpos_dimsubgboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q H
  exact
    A.jenningskernel_upperpos_dimsubgboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q Hpoint

lemma GCAmbien.posjennings_inputpos_dimsubgbouna
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.PosdimSubgroupboundQuotlayer Q) :
    A.PosJenningsinputQuotlayer Q := by
  dsimp [
    GCAmbien.PosJenningsinputQuotlayer,
    GCAmbien.PosdimSubgroupboundQuotlayer
  ] at H ⊢
  exact
    (DCCore.posjennings_inputiffpos_dimsubgboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) (A.toCore Q)).2 H

lemma DCCore.existscomplete_ambientpackaged_compgroualg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : C.PackagedCompleteGroupalg) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.CompletedAlgebra := by
  rcases H with ⟨A, Q, hcomplete, hC⟩
  have _hcore : C = A.toCore Q := hC
  exact ⟨A, hcomplete⟩

def DCCore.ClassicalPosjenningsSubgroupbound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Prop :=
  Nonempty (JLBound C)

lemma DCCore.posjennings_inputclassical_subgroupbound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (H : C.ClassicalPosjenningsSubgroupbound) :
    C.PosJenningsInput := by
  have Hnonempty :
      Nonempty (JLBound C) := H
  have hiff :
      C.PosJenningsInput ↔
        Nonempty (JLBound C) :=
    DCCore.posjennings_inputiffpos_dimsubgboun
      (p := p) (Γ := Γ) (s := s) (hs := hs) C
  exact hiff.2 Hnonempty

lemma GCAmbien.core_packagecomplet_groupalg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hcomplete : A.CompletedAlgebra) :
    (A.toCore Q).PackagedCompleteGroupalg := by
  exact
    DCCore.packaged_completegroup_algcore
      (p := p) (Γ := Γ) (s := s) (hs := hs) A Q hcomplete

lemma GCAmbien.densespan_posjennings_inputcore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.DensespanPosjenningsQuotlayer Q) :
    (A.toCore Q).DenseSpanposJenningsinput := by
  refine ⟨?_, ?_⟩
  · exact
      A.densecanon_unitalg_spancore
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q H.1
  · exact H.2

lemma dense_gens_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (h :
      ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
        ∃ Q : DCLayer
            (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
          A.DensespanPosjenningsQuotlayer Q) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      C.DenseSpanposJenningsinput := by
  rcases h with ⟨A, Q, H⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore Q
  have HC : C.DenseSpanposJenningsinput := by
    simpa [C] using
      A.densespan_posjennings_inputcore
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q H
  exact ⟨C, HC⟩

end Submission
