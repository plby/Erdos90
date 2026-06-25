import Mathlib
import Towers.Algebra.DenseGenerators.CoreFiniteness


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

namespace GCAmbien

def CompletedExtensionExistence
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
        ∃ Φ : A.completedGroupAlgebra →ₐ[ZMod p] B,
          Continuous Φ ∧
            ∀ g : Γ,
              Φ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B)

def CompletedExtensionUniqueness
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
        ∀ Φ Ψ : A.completedGroupAlgebra →ₐ[ZMod p] B,
          (Continuous Φ ∧
              ∀ g : Γ,
                Φ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B)) →
            (Continuous Ψ ∧
              ∀ g : Γ,
                Ψ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B)) →
              Φ = Ψ

def CompletedUniversalInputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  A.CompletedExtensionExistence ∧
    A.CompletedExtensionUniqueness

lemma completed_extension_existence
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hcomplete : A.CompletedAlgebra) :
    A.CompletedExtensionExistence := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv
  rcases hcomplete B v hv with ⟨Φ, hΦ, _huniq⟩
  exact ⟨Φ, hΦ⟩

lemma completed_extension_uniqueness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hcomplete : A.CompletedAlgebra) :
    A.CompletedExtensionUniqueness := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv Φ Ψ hΦ hΨ
  rcases hcomplete B v hv with ⟨Θ, hΘ, huniq⟩
  have hΦΘ : Φ = Θ := huniq Φ hΦ
  have hΨΘ : Ψ = Θ := huniq Ψ hΨ
  exact hΦΘ.trans hΨΘ.symm

lemma completed_universal_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hcomplete : A.CompletedAlgebra) :
    A.CompletedUniversalInputs := by
  have Hext : A.CompletedExtensionExistence :=
    A.completed_extension_existence hcomplete
  have Huniq : A.CompletedExtensionUniqueness :=
    A.completed_extension_uniqueness hcomplete
  exact ⟨Hext, Huniq⟩

end GCAmbien

lemma DCCore.finaug_quotbounded_augwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hbounded : C.BoundedAugWordspan) :
    Finite C.augmentationQuotient := by
  letI := C.instQuotientRing
  letI := C.instQuotientAlgebra
  have hspan : C.FinDenseWordspan :=
    C.findense_wordspan_boundedwordspan (s := s) (n := n) hbounded
  exact C.finaug_quotfin_densewordspan hspan

lemma DCCore.discretequot_unitmap_finaugquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite C.augmentationQuotient) :
    letI := C.quotientTopology
    DiscreteTopology C.quotientUnitMap.range := by
  letI := C.quotientTopology
  have hT2 :
      T2Space C.augmentationQuotient :=
    C.augmentation_t_2
  exact
    discrete_t_2
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hfinite hT2

def GCAmbien.CompleteDenseQuotlayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (_Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Prop :=
  A.CompletedAlgebra ∧ A.DenseAlgebraSpan

def GCAmbien.CompletedAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  A.CompletedAlgebra

def GCAmbien.CompletedDenseAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  A.CompletedAlgebra ∧ A.DenseAlgebraSpan

lemma GCAmbien.complete_ambientcomplete_denseambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.CompletedDenseAmbient) :
    A.CompletedAmbient := by
  rcases H with ⟨hcomplete, hdense⟩
  have hcomplete' : A.CompletedAlgebra := hcomplete
  have _hdense' : A.DenseAlgebraSpan := hdense
  simpa [GCAmbien.CompletedAmbient] using hcomplete'

def GCAmbien.CGMap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type u :=
  letI : DecidableEq Γ := Classical.decEq Γ
  Σ φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] A.completedGroupAlgebra,
    PLift
      (∀ g : Γ,
        φ (Finsupp.single g (1 : ZMod p)) =
          (A.canonicalUnit g : A.completedGroupAlgebra))

namespace GCAmbien.CGMap

def toAlgHom
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (φ : A.CGMap) :
    letI : DecidableEq Γ := Classical.decEq Γ
    MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] A.completedGroupAlgebra :=
  φ.1

lemma map_single_one
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (φ : A.CGMap)
    (g : Γ) :
    letI : DecidableEq Γ := Classical.decEq Γ
    φ.toAlgHom (Finsupp.single g (1 : ZMod p)) =
      (A.canonicalUnit g : A.completedGroupAlgebra) := by
  letI : DecidableEq Γ := Classical.decEq Γ
  exact φ.2.down g

def RangeContainedSpan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (φ : A.CGMap) :
    Prop :=
  Set.range φ.toAlgHom ⊆
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)

def HasDenseRange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (φ : A.CGMap) :
    Prop :=
  closure (Set.range φ.toAlgHom) = Set.univ

end GCAmbien.CGMap

noncomputable def GCAmbien.canonicalAlgebraLift
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    letI : DecidableEq Γ := Classical.decEq Γ
    MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] A.completedGroupAlgebra :=
  letI : DecidableEq Γ := Classical.decEq Γ
  let v : Γ →* A.completedGroupAlgebra :=
    (Units.coeHom A.completedGroupAlgebra).comp A.canonicalUnit
  (MonoidAlgebra.lift (ZMod p) A.completedGroupAlgebra Γ) v

lemma GCAmbien.canonical_lift_single
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    letI : DecidableEq Γ := Classical.decEq Γ
    A.canonicalAlgebraLift (Finsupp.single g (1 : ZMod p)) =
      (A.canonicalUnit g : A.completedGroupAlgebra) := by
  classical
  let v : Γ →* A.completedGroupAlgebra :=
    (Units.coeHom A.completedGroupAlgebra).comp A.canonicalUnit
  change
    ((MonoidAlgebra.lift (ZMod p) A.completedGroupAlgebra Γ) v)
        ((MonoidAlgebra.of (ZMod p) Γ) g) =
      (A.canonicalUnit g : A.completedGroupAlgebra)
  simp [v]

noncomputable def GCAmbien.canon_group_algmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.CGMap := by
  classical
  refine ⟨A.canonicalAlgebraLift, ⟨?_⟩⟩
  intro g
  exact A.canonical_lift_single (p := p) (Γ := Γ) (s := s) (hs := hs) g

lemma GCAmbien.canongroup_algmap_alghom
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (A.canon_group_algmap
      (p := p) (Γ := Γ) (s := s) (hs := hs)).toAlgHom =
      A.canonicalAlgebraLift := by
  rfl

lemma GCAmbien.nonempty_canongroup_algmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Nonempty A.CGMap := by
  classical
  exact ⟨A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)⟩

lemma GCAmbien.nonemptygroup_algmap_compgroualg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (_hcomplete : A.CompletedAlgebra) :
    Nonempty A.CGMap := by
  exact A.nonempty_canongroup_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)

lemma GCAmbien.groupalg_maprangcont_inunitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (φ : A.CGMap) :
    φ.RangeContainedSpan := by
  classical
  let S : Submodule (ZMod p) A.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))
  have hsingle_mem :
      ∀ g : Γ, φ.toAlgHom (Finsupp.single g (1 : ZMod p)) ∈ S := by
    intro g
    have hunit_mem :
        (A.canonicalUnit g : A.completedGroupAlgebra) ∈ S := by
      exact Submodule.subset_span ⟨g, rfl⟩
    simpa [S] using
      (show
        φ.toAlgHom (Finsupp.single g (1 : ZMod p)) ∈ S from by
          rw [φ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) g]
          exact hunit_mem)
  have hmap_mem :
      ∀ x : MonoidAlgebra (ZMod p) Γ, φ.toAlgHom x ∈ S := by
    intro x
    refine Finsupp.induction_linear x ?hz ?hadd ?hsingle
    · have hzero :
          φ.toAlgHom (0 : MonoidAlgebra (ZMod p) Γ) =
            (0 : A.completedGroupAlgebra) := by
        exact map_zero φ.toAlgHom
      exact hzero.symm ▸ S.zero_mem
    · intro x y hx hy
      have hxy :
          φ.toAlgHom (x + y) =
            φ.toAlgHom x + φ.toAlgHom y := by
        exact map_add φ.toAlgHom x y
      rw [hxy]
      exact S.add_mem hx hy
    · intro g c
      by_cases hc : c = 0
      · have hzero :
            φ.toAlgHom (0 : MonoidAlgebra (ZMod p) Γ) =
              (0 : A.completedGroupAlgebra) := by
          exact map_zero φ.toAlgHom
        rw [hc, Finsupp.single_zero]
        exact hzero.symm ▸ S.zero_mem
      · have hbasis : φ.toAlgHom (Finsupp.single g (1 : ZMod p)) ∈ S :=
          hsingle_mem g
        have hsingle :
            φ.toAlgHom (Finsupp.single g c) =
              c • φ.toAlgHom (Finsupp.single g (1 : ZMod p)) := by
          rw [← map_smul]
          congr 1
          ext a
          by_cases ha : a = g
          · subst ha
            simp
          · simp [ha]
        rw [hsingle]
        exact S.smul_mem c hbasis
  intro y hy
  rcases hy with ⟨x, rfl⟩
  simpa [
    GCAmbien.CGMap.RangeContainedSpan,
    S
  ] using hmap_mem x

lemma GCAmbien.unitspan_subsetgroup_algmaprange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (φ : A.CGMap) :
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra) ⊆
      Set.range φ.toAlgHom := by
  classical
  let S : Set A.completedGroupAlgebra :=
    Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra)
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) S := by
    simpa [S] using hy
  refine Submodule.span_induction
    (s := S)
    (p := fun z _ => z ∈ Set.range φ.toAlgHom)
    ?mem ?zero ?add ?smul hyspan
  · intro z hz
    rcases hz with ⟨g, rfl⟩
    refine ⟨Finsupp.single g (1 : ZMod p), ?_⟩
    exact φ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) g
  · exact ⟨0, by simp⟩
  · intro x y _hx _hy hx_range hy_range
    rcases hx_range with ⟨x₀, rfl⟩
    rcases hy_range with ⟨y₀, rfl⟩
    exact ⟨x₀ + y₀, by simp [map_add]⟩
  · intro a x _hx hx_range
    rcases hx_range with ⟨x₀, rfl⟩
    refine ⟨a • x₀, ?_⟩
    rw [map_smul]

lemma GCAmbien.groupalg_maprange_equnitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (φ : A.CGMap) :
    Set.range φ.toAlgHom =
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  apply Set.Subset.antisymm
  · exact A.groupalg_maprangcont_inunitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ
  · exact A.unitspan_subsetgroup_algmaprange
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ

lemma GCAmbien.canonunit_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) ∈
      ((Submodule.span (ZMod p)
        (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  let S : Set A.completedGroupAlgebra :=
    Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra)
  have hg : (A.canonicalUnit g : A.completedGroupAlgebra) ∈ S := by
    exact ⟨g, rfl⟩
  have hspan :
      (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        Submodule.span (ZMod p) S :=
    Submodule.subset_span hg
  simpa [S] using hspan

lemma GCAmbien.one_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (1 : A.completedGroupAlgebra) ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  have hunit :
      (A.canonicalUnit 1 : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.canonunit_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs) 1
  simpa using hunit

lemma GCAmbien.algmap_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : ZMod p) :
    algebraMap (ZMod p) A.completedGroupAlgebra a ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  classical
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hspan :
      Set.range φ.toAlgHom =
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.groupalg_maprange_equnitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ
  have hconst_range :
      algebraMap (ZMod p) A.completedGroupAlgebra a ∈ Set.range φ.toAlgHom := by
    refine ⟨algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Γ) a, ?_⟩
    change φ.toAlgHom (Finsupp.single (1 : Γ) a) =
      algebraMap (ZMod p) A.completedGroupAlgebra a
    have hsingle :
        φ.toAlgHom (Finsupp.single (1 : Γ) a) =
          a • φ.toAlgHom (Finsupp.single (1 : Γ) (1 : ZMod p)) := by
      rw [← map_smul]
      congr 1
      ext g
      by_cases hg : g = 1
      · subst hg
        simp
      · simp [hg]
    have hbasis :
        φ.toAlgHom (Finsupp.single (1 : Γ) (1 : ZMod p)) =
          (1 : A.completedGroupAlgebra) := by
      rw [φ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) 1]
      simp
    calc
      φ.toAlgHom (Finsupp.single (1 : Γ) a)
          = a • φ.toAlgHom (Finsupp.single (1 : Γ) (1 : ZMod p)) := hsingle
      _ = a • (1 : A.completedGroupAlgebra) := by
          rw [hbasis]
      _ = algebraMap (ZMod p) A.completedGroupAlgebra a := by
          simp [Algebra.smul_def]
  rw [hspan] at hconst_range
  exact hconst_range

lemma GCAmbien.add_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra))
    (hy : y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra)) :
    x + y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  let S : Submodule (ZMod p) A.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))
  have hxS : x ∈ S := by
    simpa [S] using hx
  have hyS : y ∈ S := by
    simpa [S] using hy
  have hsum : x + y ∈ S :=
    S.add_mem hxS hyS
  simpa [S] using hsum

lemma GCAmbien.sub_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra))
    (hy : y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra)) :
    x - y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  let S : Submodule (ZMod p) A.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))
  have hxS : x ∈ S := by
    simpa [S] using hx
  have hyS : y ∈ S := by
    simpa [S] using hy
  have hsub : x - y ∈ S :=
    S.sub_mem hxS hyS
  simpa [S] using hsub

lemma GCAmbien.mul_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra))
    (hy : y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra)) :
    x * y ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  classical
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hspan :
      Set.range φ.toAlgHom =
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.groupalg_maprange_equnitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ
  have hxrange : x ∈ Set.range φ.toAlgHom := by
    rw [hspan]
    exact hx
  have hyrange : y ∈ Set.range φ.toAlgHom := by
    rw [hspan]
    exact hy
  rcases hxrange with ⟨x₀, rfl⟩
  rcases hyrange with ⟨y₀, rfl⟩
  have hprod_range :
      φ.toAlgHom (x₀ * y₀) ∈ Set.range φ.toAlgHom := by
    exact ⟨x₀ * y₀, rfl⟩
  rw [hspan] at hprod_range
  simpa [map_mul] using hprod_range

lemma GCAmbien.pow_memcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x : A.completedGroupAlgebra}
    (hx : x ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra))
    (m : ℕ) :
    x ^ m ∈
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  induction m with
  | zero =>
      simpa using
        A.one_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs)
  | succ m hm =>
      have hmul :
          x ^ m * x ∈
            ((Submodule.span (ZMod p)
              (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
                Set A.completedGroupAlgebra) :=
        A.mul_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs) hm hx
      simpa [pow_succ] using hmul

lemma GCAmbien.canonunit_subonemem_canonunitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
      ((Submodule.span (ZMod p)
        (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) := by
  have hunit :
      (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.canonunit_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs) g
  have hone :
      (1 : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.one_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs)
  exact
    A.sub_memcanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hunit hone

lemma GCAmbien.groupalg_mapdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (φ : A.CGMap)
    (hdense : A.DenseAlgebraSpan) :
    φ.HasDenseRange := by
  dsimp [
    GCAmbien.CGMap.HasDenseRange,
    GCAmbien.DenseAlgebraSpan
  ] at hdense ⊢
  rw [A.groupalg_maprange_equnitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ]
  exact hdense

namespace GCAmbien.CGMap

lemma alg_hom
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (φ ψ : A.CGMap) :
    φ.toAlgHom = ψ.toAlgHom := by
  classical
  apply DFunLike.ext
  intro x
  refine Finsupp.induction_linear x ?hz ?hadd ?hsingle
  · calc
      φ.toAlgHom (0 : MonoidAlgebra (ZMod p) Γ) = (0 : A.completedGroupAlgebra) := by
        exact map_zero φ.toAlgHom
      _ = ψ.toAlgHom (0 : MonoidAlgebra (ZMod p) Γ) := by
        exact (map_zero ψ.toAlgHom).symm
  · intro x y hx hy
    calc
      φ.toAlgHom (x + y) = φ.toAlgHom x + φ.toAlgHom y := by
        exact map_add φ.toAlgHom x y
      _ = ψ.toAlgHom x + ψ.toAlgHom y := by
        rw [hx, hy]
      _ = ψ.toAlgHom (x + y) := by
        exact (map_add ψ.toAlgHom x y).symm
  · intro g c
    have hφ_single :
        φ.toAlgHom (Finsupp.single g c) =
          c • φ.toAlgHom (Finsupp.single g (1 : ZMod p)) := by
      rw [← map_smul]
      congr 1
      ext a
      by_cases ha : a = g
      · subst ha
        simp
      · simp [ha]
    have hψ_single :
        ψ.toAlgHom (Finsupp.single g c) =
          c • ψ.toAlgHom (Finsupp.single g (1 : ZMod p)) := by
      rw [← map_smul]
      congr 1
      ext a
      by_cases ha : a = g
      · subst ha
        simp
      · simp [ha]
    have hbasis :
        φ.toAlgHom (Finsupp.single g (1 : ZMod p)) =
          ψ.toAlgHom (Finsupp.single g (1 : ZMod p)) := by
      rw [φ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) g]
      rw [ψ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) g]
    rw [hφ_single, hψ_single, hbasis]

lemma range_alg_hom
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    {φ ψ : A.CGMap}
    (h : φ.toAlgHom = ψ.toAlgHom) :
    Set.range φ.toAlgHom = Set.range ψ.toAlgHom := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [h]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [h]⟩

lemma dense_range_alg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    {φ ψ : A.CGMap}
    (h : φ.toAlgHom = ψ.toAlgHom)
    (hψ : ψ.HasDenseRange) :
    φ.HasDenseRange := by
  have hrange : Set.range φ.toAlgHom = Set.range ψ.toAlgHom :=
    range_alg_hom (p := p) (Γ := Γ) (s := s) (hs := hs) h
  dsimp [GCAmbien.CGMap.HasDenseRange] at hψ ⊢
  calc
    closure (Set.range φ.toAlgHom) = closure (Set.range ψ.toAlgHom) := by
      rw [hrange]
    _ = Set.univ := hψ

end GCAmbien.CGMap

def GCAmbien.DenseLiftRange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  closure (Set.range A.canonicalAlgebraLift) = Set.univ

lemma GCAmbien.canongroup_algmap_denserangelift
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseLiftRange) :
    (A.canon_group_algmap
      (p := p) (Γ := Γ) (s := s) (hs := hs)).HasDenseRange := by
  dsimp [
    GCAmbien.CGMap.HasDenseRange,
    GCAmbien.DenseLiftRange
  ] at hdense ⊢
  simpa [
    GCAmbien.canongroup_algmap_alghom
      (p := p) (Γ := Γ) (s := s) (hs := hs) A
  ] using hdense

lemma GCAmbien.groupalg_mapgroup_algliftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdenseLift : A.DenseLiftRange)
    (φ : A.CGMap) :
    φ.HasDenseRange := by
  let ψ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hψ : ψ.HasDenseRange :=
    A.canongroup_algmap_denserangelift
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift
  have hmaps : φ.toAlgHom = ψ.toAlgHom :=
    φ.alg_hom (p := p) (Γ := Γ) (s := s) (hs := hs) ψ
  exact
    GCAmbien.CGMap.dense_range_alg
      (p := p) (Γ := Γ) (s := s) (hs := hs) hmaps hψ

lemma GCAmbien.nonemptydense_groupalggroup_algliftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdenseLift : A.DenseLiftRange) :
    ∃ φ : A.CGMap, φ.HasDenseRange := by
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hφ : φ.HasDenseRange :=
    A.groupalg_mapgroup_algliftrange
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift φ
  exact ⟨φ, hφ⟩

lemma GCAmbien.groupalg_mapnonedens_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : ∃ ψ : A.CGMap, ψ.HasDenseRange)
    (φ : A.CGMap) :
    φ.HasDenseRange := by
  rcases H with ⟨ψ, hψ⟩
  have hmaps : φ.toAlgHom = ψ.toAlgHom :=
    φ.alg_hom (p := p) (Γ := Γ) (s := s) (hs := hs) ψ
  exact
    GCAmbien.CGMap.dense_range_alg
      (p := p) (Γ := Γ) (s := s) (hs := hs) hmaps hψ

lemma GCAmbien.densegroup_algnonedens_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : ∃ ψ : A.CGMap, ψ.HasDenseRange) :
    A.DenseLiftRange := by
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hφ : φ.HasDenseRange :=
    A.groupalg_mapnonedens_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) H φ
  dsimp [
    GCAmbien.CGMap.HasDenseRange,
    GCAmbien.DenseLiftRange
  ] at hφ ⊢
  simpa [
    φ,
    GCAmbien.canongroup_algmap_alghom
      (p := p) (Γ := Γ) (s := s) (hs := hs) A
  ] using hφ

lemma GCAmbien.nonedensgrou_algiffgroup_algliftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (∃ φ : A.CGMap, φ.HasDenseRange) ↔
      A.DenseLiftRange := by
  constructor
  · intro H
    exact
      A.densegroup_algnonedens_groupalgmap
        (p := p) (Γ := Γ) (s := s) (hs := hs) H
  · intro hdenseLift
    exact
      A.nonemptydense_groupalggroup_algliftrange
        (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift

def GCAmbien.DenseRawAlgebra
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI : DecidableEq Γ := Classical.decEq Γ
  ∃ φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] A.completedGroupAlgebra,
    (∀ g : Γ,
      φ (Finsupp.single g (1 : ZMod p)) =
        (A.canonicalUnit g : A.completedGroupAlgebra)) ∧
      closure (Set.range φ) = Set.univ

lemma GCAmbien.densegroup_algmapdense_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : ∃ φ : A.CGMap, φ.HasDenseRange) :
    A.DenseRawAlgebra := by
  classical
  rcases H with ⟨φ, hdense⟩
  refine ⟨φ.toAlgHom, ?_, ?_⟩
  · intro g
    exact φ.map_single_one (p := p) (Γ := Γ) (s := s) (hs := hs) g
  · dsimp [
      GCAmbien.CGMap.HasDenseRange
    ] at hdense
    exact hdense

lemma GCAmbien.nonemptydense_groupalgdense_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.DenseRawAlgebra) :
    ∃ φ : A.CGMap, φ.HasDenseRange := by
  classical
  rcases H with ⟨φ, hcompat, hdense⟩
  let ψ : A.CGMap := ⟨φ, ⟨hcompat⟩⟩
  have hψ : ψ.HasDenseRange := by
    dsimp [
      GCAmbien.CGMap.HasDenseRange,
      GCAmbien.CGMap.toAlgHom,
      ψ
    ]
    exact hdense
  exact ⟨ψ, hψ⟩

lemma GCAmbien.nonedensgrou_algiffdense_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (∃ φ : A.CGMap, φ.HasDenseRange) ↔
      A.DenseRawAlgebra := by
  constructor
  · intro H
    exact
      A.densegroup_algmapdense_groupalgmap
        (p := p) (Γ := Γ) (s := s) (hs := hs) H
  · intro Hraw
    exact
      A.nonemptydense_groupalgdense_groupalgmap
        (p := p) (Γ := Γ) (s := s) (hs := hs) Hraw

lemma GCAmbien.dense_lift_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdenseLift : A.DenseLiftRange) :
    A.DenseRawAlgebra := by
  classical
  refine ⟨A.canonicalAlgebraLift, ?_, ?_⟩
  · intro g
    exact
      A.canonical_lift_single
        (p := p) (Γ := Γ) (s := s) (hs := hs) g
  · simpa [
      GCAmbien.DenseLiftRange
    ] using hdenseLift

lemma GCAmbien.dense_range_raw
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hraw : A.DenseRawAlgebra) :
    A.DenseLiftRange := by
  have Hnonempty :
      ∃ φ : A.CGMap, φ.HasDenseRange :=
    A.nonemptydense_groupalgdense_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hraw
  exact
    A.densegroup_algnonedens_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hnonempty

lemma GCAmbien.dense_algebra_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.DenseRawAlgebra ↔
      A.DenseLiftRange := by
  constructor
  · intro Hraw
    exact
      A.dense_range_raw
        (p := p) (Γ := Γ) (s := s) (hs := hs) Hraw
  · intro hdenseLift
    exact
      A.dense_lift_range
        (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift

lemma GCAmbien.denseunit_alggroup_algliftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdenseLift : A.DenseLiftRange) :
    A.DenseAlgebraSpan := by
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hφ : φ.HasDenseRange :=
    A.canongroup_algmap_denserangelift
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift
  dsimp [
    GCAmbien.CGMap.HasDenseRange,
    GCAmbien.DenseAlgebraSpan
  ] at hφ ⊢
  rw [← A.groupalg_maprange_equnitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ]
  exact hφ

lemma GCAmbien.nonemptydense_groupalgdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    ∃ φ : A.CGMap, φ.HasDenseRange := by
  let φ : A.CGMap :=
    A.canon_group_algmap (p := p) (Γ := Γ) (s := s) (hs := hs)
  have hφ : φ.HasDenseRange :=
    A.groupalg_mapdense_unitalgspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ hdense
  exact ⟨φ, hφ⟩

lemma GCAmbien.densegroup_algrangedense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    A.DenseLiftRange := by
  have H :
      ∃ φ : A.CGMap, φ.HasDenseRange :=
    A.nonemptydense_groupalgdense_unitalgspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense
  exact
    A.densegroup_algnonedens_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) H

lemma GCAmbien.denserawgroup_algmapdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    A.DenseRawAlgebra := by
  have hdenseLift : A.DenseLiftRange :=
    A.densegroup_algrangedense_unitalgspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense
  exact
    A.dense_lift_range
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift

lemma GCAmbien.canongroupalg_mapdenranden_canunialgspa
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (φ : A.CGMap) :
    φ.HasDenseRange := by
  exact
    A.groupalg_mapdense_unitalgspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ hdense

def GCAmbien.DenseCanongroupAlgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∃ φ : A.CGMap, φ.HasDenseRange

lemma GCAmbien.densegroup_algdensegroup_algliftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdenseLift : A.DenseLiftRange) :
    A.DenseCanongroupAlgmap := by
  exact
    A.nonemptydense_groupalggroup_algliftrange
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift

lemma GCAmbien.densegroupalg_liftrangedense_cangroalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.DenseCanongroupAlgmap) :
    A.DenseLiftRange := by
  exact
    A.densegroup_algnonedens_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) H

lemma GCAmbien.groupalg_mapdense_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.DenseCanongroupAlgmap)
    (φ : A.CGMap) :
    φ.HasDenseRange := by
  exact
    A.groupalg_mapnonedens_groupalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) H φ

lemma GCAmbien.denseunit_algdense_groupalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.DenseCanongroupAlgmap) :
    A.DenseAlgebraSpan := by
  have hdenseLift : A.DenseLiftRange :=
    A.densegroupalg_liftrangedense_cangroalgmap
      (p := p) (Γ := Γ) (s := s) (hs := hs) H
  exact
    A.denseunit_alggroup_algliftrange
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdenseLift

lemma GCAmbien.complete_algext_existsinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hinputs : A.CompletedUniversalInputs) :
    A.CompletedExtensionExistence := by
  rcases Hinputs with ⟨Hext, Huniq⟩
  have Hext' : A.CompletedExtensionExistence := Hext
  have _Huniq' : A.CompletedExtensionUniqueness := Huniq
  exact Hext'

lemma GCAmbien.complete_algext_uniqinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hinputs : A.CompletedUniversalInputs) :
    A.CompletedExtensionUniqueness := by
  rcases Hinputs with ⟨Hext, Huniq⟩
  have _Hext' : A.CompletedExtensionExistence := Hext
  have Huniq' : A.CompletedExtensionUniqueness := Huniq
  exact Huniq'

lemma GCAmbien.alg_homeq_equnits
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (B : Type u) [Ring B] [Algebra (ZMod p) B]
    (Φ Ψ : A.completedGroupAlgebra →ₐ[ZMod p] B)
    (hΦΨ :
      ∀ g : Γ,
        Φ (A.canonicalUnit g : A.completedGroupAlgebra) =
          Ψ (A.canonicalUnit g : A.completedGroupAlgebra)) :
    ∀ x : A.completedGroupAlgebra,
      x ∈
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) →
        Φ x = Ψ x := by
  letI := A.instRing
  letI := A.instAlgebra
  let S : Set A.completedGroupAlgebra :=
    Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra)
  intro x hx
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [S] using hx
  change Φ x = Ψ x
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ => Φ y = Ψ y)
    ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    exact hΦΨ g
  · calc
      Φ (0 : A.completedGroupAlgebra) = (0 : B) := by
        exact map_zero Φ
      _ = Ψ (0 : A.completedGroupAlgebra) := by
        exact (map_zero Ψ).symm
  · intro x y _hx _hy hx_eq hy_eq
    calc
      Φ (x + y) = Φ x + Φ y := by
        exact map_add Φ x y
      _ = Ψ x + Ψ y := by
        rw [hx_eq, hy_eq]
      _ = Ψ (x + y) := by
        exact (map_add Ψ x y).symm
  · intro a x _hx hx_eq
    calc
      Φ (a • x) = a • Φ x := by
        rw [map_smul]
      _ = a • Ψ x := by
        rw [hx_eq]
      _ = Ψ (a • x) := by
        rw [map_smul]

lemma GCAmbien.alg_ext_subset
    {p : ℕ} [Fact p.Prime]
    {R B : Type u} [TopologicalSpace R] [Ring R] [Algebra (ZMod p) R]
    [TopologicalSpace B] [Ring B] [Algebra (ZMod p) B] [T2Space B]
    {S : Set R}
    (Φ Ψ : R →ₐ[ZMod p] B)
    (hΦcont : Continuous Φ)
    (hΨcont : Continuous Ψ)
    (hdense : closure S = Set.univ)
    (hS : ∀ x : R, x ∈ S → Φ x = Ψ x) :
    Φ = Ψ := by
  have hclosed : IsClosed {x : R | Φ x = Ψ x} :=
    isClosed_eq hΦcont hΨcont
  have hS_subset : S ⊆ {x : R | Φ x = Ψ x} := by
    intro x hx
    exact hS x hx
  have hclosure_subset : closure S ⊆ {x : R | Φ x = Ψ x} := by
    exact hclosed.closure_subset_iff.mpr hS_subset
  apply DFunLike.ext
  intro x
  have hxclosure : x ∈ closure S := by
    rw [hdense]
    exact Set.mem_univ x
  exact hclosure_subset hxclosure

lemma GCAmbien.completealg_extuniqunit_algspanaux
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [CompactSpace B] [TotallyDisconnectedSpace B]
    (v : Γ →* Units B)
    (_hv : Continuous v)
    (Φ Ψ : A.completedGroupAlgebra →ₐ[ZMod p] B)
    (hΦ : Continuous Φ ∧
      ∀ g : Γ,
        Φ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B))
    (hΨ : Continuous Ψ ∧
      ∀ g : Γ,
        Ψ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B)) :
    Φ = Ψ := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  have hunit_eq :
      ∀ g : Γ,
        Φ (A.canonicalUnit g : A.completedGroupAlgebra) =
          Ψ (A.canonicalUnit g : A.completedGroupAlgebra) := by
    intro g
    calc
      Φ (A.canonicalUnit g : A.completedGroupAlgebra) = (v g : B) := hΦ.2 g
      _ = Ψ (A.canonicalUnit g : A.completedGroupAlgebra) := by
        exact (hΨ.2 g).symm
  have hspan_eq :
      ∀ x : A.completedGroupAlgebra, x ∈ S → Φ x = Ψ x := by
    intro x hx
    exact
      A.alg_homeq_equnits
        B Φ Ψ hunit_eq x (by simpa [S] using hx)
  have hdenseS : closure S = Set.univ := by
    simpa [
      GCAmbien.DenseAlgebraSpan,
      S
    ] using hdense
  exact
    GCAmbien.alg_ext_subset
      (p := p) (R := A.completedGroupAlgebra) (B := B) (S := S)
      Φ Ψ hΦ.1 hΨ.1 hdenseS hspan_eq

lemma GCAmbien.completealg_extdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    A.CompletedExtensionUniqueness := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv Φ Ψ hΦ hΨ
  exact
    A.completealg_extuniqunit_algspanaux
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense B v hv Φ Ψ hΦ hΨ

lemma GCAmbien.canon_unitspan_subsetclosure
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra) ⊆
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  intro x hx
  exact subset_closure hx

lemma GCAmbien.canonunit_memclosure_canonunitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hspan :
      (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.canonunit_memcanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) g
  exact
    A.canon_unitspan_subsetclosure
      (p := p) (Γ := Γ) (s := s) (hs := hs) hspan

lemma GCAmbien.algmap_memclosure_canonunitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : ZMod p) :
    algebraMap (ZMod p) A.completedGroupAlgebra a ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hspan :
      algebraMap (ZMod p) A.completedGroupAlgebra a ∈
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.algmap_memcanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) a
  exact
    A.canon_unitspan_subsetclosure
      (p := p) (Γ := Γ) (s := s) (hs := hs) hspan

lemma GCAmbien.denseunit_algiff_foramemclos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.DenseAlgebraSpan ↔
      ∀ x : A.completedGroupAlgebra,
        x ∈ closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  constructor
  · intro hdense x
    have hxuniv : x ∈ (Set.univ : Set A.completedGroupAlgebra) :=
      Set.mem_univ x
    have hclosure : closure S = Set.univ := by
      simpa [GCAmbien.DenseAlgebraSpan, S]
        using hdense
    simp [hclosure, S]
  · intro hmem
    dsimp [GCAmbien.DenseAlgebraSpan]
    ext x
    constructor
    · intro _hx
      exact Set.mem_univ x
    · intro _hx
      simpa [S] using hmem x

lemma GCAmbien.notdense_unitiffexists_notmemclosure
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ¬ A.DenseAlgebraSpan ↔
      ∃ x : A.completedGroupAlgebra,
        x ∉ closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) := by
  classical
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  constructor
  · intro hnot
    by_contra hno
    have hforall : ∀ x : A.completedGroupAlgebra, x ∈ closure S := by
      intro x
      by_contra hx
      exact hno ⟨x, by simpa [S] using hx⟩
    exact hnot
      ((A.denseunit_algiff_foramemclos
        (p := p) (Γ := Γ) (s := s) (hs := hs)).2 (by
          intro x
          simpa [S] using hforall x))
  · rintro ⟨x, hx⟩ hdense
    have hxclosure :
        x ∈ closure S :=
      (A.denseunit_algiff_foramemclos
        (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hdense x
    exact hx (by simpa [S] using hxclosure)

lemma GCAmbien.notdense_unitclosed_propersuperset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {C : Set A.completedGroupAlgebra}
    (hCclosed : IsClosed C)
    (hspanC :
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C)
    (hproper : ∃ x : A.completedGroupAlgebra, x ∉ C) :
    ¬ A.DenseAlgebraSpan := by
  intro hdense
  rcases hproper with ⟨x, hxC⟩
  have hclosure_subset :
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) ⊆ C := by
    exact hCclosed.closure_subset_iff.mpr hspanC
  have hxclosure :
      x ∈ closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
    exact
      (A.denseunit_algiff_foramemclos
        (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hdense x
  exact hxC (hclosure_subset hxclosure)

lemma GCAmbien.exisclosprop_supenotdens_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hnot : ¬ A.DenseAlgebraSpan) :
    ∃ C : Set A.completedGroupAlgebra,
      IsClosed C ∧
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) ⊆ C ∧
        ∃ x : A.completedGroupAlgebra, x ∉ C := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  rcases
      (A.notdense_unitiffexists_notmemclosure
        (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hnot with
    ⟨x, hx⟩
  refine ⟨closure S, ?_, ?_, ?_⟩
  · exact isClosed_closure
  · intro y hy
    exact subset_closure hy
  · exact ⟨x, by simpa [S] using hx⟩

lemma GCAmbien.notdense_unitiffexists_clospropsupe
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ¬ A.DenseAlgebraSpan ↔
      ∃ C : Set A.completedGroupAlgebra,
        IsClosed C ∧
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) ⊆ C ∧
          ∃ x : A.completedGroupAlgebra, x ∉ C := by
  constructor
  · intro hnot
    exact
      A.exisclosprop_supenotdens_unitalgspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hnot
  · rintro ⟨C, hCclosed, hspanC, hproper⟩
    exact
      A.notdense_unitclosed_propersuperset
        (p := p) (Γ := Γ) (s := s) (hs := hs) hCclosed hspanC hproper

def GCAmbien.ClosedCanonunitSpanobstruction
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∃ C : Set A.completedGroupAlgebra,
    IsClosed C ∧
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C ∧
      ∃ x : A.completedGroupAlgebra, x ∉ C

lemma GCAmbien.closedunit_spanobstruction_iffnotdense
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.ClosedCanonunitSpanobstruction ↔
      ¬ A.DenseAlgebraSpan := by
  dsimp [
    GCAmbien.ClosedCanonunitSpanobstruction
  ]
  constructor
  · rintro ⟨C, hCclosed, hspanC, hproper⟩
    exact
      A.notdense_unitclosed_propersuperset
        (p := p) (Γ := Γ) (s := s) (hs := hs) hCclosed hspanC hproper
  · intro hnot
    exact
      A.exisclosprop_supenotdens_unitalgspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hnot

lemma GCAmbien.closedunit_spanobstruction_containsunit
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {C : Set A.completedGroupAlgebra}
    (hspanC :
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) ∈ C := by
  have hspan :
      (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.canonunit_memcanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) g
  exact hspanC hspan

lemma GCAmbien.closedunit_spanobstruction_containsalgmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {C : Set A.completedGroupAlgebra}
    (hspanC :
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C)
    (a : ZMod p) :
    algebraMap (ZMod p) A.completedGroupAlgebra a ∈ C := by
  have hspan :
      algebraMap (ZMod p) A.completedGroupAlgebra a ∈
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.algmap_memcanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) a
  exact hspanC hspan

lemma GCAmbien.closedunit_spanobstcont_unitsubone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {C : Set A.completedGroupAlgebra}
    (hspanC :
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈ C := by
  have hspan :
      (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
        ((Submodule.span (ZMod p)
          (Set.range fun h : Γ => (A.canonicalUnit h : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.canonunit_subonemem_canonunitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) g
  exact hspanC hspan

lemma GCAmbien.existsopen_disjointclosed_propersuperset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {C : Set A.completedGroupAlgebra}
    (hCclosed : IsClosed C)
    (hspanC :
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra) ⊆ C)
    (hproper : ∃ x : A.completedGroupAlgebra, x ∉ C) :
    ∃ O : Set A.completedGroupAlgebra,
      IsOpen O ∧
        (∃ x : A.completedGroupAlgebra, x ∈ O) ∧
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) ∩ O = ∅ := by
  refine ⟨Cᶜ, ?_, ?_, ?_⟩
  · exact hCclosed.isOpen_compl
  · rcases hproper with ⟨x, hxC⟩
    exact ⟨x, hxC⟩
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hyspan, hyCcompl⟩
      exact False.elim (hyCcompl (hspanC hyspan))
    · intro hy
      cases hy

lemma GCAmbien.exisopendisj_spannotdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hnot : ¬ A.DenseAlgebraSpan) :
    ∃ O : Set A.completedGroupAlgebra,
      IsOpen O ∧
        (∃ x : A.completedGroupAlgebra, x ∈ O) ∧
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) ∩ O = ∅ := by
  rcases
      A.exisclosprop_supenotdens_unitalgspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hnot with
    ⟨C, hCclosed, hspanC, hproper⟩
  exact
    A.existsopen_disjointclosed_propersuperset
      (p := p) (Γ := Γ) (s := s) (hs := hs) hCclosed hspanC hproper

lemma GCAmbien.exisopendisj_closurenotdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hnot : ¬ A.DenseAlgebraSpan) :
    ∃ O : Set A.completedGroupAlgebra,
      IsOpen O ∧
        (∃ x : A.completedGroupAlgebra, x ∈ O) ∧
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) ∩ O = ∅ := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  rcases
      (A.notdense_unitiffexists_notmemclosure
        (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hnot with
    ⟨x, hx⟩
  refine ⟨(closure S)ᶜ, ?_, ?_, ?_⟩
  · exact isClosed_closure.isOpen_compl
  · exact ⟨x, by simpa [S] using hx⟩
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hycl, hycompl⟩
      exact False.elim (hycompl hycl)
    · intro hy
      cases hy

lemma GCAmbien.addmem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra))
    (hy : y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra)) :
    x + y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  let C : Set A.completedGroupAlgebra := closure S
  have hCclosed : IsClosed C := by
    simp [C]
  have hxC : x ∈ C := by
    simpa [S, C] using hx
  have hyC : y ∈ C := by
    simpa [S, C] using hy
  have hspan_add_right :
      ∀ z : A.completedGroupAlgebra, z ∈ S → z + y ∈ C := by
    intro z hz
    let T : Set A.completedGroupAlgebra := {w | z + w ∈ C}
    have hTclosed : IsClosed T := by
      change IsClosed ((fun w : A.completedGroupAlgebra => z + w) ⁻¹' C)
      exact hCclosed.preimage
        (by
          simpa using
            ((continuous_const.add continuous_id) :
              Continuous fun w : A.completedGroupAlgebra => z + w))
    have hSsubsetT : S ⊆ T := by
      intro w hw
      have hsum :
          z + w ∈
            ((Submodule.span (ZMod p)
              (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
                Set A.completedGroupAlgebra) := by
        exact
          A.add_memcanon_unitspan
            (p := p) (Γ := Γ) (s := s) (hs := hs)
            (by simpa [S] using hz) (by simpa [S] using hw)
      exact subset_closure (by simpa [S, C] using hsum)
    have hclosure_subset_T : closure S ⊆ T :=
      closure_minimal hSsubsetT hTclosed
    exact hclosure_subset_T (by simpa [C] using hyC)
  let T : Set A.completedGroupAlgebra := {z | z + y ∈ C}
  have hTclosed : IsClosed T := by
    change IsClosed ((fun z : A.completedGroupAlgebra => z + y) ⁻¹' C)
    exact hCclosed.preimage
      (by
        simpa using
          ((continuous_id.add continuous_const) :
            Continuous fun z : A.completedGroupAlgebra => z + y))
  have hSsubsetT : S ⊆ T := by
    intro z hz
    exact hspan_add_right z hz
  have hclosure_subset_T : closure S ⊆ T :=
    closure_minimal hSsubsetT hTclosed
  have hxy : x + y ∈ C :=
    hclosure_subset_T (by simpa [C] using hxC)
  simpa [S, C] using hxy

lemma GCAmbien.mulmem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra))
    (hy : y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra)) :
    x * y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  let C : Set A.completedGroupAlgebra := closure S
  have hCclosed : IsClosed C := by
    simp [C]
  have hxC : x ∈ C := by
    simpa [S, C] using hx
  have hyC : y ∈ C := by
    simpa [S, C] using hy
  have hspan_mul_right :
      ∀ z : A.completedGroupAlgebra, z ∈ S → z * y ∈ C := by
    intro z hz
    let T : Set A.completedGroupAlgebra := {w | z * w ∈ C}
    have hTclosed : IsClosed T := by
      change IsClosed ((fun w : A.completedGroupAlgebra => z * w) ⁻¹' C)
      exact hCclosed.preimage
        (by
          simpa using
            ((continuous_const.mul continuous_id) :
              Continuous fun w : A.completedGroupAlgebra => z * w))
    have hSsubsetT : S ⊆ T := by
      intro w hw
      have hprod :
          z * w ∈
            ((Submodule.span (ZMod p)
              (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
                Set A.completedGroupAlgebra) := by
        exact
          A.mul_memcanon_unitspan
            (p := p) (Γ := Γ) (s := s) (hs := hs)
            (by simpa [S] using hz) (by simpa [S] using hw)
      exact subset_closure (by simpa [S, C] using hprod)
    have hclosure_subset_T : closure S ⊆ T :=
      closure_minimal hSsubsetT hTclosed
    exact hclosure_subset_T (by simpa [C] using hyC)
  let T : Set A.completedGroupAlgebra := {z | z * y ∈ C}
  have hTclosed : IsClosed T := by
    change IsClosed ((fun z : A.completedGroupAlgebra => z * y) ⁻¹' C)
    exact hCclosed.preimage
      (by
        simpa using
          ((continuous_id.mul continuous_const) :
            Continuous fun z : A.completedGroupAlgebra => z * y))
  have hSsubsetT : S ⊆ T := by
    intro z hz
    exact hspan_mul_right z hz
  have hclosure_subset_T : closure S ⊆ T :=
    closure_minimal hSsubsetT hTclosed
  have hxy : x * y ∈ C :=
    hclosure_subset_T (by simpa [C] using hxC)
  simpa [S, C] using hxy

lemma GCAmbien.powmem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra))
    (m : ℕ) :
    x ^ m ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  induction m with
  | zero =>
      have hone :
          (1 : A.completedGroupAlgebra) ∈
            ((Submodule.span (ZMod p)
              (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
                Set A.completedGroupAlgebra) :=
        A.one_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs)
      simpa using subset_closure hone
  | succ m hm =>
      have hmul :
          x ^ m * x ∈
            closure
              ((Submodule.span (ZMod p)
                (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
                  Set A.completedGroupAlgebra) :=
        A.mulmem_closurecanon_unitspan
          (p := p) (Γ := Γ) (s := s) (hs := hs) hm hx
      simpa [pow_succ] using hmul

lemma GCAmbien.zeromem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (0 : A.completedGroupAlgebra) ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hspan :
      (0 : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
    exact (Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))).zero_mem
  exact subset_closure hspan

lemma GCAmbien.onemem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (1 : A.completedGroupAlgebra) ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hspan :
      (1 : A.completedGroupAlgebra) ∈
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) :=
    A.one_memcanon_unitspan (p := p) (Γ := Γ) (s := s) (hs := hs)
  exact subset_closure hspan

lemma GCAmbien.smulmem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : ZMod p)
    {x : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra)) :
    a • x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hscalar :
      algebraMap (ZMod p) A.completedGroupAlgebra a ∈
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) :=
    A.algmap_memclosure_canonunitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) a
  have hmul :
      algebraMap (ZMod p) A.completedGroupAlgebra a * x ∈
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) :=
    A.mulmem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hscalar hx
  simpa [Algebra.smul_def] using hmul

lemma GCAmbien.negmem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra)) :
    -x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hsmul :
      (-1 : ZMod p) • x ∈
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) :=
    A.smulmem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) (-1 : ZMod p) hx
  simpa using hsmul

lemma GCAmbien.submem_closurecanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra))
    (hy : y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra)) :
    x - y ∈
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := by
  have hneg :
      -y ∈
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) :=
    A.negmem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hy
  have hadd :
      x + -y ∈
        closure
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
              Set A.completedGroupAlgebra) :=
    A.addmem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hx hneg
  simpa [sub_eq_add_neg] using hadd

noncomputable def GCAmbien.canon_unitspan_closuresubmodu
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Submodule (ZMod p) A.completedGroupAlgebra where
  carrier :=
    closure
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra)
  zero_mem' :=
    A.zeromem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  add_mem' := by
    intro x y hx hy
    exact
      A.addmem_closurecanon_unitspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hx hy
  smul_mem' := by
    intro a x hx
    exact
      A.smulmem_closurecanon_unitspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) a hx

noncomputable def GCAmbien.canon_unitspan_closuresubalge
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Subalgebra (ZMod p) A.completedGroupAlgebra where
  carrier :=
    closure
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
          Set A.completedGroupAlgebra)
  zero_mem' :=
    A.zeromem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  one_mem' :=
    A.onemem_closurecanon_unitspan
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  add_mem' := by
    intro x y hx hy
    exact
      A.addmem_closurecanon_unitspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hx hy
  mul_mem' := by
    intro x y hx hy
    exact
      A.mulmem_closurecanon_unitspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) hx hy
  algebraMap_mem' := by
    intro a
    exact
      A.algmap_memclosure_canonunitspan
        (p := p) (Γ := Γ) (s := s) (hs := hs) a

lemma GCAmbien.canonunit_spanclosure_submodulecoe
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ((A.canon_unitspan_closuresubmodu
      (p := p) (Γ := Γ) (s := s) (hs := hs)) :
        Set A.completedGroupAlgebra) =
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := rfl

lemma GCAmbien.canonunit_spanclosure_subalgebracoe
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ((A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) :
        Set A.completedGroupAlgebra) =
      closure
        ((Submodule.span (ZMod p)
          (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
            Set A.completedGroupAlgebra) := rfl

lemma GCAmbien.closedcanon_unitspan_closuresubalge
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    IsClosed
      (((A.canon_unitspan_closuresubalge
        (p := p) (Γ := Γ) (s := s) (hs := hs)) :
          Set A.completedGroupAlgebra)) := by
  rw [A.canonunit_spanclosure_subalgebracoe
    (p := p) (Γ := Γ) (s := s) (hs := hs)]
  exact isClosed_closure

lemma GCAmbien.canonunit_spansubset_closuresubalge
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra) ⊆
      ((A.canon_unitspan_closuresubalge
        (p := p) (Γ := Γ) (s := s) (hs := hs)) :
          Set A.completedGroupAlgebra) := by
  intro x hx
  rw [A.canonunit_spanclosure_subalgebracoe
    (p := p) (Γ := Γ) (s := s) (hs := hs)]
  exact subset_closure hx

lemma GCAmbien.denseunit_algiff_clossubaeq
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.DenseAlgebraSpan ↔
      ((A.canon_unitspan_closuresubalge
        (p := p) (Γ := Γ) (s := s) (hs := hs)) :
          Set A.completedGroupAlgebra) = Set.univ := by
  rw [A.canonunit_spanclosure_subalgebracoe
    (p := p) (Γ := Γ) (s := s) (hs := hs)]
  rfl

lemma GCAmbien.notdense_unitiff_clossubaprop
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    ¬ A.DenseAlgebraSpan ↔
      ∃ x : A.completedGroupAlgebra,
        x ∉
          ((A.canon_unitspan_closuresubalge
            (p := p) (Γ := Γ) (s := s) (hs := hs)) :
              Set A.completedGroupAlgebra) := by
  rw [A.canonunit_spanclosure_subalgebracoe
    (p := p) (Γ := Γ) (s := s) (hs := hs)]
  exact
    A.notdense_unitiffexists_notmemclosure
      (p := p) (Γ := Γ) (s := s) (hs := hs)

noncomputable def GCAmbien.canonunit_spanclosure_subalgebraunit
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    Units (A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) where
  val :=
    ⟨(A.canonicalUnit g : A.completedGroupAlgebra), by
      change (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        ((A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs)) :
            Set A.completedGroupAlgebra)
      rw [A.canonunit_spanclosure_subalgebracoe
        (p := p) (Γ := Γ) (s := s) (hs := hs)]
      exact
        A.canonunit_memclosure_canonunitspan
          (p := p) (Γ := Γ) (s := s) (hs := hs) g⟩
  inv :=
    ⟨((A.canonicalUnit g)⁻¹ : Units A.completedGroupAlgebra), by
      change (((A.canonicalUnit g)⁻¹ : Units A.completedGroupAlgebra) :
          A.completedGroupAlgebra) ∈
        ((A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs)) :
            Set A.completedGroupAlgebra)
      rw [A.canonunit_spanclosure_subalgebracoe
        (p := p) (Γ := Γ) (s := s) (hs := hs)]
      have hinv :
          (((A.canonicalUnit g⁻¹ : Units A.completedGroupAlgebra) :
              A.completedGroupAlgebra)) ∈
            closure
              ((Submodule.span (ZMod p)
                (Set.range fun h : Γ =>
                  (A.canonicalUnit h : A.completedGroupAlgebra))) :
                    Set A.completedGroupAlgebra) :=
        A.canonunit_memclosure_canonunitspan
          (p := p) (Γ := Γ) (s := s) (hs := hs) g⁻¹
      simpa using hinv⟩
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

lemma GCAmbien.canonunit_spanclosure_subaunitcoe
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (((A.canonunit_spanclosure_subalgebraunit
      (p := p) (Γ := Γ) (s := s) (hs := hs) g :
        Units (A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs))) :
          A.canon_unitspan_closuresubalge
            (p := p) (Γ := Γ) (s := s) (hs := hs)) :
        A.completedGroupAlgebra) =
      (A.canonicalUnit g : A.completedGroupAlgebra) := rfl

noncomputable def GCAmbien.canonunit_spanclosure_subaunithom
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Γ →* Units (A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) where
  toFun := fun g =>
    A.canonunit_spanclosure_subalgebraunit
      (p := p) (Γ := Γ) (s := s) (hs := hs) g
  map_one' := by
    apply Units.ext
    ext
    simp [GCAmbien.canonunit_spanclosure_subalgebraunit]
  map_mul' := by
    intro g h
    apply Units.ext
    ext
    simp [GCAmbien.canonunit_spanclosure_subalgebraunit]

lemma GCAmbien.canonunit_spanclossuba_unithomcoe
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (((A.canonunit_spanclosure_subaunithom
      (p := p) (Γ := Γ) (s := s) (hs := hs) g :
        Units (A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs))) :
          A.canon_unitspan_closuresubalge
            (p := p) (Γ := Γ) (s := s) (hs := hs)) :
        A.completedGroupAlgebra) =
      (A.canonicalUnit g : A.completedGroupAlgebra) := rfl

lemma GCAmbien.toporing_unitspan_closuresubalge
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    IsTopologicalRing (A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) := by
  let C : Subalgebra (ZMod p) A.completedGroupAlgebra :=
    A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  change IsTopologicalRing C
  have hcont_add : Continuous fun z : C × C => z.1 + z.2 := by
    have hambient :
        Continuous fun z : C × C =>
          ((z.1 : A.completedGroupAlgebra) + (z.2 : A.completedGroupAlgebra)) :=
      (continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd)
    have hsub :
        Continuous fun z : C × C =>
          (⟨((z.1 : A.completedGroupAlgebra) + (z.2 : A.completedGroupAlgebra)),
            C.add_mem z.1.2 z.2.2⟩ : C) :=
      Continuous.subtype_mk hambient (by
        intro z
        exact C.add_mem z.1.2 z.2.2)
    simpa using hsub
  have hcont_mul : Continuous fun z : C × C => z.1 * z.2 := by
    have hambient :
        Continuous fun z : C × C =>
          ((z.1 : A.completedGroupAlgebra) * (z.2 : A.completedGroupAlgebra)) :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    have hsub :
        Continuous fun z : C × C =>
          (⟨((z.1 : A.completedGroupAlgebra) * (z.2 : A.completedGroupAlgebra)),
            C.mul_mem z.1.2 z.2.2⟩ : C) :=
      Continuous.subtype_mk hambient (by
        intro z
        exact C.mul_mem z.1.2 z.2.2)
    simpa using hsub
  have hcont_neg : Continuous fun z : C => -z := by
    have hambient :
        Continuous fun z : C => -((z : C) : A.completedGroupAlgebra) :=
      continuous_neg.comp continuous_subtype_val
    have hsub :
        Continuous fun z : C =>
          (⟨-((z : C) : A.completedGroupAlgebra), by
            change -((z : C) : A.completedGroupAlgebra) ∈ (C : Set A.completedGroupAlgebra)
            dsimp [C]
            rw [A.canonunit_spanclosure_subalgebracoe
              (p := p) (Γ := Γ) (s := s) (hs := hs)]
            exact
              A.negmem_closurecanon_unitspan
                (p := p) (Γ := Γ) (s := s) (hs := hs) (by
                  rw [← A.canonunit_spanclosure_subalgebracoe
                    (p := p) (Γ := Γ) (s := s) (hs := hs)]
                  exact z.2)⟩ : C) :=
      Continuous.subtype_mk hambient (by
        intro z
        change -((z : C) : A.completedGroupAlgebra) ∈ (C : Set A.completedGroupAlgebra)
        dsimp [C]
        rw [A.canonunit_spanclosure_subalgebracoe
          (p := p) (Γ := Γ) (s := s) (hs := hs)]
        exact
          A.negmem_closurecanon_unitspan
            (p := p) (Γ := Γ) (s := s) (hs := hs) (by
              rw [← A.canonunit_spanclosure_subalgebracoe
                (p := p) (Γ := Γ) (s := s) (hs := hs)]
              exact z.2))
    simpa using hsub
  haveI : ContinuousAdd C := ContinuousAdd.mk hcont_add
  haveI : ContinuousMul C := ContinuousMul.mk hcont_mul
  haveI : ContinuousNeg C := ContinuousNeg.mk hcont_neg
  haveI : IsTopologicalSemiring C := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

lemma GCAmbien.completespace_canonunit_spanclossuba
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    CompleteSpace (A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) := by
  have hclosed :
      IsClosed
        (((A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs)) :
            Set A.completedGroupAlgebra)) :=
    A.closedcanon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  exact hclosed.isComplete.completeSpace_coe

lemma GCAmbien.compactspace_canonunit_spanclossuba
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    CompactSpace (A.canon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)) := by
  have hclosed :
      IsClosed
        (((A.canon_unitspan_closuresubalge
          (p := p) (Γ := Γ) (s := s) (hs := hs)) :
            Set A.completedGroupAlgebra)) :=
    A.closedcanon_unitspan_closuresubalge
      (p := p) (Γ := Γ) (s := s) (hs := hs)
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

lemma GCAmbien.densegroupalg_mapdensecanon_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    A.DenseCanongroupAlgmap := by
  exact
    A.nonemptydense_groupalgdense_unitalgspan
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense

lemma GCAmbien.denseunit_alggroup_algmap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (φ : A.CGMap)
    (hspan : φ.RangeContainedSpan)
    (hdense : φ.HasDenseRange) :
    A.DenseAlgebraSpan := by
  let S : Set A.completedGroupAlgebra :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))) :
        Set A.completedGroupAlgebra)
  have hclosure_mono : closure (Set.range φ.toAlgHom) ⊆ closure S := by
    exact
      closure_mono (by
        simpa [S,
          GCAmbien.CGMap.RangeContainedSpan]
          using hspan)
  change closure S = Set.univ
  ext x
  constructor
  · intro _hx
    exact Set.mem_univ x
  · intro _hx
    have hx_dense : x ∈ closure (Set.range φ.toAlgHom) := by
      rw [hdense]
      exact Set.mem_univ x
    exact hclosure_mono hx_dense

lemma GCAmbien.completedense_quotlayer_compdensambi
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : A.CompletedDenseAmbient) :
    A.CompleteDenseQuotlayer Q := by
  rcases H with ⟨hcomplete, hdense⟩
  have hcomplete' : A.CompletedAlgebra := hcomplete
  have hdense' : A.DenseAlgebraSpan := hdense
  exact ⟨hcomplete', hdense'⟩

lemma GCAmbien.existscomplete_densequot_topoaugquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hambient : A.CompletedDenseAmbient)
    (hTop : A.TopoAugQuot n) :
    ∃ Q : DCLayer
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      A.CompleteDenseQuotlayer Q := by
  rcases hTop with ⟨Qalg, hTopQ⟩
  rcases hTopQ with ⟨Top⟩
  let Qaug : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Qaug with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let Qlayer : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qaug.toQuotientLayer R U
  have Hlayer : A.CompleteDenseQuotlayer Qlayer :=
    A.completedense_quotlayer_compdensambi
      (p := p) (Γ := Γ) (s := s) (hs := hs) Qlayer Hambient
  exact ⟨Qlayer, Hlayer⟩

structure DCCarrie
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Type (u + 1) where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra (ZMod p) carrier
  instUniformSpace : UniformSpace carrier
  topologicalRing :
    letI := instRing
    letI := instAlgebra
    letI := instUniformSpace
    PLift (IsTopologicalRing carrier)
  instCompleteSpace :
    letI := instUniformSpace
    PLift (CompleteSpace carrier)
  t2Space :
    letI := instUniformSpace
    PLift (T2Space carrier)
  instCompactSpace :
    letI := instUniformSpace
    PLift (CompactSpace carrier)
  totallyDisconnected :
    letI := instUniformSpace
    PLift (TotallyDisconnectedSpace carrier)
  canonicalUnit :
    letI := instRing
    Γ →* Units carrier
  canonicalUnit_continuous :
    letI := instRing
    letI := instUniformSpace
    PLift (Continuous canonicalUnit)

namespace DCCarrie

instance instCarrierRing
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Ring K.carrier :=
  K.instRing

instance instCarrierAlgebra
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Algebra (ZMod p) K.carrier :=
  K.instAlgebra

instance carrierUniformSpace
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    UniformSpace K.carrier :=
  K.instUniformSpace

instance instCarrierTopological
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    IsTopologicalRing K.carrier :=
  K.topologicalRing.down

instance instCarrierSpace
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    CompleteSpace K.carrier :=
  K.instCompleteSpace.down

instance carrierTSpace
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    T2Space K.carrier :=
  K.t2Space.down

instance carrierCompactSpace
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    CompactSpace K.carrier :=
  K.instCompactSpace.down

instance carrierDisconnectedSpace
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    TotallyDisconnectedSpace K.carrier :=
  K.totallyDisconnected.down

def HasUniversalProperty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  ∀ (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
      [CompactSpace B] [TotallyDisconnectedSpace B],
    ∀ v : Γ →* Units B,
      Continuous v →
        ∃! Φ : K.carrier →ₐ[ZMod p] B,
          Continuous Φ ∧
            ∀ g : Γ,
              Φ (K.canonicalUnit g : K.carrier) = (v g : B)

def DenseAlgebraSpan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier)) :
        Set K.carrier)) = Set.univ

def HasExtensionProperty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  ∀ (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
      [CompactSpace B] [TotallyDisconnectedSpace B],
    ∀ v : Γ →* Units B,
      Continuous v →
        ∃ Φ : K.carrier →ₐ[ZMod p] B,
          Continuous Φ ∧
            ∀ g : Γ,
              Φ (K.canonicalUnit g : K.carrier) = (v g : B)

def DenseRawAlgebra
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  letI : DecidableEq Γ := Classical.decEq Γ
  ∃ φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier,
    (∀ g : Γ,
      φ (Finsupp.single g (1 : ZMod p)) =
        (K.canonicalUnit g : K.carrier)) ∧
      closure (Set.range φ) = Set.univ

noncomputable def canonicalAlgebraLift
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    letI := K.instRing
    letI := K.instAlgebra
    letI : DecidableEq Γ := Classical.decEq Γ
    MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier :=
  letI := K.instRing
  letI := K.instAlgebra
  letI : DecidableEq Γ := Classical.decEq Γ
  let v : Γ →* K.carrier :=
    (Units.coeHom K.carrier).comp K.canonicalUnit
  (MonoidAlgebra.lift (ZMod p) K.carrier Γ) v

lemma canonical_lift_single
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    letI := K.instRing
    letI := K.instAlgebra
    letI : DecidableEq Γ := Classical.decEq Γ
    K.canonicalAlgebraLift (Finsupp.single g (1 : ZMod p)) =
      (K.canonicalUnit g : K.carrier) := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  let v : Γ →* K.carrier :=
    (Units.coeHom K.carrier).comp K.canonicalUnit
  change
    ((MonoidAlgebra.lift (ZMod p) K.carrier Γ) v)
        ((MonoidAlgebra.of (ZMod p) Γ) g) =
      (K.canonicalUnit g : K.carrier)
  simp [v]

def DenseLiftRange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  closure (Set.range K.canonicalAlgebraLift) = Set.univ

lemma dense_lift_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (hdenseLift : K.DenseLiftRange) :
    K.DenseRawAlgebra := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  refine ⟨K.canonicalAlgebraLift, ?_, ?_⟩
  · intro g
    exact K.canonical_lift_single g
  · simpa [
      DCCarrie.DenseLiftRange
    ] using hdenseLift

lemma raw_algebra_lift
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier)
    (hcompat :
      ∀ g : Γ,
        φ (Finsupp.single g (1 : ZMod p)) =
          (K.canonicalUnit g : K.carrier)) :
    φ = K.canonicalAlgebraLift := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  apply DFunLike.ext
  intro x
  refine Finsupp.induction_linear x ?hz ?hadd ?hsingle
  · calc
      φ (0 : MonoidAlgebra (ZMod p) Γ) = (0 : K.carrier) := by
        exact map_zero φ
      _ = K.canonicalAlgebraLift (0 : MonoidAlgebra (ZMod p) Γ) := by
        exact (map_zero K.canonicalAlgebraLift).symm
  · intro x y hx hy
    calc
      φ (x + y) = φ x + φ y := by
        exact map_add φ x y
      _ = K.canonicalAlgebraLift x + K.canonicalAlgebraLift y := by
        rw [hx, hy]
      _ = K.canonicalAlgebraLift (x + y) := by
        exact (map_add K.canonicalAlgebraLift x y).symm
  · intro g c
    have hφ_single :
        φ (Finsupp.single g c) =
          c • φ (Finsupp.single g (1 : ZMod p)) := by
      rw [← map_smul]
      congr 1
      ext a
      by_cases ha : a = g
      · subst ha
        simp
      · simp [ha]
    have hlift_single :
        K.canonicalAlgebraLift (Finsupp.single g c) =
          c • K.canonicalAlgebraLift (Finsupp.single g (1 : ZMod p)) := by
      rw [← map_smul]
      congr 1
      ext a
      by_cases ha : a = g
      · subst ha
        simp
      · simp [ha]
    have hbasis :
        φ (Finsupp.single g (1 : ZMod p)) =
          K.canonicalAlgebraLift (Finsupp.single g (1 : ZMod p)) := by
      rw [hcompat g]
      exact (K.canonical_lift_single g).symm
    rw [hφ_single, hlift_single, hbasis]

lemma dense_range_raw
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (Hraw : K.DenseRawAlgebra) :
    K.DenseLiftRange := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  rcases Hraw with ⟨φ, hcompat, hdense⟩
  have heq : φ = K.canonicalAlgebraLift :=
    K.raw_algebra_lift φ hcompat
  dsimp
    [DCCarrie.DenseLiftRange]
  rw [← heq]
  exact hdense

lemma dense_algebra_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    K.DenseRawAlgebra ↔
      K.DenseLiftRange := by
  constructor
  · intro Hraw
    exact K.dense_range_raw Hraw
  · intro hdenseLift
    exact K.dense_lift_range hdenseLift

lemma raw_contained_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier)
    (hcompat :
      ∀ g : Γ,
        φ (Finsupp.single g (1 : ZMod p)) =
          (K.canonicalUnit g : K.carrier)) :
    Set.range φ ⊆
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))) :
          Set K.carrier) := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  let S : Submodule (ZMod p) K.carrier :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))
  have hsingle_mem :
      ∀ g : Γ, φ (Finsupp.single g (1 : ZMod p)) ∈ S := by
    intro g
    have hunit_mem :
        (K.canonicalUnit g : K.carrier) ∈ S := by
      exact Submodule.subset_span ⟨g, rfl⟩
    rw [hcompat g]
    exact hunit_mem
  have hmap_mem :
      ∀ x : MonoidAlgebra (ZMod p) Γ, φ x ∈ S := by
    intro x
    refine Finsupp.induction_linear x ?hz ?hadd ?hsingle
    · have hzero : φ (0 : MonoidAlgebra (ZMod p) Γ) = (0 : K.carrier) := by
        exact map_zero φ
      exact hzero.symm ▸ S.zero_mem
    · intro x y hx hy
      have hxy : φ (x + y) = φ x + φ y := by
        exact map_add φ x y
      rw [hxy]
      exact S.add_mem hx hy
    · intro g c
      by_cases hc : c = 0
      · have hzero : φ (0 : MonoidAlgebra (ZMod p) Γ) = (0 : K.carrier) := by
          exact map_zero φ
        rw [hc, Finsupp.single_zero]
        exact hzero.symm ▸ S.zero_mem
      · have hbasis : φ (Finsupp.single g (1 : ZMod p)) ∈ S :=
          hsingle_mem g
        have hsingle :
            φ (Finsupp.single g c) =
              c • φ (Finsupp.single g (1 : ZMod p)) := by
          rw [← map_smul]
          congr 1
          ext a
          by_cases ha : a = g
          · subst ha
            simp
          · simp [ha]
        rw [hsingle]
        exact S.smul_mem c hbasis
  intro y hy
  rcases hy with ⟨x, rfl⟩
  simpa [S] using hmap_mem x

lemma canonical_subset_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier)
    (hcompat :
      ∀ g : Γ,
        φ (Finsupp.single g (1 : ZMod p)) =
          (K.canonicalUnit g : K.carrier)) :
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))) :
        Set K.carrier) ⊆
      Set.range φ := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  let S : Set K.carrier :=
    Set.range fun g : Γ => (K.canonicalUnit g : K.carrier)
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) S := by
    simpa [S] using hy
  refine Submodule.span_induction
    (s := S)
    (p := fun z _ => z ∈ Set.range φ)
    ?mem ?zero ?add ?smul hyspan
  · intro z hz
    rcases hz with ⟨g, rfl⟩
    refine ⟨Finsupp.single g (1 : ZMod p), ?_⟩
    exact hcompat g
  · exact ⟨0, by simp⟩
  · intro x y _hx _hy hx_range hy_range
    rcases hx_range with ⟨x₀, rfl⟩
    rcases hy_range with ⟨y₀, rfl⟩
    exact ⟨x₀ + y₀, by simp [map_add]⟩
  · intro a x _hx hx_range
    rcases hx_range with ⟨x₀, rfl⟩
    refine ⟨a • x₀, ?_⟩
    rw [map_smul]

lemma raw_range_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (φ : MonoidAlgebra (ZMod p) Γ →ₐ[ZMod p] K.carrier)
    (hcompat :
      ∀ g : Γ,
        φ (Finsupp.single g (1 : ZMod p)) =
          (K.canonicalUnit g : K.carrier)) :
    Set.range φ =
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))) :
          Set K.carrier) := by
  apply Set.Subset.antisymm
  · exact
      K.raw_contained_span
        (p := p) (Γ := Γ) (s := s) (hs := hs) φ hcompat
  · exact
      K.canonical_subset_range
        (p := p) (Γ := Γ) (s := s) (hs := hs) φ hcompat

lemma dense_span_raw
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (Hraw : K.DenseRawAlgebra) :
    K.DenseAlgebraSpan := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  rcases Hraw with ⟨φ, hcompat, hdense⟩
  dsimp [DCCarrie.DenseAlgebraSpan]
  rw [← K.raw_range_span
      (p := p) (Γ := Γ) (s := s) (hs := hs) φ hcompat]
  exact hdense

def HasExtensionUniqueness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  ∀ (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
      [CompactSpace B] [TotallyDisconnectedSpace B],
    ∀ v : Γ →* Units B,
      Continuous v →
        ∀ Φ Ψ : K.carrier →ₐ[ZMod p] B,
          (Continuous Φ ∧
              ∀ g : Γ,
                Φ (K.canonicalUnit g : K.carrier) = (v g : B)) →
            (Continuous Ψ ∧
              ∀ g : Γ,
                Ψ (K.canonicalUnit g : K.carrier) = (v g : B)) →
              Φ = Ψ

def UniversalConstructionInputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  K.HasExtensionProperty ∧ K.HasExtensionUniqueness

lemma universal_construction_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.UniversalConstructionInputs) :
    K.HasExtensionProperty := by
  rcases H with ⟨Hext, Huniq⟩
  have Hext' : K.HasExtensionProperty := Hext
  have _Huniq' : K.HasExtensionUniqueness := Huniq
  exact Hext'

lemma uniqueness_construction_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.UniversalConstructionInputs) :
    K.HasExtensionUniqueness := by
  rcases H with ⟨Hext, Huniq⟩
  have _Hext' : K.HasExtensionProperty := Hext
  have Huniq' : K.HasExtensionUniqueness := Huniq
  exact Huniq'

lemma universal_property_uniqueness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (Hext : K.HasExtensionProperty)
    (Huniq : K.HasExtensionUniqueness) :
    K.HasUniversalProperty := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv
  rcases Hext B v hv with ⟨Φ, hΦ⟩
  refine ⟨Φ, hΦ, ?_⟩
  intro Ψ hΨ
  exact
    Huniq B v hv Ψ Φ hΨ hΦ

lemma universal_property_construction
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.UniversalConstructionInputs) :
    K.HasUniversalProperty := by
  have Hext : K.HasExtensionProperty :=
    K.universal_construction_inputs H
  have Huniq : K.HasExtensionUniqueness :=
    K.uniqueness_construction_inputs H
  exact
    K.universal_property_uniqueness Hext Huniq

lemma extension_property_universal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.HasUniversalProperty) :
    K.HasExtensionProperty := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv
  rcases H B v hv with ⟨Φ, hΦ, _huniq⟩
  exact ⟨Φ, hΦ⟩

lemma uniqueness_universal_property
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.HasUniversalProperty) :
    K.HasExtensionUniqueness := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv Φ Ψ hΦ hΨ
  rcases H B v hv with ⟨Θ, hΘ, huniq⟩
  have hΦΘ : Φ = Θ := huniq Φ hΦ
  have hΨΘ : Ψ = Θ := huniq Ψ hΨ
  exact hΦΘ.trans hΨΘ.symm

lemma property_construction_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    K.HasUniversalProperty ↔ K.UniversalConstructionInputs := by
  constructor
  · intro H
    have Hext : K.HasExtensionProperty :=
      K.extension_property_universal H
    have Huniq : K.HasExtensionUniqueness :=
      K.uniqueness_universal_property H
    exact ⟨Hext, Huniq⟩
  · intro H
    exact
      K.universal_property_construction H

lemma alg_span_units
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (B : Type u) [Ring B] [Algebra (ZMod p) B]
    (Φ Ψ : K.carrier →ₐ[ZMod p] B)
    (hΦΨ :
      ∀ g : Γ,
        Φ (K.canonicalUnit g : K.carrier) =
          Ψ (K.canonicalUnit g : K.carrier)) :
    ∀ x : K.carrier,
      x ∈
          ((Submodule.span (ZMod p)
            (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))) :
              Set K.carrier) →
        Φ x = Ψ x := by
  letI := K.instRing
  letI := K.instAlgebra
  let S : Set K.carrier :=
    Set.range fun g : Γ => (K.canonicalUnit g : K.carrier)
  intro x hx
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [S] using hx
  change Φ x = Ψ x
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ => Φ y = Ψ y)
    ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    exact hΦΨ g
  · calc
      Φ (0 : K.carrier) = (0 : B) := by
        exact map_zero Φ
      _ = Ψ (0 : K.carrier) := by
        exact (map_zero Ψ).symm
  · intro x y _hx _hy hx_eq hy_eq
    calc
      Φ (x + y) = Φ x + Φ y := by
        exact map_add Φ x y
      _ = Ψ x + Ψ y := by
        rw [hx_eq, hy_eq]
      _ = Ψ (x + y) := by
        exact (map_add Ψ x y).symm
  · intro a x _hx hx_eq
    calc
      Φ (a • x) = a • Φ x := by
        rw [map_smul]
      _ = a • Ψ x := by
        rw [hx_eq]
      _ = Ψ (a • x) := by
        rw [map_smul]

lemma alg_ext_subset
    {p : ℕ} [Fact p.Prime]
    {R B : Type u} [TopologicalSpace R] [Ring R] [Algebra (ZMod p) R]
    [TopologicalSpace B] [Ring B] [Algebra (ZMod p) B] [T2Space B]
    {S : Set R}
    (Φ Ψ : R →ₐ[ZMod p] B)
    (hΦcont : Continuous Φ)
    (hΨcont : Continuous Ψ)
    (hdense : closure S = Set.univ)
    (hS : ∀ x : R, x ∈ S → Φ x = Ψ x) :
    Φ = Ψ := by
  have hclosed : IsClosed {x : R | Φ x = Ψ x} :=
    isClosed_eq hΦcont hΨcont
  have hS_subset : S ⊆ {x : R | Φ x = Ψ x} := by
    intro x hx
    exact hS x hx
  have hclosure_subset : closure S ⊆ {x : R | Φ x = Ψ x} := by
    exact hclosed.closure_subset_iff.mpr hS_subset
  apply DFunLike.ext
  intro x
  have hxclosure : x ∈ closure S := by
    rw [hdense]
    exact Set.mem_univ x
  exact hclosure_subset hxclosure

lemma extension_uniqueness_aux
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (hdense : K.DenseAlgebraSpan)
    (B : Type u) [Ring B] [Algebra (ZMod p) B] [UniformSpace B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [CompactSpace B] [TotallyDisconnectedSpace B]
    (v : Γ →* Units B)
    (_hv : Continuous v)
    (Φ Ψ : K.carrier →ₐ[ZMod p] B)
    (hΦ : Continuous Φ ∧
      ∀ g : Γ,
        Φ (K.canonicalUnit g : K.carrier) = (v g : B))
    (hΨ : Continuous Ψ ∧
      ∀ g : Γ,
        Ψ (K.canonicalUnit g : K.carrier) = (v g : B)) :
    Φ = Ψ := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  let S : Set K.carrier :=
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (K.canonicalUnit g : K.carrier))) :
        Set K.carrier)
  have hunit_eq :
      ∀ g : Γ,
        Φ (K.canonicalUnit g : K.carrier) =
          Ψ (K.canonicalUnit g : K.carrier) := by
    intro g
    calc
      Φ (K.canonicalUnit g : K.carrier) = (v g : B) := hΦ.2 g
      _ = Ψ (K.canonicalUnit g : K.carrier) := by
        exact (hΨ.2 g).symm
  have hspan_eq :
      ∀ x : K.carrier, x ∈ S → Φ x = Ψ x := by
    intro x hx
    exact
      K.alg_span_units
        B Φ Ψ hunit_eq x (by simpa [S] using hx)
  have hdenseS : closure S = Set.univ := by
    simpa [
      DCCarrie.DenseAlgebraSpan,
      S
    ] using hdense
  exact
    alg_ext_subset
      (p := p) (R := K.carrier) (B := B) (S := S)
      Φ Ψ hΦ.1 hΨ.1 hdenseS hspan_eq

lemma extension_uniqueness_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (hdense : K.DenseAlgebraSpan) :
    K.HasExtensionUniqueness := by
  intro B _instRing _instAlgebra _instUniformSpace _instTopRing _instComplete _instT2
    _instCompact _instTotallyDisconnected v hv Φ Ψ hΦ hΨ
  exact
    K.extension_uniqueness_aux
      hdense B v hv Φ Ψ hΦ hΨ

lemma construction_inputs_property
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (Hext : K.HasExtensionProperty)
    (Hdense : K.DenseAlgebraSpan) :
    K.UniversalConstructionInputs := by
  have Huniq : K.HasExtensionUniqueness := by
    exact K.extension_uniqueness_span Hdense
  constructor
  · exact Hext
  · exact Huniq

lemma universal_property_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (Hext : K.HasExtensionProperty)
    (Hdense : K.DenseAlgebraSpan) :
    K.HasUniversalProperty := by
  have Huniq : K.HasExtensionUniqueness :=
    K.extension_uniqueness_span Hdense
  exact
    K.universal_property_uniqueness Hext Huniq

def TrivialCharacterExtension
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Prop :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  ∃ Φ : K.carrier →ₐ[ZMod p] ZMod p,
    Continuous Φ ∧
      ∀ g : Γ,
        Φ (K.canonicalUnit g : K.carrier) = 1

abbrev TrivialCharacterTarget (p : ℕ) : Type u :=
  ULift.{u} (ZMod p)

noncomputable def trivialCharacterTarget
    (p : ℕ) :
    TrivialCharacterTarget.{u} p →ₐ[ZMod p] ZMod p :=
  (ULift.algEquiv (R := ZMod p) (A := ZMod p)).toAlgHom

lemma continuous_trivial_target
    {p : ℕ} [Fact p.Prime] :
    letI : UniformSpace (TrivialCharacterTarget.{u} p) := ⊥
    letI : TopologicalSpace (TrivialCharacterTarget.{u} p) :=
      (inferInstance : UniformSpace (TrivialCharacterTarget.{u} p)).toTopologicalSpace
    Continuous (trivialCharacterTarget.{u} p) := by
  letI : UniformSpace (TrivialCharacterTarget.{u} p) := ⊥
  letI : TopologicalSpace (TrivialCharacterTarget.{u} p) :=
    (inferInstance : UniformSpace (TrivialCharacterTarget.{u} p)).toTopologicalSpace
  exact continuous_of_discreteTopology

def trivialTargetHom
    (p : ℕ)
    (Γ : Type u) [Group Γ] :
    Γ →* Units (TrivialCharacterTarget.{u} p) :=
  1

lemma continuous_character_target
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] :
    letI : UniformSpace (TrivialCharacterTarget.{u} p) := ⊥
    letI : TopologicalSpace (TrivialCharacterTarget.{u} p) :=
      (inferInstance : UniformSpace (TrivialCharacterTarget.{u} p)).toTopologicalSpace
    Continuous (trivialTargetHom.{u} p Γ) := by
  letI : UniformSpace (TrivialCharacterTarget.{u} p) := ⊥
  letI : TopologicalSpace (TrivialCharacterTarget.{u} p) :=
    (inferInstance : UniformSpace (TrivialCharacterTarget.{u} p)).toTopologicalSpace
  exact continuous_const

lemma trivial_character_target
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    (g : Γ) :
    trivialCharacterTarget.{u} p
        ((trivialTargetHom.{u} p Γ g :
          Units (TrivialCharacterTarget.{u} p)) :
          TrivialCharacterTarget.{u} p) =
      (1 : ZMod p) := by
  simp [
    trivialCharacterTarget,
    trivialTargetHom,
    TrivialCharacterTarget
  ]

lemma trivial_universal_property
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.HasUniversalProperty) :
    K.TrivialCharacterExtension := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  let B : Type u := TrivialCharacterTarget.{u} p
  letI : Ring B := inferInstance
  letI : Algebra (ZMod p) B := inferInstance
  letI : UniformSpace B := ⊥
  letI : TopologicalSpace B := (inferInstance : UniformSpace B).toTopologicalSpace
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have htopRing : IsTopologicalRing B := inferInstance
  have hcomplete : CompleteSpace B := inferInstance
  have hT2 : T2Space B := inferInstance
  have hcompact : CompactSpace B := inferInstance
  have htotallyDisconnected : TotallyDisconnectedSpace B := inferInstance
  let v : Γ →* Units B := trivialTargetHom.{u} p Γ
  have hvcont : Continuous v := by
    simpa [B, v] using
      continuous_character_target (p := p) (Γ := Γ)
  rcases H B v hvcont with ⟨Ψ, hΨ, _huniq⟩
  let lower : B →ₐ[ZMod p] ZMod p :=
    trivialCharacterTarget.{u} p
  have hlower_cont : Continuous lower := by
    simpa [B, lower] using
      continuous_trivial_target (p := p)
  let Φ : K.carrier →ₐ[ZMod p] ZMod p := lower.comp Ψ
  refine ⟨Φ, ?_, ?_⟩
  · exact hlower_cont.comp hΨ.1
  · intro g
    have hΨg : Ψ (K.canonicalUnit g : K.carrier) = (v g : B) := hΨ.2 g
    calc
      Φ (K.canonicalUnit g : K.carrier) =
          lower (Ψ (K.canonicalUnit g : K.carrier)) := by
        rfl
      _ = lower (v g : B) := by
        rw [hΨg]
      _ = (1 : ZMod p) := by
        simpa [B, lower, v] using
          trivial_character_target
            (p := p) (Γ := Γ) g

end DCCarrie

end Towers
