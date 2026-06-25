import Mathlib
import Submission.Group.GolodShafarevichCore


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

lemma generator_set_univ
    (p : ℕ) (G : Type*) [Group G] {n : ℕ}
    (hn : n ≤ 1) :
    zassenhausGeneratorSet p G n = Set.univ := by
  ext g
  constructor
  · intro _hg
    exact Set.mem_univ g
  · intro _hg
    refine ⟨0, 0, g, ?_, ?_, ?_⟩
    · simp
    · simpa using hn
    · simp

lemma zassenhaus_filtration_top
    (p : ℕ) (G : Type*) [Group G] {n : ℕ}
    (hn : n ≤ 1) :
    zassenhausFiltration p G n = ⊤ := by
  rw [zassenhausFiltration, generator_set_univ p G hn]
  ext g
  constructor
  · intro _hg
    exact Subgroup.mem_top g
  · intro _hg
    exact Subgroup.subset_closure (Set.mem_univ g)

lemma filtration_zero_top
    (p : ℕ) (G : Type*) [Group G] :
    zassenhausFiltration p G 0 = ⊤ := by
  exact zassenhaus_filtration_top p G (by norm_num)

lemma filtration_one_top
    (p : ℕ) (G : Type*) [Group G] :
    zassenhausFiltration p G 1 = ⊤ := by
  exact zassenhaus_filtration_top p G (by norm_num)

lemma zassenhaus_filtration_one
    (p : ℕ) (G : Type*) [Group G] {n : ℕ}
    (hn : n ≤ 1) (g : G) :
    g ∈ zassenhausFiltration p G n := by
  rw [zassenhaus_filtration_top p G hn]
  exact Subgroup.mem_top g

noncomputable def generators_jennings_approx
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (_hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type u := by
  exact Γ ⧸ zassenhausFiltration p Γ n

noncomputable instance instGeneratorsApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Group (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  dsimp [generators_jennings_approx]
  infer_instance

noncomputable instance instSpaceApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    TopologicalSpace (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  dsimp [generators_jennings_approx]
  infer_instance

noncomputable def dense_jennings_approx
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Γ →* generators_jennings_approx (p := p) (Γ := Γ) s hs n := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  exact QuotientGroup.mk' (zassenhausFiltration p Γ n)

structure DCModel
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type (u + 1) where
  completedGroupAlgebra : Type u
  [instRing : Ring completedGroupAlgebra]
  [instAlgebra : Algebra (ZMod p) completedGroupAlgebra]
  [instUniformSpace : UniformSpace completedGroupAlgebra]
  [topologicalRing : IsTopologicalRing completedGroupAlgebra]
  [instCompleteSpace : CompleteSpace completedGroupAlgebra]
  [t2Space : T2Space completedGroupAlgebra]
  [instCompactSpace : CompactSpace completedGroupAlgebra]
  [totallyDisconnected : TotallyDisconnectedSpace completedGroupAlgebra]
  augmentationMap : completedGroupAlgebra →ₐ[ZMod p] ZMod p
  augmentationMap_continuous : Continuous augmentationMap
  augmentationIdeal : Ideal completedGroupAlgebra
  augmentation_ideal_ker :
    augmentationIdeal = RingHom.ker augmentationMap.toRingHom
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  [quotientTopology : TopologicalSpace augmentationQuotient]
  [quotientT2 : T2Space augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing augmentationQuotient]
  quotientMap : completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = augmentationIdeal ^ n
  canonicalUnit : Γ →* Units completedGroupAlgebra
  canonicalUnit_continuous : Continuous canonicalUnit
  canonicalUnit_augmentation :
    ∀ g : Γ, augmentationMap (canonicalUnit g : completedGroupAlgebra) = 1
  unitReduction : Units completedGroupAlgebra →* Units augmentationQuotient
  unitReduction_continuous : Continuous unitReduction
  unitReduction_apply :
    ∀ x : Units completedGroupAlgebra,
      (unitReduction x : augmentationQuotient) =
        quotientMap (x : completedGroupAlgebra)
  quotientUnitMap : Γ →* Units augmentationQuotient
  quotient_unit_continuous : Continuous quotientUnitMap
  quotient_unit_map :
    quotientUnitMap = unitReduction.comp canonicalUnit
  quotientEquiv :
    quotientUnitMap.range ≃*
      generators_jennings_approx (p := p) (Γ := Γ) s hs n
  quotientEquiv_apply :
    ∀ g : Γ,
      quotientEquiv ⟨quotientUnitMap g, ⟨g, rfl⟩⟩ =
        dense_jennings_approx (p := p) (Γ := Γ) s hs n g
  unit_map_ker :
    quotientUnitMap.ker = zassenhausFiltration p Γ n

lemma DCModel.augmentation_t_2
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.quotientTopology
    T2Space M.augmentationQuotient := by
  letI := M.quotientTopology
  have hT2 : T2Space M.augmentationQuotient := M.quotientT2
  exact hT2

lemma dense_completed_model
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient) :
    Finite M.quotientUnitMap.range := by
  letI := M.instQuotientRing
  letI := M.quotientTopology
  letI : Finite M.augmentationQuotient := hfinite
  have hfinite_units : Finite (Units M.augmentationQuotient) := inferInstance
  exact inferInstance

lemma completed_model_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hT2 :
      letI := M.quotientTopology
      T2Space M.augmentationQuotient) :
    letI := M.quotientTopology
    T2Space M.quotientUnitMap.range := by
  letI := M.instQuotientRing
  letI := M.quotientTopology
  letI : T2Space M.augmentationQuotient := hT2
  have hT2_units : T2Space (Units M.augmentationQuotient) := inferInstance
  exact inferInstance

lemma completed_discrete_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hT2 :
      letI := M.quotientTopology
      T2Space M.augmentationQuotient) :
    letI := M.quotientTopology
    DiscreteTopology M.quotientUnitMap.range := by
  letI := M.instQuotientRing
  letI := M.quotientTopology
  have hfinite_range : Finite M.quotientUnitMap.range :=
    dense_completed_model
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite
  have hT2_range : T2Space M.quotientUnitMap.range :=
    completed_model_t
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hT2
  letI : Finite M.quotientUnitMap.range := hfinite_range
  letI : T2Space M.quotientUnitMap.range := hT2_range
  infer_instance

structure DCCore
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type (u + 1) where
  completedGroupAlgebra : Type u
  [instRing : Ring completedGroupAlgebra]
  [instAlgebra : Algebra (ZMod p) completedGroupAlgebra]
  [instUniformSpace : UniformSpace completedGroupAlgebra]
  [topologicalRing : IsTopologicalRing completedGroupAlgebra]
  [instCompleteSpace : CompleteSpace completedGroupAlgebra]
  [t2Space : T2Space completedGroupAlgebra]
  [instCompactSpace : CompactSpace completedGroupAlgebra]
  [totallyDisconnected : TotallyDisconnectedSpace completedGroupAlgebra]
  augmentationMap : completedGroupAlgebra →ₐ[ZMod p] ZMod p
  augmentationMap_continuous : Continuous augmentationMap
  augmentationIdeal : Ideal completedGroupAlgebra
  augmentation_ideal_ker :
    augmentationIdeal = RingHom.ker augmentationMap.toRingHom
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  [quotientTopology : TopologicalSpace augmentationQuotient]
  [quotientT2 : T2Space augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing augmentationQuotient]
  quotientMap : completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = augmentationIdeal ^ n
  canonicalUnit : Γ →* Units completedGroupAlgebra
  canonicalUnit_continuous : Continuous canonicalUnit
  canonicalUnit_augmentation :
    ∀ g : Γ, augmentationMap (canonicalUnit g : completedGroupAlgebra) = 1
  unitReduction : Units completedGroupAlgebra →* Units augmentationQuotient
  unitReduction_continuous : Continuous unitReduction
  unitReduction_apply :
    ∀ x : Units completedGroupAlgebra,
      (unitReduction x : augmentationQuotient) =
        quotientMap (x : completedGroupAlgebra)
  quotientUnitMap : Γ →* Units augmentationQuotient
  quotient_unit_continuous : Continuous quotientUnitMap
  quotient_unit_map :
    quotientUnitMap = unitReduction.comp canonicalUnit

attribute [instance]
  DCCore.instRing
  DCCore.instAlgebra
  DCCore.instUniformSpace
  DCCore.topologicalRing
  DCCore.instCompleteSpace
  DCCore.t2Space
  DCCore.instCompactSpace
  DCCore.totallyDisconnected
  DCCore.instQuotientRing
  DCCore.instQuotientAlgebra
  DCCore.quotientTopology
  DCCore.quotientT2
  DCCore.quotientTopologicalRing

structure GCAmbien
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Type (u + 1) where
  completedGroupAlgebra : Type u
  [instRing : Ring completedGroupAlgebra]
  [instAlgebra : Algebra (ZMod p) completedGroupAlgebra]
  [instUniformSpace : UniformSpace completedGroupAlgebra]
  [topologicalRing : IsTopologicalRing completedGroupAlgebra]
  [instCompleteSpace : CompleteSpace completedGroupAlgebra]
  [t2Space : T2Space completedGroupAlgebra]
  [instCompactSpace : CompactSpace completedGroupAlgebra]
  [totallyDisconnected : TotallyDisconnectedSpace completedGroupAlgebra]
  augmentationMap : completedGroupAlgebra →ₐ[ZMod p] ZMod p
  augmentationMap_continuous : Continuous augmentationMap
  augmentationIdeal : Ideal completedGroupAlgebra
  augmentation_ideal_ker :
    augmentationIdeal = RingHom.ker augmentationMap.toRingHom
  canonicalUnit : Γ →* Units completedGroupAlgebra
  canonicalUnit_continuous : Continuous canonicalUnit
  canonicalUnit_augmentation :
    ∀ g : Γ, augmentationMap (canonicalUnit g : completedGroupAlgebra) = 1

attribute [instance]
  GCAmbien.instRing
  GCAmbien.instAlgebra
  GCAmbien.instUniformSpace
  GCAmbien.topologicalRing
  GCAmbien.instCompleteSpace
  GCAmbien.t2Space
  GCAmbien.instCompactSpace
  GCAmbien.totallyDisconnected

def GCAmbien.DenseAlgebraSpan
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
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra)) :
        Set A.completedGroupAlgebra)) = Set.univ

structure DCObject
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Type (u + 1) where
  completedGroupAlgebra : Type u
  [instRing : Ring completedGroupAlgebra]
  [instAlgebra : Algebra (ZMod p) completedGroupAlgebra]
  [instUniformSpace : UniformSpace completedGroupAlgebra]
  [topologicalRing : IsTopologicalRing completedGroupAlgebra]
  [instCompleteSpace : CompleteSpace completedGroupAlgebra]
  [t2Space : T2Space completedGroupAlgebra]
  [instCompactSpace : CompactSpace completedGroupAlgebra]
  [totallyDisconnected : TotallyDisconnectedSpace completedGroupAlgebra]

attribute [instance]
  DCObject.instRing
  DCObject.instAlgebra
  DCObject.instUniformSpace
  DCObject.topologicalRing
  DCObject.instCompleteSpace
  DCObject.t2Space
  DCObject.instCompactSpace
  DCObject.totallyDisconnected

structure DenseCompletedAugmentation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : DCObject (p := p) (Γ := Γ) s hs) :
    Type (u + 1) where
  augmentationMap : A.completedGroupAlgebra →ₐ[ZMod p] ZMod p
  augmentationMap_continuous : Continuous augmentationMap
  augmentationIdeal : Ideal A.completedGroupAlgebra
  augmentation_ideal_ker :
    augmentationIdeal = RingHom.ker augmentationMap.toRingHom

structure DenseCompletedUnits
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : DCObject (p := p) (Γ := Γ) s hs)
    (Aug : DenseCompletedAugmentation A) :
    Type (u + 1) where
  canonicalUnit : Γ →* Units A.completedGroupAlgebra
  canonicalUnit_continuous : Continuous canonicalUnit
  canonicalUnit_augmentation :
    ∀ g : Γ, Aug.augmentationMap (canonicalUnit g : A.completedGroupAlgebra) = 1

structure DCSpan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : DCObject (p := p) (Γ := Γ) s hs)
    (Aug : DenseCompletedAugmentation A)
    (U : DenseCompletedUnits A Aug) :
    Type (u + 1) where
  dense_span :
    letI := A.instRing
    letI := A.instAlgebra
    letI := A.instUniformSpace
    closure
      ((Submodule.span (ZMod p)
        (Set.range fun g : Γ => (U.canonicalUnit g : A.completedGroupAlgebra)) :
          Set A.completedGroupAlgebra)) = Set.univ

structure DenseCompletedExtension
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : DCObject (p := p) (Γ := Γ) s hs)
    (Aug : DenseCompletedAugmentation A)
    (U : DenseCompletedUnits A Aug) :
    Type (u + 1) where
  quotient_alg_hom :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      (φ : Γ →* Λ),
      Continuous (fun x : Γ => φ x) →
      A.completedGroupAlgebra →ₐ[ZMod p] MonoidAlgebra (ZMod p) Λ
  alg_hom_unit :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      (φ : Γ →* Λ)
      (hφ : Continuous (fun x : Γ => φ x))
      (g : Γ),
      quotient_alg_hom φ hφ (U.canonicalUnit g : A.completedGroupAlgebra) =
        MonoidAlgebra.single (φ g) 1
  finite_alg_hom :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
      (φ : Γ →* Λ)
      (hφ : Continuous (fun x : Γ => φ x))
      (x : A.completedGroupAlgebra),
      MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p)
          (quotient_alg_hom φ hφ x) =
        Aug.augmentationMap x

def DCObject.toAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : DCObject (p := p) (Γ := Γ) s hs)
    (Aug : DenseCompletedAugmentation A)
    (U : DenseCompletedUnits A Aug) :
    GCAmbien (p := p) (Γ := Γ) s hs where
  completedGroupAlgebra := A.completedGroupAlgebra
  instRing := A.instRing
  instAlgebra := A.instAlgebra
  instUniformSpace := A.instUniformSpace
  topologicalRing := A.topologicalRing
  instCompleteSpace := A.instCompleteSpace
  t2Space := A.t2Space
  instCompactSpace := A.instCompactSpace
  totallyDisconnected := A.totallyDisconnected
  augmentationMap := Aug.augmentationMap
  augmentationMap_continuous := Aug.augmentationMap_continuous
  augmentationIdeal := Aug.augmentationIdeal
  augmentation_ideal_ker := Aug.augmentation_ideal_ker
  canonicalUnit := U.canonicalUnit
  canonicalUnit_continuous := U.canonicalUnit_continuous
  canonicalUnit_augmentation := U.canonicalUnit_augmentation

lemma
    DCSpan.ambient_denseunit_algspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : DCObject (p := p) (Γ := Γ) s hs}
    {Aug : DenseCompletedAugmentation A}
    {U : DenseCompletedUnits A Aug}
    (D : DCSpan A Aug U) :
    (A.toAmbient Aug U).DenseAlgebraSpan := by
  simpa [
    GCAmbien.DenseAlgebraSpan,
    DCObject.toAmbient
  ] using D.dense_span

structure GCPackag
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Type (u + 2) where
  object :
    DCObject (p := p) (Γ := Γ) s hs
  augmentation :
    DenseCompletedAugmentation object
  canonicalUnits :
    DenseCompletedUnits object augmentation
  canonicalDenseSpan :
    DCSpan object augmentation canonicalUnits
  algebraMapExtension :
    DenseCompletedExtension
      object augmentation canonicalUnits

def GCPackag.toAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs) :
    GCAmbien (p := p) (Γ := Γ) s hs :=
  P.object.toAmbient P.augmentation P.canonicalUnits

lemma
    GCPackag.ambient_denseunit_algspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs) :
    P.toAmbient.DenseAlgebraSpan := by
  simpa [GCPackag.toAmbient] using
    P.canonicalDenseSpan.ambient_denseunit_algspan

lemma
    GCPackag.exists_object_augunits
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs) :
    ∃ A : DCObject
        (p := p) (Γ := Γ) s hs,
      ∃ Aug : DenseCompletedAugmentation A,
        Nonempty (DenseCompletedUnits A Aug) := by
  exact ⟨P.object, P.augmentation, ⟨P.canonicalUnits⟩⟩

lemma
    GCPackag.existsambient_denseunit_algspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan := by
  exact ⟨P.toAmbient, P.ambient_denseunit_algspan⟩

structure DCLayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 1) where
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  [quotientTopology : TopologicalSpace augmentationQuotient]
  [quotientT2 : T2Space augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing augmentationQuotient]
  quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n
  unitReduction : Units A.completedGroupAlgebra →* Units augmentationQuotient
  unitReduction_continuous : Continuous unitReduction
  unitReduction_apply :
    ∀ x : Units A.completedGroupAlgebra,
      (unitReduction x : augmentationQuotient) =
        quotientMap (x : A.completedGroupAlgebra)
  quotientUnitMap : Γ →* Units augmentationQuotient
  quotient_unit_continuous : Continuous quotientUnitMap
  quotient_unit_map :
    quotientUnitMap = unitReduction.comp A.canonicalUnit

attribute [instance]
  DCLayer.instQuotientRing
  DCLayer.instQuotientAlgebra
  DCLayer.quotientTopology
  DCLayer.quotientT2
  DCLayer.quotientTopologicalRing

structure DCAlg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 1) where
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  [quotientTopology : TopologicalSpace augmentationQuotient]
  [quotientT2 : T2Space augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing augmentationQuotient]
  quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n

attribute [instance]
  DCAlg.instQuotientRing
  DCAlg.instQuotientAlgebra
  DCAlg.quotientTopology
  DCAlg.quotientT2
  DCAlg.quotientTopologicalRing

structure GAAug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 1) where
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n

attribute [instance]
  GAAug.instQuotientRing
  GAAug.instQuotientAlgebra

structure GTAug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A) :
    Type (u + 1) where
  [quotientTopology : TopologicalSpace Q.augmentationQuotient]
  [quotientT2 : T2Space Q.augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing Q.augmentationQuotient]
  quotientMap_continuous : Continuous Q.quotientMap

attribute [instance]
  GTAug.quotientTopology
  GTAug.quotientT2
  GTAug.quotientTopologicalRing

def GCAmbien.TopoAugQuot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
    Nonempty
      (GTAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q)

def GAAug.toAugmentationQuotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T :
      GTAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q) :
    DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A where
  augmentationQuotient := Q.augmentationQuotient
  instQuotientRing := Q.instQuotientRing
  instQuotientAlgebra := Q.instQuotientAlgebra
  quotientTopology := T.quotientTopology
  quotientT2 := T.quotientT2
  quotientTopologicalRing := T.quotientTopologicalRing
  quotientMap := Q.quotientMap
  quotientMap_continuous := T.quotientMap_continuous
  quotientMap_surjective := Q.quotientMap_surjective
  quotientMap_ker := Q.quotientMap_ker

lemma dense_topological_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T :
      GTAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q) :
    Nonempty
      (DCAlg
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  exact ⟨Q.toAugmentationQuotient T⟩

structure DenseCompletedReduction
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg (p := p) (Γ := Γ)
      (s := s) (hs := hs) n A) :
    Type (u + 1) where
  unitReduction : Units A.completedGroupAlgebra →* Units Q.augmentationQuotient
  unitReduction_continuous : Continuous unitReduction
  unitReduction_apply :
    ∀ x : Units A.completedGroupAlgebra,
      (unitReduction x : Q.augmentationQuotient) =
        Q.quotientMap (x : A.completedGroupAlgebra)

structure DenseGeneratorsCompleted
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
    Type (u + 1) where
  quotientUnitMap : Γ →* Units Q.augmentationQuotient
  quotient_unit_continuous : Continuous quotientUnitMap
  quotient_unit_map :
    quotientUnitMap = R.unitReduction.comp A.canonicalUnit

def DCAlg.toQuotientLayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg (p := p) (Γ := Γ)
      (s := s) (hs := hs) n A)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    DCLayer (p := p) (Γ := Γ) (s := s)
      (hs := hs) n A where
  augmentationQuotient := Q.augmentationQuotient
  instQuotientRing := Q.instQuotientRing
  instQuotientAlgebra := Q.instQuotientAlgebra
  quotientTopology := Q.quotientTopology
  quotientT2 := Q.quotientT2
  quotientTopologicalRing := Q.quotientTopologicalRing
  quotientMap := Q.quotientMap
  quotientMap_continuous := Q.quotientMap_continuous
  quotientMap_surjective := Q.quotientMap_surjective
  quotientMap_ker := Q.quotientMap_ker
  unitReduction := R.unitReduction
  unitReduction_continuous := R.unitReduction_continuous
  unitReduction_apply := R.unitReduction_apply
  quotientUnitMap := U.quotientUnitMap
  quotient_unit_continuous := U.quotient_unit_continuous
  quotient_unit_map := U.quotient_unit_map

def GCAmbien.toCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer (p := p) (Γ := Γ) (s := s)
      (hs := hs) n A) :
    DCCore (p := p) (Γ := Γ) s hs n where
  completedGroupAlgebra := A.completedGroupAlgebra
  instRing := A.instRing
  instAlgebra := A.instAlgebra
  instUniformSpace := A.instUniformSpace
  topologicalRing := A.topologicalRing
  instCompleteSpace := A.instCompleteSpace
  t2Space := A.t2Space
  instCompactSpace := A.instCompactSpace
  totallyDisconnected := A.totallyDisconnected
  augmentationMap := A.augmentationMap
  augmentationMap_continuous := A.augmentationMap_continuous
  augmentationIdeal := A.augmentationIdeal
  augmentation_ideal_ker := A.augmentation_ideal_ker
  augmentationQuotient := Q.augmentationQuotient
  instQuotientRing := Q.instQuotientRing
  instQuotientAlgebra := Q.instQuotientAlgebra
  quotientTopology := Q.quotientTopology
  quotientT2 := Q.quotientT2
  quotientTopologicalRing := Q.quotientTopologicalRing
  quotientMap := Q.quotientMap
  quotientMap_continuous := Q.quotientMap_continuous
  quotientMap_surjective := Q.quotientMap_surjective
  quotientMap_ker := Q.quotientMap_ker
  canonicalUnit := A.canonicalUnit
  canonicalUnit_continuous := A.canonicalUnit_continuous
  canonicalUnit_augmentation := A.canonicalUnit_augmentation
  unitReduction := Q.unitReduction
  unitReduction_continuous := Q.unitReduction_continuous
  unitReduction_apply := Q.unitReduction_apply
  quotientUnitMap := Q.quotientUnitMap
  quotient_unit_continuous := Q.quotient_unit_continuous
  quotient_unit_map := Q.quotient_unit_map

structure DenseLazardIdentification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  quotientEquiv :
    C.quotientUnitMap.range ≃*
      generators_jennings_approx (p := p) (Γ := Γ) s hs n
  quotientEquiv_apply :
    ∀ g : Γ,
      quotientEquiv ⟨C.quotientUnitMap g, ⟨g, rfl⟩⟩ =
        dense_jennings_approx (p := p) (Γ := Γ) s hs n g
  unit_map_ker :
    C.quotientUnitMap.ker = zassenhausFiltration p Γ n

structure JLIdenti
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  unit_map_ker :
    C.quotientUnitMap.ker = zassenhausFiltration p Γ n

structure LUBound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  quotient_unit_ker :
    C.quotientUnitMap.ker ≤ zassenhausFiltration p Γ n

structure DenseLazardBound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Type (u + 1) where
  zassenhaus_filtration_ker :
    zassenhausFiltration p Γ n ≤ C.quotientUnitMap.ker

def LUBound.toIdentification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (U : LUBound C)
    (L : DenseLazardBound C) :
    JLIdenti C where
  unit_map_ker :=
    le_antisymm U.quotient_unit_ker L.zassenhaus_filtration_ker

lemma filtration_generator_set
    {p : ℕ} {Γ : Type u} [Group Γ] {n : ℕ}
    {K : Subgroup Γ}
    (hgen : zassenhausGeneratorSet p Γ n ≤ K) :
    zassenhausFiltration p Γ n ≤ K := by
  rw [zassenhausFiltration]
  exact (Subgroup.closure_le K).2 hgen

lemma jennings_lazard_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {g : Γ}
    (hg : g ∈ C.quotientUnitMap.ker) :
    (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n := by
  letI := C.instRing
  letI := C.instQuotientRing
  have hunit : C.quotientUnitMap g = 1 := by
    simpa using hg
  have hunit_reduced :
      C.unitReduction (C.canonicalUnit g) = (1 : Units C.augmentationQuotient) := by
    simpa [C.quotient_unit_map] using hunit
  have hquotient_one :
      C.quotientMap (C.canonicalUnit g : C.completedGroupAlgebra) =
        (1 : C.augmentationQuotient) := by
    have hcoe :=
      congr_arg (fun x : Units C.augmentationQuotient => (x : C.augmentationQuotient))
        hunit_reduced
    simpa [C.unitReduction_apply] using hcoe
  have hquotient_one_ring :
      C.quotientMap.toRingHom (C.canonicalUnit g : C.completedGroupAlgebra) =
        (1 : C.augmentationQuotient) := by
    simpa using hquotient_one
  have hker :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈
        RingHom.ker C.quotientMap.toRingHom := by
    rw [RingHom.mem_ker]
    rw [map_sub, hquotient_one_ring, map_one, sub_self]
  rw [← C.quotientMap_ker]
  exact hker

structure JenningsLazardEquivalence
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (_K : JLIdenti C) :
    Type (u + 1) where
  quotientEquiv :
    C.quotientUnitMap.range ≃*
      generators_jennings_approx (p := p) (Γ := Γ) s hs n
  quotientEquiv_apply :
    ∀ g : Γ,
      quotientEquiv ⟨C.quotientUnitMap g, ⟨g, rfl⟩⟩ =
        dense_jennings_approx (p := p) (Γ := Γ) s hs n g

def JLIdenti.toIdentification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (K : JLIdenti C)
    (R : JenningsLazardEquivalence C K) :
    DenseLazardIdentification C where
  quotientEquiv := R.quotientEquiv
  quotientEquiv_apply := R.quotientEquiv_apply
  unit_map_ker := K.unit_map_ker

def DCCore.toModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (J : DenseLazardIdentification C) :
    DCModel (p := p) (Γ := Γ) s hs n where
  completedGroupAlgebra := C.completedGroupAlgebra
  instRing := C.instRing
  instAlgebra := C.instAlgebra
  instUniformSpace := C.instUniformSpace
  topologicalRing := C.topologicalRing
  instCompleteSpace := C.instCompleteSpace
  t2Space := C.t2Space
  instCompactSpace := C.instCompactSpace
  totallyDisconnected := C.totallyDisconnected
  augmentationMap := C.augmentationMap
  augmentationMap_continuous := C.augmentationMap_continuous
  augmentationIdeal := C.augmentationIdeal
  augmentation_ideal_ker := C.augmentation_ideal_ker
  augmentationQuotient := C.augmentationQuotient
  instQuotientRing := C.instQuotientRing
  instQuotientAlgebra := C.instQuotientAlgebra
  quotientTopology := C.quotientTopology
  quotientT2 := C.quotientT2
  quotientTopologicalRing := C.quotientTopologicalRing
  quotientMap := C.quotientMap
  quotientMap_continuous := C.quotientMap_continuous
  quotientMap_surjective := C.quotientMap_surjective
  quotientMap_ker := C.quotientMap_ker
  canonicalUnit := C.canonicalUnit
  canonicalUnit_continuous := C.canonicalUnit_continuous
  canonicalUnit_augmentation := C.canonicalUnit_augmentation
  unitReduction := C.unitReduction
  unitReduction_continuous := C.unitReduction_continuous
  unitReduction_apply := C.unitReduction_apply
  quotientUnitMap := C.quotientUnitMap
  quotient_unit_continuous := C.quotient_unit_continuous
  quotient_unit_map := C.quotient_unit_map
  quotientEquiv := J.quotientEquiv
  quotientEquiv_apply := J.quotientEquiv_apply
  unit_map_ker := J.unit_map_ker

end Submission
