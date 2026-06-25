import Mathlib
import Towers.Algebra.DenseGenerators.CoreJennings
import Towers.Algebra.DenseGenerators.IdealFamily


open scoped Topology Pointwise BigOperators

noncomputable section

namespace Towers

universe u
universe v w z

def GCAmbien.toObject
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    DCObject (p := p) (Γ := Γ) s hs where
  completedGroupAlgebra := A.completedGroupAlgebra
  instRing := A.instRing
  instAlgebra := A.instAlgebra
  instUniformSpace := A.instUniformSpace
  topologicalRing := A.topologicalRing
  instCompleteSpace := A.instCompleteSpace
  t2Space := A.t2Space
  instCompactSpace := A.instCompactSpace
  totallyDisconnected := A.totallyDisconnected

def GCAmbien.augmentation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    DenseCompletedAugmentation A.toObject where
  augmentationMap := A.augmentationMap
  augmentationMap_continuous := A.augmentationMap_continuous
  augmentationIdeal := A.augmentationIdeal
  augmentation_ideal_ker := A.augmentation_ideal_ker

def GCAmbien.canonicalUnits
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    DenseCompletedUnits A.toObject A.augmentation where
  canonicalUnit := A.canonicalUnit
  canonicalUnit_continuous := A.canonicalUnit_continuous
  canonicalUnit_augmentation := A.canonicalUnit_augmentation

def DCCore.ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    GCAmbien (p := p) (Γ := Γ) s hs where
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
  canonicalUnit := C.canonicalUnit
  canonicalUnit_continuous := C.canonicalUnit_continuous
  canonicalUnit_augmentation := C.canonicalUnit_augmentation

def DCCore.quotientLayer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n C.ambient where
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
  unitReduction := C.unitReduction
  unitReduction_continuous := C.unitReduction_continuous
  unitReduction_apply := C.unitReduction_apply
  quotientUnitMap := C.quotientUnitMap
  quotient_unit_continuous := C.quotient_unit_continuous
  quotient_unit_map := C.quotient_unit_map

lemma completed_ambient_units
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty
      (GCAmbien
        (p := p) (Γ := Γ) s hs) :=
  completed_algebra_ambient (p := p) (Γ := Γ) s hs

lemma ambient_direct_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.FinLeftgenAugpower n) := by
  let R : Type u := ULift.{u, 0} (ZMod p)
  let uR : UniformSpace R := ⊥
  letI : UniformSpace R := uR
  letI : TopologicalSpace R := uR.toTopologicalSpace
  let augMap : R →ₐ[ZMod p] ZMod p :=
    (ULift.algEquiv (R := ZMod p) (A := ZMod p)).toAlgHom
  have haug_cont : Continuous augMap := continuous_of_discreteTopology
  let canonicalUnit : Γ →* Units R := 1
  have hunit_cont : Continuous canonicalUnit := continuous_const
  have hunit_aug : ∀ g : Γ, augMap (canonicalUnit g : R) = 1 := by
    intro g
    simp [augMap, canonicalUnit]
  let A : GCAmbien (p := p) (Γ := Γ) s hs := {
    completedGroupAlgebra := R
    instRing := inferInstance
    instAlgebra := inferInstance
    instUniformSpace := uR
    topologicalRing := inferInstance
    instCompleteSpace := inferInstance
    t2Space := inferInstance
    instCompactSpace := inferInstance
    totallyDisconnected := inferInstance
    augmentationMap := augMap
    augmentationMap_continuous := haug_cont
    augmentationIdeal := RingHom.ker augMap.toRingHom
    augmentation_ideal_ker := rfl
    canonicalUnit := canonicalUnit
    canonicalUnit_continuous := hunit_cont
    canonicalUnit_augmentation := hunit_aug }
  have hdense : A.DenseAlgebraSpan := by
    dsimp [GCAmbien.DenseAlgebraSpan,
      GCAmbien.canonicalUnit,
      GCAmbien.completedGroupAlgebra, A, canonicalUnit]
    apply Set.eq_univ_of_forall
    intro x
    apply subset_closure
    let S : Set R := Set.range fun g : Γ => (canonicalUnit g : R)
    have hone_range : (1 : R) ∈ S := by
      exact ⟨1, by simp [canonicalUnit]⟩
    have hone_span : (1 : R) ∈ Submodule.span (ZMod p) S :=
      Submodule.subset_span hone_range
    rcases x with ⟨x0⟩
    have hx : x0 • (1 : R) = (⟨x0⟩ : R) := by
      ext
      change x0 • (1 : ZMod p) = x0
      simp
    rw [← hx]
    exact Submodule.smul_mem (Submodule.span (ZMod p) S) x0 hone_span
  have hgen : Nonempty (A.FinLeftgenAugpower n) := by
    haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    haveI : Fintype R := inferInstance
    letI := A.instRing
    letI := A.instAlgebra
    letI : Fintype A.completedGroupAlgebra := by
      dsimp [GCAmbien.completedGroupAlgebra, A]
      infer_instance
    exact
      ⟨{ leftGeneratingFamily :=
          DGFam.of_fintype
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) }⟩
  exact ⟨A, hdense, hgen⟩

lemma core_lazard_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (hJLCore :
      1 < n →
        ∃ C : DCCore
            (p := p) (Γ := Γ) s hs n,
          ∀ g : Γ,
            (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
              g ∈ zassenhausFiltration p Γ n) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Nonempty (DenseLazardIdentification C) := by
  by_cases hn : n ≤ 1
  · rcases dense_algebra_core
      (p := p) (Γ := Γ) s hs n with ⟨C⟩
    have hinput : JLInput C := by
      refine ⟨?_⟩
      intro hpos
      exact False.elim ((not_lt_of_ge hn) hpos)
    exact ⟨C,
      generators_lazard_identification
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput⟩
  · have hpos : 1 < n := Nat.lt_of_not_ge hn
    rcases hJLCore hpos with ⟨C, hJLpoint⟩
    have hinput : JLInput C := by
      refine ⟨?_⟩
      intro _hpos
      exact
        (dense_lazard_bound
          (p := p) (Γ := Γ) (s := s) (hs := hs) C).2 hJLpoint
    exact ⟨C,
      generators_lazard_identification
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput⟩

end Towers
