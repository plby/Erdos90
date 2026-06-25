import Towers.Algebra.Magnus.IntegralMagnus
import Towers.Algebra.Linear.TorsionFreeCokernel


/-!
# Torsion-free cokernels of the integral graded Magnus map

The Hall PBW basis of homogeneous associative word polynomials maps
isomorphically to the corresponding augmentation layer. The image of the
lower-central graded Magnus map is spanned by the singleton Hall basis
vectors, so its cokernel is the complementary free coordinate module.
-/

namespace EChapma
namespace ICokern

open Towers
open Towers.TBluepr

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

omit [Fintype X] [DecidableEq X] in
/-- Full Hall PBW uniqueness also gives injectivity of each homogeneous
evaluation map. -/
theorem standard_sequence_injective
    [Finite X]
    (n : ℕ) :
    Function.Injective
      (Towers.HallTree.orderedStandardSequence
        (α := X) ℤ n) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  intro left right heq
  have hglobal :
      Towers.HallTree.standardSequenceInclusion
          (α := X) ℤ n left =
        Towers.HallTree.standardSequenceInclusion
          (α := X) ℤ n right := by
    apply
      (IMagnus.hallPBWInput
        (X := X)).eval_injective
    rw [
      Towers.HallTree.standard_sequence_inclusion,
      Towers.HallTree.standard_sequence_inclusion]
    exact congrArg Subtype.val heq
  exact Submodule.inclusion_injective _ hglobal

/-- Degreewise Hall PBW evaluation is a linear equivalence. -/
noncomputable def homogeneousPBWLinear
    (n : ℕ) :
    Towers.HallTree.orderedSequenceSubmodule
        (α := X) ℤ n ≃ₗ[ℤ]
      AssociativeHomogeneousWords ℤ X n :=
  LinearEquiv.ofBijective
    (Towers.HallTree.orderedStandardSequence
      (α := X) ℤ n)
    ⟨standard_sequence_injective
        (X := X) n,
      Towers.HallTree.standard_sequence_surjective
        (α := X) ℤ n⟩

/-- The homogeneous Hall PBW basis. -/
noncomputable def homogeneousPBWBasis
    (n : ℕ) :
    Module.Basis
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence}
      ℤ
      (AssociativeHomogeneousWords ℤ X n) :=
  (Towers.HallTree.standardSequenceBasis
      (α := X) ℤ n).map
    (homogeneousPBWLinear (X := X) n)

omit [Fintype X] [DecidableEq X] in
/-- The coordinate basis vector of one homogeneous ordered sequence is its
singleton coordinate. -/
theorem ordered_standard_sequence
    (n : ℕ)
    (sequence :
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence}) :
    Towers.HallTree.standardSequenceBasis
        (α := X) ℤ n sequence =
      ⟨Finsupp.single sequence.1 1,
        Finsupp.single_mem_supported ℤ 1 sequence.property⟩ := by
  apply Subtype.ext
  simpa [
    Towers.HallTree.standardSequenceBasis] using
    (Finsupp.supportedEquivFinsupp_symm_single
      (R := ℤ)
      {sequence : List (Towers.HallTree X) |
        Towers.HallTree.OrderedStandardSequence n sequence}
      sequence (1 : ℤ))

omit [DecidableEq X] in
/-- A homogeneous PBW basis vector is the polynomial product represented by
its ordered Hall sequence. -/
theorem homogeneous_pbw_basis
    (n : ℕ)
    (sequence :
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence}) :
    homogeneousPBWBasis (X := X) n sequence =
      Towers.HallTree.associativeHomogeneousRep
        ℤ sequence.1 sequence.property.2 := by
  classical
  rw [homogeneousPBWBasis, Module.Basis.map_apply,
    ordered_standard_sequence]
  apply Subtype.ext
  change
    Finsupp.linearCombination ℤ
        (Towers.HallTree.associativeWordProduct ℤ)
        (Finsupp.single sequence.1 1) =
      Towers.HallTree.associativeWordProduct ℤ sequence.1
  simp [            ]

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- A homogeneous word polynomial realizes uniquely in the free-group
augmentation layer. -/
theorem associative_homogeneous_realization
    [Finite X]
    (n : ℕ) :
    Function.Surjective
      (associativeHomogeneousRealization ℤ X n) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← free_vector_top ℤ X n]
  apply Submodule.span_le.mpr
  rintro y ⟨word, rfl⟩
  let w : AssociativeWordsLength X n :=
    (associativeVectorEquiv X n).symm word
  refine ⟨associativeHomogeneousWords ℤ X n w, ?_⟩
  rw [homogeneous_realization_basis]
  change
    freeVectorLayer ℤ X
        (associativeVectorEquiv X n w) =
      freeVectorLayer ℤ X word
  rw [show associativeVectorEquiv X n w = word by
    exact (associativeVectorEquiv X n).apply_symm_apply word]

/-- Homogeneous word polynomials are linearly equivalent to the augmentation
layer. -/
noncomputable def homogeneousRealizationLinear
    (n : ℕ) :
    AssociativeHomogeneousWords ℤ X n ≃ₗ[ℤ]
      GroupAlgebra.augmentationLayer ℤ (FreeGroup X) n :=
  LinearEquiv.ofBijective
    (associativeHomogeneousRealization ℤ X n)
    ⟨homogeneous_realization_injective ℤ X n,
      associative_homogeneous_realization
        (X := X) n⟩

/-- The Hall PBW basis transported to the integral augmentation layer. -/
noncomputable def augmentationPBWBasis
    (n : ℕ) :
    Module.Basis
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence}
      ℤ
      (GroupAlgebra.augmentationLayer ℤ (FreeGroup X) n) :=
  (homogeneousPBWBasis (X := X) n).map
    (homogeneousRealizationLinear (X := X) n)

omit [DecidableEq X] in
/-- Evaluation of an augmentation PBW basis vector is the realization of its
Hall polynomial product. -/
theorem augmentation_pbw_basis
    (n : ℕ)
    (sequence :
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence}) :
    augmentationPBWBasis (X := X) n sequence =
      associativeHomogeneousRealization ℤ X n
        (Towers.HallTree.associativeHomogeneousRep
          ℤ sequence.1 sequence.property.2) := by
  classical
  rw [augmentationPBWBasis, Module.Basis.map_apply,
    homogeneous_pbw_basis]
  rfl

/-- The ordered PBW singleton corresponding to one indexed basic Hall tree. -/
noncomputable def basicSingletonSequence
    {n : ℕ}
    (i : Towers.HallTree.BasicIndex (α := X) n) :
    {sequence : List (Towers.HallTree X) //
      Towers.HallTree.OrderedStandardSequence n sequence} :=
  ⟨[Towers.HallTree.indexedBasicTree i],
    Towers.HallTree.indexed_tree_sequence i,
    by simp [Towers.HallTree.indexed_tree_weight]⟩

/-- A singleton augmentation PBW vector is the fixed-weight Magnus image of
the corresponding lower-central Hall class. -/
theorem pbw_singleton_sequence
    {n : ℕ} (hn : 0 < n)
    (i : Towers.HallTree.BasicIndex (α := X) n) :
    augmentationPBWBasis (X := X) n
        (basicSingletonSequence i) =
      Towers.HallTree.freeMagnusInt X hn
        ((Towers.HallTree.indexedBasicTree i).freeLowerWeight
          (Towers.HallTree.indexed_tree_weight i)) := by
  rw [
    Towers.HallTree.free_magnus_int]
  rw [augmentation_pbw_basis]
  unfold
    Towers.HallTree.associativeRealizationWeight
  congr 1
  apply Subtype.ext
  simp [basicSingletonSequence,
    Towers.HallTree.associativeHomogeneousRep,
    Towers.HallTree.associativeRepWeight]

/-- The subset of homogeneous PBW indices consisting of singleton basic Hall
trees. -/
noncomputable def basicSingletonSet
    (n : ℕ) :
    Set
      {sequence : List (Towers.HallTree X) //
        Towers.HallTree.OrderedStandardSequence n sequence} :=
  Set.range (basicSingletonSequence (X := X))

set_option maxHeartbeats 1200000 in
-- Normalizing the transported Hall bases in this range calculation is expensive.
/-- The fixed-weight integral Magnus range is the span of the singleton
subset of the augmentation PBW basis. -/
theorem free_magnus_range
    {n : ℕ} (hn : 0 < n) :
    LinearMap.range
        (Towers.HallTree.freeMagnusInt
          X hn) =
      Submodule.span ℤ
        (augmentationPBWBasis (X := X) n ''
          basicSingletonSet (X := X) n) := by
  let domainBasis :=
    Towers.HallTree.freePBWUniqueness
      (IMagnus.hallPBWInput (X := X)) hn
  have hdomain
      (i : Towers.HallTree.BasicIndex (α := X) n) :
      domainBasis i =
        (Towers.HallTree.indexedBasicTree i).freeLowerWeight
          (Towers.HallTree.indexed_tree_weight i) := by
    simp only [domainBasis,
      Towers.HallTree.freePBWUniqueness,
      Module.Basis.mk_apply]
  have hfamily :
      (fun i : Towers.HallTree.BasicIndex (α := X) n =>
        Towers.HallTree.freeMagnusInt X hn
          (domainBasis i)) =
        (fun i =>
          augmentationPBWBasis (X := X) n
            (basicSingletonSequence i)) := by
    funext i
    rw [hdomain i]
    exact
      (pbw_singleton_sequence
        (X := X) hn i).symm
  rw [linear_basis_image
    (Towers.HallTree.freeMagnusInt X hn)
    domainBasis]
  rw [hfamily]
  congr 1
  exact
    Set.range_comp'
      (augmentationPBWBasis (X := X) n)
      (basicSingletonSequence (X := X))

omit [Fintype X] [DecidableEq X] in
/-- Finite-alphabet form of Efrat--Chapman, Corollary 2.4, integral case:
the cokernel of every positive fixed-weight graded Magnus map is
torsion-free. -/
theorem magnus_cokernel_torsion
    [Finite X]
    {n : ℕ} (hn : 0 < n) :
    Module.IsTorsionFree ℤ
      (GroupAlgebra.augmentationLayer ℤ (FreeGroup X) n ⧸
        LinearMap.range
          (Towers.HallTree.freeMagnusInt
            X hn)) :=
  by
    classical
    letI : Fintype X := Fintype.ofFinite X
    exact cokernel_torsion_basis
      (Towers.HallTree.freeMagnusInt X hn)
      (augmentationPBWBasis (X := X) n)
      (basicSingletonSet (X := X) n)
      (free_magnus_range
        (X := X) hn)

omit [Fintype X] [DecidableEq X] in
/-- Integral divisibility lifting through the fixed-weight Magnus map. This is
the cancellation step used in Efrat--Chapman, Corollary 2.4. -/
theorem preimage_magnus_range
    [Finite X]
    {n : ℕ} (hn : 0 < n)
    {a : ℤ} (ha : a ≠ 0)
    {y : GroupAlgebra.augmentationLayer ℤ (FreeGroup X) n}
    (hy :
      a • y ∈
        LinearMap.range
          (Towers.HallTree.freeMagnusInt
            X hn)) :
    ∃ x,
      Towers.HallTree.freeMagnusInt
          X hn x =
        y := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  exact
    cokernel_torsion_free
      (Towers.HallTree.freeMagnusInt X hn)
      (magnus_cokernel_torsion
        (X := X) hn)
      (isRegular_iff_ne_zero.mpr ha) hy

end ICokern
end EChapma
