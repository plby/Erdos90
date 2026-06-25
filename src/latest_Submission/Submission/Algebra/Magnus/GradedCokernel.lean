import Submission.Algebra.Magnus.IntegralCokernel
import Mathlib.LinearAlgebra.DirectSum.Basis


/-!
# The cokernel of the full integral graded Magnus map

This file assembles the fixed-weight Magnus maps into the map

`gr(F) → ℤ⟨X⟩`

from the direct sum of the positive lower-central layers to the full free
associative algebra.  Under the Hall PBW basis its range is exactly the span
of the singleton Hall sequences.  The complementary PBW coordinates prove
that the cokernel is torsion-free.
-/

namespace EChapma
namespace GCokern

open DirectSum
open Submission
open Submission.TBluepr

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

/-- The lower-central associated graded module of the free group, indexed
zero-based so component `n` is `γ_(n+1)(F) / γ_(n+2)(F)`. -/
abbrev FreeAssociatedGraded :
    Type _ :=
  ⨁ n : ℕ,
    Additive
      (LowerGradedLayer (FreeGroup X) n)

/-- The degree-`n+1` Magnus map, regarded as taking values in the full free
associative algebra. -/
noncomputable def gradedMagnusComponent
    (n : ℕ) :
    Additive
        (LowerGradedLayer (FreeGroup X) n) →ₗ[ℤ]
      Submission.HallTree.AssociativeWordPolynomial ℤ X :=
  (Submodule.subtype
      (AssociativeHomogeneousWords ℤ X (n + 1))).comp
    ((ICokern.homogeneousRealizationLinear
        (X := X) (n + 1)).symm.toLinearMap.comp
      (associatedGradedMagnus
        (FreeGroup X) n))

/-- The full integral graded Magnus map
`gr(F) → ℤ⟨X⟩`. -/
noncomputable def gradedMagnusLinear :
    FreeAssociatedGraded (X := X) →ₗ[ℤ]
      Submission.HallTree.AssociativeWordPolynomial ℤ X :=
  DirectSum.toModule ℤ ℕ
    (Submission.HallTree.AssociativeWordPolynomial ℤ X)
    (gradedMagnusComponent (X := X))

/-- The direct-sum Hall basis of the lower-central associated graded module. -/
noncomputable def associatedGradedBasis :
    Module.Basis
      (Σ n : ℕ, Submission.HallTree.BasicIndex (α := X) (n + 1))
      ℤ
      (FreeAssociatedGraded (X := X)) :=
  DFinsupp.basis
    (fun n => IMagnus.lowerCentralBasis (X := X) n)

/-- The full integral Hall PBW uniqueness input. -/
noncomputable def sequencePBWUniqueness :
    Submission.HallTree.PUInput
      (α := X) ℤ where
  injective :=
    (IMagnus.hallPBWInput (X := X)).eval_injective

/-- The Hall PBW basis of the full free associative algebra. -/
noncomputable def associativePBWBasis :
    Module.Basis
      {sequence : List (Submission.HallTree X) //
        Submission.HallTree.OrderedSequence sequence}
      ℤ
      (Submission.HallTree.AssociativeWordPolynomial ℤ X) :=
  (sequencePBWUniqueness (X := X)).basis ℤ

/-- The singleton PBW sequence associated to one homogeneous Hall index. -/
noncomputable def gradedSingletonSequence
    (i : Σ n : ℕ, Submission.HallTree.BasicIndex (α := X) (n + 1)) :
    {sequence : List (Submission.HallTree X) //
      Submission.HallTree.OrderedSequence sequence} :=
  ⟨[Submission.HallTree.indexedBasicTree i.2],
    Submission.HallTree.indexed_tree_sequence i.2⟩

/-- The subset of the full PBW basis indexed by singleton basic Hall trees. -/
noncomputable def gradedSingletonSet :
    Set
      {sequence : List (Submission.HallTree X) //
        Submission.HallTree.OrderedSequence sequence} :=
  Set.range (gradedSingletonSequence (X := X))

/-- A direct-sum Hall basis vector is the inclusion of its homogeneous Hall
basis vector. -/
theorem associated_graded_basis
    (i : Σ n : ℕ, Submission.HallTree.BasicIndex (α := X) (n + 1)) :
    associatedGradedBasis (X := X) i =
      DirectSum.lof ℤ ℕ
        (fun n =>
          Additive
            (LowerGradedLayer (FreeGroup X) n))
        i.1
        (IMagnus.lowerCentralBasis (X := X) i.1 i.2) := by
  rcases i with ⟨n, i⟩
  apply Module.Basis.apply_eq_iff.mpr
  ext j
  rcases j with ⟨m, j⟩
  change
    (IMagnus.lowerCentralBasis (X := X) m).repr
        ((DirectSum.lof ℤ ℕ
          (fun n =>
            Additive
              (LowerGradedLayer (FreeGroup X) n))
          n
          ((IMagnus.lowerCentralBasis (X := X) n) i)) m) j =
      Finsupp.single
        (⟨n, i⟩ :
          Σ k : ℕ, Submission.HallTree.BasicIndex (α := X) (k + 1))
        1
        (⟨m, j⟩ :
          Σ k : ℕ, Submission.HallTree.BasicIndex (α := X) (k + 1))
  by_cases h : n = m
  · subst m
    rw [DirectSum.lof_apply, Module.Basis.repr_self]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have hsigma :
          (⟨n, i⟩ :
            Σ k : ℕ, Submission.HallTree.BasicIndex (α := X) (k + 1)) ≠
            ⟨n, j⟩ := by
        intro heq
        exact hij (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
      simp [hij, hsigma]
  · have hz :
        (DirectSum.lof ℤ ℕ
          (fun k =>
            Additive
              (LowerGradedLayer (FreeGroup X) k))
          n
          ((IMagnus.lowerCentralBasis (X := X) n) i)) m =
            0 := by
      rw [DirectSum.lof_eq_of]
      exact DirectSum.of_eq_of_ne n m _ (Ne.symm h)
    rw [hz, map_zero, Finsupp.single_apply]
    have hsigma :
        (⟨n, i⟩ :
          Σ k : ℕ, Submission.HallTree.BasicIndex (α := X) (k + 1)) ≠
          ⟨m, j⟩ := by
      intro heq
      exact h (congrArg Sigma.fst heq)
    simp [hsigma]

/-- The full graded Magnus map sends a Hall basis vector to the corresponding
singleton vector in the full Hall PBW basis. -/
theorem graded_magnus_basis
    (i : Σ n : ℕ, Submission.HallTree.BasicIndex (α := X) (n + 1)) :
    gradedMagnusLinear (X := X)
        (associatedGradedBasis (X := X) i) =
      associativePBWBasis (X := X)
        (gradedSingletonSequence i) := by
  rw [associated_graded_basis]
  have hcomponent :
      gradedMagnusLinear (X := X)
          (DirectSum.lof ℤ ℕ
            (fun n =>
              Additive
                (LowerGradedLayer (FreeGroup X) n))
            i.1
            (IMagnus.lowerCentralBasis (X := X) i.1 i.2)) =
        gradedMagnusComponent (X := X) i.1
          (IMagnus.lowerCentralBasis (X := X) i.1 i.2) := by
    simpa only [gradedMagnusLinear] using
      (DirectSum.toModule_lof ℤ
        (φ := gradedMagnusComponent (X := X))
        i.1
        (IMagnus.lowerCentralBasis (X := X) i.1 i.2))
  rw [hcomponent]
  have hpbw :
      associativePBWBasis (X := X)
          (gradedSingletonSequence i) =
        Submission.HallTree.associativeWordProduct ℤ
          [Submission.HallTree.indexedBasicTree i.2] := by
    simpa [associativePBWBasis,
      gradedSingletonSequence] using
      (Submission.HallTree.PUInput.basis_apply
        ℤ
        (sequencePBWUniqueness (X := X))
        (gradedSingletonSequence i))
  rw [hpbw]
  change
    gradedMagnusComponent i.1
        (IMagnus.lowerCentralBasis (X := X) i.1 i.2) =
      Submission.HallTree.associativeWordProduct ℤ
        [Submission.HallTree.indexedBasicTree i.2]
  let domainBasis :=
    Submission.HallTree.freePBWUniqueness
      (IMagnus.hallPBWInput (X := X))
      (Nat.succ_pos i.1)
  have hdomain :
      domainBasis i.2 =
        (Submission.HallTree.indexedBasicTree i.2).freeLowerWeight
          (Submission.HallTree.indexed_tree_weight i.2) := by
    simp only [domainBasis,
      Submission.HallTree.freePBWUniqueness,
      Module.Basis.mk_apply]
  have himage :=
    ICokern.pbw_singleton_sequence
      (X := X) (Nat.succ_pos i.1) i.2
  rw [ICokern.augmentation_pbw_basis] at himage
  rw [← hdomain] at himage
  have hdomainBasis :
      domainBasis i.2 =
        IMagnus.lowerCentralBasis (X := X) i.1 i.2 :=
    rfl
  rw [hdomainBasis] at himage
  have hfixed :
      Submission.HallTree.freeMagnusInt
          X (Nat.succ_pos i.1)
          (IMagnus.lowerCentralBasis (X := X) i.1 i.2) =
        associatedGradedMagnus
          (FreeGroup X) i.1
          (IMagnus.lowerCentralBasis (X := X) i.1 i.2) := by
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one]
    change
      associatedGradedMagnus
          (FreeGroup X) i.1 _ =
        associatedGradedMagnus
          (FreeGroup X) i.1 _
    rfl
  rw [hfixed] at himage
  have hhomogeneous :
      (ICokern.homogeneousRealizationLinear
          (X := X) (i.1 + 1)).symm
          (associatedGradedMagnus
            (FreeGroup X) i.1
            (IMagnus.lowerCentralBasis (X := X) i.1 i.2)) =
        Submission.HallTree.associativeHomogeneousRep
          ℤ
          (ICokern.basicSingletonSequence i.2).1
          (ICokern.basicSingletonSequence i.2).property.2 := by
    apply
      (ICokern.homogeneousRealizationLinear
        (X := X) (i.1 + 1)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact himage.symm
  rw [gradedMagnusComponent]
  change
    ((ICokern.homogeneousRealizationLinear
        (X := X) (i.1 + 1)).symm
        (associatedGradedMagnus
          (FreeGroup X) i.1
          (IMagnus.lowerCentralBasis (X := X) i.1 i.2))).1 =
      Submission.HallTree.associativeWordProduct ℤ
        [Submission.HallTree.indexedBasicTree i.2]
  rw [hhomogeneous]
  rfl

set_option maxHeartbeats 1200000 in
-- Expanding the direct-sum Hall basis and transported PBW basis is expensive.
/-- The range of the full integral graded Magnus map is spanned by the
singleton vectors in the Hall PBW basis. -/
theorem graded_magnus_range :
    LinearMap.range (gradedMagnusLinear (X := X)) =
      Submodule.span ℤ
        (associativePBWBasis (X := X) ''
          gradedSingletonSet (X := X)) := by
  rw [linear_basis_image
    (gradedMagnusLinear (X := X))
    (associatedGradedBasis (X := X))]
  rw [show
    (fun i =>
      gradedMagnusLinear (X := X)
        (associatedGradedBasis (X := X) i)) =
      (fun i =>
        associativePBWBasis (X := X)
          (gradedSingletonSequence i)) by
      funext i
      exact graded_magnus_basis i]
  congr 1
  exact
    Set.range_comp'
      (associativePBWBasis (X := X))
      (gradedSingletonSequence (X := X))

omit [DecidableEq X] in
/-- Finite-alphabet form of Efrat--Chapman, Lemma 2.3: the cokernel of the
full integral graded Magnus map `gr(F) → ℤ⟨X⟩` is torsion-free. -/
theorem graded_magnus_cokernel :
    Module.IsTorsionFree ℤ
      (Submission.HallTree.AssociativeWordPolynomial ℤ X ⧸
        LinearMap.range (gradedMagnusLinear (X := X))) := by
  classical
  exact cokernel_torsion_basis
    (gradedMagnusLinear (X := X))
    (associativePBWBasis (X := X))
    (gradedSingletonSet (X := X))
    (graded_magnus_range (X := X))

end GCokern
end EChapma
