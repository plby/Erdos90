import Submission.Group.HallBasic.Word



noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/--
The associative leading polynomial of a Hall tree, represented directly in
the augmentation power indexed by the tree's weight.
-/
noncomputable def associativeLeadingRep
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    GroupAlgebra.augmentationPowerSubmodule R (FreeGroup α) w.weight := by
  refine ⟨w.associativeLeadingPolynomial R, ?_⟩
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      w.associative_leading_pow R

/--
The directly represented augmentation-layer class of a Hall tree's
associative leading polynomial.
-/
noncomputable def associativeLeadingDirect
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    GroupAlgebra.augmentationLayer R (FreeGroup α) w.weight :=
  Submodule.Quotient.mk (w.associativeLeadingRep R)

/--
Realizing the recursive homogeneous word polynomial gives the directly
represented leading-polynomial layer.
-/
theorem homogeneous_realization_rep
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    associativeHomogeneousRealization R α w.weight
        (w.associativeWordRep R) =
      w.associativeLeadingDirect R := by
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup α) w.weight)).mpr
  change
    freeAssociativeRealization R α (w.associativeWordPolynomial R) -
        w.associativeLeadingPolynomial R ∈
      GroupAlgebra.augmentationPower R (FreeGroup α) (w.weight + 1)
  rw [associative_realization_polynomial]
  simp

/--
The direct Hall-tree representative agrees with the layer inherited from the
general binary-commutator construction.
-/
theorem associative_leading_direct
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    w.associativeLeadingDirect R =
      w.associativeLeadingLayer R := by
  rw [associativeLeadingDirect,
    associativeLeadingLayer]
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup α) w.weight)).mpr
  change
    w.associativeLeadingPolynomial R - w.associativeLeadingPolynomial R ∈
      GroupAlgebra.augmentationPower R (FreeGroup α) (w.weight + 1)
  simp

/--
Realizing the recursive homogeneous word polynomial gives the Hall
leading-polynomial layer used by the Magnus bridge.
-/
theorem realization_associative_leading
    (R : Type*) [CommRing R]
    (w : HallTree α) :
  associativeHomogeneousRealization R α w.weight
        (w.associativeWordRep R) =
      w.associativeLeadingLayer R := by
  rw [homogeneous_realization_rep]
  exact associative_leading_direct R w

/--
The Magnus image of a Hall-tree class is the realization of its recursive
homogeneous word polynomial.
-/
theorem magnus_free_realization
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    GroupAlgebra.augmentationLayerReindex R (FreeGroup α)
        (Nat.sub_add_cancel w.weight_pos)
        (lowerAssociatedGraded R (FreeGroup α)
          (w.weight - 1) w.freeCentralLayer) =
      associativeHomogeneousRealization R α w.weight
        (w.associativeWordRep R) := by
  rw [
    lower_associated_graded,
    realization_associative_leading]

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u v

variable {α : Type u}

/--
Realize a Hall polynomial in an explicitly chosen homogeneous degree equal to
the tree's weight.
-/
def associativeRealizationWeight
    (R : Type*) [CommRing R]
    {n : ℕ}
    (w : HallTree α)
    (hweight : w.weight = n) :
    GroupAlgebra.augmentationLayer R (FreeGroup α) n :=
  associativeHomogeneousRealization R α n
    (w.associativeRepWeight R hweight)

/--
Fixed-weight realization is reindexing of the Hall leading-polynomial layer.
-/
theorem associative_realization_reindex
    (R : Type*) [CommRing R]
    {n : ℕ}
    (w : HallTree α)
    (hweight : w.weight = n) :
    w.associativeRealizationWeight R hweight =
      GroupAlgebra.augmentationLayerReindex R (FreeGroup α) hweight
        (w.associativeLeadingLayer R) := by
  subst n
  simpa [associativeRealizationWeight,
    associativeRepWeight] using
      w.realization_associative_leading
        R

/--
A Hall-tree lower-central class, reindexed into an explicitly chosen weight.
-/
def freeLowerWeight
    {n : ℕ}
    (w : HallTree α)
    (hweight : w.weight = n) :
    Additive
      (LowerGradedLayer (FreeGroup α) (n - 1)) :=
  cast
    (congrArg
      (fun k =>
        Additive
          (LowerGradedLayer (FreeGroup α) (k - 1)))
      hweight)
    w.freeCentralLayer

/--
At a positive fixed weight, compose the integer Magnus map with reindexing to
the matching augmentation layer.
-/
def freeMagnusInt
    (α : Type u)
    {n : ℕ}
    (hn : 0 < n) :
    Additive
        (LowerGradedLayer (FreeGroup α) (n - 1)) →ₗ[ℤ]
      GroupAlgebra.augmentationLayer ℤ (FreeGroup α) n :=
  (GroupAlgebra.augmentationLayerReindex ℤ (FreeGroup α)
      (Nat.sub_add_cancel hn)).toLinearMap.comp
    (associatedGradedMagnus
      (FreeGroup α) (n - 1))

/--
The fixed-weight integer Magnus map sends a Hall-tree class to the realization
of its homogeneous word polynomial.
-/
theorem free_magnus_int
    {n : ℕ}
    (hn : 0 < n)
    (w : HallTree α)
    (hweight : w.weight = n) :
    freeMagnusInt α hn
        (w.freeLowerWeight hweight) =
      w.associativeRealizationWeight ℤ hweight := by
  subst n
  simpa [freeMagnusInt,
    freeLowerWeight,
    associativeRealizationWeight,
    associativeRepWeight,
    associatedGradedMagnus] using
      w.magnus_free_realization
        ℤ

/--
If fixed-weight Hall word polynomials are linearly independent, their
realizations in the free-group augmentation layer are linearly independent.
-/
theorem associative_realization_independent
    (R : Type*) [CommRing R]
    [Finite α]
    {ι : Type v}
    {n : ℕ}
    (tree : ι → HallTree α)
    (hweight : ∀ i, (tree i).weight = n)
    (hpoly :
      LinearIndependent R fun i =>
        (tree i).associativeRepWeight R
          (hweight i)) :
    LinearIndependent R fun i =>
      (tree i).associativeRealizationWeight R
        (hweight i) := by
  letI := Fintype.ofFinite α
  classical
  let realization :=
    associativeHomogeneousRealization R α n
  have hrealization :
      LinearIndependent R
        (realization ∘ fun i =>
          (tree i).associativeRepWeight R
            (hweight i)) :=
    hpoly.map' realization
      (LinearMap.ker_eq_bot_of_injective
        (homogeneous_realization_injective
          R α n))
  simpa [associativeRealizationWeight,
    Function.comp_def] using hrealization

/--
Polynomial independence is enough to prove independence of the corresponding
fixed-weight Hall classes in the free-group lower-central associated graded.
-/
theorem free_independent_associative
    [Finite α]
    {ι : Type v}
    {n : ℕ}
    (hn : 0 < n)
    (tree : ι → HallTree α)
    (hweight : ∀ i, (tree i).weight = n)
    (hpoly :
      LinearIndependent ℤ fun i =>
        (tree i).associativeRepWeight ℤ
          (hweight i)) :
    LinearIndependent ℤ fun i =>
      (tree i).freeLowerWeight (hweight i) := by
  letI := Fintype.ofFinite α
  classical
  apply LinearIndependent.of_comp
    (freeMagnusInt α hn)
  have hrealization :=
    associative_realization_independent
      ℤ tree hweight hpoly
  convert hrealization using 1
  funext i
  exact
    free_magnus_int
      hn (tree i) (hweight i)

end HallTree
end Submission
