import Submission.Group.Zassenhaus.CtexCollectionBound

/-!
# Bridges from c.tex input packages to the free-truncation collection bound

This file keeps the strongest currently verified arbitrary-cutoff boundaries
available in the same namespace as the public collection theorem.  The
remaining work is to construct one of the input packages below for arbitrary
`d` and `n`.
-/

namespace Submission
namespace TCTex

universe u


/--
A concrete lower-triangular Hall `g h` law supplies the three Hall
collection-polynomial input families used by the paper-facing Ctex
collection bound.
-/
theorem inputs_gh_law
    (d n : ℕ)
    (hn : 2 ≤ n)
    (law :
      LGLaw
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    Ctex.HallCollectionInputs.{u} d n where
  power := fun e t ht =>
    law.collectedPolynomialData e t ht
  product := fun e =>
    law.collectedCoordinateData e
  inverse := fun e =>
    law.collectedInverseData hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      e

/--
The same bridge, immediately composed with the free-truncation collection
bound.  This isolates the exact lower-triangular Hall law still needed for an
unconditional arbitrary-cutoff proof.
-/
theorem free_gh_law
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (law :
      LGLaw
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_bounded_inputs
    (p := p) (d := d) (n := n) hn
    (inputs_gh_law
      d n hn law)

/--
Variant of the preceding bridge using the concrete Hall-family name from the
older finite-p-group collection file.  The two concrete families are
definitionally the same; this theorem keeps existing callers from having to
rewrite that detail by hand.
-/
theorem triangular_gh_law
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (law :
      LGLaw
        (n := n)
        (collectionConcreteCommutators.{u} d)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  simpa [concreteCommutatorsWeight,
    collectionConcreteCommutators] using
    free_gh_law
      (p := p) (d := d) (n := n) hn law

/--
Payload-shaped bridge for replacements of the old
`concreteHallTriangularGHLaw`: the associated-graded basis proof is already
available for the concrete Hall family, so the collection bound only consumes
the nonempty lower-triangular law component.
-/
theorem triangular_gh_payload
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (htri :
      let H : ∀ s : ℕ, BCWta.{u} d s :=
        collectionConcreteCommutators.{u} d
      (∀ s : ℕ,
          1 ≤ s →
            s < n →
              (H s).FormsAssocGradedbasis (n := n)) ∧
        Nonempty (LGLaw (n := n) H)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  dsimp only at htri
  rcases htri with ⟨_hH, ⟨law⟩⟩
  exact
    triangular_gh_law
      (p := p) (d := d) (n := n) hn law

theorem collection_triangular_gh
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (law :
      LGLaw
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (free_gh_law
      (p := p) (d := d) (n := n) hn law)

theorem collection_gh_law
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (law :
      LGLaw
        (n := n)
        (collectionConcreteCommutators.{u} d)) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (triangular_gh_law
      (p := p) (d := d) (n := n) hn law)

theorem gh_law_payload
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (htri :
      let H : ∀ s : ℕ, BCWta.{u} d s :=
        collectionConcreteCommutators.{u} d
      (∀ s : ℕ,
          1 ≤ s →
            s < n →
              (H s).FormsAssocGradedbasis (n := n)) ∧
        Nonempty (LGLaw (n := n) H)) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (triangular_gh_payload
      (p := p) (d := d) (n := n) hn htri)

/--
The paper-facing Hall collection-polynomial input package implies the target
free lower-central truncation collection bound.
-/
theorem free_truncation_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.HallCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_bounded_inputs
    (p := p) (d := d) (n := n) hn I

theorem p_collection_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.HallCollectionInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (free_truncation_inputs
      (p := p) (d := d) (n := n) hn I)

/--
Finite-index trace/profile collection inputs imply the target free
lower-central truncation collection bound.
-/
theorem truncation_collection_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.ProfileCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_collection_inputs
    (p := p) (d := d) (n := n) hn I

theorem collection_profile_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.ProfileCollectionInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  Ctex.collection_index_inputs
    (p := p) (d := d) (n := n) hn I

/--
Scalar finite-index count inputs imply the target free lower-central
truncation collection bound.
-/
theorem free_scalar_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.SCInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_scalar_inputs
    (p := p) (d := d) (n := n) hn I

theorem collection_scalar_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.SCInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  Ctex.scalar_count_inputs
    (p := p) (d := d) (n := n) hn I

/--
Decomposed scheduled finite-index multiplicity inputs imply the target free
lower-central truncation collection bound.
-/
theorem decomposed_scheduler_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.DecomposedSchedulerInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_decomposed_inputs
    (p := p) (d := d) (n := n) hn I

theorem decomposed_multiplicity_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.DecomposedSchedulerInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  Ctex.collection_decomposed_inputs
    (p := p) (d := d) (n := n) hn I

/--
The retained-recipe collection input package implies the target free
lower-central truncation collection bound.
-/
theorem free_collection_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.RCInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_recipe_inputs
    (p := p) (d := d) (n := n) hn I

theorem collection_recipe_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.RCInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  Ctex.p_recipe_inputs
    (p := p) (d := d) (n := n) hn I

/--
The universal signed-block collection input package implies the target free
lower-central truncation collection bound.
-/
theorem free_universal_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.UniversalCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  Ctex.uniform_universal_inputs
    (p := p) (d := d) (n := n) hn I

theorem collection_universal_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : Ctex.UniversalCollectionInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  Ctex.universal_block_inputs
    (p := p) (d := d) (n := n) hn I

end TCTex
end Submission
