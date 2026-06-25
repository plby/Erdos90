import Submission.Group.Zassenhaus.SemanticInsertionScheduling
import Submission.Group.Zassenhaus.Recursion

/-!
# Semantic delegation of higher-weight symbolic Hall power corrections

Every retained correction emitted by a truncated Hall-power swap has strictly
higher word weight than either parent.  Thus a collector working in stratum
`lowerWeight` may delegate the correction packet to a semantic normalizer for
stratum `lowerWeight + 1`.

This file packages that handoff.  Together with the terminal high-weight
normalizer, it supplies the filtration recursion interface needed by a
universal symbolic collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/--
A semantic normalizer for all physically truncated factor lists supported in
one lower-weight stratum.
-/
structure TSNormalb
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  normalize :
    ∀ source : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n source →
      SPFactora.WordWeightLeast lowerWeight source →
        ∃ coordinates : CCExpans H inputWeight,
          coordinates.NTBelow lowerWeight ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q
                  (coordinates.factors (n := n)) =
                SPFactora.listEval (n := n) q source

namespace TSNormalb

/-- Endpoint insertion folds to a semantic normalizer for the same stratum. -/
def ofInsertionKernel
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (kernel :
      TSInserta
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H where
  normalize := kernel.exists_normalization

/--
The commutative region `n ≤ 2 * lowerWeight` has a canonical semantic
normalizer.
-/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  ofInsertionKernel
    (TSInserta.of_highWeight
      hn H hH hcutoff)

end TSNormalb

namespace TCPkt

/-- A truncated correction packet is physically truncated as a list. -/
lemma isTruncated_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A) :
    SPFactora.IsTruncated n C.factors :=
  fun x hx => C.word_weight_cutoff x hx

/--
Corrections emitted from a left parent in stratum `lowerWeight` lie in the
next stratum.
-/
lemma least_succ_left
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB :
      lowerWeight ≤ B.word.weight PEAddres.weight) :
    SPFactora.WordWeightLeast (lowerWeight + 1) C.factors := by
  intro x hx
  have hxrise := C.word_weight_left x hx
  omega

/--
Corrections emitted from a right parent in stratum `lowerWeight` lie in the
next stratum.
-/
lemma least_succ_right
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA :
      lowerWeight ≤ A.word.weight PEAddres.weight) :
    SPFactora.WordWeightLeast (lowerWeight + 1) C.factors := by
  intro x hx
  have hxrise := C.word_weight_right x hx
  omega

end TCPkt

/--
A semantically normalized correction packet.  Its coordinate endpoint remains
in the next support stratum and evaluates to the commutator correction required
by the parent swap.
-/
structure TSNorma
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (lowerWeight : ℕ)
    (C : TCPkt n B A) where
  coordinates :
    CCExpans H inputWeight
  coordinates_no_below :
    coordinates.NTBelow (lowerWeight + 1)
  list_eval_coordinates :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          (coordinates.factors (n := n)) =
        ⁅B.eval (n := n) q, A.eval (n := n) q⁆

namespace TCPkt

/--
Delegate a correction packet to the next-stratum normalizer using the support
of its left parent.
-/
lemma normalization_left
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB :
      lowerWeight ≤ B.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TSNorma
        lowerWeight C) := by
  rcases normalizer.normalize C.factors C.isTruncated_factors
      (C.least_succ_left hB) with
    ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
  exact ⟨{
    coordinates := coordinates
    coordinates_no_below := hcoordinatesSupported
    list_eval_coordinates := fun q =>
      (hcoordinates q).trans (C.listEval_eq q) }⟩

/--
Delegate a correction packet to the next-stratum normalizer using the support
of its right parent.
-/
lemma semantic_normalization
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA :
      lowerWeight ≤ A.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TSNorma
        lowerWeight C) := by
  rcases normalizer.normalize C.factors C.isTruncated_factors
      (C.least_succ_right hA) with
    ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
  exact ⟨{
    coordinates := coordinates
    coordinates_no_below := hcoordinatesSupported
    list_eval_coordinates := fun q =>
      (hcoordinates q).trans (C.listEval_eq q) }⟩

end TCPkt

namespace TSInput

/-- A supported semantic normalizer upgrades a correctly sourced list to Claim 5. -/
theorem supportedSemanticNormalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight input.source)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight := by
  rcases normalizer.normalize input.source input.source_isTruncated
      hsourceSupported with
    ⟨coordinates, _hcoordinatesSupported, hcoordinates⟩
  exact
    CEData.toPolynomialData hinputWeight
      (collected_expansion_factors
        coordinates fun q => (hcoordinates q).trans (input.list_eval_source q))

end TSInput

end TCTex
end Submission
