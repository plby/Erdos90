import Towers.Group.Zassenhaus.SourceRecollectionOperations
import Towers.Group.Zassenhaus.SharpCorrectionNormalization

/-!
# Normalizing recollected symbolic Hall-power sources

A semantic source recollection replaces a raw symbolic list by an
evaluation-equivalent list supported at a stronger Hall-weight bound.  Once a
normalizer is available at that stronger bound, the recollected source may be
normalized without returning to the weaker physical support of the raw list.

For correction packets, this packages a sharper semantic correction endpoint:
the coordinate block retains the full support reached by recollection.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSRecol

/--
Normalize an upward-recollected source at the support bound reached by its
higher source.
-/
lemma exists_normalizedCoordinates
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {rawSource : List (SPFactora H inputWeight)}
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H) :
    ∃ coordinates : CCExpans H inputWeight,
      coordinates.NTBelow lowerWeight ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (coordinates.factors (n := n)) =
            SPFactora.listEval (n := n) q rawSource := by
  rcases normalizer.normalize recollection.higherSource
      recollection.higher_source_truncated
      recollection.higher_weight_least with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨coordinates, hcoordinates, fun q =>
      (heval q).trans (recollection.list_higher_raw q)⟩

end TSRecol

namespace TCPkt

/--
A recollected correction packet admits a normalized endpoint retaining the
complete support bound reached by recollection.
-/
lemma nonempty_semantic_normalization
    {d n inputWeight supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (recollection :
      TSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := supportWeight) H)
    (hsupportWeightPos : 1 ≤ supportWeight) :
    Nonempty
      (TSNorma
        (supportWeight - 1) C) := by
  rcases recollection.exists_normalizedCoordinates normalizer with
    ⟨coordinates, hcoordinates, heval⟩
  exact ⟨{
      coordinates := coordinates
      coordinates_no_below := by
        simpa [Nat.sub_add_cancel hsupportWeightPos] using hcoordinates
      list_eval_coordinates := fun q => (heval q).trans (C.listEval_eq q)
    }⟩

/--
Normalize a recollected correction packet while retaining the complete
support bound reached by recollection.
-/
noncomputable def normalization_recollection_support
    {d n inputWeight supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (recollection :
      TSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := supportWeight) H)
    (hsupportWeightPos : 1 ≤ supportWeight) :
    TSNorma
      (supportWeight - 1) C :=
  Classical.choice
    (C.nonempty_semantic_normalization
      recollection normalizer hsupportWeightPos)

/--
Expose a recollected correction packet through any weaker parent-support
interface.
-/
noncomputable def normalization_source_recollection
    {d n inputWeight lowerWeight supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (recollection :
      TSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := supportWeight) H)
    (hsupport : lowerWeight + 1 ≤ supportWeight) :
    TSNorma
      lowerWeight C :=
  (C.normalization_recollection_support recollection
    normalizer (by omega)).weaken (by omega)

end TCPkt

end TCTex
end Towers
