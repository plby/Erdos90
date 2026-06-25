import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.RestrictedSharp
import Towers.Group.Zassenhaus.WeightOneReduction

/-!
# Automatic symbolic Hall-power collection through class three

At cutoff at most four, every nonterminal intrinsic power-factor residual has
word weight one.  Such a factor is already its own active Hall layer, so its
intrinsic residual source recollects semantically to the empty list.

Combining this empty residual source with the explicit class-three
Hall-Petresco packet constructs power-coordinate polynomials from any
supported sourced input without a remaining residual-source hypothesis.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace
  TSBuilda

open TSSrc

/--
At cutoff at most four, the class-three packet and the empty weight-one
intrinsic residual source construct the recursive power collector.
-/
noncomputable def automatic_four
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (hn4 : n ≤ 4) :
    TSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet :=
    PFSubsti.TAPkt.n_four
      hn4
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      of_weight_one
        hn H hH factor hfactorWeightOne

end
  TSBuilda

open TSBuilda

namespace TSInput

/--
Through the class-three cutoff, a supported sourced input and graded Hall
bases construct the integer-valued power-coordinate polynomials required by
Claim 5.
-/
theorem dataAutomaticCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.sharpCollectionBuilder
    hn H hH hsourceSupported
      (automatic_four hn4)
      hinputWeight

end TSInput

end TCTex
end Towers
