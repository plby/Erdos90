import Towers.Group.Zassenhaus.InverseUniversalClosure
import Towers.Group.Zassenhaus.RestrictedSharp
import Towers.Group.Zassenhaus.WeightOneReduction

/-!
# Automatic class-three Hall-power collection from retained recipes

Through cutoff four, the selected retained recipes form the Hall-Petresco
packet consumed by the recursive power collector.  Every nonterminal intrinsic
residual has weight one, so the existing empty residual-source recollection
completes the automatic collector.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open
  CCThree
open
  TSSrc

namespace
  TSBuilda

/--
Through cutoff four, the retained recipe packet and empty weight-one intrinsic
residual sources construct the recursive power collector.
-/
noncomputable def automatic_recipe_four
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
    all_n_four hn4
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      of_weight_one hn H hH factor hfactorWeightOne

end
  TSBuilda

namespace TSInput

open
  TSBuilda

/--
Through cutoff four, a supported sourced input and the retained recipe packet
construct the integer-valued power-coordinate polynomials required by Claim 5.
-/
theorem recipeAutomaticCollection
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
      (automatic_recipe_four hn4)
      hinputWeight

end TSInput

end TCTex
end Towers
