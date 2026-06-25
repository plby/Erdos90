import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.ReductionSourceCollection
import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Concrete Hall-tree collection through class three

At cutoff at most four, every nonterminal concrete Hall-tree residual has
ordinary word weight one.  The explicit reduction residual and its comparison
with the semantic active Hall block both recollect to the empty list.

Consequently the cutoff-specific class-three Hall-Petresco packet supplies the
full concrete residual-source builder.  A parallel constructor records that
any genuinely universal packet supplies the same builder after specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  TCBuildf

/--
Through class three, a universal Hall-Petresco packet automa supplies
both concrete Hall-tree residual recollections.
-/
noncomputable def automatic_four
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (packet :
      PFSubsti.UAInt.{u})
    (hn4 : n ≤ 4) :
    TCBuildf
      (inputWeight := inputWeight) hn hH where
  packet := packet
  basicResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    exact
      TSRecollb.of_weight_one
        factor hfactorWeightOne
  comparisonResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      TCRecoll.of_weight_one
        hn hH factor hfactorWeightOne

end
  TCBuildf

namespace
  TCBuilde

/--
Through class three, the explicit cutoff Hall-Petresco packet automa
supplies both concrete Hall-tree residual recollections.
-/
noncomputable def automatic_packet_four
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (hn4 : n ≤ 4) :
    TCBuilde
      (inputWeight := inputWeight) hn hH where
  packet :=
    PFSubsti.TAPkt.n_four
      hn4
  basicResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    exact
      TSRecollb.of_weight_one
        factor hfactorWeightOne
  comparisonResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight PEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      TCRecoll.of_weight_one
        hn hH factor hfactorWeightOne

end
  TCBuilde

open
  TCBuildf
open
  TCBuilde

namespace TSInput

/--
For canonical Hall families through class three, a universal Hall-Petresco
packet and a supported sourced input construct the Claim 5 power-coordinate
polynomials through the concrete Hall-tree residual route.
-/
theorem
    automaticUniversalCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (packet :
      PFSubsti.UAInt.{u})
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.concreteCollectionBuilder
    hn hsourceSupported
      (automatic_four packet hn4)
      hinputWeight

/--
For canonical Hall families through class three, a supported sourced input
constructs the Claim 5 power-coordinate polynomials through the concrete
Hall-tree residual route.
-/
theorem
    coordinateAutomaticCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordinateCollectionBuilder
    hn hsourceSupported
      (automatic_packet_four hn4)
      hinputWeight

end TSInput
end TCTex
end Towers
