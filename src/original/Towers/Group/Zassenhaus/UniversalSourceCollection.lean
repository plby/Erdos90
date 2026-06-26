import Towers.Group.Zassenhaus.FactorSourceReduction
import Towers.Group.Zassenhaus.FormulaChooseSubstitution
import Towers.Group.Zassenhaus.RestrictedSharp

/-!
# Hall-power collection from universal packets and residual sources

A universal Hall-Petresco packet supplies all powered adjacent-swap
corrections.  The remaining nonterminal theorem can be stated concretely:
compress the intrinsic residual source of one active-weight symbolic factor
into a strictly heavier truncated source.

This file compiles those local residual-source recollections directly to the
restricted-sharp recursive collector and hence to the Claim 5 coordinate
polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A universal Hall-Petresco packet and explicit intrinsic residual-source
recollections sufficient for direct global symbolic Hall-power recollection.
-/
structure
    SUBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.UAInt.{u}
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  SUBuild

/--
Compile universal adjacent-swap packets and local residual-source recollections
to the direct restricted-sharp recursive collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      SUBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    RSRec
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    (builder.packet.powerSupportedFactory
      (by omega) lowerWeight)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal _nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorResidualSource lowerWeight hterminal factor hfactorWeight
      hfactorTruncated)
      |>.factorExpansion

end
  SUBuild

namespace TSInput

/--
A universal Hall-Petresco packet, explicit residual-source recollections, and
graded Hall bases construct the integer-valued coordinate polynomials required
by Claim 5.
-/
theorem
    coordSharpBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
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
    (builder :
      SUBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpRecursive
    hn H hH hsourceSupported
      (builder.restrictedRecursiveBuilder hinputWeight)
      hinputWeight

end TSInput

end TCTex
end Towers
