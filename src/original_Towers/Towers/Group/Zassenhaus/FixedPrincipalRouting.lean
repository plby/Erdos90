import
  Towers.Group.Zassenhaus.FixedRestartBoundary

/-!
# Principal-inventory constructors for fixed-packet restart routing

The fixed-packet structural-restart boundary should be entered through the
invariants actually available for a canonical Hall-Petresco packet: the
principal basic recipe belongs to its finite inventory and that inventory is
duplicate-free.

This file packages the dependent powered-pieces field after constructing its
active collector from those invariants, then lifts the result into the final
Claim 5 collection builder.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  PRRouteb

/--
Build scheduler-facing fixed-packet routing directly from principal inventory,
duplicate-free recipes, generated frontier callbacks, and powered pieces.
-/
noncomputable def principalNodup
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
    (principal :
      PFSubsti.TAPkt.PBRecipea
        packet)
    (hnodup : packet.recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight packet hinputWeight
          ((TRRoutea.principalNodup
            callbacks principal hnodup).fixedActiveFactory)) :
    PRRouteb
      d n inputWeight packet hinputWeight where
  activeRouting :=
    TRRoutea.principalNodup
      callbacks principal hnodup
  pieces := pieces

end
  PRRouteb

namespace
  SRBuilda

/--
Build the fixed-packet Claim 5 boundary from canonical packet inventory,
generated frontier callbacks, powered pieces, and the remaining ranked
recursion inputs.
-/
noncomputable def principalNodup
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
    (principal :
      PFSubsti.TAPkt.PBRecipea
        packet)
    (hnodup : packet.recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight packet hinputWeight
          ((TRRoutea.principalNodup
            callbacks principal hnodup).fixedActiveFactory))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect)
    (rankDefect :
      ∀ _factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight,
        ℕ) :
    SRBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := packet
  hinputWeight := hinputWeight
  routing :=
    PRRouteb.principalNodup
      hinputWeight callbacks principal hnodup pieces
  normalizerAbove := normalizerAbove
  cases := cases
  rankDefect := rankDefect

end
  SRBuilda

end TCTex
end Towers
