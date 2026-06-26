import
  Submission.Group.Zassenhaus.FixedRestartRouting
import Submission.Group.Zassenhaus.Ordered

/-!
# Fixed-packet routing from a unique principal occurrence

Generated restart routing needs one ordered split around the principal
`basic` recipe.  A unique occurrence of that recipe is enough; duplicate
nonbasic tail recipes do not interfere with strict support growth.

This file exposes the sharper fixed-route constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  TRRoutea

/--
Construct the fixed-packet route from its principal recipe invariant and a
unique occurrence of the principal `basic` recipe.
-/
noncomputable def principalUniqueBasic
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (callbacks :
      SRCallba
        d n inputWeight H packet)
    (principal :
      PFSubsti.TAPkt.PBRecipea
        packet)
    (hunique : packet.UniqueOccurrence) :
    TRRoutea
      d n inputWeight H packet where
  toSRCallba :=
    callbacks
  split := principal.ordered_unique_pair hunique

end
  TRRoutea

end TCTex
end Submission
