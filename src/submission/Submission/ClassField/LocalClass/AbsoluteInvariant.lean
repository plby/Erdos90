import Submission.ClassField.CrossedProducts.RelativeGroupMono
import Submission.ClassField.LocalBrauer.CanonicalCarryUnconditional

/-!
# Milne, Class Field Theory, Theorem III.2.1: the absolute invariant

The absolute multiplicative second cohomology group is the direct limit of
the finite Galois groups `H²(Gal(E/K), Eˣ)` constructed in Corollary
IV.3.16.  That corollary identifies this direct limit with the Brauer group.
Composing its inverse with the unconditional local Brauer invariant gives
the canonical invariant in the first assertion of Theorem III.2.1.
-/

namespace Submission.CField.LClass

noncomputable section

universe u

open CProduca LBrauer

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplication on the dependent direct limit has a deep instance term.
/-- **Theorem III.2.1 (absolute invariant).**  The direct-limit model of
`H²(Kᵃˡ/K, (Kᵃˡ)ˣ)` is canonically isomorphic to `ℚ / ℤ`.

The intermediate equivalence with `BrauerGroup K` is Corollary IV.3.16, so
this definition includes the cohomology/Brauer comparison rather than
replacing absolute cohomology by the Brauer group. -/
noncomputable def absoluteHInvariant :
    absoluteMultiplicativeH K ≃* Multiplicative LocalInvariant :=
  (brauerAbsoluteMultiplicative K).symm.trans
    (carryBrauerInvariant K)

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating the absolute direct-limit multiplication needs the same allowance.
/-- On a finite Galois level, the absolute invariant is the local Brauer
invariant of the corresponding crossed-product class. -/
@[simp]
theorem absolute_invariant_multiplicative
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (x : MHTwo (Gal(E/K)) Eˣ) :
    absoluteHInvariant K (absoluteMultiplicative2 K E x) =
      carryBrauerInvariant K (finiteHBrauer K E x) := by
  rfl

end

end Submission.CField.LClass
