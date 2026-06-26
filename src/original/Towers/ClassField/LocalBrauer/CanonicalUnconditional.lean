import Towers.ClassField.LocalBrauer.CanonicalInvariantAssembly
import Towers.ClassField.LocalBrauer.CyclicFiniteStrictification

/-!
# Unconditional canonical local invariant

Arbitrary finite invariants on the canonical factorial unramified tower can
be strictified on their targets.  This removes the carry-inflation hypothesis
from the final direct-limit assembly.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca
open CIStrict

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Inclusion between consecutive relative Brauer groups in the canonical
factorial tower is injective. -/
theorem factorial_inclusion_injective (r : ℕ) :
    Function.Injective
      (brauerCofinalInclusion K
        (unramifiedFactorialLevel K)
        (factorial_level_monotone K)
        r (r + 1) (Nat.le_succ r)) := by
  change Function.Injective (Subgroup.inclusion
    (relative_brauer_mono K
      (factorial_level_monotone K (Nat.le_succ r))))
  exact Subgroup.inclusion_injective _

/-- Strictify the unconditional finite invariants associated to any chosen
family of cyclic Galois coordinates. -/
noncomputable def canonicalStrictifiedSystem
    (eGal : FactorialGalFamily K) :
    CanonicalFactorialSystem K := by
  let S := strictifiedFactorialSystem
    (f := brauerCofinalInclusion K
      (unramifiedFactorialLevel K)
      (factorial_level_monotone K))
    (factorial_inclusion_injective K)
    (FIData.finiteInvariant K
      (factorialInvariantData K) eGal)
  exact
    { equiv := S.equiv
      compatible := S.compatible }

/-- The standard levelwise cyclic Galois coordinates on the canonical
factorial tower. -/
def factorialGalFamily :
    FactorialGalFamily K :=
  factorialGalZ K

/-- The canonical factorial unramified tower is Brauer-cofinal.  This opaque
wrapper keeps the substantial unconditional cofinality proof out of later
dependent unification. -/
theorem factorialBrauerCofinal :
    ∀ x : BrauerGroup K, ∃ r,
      x ∈ relativeBrauerGroup K
        (unramifiedFactorialLevel K r) :=
  factorial_cofinal_unconditional K

set_option maxHeartbeats 1000000 in
-- Elaborating unconditional cofinality unfolds the dependent canonical tower.
/-- The unconditional local invariant assembled from any family of cyclic
Galois coordinates.  Target-side strictification makes the result independent
of a separate carry-inflation hypothesis. -/
noncomputable def brauerInvariantUnconditional
    (eGal : FactorialGalFamily K) :
    BrauerGroup K ≃* Multiplicative LocalInvariant :=
  assembleFactorialInvariant K
    (canonicalStrictifiedSystem K eGal)
    (factorialBrauerCofinal K)

set_option maxHeartbeats 1000000 in
-- Elaborating unconditional cofinality unfolds the dependent canonical tower.
/-- The unconditional invariant restricts to the strictified finite invariant
at every canonical factorial level. -/
@[simp]
theorem brauer_unconditional_coe
    (eGal : FactorialGalFamily K) (r : ℕ)
    (x : brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
    brauerInvariantUnconditional K eGal
        (x : BrauerGroup K) =
      invariantTorsionMul r
        ((canonicalStrictifiedSystem K eGal).equiv r x) :=
  assemble_factorial_coe K
    (canonicalStrictifiedSystem K eGal)
    (factorialBrauerCofinal K) r x

/-- A canonical unconditional local invariant obtained from the standard
levelwise cyclic Galois coordinates. -/
noncomputable def canonicalBrauerInvariant :
    BrauerGroup K ≃* Multiplicative LocalInvariant :=
  brauerInvariantUnconditional K
    (factorialGalFamily K)

end

end Towers.CField.LBrauer
