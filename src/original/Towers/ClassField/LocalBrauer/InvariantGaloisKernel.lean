import Towers.ClassField.CrossedProducts.IsMulCoboundary
import Towers.ClassField.LocalBrauer.CanonicalCarryUnconditional

/-!
# Local invariant base change on the relative Brauer group

For a finite Galois extension, the local-invariant base-change formula holds
unconditionally on the kernel of Brauer scalar extension.  Indeed, scalar
extension sends such a class to one, while Corollary IV.3.17 says that the
extension degree kills the original relative Brauer class.

This is the maximal part of formula (29) that follows solely from the current
finite-Galois Brauer-group API; identifying the two maps away from their
kernel still requires the cross-base Frobenius compatibility used in the full
local invariant base-change theorem.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u v

open BGroups CProduca

section Algebraic

variable (k E : Type u) (A : Type v) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E] [CommGroup A]

/-- Any two multiplicative invariants satisfy the expected degree formula on
the relative Brauer group of a finite Galois extension.  No local-field
structure is needed for this kernel calculation. -/
theorem brauer_base_change
    (invK : BrauerGroup k →* A) (invE : BrauerGroup E →* A)
    (x : BrauerGroup k) (hx : x ∈ relativeBrauerGroup k E) :
    invE (brauerBaseChange k E x) = invK x ^ Module.finrank k E := by
  have hbase : brauerBaseChange k E x = 1 :=
    (relative_brauer_group k E x).1 hx
  let y : relativeBrauerGroup k E := ⟨x, hx⟩
  have hy := relative_brauer_one k E y
  have hpow : x ^ Module.finrank k E = 1 := congrArg Subtype.val hy
  rw [hbase, map_one, ← map_pow, hpow, map_one]

end Algebraic

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Formula (29) holds unconditionally on every Brauer class split by a
finite Galois extension. -/
theorem change_relative_brauer
    (x : BrauerGroup K) (hx : x ∈ relativeBrauerGroup K L) :
    carryBrauerInvariant L (brauerBaseChange K L x) =
      (carryBrauerInvariant K x) ^ Module.finrank K L :=
  brauer_base_change K L
    (Multiplicative LocalInvariant)
    (carryBrauerInvariant K)
    (carryBrauerInvariant L) x hx

/-- Subtype form of `change_relative_brauer`. -/
theorem base_change_relative
    (x : relativeBrauerGroup K L) :
    carryBrauerInvariant L
        (brauerBaseChange K L (x : BrauerGroup K)) =
      (carryBrauerInvariant K (x : BrauerGroup K)) ^
        Module.finrank K L :=
  change_relative_brauer K L x x.property

end

end Towers.CField.LBrauer
