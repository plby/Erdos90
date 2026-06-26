import Submission.ClassField.LocalBrauer.DivisionAlgebraOrder


/-!
# Normalized order and valuation on a local field

This small interface records that normalized additive order reverses the
ordering on the multiplicative valuation.  It is used both in the
division-algebra filtration and in the local norm calculation.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Comparing normalized orders is the reverse of comparing valuations. -/
theorem local_order_valuation (x y : Kˣ) :
    localUnitOrder K (Additive.ofMul x) ≤
        localUnitOrder K (Additive.ofMul y) ↔
      valuation K (y : K) ≤ valuation K (x : K) := by
  rw [local_order_norm]
  rw [Valuation.norm_def, Valuation.norm_def, NNReal.coe_le_coe,
    (Valuation.RankOne.strictMono (valuation K)).le_iff_le]
  change (valuation K).restrict (y : K) ≤ (valuation K).restrict (x : K) ↔
    valuation K (y : K) ≤ valuation K (x : K)
  exact (valuation K).restrict_le_iff

end

end Submission.CField.LBrauer
