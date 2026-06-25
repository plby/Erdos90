import Towers.ClassField.LocalBrauer.FiniteLocalExtension
import Towers.ClassField.LocalBrauer.UnramifiedNormOrder

/-!
# Chapter IV, Section 4: order invariance on finite local extensions

The canonical spectral norm on a finite extension is invariant under every
automorphism over the base field.  Consequently the normalized additive
order attached to its local-field structure is Galois invariant.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel

namespace FLExt

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Galois automorphisms preserve normalized order for the canonical
spectral local-field structure on a finite extension. -/
theorem unit_order_aut
    (σ : Gal(L/K)) (x : Lˣ) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L := nonarchimedeanLocalField K L
    localUnitOrder L
        (Additive.ofMul (Units.map σ.toMonoidHom x)) =
      localUnitOrder L (Additive.ofMul x) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L := nonarchimedeanLocalField K L
  apply le_antisymm
  · rw [local_order_valuation]
    rw [← Valuation.Compatible.vle_iff_le]
    change ‖(x : L)‖₊ ≤ ‖σ (x : L)‖₊
    exact NNReal.coe_le_coe.mp (spectralNorm_eq_of_equiv σ (x : L)).le
  · rw [local_order_valuation]
    rw [← Valuation.Compatible.vle_iff_le]
    change ‖σ (x : L)‖₊ ≤ ‖(x : L)‖₊
    exact NNReal.coe_le_coe.mp (spectralNorm_eq_of_equiv σ (x : L)).ge

end FLExt

end

end Towers.CField.LBrauer
