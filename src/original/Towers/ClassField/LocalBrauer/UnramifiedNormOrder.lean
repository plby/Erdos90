import Mathlib.RingTheory.Norm.Transitivity
import Towers.ClassField.LocalBrauer.LocalFieldOrder


/-!
# Normalized order of norms in an unramified extension

For an unramified extension of local fields, normalized order on the extension
restricts without a ramification factor and is invariant under the Galois
action.  The Galois product formula for the field norm then shows that norm
multiplies normalized order by the degree.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [Module.Finite K L] [IsGalois K L]

/-- Order-theoretic data of an unramified extension.  The first field says
that the normalized order has ramification index one; the second records that
the extended valuation is invariant under the Galois action. -/
structure UOExt : Prop where
  order_algebraMap (x : Kˣ) :
    localUnitOrder L
        (Additive.ofMul (Units.map (algebraMap K L) x)) =
      localUnitOrder K (Additive.ofMul x)
  order_aut (σ : Gal(L/K)) (x : Lˣ) :
    localUnitOrder L
        (Additive.ofMul (Units.map σ.toMonoidHom x)) =
      localUnitOrder L (Additive.ofMul x)

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L]
  [Valuation.Compatible (NormedField.valuation (K := L))] in
/-- The order of a Galois norm is the sum of the orders of the Galois
conjugates.  Compatibility with the base embedding and Galois invariance turn
this sum into degree times order. -/
theorem local_finrank_compatible
    (hrestrict : ∀ x : Kˣ,
      localUnitOrder L
          (Additive.ofMul (Units.map (algebraMap K L) x)) =
        localUnitOrder K (Additive.ofMul x))
    (hinvariant : ∀ (σ : Gal(L/K)) (x : Lˣ),
      localUnitOrder L
          (Additive.ofMul (Units.map σ.toMonoidHom x)) =
        localUnitOrder L (Additive.ofMul x))
    (x : Lˣ) :
    localUnitOrder K
        (Additive.ofMul (Units.map (Algebra.norm K) x)) =
      (Module.finrank K L : ℤ) *
        localUnitOrder L (Additive.ofMul x) := by
  have hnormUnits :
      Units.map (algebraMap K L) (Units.map (Algebra.norm K) x) =
        ∏ σ : Gal(L/K), Units.map σ.toMonoidHom x := by
    apply Units.ext
    simpa using Algebra.norm_eq_prod_automorphisms K (x : L)
  rw [← hrestrict (Units.map (Algebra.norm K) x), hnormUnits]
  change localUnitOrder L
      (∑ σ : Gal(L/K),
        Additive.ofMul (Units.map σ.toMonoidHom x)) = _
  rw [map_sum]
  simp_rw [hinvariant]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank]

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L]
  [Valuation.Compatible (NormedField.valuation (K := L))] in
/-- In an unramified order extension, field norm multiplies normalized order
by the extension degree. -/
theorem UOExt.order_norm
    (h : UOExt K L) (x : Lˣ) :
    localUnitOrder K
        (Additive.ofMul (Units.map (Algebra.norm K) x)) =
      (Module.finrank K L : ℤ) *
        localUnitOrder L (Additive.ofMul x) :=
  local_finrank_compatible K L
    h.order_algebraMap h.order_aut x

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L]
  [Valuation.Compatible (NormedField.valuation (K := L))] in
/-- Degree-indexed form of `UOExt.order_norm`, matching
the norm-order input used in the finite cyclic calculation. -/
theorem UOExt.order_norm_finrankeq
    (h : UOExt K L) {n : ℕ}
    (hdegree : Module.finrank K L = n) (x : Lˣ) :
    localUnitOrder K
        (Additive.ofMul (Units.map (Algebra.norm K) x)) =
      (n : ℤ) * localUnitOrder L (Additive.ofMul x) := by
  rw [h.order_norm K L x, hdegree]

end

end Towers.CField.LBrauer
