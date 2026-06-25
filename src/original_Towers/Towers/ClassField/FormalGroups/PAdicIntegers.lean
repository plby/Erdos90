import Mathlib.NumberTheory.Padics.RingHoms
import Towers.ClassField.FormalGroups.CyclotomicPowerSeries

/-!
# Class Field Theory, Chapter I, Example 2.13 over the p-adic integers

This file specializes the algebraic form of Example 2.13 to `ℤ_[p]`.
The quotient by `(p)` is identified with `ZMod p`, and the cyclotomic series
`(1+T)^p-1` is shown to satisfy the Lubin--Tate conditions.
-/

namespace Towers.CField.FGroups

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The residue ring of `ℤ_[p]` modulo `(p)` is `ZMod p`. -/
noncomputable def padicIntSpan :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq PadicInt.maximalIdeal_eq_span_p.symm).trans
    PadicInt.residueField

noncomputable instance padicIntFintype :
    Fintype (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :=
  Fintype.ofEquiv (ZMod p) (padicIntSpan p).symm.toEquiv

@[simp]
theorem padic_int_card :
    Fintype.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = p := by
  rw [Fintype.card_congr (padicIntSpan p).toEquiv, ZMod.card]

theorem padic_int_ne : (p : ℤ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem padic_int_unit : ¬ IsUnit (p : ℤ_[p]) := by
  rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem padic_int_field :
    IsField (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  exact (padicIntSpan p).toMulEquiv.isField
    (Field.toIsField (ZMod p))

/-- The cyclotomic series is a Lubin--Tate series over `ℤ_[p]`. -/
theorem lubin_tate_cyclotomic :
    LubinSeries (p : ℤ_[p])
      (Fintype.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}))
      (cyclotomicPowerSeries (R := ℤ_[p]) p) := by
  rw [padic_int_card]
  constructor
  · simp [cyclotomicPowerSeries]
  constructor
  · change PowerSeries.coeff 1 ((1 + PowerSeries.X) ^ p - 1) = (p : ℤ_[p])
    rw [map_sub]
    have hright : ((1 + PowerSeries.X) ^ p : PowerSeries ℤ_[p]) =
        (((1 : Polynomial ℤ_[p]) + Polynomial.X) ^ p).toPowerSeries := by
      simp
    rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
    simp
  · let Q := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}
    letI : Field Q := IsField.toField (padic_int_field p)
    letI : CharP Q p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
        change (p : Q) = 0
        rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}))]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl))
    letI : CharP (PowerSeries Q) p :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := Q)) p
    change PowerSeries.map
        (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}))
        ((1 + PowerSeries.X) ^ p - 1) = PowerSeries.X ^ p
    rw [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [add_pow_char]
    simp

/-- Example 2.13: the canonical Lubin--Tate formal group law for
`(1+T)^p-1` over `ℤ_[p]` is `X+Y+XY`. -/
theorem formal_law_multiplicative :
    lubinFormalLaw (p : ℤ_[p]) (padic_int_ne p)
        (padic_int_unit p) (padic_int_field p)
        (cyclotomicPowerSeries (R := ℤ_[p]) p)
        (lubin_tate_cyclotomic p) =
      FGLaw.multiplicative (R := ℤ_[p]) := by
  exact lubin_law_multiplicative
    (p : ℤ_[p]) (padic_int_ne p) (padic_int_unit p)
    (padic_int_field p) p
    (lubin_tate_cyclotomic p)

end

end Towers.CField.FGroups
