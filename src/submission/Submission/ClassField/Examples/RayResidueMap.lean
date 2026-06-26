import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Exercise 0.13: the ray residue map for `ℚ`

For a positive modulus `m`, ideals of `ℚ` prime to `m` have unique positive generators of the
form `r / s`, with `r` and `s` positive and coprime to `m`.  We model these fractions as the
Grothendieck group of the multiplicative monoid of positive integers coprime to `m`.

The map of Exercise 0.13 sends `r / s` to `[r] [s]⁻¹` in `(ZMod m)ˣ`.  The results below prove
its formula, identify its kernel by congruence modulo `m`, prove surjectivity, and record the
induced quotient isomorphism.  This is the elementary `ℚ`-case underlying the ray class group;
no general ray-class-group API is assumed.
-/

namespace Submission.CField.Examples

open Algebra

/-- The multiplicative monoid of positive natural numbers coprime to `m`. -/
def PositiveCoprime (m : ℕ) : Submonoid ℕ where
  carrier := {n | 0 < n ∧ n.Coprime m}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Nat.mul_pos ha hb, ha'.mul_left hb'⟩

/-- The group of positive fractions whose numerator and denominator are coprime to `m`. -/
abbrev PositiveCoprimeFraction (m : ℕ) := GrothendieckGroup (PositiveCoprime m)

/-- Reduction modulo `m` on positive integers coprime to `m`. -/
def positiveCoprimeMonoid (m : ℕ) : PositiveCoprime m →* (ZMod m)ˣ where
  toFun n := ZMod.unitOfCoprime n n.property.2
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp

/-- The map `r / s ↦ [r] [s]⁻¹` from ideals of `ℚ` prime to `m` to `(ZMod m)ˣ`. -/
noncomputable def positiveCoprimeHom (m : ℕ) :
    PositiveCoprimeFraction m →* (ZMod m)ˣ :=
  GrothendieckGroup.lift (positiveCoprimeMonoid m)

/-- The formal positive fraction `r / s`. -/
def positiveCoprimeFraction (m r s : ℕ) (hr : 0 < r ∧ r.Coprime m)
    (hs : 0 < s ∧ s.Coprime m) : PositiveCoprimeFraction m :=
  GrothendieckGroup.of ⟨r, hr⟩ / GrothendieckGroup.of ⟨s, hs⟩

theorem positive_coprime_hom (m : ℕ) (r : PositiveCoprime m) :
    positiveCoprimeHom m (GrothendieckGroup.of r) =
      ZMod.unitOfCoprime r r.property.2 := by
  exact DFunLike.congr_fun
    (GrothendieckGroup.lift.symm_apply_apply (positiveCoprimeMonoid m)) r

theorem coprime_residue_fraction (m r s : ℕ)
    (hr : 0 < r ∧ r.Coprime m) (hs : 0 < s ∧ s.Coprime m) :
    positiveCoprimeHom m (positiveCoprimeFraction m r s hr hs) =
      ZMod.unitOfCoprime r hr.2 / ZMod.unitOfCoprime s hs.2 := by
  rw [positiveCoprimeFraction, map_div, positive_coprime_hom,
    positive_coprime_hom]

/-- The fraction `r / s` is in the kernel exactly when `r ≡ s (mod m)`.

Positivity of `r` and `s` is the infinite-place condition in the book's description of the
kernel; the congruence is the combined finite-place condition.
-/
theorem positive_coprime_fraction (m r s : ℕ)
    (hr : 0 < r ∧ r.Coprime m) (hs : 0 < s ∧ s.Coprime m) :
    positiveCoprimeHom m (positiveCoprimeFraction m r s hr hs) = 1 ↔
      r ≡ s [MOD m] := by
  rw [coprime_residue_fraction, div_eq_one]
  constructor
  · intro h
    rw [← ZMod.natCast_eq_natCast_iff]
    exact Units.ext_iff.mp h
  · intro h
    apply Units.ext
    exact (ZMod.natCast_eq_natCast_iff r s m).mpr h

/-- Every residue-class unit has a positive representative coprime to a positive modulus. -/
theorem positive_coprime_surjective {m : ℕ} (hm : 0 < m) :
    Function.Surjective (positiveCoprimeHom m) := by
  intro u
  let n : PositiveCoprime m :=
    ⟨(u : ZMod m).val + m,
      ⟨Nat.add_pos_right _ hm,
        Nat.coprime_add_self_left.mpr (ZMod.val_coe_unit_coprime u)⟩⟩
  refine ⟨GrothendieckGroup.of n, ?_⟩
  rw [positive_coprime_hom]
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, n]
  rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  haveI : NeZero m := ⟨hm.ne'⟩
  exact ZMod.natCast_zmod_val (u : ZMod m)

/-- Exercise 0.13's induced isomorphism, stated for the elementary positive-fraction model. -/
noncomputable def coprimeFractionEquiv {m : ℕ} (hm : 0 < m) :
    PositiveCoprimeFraction m ⧸ (positiveCoprimeHom m).ker ≃* (ZMod m)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (positiveCoprimeHom m)
    (positive_coprime_surjective hm)

end Submission.CField.Examples
