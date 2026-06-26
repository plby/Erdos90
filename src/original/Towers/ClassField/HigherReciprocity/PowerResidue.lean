import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Chapter VIII, Section 5: the power-residue exact sequence

The power residue symbol at a prime is obtained by raising a nonzero residue
class to the exponent `(q - 1) / n`.  Statements 5.1 and the finite-field
part of 5.2 reduce to the cyclic-group facts proved below.  The Hensel step
from the residue field to the completion is proved separately in
`Statement52Hensel`.
-/

namespace Towers.CField.HRecip

noncomputable section

/-- The finite-group version of the power residue symbol: in a group of
order `N`, with `n ∣ N`, send `x` to `x ^ (N / n)`. -/
def powerResidueValue {G : Type*} [CommGroup G] [Finite G]
    (n : ℕ) (x : G) : G :=
  x ^ (Nat.card G / n)

/-- **Statement VIII.5.1, finite-group core.** The power residue value is
multiplicative. -/
theorem residue_value_mul {G : Type*} [CommGroup G] [Finite G]
    (n : ℕ) (x y : G) :
    powerResidueValue n (x * y) =
      powerResidueValue n x * powerResidueValue n y := by
  simp [powerResidueValue, mul_pow]

/-- When `n` divides the group order, every power residue value is an
`n`th root of unity. -/
theorem residue_value_pow {G : Type*} [CommGroup G] [Finite G]
    {n : ℕ} (hn : n ∣ Nat.card G) (x : G) :
    powerResidueValue n x ^ n = 1 := by
  rw [powerResidueValue, ← pow_mul, Nat.div_mul_cancel hn, pow_card_eq_one']

/-- The exactness assertion behind Statement VIII.5.2(a) `(a) ↔ (b)`:
in a finite cyclic group whose order is divisible by `n`, the kernel of
`x ↦ x ^ (|G| / n)` is exactly the subgroup of `n`th powers. -/
theorem power_residue_value
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {n : ℕ} (hn : n ∣ Nat.card G) (x : G) :
    powerResidueValue n x = 1 ↔ ∃ y : G, y ^ n = x := by
  let e := Nat.card G / n
  have hcard : Nat.card G = n * e := by
    simp only [e]
    exact (Nat.mul_div_cancel' hn).symm
  have he0 : e ≠ 0 := by
    intro he
    have : Nat.card G = 0 := by simp [hcard, he]
    exact Nat.card_pos.ne' this
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := G)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff x g).mp (hg x)
    have hpow : g ^ (k * e) = 1 := by
      calc
        g ^ (k * e) = (g ^ k) ^ e := pow_mul g k e
        _ = x ^ e := by rw [hk]
        _ = 1 := by simpa only [powerResidueValue, e] using hx
    have hdiv : n * e ∣ k * e := by
      rw [← hcard]
      rw [← orderOf_eq_card_of_forall_mem_powers hg]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hnk : n ∣ k := by
      exact (Nat.mul_dvd_mul_iff_right (Nat.pos_of_ne_zero he0)).mp hdiv
    obtain ⟨r, rfl⟩ := hnk
    refine ⟨g ^ r, ?_⟩
    calc
      (g ^ r) ^ n = g ^ (r * n) := (pow_mul g r n).symm
      _ = g ^ (n * r) := by rw [Nat.mul_comm]
      _ = x := hk
  · rintro ⟨y, rfl⟩
    change (y ^ n) ^ e = 1
    rw [← pow_mul, ← hcard, pow_card_eq_one']

/-- Finite-field form of Statement VIII.5.1. -/
theorem field_residue_mul
    {F : Type*} [Field F] [Finite F]
    (n : ℕ) (x y : Fˣ) :
    powerResidueValue n (x * y) =
      powerResidueValue n x * powerResidueValue n y :=
  residue_value_mul n x y

/-- Finite-field form of Statement VIII.5.2(a) `(a) ↔ (b)`.  The cardinality
of `Fˣ` is `#F - 1`, so this is precisely the exact sequence displayed in
the source. -/
theorem field_residue_one
    {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : n ∣ Nat.card F - 1) (x : Fˣ) :
    powerResidueValue n x = 1 ↔ ∃ y : Fˣ, y ^ n = x := by
  apply power_residue_value
  simpa only [Nat.card_units] using hn

end

end Towers.CField.HRecip
