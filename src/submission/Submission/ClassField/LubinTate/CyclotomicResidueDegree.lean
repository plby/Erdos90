import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Class Field Theory, Chapter I, Example 3.13

The local Artin map used in Example 3.13 has not yet been constructed in the
project.  Mathlib does, however, provide the standard Galois equivalence for a
cyclotomic extension.  The theorem below exposes its action on the chosen
primitive root, which is the algebraic action used in part (b) of the example.
-/

namespace Submission.CField.LTate

open Polynomial

noncomputable section

/-! ## The prime-to-`p` case -/

/-- The residue degree in Example 3.13(a): the multiplicative order of `p`
modulo `n`. -/
def cyclotomicResidueDegree (n p : ℕ) (hpn : p.Coprime n) : ℕ :=
  orderOf (ZMod.unitOfCoprime p hpn)

/-- A positive exponent `k` makes `p^k` congruent to one modulo `n` exactly
when it is divisible by the residue degree. -/
theorem cyclotomic_dvd_mod
    {n p : ℕ} [NeZero n] (hpn : p.Coprime n) (k : ℕ) :
    cyclotomicResidueDegree n p hpn ∣ k ↔
      Nat.ModEq n (p ^ k) 1 := by
  rw [cyclotomicResidueDegree, orderOf_dvd_iff_pow_eq_one,
    Units.ext_iff]
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    Units.val_one]
  rw [← Nat.cast_pow, ← Nat.cast_one,
    ZMod.natCast_eq_natCast_iff]

/-- Thus `p^f` is congruent to one modulo `n` for the residue degree `f`. -/
theorem cyclotomic_residue_mod
    {n p : ℕ} [NeZero n] (hpn : p.Coprime n) :
    Nat.ModEq n (p ^ cyclotomicResidueDegree n p hpn) 1 := by
  exact (cyclotomic_dvd_mod hpn _).mp dvd_rfl

/-- The residue degree is the least positive exponent for which `p^k` is
congruent to one modulo `n`. -/
theorem cyclotomic_degree_minimal
    {n p k : ℕ} [NeZero n] (hpn : p.Coprime n) (hk : 0 < k)
    (hmod : Nat.ModEq n (p ^ k) 1) :
    cyclotomicResidueDegree n p hpn ≤ k := by
  exact Nat.le_of_dvd hk
    ((cyclotomic_dvd_mod hpn k).mpr hmod)

/-- The cyclotomic automorphism corresponding to arithmetic Frobenius in the
prime-to-`p` case. -/
noncomputable def cyclotomicFrobenius
    {n p : ℕ} [NeZero n] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (hpn : p.Coprime n) : Gal(L/K) :=
  (IsCyclotomicExtension.autEquivPow L h).symm
    (ZMod.unitOfCoprime p hpn)

/-- Under the standard cyclotomic Galois equivalence, the automorphism
corresponding to `t : (ZMod n)ˣ` sends the chosen primitive root to its
`t`th power.  Taking `t = u⁻¹` gives the exponent in Example 3.13(b). -/
theorem cyclotomic_aut_zeta
    {n : ℕ} [NeZero n] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (t : (ZMod n)ˣ) :
    (IsCyclotomicExtension.autEquivPow L h).symm t
        (IsCyclotomicExtension.zeta n K L) =
      IsCyclotomicExtension.zeta n K L ^ t.val.val := by
  have hspec := (IsCyclotomicExtension.zeta_spec n K L).autToPow_spec K
    ((IsCyclotomicExtension.autEquivPow L h).symm t)
  have ht := (IsCyclotomicExtension.autEquivPow L h).apply_symm_apply t
  rw [IsCyclotomicExtension.autEquivPow_apply] at ht
  rw [← hspec]
  congr 1
  exact congrArg (fun x : (ZMod n)ˣ ↦ x.val.val) ht

/-- Arithmetic Frobenius raises the chosen primitive root to its `p`th
power, as in Example 3.13(a). -/
theorem cyclotomic_frobenius_zeta
    {n p : ℕ} [NeZero n] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (hpn : p.Coprime n) :
    cyclotomicFrobenius h hpn (L := L)
        (IsCyclotomicExtension.zeta n K L) =
      IsCyclotomicExtension.zeta n K L ^ p := by
  rw [cyclotomicFrobenius,
    cyclotomic_aut_zeta]
  simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  let hζ := IsCyclotomicExtension.zeta_spec n K L
  have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta n K L) :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, NeZero.pos n, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq]
  rw [← hζ.eq_orderOf]
  exact Nat.mod_modEq p n

/-- The powers of cyclotomic Frobenius have precisely the kernel described
in Example 3.13(a): an exponent acts trivially exactly when it is a multiple
of the residue degree. -/
theorem cyclotomic_frobenius_zpow
    {n p : ℕ} [NeZero n] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (hpn : p.Coprime n) (m : ℤ) :
    cyclotomicFrobenius h hpn (L := L) ^ m = 1 ↔
      (cyclotomicResidueDegree n p hpn : ℤ) ∣ m := by
  have hord :
      orderOf (cyclotomicFrobenius h hpn (L := L)) =
        cyclotomicResidueDegree n p hpn :=
    (IsCyclotomicExtension.autEquivPow L h).symm.orderOf_eq
      (ZMod.unitOfCoprime p hpn)
  rw [← orderOf_dvd_iff_zpow_eq_one, hord]

/-! ## The `p`-power case -/

/-- Reduction of a `p`-adic unit modulo `p^r`. -/
noncomputable def padicUnitReduction (p r : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ →* (ZMod (p ^ r))ˣ :=
  Units.map (PadicInt.toZModPow r).toMonoidHom

/-- A `p`-adic unit reduces to one modulo `p^r` exactly when it is congruent
to one modulo the ideal generated by `p^r`. -/
theorem padic_unit_reduction
    (p r : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    padicUnitReduction p r u = 1 ↔
      (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
  rw [← PadicInt.ker_toZModPow r, RingHom.mem_ker]
  change Units.map (PadicInt.toZModPow r).toMonoidHom u = 1 ↔
    PadicInt.toZModPow r ((u : ℤ_[p]) - 1) = 0
  rw [Units.ext_iff]
  constructor
  · intro hu
    change PadicInt.toZModPow r (u : ℤ_[p]) = 1 at hu
    rw [map_sub, map_one, hu, sub_self]
  · intro hu
    rw [map_sub, map_one] at hu
    change PadicInt.toZModPow r (u : ℤ_[p]) = 1
    exact sub_eq_zero.mp hu

/-- Milne's unit action in Example 3.13(b), including the inverse in the
local Artin-map convention. -/
noncomputable def padicCyclotomicAction
    (p r : ℕ) [Fact p.Prime] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p ^ r} K L]
    (h : Irreducible (cyclotomic (p ^ r) K)) : ℤ_[p]ˣ →* Gal(L/K) :=
  (IsCyclotomicExtension.autEquivPow L h).symm.toMonoidHom.comp
    ((padicUnitReduction p r).comp invMonoidHom)

/-- The unit action sends the chosen primitive root to the power indexed by
the inverse of the residue class of the unit. -/
theorem padic_action_zeta
    (p r : ℕ) [Fact p.Prime] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p ^ r} K L]
    (h : Irreducible (cyclotomic (p ^ r) K)) (u : ℤ_[p]ˣ) :
    padicCyclotomicAction p r h (L := L) u
        (IsCyclotomicExtension.zeta (p ^ r) K L) =
      IsCyclotomicExtension.zeta (p ^ r) K L ^
        ((padicUnitReduction p r u⁻¹ : ZMod (p ^ r)).val) := by
  exact cyclotomic_aut_zeta h
    (padicUnitReduction p r u⁻¹)

/-- The kernel of the `p`-adic unit action is exactly the congruence subgroup
`u ≡ 1 (mod p^r)` from Example 3.13(b). -/
theorem padic_cyclotomic_action
    (p r : ℕ) [Fact p.Prime] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p ^ r} K L]
    (h : Irreducible (cyclotomic (p ^ r) K)) (u : ℤ_[p]ˣ) :
    padicCyclotomicAction p r h (L := L) u = 1 ↔
      (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
  rw [padicCyclotomicAction]
  change (IsCyclotomicExtension.autEquivPow L h).symm
      (padicUnitReduction p r u⁻¹) = 1 ↔ _
  rw [(IsCyclotomicExtension.autEquivPow L h).symm.map_eq_one_iff]
  rw [map_inv, inv_eq_one]
  exact padic_unit_reduction p r u

/-- Under irreducibility, the degree of a `p^r`-cyclotomic extension is the
degree `(p - 1) p^(r-1)` appearing in Example 3.13(b). -/
theorem finrank_prime_cyclotomic
    (p r : ℕ) [Fact p.Prime] (hr : 0 < r) {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p ^ r} K L]
    (h : Irreducible (cyclotomic (p ^ r) K)) :
    Module.finrank K L = (p - 1) * p ^ (r - 1) := by
  rw [IsCyclotomicExtension.finrank L h,
    Nat.totient_prime_pow Fact.out hr]
  exact Nat.mul_comm _ _

end

end Submission.CField.LTate
