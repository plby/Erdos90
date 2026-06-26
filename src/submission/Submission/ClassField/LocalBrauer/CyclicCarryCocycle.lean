import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Submission.ClassField.CrossedProducts.CrossedProduct

/-!
# Chapter IV, Example 4.2: the cyclic carry cocycle

For a cyclic group of order `n`, Milne's cocycle is `1` until addition of
the chosen representatives crosses `n`, and is a fixed element `pi` after
that crossing. This file isolates that algebraic construction from the local
field valuation used later to compute its invariant.
-/

namespace Submission.CField.LBrauer

noncomputable section

open CProduca

attribute [local instance] Units.mulDistribMulActionRight

namespace CCarry

variable {n : ℕ} [NeZero n]

/-- Whether addition of the standard representatives in `ZMod n` carries. -/
def carry (a b : ZMod n) : ℕ :=
  if n ≤ a.val + b.val then 1 else 0

theorem val_add_carry (a b : ZMod n) :
    (a + b).val + n * carry a b = a.val + b.val := by
  by_cases h : n ≤ a.val + b.val
  · simp only [carry, if_pos h, mul_one]
    exact (ZMod.val_add_val_of_le h).symm
  · have hlt : a.val + b.val < n := Nat.lt_of_not_ge h
    simp only [carry, if_neg h, mul_zero, add_zero]
    exact ZMod.val_add_of_lt hlt

/-- The carries in a three-term modular sum satisfy the cocycle identity. -/
theorem carry_cocycle (a b c : ZMod n) :
    carry (a + b) c + carry a b =
      carry b c + carry a (b + c) := by
  have hab := val_add_carry a b
  have habc := val_add_carry (a + b) c
  have hbc := val_add_carry b c
  have habc' := val_add_carry a (b + c)
  have hassoc : (a + b + c).val = (a + (b + c)).val := by
    rw [add_assoc]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul :
      n * (carry (a + b) c + carry a b) =
        n * (carry b c + carry a (b + c)) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.eq_of_mul_eq_mul_left hn hmul

variable {M : Type*} [CommGroup M]
  [MulDistribMulAction (Multiplicative (ZMod n)) M]

/-- Milne's cyclic factor set: its value is `pi` exactly when the chosen
representatives of the two group elements cross the modulus. -/
def factorSet (pi : M) (hpi : ∀ g : Multiplicative (ZMod n), g • pi = pi) :
    NMCocycl₂ (G := Multiplicative (ZMod n)) (M := M) where
  toFun p := pi ^ carry p.1.toAdd p.2.toAdd
  isMulCocycle₂ := by
    intro g h j
    rw [show g • pi ^ carry h.toAdd j.toAdd = pi ^ carry h.toAdd j.toAdd by
      change (MulDistribMulAction.toMonoidHom M g)
          (pi ^ carry h.toAdd j.toAdd) = _
      rw [map_pow]
      congr 1
      exact hpi g]
    rw [← pow_add, ← pow_add]
    apply congrArg (pi ^ ·)
    change carry (g.toAdd + h.toAdd) j.toAdd + carry g.toAdd h.toAdd =
      carry h.toAdd j.toAdd + carry g.toAdd (h.toAdd + j.toAdd)
    exact carry_cocycle g.toAdd h.toAdd j.toAdd
  map_one_fst := by
    intro g
    simp [carry, ZMod.val_lt]
  map_one_snd := by
    intro g
    simp [carry, ZMod.val_lt]

@[simp]
theorem apply_of_lt (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod n), g • pi = pi)
    (a b : ZMod n) (h : a.val + b.val < n) :
    factorSet pi hpi (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = 1 := by
  simp [factorSet, carry, Nat.not_le.mpr h]

@[simp]
theorem factor_set (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod n), g • pi = pi)
    (a b : ZMod n) (h : n ≤ a.val + b.val) :
    factorSet pi hpi (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = pi := by
  simp [factorSet, carry, h]

section CProduc

variable {L : Type*} [CommRing L]
  [MulSemiringAction (Multiplicative (ZMod n)) L]
  (pi : Lˣ)
  (hpi : ∀ g : Multiplicative (ZMod n), g • pi = pi)

abbrev A := CProduc (factorSet pi hpi)

/-- Milne's basis element `e_i`. -/
def e (i : ZMod n) : A pi hpi :=
  CProduc.basis (factorSet pi hpi) (Multiplicative.ofAdd i)

/-- Multiplication before the carry is `e_i e_j = e_(i+j)`. -/
theorem e_of_lt (i j : ZMod n) (h : i.val + j.val < n) :
    e pi hpi i * e pi hpi j = e pi hpi (i + j) := by
  simp only [e, CProduc.basis_apply, CProduc.single_mul_single]
  simp [apply_of_lt pi hpi i j h]

/-- Multiplication after the carry is `e_i e_j = pi e_(i+j)`. -/
theorem e_mul (i j : ZMod n) (h : n ≤ i.val + j.val) :
    e pi hpi i * e pi hpi j =
      CProduc.single (factorSet pi hpi)
        (Multiplicative.ofAdd (i + j)) (pi : L) := by
  simp only [e, CProduc.basis_apply, CProduc.single_mul_single]
  simp [factor_set pi hpi i j h]

/-- A basis element twists coefficients by the corresponding cyclic action. -/
theorem e_mul_coefficient (i : ZMod n) (a : L) :
    e pi hpi i * CProduc.coefficientRingHom (factorSet pi hpi) a =
      CProduc.single (factorSet pi hpi) (Multiplicative.ofAdd i)
        ((Multiplicative.ofAdd i) • a) := by
  simp [e, CProduc.basis_apply]

/-- The coefficient-twisting rule in Milne's displayed presentation. -/
theorem e_coefficient (i : ZMod n) (a : L) :
    e pi hpi i * CProduc.coefficientRingHom (factorSet pi hpi) a =
      CProduc.coefficientRingHom (factorSet pi hpi)
          ((Multiplicative.ofAdd i) • a) * e pi hpi i := by
  rw [e_mul_coefficient]
  simp [e, CProduc.basis_apply]

/-- Before the final wrap, powers of `e_1` are the corresponding basis
elements. -/
theorem e_pow (k : ℕ) (hk : k < n) :
    (e pi hpi (1 : ZMod n)) ^ k = e pi hpi (k : ZMod n) := by
  induction k with
  | zero => simp [e, CProduc.basis_apply]
  | succ k ih =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      rw [pow_succ, ih hk']
      rw [e_of_lt pi hpi]
      · simp
      · have hone_lt : 1 < n := by omega
        letI : Fact (1 < n) := ⟨hone_lt⟩
        rw [ZMod.val_natCast_of_lt hk', ZMod.val_one]
        simpa using hk

/-- Milne's relation `e_1 ^ n = pi`, for the nontrivial cyclic case. -/
theorem e_one_pow (hn : 1 < n) :
    (e pi hpi (1 : ZMod n)) ^ n =
      CProduc.coefficientRingHom (factorSet pi hpi) (pi : L) := by
  have hnpos : 0 < n := hn.trans' Nat.zero_lt_one
  have hpred : n - 1 < n := Nat.sub_lt hnpos Nat.zero_lt_one
  have hpow :
      (e pi hpi (1 : ZMod n)) ^ n =
        (e pi hpi (1 : ZMod n)) ^ (n - 1) * e pi hpi (1 : ZMod n) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow, e_pow pi hpi (n - 1) hpred]
  rw [e_mul pi hpi]
  · have hindex :
        Multiplicative.ofAdd (((n - 1 : ℕ) : ZMod n) + 1) = 1 := by
      have hz : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
        have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        have hcast := congrArg (fun m : ℕ ↦ (m : ZMod n)) hnat
        simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hcast
      simpa using congrArg Multiplicative.ofAdd hz
    rw [hindex]
    rfl
  · rw [ZMod.val_natCast_of_lt hpred]
    letI : Fact (1 < n) := ⟨hn⟩
    rw [ZMod.val_one]
    omega

/-- The basis element `e₁` is invertible. -/
theorem unit_e_one (hn : 1 < n) : IsUnit (e pi hpi (1 : ZMod n)) := by
  rw [← isUnit_pow_iff (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))]
  rw [e_one_pow pi hpi hn]
  exact pi.isUnit.map (CProduc.coefficientRingHom (factorSet pi hpi))

/-- The unit of the crossed product represented by Milne's basis element
`e₁`. -/
noncomputable def eOneUnit (hn : 1 < n) : (A pi hpi)ˣ :=
  (unit_e_one pi hpi hn).unit

theorem e_unit_coe (hn : 1 < n) :
    (eOneUnit pi hpi hn : A pi hpi) = e pi hpi (1 : ZMod n) :=
  (unit_e_one pi hpi hn).unit_spec

/-- Milne's conjugation identity `e₁ a e₁⁻¹ = σ(a)`. -/
theorem e_conjugate_coefficient (hn : 1 < n) (a : L) :
    (eOneUnit pi hpi hn : A pi hpi) *
        CProduc.coefficientRingHom (factorSet pi hpi) a *
        (↑(eOneUnit pi hpi hn)⁻¹ : A pi hpi) =
      CProduc.coefficientRingHom (factorSet pi hpi)
        (Multiplicative.ofAdd (1 : ZMod n) • a) := by
  rw [e_unit_coe pi hpi hn,
    e_coefficient pi hpi]
  rw [mul_assoc, ← e_unit_coe pi hpi hn]
  simp

/-- The order calculation in Milne's Example 4.2.  Any rational additive
order on the crossed-product unit group which assigns order one to the
coefficient `pi` assigns order `1 / n` to `e₁`. -/
theorem e_unit_order
    (hn : 1 < n) (ord : Additive (A pi hpi)ˣ →+ ℚ)
    (hordPi :
      ord (Additive.ofMul
        (Units.map (CProduc.coefficientRingHom (factorSet pi hpi)) pi)) = 1) :
    ord (Additive.ofMul (eOneUnit pi hpi hn)) = 1 / (n : ℚ) := by
  have hunitPow :
      (eOneUnit pi hpi hn) ^ n =
        Units.map (CProduc.coefficientRingHom (factorSet pi hpi)) pi := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, e_unit_coe, e_one_pow pi hpi hn]
    rfl
  have hordPow := congrArg ord (congrArg Additive.ofMul hunitPow)
  have hpowAdd :
      Additive.ofMul ((eOneUnit pi hpi hn) ^ n) =
        n • Additive.ofMul (eOneUnit pi hpi hn) := rfl
  rw [hpowAdd, map_nsmul, hordPi] at hordPow
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))
  apply (eq_div_iff hnQ).2
  simpa [nsmul_eq_mul, mul_comm] using hordPow

end CProduc

end CCarry

end

end Submission.CField.LBrauer
