import Submission.ClassField.HilbertSymbols.KummerArtin
import Submission.ClassField.CrossedProducts.Cohomology
import Submission.ClassField.LocalBrauer.ConcreteInflationComparison
import Submission.ClassField.LocalBrauer.CyclicCarryCocycle

/-!
# Milne, Remark III.4.7: cyclic algebras and the Hilbert symbol

This file realizes the cyclic algebra attached to an irreducible Kummer
extension as the crossed product of the cyclic carry cocycle.  The choice of
the Kummer generator associated with `ζ⁻¹` gives Milne's convention
`i * j = ζ * (j * i)`.
-/

namespace Submission.CField.HSymbol

open Polynomial
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

universe u

section CarryRelations

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] [FiniteDimensional K L] [IsGalois K L]

/-- The standard basis vector of a Galois carry crossed product. -/
noncomputable def galoisCarryBasis
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (b : Kˣ) (z : ZMod n) :
    CProduc (galoisCarryCocycle K e b) :=
  CProduc.basis (galoisCarryCocycle K e b)
    (e (Multiplicative.ofAdd z))

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem galois_carry_cocycle
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (b : Kˣ) (r s : ZMod n) :
    galoisCarryCocycle K e b
        (e (Multiplicative.ofAdd r), e (Multiplicative.ofAdd s)) =
      (Units.map (algebraMap K L) b) ^
        CCarry.carry r s := by
  simp [galoisCarryCocycle, cyclicBaseInvariant,
    MHTrans.cocycleMap_apply, CCarry.factorSet]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Multiplication of transported carry basis vectors. -/
theorem galois_carry_mul
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (b : Kˣ) (r s : ZMod n) :
    galoisCarryBasis K L e b r * galoisCarryBasis K L e b s =
      CProduc.fieldEmbedding K L (galoisCarryCocycle K e b)
          (((algebraMap K L) b : L) ^ CCarry.carry r s) *
        galoisCarryBasis K L e b (r + s) := by
  have hindex :
      e (Multiplicative.ofAdd r) * e (Multiplicative.ofAdd s) =
        e (Multiplicative.ofAdd (r + s)) := by
    rw [← e.map_mul]
    rfl
  change
    CProduc.basis (galoisCarryCocycle K e b) (e (Multiplicative.ofAdd r)) *
        CProduc.basis (galoisCarryCocycle K e b) (e (Multiplicative.ofAdd s)) =
      CProduc.fieldEmbedding K L (galoisCarryCocycle K e b)
          (((algebraMap K L) b : L) ^ CCarry.carry r s) *
        CProduc.basis (galoisCarryCocycle K e b)
          (e (Multiplicative.ofAdd (r + s)))
  rw [CProduc.basis_mul_basis, galois_carry_cocycle, hindex]
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Before the final carry, powers of the transported generator are the
corresponding transported basis vectors. -/
theorem galois_carry_basis
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (b : Kˣ)
    (k : ℕ) (hk : k < n) :
    (galoisCarryBasis K L e b (1 : ZMod n)) ^ k =
      galoisCarryBasis K L e b (k : ZMod n) := by
  induction k with
  | zero =>
      simp [galoisCarryBasis]
  | succ k ih =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      rw [pow_succ, ih hk', galois_carry_mul]
      have hone_lt : 1 < n := by omega
      letI : Fact (1 < n) := ⟨hone_lt⟩
      have hcarry : CCarry.carry (k : ZMod n) (1 : ZMod n) = 0 := by
        rw [CCarry.carry, if_neg]
        rw [ZMod.val_natCast_of_lt hk', ZMod.val_one]
        omega
      rw [hcarry]
      simp only [pow_zero, map_one, one_mul]
      congr 1
      norm_num

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The transported carry generator has nth power equal to its base-field
parameter. -/
theorem galois_carry_pow
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (b : Kˣ)
    (hn : 1 < n) :
    (galoisCarryBasis K L e b (1 : ZMod n)) ^ n =
      algebraMap K (CProduc (galoisCarryCocycle K e b)) (b : K) := by
  have hnpos : 0 < n := hn.trans' Nat.zero_lt_one
  have hpred : n - 1 < n := Nat.sub_lt hnpos Nat.zero_lt_one
  have hpow :
      (galoisCarryBasis K L e b (1 : ZMod n)) ^ n =
        (galoisCarryBasis K L e b (1 : ZMod n)) ^ (n - 1) *
          galoisCarryBasis K L e b (1 : ZMod n) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow, galois_carry_basis K L e b (n - 1) hpred,
    galois_carry_mul]
  have hcarry : CCarry.carry ((n - 1 : ℕ) : ZMod n) (1 : ZMod n) = 1 := by
    rw [CCarry.carry, if_pos]
    letI : Fact (1 < n) := ⟨hn⟩
    rw [ZMod.val_natCast_of_lt hpred, ZMod.val_one]
    omega
  rw [hcarry]
  have hindex : (((n - 1 : ℕ) : ZMod n) + 1) = 0 := by
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    have hcast := congrArg (fun m : ℕ ↦ (m : ZMod n)) hnat
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hcast
  rw [hindex]
  simp [galoisCarryBasis]

end CarryRelations

end

end Submission.CField.HSymbol
