import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adic completion at a power of an ideal

The filtrations by powers of `I` and by powers of a positive power `I ^ e`
are cofinal.  This file implements the resulting ring equivalence directly
on the inverse-limit description of adic completion.
-/

namespace Submission.NumberTheory.Milne

open Function

noncomputable section

universe u

variable {R : Type u} [CommRing R]

private theorem nat_le_mul (e : ℕ) (he : 0 < e) (n : ℕ) : n ≤ e * n := by
  simpa using Nat.mul_le_mul_right n ((Nat.succ_le_iff).2 he)

private theorem transitionMap_one (I : Ideal R) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I R hmn
        (1 : R ⧸ (I ^ n • (⊤ : Submodule R R))) = 1 := by
  change Submodule.factor _ (Submodule.mkQ _ 1) = Submodule.mkQ _ 1
  rw [Submodule.factor_mk]

private theorem transitionMap_mul (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x y : R ⧸ (I ^ n • (⊤ : Submodule R R))) :
    AdicCompletion.transitionMap I R hmn (x * y) =
      AdicCompletion.transitionMap I R hmn x *
        AdicCompletion.transitionMap I R hmn y := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
      induction y using Submodule.Quotient.induction_on with
      | _ b =>
          change Submodule.factor _ (Submodule.mkQ _ (a * b)) =
            Submodule.factor _ (Submodule.mkQ _ a) *
              Submodule.factor _ (Submodule.mkQ _ b)
          rw [Submodule.factor_mk, Submodule.factor_mk, Submodule.factor_mk]
          rfl

private def powerQuotientEquiv (I : Ideal R) (e n : ℕ) :
    (R ⧸ ((I ^ e) ^ n • (⊤ : Submodule R R))) ≃+*
      (R ⧸ (I ^ (e * n) • (⊤ : Submodule R R))) :=
  Ideal.quotEquivOfEq (by rw [pow_mul])

@[simp]
private theorem power_quotient_mk (I : Ideal R) (e n : ℕ) (x : R) :
    powerQuotientEquiv I e n
        (Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) x) =
      Submodule.mkQ (I ^ (e * n) • (⊤ : Submodule R R)) x :=
  rfl

@[simp]
private theorem power_symm_mk (I : Ideal R) (e n : ℕ) (x : R) :
    (powerQuotientEquiv I e n).symm
        (Submodule.mkQ (I ^ (e * n) • (⊤ : Submodule R R)) x) =
      Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) x :=
  rfl

private theorem power_symm_transition (I : Ideal R) (e : ℕ)
    {m n : ℕ} (hmn : m ≤ n)
    (q : R ⧸ (I ^ (e * n) • (⊤ : Submodule R R))) :
    AdicCompletion.transitionMap (I ^ e) R hmn
        ((powerQuotientEquiv I e n).symm q) =
      (powerQuotientEquiv I e m).symm
        (AdicCompletion.transitionMap I R (Nat.mul_le_mul_left e hmn) q) := by
  apply (powerQuotientEquiv I e m).injective
  rw [RingEquiv.apply_symm_apply]
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
      change powerQuotientEquiv I e m
          (AdicCompletion.transitionMap (I ^ e) R hmn
            ((powerQuotientEquiv I e n).symm
              (Submodule.mkQ (I ^ (e * n) • (⊤ : Submodule R R)) a))) =
        AdicCompletion.transitionMap I R (Nat.mul_le_mul_left e hmn)
          (Submodule.mkQ (I ^ (e * n) • (⊤ : Submodule R R)) a)
      rw [power_symm_mk]
      change powerQuotientEquiv I e m
          (Submodule.factor _
            (Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) a)) =
        Submodule.factor _
          (Submodule.mkQ (I ^ (e * n) • (⊤ : Submodule R R)) a)
      rw [Submodule.factor_mk, power_quotient_mk,
        Submodule.factor_mk]

private theorem power_quotient_transition (I : Ideal R) (e : ℕ)
    (he : 0 < e) {m n : ℕ} (hmn : m ≤ n)
    (q : R ⧸ ((I ^ e) ^ n • (⊤ : Submodule R R))) :
    AdicCompletion.transitionMap I R hmn
        (AdicCompletion.transitionMap I R (nat_le_mul e he n)
          (powerQuotientEquiv I e n q)) =
      AdicCompletion.transitionMap I R (nat_le_mul e he m)
        (powerQuotientEquiv I e m
          (AdicCompletion.transitionMap (I ^ e) R hmn q)) := by
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
      change AdicCompletion.transitionMap I R hmn
          (AdicCompletion.transitionMap I R (nat_le_mul e he n)
            (powerQuotientEquiv I e n
              (Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) a))) =
        AdicCompletion.transitionMap I R (nat_le_mul e he m)
          (powerQuotientEquiv I e m
            (AdicCompletion.transitionMap (I ^ e) R hmn
              (Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) a)))
      rw [power_quotient_mk]
      change Submodule.factor _ (Submodule.factor _ (Submodule.mkQ _ a)) = _
      rw [Submodule.factor_mk, Submodule.factor_mk]
      change _ = AdicCompletion.transitionMap I R _
        (powerQuotientEquiv I e m
          (Submodule.factor _
            (Submodule.mkQ ((I ^ e) ^ n • (⊤ : Submodule R R)) a)))
      rw [Submodule.factor_mk, power_quotient_mk]
      change Submodule.mkQ _ a = Submodule.factor _ (Submodule.mkQ _ a)
      rw [Submodule.factor_mk]

private def toPower (I : Ideal R) (e : ℕ) (x : AdicCompletion I R) :
    AdicCompletion (I ^ e) R :=
  ⟨fun n => (powerQuotientEquiv I e n).symm (x.val (e * n)),
    fun {m n} hmn => by
      rw [power_symm_transition]
      rw [x.property (Nat.mul_le_mul_left e hmn)]⟩

private def fromPower (I : Ideal R) (e : ℕ) (he : 0 < e)
    (x : AdicCompletion (I ^ e) R) : AdicCompletion I R :=
  ⟨fun n => AdicCompletion.transitionMap I R (nat_le_mul e he n)
      (powerQuotientEquiv I e n (x.val n)),
    fun {m n} hmn => by
      rw [power_quotient_transition I e he hmn]
      rw [x.property hmn]⟩

private def powerRingHom (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R →+* AdicCompletion I R where
  toFun := fromPower I e he
  map_zero' := by
    apply AdicCompletion.ext
    intro n
    change AdicCompletion.transitionMap I R _
      (powerQuotientEquiv I e n 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    change AdicCompletion.transitionMap I R _
        (powerQuotientEquiv I e n (x.val n + y.val n)) =
      AdicCompletion.transitionMap I R _
          (powerQuotientEquiv I e n (x.val n)) +
        AdicCompletion.transitionMap I R _
          (powerQuotientEquiv I e n (y.val n))
    rw [map_add, map_add]
  map_one' := by
    apply AdicCompletion.ext
    intro n
    change AdicCompletion.transitionMap I R _
      (powerQuotientEquiv I e n 1) = 1
    rw [map_one, transitionMap_one]
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    change AdicCompletion.transitionMap I R _
        (powerQuotientEquiv I e n (x.val n * y.val n)) =
      AdicCompletion.transitionMap I R _
          (powerQuotientEquiv I e n (x.val n)) *
        AdicCompletion.transitionMap I R _
          (powerQuotientEquiv I e n (y.val n))
    rw [map_mul, transitionMap_mul]

private theorem power_coord (I : Ideal R) (e : ℕ) (he : 0 < e)
    (n : ℕ)
    (q : R ⧸ ((I ^ e) ^ (e * n) • (⊤ : Submodule R R))) :
    (powerQuotientEquiv I e n).symm
        (AdicCompletion.transitionMap I R (nat_le_mul e he (e * n))
          (powerQuotientEquiv I e (e * n) q)) =
      AdicCompletion.transitionMap (I ^ e) R (nat_le_mul e he n) q := by
  apply (powerQuotientEquiv I e n).injective
  rw [RingEquiv.apply_symm_apply]
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
      change Submodule.factor _
          (powerQuotientEquiv I e (e * n)
            (Submodule.mkQ ((I ^ e) ^ (e * n) • (⊤ : Submodule R R)) a)) =
        powerQuotientEquiv I e n
          (Submodule.factor _
            (Submodule.mkQ ((I ^ e) ^ (e * n) • (⊤ : Submodule R R)) a))
      rw [power_quotient_mk, Submodule.factor_mk,
        Submodule.factor_mk, power_quotient_mk]

/-- Replacing an ideal by a positive power does not change its adic
completion. -/
def adicPowRing (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃+* AdicCompletion I R where
  __ := powerRingHom I e he
  invFun := toPower I e
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    change (powerQuotientEquiv I e n).symm
        (AdicCompletion.transitionMap I R _
          (powerQuotientEquiv I e (e * n) (x.val (e * n)))) = x.val n
    rw [power_coord I e he]
    rw [x.property (nat_le_mul e he n)]
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    change AdicCompletion.transitionMap I R _
        (powerQuotientEquiv I e n
          ((powerQuotientEquiv I e n).symm (x.val (e * n)))) = x.val n
    rw [RingEquiv.apply_symm_apply]
    rw [x.property (nat_le_mul e he n)]

@[simp]
theorem adic_completion_ring
    (I : Ideal R) (e : ℕ) (he : 0 < e) (x : R) :
    adicPowRing I e he
        (AdicCompletion.of (I ^ e) R x) =
      AdicCompletion.of I R x := by
  apply AdicCompletion.ext
  intro n
  change AdicCompletion.transitionMap I R _
      (powerQuotientEquiv I e n
        ((AdicCompletion.of (I ^ e) R x).val n)) =
    (AdicCompletion.of I R x).val n
  rw [AdicCompletion.of_apply, AdicCompletion.of_apply]
  rw [power_quotient_mk]
  change Submodule.factor _ (Submodule.mkQ _ x) = Submodule.mkQ _ x
  rw [Submodule.factor_mk]

end

end Submission.NumberTheory.Milne
