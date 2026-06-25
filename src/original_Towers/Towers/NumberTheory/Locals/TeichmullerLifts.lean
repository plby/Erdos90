import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Teichmuller lifts in a Henselian local ring

This records the existence part of Milne's Remark 7.36: every residue class
has a lift that is a root of `X ^ q - X`, where `q` is the cardinality of the
finite residue field.
-/

namespace Towers.NumberTheory.Milne

open Polynomial IsLocalRing

noncomputable section

variable (A : Type*) [CommRing A] [HenselianLocalRing A]
variable [Fintype (ResidueField A)]

/-- Every element of the finite residue field of a Henselian local ring has a
Teichmuller lift. -/
theorem exists_teichmullerLift (a0 : ResidueField A) :
    ∃ a : A,
      (X ^ Fintype.card (ResidueField A) - X : A[X]).IsRoot a ∧
        residue A a = a0 := by
  let q := Fintype.card (ResidueField A)
  let f : A[X] := X ^ q - X
  have hq : 1 < q := Fintype.one_lt_card
  have hf : f.Monic := by
    apply monic_X_pow_sub
    simpa [q] using hq
  have hlift :=
    ((HenselianLocalRing.TFAE A).out 0 1).mp
      (inferInstance : HenselianLocalRing A)
  apply hlift f hf a0
  · simp [f, q, aeval_def, FiniteField.pow_card]
  · simp [f, q, aeval_def, derivative_sub, derivative_X_pow,
      Nat.cast_card_eq_zero]

/-- Two roots of `X ^ q - X` with the same residue are equal.  This is the
uniqueness assertion for Teichmuller lifts. -/
theorem teichmullerLift_unique {a b : A}
    (ha : (X ^ Fintype.card (ResidueField A) - X : A[X]).IsRoot a)
    (hb : (X ^ Fintype.card (ResidueField A) - X : A[X]).IsRoot b)
    (hab : residue A a = residue A b) :
    a = b := by
  let q := Fintype.card (ResidueField A)
  let s : A := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i)
  have ha0 : a ^ q - a = 0 := by
    simpa [q, Polynomial.IsRoot.def] using ha
  have hb0 : b ^ q - b = 0 := by
    simpa [q, Polynomial.IsRoot.def] using hb
  have hpow : a ^ q - b ^ q = a - b := by
    rw [sub_eq_zero.mp ha0, sub_eq_zero.mp hb0]
  have hmul : (a - b) * s = a ^ q - b ^ q := by
    exact (Commute.all a b).mul_geom_sum₂ q
  have hsres : residue A s = 0 := by
    rw [map_sum]
    calc
      ∑ i ∈ Finset.range q,
          residue A (a ^ i * b ^ (q - 1 - i)) =
          ∑ _i ∈ Finset.range q,
            (residue A a) ^ (q - 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [map_mul, map_pow, hab]
              rw [← pow_add]
              congr 1
              have hiq : i < q := Finset.mem_range.mp hi
              omega
      _ = q • (residue A a) ^ (q - 1) := by simp
      _ = 0 := by
        rw [nsmul_eq_mul, Nat.cast_card_eq_zero]
        simp
  have hsunit : IsUnit (s - 1) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp [map_sub, hsres]
  have hzero : (a - b) * (s - 1) = 0 := by
    rw [mul_sub, mul_one, hmul, hpow, sub_self]
  have hab0 : a - b = 0 := by
    apply hsunit.mul_left_cancel
    simpa [mul_comm] using hzero
  exact sub_eq_zero.mp hab0

/-- The chosen Teichmuller representative of a residue class. -/
noncomputable def teichmullerLift (a0 : ResidueField A) : A :=
  Classical.choose (exists_teichmullerLift A a0)

@[simp]
theorem teichmuller_lift_root (a0 : ResidueField A) :
    (X ^ Fintype.card (ResidueField A) - X : A[X]).IsRoot
      (teichmullerLift A a0) :=
  (Classical.choose_spec (exists_teichmullerLift A a0)).1

@[simp]
theorem residue_teichmullerLift (a0 : ResidueField A) :
    residue A (teichmullerLift A a0) = a0 :=
  (Classical.choose_spec (exists_teichmullerLift A a0)).2

section EqualCharacteristic

variable (p : ℕ) [Fact p.Prime] [CharP A p]

private theorem residue_char_pow :
    ∃ n : ℕ, Fintype.card (ResidueField A) = p ^ n := by
  letI : CharP (ResidueField A) p :=
    (CharP.charP_iff_prime_eq_zero (R := ResidueField A) Fact.out).2 <| by
      calc
        (p : ResidueField A) = residue A (p : A) := (map_natCast (residue A) p).symm
        _ = residue A 0 := congrArg (residue A) (CharP.cast_eq_zero A p)
        _ = 0 := map_zero (residue A)
  letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ _
  refine ⟨Module.finrank (ZMod p) (ResidueField A), ?_⟩
  rw [← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

private theorem teichmuller_lift_card (a0 : ResidueField A) :
    teichmullerLift A a0 ^ Fintype.card (ResidueField A) =
      teichmullerLift A a0 := by
  exact sub_eq_zero.mp (by
    simpa [Polynomial.IsRoot.def] using teichmuller_lift_root A a0)

include p

/-- In equal characteristic, the Teichmuller representatives form a
coefficient field: the residue map has a canonical ring-homomorphic section.
This supplies the missing coefficient-field construction in Remark 7.49(c). -/
noncomputable def teichmullerLiftHom : ResidueField A →+* A where
  toFun := teichmullerLift A
  map_zero' := by
    apply teichmullerLift_unique A (teichmuller_lift_root A 0)
    · simp [Polynomial.IsRoot.def, Fintype.card_ne_zero]
    · simp
  map_one' := by
    apply teichmullerLift_unique A (teichmuller_lift_root A 1)
    · simp [Polynomial.IsRoot.def]
    · simp
  map_add' x y := by
    obtain ⟨n, hcard⟩ := residue_char_pow A p
    apply teichmullerLift_unique A (teichmuller_lift_root A (x + y))
    · rw [Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero,
        hcard, add_pow_char_pow, ← hcard,
        teichmuller_lift_card A x, teichmuller_lift_card A y]
    · simp
  map_mul' x y := by
    apply teichmullerLift_unique A (teichmuller_lift_root A (x * y))
    · rw [Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero,
        mul_pow, teichmuller_lift_card A x,
        teichmuller_lift_card A y]
    · simp

@[simp]
theorem residue_comp_teichmuller :
    (residue A).comp (teichmullerLiftHom A p) = RingHom.id _ := by
  ext x
  exact residue_teichmullerLift A x

theorem teichmuller_lift_injective :
    Function.Injective (teichmullerLiftHom A p) :=
  RingHom.injective _

end EqualCharacteristic

end

end Towers.NumberTheory.Milne
