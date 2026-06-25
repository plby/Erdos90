import Submission.Group.NilpotentProducts.RankThreeModel
import Submission.Group.Edmonton.HallCommutatorIdentities
import Mathlib.Tactic.DeriveFintype


/-!
# The fourteen explicit basis axes for equation (18)
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton

/-- The fourteen coordinates in Struik's ordered basis for Theorem 1. -/
inductive BasisIndex
  | c1 | c2 | c3
  | c12 | c13 | c23
  | c121 | c131 | c232
  | c122 | c133 | c233
  | c123 | c231
  deriving DecidableEq, Fintype

/-- The integral coordinate axis at a prescribed basis position. -/
def axis :
    BasisIndex → ℤ → RLCoordi
  | .c1, n => { RLCoordi.zero with c1 := n }
  | .c2, n => { RLCoordi.zero with c2 := n }
  | .c3, n => { RLCoordi.zero with c3 := n }
  | .c12, n => { RLCoordi.zero with c12 := n }
  | .c13, n => { RLCoordi.zero with c13 := n }
  | .c23, n => { RLCoordi.zero with c23 := n }
  | .c121, n => { RLCoordi.zero with c121 := n }
  | .c131, n => { RLCoordi.zero with c131 := n }
  | .c232, n => { RLCoordi.zero with c232 := n }
  | .c122, n => { RLCoordi.zero with c122 := n }
  | .c133, n => { RLCoordi.zero with c133 := n }
  | .c233, n => { RLCoordi.zero with c233 := n }
  | .c123, n => { RLCoordi.zero with c123 := n }
  | .c231, n => { RLCoordi.zero with c231 := n }

@[simp]
private lemma choose_one_two :
    Ring.choose (1 : ℤ) 2 = 0 := by
  decide

@[simp]
private lemma choose_neg_two :
    Ring.choose (-1 : ℤ) 2 = 1 := by
  decide

@[simp]
theorem axis_zero (i : BasisIndex) :
    axis i 0 = RLCoordi.zero := by
  cases i <;> rfl

theorem axis_add (i : BasisIndex) (m n : ℤ) :
    RLCoordi.mul (axis i m) (axis i n) =
      axis i (m + n) := by
  cases i <;>
    ext <;>
    simp [axis, RLCoordi.mul,
      RLCoordi.zero]

theorem axis_neg (i : BasisIndex) (n : ℤ) :
    RLCoordi.rightInv (axis i n) =
      axis i (-n) := by
  cases i <;>
    ext <;>
    simp [axis, RLCoordi.rightInv,
      RLCoordi.zero]

private theorem axis_one_pow
    (i : BasisIndex) (n : ℕ) :
    axis i 1 ^ n = axis i n := by
  induction n with
  | zero =>
      change RLCoordi.zero = axis i 0
      exact (axis_zero i).symm
  | succ n ih =>
      rw [pow_succ, ih]
      change
        RLCoordi.mul (axis i n)
          (axis i 1) =
          axis i (n + 1)
      simpa using axis_add i n 1

/-- Integer powers of a unit axis give the corresponding integral
coordinate. -/
theorem axis_one_zpow
    (i : BasisIndex) (n : ℤ) :
    axis i 1 ^ n = axis i n := by
  cases n with
  | ofNat n =>
      simpa only [zpow_natCast, Int.ofNat_eq_natCast] using
        axis_one_pow i n
  | negSucc n =>
      rw [zpow_negSucc, axis_one_pow]
      change
        RLCoordi.rightInv (axis i (n + 1)) =
          axis i (Int.negSucc n)
      rw [axis_neg]
      congr

/-- The ordered product of the fourteen coordinate axes. -/
noncomputable def axisProduct
    (c : RLCoordi) : RLCoordi :=
  axis .c1 c.c1 *
  axis .c2 c.c2 *
  axis .c3 c.c3 *
  axis .c12 c.c12 *
  axis .c13 c.c13 *
  axis .c23 c.c23 *
  axis .c121 c.c121 *
  axis .c131 c.c131 *
  axis .c232 c.c232 *
  axis .c122 c.c122 *
  axis .c133 c.c133 *
  axis .c233 c.c233 *
  axis .c123 c.c123 *
  axis .c231 c.c231

/-- Every integral tuple is its ordered axis product. -/
theorem axisProduct_eq
    (c : RLCoordi) :
    axisProduct c = c := by
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul
            (RLCoordi.mul
              (RLCoordi.mul
                (RLCoordi.mul
                  (RLCoordi.mul
                    (RLCoordi.mul
                      (RLCoordi.mul
                        (RLCoordi.mul
                          (RLCoordi.mul
                            (RLCoordi.mul
                              (axis .c1 c.c1)
                              (axis .c2 c.c2))
                            (axis .c3 c.c3))
                          (axis .c12 c.c12))
                        (axis .c13 c.c13))
                      (axis .c23 c.c23))
                    (axis .c121 c.c121))
                  (axis .c131 c.c131))
                (axis .c232 c.c232))
              (axis .c122 c.c122))
            (axis .c133 c.c133))
          (axis .c233 c.c233))
        (axis .c123 c.c123))
      (axis .c231 c.c231) = c
  ext <;>
    simp [axis, RLCoordi.mul,
      RLCoordi.zero]

/-- The first three axes are the three coordinate generators. -/
theorem axis_generators :
    axis .c1 1 = generator1 ∧
      axis .c2 1 = generator2 ∧
        axis .c3 1 = generator3 :=
  ⟨rfl, rfl, rfl⟩

theorem hallCommutator_12 :
    hallCommutator generator1 generator2 =
      axis .c12 1 := by
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv generator1)
        (RLCoordi.rightInv generator2))
      (RLCoordi.mul generator1 generator2) =
        axis .c12 1
  ext <;>
    simp [generator1, generator2, axis,
      RLCoordi.mul, RLCoordi.rightInv,
      RLCoordi.zero]

theorem hallCommutator_13 :
    hallCommutator generator1 generator3 =
      axis .c13 1 := by
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv generator1)
        (RLCoordi.rightInv generator3))
      (RLCoordi.mul generator1 generator3) =
        axis .c13 1
  ext <;>
    simp [generator1, generator3, axis,
      RLCoordi.mul, RLCoordi.rightInv,
      RLCoordi.zero]

theorem hallCommutator_23 :
    hallCommutator generator2 generator3 =
      axis .c23 1 := by
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv generator2)
        (RLCoordi.rightInv generator3))
      (RLCoordi.mul generator2 generator3) =
        axis .c23 1
  ext <;>
    simp [generator2, generator3, axis,
      RLCoordi.mul, RLCoordi.rightInv,
      RLCoordi.zero]

private theorem hall_triple_axis
    (a b c : RLCoordi)
    (i : BasisIndex)
    (hab : hallCommutator a b = axis i 1)
    (j : BasisIndex)
    (hcalc :
      hallCommutator (axis i 1) c = axis j 1) :
    hallTripleCommutator a b c = axis j 1 := by
  rw [hallTripleCommutator, hab, hcalc]

theorem hallTriple_121 :
    hallTripleCommutator generator1 generator2
      generator1 = axis .c121 1 := by
  rw [hallTripleCommutator, hallCommutator_12]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c12 1))
        (RLCoordi.rightInv generator1))
      (RLCoordi.mul (axis .c12 1)
        generator1) =
      axis .c121 1
  ext <;>
    simp [generator1, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_131 :
    hallTripleCommutator generator1 generator3
      generator1 = axis .c131 1 := by
  rw [hallTripleCommutator, hallCommutator_13]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c13 1))
        (RLCoordi.rightInv generator1))
      (RLCoordi.mul (axis .c13 1)
        generator1) =
      axis .c131 1
  ext <;>
    simp [generator1, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_232 :
    hallTripleCommutator generator2 generator3
      generator2 = axis .c232 1 := by
  rw [hallTripleCommutator, hallCommutator_23]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c23 1))
        (RLCoordi.rightInv generator2))
      (RLCoordi.mul (axis .c23 1)
        generator2) =
      axis .c232 1
  ext <;>
    simp [generator2, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_122 :
    hallTripleCommutator generator1 generator2
      generator2 = axis .c122 1 := by
  rw [hallTripleCommutator, hallCommutator_12]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c12 1))
        (RLCoordi.rightInv generator2))
      (RLCoordi.mul (axis .c12 1)
        generator2) =
      axis .c122 1
  ext <;>
    simp [generator2, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_133 :
    hallTripleCommutator generator1 generator3
      generator3 = axis .c133 1 := by
  rw [hallTripleCommutator, hallCommutator_13]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c13 1))
        (RLCoordi.rightInv generator3))
      (RLCoordi.mul (axis .c13 1)
        generator3) =
      axis .c133 1
  ext <;>
    simp [generator3, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_233 :
    hallTripleCommutator generator2 generator3
      generator3 = axis .c233 1 := by
  rw [hallTripleCommutator, hallCommutator_23]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c23 1))
        (RLCoordi.rightInv generator3))
      (RLCoordi.mul (axis .c23 1)
        generator3) =
      axis .c233 1
  ext <;>
    simp [generator3, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_123 :
    hallTripleCommutator generator1 generator2
      generator3 = axis .c123 1 := by
  rw [hallTripleCommutator, hallCommutator_12]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c12 1))
        (RLCoordi.rightInv generator3))
      (RLCoordi.mul (axis .c12 1)
        generator3) =
      axis .c123 1
  ext <;>
    simp [generator3, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

theorem hallTriple_231 :
    hallTripleCommutator generator2 generator3
      generator1 = axis .c231 1 := by
  rw [hallTripleCommutator, hallCommutator_23]
  change
    RLCoordi.mul
      (RLCoordi.mul
        (RLCoordi.rightInv (axis .c23 1))
        (RLCoordi.rightInv generator1))
      (RLCoordi.mul (axis .c23 1)
        generator1) =
      axis .c231 1
  ext <;>
    simp [generator1, axis, RLCoordi.mul,
      RLCoordi.rightInv, RLCoordi.zero]

end P1960
end Struik
