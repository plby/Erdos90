import Mathlib.RingTheory.Binomial

/-!
# Struik (1960), equation (18)

The coordinates are ordered as in Theorem 1:
`a₁,a₂,a₃,(a₁,a₂),(a₁,a₃),(a₂,a₃)`, followed by the eight standard
weight-three commutators listed in the paper.
-/

namespace Struik
namespace P1960

/-- The fourteen integral Hall coordinates used in Theorem 1. -/
@[ext]
structure RLCoordi where
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c12 : ℤ
  c13 : ℤ
  c23 : ℤ
  c121 : ℤ
  c131 : ℤ
  c232 : ℤ
  c122 : ℤ
  c133 : ℤ
  c233 : ℤ
  c123 : ℤ
  c231 : ℤ
  deriving DecidableEq

namespace RLCoordi

/-- The degree-two Chu-Vandermonde identity over the integers. -/
lemma choose_add_two (x y : ℤ) :
    Ring.choose (x + y) 2 =
      Ring.choose x 2 + x * y + Ring.choose y 2 := by
  rw [Ring.add_choose_eq 2 (Commute.all x y)]
  simp [Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ]
  ring

/-- The multiplication table displayed as Struik's equation (18). -/
noncomputable def mul
    (c d : RLCoordi) : RLCoordi where
  c1 := c.c1 + d.c1
  c2 := c.c2 + d.c2
  c3 := c.c3 + d.c3
  c12 := c.c12 + d.c12 - c.c2 * d.c1
  c13 := c.c13 + d.c13 - c.c3 * d.c1
  c23 := c.c23 + d.c23 - c.c3 * d.c2
  c121 :=
    c.c121 + d.c121 - c.c2 * Ring.choose d.c1 2 + c.c12 * d.c1
  c131 :=
    c.c131 + d.c131 - c.c3 * Ring.choose d.c1 2 + c.c13 * d.c1
  c232 :=
    c.c232 + d.c232 - c.c3 * Ring.choose d.c2 2 + c.c23 * d.c2
  c122 :=
    c.c122 + d.c122 - d.c1 * Ring.choose c.c2 2 +
      c.c12 * d.c2 - d.c1 * d.c2 * c.c2
  c133 :=
    c.c133 + d.c133 - d.c1 * Ring.choose c.c3 2 +
      c.c13 * d.c3 - d.c1 * d.c3 * c.c3
  c233 :=
    c.c233 + d.c233 - d.c2 * Ring.choose c.c3 2 +
      c.c23 * d.c3 - d.c2 * d.c3 * c.c3
  c123 :=
    c.c123 + d.c123 + c.c13 * d.c2 + c.c12 * d.c3 -
      d.c1 * c.c2 * c.c3 - c.c3 * d.c1 * d.c2 -
        c.c2 * d.c1 * d.c3
  c231 :=
    c.c231 + d.c231 + c.c23 * d.c1 + c.c13 * d.c2 -
      c.c3 * d.c1 * d.c2

/-- The all-zero coordinate tuple. -/
def zero : RLCoordi :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The zero tuple is a left identity for the table (18). -/
theorem zero_mul (c : RLCoordi) :
    mul zero c = c := by
  ext <;> simp [mul, zero]

/-- The zero tuple is a right identity for the table (18). -/
theorem mul_zero (c : RLCoordi) :
    mul c zero = c := by
  ext <;> simp [mul, zero]

/-- The integral multiplication table (18) is associative. -/
theorem mul_assoc
    (a b c : RLCoordi) :
    mul (mul a b) c = mul a (mul b c) := by
  ext <;> simp [mul, choose_add_two] <;> ring

/-- The triangular right inverse determined by table (18). -/
noncomputable def rightInv
    (c : RLCoordi) : RLCoordi where
  c1 := -c.c1
  c2 := -c.c2
  c3 := -c.c3
  c12 := -(c.c12 - c.c2 * (-c.c1))
  c13 := -(c.c13 - c.c3 * (-c.c1))
  c23 := -(c.c23 - c.c3 * (-c.c2))
  c121 :=
    -(c.c121 - c.c2 * Ring.choose (-c.c1) 2 + c.c12 * (-c.c1))
  c131 :=
    -(c.c131 - c.c3 * Ring.choose (-c.c1) 2 + c.c13 * (-c.c1))
  c232 :=
    -(c.c232 - c.c3 * Ring.choose (-c.c2) 2 + c.c23 * (-c.c2))
  c122 :=
    -(c.c122 - (-c.c1) * Ring.choose c.c2 2 +
      c.c12 * (-c.c2) - (-c.c1) * (-c.c2) * c.c2)
  c133 :=
    -(c.c133 - (-c.c1) * Ring.choose c.c3 2 +
      c.c13 * (-c.c3) - (-c.c1) * (-c.c3) * c.c3)
  c233 :=
    -(c.c233 - (-c.c2) * Ring.choose c.c3 2 +
      c.c23 * (-c.c3) - (-c.c2) * (-c.c3) * c.c3)
  c123 :=
    -(c.c123 + c.c13 * (-c.c2) + c.c12 * (-c.c3) -
      (-c.c1) * c.c2 * c.c3 - c.c3 * (-c.c1) * (-c.c2) -
        c.c2 * (-c.c1) * (-c.c3))
  c231 :=
    -(c.c231 + c.c23 * (-c.c1) + c.c13 * (-c.c2) -
      c.c3 * (-c.c1) * (-c.c2))

/-- The triangular inverse is a right inverse. -/
theorem mul_rightInv (c : RLCoordi) :
    mul c (rightInv c) = zero := by
  ext <;> simp [mul, rightInv, zero] <;> ring

/-- In the associative table, the triangular right inverse is also a
left inverse. -/
theorem rightInv_mul (c : RLCoordi) :
    mul (rightInv c) c = zero := by
  have hinvInv : rightInv (rightInv c) = c := by
    calc
      rightInv (rightInv c) =
          mul zero (rightInv (rightInv c)) := (zero_mul _).symm
      _ = mul (mul c (rightInv c)) (rightInv (rightInv c)) := by
            rw [mul_rightInv]
      _ = mul c (mul (rightInv c) (rightInv (rightInv c))) :=
            mul_assoc _ _ _
      _ = mul c zero := by rw [mul_rightInv]
      _ = c := mul_zero c
  simpa only [hinvInv] using mul_rightInv (rightInv c)

/-- Equation (18) defines the integral coordinate group used in the proof
of Theorem 1. -/
noncomputable instance : Group RLCoordi where
  mul := mul
  one := zero
  inv := rightInv
  mul_assoc := mul_assoc
  one_mul := zero_mul
  mul_one := mul_zero
  inv_mul_cancel := rightInv_mul

end RLCoordi

end P1960
end Struik
