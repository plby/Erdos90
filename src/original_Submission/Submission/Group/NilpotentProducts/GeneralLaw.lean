import Submission.Group.NilpotentProducts.ExceptionalTwoLaw

/-!
# Struik (1960), equation (18) in arbitrary rank

This is the integral coordinate group used in Theorem 2.  Its coordinates
are arranged in the order stated in the paper:

`aᵢ`, `(aᵢ,aⱼ)`, `(aᵢ,aⱼ,aᵢ)`, `(aᵢ,aⱼ,aⱼ)`,
`(aᵢ,aⱼ,aₖ)`, `(aⱼ,aₖ,aᵢ)`.
-/

namespace Struik
namespace P1960

/-- The arbitrary-rank integral coordinates governed by equation (18). -/
@[ext]
structure GCoordi (t : ℕ) where
  single : Fin t → ℤ
  pair : Pair t → ℤ
  pairLeft : Pair t → ℤ
  pairRight : Pair t → ℤ
  tripleFirst : Triple t → ℤ
  tripleSecond : Triple t → ℤ

namespace GCoordi

/-- The arbitrary-rank multiplication table in Struik's equation (18). -/
noncomputable def mul {t : ℕ}
    (c d : GCoordi t) :
    GCoordi t where
  single i := c.single i + d.single i
  pair q := c.pair q + d.pair q - c.single q.j * d.single q.i
  pairLeft q :=
    c.pairLeft q + d.pairLeft q -
      c.single q.j * Ring.choose (d.single q.i) 2 +
      c.pair q * d.single q.i
  pairRight q :=
    c.pairRight q + d.pairRight q -
      d.single q.i * Ring.choose (c.single q.j) 2 +
      c.pair q * d.single q.j -
      d.single q.i * d.single q.j * c.single q.j
  tripleFirst q :=
    c.tripleFirst q + d.tripleFirst q +
      c.pair q.ik * d.single q.j +
      c.pair q.ij * d.single q.k -
      d.single q.i * c.single q.j * c.single q.k -
      c.single q.k * d.single q.i * d.single q.j -
      c.single q.j * d.single q.i * d.single q.k
  tripleSecond q :=
    c.tripleSecond q + d.tripleSecond q +
      c.pair q.jk * d.single q.i +
      c.pair q.ik * d.single q.j -
      c.single q.k * d.single q.i * d.single q.j

/-- The all-zero arbitrary-rank coordinate tuple. -/
def zero (t : ℕ) : GCoordi t where
  single _ := 0
  pair _ := 0
  pairLeft _ := 0
  pairRight _ := 0
  tripleFirst _ := 0
  tripleSecond _ := 0

theorem zero_mul {t : ℕ} (c : GCoordi t) :
    mul (zero t) c = c := by
  ext <;> simp [mul, zero]

theorem mul_zero {t : ℕ} (c : GCoordi t) :
    mul c (zero t) = c := by
  ext <;> simp [mul, zero]

/-- Equation (18) is associative in arbitrary rank. -/
theorem mul_assoc {t : ℕ}
    (a b c : GCoordi t) :
    mul (mul a b) c = mul a (mul b c) := by
  ext <;>
    simp [mul, Triple.ij, Triple.ik,
      Triple.jk, RLCoordi.choose_add_two] <;>
    ring

/-- The triangular right inverse for the arbitrary-rank equation-(18)
coordinates. -/
noncomputable def rightInv {t : ℕ}
    (c : GCoordi t) :
    GCoordi t where
  single i := -c.single i
  pair q :=
    -(c.pair q - c.single q.j * (-c.single q.i))
  pairLeft q :=
    -(c.pairLeft q -
      c.single q.j * Ring.choose (-c.single q.i) 2 +
      c.pair q * (-c.single q.i))
  pairRight q :=
    -(c.pairRight q -
      (-c.single q.i) * Ring.choose (c.single q.j) 2 +
      c.pair q * (-c.single q.j) -
      (-c.single q.i) * (-c.single q.j) * c.single q.j)
  tripleFirst q :=
    -(c.tripleFirst q +
      c.pair q.ik * (-c.single q.j) +
      c.pair q.ij * (-c.single q.k) -
      (-c.single q.i) * c.single q.j * c.single q.k -
      c.single q.k * (-c.single q.i) * (-c.single q.j) -
      c.single q.j * (-c.single q.i) * (-c.single q.k))
  tripleSecond q :=
    -(c.tripleSecond q +
      c.pair q.jk * (-c.single q.i) +
      c.pair q.ik * (-c.single q.j) -
      c.single q.k * (-c.single q.i) * (-c.single q.j))

theorem mul_rightInv {t : ℕ} (c : GCoordi t) :
    mul c (rightInv c) = zero t := by
  ext <;>
    simp [mul, rightInv, zero, Triple.ij,
      Triple.ik, Triple.jk] <;>
    ring

theorem rightInv_mul {t : ℕ} (c : GCoordi t) :
    mul (rightInv c) c = zero t := by
  have hinvInv : rightInv (rightInv c) = c := by
    calc
      rightInv (rightInv c) =
          mul (zero t) (rightInv (rightInv c)) := (zero_mul _).symm
      _ = mul (mul c (rightInv c)) (rightInv (rightInv c)) := by
            rw [mul_rightInv]
      _ = mul c (mul (rightInv c) (rightInv (rightInv c))) :=
            mul_assoc _ _ _
      _ = mul c (zero t) := by rw [mul_rightInv]
      _ = c := mul_zero c
  simpa only [hinvInv] using mul_rightInv (rightInv c)

/-- The arbitrary-rank equation-(18) table is a group. -/
noncomputable instance {t : ℕ} : Group (GCoordi t) where
  mul := mul
  one := zero t
  inv := rightInv
  mul_assoc := mul_assoc
  one_mul := zero_mul
  mul_one := mul_zero
  inv_mul_cancel := rightInv_mul

end GCoordi

end P1960
end Struik
