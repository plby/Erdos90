import Submission.Group.NilpotentProducts.RankThreeLaw
import Mathlib.Tactic.DeriveFintype

/-!
# Struik (1960), equation (29)

This file records the multiplication table used in Theorem 4.  The
coordinates are indexed only by strictly increasing pairs and triples, as
in the paper.
-/

namespace Struik
namespace P1960

/-- An index `i < j` for the pair coordinates in equation (29). -/
@[ext]
structure Pair (t : ℕ) where
  i : Fin t
  j : Fin t
  lt : i < j
  deriving DecidableEq, Fintype

namespace Pair

@[simp] theorem i_ne_j {t : ℕ} (q : Pair t) :
    q.i ≠ q.j :=
  ne_of_lt q.lt

@[simp] theorem j_ne_i {t : ℕ} (q : Pair t) :
    q.j ≠ q.i :=
  ne_of_gt q.lt

@[simp] theorem eq_iff_fields {t : ℕ} (q r : Pair t) :
    q = r ↔ q.i = r.i ∧ q.j = r.j := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hi, hj⟩
    cases q with
    | mk i j hij =>
        cases r with
        | mk i' j' hij' =>
            simp only at hi hj
            subst i'
            subst j'
            rfl

end Pair

instance {t : ℕ} : LinearOrder (Pair t) :=
  LinearOrder.lift'
    (fun q => toLex (q.i, q.j))
    (by
      rintro ⟨i, j, hij⟩ ⟨i', j', hij'⟩ h
      have hp : (i, j) = (i', j') :=
        congrArg ofLex h
      cases hp
      rfl)

/-- An index `i < j < k` for the two triple coordinates in equation (29). -/
@[ext]
structure Triple (t : ℕ) where
  i : Fin t
  j : Fin t
  k : Fin t
  lt_ij : i < j
  lt_jk : j < k
  deriving DecidableEq, Fintype

instance {t : ℕ} : LinearOrder (Triple t) :=
  LinearOrder.lift'
    (fun q => toLex (q.i, toLex (q.j, q.k)))
    (by
      rintro ⟨i, j, k, hij, hjk⟩
        ⟨i', j', k', hij', hjk'⟩ h
      have hp :
          (i, toLex (j, k)) =
            (i', toLex (j', k')) :=
        congrArg ofLex h
      have houter := Prod.mk.inj hp
      have hinner :
          (j, k) = (j', k') :=
        congrArg ofLex houter.2
      cases houter.1
      cases hinner
      rfl)

namespace Triple

@[simp] theorem i_ne_j {t : ℕ} (q : Triple t) :
    q.i ≠ q.j :=
  ne_of_lt q.lt_ij

@[simp] theorem j_ne_i {t : ℕ} (q : Triple t) :
    q.j ≠ q.i :=
  ne_of_gt q.lt_ij

@[simp] theorem j_ne_k {t : ℕ} (q : Triple t) :
    q.j ≠ q.k :=
  ne_of_lt q.lt_jk

@[simp] theorem k_ne_j {t : ℕ} (q : Triple t) :
    q.k ≠ q.j :=
  ne_of_gt q.lt_jk

@[simp] theorem i_ne_k {t : ℕ} (q : Triple t) :
    q.i ≠ q.k :=
  ne_of_lt (q.lt_ij.trans q.lt_jk)

@[simp] theorem k_ne_i {t : ℕ} (q : Triple t) :
    q.k ≠ q.i :=
  ne_of_gt (q.lt_ij.trans q.lt_jk)

@[simp] theorem eq_iff_fields {t : ℕ} (q r : Triple t) :
    q = r ↔ q.i = r.i ∧ q.j = r.j ∧ q.k = r.k := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hi, hj, hk⟩
    cases q with
    | mk i j k hij hjk =>
        cases r with
        | mk i' j' k' hij' hjk' =>
            simp only at hi hj hk
            subst i'
            subst j'
            subst k'
            rfl

def ij {t : ℕ} (q : Triple t) : Pair t :=
  ⟨q.i, q.j, q.lt_ij⟩

def ik {t : ℕ} (q : Triple t) : Pair t :=
  ⟨q.i, q.k, q.lt_ij.trans q.lt_jk⟩

def jk {t : ℕ} (q : Triple t) : Pair t :=
  ⟨q.j, q.k, q.lt_jk⟩

end Triple

/-- The `t + 3 * choose t 2 + 2 * choose t 3` integral coordinates
appearing in Theorem 4. -/
@[ext]
structure ELCoordi (t : ℕ) where
  single : Fin t → ℤ
  pair : Pair t → ℤ
  pairLeftSquare : Pair t → ℤ
  pairRightSquare : Pair t → ℤ
  tripleFirst : Triple t → ℤ
  tripleSecond : Triple t → ℤ

namespace ELCoordi

/-- Struik's auxiliary expression
`α(cᵢⱼ) = cᵢⱼ + 2cᵢⱼ⁽²⁾ + 2cᵢⱼ⁽³⁾`. -/
def alpha {t : ℕ} (c : ELCoordi t)
    (q : Pair t) : ℤ :=
  c.pair q + 2 * c.pairLeftSquare q + 2 * c.pairRightSquare q

/-- The multiplication table displayed as Struik's equation (29). -/
noncomputable def mul {t : ℕ}
    (c d : ELCoordi t) : ELCoordi t where
  single i := c.single i + d.single i
  pair q :=
    c.pair q + d.pair q -
      2 * alpha c q * d.single q.i -
      2 * alpha c q * d.single q.j -
      c.single q.j * d.single q.i +
      2 * c.single q.j * Ring.choose (d.single q.i) 2 +
      2 * d.single q.i * Ring.choose (c.single q.j) 2 +
      2 * c.single q.j * d.single q.i * d.single q.j
  pairLeftSquare q :=
    c.pairLeftSquare q + d.pairLeftSquare q +
      alpha c q * d.single q.i -
      c.single q.j * Ring.choose (d.single q.i) 2
  pairRightSquare q :=
    c.pairRightSquare q + d.pairRightSquare q -
      d.single q.i * Ring.choose (c.single q.j) 2 +
      alpha c q * d.single q.j -
      c.single q.j * d.single q.i * d.single q.j
  tripleFirst q :=
    c.tripleFirst q + d.tripleFirst q +
      alpha c q.ik * d.single q.j -
      c.single q.k * d.single q.i * d.single q.j -
      d.single q.i * c.single q.j * c.single q.k +
      alpha c q.ij * d.single q.k -
      c.single q.j * d.single q.i * d.single q.k
  tripleSecond q :=
    c.tripleSecond q + d.tripleSecond q +
      alpha c q.jk * d.single q.i +
      alpha c q.ik * d.single q.j -
      c.single q.k * d.single q.i * d.single q.j

/-- The all-zero tuple. -/
def zero (t : ℕ) : ELCoordi t where
  single _ := 0
  pair _ := 0
  pairLeftSquare _ := 0
  pairRightSquare _ := 0
  tripleFirst _ := 0
  tripleSecond _ := 0

/-- The zero tuple is a left identity for table (29). -/
theorem zero_mul {t : ℕ} (c : ELCoordi t) :
    mul (zero t) c = c := by
  ext <;> simp [mul, zero, alpha]

/-- The zero tuple is a right identity for table (29). -/
theorem mul_zero {t : ℕ} (c : ELCoordi t) :
    mul c (zero t) = c := by
  ext <;> simp [mul, zero, alpha]

/-- The integral multiplication table (29) is associative. -/
theorem mul_assoc {t : ℕ}
    (a b c : ELCoordi t) :
    mul (mul a b) c = mul a (mul b c) := by
  ext <;>
    simp [mul, alpha, Triple.ij, Triple.ik,
      Triple.jk, RLCoordi.choose_add_two] <;>
    ring

/-- The triangular right inverse determined by table (29). -/
noncomputable def rightInv {t : ℕ}
    (c : ELCoordi t) : ELCoordi t where
  single i := -c.single i
  pair q :=
    -(c.pair q -
      2 * alpha c q * (-c.single q.i) -
      2 * alpha c q * (-c.single q.j) -
      c.single q.j * (-c.single q.i) +
      2 * c.single q.j * Ring.choose (-c.single q.i) 2 +
      2 * (-c.single q.i) * Ring.choose (c.single q.j) 2 +
      2 * c.single q.j * (-c.single q.i) * (-c.single q.j))
  pairLeftSquare q :=
    -(c.pairLeftSquare q +
      alpha c q * (-c.single q.i) -
      c.single q.j * Ring.choose (-c.single q.i) 2)
  pairRightSquare q :=
    -(c.pairRightSquare q -
      (-c.single q.i) * Ring.choose (c.single q.j) 2 +
      alpha c q * (-c.single q.j) -
      c.single q.j * (-c.single q.i) * (-c.single q.j))
  tripleFirst q :=
    -(c.tripleFirst q +
      alpha c q.ik * (-c.single q.j) -
      c.single q.k * (-c.single q.i) * (-c.single q.j) -
      (-c.single q.i) * c.single q.j * c.single q.k +
      alpha c q.ij * (-c.single q.k) -
      c.single q.j * (-c.single q.i) * (-c.single q.k))
  tripleSecond q :=
    -(c.tripleSecond q +
      alpha c q.jk * (-c.single q.i) +
      alpha c q.ik * (-c.single q.j) -
      c.single q.k * (-c.single q.i) * (-c.single q.j))

/-- The triangular inverse is a right inverse for table (29). -/
theorem mul_rightInv {t : ℕ} (c : ELCoordi t) :
    mul c (rightInv c) = zero t := by
  ext <;>
    simp [mul, rightInv, zero, alpha, Triple.ij,
      Triple.ik, Triple.jk] <;>
    ring

/-- In the associative table, the triangular right inverse is also a
left inverse. -/
theorem rightInv_mul {t : ℕ} (c : ELCoordi t) :
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

/-- Equation (29) defines Struik's integral coordinate group for
Theorem 4. -/
noncomputable instance {t : ℕ} : Group (ELCoordi t) where
  mul := mul
  one := zero t
  inv := rightInv
  mul_assoc := mul_assoc
  one_mul := zero_mul
  mul_one := mul_zero
  inv_mul_cancel := rightInv_mul

end ELCoordi

end P1960
end Struik
