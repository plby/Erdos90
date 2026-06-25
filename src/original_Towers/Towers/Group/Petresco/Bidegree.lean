import Towers.Group.Edmonton.HallBasicCommutators

/-!
# Exact bidegrees for formal commutators

This file refines the scalar formal weight to an additive grade.  For formal
commutators on two generators, the resulting bidegree counts the occurrences
of each generator separately.
-/

namespace Towers
namespace Edmonton

universe u v

/-- Add the grades of all variable occurrences in a formal commutator. -/
def formalGrade {X : Type u} {M : Type v} [AddCommMonoid M]
    (grade : X → M) : FormalCommutator X → M
  | FreeMagma.of x => grade x
  | FreeMagma.mul u v => formalGrade grade u + formalGrade grade v

@[simp]
lemma formalGrade_variable {X : Type u} {M : Type v} [AddCommMonoid M]
    (grade : X → M) (x : X) :
    formalGrade grade (FreeMagma.of x) = grade x :=
  rfl

@[simp]
lemma formalGrade_bracket {X : Type u} {M : Type v} [AddCommMonoid M]
    (grade : X → M) (u v : FormalCommutator X) :
    formalGrade grade (formalBracket u v) =
      formalGrade grade u + formalGrade grade v :=
  rfl

/-- The exact numbers of occurrences of the left (`false`) and right (`true`)
generators. -/
def formalBidegree : FormalCommutator Bool → ℕ × ℕ :=
  formalGrade fun
    | false => (1, 0)
    | true => (0, 1)

@[simp]
lemma formalBidegree_false :
    formalBidegree (FreeMagma.of false) = (1, 0) :=
  rfl

@[simp]
lemma formalBidegree_true :
    formalBidegree (FreeMagma.of true) = (0, 1) :=
  rfl

@[simp]
lemma formalBidegree_bracket (u v : FormalCommutator Bool) :
    formalBidegree (formalBracket u v) =
      formalBidegree u + formalBidegree v :=
  rfl

/-- The number of occurrences of the left generator `false`. -/
def leftDegree (c : FormalCommutator Bool) : ℕ :=
  (formalBidegree c).1

/-- The number of occurrences of the right generator `true`. -/
def rightDegree (c : FormalCommutator Bool) : ℕ :=
  (formalBidegree c).2

/-- Grade the left generator by `A` and the right generator by `B`. -/
def weightedDegree (A B : ℕ) : FormalCommutator Bool → ℕ :=
  formalGrade fun
    | false => A
    | true => B

/-- Scalar formal weight is the sum of the two exact degrees. -/
lemma formal_degree_right
    (c : FormalCommutator Bool) :
    formalWeight c = leftDegree c + rightDegree c := by
  induction c with
  | of x =>
      cases x <;> rfl
  | mul u v ihu ihv =>
      change formalWeight u + formalWeight v =
        (leftDegree u + leftDegree v) + (rightDegree u + rightDegree v)
      rw [ihu, ihv]
      omega

/-- A two-generator weighted degree is the corresponding linear combination
of the exact left and right degrees. -/
lemma weighted_b_right
    (A B : ℕ) (c : FormalCommutator Bool) :
    weightedDegree A B c =
      A * leftDegree c + B * rightDegree c := by
  induction c with
  | of x =>
      cases x <;> simp [weightedDegree, leftDegree, rightDegree,
        formalBidegree]
  | mul u v ihu ihv =>
      change weightedDegree A B u + weightedDegree A B v =
        A * (leftDegree u + leftDegree v) +
          B * (rightDegree u + rightDegree v)
      rw [ihu, ihv, Nat.mul_add, Nat.mul_add]
      omega

end Edmonton
end Towers
