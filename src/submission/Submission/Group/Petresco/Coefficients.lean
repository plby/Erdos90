import Submission.Group.Petresco.Bidegree
import Mathlib.RingTheory.Binomial

/-!
# Admissible Petresco coefficients

This file defines the integral coefficient module associated to arbitrary
left and right block sizes.  Its generators are products of signed binomial
coefficients whose selected degrees have prescribed left and right totals.
No primality assumption is needed for the resulting divisibility theorem.
-/

namespace Submission
namespace Edmonton

/-- The sign of a block occurring in a formal collection formula. -/
inductive SBSign
  | positive
  | negative
  deriving DecidableEq

/-- The integer represented by a signed block. -/
def SBSign.intValue : SBSign → ℤ
  | .positive => 1
  | .negative => -1

/-- The binomial coefficient associated to a positive or negative block of
size `M`. -/
def signedChoose : SBSign → ℕ → ℕ → ℤ
  | .positive, M, k => Nat.choose M k
  | .negative, M, k =>
      Int.negOnePow k * Nat.choose (M + k - 1) k

/-- Signed binomial coefficients agree with generalized ring binomial
coefficients at the corresponding signed integer. -/
lemma signed_choose_ring
    (sign : SBSign) (M k : ℕ) :
    signedChoose sign M k =
      Ring.choose (sign.intValue * (M : ℤ)) k := by
  cases sign with
  | positive =>
      simp [signedChoose, SBSign.intValue,
        Ring.choose_natCast]
  | negative =>
      cases k with
      | zero =>
          simp [signedChoose, SBSign.intValue]
      | succ k =>
          have hcast :
              ((M + (k + 1) - 1 : ℕ) : ℤ) =
                (M : ℤ) + (k + 1 : ℕ) - 1 := by
            omega
          rw [show SBSign.negative.intValue * (M : ℤ) =
            -(M : ℤ) by simp [SBSign.intValue]]
          rw [Ring.choose_neg, ← hcast, Ring.choose_natCast]
          simp [signedChoose, Units.smul_def]

/-- One signed input block and the number of labels selected from it. -/
structure AdmissibleCoefficientBlock where
  sign : SBSign
  degree : ℕ

/-- The total selected degree of a list of signed blocks. -/
def admissibleBlockDegree
    (blocks : List AdmissibleCoefficientBlock) : ℕ :=
  (blocks.map AdmissibleCoefficientBlock.degree).sum

/-- The product of signed binomial coefficients contributed by a block
list. -/
def admissibleBlockProduct
    (M : ℕ) (blocks : List AdmissibleCoefficientBlock) : ℤ :=
  (blocks.map fun block =>
    signedChoose block.sign M block.degree).prod

/-- Products of signed binomial coefficients with left degree `r` and right
degree `s`. -/
def admissibleCoefficientGenerators
    (M N r s : ℕ) : Set ℤ :=
  { E |
    ∃ left right : List AdmissibleCoefficientBlock,
      admissibleBlockDegree left = r ∧
        admissibleBlockDegree right = s ∧
          admissibleBlockProduct M left *
            admissibleBlockProduct N right = E }

/-- The integral module `A_{r,s}(M,N)` of admissible coefficients. -/
def admissibleCoefficients
    (M N r s : ℕ) : Submodule ℤ ℤ :=
  Submodule.span ℤ (admissibleCoefficientGenerators M N r s)

/-- The admissible coefficient module attached to the exact bidegree of an
Edmonton formal commutator. -/
abbrev formalAdmissibleCoefficients
    (M N : ℕ) (c : FormalCommutator Bool) : Submodule ℤ ℤ :=
  admissibleCoefficients M N (leftDegree c) (rightDegree c)

/-- Appending one signed left block preserves provenance and adds its selected
degree to the left coordinate. -/
lemma admissible_coefficients_left
    {M N r s : ℕ}
    (sign : SBSign)
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ admissibleCoefficients M N r s) :
    signedChoose sign M k * E ∈
      admissibleCoefficients M N (k + r) s := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      apply Submodule.subset_span
      refine
        ⟨{ sign := sign, degree := k } :: left, right, ?_, hs, ?_⟩
      · simpa only [admissibleBlockDegree] using
          congrArg (fun n => k + n) hr
      · simp [admissibleBlockProduct]
        ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [mul_add] using
        (admissibleCoefficients M N (k + r) s).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert
        (admissibleCoefficients M N (k + r) s).smul_mem c ihE using 1
      simp
      ring

/-- Appending one signed right block preserves provenance and adds its selected
degree to the right coordinate. -/
lemma admissible_coefficients_right
    {M N r s : ℕ}
    (sign : SBSign)
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ admissibleCoefficients M N r s) :
    signedChoose sign N k * E ∈
      admissibleCoefficients M N r (k + s) := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      apply Submodule.subset_span
      refine
        ⟨left, { sign := sign, degree := k } :: right, hr, ?_, ?_⟩
      · simpa only [admissibleBlockDegree] using
          congrArg (fun n => k + n) hs
      · simp [admissibleBlockProduct]
        ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [mul_add] using
        (admissibleCoefficients M N r (k + s)).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert
        (admissibleCoefficients M N r (k + s)).smul_mem c ihE using 1
      simp
      ring

/-- The empty block pattern has coefficient one and bidegree `(0, 0)`. -/
lemma admissible_coefficients_zero
    (M N : ℕ) :
    (1 : ℤ) ∈ admissibleCoefficients M N 0 0 := by
  apply Submodule.subset_span
  exact
    ⟨[], [], by simp [admissibleBlockDegree],
      by simp [admissibleBlockDegree],
      by simp [admissibleBlockProduct]⟩

/-- Products of admissible coefficients remain admissible after adding their
exact bidegrees.  This is the provenance rule for a correction bracket. -/
lemma mul_coefficients
    {M N r s r' s' : ℕ}
    {E F : ℤ}
    (hE : E ∈ admissibleCoefficients M N r s)
    (hF : F ∈ admissibleCoefficients M N r' s') :
    E * F ∈ admissibleCoefficients M N (r + r') (s + s') := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      induction hF using Submodule.span_induction with
      | mem F hF =>
          rcases hF with ⟨left', right', hr', hs', rfl⟩
          apply Submodule.subset_span
          refine ⟨left ++ left', right ++ right', ?_, ?_, ?_⟩
          · simp only [admissibleBlockDegree, List.map_append, List.sum_append]
            exact congrArg₂ Nat.add hr hr'
          · simp only [admissibleBlockDegree, List.map_append, List.sum_append]
            exact congrArg₂ Nat.add hs hs'
          · simp [admissibleBlockProduct]
            ring
      | zero =>
          simp
      | add E F _hE _hF ihE ihF =>
          simpa [mul_add] using
            (admissibleCoefficients M N (r + r') (s + s')).add_mem ihE ihF
      | smul c E _hE ihE =>
          convert
            (admissibleCoefficients M N (r + r') (s + s')).smul_mem c ihE using 1
          simp
          ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [add_mul] using
        (admissibleCoefficients M N (r + r') (s + s')).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert
        (admissibleCoefficients M N (r + r') (s + s')).smul_mem c ihE using 1
      simp
      ring

/-- The elementary positive-binomial divisibility
`M ∣ k * choose M k`. -/
lemma dvd_mul_choose (M k : ℕ) :
    M ∣ k * Nat.choose M k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      by_cases hM : M = 0
      · subst M
        simp
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hsucc : M - 1 + 1 = M := by omega
        have hchoose := Nat.add_one_mul_choose_eq (M - 1) k
        rw [hsucc] at hchoose
        rw [Nat.mul_comm, ← hchoose]
        exact dvd_mul_right _ _

/-- The elementary negative-binomial divisibility for the multichoose
coefficient in `choose (-M) k`. -/
lemma dvd_negative_choose (M k : ℕ) :
    M ∣ k * Nat.choose (M + k - 1) k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      have hchoose := Nat.choose_succ_right_eq (M + k) k
      have hsub : M + k - k = M := by omega
      rw [show M + (k + 1) - 1 = M + k by omega,
        Nat.mul_comm, hchoose, hsub]
      exact dvd_mul_left _ _

/-- Both signs satisfy the same integral divisibility law. -/
lemma cast_dvd_choose
    (sign : SBSign) (M k : ℕ) :
    (M : ℤ) ∣ (k : ℤ) * signedChoose sign M k := by
  cases sign with
  | positive =>
      simpa [signedChoose] using
        (show (M : ℤ) ∣ (k * Nat.choose M k : ℕ) by
          exact_mod_cast dvd_mul_choose M k)
  | negative =>
      have hcast :
          (M : ℤ) ∣
            (k : ℤ) * (Nat.choose (M + k - 1) k : ℤ) := by
        exact_mod_cast dvd_negative_choose M k
      simpa [signedChoose, mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_left hcast (Int.negOnePow k)

/-- A block size divides the total selected degree times the product of all
signed binomial coefficients from those blocks. -/
lemma cast_dvd_admissible
    (M : ℕ) :
    ∀ blocks : List AdmissibleCoefficientBlock,
      (M : ℤ) ∣
        (admissibleBlockDegree blocks : ℤ) *
          admissibleBlockProduct M blocks
  | [] => by
      simp [admissibleBlockDegree, admissibleBlockProduct]
  | block :: blocks => by
      have hhead :=
        cast_dvd_choose block.sign M block.degree
      have htail :=
        cast_dvd_admissible
          M blocks
      convert
        dvd_add
          (dvd_mul_of_dvd_left hhead
            (admissibleBlockProduct M blocks))
          (dvd_mul_of_dvd_left htail
            (signedChoose block.sign M block.degree)) using 1
      simp [admissibleBlockDegree, admissibleBlockProduct]
      ring

/-- Every coefficient in `A_{r,s}(M,N)` has the expected divisibility in
both bidegree directions. -/
theorem admissibleCoefficient_divisibility
    {M N r s : ℕ} {E : ℤ}
    (hE : E ∈ admissibleCoefficients M N r s) :
    (M : ℤ) ∣ (r : ℤ) * E ∧
      (N : ℤ) ∣ (s : ℤ) * E := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      constructor
      · convert
          dvd_mul_of_dvd_left
            (cast_dvd_admissible
              M left)
            (admissibleBlockProduct N right) using 1
        simp [hr]
        ring
      · convert
          dvd_mul_of_dvd_left
            (cast_dvd_admissible
              N right)
            (admissibleBlockProduct M left) using 1
        simp [hs]
        ring
  | zero =>
      simp
  | add E F _ _ hE hF =>
      constructor
      · simpa [mul_add] using dvd_add hE.1 hF.1
      · simpa [mul_add] using dvd_add hE.2 hF.2
  | smul c E _ hE =>
      constructor
      · convert dvd_mul_of_dvd_left hE.1 c using 1
        simp
        ring
      · convert dvd_mul_of_dvd_left hE.2 c using 1
        simp
        ring

/-- The divisibility theorem specialized to the exact bidegree of an
Edmonton formal commutator. -/
theorem formal_admissible_divisibility
    {M N : ℕ} {c : FormalCommutator Bool} {E : ℤ}
    (hE : E ∈ formalAdmissibleCoefficients M N c) :
    (M : ℤ) ∣ (leftDegree c : ℤ) * E ∧
      (N : ℤ) ∣ (rightDegree c : ℤ) * E :=
  admissibleCoefficient_divisibility hE

end Edmonton
end Submission
