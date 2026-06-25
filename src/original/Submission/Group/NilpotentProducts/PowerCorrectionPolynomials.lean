import Submission.Group.NilpotentProducts.HallPetrescoPowers
import Submission.Group.NilpotentProducts.GeneralPolynomialCoordinates

/-!
# Polynomial coordinates in Struik's Theorems H2 and H3

The exact uncollected identities are recorded in
`HallPetrescoPreliminaries`.  This file records their shared polynomial
content after choosing the canonical standard Hall normal form in a free
nilpotent truncation.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton
open Submission.TCTex

universe u

/-- Coordinate-polynomial form underlying Struik's Theorems H2 and H3.
For every Hall canonical basis, each coordinate of an arbitrary integer
power is given by a compositional binomial expression in the exponent and
the input coordinates. -/
theorem h_3_expression
    {G : Type u} [Group G]
    {m : ℕ}
    (b : HCBasis G m)
    (i : Fin m) :
    ∃ p : BExpr (Option (Fin m)),
      ∀ (c : Fin m → ℤ) (a : ℤ),
        BExpr.eval (canonicalPowAssignment a c) p =
          b.coord ((b.coord.symm c) ^ a) i := by
  refine ⟨b.powExpression i, fun c a => ?_⟩
  simpa [canonicalPowCoordinate, canonicalPowAssignment] using
    b.pow_expression_int i (canonicalPowAssignment a c)

/-- The canonical-basis polynomial clause shared by H2 and H3 for a free
nilpotent truncation, with the basis chosen internally. -/
theorem h_3_coordinates
    (d n : ℕ) :
    ∃ m : ℕ,
      ∃ b :
          HCBasis
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) m,
        ∀ i : Fin m,
          ∃ p : BExpr (Option (Fin m)),
            ∀ (c : Fin m → ℤ) (a : ℤ),
              BExpr.eval (canonicalPowAssignment a c) p =
                b.coord ((b.coord.symm c) ^ a) i := by
  obtain ⟨m, ⟨b⟩⟩ :=
    Submission.Edmonton.HCBasis.fg_torsion_nilpotent
      (G := LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} d)) n)
  exact
    ⟨m, b, fun i =>
      h_3_expression b i⟩

/-- Polynomial-coordinate part of Theorem H2 in the canonical standard Hall
normal form.  A coordinate of ordinary weight `s` in the `q`th power of a
fixed word has degree at most `s`. -/
theorem standard_coordinate_polynomial
    (t n : ℕ)
    (hn : 2 ≤ n)
    (y : FreeGroup (FreeGenerator.{u} t))
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index) :
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t n hn
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (y ^ q))
            s j)
      s := by
  simpa using
    standard_coordinates_fixed
      t n 1 hn (by omega) y (by simp) s hs hsn j

/-- Polynomial-coordinate part shared by Theorem H3.  The theorem permits a
fixed reordering of the displayed power factors; the polynomial bound for
the collected power itself is independent of that chosen display order. -/
theorem standard_coordinate_reordered
    (t n : ℕ)
    (hn : 2 ≤ n)
    (y : FreeGroup (FreeGenerator.{u} t))
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index) :
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t n hn
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (y ^ q))
            s j)
      s :=
  standard_coordinate_polynomial
    t n hn y s hs hsn j

/-- Struik's equation (3) for a canonical standard Hall coordinate.  The
integer-valued coordinate polynomial is expanded in the ordinary binomial
basis through its weight. -/
theorem standardHallCoordinate
    (t n : ℕ)
    (hn : 2 ≤ n)
    (y : FreeGroup (FreeGenerator.{u} t))
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index)
    (q : ℕ) :
    let f : ℕ → ℤ :=
      fun m =>
        standardHallCoordinates t n hn
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (y ^ m))
            s j
    f q =
      ∑ k ∈ Finset.range (s + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ) :=
  standard_binomial_expansion
    t n hn y s hs hsn j q

/-- Struik's displayed form of equation (3), with the vanishing constant
term omitted. -/
theorem standard_no_constant
    (t n : ℕ)
    (hn : 2 ≤ n)
    (y : FreeGroup (FreeGenerator.{u} t))
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index)
    (q : ℕ) :
    let f : ℕ → ℤ :=
      fun m =>
        standardHallCoordinates t n hn
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (y ^ m))
            s j
    f q =
      ∑ k ∈ Finset.range s,
        natBinomialCoefficient f (k + 1) *
          (Nat.choose q (k + 1) : ℤ) := by
  let f : ℕ → ℤ :=
    fun m =>
      standardHallCoordinates t n hn
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (y ^ m))
          s j
  have hexpansion :
      f q =
        ∑ k ∈ Finset.range (s + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ) := by
    simpa [f] using
      standardHallCoordinate t n hn y s hs hsn j q
  have hcoordOne :
      standardHallCoordinates t n hn 1 s j = 0 := by
    simpa [standardHallCoordinates] using
      coordinate_one_zero
        hn (standardHallFamily.{u} t)
        (fun r hr hrn =>
          standard_forms_associated
            t n r hr hrn)
        hs hsn j
  rw [Finset.sum_range_succ'] at hexpansion
  simpa [f, natBinomialCoefficient, hcoordOne] using hexpansion

/-- The binomial polynomial `choose X k` has degree exactly `k`. -/
theorem nat_choose_polynomial
    (k : ℕ) :
    (natChoosePolynomial k).natDegree = k := by
  rw [natChoosePolynomial]
  rw [Polynomial.natDegree_smul _]
  · rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact descPochhammer_natDegree ℤ k
  · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)

/-- The particular polynomial representing Struik's nested binomial
coefficient in equation (9) has degree exactly `i*j`. -/
theorem nested_choose_nat
    (i j : ℕ) :
    ((natChoosePolynomial j).comp
      (natChoosePolynomial i)).natDegree = i * j := by
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
  · rw [nat_choose_polynomial,
      nat_choose_polynomial, Nat.mul_comm]
  · apply mul_ne_zero
    · exact Polynomial.leadingCoeff_ne_zero.mpr (by
        intro h
        have heval := eval_nat_choose j j
        rw [h] at heval
        norm_num at heval)
    · apply pow_ne_zero
      exact Polynomial.leadingCoeff_ne_zero.mpr (by
        intro h
        have heval := eval_nat_choose i i
        rw [h] at heval
        norm_num at heval)

/-- Struik's equation (9): a binomial coefficient of a binomial coefficient
is an integer-valued polynomial of degree at most the product of the two
indices. -/
theorem nestedChoose_polynomial
    (i j : ℕ) :
    IVMost
      (fun alpha : ℕ => (Nat.choose (Nat.choose alpha i) j : ℤ))
      (i * j) := by
  refine
    ⟨(natChoosePolynomial j).comp (natChoosePolynomial i), ?_, ?_⟩
  · exact (nested_choose_nat i j).le
  · intro alpha
    rw [Polynomial.eval_comp, eval_nat_choose,
      eval_nat_choose]
    norm_cast

/-- The binomial-basis conclusion following equation (9).  For positive
indices the constant coefficient vanishes, so the expansion starts with
`choose alpha 1` and stops at `choose alpha (i*j)`. -/
theorem nested_choose_binomial
    (i j : ℕ)
    (hi : 0 < i)
    (hj : 0 < j)
    (alpha : ℕ) :
    (Nat.choose (Nat.choose alpha i) j : ℤ) =
      ∑ k ∈ Finset.range (i * j),
        natBinomialCoefficient
            (fun q : ℕ => (Nat.choose (Nat.choose q i) j : ℤ))
            (k + 1) *
          (Nat.choose alpha (k + 1) : ℤ) := by
  let f : ℕ → ℤ :=
    fun q => (Nat.choose (Nat.choose q i) j : ℤ)
  have hexpansion :=
    (nestedChoose_polynomial i j).nat_binomial_basisexpansion alpha
  have hfzero : f 0 = 0 := by
    simp [f, Nat.choose_eq_zero_of_lt hi, Nat.choose_eq_zero_of_lt hj]
  rw [Finset.sum_range_succ'] at hexpansion
  simpa [f, natBinomialCoefficient, hfzero] using hexpansion

/-- The rational polynomial behind equation (9) has the same exact degree
on signed integer inputs. -/
theorem nested_choose_degree
    (i j : ℕ) :
    (nestedRingChoose i j).natDegree = i * j := by
  simpa [nestedRingChoose] using
    nested_choose_nat i j

/-- Equation (9) for an arbitrary integer `alpha`, using generalized
binomial coefficients on both levels. -/
theorem nested_binomial_expansion
    (i j : ℕ)
    (alpha : ℤ) :
    Ring.choose (Ring.choose alpha i) j =
      ∑ k ∈ Finset.range (i * j + 1),
        nestedChooseCoefficient i j k * Ring.choose alpha k := by
  simpa [nestedChooseFunction, Nat.mul_comm] using
    nested_choose_sum i j alpha

/-- The signed equation (9) expansion starts at positive binomial index when
both nested indices are positive. -/
theorem nested_no_constant
    (i j : ℕ)
    (hi : 0 < i)
    (hj : 0 < j)
    (alpha : ℤ) :
    Ring.choose (Ring.choose alpha i) j =
      ∑ k ∈ Finset.range (i * j),
        nestedChooseCoefficient i j (k + 1) *
          Ring.choose alpha (k + 1) := by
  have hexpansion :=
    nested_binomial_expansion i j alpha
  rw [Finset.sum_range_succ'] at hexpansion
  simpa [nested_ring_choose i j hi hj] using hexpansion

end P1960
end Struik
