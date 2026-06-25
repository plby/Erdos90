import Towers.Group.NilpotentProducts.CoefficientCombinatorics
import Towers.Group.NilpotentProducts.TwoSidedWords
import Towers.Group.NilpotentProducts.ChainMultiplication
import Towers.Group.Edmonton.HallEmbeddings

open scoped BigOperators

namespace Struik

open Towers Edmonton

/-- The exact raw word identity used before the Hall collection displayed in
equation (46). It does not assert that the correction factors are standard
commutators. -/
theorem rawSidedIdentity
    {G : Type*} [Group G] (uᵢ uⱼ : G) (cᵢ dⱼ : ℕ) :
    uᵢ ^ cᵢ * uⱼ ^ dⱼ =
      uⱼ ^ dⱼ * uᵢ ^ cᵢ *
        evalFormalWord
          (fun | false => uᵢ | true => uⱼ)
          (twoSidedWord cᵢ dⱼ) :=
  raw_sided_identity uᵢ uⱼ cᵢ dⱼ

/-- Each factor in the raw word preceding equation (47) has a count equal to
a product of two binomial coefficients. This is not equation (47), which is
the result after collection into standard commutators. -/
theorem rawBinomialCount
    {cᵢ dⱼ : ℕ} {w : Word} (hw : w ∈ twoSidedWord cᵢ dⱼ) :
    ∃ α β,
      (twoSidedWord cᵢ dⱼ).count w =
        Nat.choose cᵢ α * Nat.choose dⱼ β := by
  obtain ⟨q, t, hw', hcount⟩ := raw_binomial_count hw
  exact ⟨q + 1, t + 1, hcount⟩

/-- The raw-word chain count used in the derivation of equation (48).
Identifying this count with the final standard Hall coordinate requires the
collection argument of Lemma 4. -/
theorem rawChainCount
    {t s : ℕ} (hts : t < s) (cₜ d₁ : ℕ) :
    (twoSidedWord cₜ d₁).count (aChain (s - t - 1)) =
      cₜ * Nat.choose d₁ (s - t) := by
  rw [chain_sided_word]
  congr 2
  omega

/-- The raw-word chain count used in the derivation of equation (50).
Identifying this count with the final standard Hall coordinate requires the
collection argument of Lemma 4. -/
theorem bChainCount
    {s : ℕ} (hs : 0 < s) (c₂ d₁ : ℕ) :
    (twoSidedWord c₂ d₁).count (bChain (s - 1)) =
      d₁ * Nat.choose c₂ s := by
  rw [count_b_sided]
  congr 2
  omega

/-- A nonnegative two-variable binomial expansion whose support satisfies
the degree bounds used in Lemma 5 and equation (52). -/
structure BBExp (leftBound rightBound : ℕ) where
  coefficient : ℕ → ℕ → ℕ
  coefficient_left :
    ∀ {a b}, leftBound < a → coefficient a b = 0
  coefficient_right :
    ∀ {a b}, rightBound < b → coefficient a b = 0

namespace BBExp

def eval
    {leftBound rightBound : ℕ}
    (E : BBExp leftBound rightBound)
    (r s : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (leftBound + 1),
    ∑ b ∈ Finset.range (rightBound + 1),
      E.coefficient a b * Nat.choose r a * Nat.choose s b

/-- Lemma 5 supplies the bounded nonnegative expansion needed whenever a
binomial coefficient is taken of a product of two binomial coefficients. -/
noncomputable def ofNestedChoose (i j k : ℕ) :
    BBExp (i * k) (j * k) where
  coefficient := Struik.coefficient i j k
  coefficient_left := by
    intro a b ha
    exact Struik.coefficient_zero_left ha
  coefficient_right := by
    intro a b hb
    exact Struik.coefficient_zero_right hb

theorem eval_nested_choose (i j k r s : ℕ) :
    (ofNestedChoose i j k).eval r s =
      Nat.choose (Nat.choose r i * Nat.choose s j) k := by
  symm
  exact choose_coeff_mul i j k r s

end BBExp

/-- Multiplication coordinates attached to a supplied finite Hall canonical
basis are compositional integer-valued binomial expressions.

This is a general transfer theorem, not Struik's Theorem 5: the latter must
construct the standard-commutator coordinates for the free nilpotent group
and prove the particular nonnegative expansion and degree bounds in (52). -/
theorem basis_binomial_expression
    {G : Type*} [Group G] {n : ℕ}
    (b : HCBasis G n) :
    ∀ i, IEMap
      (canonicalMulCoordinate b.coord i) :=
  (b.canonical_coordinate_expressions).1

/-- Corollary 1, first exceptional case: among grid words of weight at most
`p+1`, an `a`-binomial index equal to `p` forces the pure `a`-chain. -/
theorem left_exception_only
    {p q t : ℕ}
    (ht : t + 1 = p)
    (hweight : 2 + q + t ≤ p + 1) :
    q = 0 := by
  omega

/-- Corollary 1, second exceptional case: a `b`-binomial index equal to `p`
forces the pure `b`-chain. -/
theorem right_exception_only
    {p q t : ℕ}
    (hq : q + 1 = p)
    (hweight : 2 + q + t ≤ p + 1) :
    t = 0 := by
  omega

/-- A positive exponent list of length at least three and total degree at
most `p+1` cannot contain the index `p`. This is the degree-counting core of
Corollary 2. -/
theorem indices_lt_prime
    {p : ℕ}
    (degrees : List ℕ)
    (hpositive : ∀ d ∈ degrees, 0 < d)
    (hlength : 3 ≤ degrees.length)
    (hsum : degrees.sum ≤ p + 1) :
    ∀ d ∈ degrees, d < p := by
  intro d hd
  by_contra hdp
  have hpd : p ≤ d := Nat.le_of_not_gt hdp
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hd
  simp only [List.length_append, List.length_cons, List.sum_append,
    List.sum_cons] at hlength hsum
  have hbefore : before.length ≤ before.sum := by
    apply List.length_le_sum_of_one_le
    intro x hx
    exact hpositive x (by simp [hx])
  have hafter : after.length ≤ after.sum := by
    apply List.length_le_sum_of_one_le
    intro x hx
    exact hpositive x (by simp [hx])
  omega

end Struik
