import Towers.Group.NilpotentProducts.PrimeBinomialCongruences

open scoped BigOperators

namespace Struik

/-- The contribution to the left-normed `a`-chain while `a^d` is
collected, with the generator `b` stored separately as the zeroth term. -/
noncomputable def leftChainContribution
    (s : ℕ) (c₂ d₁ : ℤ) (c' : ℕ → ℤ) : ℤ :=
  c₂ * Ring.choose d₁ s +
    ∑ t ∈ Finset.Ioo 0 s, c' t * Ring.choose d₁ (s - t)

/-- The expression on the right side of (49), with `c₂` representing
Struik's zeroth chain term `u₀' = b`.

Defining this expression does not prove that it is the corresponding group
multiplication coordinate. -/
noncomputable def leftChainExponent
    (s : ℕ) (c₂ d₁ : ℤ) (c' d' : ℕ → ℤ) : ℤ :=
  c' s + d' s + leftChainContribution s c₂ d₁ c'

theorem left_chain_formula
    (s : ℕ) (c₂ d₁ : ℤ) (c' d' : ℕ → ℤ) :
    leftChainExponent s c₂ d₁ c' d' =
      c' s + d' s +
        ∑ t ∈ Finset.Ioo 0 s,
          c' t * Ring.choose d₁ (s - t) +
        c₂ * Ring.choose d₁ s := by
  simp only [leftChainExponent, leftChainContribution]
  ring

/-- The exponent present on the `t`th right-normed `b`-chain after
collecting `a^d₁`, as used immediately before equation (51). -/
noncomputable def chainIntermediateExponent
    (t : ℕ) (c₂ d₁ : ℤ) (c'' : ℕ → ℤ) : ℤ :=
  c'' t + d₁ * Ring.choose c₂ t

/-- The expression on the right side of (51). -/
noncomputable def rightChainExponent
    (s : ℕ) (c₂ d₁ d₂ : ℤ) (c'' d'' : ℕ → ℤ) : ℤ :=
  c'' s + d'' s +
    ∑ t ∈ Finset.Ioo 0 s,
      chainIntermediateExponent t c₂ d₁ c'' *
        Ring.choose d₂ (s - t) +
    d₁ * Ring.choose c₂ s

theorem chain_exponent_formula
    (s : ℕ) (c₂ d₁ d₂ : ℤ) (c'' d'' : ℕ → ℤ) :
    rightChainExponent s c₂ d₁ d₂ c'' d'' =
      c'' s + d'' s +
        ∑ t ∈ Finset.Ioo 0 s,
          (c'' t + d₁ * Ring.choose c₂ t) *
            Ring.choose d₂ (s - t) +
        d₁ * Ring.choose c₂ s :=
  rfl

/-- The specialization of the encoded (49) expression at index `p`.
This is an algebraic specialization, not Corollary 1 itself. -/
theorem left_chain_exponent
    (p : ℕ) (c₂ d₁ : ℤ) (c' d' : ℕ → ℤ) :
    leftChainExponent p c₂ d₁ c' d' =
      c' p + d' p +
        ∑ t ∈ Finset.Ioo 0 p,
          c' t * Ring.choose d₁ (p - t) +
        c₂ * Ring.choose d₁ p :=
  left_chain_formula p c₂ d₁ c' d'

/-- The specialization of the encoded (51) expression at index `p`.
This is an algebraic specialization, not Corollary 1 itself. -/
theorem chain_exponent_prime
    (p : ℕ) (c₂ d₁ d₂ : ℤ) (c'' d'' : ℕ → ℤ) :
    rightChainExponent p c₂ d₁ d₂ c'' d'' =
      c'' p + d'' p +
        ∑ t ∈ Finset.Ioo 0 p,
          (c'' t + d₁ * Ring.choose c₂ t) *
            Ring.choose d₂ (p - t) +
        d₁ * Ring.choose c₂ p :=
  chain_exponent_formula p c₂ d₁ d₂ c'' d''

/-- The index-one simplification of the encoded (49) expression.
The group-coordinate identification required for (55) is separate. -/
theorem left_chain_one
    (c₂ d₁ : ℤ) (c' d' : ℕ → ℤ) :
    leftChainExponent 1 c₂ d₁ c' d' =
      c' 1 + d' 1 + c₂ * d₁ := by
  have hsum :
      ∑ t ∈ Finset.Ioo 0 1,
        c' t * Ring.choose d₁ (1 - t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have ht' := Finset.mem_Ioo.mp ht
    omega
  simp [leftChainExponent, leftChainContribution, hsum]

end Struik
