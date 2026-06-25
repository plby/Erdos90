import Towers.Group.NilpotentProducts.PrimeBinomialCongruences
import Towers.Group.NilpotentProducts.TwoSidedWords

namespace Struik

open Towers Edmonton

/-- The raw word identity to which Hall collection is applied in the proof
of equation (56). It is not the collected congruence (56). -/
theorem rawRightIdentity
    {G : Type*} [Group G] (b a : G) (p : ℕ) :
    evalFormalWord
        (fun | false => b | true => a)
        (twoSidedWord 1 p) =
      hallCommutator b (a ^ p) := by
  simpa using eval_sided_word b a 1 p

/-- The symmetric raw word identity used before deriving equation (58). -/
theorem rawLeftIdentity
    {G : Type*} [Group G] (b a : G) (p : ℕ) :
    evalFormalWord
        (fun | false => b | true => a)
        (twoSidedWord p 1) =
      hallCommutator (b ^ p) a := by
  simpa using eval_sided_word b a p 1

/-- The exceptional `p`-fold `a`-chain occurs exactly once in the raw word
used to derive (57). -/
theorem chainExceptionalCount
    {p : ℕ} (hp : 0 < p) :
    (twoSidedWord 1 p).count (aChain (p - 1)) = 1 := by
  rw [chain_sided_word]
  simp [Nat.sub_add_cancel hp]

/-- The exceptional `p`-fold `b`-chain occurs exactly once in the raw word
used to derive (58). -/
theorem bChainExceptional
    {p : ℕ} (hp : 0 < p) :
    (twoSidedWord p 1).count (bChain (p - 1)) = 1 := by
  rw [count_b_sided]
  simp [Nat.sub_add_cancel hp]

/-- Every proper nontrivial `a`-chain count in the raw word used for (57) is
divisible by the prime `p`. -/
theorem chain_intermediate_dvd
    {p α : ℕ} (hp : p.Prime) (hα : 0 < α) (hαp : α < p) :
    p ∣ (twoSidedWord 1 p).count (aChain (α - 1)) := by
  rw [chain_sided_word]
  simp only [one_mul, Nat.sub_add_cancel hα]
  exact hp.dvd_choose_self hα.ne' hαp

/-- Every proper nontrivial `b`-chain count in the raw word used for (58) is
divisible by the prime `p`. -/
theorem b_chain_dvd
    {p β : ℕ} (hp : p.Prime) (hβ : 0 < β) (hβp : β < p) :
    p ∣ (twoSidedWord p 1).count (bChain (β - 1)) := by
  rw [count_b_sided]
  simp only [one_mul, Nat.sub_add_cancel hβ]
  exact hp.dvd_choose_self hβ.ne' hβp

/-- If `a^(p^α)=1`, the entire raw correction word evaluates to one.

Equation (67) additionally isolates the exceptional collected commutator and
its lower-weight correction, which this theorem does not do. -/
theorem raw_correction_pow
    {G : Type*} [Group G] (b a : G) (p α : ℕ)
    (ha : a ^ (p ^ α) = 1) :
    evalFormalWord
        (fun | false => b | true => a)
        (twoSidedWord 1 (p ^ α)) = 1 := by
  rw [rawRightIdentity, ha]
  simp [hallCommutator]

/-- The corresponding raw-word identity for the exponent `p^(α+1)`.
This does not isolate the factors appearing in equation (68). -/
theorem raw_succ_pow
    {G : Type*} [Group G] (b a : G) (p α : ℕ)
    (ha : a ^ (p ^ (α + 1)) = 1) :
    evalFormalWord
        (fun | false => b | true => a)
        (twoSidedWord 1 (p ^ (α + 1))) = 1 := by
  rw [rawRightIdentity, ha]
  simp [hallCommutator]

/-- The first two replacement coordinates, equation (60). -/
def replacementCoordinate (γ δ : ℤ) : ℤ :=
  γ + δ

theorem unambiguous
    {m γ γ' δ δ' : ℤ}
    (hγ : γ ≡ γ' [ZMOD m])
    (hδ : δ ≡ δ' [ZMOD m]) :
    replacementCoordinate γ δ ≡ replacementCoordinate γ' δ' [ZMOD m] :=
  hγ.add hδ

/-- The arithmetically delicate part of equation (61). The remaining
correction terms in Struik's formula carry an explicit factor `p`. -/
def exceptionalReplacementCoordinate
    (p : ℕ) (γ₃ δ₃ γ₂ δ₁ correction : ℤ) : ℤ :=
  γ₃ + δ₃ + form p γ₂ δ₁ + p * correction

/-- The encoded part of equation (61) is well-defined modulo `p^(α+1)` if
the abstract bracketed correction is already well-defined modulo `p^α`.
This is a conditional congruence helper, not the paper's complete
unambiguity argument for equation (61). -/
theorem coordinate_mod_correction
    {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    {γ₃ γ₃' δ₃ δ₃' γ₂ γ₂' δ₁ δ₁' correction correction' : ℤ}
    (hγ₃ : γ₃ ≡ γ₃' [ZMOD (p ^ (α + 1) : ℕ)])
    (hδ₃ : δ₃ ≡ δ₃' [ZMOD (p ^ (α + 1) : ℕ)])
    (hγ₂ : γ₂ ≡ γ₂' [ZMOD (p ^ α : ℕ)])
    (hδ₁ : δ₁ ≡ δ₁' [ZMOD (p ^ α : ℕ)])
    (hcorrection :
      correction ≡ correction' [ZMOD (p ^ α : ℕ)]) :
    exceptionalReplacementCoordinate p γ₃ δ₃ γ₂ δ₁ correction ≡
      exceptionalReplacementCoordinate p γ₃' δ₃' γ₂' δ₁' correction'
        [ZMOD (p ^ (α + 1) : ℕ)] := by
  have hcore := prime_congruence_form hp hα hγ₂ hδ₁
  have hscaled :
      (p : ℤ) * correction ≡ p * correction'
        [ZMOD (p ^ (α + 1) : ℕ)] := by
    have h := hcorrection.mul_left' (c := (p : ℤ))
    simpa [Nat.pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  exact ((hγ₃.add hδ₃).add hcore).add hscaled

/-- The low-degree binomial factors in equations (62)--(64) are
well-defined at the full modulus `p^α`. -/
theorem low_degree_unambiguous
    {p α k : ℕ} (hp : p.Prime) (hk : k < p)
    {A C : ℤ} (hAC : A ≡ C [ZMOD (p ^ α : ℕ)]) :
    Ring.choose A k ≡ Ring.choose C k [ZMOD (p ^ α : ℕ)] :=
  choose_mod_pow hp hk hAC

/-- The exceptional degree-`p` factors in equations (63)--(64) are
well-defined at the reduced modulus prescribed by equation (69). -/
theorem exceptionalFactor_unambiguous
    {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    {A C : ℤ} (hAC : A ≡ C [ZMOD (p ^ α : ℕ)]) :
    Ring.choose A p ≡ Ring.choose C p
      [ZMOD (p ^ (α - 1) : ℕ)] :=
  choose_mod_power hp hα hAC

end Struik
