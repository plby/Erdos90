import Towers.Group.Zassenhaus.TriangularGHLaw

open Towers.TCTex

/-!
# Binomial polynomials for repeated Hall blocks

This file isolates the one-variable polynomial arithmetic needed by a future
symbolic collector for powers of one collected Hall word.  A collection recipe
selects finitely many independent groups of repeated blocks.  A group of size
`k` contributes `Nat.choose q k` when the word is repeated `q` times.

The file is intentionally not imported by the existing collection proof.  It
is a standalone extension point for the missing repeated-block collector.
-/

namespace Towers
namespace TCTex

/--
The rational polynomial whose values on natural inputs are products of
ordinary binomial coefficients.
-/
noncomputable def natChooseProduct
    (indices : List ℕ) :
    Polynomial ℚ :=
  (indices.map natChoosePolynomial).prod

lemma nat_choose_product
    (indices : List ℕ)
    (q : ℕ) :
    (natChooseProduct indices).eval (q : ℚ) =
      ((indices.map fun k => (Nat.choose q k : ℤ)).prod : ℤ) := by
  induction indices with
  | nil =>
      simp [natChooseProduct]
  | cons k indices ih =>
      rw [show natChooseProduct (k :: indices) =
        natChoosePolynomial k * natChooseProduct indices by
          simp [natChooseProduct]]
      rw [Polynomial.eval_mul, eval_nat_choose, ih]
      simp

lemma nat_degree_choose
    (indices : List ℕ) :
    (natChooseProduct indices).natDegree ≤ indices.sum := by
  induction indices with
  | nil =>
      simp [natChooseProduct]
  | cons k indices ih =>
      change
        (natChoosePolynomial k * natChooseProduct indices).natDegree ≤
          k + indices.sum
      exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (degree_choose_polynomial k) ih)

/--
A product of binomial coefficients whose total binomial degree is bounded by
`degreeBound`.
-/
structure NBMono
    (degreeBound : ℕ) where
  indices :
    List ℕ
  indices_sum_le :
    indices.sum ≤ degreeBound

namespace NBMono

/-- Evaluate one bounded binomial monomial on a natural block count. -/
def eval
    {degreeBound : ℕ}
    (m : NBMono degreeBound)
    (q : ℕ) :
    ℤ :=
  (m.indices.map fun k => (Nat.choose q k : ℤ)).prod

/-- The rational polynomial represented by one bounded binomial monomial. -/
noncomputable def polynomial
    {degreeBound : ℕ}
    (m : NBMono degreeBound) :
    Polynomial ℚ :=
  natChooseProduct m.indices

lemma eval_polynomial
    {degreeBound : ℕ}
    (m : NBMono degreeBound)
    (q : ℕ) :
    m.polynomial.eval (q : ℚ) = (m.eval q : ℚ) := by
  exact nat_choose_product m.indices q

lemma nat_degree
    {degreeBound : ℕ}
    (m : NBMono degreeBound) :
    m.polynomial.natDegree ≤ degreeBound :=
  (nat_degree_choose m.indices).trans m.indices_sum_le

/--
Every bounded binomial monomial is an integer-valued polynomial of the
recorded degree.
-/
lemma integerValuedMost
    {degreeBound : ℕ}
    (m : NBMono degreeBound) :
    IVMost m.eval degreeBound := by
  exact ⟨m.polynomial, m.nat_degree, m.eval_polynomial⟩

end NBMono

namespace IVMost

lemma zero
    (degreeBound : ℕ) :
    IVMost
      (0 : ℕ → ℤ) degreeBound := by
  exact ⟨0, by simp, by simp⟩

lemma add
    {f g : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (hg : IVMost g degreeBound) :
    IVMost (f + g) degreeBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  rcases hg with ⟨Q, hQdegree, hQeval⟩
  refine ⟨P + Q, Polynomial.natDegree_add_le_of_degree_le hPdegree hQdegree, ?_⟩
  intro q
  simp [Polynomial.eval_add, hPeval q, hQeval q]

lemma smul
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (a : ℤ)
    (hf : IVMost f degreeBound) :
    IVMost (a • f) degreeBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  refine ⟨(a : ℚ) • P, (Polynomial.natDegree_smul_le (a : ℚ) P).trans hPdegree, ?_⟩
  intro q
  simp [Polynomial.eval_smul, hPeval q]

end IVMost

/--
The integer span of bounded one-variable binomial monomials.  This is the
natural output language for a repeated-block collector after its recipes have
been compressed by block support.
-/
def LinearCombinationMonomials
    (degreeBound : ℕ)
    (f : ℕ → ℤ) :
    Prop :=
  f ∈ Submodule.span ℤ
    (Set.range fun m : NBMono degreeBound => m.eval)

theorem most_combination_monomials
    {degreeBound : ℕ}
    {f : ℕ → ℤ}
    (hf : LinearCombinationMonomials degreeBound f) :
    IVMost f degreeBound := by
  refine Submodule.span_induction
    (p := fun g _ => IVMost g degreeBound)
    ?_ (IVMost.zero degreeBound) ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨m, rfl⟩
    exact m.integerValuedMost
  · intro g h _hg _hh hg hh
    exact hg.add hh
  · intro a g _hg hg
    exact hg.smul a

/--
One repeated-block collection recipe contributing to a coordinate of ordinary
weight `targetWeight`.  Selecting `k` independent groups of input blocks costs
at least `inputWeight * k` ordinary weight.
-/
structure WBMono
    (inputWeight targetWeight : ℕ) where
  indices :
    List ℕ
  indices_pos :
    ∀ k ∈ indices, 0 < k
  weighted_degree_le :
    inputWeight * indices.sum ≤ targetWeight

namespace WBMono

/-- Evaluate a weighted repeated-block recipe on a natural block count. -/
def eval
    {inputWeight targetWeight : ℕ}
    (m : WBMono inputWeight targetWeight)
    (q : ℕ) :
    ℤ :=
  (m.indices.map fun k => (Nat.choose q k : ℤ)).prod

/--
A positive input weight turns the weighted recipe inequality into the degree
bound needed by Claim 5.
-/
lemma indices_sum_div
    {inputWeight targetWeight : ℕ}
    (m : WBMono inputWeight targetWeight)
    (hinputWeight : 0 < inputWeight) :
    m.indices.sum ≤ targetWeight / inputWeight := by
  rw [Nat.le_div_iff_mul_le hinputWeight]
  simpa [Nat.mul_comm] using m.weighted_degree_le

/-- Forget the weight proof after converting it to a binomial degree bound. -/
def natBinomialMonomial
    {inputWeight targetWeight : ℕ}
    (m : WBMono inputWeight targetWeight)
    (hinputWeight : 0 < inputWeight) :
    NBMono (targetWeight / inputWeight) where
  indices := m.indices
  indices_sum_le := m.indices_sum_div hinputWeight

lemma nat_binomial_monomial
    {inputWeight targetWeight : ℕ}
    (m : WBMono inputWeight targetWeight)
    (hinputWeight : 0 < inputWeight) :
    (m.natBinomialMonomial hinputWeight).eval = m.eval :=
  rfl

lemma integerValuedMost
    {inputWeight targetWeight : ℕ}
    (m : WBMono inputWeight targetWeight)
    (hinputWeight : 0 < inputWeight) :
    IVMost
      m.eval (targetWeight / inputWeight) := by
  simpa [m.nat_binomial_monomial hinputWeight] using
    (m.natBinomialMonomial hinputWeight).integerValuedMost

end WBMono

/--
The integer span of weighted repeated-block recipe monomials contributing to
one target weight.
-/
def CombinationBinomialMonomials
    (inputWeight targetWeight : ℕ)
    (f : ℕ → ℤ) :
    Prop :=
  f ∈ Submodule.span ℤ
    (Set.range fun m :
      WBMono inputWeight targetWeight => m.eval)

/--
Weighted repeated-block recipes automa give the integer-valued
polynomial and degree bound required by Claim 5.
-/
theorem valued_most_combination
    {inputWeight targetWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      CombinationBinomialMonomials
        inputWeight targetWeight f) :
    IVMost
      f (targetWeight / inputWeight) := by
  refine Submodule.span_induction
    (p := fun g _ =>
      IVMost
        g (targetWeight / inputWeight))
    ?_ (IVMost.zero _) ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨m, rfl⟩
    exact m.integerValuedMost hinputWeight
  · intro g h _hg _hh hg hh
    exact hg.add hh
  · intro a g _hg hg
    exact hg.smul a

end TCTex
end Towers
