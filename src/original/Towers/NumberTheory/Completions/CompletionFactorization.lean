import Mathlib


/-!
# Milne, Chapter 8, Propositions 8.1 and 8.2: algebraic core

After passing to the completion, the minimal polynomial of a primitive
element factors into distinct monic irreducibles.  The corresponding simple
algebra is the product of the quotient fields defined by those factors.  This
is the Chinese-remainder step in Milne's construction of the completions of a
finite separable extension.
-/

namespace Towers.NumberTheory.Milne

open Function Polynomial

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

omit [Fintype ι] in
/-- Distinct monic irreducible polynomials over a field are pairwise coprime. -/
theorem pairwise_monic_irreducible
    (g : ι → K[X]) (hmonic : ∀ i, (g i).Monic)
    (hirr : ∀ i, Irreducible (g i)) (hinj : Injective g) :
    Pairwise (IsCoprime on g) := by
  intro i j hij
  rcases (hirr i).isCoprime_or_dvd (g j) with hcoprime | hdvd
  · exact hcoprime
  · exact (hij (hinj (eq_of_monic_of_associated (hmonic i) (hmonic j)
      ((hirr i).associated_of_dvd (hirr j) hdvd)))).elim

/-- The Chinese-remainder decomposition underlying Milne's Proposition 8.2.

If `f = ∏ i, g i` is a factorization into distinct monic irreducibles over
the completed base field, then adjoining a root of `f` decomposes as the
product of the fields obtained by adjoining one root of each `g i`.
-/
def polynomialPiFactors
    (g : ι → K[X]) (hmonic : ∀ i, (g i).Monic)
    (hirr : ∀ i, Irreducible (g i)) (hinj : Injective g) :
    K[X] ⧸ Ideal.span { ∏ i, g i } ≃+* (∀ i, K[X] ⧸ Ideal.span {g i}) := by
  let I : ι → Ideal K[X] := fun i ↦ Ideal.span {g i}
  have hpoly : Pairwise (IsCoprime on g) :=
    pairwise_monic_irreducible g hmonic hirr hinj
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff (g i) (g j)).2 (hpoly hij)
  exact (Ideal.quotEquivOfEq (Ideal.iInf_span_singleton hpoly).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient I hI)

@[simp]
theorem pi_factors_mk
    (g : ι → K[X]) (hmonic : ∀ i, (g i).Monic)
    (hirr : ∀ i, Irreducible (g i)) (hinj : Injective g) (p : K[X]) (i : ι) :
    polynomialPiFactors g hmonic hirr hinj
        (Ideal.Quotient.mk _ p) i = Ideal.Quotient.mk _ p :=
  rfl

end

end Towers.NumberTheory.Milne
