import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.3

Evaluating a polynomial with coefficients in the base ring at integral elements again gives an
integral element.
-/

namespace Towers.NumberTheory.Milne

/-- A multivariable polynomial in integral elements is integral. -/
theorem MvPolynomial.isIntegral_eval₂
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (g : MvPolynomial ι A) (x : ι → B) (hx : ∀ i, IsIntegral A (x i)) :
    IsIntegral A (MvPolynomial.eval₂ (algebraMap A B) x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using (isIntegral_algebraMap : IsIntegral A (algebraMap A B a))
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (hx i)

/-- If `x i` are roots of one monic polynomial over `A`, then every polynomial expression in the
`x i` with coefficients in `A` is integral over `A`. This is Proposition 2.3. -/
theorem isIntegral_eval₂_of_roots_of_monic
    {A Ω ι : Type*} [CommRing A] [Field Ω] [Algebra A Ω]
    (f : Polynomial A) (hf : f.Monic) (x : ι → Ω)
    (hx : ∀ i, Polynomial.eval₂ (algebraMap A Ω) (x i) f = 0)
    (g : MvPolynomial ι A) :
    IsIntegral A (MvPolynomial.eval₂ (algebraMap A Ω) x g) :=
  MvPolynomial.isIntegral_eval₂ g x fun i ↦ ⟨f, hf, hx i⟩

end Towers.NumberTheory.Milne
