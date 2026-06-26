import Towers.ClassField.LubinTate.TorsionSeries

/-!
# Class Field Theory, Chapter I, Remark 3.1

For a polynomial Lubin--Tate series of degree `q`, its `n`-fold
compositional iterate is monic of degree `q^n`.  Together with the linear
coefficient calculation in `TorsionSeries`, this formalizes the displayed
shape `f^(n)(T) = pi^n T + ... + T^(q^n)` in Remark 3.1.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial

/-- The degree of an `n`-fold compositional polynomial iterate applied to
`X` is the `n`th power of the original degree. -/
theorem nat_iterate_x
    {R : Type*} [CommSemiring R] [Nontrivial R] [NoZeroDivisors R]
    (f : R[X]) (n : ℕ) :
    (f.comp^[n] Polynomial.X).natDegree = f.natDegree ^ n := by
  rw [Polynomial.natDegree_iterate_comp, Polynomial.natDegree_X, mul_one]

/-- Iterating composition of a positive-degree monic polynomial preserves
monicity. -/
theorem monic_iterate_x
    {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    (hf : f.Monic) (hdeg : f.natDegree ≠ 0) (n : ℕ) :
    (f.comp^[n] Polynomial.X).Monic := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      apply hf.comp ih
      rw [nat_iterate_x]
      exact pow_ne_zero n hdeg

/-- The coefficient of the top-degree term of a monic compositional iterate
is one. -/
theorem coeff_iterate_x
    {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    (hf : f.Monic) (hdeg : f.natDegree ≠ 0) (n : ℕ) :
    (f.comp^[n] Polynomial.X).coeff (f.natDegree ^ n) = 1 := by
  have hmonic := monic_iterate_x hf hdeg n
  rw [← nat_iterate_x f n]
  exact hmonic.coeff_natDegree

/-- Remark 3.1's source-facing degree and leading-coefficient assertion for
a monic Lubin--Tate polynomial of degree `q`. -/
theorem iterate_leading_coeff
    {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {q : ℕ}
    (hf : f.Monic) (hq : f.natDegree = q) (hq0 : q ≠ 0) (n : ℕ) :
    (f.comp^[n] Polynomial.X).natDegree = q ^ n ∧
      (f.comp^[n] Polynomial.X).coeff (q ^ n) = 1 := by
  subst q
  exact ⟨nat_iterate_x f n,
    coeff_iterate_x hf hq0 n⟩

end

end Towers.CField.LTate
