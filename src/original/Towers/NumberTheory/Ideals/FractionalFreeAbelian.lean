import Mathlib

/-!
# Milne, Algebraic Number Theory, Theorem 3.20

The multiplicative group of nonzero fractional ideals of a Dedekind domain is the free
abelian group on its nonzero prime ideals. Mathlib contains the existence and uniqueness
of the prime-exponent factorization; here we package those results as a group isomorphism.
-/

namespace Towers.NumberTheory.Milne

open scoped nonZeroDivisors

open IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private noncomputable def fractionalIdealExponents
    (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mk
    ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K))).toFinset)
    (fun v => FractionalIdeal.count K v (I : FractionalIdeal R⁰ K))
    (by
      intro v
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq])

omit [IsDomain R] in
private theorem fractional_ideal_exponents
    (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    fractionalIdealExponents R K I v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := rfl

private noncomputable def fractionalExponents
    (e : HeightOneSpectrum R →₀ ℤ) : FractionalIdeal R⁰ K :=
  e.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n

omit [IsDomain R] in
private theorem fractional_exponents_ne
    (e : HeightOneSpectrum R →₀ ℤ) : fractionalExponents R K e ≠ 0 := by
  classical
  rw [fractionalExponents, Finsupp.prod]
  exact (Finset.prod_ne_zero_iff.mpr fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

omit [IsDomain R] in
private theorem fractional_exponents_add
    (e f : HeightOneSpectrum R →₀ ℤ) :
    fractionalExponents R K (e + f) =
      fractionalExponents R K e * fractionalExponents R K f := by
  classical
  exact Finsupp.prod_add_index
    (fun _ _ => zpow_zero _)
    (fun v _ m n => zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) m n)

/-- Theorem 3.20: the nonzero fractional ideals form the free abelian group on the
nonzero prime ideals. The source is the standard finitely supported exponent model of a
free abelian group. -/
noncomputable def fractionalIdealFactorization :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) ≃* (FractionalIdeal R⁰ K)ˣ where
  toFun e := Units.mk0
    (fractionalExponents R K e.toAdd)
    (fractional_exponents_ne R K e.toAdd)
  invFun I := Multiplicative.ofAdd (fractionalIdealExponents R K I)
  left_inv e := by
    apply Multiplicative.toAdd.injective
    apply Finsupp.ext
    intro v
    exact FractionalIdeal.count_finsuppProd K v e.toAdd
  right_inv I := by
    apply Units.ext
    change fractionalExponents R K (fractionalIdealExponents R K I) =
      (I : FractionalIdeal R⁰ K)
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
        (fractional_exponents_ne R K (fractionalIdealExponents R K I)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero I)]
    apply finprod_congr
    intro v
    rw [fractionalExponents, FractionalIdeal.count_finsuppProd,
      fractional_ideal_exponents]
  map_mul' e f := by
    apply Units.ext
    exact fractional_exponents_add R K e.toAdd f.toAdd

omit [IsDomain R] in
/-- A basis vector of the free abelian group is sent to the corresponding power of its
prime fractional ideal. -/
theorem fractional_ideal_single
    (v : HeightOneSpectrum R) (n : ℤ) :
    ((fractionalIdealFactorization R K
        (Multiplicative.ofAdd (Finsupp.single v n))) : FractionalIdeal R⁰ K) =
      (v.asIdeal : FractionalIdeal R⁰ K) ^ n := by
  change fractionalExponents R K (Finsupp.single v n) = _
  rw [fractionalExponents]
  simp

end Towers.NumberTheory.Milne
