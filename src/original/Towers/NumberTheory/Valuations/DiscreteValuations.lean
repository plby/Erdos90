import Mathlib

/-!
# Milne, Algebraic Number Theory, Examples 3.26 and Proposition 3.27

We record the strict-inequality rule for nonarchimedean valuations and the fact that the
valuation subring of a nontrivial discrete valuation is a discrete valuation ring. A
uniformizer generates its maximal ideal.
-/

namespace Towers.NumberTheory.Milne

open scoped nonZeroDivisors

open IsDedekindDomain
open UniqueFactorizationMonoid

/-- Equation (9), in Mathlib's multiplicative convention: the value of a finite sum is at
most the maximum of the values of its summands. -/
theorem valuation_finset_sup
    {R Γ₀ ι : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (s : Finset ι) (f : ι → R) :
    v (∑ i ∈ s, f i) ≤ s.sup fun i ↦ v (f i) := by
  apply v.map_sum_le
  intro i hi
  exact Finset.le_sup (f := fun i ↦ v (f i)) hi

/-- A root of unity has valuation one, equivalently additive order zero. -/
theorem valuation_one_pow
    {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) {ζ : R} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    v ζ = 1 := by
  apply (pow_eq_one_iff_left hn).mp
  rw [← v.map_pow, hζ, v.map_one]

/-- Negation does not change a valuation, the observation used in the strict-inequality
argument following Example 3.26. -/
theorem valuation_neg_eq
    {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x : R) :
    v (-x) = v x := by
  exact v.map_neg x

/-- The property following Example 3.26: when the two summands have distinct valuation,
the valuation of their sum is the larger value in Mathlib's multiplicative convention. -/
theorem valuation_add
    {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) {x y : R} (h : v x < v y) :
    v (x + y) = v y := by
  exact v.map_add_eq_of_lt_right h

/-- The observation preceding Proposition 3.53: a finite sum with a unique term of minimum
additive order cannot vanish. In the multiplicative convention, that term has uniquely maximal
valuation. -/
theorem unique_max_valuation
    {R Γ₀ ι : Type*} [DivisionRing R] [LinearOrderedCommMonoidWithZero Γ₀]
    [Nontrivial Γ₀] [DecidableEq ι]
    (v : Valuation R Γ₀) (s : Finset ι) (f : ι → R) (j : ι)
    (hj : j ∈ s) (hf : ∀ i ∈ s \ {j}, v (f i) < v (f j)) (hj0 : f j ≠ 0) :
    ∑ i ∈ s, f i ≠ 0 := by
  intro hzero
  have hval := v.map_sum_eq_of_lt hj hf
  rw [hzero, v.map_zero] at hval
  exact hj0 (v.zero_iff.mp hval.symm)

/-- Example 3.26(b): a prime element of a principal ideal domain determines a nonzero
prime ideal, hence a point of the height-one spectrum. -/
noncomputable def principalHeightSpectrum
    (A : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {π : A} (hπ : Prime π) : HeightOneSpectrum A :=
  ⟨Ideal.span {π},
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ,
    fun h ↦ hπ.ne_zero ((Ideal.span_singleton_eq_bot).mp h)⟩

/-- In the normalized valuation at the prime element `π`, the element `π` has additive
order one (and therefore value `exp (-1)` in Mathlib's multiplicative convention). -/
theorem principal_valuation_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {π : A} (hπ : Prime π) :
    (principalHeightSpectrum A hπ).intValuation π = WithZero.exp (-1 : ℤ) := by
  exact (principalHeightSpectrum A hπ).intValuation_singleton hπ.ne_zero rfl

/-- Example 3.26(c): a nonzero prime of a Dedekind domain defines a normalized
multiplicative valuation on its fraction field. Its values are written as `exp (-n)` where
Milne's additive convention writes `n`. -/
noncomputable def dedekindPrimeValuation
    (A K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (P : HeightOneSpectrum A) : Valuation K (WithZero (Multiplicative ℤ)) :=
  P.valuation K

/-- The Dedekind-prime valuation is normalized: every value in `ℤᵐ⁰` occurs. -/
theorem dedekind_valuation_surjective
    (A K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (P : HeightOneSpectrum A) :
    Function.Surjective (dedekindPrimeValuation A K P) := by
  exact P.valuation_surjective K

/-- Example 3.26(c), evaluated on a fraction: the value of `a / b` is the quotient of
the values of its numerator and denominator. -/
theorem dedekind_valuation_mk
    (A K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (P : HeightOneSpectrum A) (a : A) (b : nonZeroDivisors A) :
    dedekindPrimeValuation A K P (IsLocalization.mk' K a b) =
      P.intValuation a / P.intValuation b := by
  exact P.valuation_of_mk'

/-- A normalized prime valuation has a uniformizer, i.e. an element of additive order
one (value `exp (-1)` in Mathlib's multiplicative convention). -/
theorem dedekind_valuation_uniformizer
    (A K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (P : HeightOneSpectrum A) :
    ∃ π : K, dedekindPrimeValuation A K P π = WithZero.exp (-1 : ℤ) := by
  exact P.valuation_exists_uniformizer K

/-- Equation (13) preceding Proposition 3.53, in ideal-multiplicity form: restricting the
normalized valuation at `P` to the base multiplies the valuation at `p` by `e(P/p)`. -/
theorem emultiplicity_ramification_idx
    {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal] (a : A) (ha : a ≠ 0) :
    emultiplicity P.asIdeal (Ideal.span {algebraMap A B a}) =
      Ideal.ramificationIdx p.asIdeal P.asIdeal *
        emultiplicity p.asIdeal (Ideal.span {a}) := by
  have hspan : (Ideal.span {a} : Ideal A) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  have hmap : (Ideal.span {a}).map (algebraMap A B) =
      Ideal.span {algebraMap A B a} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hmap]
  exact Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hspan p.irreducible P.irreducible P.ne_bot

/-- Proposition 3.27: the valuation subring of a nontrivial valuation with cyclic value
group is a discrete valuation ring. -/
theorem valuationSubring_discrete
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [IsCyclic (MonoidWithZeroHom.valueGroup v)]
    [Nontrivial (MonoidWithZeroHom.valueGroup v)] :
    IsDiscreteValuationRing v.valuationSubring := by
  exact Valuation.valuationSubring_isDiscreteValuationRing v

/-- Proposition 3.27's description of the valuation ring. With Mathlib's multiplicative
ordering, additive order at least zero is the condition `v x ≤ 1`. -/
theorem valuation_subring_value
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (x : K) :
    x ∈ v.valuationSubring ↔ v x ≤ 1 := by
  exact v.mem_valuationSubring_iff x

/-- Proposition 3.27's description of the maximal ideal: it consists of the elements of
strictly positive additive order, equivalently those whose multiplicative value is below one. -/
theorem valuation_subring_maximal
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (x : v.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v x < 1 := by
  exact v.mem_maximalIdeal_iff

/-- The final assertion of Proposition 3.27: a uniformizer generates the maximal ideal of
the valuation subring. -/
theorem valuation_subring_uniformizer
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [IsCyclic (MonoidWithZeroHom.valueGroup v)]
    [Nontrivial (MonoidWithZeroHom.valueGroup v)]
    {π : v.valuationSubring} (hπ : v.IsUniformizer (π : K)) :
    IsLocalRing.maximalIdeal v.valuationSubring = Ideal.span {π} := by
  exact hπ.is_generator

end Towers.NumberTheory.Milne
