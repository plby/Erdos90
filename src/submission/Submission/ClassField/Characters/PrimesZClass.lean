import Submission.NumberTheory.Galois.CyclotomicQuadraticFrobenius
import Submission.NumberTheory.Density.SplittingPrimeDensity
import Submission.ClassField.Characters.HasDirichletDensity

/-!
# Chapter V, Section 2, Theorem 2.2 and Corollary 2.3

This file states the literal Dirichlet-density claims using the existing
`HasDirichletDensity` predicate.  It proves the bridges between the `ZMod`,
natural-congruence, and integral-ideal cyclotomic-splitting forms, including
invariance of density under finite changes.  The remaining adapter to the
existing `HeightOneSpectrum (𝓞 ℚ)` splitting API is stated explicitly.

No infinitude theorem is presented as a density theorem.  The remaining
analytic input is the asymptotic for the reciprocal-prime sum in one reduced
residue class.  Mathlib's `PrimesInAP` currently proves infinitude from a
lower bound for a von-Mangoldt series, but does not prove this normalized
limit.
-/

namespace Submission.CField.Charac

open IsDedekindDomain NumberField Set Filter
open scoped Topology

noncomputable section

/-- Natural numbers in the residue class `a` modulo `m`.  Primality is
already imposed internally by `HasDirichletDensity`. -/
def primesZClass (m : ℕ) (a : ZMod m) : Set ℕ :=
  {p | (p : ZMod m) = a}

/-- Natural numbers congruent to `a` modulo `m`. -/
def primesCongruenceClass (m a : ℕ) : Set ℕ :=
  {p | p ≡ a [MOD m]}

theorem primes_z_cast (m a : ℕ) :
    primesZClass m (a : ZMod m) =
      primesCongruenceClass m a := by
  ext p
  simp [primesZClass, primesCongruenceClass,
    ZMod.natCast_eq_natCast_iff]

/-- Literal statement of Theorem V.2.2 for one reduced residue class. -/
def DirichletDensityStatement
    (m : ℕ) [NeZero m] (a : ZMod m) : Prop :=
  IsUnit a ∧
    HasDirichletDensity (primesZClass m a)
      ((1 : ℝ) / Nat.totient m)

/-- Literal simultaneous form of Theorem V.2.2. -/
def AllDirichletStatement
    (m : ℕ) [NeZero m] : Prop :=
  ∀ a : ZMod m, IsUnit a →
    HasDirichletDensity (primesZClass m a)
      ((1 : ℝ) / Nat.totient m)

/-- The `ZMod` and natural-number formulations of the density assertion are
definitionally about the same set. -/
theorem zmod_nat_mod
    (m a : ℕ) [NeZero m] :
    HasDirichletDensity (primesZClass m (a : ZMod m))
        ((1 : ℝ) / Nat.totient m) ↔
      HasDirichletDensity (primesCongruenceClass m a)
        ((1 : ℝ) / Nat.totient m) := by
  rw [primes_z_cast]

/-- Theorem 2.2 formally implies its `a = 1` density specialization. -/
theorem congruence_dirichlet_characters
    (m : ℕ) [NeZero m]
    (h : AllDirichletStatement m) :
    HasDirichletDensity (primesCongruenceClass m 1)
      ((1 : ℝ) / Nat.totient m) := by
  rw [← primes_z_cast m 1]
  simpa using h (1 : ZMod m) isUnit_one

/-- Two sets have the same prime elements up to finitely many exceptions.
This ignores composite elements, exactly as `HasDirichletDensity` does. -/
def DBFinite (S T : Set ℕ) : Prop :=
  ((S \ T) ∩ {p | p.Prime}).Finite ∧
    ((T \ S) ∩ {p | p.Prime}).Finite

theorem DBFinite.trans {S T U : Set ℕ}
    (hST : DBFinite S T) (hTU : DBFinite T U) :
    DBFinite S U := by
  constructor
  · apply (hST.1.union hTU.1).subset
    rintro p ⟨⟨hpS, hpU⟩, hp⟩
    by_cases hpT : p ∈ T
    · exact Or.inr ⟨⟨hpT, hpU⟩, hp⟩
    · exact Or.inl ⟨⟨hpS, hpT⟩, hp⟩
  · apply (hTU.2.union hST.2).subset
    rintro p ⟨⟨hpU, hpS⟩, hp⟩
    by_cases hpT : p ∈ T
    · exact Or.inr ⟨⟨hpT, hpS⟩, hp⟩
    · exact Or.inl ⟨⟨hpU, hpT⟩, hp⟩

/-- The integral-ideal formulation of complete splitting at the rational
prime `p`: in a Galois extension it is enough to exhibit one prime above
`(p)` with ramification index and inertia degree one. -/
def CyclotomicSplitsCompletely
    (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K),
    P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) ∧
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1

/-- Away from primes dividing the chosen cyclotomic level, the standard
inertia-degree computation gives the literal splitting criterion
`p ≡ 1 (mod m)`. -/
theorem splits_completely_dvd
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [hcycl : IsCyclotomicExtension {m} ℚ K]
    (p : ℕ) (hp : p.Prime) (hpm : ¬p ∣ m) :
    CyclotomicSplitsCompletely K p ↔ p ≡ 1 [MOD m] := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨P, hP, he, hf⟩
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    have hdegrees :=
      @Submission.NumberTheory.Milne.inertia_ramification_dvd
        K _ _ p m inferInstance inferInstance hcycl P inferInstance inferInstance hpm
    have hord : orderOf (p : ZMod m) = 1 := hdegrees.1.symm.trans hf
    have hzmod : (p : ZMod m) = 1 := orderOf_eq_one_iff.mp hord
    exact (ZMod.natCast_eq_natCast_iff p 1 m).mp (by simpa using hzmod)
  · intro hmod
    let q : Ideal ℤ := Ideal.span {(p : ℤ)}
    have hq0 : q ≠ ⊥ := by
      simpa [q, Ideal.span_singleton_eq_bot] using hp.ne_zero
    obtain ⟨P : Ideal (𝓞 K), hPprime, hPlies⟩ :=
      q.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K)
    have hPmem : P ∈ Ideal.primesOver q (𝓞 K) :=
      ⟨hPprime.isPrime, hPlies⟩
    letI : P.IsPrime := hPprime.isPrime
    letI : P.LiesOver q := hPlies
    have hdegrees :=
      @Submission.NumberTheory.Milne.inertia_ramification_dvd
        K _ _ p m inferInstance inferInstance hcycl P inferInstance inferInstance hpm
    have hzmod : (p : ZMod m) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff p 1 m).mpr hmod
    have hord : orderOf (p : ZMod m) = 1 := orderOf_eq_one_iff.mpr hzmod
    refine ⟨P, ?_, hdegrees.2, ?_⟩
    · simpa [q] using hPmem
    · exact hdegrees.1.trans hord

/-- Rational primes satisfying the integral-ideal splitting criterion. -/
def cyclotomicSplittingPrimes
    (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {p | CyclotomicSplitsCompletely K p}

/-- The integral-ideal cyclotomic splitting locus and the progression
`1 mod m` have the same prime elements outside the finite set of divisors of
`m`. -/
theorem differ_finitely_congruence
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [hcycl : IsCyclotomicExtension {m} ℚ K] :
    DBFinite (cyclotomicSplittingPrimes K)
      (primesCongruenceClass m 1) := by
  have hdiv : {p : ℕ | p ∣ m}.Finite := by
    apply m.divisors.finite_toSet.subset
    intro p hp
    exact Nat.mem_divisors.mpr ⟨hp, NeZero.ne m⟩
  constructor
  · apply hdiv.subset
    rintro p ⟨⟨hsplit, hnmod⟩, hp⟩
    by_contra hpm
    exact hnmod ((splits_completely_dvd
      m K p hp hpm).mp hsplit)
  · apply hdiv.subset
    rintro p ⟨⟨hmod, hnsplit⟩, hp⟩
    by_contra hpm
    exact hnsplit ((splits_completely_dvd
      m K p hp hpm).mpr hmod)

/-- Rational primes which split completely in a chosen number field. -/
def primesSplittingCompletely
    (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {p | ∃ hp : p.Prime,
    (Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩) ∈
      Submission.NumberTheory.Milne.splittingPrimes ℚ K}

/-- The precise algebraic bridge needed to turn the `a = 1` progression
statement into the cyclotomic splitting statement.  Equality would be too
strong for a nonminimal cyclotomic level: primes dividing the displayed
level are the finite exceptional set. -/
def SplittingCongruenceBridge
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] : Prop :=
  DBFinite (primesSplittingCompletely K)
    (primesCongruenceClass m 1)

/-- The remaining pointwise adapter between the existing
`HeightOneSpectrum (𝓞 ℚ)` splitting API and Mathlib's cyclotomic ideal API,
which is formulated over `ℤ`.  The two base rings are canonically equivalent,
but no theorem transporting `primesOver`, ramification indices, and inertia
degrees across that equivalence is currently exported. -/
def SplittingCriterionBridge
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ p : ℕ, p.Prime →
    (p ∈ primesSplittingCompletely K ↔
      p ∈ cyclotomicSplittingPrimes K)

theorem differ_finitely_criterion
    (K : Type*) [Field K] [NumberField K]
    (h : SplittingCriterionBridge K) :
    DBFinite (primesSplittingCompletely K)
      (cyclotomicSplittingPrimes K) := by
  constructor
  · have hempty :
        ((primesSplittingCompletely K \
            cyclotomicSplittingPrimes K) ∩ {p | p.Prime}) = ∅ := by
      ext p
      constructor
      · rintro ⟨⟨hp, hnp⟩, hpprime⟩
        exact (hnp ((h p hpprime).mp hp)).elim
      · simp
    rw [hempty]
    exact finite_empty
  · have hempty :
        ((cyclotomicSplittingPrimes K \
            primesSplittingCompletely K) ∩ {p | p.Prime}) = ∅ := by
      ext p
      constructor
      · rintro ⟨⟨hp, hnp⟩, hpprime⟩
        exact (hnp ((h p hpprime).mpr hp)).elim
      · simp
    rw [hempty]
    exact finite_empty

/-- The proved cyclotomic congruence criterion, together with only the
base-ring adapter above, supplies the exact set-level bridge needed for
Corollary V.2.3. -/
theorem splitting_congruence_criterion
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [hcycl : IsCyclotomicExtension {m} ℚ K]
    (h : SplittingCriterionBridge K) :
    SplittingCongruenceBridge m K :=
  (differ_finitely_criterion K h).trans
    (differ_finitely_congruence m K)

/-- The analytic invariance under finite modification needed when passing
from the congruence locus to the actual cyclotomic splitting locus. -/
def DirichletDensityModification : Prop :=
  ∀ (S T : Set ℕ) (delta : ℝ), DBFinite S T →
    (HasDirichletDensity S delta ↔ HasDirichletDensity T delta)

private def dirichletDensityNumerator (T : Set ℕ) (s : ℝ) : ℝ :=
  ∑' p : {p : ℕ // p ∈ T ∧ p.Prime}, 1 / (p.1 : ℝ) ^ s

private def dirichletDensityDenominator (s : ℝ) : ℝ :=
  Real.log (1 / (s - 1))

private theorem dirichlet_denominator_tendsto :
    Tendsto dirichletDensityDenominator (𝓝[>] 1) atTop := by
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun s : ℝ => s - (1 : ℝ)) 1 :=
        continuousAt_id.sub (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (1 : ℝ)) 1)
      simpa using hc.tendsto.mono_left
        (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 1 < s := hs
      exact sub_pos.mpr hs'
  unfold dirichletDensityDenominator
  have hinv : Tendsto (fun s : ℝ => 1 / (s - 1)) (𝓝[>] 1) atTop := by
    simpa only [one_div, Function.comp_apply] using
      (tendsto_inv_nhdsGT_zero.comp hsub)
  simpa only [Function.comp_apply] using Real.tendsto_log_atTop.comp hinv

private theorem dirichlet_numerator_indicator (T : Set ℕ) (s : ℝ) :
    dirichletDensityNumerator T s =
      ∑' p : ℕ, ({p | p ∈ T ∧ p.Prime}.indicator
        (fun p : ℕ => 1 / (p : ℝ) ^ s)) p := by
  simpa [dirichletDensityNumerator] using
    (tsum_subtype {p : ℕ | p ∈ T ∧ p.Prime}
      (fun p : ℕ => 1 / (p : ℝ) ^ s))

private theorem difference_tendsto_zero
    (S T : Set ℕ) (hST : DBFinite S T) :
    Tendsto (fun s =>
      dirichletDensityNumerator S s / dirichletDensityDenominator s -
        dirichletDensityNumerator T s / dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 0) := by
  let U : Set ℕ := ((S \ T) ∩ {p | p.Prime}) ∪
    ((T \ S) ∩ {p | p.Prime})
  have hU : U.Finite := hST.1.union hST.2
  let u : Finset ℕ := hU.toFinset
  let term (A : Set ℕ) (p : ℕ) (s : ℝ) : ℝ :=
    ({p | p ∈ A ∧ p.Prime}.indicator
      (fun q : ℕ => 1 / (q : ℝ) ^ s)) p
  have hcontinuous (p : ℕ) :
      Continuous (fun s : ℝ => term S p s - term T p s) := by
    by_cases hp : p.Prime
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hc : Continuous (fun s : ℝ => 1 / (p : ℝ) ^ s) := by
        simpa [one_div] using
          (Real.continuous_const_rpow hp0).inv₀
            (fun s => (Real.rpow_pos_of_pos (by positivity : 0 < (p : ℝ)) s).ne')
      by_cases hpS : p ∈ S <;> by_cases hpT : p ∈ T
      · simpa [term, hp, hpS, hpT] using hc.sub hc
      · simpa [term, hp, hpS, hpT] using hc
      · simpa [term, hp, hpS, hpT] using hc.neg
      · simpa [term, hp, hpS, hpT] using
          (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
    · simpa [term, hp] using
        (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  have hnum : Tendsto
      (fun s : ℝ => ∑ p ∈ u, (term S p s - term T p s))
      (𝓝[>] 1) (𝓝 (∑ p ∈ u, (term S p 1 - term T p 1))) := by
    exact ((continuous_finsetSum u fun p _ => hcontinuous p).tendsto 1).mono_left
      inf_le_left
  have hratio : Tendsto
      (fun s : ℝ =>
        (∑ p ∈ u, (term S p s - term T p s)) /
          dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 0) :=
    hnum.div_atTop dirichlet_denominator_tendsto
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := hs
  have hbase : Summable (fun p : ℕ => 1 / (p : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs1
  have hSsum : Summable (fun p : ℕ => term S p s) := hbase.indicator _
  have hTsum : Summable (fun p : ℕ => term T p s) := hbase.indicator _
  have hsupport (p : ℕ) (hp : p ∉ u) : term S p s - term T p s = 0 := by
    have hpU : p ∉ U := by simpa [u] using hp
    by_cases hpPrime : p.Prime
    · have hnST : p ∉ S \ T := fun h => hpU (Or.inl ⟨h, hpPrime⟩)
      have hnTS : p ∉ T \ S := fun h => hpU (Or.inr ⟨h, hpPrime⟩)
      have hmem : p ∈ S ↔ p ∈ T := by
        constructor
        · intro hpS
          by_contra hpT
          exact hnST ⟨hpS, hpT⟩
        · intro hpT
          by_contra hpS
          exact hnTS ⟨hpT, hpS⟩
      by_cases hpS : p ∈ S
      · have hpT : p ∈ T := hmem.mp hpS
        simp [term, hpS, hpT, hpPrime]
      · have hpT : p ∉ T := fun h => hpS (hmem.mpr h)
        simp [term, hpS, hpT, hpPrime]
    · simp [term, hpPrime]
  have htsum :
      dirichletDensityNumerator S s - dirichletDensityNumerator T s =
        ∑ p ∈ u, (term S p s - term T p s) := by
    rw [dirichlet_numerator_indicator,
      dirichlet_numerator_indicator]
    change (∑' p : ℕ, term S p s) - (∑' p : ℕ, term T p s) = _
    rw [← hSsum.tsum_sub hTsum, tsum_eq_sum hsupport]
  rw [← sub_div, htsum]

/-- Dirichlet density is unchanged by adding or removing finitely many
primes.  This proves the analytic transport step used in Corollary V.2.3. -/
theorem dirichlet_density_modification :
    DirichletDensityModification := by
  intro S T delta hST
  have hdiff := difference_tendsto_zero S T hST
  constructor
  · intro hS
    rw [HasDirichletDensity] at hS ⊢
    change Tendsto
      (fun s => dirichletDensityNumerator S s / dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 delta) at hS
    change Tendsto
      (fun s => dirichletDensityNumerator T s / dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 delta)
    simpa only [sub_sub_cancel, sub_zero] using hS.sub hdiff
  · intro hT
    rw [HasDirichletDensity] at hT ⊢
    change Tendsto
      (fun s => dirichletDensityNumerator T s / dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 delta) at hT
    change Tendsto
      (fun s => dirichletDensityNumerator S s / dirichletDensityDenominator s)
      (𝓝[>] 1) (𝓝 delta)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hT.add hdiff

/-- Thus Theorem V.2.2 already gives the claimed density for the
integral-ideal cyclotomic splitting locus, with no additional analytic
assumption. -/
theorem splitting_density_congruence
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [hcycl : IsCyclotomicExtension {m} ℚ K]
    (hcong : HasDirichletDensity (primesCongruenceClass m 1)
      ((1 : ℝ) / Nat.totient m)) :
    HasDirichletDensity (cyclotomicSplittingPrimes K)
      ((1 : ℝ) / Nat.totient m) := by
  exact (dirichlet_density_modification _ _ _
    (differ_finitely_congruence m K)).2 hcong

/-- Once the standard cyclotomic splitting criterion is available in the
set-level form above, the congruence density statement transports exactly
to Corollary V.2.3. -/
theorem cyclotomic_density_bridge
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K]
    (hcong : HasDirichletDensity (primesCongruenceClass m 1)
      ((1 : ℝ) / Nat.totient m))
    (hbridge : SplittingCongruenceBridge m K) :
    (HasDirichletDensity (primesSplittingCompletely K)
          ((1 : ℝ) / Nat.totient m)) := by
  exact (dirichlet_density_modification _ _ _ hbridge).2 hcong

/-- A version of the preceding implication that exposes only the exact
missing base-ring compatibility theorem, while discharging the cyclotomic
criterion and finite-modification analysis internally. -/
theorem cyclotomic_density_criterion
    (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K]
    [hcycl : IsCyclotomicExtension {m} ℚ K]
    (hcong : HasDirichletDensity (primesCongruenceClass m 1)
      ((1 : ℝ) / Nat.totient m))
    (hcriterion : SplittingCriterionBridge K) :
    (HasDirichletDensity (primesSplittingCompletely K)
          ((1 : ℝ) / Nat.totient m)) :=
  cyclotomic_density_bridge m K hcong
    (splitting_congruence_criterion m K hcriterion)

end

end Submission.CField.Charac
