import Mathlib.GroupTheory.GroupAction.Quotient
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.NumberTheory.Galois.FrobeniusElement
import Submission.NumberTheory.Density.PrimeIdealNatural


/-!
# Milne, Chapter 8, Theorem 8.31 and Corollary 8.32

This file records the exact finite-group density assertion occurring in the
Chebotarev density theorem and develops the elementary natural-density
consequences used immediately after it.

The analytic Chebotarev theorem itself is not currently available in Mathlib.
Accordingly, `ChebotarevDensityProperty` is the proposition that a Frobenius
class map satisfies Chebotarev; the results below prove its identity-class and
infinitude consequences from that stated hypothesis.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

section ChebotarevStatement

variable {G : Type*} [Group G] [Finite G]

/-- The prime ideals whose (possibly undefined, at ramified primes) Frobenius
class is `C`. -/
def primesFrobeniusClass
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (C : ConjClasses G) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | frobeniusClass p = some C}

/-- The density assertion of Milne's Theorem 8.31 for a Frobenius-class map.

For the arithmetic Frobenius map of a finite Galois extension, Chebotarev says
that this proposition holds.  Using `Option` makes the map total: ramified
primes, where the Frobenius conjugacy class is not defined, are sent to
`none`.
-/
def ChebotarevDensityProperty
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)) : Prop :=
  ∀ C : ConjClasses G,
    PNDensit K
      (primesFrobeniusClass K frobeniusClass C)
      ((C.carrier.ncard : ℝ) / Nat.card G)

omit [Finite G] in
private theorem conjugacy_class_carrier :
    (ConjClasses.mk (1 : G)).carrier = ({1} : Set G) := by
  ext sigma
  simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_singleton_iff]
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_one_left

omit [Finite G] in
/-- The identity conjugacy class has one element. -/
@[simp]
theorem conjugacy_class_ncard :
    (ConjClasses.mk (1 : G)).carrier.ncard = 1 := by
  rw [conjugacy_class_carrier]
  simp

omit [Finite G] in
/-- The completely-split (identity Frobenius) part of Chebotarev has density
`1 / |G|`.  This is the density calculation in Corollary 8.32. -/
theorem identity_frobenius_density
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / Nat.card G) := by
  simpa using hcheb (ConjClasses.mk 1)

/-- In particular, Chebotarev supplies infinitely many primes with trivial
Frobenius class. -/
theorem infinite_identity_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    (primesFrobeniusClass K frobeniusClass
      (ConjClasses.mk (1 : G))).Infinite := by
  apply Set.Infinite.prime_ideal_densi K
    (identity_frobenius_density K hcheb)
  exact one_div_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)

omit [NumberField K] [Finite G] in
/-- Distinct Frobenius conjugacy classes define disjoint sets of primes. -/
theorem disjoint_primes_frobenius
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    {C D : ConjClasses G} (hCD : C ≠ D) :
    Disjoint (primesFrobeniusClass K frobeniusClass C)
      (primesFrobeniusClass K frobeniusClass D) := by
  apply Set.disjoint_left.2
  intro p hpC hpD
  apply hCD
  exact Option.some.inj (hpC.symm.trans hpD)

/-- Milne, Remark 8.33, in its qualitative form: there is one norm bound
below which every Frobenius conjugacy class that occurs at all already
occurs.

The effective Chebotarev theorem supplies a computable bound in terms of
arithmetic invariants.  The bare existence asserted here is the finite-group
core of that conclusion: choose one prime for each occurring conjugacy class
and take the maximum of their norms.  Since a permutation cycle type is
constant on conjugacy classes, this is stronger than the stated cycle-type
conclusion. -/
theorem realizing_frobenius_classes
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)) :
    ∃ B : ℕ, ∀ C : ConjClasses G,
      (∃ p, frobeniusClass p = some C) ↔
        ∃ p, p.asIdeal.absNorm ≤ B ∧ frobeniusClass p = some C := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let boundOf : ConjClasses G → ℕ := fun C ↦
    if h : ∃ p, frobeniusClass p = some C then
      (Classical.choose h).asIdeal.absNorm
    else 0
  let B := Finset.univ.sup boundOf
  refine ⟨B, fun C ↦ ?_⟩
  constructor
  · intro hC
    let p : HeightOneSpectrum (𝓞 K) := Classical.choose hC
    have hp : frobeniusClass p = some C := Classical.choose_spec hC
    have hle : boundOf C ≤ B :=
      Finset.le_sup (Finset.mem_univ C)
    have hbound : p.asIdeal.absNorm ≤ B := by
      simpa only [boundOf, dif_pos hC] using hle
    exact ⟨p, hbound, hp⟩
  · rintro ⟨p, -, hp⟩
    exact ⟨p, hp⟩

/-- Contrapositive form of Remark 8.33: once all primes through the bound
have been checked, a missing Frobenius class can never occur. -/
theorem detecting_absent_classes
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)) :
    ∃ B : ℕ, ∀ C : ConjClasses G,
      (∀ p, p.asIdeal.absNorm ≤ B → frobeniusClass p ≠ some C) →
        ∀ p, frobeniusClass p ≠ some C := by
  obtain ⟨B, hB⟩ := realizing_frobenius_classes K frobeniusClass
  refine ⟨B, fun C hsmall p hp ↦ ?_⟩
  obtain ⟨q, hqbound, hq⟩ := (hB C).mp ⟨p, hp⟩
  exact hsmall q hqbound hq

omit [Finite G] in
/-- Chebotarev's density formula is elementary for a trivial group: there is
one conjugacy class, and every prime belongs to it. -/
theorem chebotarev_property_subsingleton [Subsingleton G]
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → ConjClasses G) :
    ChebotarevDensityProperty K (fun p ↦ some (frobeniusClass p)) := by
  have hclass (D : ConjClasses G) : D = ConjClasses.mk (1 : G) := by
    rcases ConjClasses.exists_rep D with ⟨g, hg⟩
    calc
      D = ConjClasses.mk g := hg.symm
      _ = ConjClasses.mk 1 := congrArg ConjClasses.mk (Subsingleton.elim _ _)
  intro C
  have hC : C = ConjClasses.mk (1 : G) := hclass C
  subst C
  have hset : primesFrobeniusClass K
      (fun p ↦ some (frobeniusClass p)) (ConjClasses.mk (1 : G)) =
        Set.univ := by
    ext p
    simp only [primesFrobeniusClass, Set.mem_setOf_eq, Option.some.injEq,
      Set.mem_univ, iff_true]
    exact hclass (frobeniusClass p)
  rw [hset]
  simpa using natural_density_univ K

omit [Finite G] in
/-- For a group of order two, the density of the nonidentity Frobenius class
is forced by the density of the identity class.  Thus quadratic Chebotarev
reduces to one of its two class-density assertions. -/
theorem nontrivial_frobenius_density
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → ConjClasses G)
    (hcard : Nat.card G = 2) {sigma : G} (hsigma : sigma ≠ 1)
    (hone : PNDensit K
      (primesFrobeniusClass K (fun p ↦ some (frobeniusClass p))
        (ConjClasses.mk (1 : G))) (1 / 2)) :
    PNDensit K
      (primesFrobeniusClass K (fun p ↦ some (frobeniusClass p))
        (ConjClasses.mk sigma)) (1 / 2) := by
  obtain ⟨tau, htau, hunique⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hcard
  have hnontrivial (g : G) (hg : g ≠ 1) : g = sigma :=
    (hunique g hg).trans (hunique sigma hsigma).symm
  have hclasses (C : ConjClasses G) :
      C = ConjClasses.mk (1 : G) ∨ C = ConjClasses.mk sigma := by
    rcases ConjClasses.exists_rep C with ⟨g, hg⟩
    by_cases hg1 : g = 1
    · exact Or.inl (hg.symm.trans (congrArg ConjClasses.mk hg1))
    · exact Or.inr (hg.symm.trans (congrArg ConjClasses.mk (hnontrivial g hg1)))
  have hclass_ne : ConjClasses.mk sigma ≠ ConjClasses.mk (1 : G) := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] at h
    exact hsigma h
  have hset :
      primesFrobeniusClass K (fun p ↦ some (frobeniusClass p))
          (ConjClasses.mk sigma) =
        (primesFrobeniusClass K (fun p ↦ some (frobeniusClass p))
          (ConjClasses.mk (1 : G)))ᶜ := by
    ext p
    simp only [primesFrobeniusClass, Set.mem_setOf_eq, Option.some.injEq,
      Set.mem_compl_iff]
    constructor
    · intro hp hpid
      exact hclass_ne (hp.symm.trans hpid)
    · intro hp
      rcases hclasses (frobeniusClass p) with hpid | hpsigma
      · exact (hp hpid).elim
      · exact hpsigma
  rw [hset]
  convert hone.compl K using 1 ; norm_num

end ChebotarevStatement

section AbelianChebotarev

variable {G : Type*} [CommGroup G] [Finite G]

omit [Finite G] in
private theorem conjugacy_carrier_comm (sigma : G) :
    (ConjClasses.mk sigma).carrier = ({sigma} : Set G) := by
  ext tau
  simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_singleton_iff]
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]

omit [Finite G] in
/-- In an abelian Galois group, each individual Frobenius element occurs with
density `1 / |G|`, as stated immediately after Theorem 8.31. -/
theorem abelian_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) (sigma : G) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma))
      (1 / Nat.card G) := by
  have hcard : (ConjClasses.mk sigma).carrier.ncard = 1 := by
    rw [conjugacy_carrier_comm]
    simp
  simpa [hcard] using hcheb (ConjClasses.mk sigma)

omit [Finite G] in
/-- Milne's Example 8.35, at the Frobenius-class level: when the Galois group
has order two, each of its two Frobenius classes has density one half. -/
theorem quadratic_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (hcard : Nat.card G = 2) (sigma : G) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma))
      (1 / 2) := by
  simpa [hcard] using
    (abelian_density_chebotarev K hcheb sigma)

omit [Finite G] in
/-- The union of two distinct Frobenius elements in an abelian group of order
three has density `2/3`.  This is the irreducible portion of the `A₃` row in
Milne's Example 8.36. -/
theorem abelian_classes_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (hcard : Nat.card G = 3) {sigma tau : G} (hne : sigma ≠ tau) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma) ∪
        primesFrobeniusClass K frobeniusClass (ConjClasses.mk tau))
      (2 / 3) := by
  have hclasses : ConjClasses.mk sigma ≠ ConjClasses.mk tau := by
    intro h
    apply hne
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h
    exact h
  have hsigma := abelian_density_chebotarev K hcheb sigma
  have htau := abelian_density_chebotarev K hcheb tau
  have hunion := hsigma.union_of_disjoint K htau
    (disjoint_primes_frobenius K hclasses)
  rw [hcard] at hunion
  convert hunion using 1 ; norm_num

end AbelianChebotarev

section NumberFieldFrobeniusClass

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A fixed prime of `L` above a finite prime of `K`.  The conjugacy class of
the chosen arithmetic Frobenius does not depend on this choice. -/
noncomputable def arithmeticFrobeniusAbove
    (p : HeightOneSpectrum (𝓞 K)) :
    p.asIdeal.primesOver (𝓞 L) :=
  Classical.choice (Ideal.nonempty_primesOver p.asIdeal)

/-- The arithmetic Frobenius conjugacy class attached to a finite prime.

Mathlib chooses compatible arithmetic Frobenius elements even at ramified
primes.  At an unramified prime this is the usual Frobenius conjugacy class;
the arbitrary values at the finitely many ramified primes do not affect the
Chebotarev density formula.
-/
noncomputable def arithmeticFrobeniusClass
    (p : HeightOneSpectrum (𝓞 K)) : ConjClasses Gal(L/K) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  let P := arithmeticFrobeniusAbove K L p
  letI : P.1.IsPrime := P.2.1
  letI : Finite (𝓞 L ⧸ P.1) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2)
  exact ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) P.1)

/-- The finite primes of `K` that ramify in `L`.  This formulation uses a
prime above `p`, so it does not depend on the auxiliary choice made in
`arithmeticFrobeniusClass`. -/
def ramifiedPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ P : Ideal (𝓞 L),
    Ideal.IsPrime P ∧ P ≠ ⊥ ∧ P.under (𝓞 K) = p.asIdeal ∧
      Ideal.ramificationIdx p.asIdeal P ≠ 1}

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Only finitely many finite primes ramify in a number-field extension. -/
theorem finite_ramifiedPrimes : (ramifiedPrimes K L).Finite := by
  let S : Set (Ideal (𝓞 K)) := {p | ∃ P : Ideal (𝓞 L),
    Ideal.IsPrime P ∧ P ≠ ⊥ ∧ P.under (𝓞 K) = p ∧
      Ideal.ramificationIdx p P ≠ 1}
  have hS : S.Finite := ramified_base_primes (𝓞 K) (𝓞 L)
  change ((fun p : HeightOneSpectrum (𝓞 K) ↦ p.asIdeal) ⁻¹' S).Finite
  exact Set.Finite.preimage
    (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h) hS

/-- The standard partial Frobenius-class map: it is undefined precisely at
the finitely many ramified primes. -/
noncomputable def arithmeticFrobeniusOption
    (p : HeightOneSpectrum (𝓞 K)) : Option (ConjClasses Gal(L/K)) := by
  classical
  exact if p ∈ ramifiedPrimes K L then none
    else some (arithmeticFrobeniusClass K L p)

/-- For a fixed conjugacy class, using the partial Frobenius map amounts to
removing the ramified primes from the set defined using the total chosen
map. -/
theorem primes_option_diff (C : ConjClasses Gal(L/K)) :
    primesFrobeniusClass K (arithmeticFrobeniusOption K L) C =
      primesFrobeniusClass K
        (fun p ↦ some (arithmeticFrobeniusClass K L p)) C \
          ramifiedPrimes K L := by
  classical
  ext p
  by_cases hp : p ∈ ramifiedPrimes K L <;>
    simp [primesFrobeniusClass, arithmeticFrobeniusOption, hp]

/-- A concrete statement of Milne's Theorem 8.31 for `L/K`.

This definition is the exact density assertion.  Its proof is the analytic
Chebotarev density theorem, which is not yet part of the pinned Mathlib.
-/
def ChebotarevDensityTheorem : Prop :=
  ChebotarevDensityProperty K fun p ↦
    some (arithmeticFrobeniusClass K L p)

/-- The standard formulation, in which Frobenius is undefined at ramified
primes, is equivalent to the total-map formulation used above.  Thus the
finite exceptional set is not part of the remaining analytic content of
Chebotarev. -/
theorem chebotarev_property_option :
    ChebotarevDensityProperty K (arithmeticFrobeniusOption K L) ↔
      ChebotarevDensityTheorem K L := by
  change ChebotarevDensityProperty K (arithmeticFrobeniusOption K L) ↔
    ChebotarevDensityProperty K
      (fun p ↦ some (arithmeticFrobeniusClass K L p))
  constructor
  · intro hpartial C
    have hC := hpartial C
    rw [primes_option_diff K L C] at hC
    apply hC.congr_fin_diff K
    · simp
    · exact (finite_ramifiedPrimes K L).subset (by
        intro p hp
        by_contra hpr
        exact hp.2 ⟨hp.1, hpr⟩)
  · intro htotal C
    rw [primes_option_diff K L C]
    exact (htotal C).diff_of_finite K (finite_ramifiedPrimes K L)

/-- Milne's Theorem 8.31 holds unconditionally when the Galois group is
trivial. -/
theorem chebotarev_theorem_subsingleton
    [Subsingleton Gal(L/K)] : ChebotarevDensityTheorem K L :=
  chebotarev_property_subsingleton K
    (arithmeticFrobeniusClass K L)

/-- In particular, Chebotarev holds for the trivial extension `K/K`. -/
theorem chebotarev_theorem_self : ChebotarevDensityTheorem K K :=
  chebotarev_theorem_subsingleton K K

/-- The concrete Chebotarev statement implies the density formula for every
conjugacy class. -/
theorem natural_density_frobenius
    (hcheb : ChebotarevDensityTheorem K L) (C : ConjClasses Gal(L/K)) :
    PNDensit K
      {p | arithmeticFrobeniusClass K L p = C}
      ((C.carrier.ncard : ℝ) / Nat.card Gal(L/K)) := by
  simpa [ChebotarevDensityTheorem, primesFrobeniusClass] using hcheb C

end NumberFieldFrobeniusClass

end

end Submission.NumberTheory.Milne
