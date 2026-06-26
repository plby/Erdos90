import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Insert
import Submission.NumberTheory.Density.ConjugacyInvariantDensity
import Submission.ClassField.ChebotarevDensity.Density
import Submission.ClassField.DirichletDensity.PolarLogBridge

/-!
# Chapter VIII, Section 7: unions of Frobenius conjugacy classes

Milne states Chebotarev for an arbitrary conjugation-stable subset of the
Galois group.  Since a finite group has finitely many conjugacy classes, such
a subset is a finite disjoint union of classes.  This file records both the
finite-class form and Milne's literal arbitrary-subset source statement, and
proves the reduction between them.

The analytic proof of the Chebotarev hypothesis remains outside the current
Mathlib API, as documented in `Density.lean`.
-/

namespace Submission.CField.CDensit

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.DDensit
open scoped BigOperators IsMulCommutative

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]
variable {G : Type*} [Group G] [Finite G]

variable (L : Type u) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Corollary VIII.7.3 (source statement).** In a finite abelian extension,
the unramified primes with any prescribed Frobenius element have Dirichlet
density `1 / [L : K]`.  Ramified primes are excluded by the partial
arithmetic Frobenius map. -/
def FrobeniusElementDensity [IsMulCommutative Gal(L/K)] : Prop :=
  ∀ sigma : Gal(L/K),
    PrimeDirichletDensity K
      (primesFrobeniusClass K
        (arithmeticFrobeniusOption K L) (ConjClasses.mk sigma))
      (1 / Module.finrank K L)

/-- **Corollary 7.3, arithmetic form.** For an abelian Galois extension, each
Frobenius element has natural density `1 / [L : K]`, conditional on the exact
Chebotarev statement. -/
theorem arithmetic_frobenius_density
    [IsMulCommutative Gal(L/K)]
    (hcheb : DensityStatement K L) (sigma : Gal(L/K)) :
    PNDensit K
      {p | arithmeticFrobeniusClass K L p = ConjClasses.mk sigma}
      (1 / Module.finrank K L) := by
  have h := abelian_density_chebotarev K hcheb sigma
  rw [IsGalois.card_aut_eq_finrank] at h
  simpa only [primesFrobeniusClass, Set.mem_setOf_eq,
    Option.some.injEq] using h

/-- **Corollary VIII.7.3, literal Dirichlet-density form.** Ramified primes
are excluded by the partial arithmetic Frobenius map. -/
theorem arithmetic_dirichlet_density
    [IsMulCommutative Gal(L/K)]
    (hNaturalToDirichlet :
      ∀ (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
        PNDensit K T δ →
          PrimeDirichletDensity K T δ)
    (hcheb : DensityStatement K L) (sigma : Gal(L/K)) :
    PrimeDirichletDensity K
      (primesFrobeniusClass K
        (arithmeticFrobeniusOption K L) (ConjClasses.mk sigma))
      (1 / Module.finrank K L) := by
  have hoption :
      ChebotarevDensityProperty K (arithmeticFrobeniusOption K L) :=
    (chebotarev_property_option K L).2 hcheb
  have hnatural := abelian_density_chebotarev K hoption sigma
  rw [IsGalois.card_aut_eq_finrank] at hnatural
  exact hNaturalToDirichlet _ _ hnatural

/-- Corollary 7.3 with no analytic comparison hypothesis added to the source
statement.  Proposition VI.4.1(b) supplies the natural-to-Dirichlet passage. -/
theorem frobenius_density_chebotarev
    [IsMulCommutative Gal(L/K)]
    (hNaturalToDirichlet : DensityImpliesDirichlet.{u})
    (hcheb : DensityStatement K L) :
    FrobeniusElementDensity K L := by
  intro sigma
  exact arithmetic_dirichlet_density K L
    (hNaturalToDirichlet K) hcheb sigma

variable {L}

/-- The primes whose Frobenius conjugacy class belongs to a prescribed finite
collection of conjugacy classes. -/
def primesFrobeniusClasses
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (classes : Finset (ConjClasses G)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ C ∈ classes, frobeniusClass p = some C}

/-- **Theorem VIII.7.4 (source statement, finite-conjugacy-class form).** A
conjugation-stable subset of a finite Galois group is represented by the
finite collection of conjugacy classes it contains.  The primes with
Frobenius in that subset have the displayed Dirichlet density. -/
def FrobeniusDirichletDensity : Prop :=
  ∀ classes : Finset (ConjClasses Gal(L/K)),
    PrimeDirichletDensity K
      (primesFrobeniusClasses K
        (arithmeticFrobeniusOption K L) classes)
      ((∑ C ∈ classes, (C.carrier.ncard : ℝ)) / Nat.card Gal(L/K))

/-- Milne's literal condition that a subset is stable under conjugation. -/
def IsConjugationStable (C : Set G) : Prop :=
  ∀ x ∈ C, ∀ tau : G, tau * x * tau⁻¹ ∈ C

/-- The unramified primes whose arithmetic Frobenius conjugacy class is
contained in `C`.  Since the Frobenius map is `Option`-valued, ramified
primes—where it is `none`—are excluded by definition. -/
def primesArithmeticFrobenius
    (C : Set Gal(L/K)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ D : ConjClasses Gal(L/K),
    arithmeticFrobeniusOption K L p = some D ∧ D.carrier ⊆ C}

/-- **Theorem VIII.7.4 (literal source statement).** For every
conjugation-stable subset `C` of the actual Galois group, the unramified
primes with Frobenius class in `C` have Dirichlet density `|C| / |G|`.

The analytic inputs used to prove this assertion are deliberately absent
from the source statement. -/
def ConjugacyUnionDensity : Prop :=
  ∀ C : Set Gal(L/K), IsConjugationStable C →
    PrimeDirichletDensity K
      (primesArithmeticFrobenius K (L := L) C)
      ((C.ncard : ℝ) / Nat.card Gal(L/K))

/-- The finite set of conjugacy classes entirely contained in `C`. -/
noncomputable def conjugacyClassesContained (C : Set G) :
    Finset (ConjClasses G) := by
  classical
  exact Submission.NumberTheory.Milne.conjugacyClassesSatisfying
    (fun D : ConjClasses G => D.carrier ⊆ C)

/-- The literal Frobenius prime set is the finite union indexed by the
conjugacy classes contained in `C`. -/
theorem arithmetic_classes_contained
    (C : Set Gal(L/K)) :
    primesArithmeticFrobenius K (L := L) C =
      primesFrobeniusClasses K
        (arithmeticFrobeniusOption K L)
        (conjugacyClassesContained C) := by
  classical
  ext p
  simp only [primesArithmeticFrobenius,
    primesFrobeniusClasses, Set.mem_setOf_eq,
    conjugacyClassesContained,
    Submission.NumberTheory.Milne.conjugacyClassesSatisfying,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D, hpD, hD⟩
    exact ⟨D, hD, hpD⟩
  · rintro ⟨D, hD, hpD⟩
    exact ⟨D, hpD, hD⟩

/-- A conjugation-stable subset is exactly the disjoint union of the
conjugacy classes contained in it, so the class sizes sum to its cardinality. -/
theorem conjugacy_contained_ncard
    (C : Set G) (hC : IsConjugationStable C) :
    ∑ D ∈ conjugacyClassesContained C, D.carrier.ncard = C.ncard := by
  classical
  have hmem (g : G) : (ConjClasses.mk g).carrier ⊆ C ↔ g ∈ C := by
    constructor
    · intro hg
      exact hg ConjClasses.mem_carrier_mk
    · intro hg x hx
      have hclass : ConjClasses.mk x = ConjClasses.mk g :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      have hconj : IsConj g x :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hclass.symm
      obtain ⟨tau, htau⟩ := isConj_iff.mp hconj
      rw [← htau]
      exact hC g hg tau
  calc
    ∑ D ∈ conjugacyClassesContained C, D.carrier.ncard =
        Nat.card {g : G // (ConjClasses.mk g).carrier ⊆ C} :=
      by
        simpa only [conjugacyClassesContained] using
          (Submission.NumberTheory.Milne.conjugacy_satisfying_ncard
            (fun D : ConjClasses G => D.carrier ⊆ C))
    _ = Nat.card C := by
      apply Nat.card_congr
      exact Equiv.setCongr (Set.ext fun g => hmem g)
    _ = C.ncard := Nat.card_coe_set_eq C

omit [NumberField K] [Finite G] in
@[simp]
theorem primes_classes_empty
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)) :
    primesFrobeniusClasses K frobeniusClass ∅ = ∅ := by
  ext p
  simp [primesFrobeniusClasses]

omit [NumberField K] [Finite G] in
theorem primes_classes_cons
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (C : ConjClasses G) (classes : Finset (ConjClasses G))
    (hC : C ∉ classes) :
    primesFrobeniusClasses K frobeniusClass (classes.cons C hC) =
      primesFrobeniusClass K frobeniusClass C ∪
        primesFrobeniusClasses K frobeniusClass classes := by
  ext p
  simp [primesFrobeniusClasses, primesFrobeniusClass]

omit [Finite G] in
/-- **Theorem 7.4 (Chebotarev), finite-union form.** Conditional on the exact
Chebotarev property, the primes whose Frobenius belongs to a finite collection
of conjugacy classes have density equal to the sum of the class sizes divided
by the order of the group.  This is Milne's formulation for a
conjugation-stable subset, represented by its constituent classes. -/
theorem frobenius_classes_density
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (classes : Finset (ConjClasses G)) :
    PNDensit K
      (primesFrobeniusClasses K frobeniusClass classes)
      ((∑ C ∈ classes, (C.carrier.ncard : ℝ)) / Nat.card G) := by
  classical
  induction classes using Finset.induction_on with
  | empty =>
      simpa using
        (prime_natural_density K
          (Set.finite_empty : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite))
  | @insert C classes hC ih =>
      have hdisjoint :
          Disjoint (primesFrobeniusClass K frobeniusClass C)
            (primesFrobeniusClasses K frobeniusClass classes) := by
        apply Set.disjoint_left.2
        intro p hpC hpclasses
        rcases hpclasses with ⟨D, hD, hpD⟩
        have hCD : C = D := Option.some.inj (hpC.symm.trans hpD)
        exact hC (hCD ▸ hD)
      have hunion :=
        (hcheb C).union_of_disjoint K ih hdisjoint
      have hsets :
          primesFrobeniusClasses K frobeniusClass (insert C classes) =
            primesFrobeniusClass K frobeniusClass C ∪
              primesFrobeniusClasses K frobeniusClass classes := by
        ext p
        simp [primesFrobeniusClasses, primesFrobeniusClass]
      rw [hsets]
      simpa [Finset.sum_insert, hC, add_div] using hunion

/-- **Theorem VIII.7.4, Dirichlet-density form for a conjugation-stable set
represented by its finite collection of conjugacy classes.** -/
theorem classes_dirichlet_density
    (hNaturalToDirichlet :
      ∀ (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
        PNDensit K T δ →
          PrimeDirichletDensity K T δ)
    (hcheb : ChebotarevDensityTheorem K L)
    (classes : Finset (ConjClasses Gal(L/K))) :
    PrimeDirichletDensity K
      (primesFrobeniusClasses K
        (arithmeticFrobeniusOption K L) classes)
      ((∑ C ∈ classes, (C.carrier.ncard : ℝ)) / Nat.card Gal(L/K)) := by
  have hoption : ChebotarevDensityProperty K
      (arithmeticFrobeniusOption K L) :=
    (chebotarev_property_option K L).2 hcheb
  exact hNaturalToDirichlet _ _
    (frobenius_classes_density K hoption classes)

/-- The literal Dirichlet-density theorem follows from the exact arithmetic
Chebotarev statement and Proposition VI.4.1(b), without placing either input
inside the source statement. -/
theorem dirichlet_density_chebotarev
    (hNaturalToDirichlet : DensityImpliesDirichlet.{u})
    (hcheb : ChebotarevDensityTheorem K L) :
    FrobeniusDirichletDensity K (L := L) := by
  intro classes
  exact classes_dirichlet_density K (L := L)
    (hNaturalToDirichlet K) hcheb classes

/-- Milne's literal arbitrary-subset theorem reduces to the finite-class
form because the Galois group is finite. -/
theorem conjugacy_unions_classes
    (hfinite : FrobeniusDirichletDensity K (L := L)) :
    ConjugacyUnionDensity K (L := L) := by
  intro C hC
  have h := hfinite (conjugacyClassesContained C)
  rw [← arithmetic_classes_contained K (L := L) C] at h
  have hcard :
      ∑ D ∈ conjugacyClassesContained C, (D.carrier.ncard : ℝ) =
        (C.ncard : ℝ) := by
    exact_mod_cast conjugacy_contained_ncard C hC
  rwa [hcard] at h

/-- The literal source statement follows from arithmetic Chebotarev and the
natural-to-Dirichlet density comparison, while neither analytic input occurs
in `ConjugacyUnionDensity` itself. -/
theorem conjugacy_density_chebotarev
    (hNaturalToDirichlet : DensityImpliesDirichlet.{u})
    (hcheb : ChebotarevDensityTheorem K L) :
    ConjugacyUnionDensity K (L := L) :=
  conjugacy_unions_classes K (L := L)
    (dirichlet_density_chebotarev K (L := L)
      hNaturalToDirichlet hcheb)

end

end Submission.CField.CDensit
