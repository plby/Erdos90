import Towers.NumberTheory.Density.ChebotarevDensity


/-!
# Chebotarev density for conjugacy-invariant conditions

Polynomial factorization patterns can correspond to a union of Frobenius
conjugacy classes rather than to one class.  This file packages the finite,
disjoint union argument that passes from Chebotarev for individual classes to
Chebotarev for any finite collection of classes.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
  {G : Type*} [Group G] [Finite G]

/-- The finite primes whose Frobenius class belongs to `classes`. -/
def primesFrobeniusClasses
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (classes : Finset (ConjClasses G)) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ C ∈ classes, frobeniusClass p = some C}

omit [Finite G] in
/-- Chebotarev for a finite union of conjugacy classes.  The fibers are
pairwise disjoint, so their densities add. -/
theorem primes_classes_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (classes : Finset (ConjClasses G)) :
    PNDensit K
      (primesFrobeniusClasses K frobeniusClass classes)
      (∑ C ∈ classes, (C.carrier.ncard : ℝ) / Nat.card G) := by
  classical
  induction classes using Finset.induction_on with
  | empty =>
      simpa [primesFrobeniusClasses] using
        (prime_natural_density K Set.finite_empty)
  | @insert C classes hC ih =>
      have hset :
          primesFrobeniusClasses K frobeniusClass (insert C classes) =
            primesFrobeniusClass K frobeniusClass C ∪
              primesFrobeniusClasses K frobeniusClass classes := by
        ext p
        simp only [primesFrobeniusClasses, primesFrobeniusClass,
          Set.mem_setOf_eq, Set.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨D, hD | hD, hp⟩
          · exact Or.inl (hD ▸ hp)
          · exact Or.inr ⟨D, hD, hp⟩
        · rintro (hp | ⟨D, hD, hp⟩)
          · exact ⟨C, Or.inl rfl, hp⟩
          · exact ⟨D, Or.inr hD, hp⟩
      have hdisjoint :
          Disjoint (primesFrobeniusClass K frobeniusClass C)
            (primesFrobeniusClasses K frobeniusClass classes) := by
        apply Set.disjoint_left.2
        intro p hpC hpClasses
        obtain ⟨D, hD, hpD⟩ := hpClasses
        apply hC
        have hCD : C = D := Option.some.inj (hpC.symm.trans hpD)
        exact hCD ▸ hD
      rw [hset]
      have hunion := (hcheb C).union_of_disjoint K ih hdisjoint
      simpa [Finset.sum_insert hC] using hunion

omit [Finite G] in
/-- The finite-union formula with the density written as the total number of
group elements in the selected classes divided by the group order. -/
theorem classes_ratio_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (classes : Finset (ConjClasses G)) :
    PNDensit K
      (primesFrobeniusClasses K frobeniusClass classes)
      (((∑ C ∈ classes, C.carrier.ncard : ℕ) : ℝ) / Nat.card G) := by
  convert primes_classes_chebotarev K hcheb classes using 1
  rw [Nat.cast_sum, Finset.sum_div]

/-- The conjugacy classes satisfying a decidable class property. -/
def conjugacyClassesSatisfying
    (P : ConjClasses G → Prop) [DecidablePred P] :
    Finset (ConjClasses G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact Finset.univ.filter P

/-- The elements in the selected conjugacy classes, indexed by their class,
are equivalent to the elements whose conjugacy class satisfies `P`. -/
private noncomputable def satisfyingConjugacySigma
    (P : ConjClasses G → Prop) [DecidablePred P] :
    (Σ C : ↥(conjugacyClassesSatisfying P), C.1.carrier) ≃
      {g : G // P (ConjClasses.mk g)} where
  toFun x := ⟨x.2.1, by
    have hP : P x.1.1 := by
      simpa only [conjugacyClassesSatisfying, Finset.mem_filter,
        Finset.mem_univ, true_and] using x.1.2
    have hclass : ConjClasses.mk x.2.1 = x.1.1 :=
      ConjClasses.mem_carrier_iff_mk_eq.mp x.2.2
    rwa [hclass]⟩
  invFun g :=
    ⟨⟨ConjClasses.mk g.1, by
        simp only [conjugacyClassesSatisfying, Finset.mem_filter,
          Finset.mem_univ, true_and, g.2]⟩,
      ⟨g.1, by
        rw [ConjClasses.mem_carrier_iff_mk_eq]⟩⟩
  left_inv x := by
    rcases x with ⟨⟨C, hP⟩, ⟨g, hg⟩⟩
    have hclass : ConjClasses.mk g = C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hg
    subst C
    rfl
  right_inv g := by
    rcases g with ⟨g, hg⟩
    rfl

/-- Summing the sizes of conjugacy classes satisfying `P` counts exactly
the group elements whose conjugacy class satisfies `P`. -/
theorem conjugacy_satisfying_ncard
    (P : ConjClasses G → Prop) [DecidablePred P] :
    ∑ C ∈ conjugacyClassesSatisfying P, C.carrier.ncard =
      Nat.card {g : G // P (ConjClasses.mk g)} := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    ← Fintype.card_congr (satisfyingConjugacySigma P),
    Fintype.card_sigma]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- The finite primes whose Frobenius class satisfies `P`. -/
def primesFrobeniusProperty
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (P : ConjClasses G → Prop) [DecidablePred P] :
    Set (HeightOneSpectrum (𝓞 K)) :=
  primesFrobeniusClasses K frobeniusClass
    (conjugacyClassesSatisfying P)

omit [NumberField K] in
@[simp]
theorem primes_frobenius_property
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (P : ConjClasses G → Prop) [DecidablePred P]
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ primesFrobeniusProperty K frobeniusClass P ↔
      ∃ C, frobeniusClass p = some C ∧ P C := by
  classical
  simp [primesFrobeniusProperty, primesFrobeniusClasses,
    conjugacyClassesSatisfying, and_comm]

/-- Chebotarev for an arbitrary decidable property of conjugacy classes. -/
theorem property_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (P : ConjClasses G → Prop) [DecidablePred P] :
    PNDensit K
      (primesFrobeniusProperty K frobeniusClass P)
      (∑ C ∈ conjugacyClassesSatisfying P,
        (C.carrier.ncard : ℝ) / Nat.card G) :=
  primes_classes_chebotarev K hcheb _

section PermutationPartitions

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The full cycle partition represented by a conjugacy class of
permutations.  Unlike `Equiv.Perm.cycleType`, this includes fixed points. -/
def permutationConjugacyPartition :
    ConjClasses (Equiv.Perm alpha) → (Fintype.card alpha).Partition :=
  Quotient.lift Equiv.Perm.partition fun _ _ h =>
    Equiv.Perm.partition_eq_of_isConj.mp h

@[simp]
theorem permutation_conjugacy_partition
    (sigma : Equiv.Perm alpha) :
    permutationConjugacyPartition (ConjClasses.mk sigma) =
      sigma.partition :=
  rfl

/-- The full cycle partition of a conjugacy class after applying a
permutation representation. -/
def conjugacyActionPartition
    (rho : G →* Equiv.Perm alpha) (C : ConjClasses G) :
    (Fintype.card alpha).Partition :=
  permutationConjugacyPartition (ConjClasses.map rho C)

omit [Finite G] in
@[simp]
theorem conjugacy_partition_mk
    (rho : G →* Equiv.Perm alpha) (sigma : G) :
    conjugacyActionPartition rho (ConjClasses.mk sigma) =
      (rho sigma).partition :=
  rfl

/-- The finite primes whose Frobenius permutation has full cycle partition
`parts`. -/
def primesFrobeniusPartition
    (frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G))
    (rho : G →* Equiv.Perm alpha) (parts : Multiset ℕ) :
    Set (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact primesFrobeniusProperty K frobeniusClass fun C =>
    (conjugacyActionPartition rho C).parts = parts

omit [NumberField K] in
@[simp]
theorem primes_frobenius_partition
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (rho : G →* Equiv.Perm alpha) (parts : Multiset ℕ)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ primesFrobeniusPartition K frobeniusClass rho parts ↔
      ∃ C, frobeniusClass p = some C ∧
        (conjugacyActionPartition rho C).parts = parts := by
  classical
  simp [primesFrobeniusPartition]

/-- Chebotarev density for a specified full cycle partition in a finite
permutation representation. -/
theorem partition_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (rho : G →* Equiv.Perm alpha) (parts : Multiset ℕ) :
    PNDensit K
      (primesFrobeniusPartition K frobeniusClass rho parts)
      (∑ C ∈ conjugacyClassesSatisfying
          (fun C : ConjClasses G =>
            (conjugacyActionPartition rho C).parts = parts),
        (C.carrier.ncard : ℝ) / Nat.card G) := by
  classical
  exact property_density_chebotarev K hcheb _

/-- The partition-density formula in cardinal-ratio form. -/
theorem partition_ratio_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (rho : G →* Equiv.Perm alpha) (parts : Multiset ℕ) :
    PNDensit K
      (primesFrobeniusPartition K frobeniusClass rho parts)
      (((∑ C ∈ conjugacyClassesSatisfying
          (fun C : ConjClasses G =>
            (conjugacyActionPartition rho C).parts = parts),
        C.carrier.ncard : ℕ) : ℝ) / Nat.card G) :=
  classes_ratio_chebotarev K hcheb _

omit [Finite G] in
/-- Equivalent groups with pointwise-identical action partitions have the
same number of elements of every partition type.  The explicit pointwise
hypothesis is essential: an abstract group isomorphism alone does not
determine a permutation representation. -/
theorem nat_action_partition
    {H : Type*} [Group H] [Finite H]
    {beta : Type*} [Fintype beta] [DecidableEq beta]
    (rho : G →* Equiv.Perm alpha) (tau : H →* Equiv.Perm beta)
    (e : G ≃* H)
    (hparts : ∀ g,
      ((rho g).partition).parts = ((tau (e g)).partition).parts)
    (parts : Multiset ℕ) :
  Nat.card {g : G // ((rho g).partition).parts = parts} =
      Nat.card {h : H // ((tau h).partition).parts = parts} := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv fun g => by
    change ((rho g).partition).parts = parts ↔
      ((tau (e g)).partition).parts = parts
    rw [hparts g]

end PermutationPartitions

end

end Towers.NumberTheory.Milne
