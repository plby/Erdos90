import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Submission.ClassField.Shifting.LowTateCohomology

/-!
# Milne, Class Field Theory, Proposition II.3.4

The cohomology of a finite cyclic group is periodic with period two.  Mathlib
computes every positive cohomology group using the two alternating homology
objects attached to the norm and `ρ(g) - 1`.  Composing these computations in
degrees `n` and `n + 2` gives the source's generator-dependent period
isomorphisms in all ordinary positive degrees.

The exceptional Tate groups in degrees zero and minus one are treated below
using the same two homology objects.
-/

namespace Submission.CField.Shifting

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- Odd-degree cyclic cohomology is two-periodic. -/
noncomputable def cohomologyPeriodicityOdd
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : Odd n) :
    groupCohomology A n ≅ groupCohomology A (n + 2) :=
  Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (n + 2)
      (hn.add_even even_two)).symm

/-- Positive even-degree cyclic cohomology is two-periodic. -/
noncomputable def cohomologyPeriodicityEven
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) [NeZero n] (hn : Even n) :
    groupCohomology A n ≅ groupCohomology A (n + 2) := by
  letI : NeZero (n + 2) := NeZero.of_pos (by omega)
  exact Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg (n + 2)
      (hn.add even_two)).symm

set_option linter.unusedFintypeInType false in
private theorem cohomology_periodicity_nonempty
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (groupCohomology A n ≅ groupCohomology A (n + 2)) := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · letI : NeZero n := NeZero.of_pos hn
    exact ⟨cohomologyPeriodicityEven A g hg n hnEven⟩
  · exact ⟨cohomologyPeriodicityOdd A g hg n hnOdd⟩

/-- **Proposition II.3.4, ordinary positive degrees.** A choice of generator
of a finite cyclic group determines an isomorphism
`Hⁿ(G,A) ≅ Hⁿ⁺²(G,A)` for every `n > 0`. -/
noncomputable def groupCohomologyPeriodicity
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    groupCohomology A n ≅ groupCohomology A (n + 2) :=
  Classical.choice (cohomology_periodicity_nonempty A g hg n hn)

/-- Odd-degree cyclic group homology is two-periodic. -/
noncomputable def homologyPeriodicityOdd
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : Odd n) :
    groupHomology A n ≅ groupHomology A (n + 2) := by
  letI := Classical.decEq G
  exact Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg (n + 2)
      (hn.add_even even_two)).symm

/-- Positive even-degree cyclic group homology is two-periodic. -/
noncomputable def homologyPeriodicityEven
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) [NeZero n] (hn : Even n) :
    groupHomology A n ≅ groupHomology A (n + 2) := by
  letI := Classical.decEq G
  letI : NeZero (n + 2) := NeZero.of_pos (by omega)
  exact Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg (n + 2)
      (hn.add even_two)).symm

set_option linter.unusedFintypeInType false in
private theorem homology_periodicity_nonempty
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (groupHomology A n ≅ groupHomology A (n + 2)) := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · letI : NeZero n := NeZero.of_pos hn
    exact ⟨homologyPeriodicityEven A g hg n hnEven⟩
  · exact ⟨homologyPeriodicityOdd A g hg n hnOdd⟩

/-- **Proposition II.3.4, ordinary negative Tate range.** Positive group
homology, which models Tate degrees below `-1`, is two-periodic. -/
noncomputable def groupHomologyPeriodicity
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    groupHomology A n ≅ groupHomology A (n + 2) :=
  Classical.choice (homology_periodicity_nonempty A g hg n hn)

/-- For a chosen generator, invariant elements are exactly the kernel of
`ρ(g) - 1`. -/
private noncomputable def invariantsGeneratorKernel
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants ≃ₗ[k]
      LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
  LinearEquiv.ofEq _ _ <| by
    ext x
    simpa [Rep.sub_hom, sub_eq_zero]
      using Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x

/-- The map from invariant representatives to second cohomology supplied by
the even cyclic resolution. -/
private noncomputable def invariantsCohomologyTwo
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants →ₗ[k] groupCohomology A 2 :=
  (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two).hom.comp
    (invariantsGeneratorKernel A g hg).toLinearMap

private theorem ker_invariants_cohomology
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (invariantsCohomologyTwo A g hg) =
      LinearMap.range (normCoinvariantsInvariants A) := by
  ext y
  constructor
  · intro hy
    have hzero :
        Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two
            (invariantsGeneratorKernel A g hg y) = 0 :=
      LinearMap.mem_ker.mp hy
    obtain ⟨x, hx⟩ :=
      (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
        A g hg 2 even_two (invariantsGeneratorKernel A g hg y)).mp hzero
    refine ⟨Coinvariants.mk A.ρ x, ?_⟩
    apply Subtype.ext
    exact hx
  · rintro ⟨q, rfl⟩
    rw [LinearMap.mem_ker]
    induction q using Coinvariants.induction_on with
    | _ x =>
        apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
          A g hg 2 even_two _).mpr
        exact ⟨x, rfl⟩

private theorem invariants_cohomology_surjective
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Surjective (invariantsCohomologyTwo A g hg) := by
  intro z
  obtain ⟨x, hx⟩ :=
    (ModuleCat.epi_iff_surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two)).mp
      inferInstance z
  refine ⟨(invariantsGeneratorKernel A g hg).symm x, ?_⟩
  simpa [invariantsCohomologyTwo] using hx

/-- The quotient map from degree-zero Tate representatives to second group
cohomology. -/
private noncomputable def tateCohomologyGroup
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomologyZero A →ₗ[k] groupCohomology A 2 :=
  (LinearMap.range (normCoinvariantsInvariants A)).liftQ
    (invariantsCohomologyTwo A g hg)
    (ker_invariants_cohomology A g hg).ge

/-- **Proposition II.3.4, degree zero.** For a chosen generator of a finite
cyclic group, `H_T⁰(G,A)` is canonically identified with `H²(G,A)`. -/
noncomputable def tateCohomologyTwo
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomologyZero A ≃ₗ[k] groupCohomology A 2 :=
  LinearEquiv.ofBijective (tateCohomologyGroup A g hg) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot'
        (LinearMap.range (normCoinvariantsInvariants A))
        (invariantsCohomologyTwo A g hg)
        (ker_invariants_cohomology A g hg).symm
    · intro z
      obtain ⟨y, hy⟩ := invariants_cohomology_surjective A g hg z
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      exact hy

/-- Send an element killed by the norm to its coinvariant class, regarded as
an element of `H_T⁻¹`. -/
private noncomputable def normCohomologyNeg
    (A : Rep k G) :
    LinearMap.ker A.norm.hom.toLinearMap →ₗ[k] tateCohomologyOne A :=
  ((Coinvariants.mk A.ρ).comp
      (LinearMap.ker A.norm.hom.toLinearMap).subtype).codRestrict
    (LinearMap.ker (normCoinvariantsInvariants A)) fun x ↦ by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      exact LinearMap.mem_ker.mp x.2

private theorem cohomology_neg_surjective
    (A : Rep k G) :
    Function.Surjective (normCohomologyNeg A) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, hx⟩ := Coinvariants.mk_surjective A.ρ q
  have hnorm : A.norm.hom.toLinearMap x = 0 := by
    have h := congrArg (normCoinvariantsInvariants A) hx
    rw [LinearMap.mem_ker.mp hq] at h
    exact Subtype.ext_iff.mp h
  refine ⟨⟨x, hnorm⟩, ?_⟩
  apply Subtype.ext
  exact hx

private theorem ker_cohomology_negπOdd
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (normCohomologyNeg A) =
      LinearMap.ker
        (Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one).hom := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hleft :
      normCohomologyNeg A x = 0 ↔
        Coinvariants.mk A.ρ x.1 = 0 := by
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  rw [hleft]
  rw [Coinvariants.mk_eq_zero]
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
  rw [Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff]
  rfl

private theorem groupCohomologyπOdd_one_surjective
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one).hom :=
  (ModuleCat.epi_iff_surjective
    (Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one)).mp inferInstance

/-- **Proposition II.3.4, degree minus one.** For a chosen generator of a
finite cyclic group, `H_T⁻¹(G,A)` is canonically identified with `H¹(G,A)`. -/
noncomputable def tateCohomologyNeg
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomologyOne A ≃ₗ[k] groupCohomology A 1 :=
  (LinearMap.quotKerEquivOfSurjective
      (normCohomologyNeg A)
      (cohomology_neg_surjective A)).symm.trans <|
    (Submodule.quotEquivOfEq _ _
      (ker_cohomology_negπOdd
        A g hg)).trans <|
      LinearMap.quotKerEquivOfSurjective
        (Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one).hom
        (groupCohomologyπOdd_one_surjective A g hg)

/-- **Proposition II.3.4, degree minus two.** Under the definition
`H_T⁻²(G,A) = H₁(G,A)`, periodicity identifies this group with
`H_T⁰(G,A)`. -/
noncomputable def homologyTateCohomology
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupHomology A 1 ≃ₗ[k] tateCohomologyZero A := by
  letI := Classical.decEq G
  exact
    (Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg 1 odd_one).toLinearEquiv |>.trans
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm.toLinearEquiv |>.trans
        (tateCohomologyTwo A g hg).symm)

/-- **Proposition II.3.4, degree minus three.** Under the definition
`H_T⁻³(G,A) = H₂(G,A)`, periodicity identifies this group with
`H_T⁻¹(G,A)`. -/
noncomputable def homologyCohomologyNeg
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupHomology A 2 ≃ₗ[k] tateCohomologyOne A := by
  letI := Classical.decEq G
  exact
    (Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg 2 even_two).toLinearEquiv |>.trans
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm.toLinearEquiv |>.trans
        (tateCohomologyNeg A g hg).symm)

end

end Submission.CField.Shifting
