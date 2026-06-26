import Submission.ClassField.Shifting.NormExactSequence
import Submission.ClassField.Shifting.GroupPeriodicityOdd
import Submission.ClassField.Shifting.CyclicTateShape

/-!
# Milne, Class Field Theory, Proposition II.3.8

The Herbrand quotient of a finite module is one.  The proof follows the two
exact sequences in the source: first compare invariants and coinvariants via
`g - 1`, then compare the kernel and cokernel of the norm.
-/

namespace Submission.CField.Shifting

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

private noncomputable def generatorSub (A : Rep k G) (g : G) : A →ₗ[k] A :=
  (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap

private noncomputable def invariantsGeneratorKer
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants ≃ₗ[k] LinearMap.ker (generatorSub A g) :=
  LinearEquiv.ofEq _ _ <| by
    ext x
    simpa [generatorSub, Rep.sub_hom, sub_eq_zero]
      using Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x

set_option linter.unusedFintypeInType false in
private theorem exact_coinvariants_mk
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Exact (generatorSub A g) (Coinvariants.mk A.ρ) := by
  intro x
  rw [Coinvariants.mk_eq_zero,
    Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
  rfl

set_option linter.unusedFintypeInType false in
private theorem invariants_card_coinvariants
    (A : Rep k G) [Finite A] [Finite A.ρ.Coinvariants] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    addCardUnit A.ρ.invariants =
      addCardUnit A.ρ.Coinvariants := by
  let d := generatorSub A g
  have hKerExact : Function.Exact
      (LinearMap.ker d).subtype.toAddMonoidHom d.rangeRestrict.toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hdx : d x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hdx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact x.property
  have hCokerExact : Function.Exact
      d.range.subtype.toAddMonoidHom (Coinvariants.mk A.ρ).toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ LinearMap.range d :=
        (exact_coinvariants_mk A g hg x).mp hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (exact_coinvariants_mk A g hg x).mpr x.property
  have hKer := card_short_exact
    (LinearMap.ker d).subtype.toAddMonoidHom d.rangeRestrict.toAddMonoidHom
    (Submodule.injective_subtype _)
    hKerExact
    d.toAddMonoidHom.rangeRestrict_surjective
  have hCoker := card_short_exact
    d.range.subtype.toAddMonoidHom (Coinvariants.mk A.ρ).toAddMonoidHom
    (Submodule.injective_subtype _)
    hCokerExact
    (Coinvariants.mk_surjective A.ρ)
  have hInvKer :
      addCardUnit A.ρ.invariants =
        addCardUnit (LinearMap.ker d) := by
    apply Units.ext
    simp only [card_unit_val]
    exact_mod_cast Nat.card_congr
      (invariantsGeneratorKer A g hg).toEquiv
  rw [hInvKer]
  rw [hKer] at hCoker
  calc
    addCardUnit (LinearMap.ker d) =
        (addCardUnit (LinearMap.range d))⁻¹ *
          (addCardUnit (LinearMap.ker d) *
            addCardUnit (LinearMap.range d)) := by
      simp [mul_assoc, mul_comm]
    _ = (addCardUnit (LinearMap.range d))⁻¹ *
          (addCardUnit (LinearMap.range d) *
            addCardUnit A.ρ.Coinvariants) := by rw [hCoker]
    _ = addCardUnit A.ρ.Coinvariants := by
      simp [mul_assoc, mul_comm]

private theorem tate_neg_zero
    (A : Rep k G) [Finite A] [Finite A.ρ.Coinvariants]
    [Finite (tateCohomologyOne A)] [Finite (tateCohomologyZero A)] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    addCardUnit (tateCohomologyOne A) =
      addCardUnit (tateCohomologyZero A) := by
  have hKerExact : Function.Exact
      (tateCohomologyInclusion A).toAddMonoidHom
        (normCoinvariantsInvariants A).rangeRestrict.toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hnorm : normCoinvariantsInvariants A x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hnorm⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact x.property
  have hCokerExact : Function.Exact
      (normCoinvariantsInvariants A).range.subtype.toAddMonoidHom
        (tateCohomologyProjection A).toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ LinearMap.range (normCoinvariantsInvariants A) :=
        (exact_cohomology_projection A x).mp hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (exact_cohomology_projection A x).mpr x.property
  have hKer := card_short_exact
    (tateCohomologyInclusion A).toAddMonoidHom
    (normCoinvariantsInvariants A).rangeRestrict.toAddMonoidHom
    (tate_inclusion_injective A)
    hKerExact
    (normCoinvariantsInvariants A).toAddMonoidHom.rangeRestrict_surjective
  have hCoker := card_short_exact
    (normCoinvariantsInvariants A).range.subtype.toAddMonoidHom
    (tateCohomologyProjection A).toAddMonoidHom
    (Submodule.injective_subtype _)
    hCokerExact
    (tate_projection_surjective A)
  have hInvCoinv := invariants_card_coinvariants A g hg
  rw [hKer, hCoker] at hInvCoinv
  simpa [mul_comm] using hInvCoinv.symm

set_option linter.unusedFintypeInType false in
/-- For a finite module over a finite cyclic group, `H¹` is finite. -/
theorem group_cohomology_module
    (A : Rep k G) [Finite A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (groupCohomology A 1) := by
  letI : Finite A.ρ.Coinvariants :=
    Finite.of_surjective (Coinvariants.mk A.ρ) (Coinvariants.mk_surjective A.ρ)
  letI : Finite (tateCohomologyOne A) := inferInstance
  exact Finite.of_equiv (tateCohomologyOne A)
    (tateCohomologyNeg A g hg).toEquiv

set_option linter.unusedFintypeInType false in
/-- For a finite module over a finite cyclic group, `H²` is finite. -/
theorem cohomology_two_module
    (A : Rep k G) [Finite A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (groupCohomology A 2) := by
  letI : Finite (tateCohomologyZero A) :=
    Finite.of_surjective (tateCohomologyProjection A)
      (tate_projection_surjective A)
  exact Finite.of_equiv (tateCohomologyZero A)
    (tateCohomologyTwo A g hg).toEquiv

private theorem card_unit_linear
    {A B : Type*} [AddGroup A] [AddGroup B] [Finite A] [Finite B]
    (e : A ≃+ B) : addCardUnit A = addCardUnit B := by
  apply Units.ext
  simp only [card_unit_val]
  exact_mod_cast Nat.card_congr e.toEquiv

set_option linter.unusedFintypeInType false in
/-- **Proposition II.3.8.** A finite module has Herbrand quotient one. -/
theorem herbrand_quotient_module
    (A : Rep k G) [Finite A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI : Finite (groupCohomology A 1) :=
      group_cohomology_module A g hg
    letI : Finite (groupCohomology A 2) :=
      cohomology_two_module A g hg
    herbrandQuotient A = 1 := by
  letI : Finite (groupCohomology A 1) :=
    group_cohomology_module A g hg
  letI : Finite (groupCohomology A 2) :=
    cohomology_two_module A g hg
  letI : Finite A.ρ.Coinvariants :=
    Finite.of_surjective (Coinvariants.mk A.ρ) (Coinvariants.mk_surjective A.ρ)
  letI : Finite (tateCohomologyOne A) := inferInstance
  letI : Finite (tateCohomologyZero A) :=
    Finite.of_surjective (tateCohomologyProjection A)
      (tate_projection_surjective A)
  have hcard := tate_neg_zero A g hg
  have hOne := card_unit_linear
    (tateCohomologyNeg A g hg).toAddEquiv
  have hTwo := card_unit_linear
    (tateCohomologyTwo A g hg).toAddEquiv
  rw [hOne, hTwo] at hcard
  simp only [herbrandQuotient]
  rw [← hcard]
  simp

end

end Submission.CField.Shifting
