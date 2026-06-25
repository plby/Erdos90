import Submission.FieldTheory.QuotientKoch.CanonicalInverseLimit
import Submission.Group.FinitePRelator.ResidualQuotient
import Submission.Group.FiniteQuotientTower.Completeness


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open PRQuotie
open RRQuot

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The canonical quotient tower remembers the discrete topology already carried by
each relator quotient shadow target.
-/
instance system_obj_topological
    (D : KRData)
    (n : ℕ) :
    TopologicalSpace (D.ZassenhausRelatorSystem.obj n) :=
  (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.targetTopologicalSpace

/--
Each canonical quotient tower level is Hausdorff because its remembered target
topology is discrete.
-/
instance system_obj_space
    (D : KRData)
    (n : ℕ) :
    T2Space (D.ZassenhausRelatorSystem.obj n) := by
  change T2Space (D.ZassenhausRelatorQuotient n).Target
  infer_instance

/--
The canonical Koch Zassenhaus relator quotient tower, now remembering the
discrete `T₂` topology on every finite level so compactness can be applied to
coherent fibers.
-/
def RelatorTopologicalSystem
    (D : KRData) :
    Group.tSQuotie where
  toSystem := D.ZassenhausRelatorSystem
  topologicalSpace_obj := fun _n => inferInstance
  objT2 := fun _n => inferInstance

/--
Every coherent thread in the canonical Koch Zassenhaus relator quotient tower
comes from an element of the initial free pro-`3` group.
-/
lemma zassenhaus_relator_surjective
    (D : KRData) :
    Function.Surjective D.zassenhausRelatorCompletion := by
  exact Group.tSQuotie.limit_compact_space
    D.RelatorTopologicalSystem
    (fun n => (D.ZassenhausRelatorQuotient n).map)
    (fun n => (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.map_continuous)
    (fun n => (D.ZassenhausRelatorQuotient n).map_surjective)
    (fun hmn => D.relator_transition_comp hmn)

/--
The canonical map from the initial free pro-`3` group into the canonical
relator quotient inverse limit is continuous.
-/
lemma zassenhaus_relator_continuous
    (D : KRData) :
    Continuous D.zassenhausRelatorCompletion := by
  exact Group.tSQuotie.inverse_lift_continuous
    D.RelatorTopologicalSystem
    (fun n => (D.ZassenhausRelatorQuotient n).map)
    (fun n => (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.map_continuous)
    (fun hmn => D.relator_transition_comp hmn)

/--
The canonical completion map is exactly the quotient map by the finite-`3`
tame Koch relator residual kernel, followed by one unique residual comparison
map.
-/
lemma uniquely_through_residual
    (D : KRData) :
    FactorsUniquelyThrough
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      D.zassenhausRelatorCompletion := by
  apply factors_uniquely_ker
    (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
    D.zassenhausRelatorCompletion
    (residual_quotient_surjective (p := 3) (initialTameRelator D.frobeniusLift))
  rw [ker_residual_quotient,
    D.relator_completion_kernel]

/--
The finite quotient Koch theorem says exactly that the universal finite-`3`
tame Koch relator residual quotient descends through the actual initial Koch
quotient.
-/
lemma theorem_uniquely_through
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      FactorsUniquelyThrough
        initialKochQuotient
        (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift)) := by
  constructor
  · intro hfactor
    apply factors_uniquely_ker
      initialKochQuotient
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      initial_quotient_surjective
    rw [ker_residual_quotient]
    exact D.factorization_statement_relator.mp
      (D.factorization_theorem_statement.mp hfactor)
  · intro hfactor
    apply D.factorization_theorem_statement.mpr
    apply D.factorization_statement_relator.mpr
    rw [← ker_residual_quotient]
    exact (uniquely_through_ker
      initialKochQuotient
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      initial_quotient_surjective).mp hfactor

/--
The finite-`3` tame Koch relator residual quotient is the inverse limit of the
canonical Zassenhaus finite-layer relator quotients.
-/
def relatorInverseLimit
    (D : KRData) :
    relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift) ≃*
      D.RelatorInverseLimit :=
  (QuotientGroup.quotientMulEquivOfEq
      D.relator_completion_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      D.zassenhausRelatorCompletion
      D.zassenhaus_relator_surjective)

/--
The residual quotient equivalence sends the residual quotient class of an
ambient element to its coherent canonical finite-layer relator quotient thread.
-/
lemma relatorResidualComp
    (D : KRData) :
    D.relatorInverseLimit.toMonoidHom.comp
        (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift)) =
      D.zassenhausRelatorCompletion := by
  apply MonoidHom.ext
  intro x
  simp [relatorInverseLimit,
    residualQuotientMap, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]

/--
The canonical residual quotient equivalence to the canonical relator quotient
inverse limit is continuous.
-/
lemma relatorLimitContinuous
    (D : KRData) :
    Continuous D.relatorInverseLimit := by
  apply (map_is_map
    (p := 3) (initialTameRelator D.frobeniusLift)).continuous_iff.mpr
  change Continuous
    (D.relatorInverseLimit.toMonoidHom.comp
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift)))
  rw [D.relatorResidualComp]
  exact D.zassenhaus_relator_continuous

/--
The canonical residual quotient equivalence to the canonical relator quotient
inverse limit is a homeomorphism.
-/
lemma relator_limit_homeomorph
    (D : KRData) :
    IsHomeomorph D.relatorInverseLimit := by
  apply isHomeomorph_iff_continuous_bijective.mpr
  exact ⟨D.relatorLimitContinuous,
    D.relatorInverseLimit.bijective⟩

/--
The finite-`3` tame Koch relator residual quotient and the canonical
Zassenhaus relator quotient inverse limit are canonically continuously
isomorphic.
-/
def relatorContinuousLimit
    (D : KRData) :
    relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift) ≃ₜ*
      D.RelatorInverseLimit where
  toMulEquiv :=
    D.relatorInverseLimit
  continuous_toFun :=
    D.relatorLimitContinuous
  continuous_invFun :=
    D.relatorLimitContinuous.continuous_symm_of_equiv_compact_to_t2

/--
Assuming the finite quotient Koch theorem, the actual initial Galois group has
one canonical map onto the finite-`3` tame Koch relator residual quotient.
-/
def residualProjectionTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup →*
      relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift) :=
  factorSurjective
    initialKochQuotient
    (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
    initial_quotient_surjective
    (by
      rw [ker_residual_quotient]
      exact (D.factorization_statement_relator.mp
        (D.factorization_theorem_statement.mp
          hfactor)))

/--
The theorem-induced residual projection really descends the ambient residual
quotient map.
-/
lemma koch_projection_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.residualProjectionTheorem hfactor).comp initialKochQuotient =
      residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) := by
  exact factor_map_of
    initialKochQuotient
    (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
    initial_quotient_surjective
    (by
      rw [ker_residual_quotient]
      exact (D.factorization_statement_relator.mp
        (D.factorization_theorem_statement.mp
          hfactor)))

/--
The theorem-induced residual projection is onto: the initial Koch quotient
still sees every finite-`3` relator-residual class.
-/
lemma projection_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Function.Surjective (D.residualProjectionTheorem hfactor) := by
  intro y
  rcases residual_quotient_surjective
      (p := 3) (initialTameRelator D.frobeniusLift) y with
    ⟨x, rfl⟩
  exact ⟨initialKochQuotient x, by
    simpa using congrArg
      (fun φ : initialKochFree.Carrier →*
          relatorResidualQuotient
            (p := 3) (initialTameRelator D.frobeniusLift) =>
        φ x)
      (D.koch_projection_theorem hfactor)⟩

/--
Any map from the actual initial Galois group descending the ambient residual
quotient map is automa onto the residual quotient.
-/
lemma projection_surjective_comp
    (D : KRData)
    (β : initialGaloisGroup →*
      relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift))
    (hβ : β.comp initialKochQuotient =
      residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift)) :
    Function.Surjective β := by
  intro y
  rcases residual_quotient_surjective
      (p := 3) (initialTameRelator D.frobeniusLift) y with
    ⟨x, rfl⟩
  exact ⟨initialKochQuotient x, by
    simpa using congrArg
      (fun φ : initialKochFree.Carrier →*
          relatorResidualQuotient
            (p := 3) (initialTameRelator D.frobeniusLift) =>
        φ x) hβ⟩

/--
Equivalently, the finite quotient Koch theorem produces one compatible
surjection from the actual initial Galois group onto the universal finite-`3`
tame Koch relator residual quotient.
-/
lemma factorization_theorem_projection
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ β : initialGaloisGroup →*
          relatorResidualQuotient
            (p := 3) (initialTameRelator D.frobeniusLift),
        Function.Surjective β ∧
          β.comp initialKochQuotient =
            residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) := by
  constructor
  · intro hfactor
    exact ⟨D.residualProjectionTheorem hfactor,
      D.projection_theorem_surjective hfactor,
      D.koch_projection_theorem hfactor⟩
  · rintro ⟨β, _hβsurj, hβ⟩
    apply
      D.theorem_uniquely_through.mpr
    apply factors_uniquely_ker
      initialKochQuotient
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      initial_quotient_surjective
    exact ker_factors_through
      initialKochQuotient
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      ⟨β, hβ⟩

/--
Assuming the finite quotient Koch theorem, the actual initial Galois group maps
surjectively onto the canonical relator quotient inverse limit.
-/
def limitComparisonTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup →* D.RelatorInverseLimit :=
  D.relatorInverseLimit.toMonoidHom.comp
    (D.residualProjectionTheorem hfactor)

/--
The theorem-induced inverse-limit comparison map descends the ambient
canonical completion map.
-/
lemma comparison_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.limitComparisonTheorem hfactor).comp
        initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  rw [limitComparisonTheorem,
    MonoidHom.comp_assoc,
    D.koch_projection_theorem,
    D.relatorResidualComp]

/--
The theorem-induced inverse-limit comparison map is onto every coherent
canonical finite-layer relator quotient thread.
-/
lemma limit_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Function.Surjective
      (D.limitComparisonTheorem hfactor) := by
  exact D.relatorInverseLimit.surjective.comp
    (D.projection_theorem_surjective hfactor)

/--
Any map from the actual initial Galois group descending the ambient canonical
completion map is automa onto the canonical relator quotient inverse
limit.
-/
lemma limit_comparison_comp
    (D : KRData)
    (β : initialGaloisGroup →* D.RelatorInverseLimit)
    (hβ : β.comp initialKochQuotient =
      D.zassenhausRelatorCompletion) :
    Function.Surjective β := by
  intro y
  rcases D.zassenhaus_relator_surjective y with
    ⟨x, rfl⟩
  exact ⟨initialKochQuotient x, by
    simpa using congrArg
      (fun φ : initialKochFree.Carrier →*
          D.RelatorInverseLimit =>
        φ x) hβ⟩

/--
Equivalently, the finite quotient Koch theorem produces one compatible
surjection from the actual initial Galois group onto the canonical relator
quotient inverse limit.
-/
lemma
  theorem_limit_comparison
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ β : initialGaloisGroup →* D.RelatorInverseLimit,
        Function.Surjective β ∧
          β.comp initialKochQuotient =
            D.zassenhausRelatorCompletion := by
  constructor
  · intro hfactor
    exact ⟨D.limitComparisonTheorem hfactor,
      D.limit_theorem_surjective hfactor,
      D.comparison_theorem_comp hfactor⟩
  · rintro ⟨β, _hβsurj, hβ⟩
    apply D.koch_unique_through.mpr
    apply factors_uniquely_ker
      initialKochQuotient
      D.zassenhausRelatorCompletion
      initial_quotient_surjective
    exact ker_factors_through
      initialKochQuotient
      D.zassenhausRelatorCompletion
      ⟨β, hβ⟩

end KRData

end TBluepr
end Submission
