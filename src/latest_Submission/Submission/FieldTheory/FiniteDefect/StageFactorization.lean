import Submission.FieldTheory.FiniteDefect.Separation


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open RCFact
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The ambient honest finite kernel-image quotient map from the initial free
pro-`3` group is continuous for the remembered discrete finite quotient
topology.
-/
lemma initial_image_continuous
    (n : ℕ) :
    Continuous (initialKochImage n) := by
  letI : DiscreteTopology (OpenNormalLayer (zassenhausOpenSubgroup n)) :=
    pro_discrete_topology (zassenhausOpenSubgroup n)
  change Continuous
    ((QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))).comp
      (openNormalLayer (zassenhausOpenSubgroup n)))
  have hkernelImageQuotientMapContinuous :
      Continuous
        (QuotientGroup.mk'
          (kernelImage initialKochQuotient
            (zassenhausOpenSubgroup n))) :=
    continuous_of_discreteTopology
  exact hkernelImageQuotientMapContinuous.comp
    (pro_open_continuous
      (zassenhausOpenSubgroup n))

/--
The ambient honest finite kernel-image quotient map is a topological quotient
map.
-/
lemma koch_image_quotient
    (n : ℕ) :
    Topology.IsQuotientMap (initialKochImage n) := by
  exact surjective_t_space
    (initialKochImage n)
    (koch_image_surjective n)
    (initial_image_continuous n)

/--
Under the desired finite quotient Koch theorem, the honest finite
kernel-image quotient at the canonical target depth of a finite relator map
already kills that map's kernel.
-/
lemma initial_target_depth
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (initialKochImage
      (D.ThreeTargetDepth α hα hP hkill)).ker ≤
      α.ker := by
  apply initial_koch_layer
  · exact D.relator_target_depth
      α hα hP hkill
  · exact hfactor α hα hP hkill

/--
The canonical honest finite kernel-image stage factor of a finite relator map
under the desired theorem.
-/
def initialStageTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    InitialKochImage
        (D.ThreeTargetDepth α hα hP hkill) →* P :=
  continuousFactorQuotient
    (initialKochImage
      (D.ThreeTargetDepth α hα hP hkill))
    α
    (koch_image_quotient
      (D.ThreeTargetDepth α hα hP hkill))
    (D.initial_target_depth
      hfactor α hα hP hkill)

/--
The honest finite kernel-image stage factor descends the original finite
relator map.
-/
lemma stage_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.initialStageTheorem
      hfactor α hα hP hkill).comp
        (initialKochImage
          (D.ThreeTargetDepth α hα hP hkill)) =
      α := by
  exact continuous_quotient_comp
    (initialKochImage
      (D.ThreeTargetDepth α hα hP hkill))
    α
    (koch_image_quotient
      (D.ThreeTargetDepth α hα hP hkill))
    (D.initial_target_depth
      hfactor α hα hP hkill)

/--
The honest finite kernel-image stage factor is continuous.
-/
lemma stage_theorem_continuous
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    Continuous (D.initialStageTheorem
      hfactor α hα hP hkill) := by
  exact continuous_factor_quotient
    (initialKochImage
      (D.ThreeTargetDepth α hα hP hkill))
    α
    (koch_image_quotient
      (D.ThreeTargetDepth α hα hP hkill))
    hα
    (D.initial_target_depth
      hfactor α hα hP hkill)

/--
If the original finite relator map is onto, then its honest finite
kernel-image stage factor is onto.
-/
lemma stage_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hαsurj : Function.Surjective α) :
    Function.Surjective
      (D.initialStageTheorem
        hfactor α hα hP hkill) := by
  intro y
  rcases hαsurj y with ⟨x, rfl⟩
  exact ⟨initialKochImage
      (D.ThreeTargetDepth α hα hP hkill) x,
    DFunLike.congr_fun
      (D.stage_theorem_comp
        hfactor α hα hP hkill)
      x⟩

/--
The unique induced map from the actual initial Galois group to one finite
relator-map target under the desired theorem.
-/
def relatorFactorTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    initialGaloisGroup →* P :=
  continuousFactorQuotient
    initialKochQuotient
    α
    initial_koch
    (hfactor α hα hP hkill)

/--
The theorem-level factor from the actual initial Galois group descends the
original finite relator map.
-/
lemma relator_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.relatorFactorTheorem hfactor α hα hP hkill).comp
        initialKochQuotient =
      α := by
  exact continuous_quotient_comp
    initialKochQuotient
    α
    initial_koch
    (hfactor α hα hP hkill)

/--
The theorem-level factor from the actual initial Galois group is continuous.
-/
lemma relator_theorem_continuous
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    Continuous (D.relatorFactorTheorem hfactor α hα hP hkill) := by
  exact continuous_factor_quotient
    initialKochQuotient
    α
    initial_koch
    hα
    (hfactor α hα hP hkill)

/--
The desired theorem gives the user-facing continuous unique factorization of
every finite `3`-group relator map through the actual initial Galois quotient.
-/
lemma continuously_uniquely_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    ContinuouslyFactorsUniquely initialKochQuotient α := by
  exact continuously_through_ker
    initialKochQuotient
    α
    initial_koch
    hα
    (hfactor α hα hP hkill)

/--
The honest finite kernel-image stage factor realizes the theorem-level factor
from the actual initial Galois group after passing through the honest finite
kernel-image quotient of that group.
-/
lemma initial_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.initialStageTheorem
      hfactor α hα hP hkill).comp
        (initialKochFactor
          (D.ThreeTargetDepth α hα hP hkill)) =
      D.relatorFactorTheorem hfactor α hα hP hkill := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hstage := DFunLike.congr_fun
    (D.stage_theorem_comp
      hfactor α hα hP hkill)
    x
  have hfinite := DFunLike.congr_fun
    (initial_image_comp
      (D.ThreeTargetDepth α hα hP hkill))
    x
  have hgalois := DFunLike.congr_fun
    (D.relator_theorem_comp
      hfactor α hα hP hkill)
    x
  change D.initialStageTheorem
      hfactor α hα hP hkill
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill) x) =
    α x at hstage
  change initialKochFactor
      (D.ThreeTargetDepth α hα hP hkill)
      (initialKochQuotient x) =
    initialKochImage
      (D.ThreeTargetDepth α hα hP hkill) x at hfinite
  change D.relatorFactorTheorem hfactor α hα hP hkill
      (initialKochQuotient x) =
    α x at hgalois
  change D.initialStageTheorem
      hfactor α hα hP hkill
      (initialKochFactor
        (D.ThreeTargetDepth α hα hP hkill)
        (initialKochQuotient x)) =
    D.relatorFactorTheorem hfactor α hα hP hkill
      (initialKochQuotient x)
  rw [hfinite, hstage, hgalois]

/--
Every finite relator map factors uniquely through its canonical honest finite
kernel-image stage.
-/
def AllTargetDepth
    (D : KRData) :
    Prop :=
  ∀ {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : initialKochFree.Carrier →* P) →
    (hα : Continuous α) →
    (hP : IsPGroup 3 P) →
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) →
    FactorsUniquelyThrough
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill))
      α

/--
Every finite relator map factors continuously and uniquely through its
canonical honest finite kernel-image stage.
-/
def AllUniqueTarget
    (D : KRData) :
    Prop :=
  ∀ {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : initialKochFree.Carrier →* P) →
    (hα : Continuous α) →
    (hP : IsPGroup 3 P) →
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) →
    ContinuouslyFactorsUniquely
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill))
      α

/--
The desired finite quotient Koch theorem is exactly finite-stage factorization
through the canonical honest finite kernel-image quotient selected by each
finite relator map's target depth.
-/
lemma unique_target_depth
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllTargetDepth := by
  constructor
  · intro hfactor P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    apply factors_uniquely_ker
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (koch_image_surjective
        (D.ThreeTargetDepth α hα hP hkill))
    exact D.initial_target_depth
      hfactor α hα hP hkill
  · intro hstage P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let n := D.ThreeTargetDepth α hα hP hkill
    exact (initial_koch_image
      n).trans
      ((uniquely_through_ker
        (initialKochImage n)
        α
        (koch_image_surjective n)).mp
        (hstage α hα hP hkill))

/--
The desired finite quotient Koch theorem is equivalently continuous finite-stage
factorization through the canonical honest finite kernel-image quotient
selected by each finite relator map's target depth.
-/
lemma fin_target_depth
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllUniqueTarget := by
  constructor
  · intro hfactor P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    apply continuously_through_ker
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (koch_image_quotient
        (D.ThreeTargetDepth α hα hP hkill))
      hα
    exact D.initial_target_depth
      hfactor α hα hP hkill
  · intro hstage
    apply (D.unique_target_depth).mpr
    intro P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    exact (continuously_factors_through
      (initialKochImage
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (koch_image_quotient
        (D.ThreeTargetDepth α hα hP hkill))
      hα).mp
      (hstage α hα hP hkill)

/--
The corrected canonical finite defect stage as an ambient quotient map from
the initial free pro-`3` group.
-/
def canonicalDefectAmbient
    (D : KRData)
    (n : ℕ) :
    initialKochFree.Carrier →* D.CanonicalKochDefect n :=
  (D.canonicalDefectFactor n).comp initialKochQuotient

/--
The corrected canonical finite defect ambient map is also the canonical
relator quotient map followed by the finite defect quotient map.
-/
lemma koch_fin_ambient
    (D : KRData)
    (n : ℕ) :
    D.canonicalDefectAmbient n =
      (D.canonicalKochDefect n).comp
        (D.ZassenhausRelatorQuotient n).map := by
  exact D.canonical_defect_comp n

/--
The finite-level defect/image equivalence carries the corrected canonical
finite defect ambient map to the honest finite kernel-image quotient map.
-/
lemma defect_comp_ambient
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.canonicalDefectAmbient n) =
      initialKochImage n := by
  rw [canonicalDefectAmbient, ← MonoidHom.comp_assoc,
    D.defect_comp_factor,
    initial_image_comp]

/--
The corrected canonical finite defect ambient map has exactly the honest finite
kernel-image quotient kernel.
-/
lemma defect_ambient_image
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectAmbient n).ker =
      (initialKochImage n).ker := by
  rw [← D.defect_comp_ambient
    n]
  exact (monoid_ker_comp
    (D.canonicalDefectImage n)
    (D.canonicalDefectAmbient n)).symm

/--
The corrected canonical finite defect ambient map is continuous.
-/
lemma defect_ambient_continuous
    (D : KRData)
    (n : ℕ) :
    Continuous (D.canonicalDefectAmbient n) := by
  exact (D.canonical_defect_continuous n).comp
    initial_quotient_continuous

/--
The corrected canonical finite defect ambient map is onto.
-/
lemma defect_ambient_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective (D.canonicalDefectAmbient n) := by
  exact (D.canonical_defect_surjective n).comp
    initial_quotient_surjective

/--
The corrected canonical finite defect ambient map is a topological quotient
map.
-/
lemma koch_defect_ambient
    (D : KRData)
    (n : ℕ) :
    Topology.IsQuotientMap (D.canonicalDefectAmbient n) := by
  exact surjective_t_space
    (D.canonicalDefectAmbient n)
    (D.defect_ambient_surjective n)
    (D.defect_ambient_continuous n)

/--
Under the desired theorem, the corrected canonical finite defect stage at the
canonical target depth of a finite relator map already kills that map's
kernel.
-/
lemma ambient_target_depth
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.canonicalDefectAmbient
      (D.ThreeTargetDepth α hα hP hkill)).ker ≤
      α.ker := by
  rw [D.defect_ambient_image]
  exact D.initial_target_depth
    hfactor α hα hP hkill

/--
The corrected canonical finite defect stage factor of one finite relator map
under the desired theorem.
-/
def defectStageTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    D.CanonicalKochDefect
        (D.ThreeTargetDepth α hα hP hkill) →* P :=
  (D.initialStageTheorem
      hfactor α hα hP hkill).comp
    (D.canonicalDefectImage
      (D.ThreeTargetDepth α hα hP hkill)).toMonoidHom

/--
The corrected canonical finite defect stage factor descends the original finite
relator map.
-/
lemma stage_theorem_ambient
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.defectStageTheorem
      hfactor α hα hP hkill).comp
        (D.canonicalDefectAmbient
          (D.ThreeTargetDepth α hα hP hkill)) =
      α := by
  rw [defectStageTheorem, MonoidHom.comp_assoc,
    D.defect_comp_ambient,
    D.stage_theorem_comp]

/--
The corrected canonical finite defect stage factor is continuous.
-/
lemma defect_stage_continuous
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    Continuous (D.defectStageTheorem
      hfactor α hα hP hkill) := by
  exact continuous_of_discreteTopology

/--
If the original finite relator map is onto, then its corrected canonical
finite defect stage factor is onto.
-/
lemma defect_stage_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hαsurj : Function.Surjective α) :
    Function.Surjective
      (D.defectStageTheorem
        hfactor α hα hP hkill) := by
  intro y
  rcases hαsurj y with ⟨x, rfl⟩
  exact ⟨D.canonicalDefectAmbient
      (D.ThreeTargetDepth α hα hP hkill) x,
    DFunLike.congr_fun
      (D.stage_theorem_ambient
        hfactor α hα hP hkill)
      x⟩

/--
The corrected canonical finite defect stage factor realizes the theorem-level
factor from the actual initial Galois group after passing through the
corrected canonical finite defect quotient of that group.
-/
lemma defect_stage_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (D.defectStageTheorem
      hfactor α hα hP hkill).comp
        (D.canonicalDefectFactor
          (D.ThreeTargetDepth α hα hP hkill)) =
      D.relatorFactorTheorem hfactor α hα hP hkill := by
  rw [defectStageTheorem, MonoidHom.comp_assoc,
    D.defect_comp_factor,
    D.initial_theorem_comp]

/--
Every finite relator map factors uniquely through its corrected canonical
finite defect stage.
-/
def AllUniqueDepth
    (D : KRData) :
    Prop :=
  ∀ {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : initialKochFree.Carrier →* P) →
    (hα : Continuous α) →
    (hP : IsPGroup 3 P) →
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) →
    FactorsUniquelyThrough
      (D.canonicalDefectAmbient
        (D.ThreeTargetDepth α hα hP hkill))
      α

/--
Every finite relator map factors continuously and uniquely through its
corrected canonical finite defect stage.
-/
def UniqueTargetDepth
    (D : KRData) :
    Prop :=
  ∀ {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : initialKochFree.Carrier →* P) →
    (hα : Continuous α) →
    (hP : IsPGroup 3 P) →
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) →
    ContinuouslyFactorsUniquely
      (D.canonicalDefectAmbient
        (D.ThreeTargetDepth α hα hP hkill))
      α

/--
The desired finite quotient Koch theorem is exactly finite-stage factorization
through the corrected canonical finite defect quotient selected by each finite
relator map's target depth.
-/
lemma fin_unique_target
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllUniqueDepth := by
  constructor
  · intro hfactor P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    apply factors_uniquely_ker
      (D.canonicalDefectAmbient
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (D.defect_ambient_surjective
        (D.ThreeTargetDepth α hα hP hkill))
    exact D.ambient_target_depth
      hfactor α hα hP hkill
  · intro hstage P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let n := D.ThreeTargetDepth α hα hP hkill
    exact (initial_koch_image
      n).trans
      ((D.defect_ambient_image
        n).symm.le.trans
        ((uniquely_through_ker
          (D.canonicalDefectAmbient n)
          α
          (D.defect_ambient_surjective n)).mp
          (hstage α hα hP hkill)))

/--
The desired finite quotient Koch theorem is equivalently continuous finite-stage
factorization through the corrected canonical finite defect quotient selected
by each finite relator map's target depth.
-/
lemma continuous_target_depth
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.UniqueTargetDepth := by
  constructor
  · intro hfactor P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    apply continuously_through_ker
      (D.canonicalDefectAmbient
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (D.koch_defect_ambient
        (D.ThreeTargetDepth α hα hP hkill))
      hα
    exact D.ambient_target_depth
      hfactor α hα hP hkill
  · intro hstage
    apply (D.fin_unique_target).mpr
    intro P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    exact (continuously_factors_through
      (D.canonicalDefectAmbient
        (D.ThreeTargetDepth α hα hP hkill))
      α
      (D.koch_defect_ambient
        (D.ThreeTargetDepth α hα hP hkill))
      hα).mp
      (hstage α hα hP hkill)

end KRData

end TBluepr
end Submission
