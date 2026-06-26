import Towers.FieldTheory.HMRProThree.KernelGeneration
import Towers.Group.OpenRelators.NormalRelatorFactorization
import Towers.Group.RelatorsThreeFive.ShadowCorrespondence


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open PRQuotie
open RCFact
open TFFact
open FCFact
open FSCorr

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/-- The five displayed tame Koch relators as a named finite relator family. -/
def fiveRelatorFamily
    (D : KRData) :
    FRFam initialKochFree.Carrier where
  relator := initialTameRelator D.frobeniusLift

@[simp] lemma five_relator_family
    (D : KRData) :
    D.fiveRelatorFamily.relator =
      initialTameRelator D.frobeniusLift := rfl

/-- The initial Koch quotient candidate as a five-relator presented quotient. -/
def fiveRelatorPresented
    (D : KRData) :
    FRPresen
      (G := initialGaloisGroup)
      D.fiveRelatorFamily where
  quotientMap := initialKochQuotient
  quotientMap_continuous := initial_quotient_continuous
  quotientMap_surjective := initial_quotient_surjective
  relator_killed := D.tame_maps_one

@[simp] lemma five_relator_presented
    (D : KRData) :
    D.fiveRelatorPresented.quotientMap =
      initialKochQuotient := rfl

/--
The concrete finite quotient Koch factorization statement for the chosen tame
relator lifts: every continuous finite `3`-group map killing those five
relators contains the initial Koch kernel.
-/
def KochFactorizationTheorem
    (D : KRData) :
    Prop :=
  ∀ {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : initialKochFree.Carrier →* P) →
    Continuous α →
    IsPGroup 3 P →
    (∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) →
    initialKochQuotient.ker ≤ α.ker

lemma factorization_theorem_statement
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.KochFactorizationTheorem := by
  rfl

/--
The initial Koch finite quotient factorization statement is exactly kernel
containment in the finite-`3` relator residual kernel.
-/
lemma factorization_statement_relator
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      initialKochQuotient.ker ≤
        relatorKernel 3 (initialTameRelator D.frobeniusLift) := by
  unfold KochFactorizationTheorem
  change (∀ {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P]
      [Finite P], (α : initialKochFree.Carrier →* P) → Continuous α →
        IsPGroup 3 P → D.fiveRelatorFamily.Kills α →
          initialKochQuotient.ker ≤ α.ker) ↔ _
  rw [Towers.TFFact.fin_statement_property]
  exact factorization_property_relator

/--
For the actual free pro-`3` source, the finite-`3` relator residual kernel is
the intersection of the algebraic tame-relator kernels in all open-normal
finite layers.
-/
lemma relator_algebraic_layer
    (D : KRData) :
    relatorKernel 3 (initialTameRelator D.frobeniusLift) =
      ONFact.algebraicOpenKernel
        (initialTameRelator D.frobeniusLift) := by
  exact ONFact.relator_algebraic_pro
    initialKochFree.isProP

/--
The concrete finite quotient Koch theorem is equivalently containment of the
initial Koch kernel in the algebraic finite-layer relator kernel.
-/
lemma factorization_theorem_algebraic
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      initialKochQuotient.ker ≤
        ONFact.algebraicOpenKernel
          (initialTameRelator D.frobeniusLift) := by
  rw [D.factorization_statement_relator]
  rw [D.relator_algebraic_layer]

/--
The exact finite quotient Koch statement is equivalent to the arithmetic
finite-layer predicate already isolated in the Koch kernel-generation
scaffold.
-/
lemma statement_algebraic_shadows
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift) := by
  unfold KochFactorizationTheorem
  change (∀ {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P]
      [Finite P], (α : initialKochFree.Carrier →* P) → Continuous α →
        IsPGroup 3 P → D.fiveRelatorFamily.Kills α →
          initialKochQuotient.ker ≤ α.ker) ↔ _
  rw [Towers.TFFact.fin_statement_property]
  simpa [IGScaffo.GeneratedAlgebraicallyEvery,
    IGScaffo.GeneratedAlgebraicallyOpen,
    IGScaffoa.quotientMap,
    IGScaffo.relationSubgroup,
    ONFact.GeneratedAlgebraicallyEvery,
    ONFact.GeneratedAlgebraicallyOpen,
    PRFact.relationSubgroup] using
      (ONFact.property_every_pro
        (p := 3)
        (relator := initialTameRelator D.frobeniusLift)
        initialKochFree.isProP
        initialKochQuotient)

/--
The concrete displayed finite quotient Koch theorem has the same exact
finite-layer arithmetic formulation.
-/
lemma theorem_algebraic_shadows
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift) := by
  exact D.statement_algebraic_shadows

/--
Topological normal generation of the Koch kernel by the five tame relators is
enough for the finite quotient Koch factorization statement.
-/
lemma factorization_statement_completed
    (D : KRData)
    (hkernel :
      initialKochQuotient.ker ≤
        Towers.PRFact.completedRelationSubgroup
          (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  apply (D.factorization_statement_relator).mpr
  exact hkernel.trans completed_relation_relator

lemma statement_scaffold_completed
    (D : KRData)
    (hkernel :
      initialKochQuotient.ker ≤
        IGScaffo.completedRelationSubgroup
          (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  apply D.factorization_statement_completed
  simpa [IGScaffo.completedRelationSubgroup,
    IGScaffo.relationSubgroup,
    Towers.PRFact.completedRelationSubgroup,
    Towers.PRFact.relationSubgroup] using hkernel

/--
The topological finite-shadow kernel-generation obligation in the existing Koch
scaffold implies the finite quotient Koch factorization statement.
-/
lemma factorization_statement_shadows
    (D : KRData)
    (h :
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  apply D.statement_scaffold_completed
  exact relation_topological_shadows h

/--
The stronger algebraic finite-shadow kernel-generation obligation also implies
the finite quotient Koch factorization statement.
-/
lemma three_algebraic_shadows
    (D : KRData)
    (h :
      GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  apply D.statement_scaffold_completed
  exact completed_algebraic_shadows h

/--
The topological finite-shadow predicate is also exact here: finite quotient
factorization implies the algebraic finite-layer predicate, hence its
topological weakening.
-/
lemma statement_topological_shadows
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift) := by
  constructor
  · intro hfactor
    exact topologically_every_algebraically
      ((D.statement_algebraic_shadows).mp hfactor)
  · exact D.factorization_statement_shadows

/--
The concrete displayed finite quotient Koch theorem is equivalently the
topological finite-shadow predicate.
-/
lemma theorem_topological_shadows
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift) := by
  exact D.statement_topological_shadows

/--
The pointwise finite-layer relation-word witnesses that an arithmetic proof can
construct directly.
-/
def PointwiseLayerCertificates
    (D : KRData) :
    Prop :=
  ∀ (N : OpenNormalSubgroup initialKochFree.Carrier)
      (x : initialKochFree.Carrier),
    x ∈ initialKochQuotient.ker →
      Nonempty
        (KECert
          initialKochQuotient
          (initialTameRelator D.frobeniusLift)
          N
          x)

/--
The existing algebraic finite-shadow predicate is exactly pointwise existence
of explicit relation-word certificates in every finite layer.
-/
lemma algebraic_shadows_certificates
    (D : KRData) :
    GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift) ↔
      D.PointwiseLayerCertificates := by
  constructor
  · intro h N x hx
    exact ⟨KECert.quotient_relation_subgroup
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      N
      x
      (h N x hx)⟩
  · exact algebraically_every_words

/--
The concrete finite quotient Koch theorem is exactly the pointwise
relation-word certificate problem in every open-normal finite layer.
-/
lemma factorization_pointwise_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.PointwiseLayerCertificates := by
  rw [D.theorem_algebraic_shadows]
  exact D.algebraic_shadows_certificates

/--
The existing topological finite-shadow obligation proves the concrete finite
quotient Koch factorization statement for the actual tame relators.
-/
lemma factorization_topological_shadows
    (D : KRData)
    (h :
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  intro P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
  exact D.factorization_statement_shadows h α hα hP hkill

/--
The stronger algebraic finite-shadow obligation proves the same concrete finite
quotient Koch factorization statement.
-/
lemma factorization_algebraic_shadows
    (D : KRData)
    (h :
      GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)) :
    D.KochFactorizationTheorem := by
  intro P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
  exact D.three_algebraic_shadows h α hα hP hkill

/--
The topological finite-shadow obligation gives the concrete kernel-containment
form of the finite quotient Koch theorem for any continuous finite `3`-group
map killing the five tame relators.
-/
lemma initial_topological_shadows
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (D : KRData)
    (h :
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift))
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : D.fiveRelatorFamily.Kills α) :
    initialKochQuotient.ker ≤ α.ker := by
  exact D.factorization_statement_shadows h α hα hP hkill

/--
The stronger algebraic finite-shadow obligation gives the same concrete
kernel-containment theorem.
-/
lemma initial_algebraic_shadows
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (D : KRData)
    (h :
      GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift))
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : D.fiveRelatorFamily.Kills α) :
    initialKochQuotient.ker ≤ α.ker := by
  exact D.three_algebraic_shadows h α hα hP hkill

lemma five_presented_topological
    (D : KRData) :
    RCFact.PQuot.IsTopologicalQuotient
      D.fiveRelatorPresented := by
  exact RCFact.PQuot.topological_t_1
      D.fiveRelatorPresented

/--
Under the topological finite-shadow kernel-generation obligation, every actual
finite `3`-group quotient killing the five tame relators descends continuously,
surjectively, and uniquely through the initial Galois quotient.
-/
lemma descend_continuously_shadows
    (D : KRData)
    (h :
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)) :
    ∀ S : RQShadow 3 initialKochFree.Carrier
        (initialTameRelator D.frobeniusLift),
      DescendsContinuouslyThrough
        D.fiveRelatorFamily
        D.fiveRelatorPresented
        S := by
  apply (FSCorr.quotients_descend_unique
      D.fiveRelatorFamily
      D.fiveRelatorPresented
      D.five_presented_topological).mp
  exact D.factorization_statement_shadows h

/--
Under the topological finite-shadow kernel-generation obligation, every
continuous finite `3`-group map killing the five tame relators factors
continuously and uniquely through the initial Galois quotient.
-/
lemma continuously_uniquely_shadows
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (D : KRData)
    (h :
      GeneratedTopologicallyEvery
        initialKochQuotient
        (initialTameRelator D.frobeniusLift))
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : D.fiveRelatorFamily.Kills α) :
    ContinuouslyFactorsUniquely initialKochQuotient α := by
  exact FCFact.FRPresen.fin_three_continuous
      D.fiveRelatorFamily
      D.fiveRelatorPresented
      D.five_presented_topological
      (D.factorization_statement_shadows h)
      α
      hα
      hP
      hkill

end KRData

end TBluepr
end Towers
