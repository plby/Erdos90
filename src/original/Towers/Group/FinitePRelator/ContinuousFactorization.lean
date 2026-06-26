import Towers.Group.FinitePRelator.PresentedQuotients
import Mathlib.Topology.Separation.Hausdorff


open scoped Topology

noncomputable section

namespace Towers
namespace RCFact

open PCShadow
open PRFact
open PRQuotie
open RPQuotie

universe u

/-- A factorization whose induced map from the quotient candidate is continuous. -/
def CFThroug
    {F G P : Type u}
    [Group F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P) :
    Prop :=
  ∃ β : G →* P, Continuous β ∧ β.comp q = α

/-- A unique factorization whose induced map from the quotient candidate is continuous. -/
def ContinuouslyFactorsUniquely
    {F G P : Type u}
    [Group F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P) :
    Prop :=
  ∃! β : G →* P, Continuous β ∧ β.comp q = α

variable
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P)

omit [TopologicalSpace F] [IsTopologicalGroup F] in
lemma CFThroug.factorsThrough
    (hfactor : CFThroug q α) :
    FactorsThrough q α := by
  rcases hfactor with ⟨β, _hβcontinuous, hβ⟩
  exact ⟨β, hβ⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
lemma ker_continuously_through
    (hfactor : CFThroug q α) :
    q.ker ≤ α.ker := by
  exact ker_factors_through q α hfactor.factorsThrough

omit [IsTopologicalGroup F] in
/--
A continuous surjection from a compact source to a Hausdorff target is a
quotient map.
-/
lemma surjective_t_space
    [CompactSpace F]
    [T2Space G]
    (hq : Function.Surjective q)
    (hqcontinuous : Continuous q) :
    Topology.IsQuotientMap q := by
  exact IsQuotientMap.of_surjective_continuous hq hqcontinuous

omit [IsTopologicalGroup F] in
/--
The canonical algebraic factor through a quotient map is continuous whenever
the original map is continuous.
-/
lemma factor_surjective_continuous
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hker : q.ker ≤ α.ker) :
    Continuous (factorSurjective q α hquot.surjective hker) := by
  apply hquot.continuous_iff.mpr
  change Continuous ((factorSurjective q α hquot.surjective hker).comp q)
  rw [factor_map_of]
  exact hα

/-- The canonical continuous factor map through a quotient map. -/
noncomputable def continuousFactorQuotient
    (hquot : Topology.IsQuotientMap q)
    (hker : q.ker ≤ α.ker) :
    G →* P :=
  factorSurjective q α hquot.surjective hker

omit [TopologicalSpace P] in
omit [IsTopologicalGroup F] in
lemma continuous_quotient_comp
    (hquot : Topology.IsQuotientMap q)
    (hker : q.ker ≤ α.ker) :
    (continuousFactorQuotient q α hquot hker).comp q = α := by
  exact factor_map_of q α hquot.surjective hker

omit [IsTopologicalGroup F] in
lemma continuous_factor_quotient
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hker : q.ker ≤ α.ker) :
    Continuous (continuousFactorQuotient q α hquot hker) := by
  exact factor_surjective_continuous q α hquot hα hker

omit [IsTopologicalGroup F] in
lemma factors_through_ker
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hker : q.ker ≤ α.ker) :
    CFThroug q α := by
  exact ⟨continuousFactorQuotient q α hquot hker,
    continuous_factor_quotient q α hquot hα hker,
    continuous_quotient_comp q α hquot hker⟩

omit [IsTopologicalGroup F] in
lemma continuously_factors_ker
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α) :
    CFThroug q α ↔ q.ker ≤ α.ker := by
  constructor
  · exact ker_continuously_through q α
  · exact factors_through_ker q α hquot hα

omit [IsTopologicalGroup F] in
lemma continuously_through_ker
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hker : q.ker ≤ α.ker) :
    ContinuouslyFactorsUniquely q α := by
  let β := continuousFactorQuotient q α hquot hker
  refine ⟨β, ?_, ?_⟩
  · exact ⟨continuous_factor_quotient q α hquot hα hker,
      continuous_quotient_comp q α hquot hker⟩
  · intro γ hγ
    apply MonoidHom.ext
    intro y
    rcases hquot.surjective y with ⟨x, rfl⟩
    have hβx := congrArg
      (fun φ : F →* P => φ x)
      (continuous_quotient_comp q α hquot hker)
    have hγx := congrArg (fun φ : F →* P => φ x) hγ.2
    change β (q x) = α x at hβx
    change γ (q x) = α x at hγx
    exact hγx.trans hβx.symm

omit [IsTopologicalGroup F] in
lemma continuously_uniquely_ker
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α) :
    ContinuouslyFactorsUniquely q α ↔ q.ker ≤ α.ker := by
  constructor
  · rintro ⟨β, hβ, _hunique⟩
    exact ker_factors_through q α ⟨β, hβ.2⟩
  · exact continuously_through_ker q α hquot hα

omit [IsTopologicalGroup F] in
lemma continuously_factors_through
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α) :
    ContinuouslyFactorsUniquely q α ↔ FactorsUniquelyThrough q α := by
  rw [continuously_uniquely_ker q α hquot hα]
  exact (uniquely_through_ker q α hquot.surjective).symm

variable
    {p : ℕ}
    {ι : Type*}
    {relator : ι → F}

/--
Every finite relator shadow has a unique continuous factor through the quotient
candidate.
-/
def ContinuousFactorizationProperty
    (p : ℕ)
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    {ι : Type*}
    (relator : ι → F)
    (q : F →* G) :
    Prop :=
  ∀ S : RShadow p F relator,
    ContinuouslyFactorsUniquely q S.map

/--
Every actual surjective finite relator quotient has a unique continuous factor
through the quotient candidate.
-/
def ContinuousQuotientProperty
    (p : ℕ)
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    {ι : Type*}
    (relator : ι → F)
    (q : F →* G) :
    Prop :=
  ∀ S : RQShadow p F relator,
    ContinuouslyFactorsUniquely q S.map

lemma continuous_property
    (hquot : Topology.IsQuotientMap q) :
    ContinuousFactorizationProperty p relator q ↔
      FactorizationProperty p relator q := by
  constructor
  · intro hfactor S
    exact (continuously_uniquely_ker
      q S.map hquot S.toShadow.map_continuous).mp (hfactor S)
  · intro hfactor S
    exact continuously_through_ker
      q S.map hquot S.toShadow.map_continuous (hfactor S)

omit [IsTopologicalGroup F] in
lemma continuous_quotient_property
    [IsTopologicalGroup F]
    (hquot : Topology.IsQuotientMap q) :
    ContinuousQuotientProperty p relator q ↔
      QuotientFactorizationProperty p relator q := by
  constructor
  · intro hfactor S
    exact (continuously_uniquely_ker
      q S.map hquot S.toRShadow.toShadow.map_continuous).mp (hfactor S)
  · intro hfactor S
    exact continuously_through_ker
      q S.map hquot S.toRShadow.toShadow.map_continuous (hfactor S)

omit [IsTopologicalGroup F] in
lemma continuous_factorization_property
    [IsTopologicalGroup F]
    (hquot : Topology.IsQuotientMap q) :
    ContinuousFactorizationProperty p relator q ↔
      ContinuousQuotientProperty p relator q := by
  rw [continuous_property q hquot]
  rw [continuous_quotient_property q hquot]
  exact factorization_property_quotient

omit [IsTopologicalGroup F] [TopologicalSpace P] in
lemma continuously_uniquely_property
    [IsTopologicalGroup F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : Topology.IsQuotientMap q)
    (hfactor : QuotientFactorizationProperty p relator q)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    ContinuouslyFactorsUniquely q α := by
  apply continuously_through_ker q α hquot hα
  exact factorization_property_group
    hfactor hα hP hkill

namespace PQuot

variable
    [T1Space G]
    (Q : PQuot (G := G) relator)

/-- The quotient candidate carries the quotient topology from the source map. -/
def IsTopologicalQuotient :
    Prop :=
  Topology.IsQuotientMap Q.quotientMap

lemma topological_space_t
    [CompactSpace F]
    [T2Space G] :
    IsTopologicalQuotient Q := by
  exact surjective_t_space
    Q.quotientMap Q.quotientMap_surjective Q.quotientMap_continuous

lemma topological_t_1
    [CompactSpace F]
    [IsTopologicalGroup G] :
    IsTopologicalQuotient Q := by
  exact topological_space_t Q

lemma universal_factorization_property
    (hquot : IsTopologicalQuotient Q) :
    Q.FinitePUniversal p ↔
      ContinuousFactorizationProperty p relator Q.quotientMap := by
  change QuotientFactorizationProperty p relator Q.quotientMap ↔
    ContinuousFactorizationProperty p relator Q.quotientMap
  rw [continuous_property Q.quotientMap hquot]
  exact (factorization_property_quotient
    (p := p) (relator := relator) (q := Q.quotientMap)).symm

lemma fin_factorization_property
    (hquot : IsTopologicalQuotient Q) :
    Q.FinitePUniversal p ↔
      ContinuousQuotientProperty p relator Q.quotientMap := by
  change QuotientFactorizationProperty p relator Q.quotientMap ↔
    ContinuousQuotientProperty p relator Q.quotientMap
  exact (continuous_quotient_property
    (p := p) (relator := relator) (q := Q.quotientMap) hquot).symm

omit [TopologicalSpace P] in
lemma continuously_uniquely_through
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    ContinuouslyFactorsUniquely Q.quotientMap α := by
  exact continuously_uniquely_property
    (q := Q.quotientMap) (α := α) hquot hUniversal hα hP hkill

end PQuot

end RCFact
end Towers
