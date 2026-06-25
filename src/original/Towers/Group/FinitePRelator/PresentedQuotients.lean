import Towers.Group.FinitePRelator.FiniteQuotients


open scoped Topology

noncomputable section

namespace Towers
namespace RPQuotie

open PCShadow
open PRFact
open FPQuotie
open PRQuotie

universe u

/--
A homomorphism is a finite-`p` residual monomorphism when every element of its
kernel is invisible in every continuous finite discrete `p`-group shadow of
the source.
-/
def PResidualMonomorphism
    (p : ℕ)
    {H G : Type u}
    [Group H]
    [TopologicalSpace H]
    [Group G]
    (β : H →* G) :
    Prop :=
  β.ker ≤ residualKernel p H

variable
    {p : ℕ}
    {H G : Type u}
    [Group H]
    [TopologicalSpace H]
    [Group G]
    (β : H →* G)

lemma monomorphism_shadows_kill :
    PResidualMonomorphism p β ↔
      ∀ S : Shadow p H, β.ker ≤ S.map.ker := by
  constructor
  · intro hres S
    exact hres.trans (residual_le_kernel S)
  · intro hres
    apply le_sInf
    rintro K ⟨S, rfl⟩
    exact hres S

lemma monomorphism_injective_residually
    (hres : RFP p H) :
    PResidualMonomorphism p β ↔ Function.Injective β := by
  constructor
  · intro hβ
    apply (MonoidHom.ker_eq_bot_iff β).mp
    apply le_antisymm
    · rw [← hres]
      exact hβ
    · exact bot_le
  · intro hβ
    rw [← MonoidHom.ker_eq_bot_iff] at hβ
    change β.ker ≤ residualKernel p H
    rw [hβ]
    exact bot_le

lemma monomorphism_shadows_uniquely
    [IsTopologicalGroup H]
    (hβ : Function.Surjective β) :
    PResidualMonomorphism p β ↔
      ∀ S : Shadow p H, FactorsUniquelyThrough β S.map := by
  rw [monomorphism_shadows_kill]
  constructor
  · intro h S
    exact factors_uniquely_ker β S.map hβ (h S)
  · intro h S
    exact (uniquely_through_ker β S.map hβ).mp (h S)

lemma comap_le_iff
    {F H : Type u}
    [Group F]
    [Group H]
    (π : F →* H)
    (hπ : Function.Surjective π)
    (A B : Subgroup H) :
    A.comap π ≤ B.comap π ↔ A ≤ B := by
  constructor
  · intro hAB y hy
    rcases hπ y with ⟨x, rfl⟩
    exact hAB hy
  · intro hAB x hx
    exact hAB hx

/--
A continuous surjective quotient candidate of `F` killing a displayed relator
family.  Later Koch-specific arithmetic can fill in this record with the
chosen `q : F →* G` and the five tame relators.
-/
structure PQuot
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    {ι : Type*}
    (relator : ι → F) where
  quotientMap : F →* G
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  relator_killed : KillsRelators relator quotientMap

namespace PQuot

variable
    {p : ℕ}
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    [Group P]
    {ι : Type*}
    {relator : ι → F}
    (Q : PQuot (G := G) relator)

/-- The induced map from the completed relator quotient to the quotient candidate. -/
def quotientLift :
    completedRelatorQuotient relator →* G :=
  descendMap relator Q.quotientMap Q.quotientMap_continuous Q.relator_killed

abbrev completedQuotientMap :
    F →* completedRelatorQuotient relator :=
  FPQuotie.quotientMap relator

lemma quotientLift_continuous :
    Continuous Q.quotientLift := by
  exact descendMap_continuous
    relator Q.quotientMap Q.quotientMap_continuous Q.relator_killed

lemma quotient_lift_comp :
    Q.quotientLift.comp (completedQuotientMap (relator := relator)) = Q.quotientMap := by
  exact descend_comp
    relator Q.quotientMap Q.quotientMap_continuous Q.relator_killed

lemma quotientLift_surjective :
    Function.Surjective Q.quotientLift := by
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  exact ⟨completedQuotientMap (relator := relator) x, by
    simpa using congrArg (fun φ : F →* G => φ x) Q.quotient_lift_comp⟩

lemma quotient_comap_lift :
    Q.quotientMap.ker =
      Q.quotientLift.ker.comap (completedQuotientMap (relator := relator)) := by
  ext x
  change Q.quotientMap x = 1 ↔
    Q.quotientLift (completedQuotientMap (relator := relator) x) = 1
  rw [show Q.quotientLift (completedQuotientMap (relator := relator) x) = Q.quotientMap x by
    exact congrArg (fun φ : F →* G => φ x) Q.quotient_lift_comp]

lemma completed_relation_kernel :
    completedRelationSubgroup relator ≤ Q.quotientMap.ker := by
  exact completed_kills_relators
    relator Q.quotientMap Q.quotientMap_continuous Q.relator_killed

lemma lift_completed_relation
    (hker : Q.quotientMap.ker = completedRelationSubgroup relator) :
    Function.Injective Q.quotientLift := by
  apply (MonoidHom.ker_eq_bot_iff Q.quotientLift).mp
  apply le_antisymm
  · intro y hy
    rcases FPQuotie.quotientMap_surjective relator y with ⟨x, rfl⟩
    have hxq : Q.quotientMap x = 1 := by
      have hxLift : Q.quotientLift (completedQuotientMap (relator := relator) x) = 1 :=
        MonoidHom.mem_ker.mp hy
      simpa using hxLift
    have hxRelation : x ∈ completedRelationSubgroup relator := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hxq
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr hxRelation
  · exact bot_le

lemma completed_relation_subgroup :
    Function.Injective Q.quotientLift ↔
      Q.quotientMap.ker = completedRelationSubgroup relator := by
  constructor
  · intro hInjective
    apply le_antisymm
    · intro x hx
      have hxLift : Q.quotientLift (completedQuotientMap (relator := relator) x) = 1 := by
        have hxq : Q.quotientMap x = 1 := MonoidHom.mem_ker.mp hx
        simpa using hxq
      have hxQuotient : completedQuotientMap (relator := relator) x = 1 := by
        apply hInjective
        simpa using hxLift
      exact (QuotientGroup.eq_one_iff x).mp hxQuotient
    · exact Q.completed_relation_kernel
  · exact Q.lift_completed_relation

/--
The generic finite-`p` quotient factorization property for the displayed
relators and this quotient candidate.
-/
def FinitePUniversal
    (p : ℕ) :
    Prop :=
  QuotientFactorizationProperty p relator Q.quotientMap

lemma universal_lift_monomorphism :
    Q.FinitePUniversal p ↔
      PResidualMonomorphism p Q.quotientLift := by
  rw [FinitePUniversal, property_comap_residual]
  rw [Q.quotient_comap_lift]
  exact comap_le_iff
    (completedQuotientMap (relator := relator))
    (FPQuotie.quotientMap_surjective relator)
    Q.quotientLift.ker
    (residualKernel p (completedRelatorQuotient relator))

lemma all_shadows_uniquely :
    Q.FinitePUniversal p ↔
      ∀ S : Shadow p (completedRelatorQuotient relator),
        FactorsUniquelyThrough Q.quotientLift S.map := by
  rw [Q.universal_lift_monomorphism]
  exact monomorphism_shadows_uniquely
    Q.quotientLift Q.quotientLift_surjective

lemma universal_lift_residually
    (hres : RFP p (completedRelatorQuotient relator)) :
    Q.FinitePUniversal p ↔ Function.Injective Q.quotientLift := by
  rw [Q.universal_lift_monomorphism]
  exact monomorphism_injective_residually
    Q.quotientLift hres

lemma completed_relation_residually
    (hres : RFP p (completedRelatorQuotient relator)) :
    Q.FinitePUniversal p ↔
      Q.quotientMap.ker = completedRelationSubgroup relator := by
  rw [Q.universal_lift_residually hres]
  exact Q.completed_relation_subgroup

lemma universal_quotients_uniquely :
    Q.FinitePUniversal p ↔
      ∀ S : RQShadow p F relator,
        FactorsUniquelyThrough Q.quotientMap S.map := by
  exact property_quotients_uniquely
    (q := Q.quotientMap) Q.quotientMap_surjective

/--
Under residual finite-`p`, a finite-`p` universal quotient candidate is
canonically isomorphic to the completed relator quotient.
-/
noncomputable def pUniversalResidually
    (hres : RFP p (completedRelatorQuotient relator))
    (hUniversal : Q.FinitePUniversal p) :
    completedRelatorQuotient relator ≃* G :=
  MulEquiv.ofBijective
    Q.quotientLift
    ⟨(Q.universal_lift_residually
        hres).mp hUniversal,
      Q.quotientLift_surjective⟩

/-- The actual factor map from a universal quotient candidate to one finite `p` quotient. -/
noncomputable def finitePFactor
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    G →* S.Target :=
  factorSurjective
    Q.quotientMap
    S.map
    Q.quotientMap_surjective
    (hUniversal S)

lemma p_factor_comp
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    (Q.finitePFactor hUniversal S).comp Q.quotientMap = S.map := by
  exact factor_map_of
    Q.quotientMap
    S.map
    Q.quotientMap_surjective
    (hUniversal S)

lemma p_factor_unique
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator)
    (β : G →* S.Target)
    (hβ : β.comp Q.quotientMap = S.map) :
    β = Q.finitePFactor hUniversal S := by
  apply MonoidHom.ext
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hβx := congrArg (fun φ : F →* S.Target => φ x) hβ
  have hfactorx := congrArg
    (fun φ : F →* S.Target => φ x)
    (Q.p_factor_comp hUniversal S)
  change β (Q.quotientMap x) = S.map x at hβx
  change Q.finitePFactor hUniversal S (Q.quotientMap x) = S.map x at hfactorx
  exact hβx.trans hfactorx.symm

lemma p_universal_group
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    Q.quotientMap.ker ≤ α.ker := by
  exact factorization_property_group
    hUniversal hα hP hkill

/-- The actual factor map from a universal quotient candidate to an arbitrary finite `p` map. -/
noncomputable def pGroupFactor
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    G →* P :=
  factorSurjective
    Q.quotientMap
    α
    Q.quotientMap_surjective
    (Q.p_universal_group
      hUniversal α hα hP hkill)

lemma p_comp_quotient
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    (Q.pGroupFactor hUniversal α hα hP hkill).comp Q.quotientMap = α := by
  exact factor_map_of
    Q.quotientMap
    α
    Q.quotientMap_surjective
    (Q.p_universal_group
      hUniversal α hα hP hkill)

lemma p_group_unique
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α)
    (β : G →* P)
    (hβ : β.comp Q.quotientMap = α) :
    β = Q.pGroupFactor hUniversal α hα hP hkill := by
  apply MonoidHom.ext
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hβx := congrArg (fun φ : F →* P => φ x) hβ
  have hfactorx := congrArg
    (fun φ : F →* P => φ x)
    (Q.p_comp_quotient hUniversal α hα hP hkill)
  change β (Q.quotientMap x) = α x at hβx
  change Q.pGroupFactor hUniversal α hα hP hkill (Q.quotientMap x) = α x at hfactorx
  exact hβx.trans hfactorx.symm

lemma factors_uniquely_through
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FinitePUniversal p)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    FactorsUniquelyThrough Q.quotientMap α := by
  exact uniquely_through_property
    (q := Q.quotientMap) Q.quotientMap_surjective hUniversal hα hP hkill

end PQuot

end RPQuotie
end Towers
