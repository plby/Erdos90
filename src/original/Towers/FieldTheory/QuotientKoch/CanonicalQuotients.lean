import Towers.FieldTheory.QuotientKoch.FiniteFamilies
import Towers.Group.OpenRelators.CanonicalQuotients


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
open OCQuotie

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The canonical actual surjective finite `3`-group relator quotient obtained by
killing the `n`th Zassenhaus finite layer and the five tame Koch relators
algebraically.
-/
abbrev ZassenhausRelatorQuotient
    (D : KRData)
    (n : ℕ) :
    D.ThreeRelatorQuotient :=
  OCQuotie.zassenhausRelatorQuotient
    (p := 3)
    (relator := initialTameRelator D.frobeniusLift)
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    n

/--
The least canonical Zassenhaus depth whose finite layer lies inside the kernel
of one actual surjective finite `3`-group relator quotient.
-/
abbrev RelatorTargetDepth
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :=
  D.ThreeTargetDepth
    S.map
    S.toRShadow.toShadow.map_continuous
    S.toRShadow.toShadow.target_p_group
    S.toRShadow.relator_killed

/--
At the target depth of one actual surjective finite `3`-group relator quotient,
the canonical Zassenhaus finite-layer relator quotient lies above that target
quotient.
-/
lemma finTargetDepth
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    (D.ZassenhausRelatorQuotient
      (D.RelatorTargetDepth S)).map.ker ≤ S.map.ker := by
  apply OCQuotie.zassenhaus_kills_relators
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    S.map
    (D.RelatorTargetDepth S)
  · exact D.relator_target_depth
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed
  · exact S.toRShadow.relator_killed

/--
Every actual surjective finite `3`-group relator quotient lies above one
canonical Zassenhaus finite-layer relator quotient.
-/
lemma zassenhaus_relator_kernel
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    ∃ n : ℕ, (D.ZassenhausRelatorQuotient n).map.ker ≤ S.map.ker := by
  exact ⟨D.RelatorTargetDepth S,
    D.finTargetDepth
      S⟩

/--
At the common target depth of one finite family of actual surjective finite
`3`-group relator quotients, the canonical Zassenhaus finite-layer relator
quotient lies above the family's canonical common refinement.
-/
lemma commonTargetDepth
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    (D.ZassenhausRelatorQuotient
      (D.FamilyCommonTarget shadows)).map.ker ≤
      (D.RelatorCommonRefinement shadows).map.ker := by
  exact D.finTargetDepth
    (D.RelatorCommonRefinement shadows)

/--
At the common target depth of one finite quotient family, the canonical
Zassenhaus finite-layer relator quotient lies above every quotient in the
family.
-/
lemma zassenhaus_target_depth
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows) :
    (D.ZassenhausRelatorQuotient
      (D.FamilyCommonTarget shadows)).map.ker ≤
      S.map.ker := by
  exact (D.commonTargetDepth
    shadows).trans
      (D.common_refinement_kernel shadows S hS)

/--
Every finite family of actual surjective finite `3`-group relator quotients is
simultaneously dominated by one canonical Zassenhaus finite-layer relator
quotient.
-/
lemma zassenhaus_relator_family
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    ∃ n : ℕ, ∀ S ∈ shadows,
      (D.ZassenhausRelatorQuotient n).map.ker ≤ S.map.ker := by
  exact ⟨D.FamilyCommonTarget shadows,
    D.zassenhaus_target_depth
      shadows⟩

/--
Every canonical Zassenhaus finite-layer relator quotient factors continuously
and uniquely through the actual initial Koch quotient.
-/
def ContinuouslyUniquelyThrough
    (D : KRData) :
    Prop :=
  ∀ n : ℕ,
    ContinuouslyFactorsUniquely initialKochQuotient
      (D.ZassenhausRelatorQuotient n).map

/--
A canonical Zassenhaus finite-layer relator quotient counterexample is one
initial Koch kernel element surviving in one quotient of the canonical
Zassenhaus relator quotient tower.
-/
def ZassenhausRelatorCounterexample
    (D : KRData) :
    Prop :=
  ∃ n : ℕ, ∃ x : initialKochFree.Carrier,
    x ∈ initialKochQuotient.ker ∧
      x ∉ (D.ZassenhausRelatorQuotient n).map.ker

/--
The concrete finite quotient Koch factorization theorem is equivalent to
testing the initial Koch kernel only against the directed canonical tower of
Zassenhaus finite-layer relator quotients.
-/
lemma fin_factorization_forall
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, initialKochQuotient.ker ≤
        (D.ZassenhausRelatorQuotient n).map.ker := by
  calc
    D.KochFactorizationTheorem ↔
        D.KochFactorizationTheorem :=
      D.factorization_theorem_statement
    _ ↔ QuotientFactorizationProperty 3 D.fiveRelatorFamily.relator
        initialKochQuotient :=
      Towers.TFFact.fin_statement_property
        D.fiveRelatorFamily initialKochQuotient
    _ ↔ QuotientFactorizationProperty 3
        (initialTameRelator D.frobeniusLift) initialKochQuotient := by
      rw [D.five_relator_family]
    _ ↔ ∀ n : ℕ, initialKochQuotient.ker ≤
        (D.ZassenhausRelatorQuotient n).map.ker :=
      OCQuotie.property_kernels_pro
        initialKochFree.isProP
        initialKochFree.generator
        initialKochFree.dense_generator
        initialKochQuotient

/--
The concrete finite quotient Koch factorization theorem is equivalent to
continuous unique factorization only for the directed canonical tower of
Zassenhaus finite-layer relator quotients.
-/
lemma fin_unique_through
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.ContinuouslyUniquelyThrough := by
  rw [D.fin_factorization_forall]
  exact forall_congr' fun n =>
    (RCFact.continuously_uniquely_ker
      initialKochQuotient
      (D.ZassenhausRelatorQuotient n).map
      initial_koch
      (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.map_continuous).symm

/--
Failure of the concrete finite quotient Koch factorization theorem is witnessed
by one actual canonical Zassenhaus finite-layer relator quotient
counterexample.
-/
lemma not_fin_counterexample
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      D.ZassenhausRelatorCounterexample := by
  rw [D.fin_factorization_forall]
  simp only [ZassenhausRelatorCounterexample, not_forall,
    SetLike.not_le_iff_exists]

end KRData

end TBluepr
end Towers
