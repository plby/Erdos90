import Towers.FieldTheory.QuotientKoch.TargetDepths


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

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
An actual surjective continuous finite `3`-group quotient of the initial free
pro-`3` source killing the five displayed tame Koch relators.
-/
abbrev ThreeRelatorQuotient
    (D : KRData) :=
  RQShadow 3 initialKochFree.Carrier
    (initialTameRelator D.frobeniusLift)

/--
One actual finite `3`-group relator quotient has a certified kernel layer when
some canonical Zassenhaus finite layer inside its kernel carries one bounded
quotient-level tame Koch relation-word certificate at its canonical radius.
-/
abbrev RelatorCertifiedLayer
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :=
  D.CertifiedKernelLayer S.map

/--
One actual finite `3`-group relator quotient has a raw certifying table kernel
layer when some canonical Zassenhaus finite layer inside its kernel carries one
raw bounded quotient-level tame Koch relation-word table satisfying the finite
certificate equations at its canonical radius.
-/
abbrev CertifyingTableLayer
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :=
  D.RelatorCertifyingTable S.map

/--
Every actual surjective continuous finite `3`-group relator quotient has some
certified kernel-contained Zassenhaus finite layer.
-/
def QuotientsHaveCertified
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    D.RelatorCertifiedLayer S

/--
Every actual surjective continuous finite `3`-group relator quotient has some
raw certifying bounded relation-word table in a kernel-contained Zassenhaus
finite layer.
-/
def HaveCertifyingTable
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    D.CertifyingTableLayer S

/--
Every actual surjective continuous finite `3`-group relator quotient factors
continuously and uniquely through the actual initial Koch quotient.
-/
def QuotientsContinuouslyThrough
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    ContinuouslyFactorsUniquely initialKochQuotient S.map

/--
For one actual finite `3`-group relator quotient, certified and raw
certifying-table kernel layers are equivalent formulations.
-/
lemma fin_table_kernel
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    D.RelatorCertifiedLayer S ↔
      D.CertifyingTableLayer S := by
  exact (D.relator_verified_certified S.map).symm.trans
    (D.fin_three_table S.map)

/--
A certified kernel-contained Zassenhaus finite layer for one actual finite
`3`-group relator quotient gives continuous unique factorization of that
quotient through the actual initial Koch quotient.
-/
lemma continuously_uniquely_certified
    (D : KRData)
    (S : D.ThreeRelatorQuotient)
    (hcertified : D.RelatorCertifiedLayer S) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  exact D.uniquely_through_certified
    S.map
    S.toRShadow.toShadow.map_continuous
    S.toRShadow.toShadow.target_p_group
    S.toRShadow.relator_killed
    hcertified

/--
A raw certifying bounded relation-word table in a kernel-contained Zassenhaus
finite layer for one actual finite `3`-group relator quotient gives continuous
unique factorization through the actual initial Koch quotient.
-/
lemma certifying_table_layer
    (D : KRData)
    (S : D.ThreeRelatorQuotient)
    (htable : D.CertifyingTableLayer S) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  exact D.relator_table_layer
    S.map
    S.toRShadow.toShadow.map_continuous
    S.toRShadow.toShadow.target_p_group
    S.toRShadow.relator_killed
    htable

/--
The arbitrary finite-map certified kernel-layer criterion is equivalent to the
same criterion restricted to actual surjective finite relator quotients.
-/
lemma all_have_certified
    (D : KRData) :
    D.AllHaveCertified ↔
      D.QuotientsHaveCertified := by
  constructor
  · intro hmaps S
    exact hmaps S.map S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group S.toRShadow.relator_killed
  · intro hquot P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    have hS : D.RelatorCertifiedLayer S :=
      hquot S
    rcases hS with ⟨n, hN, C⟩
    exact ⟨n, by simpa [S] using hN, C⟩

/--
The arbitrary finite-map raw certifying-table kernel-layer criterion is
equivalent to the same criterion restricted to actual surjective finite
relator quotients.
-/
lemma all_fin_table
    (D : KRData) :
    D.AllHaveCertifying ↔
      D.HaveCertifyingTable := by
  constructor
  · intro hmaps S
    exact hmaps S.map S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group S.toRShadow.relator_killed
  · intro hquot P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    have hS : D.CertifyingTableLayer S :=
      hquot S
    rcases hS with ⟨n, hN, table, htable⟩
    exact ⟨n, by simpa [S] using hN, table, htable⟩

/--
The concrete finite quotient Koch factorization theorem is equivalent to
certified kernel-contained Zassenhaus finite layers for every actual surjective
finite `3`-group relator quotient.
-/
lemma quotients_have_certified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.QuotientsHaveCertified := by
  rw [D.fin_have_certified]
  exact D.all_have_certified

/--
The concrete finite quotient Koch factorization theorem is equivalent to raw
certifying bounded quotient-level relation-word tables in kernel-contained
Zassenhaus finite layers for every actual surjective finite `3`-group relator
quotient.
-/
lemma fin_quotients_table
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.HaveCertifyingTable := by
  rw [D.fin_factorization_table]
  exact D.all_fin_table

/--
The concrete finite quotient Koch factorization theorem is equivalent to
continuous unique factorization of every actual surjective finite `3`-group
relator quotient through the actual initial Koch quotient.
-/
lemma factorization_unique_through
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.QuotientsContinuouslyThrough := by
  constructor
  · intro hfactor S
    apply RCFact.continuously_through_ker
      initialKochQuotient
      S.map
      initial_koch
      S.toRShadow.toShadow.map_continuous
    exact hfactor S.map S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group S.toRShadow.relator_killed
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    have hS : initialKochQuotient.ker ≤ S.map.ker :=
      (RCFact.continuously_uniquely_ker
        initialKochQuotient
        S.map
        initial_koch
        S.toRShadow.toShadow.map_continuous).mp (hfactor S)
    simpa [S, RQShadow.relator_shadow_range] using hS

end KRData

end TBluepr
end Towers
