import Submission.FieldTheory.QuotientKoch.SurjectiveCertificates


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
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
The canonical common refinement of a finite list of actual surjective finite
`3`-group relator quotients.
-/
abbrev RelatorCommonRefinement
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :=
  RQShadow.infList shadows

/--
The least canonical Zassenhaus depth whose finite layer lies inside the kernel
of the canonical common refinement of one finite family of actual surjective
finite `3`-group relator quotients.
-/
abbrev FamilyCommonTarget
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :=
  D.ThreeTargetDepth
    (D.RelatorCommonRefinement shadows).map
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.map_continuous
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.target_p_group
    (D.RelatorCommonRefinement shadows).toRShadow.relator_killed

/--
One finite quotient family has its canonical common target depth verified when
the actual candidate-kernel image is covered by tame Koch relation words at the
canonical relation-word radius in that one Zassenhaus layer.
-/
def CommonTargetVerified
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    Prop :=
  D.ImageCoveredRadius
    (D.FamilyCommonTarget shadows)

/--
One finite quotient family has a raw common-target-depth certifying table when
the canonical common target Zassenhaus layer carries a bounded relation-word
table satisfying the finite certificate equations at its canonical radius.
-/
def CommonCertifyingTable
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    Prop :=
  ∃ table : BoundedRelationTable
      (D.FamilyCommonTarget shadows)
      (D.ZassenhausRelationRadius
        (D.FamilyCommonTarget shadows)),
    D.BoundedTableCertifies
      (D.FamilyCommonTarget shadows)
      (D.ZassenhausRelationRadius
        (D.FamilyCommonTarget shadows))
      table

/--
One finite list of actual surjective finite `3`-group relator quotients has a
common certified kernel layer when its canonical common refinement has a
certified kernel-contained Zassenhaus finite layer.
-/
abbrev CommonCertifiedLayer
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :=
  D.RelatorCertifiedLayer
    (D.RelatorCommonRefinement shadows)

/--
One finite list of actual surjective finite `3`-group relator quotients has a
common raw certifying table kernel layer when its canonical common refinement
has a raw certifying bounded relation-word table in a kernel-contained
Zassenhaus finite layer.
-/
abbrev CertifyingRelationTable
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :=
  D.CertifyingTableLayer
    (D.RelatorCommonRefinement shadows)

/--
A common certified kernel layer for a finite quotient family is exactly a common
raw certifying-table kernel layer.
-/
lemma fin_table_layer
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    D.CommonCertifiedLayer shadows ↔
      D.CertifyingRelationTable shadows :=
        by
  exact D.fin_table_kernel
    (D.RelatorCommonRefinement shadows)

/--
Every quotient in a finite family lies above the kernel of the canonical common
refinement.
-/
lemma common_refinement_kernel
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows) :
    (D.RelatorCommonRefinement shadows).map.ker ≤ S.map.ker := by
  exact RQShadow.inf_list_kernel shadows S hS

/--
The canonical common target Zassenhaus layer of a finite quotient family lies
inside the kernel of its canonical common refinement.
-/
lemma openCommonTarget
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    (zassenhausOpenSubgroup
        (D.FamilyCommonTarget shadows) :
      Subgroup initialKochFree.Carrier) ≤
      (D.RelatorCommonRefinement shadows).map.ker := by
  exact D.relator_target_depth
    (D.RelatorCommonRefinement shadows).map
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.map_continuous
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.target_p_group
    (D.RelatorCommonRefinement shadows).toRShadow.relator_killed

/--
The canonical common target Zassenhaus layer of a finite quotient family lies
inside the kernel of every quotient in the family.
-/
lemma normal_target_depth
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows) :
    (zassenhausOpenSubgroup
        (D.FamilyCommonTarget shadows) :
      Subgroup initialKochFree.Carrier) ≤ S.map.ker := by
  exact (D.openCommonTarget
    shadows).trans
      (D.common_refinement_kernel shadows S hS)

/--
Verification at the canonical common target depth of a finite quotient family
is exactly existence of one raw certifying relation-word table at that depth.
-/
lemma verified_certifying_table
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient) :
    D.CommonTargetVerified shadows ↔
      D.CommonCertifyingTable shadows :=
        by
  exact D.image_bounded_table
    (D.FamilyCommonTarget shadows)

/--
Certified kernel-layer witnesses descend along enlargement of the target
quotient kernel: a certificate for a finer quotient is also a certificate for
every coarser quotient.
-/
lemma relator_certified_layer
    (D : KRData)
    (S T : D.ThreeRelatorQuotient)
    (hker : S.map.ker ≤ T.map.ker)
    (hcertified : D.RelatorCertifiedLayer S) :
    D.RelatorCertifiedLayer T := by
  rcases hcertified with ⟨n, hN, C⟩
  exact ⟨n, hN.trans hker, C⟩

/--
Raw certifying-table kernel-layer witnesses descend along enlargement of the
target quotient kernel.
-/
lemma certifying_relation_table
    (D : KRData)
    (S T : D.ThreeRelatorQuotient)
    (hker : S.map.ker ≤ T.map.ker)
    (htable : D.CertifyingTableLayer S) :
    D.CertifyingTableLayer T := by
  rcases htable with ⟨n, hN, table, htable⟩
  exact ⟨n, hN.trans hker, table, htable⟩

/--
Verification at the canonical common target depth gives a common certified
kernel-contained Zassenhaus finite layer for the whole quotient family.
-/
lemma common_certified_verified
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (hverified : D.CommonTargetVerified shadows) :
    D.CommonCertifiedLayer shadows := by
  exact ⟨D.FamilyCommonTarget shadows,
    D.openCommonTarget
      shadows,
    (D.image_relation_certificate
      (D.FamilyCommonTarget shadows)).mp hverified⟩

/--
A raw certifying table at the canonical common target depth gives a common raw
certifying-table kernel layer for the whole quotient family.
-/
lemma fin_certifying_table
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (htable : D.CommonCertifyingTable
      shadows) :
    D.CertifyingRelationTable shadows := by
  exact ⟨D.FamilyCommonTarget shadows,
    D.openCommonTarget
      shadows,
    htable⟩

/--
A common certified kernel layer for a finite quotient family gives continuous
unique factorization of every quotient in that family through the actual
initial Koch quotient.
-/
lemma fin_common_certified
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows)
    (hcertified : D.CommonCertifiedLayer shadows) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  apply RCFact.continuously_through_ker
    initialKochQuotient
    S.map
    initial_koch
    S.toRShadow.toShadow.map_continuous
  exact (RCFact.continuously_uniquely_ker
    initialKochQuotient
    (D.RelatorCommonRefinement shadows).map
    initial_koch
    (D.RelatorCommonRefinement
      shadows).toRShadow.toShadow.map_continuous).mp
      (D.continuously_uniquely_certified
        (D.RelatorCommonRefinement shadows)
        hcertified) |>.trans
        (D.common_refinement_kernel shadows S hS)

/--
A common raw certifying bounded relation-word table for a finite quotient family
gives continuous unique factorization of every quotient in that family through
the actual initial Koch quotient.
-/
lemma fin_relator_table
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows)
    (htable : D.CertifyingRelationTable
      shadows) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  apply D.fin_common_certified
    shadows S hS
  exact (D.fin_table_layer
    shadows).mpr htable

/--
Verification at the canonical common target depth of a finite quotient family
gives continuous unique factorization of every quotient in that family through
the actual initial Koch quotient.
-/
lemma common_target_verified
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows)
    (hverified : D.CommonTargetVerified shadows) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  apply D.fin_common_certified
    shadows S hS
  exact D.common_certified_verified
    shadows hverified

/--
A raw certifying relation-word table at the canonical common target depth of a
finite quotient family gives continuous unique factorization of every quotient
in that family through the actual initial Koch quotient.
-/
lemma relator_certifying_table
    (D : KRData)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows)
    (htable : D.CommonCertifyingTable
      shadows) :
    ContinuouslyFactorsUniquely initialKochQuotient S.map := by
  apply D.common_target_verified
    shadows S hS
  exact
    (D.verified_certifying_table
    shadows).mpr htable

/--
The concrete finite quotient Koch factorization theorem implies a common
certified kernel-contained Zassenhaus finite layer for every finite family of
actual surjective finite `3`-group relator quotients.
-/
lemma fin_certified_factorization
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (shadows : List D.ThreeRelatorQuotient) :
    D.CommonCertifiedLayer shadows := by
  exact (D.quotients_have_certified.mp
    hfactor) (D.RelatorCommonRefinement shadows)

/--
The concrete finite quotient Koch factorization theorem implies one common raw
certifying bounded relation-word table in a kernel-contained Zassenhaus finite
layer for every finite family of actual surjective finite `3`-group relator
quotients.
-/
lemma fin_relator_factorization
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (shadows : List D.ThreeRelatorQuotient) :
    D.CertifyingRelationTable shadows := by
  exact (D.fin_table_layer
    shadows).mp
      (D.fin_certified_factorization
        hfactor shadows)

/--
The concrete finite quotient Koch factorization theorem is equivalent to common
certified kernel-contained Zassenhaus finite layers for every finite family of
actual surjective finite `3`-group relator quotients.
-/
lemma forall_common_certified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ shadows : List D.ThreeRelatorQuotient,
        D.CommonCertifiedLayer shadows := by
  constructor
  · exact D.fin_certified_factorization
  · intro hfamilies
    apply D.quotients_have_certified.mpr
    intro S
    apply D.relator_certified_layer
      (D.RelatorCommonRefinement [S]) S
      (D.common_refinement_kernel [S] S (by simp))
    exact hfamilies [S]

/--
The concrete finite quotient Koch factorization theorem is equivalent to common
raw certifying bounded relation-word tables in kernel-contained Zassenhaus
finite layers for every finite family of actual surjective finite `3`-group
relator quotients.
-/
lemma factorization_forall_table
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ shadows : List D.ThreeRelatorQuotient,
        D.CertifyingRelationTable shadows :=
          by
  rw [D.forall_common_certified]
  exact forall_congr' fun shadows =>
    D.fin_table_layer
      shadows

/--
Every finite family of actual surjective finite `3`-group relator quotients has
its one canonical common target Zassenhaus depth verified.
-/
def CommonDepthsVerified
    (D : KRData) :
    Prop :=
  ∀ shadows : List D.ThreeRelatorQuotient,
    D.CommonTargetVerified shadows

/--
Every finite family of actual surjective finite `3`-group relator quotients has
one raw certifying relation-word table at its canonical common target depth.
-/
def DepthsHaveTables
    (D : KRData) :
    Prop :=
  ∀ shadows : List D.ThreeRelatorQuotient,
    D.CommonCertifyingTable shadows

/--
The concrete finite quotient Koch factorization theorem is equivalent to
canonical-radius verification only at the one common target Zassenhaus depth
attached to each finite family of actual surjective finite `3`-group relator
quotients.
-/
lemma common_depths_verified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.CommonDepthsVerified := by
  constructor
  · intro hfactor shadows
    exact (D.fin_factorization_radius.mp
      hfactor) (D.FamilyCommonTarget shadows)
  · intro hverified
    apply D.forall_common_certified.mpr
    intro shadows
    exact
      D.common_certified_verified
      shadows (hverified shadows)

/--
The concrete finite quotient Koch factorization theorem is equivalent to raw
certifying bounded relation-word tables only at the one common target
Zassenhaus depth attached to each finite family of actual surjective finite
`3`-group relator quotients.
-/
lemma fin_certifying_tables
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.DepthsHaveTables := by
  rw [D.common_depths_verified]
  exact forall_congr' fun shadows =>
    D.verified_certifying_table
      shadows

end KRData

end TBluepr
end Submission
