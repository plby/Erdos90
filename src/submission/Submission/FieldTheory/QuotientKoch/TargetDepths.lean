import Submission.FieldTheory.QuotientKoch.LayerWordRadius
import Submission.Group.OpenRelators.TargetLayers
import Submission.Group.FinitePRelator.ContinuousFactorization


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar
open OTLayers
open RCFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The actual initial Koch quotient map is a topological quotient map: it is a
continuous surjection from the compact free pro-`3` source to the Hausdorff
initial Galois target.
-/
lemma initial_koch :
    Topology.IsQuotientMap initialKochQuotient := by
  exact RCFact.surjective_t_space
    initialKochQuotient
    initial_quotient_surjective
    initial_quotient_continuous

/--
The least canonical Zassenhaus depth whose finite layer lies inside the kernel
of one actual continuous finite `3`-group map killing the five tame Koch
relators.
-/
abbrev ThreeTargetDepth
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :=
  OTLayers.targetDepthRelator
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    α
    hα
    hP
    hkill

/--
The canonical target Zassenhaus layer of one actual continuous finite `3`-group
map killing the five tame Koch relators lies inside that map's kernel.
-/
lemma relator_target_depth
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1) :
    (zassenhausOpenSubgroup
        (D.ThreeTargetDepth α hα hP hkill) :
      Subgroup initialKochFree.Carrier) ≤ α.ker := by
  exact OTLayers.openFinRelator
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    α
    hα
    hP
    hkill

/--
Every canonical Zassenhaus layer at or deeper than the target depth of one
actual continuous finite `3`-group relator map lies inside that map's kernel.
-/
lemma open_target_depth
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    {n : ℕ}
    (htarget : D.ThreeTargetDepth α hα hP hkill ≤ n) :
    (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤ α.ker := by
  exact OTLayers.open_normal_relator
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    α
    hα
    hP
    hkill
    htarget

/--
Verification at the canonical target Zassenhaus depth of one actual continuous
finite `3`-group relator map forces the initial Koch kernel into that map's
kernel.
-/
lemma ker_target_verified
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hverified : D.ImageCoveredRadius
      (D.ThreeTargetDepth α hα hP hkill)) :
    initialKochQuotient.ker ≤ α.ker := by
  let n := D.ThreeTargetDepth α hα hP hkill
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  have hgen :
      ONFact.GeneratedAlgebraicallyOpen
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n) :=
    (algebraically_open_radius
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)).mpr hverified
  exact OTLayers.fin_p_relator
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    α
    hα
    hP
    hkill
    hgen

/--
Verification at the canonical target Zassenhaus depth of one actual continuous
finite `3`-group relator map gives unique factorization of that map through the
surjective initial Koch quotient.
-/
lemma uniquely_through_verified
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hverified : D.ImageCoveredRadius
      (D.ThreeTargetDepth α hα hP hkill)) :
    PRFact.FactorsUniquelyThrough initialKochQuotient α := by
  apply PRFact.factors_uniquely_ker
    initialKochQuotient α initial_quotient_surjective
  exact D.ker_target_verified α hα hP hkill hverified

/--
Verification at the canonical target Zassenhaus depth of one actual continuous
finite `3`-group relator map gives continuous unique factorization through the
actual initial Koch quotient.
-/
lemma continuously_uniquely_verified
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hverified : D.ImageCoveredRadius
      (D.ThreeTargetDepth α hα hP hkill)) :
    RCFact.ContinuouslyFactorsUniquely
      initialKochQuotient α := by
  apply RCFact.continuously_through_ker
    initialKochQuotient
    α
    initial_koch
    hα
  exact D.ker_target_verified α hα hP hkill hverified

/--
At one canonical Zassenhaus depth, canonical-radius candidate-kernel-image
coverage is exactly existence of one bounded quotient-level relation-word
certificate at that canonical radius.
-/
lemma image_relation_certificate
    (D : KRData)
    (n : ℕ) :
    D.ImageCoveredRadius n ↔
      Nonempty (D.BoundedRelationCertificate n
        (D.ZassenhausRelationRadius n)) := by
  exact covered_nonempty_certificate
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    (D.ZassenhausRelationRadius n)

/--
At one canonical Zassenhaus depth, canonical-radius candidate-kernel-image
coverage is exactly existence of one raw bounded quotient-level relation-word
table satisfying the finite certificate equations at that canonical radius.
-/
lemma image_bounded_table
    (D : KRData)
    (n : ℕ) :
    D.ImageCoveredRadius n ↔
      ∃ table : BoundedRelationTable n
          (D.ZassenhausRelationRadius n),
        D.BoundedTableCertifies n
          (D.ZassenhausRelationRadius n)
          table := by
  exact covered_certifying_table
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    (D.ZassenhausRelationRadius n)

/--
One actual continuous finite `3`-group relator map has a verified kernel layer
when some canonical Zassenhaus finite layer inside its kernel has
canonical-radius tame Koch relation-word coverage.
-/
def RelatorVerifiedLayer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P) :
    Prop :=
  ∃ n : ℕ,
    (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤ α.ker ∧
      D.ImageCoveredRadius n

/--
One actual continuous finite `3`-group relator map has a certified kernel layer
when some canonical Zassenhaus finite layer inside its kernel carries one
bounded quotient-level relation-word certificate at its canonical radius.
-/
def CertifiedKernelLayer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P) :
    Prop :=
  ∃ n : ℕ,
    (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤ α.ker ∧
      Nonempty (D.BoundedRelationCertificate n
        (D.ZassenhausRelationRadius n))

/--
One actual continuous finite `3`-group relator map has a certifying table kernel
layer when some canonical Zassenhaus finite layer inside its kernel carries one
raw bounded quotient-level relation-word table satisfying the certificate
equations at its canonical radius.
-/
def RelatorCertifyingTable
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P) :
    Prop :=
  ∃ n : ℕ,
    (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤ α.ker ∧
      ∃ table : BoundedRelationTable n
          (D.ZassenhausRelationRadius n),
        D.BoundedTableCertifies n
          (D.ZassenhausRelationRadius n)
          table

/--
For one actual continuous finite `3`-group relator map, verified and certified
kernel layers are equivalent formulations of the same finite-layer witness.
-/
lemma relator_verified_certified
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P) :
    D.RelatorVerifiedLayer α ↔
      D.CertifiedKernelLayer α := by
  exact exists_congr fun n => and_congr Iff.rfl
    (D.image_relation_certificate n)

/--
For one actual continuous finite `3`-group relator map, verified kernel layers
and raw certifying-table kernel layers are equivalent finite-layer witnesses.
-/
lemma fin_three_table
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P) :
    D.RelatorVerifiedLayer α ↔
      D.RelatorCertifyingTable α := by
  exact exists_congr fun n => and_congr Iff.rfl
    (D.image_bounded_table n)

/--
A verified kernel-contained Zassenhaus finite layer for one actual continuous
finite `3`-group relator map forces the initial Koch kernel into that map's
kernel.
-/
lemma ker_verified_layer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (_hα : Continuous α)
    (_hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hverified : D.RelatorVerifiedLayer α) :
    initialKochQuotient.ker ≤ α.ker := by
  rcases hverified with ⟨n, hN, hcover⟩
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  have hgen :
      ONFact.GeneratedAlgebraicallyOpen
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n) :=
    (algebraically_open_radius
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)).mpr hcover
  exact OTLayers.kernel_kills_relators
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    α
    (zassenhausOpenSubgroup n)
    hN
    hgen
    hkill

/--
A certified kernel-contained Zassenhaus finite layer for one actual continuous
finite `3`-group relator map forces the initial Koch kernel into that map's
kernel.
-/
lemma ker_certified_layer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hcertified : D.CertifiedKernelLayer α) :
    initialKochQuotient.ker ≤ α.ker := by
  apply D.ker_verified_layer α hα hP hkill
  exact (D.relator_verified_certified
    α).mpr hcertified

/--
A certified kernel-contained Zassenhaus finite layer gives unique factorization
of one actual continuous finite `3`-group relator map through the surjective
initial Koch quotient.
-/
lemma uniquely_certified_layer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hcertified : D.CertifiedKernelLayer α) :
    PRFact.FactorsUniquelyThrough initialKochQuotient α := by
  apply PRFact.factors_uniquely_ker
    initialKochQuotient α initial_quotient_surjective
  exact D.ker_certified_layer
    α hα hP hkill hcertified

/--
A raw certifying bounded relation-word table in a kernel-contained Zassenhaus
finite layer gives continuous unique factorization of one actual continuous
finite `3`-group relator map through the actual initial Koch quotient.
-/
lemma relator_table_layer
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (htable : D.RelatorCertifyingTable α) :
    RCFact.ContinuouslyFactorsUniquely
      initialKochQuotient α := by
  apply RCFact.continuously_through_ker
    initialKochQuotient
    α
    initial_koch
    hα
  apply D.ker_verified_layer α hα hP hkill
  exact (D.fin_three_table
    α).mpr htable

/--
A certified kernel-contained Zassenhaus finite layer gives continuous unique
factorization of one actual continuous finite `3`-group relator map through the
actual initial Koch quotient.
-/
lemma uniquely_through_certified
    (D : KRData)
    {P : Type}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : initialKochFree.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : ∀ i : Fin 5, α (initialTameRelator D.frobeniusLift i) = 1)
    (hcertified : D.CertifiedKernelLayer α) :
    RCFact.ContinuouslyFactorsUniquely
      initialKochQuotient α := by
  apply RCFact.continuously_through_ker
    initialKochQuotient
    α
    initial_koch
    hα
  exact D.ker_certified_layer
    α hα hP hkill hcertified

/--
Every actual continuous finite `3`-group relator map has some verified
kernel-contained Zassenhaus finite layer.
-/
def AllHaveVerified
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
    D.RelatorVerifiedLayer α

/--
Every actual continuous finite `3`-group relator map has some certified
kernel-contained Zassenhaus finite layer.
-/
def AllHaveCertified
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
    D.CertifiedKernelLayer α

/--
Every actual continuous finite `3`-group relator map has some raw certifying
bounded relation-word table in a kernel-contained Zassenhaus finite layer.
-/
def AllHaveCertifying
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
    D.RelatorCertifyingTable α

/--
The concrete finite quotient Koch factorization theorem is equivalent to
verified kernel-contained Zassenhaus finite layers for every actual continuous
finite `3`-group relator map.
-/
lemma theorem_have_verified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllHaveVerified := by
  constructor
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    let n := D.ThreeTargetDepth α hα hP hkill
    exact ⟨n,
      D.relator_target_depth
        α hα hP hkill,
      (D.fin_factorization_radius.mp
        hfactor) n⟩
  · intro hverified P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    exact D.ker_verified_layer
      α hα hP hkill (hverified α hα hP hkill)

/--
The concrete finite quotient Koch factorization theorem is equivalent to
explicit bounded quotient-level relation-word certificates in some
kernel-contained Zassenhaus finite layer for every actual continuous finite
`3`-group relator map.
-/
lemma fin_have_certified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllHaveCertified := by
  rw
    [D.theorem_have_verified]
  exact forall_congr' fun P => by
    exact forall_congr' fun instGroupP => by
      exact forall_congr' fun instTopologicalSpaceP => by
        exact forall_congr' fun instDiscreteTopologyP => by
          exact forall_congr' fun instFiniteP => by
            exact forall_congr' fun α => forall_congr' fun hα => forall_congr' fun hP =>
              forall_congr' fun hkill =>
                D.relator_verified_certified
                  α

/--
The concrete finite quotient Koch factorization theorem is equivalent to raw
certifying bounded quotient-level relation-word tables in some
kernel-contained Zassenhaus finite layer for every actual continuous finite
`3`-group relator map.
-/
lemma fin_factorization_table
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllHaveCertifying := by
  rw
    [D.theorem_have_verified]
  exact forall_congr' fun P => by
    exact forall_congr' fun instGroupP => by
      exact forall_congr' fun instTopologicalSpaceP => by
        exact forall_congr' fun instDiscreteTopologyP => by
          exact forall_congr' fun instFiniteP => by
            exact forall_congr' fun α => forall_congr' fun hα => forall_congr' fun hP =>
              forall_congr' fun hkill =>
                D.fin_three_table
                  α

/--
Every actual continuous finite `3`-group relator map has a target Zassenhaus
depth whose canonical-radius verification suffices for the desired Koch kernel
containment.
-/
def TargetDepthsVerified
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
    D.ImageCoveredRadius
      (D.ThreeTargetDepth α hα hP hkill)

/--
The concrete finite quotient Koch factorization theorem is equivalent to
canonical-radius verification only at the one target Zassenhaus depth attached
to each actual continuous finite `3`-group relator map.
-/
lemma target_depths_verified
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.TargetDepthsVerified := by
  constructor
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    exact (D.fin_factorization_radius.mp
      hfactor) (D.ThreeTargetDepth α hα hP hkill)
  · intro hverified P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    exact D.ker_target_verified
      α hα hP hkill (hverified α hα hP hkill)

end KRData

end TBluepr
end Submission
