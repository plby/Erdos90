import Towers.FieldTheory.QuotientKoch.FiniteQuotientFactorization
import Towers.Group.OpenRelators.Cofinality


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCofina

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace IRScaffo

universe u v w

namespace KECert

/--
A relation-word certificate in a finer open-normal quotient remains a
certificate in every coarser open-normal quotient.
-/
def coarsen
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {M N : OpenNormalSubgroup F}
    {x : F}
    (hMN : (M : Subgroup F) ≤ N)
    (C : KECert q relator M x) :
    KECert q relator N x where
  word := C.word
  quotient_value_eq := by
    simpa [IGScaffoa.quotientMap] using
      ONCofina.of_eq_le hMN
        C.quotient_value_eq

end KECert

namespace ORCert

/--
A certificate for every kernel element in a finer open-normal quotient
coarsens to a certificate for every kernel element in a coarser quotient.
-/
def coarsen
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (C : ORCert q relator M) :
    ORCert q relator N where
  wordFor := fun x hx => (C.wordFor x hx).coarsen hMN

end ORCert

/--
Pointwise relation-word certificates for every kernel element in every
open-normal quotient.
-/
def PointwiseCertificatesEvery
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F) :
    Prop :=
  ∀ (N : OpenNormalSubgroup F) (x : F), x ∈ q.ker →
    Nonempty (KECert q relator N x)

/--
Pointwise relation-word certificates restricted to one indexed open-normal
family.
-/
def PointwiseCertificatesAlong
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {κ : Type*}
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F) :
    Prop :=
  ∀ (k : κ) (x : F), x ∈ q.ker →
    Nonempty (KECert q relator (B k) x)

/--
A cofinal open-normal family is enough to build pointwise relation-word
certificates in every open-normal quotient.
-/
lemma pointwise_certificates_along
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {κ : Type*}
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F)
    (hB : ONCofina.CofinalOpenFamily B) :
    PointwiseCertificatesEvery q relator ↔
      PointwiseCertificatesAlong q relator B := by
  constructor
  · intro h k x hx
    exact h (B k) x hx
  · intro h N x hx
    rcases hB N with ⟨k, hk⟩
    rcases h k x hx with ⟨C⟩
    exact ⟨C.coarsen hk⟩

/--
The algebraic finite-shadow predicate is exactly pointwise existence of
relation-word certificates in every open-normal quotient.
-/
lemma algebraically_every_certificates
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F) :
    GeneratedAlgebraicallyEvery q relator ↔
      PointwiseCertificatesEvery q relator := by
  constructor
  · intro h N x hx
    exact ⟨KECert.quotient_relation_subgroup
      q relator N x (h N x hx)⟩
  · exact algebraically_every_words

/--
The algebraic finite-shadow predicate can be proved by relation-word
certificates only on any cofinal open-normal family.
-/
lemma algebraically_certificates_along
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {κ : Type*}
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F)
    (hB : ONCofina.CofinalOpenFamily B) :
    GeneratedAlgebraicallyEvery q relator ↔
      PointwiseCertificatesAlong q relator B := by
  rw [algebraically_every_certificates]
  exact pointwise_certificates_along
    q relator B hB

end IRScaffo

namespace KRData

/-- The canonical open-normal `n`th Zassenhaus layer of the initial free pro-`3` group. -/
abbrev zassenhausOpenSubgroup
    (n : ℕ) :
    OpenNormalSubgroup initialKochFree.Carrier :=
  ONCofina.zassenhausOpenNormal
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    n

/-- A relation-word certificate for one Koch-kernel element at one Zassenhaus depth. -/
abbrev ZassenhausRelationCertificate
    (D : KRData)
    (n : ℕ)
    (x : initialKochFree.Carrier) :=
  KECert
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    x

/-- Pointwise relation-word certificates at one fixed Zassenhaus depth. -/
def PointwiseCertificatesDepth
    (D : KRData)
    (n : ℕ) :
    Prop :=
  ∀ x : initialKochFree.Carrier, x ∈ initialKochQuotient.ker →
    Nonempty (D.ZassenhausRelationCertificate n x)

/--
Pointwise relation-word certificates only in the canonical Zassenhaus finite
layers of the initial free pro-`3` group.
-/
def PointwiseRelationCertificates
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, D.PointwiseCertificatesDepth n

lemma certificates_along_family
    (D : KRData) :
    D.PointwiseRelationCertificates ↔
      PointwiseCertificatesAlong
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (ONCofina.zassenhausOpenNormal
          initialKochFree.isProP
          initialKochFree.generator
          initialKochFree.dense_generator) := by
  rfl

/--
The concrete finite quotient Koch theorem is exactly the relation-word
certificate problem in the canonical Zassenhaus finite layers.
-/
lemma theorem_pointwise_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.PointwiseRelationCertificates := by
  rw [D.theorem_algebraic_shadows]
  rw [D.certificates_along_family]
  exact
    (IRScaffo.algebraically_certificates_along
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (ONCofina.zassenhausOpenNormal
        initialKochFree.isProP
        initialKochFree.generator
        initialKochFree.dense_generator)
      (ONCofina.open_normal_cofinal
        initialKochFree.isProP
        initialKochFree.generator
        initialKochFree.dense_generator))

/--
Depthwise form of the remaining certificate problem: prove one explicit
Zassenhaus-layer relation-word theorem for each depth.
-/
lemma theorem_forall_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, D.PointwiseCertificatesDepth n := by
  exact
    D.theorem_pointwise_certificates

end KRData

end TBluepr
end Towers
