import Submission.FieldTheory.HMRProThree.KernelGeneration
import Submission.FieldTheory.QuotientKoch.FiniteQuotientFactorization
import Submission.FieldTheory.TameThreeKoch

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open STBuild
open KPScaffo
open IGScaffoa
open GSScaffo
open ILScaffo
open IGScaffo
open IRScaffo

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-!
## Generic finite-presentation factorization adapters

The arithmetic leaf below is intentionally pointwise: it produces one
relation word for one kernel element after passage to one open-normal
quotient.  This section proves the algebraic assembly needed to turn that
local witness into a factorization through a finite presented quotient.

Keeping these adapters generic has two benefits.  First, the arithmetic input
cannot accidentally depend on the specialized Koch factorization theorem.
Second, the direction of implication is explicit:

1. a relation word gives mapped ordinary-normal-closure membership;
2. mapped membership gives membership in the join of the relation subgroup
   with the selected open normal subgroup;
3. pointwise membership gives a reverse kernel containment;
4. a surjective map factors any homomorphism whose kernel contains its
   kernel.

Only the first step knows what a relation word is.  Only the last step knows
about surjectivity.  The middle steps are ordinary quotient-group algebra.
-/

namespace PQScaffo

universe u v w z

/--
The subgroup used by a finite presentation shadow: impose the ordinary normal
closure of the displayed relators and one open normal subgroup.
-/
abbrev presentedRelationSubgroup
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Subgroup F :=
  relationSubgroup relator ⊔ N.toSubgroup

/--
The finite presentation shadow obtained from a displayed family of relators
and one open normal subgroup.
-/
abbrev presentedQuotient
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :=
  F ⧸ presentedRelationSubgroup relator N

/--
The ordinary relation subgroup lies in the finite presented relation
subgroup.
-/
lemma relation_subgroup_presented
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    relationSubgroup relator ≤
      presentedRelationSubgroup relator N := by
  exact
    le_sup_left

/--
The selected open normal subgroup lies in the finite presented relation
subgroup.
-/
lemma open_presented_relation
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    N.toSubgroup ≤
      presentedRelationSubgroup relator N := by
  exact
    le_sup_right

/--
The quotient map attached to an open normal subgroup kills that subgroup.
-/
lemma quotient_open_subgroup
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    (N : OpenNormalSubgroup F)
    {x : F}
    (hx : x ∈ N.toSubgroup) :
    IGScaffoa.quotientMap N x =
      1 := by
  exact
    (QuotientGroup.eq_one_iff
      (N := N.toSubgroup)
      x).mpr hx

/--
Conversely, the kernel of the open-normal quotient map is exactly the selected
open normal subgroup.
-/
lemma open_normal_one
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    (N : OpenNormalSubgroup F)
    {x : F}
    (hx :
      IGScaffoa.quotientMap N x =
        1) :
    x ∈ N.toSubgroup := by
  exact
    (QuotientGroup.eq_one_iff
      (N := N.toSubgroup)
      x).mp hx

/--
Equal images in an open-normal quotient mean that the quotient of the two
ambient elements lies in the selected open normal subgroup.
-/
lemma inv_open_normal
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    (N : OpenNormalSubgroup F)
    {left right : F}
    (h :
      IGScaffoa.quotientMap N left =
        IGScaffoa.quotientMap N right) :
    left⁻¹ * right ∈ N.toSubgroup := by
  apply
    open_normal_one N
  rw [map_mul, map_inv, h]
  exact
    inv_mul_cancel _

/--
Mapped ordinary-normal-closure membership lifts to membership in the join of
the relation subgroup with the selected open normal subgroup.

This is the algebraic quotient-reflection step.  It does not use the global
kernel of any map and it does not mention a factorization.
-/
lemma presented_relation_quotient
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    {x : F}
    (hx :
      IGScaffoa.quotientMap N x ∈
        (relationSubgroup relator).map
          (IGScaffoa.quotientMap N)) :
    x ∈ presentedRelationSubgroup relator N := by
  rcases hx with
    ⟨representative, hrepresentative, hquotient⟩
  have hrepresentativeJoin :
      representative ∈
        presentedRelationSubgroup relator N := by
    exact
      relation_subgroup_presented
        relator
        N
        hrepresentative
  have herrorN :
      representative⁻¹ * x ∈ N.toSubgroup := by
    apply
      inv_open_normal N
    exact
      hquotient
  have herrorJoin :
      representative⁻¹ * x ∈
        presentedRelationSubgroup relator N := by
    exact
      open_presented_relation
        relator
        N
        herrorN
  have hproduct :
      representative * (representative⁻¹ * x) ∈
        presentedRelationSubgroup relator N := by
    exact
      (presentedRelationSubgroup relator N).mul_mem
        hrepresentativeJoin
        herrorJoin
  simpa [mul_assoc] using
    hproduct

/--
An explicit pointwise relation-word certificate lifts to the finite presented
relation subgroup.
-/
lemma presented_relation_certificate
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {N : OpenNormalSubgroup F}
    {x : F}
    (C :
      KECert
        q
        relator
        N
        x) :
    x ∈ presentedRelationSubgroup relator N := by
  apply
    presented_relation_quotient
      relator
      N
  exact
    C.relation_subgroup

/--
Pointwise mapped relation-subgroup membership implies the reverse kernel
containment needed by the finite presentation shadow.
-/
lemma presented_pointwise_membership
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (h :
      ∀ x : F, x ∈ q.ker →
        IGScaffoa.quotientMap N x ∈
          (relationSubgroup relator).map
            (IGScaffoa.quotientMap N)) :
    q.ker ≤ presentedRelationSubgroup relator N := by
  intro x hx
  apply
    presented_relation_quotient
      relator
      N
  exact
    h x hx

/--
Pointwise explicit relation words imply the reverse kernel containment needed
by the finite presentation shadow.
-/
lemma presented_pointwise_words
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (h :
      ∀ x : F, x ∈ q.ker →
        Nonempty
          (KECert
            q
            relator
            N
            x)) :
    q.ker ≤ presentedRelationSubgroup relator N := by
  intro x hx
  let C :
      KECert
        q
        relator
        N
        x :=
    Classical.choice (h x hx)
  exact
    presented_relation_certificate
      C

/--
Membership in the finite presented relation subgroup is equivalent to
vanishing under its canonical quotient map.
-/
lemma ker_mk_presented
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    {ι : Type w}
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (x : F) :
    x ∈
        (QuotientGroup.mk'
          (presentedRelationSubgroup relator N)).ker ↔
      x ∈ presentedRelationSubgroup relator N := by
  change
    QuotientGroup.mk'
        (presentedRelationSubgroup relator N) x =
      1 ↔
    x ∈ presentedRelationSubgroup relator N
  exact
    QuotientGroup.eq_one_iff x

/--
A reverse containment into the finite presented relation subgroup is the same
containment into the kernel of the canonical projection.
-/
lemma mk_presented_relation
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (h :
      q.ker ≤ presentedRelationSubgroup relator N) :
    q.ker ≤
      (QuotientGroup.mk'
        (presentedRelationSubgroup relator N)).ker := by
  intro x hx
  rw [
    ker_mk_presented
      relator
      N
      x
  ]
  exact
    h hx

/--
A surjective homomorphism factors any target homomorphism whose kernel
contains its kernel.  This is the generic group-theoretic factor-through-kernel
constructor used by the Koch specialization below.
-/
noncomputable def factorThroughSurjective
    {F : Type u}
    {G : Type v}
    {Q : Type z}
    [Group F]
    [Group G]
    [Group Q]
    (q : F →* G)
    (target : F →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ target.ker) :
    G →* Q :=
  q.liftOfSurjective hq
    ⟨target, hker⟩

/--
The generic factor-through-kernel constructor composes back to the original
target homomorphism.
-/
lemma through_surjective_comp
    {F : Type u}
    {G : Type v}
    {Q : Type z}
    [Group F]
    [Group G]
    [Group Q]
    (q : F →* G)
    (target : F →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ target.ker) :
    (factorThroughSurjective q target hq hker).comp q =
      target := by
  exact
    q.liftOfRightInverse_comp
      (Function.surjInv hq)
      (Function.rightInverse_surjInv hq)
      ⟨target, hker⟩

/--
Reverse kernel containment and surjectivity produce a factorization to the
finite presented quotient.
-/
lemma factor_presented_kernel
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (hq : Function.Surjective q)
    (hker :
      q.ker ≤ presentedRelationSubgroup relator N) :
    ∃ ψ : G →* presentedQuotient relator N,
      ψ.comp q =
        QuotientGroup.mk'
          (presentedRelationSubgroup relator N) := by
  have hker' :
      q.ker ≤
        (QuotientGroup.mk'
          (presentedRelationSubgroup relator N)).ker := by
    exact
      mk_presented_relation
        q
        relator
        N
        hker
  let ψ :
      G →* presentedQuotient relator N :=
    factorThroughSurjective
      q
      (QuotientGroup.mk'
        (presentedRelationSubgroup relator N))
      hq
      hker'
  refine
    ⟨ψ, ?_⟩
  exact
    through_surjective_comp
      q
      (QuotientGroup.mk'
        (presentedRelationSubgroup relator N))
      hq
      hker'

/--
Pointwise explicit relation words and surjectivity produce a factorization to
the finite presented quotient.
-/
lemma pointwise_relation_words
    {F : Type u}
    {G : Type v}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (hq : Function.Surjective q)
    (h :
      ∀ x : F, x ∈ q.ker →
        Nonempty
          (KECert
            q
            relator
            N
            x)) :
    ∃ ψ : G →* presentedQuotient relator N,
      ψ.comp q =
        QuotientGroup.mk'
          (presentedRelationSubgroup relator N) := by
  apply
    factor_presented_kernel
      q
      relator
      N
      hq
  exact
    presented_pointwise_words
      q
      relator
      N
      h

end PQScaffo

open PQScaffo

/--
A choice of local tame relations together with the finite-shadow Koch
certificates that make those specific relations generate the quotient-map
kernel.

The Frobenius lifts are retained in the datum because merely choosing
arbitrary free-group preimages of quotient-side Frobenius elements does not
preserve normal generation.
-/
structure InitialRelationData where
  localRelationData :
    KRData
  rationalSetup :
    RationalKochSetup
      initialRamifiedPrimes
      initialKochFree
      initialKochQuotient
      initialKochPrime
      localRelationData.frobeniusLift
  relationWord_exists :
    ∀ (N : OpenNormalSubgroup initialKochFree.Carrier)
      (x : initialKochFree.Carrier),
      x ∈ initialKochQuotient.ker →
        Nonempty
          (KECert
            initialKochQuotient
            (initialTameRelator
              localRelationData.frobeniusLift)
            N
            x)

/--
The initial ordered Koch generator at index `i` is certified as a tame inertia
generator in every finite layer of the corresponding rational tame
pro-`3` extension.
-/
noncomputable def tameInertiaData
    (i : Fin 5) :
    RationalInertiaData
      initialRamifiedPrimes
      (initialKochPrime i)
      (initialKochQuotient (initialKochFree.generator i)) where
  prime_mem :=
    initial_ramified_primes i
  primeAbove :=
    fun N =>
      (initialInertiaData.finiteLayerData N).primeAbove
        (initialRamifiedOrder i)
  primeAbove_mem :=
    fun N =>
      (initialInertiaData.finiteLayerData N).primeAbove_mem
        (initialRamifiedOrder i)
  primeAbove_comap := by
    intro M N hMN
    simpa [rationalIntegersInclusion,
      rationalTameInclusion,
      initialIntegersInclusion,
      initialKochInclusion] using
      (initialInertiaData.primeAbove_comap
        hMN
        (initialRamifiedOrder i))
  inertiaGenerator :=
    fun N =>
      (initialInertiaData.finiteLayerData N).inertiaGenerator
        (initialRamifiedOrder i)
  mapsFiniteLayer := by
    intro N
    change
      initialKochEquiv N
          (IGScaffoa.quotientMap N
            (initialKochQuotient (initialKochFree.generator i))) =
        ((initialInertiaData.finiteLayerData N).inertiaGenerator
          (initialRamifiedOrder i) :
          Gal(initialKochLayer N / ℚ))
    have hmap :
        IGScaffoa.quotientMap N
            (initialInertiaGenerator (initialRamifiedOrder i)) =
          (initialKochEquiv N).symm
            ((initialInertiaData.finiteLayerData N).inertiaGenerator
              (initialRamifiedOrder i)) := by
      exact
        (initialInertiaData.mapsFiniteLayer
            N
            (initialRamifiedOrder i)).trans
          ((initialInertiaData.finiteLayerData N).generator_eq
            (initialRamifiedOrder i))
    rw [
      initial_koch_generator,
      show
        initialGeneratorData.generator i =
          initialInertiaGenerator (initialRamifiedOrder i) by
          rfl,
      hmap,
      MulEquiv.apply_symm_apply
    ]
  inertiaGenerator_generates :=
    fun N =>
      (initialInertiaData.finiteLayerData N).inertiaGenerator_generates
        (initialRamifiedOrder i)

/--
Arithmetic input three: choose Frobenius lifts for which every finite shadow of
the quotient-map kernel is generated by the resulting five local tame
relations.

This is the Koch arithmetic boundary.  It is existential in the Frobenius
lifts: arbitrary free-group preimages of quotient-side Frobenius elements need
not preserve the normal closure of the resulting relators.
-/
theorem initial_factorization_theorem :
    ∃ (D : KRData)
      (_hsetup :
        RationalKochSetup
          initialRamifiedPrimes
          initialKochFree
          initialKochQuotient
          initialKochPrime
          D.frobeniusLift),
      D.KochFactorizationTheorem := by
  have hprimeRange :
      Finset.univ.image initialKochPrime =
        initialRamifiedPrimes := by
    ext r
    constructor
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨i, _hi, rfl⟩
      exact
        initial_ramified_primes i
    · intro hr
      let s : {s // s ∈ initialRamifiedPrimes} :=
        ⟨r, hr⟩
      rcases initial_ramified_surjective s with
        ⟨i, hi⟩
      refine
        Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, ?_⟩
      unfold initialKochPrime
      exact
        congrArg Subtype.val hi
  have hprimeInjective :
      Function.Injective initialKochPrime := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [initialKochPrime, initialRamifiedOrder] at hij ⊢
  have hbase :
      RationalTameSetup
        initialRamifiedPrimes
        initialKochFree
        initialKochQuotient
        initialKochPrime := by
    refine
      {
        prime_range := hprimeRange
        prime_injective := hprimeInjective
        prime_isPrime := ?_
        prime_mod_three := ?_
        quotientMap_continuous :=
          initial_quotient_continuous
        quotientMap_surjective :=
          initial_quotient_surjective
        target_pro_three := ?_
        generators_tame_inertia :=
          tameInertiaData
      }
    · intro i
      exact
        ramified_primes_prime
          _
          (initial_ramified_primes i)
    · intro i
      exact
        ramified_primes_mod
          _
          (initial_ramified_primes i)
    · change
        ProP.ProPGroup 3 initialGaloisGroup
      exact
        initial_pro_three
  rcases
      rational_shafarevich_factorization
        hbase with
    ⟨frobeniusLift, hsetup, hfactor⟩
  let D : KRData :=
    {
      frobeniusLift := frobeniusLift
      tame_maps_one := by
        intro i
        change
          initialKochQuotient
              (rationalTameRelator
                initialKochFree
                initialKochPrime
                frobeniusLift
                i) =
            1
        exact
          hsetup.tame_maps_one i
    }
  refine
    ⟨D, ?_, ?_⟩
  · exact
      hsetup
  · intro P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
    exact
      hfactor
        α
        hα
        hP
        (by
          intro i
          change
            α (initialTameRelator D.frobeniusLift i) =
              1
          exact
            hkill i)

theorem initial_relation_nonempty :
    Nonempty InitialRelationData := by
  rcases initial_factorization_theorem with
    ⟨D, hsetup, hfactor⟩
  have hcert :
      D.PointwiseLayerCertificates :=
    (D.factorization_pointwise_certificates.mp
      hfactor)
  refine
    ⟨{
      localRelationData := D
      rationalSetup := hsetup
      relationWord_exists := ?_
    }⟩
  exact hcert

/--
A fixed provenance-preserving choice of the five local tame relations and
their finite-shadow Koch certificates.
-/
noncomputable def initialRelationData :
    InitialRelationData :=
  Classical.choice initial_relation_nonempty

/--
The fixed local tame relations are chosen together with their finite-shadow
Koch certificates, rather than as arbitrary free-group preimages.
-/
noncomputable def kochRelationData :
    KRData :=
  initialRelationData.localRelationData

/--
The finite presented relation subgroup obtained by imposing the five local
tame relations together with one open normal subgroup.
-/
abbrev initialKochPresented
    (N : OpenNormalSubgroup initialKochFree.Carrier) :
    Subgroup initialKochFree.Carrier :=
  relationSubgroup
      (initialTameRelator
        kochRelationData.frobeniusLift) ⊔
    N.toSubgroup

/--
The finite quotient presented by the five local tame relations modulo one
open normal subgroup.
-/
abbrev initialPresentedQuotient
    (N : OpenNormalSubgroup initialKochFree.Carrier) :=
  initialKochFree.Carrier ⧸
    initialKochPresented N

/--
For one open-normal finite quotient and one element of the free quotient-map
kernel, exhibit one finite product of conjugates of the five selected local
tame relators and their inverses with the same image in that quotient.
-/
theorem initial_koch_word
    (N : OpenNormalSubgroup initialKochFree.Carrier)
    (x : initialKochFree.Carrier)
    (hx : x ∈ initialKochQuotient.ker) :
    Nonempty
      (KECert
        initialKochQuotient
        (initialTameRelator
          kochRelationData.frobeniusLift)
        N
        x) := by
  exact
    initialRelationData.relationWord_exists
      N
      x
      hx

/--
The pointwise arithmetic leaf implies the reverse kernel containment for one
finite presented quotient.
-/
theorem initial_koch_presented
    (N : OpenNormalSubgroup initialKochFree.Carrier) :
    initialKochQuotient.ker ≤
      initialKochPresented N := by
  apply
    presented_pointwise_words
      initialKochQuotient
      (initialTameRelator
        kochRelationData.frobeniusLift)
      N
  intro x hx
  exact
    initial_koch_word
      N
      x
      hx

/--
Finite Koch realization theorem: after imposing an arbitrary open normal
subgroup, the quotient by the five provenance-preserving local tame
relations factors through the initial Galois group.

This is the exact finite-shadow Koch realization boundary.  It amounts to the
reverse kernel inclusion after passage to every finite presented quotient, so
it requires an independent arithmetic realization theorem.  It is strictly
more informative than pointwise subgroup membership and keeps the finite
presented quotient visible.
-/
theorem initial_presented_factors
    (N : OpenNormalSubgroup initialKochFree.Carrier) :
    ∃ ψ : initialGaloisGroup →*
        initialPresentedQuotient N,
      ψ.comp initialKochQuotient =
        QuotientGroup.mk'
          (initialKochPresented N) := by
  exact
    factor_presented_kernel
      initialKochQuotient
      (initialTameRelator
        kochRelationData.frobeniusLift)
      N
      initial_quotient_surjective
      (initial_koch_presented N)

/--
Finite-layer normal-closure membership input: for one open-normal quotient and
one element in the free quotient-map kernel, the image of that element lies in
the mapped algebraic normal subgroup generated by the five local tame
relators.

This is genuinely smaller than constructing an explicit signed-conjugate word:
it asks only for subgroup membership in one fixed finite quotient.  The
generic relation-word scaffold above performs the constructive extraction.
-/
theorem initial_koch_subgroup
    (N : OpenNormalSubgroup initialKochFree.Carrier)
    (x : initialKochFree.Carrier)
    (hx : x ∈ initialKochQuotient.ker) :
    IGScaffoa.quotientMap N x ∈
      (relationSubgroup
        (initialTameRelator
          kochRelationData.frobeniusLift)).map
        (IGScaffoa.quotientMap N) := by
  exact
    (Classical.choice
      (initial_koch_word
        N
        x
        hx)).relation_subgroup

/--
Arithmetic finite-layer input: in every finite quotient of the free pro-`3`
group, the image of each relation in the kernel of the Koch quotient map is
generated by the images of the five local tame relations.

This is strictly smaller than the global kernel theorem below.  It asks only
for ordinary algebraic normal generation after quotienting by an arbitrary
open normal subgroup.  It contains no topological closure and no inverse-limit
separation argument.
-/
theorem initial_relations_generate :
    GeneratedAlgebraicallyEvery
        initialKochQuotient
        (initialTameRelator
          kochRelationData.frobeniusLift) := by
  apply
    algebraically_every_words
  intro N x hx
  exact
    initial_koch_word N x hx

/--
Arithmetic input three: the five selected local tame relations topologically
normally generate every relation among the five tame generators.

This is the global Koch relation theorem in its narrow kernel-inclusion form.
The opposite inclusion, continuity, surjectivity, and final presentation
packaging are all proved independently above.
-/
theorem initial_topological_closure :
    initialKochQuotient.ker ≤
      (Subgroup.normalClosure
        (Set.range
          (initialTameRelator
            kochRelationData.frobeniusLift))).topologicalClosure := by
  exact
    completed_algebraic_shadows
      initial_relations_generate

/--
The chosen five local tame relators give the exact topological kernel
certificate required by the generic scaffold.
-/
noncomputable def initialGenerationData :
    KGData 5 initialKochQuotient where
  toRData :=
    kochRelationData.toRData
  kernel_topological_closure :=
    initial_topological_closure

/--
The specialized five-generator, five-relator Koch presentation assembled from
the three arithmetic inputs.
-/
noncomputable def initialKochPresentation :
    ProP.Presentation.{0, 0} 3 5 5 initialGaloisGroup :=
  presentation
    initialKochFree
    initialKochQuotient
    initial_quotient_continuous
    initial_quotient_surjective
    initialGenerationData

/--
The specialized global Koch presentation for the maximal pro-`3` extension of
`ℚ` unramified outside `{7, 13, 19, 31, 37}`: the Galois group admits a free
pro-`3` presentation with five generators and five relators.
-/
theorem initial_koch_presentation :
    Nonempty (ProP.Presentation.{0, 0} 3 5 5 initialGaloisGroup) := by
  exact
    ⟨initialKochPresentation⟩

/-- The actual pro-`3` generator rank `d_3(G)`. -/
abbrev initialProRank : ℕ :=
  ProP.generatorRank initialGaloisGroup

/--
The initial tame pro-`3` Galois group is topologically finitely generated.
This is the finiteness assertion needed for `d_3(G)` to be realized by an
actual finite dense family.
-/
theorem initial_pro_rank :
    ProP.FiniteGeneratorRank initialGaloisGroup := by
  rcases STBuild.initial_topologically_fg with
    ⟨d, s, hs⟩
  exact ⟨d, s, hs⟩

/-- The minimum defining `d_3(G)` is attained. -/
theorem initial_pro_realized :
    ProP.GeneratorCountWitness initialGaloisGroup initialProRank := by
  exact
    ProP.generator_rank_counts initialGaloisGroup
      initial_pro_rank

set_option maxHeartbeats 800000 in
-- Building the continuous cubic-compositum quotient requires substantial Galois bookkeeping.
set_option synthInstance.maxHeartbeats 100000 in
/--
The five explicit cubic subextensions give the lower bound `5 ≤ d_3(G)`.
The existing rank-five elementary-abelian quotient is the arithmetic input; the
topological quotient comparison is kept as its own named result.
-/
theorem initial_pro_five :
    5 ≤ initialProRank := by
  classical
  rcases cubic_compositum_five with ⟨hGal, ⟨eGal⟩⟩
  letI : IsGalois ℚ initialCubicCompositum := hGal
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    .mk initialCompositumIntermediate
  have hPGroup : IsPGroup 3 (Gal(E/ℚ)) := by
    let hEA : IsPGroup 3 (ElementaryAbelianGroup 5) := by
      apply IsPGroup.of_card (n := 5)
      simp [ElementaryAbelianGroup]
    exact IsPGroup.of_equiv hEA eGal.symm
  have hUnramified : UnramifiedOutside E initialRamifiedPrimes := by
    simpa [E, initialCubicCompositum, UnramifiedOutside] using
      initial_compositum_outside
  let x :
      {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
        IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} :=
    ⟨E, hPGroup, hUnramified⟩
  have hle : initialCompositumIntermediate ≤ initialProIntermediate := by
    simpa [x, initialProIntermediate] using
      (le_iSup
        (fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
            IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} =>
          E.1.toIntermediateField)
        x)
  let i : initialCubicCompositum →ₐ[ℚ] initialProExtension :=
    IntermediateField.inclusion hle
  let E' : IntermediateField ℚ initialProExtension := i.fieldRange
  let eField : initialCubicCompositum ≃ₐ[ℚ] E' := AlgEquiv.ofInjectiveField i
  letI : FiniteDimensional ℚ E' := eField.toLinearEquiv.finiteDimensional
  letI : IsGalois ℚ E' := IsGalois.of_algEquiv eField
  letI : Normal ℚ E' := (inferInstance : IsGalois ℚ E').to_normal
  let q : initialGaloisGroup →* ElementaryAbelianGroup 5 :=
    eGal.toMonoidHom.comp
      ((AlgEquiv.autCongr eField).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom E'))
  have hq_surjective : Function.Surjective q := by
    intro y
    obtain ⟨σ, rfl⟩ := eGal.surjective y
    let τ : Gal(↥E'/ℚ) := (AlgEquiv.autCongr eField) σ
    obtain ⟨g, hg⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := ℚ) (K₁ := ↥E') (E := initialProExtension)) τ
    refine ⟨g, ?_⟩
    change eGal (((AlgEquiv.autCongr eField).symm) ((AlgEquiv.restrictNormalHom ↥E') g)) =
      eGal σ
    rw [hg]
    simpa [τ] using congrArg eGal ((AlgEquiv.autCongr eField).symm_apply_apply σ)
  letI : TopologicalSpace (ElementaryAbelianGroup 5) := ⊥
  letI : DiscreteTopology (ElementaryAbelianGroup 5) :=
    discreteTopology_bot (ElementaryAbelianGroup 5)
  letI : IsTopologicalGroup (ElementaryAbelianGroup 5) := by
    infer_instance
  have hq_continuous : Continuous q := by
    have hrestrict :
        Continuous (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := initialProExtension) E') :=
      @InfiniteGalois.restrictNormalHom_continuous
        ℚ initialProExtension inferInstance inferInstance inferInstance E'
        (inferInstance : Normal ℚ E')
    have haut :
        Continuous ((AlgEquiv.autCongr eField).symm.toMonoidHom) :=
      continuous_of_discreteTopology
    have heGal : Continuous eGal.toMonoidHom :=
      continuous_of_discreteTopology
    exact heGal.comp (haut.comp hrestrict)
  rcases initial_pro_realized with ⟨s, hs⟩
  have htopological :
      (Subgroup.closure (Set.range (q ∘ s))).topologicalClosure = ⊤ := by
    simpa only [MonoidHom.map_closure, ← Set.range_comp'] using
      DenseRange.topologicalClosure_map_subgroup
        hq_continuous hq_surjective.denseRange hs
  have hclosure : Subgroup.closure (Set.range (q ∘ s)) = ⊤ := by
    simpa [Subgroup.topologicalClosure] using htopological
  letI : Module (ZMod 3) (Additive (ElementaryAbelianGroup 5)) :=
    AddCommGroup.zmodModule (by
      intro a
      apply Additive.toMul.injective
      simpa using
        elementary_abelian_one (Additive.toMul a))
  have hspan :
      Submodule.span (ZMod 3)
          (Additive.ofMul '' Set.range (q ∘ s) :
            Set (Additive (ElementaryAbelianGroup 5))) = ⊤ :=
    FFSelect.span_top_closure
      (p := 3) hclosure
  have hspan_range :
      Submodule.span (ZMod 3)
          (Set.range (fun j => Additive.ofMul (q (s j))) :
            Set (Additive (ElementaryAbelianGroup 5))) = ⊤ := by
    simpa only [← Set.range_comp', Function.comp_apply] using hspan
  let eAdd :
      Additive (ElementaryAbelianGroup 5) ≃+ (Fin 5 → ZMod 3) :=
    (AddEquiv.piAdditive (fun _ : Fin 5 => Multiplicative (ZMod 3))).trans
      (AddEquiv.piCongrRight (fun _ : Fin 5 =>
        AddEquiv.additiveMultiplicative (ZMod 3)))
  let eLin :
      Additive (ElementaryAbelianGroup 5) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
    LinearEquiv.ofBijective (eAdd.toAddMonoidHom.toZModLinearMap 3) eAdd.bijective
  have hfive :
      Module.finrank (ZMod 3) (Additive (ElementaryAbelianGroup 5)) = 5 := by
    calc
      Module.finrank (ZMod 3) (Additive (ElementaryAbelianGroup 5))
          = Module.finrank (ZMod 3) (Fin 5 → ZMod 3) := eLin.finrank_eq
      _ = 5 := Module.finrank_fin_fun (ZMod 3)
  calc
    5 = Module.finrank (ZMod 3) (Additive (ElementaryAbelianGroup 5)) := hfive.symm
    _ = Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3)
          (Set.range (fun j => Additive.ofMul (q (s j))) :
            Set (Additive (ElementaryAbelianGroup 5)))) := by
      rw [hspan_range, finrank_top]
    _ ≤ Fintype.card (Fin initialProRank) :=
      finrank_range_le_card _
    _ = initialProRank := Fintype.card_fin _

/-- The actual pro-`3` relation rank `r_3(G)`. -/
abbrev proRelationRank : ℕ :=
  ProP.relationRank 3 initialGaloisGroup

/--
The initial Galois group has a finite free pro-`3` presentation on exactly
`d_3(G)` generators. This is the structural finite-presentability input needed
before the numerical Shafarevich estimate can even be stated.
-/
theorem pro_relation_rank :
    ProP.FiniteRelationRank 3 initialGaloisGroup := by
  rcases initial_koch_presentation with ⟨P⟩
  have hgenFive : ProP.GeneratorCountWitness initialGaloisGroup 5 := by
    refine ⟨fun i => P.quotientMap (P.free.generator i), ?_⟩
    simpa only [MonoidHom.map_closure, ← Set.range_comp'] using
      DenseRange.topologicalClosure_map_subgroup
        P.quotientMap_continuous P.quotientMap_surjective.denseRange
        P.free.dense_generator
  have hdLe : initialProRank ≤ 5 := by
    exact Nat.sInf_le hgenFive
  have hd : initialProRank = 5 :=
    Nat.le_antisymm hdLe initial_pro_five
  change (ProP.relationCountsGenerators 3 initialGaloisGroup
    initialProRank).Nonempty
  rw [hd]
  exact ⟨5, ⟨P⟩⟩

/-- The minimum defining `r_3(G)` is attained by an actual presentation. -/
theorem pro_rank_realized :
    ProP.RelationCountWitness 3 initialGaloisGroup initialProRank
      proRelationRank := by
  exact
    ProP.relation_rank_counts 3 initialGaloisGroup
      pro_relation_rank

/-- A chosen minimal free pro-`3` presentation of the initial Galois group. -/
noncomputable def minimalProPresentation :
    ProP.Presentation 3 initialProRank proRelationRank
      initialGaloisGroup :=
  ProP.minimalPresentation 3 initialGaloisGroup
    pro_relation_rank

/--
Every base relator in the chosen minimal free pro-`3` presentation has
Zassenhaus depth at least two.
-/
theorem minimal_pro_presentation :
    minimalProPresentation.RelatorsHaveDepthleast 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact
    ProP.minimal_presentation_relators 3 initialGaloisGroup
      initial_pro_three
      initial_pro_rank
      pro_relation_rank

/--
Shafarevich's relation bound for the initial tame pro-`3` extension.

This theorem contains only the arithmetic inequality `r_3(G) ≤ d_3(G)`.
It does not contain any cutting presentation, tail estimate, GS polynomial
evaluation, or infinitude conclusion.
-/
theorem initial_shafarevich_rank :
    proRelationRank ≤ initialProRank := by
  rcases initial_koch_presentation with ⟨P⟩
  have hgenFive : ProP.GeneratorCountWitness initialGaloisGroup 5 := by
    refine ⟨fun i => P.quotientMap (P.free.generator i), ?_⟩
    simpa only [MonoidHom.map_closure, ← Set.range_comp'] using
      DenseRange.topologicalClosure_map_subgroup
        P.quotientMap_continuous P.quotientMap_surjective.denseRange
        P.free.dense_generator
  have hdLe : initialProRank ≤ 5 := by
    exact Nat.sInf_le hgenFive
  have hd : initialProRank = 5 :=
    Nat.le_antisymm hdLe initial_pro_five
  have hrLe : proRelationRank ≤ 5 := by
    change sInf (ProP.relationCountsGenerators 3 initialGaloisGroup
      initialProRank) ≤ 5
    rw [hd]
    exact Nat.sInf_le ⟨P⟩
  exact hrLe.trans initial_pro_five

end TBluepr
end Submission
