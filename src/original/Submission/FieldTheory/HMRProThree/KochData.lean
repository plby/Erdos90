import Submission.FieldTheory.HMRProThree.FiniteLayer

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open STBuild
open KPScaffo
open IGScaffoa
open GSScaffo
open ILScaffo

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

set_option maxHeartbeats 5000000 in
-- Inertia transport through fixed fields and integer rings needs more heartbeats.
set_option synthInstance.maxHeartbeats 200000 in
/--
One-step generator descent along a refinement of finite layers.

This is the arithmetic transport step inside the finite-intersection witness:
an inertia generator upstairs descends to an inertia generator downstairs at
the compatibly chosen prime.
-/
theorem initial_inertia_descends
    (r : InitialKochRamified)
    (P : CAData r)
    {M N : OpenNormalSubgroup initialGaloisGroup}
    (hMN : M ≤ N)
    (σM : Gal(initialKochLayer M/ℚ))
    (hσM_mem :
      σM ∈ (P.primeAbove M).inertia
          (Gal(initialKochLayer M/ℚ)))
    (hσM_gen :
      Subgroup.closure ({σM} : Set (Gal(initialKochLayer M/ℚ))) =
        (P.primeAbove M).inertia
          (Gal(initialKochLayer M/ℚ))) :
    let hfieldMN :
        (IntermediateField.fixedField
            (initialKochClosed N).1) ≤
          IntermediateField.fixedField
            (initialKochClosed M).1 :=
      IntermediateField.fixedField_le hMN
    letI : Algebra (initialKochLayer N) (initialKochLayer M) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hfieldMN).toRingHom
    letI : Module (initialKochLayer N) (initialKochLayer M) :=
      Algebra.toModule
    letI : IsGalois ℚ (initialKochLayer N) :=
      (initial_galois_open N).2
    letI : Normal ℚ (initialKochLayer N) :=
      (initial_galois_open N).2.to_normal
    ∃ σN : Gal(initialKochLayer N / ℚ),
      σN ∈ (P.primeAbove N).inertia
          (Gal(initialKochLayer N / ℚ)) ∧
        Subgroup.closure ({σN} : Set (Gal(initialKochLayer N / ℚ))) =
          (P.primeAbove N).inertia
            (Gal(initialKochLayer N / ℚ)) ∧
        σM.restrictNormalHom (initialKochLayer N) = σN := by
  let hfieldMN :
      (IntermediateField.fixedField
          (initialKochClosed N).1) ≤
        IntermediateField.fixedField
          (initialKochClosed M).1 :=
    IntermediateField.fixedField_le hMN
  letI : Algebra (initialKochLayer N) (initialKochLayer M) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion hfieldMN).toRingHom
  letI : Module (initialKochLayer N) (initialKochLayer M) :=
    Algebra.toModule
  letI : IsGalois ℚ (initialKochLayer N) :=
    (initial_galois_open N).2
  letI : Normal ℚ (initialKochLayer N) :=
    (initial_galois_open N).2.to_normal
  have hMfg :
      FiniteDimensional ℚ (initialKochLayer M) ∧
        IsGalois ℚ (initialKochLayer M) := by
    simpa [initialKochLayer, initialKochClosed] using
      (initial_galois_open M)
  have hNfg :
      FiniteDimensional ℚ (initialKochLayer N) ∧
        IsGalois ℚ (initialKochLayer N) := by
    simpa [initialKochLayer, initialKochClosed] using
      (initial_galois_open N)
  letI : FiniteDimensional ℚ (initialKochLayer M) :=
    hMfg.1
  letI : IsGalois ℚ (initialKochLayer M) :=
    hMfg.2
  letI : Normal ℚ (initialKochLayer M) :=
    hMfg.2.to_normal
  letI : NumberField (initialKochLayer M) :=
    NumberField.of_module_finite ℚ (initialKochLayer M)
  letI : FiniteDimensional ℚ (initialKochLayer N) :=
    hNfg.1
  letI : NumberField (initialKochLayer N) :=
    NumberField.of_module_finite ℚ (initialKochLayer N)
  letI :
      IsScalarTower ℚ (initialKochLayer N) (initialKochLayer M) :=
    IsScalarTower.of_algebraMap_eq
      (congrFun rfl)
  let PM := P.primeAbove M
  let PN := P.primeAbove N
  have hPMmem :=
    P.primeAbove_mem M
  letI : PM.IsPrime :=
    hPMmem.1
  letI : PM.LiesOver (Ideal.rationalPrimeIdeal r.1) :=
    hPMmem.2
  have hPMunder :
      PM.under (NumberField.RingOfIntegers (initialKochLayer N)) =
        PN := by
    simpa [PM, PN, Ideal.under,
      initialIntegersInclusion] using
      (P.primeAbove_comap hMN)
  let σN : Gal(initialKochLayer N / ℚ) :=
    σM.restrictNormalHom (initialKochLayer N)
  have hσN_mem :
      σN ∈ PN.inertia (Gal(initialKochLayer N / ℚ)) := by
    intro x
    rw [Submodule.mem_toAddSubgroup, ← hPMunder, Ideal.under_def, Ideal.mem_comap]
    simpa [σN] using
      (number_restrict_tower
        (K := initialKochLayer N)
        (L := initialKochLayer M)
        (q := r.1)
        σM
        hσM_mem
        x)
  let E : IntermediateField ℚ (initialKochLayer M) :=
    IntermediateField.restrict hfieldMN
  let e : initialKochLayer N ≃ₐ[ℚ] E :=
    IntermediateField.restrict_algEquiv hfieldMN
  letI : FiniteDimensional ℚ E :=
    e.toLinearEquiv.finiteDimensional
  letI : IsGalois ℚ E :=
    IsGalois.of_algEquiv e
  letI : Normal ℚ E :=
    (inferInstance : IsGalois ℚ E).to_normal
  let eO :
      NumberField.RingOfIntegers (initialKochLayer N) ≃+*
        NumberField.RingOfIntegers E :=
    NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  let PE : Ideal (NumberField.RingOfIntegers E) :=
    PM.under (NumberField.RingOfIntegers E)
  have heO_inclusion
      (x : NumberField.RingOfIntegers (initialKochLayer N)) :
      algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers (initialKochLayer M)) (eO x) =
        algebraMap (NumberField.RingOfIntegers (initialKochLayer N))
          (NumberField.RingOfIntegers (initialKochLayer M)) x := by
    apply NumberField.RingOfIntegers.ext
    change
      algebraMap E (initialKochLayer M) (e (x : initialKochLayer N)) =
        algebraMap (initialKochLayer N) (initialKochLayer M) x
    rfl
  have hPEcomap :
      PE.comap eO = PN := by
    rw [← hPMunder]
    ext x
    change
      algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers (initialKochLayer M)) (eO x) ∈ PM ↔
        algebraMap (NumberField.RingOfIntegers (initialKochLayer N))
          (NumberField.RingOfIntegers (initialKochLayer M)) x ∈ PM
    rw [heO_inclusion]
  have hPE :
      PN.map eO = PE := by
    calc
      PN.map eO = (PE.comap eO).map eO := by
        rw [hPEcomap]
      _ = PE := Ideal.map_comap_eq_self_of_equiv eO PE
  let eAut :
      Gal(initialKochLayer N / ℚ) ≃*
        Gal(E / ℚ) :=
    AlgEquiv.autCongr e
  have heO_smul
      (τ : Gal(initialKochLayer N / ℚ))
      (x : NumberField.RingOfIntegers (initialKochLayer N)) :
      eO (τ • x) = eAut τ • eO x := by
    apply NumberField.RingOfIntegers.ext
    change
      e (τ (x : initialKochLayer N)) =
        (eAut τ) (e (x : initialKochLayer N))
    simp [eAut, AlgEquiv.autCongr_apply]
  have heAut_mem_inertia
      (τ : Gal(initialKochLayer N / ℚ)) :
      τ ∈ PN.inertia (Gal(initialKochLayer N / ℚ)) ↔
        eAut τ ∈ PE.inertia (Gal(E / ℚ)) := by
    constructor
    · intro hτ x
      let y :
          NumberField.RingOfIntegers (initialKochLayer N) :=
        eO.symm x
      have hy :
          τ • y - y ∈ PN :=
        hτ y
      have hy' :
          eO (τ • y - y) ∈ PE := by
        rw [← hPE]
        exact Ideal.mem_map_of_mem eO hy
      simpa [y, map_sub, heO_smul] using hy'
    · intro hτ x
      rw [Submodule.mem_toAddSubgroup, ← hPEcomap, Ideal.mem_comap]
      simpa [map_sub, heO_smul] using hτ (eO x)
  let eInertia :
      PN.inertia (Gal(initialKochLayer N / ℚ)) ≃*
        PE.inertia (Gal(E / ℚ)) :=
    { toEquiv := Equiv.subtypeEquiv eAut.toEquiv heAut_mem_inertia
      map_mul' := by
        intro τ υ
        ext
        simp [eAut] }
  let inertiaRestriction :
      PM.inertia (Gal(initialKochLayer M / ℚ)) →*
        PN.inertia (Gal(initialKochLayer N / ℚ)) :=
    { toFun := fun σ =>
        ⟨σ.1.restrictNormalHom (initialKochLayer N), by
          simpa [hPMunder] using
            (number_restrict_tower
              (K := initialKochLayer N)
              (L := initialKochLayer M)
              (q := r.1)
              σ.1
              σ.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro σ τ
        ext
        simp }
  have hrPrime :
      Nat.Prime r.1 :=
    ramified_primes_prime r.1 r.2
  have hrestrict_congr
      (σ : Gal(initialKochLayer M / ℚ)) :
      eAut (σ.restrictNormalHom (initialKochLayer N)) =
        σ.restrictNormalHom E := by
    ext x
    rcases e.surjective x with ⟨y, rfl⟩
    have hE :
        e (σ.restrictNormalHom (initialKochLayer N) y) =
          σ.restrictNormalHom E (e y) := by
      apply Subtype.ext
      change
        algebraMap (initialKochLayer N) (initialKochLayer M)
            (σ.restrictNormalHom (initialKochLayer N) y) =
          algebraMap E (initialKochLayer M)
            (σ.restrictNormalHom E (e y))
      simp [AlgEquiv.restrictNormalHom]
      rfl
    simpa [eAut, AlgEquiv.autCongr_apply] using hE
  have hinertiaRestriction_surjective :
      Function.Surjective inertiaRestriction := by
    intro τ
    let τE : PE.inertia (Gal(E / ℚ)) :=
      eInertia τ
    obtain ⟨σ, hσ⟩ :=
      number_restriction_preimage
        E
        (inferInstance : FiniteDimensional ℚ E)
        (inferInstance : IsGalois ℚ E)
        hrPrime
        PM
        τE
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    change
      σ.1.restrictNormalHom (initialKochLayer N) =
        (τ : Gal(initialKochLayer N / ℚ))
    apply eAut.injective
    calc
      eAut (σ.1.restrictNormalHom (initialKochLayer N)) =
          σ.1.restrictNormalHom E := hrestrict_congr σ.1
      _ = (τE : Gal(E / ℚ)) := congrArg Subtype.val hσ
      _ = eAut (τ : Gal(initialKochLayer N / ℚ)) := rfl
  let restriction :
      Gal(initialKochLayer M / ℚ) →*
        Gal(initialKochLayer N / ℚ) :=
    AlgEquiv.restrictNormalHom (initialKochLayer N)
  have hmap_inertia :
      Subgroup.map restriction
          (PM.inertia (Gal(initialKochLayer M / ℚ))) =
        PN.inertia (Gal(initialKochLayer N / ℚ)) := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact (inertiaRestriction ⟨σ, hσ⟩).2
    · intro τ hτ
      obtain ⟨σ, hσ⟩ :=
        hinertiaRestriction_surjective ⟨τ, hτ⟩
      exact ⟨σ.1, σ.2, congrArg Subtype.val hσ⟩
  have hσN_gen :
      Subgroup.closure
          ({σN} : Set (Gal(initialKochLayer N / ℚ))) =
        PN.inertia (Gal(initialKochLayer N / ℚ)) := by
    calc
      Subgroup.closure
          ({σN} : Set (Gal(initialKochLayer N / ℚ))) =
          Subgroup.map restriction
            (Subgroup.closure
              ({σM} : Set (Gal(initialKochLayer M / ℚ)))) := by
        rw [MonoidHom.map_closure]
        simp [σN, restriction]
      _ = Subgroup.map restriction
          (PM.inertia (Gal(initialKochLayer M / ℚ))) := by
        rw [hσM_gen]
      _ = PN.inertia (Gal(initialKochLayer N / ℚ)) :=
        hmap_inertia
  exact ⟨σN, hσN_mem, hσN_gen, rfl⟩

set_option maxHeartbeats 1000000 in
-- Nested fixed-field restriction needs the same larger elaboration budget.
/--
Formal compatibility between quotient images in the profinite group and field
restriction along a refinement of finite layers.
-/
theorem initial_koch_restrict
    {M N : OpenNormalSubgroup initialGaloisGroup}
    (hMN : M ≤ N)
    (g : initialGaloisGroup) :
    let hfieldMN :
        (IntermediateField.fixedField
            (initialKochClosed N).1) ≤
          IntermediateField.fixedField
            (initialKochClosed M).1 :=
      IntermediateField.fixedField_le hMN
    letI : Algebra (initialKochLayer N) (initialKochLayer M) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hfieldMN).toRingHom
    letI : Module (initialKochLayer N) (initialKochLayer M) :=
      Algebra.toModule
    letI : IsGalois ℚ (initialKochLayer N) :=
      (initial_galois_open N).2
    letI : Normal ℚ (initialKochLayer N) :=
      (initial_galois_open N).2.to_normal
    (initialKochEquiv M
        (IGScaffoa.quotientMap M g)).restrictNormalHom
          (initialKochLayer N) =
      initialKochEquiv N
        (IGScaffoa.quotientMap N g) := by
  let hfieldMN :
      (IntermediateField.fixedField
          (initialKochClosed N).1) ≤
        IntermediateField.fixedField
          (initialKochClosed M).1 :=
    IntermediateField.fixedField_le hMN
  letI : Algebra (initialKochLayer N) (initialKochLayer M) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion hfieldMN).toRingHom
  letI : SMul (initialKochLayer N) (initialKochLayer M) :=
    Algebra.toSMul
  letI : Module (initialKochLayer N) (initialKochLayer M) :=
    Algebra.toModule
  letI : Module (initialKochLayer N) initialProExtension :=
    Algebra.toModule
  letI : Module (initialKochLayer M) initialProExtension :=
    Algebra.toModule
  letI : SMul (initialKochLayer N) initialProExtension :=
    Algebra.toSMul
  letI : SMul (initialKochLayer M) initialProExtension :=
    Algebra.toSMul
  letI : IsGalois ℚ (initialKochLayer N) :=
    (initial_galois_open N).2
  letI : Normal ℚ (initialKochLayer N) :=
    (initial_galois_open N).2.to_normal
  letI : IsGalois ℚ (initialKochLayer M) :=
    (initial_galois_open M).2
  letI : Normal ℚ (initialKochLayer M) :=
    (initial_galois_open M).2.to_normal
  letI : (initialKochClosed M).toSubgroup.Normal := by
    change (M : Subgroup initialGaloisGroup).Normal
    infer_instance
  letI : (initialKochClosed N).toSubgroup.Normal := by
    change (N : Subgroup initialGaloisGroup).Normal
    infer_instance
  have hM :
      initialKochEquiv M
          (IGScaffoa.quotientMap M g) =
        g.restrictNormalHom (initialKochLayer M) := by
    simpa [initialKochEquiv, galoisFixedField,
      IGScaffoa.quotientMap, initialKochLayer] using
      (InfiniteGalois.normalAutEquivQuotient_apply
        (initialKochClosed M)
        g)
  have hN :
      initialKochEquiv N
          (IGScaffoa.quotientMap N g) =
        g.restrictNormalHom (initialKochLayer N) := by
    simpa [initialKochEquiv, galoisFixedField,
      IGScaffoa.quotientMap, initialKochLayer] using
      (InfiniteGalois.normalAutEquivQuotient_apply
        (initialKochClosed N)
        g)
  rw [hM, hN]
  letI :
      IsScalarTower ℚ (initialKochLayer N) (initialKochLayer M) :=
    IsScalarTower.of_algebraMap_eq
      (congrFun rfl)
  letI :
      IsScalarTower
        (initialKochLayer N)
        (initialKochLayer M)
        initialProExtension :=
    IsScalarTower.of_algebraMap_eq'
      rfl
  exact
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
      (initialKochLayer N)
      (initialKochLayer M)
      g).symm

/--
Arithmetic leaf for the one-coordinate compactness argument: every finite
family of layer conditions for a fixed coherent prime tower is simultaneously
realizable by one ambient element.

This is strictly smaller than
`compatible_inertia_nonempty`. It does not package the
result into global data, and it only asks for finite compatibility rather than
the full inverse-limit conclusion.
-/
theorem compatible_inertia_intersection
    (r : InitialKochRamified)
    (P : CAData r)
    (s : Finset (OpenNormalSubgroup initialGaloisGroup)) :
    (⋂ N ∈ s, compatibleGoodSet r P N).Nonempty := by
  let M : OpenNormalSubgroup initialGaloisGroup :=
    s.inf (fun N : OpenNormalSubgroup initialGaloisGroup => N)
  obtain ⟨σM, hσM_mem, hσM_gen⟩ :=
    initial_inertia_generator
      r
      P
      M
  let qM : initialGaloisGroup ⧸ M.toSubgroup :=
    (initialKochEquiv M).symm σM
  obtain ⟨g, hgM⟩ :=
    IGScaffoa.quotientMap_surjective M qM
  refine ⟨g, ?_⟩
  rw [Set.mem_iInter₂]
  intro N hN
  have hMN :
      M ≤ N :=
    Finset.inf_le hN
  obtain ⟨σN, hσN_mem, hσN_gen, hσN_restrict⟩ :=
    initial_inertia_descends
      r
      P
      hMN
      σM
      hσM_mem
      hσM_gen
  change
    let σ :=
      initialKochEquiv N
        (IGScaffoa.quotientMap N g)
    σ ∈ (P.primeAbove N).inertia
        (Gal(initialKochLayer N / ℚ)) ∧
      Subgroup.closure ({σ} : Set (Gal(initialKochLayer N / ℚ))) =
        (P.primeAbove N).inertia
          (Gal(initialKochLayer N / ℚ))
  have hgM' :
      initialKochEquiv M
          (IGScaffoa.quotientMap M g) =
        σM := by
    simpa [qM] using congrArg (initialKochEquiv M) hgM
  have hfieldMN :
      (IntermediateField.fixedField
          (initialKochClosed N).1) ≤
        IntermediateField.fixedField
          (initialKochClosed M).1 :=
    IntermediateField.fixedField_le hMN
  letI :
      Algebra (initialKochLayer N) (initialKochLayer M) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion hfieldMN).toRingHom
  letI : Module (initialKochLayer N) (initialKochLayer M) :=
    Algebra.toModule
  letI : IsGalois ℚ (initialKochLayer N) :=
    (initial_galois_open N).2
  letI : Normal ℚ (initialKochLayer N) :=
    (initial_galois_open N).2.to_normal
  have hσeq :
      initialKochEquiv N
          (IGScaffoa.quotientMap N g) =
        σN := by
    have htmp :
        (initialKochEquiv M
            (IGScaffoa.quotientMap M g)).restrictNormalHom
              (initialKochLayer N) =
          σN := by
      rw [hgM']
      exact hσN_restrict
    exact
      (initial_koch_restrict hMN g).symm.trans
        htmp
  refine ⟨?_, ?_⟩
  · simpa [hσeq] using hσN_mem
  · simpa [hσeq] using hσN_gen

/--
Compactness upgrades the finite-intersection witnesses for one coherent prime
tower to a single ambient element satisfying every finite-layer inertia
condition at once.

This remains smaller than the final data theorem: it produces only the ambient
element, not the packaged structure fields built from it.
-/
theorem good_total_intersection
    (r : InitialKochRamified)
    (P : CAData r) :
    (⋂ N : OpenNormalSubgroup initialGaloisGroup,
      compatibleGoodSet r P N).Nonempty := by
  have hclosed :
      ∀ N : OpenNormalSubgroup initialGaloisGroup,
        IsClosed (compatibleGoodSet r P N) := by
    intro N
    exact
      compatible_good_closed
        r
        P
        N
  have hfip :
      ∀ s : Finset (OpenNormalSubgroup initialGaloisGroup),
        (⋂ N ∈ s,
          compatibleGoodSet r P N).Nonempty := by
    intro s
    exact
      compatible_inertia_intersection
        r
        P
        s
  exact
    CompactSpace.iInter_nonempty
      hclosed
      hfip

/--
Package a single ambient element satisfying all local good-generator conditions
into the full compatible inertia-generator datum.

This is bookkeeping only: all arithmetic content has already been moved into
the total-intersection hypothesis.
-/
def CIData.mem_total_inter
    {r : InitialKochRamified}
    {P : CAData r}
    (g : initialGaloisGroup)
    (hg :
      g ∈ ⋂ N : OpenNormalSubgroup initialGaloisGroup,
        compatibleGoodSet r P N) :
    CIData r P where
  generator := g
  inertiaGenerator := fun N =>
    ⟨initialKochEquiv N
        (IGScaffoa.quotientMap N g),
      (Set.mem_iInter.mp hg N).1⟩
  mapsFiniteLayer := by
    intro N
    rfl
  inertiaGenerator_generates := by
    intro N
    exact
      (Set.mem_iInter.mp hg N).2

/--
Arithmetic leaf: over a coherent prime tower, select one compatible ambient
inertia generator.

This is a one-coordinate compactness problem.  Its transition maps are the
surjective inertia restrictions established above; tameness makes every
finite inertia group cyclic, so a generator can be lifted compatibly.  The
statement is strictly smaller than the original target because it fixes one
rational prime and assumes the entire coherent prime tower as input.  It
does not assert that the five selected coordinates generate any global
Galois quotient.
-/
theorem compatible_inertia_nonempty
    (r : InitialKochRamified)
    (P : CAData r) :
    Nonempty (CIData r P) := by
  classical
  have hall :
      (⋂ N : OpenNormalSubgroup initialGaloisGroup,
        compatibleGoodSet r P N).Nonempty := by
    exact
      good_total_intersection
        r
        P
  rcases hall with ⟨g, hg⟩
  exact
    ⟨CIData.mem_total_inter g hg⟩

/--
The prime and inertia selections for one initially ramified rational prime.
-/
structure TIFam
    (r : InitialKochRamified) where
  coherentAboveData :
    CAData r
  compatibleInertiaData :
    CIData
      r
      coherentAboveData

namespace TIFam

/--
The ambient inertia generator selected for this rational prime.
-/
def generator
    {r : InitialKochRamified}
    (D : TIFam r) :
    initialGaloisGroup :=
  D.compatibleInertiaData.generator

/--
The selected prime above `r` in one finite fixed-field layer.
-/
def primeAbove
    {r : InitialKochRamified}
    (D : TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Ideal (NumberField.RingOfIntegers (initialKochLayer N)) :=
  D.coherentAboveData.primeAbove N

/--
The selected prime is a prime above the indexed rational prime.
-/
lemma primeAbove_mem
    {r : InitialKochRamified}
    (D : TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    D.primeAbove N ∈
      Ideal.primesOver
        (Ideal.rationalPrimeIdeal r.1)
        (NumberField.RingOfIntegers (initialKochLayer N)) := by
  exact
    D.coherentAboveData.primeAbove_mem N

/--
The selected primes descend compatibly along refinement of finite layers.
-/
lemma primeAbove_comap
    {r : InitialKochRamified}
    (D : TIFam r)
    {M N : OpenNormalSubgroup initialGaloisGroup}
    (hMN : M ≤ N) :
    Ideal.comap
        (initialIntegersInclusion hMN)
        (D.primeAbove M) =
      D.primeAbove N := by
  exact
    D.coherentAboveData.primeAbove_comap hMN

/--
The inertia generator selected in one finite fixed-field layer.
-/
def inertiaGenerator
    {r : InitialKochRamified}
    (D : TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    (D.primeAbove N).inertia
      (Gal(initialKochLayer N / ℚ)) :=
  D.compatibleInertiaData.inertiaGenerator N

/--
The ambient generator projects to the selected finite-layer inertia
generator.
-/
lemma mapsFiniteLayer
    {r : InitialKochRamified}
    (D : TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    initialKochEquiv N
        (IGScaffoa.quotientMap N D.generator) =
      (D.inertiaGenerator N :
        Gal(initialKochLayer N / ℚ)) := by
  exact
    D.compatibleInertiaData.mapsFiniteLayer N

/--
The chosen finite-layer inertia element generates its local inertia group.
-/
lemma inertiaGenerator_generates
    {r : InitialKochRamified}
    (D : TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Subgroup.closure
        ({(D.inertiaGenerator N :
          Gal(initialKochLayer N / ℚ))} : Set _) =
      (D.primeAbove N).inertia
        (Gal(initialKochLayer N / ℚ)) := by
  exact
    D.compatibleInertiaData.inertiaGenerator_generates N

end TIFam

/--
Choose the compatible prime and inertia-generator package for one rational
prime.
-/
noncomputable def initialTameFamily
    (r : InitialKochRamified) :
    TIFam r := by
  let P :
      CAData r :=
    Classical.choice
      (coherent_above_nonempty r)
  let I :
      CIData r P :=
    Classical.choice
      (compatible_inertia_nonempty r P)
  exact
    { coherentAboveData := P
      compatibleInertiaData := I }

set_option maxHeartbeats 1000000 in
-- The fixed-field ramification argument synthesizes several nested Galois instances.
set_option synthInstance.maxHeartbeats 200000 in
/--
Arithmetic leaf: the five compatible inertia elements generate one fixed
finite quotient.

This is the finite Shafarevich-generation boundary.  Unlike the original
target, it has no inverse-limit quantification, no prime-descent coherence,
and no construction of ambient elements.  All compatible choices have
already been supplied as parameters; the remaining assertion is a finite
group calculation in the quotient by one `N`.
-/
theorem tame_inertia_generate
    (family :
      ∀ r : InitialKochRamified,
        TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Subgroup.closure
        (Set.range
          (fun r =>
            IGScaffoa.quotientMap N
              (family r).generator)) =
      ⊤ := by
  classical
  let K := initialKochLayer N
  have hKfg :
      FiniteDimensional ℚ K ∧
        IsGalois ℚ K := by
    simpa [K, initialKochLayer, initialKochClosed] using
      (STBuild.initial_galois_open
        N)
  letI : FiniteDimensional ℚ K := hKfg.1
  letI : IsGalois ℚ K := hKfg.2
  letI : NumberField K := NumberField.of_module_finite ℚ K
  letI : Finite (Gal(K / ℚ)) :=
    IsGaloisGroup.finite (Gal(K / ℚ)) ℚ K
  have hPGroup : IsPGroup 3 (Gal(K / ℚ)) := by
    exact
      @STBuild.initial_pro_subextension
        (IntermediateField.fixedField
          (initialKochClosed N).1)
        hKfg.1
        hKfg.2
  let e : initialGaloisGroup ⧸ N.toSubgroup ≃* Gal(K / ℚ) :=
    initialKochEquiv N
  let g : InitialKochRamified → Gal(K / ℚ) := fun r =>
    e (IGScaffoa.quotientMap N (family r).generator)
  have hnormalClosure_top :
      Subgroup.normalClosure (Set.range g) = ⊤ := by
    let H : Subgroup (Gal(K / ℚ)) :=
      Subgroup.normalClosure (Set.range g)
    letI : H.Normal := Subgroup.normalClosure_normal
    let L : IntermediateField ℚ K :=
      STBuild.ramifiedFixedField K H
    letI : Field L := L.toField
    letI : Algebra ℚ L := L.algebra'
    letI : FiniteDimensional ℚ L := by
      dsimp [L, STBuild.ramifiedFixedField]
      infer_instance
    letI : IsGalois ℚ L := by
      dsimp [L, STBuild.ramifiedFixedField]
      infer_instance
    letI : NumberField L := NumberField.of_module_finite ℚ L
    let hstRat :
        IsScalarTower
          ℤ
          ℚ
          L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let hstInt :
        IsScalarTower
          ℤ
          (NumberField.RingOfIntegers L)
          L :=
      STBuild.integers_scalar_tower
        (K := L)
    letI :
        IsGaloisGroup
          (Gal(L / ℚ))
          ℤ
          (NumberField.RingOfIntegers L) := by
      exact
        @IsGaloisGroup.of_isFractionRing
          (Gal(L / ℚ))
          ℤ
          (NumberField.RingOfIntegers L)
          ℚ
          L
          _ _ _ _ _ _ _ _ _ _ _ _ _
          hstRat
          hstInt
          _ _ _ _ _
    have hKunram :
        UnramifiedOutside K initialRamifiedPrimes := by
      simpa [K, initialKochLayer, initialKochClosed] using
        (STBuild.initial_unramified_outside
          N)
    have hKemb :
        EmbedsIntoExtension K initialProExtension := by
      simpa [K, initialKochLayer, initialKochClosed] using
        (embeds_pro_extension
          N)
    have hLunram :
        UnramifiedOutside L initialRamifiedPrimes := by
      simpa [L] using
        (STBuild.ramified_fixed_outside
          K hKunram H)
    have hLemb :
        EmbedsIntoExtension L initialProExtension := by
      simpa [L] using
        (ramified_embeds_extension
          K hKemb H)
    have hfix :
        L.fixingSubgroup = H := by
      simpa [L, STBuild.ramifiedFixedField] using
        (IntermediateField.fixingSubgroup_fixedField H)
    have hall :
        ∀ q : ℕ, Nat.Prime q →
          RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q := by
      intro q hq
      by_cases hqS : q ∈ initialRamifiedPrimes
      · let r : InitialKochRamified := ⟨q, hqS⟩
        let P : Ideal (NumberField.RingOfIntegers K) :=
          (family r).primeAbove N
        have hPmem :
            P ∈
              Ideal.primesOver
                (Ideal.rationalPrimeIdeal q)
                (NumberField.RingOfIntegers K) := by
          simpa [P, r] using (family r).primeAbove_mem N
        letI : P.IsPrime := hPmem.1
        letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPmem.2
        let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
        let Q : Ideal (NumberField.RingOfIntegers L) :=
          P.under (NumberField.RingOfIntegers L)
        letI : qI.IsPrime := rational_prime_ideal hq
        have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
        letI : qI.IsMaximal := rational_ideal_maximal hq
        letI : Q.LiesOver qI := by
          rw [Ideal.liesOver_iff]
          simpa [Q, qI, Ideal.liesOver_iff] using
            (show P.LiesOver qI by infer_instance)
        have hQ0 : Q ≠ ⊥ :=
          Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 Q
        letI : Q.IsMaximal :=
          Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := Q)
        have hPinertia_le_H :
            P.inertia (Gal(K / ℚ)) ≤ H := by
          rw [← (family r).inertiaGenerator_generates N]
          rw [Subgroup.closure_le]
          intro σ hσ
          rw [Set.mem_singleton_iff] at hσ
          subst hσ
          have hgmem : g r ∈ H :=
            Subgroup.subset_normalClosure (Set.mem_range_self r)
          have hgr :
              g r = ((family r).inertiaGenerator N : Gal(K / ℚ)) := by
            simpa [g] using (family r).mapsFiniteLayer N
          exact hgr ▸ hgmem
        have hLfin : FiniteDimensional ℚ L := inferInstance
        have hLgal : IsGalois ℚ L := inferInstance
        have htrivialRestriction :
            ∀ σ : P.inertia (Gal(K / ℚ)),
              numberInertiaRestriction L hLgal.to_normal q P σ = 1 := by
          intro σ
          apply Subtype.ext
          have hσfix : (σ : Gal(K / ℚ)) ∈ L.fixingSubgroup := by
            rw [hfix]
            exact hPinertia_le_H σ.2
          ext x
          have hsub :
              ((σ : Gal(K / ℚ)).restrictNormalHom L) x = x := by
            apply Subtype.ext
            rw [AlgEquiv.restrictNormalHom_apply]
            exact
              (IntermediateField.mem_fixingSubgroup_iff
                (K := L) (σ := (σ : Gal(K / ℚ)))).1 hσfix x x.2
          simpa [numberInertiaRestriction] using congrArg Subtype.val hsub
        have hQinertia_bot :
            Q.inertia (Gal(L / ℚ)) = ⊥ := by
          apply bot_unique
          intro τ hτ
          obtain ⟨σ, hσeq⟩ :=
            number_restriction_preimage
              L
              hLfin
              hLgal
              hq
              P
              ⟨τ, hτ⟩
          have hσone :
              numberInertiaRestriction L hLgal.to_normal q P σ = 1 :=
            htrivialRestriction σ
          have hτone :
              τ = 1 := by
            have :
                ((numberInertiaRestriction L hLgal.to_normal q P σ :
                    Q.inertia (Gal(L / ℚ))) :
                  Gal(L / ℚ)) = 1 := by
              simpa using congrArg Subtype.val hσone
            simpa [hσeq] using this
          exact Subgroup.mem_bot.mpr hτone
        have hQram :
            Ideal.ramificationIdx qI Q = 1 := by
          exact
            Submission.ramification_idx_bot
              (L := L) hq Q hQinertia_bot
        intro R hR
        letI : R.IsPrime := hR.1
        letI : R.LiesOver qI := hR.2
        calc
          Ideal.ramificationIdx qI R =
              Ideal.ramificationIdx qI Q := by
                exact
                  Ideal.ramificationIdx_eq_of_isGaloisGroup
                    (p := qI)
                    (P := R)
                    (Q := Q)
                    (G := Gal(L / ℚ))
          _ = 1 := hQram
      · exact hLunram q hq hqS
    have hLbot :
        L = ⊥ := by
      exact
        ramified_intermediate_primes
          K L hLemb hall
    exact
      STBuild.ramified_top_bot
        K hLbot
  have hclosure_top :
      Subgroup.closure (Set.range g) = ⊤ := by
    exact
      closure_top_pgroup
        hPGroup
        hnormalClosure_top
  have hmapped :
      Subgroup.map e.toMonoidHom
          (Subgroup.closure
            (Set.range
              (fun r =>
                IGScaffoa.quotientMap N
                  (family r).generator))) =
        ⊤ := by
    simpa only [MonoidHom.map_closure, ← Set.range_comp', g] using hclosure_top
  exact
    (MulEquiv.mapSubgroup e).injective (by
      simpa using hmapped)

/--
Package a prime-indexed compatible family into the certified datum for one
finite layer.
-/
noncomputable def tameInertiaFamily
    (family :
      ∀ r : InitialKochRamified,
        TIFam r)
    (N : OpenNormalSubgroup initialGaloisGroup)
    (hgenerates :
      Subgroup.closure
          (Set.range
            (fun r =>
              IGScaffoa.quotientMap N
                (family r).generator)) =
        ⊤) :
    TameInertiaData N where
  quotientGeneratorData :=
    { generator :=
        fun r =>
          IGScaffoa.quotientMap N
            (family r).generator
      generates :=
        hgenerates }
  primeAbove :=
    fun r =>
      (family r).primeAbove N
  primeAbove_mem :=
    fun r =>
      (family r).primeAbove_mem N
  inertiaGenerator :=
    fun r =>
      (family r).inertiaGenerator N
  inertiaGenerator_generates :=
    fun r =>
      (family r).inertiaGenerator_generates N
  generator_eq := by
    intro r
    apply
      (initialKochEquiv N).injective
    simp only [
      MulEquiv.apply_symm_apply
    ]
    exact
      (family r).mapsFiniteLayer N

/--
Package compatible prime-indexed selections into the global inverse-limit
datum once finite-layer generation has been discharged.
-/
noncomputable def initialInertiaFamily
    (family :
      ∀ r : InitialKochRamified,
        TIFam r)
    (hgenerates :
      ∀ N : OpenNormalSubgroup initialGaloisGroup,
        Subgroup.closure
            (Set.range
              (fun r =>
                IGScaffoa.quotientMap N
                  (family r).generator)) =
          ⊤) :
    InitialInertiaData where
  generator :=
    fun r =>
      (family r).generator
  finiteLayerData :=
    fun N =>
      tameInertiaFamily
        family
        N
        (hgenerates N)
  mapsFiniteLayer := by
    intro N r
    rfl
  primeAbove_comap := by
    intro M N hMN r
    exact
      (family r).primeAbove_comap hMN

/--
Arithmetic input: choose compatible tame inertia elements in the inverse
limit whose images generate every finite Galois layer.

This is the provenance-preserving form needed by the later local Koch
relation.  Its proof may use compactness, but the selected limit elements and
their inertia certificates must remain linked.
-/
theorem tame_inertia_nonempty :
    Nonempty InitialInertiaData := by
  let family :
      ∀ r : InitialKochRamified,
        TIFam r :=
    fun r =>
      initialTameFamily r
  refine
    ⟨initialInertiaFamily
      family
      ?_⟩
  intro N
  exact
    tame_inertia_generate
      family
      N

/--
A fixed provenance-preserving choice of tame inertia elements.
-/
noncomputable def initialInertiaData :
    InitialInertiaData :=
  Classical.choice tame_inertia_nonempty

/--
A fixed prime-indexed choice of tame inertia elements.
-/
noncomputable def initialInertiaGenerator :
    InitialKochRamified → initialGaloisGroup :=
  initialInertiaData.generator

/--
Finite-layer tame inertia generation, obtained by projecting the compatible
inverse-limit arithmetic datum to the quotient by `N`.
-/
theorem inertia_images_generate
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Nonempty
      (TameInertiaData N) := by
  exact
    tame_inertia_nonempty.map
      (fun D => D.finiteLayerData N)

/--
The forgetful finite-layer bridge to the generic quotient lifting scaffold.
-/
theorem initial_koch_nonempty
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Nonempty
      (QGData
        InitialKochRamified
        N) := by
  exact
    (inertia_images_generate N).map
      TameInertiaData.quotientGeneratorData

/--
Forgetting provenance in one finite layer still yields ambient
representatives whose quotient images generate that layer.

These arbitrary ambient representatives are a generic lifting convenience;
the main Koch construction below uses the compatible certified family
instead.
-/
theorem initial_generate_single
    (N : OpenNormalSubgroup initialGaloisGroup) :
    ∃ generator : InitialKochRamified → initialGaloisGroup,
      GeneratesOpenNormal generator N := by
  exact
    lift_generates_nonempty
      (initial_koch_nonempty N)

/--
The fixed tame inertia elements generate every open-normal finite quotient
when indexed by the actual ramified primes.
-/
lemma initial_inertia_generates
    (N : OpenNormalSubgroup initialGaloisGroup) :
    Subgroup.closure
        (Set.range
          (fun r =>
            IGScaffoa.quotientMap N
              (initialInertiaGenerator r))) =
      ⊤ := by
  let D :=
    initialInertiaData.finiteLayerData N
  rw [
    show
        (fun r =>
          IGScaffoa.quotientMap N
            (initialInertiaGenerator r)) =
          D.quotientGeneratorData.generator by
      funext r
      exact
        initialInertiaData.mapsFiniteLayer N r
  ]
  exact
    D.quotientGeneratorData.generates

/--
The compatible certified tame inertia family generates every open-normal
finite quotient.
-/
theorem initial_generate_quotients :
    ∃ generator : InitialKochRamified → initialGaloisGroup,
      ∀ N : OpenNormalSubgroup initialGaloisGroup,
        Subgroup.closure
            (Set.range
              (fun r =>
                IGScaffoa.quotientMap N (generator r))) =
          ⊤ := by
  exact
    ⟨initialInertiaGenerator,
      initial_inertia_generates⟩

/--
The fixed tame inertia elements in the order expected by the five-generator
Koch presentation.
-/
noncomputable def tameInertiaGenerator :
    Fin 5 → initialGaloisGroup :=
  initialTameGenerator
    initialInertiaGenerator

/--
The ordered tame inertia elements generate each open-normal finite quotient.
-/
lemma tame_inertia_generates
    (N : OpenNormalSubgroup initialGaloisGroup) :
    GeneratesOpenNormal
      tameInertiaGenerator
      N := by
  unfold
    GeneratesOpenNormal
  unfold
    tameInertiaGenerator
  rw [
    initial_tame_closure
      initialInertiaGenerator
      (IGScaffoa.quotientMap N)
  ]
  exact
    initial_inertia_generates N

/--
The ordered tame inertia elements generate all open-normal finite shadows.
-/
lemma initial_generates_every :
    GeneratesEveryOpen
      tameInertiaGenerator := by
  intro N
  exact
    tame_inertia_generates N

/--
The ordered tame inertia elements topologically generate the initial Galois
group.  This is now a formal profinite consequence of their finite-layer
arithmetic generation property.
-/
lemma initial_topologically_generates :
    ProP.TopologicallyGenerates
      tameInertiaGenerator := by
  exact
    topologically_generates_every
      tameInertiaGenerator
      initial_generates_every

/--
Arithmetic input one: choose five tame generators and prove that they
topologically generate the initial Galois group.

This is smaller than a Koch presentation: it neither mentions a free pro-`3`
group nor asks for relators or a kernel computation.
-/
theorem initial_generator_nonempty :
    Nonempty (GData 5 initialGaloisGroup) := by
  refine
    ⟨{
      generator :=
        tameInertiaGenerator
      topologicallyGenerates := ?_
    }⟩
  exact
    initial_topologically_generates

/--
A fixed choice of the five tame topological generators.
-/
noncomputable def initialGeneratorData :
    GData 5 initialGaloisGroup :=
  {
    generator :=
      tameInertiaGenerator
    topologicallyGenerates :=
      initial_topologically_generates
  }

/--
The chosen free pro-`3` group on the five tame generators.
-/
noncomputable def initialKochFree :
    ProP.FreeGroup.{0} 3 5 :=
  ProP.freeGroup 3 5

/--
The continuous quotient candidate induced by the five tame generators.
-/
noncomputable def initialKochHom :
    ProP.ContinuousHom initialKochFree.Carrier initialGaloisGroup :=
  freeLift
    initialKochFree
    initial_pro_three
    initialGeneratorData

/--
The underlying homomorphism of the Koch quotient candidate.
-/
noncomputable def initialKochQuotient :
    initialKochFree.Carrier →* initialGaloisGroup :=
  initialKochHom.toMonoidHom

/--
The Koch quotient candidate is continuous.
-/
lemma initial_quotient_continuous :
    Continuous initialKochQuotient := by
  exact
    initialKochHom.continuous_toFun

/--
The Koch quotient candidate sends the universal generator at `i` to the
chosen tame generator at `i`.
-/
lemma initial_koch_generator
    (i : Fin 5) :
    initialKochQuotient (initialKochFree.generator i) =
      initialGeneratorData.generator i := by
  exact
    freeLift_generator
      initialKochFree
      initial_pro_three
      initialGeneratorData
      i

/--
The candidate map is onto because the chosen tame generators are
topological generators.
-/
lemma initial_quotient_surjective :
    Function.Surjective initialKochQuotient := by
  exact
    freeLift_surjective
      initialKochFree
      initial_pro_three
      initialGeneratorData

/--
The standard tame local relator at the `i`th prime.  The second argument is a
lift of the corresponding Frobenius element to the free pro-`3` group.
-/
def initialTameRelator
    (frobeniusLift : Fin 5 → initialKochFree.Carrier)
    (i : Fin 5) :
    initialKochFree.Carrier :=
  initialKochFree.generator i ^ initialTameExponent i *
    ⁅initialKochFree.generator i, frobeniusLift i⁆

/--
Local arithmetic data for the five tame primes: a Frobenius lift at each
prime for which the standard tame local relation vanishes in the Galois
group.
-/
structure KRData where
  frobeniusLift :
    Fin 5 → initialKochFree.Carrier
  tame_maps_one :
    ∀ i,
      initialKochQuotient (initialTameRelator frobeniusLift i) = 1

/-!
### Lifting quotient-side local relations

The arithmetic tame relation naturally lives in the Galois group: inertia and
Frobenius satisfy a relation there.  The presentation scaffold needs a
Frobenius lift in the free pro-`3` group.  The following reusable bridge
separates those two tasks.  Its only group-theoretic input is a surjective
homomorphism carrying the displayed source generators to the displayed target
generators.
-/

namespace KRScaffo

universe u v w

/--
The standard tame relator attached to a displayed generator, exponent, and
Frobenius element.

This generic version makes the quotient-to-lift argument independent of the
specific initial Galois group.
-/
def tameRelator
    {F : Type u}
    [Group F]
    {ι : Type w}
    (generator : ι → F)
    (exponent : ι → ℕ)
    (frobenius : ι → F)
    (i : ι) :
    F :=
  generator i ^ exponent i *
    ⁅generator i, frobenius i⁆

/--
Quotient-side local arithmetic data: a Frobenius element at each displayed
prime and the corresponding tame relation in the target group.

This package does not mention a free group or any choice of lifts.
-/
structure QRData
    {G : Type v}
    [Group G]
    {ι : Type w}
    (generator : ι → G)
    (exponent : ι → ℕ) where
  frobenius :
    ι → G
  tameRelation :
    ∀ i,
      tameRelator generator exponent frobenius i = 1

namespace QRData

/--
The quotient-side tame relation can be unfolded into its familiar power times
commutator form.
-/
lemma power_commutator_one
    {G : Type v}
    [Group G]
    {ι : Type w}
    {generator : ι → G}
    {exponent : ι → ℕ}
    (D : QRData generator exponent)
    (i : ι) :
    generator i ^ exponent i *
        ⁅generator i, D.frobenius i⁆ =
      1 := by
  change
    tameRelator generator exponent D.frobenius i =
      1
  exact
    D.tameRelation i

end QRData

/--
A displayed source generator family maps to a displayed target generator
family under a homomorphism.
-/
structure GLData
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (sourceGenerator : ι → F)
    (targetGenerator : ι → G) where
  generator_mapsTo :
    ∀ i,
      q (sourceGenerator i) =
        targetGenerator i

namespace GLData

/--
Mapping a tame relator maps the displayed source generator and the chosen
Frobenius lift pointwise.
-/
lemma map_tameRelator
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : GLData q sourceGenerator targetGenerator)
    (exponent : ι → ℕ)
    (frobeniusLift : ι → F)
    (i : ι) :
    q (tameRelator sourceGenerator exponent frobeniusLift i) =
      tameRelator
        targetGenerator
        exponent
        (fun j => q (frobeniusLift j))
        i := by
  simp [
    tameRelator,
    L.generator_mapsTo,
    map_commutatorElement
  ]

/--
If the chosen Frobenius lifts map to a target-side Frobenius family, then
mapping the source relator gives exactly the corresponding target relator.
-/
lemma tame_frobenius_maps
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : GLData q sourceGenerator targetGenerator)
    (exponent : ι → ℕ)
    (frobeniusLift : ι → F)
    (frobenius : ι → G)
    (hfrobenius :
      ∀ i,
        q (frobeniusLift i) =
          frobenius i)
    (i : ι) :
    q (tameRelator sourceGenerator exponent frobeniusLift i) =
      tameRelator targetGenerator exponent frobenius i := by
  rw [
    L.map_tameRelator
      exponent
      frobeniusLift
      i
  ]
  simp [
    tameRelator,
    hfrobenius
  ]

end GLData

/--
Lifted local relation data in the source group.  This is the formal output
needed after choosing pointwise Frobenius preimages.
-/
structure LRData
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (sourceGenerator : ι → F)
    (exponent : ι → ℕ) where
  frobeniusLift :
    ι → F
  tame_maps_one :
    ∀ i,
      q (tameRelator sourceGenerator exponent frobeniusLift i) = 1

namespace LRData

/--
Each relator in lifted local relation data belongs to the kernel of the
quotient homomorphism.
-/
lemma tame_relator_kernel
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {exponent : ι → ℕ}
    (D : LRData q sourceGenerator exponent)
    (i : ι) :
    tameRelator sourceGenerator exponent D.frobeniusLift i ∈
      q.ker := by
  apply
    MonoidHom.mem_ker.mpr
  exact
    D.tame_maps_one i

/--
The algebraic normal closure of a lifted tame-relator family lies in the
quotient kernel.
-/
lemma normal_closure_kernel
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {exponent : ι → ℕ}
    (D : LRData q sourceGenerator exponent) :
    Subgroup.normalClosure
        (Set.range
          (tameRelator sourceGenerator exponent D.frobeniusLift)) ≤
      q.ker := by
  apply
    Subgroup.normalClosure_le_normal
  rintro _ ⟨i, rfl⟩
  exact
    D.tame_relator_kernel i

end LRData

/--
A generator-lift package together with surjectivity.  Surjectivity is exactly
what is needed to choose a source Frobenius lift for each target Frobenius
element.
-/
structure SLData
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    (q : F →* G)
    (sourceGenerator : ι → F)
    (targetGenerator : ι → G)
    extends GLData q sourceGenerator targetGenerator where
  surjective :
    Function.Surjective q

namespace SLData

/--
Choose one source lift for every target-side Frobenius element.
-/
noncomputable def frobeniusLift
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : SLData q sourceGenerator targetGenerator)
    {exponent : ι → ℕ}
    (D : QRData targetGenerator exponent) :
    ι → F :=
  fun i =>
    Classical.choose
      (L.surjective (D.frobenius i))

/--
The chosen source Frobenius lift maps back to the target-side Frobenius
element.
-/
lemma frobenius_lift_maps
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : SLData q sourceGenerator targetGenerator)
    {exponent : ι → ℕ}
    (D : QRData targetGenerator exponent)
    (i : ι) :
    q (L.frobeniusLift D i) =
      D.frobenius i := by
  exact
    Classical.choose_spec
      (L.surjective (D.frobenius i))

/--
Mapping a relator built from the chosen source Frobenius lifts gives the
target-side tame relator.
-/
lemma tame_relator_lift
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : SLData q sourceGenerator targetGenerator)
    {exponent : ι → ℕ}
    (D : QRData targetGenerator exponent)
    (i : ι) :
    q (tameRelator sourceGenerator exponent (L.frobeniusLift D) i) =
      tameRelator targetGenerator exponent D.frobenius i := by
  apply
    L.toGLData.tame_frobenius_maps
      exponent
      (L.frobeniusLift D)
      D.frobenius
      (L.frobenius_lift_maps D)
      i

/--
The lifted tame relator maps to one because the quotient-side arithmetic
relation maps to one.
-/
lemma tame_frobenius_lift
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : SLData q sourceGenerator targetGenerator)
    {exponent : ι → ℕ}
    (D : QRData targetGenerator exponent)
    (i : ι) :
    q (tameRelator sourceGenerator exponent (L.frobeniusLift D) i) =
      1 := by
  rw [
    L.tame_relator_lift
      D
      i
  ]
  exact
    D.tameRelation i

/--
Lift quotient-side local relation data through a surjective homomorphism.
-/
noncomputable def liftRelationData
    {F : Type u}
    {G : Type v}
    [Group F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {sourceGenerator : ι → F}
    {targetGenerator : ι → G}
    (L : SLData q sourceGenerator targetGenerator)
    {exponent : ι → ℕ}
    (D : QRData targetGenerator exponent) :
    LRData q sourceGenerator exponent where
  frobeniusLift :=
    L.frobeniusLift D
  tame_maps_one :=
    L.tame_frobenius_lift D

end SLData

end KRScaffo

/--
The chosen free quotient map sends the universal generators to the selected
tame inertia generators and is surjective.
-/
noncomputable def initialLiftData :
    KRScaffo.SLData
      initialKochQuotient
      initialKochFree.generator
      initialGeneratorData.generator where
  generator_mapsTo :=
    initial_koch_generator
  surjective :=
    initial_quotient_surjective

/--
The genuinely arithmetic local input stated in the target Galois group:
choose Frobenius elements satisfying the five tame relations.

Unlike `KRData`, this asks for no free-group lifts.
-/
abbrev InitialKochData :=
  KRScaffo.QRData
    initialGeneratorData.generator
    initialTameExponent

set_option maxHeartbeats 1000000 in
-- lots of instances
set_option synthInstance.maxHeartbeats 200000 in
/--
Arithmetic input at an arbitrary initially ramified prime: choose one
quotient-side Frobenius element satisfying its tame relation.

This indexed statement replaces the five prime-specific local obligations.
-/
theorem initial_local_relation
    (i : Fin 5) :
    ∃ frobenius : initialGaloisGroup,
      initialGeneratorData.generator i ^
            initialTameExponent i *
          ⁅initialGeneratorData.generator i, frobenius⁆ =
        1 := by
  classical
  let relator : initialGaloisGroup → initialGaloisGroup :=
    fun frobenius =>
      initialGeneratorData.generator i ^
            initialTameExponent i *
          ⁅initialGeneratorData.generator i, frobenius⁆
  let solutionSet :
      OpenNormalSubgroup initialGaloisGroup → Set initialGaloisGroup :=
    fun N =>
      {frobenius | relator frobenius ∈ (N : Subgroup initialGaloisGroup)}
  have hrelatorContinuous :
      Continuous relator := by
    dsimp [relator]
    simp only [commutatorElement_def]
    fun_prop
  have hsolutionSetClosed :
      ∀ N : OpenNormalSubgroup initialGaloisGroup,
        IsClosed (solutionSet N) := by
    intro N
    change
      IsClosed
        (relator ⁻¹' (N : Set initialGaloisGroup))
    exact
      N.toOpenSubgroup.isClosed.preimage
        hrelatorContinuous
  have hsolutionSetFiniteIntersection :
      ∀ s : Finset (OpenNormalSubgroup initialGaloisGroup),
        (⋂ N ∈ s, solutionSet N).Nonempty := by
    intro s
    let M : OpenNormalSubgroup initialGaloisGroup :=
      s.inf (fun N : OpenNormalSubgroup initialGaloisGroup => N)
    have hKNfg :
        FiniteDimensional ℚ (initialKochLayer M) ∧
          IsGalois ℚ (initialKochLayer M) := by
      simpa [initialKochLayer, initialKochClosed] using
        (STBuild.initial_galois_open M)
    letI : FiniteDimensional ℚ (initialKochLayer M) :=
      hKNfg.1
    letI : IsGalois ℚ (initialKochLayer M) :=
      hKNfg.2
    letI : NumberField (initialKochLayer M) :=
      NumberField.of_module_finite ℚ (initialKochLayer M)
    let D :=
      initialInertiaData.finiteLayerData M
    let r : InitialKochRamified :=
      initialRamifiedOrder i
    let P :=
      D.primeAbove r
    have hPmem :=
      D.primeAbove_mem r
    letI : P.IsPrime :=
      hPmem.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal r.1) :=
      hPmem.2
    have hrPrime :
        Nat.Prime r.1 := by
      exact
        ramified_primes_prime
          r.1
          r.2
    have hPGroup :
        IsPGroup 3 (Gal(initialKochLayer M / ℚ)) := by
      exact
        @STBuild.initial_pro_subextension
          (IntermediateField.fixedField
            (initialKochClosed M).1)
          hKNfg.1
          hKNfg.2
    have hCardCoprime :
        Nat.Coprime r.1
          (Nat.card (Gal(initialKochLayer M / ℚ))) :=
      STBuild.p_coprime_ramified
        hPGroup
        r
    have hTame :
        RationalTamePrimes
          (S := NumberField.RingOfIntegers (initialKochLayer M))
          r.1 :=
      STBuild.primes_coprime_card
        (L := initialKochLayer M)
        hrPrime
        hCardCoprime
    letI : Finite (Gal(initialKochLayer M / ℚ)) :=
      IsGaloisGroup.finite
        (Gal(initialKochLayer M / ℚ))
        ℚ
        (initialKochLayer M)
    let hstRat :
        IsScalarTower
          ℤ
          ℚ
          (initialKochLayer M) :=
      by
        refine IsScalarTower.of_algebraMap_eq ?_
        intro z
        simp
    let hstInt :
        IsScalarTower
          ℤ
          (NumberField.RingOfIntegers (initialKochLayer M))
          (initialKochLayer M) :=
      STBuild.integers_scalar_tower
        (K := initialKochLayer M)
    letI :
        IsGaloisGroup
          (Gal(initialKochLayer M / ℚ))
          ℤ
          (NumberField.RingOfIntegers (initialKochLayer M)) :=
      by
        exact
          @IsGaloisGroup.of_isFractionRing
            (Gal(initialKochLayer M / ℚ))
            ℤ
            (NumberField.RingOfIntegers (initialKochLayer M))
            ℚ
            (initialKochLayer M)
            _ _ _ _ _ _ _ _ _ _ _ _ _
            hstRat
            hstInt
            _ _ _ _ _
    letI :
        Algebra.IsInvariant
          ℤ
          (NumberField.RingOfIntegers (initialKochLayer M))
          (Gal(initialKochLayer M / ℚ)) :=
      inferInstance
    have hPne :
        P ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot
        (rational_ne_bot hrPrime)
        P
    letI :
        Finite
          (NumberField.RingOfIntegers (initialKochLayer M) ⧸ P) :=
      Ideal.finiteQuotientOfFreeOfNeBot
        P
        hPne
    let σ : Gal(initialKochLayer M / ℚ) :=
      arithFrobAt
        ℤ
        (Gal(initialKochLayer M / ℚ))
        P
    have hσ :
        IsArithFrobAt ℤ σ P := by
      simpa [σ] using
        (IsArithFrobAt.arithFrobAt
          (R := ℤ)
          (S := NumberField.RingOfIntegers (initialKochLayer M))
          (G := Gal(initialKochLayer M / ℚ))
          (Q := P))
    have hconj :
        σ *
              (D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ)) *
            σ⁻¹ =
          (D.inertiaGenerator r :
            Gal(initialKochLayer M / ℚ)) ^ r.1 :=
      Submission.arith_frob_inertia
        (L := initialKochLayer M)
        hrPrime
        hTame
        P
        σ
        hσ
        (D.inertiaGenerator r)
    have hfiniteRelation :
        (D.inertiaGenerator r :
              Gal(initialKochLayer M / ℚ)) ^ (r.1 - 1) *
            ⁅(D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ)), σ⁆ =
          1 := by
      rw [commutatorElement_def]
      calc
        (D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ)) ^ (r.1 - 1) *
              ((D.inertiaGenerator r :
                    Gal(initialKochLayer M / ℚ)) *
                σ *
                (D.inertiaGenerator r :
                    Gal(initialKochLayer M / ℚ))⁻¹ *
                σ⁻¹) =
            (((D.inertiaGenerator r :
                    Gal(initialKochLayer M / ℚ)) ^ (r.1 - 1) *
                (D.inertiaGenerator r :
                  Gal(initialKochLayer M / ℚ))) *
              σ *
              (D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ))⁻¹ *
              σ⁻¹) := by
                group
        _ =
            (D.inertiaGenerator r :
                  Gal(initialKochLayer M / ℚ)) ^ r.1 *
              σ *
              (D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ))⁻¹ *
              σ⁻¹ := by
                rw [← pow_succ, Nat.sub_add_cancel hrPrime.one_le]
        _ =
            (σ *
                  (D.inertiaGenerator r :
                    Gal(initialKochLayer M / ℚ)) *
                σ⁻¹) *
              σ *
              (D.inertiaGenerator r :
                Gal(initialKochLayer M / ℚ))⁻¹ *
              σ⁻¹ := by
                rw [hconj]
        _ = 1 := by
              group
    have hgenerator :
        initialKochEquiv M
              (IGScaffoa.quotientMap M
                (initialGeneratorData.generator i)) =
            (D.inertiaGenerator r :
              Gal(initialKochLayer M / ℚ)) := by
      change
        initialKochEquiv M
              (IGScaffoa.quotientMap M
                (initialInertiaGenerator r)) =
            (D.inertiaGenerator r :
              Gal(initialKochLayer M / ℚ))
      unfold
        initialInertiaGenerator
      rw [
        initialInertiaData.mapsFiniteLayer
          M
          r,
        D.generator_eq
      ]
      simp
    obtain ⟨frobenius, hfrobenius⟩ :=
      IGScaffoa.quotientMap_surjective
        M
        ((initialKochEquiv M).symm σ)
    have hfrobenius' :
        initialKochEquiv M
              (IGScaffoa.quotientMap M frobenius) =
            σ := by
      rw [
        hfrobenius
      ]
      simp
    have hquotientRelation :
        IGScaffoa.quotientMap M
              (initialGeneratorData.generator i ^
                    initialTameExponent i *
                  ⁅initialGeneratorData.generator i, frobenius⁆) =
            1 := by
      calc
        IGScaffoa.quotientMap M
              (initialGeneratorData.generator i ^
                    initialTameExponent i *
                  ⁅initialGeneratorData.generator i, frobenius⁆) =
            (IGScaffoa.quotientMap M
                  (initialGeneratorData.generator i)) ^
                initialTameExponent i *
              ⁅IGScaffoa.quotientMap M
                  (initialGeneratorData.generator i),
                IGScaffoa.quotientMap M frobenius⁆ := by
                  rw [
                    map_mul,
                    map_pow,
                    map_commutatorElement
                  ]
        _ = 1 := by
          apply
            (initialKochEquiv M).injective
          rw [
            map_mul,
            map_pow,
            map_commutatorElement,
            map_one,
            hgenerator,
            hfrobenius'
          ]
          simpa only [
            initialTameExponent,
            initialKochPrime,
            r
          ] using
            hfiniteRelation
    have hrelationMem :
        initialGeneratorData.generator i ^
              initialTameExponent i *
            ⁅initialGeneratorData.generator i, frobenius⁆ ∈
          (M : Subgroup initialGaloisGroup) := by
      apply
        (QuotientGroup.eq_one_iff
          (N := (M : Subgroup initialGaloisGroup))
          _).mp
      exact
        hquotientRelation
    refine
      ⟨frobenius, Set.mem_iInter₂.mpr ?_⟩
    intro N hN
    change
      relator frobenius ∈
        (N : Subgroup initialGaloisGroup)
    exact
      (show M ≤ N from by
        dsimp [M]
        exact Finset.inf_le hN) <| by
          simpa [relator] using
            hrelationMem
  obtain ⟨frobenius, hfrobenius⟩ :=
    CompactSpace.iInter_nonempty
      hsolutionSetClosed
      hsolutionSetFiniteIntersection
  refine
    ⟨frobenius, ?_⟩
  change
    relator frobenius =
      1
  by_contra hne
  obtain ⟨N, hN⟩ :=
    open_normal_not
      (Γ := initialGaloisGroup)
      hne
  apply
    hN
  exact
    Set.mem_iInter.mp
      hfrobenius
      N

/--
Arithmetic local data with retained Frobenius provenance.

The ambient Frobenius elements project to arithmetic Frobenii at the explicit
compatibly descending finite-layer primes stored with the tame inertia
generators.  Keeping the ambient elements makes those finite-layer Frobenius
choices compatible under further quotient maps.  The final field records the
tame relations they satisfy in the initial Galois group.
-/
structure IADataa where
  frobenius :
    InitialKochRamified → initialGaloisGroup
  frobenius_arith_frob :
    ∀ (N : OpenNormalSubgroup initialGaloisGroup)
      (r : InitialKochRamified),
      IsArithFrobAt ℤ
        (initialKochEquiv N
          (IGScaffoa.quotientMap N (frobenius r)))
        ((initialInertiaData.finiteLayerData N).primeAbove r)
  tameRelation :
    ∀ i : Fin 5,
      initialGeneratorData.generator i ^
            initialTameExponent i *
          ⁅initialGeneratorData.generator i,
            frobenius (initialRamifiedOrder i)⁆ =
        1

set_option maxHeartbeats 1000000 in
-- long proof
set_option synthInstance.maxHeartbeats 200000 in
/--
Arithmetic input: choose compatible ambient Frobenius elements at the five
initially ramified primes, retaining their finite-layer arithmetic
provenance and the resulting tame local relations.
-/
theorem initial_arithmetic_nonempty :
    Nonempty IADataa := by
  classical
  let frobeniusSet :
      OpenNormalSubgroup initialGaloisGroup →
        InitialKochRamified → Set initialGaloisGroup :=
    fun N r =>
      {frobenius |
        IsArithFrobAt ℤ
          (initialKochEquiv N
            (IGScaffoa.quotientMap N frobenius))
          ((initialInertiaData.finiteLayerData N).primeAbove r)}
  have hfrobeniusSetClosed :
      ∀ (N : OpenNormalSubgroup initialGaloisGroup)
        (r : InitialKochRamified),
        IsClosed (frobeniusSet N r) := by
    intro N r
    change
      IsClosed
        ((IGScaffoa.quotientMap N) ⁻¹'
          {x |
            IsArithFrobAt ℤ
              (initialKochEquiv N x)
              ((initialInertiaData.finiteLayerData N).primeAbove r)})
    exact
      (Set.toFinite
        {x : initialGaloisGroup ⧸ N.toSubgroup |
          IsArithFrobAt ℤ
            (initialKochEquiv N x)
            ((initialInertiaData.finiteLayerData N).primeAbove
              r)}).isClosed.preimage
        (IGScaffoa.quotientMap_continuous N)
  have hfrobeniusSetFiniteIntersection :
      ∀ (r : InitialKochRamified)
        (s : Finset (OpenNormalSubgroup initialGaloisGroup)),
        (⋂ N ∈ s, frobeniusSet N r).Nonempty := by
    intro r s
    let M : OpenNormalSubgroup initialGaloisGroup :=
      s.inf (fun N : OpenNormalSubgroup initialGaloisGroup => N)
    have hMfg :
        FiniteDimensional ℚ (initialKochLayer M) ∧
          IsGalois ℚ (initialKochLayer M) := by
      simpa [initialKochLayer, initialKochClosed] using
        (STBuild.initial_galois_open M)
    letI : FiniteDimensional ℚ (initialKochLayer M) :=
      hMfg.1
    letI : IsGalois ℚ (initialKochLayer M) :=
      hMfg.2
    letI : NumberField (initialKochLayer M) :=
      NumberField.of_module_finite ℚ (initialKochLayer M)
    let PM :=
      (initialInertiaData.finiteLayerData M).primeAbove r
    have hPMmem :=
      (initialInertiaData.finiteLayerData M).primeAbove_mem r
    letI : PM.IsPrime :=
      hPMmem.1
    letI : PM.LiesOver (Ideal.rationalPrimeIdeal r.1) :=
      hPMmem.2
    have hrPrime :
        Nat.Prime r.1 :=
      ramified_primes_prime r.1 r.2
    have hPMne :
        PM ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot
        (rational_ne_bot hrPrime)
        PM
    letI :
        Finite
          (NumberField.RingOfIntegers (initialKochLayer M) ⧸ PM) :=
      Ideal.finiteQuotientOfFreeOfNeBot
        PM
        hPMne
    let σM : Gal(initialKochLayer M / ℚ) :=
      arithFrobAt
        ℤ
        (Gal(initialKochLayer M / ℚ))
        PM
    have hσM :
        IsArithFrobAt ℤ σM PM := by
      simpa [σM] using
        (IsArithFrobAt.arithFrobAt
          (R := ℤ)
          (S := NumberField.RingOfIntegers (initialKochLayer M))
          (G := Gal(initialKochLayer M / ℚ))
          (Q := PM))
    obtain ⟨frobenius, hfrobenius⟩ :=
      IGScaffoa.quotientMap_surjective
        M
        ((initialKochEquiv M).symm σM)
    refine
      ⟨frobenius, Set.mem_iInter₂.mpr ?_⟩
    intro N hN
    have hMN :
        M ≤ N := by
      dsimp [M]
      exact Finset.inf_le hN
    have hNfg :
        FiniteDimensional ℚ (initialKochLayer N) ∧
          IsGalois ℚ (initialKochLayer N) := by
      simpa [initialKochLayer, initialKochClosed] using
        (STBuild.initial_galois_open N)
    letI : FiniteDimensional ℚ (initialKochLayer N) :=
      hNfg.1
    letI : IsGalois ℚ (initialKochLayer N) :=
      hNfg.2
    letI : NumberField (initialKochLayer N) :=
      NumberField.of_module_finite ℚ (initialKochLayer N)
    have hfieldMN :
        (IntermediateField.fixedField
            (initialKochClosed N).1) ≤
          IntermediateField.fixedField
            (initialKochClosed M).1 :=
      IntermediateField.fixedField_le hMN
    letI :
        Algebra (initialKochLayer N) (initialKochLayer M) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hfieldMN).toRingHom
    letI :
        IsScalarTower ℚ (initialKochLayer N) (initialKochLayer M) :=
      IsScalarTower.of_algebraMap_eq
        (congrFun rfl)
    letI :
        IsScalarTower
          (initialKochLayer N)
          (initialKochLayer M)
          initialProExtension :=
      IsScalarTower.of_algebraMap_eq'
        rfl
    let PN :=
      (initialInertiaData.finiteLayerData N).primeAbove r
    have hPNmem :=
      (initialInertiaData.finiteLayerData N).primeAbove_mem r
    letI : PN.IsPrime :=
      hPNmem.1
    letI : PN.LiesOver (Ideal.rationalPrimeIdeal r.1) :=
      hPNmem.2
    have hPMunder :
        PM.under (NumberField.RingOfIntegers (initialKochLayer N)) =
          PN := by
      simpa [PM, PN, Ideal.under,
        initialIntegersInclusion] using
        (initialInertiaData.primeAbove_comap hMN r)
    have hσMN :
        IsArithFrobAt ℤ
          (σM.restrictNormalHom (initialKochLayer N))
          PN := by
      simpa [hPMunder] using
        (arith_frob_int
          (E := initialKochLayer N)
          (L := initialKochLayer M)
          hσM)
    change
      IsArithFrobAt ℤ
        (initialKochEquiv N
          (IGScaffoa.quotientMap N frobenius))
        PN
    have hfrobeniusM :
        initialKochEquiv M
            (IGScaffoa.quotientMap M frobenius) =
          σM := by
      rw [hfrobenius]
      simp
    have hrestrict :
        (initialKochEquiv M
            (IGScaffoa.quotientMap M frobenius)).restrictNormalHom
              (initialKochLayer N) =
          initialKochEquiv N
            (IGScaffoa.quotientMap N frobenius) := by
      change
        (AlgEquiv.restrictNormalHom (initialKochLayer N))
            ((AlgEquiv.restrictNormalHom (initialKochLayer M))
              frobenius) =
          (AlgEquiv.restrictNormalHom (initialKochLayer N))
            frobenius
      exact
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
          (initialKochLayer N)
          (initialKochLayer M)
          frobenius).symm
    rw [← hrestrict, hfrobeniusM]
    exact hσMN
  have hfrobeniusExists :
      ∀ r : InitialKochRamified,
        ∃ frobenius : initialGaloisGroup,
          ∀ N : OpenNormalSubgroup initialGaloisGroup,
            frobenius ∈ frobeniusSet N r := by
    intro r
    obtain ⟨frobenius, hfrobenius⟩ :=
      CompactSpace.iInter_nonempty
        (fun N => hfrobeniusSetClosed N r)
        (hfrobeniusSetFiniteIntersection r)
    exact
      ⟨frobenius, Set.mem_iInter.mp hfrobenius⟩
  choose frobenius hfrobenius using hfrobeniusExists
  refine
    ⟨{
      frobenius := frobenius
      frobenius_arith_frob :=
        fun N r => hfrobenius r N
      tameRelation := ?_
    }⟩
  intro i
  let r : InitialKochRamified :=
    initialRamifiedOrder i
  let relator : initialGaloisGroup :=
    initialGeneratorData.generator i ^
          initialTameExponent i *
        ⁅initialGeneratorData.generator i, frobenius r⁆
  change
    relator =
      1
  by_contra hrelator
  obtain ⟨N, hN⟩ :=
    open_normal_not
      (Γ := initialGaloisGroup)
      hrelator
  have hNfg :
      FiniteDimensional ℚ (initialKochLayer N) ∧
        IsGalois ℚ (initialKochLayer N) := by
    simpa [initialKochLayer, initialKochClosed] using
      (STBuild.initial_galois_open N)
  letI : FiniteDimensional ℚ (initialKochLayer N) :=
    hNfg.1
  letI : IsGalois ℚ (initialKochLayer N) :=
    hNfg.2
  letI : NumberField (initialKochLayer N) :=
    NumberField.of_module_finite ℚ (initialKochLayer N)
  let D :=
    initialInertiaData.finiteLayerData N
  let P :=
    D.primeAbove r
  have hPmem :=
    D.primeAbove_mem r
  letI : P.IsPrime :=
    hPmem.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal r.1) :=
    hPmem.2
  have hrPrime :
      Nat.Prime r.1 :=
    ramified_primes_prime r.1 r.2
  have hPGroup :
      IsPGroup 3 (Gal(initialKochLayer N / ℚ)) := by
    exact
      @STBuild.initial_pro_subextension
        (IntermediateField.fixedField
          (initialKochClosed N).1)
        hNfg.1
        hNfg.2
  have hCardCoprime :
      Nat.Coprime r.1
        (Nat.card (Gal(initialKochLayer N / ℚ))) :=
    STBuild.p_coprime_ramified
      hPGroup
      r
  have hTame :
      RationalTamePrimes
        (S := NumberField.RingOfIntegers (initialKochLayer N))
        r.1 :=
    STBuild.primes_coprime_card
      (L := initialKochLayer N)
      hrPrime
      hCardCoprime
  have hσ :
      IsArithFrobAt ℤ
        (initialKochEquiv N
          (IGScaffoa.quotientMap N (frobenius r)))
        P := by
    exact hfrobenius r N
  have hconj :
      initialKochEquiv N
            (IGScaffoa.quotientMap N (frobenius r)) *
          (D.inertiaGenerator r :
            Gal(initialKochLayer N / ℚ)) *
          (initialKochEquiv N
            (IGScaffoa.quotientMap N (frobenius r)))⁻¹ =
        (D.inertiaGenerator r :
          Gal(initialKochLayer N / ℚ)) ^ r.1 :=
    Submission.arith_frob_inertia
      (L := initialKochLayer N)
      hrPrime
      hTame
      P
      (initialKochEquiv N
        (IGScaffoa.quotientMap N (frobenius r)))
      hσ
      (D.inertiaGenerator r)
  have hgenerator :
      initialKochEquiv N
            (IGScaffoa.quotientMap N
              (initialGeneratorData.generator i)) =
          (D.inertiaGenerator r :
            Gal(initialKochLayer N / ℚ)) := by
    change
      initialKochEquiv N
            (IGScaffoa.quotientMap N
              (initialInertiaGenerator r)) =
          (D.inertiaGenerator r :
            Gal(initialKochLayer N / ℚ))
    unfold
      initialInertiaGenerator
    rw [
      initialInertiaData.mapsFiniteLayer
        N
        r,
      D.generator_eq
    ]
    simp
  have hfiniteRelation :
    (D.inertiaGenerator r :
          Gal(initialKochLayer N / ℚ)) ^
        (r.1 - 1) *
      ⁅(D.inertiaGenerator r :
          Gal(initialKochLayer N / ℚ)),
        initialKochEquiv N
          (IGScaffoa.quotientMap N (frobenius r))⁆ =
      1 := by
    rw [commutatorElement_def]
    calc
      (D.inertiaGenerator r :
              Gal(initialKochLayer N / ℚ)) ^ (r.1 - 1) *
            ((D.inertiaGenerator r :
                  Gal(initialKochLayer N / ℚ)) *
              initialKochEquiv N
                (IGScaffoa.quotientMap N (frobenius r)) *
              (D.inertiaGenerator r :
                Gal(initialKochLayer N / ℚ))⁻¹ *
              (initialKochEquiv N
                (IGScaffoa.quotientMap N (frobenius r)))⁻¹) =
          (((D.inertiaGenerator r :
                  Gal(initialKochLayer N / ℚ)) ^ (r.1 - 1) *
              (D.inertiaGenerator r :
                Gal(initialKochLayer N / ℚ))) *
            initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)) *
            (D.inertiaGenerator r :
              Gal(initialKochLayer N / ℚ))⁻¹ *
            (initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)))⁻¹) := by
                group
      _ =
          (D.inertiaGenerator r :
                Gal(initialKochLayer N / ℚ)) ^ r.1 *
            initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)) *
            (D.inertiaGenerator r :
              Gal(initialKochLayer N / ℚ))⁻¹ *
            (initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)))⁻¹ := by
                rw [← pow_succ, Nat.sub_add_cancel hrPrime.one_le]
      _ =
          (initialKochEquiv N
                (IGScaffoa.quotientMap N (frobenius r)) *
              (D.inertiaGenerator r :
                Gal(initialKochLayer N / ℚ)) *
              (initialKochEquiv N
                (IGScaffoa.quotientMap N (frobenius r)))⁻¹) *
            initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)) *
            (D.inertiaGenerator r :
              Gal(initialKochLayer N / ℚ))⁻¹ *
            (initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r)))⁻¹ := by
                rw [hconj]
      _ = 1 := by
        group
  apply hN
  apply
    (QuotientGroup.eq_one_iff
      (N := (N : Subgroup initialGaloisGroup))
      relator).mp
  apply
    (initialKochEquiv N).injective
  calc
    initialKochEquiv N
          (IGScaffoa.quotientMap N relator) =
        (initialKochEquiv N
              (IGScaffoa.quotientMap N
                (initialGeneratorData.generator i))) ^
            initialTameExponent i *
          ⁅initialKochEquiv N
              (IGScaffoa.quotientMap N
                (initialGeneratorData.generator i)),
            initialKochEquiv N
              (IGScaffoa.quotientMap N (frobenius r))⁆ := by
                dsimp [relator]
                rw [
                  map_mul,
                  map_pow,
                  map_commutatorElement,
                  map_mul,
                  map_pow,
                  map_commutatorElement
                ]
    _ = 1 := by
      rw [hgenerator]
      simpa only [
        initialTameExponent,
        initialKochPrime,
        r
      ] using
        hfiniteRelation
    _ =
        initialKochEquiv N
          (IGScaffoa.quotientMap N 1) := by
            simp

/--
A fixed provenance-preserving choice of local arithmetic data.
-/
noncomputable def initialArithmeticData :
    IADataa :=
  Classical.choice initial_arithmetic_nonempty

/--
Forget Frobenius provenance after constructing the quotient-side tame
relations consumed by the presentation scaffold.
-/
noncomputable def IADataa.quot_local_reldata
    (D : IADataa) :
    InitialKochData where
  frobenius :=
    fun i => D.frobenius (initialRamifiedOrder i)
  tameRelation := by
    intro i
    exact
      D.tameRelation i

/--
The fixed target-side local tame relations are obtained from the
provenance-preserving arithmetic datum.
-/
noncomputable def initialKochData :
    InitialKochData :=
  initialArithmeticData.quot_local_reldata

/--
Lift the fixed target-side tame relations through the free quotient map.
-/
noncomputable def initialLiftedData :
    KRScaffo.LRData
      initialKochQuotient
      initialKochFree.generator
      initialTameExponent :=
  initialLiftData.liftRelationData
    initialKochData

/--
The specialized tame relator agrees definitionally with the generic scaffold
relator.
-/
lemma initial_tame_scaffold
    (frobeniusLift : Fin 5 → initialKochFree.Carrier)
    (i : Fin 5) :
    initialTameRelator frobeniusLift i =
      KRScaffo.tameRelator
        initialKochFree.generator
        initialTameExponent
        frobeniusLift
        i := by
  rfl

/--
The lifted target-side arithmetic data supplies the specialized local
relation package expected by the Koch presentation assembly.
-/
noncomputable def initial_koch_relation
    (D : InitialKochData) :
    KRData := by
  let L :=
    initialLiftData.liftRelationData D
  exact
    {
      frobeniusLift :=
        L.frobeniusLift
      tame_maps_one := by
        intro i
        rw [
          initial_tame_scaffold
            L.frobeniusLift
            i
        ]
        exact
          L.tame_maps_one i
    }

namespace KRData

/--
Forget the arithmetic shape of the local tame relators and retain the finite
relator family consumed by the generic presentation scaffold.
-/
def toRData
    (D : KRData) :
    RData 5 initialKochQuotient where
  relator :=
    initialTameRelator D.frobeniusLift
  relator_maps_one :=
    D.tame_maps_one

/--
Each chosen local tame relation belongs to the quotient kernel.
-/
lemma tame_relator_kernel
    (D : KRData)
    (i : Fin 5) :
    initialTameRelator D.frobeniusLift i ∈
      initialKochQuotient.ker := by
  exact
    D.toRData.relator_mem_kernel i

/--
The algebraic normal closure of the local tame relations lies in the quotient
kernel.
-/
lemma normal_closure_kernel
    (D : KRData) :
    Subgroup.normalClosure
        (Set.range (initialTameRelator D.frobeniusLift)) ≤
      initialKochQuotient.ker := by
  exact
    D.toRData.normal_closure_kernel

/--
The topological normal closure of the local tame relations lies in the
quotient kernel.
-/
lemma topological_normal_closure
    (D : KRData) :
    (Subgroup.normalClosure
        (Set.range (initialTameRelator D.frobeniusLift))).topologicalClosure ≤
      initialKochQuotient.ker := by
  exact
    D.toRData.topological_normal_closure
      initial_quotient_continuous

end KRData

/--
Arithmetic input two: choose Frobenius lifts satisfying the five standard
local tame relations.

This is smaller than the final theorem: it proves only that five explicit
elements lie in the quotient kernel.  It does not claim that they generate
the kernel.
-/
theorem initial_data_nonempty :
    Nonempty KRData := by
  exact
    ⟨initial_koch_relation
      initialKochData⟩

end TBluepr
end Submission
