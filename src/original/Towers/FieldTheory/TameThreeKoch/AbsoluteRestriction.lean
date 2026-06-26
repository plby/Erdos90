import Towers.FieldTheory.TameThreeKoch.CyclotomicCubicSubfields
import Towers.FieldTheory.RationalRamificationCleanup
import Towers.FieldTheory.CyclotomicCleanupAssembly
import Towers.FieldTheory.FinalCleanupAssembly
import Towers.FieldTheory.ConductorNineAssembly
import Towers.ClassField.GrunwaldWang.IdeleCharacterGlobalization
import Towers.NumberTheory.Galois.DecompositionGroup
import Towers.ClassField.IdeleCohomology.CompletionConjugation
import Towers.Group.ProPTopology
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Fintype.Shrink

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

universe u v

open NumberField
open Towers.CField.Ideles
open Towers.CField.LBrauer

-- Ramification-cleanup factorization lemmas are developed below.

local instance part2FiniteGaloisIntermediateFieldFiniteDimensional
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ K :=
  K.finiteDimensional

local instance part2FiniteGaloisIntermediateFieldIsGalois
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ K :=
  K.isGalois

local instance part2AlgebraicClosureAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isAlgebraic ℚ (AlgebraicClosure ℚ) inferInstance
    inferInstance inferInstance inferInstance (AlgebraicClosure.instIsAlgClosure ℚ)

local instance part2AlgebraicClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) := by
  rw [normal_iff]
  intro x
  exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

local instance algebraicClosureIsGalois :
    IsGalois ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
    inferInstance inferInstance inferInstance
    (AlgebraicClosure.instIsAlgClosure ℚ) inferInstance

/-- Conjugating automorphisms along an algebra equivalence is continuous for
the Krull topologies. -/
theorem autCongr_continuous
    {k Omega Omega' : Type*}
    [Field k] [Field Omega] [Field Omega']
    [Algebra k Omega] [Algebra k Omega']
    (e : Omega ≃ₐ[k] Omega') :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨L, hLfin, hLs⟩ := hs
  let L' : IntermediateField k Omega := L.map e.symm.toAlgHom
  letI : FiniteDimensional k L := hLfin
  letI : FiniteDimensional k L' :=
    Module.Finite.equiv
      (IntermediateField.equivMap L e.symm.toAlgHom).toLinearEquiv
  apply Filter.mem_of_superset
    (show (L'.fixingSubgroup : Set Gal(Omega/k)) ∈ 𝓝 1 from
      IsOpen.mem_nhds L'.fixingSubgroup_isOpen (Subgroup.one_mem _))
  intro sigma hsigma
  apply hLs
  intro x
  have hfix := hsigma (IntermediateField.equivMap L e.symm.toAlgHom x)
  change sigma (e.symm (x : Omega')) = e.symm (x : Omega') at hfix
  change e (sigma (e.symm x)) = x
  rw [hfix]
  exact e.apply_symm_apply x

theorem aut_congr_continuous
    {k Omega Omega' : Type*}
    [Field k] [Field Omega] [Field Omega']
    [Algebra k Omega] [Algebra k Omega']
    (e : Omega ≃ₐ[k] Omega') :
    Continuous (AlgEquiv.autCongr e).symm := by
  rw [AlgEquiv.autCongr_symm]
  exact autCongr_continuous e.symm

private noncomputable def factorThroughSurjective
    {F G Q : Type*} [Group F] [Group G] [Group Q]
    (q : F →* G) (target : F →* Q)
    (hq : Function.Surjective q) (hker : q.ker ≤ target.ker) : G →* Q :=
  q.liftOfSurjective hq ⟨target, hker⟩

private lemma through_surjective_comp
    {F G Q : Type*} [Group F] [Group G] [Group Q]
    (q : F →* G) (target : F →* Q)
    (hq : Function.Surjective q) (hker : q.ker ≤ target.ker) :
    (factorThroughSurjective q target hq hker).comp q = target := by
  exact q.liftOfRightInverse_comp
    (Function.surjInv hq) (Function.rightInverse_surjInv hq) ⟨target, hker⟩

/-- An embedding between algebraic closures extending a prescribed embedding
of an intermediate algebraic field. -/
private noncomputable def algEmbeddingExtending
    {K L Omega Omega' : Type*}
    [Field K] [Field L] [Field Omega] [Field Omega']
    [Algebra K L] [Algebra K Omega] [Algebra L Omega]
    [IsScalarTower K L Omega] [Algebra.IsAlgebraic L Omega]
    [Algebra K Omega'] [IsAlgClosure K Omega] [IsAlgClosure K Omega']
    (i : L →ₐ[K] Omega') : Omega →ₐ[K] Omega' := by
  letI : IsAlgClosed Omega := IsAlgClosure.isAlgClosed K
  letI : IsAlgClosed Omega' := IsAlgClosure.isAlgClosed K
  exact Classical.choose
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (E := Omega) (M := Omega') i)

private theorem extending_restrict_domain
    {K L Omega Omega' : Type*}
    [Field K] [Field L] [Field Omega] [Field Omega']
    [Algebra K L] [Algebra K Omega] [Algebra L Omega]
    [IsScalarTower K L Omega] [Algebra.IsAlgebraic L Omega]
    [Algebra K Omega'] [IsAlgClosure K Omega] [IsAlgClosure K Omega']
    (i : L →ₐ[K] Omega') :
    (algEmbeddingExtending
      (K := K) (L := L) (Omega := Omega) (Omega' := Omega') i
      ).restrictDomain L = i := by
  letI : IsAlgClosed Omega' := IsAlgClosure.isAlgClosed K
  exact Classical.choose_spec
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (E := Omega) (M := Omega') i)

/-- An equivalence between algebraic closures can be chosen to extend a
specified embedding of an intermediate algebraic field. -/
noncomputable def algClosureExtending
    {K L Omega Omega' : Type*}
    [Field K] [Field L] [Field Omega] [Field Omega']
    [Algebra K L] [Algebra K Omega] [Algebra L Omega]
    [IsScalarTower K L Omega] [Algebra.IsAlgebraic L Omega]
    [Algebra K Omega'] [IsAlgClosure K Omega] [IsAlgClosure K Omega']
    (i : L →ₐ[K] Omega') : Omega ≃ₐ[K] Omega' := by
  letI : IsAlgClosed Omega := IsAlgClosure.isAlgClosed K
  letI : IsAlgClosed Omega' := IsAlgClosure.isAlgClosed K
  let e : Omega →ₐ[K] Omega' :=
    algEmbeddingExtending
      (K := K) (L := L) (Omega := Omega) (Omega' := Omega') i
  let eBack : Omega' →ₐ[K] Omega := IsAlgClosed.lift
  exact AlgEquiv.ofBijective e
    (IsAlgClosure.isAlgebraic.algHom_bijective₂ e eBack).1

theorem alg_extending_domain
    {K L Omega Omega' : Type*}
    [Field K] [Field L] [Field Omega] [Field Omega']
    [Algebra K L] [Algebra K Omega] [Algebra L Omega]
    [IsScalarTower K L Omega] [Algebra.IsAlgebraic L Omega]
    [Algebra K Omega'] [IsAlgClosure K Omega] [IsAlgClosure K Omega']
    (i : L →ₐ[K] Omega') :
    (algClosureExtending
      (K := K) (L := L) (Omega := Omega) (Omega' := Omega') i
      ).toAlgHom.restrictDomain L = i := by
  letI : IsAlgClosed Omega := IsAlgClosure.isAlgClosed K
  letI : IsAlgClosed Omega' := IsAlgClosure.isAlgClosed K
  change (algEmbeddingExtending
    (K := K) (L := L) (Omega := Omega) (Omega' := Omega') i
    ).restrictDomain L = i
  exact extending_restrict_domain
    (K := K) (L := L) (Omega := Omega) (Omega' := Omega') i

section RestrictionTransport

variable {Omega : Type u} [Field Omega] [Algebra ℚ Omega]
variable [IsAlgClosure ℚ Omega]
variable (C : IntermediateField ℚ Omega)

local instance restrictionTransportBaseAlgebra : Algebra ℚ C := C.algebra'
local instance restrictionTransportAmbientAlgebra : Algebra C Omega := C.toAlgebra

set_option synthInstance.maxHeartbeats 500000 in
-- Restriction transport synthesizes algebra structures on both closures.
omit [IsAlgClosure ℚ Omega] in
/-- Transporting an absolute automorphism across an equivalence of algebraic
closures commutes with restriction to a finite Galois subfield, provided the
equivalence extends the chosen identification of that subfield. -/
theorem aut_congr_extends
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ C] [IsGalois ℚ C]
    (eC : L ≃ₐ[ℚ] C)
    (eOmega : Omega ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (heOmega : ∀ x : C, eOmega x = (eC.symm x : AlgebraicClosure ℚ))
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    (AlgEquiv.autCongr eC).symm
        (AlgEquiv.restrictNormalHom C
          ((AlgEquiv.autCongr eOmega).symm sigma)) =
      AlgEquiv.restrictNormalHom L sigma := by
  letI : Algebra ℚ C := C.algebra'
  letI : Algebra C Omega := C.toAlgebra
  apply AlgEquiv.ext
  intro x
  apply eC.injective
  apply Subtype.ext
  apply eOmega.injective
  simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.symm_symm]
  rw [AlgEquiv.apply_symm_apply]
  let rho : Gal(Omega/ℚ) := eOmega.trans (sigma.trans eOmega.symm)
  have hnormalC : Normal ℚ C :=
    (inferInstance : IsGalois ℚ C).to_normal
  have hres := congrArg eOmega
    (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance Omega inferInstance
      inferInstance C hnormalC rho (eC x))
  change eOmega ↑((AlgEquiv.restrictNormalHom C rho) (eC x)) = _
  calc
    _ = eOmega (rho (eC x : Omega)) := hres
    _ = eOmega (eC
        ((AlgEquiv.restrictNormalHom L sigma) x) : Omega) := by
      change eOmega (eOmega.symm (sigma (eOmega (eC x : Omega)))) = _
      rw [eOmega.apply_symm_apply]
      rw [show eOmega (eC x : Omega) = (x : AlgebraicClosure ℚ) by
        simpa using heOmega (eC x)]
      rw [show eOmega (eC
          ((AlgEquiv.restrictNormalHom L sigma) x) : Omega) =
          ((AlgEquiv.restrictNormalHom L sigma) x : AlgebraicClosure ℚ) by
        simpa using heOmega
          (eC ((AlgEquiv.restrictNormalHom L sigma) x))]
      have hnormalL : Normal ℚ L :=
        (inferInstance : IsGalois ℚ L).to_normal
      exact (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance L hnormalL
        sigma x).symm

end RestrictionTransport

set_option synthInstance.maxHeartbeats 500000 in
-- The finite-layer quotient equivalence has a deeply nested instance search.
/-- On the finite layer cut out by `betaA`, the quotient equivalence with the
range of `betaA` sends absolute restriction to the value of `betaA` on the
maximal tame pro-`3` restriction. -/
theorem rational_tame_restrict
    {S : Finset ℕ} {A : Type v} [Group A]
    [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    let N := rational_tame_open betaA hbetaA
    let L := rationalLayerClosure S N
    rational_tame_range betaA hbetaA
      ((AlgEquiv.autCongr
        (rationalTameClosure S N)).symm
          (AlgEquiv.restrictNormalHom L sigma)) =
      betaA.rangeRestrict
        (AlgEquiv.restrictNormalHom
          (rationalTameIntermediate S) sigma) := by
  dsimp only
  let N := rational_tame_open betaA hbetaA
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  letI : H.1.Normal := by
    change (N : Subgroup (rationalTameGalois S)).Normal
    infer_instance
  letI : Normal ℚ (rationalLayerClosure S N) :=
    (inferInstance : IsGalois ℚ
      (rationalLayerClosure S N)).to_normal
  have hnormalL : Normal ℚ
      (rationalLayerClosure S N) := inferInstance
  let gamma : rationalTameGalois S :=
    AlgEquiv.restrictNormalHom
      (rationalTameIntermediate S) sigma
  have hfinite :
      (AlgEquiv.autCongr
        (rationalTameClosure S N)).symm
          (AlgEquiv.restrictNormalHom
            (rationalLayerClosure S N) sigma) =
        AlgEquiv.restrictNormalHom
          (IntermediateField.fixedField H.1) gamma := by
    apply AlgEquiv.ext
    intro x
    apply (rationalTameClosure S N).injective
    simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply]
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [AlgEquiv.symm_symm]
    calc
      _ = sigma ((rationalTameClosure S N x :
          rationalLayerClosure S N) : AlgebraicClosure ℚ) :=
        @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance
          (rationalLayerClosure S N) hnormalL sigma
          (rationalTameClosure S N x)
      _ = _ := by
        symm
        calc
          _ = ((gamma (x : IntermediateField.fixedField H.1) :
                rationalTameExtension S) : AlgebraicClosure ℚ) := by
              have h := AlgEquiv.restrictNormalHom_apply
                (IntermediateField.fixedField H.1) gamma x
              exact congrArg
                (fun z : rationalTameExtension S =>
                  (z : AlgebraicClosure ℚ)) h
          _ = sigma (((x : IntermediateField.fixedField H.1) :
                rationalTameExtension S) : AlgebraicClosure ℚ) := by
              exact AlgEquiv.restrictNormalHom_apply
                (rationalTameIntermediate S) sigma
                  (x : IntermediateField.fixedField H.1)
          _ = sigma
                ((rationalTameClosure S N x :
                  rationalLayerClosure S N) :
                    AlgebraicClosure ℚ) := rfl
  rw [hfinite]
  change (QuotientGroup.quotientKerEquivRange betaA)
      ((galoisFixedField H).symm
        (AlgEquiv.restrictNormalHom
          (IntermediateField.fixedField H.1) gamma)) =
    betaA.rangeRestrict gamma
  rw [← InfiniteGalois.normalAutEquivQuotient_apply H gamma]
  change (QuotientGroup.quotientKerEquivRange betaA)
      ((InfiniteGalois.normalAutEquivQuotient H).symm
        (InfiniteGalois.normalAutEquivQuotient H
          (gamma : rationalTameGalois S ⧸ H.1))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The subgroup of the absolute Galois group fixing an embedded base field
acts by automorphisms over that base field. -/
noncomputable def fixingRelativeAut
    {k K Omega : Type*}
    [Field k] [Field K] [Field Omega]
    [Algebra k K] [Algebra K Omega] [Algebra k Omega]
    [IsScalarTower k K Omega] :
    let i : K →ₐ[k] Omega := IsScalarTower.toAlgHom k K Omega
    ↥i.fieldRange.fixingSubgroup →* Gal(Omega/K) := by
  let i : K →ₐ[k] Omega := IsScalarTower.toAlgHom k K Omega
  let H : Subgroup Gal(Omega/k) := i.fieldRange.fixingSubgroup
  let result : ↥H →* Gal(Omega/K) :=
    { toFun := fun sigma => show Gal(Omega/K) from
        { AlgEquiv.toRingEquiv (sigma : Gal(Omega/k)) with
          commutes' := fun x => by
            change (sigma : Gal(Omega/k)) (i x) = i x
            exact sigma.2 ⟨i x,
              (AlgHom.mem_fieldRange (f := i)).2 ⟨x, rfl⟩⟩ }
      map_one' := by ext; rfl
      map_mul' := by intro sigma tau; ext; rfl }
  exact result

/-- Restriction from the fixed absolute Galois group of `ℚ` to the maximal
pro-`3` extension unramified outside `S`. -/
noncomputable def rationalAbsoluteRestriction
    (S : Finset ℕ) :
    Gal(AlgebraicClosure ℚ/ℚ) →* rationalTameGalois S :=
  AlgEquiv.restrictNormalHom (rationalTameIntermediate S)

theorem absolute_restriction_surjective
    (S : Finset ℕ) :
    Function.Surjective (rationalAbsoluteRestriction S) := by
  exact AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := rationalTameExtension S)
      (E := AlgebraicClosure ℚ)

theorem absolute_restriction_continuous
    (S : Finset ℕ) :
    Continuous (rationalAbsoluteRestriction S) := by
  exact InfiniteGalois.restrictNormalHom_continuous
    (k := ℚ) (K := AlgebraicClosure ℚ)
      (L := rationalTameIntermediate S)

/-- A finite Galois `3`-extension of `ℚ` unramified outside `S` occurs in
the defining compositum `ℚ_S(3)`. -/
theorem intermediate_tame_three
    (S : Finset ℕ)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hKthree : IsPGroup 3 Gal(K/ℚ))
    (hKunramified : UnramifiedOutside K S) :
    K.toIntermediateField ≤ rationalTameIntermediate S := by
  let component :
      {L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
        IsPGroup 3 Gal(L/ℚ) ∧ UnramifiedOutside L S} :=
    ⟨K, hKthree, hKunramified⟩
  simpa [component, rationalTameIntermediate] using
    (le_iSup
      (fun L :
        {L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 Gal(L/ℚ) ∧ UnramifiedOutside L S} =>
        L.1.toIntermediateField)
      component)

/-- If a finite Galois field is cut out by a homomorphism to a finite
`3`-group, then its Galois group is itself a `3`-group. -/
theorem galois_fixed_target
    {E : Type v} [Group E]
    (hE : IsPGroup 3 E)
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup) :
    IsPGroup 3 Gal(K/ℚ) := by
  let restrictionK : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hrestrictionK_surjective : Function.Surjective restrictionK :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hrestrictionK_ker : restrictionK.ker ≤ phi.ker := by
    rw [show restrictionK.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restrictionK] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [hphiKer]
  let finiteMap : Gal(K/ℚ) →* E :=
    factorThroughSurjective restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  have hfiniteMap : finiteMap.comp restrictionK = phi :=
    through_surjective_comp restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  have hfiniteMapInjective : Function.Injective finiteMap := by
    apply (injective_iff_map_eq_one finiteMap).2
    intro sigma hsigma
    obtain ⟨tau, rfl⟩ := hrestrictionK_surjective sigma
    have hphiTau : phi tau = 1 := by
      rw [← DFunLike.congr_fun hfiniteMap tau]
      exact hsigma
    have htauKer : tau ∈ restrictionK.ker := by
      rw [show restrictionK.ker = K.toIntermediateField.fixingSubgroup by
        simpa [restrictionK] using
          (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
      rw [← hphiKer]
      exact hphiTau
    exact htauKer
  let eRange : Gal(K/ℚ) ≃* finiteMap.range :=
    MulEquiv.ofBijective finiteMap.rangeRestrict
      ⟨(fun _ _ h => hfiniteMapInjective (congrArg Subtype.val h)),
        finiteMap.rangeRestrict_surjective⟩
  exact IsPGroup.of_equiv (hE.to_subgroup finiteMap.range) eRange.symm

/-- A continuous homomorphism from the absolute Galois group to a finite
discrete group cuts out a bundled finite Galois intermediate field. -/
theorem intermediate_fixed_continuous
    {E : Type v}
    [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hphi : Continuous phi) :
    ∃ K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ),
      phi.ker = K.toIntermediateField.fixingSubgroup := by
  have hopen : IsOpen (phi.ker : Set Gal(AlgebraicClosure ℚ/ℚ)) :=
    by
      simpa [MonoidHom.mem_ker] using
        ((isOpen_discrete ({1} : Set E)).preimage hphi :
          IsOpen (phi ⁻¹' ({1} : Set E)))
  let H : ClosedSubgroup Gal(AlgebraicClosure ℚ/ℚ) :=
    ⟨phi.ker, Subgroup.isClosed_of_isOpen phi.ker hopen⟩
  letI : (H : Subgroup Gal(AlgebraicClosure ℚ/ℚ)).Normal := by
    dsimp [H]
    infer_instance
  let Kfield : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField H.1
  have hfinite : FiniteDimensional ℚ Kfield := by
    rw [← InfiniteGalois.isOpen_iff_finite Kfield]
    rw [show Kfield.fixingSubgroup = H by
      simpa [Kfield] using InfiniteGalois.fixingSubgroup_fixedField H]
    exact hopen
  letI : FiniteDimensional ℚ Kfield := hfinite
  letI : IsGalois ℚ Kfield := by
    change IsGalois ℚ (IntermediateField.fixedField H.1)
    exact IsGalois.of_fixedField_normal_subgroup H.1
  let K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := Kfield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  refine ⟨K, ?_⟩
  change phi.ker = Kfield.fixingSubgroup
  simpa [Kfield, H] using
    (InfiniteGalois.fixingSubgroup_fixedField H).symm

/-- In addition to the fixed field, retain the faithful finite representation
through which the original absolute homomorphism factors. -/
theorem intermediate_fixed_faithful
    {E : Type v}
    [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hphi : Continuous phi) :
    ∃ (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
        (finiteMap : Gal(K/ℚ) →* E),
      phi.ker = K.toIntermediateField.fixingSubgroup ∧
        finiteMap.comp
            (AlgEquiv.restrictNormalHom K.toIntermediateField) = phi ∧
          Function.Injective finiteMap := by
  obtain ⟨K, hker⟩ :=
    intermediate_fixed_continuous
      phi hphi
  let restrictionK : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hrestrictionK_surjective : Function.Surjective restrictionK :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hrestrictionK_ker : restrictionK.ker ≤ phi.ker := by
    rw [show restrictionK.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restrictionK] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [hker]
  let finiteMap : Gal(K/ℚ) →* E :=
    factorThroughSurjective restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  have hfiniteMap : finiteMap.comp restrictionK = phi :=
    through_surjective_comp restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  have hfiniteMapInjective : Function.Injective finiteMap := by
    apply (injective_iff_map_eq_one finiteMap).2
    intro sigma hsigma
    obtain ⟨tau, rfl⟩ := hrestrictionK_surjective sigma
    have hphiTau : phi tau = 1 := by
      rw [← DFunLike.congr_fun hfiniteMap tau]
      exact hsigma
    have htauKer : tau ∈ restrictionK.ker := by
      rw [show restrictionK.ker = K.toIntermediateField.fixingSubgroup by
        simpa [restrictionK] using
          (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
      rw [← hker]
      exact hphiTau
    exact htauKer
  exact ⟨K, finiteMap, hker, hfiniteMap, hfiniteMapInjective⟩

/-- A finite absolute Galois homomorphism is unramified outside `S` when its
kernel cuts out a finite Galois field unramified outside `S`. -/
def AbsoluteUnramifiedOutside
    {E : Type v} [Group E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (S : Finset ℕ) : Prop :=
  ∃ K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ),
    phi.ker = K.toIntermediateField.fixingSubgroup ∧
      UnramifiedOutside K S

/-- Killing every inertia subgroup above primes outside `S` proves that a
finite Galois field is unramified outside `S`. -/
theorem outside_inertia_bot
    (S : Finset ℕ)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hinertia :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers K)),
          P.IsPrime →
          P.LiesOver (Ideal.rationalPrimeIdeal q) →
          P.inertia Gal(K/ℚ) = ⊥) :
    UnramifiedOutside K S := by
  intro q hq hqS P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
  exact ramification_idx_bot
    K hq P (hinertia q hq hqS P inferInstance inferInstance)

set_option synthInstance.maxHeartbeats 1000000 in
-- Factoring the absolute homomorphism needs a larger outer synthesis budget.
set_option maxHeartbeats 2000000 in
-- The fixed-field and quotient construction needs a larger elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
-- Factoring through the tame quotient expands the finite fixed-field tower.
/-- A finite absolute Galois homomorphism whose fixed field is a `3`-extension
unramified outside `S` factors continuously through `G_S(ℚ)(3)`.

The kernel equality says exactly that the bundled finite field `K` is the
field cut out by `phi`. -/
theorem rational_tame_absolute
    (S : Finset ℕ)
    {E : Type v}
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup)
    (hKthree : IsPGroup 3 Gal(K/ℚ))
    (hKunramified : UnramifiedOutside K S) :
    ∃ beta : rationalTameGalois S →* E,
      Continuous beta ∧
        beta.comp (rationalAbsoluteRestriction S) = phi := by
  let hKle : K.toIntermediateField ≤ rationalTameIntermediate S :=
    intermediate_tame_three
      S K hKthree hKunramified
  let i : K →ₐ[ℚ] rationalTameExtension S :=
    IntermediateField.inclusion hKle
  let K' : IntermediateField ℚ (rationalTameExtension S) :=
    i.fieldRange
  let e : K ≃ₐ[ℚ] K' := AlgEquiv.ofInjectiveField i
  letI : FiniteDimensional ℚ K' :=
    Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois ℚ K' := IsGalois.of_algEquiv e
  let hK'normal : Normal ℚ K' :=
    (inferInstance : IsGalois ℚ K').to_normal
  letI : Normal ℚ K' := hK'normal
  let restrictionK : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hrestrictionK_surjective : Function.Surjective restrictionK :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hrestrictionK_ker : restrictionK.ker ≤ phi.ker := by
    rw [show restrictionK.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restrictionK] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [hphiKer]
  let finiteMap : Gal(K/ℚ) →* E :=
    factorThroughSurjective restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  have hfiniteMap : finiteMap.comp restrictionK = phi :=
    through_surjective_comp restrictionK phi
      hrestrictionK_surjective hrestrictionK_ker
  let restrictionK' : rationalTameGalois S →* Gal(K'/ℚ) :=
    AlgEquiv.restrictNormalHom K'
  let beta : rationalTameGalois S →* E :=
    finiteMap.comp
      ((AlgEquiv.autCongr e).symm.toMonoidHom.comp restrictionK')
  refine ⟨beta, ?_, ?_⟩
  · have hrestrictionK'_continuous : Continuous restrictionK' :=
      @InfiniteGalois.restrictNormalHom_continuous
        ℚ (rationalTameExtension S)
        inferInstance inferInstance inferInstance K'
        ((inferInstance : IsGalois ℚ K').to_normal)
    have hautContinuous : Continuous
        ((AlgEquiv.autCongr e).symm : Gal(K'/ℚ) → Gal(K/ℚ)) :=
      continuous_of_discreteTopology
    have htransportContinuous : Continuous
        ((AlgEquiv.autCongr e).symm.toMonoidHom.comp restrictionK') :=
      hautContinuous.comp hrestrictionK'_continuous
    have hfiniteMapContinuous : Continuous
        (finiteMap : Gal(K/ℚ) → E) :=
      continuous_of_discreteTopology
    exact hfiniteMapContinuous.comp htransportContinuous
  · ext sigma
    change finiteMap
        ((AlgEquiv.autCongr e).symm
          (restrictionK' (rationalAbsoluteRestriction S sigma))) =
      phi sigma
    have hrestrict :
        (AlgEquiv.autCongr e).symm
            (restrictionK' (rationalAbsoluteRestriction S sigma)) =
          AlgEquiv.restrictNormalHom K.toIntermediateField sigma := by
      apply AlgEquiv.ext
      intro x
      apply e.symm_apply_eq.mpr
      apply Subtype.ext
      change
        ((AlgEquiv.restrictNormalHom K'
            (rationalAbsoluteRestriction S sigma)) (e x) :
              rationalTameExtension S) =
          (e (AlgEquiv.restrictNormalHom K.toIntermediateField sigma x) :
            rationalTameExtension S)
      calc
        _ = rationalAbsoluteRestriction S sigma
              (e x : rationalTameExtension S) :=
          @AlgEquiv.restrictNormalHom_apply
            ℚ _ (rationalTameExtension S) _ _ K' hK'normal
              (rationalAbsoluteRestriction S sigma) (e x)
        _ = (e (AlgEquiv.restrictNormalHom
              K.toIntermediateField sigma x) :
                rationalTameExtension S) := by
          apply Subtype.ext
          calc
            _ = sigma ((e x : K') : rationalTameExtension S) :=
              AlgEquiv.restrictNormalHom_apply
                (rationalTameIntermediate S) sigma
                  (e x : rationalTameExtension S)
            _ = sigma (x : AlgebraicClosure ℚ) := rfl
            _ = (AlgEquiv.restrictNormalHom
                  K.toIntermediateField sigma x : AlgebraicClosure ℚ) :=
              (AlgEquiv.restrictNormalHom_apply
                K.toIntermediateField sigma x).symm
            _ = ((e (AlgEquiv.restrictNormalHom
                  K.toIntermediateField sigma x) : K') :
                    rationalTameExtension S) := rfl
    rw [hrestrict]
    exact DFunLike.congr_fun hfiniteMap sigma

/-- Projection compatibility is preserved when the corrected absolute lift
is factored through `G_S(ℚ)(3)`.  This is the form consumed by the central
embedding argument after the cyclotomic twists. -/
theorem rational_tame_preliminary
    (S : Finset ℕ)
    {A E : Type v}
    [Group A]
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (pi : E →* A)
    (betaA : rationalTameGalois S →* A)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftAbs :
      pi.comp liftAbs =
        betaA.comp (rationalAbsoluteRestriction S))
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hliftKer : liftAbs.ker = K.toIntermediateField.fixingSubgroup)
    (hKthree : IsPGroup 3 Gal(K/ℚ))
    (hKunramified : UnramifiedOutside K S) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧ pi.comp betaE = betaA := by
  obtain ⟨betaE, hbetaEContinuous, hfactor⟩ :=
    rational_tame_absolute
      S liftAbs K hliftKer hKthree hKunramified
  refine ⟨betaE, hbetaEContinuous, ?_⟩
  apply MonoidHom.ext
  intro gamma
  obtain ⟨sigma, rfl⟩ :=
    absolute_restriction_surjective S gamma
  change pi (betaE (rationalAbsoluteRestriction S sigma)) =
    betaA (rationalAbsoluteRestriction S sigma)
  calc
    pi (betaE (rationalAbsoluteRestriction S sigma)) =
        pi (liftAbs sigma) := congrArg pi (DFunLike.congr_fun hfactor sigma)
    _ = betaA (rationalAbsoluteRestriction S sigma) :=
      DFunLike.congr_fun hliftAbs sigma

/-- Version of the preceding factorization theorem in which the `3`-group
property of the corrected fixed field is derived from the target group. -/
theorem rational_preliminary_absolute
    (S : Finset ℕ)
    {A E : Type v}
    [Group A]
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (hE : IsPGroup 3 E)
    (pi : E →* A)
    (betaA : rationalTameGalois S →* A)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftAbs :
      pi.comp liftAbs =
        betaA.comp (rationalAbsoluteRestriction S))
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hliftKer : liftAbs.ker = K.toIntermediateField.fixingSubgroup)
    (hKunramified : UnramifiedOutside K S) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧ pi.comp betaE = betaA := by
  exact rational_tame_preliminary
    S pi betaA liftAbs hliftAbs K hliftKer
      (galois_fixed_target hE liftAbs K hliftKer)
      hKunramified

/-- A corrected finite representation that kills every inertia group outside
`S` supplies the unramified fixed field required to descend its absolute
counterpart to `G_S(ℚ)(3)`. -/
theorem rational_preliminary_cleanup
    (S : Finset ℕ)
    {A E : Type v}
    [Group A]
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (hE : IsPGroup 3 E)
    (pi : E →* A)
    (betaA : rationalTameGalois S →* A)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftAbs :
      pi.comp liftAbs =
        betaA.comp (rationalAbsoluteRestriction S))
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (liftFinite : Gal(D/ℚ) →* E)
    (hfactor : liftFinite.comp
      (AlgEquiv.restrictNormalHom D.toIntermediateField) = liftAbs)
    (hkill :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers D)),
          P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
            ∀ sigma : P.inertia Gal(D/ℚ), liftFinite sigma.1 = 1) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧ pi.comp betaE = betaA := by
  let H : Subgroup Gal(D/ℚ) := liftFinite.ker
  letI : H.Normal := by
    dsimp only [H]
    infer_instance
  let F : IntermediateField ℚ D := IntermediateField.fixedField H
  letI : FiniteDimensional ℚ F := inferInstance
  letI : IsGalois ℚ F := IsGalois.of_fixedField_normal_subgroup H
  let Kfield : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.lift F
  let eF : F ≃ₐ[ℚ] Kfield := IntermediateField.liftAlgEquiv F
  let hKfinite : FiniteDimensional ℚ Kfield :=
    Module.Finite.equiv eF.toLinearEquiv
  letI : FiniteDimensional ℚ Kfield := hKfinite
  let hKgalois : IsGalois ℚ Kfield := IsGalois.of_algEquiv eF
  letI : IsGalois ℚ Kfield := hKgalois
  letI : NumberField Kfield := NumberField.of_module_finite ℚ Kfield
  let K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := Kfield
      finiteDimensional := hKfinite
      isGalois := hKgalois }
  have hliftKer : liftAbs.ker = K.toIntermediateField.fixingSubgroup := by
    ext sigma
    rw [MonoidHom.mem_ker]
    have hfac := DFunLike.congr_fun hfactor sigma
    rw [← hfac, MonoidHom.comp_apply]
    change AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
        liftFinite.ker ↔ sigma ∈ Kfield.fixingSubgroup
    change AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈ H ↔
      sigma ∈ (IntermediateField.lift F).fixingSubgroup
    rw [fixing_restrict_galois D F sigma]
    change AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈ H ↔
      AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
        (IntermediateField.fixedField H).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
  have hFunramified : UnramifiedOutside F S :=
    outside_inertia_killed
      D S liftFinite hkill
  have hKunramified : UnramifiedOutside K S := by
    intro q hq hqS
    exact rational_unramified_alg eF
      (hFunramified q hq hqS)
  exact
    rational_preliminary_absolute
      S hE pi betaA liftAbs hliftAbs K hliftKer hKunramified

/-- If a kernel-valued character is the inverse of a preliminary lift on an
inertia element, the central-kernel twist kills that inertia element. -/
theorem central_twist_value
    {Gamma E A : Type*}
    [Group Gamma] [Group E] [Group A]
    (pi : E →* A)
    (lift : Gamma →* E)
    (chi : Gamma →* pi.ker)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (sigma : Gamma)
    (hchi : (chi sigma : E) = (lift sigma)⁻¹) :
    centralKernelTwist pi lift chi hcentral sigma = 1 := by
  change (chi sigma : E) * lift sigma = 1
  rw [hchi]
  exact inv_mul_cancel (lift sigma)

/-- The pointwise difference of two lifts of the same base homomorphism is a
character valued in the central kernel. -/
def centralDifferenceLifts
    {Gamma E A : Type*}
    [Group Gamma] [Group E] [Group A]
    (pi : E →* A)
    (first second : Gamma →* E)
    (hprojection : pi.comp first = pi.comp second)
    (hcentral : pi.ker ≤ Subgroup.center E) :
    Gamma →* pi.ker where
  toFun gamma :=
    ⟨first gamma * (second gamma)⁻¹, by
      have h := DFunLike.congr_fun hprojection gamma
      change pi (first gamma) = pi (second gamma) at h
      change pi (first gamma * (second gamma)⁻¹) = 1
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel (pi (second gamma))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' gamma delta := by
    apply Subtype.ext
    change first (gamma * delta) * (second (gamma * delta))⁻¹ =
      (first gamma * (second gamma)⁻¹) *
        (first delta * (second delta)⁻¹)
    rw [map_mul, map_mul, mul_inv_rev]
    have hdeltaKer :
        first delta * (second delta)⁻¹ ∈ pi.ker := by
      change pi (first delta * (second delta)⁻¹) = 1
      have h := DFunLike.congr_fun hprojection delta
      change pi (first delta) = pi (second delta) at h
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel (pi (second delta))
    have hcomm :
        (first delta * (second delta)⁻¹) * (second gamma)⁻¹ =
          (second gamma)⁻¹ *
            (first delta * (second delta)⁻¹) :=
      (Subgroup.mem_center_iff.mp
        (hcentral hdeltaKer) (second gamma)⁻¹).symm
    calc
      first gamma * first delta * ((second delta)⁻¹ * (second gamma)⁻¹) =
          first gamma * (first delta * (second delta)⁻¹) *
            (second gamma)⁻¹ := by simp [mul_assoc]
      _ = first gamma * (second gamma)⁻¹ *
            (first delta * (second delta)⁻¹) := by
          simpa only [mul_assoc] using
            congrArg (fun x => first gamma * x) hcomm

theorem twist_difference_lifts
    {Gamma E A : Type*}
    [Group Gamma] [Group E] [Group A]
    (pi : E →* A)
    (first second : Gamma →* E)
    (hprojection : pi.comp first = pi.comp second)
    (hcentral : pi.ker ≤ Subgroup.center E) :
    centralKernelTwist pi second
        (centralDifferenceLifts
          pi first second hprojection hcentral)
        hcentral = first := by
  ext gamma
  change (first gamma * (second gamma)⁻¹) * second gamma = first gamma
  group

theorem difference_lifts_continuous
    {Gamma E A : Type*}
    [Group Gamma] [TopologicalSpace Gamma]
    [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [Group A]
    (pi : E →* A)
    (first second : Gamma →* E)
    (hprojection : pi.comp first = pi.comp second)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (hfirst : Continuous first)
    (hsecond : Continuous second) :
    Continuous (centralDifferenceLifts
      pi first second hprojection hcentral) := by
  exact (hfirst.mul hsecond.inv).subtype_mk _

/-- Once a global kernel character has removed the unwanted ramification,
the corrected absolute lift gives a continuous preliminary lift on
`G_S(ℚ)(3)`.  All remaining arithmetic is concentrated in the hypothesis
that the fixed field of the corrected twist is unramified outside `S`. -/
theorem preliminary_cleanup_character
    (S : Finset ℕ)
    {A E : Type v}
    [Group A]
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (hE : IsPGroup 3 E)
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (betaA : rationalTameGalois S →* A)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftAbs :
      pi.comp liftAbs =
        betaA.comp (rationalAbsoluteRestriction S))
    (chi : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hcorrectedKer :
      (centralKernelTwist pi liftAbs chi hcentral).ker =
        K.toIntermediateField.fixingSubgroup)
    (hKunramified : UnramifiedOutside K S) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧ pi.comp betaE = betaA := by
  let corrected : Gal(AlgebraicClosure ℚ/ℚ) →* E :=
    centralKernelTwist pi liftAbs chi hcentral
  have hcorrectedLift :
      pi.comp corrected =
        betaA.comp (rationalAbsoluteRestriction S) := by
    rw [show pi.comp corrected = pi.comp liftAbs by
      simpa [corrected] using
        (central_twist_projection (π := pi) liftAbs chi hcentral)]
    exact hliftAbs
  exact
    rational_preliminary_absolute
      S hE pi betaA corrected hcorrectedLift K hcorrectedKer hKunramified

/-- Packaged form of ramification cleanup: a kernel character whose corrected
absolute lift is unramified outside `S` produces the preliminary `G_S` lift. -/
theorem rational_preliminary_twist
    (S : Finset ℕ)
    {A E : Type v}
    [Group A]
    [Group E] [TopologicalSpace E] [DiscreteTopology E]
    (hE : IsPGroup 3 E)
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (betaA : rationalTameGalois S →* A)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftAbs :
      pi.comp liftAbs =
        betaA.comp (rationalAbsoluteRestriction S))
    (chi : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker)
    (hclean : AbsoluteUnramifiedOutside
      (centralKernelTwist pi liftAbs chi hcentral) S) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧ pi.comp betaE = betaA := by
  obtain ⟨K, hker, hunramified⟩ := hclean
  exact preliminary_cleanup_character
    S hE pi hcentral betaA liftAbs hliftAbs chi K hker hunramified

/-- The absolute cubic character cut out by a cyclic cubic subfield, with a
chosen value on a chosen generator of its Galois group.  This is the common
construction behind both the prime-conductor characters (`q ≠ 3`) and the
conductor-`9` character. -/
noncomputable def absoluteCubicValue
    {C : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ C] [IsGalois ℚ C]
    {K : Type v} [Group K]
    (generator : Gal(C/ℚ))
    (hgenerator : ∀ sigma : Gal(C/ℚ),
      sigma ∈ Subgroup.zpowers generator)
    (hcard : Nat.card Gal(C/ℚ) = 3)
    (eK : Multiplicative (ZMod 3) ≃* K)
    (value : K) :
    Gal(AlgebraicClosure ℚ/ℚ) →* K :=
  (cyclicGeneratorValue
      generator hgenerator hcard eK value).comp
    (AlgEquiv.restrictNormalHom C)

@[simp]
theorem absolute_cubic_restrict
    {C : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ C] [IsGalois ℚ C]
    {K : Type v} [Group K]
    (generator : Gal(C/ℚ))
    (hgenerator : ∀ sigma : Gal(C/ℚ),
      sigma ∈ Subgroup.zpowers generator)
    (hcard : Nat.card Gal(C/ℚ) = 3)
    (eK : Multiplicative (ZMod 3) ≃* K)
    (value : K)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ))
    (hsigma : AlgEquiv.restrictNormalHom C sigma = generator) :
    absoluteCubicValue
        generator hgenerator hcard eK value sigma = value := by
  change cyclicGeneratorValue
      generator hgenerator hcard eK value
        (AlgEquiv.restrictNormalHom C sigma) = value
  rw [hsigma]
  exact cyclic_generator_value
    generator hgenerator hcard eK value

theorem absolute_cubic_continuous
    {C : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ C] [IsGalois ℚ C]
    {K : Type v}
    [Group K] [TopologicalSpace K] [DiscreteTopology K]
    (generator : Gal(C/ℚ))
    (hgenerator : ∀ sigma : Gal(C/ℚ),
      sigma ∈ Subgroup.zpowers generator)
    (hcard : Nat.card Gal(C/ℚ) = 3)
    (eK : Multiplicative (ZMod 3) ≃* K)
    (value : K) :
    Continuous (absoluteCubicValue
      generator hgenerator hcard eK value) := by
  letI : Normal ℚ C :=
    (inferInstance : IsGalois ℚ C).to_normal
  have hfiniteContinuous : Continuous
      (cyclicGeneratorValue
        generator hgenerator hcard eK value : Gal(C/ℚ) → K) :=
    continuous_of_discreteTopology
  exact hfiniteContinuous.comp
    (@InfiniteGalois.restrictNormalHom_continuous
      ℚ (AlgebraicClosure ℚ) inferInstance inferInstance inferInstance C
      ((inferInstance : IsGalois ℚ C).to_normal))

/-- A field embedding is an equivalence onto its intermediate-field range.
This version allows an arbitrary ambient field (rather than a fixed
separable closure). -/
noncomputable def algHomRange
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω]
    (i : L →ₐ[K] Ω) : L ≃ₐ[K] i.fieldRange := by
  let f : L →ₐ[K] i.fieldRange :=
    { toFun := fun x =>
        ⟨i x, (AlgHom.mem_fieldRange (f := i)).2 ⟨x, rfl⟩⟩
      map_one' := by apply Subtype.ext; exact map_one i
      map_mul' := by intro x y; apply Subtype.ext; exact map_mul i x y
      map_zero' := by apply Subtype.ext; exact map_zero i
      map_add' := by intro x y; apply Subtype.ext; exact map_add i x y
      commutes' := by intro x; apply Subtype.ext; exact i.commutes x }
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply i.injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := i)).1 y.property
    exact ⟨x, Subtype.ext hx⟩

/-- A lift on a finite-index subgroup descends continuously when it is
already trivial on an open normal subgroup and the subgroup index is
coprime to the exponent of the central kernel.  The open normal subgroup
reduces the assertion to the finite-group descent theorem. -/
theorem continuous_coprime_index
    {Gamma E G : Type*}
    [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma]
    [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (f : Gamma →* G)
    (H : Subgroup Gamma) [H.FiniteIndex]
    (n : ℕ) (hcoprime : Nat.Coprime H.index n)
    (hkernel : ∀ z : q.ker, z ^ n = 1)
    (liftH : ↥H →* E)
    (hliftH : q.comp liftH = f.comp H.subtype)
    (N : OpenNormalSubgroup Gamma)
    (hNH : (N : Subgroup Gamma) ≤ H)
    (hNf : (N : Subgroup Gamma) ≤ f.ker)
    (hNlift : ∀ x : N, liftH ⟨x, hNH x.2⟩ = 1) :
    ∃ lift : Gamma →* E, Continuous lift ∧ q.comp lift = f := by
  let p : Gamma →* Gamma ⧸ (N : Subgroup Gamma) :=
    QuotientGroup.mk' (N : Subgroup Gamma)
  let Delta := Gamma ⧸ (N : Subgroup Gamma)
  let fbar : Delta →* G := QuotientGroup.lift (N : Subgroup Gamma) f hNf
  let hmap : ↥H →* Delta := p.comp H.subtype
  let Hbar : Subgroup Delta := hmap.range
  have hker_le : hmap.ker ≤ liftH.ker := by
    intro x hx
    change p (x : Gamma) = 1 at hx
    have hxN : (x : Gamma) ∈ (N : Subgroup Gamma) := by
      simpa [p] using hx
    exact hNlift ⟨(x : Gamma), hxN⟩
  let liftQuot : (↥H) ⧸ hmap.ker →* E :=
    QuotientGroup.lift hmap.ker liftH hker_le
  let eH : ((↥H) ⧸ hmap.ker) ≃* ↥Hbar :=
    QuotientGroup.quotientKerEquivRange hmap
  let liftBar : ↥Hbar →* E := liftQuot.comp eH.symm.toMonoidHom
  have hliftBar : q.comp liftBar = fbar.comp Hbar.subtype := by
    ext y
    obtain ⟨x, hx⟩ := y.2
    have hy : y = hmap.rangeRestrict x := Subtype.ext hx.symm
    subst y
    have he : eH.symm (hmap.rangeRestrict x) =
        ((x : ↥H) : (↥H) ⧸ hmap.ker) := by
      apply eH.symm_apply_eq.mpr
      rfl
    have hx := DFunLike.congr_fun hliftH x
    simpa [liftBar, liftQuot, he, fbar, Hbar, hmap, p] using hx
  letI : DiscreteTopology Delta :=
    pro_discrete_topology N
  letI : Finite Delta := pro_p_open N
  have hp_surj : Function.Surjective p :=
    QuotientGroup.mk'_surjective (N : Subgroup Gamma)
  have hpker : p.ker ≤ H := by
    rw [show p.ker = (N : Subgroup Gamma) by
      simp [p]]
    exact hNH
  have hindex : Hbar.index = H.index := by
    change hmap.range.index = H.index
    rw [show hmap.range = H.map p by ext y; simp [hmap]]
    exact H.index_map_eq hp_surj hpker
  have hcoprimeBar : Nat.Coprime Hbar.index n := by
    rw [hindex]
    exact hcoprime
  letI : Finite G := Finite.of_surjective q hq
  letI : Small.{0} Delta := by
    rcases Finite.exists_equiv_fin Delta with ⟨m, ⟨e⟩⟩
    exact Small.mk' e
  letI : Small.{0} E := by
    rcases Finite.exists_equiv_fin E with ⟨m, ⟨e⟩⟩
    exact Small.mk' e
  letI : Small.{0} G := by
    rcases Finite.exists_equiv_fin G with ⟨m, ⟨e⟩⟩
    exact Small.mk' e
  let eDelta0 : Shrink.{0} Delta ≃* Delta := Shrink.mulEquiv
  let eE0 : Shrink.{0} E ≃* E := Shrink.mulEquiv
  let eG0 : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let q0 : Shrink.{0} E →* Shrink.{0} G :=
    eG0.symm.toMonoidHom.comp (q.comp eE0.toMonoidHom)
  let f0 : Shrink.{0} Delta →* Shrink.{0} G :=
    eG0.symm.toMonoidHom.comp (fbar.comp eDelta0.toMonoidHom)
  let H0 : Subgroup (Shrink.{0} Delta) :=
    Hbar.comap eDelta0.toMonoidHom
  let H0toHbar : ↑H0 →* ↑Hbar :=
    { toFun := fun x => ⟨eDelta0 x.1, by
        have hx : x.1 ∈ H0 := x.2
        change eDelta0 x.1 ∈ Hbar at hx
        exact hx⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let liftBar0 : ↑H0 →* Shrink.{0} E :=
    eE0.symm.toMonoidHom.comp (liftBar.comp H0toHbar)
  have hq0 : Function.Surjective q0 := by
    intro y
    obtain ⟨x, hx⟩ := hq (eG0 y)
    refine ⟨eE0.symm x, ?_⟩
    simp [q0, hx]
  have hcentral0 : q0.ker ≤ Subgroup.center (Shrink.{0} E) := by
    intro z hz
    change q0 z = 1 at hz
    have hzE : eE0 z ∈ q.ker := by
      change q (eE0 z) = 1
      have hz' := congrArg eG0 hz
      simpa [q0] using hz'
    rw [Subgroup.mem_center_iff]
    intro y
    apply eE0.injective
    simpa using (Subgroup.mem_center_iff.mp (hcentral hzE) (eE0 y))
  have hindex0 : H0.index = Hbar.index := by
    simpa [H0] using
      (Hbar.index_comap_of_surjective eDelta0.surjective)
  have hcoprime0 : Nat.Coprime H0.index n := by
    rw [hindex0]
    exact hcoprimeBar
  have hkernel0 : ∀ z : q0.ker, z ^ n = 1 := by
    intro z
    have hz0 : q0 z.1 = 1 := by
      simpa only [MonoidHom.mem_ker] using z.2
    have hzE : eE0 z.1 ∈ q.ker := by
      change q (eE0 z.1) = 1
      have hz' := congrArg eG0 hz0
      simpa [q0] using hz'
    apply Subtype.ext
    apply eE0.injective
    have hzpow := congrArg Subtype.val (hkernel ⟨eE0 z.1, hzE⟩)
    simpa using hzpow
  have hliftBar0 : q0.comp liftBar0 = f0.comp H0.subtype := by
    apply MonoidHom.ext
    intro x
    apply eG0.injective
    have hx := DFunLike.congr_fun hliftBar (H0toHbar x)
    simpa [q0, f0, liftBar0, H0toHbar] using hx
  obtain ⟨liftDelta0, hliftDelta0⟩ :=
    extension_lift_coprime
      q0 hq0 hcentral0 f0 H0 n hcoprime0 hkernel0 liftBar0 hliftBar0
  let liftDelta : Delta →* E :=
    eE0.toMonoidHom.comp (liftDelta0.comp eDelta0.symm.toMonoidHom)
  have hliftDelta : q.comp liftDelta = fbar := by
    ext x
    have hx := DFunLike.congr_fun hliftDelta0 (eDelta0.symm x)
    have hx' := congrArg eG0 hx
    simpa [q0, f0, liftDelta] using hx'
  let lift : Gamma →* E := liftDelta.comp p
  refine ⟨lift, ?_, ?_⟩
  · have hliftDeltaContinuous : Continuous (liftDelta : Delta → E) :=
      continuous_of_discreteTopology
    exact hliftDeltaContinuous.comp
      (pro_open_continuous N)
  · apply MonoidHom.ext
    intro x
    change q (liftDelta (p x)) = f x
    calc
      q (liftDelta (p x)) = fbar (p x) :=
        DFunLike.congr_fun hliftDelta (p x)
      _ = f x := by
        have hcomp :=
          QuotientGroup.lift_comp_mk' (N : Subgroup Gamma) f hNf
        change fbar.comp p = f at hcomp
        exact DFunLike.congr_fun hcomp x

set_option maxHeartbeats 1000000 in
-- Primitive-root lifting invokes the Henselian residue-field construction.
/-- A divisor of the multiplicative order of a finite residue field lifts to
a primitive root in a Henselian local ring. -/
theorem integer_primitive_dvd
    (B : Type*) [CommRing B] [HenselianLocalRing B]
    [Finite (IsLocalRing.ResidueField B)]
    (n : ℕ) [NeZero n]
    (hn : n ∣ Nat.card (IsLocalRing.ResidueField B) - 1) :
    ∃ z : Bˣ, IsPrimitiveRoot z n := by
  classical
  letI : Fintype (IsLocalRing.ResidueField B) := Fintype.ofFinite _
  let k := IsLocalRing.ResidueField B
  letI : IsCyclic kˣ :=
    isCyclic_of_injective_ringHom (Units.coeHom k) Units.val_injective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hcardUnits : Nat.card kˣ = Fintype.card k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hn' : n ∣ orderOf g := by
    rw [hg, hcardUnits]
    simpa [Nat.card_eq_fintype_card] using hn
  let g0 : kˣ := g ^ (orderOf g / n)
  have hg0Order : orderOf g0 = n := by
    dsimp [g0]
    exact orderOf_pow_orderOf_div
      (isOfFinOrder_of_finite g).orderOf_pos.ne' hn'
  let a0 : k := g0
  let a : B :=
    Towers.NumberTheory.Milne.teichmullerLift B a0
  let q := Fintype.card k
  have haq : a ^ q = a := by
    exact sub_eq_zero.mp (by
      simpa [a, q, Polynomial.IsRoot.def] using
        Towers.NumberTheory.Milne.teichmuller_lift_root B a0)
  have haPowRoot :
      (Polynomial.X ^ q - Polynomial.X : Polynomial B).IsRoot (a ^ n) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    rw [← pow_mul, Nat.mul_comm n q, pow_mul, haq]
  have hOneRoot :
      (Polynomial.X ^ q - Polynomial.X : Polynomial B).IsRoot 1 := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
    simp
  have haResiduePow :
      IsLocalRing.residue B (a ^ n) = IsLocalRing.residue B 1 := by
    rw [map_pow, map_one]
    rw [show IsLocalRing.residue B a = a0 by
      exact Towers.NumberTheory.Milne.residue_teichmullerLift B a0]
    change ((g0 : k) ^ n) = 1
    have hg0Pow : g0 ^ n = 1 := by
      rw [← hg0Order]
      exact pow_orderOf_eq_one g0
    exact congrArg Units.val hg0Pow
  have haPow : a ^ n = 1 :=
    Towers.NumberTheory.Milne.teichmullerLift_unique B
      haPowRoot hOneRoot haResiduePow
  have haUnit : IsUnit a := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [Towers.NumberTheory.Milne.residue_teichmullerLift]
    exact Units.ne_zero g0
  let z : Bˣ := haUnit.unit
  have hzval : (z : B) = a := haUnit.unit_spec
  refine ⟨z, (IsPrimitiveRoot.iff_orderOf).2 ?_⟩
  rw [← orderOf_units]
  change orderOf a = n
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one haPow
  · have hmap := orderOf_map_dvd (IsLocalRing.residue B).toMonoidHom a
    change orderOf (IsLocalRing.residue B a) ∣ orderOf a at hmap
    have hresidue : IsLocalRing.residue B a = a0 :=
      Towers.NumberTheory.Milne.residue_teichmullerLift B a0
    rw [hresidue, show orderOf a0 = n by
      change orderOf (g0 : k) = n
      rw [orderOf_units, hg0Order]] at hmap
    exact hmap

/-- Primitive Teichmuller representatives have the expected inertia and
Frobenius action. -/
theorem primitive_inertia_fixed
    {B F G : Type u} [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Field F] [Algebra B F]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G F]
    [MulDistribMulAction G Fˣ]
    [Finite (IsLocalRing.ResidueField B)]
    (halg : Function.Injective (algebraMap B F))
    (hcompat : ∀ g : G, ∀ b : B,
      algebraMap B F (g • b) = g • algebraMap B F b)
    (hcompatUnits : ∀ g : G, ∀ z : Fˣ,
      ((g • z : Fˣ) : F) = g • (z : F))
    (n : ℕ) [NeZero n]
    (hnunit : IsUnit (n : B))
    (y : G) (r : ℕ)
    (hyResidue : ∀ z : Bˣ,
      IsLocalRing.residue B (y • (z : B)) =
        IsLocalRing.residue B ((z : B) ^ r))
    (hdiv : n ∣ Nat.card (IsLocalRing.ResidueField B) - 1) :
    ∃ zeta : Fˣ, IsPrimitiveRoot zeta n ∧
      (∀ i : (IsLocalRing.maximalIdeal B).inertia G,
        i.1 • zeta = zeta) ∧
      y • zeta = zeta ^ r := by
  obtain ⟨z, hz⟩ :=
    integer_primitive_dvd B n hdiv
  let zeta : Fˣ := Units.map (algebraMap B F) z
  have hzeta : IsPrimitiveRoot zeta n := by
    exact hz.map_of_injective
      (Units.map_injective halg)
  have hzpow : (z : B) ^ n = 1 :=
    congrArg Units.val hz.pow_eq_one
  obtain ⟨hzfixed, hzy⟩ := integral_inertia_fixed
    hcompat hcompatUnits n hnunit z hzpow y r (hyResidue z)
  exact ⟨zeta, hzeta, hzfixed, hzy⟩

/-- A rational prime congruent to one modulo three is unramified in the
chosen copy of the cube-root field. -/
theorem rational_cube_ramification
    {r : ℕ} (hr : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    (P : Ideal (NumberField.RingOfIntegers rationalCubeField))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal r)] :
    (Ideal.rationalPrimeIdeal r).ramificationIdx P = 1 := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsScalarTower ℤ ℚ (CyclotomicField 3 ℚ) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  let eZ : CyclotomicField 3 ℚ ≃ₐ[ℤ] rationalCubeField :=
    AlgEquiv.ofRingEquiv
      (f := rationalCubeRoot.toRingEquiv) (fun z => by simp)
  let e0 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ) ≃ₐ[ℤ]
      NumberField.RingOfIntegers rationalCubeField :=
    eZ.mapIntegralClosure
  let Q : Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
    P.comap e0
  have hQover : Q ∈ (Ideal.rationalPrimeIdeal r).primesOver
      (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
    ext z
    change z ∈ Ideal.rationalPrimeIdeal r ↔
      e0.toRingHom (algebraMap ℤ
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) z) ∈ P
    simpa using (Ideal.mem_of_liesOver
      (P := P) (p := Ideal.rationalPrimeIdeal r) z)
  letI : Q.IsPrime := hQover.1
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal r) := hQover.2
  letI : Q.LiesOver (Ideal.span {(r : ℤ)}) := by
    simpa [Ideal.rationalPrimeIdeal] using hQover.2
  have hrnotdvd : ¬r ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with hr1 | hr3eq
    · exact hr.ne_one hr1
    · subst r
      norm_num at hr3
  have hQ : (Ideal.rationalPrimeIdeal r).ramificationIdx Q = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      r (CyclotomicField 3 ℚ) Q hrnotdvd
  calc
    (Ideal.rationalPrimeIdeal r).ramificationIdx P =
        (Ideal.rationalPrimeIdeal r).ramificationIdx Q := by
      symm
      exact (Ideal.rationalPrimeIdeal r).ramificationIdx_comap_eq e0 P
    _ = 1 := hQ

/-- Hence the decomposition group at such a prime of the quadratic
cube-root field is trivial. -/
theorem cube_stabilizer_bot
    {r : ℕ} (hr : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    (P : Ideal (NumberField.RingOfIntegers rationalCubeField))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal r)] :
    MulAction.stabilizer Gal(rationalCubeField/ℚ) P = ⊥ := by
  have he := rational_cube_ramification hr hr3 P
  have hf := rational_cube_deg hr hr3 P
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hr) P
  letI : (Ideal.rationalPrimeIdeal r).IsPrime := rational_prime_ideal hr
  letI : (Ideal.rationalPrimeIdeal r).IsMaximal :=
    rational_ideal_maximal hr
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  letI : Field (ℤ ⧸ Ideal.rationalPrimeIdeal r) :=
    Ideal.Quotient.field (Ideal.rationalPrimeIdeal r)
  letI : Field (NumberField.RingOfIntegers rationalCubeField ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (ℤ ⧸ Ideal.rationalPrimeIdeal r) :=
    Ring.HasFiniteQuotients.finiteQuotient (rational_ne_bot hr)
  letI : Finite (NumberField.RingOfIntegers rationalCubeField ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hP0
  have hcard :=
    Towers.NumberTheory.Milne.decomposition_inertia_deg
    (G := Gal(rationalCubeField/ℚ))
    (Ideal.rationalPrimeIdeal r) (rational_ne_bot hr) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := Ideal.rationalPrimeIdeal r) (P := P)
      (B := NumberField.RingOfIntegers rationalCubeField)
      (G := Gal(rationalCubeField/ℚ)),
    Ideal.inertiaDegIn_eq_inertiaDeg
      (p := Ideal.rationalPrimeIdeal r) (P := P)
      (B := NumberField.RingOfIntegers rationalCubeField)
      (G := Gal(rationalCubeField/ℚ)),
    he, hf, mul_one] at hcard
  apply (Subgroup.eq_bot_iff_forall _).2
  intro sigma hsigma
  haveI : Subsingleton
      (MulAction.stabilizer Gal(rationalCubeField/ℚ) P) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg Subtype.val
    (Subsingleton.elim
      (⟨sigma, hsigma⟩ :
        MulAction.stabilizer Gal(rationalCubeField/ℚ) P) 1)

lemma integers_alg_smul
    {k L E : Type u} [Field k] [NumberField k]
    [Field L] [NumberField L] [Field E] [NumberField E]
    [Algebra k L] [Algebra k E]
    (e : L ≃ₐ[k] E) (sigma : Gal(L/k))
    (x : NumberField.RingOfIntegers L) :
    (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) (sigma • x) =
      (AlgEquiv.autCongr e sigma) •
        (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) x := by
  apply NumberField.RingOfIntegers.ext
  change e (sigma (x : L)) =
    (AlgEquiv.autCongr e sigma) (e (x : L))
  simp [AlgEquiv.autCongr_apply]

/-- Arithmetic Frobenius is preserved when both the number field and its
prime are transported across a rational algebra equivalence. -/
lemma arith_frob_alg
    {L E : Type u} [Field L] [NumberField L]
    [Field E] [NumberField E]
    [Algebra ℚ L] [Algebra ℚ E]
    [FiniteDimensional ℚ L] [FiniteDimensional ℚ E]
    [IsGalois ℚ L] [IsGalois ℚ E]
    {r : ℕ} (e : L ≃ₐ[ℚ] E)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    (sigma : Gal(L/ℚ)) (hsigma : IsArithFrobAt ℤ sigma P) :
    IsArithFrobAt ℤ (AlgEquiv.autCongr e sigma)
      (P.map (NumberField.RingOfIntegers.mapAlgEquiv e)) := by
  change IsArithFrobAt ℤ (AlgEquiv.autCongr e sigma)
    (P.map (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv))
  let eO := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  let PT : Ideal (NumberField.RingOfIntegers E) := P.map eO
  letI : PT.IsPrime := Ideal.map_isPrime_of_equiv eO
  have heOint (z : ℤ) :
      eO (algebraMap ℤ (NumberField.RingOfIntegers L) z) =
        algebraMap ℤ (NumberField.RingOfIntegers E) z := by
    apply Subtype.ext
    simp [eO]
  letI : PT.LiesOver (Ideal.rationalPrimeIdeal r) := by
    rw [Ideal.liesOver_iff]
    ext z
    rw [Ideal.mem_comap]
    rw [← heOint]
    constructor
    · intro hz
      exact Ideal.mem_map_of_mem eO
        ((Ideal.mem_of_liesOver (P := P)
          (p := Ideal.rationalPrimeIdeal r) z).mp hz)
    · intro hz
      obtain ⟨a, ha, hae⟩ :=
        (Ideal.mem_map_iff_of_surjective eO eO.surjective).mp hz
      have haeq : a = algebraMap ℤ (NumberField.RingOfIntegers L) z :=
        eO.injective hae
      exact (Ideal.mem_of_liesOver (P := P)
        (p := Ideal.rationalPrimeIdeal r) z).mpr (haeq ▸ ha)
  intro x
  let y : NumberField.RingOfIntegers L := eO.symm x
  have hy := hsigma y
  have hunderP : P.under ℤ = Ideal.rationalPrimeIdeal r :=
    (P.over_def (Ideal.rationalPrimeIdeal r)).symm
  rw [hunderP] at hy
  have hymap : eO (sigma • y - y ^ Nat.card
      (ℤ ⧸ Ideal.rationalPrimeIdeal r)) ∈ PT := Ideal.mem_map_of_mem eO hy
  have hunderPT : PT.under ℤ = Ideal.rationalPrimeIdeal r :=
    (PT.over_def (Ideal.rationalPrimeIdeal r)).symm
  rw [hunderPT]
  have hact : eO (sigma • eO.symm x) =
      (AlgEquiv.autCongr e sigma) • x := by
    apply NumberField.RingOfIntegers.ext
    dsimp only [eO]
    change e (sigma (e.symm (x : E))) =
      (AlgEquiv.autCongr e sigma) (x : E)
    simp [AlgEquiv.autCongr_apply]
  simpa [PT, y, map_sub, map_pow, hact] using hymap

lemma ideal_alg_smul
    {k L E : Type u} [Field k] [NumberField k]
    [Field L] [NumberField L] [Field E] [NumberField E]
    [Algebra k L] [Algebra k E]
    (e : L ≃ₐ[k] E) (sigma : Gal(L/k))
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (sigma • P).map
        (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) =
      (AlgEquiv.autCongr e sigma) •
        P.map (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) := by
  let eO := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  let eAut := AlgEquiv.autCongr e
  apply Ideal.ext
  intro y
  let x := eO.symm y
  have hy : y = eO x := by simp [x]
  rw [hy]
  have hmem (J : Ideal (NumberField.RingOfIntegers L))
      (z : NumberField.RingOfIntegers L) :
      eO z ∈ J.map eO ↔ z ∈ J := by
    constructor
    · intro hz
      have hz' : eO.symm (eO z) ∈ J := by
        rw [← Ideal.mem_comap]
        simpa using hz
      simpa using hz'
    · exact Ideal.mem_map_of_mem eO
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show (eAut sigma)⁻¹ • eO x = eO (sigma⁻¹ • x) by
    rw [← map_inv]
    exact (integers_alg_smul e sigma⁻¹ x).symm]
  exact (hmem (sigma • P) x).trans
    ((Ideal.mem_pointwise_smul_iff_inv_smul_mem
      (a := sigma) (S := P) (x := x)).trans
        (hmem P (sigma⁻¹ • x)).symm)

lemma integers_rat_lies
    {E F : Type u} [Field E] [NumberField E] [Algebra ℚ E]
    [Field F] [NumberField F] [Algebra ℚ F]
    {r : ℕ}
    (P : Ideal (NumberField.RingOfIntegers E))
    (Q : Ideal (NumberField.RingOfIntegers F))
    [P.LiesOver (Ideal.rationalPrimeIdeal r)]
    [Q.LiesOver (Ideal.rationalPrimeIdeal r)] :
    P.under (NumberField.RingOfIntegers ℚ) =
      Q.under (NumberField.RingOfIntegers ℚ) := by
  let e0 : NumberField.RingOfIntegers ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) (by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe])
  have hmap (L : Type u) [Field L] [NumberField L] [Algebra ℚ L]
      (R : Ideal (NumberField.RingOfIntegers L)) :
      R.under ℤ = (R.under (NumberField.RingOfIntegers ℚ)).map e0 := by
    have hcomp :
        (algebraMap ℤ (NumberField.RingOfIntegers L)) =
          (algebraMap (NumberField.RingOfIntegers ℚ)
            (NumberField.RingOfIntegers L)).comp e0.symm.toRingHom :=
      Subsingleton.elim _ _
    calc
      R.under ℤ =
          (R.under (NumberField.RingOfIntegers ℚ)).comap
            e0.symm.toRingHom := by
        rw [Ideal.under, hcomp, Ideal.under, Ideal.comap_comap]
      _ = (R.under (NumberField.RingOfIntegers ℚ)).map e0.toRingHom := by
        symm
        exact Ideal.map_comap_of_equiv
          (I := R.under (NumberField.RingOfIntegers ℚ)) e0.toRingEquiv
  have hm : (P.under (NumberField.RingOfIntegers ℚ)).map e0 =
      (Q.under (NumberField.RingOfIntegers ℚ)).map e0 := by
    rw [← hmap E P, ← hmap F Q]
    rw [← P.over_def (Ideal.rationalPrimeIdeal r),
      ← Q.over_def (Ideal.rationalPrimeIdeal r)]
  have hsup :=
    (Ideal.map_eq_iff_sup_ker_eq_of_surjective e0.toRingHom
      e0.surjective).mp hm
  have hker : RingHom.ker e0.toRingHom = ⊥ := by
    apply Ideal.ext
    intro x
    simp
  simpa [hker] using hsup

lemma global_integers_restrict
    {F E N : Type u} [Field F] [NumberField F]
    [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra F E] [Algebra F N] [Algebra E N] [IsScalarTower F E N]
    [IsGalois F E] [IsGalois F N]
    (sigma : Gal(N/F)) (x : NumberField.RingOfIntegers E) :
    sigma • algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N) x =
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N)
        ((AlgEquiv.restrictNormalHom E sigma) • x) := by
  apply Subtype.ext
  let y : NumberField.RingOfIntegers N :=
    algebraMap (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers N) x
  calc
    algebraMap (NumberField.RingOfIntegers N) N
        (sigma • algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N) x) =
        sigma (algebraMap (NumberField.RingOfIntegers N) N y) := by rfl
    _ = sigma (algebraMap E N
        (algebraMap (NumberField.RingOfIntegers E) E x)) := by rfl
    _ = algebraMap E N
        ((AlgEquiv.restrictNormalHom E sigma)
          (algebraMap (NumberField.RingOfIntegers E) E x)) := by
      exact (AlgEquiv.restrictNormal_commutes sigma E
        (algebraMap (NumberField.RingOfIntegers E) E x)).symm
    _ = algebraMap E N
        (algebraMap (NumberField.RingOfIntegers E) E
          ((AlgEquiv.restrictNormalHom E sigma) • x)) := by congr 1
    _ = algebraMap (NumberField.RingOfIntegers N) N
        (algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          ((AlgEquiv.restrictNormalHom E sigma) • x)) := by rfl

lemma global_smul_restrict
    {F E N : Type u} [Field F] [NumberField F]
    [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra F E] [Algebra F N] [Algebra E N] [IsScalarTower F E N]
    [IsGalois F E] [IsGalois F N]
    (sigma : Gal(N/F)) (P : Ideal (NumberField.RingOfIntegers N)) :
    Ideal.under (NumberField.RingOfIntegers E) (sigma • P) =
      (AlgEquiv.restrictNormalHom E sigma) •
        Ideal.under (NumberField.RingOfIntegers E) P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  change
    (sigma⁻¹ • algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N) x) ∈ P ↔
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N)
        ((AlgEquiv.restrictNormalHom E sigma)⁻¹ • x) ∈ P
  have h := global_integers_restrict
    (F := F) (E := E) (N := N) (sigma := sigma⁻¹) (x := x)
  constructor <;> intro hx
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          (AlgEquiv.restrictNormalHom E sigma⁻¹ • x) ∈ P := h ▸ hx
    simpa using hx'
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          (AlgEquiv.restrictNormalHom E sigma⁻¹ • x) ∈ P := by
      simpa using hx
    exact h.symm ▸ hx'

theorem global_centered_smul
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) (sigma : Gal(L/K)) :
    (Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
        (sigma • w)
        (by
          obtain ⟨x, hx0, hx1⟩ := hw
          refine ⟨sigma x, ?_, ?_⟩
          · simpa only [map_zero] using sigma.injective.ne hx0
          · simpa using hx1)
        (by
          intro x y
          change w (sigma.symm (x + y)) ≤
            max (w (sigma.symm x)) (w (sigma.symm y))
          rw [map_add]
          exact hna _ _)).asIdeal =
      sigma •
        (Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
          w hw hna).asIdeal := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change w (sigma.symm
      (algebraMap (NumberField.RingOfIntegers L) L x)) < 1 ↔
    w (algebraMap (NumberField.RingOfIntegers L) L (sigma⁻¹ • x)) < 1
  rfl

set_option maxHeartbeats 1000000 in
-- Aligning the two contracted primes requires several integral-closure actions.
theorem compositum_conjugate_completion
    {k Omega L0 : Type u} [Field k] [NumberField k]
    [Field Omega] [NumberField Omega] [Algebra k Omega]
    [Field L0] [NumberField L0] [Algebra k L0]
    (L K : IntermediateField k Omega)
    [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional K Omega] [IsGalois K Omega]
    [FiniteDimensional k Omega] [IsGalois k Omega]
    (hsup : L ⊔ K = ⊤) (hinf : L ⊓ K = ⊥)
    (eL : L0 ≃ₐ[k] L)
    (p : Ideal (NumberField.RingOfIntegers k))
    (P0 : Ideal (NumberField.RingOfIntegers L0))
    [P0.IsPrime] [P0.LiesOver p]
    (PK : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    [Fact (FinitePlace.mk PK).val.IsNontrivial]
    [IsUltrametricDist (FinitePlace.mk PK).val.Completion]
    (hPK : PK.asIdeal.LiesOver p)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := Omega) (FinitePlace.mk PK).val) :
    ∃ sigma : Gal(Omega/K),
      let w' := sigma • w
      let hw' : w'.1.IsNontrivial :=
        Towers.NumberTheory.Milne.absolute_extension_nontrivial
          (FinitePlace.mk PK).val w'
      let hna' : IsNonarchimedean w'.1 :=
        Towers.NumberTheory.Milne.absolute_extension_nonarchimedean
          (FinitePlace.mk PK).val w'
      Ideal.under (NumberField.RingOfIntegers L)
          (Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
            w'.1 hw' hna').asIdeal =
        P0.map (NumberField.RingOfIntegers.mapAlgEquiv eL) := by
  letI : Normal k L := (inferInstance : IsGalois k L).to_normal
  letI : Normal k K := (inferInstance : IsGalois k K).to_normal
  let v := (FinitePlace.mk PK).val
  have hw : w.1.IsNontrivial :=
    Towers.NumberTheory.Milne.absolute_extension_nontrivial v w
  have hna : IsNonarchimedean w.1 :=
    Towers.NumberTheory.Milne.absolute_extension_nonarchimedean v w
  let Qs :=
    Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
      w.1 hw hna
  let Q : Ideal (NumberField.RingOfIntegers Omega) := Qs.asIdeal
  letI : Q.IsPrime := Qs.isPrime
  letI : Q.LiesOver PK.asIdeal :=
    Towers.NumberTheory.Milne.nonarchimedean_spectrum_lies
      PK w.1 w.2 hw hna
  letI : PK.asIdeal.LiesOver p := hPK
  letI : Q.LiesOver p := Ideal.LiesOver.trans Q PK.asIdeal p
  let eO : NumberField.RingOfIntegers L0 ≃ₐ[NumberField.RingOfIntegers k]
      NumberField.RingOfIntegers L :=
    NumberField.RingOfIntegers.mapAlgEquiv eL
  let PT : Ideal (NumberField.RingOfIntegers L) := P0.map eO
  letI : PT.IsPrime := Ideal.map_isPrime_of_equiv eO
  letI : PT.LiesOver p := Ideal.map_equiv_liesOver P0 p eO
  let R : Ideal (NumberField.RingOfIntegers L) :=
    Q.under (NumberField.RingOfIntegers L)
  letI : Q.LiesOver R := inferInstance
  letI : R.IsPrime :=
    Ideal.IsPrime.comap
      (algebraMap (NumberField.RingOfIntegers L)
        (NumberField.RingOfIntegers Omega))
  letI : R.LiesOver p := Ideal.LiesOver.tower_bot Q R p
  let e : Gal(Omega/K) ≃* Gal(L/k) :=
    galoisCompositumEquiv L K hsup hinf
  obtain ⟨tau, htau⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup p R PT Gal(L/k)
  let sigma : Gal(Omega/K) := e.symm tau
  refine ⟨sigma, ?_⟩
  dsimp only
  let sigma0 : Gal(Omega/k) :=
    MulSemiringAction.toAlgAut Gal(Omega/K) k Omega sigma
  have hrestrict : AlgEquiv.restrictNormalHom L sigma0 = tau := by
    change e sigma = tau
    simp [sigma]
  have hUnder : Ideal.under (NumberField.RingOfIntegers L) (sigma0 • Q) =
      tau • R := by
    rw [global_smul_restrict, hrestrict]
  have haction : (sigma • Q : Ideal (NumberField.RingOfIntegers Omega)) =
      sigma0 • Q := by
    apply Ideal.ext
    intro x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hcenter := global_centered_smul
    (K := K) w.1 hw hna sigma
  calc
    Ideal.under (NumberField.RingOfIntegers L)
        (Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
          (sigma • w).1
          (Towers.NumberTheory.Milne.absolute_extension_nontrivial
            v (sigma • w))
          (Towers.NumberTheory.Milne.absolute_extension_nonarchimedean
            v (sigma • w))).asIdeal =
      Ideal.under (NumberField.RingOfIntegers L) (sigma • Q) := by
        simpa [Q, Qs] using
          congrArg (Ideal.under (NumberField.RingOfIntegers L)) hcenter
    _ = Ideal.under (NumberField.RingOfIntegers L) (sigma0 • Q) := by
      rw [haction]
    _ = tau • R := hUnder
    _ = PT := htau
    _ = P0.map (NumberField.RingOfIntegers.mapAlgEquiv eL) := rfl

set_option maxHeartbeats 5000000 in
-- Lifting a decomposition element uses transitivity twice in the compositum.
theorem decomposition_lift_compositum
    {k Omega : Type u} [Field k] [NumberField k]
    [Field Omega] [NumberField Omega] [Algebra k Omega]
    (L K : IntermediateField k Omega)
    [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional K Omega] [IsGalois K Omega]
    [FiniteDimensional k Omega] [IsGalois k Omega]
    (hsup : L ⊔ K = ⊤) (hinf : L ⊓ K = ⊥)
    (Q : Ideal (NumberField.RingOfIntegers Omega)) [Q.IsPrime]
    (hKbot : MulAction.stabilizer Gal(K/k)
      (Q.under (NumberField.RingOfIntegers K)) = ⊥)
    (tau : Gal(L/k))
    (htau : tau • Q.under (NumberField.RingOfIntegers L) =
      Q.under (NumberField.RingOfIntegers L)) :
    ∃ sigma : Gal(Omega/K),
      let sigma0 : Gal(Omega/k) :=
        MulSemiringAction.toAlgAut Gal(Omega/K) k Omega sigma
      sigma0 • Q = Q ∧
        galoisCompositumEquiv L K hsup hinf sigma = tau := by
  letI : Normal k L := (inferInstance : IsGalois k L).to_normal
  letI : Normal k K := (inferInstance : IsGalois k K).to_normal
  let PL := Q.under (NumberField.RingOfIntegers L)
  let PK := Q.under (NumberField.RingOfIntegers K)
  obtain ⟨rho0, hrho0⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := k) (K₁ := L) (E := Omega) tau
  let Q2 : Ideal (NumberField.RingOfIntegers Omega) := rho0 • Q
  have hQ2under : Q2.under (NumberField.RingOfIntegers L) = PL := by
    rw [show Q2 = rho0 • Q from rfl,
      global_smul_restrict]
    rw [hrho0, htau]
  letI : Q2.IsPrime := inferInstance
  letI : Q.LiesOver PL := inferInstance
  letI : Q2.LiesOver PL := ⟨hQ2under.symm⟩
  obtain ⟨delta, hdelta⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup PL Q2 Q Gal(Omega/L)
  let delta0 : Gal(Omega/k) :=
    MulSemiringAction.toAlgAut Gal(Omega/L) k Omega delta
  let rho : Gal(Omega/k) := delta0 * rho0
  have hrhoQ : rho • Q = Q := by
    change (delta0 * rho0) • Q = Q
    rw [mul_smul]
    exact hdelta
  have hdeltaL : AlgEquiv.restrictNormalHom L delta0 = 1 := by
    ext x
    calc
      ((AlgEquiv.restrictNormalHom L delta0) x : Omega) =
          delta0 (algebraMap L Omega x) :=
        AlgEquiv.restrictNormalHom_apply L delta0 x
      _ = algebraMap L Omega x := delta.commutes x
  have hrhoL : AlgEquiv.restrictNormalHom L rho = tau := by
    change AlgEquiv.restrictNormalHom L (delta0 * rho0) = tau
    rw [map_mul, hdeltaL, one_mul, hrho0]
  have hrhoKmem : AlgEquiv.restrictNormalHom K rho ∈
      MulAction.stabilizer Gal(K/k) PK := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      AlgEquiv.restrictNormalHom K rho • PK =
          Ideal.under (NumberField.RingOfIntegers K) (rho • Q) := by
        exact (global_smul_restrict rho Q).symm
      _ = PK := by rw [hrhoQ]
  have hrhoK : AlgEquiv.restrictNormalHom K rho = 1 := by
    rw [hKbot] at hrhoKmem
    exact hrhoKmem
  let sigma : Gal(Omega/K) :=
    { rho.toRingEquiv with
      commutes' := by
        intro x
        have hx : (AlgEquiv.restrictNormalHom K rho) x = x :=
          DFunLike.congr_fun hrhoK x
        calc
          rho (algebraMap K Omega x) =
              ((AlgEquiv.restrictNormalHom K rho) x : Omega) :=
            (AlgEquiv.restrictNormalHom_apply K rho x).symm
          _ = algebraMap K Omega x :=
            congrArg (fun z : K => (z : Omega)) hx }
  refine ⟨sigma, ?_, ?_⟩
  · exact hrhoQ
  · change AlgEquiv.restrictNormalHom L rho = tau
    exact hrhoL

set_option synthInstance.maxHeartbeats 1000000 in
-- The valuative-topology criterion synthesizes the completion's discrete rank-one valuation.
set_option maxHeartbeats 2000000 in
-- The direct construction avoids changing the canonical norm on an absolute-value completion.
@[implicit_reducible]
noncomputable def absoluteExtensionNonarchimedean
    {L : Type u} [Field L]
    (w : AbsoluteValue L ℝ)
    [Fact w.IsNontrivial]
    [IsUltrametricDist w.Completion]
    [ValuativeRel w.Completion]
    [LocallyCompactSpace w.Completion]
    [Valuation.Compatible (NormedField.valuation (K := w.Completion))] :
    IsNonarchimedeanLocalField w.Completion := by
  letI : NontriviallyNormedField w.Completion :=
    Towers.NumberTheory.Milne.absoluteNontriviallyNormed w
  haveI hcompact : LocallyCompactSpace w.Completion := inferInstance
  haveI htop : IsValuativeTopology w.Completion := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : w.Completion) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := w.Completion)))ˣ,
          {x | (NormedField.valuation (K := w.Completion)).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := w.Completion)).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := w.Completion))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial w.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := w.Completion))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }

end TBluepr
end Towers
