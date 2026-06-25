import Submission.FieldTheory.TameThreeKoch.AbsoluteRestriction

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v

open NumberField

local instance part4FiniteGaloisFiniteDimensional
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ K := K.finiteDimensional

local instance part4FiniteGaloisIsGalois
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ K := K.isGalois

local instance part4FiniteGaloisNormal
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Normal ℚ K := K.isGalois.to_normal

local instance part4AlgebraicClosureAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isAlgebraic ℚ (AlgebraicClosure ℚ) inferInstance
    inferInstance inferInstance inferInstance
      (AlgebraicClosure.instIsAlgClosure ℚ)

local instance part4AlgebraicClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) := by
  rw [normal_iff]
  intro x
  exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Transport across algebraic closures has a large finite-layer instance tower.
/-- Transporting an absolute lift between two chosen algebraic closures
preserves its projection to the canonical finite layer, provided the chosen
closure equivalence extends the displayed identification of that layer. -/
theorem transport_projection_base
    {S : Finset ℕ} {A E Gamma : Type*}
    [Group A] [Group E] [Group Gamma]
    (betaA : rationalTameGalois S →* A)
    (q : E →* betaA.range)
    (liftAbs : Gamma →* E)
    (baseAbs : Gamma →* betaA.range)
    (transportAbsolute : Gal(AlgebraicClosure ℚ/ℚ) →* Gamma)
    (hliftAbs : q.comp liftAbs = baseAbs)
    (hbaseTransport : baseAbs.comp transportAbsolute =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S)) :
    q.comp (liftAbs.comp transportAbsolute) =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S) := by
  rw [← MonoidHom.comp_assoc, hliftAbs]
  exact hbaseTransport

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Preliminary-lift transport synthesizes both closure and finite-layer structures.
/-- Transporting the preliminary lift to the fixed algebraic closure preserves
its projection to the canonical finite layer. -/
theorem transport_absolute_projection
    {S : Finset ℕ}
    {A E M Omega : Type*}
    [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [Group E]
    [Field M] [Algebra ℚ M]
    [Field Omega] [Algebra ℚ Omega] [IsAlgClosure ℚ Omega]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA)
    (Lc : IntermediateField ℚ M)
    (eLc : rationalLayerClosure S
      (rational_tame_open betaA hbetaA) ≃ₐ[ℚ] Lc)
    (LcInClosure : IntermediateField ℚ Omega)
    (eLcInClosure : Lc ≃ₐ[ℚ] LcInClosure)
    [FiniteDimensional ℚ LcInClosure] [IsGalois ℚ LcInClosure]
    [IsScalarTower ℚ LcInClosure Omega]
    (rangeEquiv : Gal(LcInClosure/ℚ) ≃* betaA.range)
    (hrangeEquiv : rangeEquiv =
      (AlgEquiv.autCongr eLcInClosure).symm.trans
        ((AlgEquiv.autCongr eLc).symm.trans
          ((AlgEquiv.autCongr
            (rationalTameClosure S
              (rational_tame_open betaA hbetaA))).symm.trans
              (rational_tame_range betaA hbetaA))))
    (q : E →* betaA.range)
    (liftAbs : Gal(Omega/ℚ) →* E)
    (hliftAbs : q.comp liftAbs =
      rangeEquiv.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom LcInClosure))
    (eOmega : Omega ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (heOmega : ∀ x : LcInClosure,
      eOmega x =
        ((eLc.trans eLcInClosure).symm x : AlgebraicClosure ℚ)) :
    let transportAbsolute : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(Omega/ℚ) :=
      (AlgEquiv.autCongr eOmega).symm.toMonoidHom
    q.comp (liftAbs.comp transportAbsolute) =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S) := by
  dsimp only
  letI : IsGalois ℚ (rationalLayerClosure S
      (rational_tame_open betaA hbetaA)) :=
    instGaloisClosure S
      (rational_tame_open betaA hbetaA)
  letI : Normal ℚ LcInClosure :=
    (inferInstance : IsGalois ℚ LcInClosure).to_normal
  let transportAbsolute : Gal(AlgebraicClosure ℚ/ℚ) →*
      Gal(Omega/ℚ) := (AlgEquiv.autCongr eOmega).symm.toMonoidHom
  apply MonoidHom.ext
  intro sigma
  have hproj := DFunLike.congr_fun hliftAbs (transportAbsolute sigma)
  rw [MonoidHom.comp_apply] at hproj
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hproj]
  apply Subtype.ext
  change rangeEquiv
      (AlgEquiv.restrictNormalHom LcInClosure
        (transportAbsolute sigma)) =
    betaA (rationalAbsoluteRestriction S sigma)
  rw [hrangeEquiv]
  let eCombined := eLc.trans eLcInClosure
  have htransport :
      (AlgEquiv.autCongr eCombined).symm
          (AlgEquiv.restrictNormalHom LcInClosure
            ((AlgEquiv.autCongr eOmega).symm sigma)) =
        AlgEquiv.restrictNormalHom
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA)) sigma := by
    apply AlgEquiv.ext
    intro x
    apply eCombined.injective
    apply Subtype.ext
    apply eOmega.injective
    simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, AlgEquiv.symm_symm]
    rw [AlgEquiv.apply_symm_apply]
    let rho : Gal(Omega/ℚ) := eOmega.trans (sigma.trans eOmega.symm)
    change eOmega ↑((AlgEquiv.restrictNormalHom LcInClosure rho)
      (eCombined x)) = _
    calc
      _ = eOmega (rho (eCombined x : Omega)) := by
        congr 1
        let hnormalCanonical : @Normal ℚ LcInClosure Rat.instField
            LcInClosure.toField LcInClosure.algebra' := by
          have halg : (inferInstance : Algebra ℚ LcInClosure) =
              LcInClosure.algebra' := Subsingleton.elim _ _
          exact halg ▸ (inferInstance : Normal ℚ LcInClosure)
        exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance Omega
          inferInstance inferInstance LcInClosure hnormalCanonical rho
            (eCombined x)
      _ = eOmega (eCombined
          ((AlgEquiv.restrictNormalHom
            (rationalLayerClosure S
              (rational_tame_open betaA hbetaA)) sigma) x) :
              Omega) := by
        change eOmega (eOmega.symm
          (sigma (eOmega (eCombined x : Omega)))) = _
        rw [eOmega.apply_symm_apply]
        rw [show eOmega (eCombined x : Omega) =
            (x : AlgebraicClosure ℚ) by
          simpa [eCombined] using heOmega (eCombined x)]
        rw [show eOmega (eCombined
            ((AlgEquiv.restrictNormalHom
              (rationalLayerClosure S
                (rational_tame_open betaA hbetaA)) sigma) x) :
                Omega) =
            ((AlgEquiv.restrictNormalHom
              (rationalLayerClosure S
                (rational_tame_open betaA hbetaA)) sigma) x :
                AlgebraicClosure ℚ) by
          simpa [eCombined] using heOmega (eCombined
            ((AlgEquiv.restrictNormalHom
              (rationalLayerClosure S
                (rational_tame_open betaA hbetaA)) sigma) x))]
        have hnormalL : Normal ℚ
            (rationalLayerClosure S
              (rational_tame_open betaA hbetaA)) :=
          (inferInstance : IsGalois ℚ
            (rationalLayerClosure S
              (rational_tame_open betaA hbetaA))).to_normal
        exact (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA))
          hnormalL sigma x).symm
  have hbase :=
    rational_tame_restrict
      betaA hbetaA sigma
  simp only [MulEquiv.trans_apply]
  rw [show (AlgEquiv.autCongr eLc).symm
      ((AlgEquiv.autCongr eLcInClosure).symm
        (AlgEquiv.restrictNormalHom LcInClosure
          (transportAbsolute sigma))) =
      AlgEquiv.restrictNormalHom
        (rationalLayerClosure S
          (rational_tame_open betaA hbetaA)) sigma by
    simpa [transportAbsolute, AlgEquiv.autCongr_trans] using htransport]
  simpa [rationalAbsoluteRestriction] using
    congrArg Subtype.val hbase

/-- The finite field cut out by a lift contains the canonical finite layer
whenever the lift projects to the canonical base representation. -/
theorem rational_tame_fixing
    {S : Finset ℕ}
    (N : OpenNormalSubgroup (rationalTameGalois S))
    {A E : Type*}
    [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [Group E]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA)
    (hN : N = rational_tame_open betaA hbetaA)
    (q : E →* betaA.range)
    (liftStandard : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftStandard : q.comp liftStandard =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S))
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hliftStandardKer : liftStandard.ker =
      D0.toIntermediateField.fixingSubgroup) :
    D0.toIntermediateField.fixingSubgroup ≤
      (rationalLayerClosure S N).fixingSubgroup := by
  subst N
  letI : Normal ℚ (rationalLayerClosure S
      (rational_tame_open betaA hbetaA)) :=
    (instGaloisClosure S
      (rational_tame_open betaA hbetaA)).to_normal
  intro tau htau
  have hliftOne : liftStandard tau = 1 := by
    have htauKer : tau ∈ liftStandard.ker := by
      rw [hliftStandardKer]
      exact htau
    exact htauKer
  have hbaseOne : betaA.rangeRestrict
      (rationalAbsoluteRestriction S tau) = 1 := by
    have h := DFunLike.congr_fun hliftStandard tau
    simpa [hliftOne] using h.symm
  have hfinite :=
    rational_tame_restrict
      betaA hbetaA tau
  let finiteEquiv := (AlgEquiv.autCongr
    (rationalTameClosure S
      (rational_tame_open betaA hbetaA))).symm
  let baseEquiv :=
    rational_tame_range betaA hbetaA
  have hres : AlgEquiv.restrictNormalHom
      (rationalLayerClosure S
        (rational_tame_open betaA hbetaA)) tau = 1 := by
    have hboth : baseEquiv (finiteEquiv
        (AlgEquiv.restrictNormalHom
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA)) tau)) = 1 := by
      change (rational_tame_range betaA hbetaA)
        ((AlgEquiv.autCongr
          (rationalTameClosure S
            (rational_tame_open betaA hbetaA))).symm
              (AlgEquiv.restrictNormalHom
                (rationalLayerClosure S
                  (rational_tame_open betaA hbetaA)) tau)) = 1
      exact hfinite.trans hbaseOne
    have hfiniteOne : finiteEquiv
        (AlgEquiv.restrictNormalHom
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA)) tau) = 1 := by
      apply baseEquiv.injective
      exact hboth.trans (map_one baseEquiv).symm
    apply finiteEquiv.injective
    exact hfiniteOne.trans (map_one finiteEquiv).symm
  intro x
  have hx := DFunLike.congr_fun hres x
  change tau (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)
  calc
    tau (x : AlgebraicClosure ℚ) =
        ((AlgEquiv.restrictNormalHom
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA)) tau x) :
              AlgebraicClosure ℚ) := by
      symm
      exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance
        (rationalLayerClosure S
          (rational_tame_open betaA hbetaA))
        (instGaloisClosure S
          (rational_tame_open betaA hbetaA)).to_normal tau x
    _ = (x : AlgebraicClosure ℚ) := congrArg Subtype.val hx

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Projected inertia uses the full canonical correction-compositum field tower.
/-- The finite lift has trivial projected inertia at every tame ramified
prime of its correction compositum, because the canonical base layer is
unramified there. -/
theorem rational_tame_projected
    {S : Finset ℕ}
    (N : OpenNormalSubgroup (rationalTameGalois S))
    {A E : Type*}
    [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [Group E]
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA)
    (hN : N = rational_tame_open betaA hbetaA)
    (q : E →* betaA.range)
    (liftStandard : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hliftStandard : q.comp liftStandard =
      betaA.rangeRestrict.comp (rationalAbsoluteRestriction S))
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (liftFinite : Gal(D0/ℚ) →* E)
    (hliftFinite : liftFinite.comp
      (AlgEquiv.restrictNormalHom D0.toIntermediateField) = liftStandard)
    (hL0D0 : rationalLayerClosure S N ≤
      D0.toIntermediateField) :
    ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        q (liftFinite
          (tameCyclotomicRestriction
            D0 hD0three S sigma.1)) = 1 := by
  subst N
  intro i sigma
  let D := tameCorrectionCompositum D0 hD0three S
  let P := tameCyclotomicAbove D0 hD0three S i
  letI : P.IsPrime :=
    tame_cyclotomic_above D0 hD0three S i
  letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
    tame_above_lies D0 hD0three S i
  have hD0D : D0.toIntermediateField ≤ D.toIntermediateField := by
    simpa [D, tameCyclotomicFamily] using
      tame_cyclotomic_compositum D0 hD0three S none
  have hL0D : rationalLayerClosure S
      (rational_tame_open betaA hbetaA) ≤
      D.toIntermediateField := hL0D0.trans hD0D
  let C : IntermediateField ℚ D :=
    (rationalLayerClosure S
      (rational_tame_open betaA hbetaA)).restrict hL0D
  let eC : rationalLayerClosure S
      (rational_tame_open betaA hbetaA) ≃ₐ[ℚ] C :=
    IntermediateField.restrict_algEquiv hL0D
  let hCfin : FiniteDimensional ℚ C :=
    Module.Finite.equiv eC.toLinearEquiv
  let hCgal : IsGalois ℚ C := IsGalois.of_algEquiv eC
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  have hCunramified : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers C) i.prime :=
    rational_unramified_alg eC
      (rational_tame_outside
        S (rational_tame_open betaA hbetaA)
          i.prime i.prime_isPrime i.prime_not_mem)
  have hCres : AlgEquiv.restrictNormalHom C sigma.1 = 1 := by
    have h := character_restriction_unramified
      C hCfin hCgal (MonoidHom.id Gal(C/ℚ))
        i.prime_isPrime hCunramified P sigma
    change (numberInertiaRestriction C hCgal.to_normal
      i.prime P sigma).1 = 1 at h
    exact h
  obtain ⟨tau, htau⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := D) (E := AlgebraicClosure ℚ) sigma.1
  rcases sigma with ⟨sigma, hsigma⟩
  dsimp only at htau ⊢
  subst sigma
  have hL0res : AlgEquiv.restrictNormalHom
      (rationalLayerClosure S
        (rational_tame_open betaA hbetaA)) tau = 1 := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun hCres (eC x)
    apply eC.injective
    apply Subtype.ext
    apply Subtype.ext
    calc
      (((eC ((AlgEquiv.restrictNormalHom
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA)) tau) x) : C) :
            D) : AlgebraicClosure ℚ) = tau (x : AlgebraicClosure ℚ) :=
        @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance
          (rationalLayerClosure S
            (rational_tame_open betaA hbetaA))
          (instGaloisClosure S
            (rational_tame_open betaA hbetaA)).to_normal tau x
      _ = tau ((((eC x : C) : D) : AlgebraicClosure ℚ)) := by rfl
      _ = (((AlgEquiv.restrictNormalHom D.toIntermediateField tau)
            ((eC x : C) : D) : D) : AlgebraicClosure ℚ) := by
        symm
        exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance D
            D.isGalois.to_normal tau ((eC x : C) : D)
      _ = (((eC x : C) : D) : AlgebraicClosure ℚ) := by
        apply congrArg (fun z : D => (z : AlgebraicClosure ℚ))
        calc
          (AlgEquiv.restrictNormalHom D.toIntermediateField tau)
              ((eC x : C) : D) =
              ((AlgEquiv.restrictNormalHom C
                (AlgEquiv.restrictNormalHom D.toIntermediateField tau))
                  (eC x) : C) := by
            symm
            exact AlgEquiv.restrictNormalHom_apply C _ _
          _ = ((eC x : C) : D) := congrArg Subtype.val hx
  calc
    q (liftFinite
        (tameCyclotomicRestriction D0 hD0three S
          (AlgEquiv.restrictNormalHom D.toIntermediateField tau))) =
        q (liftStandard tau) := by
      rw [tame_restriction_restrict]
      exact congrArg q (DFunLike.congr_fun hliftFinite tau)
    _ = betaA.rangeRestrict
        (rationalAbsoluteRestriction S tau) :=
      DFunLike.congr_fun hliftStandard tau
    _ = rational_tame_range betaA hbetaA
        ((AlgEquiv.autCongr
          (rationalTameClosure S
            (rational_tame_open betaA hbetaA))).symm
            (AlgEquiv.restrictNormalHom
              (rationalLayerClosure S
                (rational_tame_open betaA hbetaA)) tau)) := by
      symm
      exact rational_tame_restrict
        betaA hbetaA tau
    _ = 1 := by
      rw [hL0res]
      have hfirst : (AlgEquiv.autCongr
          (rationalTameClosure S
            (rational_tame_open betaA hbetaA))).symm 1 = 1 :=
        map_one _
      rw [hfirst]
      exact map_one _

end TBluepr
end Submission
