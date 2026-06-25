import Towers.FieldTheory.TameThreeKoch.AbsoluteLiftTransport

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open NumberField

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The nested restricted-field instances need extra search time.
set_option maxHeartbeats 60000000 in
-- The inertia calculation traverses several finite Galois field towers.
/-- The finite lift above the original tame layer has trivial projection on
inertia at `3` after adjoining the rational degree-three correction field. -/
theorem rational_projected_inertia
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
    (liftFinite : Gal(D0/ℚ) →* E)
    (hliftFinite : liftFinite.comp
      (AlgEquiv.restrictNormalHom D0.toIntermediateField) = liftStandard)
    (hL0D0 : rationalLayerClosure S N ≤
      D0.toIntermediateField)
    (hthreeNotMem : 3 ∉ S) :
    ∀ sigma : (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ),
      q (liftFinite (nineRestrictionLift D0 sigma.1)) = 1 := by
  subst N
  let L0 : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    rationalLayerClosure S
      (rational_tame_open betaA hbetaA)
  let Dthree := nineCorrectionCompositum D0
  let Pthree := rationalNineAbove D0
  intro sigma
  letI : Pthree.IsPrime := rational_nine_above D0
  letI : Pthree.LiesOver (Ideal.rationalPrimeIdeal 3) :=
    nine_above_lies D0
  have hL0Dthree : L0 ≤ Dthree.toIntermediateField :=
    hL0D0.trans le_sup_left
  let C : IntermediateField ℚ Dthree := L0.restrict hL0Dthree
  let eC : L0 ≃ₐ[ℚ] C := IntermediateField.restrict_algEquiv hL0Dthree
  let hCfin : FiniteDimensional ℚ C :=
    Module.Finite.equiv eC.toLinearEquiv
  let hCgal : IsGalois ℚ C := IsGalois.of_algEquiv eC
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  have hCunramified : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers C) 3 :=
    rational_unramified_alg eC
      (rational_tame_outside
        S (rational_tame_open betaA hbetaA)
          3 Nat.prime_three hthreeNotMem)
  have hCres : AlgEquiv.restrictNormalHom C sigma.1 = 1 := by
    have h := character_restriction_unramified
      C hCfin hCgal (MonoidHom.id Gal(C/ℚ))
        Nat.prime_three hCunramified Pthree sigma
    change (numberInertiaRestriction C hCgal.to_normal
      3 Pthree sigma).1 = 1 at h
    exact h
  obtain ⟨tau, htau⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := Dthree) (E := AlgebraicClosure ℚ) sigma.1
  rcases sigma with ⟨sigma, hsigma⟩
  dsimp only at htau ⊢
  subst sigma
  have hL0res : AlgEquiv.restrictNormalHom L0 tau = 1 := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun hCres (eC x)
    apply eC.injective
    apply Subtype.ext
    apply Subtype.ext
    calc
      (((eC ((AlgEquiv.restrictNormalHom L0 tau) x) : C) : Dthree) :
          AlgebraicClosure ℚ) = tau (x : AlgebraicClosure ℚ) :=
        @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance L0
            (instGaloisClosure S
              (rational_tame_open betaA hbetaA)).to_normal
              tau x
      _ = tau ((((eC x : C) : Dthree) : AlgebraicClosure ℚ)) := by
        rfl
      _ = (((AlgEquiv.restrictNormalHom Dthree.toIntermediateField tau)
            ((eC x : C) : Dthree) : Dthree) : AlgebraicClosure ℚ) := by
        symm
        exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
          (AlgebraicClosure ℚ) inferInstance inferInstance Dthree
            Dthree.isGalois.to_normal tau ((eC x : C) : Dthree)
      _ = (((eC x : C) : Dthree) : AlgebraicClosure ℚ) := by
        apply congrArg (fun z : Dthree => (z : AlgebraicClosure ℚ))
        calc
          (AlgEquiv.restrictNormalHom Dthree.toIntermediateField tau)
              ((eC x : C) : Dthree) =
              ((AlgEquiv.restrictNormalHom C
                (AlgEquiv.restrictNormalHom Dthree.toIntermediateField tau))
                  (eC x) : C) := by
            symm
            exact AlgEquiv.restrictNormalHom_apply C _ _
          _ = ((eC x : C) : Dthree) := congrArg Subtype.val hx
  calc
    q (liftFinite
        (nineRestrictionLift D0
          (AlgEquiv.restrictNormalHom Dthree.toIntermediateField tau))) =
        q (liftStandard tau) := by
      rw [nine_restriction_restrict]
      exact congrArg q (DFunLike.congr_fun hliftFinite tau)
    _ = betaA.rangeRestrict
        (rationalAbsoluteRestriction S tau) :=
      DFunLike.congr_fun hliftStandard tau
    _ = rational_tame_range betaA hbetaA
        ((AlgEquiv.autCongr
          (rationalTameClosure S
            (rational_tame_open betaA hbetaA))).symm
            (AlgEquiv.restrictNormalHom L0 tau)) := by
      symm
      exact rational_tame_restrict
        betaA hbetaA tau
    _ = 1 := by rw [hL0res, map_one, map_one]

end TBluepr
end Towers
