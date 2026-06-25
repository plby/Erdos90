import Submission.NumberTheory.Locals.ThreeUnitCubes
import Submission.FieldTheory.TameThreeKoch.CyclotomicCubicSubfields
import Submission.FieldTheory.RationalRamificationCleanup

/-!
# The conductor-nine correction at 3

This file is the wild-prime analogue of the tame cyclotomic cleanup.  The
local input is stated in the form supplied by local reciprocity: local units
simultaneously parametrize the restriction to a totally ramified cubic layer
and an exponent-three character of the ambient inertia group.

The calculation of `ℤ_[3]ˣ / (ℤ_[3]ˣ)³` then shows that the latter
character factors through the former.  Taking the inverse descended
character gives the required cancellation.  The conductor-nine field from
`Part1` supplies the totally ramified cubic layer in the intended use.
-/

open scoped Pointwise Topology

noncomputable section

namespace Submission
namespace TBluepr

open Submission.NumberTheory.Milne

local instance conductorNineCleanupFiniteDimensional
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ D :=
  D.finiteDimensional

local instance conductorNineCleanupIsGalois
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ D :=
  D.isGalois

set_option maxHeartbeats 2000000 in
-- The finite-field cardinality and nested restriction instances need extra elaboration time.
set_option synthInstance.maxHeartbeats 500000 in
/-- At the rational prime `3`, an exponent-three inertia character that is
simultaneously parametrized with restriction to a totally ramified cubic
layer descends to that cubic Galois group and can be cancelled there.

The simultaneous parametrization is the exact group-theoretic output needed
from local reciprocity.  It only concerns the abelian quotient detected by
`restriction × lift`; it does not require local units to surject onto a
possibly nonabelian ambient inertia group. -/
theorem cubic_cancels_nine
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal 3)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A : Type*} [CommGroup A]
    (hAcube : ∀ a : A, a ^ 3 = 1)
    (lift : P.inertia Gal(L/ℚ) →* A)
    (unitRestriction :
      letI : Algebra ℚ C := C.algebra'
      RationalPlaceUnits →* Gal(C/ℚ))
    (unitLift : RationalPlaceUnits →* A)
    (hlocalize :
      letI : Algebra ℚ C := C.algebra'
      ∀ sigma : P.inertia Gal(L/ℚ),
        ∃ u : RationalPlaceUnits,
          unitRestriction u =
              AlgEquiv.restrictNormalHom C sigma.1 ∧
            unitLift u = lift sigma) :
    letI : Algebra ℚ C := C.algebra'
    ∃ chi : Gal(C/ℚ) →* A,
      ∀ sigma : P.inertia Gal(L/ℚ),
        chi (AlgEquiv.restrictNormalHom C sigma.1) * lift sigma = 1 := by
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let Q : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  let restrictionI :=
    numberInertiaRestriction C hCgal.to_normal 3 P
  have htargetCard : Nat.card (Q.inertia Gal(C/ℚ)) = 3 :=
    (inertia_ramification_idx
      (L := C) Nat.prime_three Q).trans hram
  have htop : Q.inertia Gal(C/ℚ) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact htargetCard.trans hcard.symm
  have hsurjectiveI : Function.Surjective restrictionI :=
    number_restriction_surjective C hCfin hCgal
      Nat.prime_three P
  let restriction : P.inertia Gal(L/ℚ) →* Gal(C/ℚ) :=
    (Q.inertia Gal(C/ℚ)).subtype.comp restrictionI
  have hrestriction : Function.Surjective restriction := by
    intro tau
    let tauI : Q.inertia Gal(C/ℚ) :=
      ⟨tau, by rw [htop]; exact Subgroup.mem_top tau⟩
    obtain ⟨sigma, hsigma⟩ := hsurjectiveI tauI
    refine ⟨sigma, ?_⟩
    exact congrArg Subtype.val hsigma
  have hunitRestriction : Function.Surjective unitRestriction := by
    intro tau
    obtain ⟨sigma, hsigma⟩ := hrestriction tau
    obtain ⟨u, huRestriction, -⟩ := hlocalize sigma
    refine ⟨u, ?_⟩
    exact huRestriction.trans hsigma
  have hGalCube : ∀ tau : Gal(C/ℚ), tau ^ 3 = 1 := by
    intro tau
    rw [← hcard]
    exact pow_card_eq_one'
  obtain ⟨restrictionQ, hrestrictionQ⟩ :=
    rational_character_cubic
      unitRestriction hGalCube
  have hrestrictionQsurj : Function.Surjective restrictionQ := by
    intro tau
    obtain ⟨u, hu⟩ := hunitRestriction tau
    refine ⟨rationalCubicCharacter u, ?_⟩
    exact (DFunLike.congr_fun hrestrictionQ u).trans hu
  letI : Fintype PadicIntCubic := Fintype.ofFinite _
  letI : Fintype Gal(C/ℚ) := Fintype.ofFinite _
  have hcards : Fintype.card PadicIntCubic =
      Fintype.card Gal(C/ℚ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      padic_cubic_card, hcard]
  have hrestrictionQinj : Function.Injective restrictionQ :=
    ((Fintype.bijective_iff_surjective_and_card restrictionQ).2
      ⟨hrestrictionQsurj, hcards⟩).1
  obtain ⟨liftQ, hliftQ⟩ :=
    rational_character_cubic
      unitLift hAcube
  have hker : restriction.ker ≤ lift.ker := by
    intro sigma hsigma
    obtain ⟨u, huRestriction, huLift⟩ := hlocalize sigma
    have hresU : unitRestriction u = 1 := by
      rw [huRestriction]
      exact hsigma
    have hresQone : restrictionQ
        (rationalCubicCharacter u) = 1 :=
      (DFunLike.congr_fun hrestrictionQ u).trans hresU
    have hQone : rationalCubicCharacter u = 1 := by
      apply hrestrictionQinj
      simpa using hresQone
    rw [MonoidHom.mem_ker]
    have h := DFunLike.congr_fun hliftQ u
    calc
      lift sigma = unitLift u := huLift.symm
      _ = liftQ (rationalCubicCharacter u) := h.symm
      _ = liftQ 1 := by rw [hQone]
      _ = 1 := map_one liftQ
  refine ⟨inverseFactorCharacter restriction hrestriction lift hker, ?_⟩
  intro sigma
  exact inverse_character_mul
    restriction hrestriction lift hker sigma

set_option maxHeartbeats 2000000 in
-- The nested finite-field and restriction instances need extra elaboration time.
set_option synthInstance.maxHeartbeats 500000 in
/-- A convenient special case in which local reciprocity is presented as a
surjective map from rational local units onto the ambient inertia group. -/
theorem cancels_nine_surjective
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal 3)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A : Type*} [CommGroup A]
    (hAcube : ∀ a : A, a ^ 3 = 1)
    (lift : P.inertia Gal(L/ℚ) →* A)
    (unitArtin : RationalPlaceUnits →*
      P.inertia Gal(L/ℚ))
    (hunitArtin : Function.Surjective unitArtin) :
    letI : Algebra ℚ C := C.algebra'
    ∃ chi : Gal(C/ℚ) →* A,
      ∀ sigma : P.inertia Gal(L/ℚ),
        chi (AlgEquiv.restrictNormalHom C sigma.1) * lift sigma = 1 := by
  letI : Algebra ℚ C := C.algebra'
  let unitRestriction : RationalPlaceUnits →* Gal(C/ℚ) :=
    (AlgEquiv.restrictNormalHom C).comp
      ((P.inertia Gal(L/ℚ)).subtype.comp unitArtin)
  let unitLift : RationalPlaceUnits →* A :=
    lift.comp unitArtin
  apply cubic_cancels_nine
    C hCfin hCgal P hram hcard hAcube lift unitRestriction unitLift
  intro sigma
  obtain ⟨u, hu⟩ := hunitArtin sigma
  refine ⟨u, ?_, ?_⟩
  · change AlgEquiv.restrictNormalHom C (unitArtin u).1 = _
    rw [hu]
  · change lift (unitArtin u) = lift sigma
    rw [hu]

set_option maxHeartbeats 2000000 in
-- Absolute-character inflation requires a larger typeclass search budget.
set_option synthInstance.maxHeartbeats 500000 in
/-- The conductor-nine cancellation character inflated to the absolute
Galois group. -/
theorem absolute_cancels_nine
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ D)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    (P : Ideal (NumberField.RingOfIntegers D))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal 3)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    (hAcube : ∀ a : A, a ^ 3 = 1)
    (liftFinite : Gal(D/ℚ) →* A)
    (unitRestriction :
      letI : Algebra ℚ C := C.algebra'
      RationalPlaceUnits →* Gal(C/ℚ))
    (unitLift : RationalPlaceUnits →* A)
    (hlocalize :
      letI : Algebra ℚ C := C.algebra'
      ∀ sigma : P.inertia Gal(D/ℚ),
        ∃ u : RationalPlaceUnits,
          unitRestriction u =
              AlgEquiv.restrictNormalHom C sigma.1 ∧
            unitLift u = liftFinite sigma.1) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        ∀ sigma : Gal(AlgebraicClosure ℚ/ℚ),
          AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
              P.inertia Gal(D/ℚ) →
            chi sigma *
              liftFinite
                (AlgEquiv.restrictNormalHom D.toIntermediateField sigma) = 1 := by
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let liftI : P.inertia Gal(D/ℚ) →* A :=
    liftFinite.comp (P.inertia Gal(D/ℚ)).subtype
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_nine
      C hCfin hCgal P hram hcard hAcube liftI unitRestriction unitLift
        (by simpa [liftI] using hlocalize)
  let chi : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    absoluteThroughIntermediate D C hCgal.to_normal chiC
  refine ⟨chi,
    absolute_through_continuous
      D C hCgal.to_normal chiC, ?_⟩
  intro sigma hsigma
  let tau : P.inertia Gal(D/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma, hsigma⟩
  change chiC (finiteIntermediateRestriction D C hCgal.to_normal tau.1) *
      liftFinite tau.1 = 1
  exact hcancel tau

set_option maxHeartbeats 2000000 in
-- Absolute-character inflation requires a larger typeclass search budget.
set_option synthInstance.maxHeartbeats 500000 in
/-- Absolute conductor-nine cancellation when the character to cancel is
defined only on the selected finite inertia subgroup.  This is the form used
by a central-kernel lift that has no global kernel-valued extension. -/
theorem cancels_conductor_nine
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ D)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    (P : Ideal (NumberField.RingOfIntegers D))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal 3)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    (hAcube : ∀ a : A, a ^ 3 = 1)
    (liftI : P.inertia Gal(D/ℚ) →* A)
    (unitRestriction :
      letI : Algebra ℚ C := C.algebra'
      RationalPlaceUnits →* Gal(C/ℚ))
    (unitLift : RationalPlaceUnits →* A)
    (hlocalize :
      letI : Algebra ℚ C := C.algebra'
      ∀ sigma : P.inertia Gal(D/ℚ),
        ∃ u : RationalPlaceUnits,
          unitRestriction u =
              AlgEquiv.restrictNormalHom C sigma.1 ∧
            unitLift u = liftI sigma) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
          (hsigma : AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
            P.inertia Gal(D/ℚ)),
          chi sigma *
            liftI
              ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
                hsigma⟩ = 1 := by
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_nine
      C hCfin hCgal P hram hcard hAcube liftI unitRestriction unitLift
        hlocalize
  let chi : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    absoluteThroughIntermediate D C hCgal.to_normal chiC
  refine ⟨chi,
    absolute_through_continuous
      D C hCgal.to_normal chiC, ?_⟩
  intro sigma hsigma
  let tau : P.inertia Gal(D/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma, hsigma⟩
  change chiC (finiteIntermediateRestriction D C hCgal.to_normal tau.1) *
      liftI tau = 1
  exact hcancel tau

end TBluepr
end Submission
