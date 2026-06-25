import Submission.FieldTheory.LocalReciprocityBridge
import Submission.ClassField.LocalExistence.AssembledLocalReciprocity
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Canonical conductor-nine correction compositum

This file adjoins the canonical cubic subfield of `ℚ(ζ₉)` to an arbitrary
finite Galois lift field and packages the resulting correction theorem.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LBrauer
open Submission.CField.Ideles
open NumberField

local instance rationalNineFiniteGaloisFiniteDimensional
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ K := K.finiteDimensional

local instance rationalNineFiniteGaloisIsGalois
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ K := K.isGalois

local instance rationalNineFiniteGaloisNormal
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Normal ℚ K := K.isGalois.to_normal

/-- The height-one prime selected by `rationalThreePlace` is the prime
of `ℚ` above the ordinary ideal `(3)` of `ℤ`. -/
theorem rational_lies_ideal :
    rationalThreePlace.asIdeal.LiesOver
      (Ideal.rationalPrimeIdeal 3) := by
  rw [Ideal.liesOver_iff]
  symm
  let e0 : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have halg : algebraMap ℤ (NumberField.RingOfIntegers ℚ) =
      e0.symm.toRingHom := Subsingleton.elim _ _
  change rationalThreePlace.asIdeal.comap
      (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) =
        Ideal.rationalPrimeIdeal 3
  rw [halg]
  change ((Ideal.span {((3 : ℕ) : ℤ)}).map e0.symm.toRingHom).comap
      e0.symm.toRingHom = Ideal.rationalPrimeIdeal 3
  change ((Ideal.span {((3 : ℕ) : ℤ)}).map e0.symm.toRingHom).comap
      e0.symm.toRingHom = Ideal.span {(3 : ℤ)}
  ext x
  change e0.symm x ∈ (Ideal.span {(3 : ℤ)}).map e0.symm ↔
    x ∈ Ideal.span {(3 : ℤ)}
  rw [Ideal.mem_map_iff_of_surjective e0.symm e0.symm.surjective]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := e0.symm.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The conductor-nine cubic field as a finite Galois intermediate field. -/
noncomputable def rationalNineGalois :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) := by
  exact
    { toIntermediateField := rationalNineCubic
      finiteDimensional := inferInstance
      isGalois := rational_nine_galois.2.1 }

/-- The common compositum of a finite Galois lift field and the
conductor-nine cubic field. -/
noncomputable def nineCorrectionCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  D0 ⊔ rationalNineGalois

/-- The conductor-nine cubic field inside the common compositum. -/
noncomputable def nineCubicCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IntermediateField ℚ (nineCorrectionCompositum D0) :=
  rationalNineCubic.restrict (by exact le_sup_right)

/-- Its canonical equivalence with the original cubic subfield of
`ℚ(ζ₉)`. -/
noncomputable def rationalNineCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    letI : Algebra ℚ (nineCubicCompositum D0) :=
      (nineCubicCompositum D0).algebra'
    nineCubicCompositum D0 ≃ₐ[ℚ]
      rationalNineCubic := by
  exact (IntermediateField.restrict_algEquiv (show
      rationalNineCubic ≤
        (nineCorrectionCompositum D0).toIntermediateField by
          exact le_sup_right)).symm

/-- The original lift field inside the conductor-nine compositum. -/
noncomputable def rationalNineLift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IntermediateField ℚ (nineCorrectionCompositum D0) :=
  D0.toIntermediateField.restrict (by exact le_sup_left)

/-- The canonical equivalence from the original lift field to its copy in
the common compositum. -/
noncomputable def nineLiftCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    letI : Algebra ℚ (rationalNineLift D0) :=
      (rationalNineLift D0).algebra'
    D0 ≃ₐ[ℚ] rationalNineLift D0 :=
  IntermediateField.restrict_algEquiv (by exact le_sup_left)

/-- Restriction from the conductor-nine compositum to the original finite
lift field.  A finite lift on `D0` can be pulled back along this map. -/
noncomputable def nineRestrictionLift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(nineCorrectionCompositum D0/ℚ) →* Gal(D0/ℚ) := by
  let E := rationalNineLift D0
  let eE := nineLiftCompositum D0
  letI : FiniteDimensional ℚ D0 := D0.finiteDimensional
  letI : IsGalois ℚ D0 := D0.isGalois
  letI : Algebra ℚ E := E.algebra'
  let eE' : D0 ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := eE.toRingEquiv) (by
    intro x
    rfl)
  letI : IsGalois ℚ E := IsGalois.of_algEquiv eE'
  exact (AlgEquiv.autCongr eE').symm.toMonoidHom.comp
    (finiteIntermediateRestriction
      (nineCorrectionCompositum D0) E
      (inferInstance : Normal ℚ E))

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Restriction through the conductor-nine compositum has a large field tower.
/-- Restricting an absolute automorphism first to the conductor-nine
compositum and then to its copy of the lift field agrees with direct
restriction to the original lift field. -/
@[simp]
theorem nine_restriction_restrict
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    nineRestrictionLift D0
        (AlgEquiv.restrictNormalHom
          (nineCorrectionCompositum D0).toIntermediateField sigma) =
      AlgEquiv.restrictNormalHom D0.toIntermediateField sigma := by
  let D := nineCorrectionCompositum D0
  let E := rationalNineLift D0
  let eE := nineLiftCompositum D0
  letI : FiniteDimensional ℚ D0 := D0.finiteDimensional
  letI : IsGalois ℚ D0 := D0.isGalois
  letI : Algebra ℚ E := E.algebra'
  let eE' : D0 ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := eE.toRingEquiv) (by
    intro x
    rfl)
  let hEgal : IsGalois ℚ E := IsGalois.of_algEquiv eE'
  letI : Algebra E D := E.toAlgebra
  letI : IsScalarTower ℚ E D := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal ℚ E := hEgal.to_normal
  change (AlgEquiv.autCongr eE').symm
      (AlgEquiv.restrictNormalHom E
        (AlgEquiv.restrictNormalHom D.toIntermediateField sigma)) =
    AlgEquiv.restrictNormalHom D0.toIntermediateField sigma
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let rhoD := AlgEquiv.restrictNormalHom D.toIntermediateField sigma
  let rhoE := AlgEquiv.restrictNormalHom E rhoD
  have he (y : E) :
      ((eE'.symm y : D0) : AlgebraicClosure ℚ) =
        (((y : E) : D) : AlgebraicClosure ℚ) := by
    have h := eE'.apply_symm_apply y
    exact congrArg
      (fun z : E => (((z : E) : D) : AlgebraicClosure ℚ)) h
  calc
    (((AlgEquiv.autCongr eE').symm rhoE x : D0) : AlgebraicClosure ℚ) =
        ((eE'.symm (rhoE (eE' x)) : D0) : AlgebraicClosure ℚ) := rfl
    _ = (((rhoE (eE' x) : E) : D) : AlgebraicClosure ℚ) :=
      he (rhoE (eE' x))
    _ = ((rhoD ((eE' x : E) : D) : D) : AlgebraicClosure ℚ) := by
      exact congrArg (fun z : D => (z : AlgebraicClosure ℚ))
        (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance D
          inferInstance inferInstance E hEgal.to_normal rhoD (eE' x))
    _ = sigma ((((eE' x : E) : D) : AlgebraicClosure ℚ)) := by
      exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance D
        D.isGalois.to_normal sigma ((eE' x : E) : D)
    _ = sigma (x : AlgebraicClosure ℚ) := by rfl
    _ = ((AlgEquiv.restrictNormalHom D0.toIntermediateField sigma x : D0) :
          AlgebraicClosure ℚ) :=
      (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance D0
        D0.isGalois.to_normal sigma x).symm

/-- Restriction from the common compositum to its conductor-nine cubic
subfield, with the dependent tower instances internalized. -/
noncomputable def rationalNineRestriction
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(nineCorrectionCompositum D0/ℚ) →*
      Gal(nineCubicCompositum D0/ℚ) := by
  let C := nineCubicCompositum D0
  let eC := rationalNineCompositum D0
  letI : Algebra ℚ C := C.algebra'
  let eC' : C ≃ₐ[ℚ] rationalNineCubic :=
    AlgEquiv.ofRingEquiv (f := eC.toRingEquiv) (by
      intro x
      apply Subtype.ext
      have hC : (algebraMap ℚ C) x = (x : C) :=
        DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ C)
          (Rat.castHom C)) x
      have hT : (algebraMap ℚ rationalNineCubic) x =
          (x : rationalNineCubic) :=
        DFunLike.congr_fun (Subsingleton.elim
          (algebraMap ℚ rationalNineCubic)
          (Rat.castHom rationalNineCubic)) x
      rw [hC, hT]
      exact congrArg Subtype.val (map_ratCast eC.toRingEquiv x))
  letI : IsGalois ℚ rationalNineCubic :=
    rational_nine_galois.2.1
  letI : IsGalois ℚ C := IsGalois.of_algEquiv eC'.symm
  exact finiteIntermediateRestriction
    (nineCorrectionCompositum D0) C inferInstance

/-- Restriction from the absolute Galois group to the canonical common
compositum. -/
noncomputable def nineAbsoluteRestriction
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(AlgebraicClosure ℚ/ℚ) →*
      Gal(nineCorrectionCompositum D0/ℚ) := by
  let D := nineCorrectionCompositum D0
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  exact AlgEquiv.restrictNormalHom D.toIntermediateField

private theorem nine_compositum_above
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ P : Ideal (NumberField.RingOfIntegers
        (nineCorrectionCompositum D0)),
      P.IsMaximal ∧ P.LiesOver (Ideal.rationalPrimeIdeal 3) := by
  letI : (Ideal.rationalPrimeIdeal 3).IsMaximal :=
    rational_ideal_maximal Nat.prime_three
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.rationalPrimeIdeal 3)
      (S := NumberField.RingOfIntegers
        (nineCorrectionCompositum D0))

/-- A chosen prime of the common compositum above `3`. -/
noncomputable def rationalNineAbove
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Ideal (NumberField.RingOfIntegers
      (nineCorrectionCompositum D0)) :=
  Classical.choose (nine_compositum_above D0)

theorem rational_nine_above
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    (rationalNineAbove D0).IsPrime :=
  (Classical.choose_spec
    (nine_compositum_above D0)).1.isPrime

theorem nine_above_lies
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    (rationalNineAbove D0).LiesOver
      (Ideal.rationalPrimeIdeal 3) :=
  (Classical.choose_spec
    (nine_compositum_above D0)).2

/-- Pull a finite lift on `D0` back to the canonical conductor-nine
compositum and corestrict its inertia values to the kernel of the projection.
The only input needed for the corestriction is that the projected lift kills
the selected inertia group. -/
noncomputable def rationalNineInertia
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    {E B : Type*} [Group E] [Group B]
    (q : E →* B) (liftFinite : Gal(D0/ℚ) →* E)
    (hbaseInertia : ∀ sigma :
      (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ),
      q (liftFinite
        (nineRestrictionLift D0 sigma.1)) = 1) :
    (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ) →* q.ker where
  toFun sigma := ⟨liftFinite
    (nineRestrictionLift D0 sigma.1), hbaseInertia sigma⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' sigma tau := by
    apply Subtype.ext
    simp

set_option maxHeartbeats 3000000 in
-- The common-compositum and integral-closure structures have a large telescope.
/-- The conductor-nine correction at finite level, together with its absolute
inflation and its ramification control. -/
theorem cancels_nine_compositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    (hAcube : ∀ a : A, a ^ 3 = 1)
    (liftI : (rationalNineAbove D0).inertia
      Gal(nineCorrectionCompositum D0/ℚ) →* A)
    (unitRestriction : RationalPlaceUnits →*
      Gal(nineCubicCompositum D0/ℚ))
    (unitLift : RationalPlaceUnits →* A)
    (hlocalize : ∀ sigma : (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ),
      ∃ u : RationalPlaceUnits,
        unitRestriction u = rationalNineRestriction D0 sigma.1 ∧
        unitLift u = liftI sigma) :
    ∃ chiFinite : Gal(nineCorrectionCompositum D0/ℚ) →* A,
      ∃ chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* A,
        chiAbs = chiFinite.comp (nineAbsoluteRestriction D0) ∧
        Continuous chiAbs ∧
        (∀ sigma : (rationalNineAbove D0).inertia
            Gal(nineCorrectionCompositum D0/ℚ),
          chiFinite sigma.1 * liftI sigma = 1) ∧
        ∀ (q : ℕ) (_hq : Nat.Prime q) (_hq3 : q ≠ 3)
          (P : Ideal (NumberField.RingOfIntegers
            (nineCorrectionCompositum D0)))
          (_hP : P.IsPrime) (_hPover : P.LiesOver (Ideal.rationalPrimeIdeal q))
          (sigma : P.inertia Gal(nineCorrectionCompositum D0/ℚ)),
          chiFinite sigma.1 = 1 := by
  let D := nineCorrectionCompositum D0
  let C := nineCubicCompositum D0
  let eC := rationalNineCompositum D0
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  let eC' : C ≃ₐ[ℚ] rationalNineCubic :=
    AlgEquiv.ofRingEquiv (f := eC.toRingEquiv) (by
      intro x
      apply Subtype.ext
      have hC : (algebraMap ℚ C) x = (x : C) :=
        DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ C)
          (Rat.castHom C)) x
      have hT : (algebraMap ℚ rationalNineCubic) x =
          (x : rationalNineCubic) :=
        DFunLike.congr_fun (Subsingleton.elim
          (algebraMap ℚ rationalNineCubic)
          (Rat.castHom rationalNineCubic)) x
      rw [hC, hT]
      exact congrArg Subtype.val (map_ratCast eC.toRingEquiv x))
  letI : FiniteDimensional ℚ rationalNineCubic := inferInstance
  letI : IsGalois ℚ rationalNineCubic :=
    rational_nine_galois.2.1
  letI : FiniteDimensional ℚ C :=
    Module.Finite.equiv eC'.symm.toLinearEquiv
  letI : IsGalois ℚ C := IsGalois.of_algEquiv eC'.symm
  letI : NumberField C := NumberField.of_module_finite ℚ C
  letI : (rationalNineAbove D0).IsPrime :=
    rational_nine_above D0
  letI : (rationalNineAbove D0).LiesOver
      (Ideal.rationalPrimeIdeal 3) :=
    nine_above_lies D0
  have hcard : Nat.card Gal(C/ℚ) = 3 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact eC'.toLinearEquiv.finrank_eq.trans
      rational_nine_galois.1
  have hram : Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3)
      ((rationalNineAbove D0).under
        (NumberField.RingOfIntegers C)) = 3 := by
    let Q := (rationalNineAbove D0).under
      (NumberField.RingOfIntegers C)
    let eO : NumberField.RingOfIntegers C ≃ₐ[ℤ]
        NumberField.RingOfIntegers rationalNineCubic :=
      (eC'.restrictScalars ℤ).mapIntegralClosure
    let Q9 := Q.map eO
    have hQ9 : Q9 ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal 3)
        (NumberField.RingOfIntegers rationalNineCubic) := by
      letI : Q.IsPrime := inferInstance
      letI : Q.LiesOver (Ideal.rationalPrimeIdeal 3) := inferInstance
      exact ⟨inferInstance, inferInstance⟩
    calc
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3) Q =
          Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3) Q9 := by
        symm
        exact Ideal.ramificationIdx_map_eq
          (p := Ideal.rationalPrimeIdeal 3) (P := Q) eO
      _ = 3 :=
        rational_nine_ramification Q9 hQ9
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_nine
      C inferInstance inferInstance (rationalNineAbove D0)
        hram hcard hAcube liftI unitRestriction unitLift hlocalize
  let chiFinite : Gal(D/ℚ) →* A :=
    chiC.comp (finiteIntermediateRestriction D C inferInstance)
  let chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    absoluteThroughIntermediate D C inferInstance chiC
  refine ⟨chiFinite, chiAbs, rfl,
    absolute_through_continuous D C inferInstance chiC,
    ?_, ?_⟩
  · intro sigma
    exact hcancel sigma
  · intro q hq hq3 P hP hPover sigma
    letI : P.IsPrime := hP
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPover
    have hunramified : RationalPrimeUnramified
        (S := NumberField.RingOfIntegers C) q :=
      rational_unramified_alg eC'.symm
        (rational_nine_away hq hq3)
    change chiC (finiteIntermediateRestriction D C inferInstance sigma.1) = 1
    exact character_restriction_unramified
      C inferInstance inferInstance chiC hq hunramified P sigma

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The canonical correction unfolds the conductor-nine compositum and inertia.
/-- The canonical conductor-nine correction attached to a finite lift.

The finite lift and the vanishing of its projection on the selected inertia
group automa produce the kernel-valued character to be cancelled.
Local class field theory is exposed through just one surjective Artin map from
rational `3`-adic units onto that inertia group. -/
theorem canonical_nine_artin
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    {E B : Type*} [Group E] [Group B]
    [TopologicalSpace E] [DiscreteTopology E]
    (q : E →* B)
    (hcentral : q.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hkernelCube : ∀ z : q.ker, z ^ 3 = 1)
    (hbaseInertia : ∀ sigma :
      (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ),
      q (liftFinite
        (nineRestrictionLift D0 sigma.1)) = 1)
    (unitArtin : RationalPlaceUnits →*
      (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ))
    (hunitArtin : Function.Surjective unitArtin) :
    let liftI := rationalNineInertia
      D0 q liftFinite hbaseInertia
    ∃ chiFinite : Gal(nineCorrectionCompositum D0/ℚ) →* q.ker,
      ∃ chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* q.ker,
        chiAbs = chiFinite.comp (nineAbsoluteRestriction D0) ∧
        Continuous chiAbs ∧
        (∀ sigma : (rationalNineAbove D0).inertia
            Gal(nineCorrectionCompositum D0/ℚ),
          chiFinite sigma.1 * liftI sigma = 1) ∧
        ∀ (p : ℕ) (_hp : Nat.Prime p) (_hp3 : p ≠ 3)
          (P : Ideal (NumberField.RingOfIntegers
            (nineCorrectionCompositum D0)))
          (_hP : P.IsPrime) (_hPover : P.LiesOver (Ideal.rationalPrimeIdeal p))
          (sigma : P.inertia Gal(nineCorrectionCompositum D0/ℚ)),
          chiFinite sigma.1 = 1 := by
  dsimp only
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  let liftI := rationalNineInertia
    D0 q liftFinite hbaseInertia
  let unitRestriction : RationalPlaceUnits →*
      Gal(nineCubicCompositum D0/ℚ) :=
    (rationalNineRestriction D0).comp
        (((rationalNineAbove D0).inertia
          Gal(nineCorrectionCompositum D0/ℚ)).subtype.comp unitArtin)
  let unitLift : RationalPlaceUnits →* q.ker :=
    liftI.comp unitArtin
  apply cancels_nine_compositum
    D0 hkernelCube liftI unitRestriction unitLift
  intro sigma
  obtain ⟨u, hu⟩ := hunitArtin sigma
  refine ⟨u, ?_, ?_⟩
  · change rationalNineRestriction D0 (unitArtin u).1 = _
    rw [hu]
  · change liftI (unitArtin u) = liftI sigma
    rw [hu]

set_option maxHeartbeats 12000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Completion transport and local reciprocity build a very large instance tower.
/-- The canonical conductor-nine correction.  Local reciprocity at the
rational `3`-adic completion, completion/decomposition transport, the
spectral integral model, and the kernel corestriction are internal. -/
theorem canonical_nine_reciprocity
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    {E B : Type*} [Group E] [Group B]
    [TopologicalSpace E] [DiscreteTopology E]
    (q : E →* B)
    (hcentral : q.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hkernelCube : ∀ z : q.ker, z ^ 3 = 1)
    (hbaseInertia : ∀ sigma :
      (rationalNineAbove D0).inertia
        Gal(nineCorrectionCompositum D0/ℚ),
      q (liftFinite
        (nineRestrictionLift D0 sigma.1)) = 1) :
    let liftI := rationalNineInertia
      D0 q liftFinite hbaseInertia
    ∃ chiFinite : Gal(nineCorrectionCompositum D0/ℚ) →* q.ker,
      ∃ chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* q.ker,
        chiAbs = chiFinite.comp (nineAbsoluteRestriction D0) ∧
        Continuous chiAbs ∧
        (∀ sigma : (rationalNineAbove D0).inertia
            Gal(nineCorrectionCompositum D0/ℚ),
          chiFinite sigma.1 * liftI sigma = 1) ∧
        ∀ (p : ℕ) (_hp : Nat.Prime p) (_hp3 : p ≠ 3)
          (P : Ideal (NumberField.RingOfIntegers
            (nineCorrectionCompositum D0)))
          (_hP : P.IsPrime) (_hPover : P.LiesOver (Ideal.rationalPrimeIdeal p))
          (sigma : P.inertia Gal(nineCorrectionCompositum D0/ℚ)),
          chiFinite sigma.1 = 1 := by
  dsimp only
  letI : CommGroup q.ker := centralExtensionComm q hcentral
  let D := nineCorrectionCompositum D0
  let Pselected := rationalNineAbove D0
  let P3 := rationalThreePlace
  let v := (FinitePlace.mk P3).val
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : NumberField D := NumberField.of_module_finite ℚ D
  letI : MulSemiringAction Gal(D/ℚ) (NumberField.RingOfIntegers D) :=
    NumberField.RingOfIntegers.instMulSemiringAction D
  letI : Pselected.IsPrime := rational_nine_above D0
  letI : Pselected.LiesOver (Ideal.rationalPrimeIdeal 3) :=
    nine_above_lies D0
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P3⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P3
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P3
  letI : ValuativeRel v.Completion := placeValuativeRel P3
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P3
  letI : Algebra ℚ v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap ℚ v.Completion).injective).mp
      inferInstance
  have hrec : LocalReciprocityLaw v.Completion :=
    Submission.CField.LExist.reciprocity_law_assembled
      v.Completion
  let Places :=
    Submission.CField.ICohomo.CompletionPlacesAbove
      (L := D) v
  letI : Finite Places := absolute_extensions_separable v
  letI : Nonempty Places :=
    absolute_value_extension (K := ℚ) (L := D) v
  letI : MulAction.IsPretransitive Gal(D/ℚ) Places :=
    completion_above_pretransitive P3
  let w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := D) v := Classical.choice (inferInstance : Nonempty Places)
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Q.asIdeal.IsPrime := Q.isPrime
  letI : Q.asIdeal.LiesOver P3.asIdeal :=
    nonarchimedean_spectrum_lies P3 w.1 w.2 hw hwna
  letI : P3.asIdeal.LiesOver (Ideal.rationalPrimeIdeal 3) :=
    rational_lies_ideal
  letI : Q.asIdeal.LiesOver (Ideal.rationalPrimeIdeal 3) :=
    Ideal.LiesOver.trans Q.asIdeal P3.asIdeal (Ideal.rationalPrimeIdeal 3)
  let globalLift : Gal(D/ℚ) →* E :=
    liftFinite.comp (nineRestrictionLift D0)
  let globalBase : Gal(D/ℚ) →* B := q.comp globalLift
  have hbaseQ : ∀ sigma : Q.asIdeal.inertia Gal(D/ℚ),
      globalBase sigma.1 = 1 := by
    intro sigma
    exact number_all_inertia
      D globalBase (q := 3) Pselected hbaseInertia Q.asIdeal sigma
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let Acomp := completionIntegerRing v
  let Bcomp := completionIntegerRing w.1
  letI : Algebra Acomp v.Completion := Acomp.subtype.toAlgebra
  letI : Algebra Acomp Bcomp :=
    completionIntegerLies v w.1 w.2
  letI : Algebra Bcomp w.1.Completion := Bcomp.subtype.toAlgebra
  letI : Algebra Acomp w.1.Completion :=
    ((completionLies v w.1 w.2).comp Acomp.subtype).toAlgebra
  letI : IsScalarTower Acomp Bcomp w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Acomp v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Acomp v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure Bcomp Acomp w.1.Completion :=
    completion_integer_closure v w.1 w.2
      (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
  letI : MulSemiringAction Gal(w.1.Completion/v.Completion) Bcomp :=
    IsIntegralClosure.MulSemiringAction
      Acomp v.Completion w.1.Completion Bcomp
  let eD := decompositionCompletionExtension v w.1
  let toGlobal : Gal(w.1.Completion/v.Completion) →* Gal(D/ℚ) :=
    (absoluteValueDecomposition v w.1).subtype.comp
      eD.symm.toMonoidHom
  let Icomp := (IsLocalRing.maximalIdeal Bcomp).inertia
    Gal(w.1.Completion/v.Completion)
  let globalIntegralAction :
      MulSemiringAction Gal(D/ℚ) (NumberField.RingOfIntegers D) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers ℚ) ℚ D
        (NumberField.RingOfIntegers D)
  have hglobalSmul (g : Gal(D/ℚ))
      (x : NumberField.RingOfIntegers D) :
      @SMul.smul _ _ globalIntegralAction.toSMul g x =
        @SMul.smul _ _
          (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
            g x := by
    apply NumberField.RingOfIntegers.ext
    have hleft :
        ((@SMul.smul _ _ globalIntegralAction.toSMul g x :
            NumberField.RingOfIntegers D) : D) = g (x : D) := by
      exact algebraMap_galRestrictHom_apply
        (NumberField.RingOfIntegers ℚ) ℚ D
          (NumberField.RingOfIntegers D) g x
    have hright :
        ((@SMul.smul _ _
          (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
            g x : NumberField.RingOfIntegers D) : D) = g (x : D) := by
      change _ = g • (x : D)
      exact integralClosure.coe_smul g x
    exact hleft.trans hright.symm
  have hdecomp (tau : Gal(w.1.Completion/v.Completion)) :
      tau ∈ Icomp ↔ toGlobal tau ∈ Q.asIdeal.inertia Gal(D/ℚ) := by
    let sigmaD := eD.symm tau
    have h := decomposition_completion_inertia
      v (fun x y => (FinitePlace.mk P3).add_le x y)
        w sigmaD
    have he : eD sigmaD = tau := eD.apply_symm_apply tau
    have hg : toGlobal tau = sigmaD.1 := rfl
    constructor
    · intro htau
      have hsigma := h.mpr (by
        rw [he]
        change tau ∈ Icomp
        exact htau)
      rw [hg]
      intro x
      have hx := hsigma x
      change (@SMul.smul _ _ globalIntegralAction.toSMul
        sigmaD.1 x - x) ∈ Q.asIdeal at hx
      rw [Submodule.mem_toAddSubgroup]
      have heq :
          @SMul.smul _ _ globalIntegralAction.toSMul sigmaD.1 x - x =
            @SMul.smul _ _
              (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
                sigmaD.1 x - x :=
        congrArg (fun y ↦ y - x) (hglobalSmul sigmaD.1 x)
      exact heq ▸ hx
    · intro hsigma
      have hsigmaOld : sigmaD.1 ∈
          (nonarchimedeanHeightSpectrum w.1 hw hwna).asIdeal.inertia
            Gal(D/ℚ) := by
        intro x
        have hx0 := hsigma x
        rw [hg] at hx0
        change (@SMul.smul _ _ globalIntegralAction.toSMul
          sigmaD.1 x - x) ∈ Q.asIdeal.toAddSubgroup
        rw [Submodule.mem_toAddSubgroup]
        rw [Submodule.mem_toAddSubgroup] at hx0
        have heq :
            @SMul.smul _ _ globalIntegralAction.toSMul sigmaD.1 x - x =
              @SMul.smul _ _
                (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
                  sigmaD.1 x - x :=
          congrArg (fun y ↦ y - x) (hglobalSmul sigmaD.1 x)
        exact heq.symm ▸ hx0
      have htau := h.mp hsigmaOld
      rw [← he]
      change eD sigmaD ∈ Icomp
      exact htau
  let C := nineCubicCompositum D0
  letI : Algebra ℚ C := C.algebra'
  let eC : C ≃ₐ[ℚ] rationalNineCubic :=
    rationalNineCompositum D0
  letI : IsCyclic Gal(rationalNineCubic/ℚ) :=
    rational_nine_galois.2.2
  letI : IsMulCommutative Gal(rationalNineCubic/ℚ) :=
    IsCyclic.isMulCommutative
  letI : CommGroup Gal(rationalNineCubic/ℚ) :=
    { (inferInstance : Group Gal(rationalNineCubic/ℚ)) with
      mul_comm := mul_comm' }
  let eAut : Gal(C/ℚ) ≃* Gal(rationalNineCubic/ℚ) :=
    AlgEquiv.autCongr eC
  letI : IsMulCommutative Gal(C/ℚ) := by
    refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
    apply eAut.injective
    simpa only [map_mul] using mul_comm (eAut sigma) (eAut tau)
  letI : CommGroup Gal(C/ℚ) :=
    { (inferInstance : Group Gal(C/ℚ)) with
      mul_comm := mul_comm' }
  let localRestriction : Gal(w.1.Completion/v.Completion) →*
      Gal(nineCubicCompositum D0/ℚ) :=
    (rationalNineRestriction D0).comp toGlobal
  let localLift : Gal(w.1.Completion/v.Completion) →* E :=
    globalLift.comp toGlobal
  have hkillComp : ∀ i : Icomp, q (localLift i.1) = 1 := by
    intro i
    have hi := (hdecomp i.1).mp i.2
    have hb := hbaseQ ⟨toGlobal i.1, by
      intro x
      have hx := hi x
      change (@SMul.smul _ _ globalIntegralAction.toSMul
        (toGlobal i.1) x - x) ∈ Q.asIdeal at hx
      change (@SMul.smul _ _
        (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
          (toGlobal i.1) x - x) ∈ Q.asIdeal.toAddSubgroup
      rw [Submodule.mem_toAddSubgroup]
      have heq :
          @SMul.smul _ _ globalIntegralAction.toSMul
                (toGlobal i.1) x - x =
            @SMul.smul _ _
              (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
                (toGlobal i.1) x - x :=
        congrArg (fun y ↦ y - x) (hglobalSmul (toGlobal i.1) x)
      exact heq ▸ hx⟩
    change q (globalLift (toGlobal i.1)) = 1
    exact hb
  have hcenterComp : ∀ i : Icomp,
      localLift i.1 ∈ Subgroup.center E := by
    intro i
    apply hcentral
    exact hkillComp i
  let AKnorm :=
    Valuation.integer (NormedField.valuation (K := v.Completion))
  letI : Algebra AKnorm Bcomp :=
    completionIntegerLies v w.1 w.2
  letI : IsScalarTower AKnorm Bcomp w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure Bcomp AKnorm w.1.Completion :=
    completion_integer_closure v w.1 w.2
      (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
  obtain ⟨unitRestriction, unitLift, hparam⟩ :=
    joint_parametrization_model
      (R := Gal(nineCubicCompositum D0/ℚ))
      (A := E) (B := B)
      v.Completion hrec w.1.Completion Bcomp
        localRestriction localLift q
        (IsScalarTower.of_algebraMap_eq' rfl)
        (completion_integer_closure v w.1 w.2
          (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion))
        (by
          intro tau x
          exact algebraMap_galRestrictHom_apply
            Acomp v.Completion w.1.Completion Bcomp tau x)
        hkillComp hcenterComp
  apply cancels_nine_compositum
    D0 hkernelCube
      (rationalNineInertia D0 q liftFinite hbaseInertia)
      unitRestriction unitLift
  intro sigma
  letI : IsGaloisGroup Gal(D/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers D) :=
    IsGaloisGroup.of_isFractionRing Gal(D/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers D) ℚ D
  have hPselectedOverP3 : Pselected.LiesOver P3.asIdeal := by
    rw [Ideal.liesOver_iff]
    let e0 : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
      Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
    have halg : algebraMap ℤ (NumberField.RingOfIntegers ℚ) =
        e0.symm.toRingHom := Subsingleton.elim _ _
    have hsurj : Function.Surjective
        (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) := by
      rw [halg]
      exact e0.symm.surjective
    apply Ideal.comap_injective_of_surjective _ hsurj
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers D)]
    have hPunder := (show Pselected.LiesOver
      (Ideal.rationalPrimeIdeal 3) from inferInstance).over
    have hP3under :=
      (show P3.asIdeal.LiesOver (Ideal.rationalPrimeIdeal 3) from inferInstance).over
    exact hP3under.symm.trans hPunder
  letI : Pselected.LiesOver P3.asIdeal := hPselectedOverP3
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    P3.asIdeal Q.asIdeal Pselected Gal(D/ℚ)
  have hsigmaQ : g⁻¹ * sigma.1 * g ∈ Q.asIdeal.inertia Gal(D/ℚ) := by
    apply inertia_conj_mem Q.asIdeal g sigma.1
    rw [hg]
    intro x
    have hx0 := sigma.property x
    change (@SMul.smul _ _ globalIntegralAction.toSMul
      sigma.1 x - x) ∈ Pselected.toAddSubgroup
    rw [Submodule.mem_toAddSubgroup]
    rw [Submodule.mem_toAddSubgroup] at hx0
    have heq :
        @SMul.smul _ _ globalIntegralAction.toSMul sigma.1 x - x =
          @SMul.smul _ _
            (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
              sigma.1 x - x :=
      congrArg (fun y ↦ y - x) (hglobalSmul sigma.1 x)
    exact heq.symm ▸ hx0
  let tauQ : Q.asIdeal.inertia Gal(D/ℚ) :=
    ⟨g⁻¹ * sigma.1 * g, hsigmaQ⟩
  let tauD : absoluteValueDecomposition v w.1 :=
    ⟨tauQ.1, by
      rw [absolute_decomposition_stabilizer]
      apply absolute_stabilizer_centered
        w.1 hw hwna tauQ.1
      apply Ideal.inertia_le_stabilizer Q.asIdeal
      intro x
      have hx0 := tauQ.property x
      change (@SMul.smul _ _ globalIntegralAction.toSMul
        tauQ.1 x - x) ∈ Q.asIdeal.toAddSubgroup
      rw [Submodule.mem_toAddSubgroup]
      rw [Submodule.mem_toAddSubgroup] at hx0
      have heq :
          @SMul.smul _ _ globalIntegralAction.toSMul tauQ.1 x - x =
            @SMul.smul _ _
              (NumberField.RingOfIntegers.instMulSemiringAction D).toSMul
                tauQ.1 x - x :=
        congrArg (fun y ↦ y - x) (hglobalSmul tauQ.1 x)
      exact heq.symm ▸ hx0⟩
  let tauLocal : Gal(w.1.Completion/v.Completion) := eD tauD
  have htauLocalGlobal : toGlobal tauLocal = tauQ.1 := by
    simp [toGlobal, tauLocal, tauD]
  have htauComp : tauLocal ∈ Icomp :=
    (hdecomp tauLocal).mpr (by simp [htauLocalGlobal, tauQ.2])
  obtain ⟨unit, hunitRestriction, hunitLift⟩ :=
    hparam ⟨tauLocal, htauComp⟩
  refine ⟨unit, ?_, ?_⟩
  · calc
      unitRestriction unit = localRestriction tauLocal := hunitRestriction
      _ = rationalNineRestriction D0 (toGlobal tauLocal) := rfl
      _ = rationalNineRestriction D0 tauQ.1 :=
        congrArg (rationalNineRestriction D0) htauLocalGlobal
      _ = rationalNineRestriction D0 sigma.1 := by
        dsimp only [tauQ]
        simp only [map_mul, map_inv]
        have hc :
            ((rationalNineRestriction D0) g)⁻¹ *
                (rationalNineRestriction D0) sigma.1 =
              (rationalNineRestriction D0) sigma.1 *
                ((rationalNineRestriction D0) g)⁻¹ := by
          exact (show IsMulCommutative Gal(C/ℚ) from inferInstance).is_comm.comm
            _ _
        rw [hc, mul_assoc, inv_mul_cancel, mul_one]
  · apply Subtype.ext
    calc
      (unitLift unit : E) = localLift tauLocal := hunitLift
      _ = globalLift (toGlobal tauLocal) := rfl
      _ = globalLift tauQ.1 := congrArg globalLift htauLocalGlobal
      _ = liftFinite
          (nineRestrictionLift D0 sigma.1) := by
        dsimp only [tauQ, globalLift]
        simp only [map_mul, map_inv]
        have hsigmaCentral : liftFinite
            (nineRestrictionLift D0 sigma.1) ∈
              Subgroup.center E := hcentral (hbaseInertia sigma)
        calc
          (globalLift g)⁻¹ * liftFinite
                (nineRestrictionLift D0 sigma.1) *
              globalLift g =
            liftFinite (nineRestrictionLift D0 sigma.1) *
                (globalLift g)⁻¹ * globalLift g := by
              rw [Subgroup.mem_center_iff.mp hsigmaCentral
                (globalLift g)⁻¹]
          _ = liftFinite
                (nineRestrictionLift D0 sigma.1) := by
              simp only [mul_assoc, inv_mul_cancel, mul_one]

end TBluepr
end Submission
