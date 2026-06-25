import Towers.ClassField.HasseNorm.FiniteStageDecomposition
import Towers.ClassField.HasseNorm.UnramifiedLocal
import Towers.ClassField.HasseNorm.LiftedH2
import Towers.NumberTheory.Ramification.RamificationDiscriminant
import Towers.NumberTheory.Locals.UnramifiedExtensions

/-!
# Cohomology of the finite-place idèle stages

This file applies the arbitrary-product form of Proposition II.1.25 to the
finite-place product constructed in `HasseNormFiniteStageDecomposition`.
It keeps the pointwise product representation used by the idèle action and
the categorical product required by the proposition connected by an
explicit representation isomorphism.
-/

namespace Towers.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.COps
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The resized representation on the pointwise product of all finite
base-prime orbits in the stage `I_{L,S}`. -/
noncomputable def resizedStageRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := ideleStageAction (K := K) (L := L) S
  exact uliftMulRepresentation
    (G := Gal(L/K))
    (M := ∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      IdeleStageOrbit (K := K) (L := L) S P)

private abbrev stageOrbitFamily
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  stageOrbitRepresentation (K := K) (L := L) S P

/-- Galois conjugation is transitive on the literal upper primes over a
fixed finite base prime. -/
noncomputable instance primesAbovePretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    letI := aboveMulAction (K := K) (L := L) P
    MulAction.IsPretransitive Gal(L/K)
      (FinitePrimesAbove (K := K) (L := L) P) := by
  let R := NumberField.RingOfIntegers K
  let T := NumberField.RingOfIntegers L
  letI : MulSemiringAction Gal(L/K) T :=
    IsIntegralClosure.MulSemiringAction R K L T
  letI : IsGaloisGroup Gal(L/K) R T :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) R T K L
  letI : Algebra.IsInvariant R T Gal(L/K) := inferInstance
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  constructor
  intro Q Q'
  have hunder : Q.1.asIdeal.under R = Q'.1.asIdeal.under R := by
    rw [show Q.1.asIdeal.under R = P.asIdeal from
      congrArg HeightOneSpectrum.asIdeal Q.2,
      show Q'.1.asIdeal.under R = P.asIdeal from
        congrArg HeightOneSpectrum.asIdeal Q'.2]
  obtain ⟨sigma, hsigma⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq
      R T Gal(L/K) Q.1.asIdeal Q'.1.asIdeal hunder
  refine ⟨sigma, Subtype.ext ?_⟩
  apply HeightOneSpectrum.ext
  change (sigma • Q.1).asIdeal = Q'.1.asIdeal
  rw [prime_action_ideal]
  exact hsigma.symm

/-- The local-unit subgroup used in the finite idèles is the unit group of
the corresponding prime-adic valuation ring. -/
noncomputable def adicIntegersUnits
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q ≃*
      (Q.adicCompletionIntegers L)ˣ :=
  (Q.adicCompletionIntegers L).unitsEquivUnitsType

set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the categorical product representation and its pointwise action
-- requires a deeper instance search.
set_option maxHeartbeats 1000000 in
/-- Evaluation from the categorical product of orbit representations to
the concrete pointwise product representation. -/
noncomputable def categoricalStagePointwise
    (S : Finset (NumberFieldPlace K)) :
    (∏ᶜ fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        stageOrbitFamily (K := K) (L := L) S P) ⟶
      resizedStageRepresentation (K := K) (L := L) S := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
    stageOrbitFamily (K := K) (L := L) S P
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x P => (Pi.π A P).hom x
          map_add' := fun x y => by
            funext P
            exact (Pi.π A P).hom.map_add x y
          map_smul' := fun r x => by
            funext P
            exact (Pi.π A P).hom.map_smul r x }
      isIntertwining' := fun sigma => by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        funext P
        exact congrArg Additive.toMul
          (Rep.hom_comm_apply (Pi.π A P) sigma x) }

set_option synthInstance.maxHeartbeats 300000 in
-- The inverse built from the concrete product equivalence generates deeply
-- nested categorical module instances.
omit [FiniteDimensional K L] in
/-- The evaluation map from the categorical product to the pointwise
product is bijective on carriers. -/
theorem categorical_stage_bijective
    (S : Finset (NumberFieldPlace K)) :
    Function.Bijective
      (categoricalStagePointwise
        (K := K) (L := L) S) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
    stageOrbitFamily (K := K) (L := L) S P
  letI : PreservesLimit (Discrete.functor A)
      (forget (Rep (ULift.{u} ℤ) Gal(L/K))) := by
    change PreservesLimit (Discrete.functor A)
      (forget₂ (Rep (ULift.{u} ℤ) Gal(L/K))
        (ModuleCat (ULift.{u} ℤ)) ⋙ forget (ModuleCat (ULift.{u} ℤ)))
    infer_instance
  constructor
  · intro x y hxy
    apply (Concrete.productEquiv A).injective
    funext P
    rw [Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    exact congrFun hxy P
  · intro y
    let x := (Concrete.productEquiv A).symm y
    refine ⟨x, ?_⟩
    funext P
    change (Pi.π A P).hom ((Concrete.productEquiv A).symm y) = y P
    exact Concrete.productEquiv_symm_apply_π A y P

set_option synthInstance.maxHeartbeats 300000 in
-- Packaging the pointwise product equivalence as a representation isomorphism
-- requires elaborating the full dependent product instance.
/-- The concrete pointwise finite-stage representation is the categorical
product of its orbit representations. -/
noncomputable def stageIsoCategorical
    (S : Finset (NumberFieldPlace K)) :
    resizedStageRepresentation (K := K) (L := L) S ≅
      (∏ᶜ fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        stageOrbitFamily (K := K) (L := L) S P) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  exact (Rep.mkIso
      ((categoricalStagePointwise
        (K := K) (L := L) S).hom.ofBijective
          (categorical_stage_bijective
            (K := K) (L := L) S))).symm

/-- The carrier of a categorical product of modules, additively identified
with the corresponding dependent function type. -/
noncomputable def moduleCatPi
    {k : Type u} [CommRing k] {I : Type u}
    (A : I → ModuleCat.{u} k) :
    (∏ᶜ A : ModuleCat.{u} k) ≃+ (∀ i, A i) :=
  { toEquiv := Concrete.productEquiv A
    map_add' := fun x y => by
      funext i
      calc
        (Concrete.productEquiv A).toFun (x + y) i =
            (Pi.π A i).hom (x + y) :=
          Concrete.productEquiv_apply_apply A (x + y) i
        _ = (Pi.π A i).hom x + (Pi.π A i).hom y :=
          (Pi.π A i).hom.map_add x y
        _ = ((Concrete.productEquiv A).toFun x +
            (Concrete.productEquiv A).toFun y) i := by
          rw [Pi.add_apply]
          exact congrArg₂ (· + ·)
            (Concrete.productEquiv_apply_apply A x i).symm
            (Concrete.productEquiv_apply_apply A y i).symm }

set_option synthInstance.maxHeartbeats 400000 in
-- Applying cohomology to the categorical product isomorphism requires a large
-- dependent product of module and representation instances.
/-- Proposition II.1.25 applied to the concrete product of all finite stage
orbits. -/
noncomputable def ideleStagePi
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H2 (stageOrbitRepresentation
          (K := K) (L := L) S P)) := by
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
    stageOrbitFamily (K := K) (L := L) S P
  let e₁ := ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (stageIsoCategorical
      (K := K) (L := L) S)).toLinearEquiv.toAddEquiv
  let e₂ := (groupProductIso
    (ULift.{u} ℤ) Gal(L/K) A 2).toLinearEquiv.toAddEquiv
  let e₃ := moduleCatPi (fun P => H2 (A P))
  exact e₁.trans (e₂.trans e₃)

/-- At an exceptional finite base prime, its degree-two stage factor is the
degree-two cohomology of the unrestricted completion orbit. -/
noncomputable def ideleStageFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    H2 (stageOrbitRepresentation
      (K := K) (L := L) S P) ≃+
      H2 (resizedAboveRepresentation
        (K := K) (L := L) P) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (stageIsoFull
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

/-- At a nonexceptional finite base prime, its degree-two stage factor is
the cohomology of the product of upper local-unit groups. -/
noncomputable def resizedIdeleStage
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    H2 (stageOrbitRepresentation
      (K := K) (L := L) S P) ≃+
      H2 (resizedPrimesRepresentation
        (K := K) (L := L) P) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedStageIso
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

omit [FiniteDimensional K L] [IsGalois K L] in
/-- There is a finite idèle stage containing every ramified finite base
prime.  Consequently every upper completion orbit outside that stage is
unramified. -/
theorem stage_unramified_outside :
    ∃ S : Finset (NumberFieldPlace K),
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
              (upperPrime (K := K) (L := L) P Q).asIdeal := by
  let R := NumberField.RingOfIntegers K
  let T := NumberField.RingOfIntegers L
  let ramifiedIdeals : Set (Ideal R) :=
    {p | ∃ Q : Ideal T, Ideal.IsPrime Q ∧ Q ≠ ⊥ ∧
      Q.under R = p ∧ Ideal.ramificationIdx p Q ≠ 1}
  have hramifiedIdeals : ramifiedIdeals.Finite := by
    exact ramified_base_primes R T
  let ramifiedPrimes : Set (HeightOneSpectrum R) :=
    {P | P.asIdeal ∈ ramifiedIdeals}
  have hprimeInjective : Function.Injective
      (fun P : HeightOneSpectrum R => P.asIdeal) := by
    intro P Q hPQ
    exact HeightOneSpectrum.ext_iff.mpr hPQ
  have hramifiedPrimes : ramifiedPrimes.Finite :=
    Set.Finite.preimage hprimeInjective.injOn hramifiedIdeals
  let ramifiedPlaces : Set (NumberFieldPlace K) :=
    Sum.inl '' ramifiedPrimes
  have hramifiedPlaces : ramifiedPlaces.Finite :=
    hramifiedPrimes.image Sum.inl
  refine ⟨hramifiedPlaces.toFinset, ?_⟩
  intro P hP Q
  let q := upperPrime (K := K) (L := L) P Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q)).symm
  apply (unramified_ramification_idx
    P.asIdeal q.asIdeal q.ne_bot).2
  by_contra hramificationIdx
  apply hP
  rw [Set.Finite.mem_toFinset]
  exact ⟨P, ⟨q.asIdeal, q.isPrime, q.ne_bot,
    congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q),
    hramificationIdx⟩, rfl⟩

end

end Towers.CField.HNorm
