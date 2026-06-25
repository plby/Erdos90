import Submission.ClassField.HasseNorm.FiniteRestrictedShapiro
import Submission.ClassField.HasseNorm.UnramifiedLocal
import Submission.ClassField.HasseNorm.LiftedH2
import Submission.ClassField.HasseNorm.LocalStabilizerComparison
import Submission.ClassField.HasseNorm.FinitePlaceBridge

/-!
# Unramified finite-place local-unit cohomology

At an unramified finite prime, the decomposition group is cyclic and the
norm on completed valuation-ring units is onto.  Restricted Shapiro then
identifies the degree-two cohomology of all upper local-unit factors with
that of one chosen factor, which therefore vanishes.
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.COps
open Submission.CField.UCohom
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

attribute [local instance] Units.mulDistribMulActionRight

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance unramifiedH2FinitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance unramifiedH2FinitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance unramifiedH2FiniteCompletionPlacesAboveFinite
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  absolute_extensions_separable (FinitePlace.mk P).val

local instance unramifiedH2FiniteCompletionPlacesAboveNonempty
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  absolute_value_extension
    (K := K) (L := L) (FinitePlace.mk P).val

local instance unramifiedH2CompletionPlacesAbovePretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

local instance unramifiedH2CompletionPlaceLiesOverFact
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩

local instance unramifiedH2FinitePlaceCompletionNontriviallyNormed
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NontriviallyNormedField (FinitePlace.mk P).val.Completion :=
  placeNontriviallyNormed P

local instance unramifiedH2CompletionPlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Fact w.1.IsNontrivial :=
  ⟨absolute_extension_nontrivial (FinitePlace.mk P).val w⟩

local instance unramifiedH2CompletionPlaceUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    IsUltrametricDist w.1.Completion :=
  absoluteUltrametricDist w.1
    (absolute_extension_nonarchimedean (FinitePlace.mk P).val w)

omit [FiniteDimensional K L] in
/-- The stabilizer of an upper prime in the literal fiber is the usual
ideal decomposition group. -/
theorem above_stabilizer_ideal
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    letI : MulSemiringAction Gal(L/K)
        (NumberField.RingOfIntegers L) :=
      IsIntegralClosure.MulSemiringAction
        (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)
    letI : MulSemiringAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      Ideal.pointwiseMulSemiringAction
    primeAboveStabilizer (K := K) (L := L) P Q =
      MulAction.stabilizer Gal(L/K) Q.1.asIdeal := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  ext sigma
  simp only [primeAboveStabilizer, MulAction.mem_stabilizer_iff]
  constructor
  · intro hsigma
    have hval := congrArg
      (fun R : FinitePrimesAbove (K := K) (L := L) P => R.1.asIdeal)
      hsigma
    change (sigma • Q.1).asIdeal = Q.1.asIdeal at hval
    rwa [prime_action_ideal] at hval
  · intro hsigma
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    change (sigma • Q.1).asIdeal = Q.1.asIdeal
    rw [prime_action_ideal]
    exact hsigma

/-- An unramified chosen upper prime has a cyclic literal-fiber
stabilizer. -/
theorem above_stabilizer_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    IsCyclic (primeAboveStabilizer (K := K) (L := L) P Q) := by
  letI : MulSemiringAction Gal(L/K)
      (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  letI : MulSemiringAction Gal(L/K)
      (Ideal (NumberField.RingOfIntegers L)) :=
    Ideal.pointwiseMulSemiringAction
  letI : Q.1.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal Q.2).symm
  rw [above_stabilizer_ideal
    (K := K) (L := L) P Q]
  exact decomposition_cyclic_unramified P Q.1 hQ

/-- The normalized absolute-value completion place centered at a literal
upper prime. -/
noncomputable def aboveCompletionPlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
  (placesAboveFactors
      (K := K) (L := L) P).symm
    ((upperPrimesAbove
      (K := K) (L := L) P).symm Q)

/-- The chosen normalized completion place is centered at the prescribed
literal upper prime. -/
theorem above_place_center
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) = Q.1 := by
  dsimp only [aboveCompletionPlace]
  have hw := (placesAboveFactors
    (K := K) (L := L) P).apply_symm_apply
      ((upperPrimesAbove
        (K := K) (L := L) P).symm Q)
  rw [show placeUpperFactor
      (K := K) (L := L) P
        ((placesAboveFactors
          (K := K) (L := L) P).symm
            ((upperPrimesAbove
              (K := K) (L := L) P).symm Q)) =
      (upperPrimesAbove
        (K := K) (L := L) P).symm Q from hw]
  exact congrArg Subtype.val
    ((upperPrimesAbove
      (K := K) (L := L) P).apply_symm_apply Q)

/-- The upper prime factor attached to a completion place is its centered
literal height-one prime. -/
theorem upper_place_factor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) =
      (completionPlaceAbove
        (K := K) (L := L) P w).1 := by
  have h := (upperPrimesAbove
    (K := K) (L := L) P).apply_symm_apply
      (completionPlaceAbove (K := K) (L := L) P w)
  exact congrArg Subtype.val h

/-- The upper prime factor attached to a completion place is equivariant
under Galois conjugation. -/
theorem upper_place_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P (sigma • w)) =
      sigma • upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) := by
  letI := finitePrimeAction (K := K) (L := L)
  calc
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P (sigma • w)) =
        (completionPlaceAbove
          (K := K) (L := L) P (sigma • w)).1 :=
      upper_place_factor
        (K := K) (L := L) P (sigma • w)
    _ = sigma • (completionPlaceAbove
          (K := K) (L := L) P w).1 :=
      place_above_smul
        (K := K) (L := L) P sigma w
    _ = sigma • upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) := by
      rw [upper_place_factor]

private theorem adic_embedding_transport
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') (x : L) :
    RingEquiv.cast (R := fun R => R.adicCompletion L) h
        (FinitePlace.embedding Q x) =
      FinitePlace.embedding Q' x := by
  subst Q'
  rfl

private theorem continuous_cast_transport
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun R => R.adicCompletion L) h) := by
  subst Q'
  exact continuous_id

private theorem continuous_adic_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Continuous (placeCompletionAdic P) := by
  let h := completion_universal (FinitePlace.mk P).val
    (FinitePlace.embedding P) (by
      intro x
      exact (FinitePlace.mk_apply P x).symm)
  change Continuous h.choose
  exact h.choose_spec.1.1.continuous

/-- The Chapter 8 completion/adic comparison is continuous. -/
theorem place_adic_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (completionPlaceAdic
      (K := K) (L := L) P w) := by
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q :=
    (upper_place_factor
      (K := K) (L := L) P w).symm
  unfold completionPlaceAdic
  exact (continuous_cast_transport hq).comp
    ((continuous_adic_transport q).comp
      (continuous_ring_equiv
        (place_centered_prime w.1 hw hwna)))

/-- The literal upper-prime stabilizer is the stabilizer of its normalized
completion-place model. -/
theorem above_stabilizer_place
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    primeAboveStabilizer (K := K) (L := L) P Q =
      CompletionPlaceStabilizer (FinitePlace.mk P).val
        (aboveCompletionPlace (K := K) (L := L) P Q) := by
  letI := aboveMulAction (K := K) (L := L) P
  let e := (placesAboveFactors
      (K := K) (L := L) P).trans
    (upperPrimesAbove (K := K) (L := L) P)
  have eeq
      (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
      e w = completionPlaceAbove
        (K := K) (L := L) P w := by
    change (upperPrimesAbove
        (K := K) (L := L) P)
      ((upperPrimesAbove
        (K := K) (L := L) P).symm
          (completionPlaceAbove
            (K := K) (L := L) P w)) = _
    exact (upperPrimesAbove
      (K := K) (L := L) P).apply_symm_apply _
  have heq (sigma : Gal(L/K))
      (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
      e (sigma • w) = sigma • e w :=
    (eeq (sigma • w)).trans <| (Subtype.ext
      (place_above_smul
        (K := K) (L := L) P sigma w)).trans <|
      congrArg (fun R => sigma • R) (eeq w).symm
  have ew : e (aboveCompletionPlace
      (K := K) (L := L) P Q) = Q := by
    change e (e.symm Q) = Q
    exact e.apply_symm_apply Q
  ext sigma
  simp only [primeAboveStabilizer, CompletionPlaceStabilizer,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro hsigma
    apply e.injective
    rw [heq, ew, hsigma]
  · intro hsigma
    have h := congrArg e hsigma
    rw [heq, ew] at h
    exact h

set_option maxHeartbeats 1000000 in
-- Comparing the two completion actions expands their dependent transport
-- maps on a dense set of global elements.
set_option maxRecDepth 5000 in
/-- On the chosen stabilized completion, the absolute-completion action and
the prime-adic action agree.  This specialized form avoids the dependent
change of completion place needed by the unrestricted transport statement. -/
theorem stabilizer_adic_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (sigma : primeAboveStabilizer (K := K) (L := L) P Q)
    (z : let w := aboveCompletionPlace (K := K) (L := L) P Q
      w.1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let targetQ := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let sigma' : CompletionPlaceStabilizer v w :=
      MulEquiv.subgroupCongr
        (above_stabilizer_place
          (K := K) (L := L) P Q) sigma
    let hcenter : targetQ = Q.1 :=
      above_place_center (K := K) (L := L) P Q
    let hfix : sigma.1⁻¹ • Q = Q := (sigma⁻¹).2
    let hQ : Q.1 = sigma.1⁻¹ • Q.1 :=
      (congrArg Subtype.val hfix).symm
    RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L)
        hcenter
        (completionPlaceAdic (K := K) (L := L) P w
          (stabilizerRingHom v w sigma' z)) =
      finitePlaceTransport (K := K) sigma.1 Q.1
        (RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hQ
          (RingEquiv.cast
            (R := fun R : HeightOneSpectrum
              (NumberField.RingOfIntegers L) => R.adicCompletion L)
            hcenter
            (completionPlaceAdic
      (K := K) (L := L) P w z))) := by
  dsimp only
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let targetQ := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  let sigma' : CompletionPlaceStabilizer v w :=
    MulEquiv.subgroupCongr
      (above_stabilizer_place
        (K := K) (L := L) P Q) sigma
  let hcenter : targetQ = Q.1 :=
    above_place_center (K := K) (L := L) P Q
  let hfix : sigma.1⁻¹ • Q = Q := (sigma⁻¹).2
  let hQ : Q.1 = sigma.1⁻¹ • Q.1 :=
    (congrArg Subtype.val hfix).symm
  let eField := completionPlaceAdic (K := K) (L := L) P w
  have hfun :
      (fun y : w.1.Completion =>
        RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hcenter
          (eField (stabilizerRingHom v w sigma' y))) =
      fun y : w.1.Completion =>
        finitePlaceTransport (K := K) sigma.1 Q.1
          (RingEquiv.cast
            (R := fun R : HeightOneSpectrum
              (NumberField.RingOfIntegers L) => R.adicCompletion L)
            hQ
            (RingEquiv.cast
              (R := fun R : HeightOneSpectrum
                (NumberField.RingOfIntegers L) => R.adicCompletion L)
              hcenter (eField y))) :=
    (dense_range_embedding w.1).equalizer
      ((continuous_cast_transport hcenter).comp
        ((place_adic_continuous
            (K := K) (L := L) P w).comp
          (place_stabilizer_isometry v w sigma').continuous))
      ((finite_transport_continuous (K := K) sigma.1 Q.1).comp
        ((continuous_cast_transport hQ).comp
          ((continuous_cast_transport hcenter).comp
            (place_adic_continuous
              (K := K) (L := L) P w))))
      (funext fun x => by
        change RingEquiv.cast hcenter
            (eField (stabilizerRingHom v w sigma'
              (completionEmbedding w.1 x))) =
          finitePlaceTransport (K := K) sigma.1 Q.1
            (RingEquiv.cast hQ
              (RingEquiv.cast hcenter
                (eField (completionEmbedding w.1 x))))
        dsimp only [eField]
        rw [place_stabilizer_embedding]
        simp_rw [place_adic_embedding]
        repeat rw [adic_embedding_transport hcenter]
        repeat rw [adic_embedding_transport hQ]
        rw [place_transport_embedding]
        rfl)
  exact congrFun hfun z

/-- The chosen literal stabilizer is the Galois group of the corresponding
extension of completed fields. -/
noncomputable def aboveStabilizerGal
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    primeAboveStabilizer (K := K) (L := L) P Q ≃*
      Gal(w.1.Completion/v.Completion) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  exact (MulEquiv.subgroupCongr
    (above_stabilizer_place
      (K := K) (L := L) P Q)).trans
    ((MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w)).trans
      (decompositionCompletionExtension v w.1))

/-- Under the completed-field Galois equivalence, the local automorphism is
the continuous extension of the original stabilizer element. -/
theorem above_stabilizer_gal
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (sigma : primeAboveStabilizer (K := K) (L := L) P Q)
    (x : let w := aboveCompletionPlace (K := K) (L := L) P Q
      w.1.Completion) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let sigma' : CompletionPlaceStabilizer v w :=
      MulEquiv.subgroupCongr
        (above_stabilizer_place
          (K := K) (L := L) P Q) sigma
    aboveStabilizerGal
        (K := K) (L := L) P Q sigma x =
      stabilizerRingHom v w sigma' x := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let sigma' : CompletionPlaceStabilizer v w :=
    MulEquiv.subgroupCongr
      (above_stabilizer_place
        (K := K) (L := L) P Q) sigma
  let d : absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w) sigma'
  change decompositionCompletionEquiv v w.1 d x =
    stabilizerRingHom v w sigma' x
  symm
  exact congrFun ((dense_range_embedding w.1).equalizer
    (place_stabilizer_isometry v w sigma').continuous
    (decomposition_alg_continuous v w.1 d)
    (funext fun y => by
      change stabilizerRingHom v w sigma'
          (completionEmbedding w.1 y) =
        decompositionCompletionEquiv v w.1 d
          (completionEmbedding w.1 y)
      rw [place_stabilizer_embedding,
        decomposition_alg_embedding]
      rfl)) x

/-- The centered valuation ring in the normalized completion model is the
prime-adic valuation ring at the prescribed upper prime. -/
noncomputable def aboveIntegerRing
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let hwna :=
      absolute_extension_nonarchimedean (FinitePlace.mk P).val w
    letI : IsUltrametricDist w.1.Completion :=
      absoluteUltrametricDist w.1 hwna
    completionIntegerRing w.1 ≃+* Q.1.adicCompletionIntegers L := by
  dsimp only
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna :=
    absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  have hcenter :
      nonarchimedeanHeightSpectrum w.1 hw hwna = Q.1 :=
    (upper_place_factor
        (K := K) (L := L) P w).symm.trans
      (above_place_center (K := K) (L := L) P Q)
  exact (centeredIntegerAdic w.1 hw hwna).trans
    (RingEquiv.cast
      (R := fun R : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        R.adicCompletionIntegers L) hcenter)

private theorem completion_integer_coe
    {F₀ : Type*} [Field F₀] {v₀ u₀ : AbsoluteValue F₀ ℝ}
    [IsUltrametricDist v₀.Completion] [IsUltrametricDist u₀.Completion]
    (h : v₀.IsEquiv u₀) (z : completionIntegerRing v₀) :
    ((completionIntegerEquiv h z :
        completionIntegerRing u₀) : u₀.Completion) =
      completionRing h (z : v₀.Completion) := rfl

private theorem integer_adic_coe
    {F₀ : Type*} [Field F₀] [NumberField F₀]
    (R : HeightOneSpectrum (NumberField.RingOfIntegers F₀))
    (z : completionIntegerRing (FinitePlace.mk R).val) :
    ((placeIntegerAdic R z :
        R.adicCompletionIntegers F₀) : R.adicCompletion F₀) =
      placeCompletionAdic R
        (z : (FinitePlace.mk R).val.Completion) := rfl

private theorem integers_cast_coe
    {F₀ : Type*} [Field F₀] [NumberField F₀]
    {R R' : HeightOneSpectrum (NumberField.RingOfIntegers F₀)}
    (h : R = R') (z : R.adicCompletionIntegers F₀) :
    (((RingEquiv.cast
        (R := fun S : HeightOneSpectrum (NumberField.RingOfIntegers F₀) =>
          S.adicCompletionIntegers F₀) h) z :
        R'.adicCompletionIntegers F₀) : R'.adicCompletion F₀) =
      RingEquiv.cast
        (R := fun S : HeightOneSpectrum (NumberField.RingOfIntegers F₀) =>
          S.adicCompletion F₀) h (z : R.adicCompletion F₀) := by
  subst R'
  rfl

private theorem adic_cast
    {F₀ : Type*} [Field F₀] [NumberField F₀]
    {R S T : HeightOneSpectrum (NumberField.RingOfIntegers F₀)}
    (h : R = S) (h' : S = T) (z : R.adicCompletion F₀) :
    RingEquiv.cast
        (R := fun U : HeightOneSpectrum (NumberField.RingOfIntegers F₀) =>
          U.adicCompletion F₀) h'
        (RingEquiv.cast
          (R := fun U : HeightOneSpectrum (NumberField.RingOfIntegers F₀) =>
            U.adicCompletion F₀) h z) =
      RingEquiv.cast
        (R := fun U : HeightOneSpectrum (NumberField.RingOfIntegers F₀) =>
          U.adicCompletion F₀) (h.trans h') z := by
  subst S
  subst T
  rfl

set_option maxHeartbeats 2000000 in
-- Unfolding both completion models creates a large dependent cast term.
/-- The field comparison restricts to the chosen integer-ring comparison. -/
theorem above_integer_coe
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (z : let w := aboveCompletionPlace (K := K) (L := L) P Q
      completionIntegerRing w.1) :
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let targetQ := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let hcenter : targetQ = Q.1 :=
      above_place_center (K := K) (L := L) P Q
    RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L)
        hcenter
        (completionPlaceAdic (K := K) (L := L) P w
          (z : w.1.Completion)) =
      ((aboveIntegerRing
        (K := K) (L := L) P Q z : Q.1.adicCompletionIntegers L) :
          Q.1.adicCompletion L) := by
  dsimp only
  unfold aboveIntegerRing
  unfold completionPlaceAdic
  dsimp only [centeredIntegerAdic, RingEquiv.trans_apply, id]
  rw [integers_cast_coe]
  rw [integer_adic_coe]
  rw [completion_integer_coe]
  rw [adic_cast]

/-- The chosen upper local-unit subgroup is the unit group of the centered
valuation ring in the normalized completion model. -/
noncomputable def unitsCompletionInteger
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1 ≃*
      (completionIntegerRing w.1)ˣ := by
  dsimp only
  exact (adicIntegersUnits Q.1).trans
    (Units.mapEquiv
      (aboveIntegerRing
        (K := K) (L := L) P Q).toMulEquiv).symm

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
private theorem idele_transport_val
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {Q Q' : FinitePrimesAbove (K := K) (L := L) P}
    (h : Q = Q')
    (x : IdeleUnitSubgroup
      (NumberField.RingOfIntegers L) L Q.1) :
    ((((h ▸ x).1 : (Q'.1.adicCompletion L)ˣ) :
        Q'.1.adicCompletion L)) =
      RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L)
        (congrArg Subtype.val h) ((x.1 : (Q.1.adicCompletion L)ˣ) :
          Q.1.adicCompletion L) := by
  subst Q'
  rfl

set_option maxHeartbeats 1000000 in
-- Preservation of the completed valuation ring unfolds the normalized
-- absolute-value action and its valuation estimates.
/-- The local completed Galois group preserves the canonical valuation ring
inside the chosen absolute-value completion. -/
noncomputable abbrev integerRingAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let F := v.Completion
    let E := w.1.Completion
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist F := placeUltrametricDist P
    letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional F E := placeCompletionDimensional v w
    MulSemiringAction Gal(E/F) (completionIntegerRing w.1) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let F := v.Completion
  let E := w.1.Completion
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F E := placeCompletionDimensional v w
  have hnorm (x : E) : ‖x‖ = spectralNorm F E x :=
    norm_spectral_completion v w.1 w.2
      (Algebra.IsAlgebraic.of_finite F E) x
  refine
    { smul := fun (sigma : Gal(E/F))
        (x : completionIntegerRing w.1) => ⟨sigma (x : E), ?_⟩
      one_smul := fun x => Subtype.ext (one_smul Gal(E/F) (x : E))
      mul_smul := fun sigma tau x =>
        Subtype.ext (mul_smul sigma tau (x : E))
      smul_zero := fun sigma => Subtype.ext (map_zero sigma)
      smul_add := fun sigma x y =>
        Subtype.ext (map_add sigma (x : E) (y : E))
      smul_one := fun sigma => Subtype.ext (map_one sigma)
      smul_mul := fun sigma x y =>
        Subtype.ext (map_mul sigma (x : E) (y : E)) }
  change ‖sigma (x : E)‖₊ ≤ 1
  have hspectral : spectralNorm F E (sigma (x : E)) =
      spectralNorm F E (x : E) :=
    (spectralNorm_eq_of_equiv sigma (x : E)).symm
  have hreal : ‖sigma (x : E)‖ = ‖(x : E)‖ := by
    rw [hnorm, hnorm, hspectral]
  exact_mod_cast hreal.le.trans x.property

set_option maxHeartbeats 1000000 in
-- Lifting the completed action to units elaborates dependent subtype and
-- transported ring-action data.
/-- Induced action on units of the chosen completed valuation ring. -/
noncomputable abbrev integerUnitsAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let F := v.Completion
    let E := w.1.Completion
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist F := placeUltrametricDist P
    letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional F E := placeCompletionDimensional v w
    MulDistribMulAction Gal(E/F) (completionIntegerRing w.1)ˣ := by
  dsimp only
  letI := integerRingAction
    (K := K) (L := L) P Q
  infer_instance

omit [FiniteDimensional K L] in
/-- Explicit chosen-coordinate formula for the stabilizer action transported
from supported local-unit families. -/
theorem units_stabilizer_action
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (sigma : primeAboveStabilizer (K := K) (L := L) P Q)
    (x : IdeleUnitSubgroup
      (NumberField.RingOfIntegers L) L Q.1) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    let hfix : sigma.1⁻¹ • Q = Q := (sigma⁻¹).2
    ((unitsStabilizerAction
      (K := K) (L := L) P Q).smul sigma x).1 =
      Units.map
        (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom
        ((hfix.symm ▸ x).1) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := primesAboveAction
    (K := K) (L := L) P Q
  let e := primesAboveSupported
    (K := K) (L := L) P Q
  let hfix : sigma.1⁻¹ • Q = Q := (sigma⁻¹).2
  change Units.map
      (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom
        ((e.symm x).1 (sigma.1⁻¹ • Q)).1 = _
  congr 1
  have heval : (e.symm x).1 (sigma.1⁻¹ • Q) ≍ (e.symm x).1 Q :=
    congr_arg_heq (fun R => (e.symm x).1 R) hfix
  have hcast : (hfix.symm ▸ x) ≍ x :=
    @eqRec_heq
      (FinitePrimesAbove (K := K) (L := L) P)
      (fun R => IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L R.1)
      Q (sigma.1⁻¹ • Q) hfix.symm x
  have hfull : (e.symm x).1 (sigma.1⁻¹ • Q) ≍ (hfix.symm ▸ x) :=
    heval.trans ((heq_of_eq (e.apply_symm_apply x)).trans hcast.symm)
  exact congr_heq (by rfl) hfull

set_option maxHeartbeats 4000000 in
-- The comparison of the two chosen-factor actions requires normalizing the
-- full completion and integer-ring transport chain.
set_option maxRecDepth 100000 in
/-- The chosen-factor action used by restricted Shapiro agrees, through the
completion-integer equivalence, with the local completed Galois action. -/
theorem units_integer_equivariant
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let F := v.Completion
    let E := w.1.Completion
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist F := placeUltrametricDist P
    letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional F E := placeCompletionDimensional v w
    letI : IsGalois F E := placeCompletionGalois v w
    letI : MulSemiringAction Gal(E/F) (completionIntegerRing w.1) :=
      integerRingAction
        (K := K) (L := L) P Q
    letI : MulDistribMulAction Gal(E/F) (completionIntegerRing w.1)ˣ :=
      integerUnitsAction
        (K := K) (L := L) P Q
    ∀ sigma : primeAboveStabilizer (K := K) (L := L) P Q,
      ∀ x : IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q.1,
      unitsCompletionInteger
          (K := K) (L := L) P Q
          ((unitsStabilizerAction
            (K := K) (L := L) P Q).smul sigma x) =
        (integerUnitsAction
          (K := K) (L := L) P Q).smul
            (aboveStabilizerGal
              (K := K) (L := L) P Q sigma)
            (unitsCompletionInteger
              (K := K) (L := L) P Q x) := by
  dsimp only
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := unitsStabilizerAction (K := K) (L := L) P Q
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let F := v.Completion
  let E := w.1.Completion
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F E := placeCompletionDimensional v w
  letI : IsGalois F E := placeCompletionGalois v w
  letI : MulSemiringAction Gal(E/F) (completionIntegerRing w.1) :=
    integerRingAction
      (K := K) (L := L) P Q
  letI : MulDistribMulAction Gal(E/F) (completionIntegerRing w.1)ˣ :=
    integerUnitsAction
      (K := K) (L := L) P Q
  let eInt := unitsCompletionInteger
    (K := K) (L := L) P Q
  intro sigma x
  let sigma' : CompletionPlaceStabilizer v w :=
    MulEquiv.subgroupCongr
      (above_stabilizer_place
        (K := K) (L := L) P Q) sigma
  let z : (completionIntegerRing w.1)ˣ := eInt x
  apply Units.ext
  apply Subtype.ext
  change ((eInt
      ((unitsStabilizerAction
        (K := K) (L := L) P Q).smul sigma x) :
      completionIntegerRing w.1) : E) =
    aboveStabilizerGal
      (K := K) (L := L) P Q sigma (z : E)
  let hfix : sigma.1⁻¹ • Q = Q := (sigma⁻¹).2
  let transported : (Q.1.adicCompletion L)ˣ :=
    Units.map
      (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom
      ((hfix.symm ▸ x).1)
  have ha : ((unitsStabilizerAction
      (K := K) (L := L) P Q).smul sigma x).1 = transported :=
    units_stabilizer_action
      (K := K) (L := L) P Q sigma x
  let oldInt : Q.1.adicCompletionIntegers L :=
    ((adicIntegersUnits Q.1)
      ((unitsStabilizerAction
        (K := K) (L := L) P Q).smul sigma x)).1
  have hmem : (transported : Q.1.adicCompletion L) ∈
      Q.1.adicCompletionIntegers L := by
    rw [← congrArg Units.val ha]
    exact oldInt.property
  let newInt : Q.1.adicCompletionIntegers L :=
    ⟨(transported : Q.1.adicCompletion L), hmem⟩
  have hInt : oldInt = newInt := by
    apply Subtype.ext
    exact congrArg Units.val ha
  change (((aboveIntegerRing
      (K := K) (L := L) P Q).symm oldInt :
        completionIntegerRing w.1) : E) = _
  rw [hInt]
  rw [above_stabilizer_gal]
  let eField := completionPlaceAdic (K := K) (L := L) P w
  let targetQ := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  let hcenter : targetQ = Q.1 :=
    above_place_center (K := K) (L := L) P Q
  let eFieldQ := eField.trans (RingEquiv.cast
    (R := fun R : HeightOneSpectrum
      (NumberField.RingOfIntegers L) => R.adicCompletion L) hcenter)
  let xInt : Q.1.adicCompletionIntegers L :=
    ((adicIntegersUnits Q.1) x).1
  have hzval : (z : completionIntegerRing w.1) =
      (aboveIntegerRing
        (K := K) (L := L) P Q).symm xInt := by
    rfl
  have hzcomp : eFieldQ (z : E) = (xInt : Q.1.adicCompletion L) := by
    rw [hzval]
    dsimp only [eFieldQ, eField, RingEquiv.trans_apply]
    rw [above_integer_coe]
    exact congrArg Subtype.val
      ((aboveIntegerRing
        (K := K) (L := L) P Q).apply_symm_apply xInt)
  let hQ : Q.1 = sigma.1⁻¹ • Q.1 :=
    (congrArg Subtype.val hfix).symm
  have htransport :=
    stabilizer_adic_transport
      (K := K) (L := L) P Q sigma (z : E)
  change eFieldQ
      (stabilizerRingHom v w sigma' (z : E)) =
    finitePlaceTransport (K := K) sigma.1 Q.1
      (RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L)
        hQ (eFieldQ (z : E))) at htransport
  rw [hzcomp] at htransport
  have hcastx :
      RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hQ (xInt : Q.1.adicCompletion L) =
        ((((hfix.symm ▸ x).1 :
            ((sigma.1⁻¹ • Q).1.adicCompletion L)ˣ) :
          (sigma.1⁻¹ • Q).1.adicCompletion L)) := by
    rw [show (xInt : Q.1.adicCompletion L) =
      ((x.1 : (Q.1.adicCompletion L)ˣ) : Q.1.adicCompletion L) by rfl]
    exact (idele_transport_val
      (K := K) (L := L) P hfix.symm x).symm
  rw [hcastx] at htransport
  have hcomp :
      eFieldQ (((aboveIntegerRing
        (K := K) (L := L) P Q).symm newInt :
          completionIntegerRing w.1) : E) =
        (newInt : Q.1.adicCompletion L) := by
    dsimp only [eFieldQ, eField, RingEquiv.trans_apply]
    rw [above_integer_coe]
    exact congrArg Subtype.val
      ((aboveIntegerRing
        (K := K) (L := L) P Q).apply_symm_apply newInt)
  apply eFieldQ.injective
  rw [hcomp]
  simpa [eFieldQ, eField, eInt, z, sigma', newInt, transported, xInt, hQ, hfix,
    targetQ, hcenter, aboveIntegerRing]
    using htransport.symm

/-- The cyclic action-norm criterion, including the possibly trivial cyclic
group.  The nontrivial case is the multiplicative `H²` calculation; the
trivial case is the standard positive-degree vanishing theorem. -/
theorem ulift_subsingleton_surjective
    {G M : Type u} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M]
    (hcyclic : IsCyclic G)
    (hN : Function.Surjective (FMAct.norm G M)) :
    Subsingleton (H2 (uliftMulRepresentation (G := G) (M := M))) := by
  let n := Nat.card G
  letI : NeZero n := ⟨(Nat.card_pos : 0 < Nat.card G).ne'⟩
  by_cases hn : n = 1
  · letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hn).1
    exact ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton
        (uliftMulRepresentation (G := G) (M := M)) 1)
  · have hn' : 1 < n :=
      (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne n, hn⟩
    exact ulift_cohomology_subsingleton
      hn' (zmodCyclicMulEquiv (G := G) hcyclic) hN

section FixedUnits

variable {A B G : Type u} [CommRing A] [CommRing B]
  [Group G] [Fintype G] [MulSemiringAction G B]
  [Algebra A B] [IsGaloisGroup G A B]

/-- Base units as invariant units in a finite Galois integral model. -/
private def unramifiedUnitsInvariants :
    Aˣ →* FMAct.invariants G Bˣ where
  toFun x := ⟨Units.map (algebraMap A B) x, by
    intro g
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

variable [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]

omit [Fintype G] in
private theorem unramified_invariants_bijective :
    Function.Bijective
      (unramifiedUnitsInvariants (A := A) (B := B) (G := G)) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective A B
    have h := congrArg
      (fun z : FMAct.invariants G Bˣ ↦ ((z.1 : Bˣ) : B)) hxy
    simpa [unramifiedUnitsInvariants] using h
  · intro x
    have hfixed : ∀ g : G, g • (x.1 : B) = (x.1 : B) := by
      intro g
      exact congrArg Units.val (x.2 g)
    obtain ⟨a, ha⟩ :=
      Algebra.IsInvariant.isInvariant (A := A) (B := B) (G := G)
        (x.1 : B) hfixed
    have haUnit : IsUnit a := by
      rw [← isUnit_map_iff (algebraMap A B) a, ha]
      exact x.1.isUnit
    refine ⟨haUnit.unit, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change algebraMap A B (haUnit.unit : A) = (x.1 : B)
    rw [haUnit.unit_spec, ha]

private noncomputable def unramifiedBaseInvariants :
    Aˣ ≃* FMAct.invariants G Bˣ :=
  MulEquiv.ofBijective
    (unramifiedUnitsInvariants (A := A) (B := B) (G := G))
    unramified_invariants_bijective

/-- Surjectivity of a base-valued unit norm gives surjectivity of the
finite-action norm once the usual product formula is known. -/
private theorem unramified_action_surjective
    (N : Bˣ →* Aˣ) (hN : Function.Surjective N)
    (hprod : ∀ v : Bˣ,
      algebraMap A B (N v : A) = ∏ g : G, g • (v : B)) :
    Function.Surjective (FMAct.norm G Bˣ) := by
  intro y
  obtain ⟨v, hv⟩ := hN
    ((unramifiedBaseInvariants
      (A := A) (B := B) (G := G)).symm y)
  refine ⟨v, ?_⟩
  apply Subtype.ext
  rw [FMAct.norm_coe]
  apply Units.ext
  change ((∏ g : G, g • v : Bˣ) : B) = (y.1 : Bˣ)
  rw [Units.coe_prod]
  change (∏ g : G, g • (v : B)) = (y.1 : Bˣ)
  rw [← hprod, hv]
  exact congrArg
    (fun z : FMAct.invariants G Bˣ ↦ ((z.1 : Bˣ) : B))
    ((unramifiedBaseInvariants
      (A := A) (B := B) (G := G)).apply_symm_apply y)

end FixedUnits

set_option synthInstance.maxHeartbeats 1000000 in
-- Resolving the completed decomposition-group action and its fixed-unit
-- algebra requires an unusually deep instance search.
set_option maxHeartbeats 6000000 in
-- The local norm-surjectivity proof combines completion transport, fixed
-- units, and the unramified integral norm theorem.
/-- At an unramified chosen completion, the finite-action norm on its
canonical valuation-ring units is onto the invariant units. -/
theorem units_action_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let F := v.Completion
    let E := w.1.Completion
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : NontriviallyNormedField F :=
      placeNontriviallyNormed P
    letI : IsUltrametricDist F := placeUltrametricDist P
    letI : ValuativeRel F := placeValuativeRel P
    letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
    letI : IsNonarchimedeanLocalField F :=
      placeNonarchimedeanField P
    letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional F E := placeCompletionDimensional v w
    letI : IsGalois F E := placeCompletionGalois v w
    letI : MulDistribMulAction Gal(E/F) (completionIntegerRing w.1)ˣ :=
      integerUnitsAction
        (K := K) (L := L) P Q
    Function.Surjective
      (FMAct.norm Gal(E/F) (completionIntegerRing w.1)ˣ) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let F := v.Completion
  let E := w.1.Completion
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : NontriviallyNormedField F :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : IsUltrametricDist E :=
    absoluteUltrametricDist w.1 hwna
  letI : ValuativeRel F := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    placeNonarchimedeanField P
  let A := Valuation.integer (ValuativeRel.valuation F)
  let A' := completionIntegerRing v
  let B := completionIntegerRing w.1
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  let hFinite : FiniteDimensional F E := placeCompletionDimensional v w
  letI : FiniteDimensional F E := hFinite
  letI : IsGalois F E := placeCompletionGalois v w
  let hSeparable : Algebra.IsSeparable F E := IsGalois.to_isSeparable
  letI : Algebra A' B := completionIntegerLies v w.1 w.2
  let eA : A ≃+* A' :=
    valuativeIntegerNorm F
  letI : Algebra A B :=
    ((algebraMap A' B).comp eA.toRingHom).toAlgebra
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra A E := Algebra.ofSubring A
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (centeredIntegerAdic v
        (absolute_value_nontrivial P)
        (fun x y ↦ (FinitePlace.mk P).add_le x y)).symm
  letI : Module.Finite A' B :=
    completion_integer_module v w.1 w.2 hFinite hSeparable
  letI : Module.Finite A B := by
    apply Module.Finite.of_equiv_equiv eA.symm (RingEquiv.refl B)
    ext x
    rfl
  have hcenter :
      nonarchimedeanHeightSpectrum w.1 hw hwna = Q.1 :=
    (upper_place_factor
        (K := K) (L := L) P w).symm.trans
      (above_place_center (K := K) (L := L) P Q)
  have hUnramifiedA' : Algebra.FormallyUnramified A' B := by
    have hQcenter : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K)
        (nonarchimedeanHeightSpectrum w.1 hw hwna).asIdeal :=
      hcenter.symm ▸ hQ
    exact completion_formally_unramified
      P w.1 w.2 hw hwna hQcenter hFinite hSeparable
  letI : Algebra.FormallyUnramified A' B := hUnramifiedA'
  letI : IsLocalHom (algebraMap A' B) :=
    completion_integer_lies v w.1 w.2
  letI : IsLocalHom eA.toRingHom :=
    IsLocalHom.of_surjective eA.toRingHom eA.surjective
  letI : IsLocalHom (algebraMap A B) := by
    change IsLocalHom ((algebraMap A' B).comp eA.toRingHom)
    infer_instance
  letI : Algebra.FormallyUnramified A B := by
    apply Algebra.FormallyUnramified.of_map_maximalIdeal
    calc
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          ((IsLocalRing.maximalIdeal A).map eA.toRingHom).map
            (algebraMap A' B) := by rw [Ideal.map_map]; rfl
      _ = (IsLocalRing.maximalIdeal A').map (algebraMap A' B) := by
        congr 1
        exact IsLocalRing.map_ringEquiv_maximalIdeal eA
      _ = IsLocalRing.maximalIdeal B :=
        Algebra.FormallyUnramified.map_maximalIdeal
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : IsFractionRing B E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : IsIntegrallyClosed B :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isIntegrallyClosed
  letI : IsIntegralClosure B A E :=
    IsIntegralClosure.of_isIntegrallyClosed B A E
  letI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B) :=
    unramified_maximal_formally A B
  letI : MulSemiringAction Gal(E/F) B :=
    integerRingAction
      (K := K) (L := L) P Q
  letI : SMulDistribClass Gal(E/F) B E := ⟨by
    intro g b x
    change g ((b : E) * x) = (g (b : E)) * g x
    exact map_mul g (b : E) x⟩
  letI : IsGaloisGroup Gal(E/F) A B :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A B F E
  letI : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap F E).injective
    have h := congrArg (algebraMap B E) hxy
    simpa only [IsScalarTower.algebraMap_apply] using h
  let N : Bˣ →* Aˣ := Units.map (Algebra.intNorm A B)
  have hN : Function.Surjective N := by
    intro x
    obtain ⟨y, hy⟩ :=
      model_units_surjective F E B x
    refine ⟨y, ?_⟩
    apply Units.ext
    apply Subtype.ext
    change algebraMap A F (Algebra.intNorm A B (y : B)) =
      algebraMap A F (x : A)
    rw [Algebra.algebraMap_intNorm (K := F) (L := E)]
    exact hy
  have hprod (y : Bˣ) :
      algebraMap A B (N y : A) = ∏ g : Gal(E/F), g • (y : B) := by
    apply IsFractionRing.injective B E
    calc
      algebraMap B E (algebraMap A B (N y : A)) =
          algebraMap F E (Algebra.norm F (y : E)) := by
        change algebraMap F E
            (algebraMap A F (Algebra.intNorm A B (y : B))) =
          algebraMap F E (Algebra.norm F (algebraMap B E (y : B)))
        rw [Algebra.algebraMap_intNorm (K := F) (L := E)]
      _ = ∏ g : Gal(E/F), g (y : E) :=
        Algebra.norm_eq_prod_automorphisms F (y : E)
      _ = algebraMap B E (∏ g : Gal(E/F), g • (y : B)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro g _
        exact (algebraMap.coe_smul' (B := B) (C := E) g (y : B)).symm
  exact unramified_action_surjective N hN hprod

section NormTransport

variable {G H M N : Type u} [Group G] [Fintype G]
  [Group H] [Fintype H] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction H N]

/-- Surjectivity of the finite-action norm is invariant under simultaneous
equivariant relabelling of the group and coefficient group. -/
private theorem action_surjective_equivariant
    (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ g : G, ∀ x : M, eM (g • x) = eG g • eM x)
    (hN : Function.Surjective (FMAct.norm H N)) :
    Function.Surjective (FMAct.norm G M) := by
  intro y
  let y' : FMAct.invariants H N :=
    ⟨eM y.1, fun h => by
      let g := eG.symm h
      change h • eM y.1 = eM y.1
      rw [← eG.apply_symm_apply h, ← heq]
      exact congrArg eM (y.2 g)⟩
  obtain ⟨z, hz⟩ := hN y'
  refine ⟨eM.symm z, ?_⟩
  apply Subtype.ext
  apply eM.injective
  change eM ((∏ g : G, g • eM.symm z)) = eM y.1
  rw [map_prod]
  simp_rw [heq, eM.apply_symm_apply]
  have hz' := congrArg Subtype.val hz
  calc
    ∏ g : G, eG g • z = ∏ h : H, h • z :=
      Fintype.prod_equiv eG.toEquiv
        (fun g : G ↦ eG g • z) (fun h : H ↦ h • z) (fun _ ↦ rfl)
    _ = eM y.1 := hz'

end NormTransport

/-- Restricted Shapiro transports chosen-factor vanishing back to the
whole product of upper local-unit factors. -/
theorem resized_subsingleton_chosen
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Subsingleton
      (H2 (resizedUnitsRepresentation
        (K := K) (L := L) P Q))) :
    Subsingleton
      (H2 (resizedPrimesRepresentation
        (K := K) (L := L) P)) := by
  letI := hQ
  exact (resizedAboveUnits
    (K := K) (L := L) P Q).injective.subsingleton

set_option synthInstance.maxHeartbeats 1000000 in
-- The restricted-Shapiro comparison requires resolving nested local-unit,
-- stabilizer, and cohomology instances.
set_option maxHeartbeats 6000000 in
-- Assembling vanishing over every unramified upper-prime orbit expands the
-- complete Shapiro and norm-surjectivity calculation.
/-- The degree-two cohomology of all upper local-unit factors above an
unramified finite base prime is trivial. -/
theorem primes_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    Subsingleton
      (H2 (resizedPrimesRepresentation
        (K := K) (L := L) P)) := by
  letI := unitsStabilizerAction (K := K) (L := L) P Q
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let F := v.Completion
  let E := w.1.Completion
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField F :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : ValuativeRel F := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    placeNonarchimedeanField P
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F E := placeCompletionDimensional v w
  letI : IsGalois F E := placeCompletionGalois v w
  letI : MulSemiringAction Gal(E/F) (completionIntegerRing w.1) :=
    integerRingAction
      (K := K) (L := L) P Q
  letI : MulDistribMulAction Gal(E/F) (completionIntegerRing w.1)ˣ :=
    integerUnitsAction
      (K := K) (L := L) P Q
  letI : Fintype
      (primeAboveStabilizer (K := K) (L := L) P Q) :=
    Fintype.ofFinite _
  let eG := aboveStabilizerGal
    (K := K) (L := L) P Q
  let eM := unitsCompletionInteger
    (K := K) (L := L) P Q
  have hCompletionNorm :
      Function.Surjective (FMAct.norm Gal(E/F)
        (completionIntegerRing w.1)ˣ) :=
    by
      simpa [integerUnitsAction] using
        (units_action_unramified
          (K := K) (L := L) P Q hQ)
  have hChosenNorm : Function.Surjective
      (FMAct.norm
        (primeAboveStabilizer (K := K) (L := L) P Q)
        (IdeleUnitSubgroup
          (NumberField.RingOfIntegers L) L Q.1)) :=
    action_surjective_equivariant eG eM
      (units_integer_equivariant
        (K := K) (L := L) P Q) hCompletionNorm
  have hChosen : Subsingleton
      (H2 (resizedUnitsRepresentation
        (K := K) (L := L) P Q)) := by
    change Subsingleton
      (H2 (uliftMulRepresentation
        (G := primeAboveStabilizer (K := K) (L := L) P Q)
        (M := IdeleUnitSubgroup
          (NumberField.RingOfIntegers L) L Q.1)))
    exact ulift_subsingleton_surjective
      (above_stabilizer_unramified
        (K := K) (L := L) P Q hQ) hChosenNorm
  exact resized_subsingleton_chosen
    (K := K) (L := L) P Q hChosen

end

end Submission.CField.HNorm
