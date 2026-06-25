import Submission.ClassField.BrauerLocalization.LocalTateZero
import Submission.ClassField.HasseNorm.FiniteStageAssembly
import Submission.ClassField.HasseNorm.InfiniteStageLimit
import Submission.ClassField.HasseNorm.InfiniteCompletionPlaces
import Submission.ClassField.HasseNorm.HCompletionProduct

/-!
# Tate degree zero for the restricted idèle product in Proposition VII.2.7

For an admissible finite set of places, the existing finite-stage
decomposition deletes the unramified local-unit coordinates outside the set.
Shapiro then identifies every remaining finite and infinite orbit with the
chosen completion-place representation.  Cyclic periodicity transports the
result back from `H²` to Tate degree zero.
-/

namespace Submission.CField.BLoc

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Source admissibility implies the exact unramified-outside condition used
by the finite-stage decomposition. -/
theorem unramified_outside
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S) :
    ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
          Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
            (upperPrime (K := K) (L := L) P Q).asIdeal := by
  intro P hP Q
  let q := upperPrime (K := K) (L := L) P Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q)).symm
  apply (unramified_ramification_idx
    P.asIdeal q.asIdeal q.ne_bot).2
  by_contra hramified
  apply hP
  have hmem := hS.2 q (by
    simpa [q, upperPrime_under (K := K) (L := L) P Q] using hramified)
  simpa [q, upperPrime_under (K := K) (L := L) P Q] using hmem

/-- The finite part of an admissible stage has `H²` equal to the product of
the unrestricted completion orbits selected by `S`. -/
noncomputable def stage2Exceptional
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H2 (resizedAboveRepresentation
          (K := K) (L := L) P.1)) :=
  (ideleStagePi
    (K := K) (L := L) S).trans
      (ideleStageExceptional
        (K := K) (L := L) S
        (fun P hP ↦
          resized_stage_outside
            (K := K) (L := L) S
            (unramified_outside S hS) P hP))

/-- One unrestricted finite completion orbit is Shapiro-equivalent to the
chosen local completion-place representation. -/
noncomputable def orbitHChosen
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    H2 (resizedAboveRepresentation
      (K := K) (L := L) P) ≃+
      H2 (uliftIntegralRepresentation
        (placeUnitsRepresentation (FinitePlace.mk P).val w)) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedIsoOrbit
      (K := K) (L := L) P).symm).toLinearEquiv.toAddEquiv |>.trans
        (uliftUnitsH
          (K := K) (L := L) P w)

/-- The infinite idèle factor is the product of the chosen local `H²`
groups. -/
noncomputable def idelesHChosen
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    H2 (resizedInfiniteRepresentation K L) ≃+
      (∀ v : InfinitePlace K,
        H2 (uliftIntegralRepresentation
          (placeUnitsRepresentation v.1
            (w ⟨Sum.inr v, hS.1 v⟩)))) :=
  (resizedDirectSum
    (K := K) (L := L)).trans <|
      (DirectSum.addEquivProd (fun v : InfinitePlace K ↦
        H2 (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v)))).trans <|
        AddEquiv.piCongrRight fun v ↦
          uliftInfiniteUnits
            (K := K) (L := L) v (w ⟨Sum.inr v, hS.1 v⟩)

/-- The finite factor is the product of the chosen local `H²` groups at
the finite members of `S`. -/
noncomputable def stageHChosen
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H2 (uliftIntegralRepresentation
          (placeUnitsRepresentation (FinitePlace.mk P.1).val
            (w ⟨Sum.inl P.1, P.2⟩)))) :=
  (stage2Exceptional S hS).trans <|
    AddEquiv.piCongrRight fun P ↦
      orbitHChosen P.1
        (w ⟨Sum.inl P.1, P.2⟩)

/-- Recombine the infinite and finite products into the product indexed by
the literal subtype `S`. -/
noncomputable def splitH2
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    ((∀ v : InfinitePlace K,
        H2 (uliftIntegralRepresentation
          (placeUnitsRepresentation v.1
            (w ⟨Sum.inr v, hS.1 v⟩)))) ×
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H2 (uliftIntegralRepresentation
          (placeUnitsRepresentation (FinitePlace.mk P.1).val
            (w ⟨Sum.inl P.1, P.2⟩))))) ≃+
      (∀ v : S, H2 (uliftIntegralRepresentation
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
          (w v)))) where
  toFun x := fun v ↦ match v with
    | ⟨Sum.inl P, hP⟩ => x.2 ⟨P, hP⟩
    | ⟨Sum.inr v, _⟩ => x.1 v
  invFun y :=
    ⟨fun v ↦ y ⟨Sum.inr v, hS.1 v⟩,
      fun P ↦ y ⟨Sum.inl P.1, P.2⟩⟩
  left_inv x := by
    apply Prod.ext
    · funext v
      rfl
    · funext P
      rfl
  right_inv y := by
    funext v
    rcases v with ⟨v, hv⟩
    cases v <;> rfl
  map_add' x y := by
    funext v
    rcases v with ⟨v, hv⟩
    cases v <;> rfl

/-- Degree-two cohomology of an admissible restricted idèle stage is the
product of the chosen local degree-two groups. -/
noncomputable def idelesPlacesLocal
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) ≃+
      (∀ v : S, H2 (uliftIntegralRepresentation
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
          (w v)))) :=
  (resizedPlacesH
    (K := K) (L := L) S).trans <|
      (AddEquiv.prodCongr
        (idelesHChosen S hS w)
        (stageHChosen S hS w)).trans
          (splitH2 S hS w)

/-- Cyclic periodicity identifies local Tate degree zero with the resized
local `H²` presentation. -/
noncomputable def tateH2
    [IsCyclic Gal(L/K)]
    (v : NumberFieldPlace K)
    (w : CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) :
    letI : Fintype (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute v) w) := Fintype.ofFinite _
    tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute v) w) ≃+
      H2 (uliftIntegralRepresentation
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute v) w)) := by
  let H := CompletionPlaceStabilizer (coinvariantsInvariantsAbsolute v) w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  let g := Classical.choose (IsCyclic.exists_generator (α := H))
  let hg := Classical.choose_spec (IsCyclic.exists_generator (α := H))
  exact (tateIntLift
    (placeUnitsRepresentation
      (coinvariantsInvariantsAbsolute v) w)).trans
        (tateCohomologyTwo
          (uliftIntegralRepresentation
            (placeUnitsRepresentation
              (coinvariantsInvariantsAbsolute v) w)) g hg).toAddEquiv

set_option synthInstance.maxHeartbeats 500000 in
-- The stage and every dependent local periodicity equivalence elaborate together.
set_option maxHeartbeats 6000000 in
-- The Tate-zero product comparison unfolds every finite-stage coordinate.
/-- Tate degree zero of an admissible restricted idèle stage is the product
of the chosen local Tate-zero groups. -/
noncomputable def idelesPlacesTate
    [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI (v : S) : Fintype (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
      Fintype.ofFinite _
    letI (v : S) : AddCommGroup (tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
          (w v))) := inferInstance
    tateZero
        (idelesRepresentation (K := K) (L := L) S) ≃+
      (∀ v : S, tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
          (w v))) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  letI (v : S) : Fintype (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
    Fintype.ofFinite _
  letI (v : S) : AddCommGroup (tateZero
      (placeUnitsRepresentation
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
        (w v))) := inferInstance
  let g := Classical.choose (IsCyclic.exists_generator (α := Gal(L/K)))
  let hg := Classical.choose_spec (IsCyclic.exists_generator (α := Gal(L/K)))
  exact ((tateIntLift
    (idelesRepresentation (K := K) (L := L) S)).trans
      (tateCohomologyTwo
        (resizedPlacesRepresentation (K := K) (L := L) S)
        g hg).toAddEquiv).trans <|
    (idelesPlacesLocal S hS w).trans <|
      (AddEquiv.piCongrRight fun v ↦
        (tateH2
          (K := K) (L := L) (v : NumberFieldPlace K) (w v)).symm)

set_option synthInstance.maxHeartbeats 500000 in
-- Finiteness instances are assembled over the dependent finite product.
set_option maxHeartbeats 4000000 in
-- The numerator-cardinality calculation normalizes the full restricted product.
/-- The numerator of the restricted-product Herbrand quotient has the
cardinality predicted by Proposition VII.2.7. -/
theorem ideles_places_cardinality
    [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (hlocal : ∀ v : S,
      letI : Fintype (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
          Fintype.ofFinite _
      Finite (tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) ∧
      Nat.card (tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) =
        Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Finite (tateZero
      (idelesRepresentation (K := K) (L := L) S)) ∧
    Nat.card (tateZero
      (idelesRepresentation (K := K) (L := L) S)) =
      ∏ v : S, Nat.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  letI (v : S) : Fintype (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
    Fintype.ofFinite _
  letI (v : S) : AddCommGroup (tateZero
      (placeUnitsRepresentation
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
        (w v))) := inferInstance
  letI (v : S) : Finite (tateZero
      (placeUnitsRepresentation
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) :=
    (hlocal v).1
  let e := idelesPlacesTate
    (K := K) (L := L) S hS w
  let hfinite : Finite (tateZero
      (idelesRepresentation (K := K) (L := L) S)) :=
    Finite.of_equiv
      (∀ v : S, tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))
      e.symm.toEquiv
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card (tateZero
        (idelesRepresentation (K := K) (L := L) S)) =
        Nat.card (∀ v : S, tateZero
          (placeUnitsRepresentation
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
            (w v))) := Nat.card_congr e.toEquiv
    _ = ∏ v : S, Nat.card (tateZero
          (placeUnitsRepresentation
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
            (w v))) := Nat.card_pi
    _ = ∏ v : S, Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) := by
      apply Finset.prod_congr rfl
      intro v _
      exact (hlocal v).2

end

end Submission.CField.BLoc
