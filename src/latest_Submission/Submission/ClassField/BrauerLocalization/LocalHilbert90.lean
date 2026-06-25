import Submission.ClassField.HasseNorm.InfiniteCompletionPlaces
import Submission.ClassField.HasseNorm.ClassH1
import Submission.ClassField.HasseNorm.IdeleDecomposition

/-!
# The Tate-minus-one local input to Proposition VII.2.7

The classical Hilbert 90 helpers in Mathlib are specialized to universe zero.
This file repeats only their two elementary cocycle wrappers at arbitrary
universe, proves Hilbert 90 for the `ULift ℤ` completed-unit representation,
and transports the result through the decomposition-group/completion
equivalence.  Cyclic periodicity then makes Tate degree minus one of every
chosen completion factor trivial.
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

private theorem isMulCocycle₁_of_mem_cocycles₁_ulift
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (f : G → Additive M)
    (hf : f ∈ cocycles₁ (uliftMulRepresentation (G := G) (M := M))) :
    IsMulCocycle₁ (Additive.toMul ∘ f) :=
  (mem_cocycles₁_iff
    (A := uliftMulRepresentation (G := G) (M := M)) f).1 hf

private def coboundariesMulCoboundary₁_ulift
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {f : G → M} (hf : IsMulCoboundary₁ f) :
    coboundaries₁ (uliftMulRepresentation (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f, hf.choose, funext hf.choose_spec⟩

/-- Hilbert 90 for the universe-resized multiplicative Galois
representation.  The proof is the usual cocycle-to-coboundary argument; the
coefficient ring plays no role. -/
theorem hasse_global_units
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (a : H1 (hasseGlobalRepresentation F E)) :
    a = 0 := by
  exact H1_induction_on a fun x ↦ (H1π_eq_zero_iff _).2 <| by
    refine (coboundariesMulCoboundary₁_ulift ?_).2
    exact isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (Additive.toMul ∘ x)
      (isMulCocycle₁_of_mem_cocycles₁_ulift _ x.2)

/-- Relabeling the local Galois group by an equivalent group and rewriting
the action does not change degree-one cohomology. -/
private noncomputable def hasseH1
    {F E H : Type u} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    [Group H] [MulDistribMulAction H Eˣ]
    (e : H ≃* Gal(E/F))
    (hintertwines : ∀ h : H,
      (hasseGlobalRepresentation F E).ρ (e h) =
        (uliftMulRepresentation (G := H) (M := Eˣ)).ρ h) :
    H1 (hasseGlobalRepresentation F E) ≃+
      H1 (uliftMulRepresentation (G := H) (M := Eˣ)) :=
  ((cohomologyMulIso e
      (hasseGlobalRepresentation F E) 1).trans
    ((groupCohomology.functor (ULift.{u} ℤ) H 1).mapIso
      (hasseRestrictIso e hintertwines))).toLinearEquiv.toAddEquiv

set_option synthInstance.maxHeartbeats 500000 in
-- The completed Galois action and the transported cohomology elaborate together.
set_option maxHeartbeats 4000000 in
/-- Degree-one comparison between a finite completed extension and the
stabilizer action on the chosen completion. -/
private noncomputable def h1Stabilizer
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [Fact v.IsNontrivial] [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v) :
    let W := CompletionPlacesAbove (L := L) v
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      above_pretr_nonar v hvna
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Submission.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    H1 (hasseGlobalRepresentation
        v.Completion w.1.Completion) ≃+
      H1 (hasseUnitsRepresentation v w) := by
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : MulDistribMulAction Gal(w.1.Completion/v.Completion)
      w.1.Completionˣ := Units.mulDistribMulActionRight
  letI : MulSemiringAction (CompletionPlaceStabilizer v w)
      w.1.Completion := stabilizerSemiringAction v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  let e : CompletionPlaceStabilizer v w ≃*
      Gal(w.1.Completion/v.Completion) :=
    (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w)).trans
        (decompositionCompletionExtension v w.1)
  have hsmul (sigma : CompletionPlaceStabilizer v w)
      (x : w.1.Completionˣ) : e sigma • x = sigma • x := by
    apply Units.ext
    change (e sigma : w.1.Completion ≃ₐ[v.Completion] w.1.Completion)
        (x : w.1.Completion) =
      stabilizerRingHom v w sigma (x : w.1.Completion)
    let d : absoluteValueDecomposition v w.1 :=
      MulEquiv.subgroupCongr
        (hasse_stabilizer_decomposition v w) sigma
    change decompositionCompletionEquiv v w.1 d (x : w.1.Completion) =
      stabilizerRingHom v w sigma (x : w.1.Completion)
    exact (stabilizer_decomposition_action
      v w sigma x).symm
  have hintertwines (sigma : CompletionPlaceStabilizer v w) :
      (hasseGlobalRepresentation
        v.Completion w.1.Completion).ρ (e sigma) =
      (uliftMulRepresentation (G := CompletionPlaceStabilizer v w)
        (M := w.1.Completionˣ)).ρ sigma := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (e sigma •
        (show Additive w.1.Completionˣ from x).toMul) =
      Additive.ofMul (sigma •
        (show Additive w.1.Completionˣ from x).toMul)
    exact congrArg Additive.ofMul
      (hsmul sigma (show Additive w.1.Completionˣ from x).toMul)
  exact hasseH1 e hintertwines

set_option synthInstance.maxHeartbeats 500000 in
-- The archimedean completion and its transported action elaborate together.
set_option maxHeartbeats 4000000 in
/-- Archimedean analogue of
`h1Stabilizer`. -/
private noncomputable def infinite1Stabilizer
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    H1 (hasseGlobalRepresentation
        v.1.Completion w.1.1.Completion) ≃+
      H1 (hasseUnitsRepresentation v.1 w0) := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  letI : MulDistribMulAction Gal(w.1.1.Completion/v.1.Completion)
      w.1.1.Completionˣ := Units.mulDistribMulActionRight
  letI : MulSemiringAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completion := stabilizerSemiringAction v.1 w0
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  let e : CompletionPlaceStabilizer v.1 w0 ≃*
      Gal(w.1.1.Completion/v.1.Completion) :=
    (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v.1 w0)).trans
        (infiniteDecompositionGroup v w.1)
  have hsmul (sigma : CompletionPlaceStabilizer v.1 w0)
      (x : w.1.1.Completionˣ) : e sigma • x = sigma • x := by
    apply Units.ext
    change (e sigma : w.1.1.Completion ≃ₐ[v.1.Completion]
        w.1.1.Completion) (x : w.1.1.Completion) =
      stabilizerRingHom v.1 w0 sigma
        (x : w.1.1.Completion)
    let d : absoluteValueDecomposition v.1 w.1.1 :=
      MulEquiv.subgroupCongr
        (hasse_stabilizer_decomposition v.1 w0)
        sigma
    change decompositionCompletionEquiv v.1 w.1.1 d
        (x : w.1.1.Completion) =
      stabilizerRingHom v.1 w0 sigma
        (x : w.1.1.Completion)
    exact (stabilizer_decomposition_action
      v.1 w0 sigma x).symm
  have hintertwines (sigma : CompletionPlaceStabilizer v.1 w0) :
      (hasseGlobalRepresentation
        v.1.Completion w.1.1.Completion).ρ (e sigma) =
      (uliftMulRepresentation (G := CompletionPlaceStabilizer v.1 w0)
        (M := w.1.1.Completionˣ)).ρ sigma := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (e sigma •
        (show Additive w.1.1.Completionˣ from x).toMul) =
      Additive.ofMul (sigma •
        (show Additive w.1.1.Completionˣ from x).toMul)
    exact congrArg Additive.ofMul
      (hsmul sigma (show Additive w.1.1.Completionˣ from x).toMul)
  exact hasseH1 e hintertwines

/-- Degree-one cohomology of the chosen completion under its global
decomposition group is trivial, uniformly at finite and infinite places. -/
theorem units_h_1
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : NumberFieldPlace K)
    (w : CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v))
    (a : H1 (hasseUnitsRepresentation
      (coinvariantsInvariantsAbsolute v) w)) :
    a = 0 := by
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      let W := CompletionPlacesAbove (L := L) v
      letI : Finite W := absolute_extensions_separable v
      letI : Nonempty W :=
        absolute_value_extension (K := K) (L := L) v
      letI : MulAction.IsPretransitive Gal(L/K) W :=
        completion_above_pretransitive P
      letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      letI : FiniteDimensional v.Completion w.1.Completion :=
        Submission.NumberTheory.Milne.placeCompletionDimensional v w
      letI : IsGalois v.Completion w.1.Completion :=
        placeCompletionGalois v w
      let e := h1Stabilizer
        (K := K) (L := L) v w (fun x y ↦ (FinitePlace.mk P).add_le x y)
      apply e.symm.injective
      simpa using hasse_global_units
        v.Completion w.1.Completion (e.symm a)
  | inr v =>
      let w' : InfinitePlacesAbove (K := K) (L := L) v :=
        normalizedPlacesAbove
          (K := K) (L := L) v w
      let hwv := infinite_lies_comap v w'.1 w'.2
      letI : Fact (AbsoluteValue.LiesOver w'.1.1 v.1) := ⟨hwv⟩
      letI : Algebra v.1.Completion w'.1.1.Completion :=
        (completionLies v.1 w'.1.1 hwv).toAlgebra
      letI : Module.Finite v.1.Completion w'.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v w'
      letI : IsGalois v.1.Completion w'.1.1.Completion :=
        infiniteHasseGalois K L v w'
      let e := infinite1Stabilizer
        (K := K) (L := L) v w'
      apply e.symm.injective
      simpa using hasse_global_units
        v.1.Completion w'.1.1.Completion (e.symm a)

/-- The denominator of the local Herbrand quotient in Proposition VII.2.7
is trivial. -/
theorem tate_neg_subsingleton
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (v : NumberFieldPlace K)
    (w : CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) :
    letI : Fintype (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute v) w) := Fintype.ofFinite _
    Subsingleton (tateNegOne
      (placeUnitsRepresentation
        (coinvariantsInvariantsAbsolute v) w)) := by
  let H := CompletionPlaceStabilizer
    (coinvariantsInvariantsAbsolute v) w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  let A := placeUnitsRepresentation
    (coinvariantsInvariantsAbsolute v) w
  let e₁ : tateNegOne A ≃+
      H1 (uliftIntegralRepresentation A) :=
    (tateULift A).trans
      (tateCohomologyNeg
        (uliftIntegralRepresentation A) g hg).toAddEquiv
  let e₂ : H1 (uliftIntegralRepresentation A) ≃+
      H1 (hasseUnitsRepresentation
        (coinvariantsInvariantsAbsolute v) w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 1).mapIso
      (uliftIsoHasse
        (K := K) (L := L)
        (coinvariantsInvariantsAbsolute v)
        w)).toLinearEquiv.toAddEquiv
  refine ⟨fun x y ↦ ?_⟩
  apply e₁.injective
  apply e₂.injective
  exact (units_h_1 v w (e₂ (e₁ x))).trans
    (units_h_1 v w (e₂ (e₁ y))).symm

/-- After Hilbert 90, the only local numerical input left in Proposition
VII.2.7 is the cardinality of Tate degree zero. -/
def TateCardinalityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (v : NumberFieldPlace K)
      (w : CompletionPlacesAbove (L := L)
        (coinvariantsInvariantsAbsolute v)),
      letI : Fintype (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute v) w) := Fintype.ofFinite _
      Finite (tateZero
          (placeUnitsRepresentation
            (coinvariantsInvariantsAbsolute v) w)) ∧
        Nat.card (tateZero
          (placeUnitsRepresentation
            (coinvariantsInvariantsAbsolute v) w)) =
          Nat.card (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute v) w)

/-- The local Herbrand bridge follows from its Tate-zero cardinality; its
Tate-minus-one group is already trivial by Hilbert 90. -/
theorem herbrand_bridge_cardinality
    (hzero : TateCardinalityBridge.{u}) :
    LocalHerbrandBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  intro v w
  let H := CompletionPlaceStabilizer (coinvariantsInvariantsAbsolute v) w
  letI : Fintype H := Fintype.ofFinite H
  let A := placeUnitsRepresentation
    (coinvariantsInvariantsAbsolute v) w
  obtain ⟨hfiniteZero, hcardZero⟩ := hzero K L v w
  letI : Finite (tateZero A) := hfiniteZero
  letI : Subsingleton (tateNegOne A) :=
    tate_neg_subsingleton v w
  letI : Finite (tateNegOne A) := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hcardNeg : Nat.card (tateNegOne A) = 1 :=
    Nat.card_unique
  rw [hcardZero, hcardNeg, Nat.cast_one, div_one]

end

end Submission.CField.BLoc
