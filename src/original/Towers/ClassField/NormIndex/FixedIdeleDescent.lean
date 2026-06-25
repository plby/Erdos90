import Towers.ClassField.NormIndex.CanonicalFixedMap
import Towers.ClassField.NormIndex.CompletionPlaceComparison

/-!
# Descent of fixed idèles

This file proves Proposition VII.2.5(a) for the concrete idèle action: an
idèle of `L` fixed by `Gal(L/K)` is the coordinatewise extension of a unique
idèle of `K`.
-/

namespace Towers.CField.NIndex

open AbsoluteValue Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option maxHeartbeats 1000000 in
-- The completed-field Galois structure and decomposition action elaborate
-- simultaneously in this fixed-field calculation.
set_option maxRecDepth 100000 in
omit [NumberField L] in
/-- An element of one completed factor fixed by its decomposition group lies
in the image of the completed base field. -/
theorem fixed_range_stabilizer
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (a : w.1.Completion)
    (hfixed : ∀ sigma : CompletionPlaceStabilizer v w,
      stabilizerRingHom v w sigma a = a) :
    ∃ b : v.Completion, completionLies v w.1 w.2 b = a := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (F := v.Completion) (E := w.1.Completion) a).2
  intro phi
  let stabilizerToDecomposition :
      CompletionPlaceStabilizer v w ≃*
        absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr
      (stabilizer_decomposition_group v w)
  let e : CompletionPlaceStabilizer v w ≃*
      Gal(w.1.Completion/v.Completion) :=
    stabilizerToDecomposition.trans
      (decompositionCompletionExtension v w.1)
  let sigma : CompletionPlaceStabilizer v w := e.symm phi
  have haction := stabilizer_decomposition_action
    (K := K) (L := L) v w sigma a
  have he : e sigma = phi := e.apply_symm_apply phi
  calc
    phi a = e sigma a := by rw [he]
    _ = stabilizerRingHom v w sigma a := by
      simpa [e, stabilizerToDecomposition] using haction.symm
    _ = a := hfixed sigma

set_option maxHeartbeats 1000000 in
-- The product action is reduced to the preceding decomposition-group
-- fixed-field statement.
set_option maxRecDepth 100000 in
omit [NumberField L] in
/-- A fixed family of completions descends at a distinguished coordinate to
the completed base field. -/
theorem completion_fixed_range
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (alpha : ∀ z : CompletionPlacesAbove (L := L) v, z.1.Completion)
    (hfixed : ∀ sigma : Gal(L/K),
      completionProductAction v sigma alpha = alpha) :
    ∃ b : v.Completion,
      completionLies v w.1 w.2 b = alpha w := by
  apply fixed_range_stabilizer
    (K := K) (L := L) v w (alpha w)
  intro sigma
  have hcoord := congrFun (hfixed sigma.1) w
  rwa [action_stabilizer_coordinate] at hcoord

set_option maxHeartbeats 1000000 in
-- The archimedean completion Galois instance and both stabilizer actions
-- unfold together in the fixed-field argument.
set_option maxRecDepth 100000 in
/-- A fixed infinite-adele coordinate descends to the corresponding
archimedean completion of the base field. -/
theorem infinite_adele_range
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : InfiniteAdeleRing L)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteAdeleAction (K := K) (L := L)).smul sigma x = x) :
    ∃ b : v.1.Completion,
      completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2) b = x w.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteCompletionGalois (K := K) (L := L) v w
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (F := v.1.Completion) (E := w.1.1.Completion) (x w.1)).2
  intro phi
  let stabilizerToDecomposition :
      InfinitePlaceStabilizer (K := K) (L := L) v w ≃*
        absoluteValueDecomposition v.1 w.1.1 :=
    MulEquiv.subgroupCongr
      (infinite_stabilizer_decomposition v w)
  let e : InfinitePlaceStabilizer (K := K) (L := L) v w ≃*
      Gal(w.1.1.Completion/v.1.Completion) :=
    stabilizerToDecomposition.trans
      (infiniteDecompositionGroup v w.1)
  let sigma : InfinitePlaceStabilizer (K := K) (L := L) v w := e.symm phi
  have hcoord := congrFun (hfixed sigma.1) w.1
  change numberInfiniteTransport (K := K) sigma.1 w.1
      (x (sigma.1⁻¹ • w.1)) = x w.1 at hcoord
  have hstab : infinitePlaceStabilizer v w sigma (x w.1) =
      x w.1 := by
    rw [infinite_stabilizer_pi]
    exact hcoord
  have haction := infinite_stabilizer_action
    (K := K) (L := L) v w sigma (x w.1)
  have he : e sigma = phi := e.apply_symm_apply phi
  calc
    phi (x w.1) = e sigma (x w.1) := by rw [he]
    _ = infinitePlaceStabilizer v w sigma (x w.1) := by
      simpa [e, stabilizerToDecomposition] using haction.symm
    _ = x w.1 := hstab

/-- Unit-valued form of archimedean fixed-coordinate descent. -/
theorem infinite_fixed_range
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    ∃ b : v.1.Completionˣ,
      Units.map (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toMonoidHom b =
        MulEquiv.piUnits x w.1 := by
  have hfixed_val (sigma : Gal(L/K)) :
      (infiniteAdeleAction (K := K) (L := L)).smul sigma
          (x : InfiniteAdeleRing L) = x :=
    congrArg Units.val (hfixed sigma)
  obtain ⟨b, hb⟩ := infinite_adele_range
    (K := K) (L := L) v w (x : InfiniteAdeleRing L) hfixed_val
  have hb0 : b ≠ 0 := by
    intro hbzero
    rw [hbzero, map_zero] at hb
    exact (MulEquiv.piUnits x w.1).ne_zero hb.symm
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  exact hb

private theorem ring_cast_pi
    {I : Type*} {R : I → Type*} [∀ i, Semiring (R i)]
    (x : ∀ i, R i) {i j : I} (h : i = j) :
    RingEquiv.cast h (x i) = x j := by
  subst j
  rfl

private theorem ring_cast_isometry
    {I : Type*} {R : I → Type*} [∀ i, Semiring (R i)]
    [∀ i, PseudoMetricSpace (R i)] {i j : I} (h : i = j) :
    Isometry (RingEquiv.cast (R := R) h) := by
  subst j
  exact isometry_id

set_option synthInstance.maxHeartbeats 300000 in
-- Comparing normalized and prime-adic completions synthesizes both valuation models.
/-- The comparison from a normalized finite completion to its prime-adic
model preserves the condition of lying in the valuation ring. -/
theorem place_ring_adic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : w.1.Completion) :
    ‖completionPlaceAdic (K := K) (L := L) P w z‖ ≤ 1 ↔
      ‖z‖ ≤ 1 := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  letI : IsUltrametricDist (FinitePlace.mk q).val.Completion :=
    placeUltrametricDist q
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q := by
    have hfiber := (upperAboveBase
      (K := K) (L := L) P).apply_symm_apply
        (placeAboveBase (K := K) (L := L) P w)
    exact congrArg Subtype.val hfiber |>.symm
  unfold completionPlaceAdic
  dsimp only [RingEquiv.trans_apply]
  rw [(ring_cast_isometry
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) ↦ R.adicCompletion L) hq).norm_map_of_map_zero
      (map_zero (RingEquiv.cast hq)),
    (place_adic_isometry q).norm_map_of_map_zero
      (map_zero (placeCompletionAdic
        q)),
    completion_ring_one]

set_option maxHeartbeats 1000000 in
-- The completed-field embedding comparison unfolds dependent valuation-ring maps.
set_option maxRecDepth 100000 in
/-- A finite completed-field embedding preserves and reflects the valuation
ring. -/
theorem factor_extension_ring
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (c : P.adicCompletion K) :
    ‖factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) c‖ ≤ 1 ↔ ‖c‖ ≤ 1 := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let d := eK.symm c
  have hmap :
      factorExtensionHom (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) c =
        eL (completionLies (FinitePlace.mk P).val w.1 w.2 d) := by
    calc
      _ = factorExtensionHom (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) (eK d) := by
        rw [eK.apply_symm_apply]
      _ = _ := RingHom.congr_fun
        (place_adic_algebra
          (K := K) (L := L) P w) d
  rw [hmap]
  calc
    ‖eL (completionLies (FinitePlace.mk P).val w.1 w.2 d)‖ ≤ 1 ↔
        ‖completionLies (FinitePlace.mk P).val w.1 w.2 d‖ ≤ 1 :=
      place_ring_adic
        (K := K) (L := L) P w _
    _ ↔ ‖d‖ ≤ 1 := by
      rw [(completion_lies_isometry
        (FinitePlace.mk P).val w.1 w.2).norm_map_of_map_zero
          (map_zero (completionLies
            (FinitePlace.mk P).val w.1 w.2))]
    _ ↔ ‖c‖ ≤ 1 := by
      rw [(adic_symm_isometry P).norm_map_of_map_zero
        (map_zero eK.symm)]

set_option maxRecDepth 100000 in
/-- The finite completed-field embedding reflects the distinguished local
unit subgroup. -/
theorem extension_reflects_subgroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (c : (P.adicCompletion K)ˣ)
    (hc : factorMonoidHom (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) c ∈
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L
        (upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w))) :
    c ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P := by
  change
    (factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) (c : P.adicCompletion K) ∈
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletionIntegers L) ∧
    (factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)
          ((c⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K) ∈
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletionIntegers L) at hc
  change ((c : P.adicCompletion K) ∈ P.adicCompletionIntegers K) ∧
    (((c⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K) ∈
      P.adicCompletionIntegers K)
  constructor
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    apply (factor_extension_ring
      (K := K) (L := L) P w (c : P.adicCompletion K)).1
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hc.1
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    apply (factor_extension_ring
      (K := K) (L := L) P w
        ((c⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K)).1
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hc.2

set_option maxHeartbeats 2000000 in
-- The finite-idèle coordinate action and the normalized-completion
-- stabilizer action contain several dependent prime casts.
set_option maxRecDepth 100000 in
/-- At a normalized finite place, a fixed finite idèle coordinate descends
to a unit of the corresponding prime-adic completion of the base field. -/
theorem fixed_centered_range
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    ∃ b : (P.adicCompletion K)ˣ,
      factorMonoidHom (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) b =
        x.1 (upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w)) := by
  letI := finitePrimeAction (K := K) (L := L)
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  let Q := placeUpperFactor (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let a : w.1.Completion := eL.symm (x.1 q : q.adicCompletion L)
  have ha : eL a = (x.1 q : q.adicCompletion L) := eL.apply_symm_apply _
  have ha_fixed (sigma : CompletionPlaceStabilizer v w) :
      stabilizerRingHom v w sigma a = a := by
    apply eL.injective
    rw [adic_stabilizer_transport]
    let hq : q = sigma.1⁻¹ • q :=
      centered_upper_stabilizer
        (K := K) (L := L) P w sigma
    have hcoordUnits := congrArg (fun y => y.1 q) (hfixed sigma.1)
    change Units.map
        (finitePlaceTransport (K := K) sigma.1 q).toRingHom.toMonoidHom
          (x.1 (sigma.1⁻¹ • q)) = x.1 q at hcoordUnits
    have hcoord := congrArg Units.val hcoordUnits
    calc
      finitePlaceTransport (K := K) sigma.1 q
          (RingEquiv.cast hq (eL a)) =
          finitePlaceTransport (K := K) sigma.1 q
            (x.1 (sigma.1⁻¹ • q) :
              (sigma.1⁻¹ • q).adicCompletion L) := by
        apply congrArg (finitePlaceTransport (K := K) sigma.1 q)
        rw [ha]
        exact ring_cast_pi
          (fun R => (x.1 R : R.adicCompletion L)) hq
      _ = (x.1 q : q.adicCompletion L) := hcoord
      _ = eL a := ha.symm
  obtain ⟨b, hb⟩ := fixed_range_stabilizer
    (K := K) (L := L) v w a ha_fixed
  have ha0 : a ≠ 0 := by
    intro hazero
    apply (x.1 q).ne_zero
    calc
      (x.1 q : q.adicCompletion L) = eL a := ha.symm
      _ = eL 0 := congrArg eL hazero
      _ = 0 := eL.map_zero
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply ha0
    calc
      a = completionLies v w.1 w.2 b := hb.symm
      _ = completionLies v w.1 w.2 0 :=
        congrArg (completionLies v w.1 w.2) hbzero
      _ = 0 := map_zero _
  have heKb0 : eK b ≠ 0 := by
    intro hzero
    apply hb0
    apply eK.injective
    exact hzero.trans eK.map_zero.symm
  let bUnit : (P.adicCompletion K)ˣ := Units.mk0 (eK b) heKb0
  refine ⟨bUnit, ?_⟩
  apply Units.ext
  change factorExtensionHom (K := K) (L := L) P Q (eK b) =
    (x.1 q : q.adicCompletion L)
  calc
    factorExtensionHom (K := K) (L := L) P Q (eK b) =
        eL (completionLies v w.1 w.2 b) :=
      RingHom.congr_fun
        (place_adic_algebra
          (K := K) (L := L) P w) b
    _ = eL a := congrArg eL hb
    _ = (x.1 q : q.adicCompletion L) := ha

/-- A distinguished normalized completion place above each finite base
prime. -/
private noncomputable def chosenCompletionPlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  exact Classical.choice
    (absolute_value_extension (K := K) (L := L) (FinitePlace.mk P).val)

/-- The literal upper prime centered at the distinguished completion place. -/
private noncomputable def chosenCenteredUpper
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) :=
  upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P
      (chosenCompletionPlace (K := K) (L := L) P))

private theorem chosen_centered_upper
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (chosenCenteredUpper (K := K) (L := L) P).under
        (NumberField.RingOfIntegers K) = P :=
  upperPrime_under (K := K) (L := L) P _

private theorem chosen_centered_injective :
    Function.Injective
      (chosenCenteredUpper (K := K) (L := L)) := by
  intro P R h
  calc
    P = (chosenCenteredUpper (K := K) (L := L) P).under
        (NumberField.RingOfIntegers K) :=
      (chosen_centered_upper (K := K) (L := L) P).symm
    _ = (chosenCenteredUpper (K := K) (L := L) R).under
        (NumberField.RingOfIntegers K) := congrArg
          (fun Q => Q.under (NumberField.RingOfIntegers K)) h
    _ = R := chosen_centered_upper (K := K) (L := L) R

/-- The descended finite coordinate selected at `P`. -/
private noncomputable def descendedFiniteCoordinate
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (P.adicCompletion K)ˣ :=
  Classical.choose (fixed_centered_range
    (K := K) (L := L) P
      (chosenCompletionPlace (K := K) (L := L) P) x hfixed)

set_option maxRecDepth 100000 in
private theorem descended_coordinate_chosen
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    factorMonoidHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P
          (chosenCompletionPlace (K := K) (L := L) P))
        (descendedFiniteCoordinate (K := K) (L := L) x hfixed P) =
      x.1 (chosenCenteredUpper (K := K) (L := L) P) :=
  Classical.choose_spec (fixed_centered_range
    (K := K) (L := L) P
      (chosenCompletionPlace (K := K) (L := L) P) x hfixed)

set_option maxHeartbeats 1000000 in
-- Return transport compares an arbitrary completion place with the
-- distinguished one while retaining all dependent prime casts.
set_option maxRecDepth 100000 in
private theorem descended_extension_place
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    factorMonoidHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w)
        (descendedFiniteCoordinate (K := K) (L := L) x hfixed P) =
      x.1 (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  let w₀ := chosenCompletionPlace (K := K) (L := L) P
  let Qw := placeUpperFactor (K := K) (L := L) P w
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let qw := upperPrime (K := K) (L := L) P Qw
  let q₀ := upperPrime (K := K) (L := L) P Q₀
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let hreturn : qw = r⁻¹ • q₀ :=
    centered_return_smul (K := K) (L := L) P w₀ w
  apply Units.ext
  apply (RingEquiv.cast
    (R := fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
      Q.adicCompletion L) hreturn).injective
  apply (finitePlaceTransport (K := K) r q₀).injective
  calc
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (factorExtensionHom (K := K) (L := L) P Qw
            (descendedFiniteCoordinate (K := K) (L := L) x hfixed P))) =
        factorExtensionHom (K := K) (L := L) P Q₀
          (descendedFiniteCoordinate (K := K) (L := L) x hfixed P) :=
      extension_return_transport
        (K := K) (L := L) P w₀ w _
    _ = (x.1 q₀ : q₀.adicCompletion L) :=
      congrArg Units.val
        (descended_coordinate_chosen
          (K := K) (L := L) x hfixed P)
    _ = finitePlaceTransport (K := K) r q₀
        (x.1 (r⁻¹ • q₀) : (r⁻¹ • q₀).adicCompletion L) := by
      have hcoordUnits := congrArg (fun y => y.1 q₀) (hfixed r)
      change Units.map
          (finitePlaceTransport (K := K) r q₀).toRingHom.toMonoidHom
            (x.1 (r⁻¹ • q₀)) = x.1 q₀ at hcoordUnits
      exact (congrArg Units.val hcoordUnits).symm
    _ = finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn (x.1 qw : qw.adicCompletion L)) := by
      apply congrArg (finitePlaceTransport (K := K) r q₀)
      exact (ring_cast_pi
        (fun Q => (x.1 Q : Q.adicCompletion L)) hreturn).symm

set_option maxRecDepth 100000 in
private theorem descended_extension_factor
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    factorMonoidHom (K := K) (L := L) P Q
        (descendedFiniteCoordinate (K := K) (L := L) x hfixed P) =
      x.1 (upperPrime (K := K) (L := L) P Q) := by
  let w := (placesAboveFactors
    (K := K) (L := L) P).symm Q
  have hw : placeUpperFactor
      (K := K) (L := L) P w = Q := by
    dsimp only [w]
    exact place_upper_symm
      (K := K) (L := L) P Q
  have h := descended_extension_place
    (K := K) (L := L) x hfixed P w
  rw [hw] at h
  exact h

private theorem units_cast_pi
    {I : Type*} {R : I → Type*} [∀ i, Semiring (R i)]
    (x : ∀ i, (R i)ˣ) {i j : I} (h : i = j) :
    Units.map (RingEquiv.cast h).toRingHom.toMonoidHom (x i) = x j := by
  subst j
  rfl

set_option maxHeartbeats 1000000 in
-- Rewriting a descended coordinate at a literal prime retains dependent prime casts.
set_option maxRecDepth 100000 in
private theorem descended_extension_literal
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    extensionMonoidHom (K := K) (L := L) Q
        (descendedFiniteCoordinate (K := K) (L := L) x hfixed
          (Q.under (NumberField.RingOfIntegers K))) = x.1 Q := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  have hq : upperPrime (K := K) (L := L) P q = Q :=
    upper_prime_factor (K := K) (L := L) Q
  rw [extension_monoid_hom]
  rw [descended_extension_factor
    (K := K) (L := L) x hfixed P q]
  exact units_cast_pi (fun R => x.1 R) hq

private theorem descended_eventually_unit
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    ∀ᶠ P in Filter.cofinite,
      descendedFiniteCoordinate (K := K) (L := L) x hfixed P ∈
        IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P := by
  have htendsto : Filter.Tendsto
      (chosenCenteredUpper (K := K) (L := L))
      Filter.cofinite Filter.cofinite :=
    (chosen_centered_injective
      (K := K) (L := L)).tendsto_cofinite
  have hx := htendsto.eventually x.2
  filter_upwards [hx] with P hP
  let w := chosenCompletionPlace (K := K) (L := L) P
  apply extension_reflects_subgroup
    (K := K) (L := L) P w
  rw [descended_coordinate_chosen
    (K := K) (L := L) x hfixed P]
  exact hP

/-- The finite idèle over `K` obtained from the descended local
coordinates. -/
private noncomputable def descendedFiniteIdele
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    FiniteIdeles (NumberField.RingOfIntegers K) K :=
  RestrictedProduct.mk
    (descendedFiniteCoordinate (K := K) (L := L) x hfixed)
    (descended_eventually_unit
      (K := K) (L := L) x hfixed)

set_option maxHeartbeats 1000000 in
-- Coordinatewise finite-idèle extension elaborates every restricted-product fiber.
set_option maxRecDepth 100000 in
/-- Coordinatewise extension of the descended finite idèle recovers the
original fixed finite idèle. -/
private theorem descended_idele_extension
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (hfixed : ∀ sigma : Gal(L/K),
      (finiteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    ideleMonoidHom (K := K) (L := L)
        (descendedFiniteIdele (K := K) (L := L) x hfixed) = x := by
  apply RestrictedProduct.ext
  intro Q
  change (ideleMonoidHom (K := K) (L := L)
      (descendedFiniteIdele (K := K) (L := L) x hfixed)).1 Q = x.1 Q
  rw [idele_monoid_hom]
  exact descended_extension_literal
    (K := K) (L := L) x hfixed Q

/-- A distinguished infinite place of `L` above each infinite place of
`K`. -/
private noncomputable def chosenInfiniteAbove (v : InfinitePlace K) :
    InfinitePlacesAbove (K := K) (L := L) v := by
  let w : InfinitePlace L :=
    Classical.choose (InfinitePlace.comap_surjective (K := L) v)
  exact ⟨w, Classical.choose_spec
    (InfinitePlace.comap_surjective (K := L) v)⟩

/-- The descended archimedean coordinate selected at `v`. -/
private noncomputable def descendedInfiniteCoordinate
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (v : InfinitePlace K) : v.1.Completionˣ :=
  Classical.choose (infinite_fixed_range
    (K := K) (L := L) v
      (chosenInfiniteAbove (K := K) (L := L) v) x hfixed)

private theorem descended_chosen_extension
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (v : InfinitePlace K) :
    Units.map (completionLies v.1
        (chosenInfiniteAbove (K := K) (L := L) v).1.1
        (infinite_lies_comap v
          (chosenInfiniteAbove (K := K) (L := L) v).1
          (chosenInfiniteAbove (K := K) (L := L) v).2)).toMonoidHom
        (descendedInfiniteCoordinate (K := K) (L := L) x hfixed v) =
      MulEquiv.piUnits x
        (chosenInfiniteAbove (K := K) (L := L) v).1 :=
  Classical.choose_spec (infinite_fixed_range
    (K := K) (L := L) v
      (chosenInfiniteAbove (K := K) (L := L) v) x hfixed)

/-- The infinite idèle over `K` assembled from its descended local
coordinates. -/
private noncomputable def descendedInfiniteIdele
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    (InfiniteAdeleRing K)ˣ :=
  MulEquiv.piUnits.symm
    (descendedInfiniteCoordinate (K := K) (L := L) x hfixed)

set_option maxHeartbeats 1000000 in
-- Archimedean descent compares dependent completion fibers and transport maps.
set_option maxRecDepth 100000 in
private theorem descended_infinite_place
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    Units.map (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toMonoidHom
        (descendedInfiniteCoordinate (K := K) (L := L) x hfixed v) =
      MulEquiv.piUnits x w.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  let w₀ := chosenInfiniteAbove (K := K) (L := L) v
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  apply Units.ext
  apply (infiniteReturnRing
    (K := K) (L := L) v w₀ w).injective
  calc
    infiniteReturnRing (K := K) (L := L) v w₀ w
        (completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2)
          (descendedInfiniteCoordinate (K := K) (L := L) x hfixed v)) =
        completionLies v.1 w₀.1.1
          (infinite_lies_comap v w₀.1 w₀.2)
          (descendedInfiniteCoordinate (K := K) (L := L) x hfixed v) :=
      infinite_return_extension
        (K := K) (L := L) v w₀ w _
    _ = (MulEquiv.piUnits x w₀.1 : w₀.1.1.Completion) :=
      congrArg Units.val
        (descended_chosen_extension
          (K := K) (L := L) x hfixed v)
    _ = infiniteReturnRing (K := K) (L := L) v w₀ w
        (MulEquiv.piUnits x w.1 : w.1.1.Completion) := by
      have hval := congrArg Units.val (hfixed r)
      have hcoord := congrFun hval w₀.1
      change numberInfiniteTransport (K := K) r w₀.1
          ((x : InfiniteAdeleRing L) (r⁻¹ • w₀.1)) =
        (x : InfiniteAdeleRing L) w₀.1 at hcoord
      change (x : InfiniteAdeleRing L) w₀.1 =
        infiniteReturnRing (K := K) (L := L) v w₀ w
          ((x : InfiniteAdeleRing L) w.1)
      rw [infinite_return_pi]
      exact hcoord.symm

set_option maxHeartbeats 1000000 in
-- Coordinatewise infinite-idèle extension unfolds the dependent product action.
set_option maxRecDepth 100000 in
/-- Coordinatewise extension of the descended infinite idèle recovers the
original fixed infinite idèle. -/
private theorem descended_infinite_extension
    (x : (InfiniteAdeleRing L)ˣ)
    (hfixed : ∀ sigma : Gal(L/K),
      (infiniteIdelesAction (K := K) (L := L)).smul sigma x = x) :
    infiniteMonoidHom (K := K) (L := L)
        (descendedInfiniteIdele (K := K) (L := L) x hfixed) = x := by
  apply Units.ext
  funext w
  let v := w.comap (algebraMap K L)
  let wAbove : InfinitePlacesAbove (K := K) (L := L) v := ⟨w, rfl⟩
  have h := descended_infinite_place
    (K := K) (L := L) x hfixed v wAbove
  have hval := congrArg Units.val h
  simpa only [descendedInfiniteIdele, MulEquiv.apply_symm_apply] using hval

set_option maxHeartbeats 1000000 in
-- The fixed-idèle equivalence packages both finite and infinite descent constructions.
set_option maxRecDepth 100000 in
/-- **Proposition VII.2.5(a).** Every idèle fixed by the concrete Galois
action is the coordinatewise extension of a base-field idèle. -/
theorem canonicalFixedDescent : CanonicalFixedDescent.{u} := by
  intro K L _ _ _ _ _ _ _ z hz
  have hinfinite (sigma : Gal(L/K)) :
      (infiniteIdelesAction (K := K) (L := L)).smul sigma z.1 = z.1 :=
    congrArg Prod.fst (hz sigma)
  have hfinite (sigma : Gal(L/K)) :
      (finiteIdelesAction (K := K) (L := L)).smul sigma z.2 = z.2 :=
    congrArg Prod.snd (hz sigma)
  let yInfinite := descendedInfiniteIdele
    (K := K) (L := L) z.1 hinfinite
  let yFinite := descendedFiniteIdele
    (K := K) (L := L) z.2 hfinite
  refine ⟨(yInfinite, yFinite), ?_⟩
  apply Prod.ext
  · exact descended_infinite_extension
      (K := K) (L := L) z.1 hinfinite
  · exact descended_idele_extension
      (K := K) (L := L) z.2 hfinite

set_option maxHeartbeats 1000000 in
-- Passing fixed-idèle descent to quotient classes unfolds nested quotient maps.
set_option maxRecDepth 100000 in
/-- The canonical class map is a bijection onto the Galois-fixed idèle
classes.  This is Lemma VII.4.1 for the concrete extension map. -/
theorem canonical_fixed_bijective :
    Function.Bijective
      (canonicalExtensionData (K := K) (L := L)).class_map_fixed := by
  let E := canonicalExtensionData (K := K) (L := L)
  constructor
  · apply (MonoidHom.ker_eq_bot_iff E.class_map_fixed).mp
    ext c
    constructor
    · intro hc
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
        (principalIdeles (NumberField.RingOfIntegers K) K) c
      have hc' := congrArg Subtype.val hc
      change E.classMap
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) x) = 1 at hc'
      rw [E.classMap_mk] at hc'
      apply Subgroup.mem_bot.mpr
      apply (QuotientGroup.eq_one_iff x).mpr
      rw [← canonical_principal_descent
        (K := K) (L := L)]
      exact (QuotientGroup.eq_one_iff (E.toMonoidHom x)).mp hc'
    · intro hc
      have hc' : c = 1 := Subgroup.mem_bot.mp hc
      subst c
      exact E.class_map_fixed.ker.one_mem
  · intro c
    obtain ⟨x, hx⟩ := canonical_fixed_lifting
      (K := K) (L := L) canonicalFixedDescent c
    exact ⟨QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers K) K) x, hx⟩

/-- **Lemma VII.4.1.** The canonical map identifies `C_K` with
`C_L^{Gal(L/K)}`. -/
theorem fixedDescentStatement :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      ∃ E : IEData (K := K) (L := L),
        Function.Bijective E.class_map_fixed := by
  intro K L _ _ _ _ _ _ _
  exact ⟨canonicalExtensionData (K := K) (L := L),
    canonical_fixed_bijective
      (K := K) (L := L)⟩

end

end Towers.CField.NIndex
