import Submission.ClassField.BrauerLocalization.KernelLiftingAssembly
import Submission.ClassField.BrauerLocalization.LocalKernelVanishing
import Submission.ClassField.BrauerLocalization.CardinalityDirect
import Submission.ClassField.CyclotomicBrauer.RationalBaseChange
import Submission.ClassField.HasseNorm.FinitePlaceBridge

/-!
# Finite support and completion choices for the killing extension

This file connects the actual finite support of a local Brauer tuple with the
local-degree witnesses produced by Lemma VII.7.3.  Its main construction
turns the selected normalized completion places in
`LocalDegreesDvd` into one `HasseCompletionData`, without
changing the selected places on the finite support.
-/

namespace Submission.CField.BLoc

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.LFTheory
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.ICohomo
open Submission.CField.CIdeles
open Submission.CField.CBrauer
open Submission.CField.RExist
open Submission.CField.HNorm
open Submission.CField.GClass

noncomputable section

universe u

/-- The finite primes occurring in the support of an absolute local Brauer
tuple. -/
noncomputable def finitePlaceSupport
    (K : Type u) [Field K] [NumberField K]
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))) :
    Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  exact y.support.biUnion fun
    | .inl P => {P}
    | .inr _ => ∅

@[simp]
theorem finite_place_support
    (K : Type u) [Field K] [NumberField K]
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    P ∈ finitePlaceSupport K y ↔
      y (.inl P) ≠ 0 := by
  classical
  simp [finitePlaceSupport, DFinsupp.mem_support_toFun]

/-- A finite coordinate outside the extracted support is zero. -/
theorem coordinate_not_support
    (K : Type u) [Field K] [NumberField K]
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : P ∉ finitePlaceSupport K y) :
    y (.inl P) = 0 := by
  by_contra hne
  apply hP
  exact (finite_place_support K y P).2 hne

/-- Completion data which remembers the particular finite completion places
selected on `S`, together with their degree divisibilities. -/
structure FiniteCompletionSelection
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (finitePrime K)) (m : ℕ) where
  completion : HasseCompletionData K L
  selected : ∀ P : S,
    CompletionPlacesAbove (L := L) (FinitePlace.mk P.1).val
  chosen_eq_selected : ∀ P : S,
    hasseChosenPlace completion (.inl P.1) = selected P
  degree_dvd : ∀ P : S,
    letI : Algebra (FinitePlace.mk P.1).val.Completion
        (selected P).1.Completion :=
      (completionLies
        (FinitePlace.mk P.1).val (selected P).1 (selected P).2).toAlgebra
    m ∣ Module.finrank
      (FinitePlace.mk P.1).val.Completion (selected P).1.Completion

/-- Convert the completion-place witnesses in
`LocalDegreesDvd` into a simultaneous `HasseCompletionData`.
Outside `S` arbitrary prolongations are retained. -/
theorem finite_completion_selection
    (K : Type u) [Field K] [NumberField K]
    (data : FEData K)
    (S : Finset (finitePrime K)) (m : ℕ)
    (hdegrees : data.LocalDegreesDvd S m) :
    letI : Field data.L := data.fieldL
    letI : NumberField data.L := data.numberFieldL
    letI : Algebra K data.L := data.algebraKL
    letI : FiniteDimensional K data.L := data.finiteDimensionalKL
    letI : IsGalois K data.L := data.isGaloisKL
    Nonempty (FiniteCompletionSelection K data.L S m) := by
  classical
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  obtain ⟨selected, hdegree⟩ := hdegrees
  let default : HasseCompletionData K data.L :=
    Classical.choice (hasseExistenceBridge K data.L)
  let completion : HasseCompletionData K data.L :=
    { finiteUpper := fun P =>
        if hP : P ∈ S then
          placesAboveFactors
            (K := K) (L := data.L) P (selected ⟨P, hP⟩)
        else default.finiteUpper P
      infiniteUpper := default.infiniteUpper }
  have hchosen : ∀ P : S,
      hasseChosenPlace completion (.inl P.1) = selected P := by
    intro P
    change (placesAboveFactors
        (K := K) (L := data.L) P.1).symm
        (completion.finiteUpper P.1) = selected P
    simp [completion, P.2]
  refine ⟨{
    completion := completion
    selected := selected
    chosen_eq_selected := hchosen
    degree_dvd := hdegree }⟩

/-- The spectral local-invariant base-change formula at one selected finite
completion, with all local-field structures installed internally. -/
def SelectedSpectralFormula
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {S : Finset (finitePrime K)} {m : ℕ}
    (selection : FiniteCompletionSelection K L S m)
    (P : S) : Prop :=
  let v := (FinitePlace.mk P.1).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P.1⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P.1
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P.1
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P.1
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P.1
  letI : Algebra v.Completion (selection.selected P).1.Completion :=
    (completionLies v
      (selection.selected P).1 (selection.selected P).2).toAlgebra
  letI : FiniteDimensional v.Completion
      (selection.selected P).1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional
      v (selection.selected P)
  SpectralChangeFormula
    v.Completion (selection.selected P).1.Completion

/-- At a selected supported finite prime, the spectral local invariant
base-change formula and the degree supplied by Lemma VII.7.3 kill the local
Brauer coordinate. -/
theorem selected_base_change
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (selection : FiniteCompletionSelection K L
      (finitePlaceSupport K y)
      (localInvariantAnnihilator K data y))
    (P : finitePlaceSupport K y)
    (hbaseChange : SelectedSpectralFormula selection P) :
    letI : Algebra (FinitePlace.mk P.1).val.Completion
        (selection.selected P).1.Completion :=
      (completionLies (FinitePlace.mk P.1).val
        (selection.selected P).1 (selection.selected P).2).toAlgebra
    brauerBaseChange (FinitePlace.mk P.1).val.Completion
      (selection.selected P).1.Completion (y (.inl P.1)).toMul = 1 := by
  let v := (FinitePlace.mk P.1).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P.1⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P.1
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P.1
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P.1
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P.1
  letI : Algebra v.Completion (selection.selected P).1.Completion :=
    (completionLies v
      (selection.selected P).1 (selection.selected P).2).toAlgebra
  letI : FiniteDimensional v.Completion
      (selection.selected P).1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional
      v (selection.selected P)
  change SpectralChangeFormula
    v.Completion (selection.selected P).1.Completion at hbaseChange
  have hannihilate : localInvariantAnnihilator K data y •
      (carryBrauerInvariant v.Completion
        (y (.inl P.1)).toMul).toAdd = 0 := by
    simpa only [finitePlaceInvariant] using
      invariant_annihilator_nsmul K data y P.1
  exact
    brauer_spectral_nsmul
      v.Completion (selection.selected P).1.Completion hbaseChange
      (y (.inl P.1)) (localInvariantAnnihilator K data y)
      hannihilate (selection.degree_dvd P)

set_option synthInstance.maxHeartbeats 500000 in
-- The completion Galois structure and the direct local cardinality comparison
-- elaborate through several dependent completion-place equivalences.
set_option maxHeartbeats 5000000 in
/-- The supported finite coordinate vanishes without the full invariant
base-change formula: the direct local Herbrand calculation gives the relative
Brauer cardinality, so degree-torsion of the invariant already characterizes
the scalar-extension kernel. -/
theorem selected_change_direct
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (selection : FiniteCompletionSelection K L
      (finitePlaceSupport K y)
      (localInvariantAnnihilator K data y))
    (P : finitePlaceSupport K y) :
    letI : Algebra (FinitePlace.mk P.1).val.Completion
        (selection.selected P).1.Completion :=
      (completionLies (FinitePlace.mk P.1).val
        (selection.selected P).1 (selection.selected P).2).toAlgebra
    brauerBaseChange (FinitePlace.mk P.1).val.Completion
      (selection.selected P).1.Completion (y (.inl P.1)).toMul = 1 := by
  let v := (FinitePlace.mk P.1).val
  let w := selection.selected P
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P.1⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P.1
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P.1
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P.1
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P.1
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P.1
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  have hcard : Nat.card
      (relativeBrauerGroup v.Completion w.1.Completion) =
        Module.finrank v.Completion w.1.Completion :=
    relative_brauer_direct P.1 w
  have hannihilate : localInvariantAnnihilator K data y •
      (carryBrauerInvariant v.Completion
        (y (.inl P.1)).toMul).toAdd = 0 := by
    simpa only [finitePlaceInvariant] using
      invariant_annihilator_nsmul K data y P.1
  exact
    brauer_nsmul_cardinality
      v.Completion w.1.Completion hcard (y (.inl P.1))
      (localInvariantAnnihilator K data y) hannihilate
      (selection.degree_dvd P)

/-- Triviality of Brauer scalar extension transports along equality of two
chosen completion places.  Abstracting both places makes the dependent
elimination transparent. -/
theorem brauer_change_place
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (v : AbsoluteValue k ℝ)
    (w w' : CompletionPlacesAbove (L := L) v)
    (hww' : w = w') (x : BrauerGroup v.Completion)
    (hx :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      brauerBaseChange v.Completion w.1.Completion x = 1) :
    letI : Algebra v.Completion w'.1.Completion :=
      (completionLies v w'.1 w'.2).toAlgebra
    brauerBaseChange v.Completion w'.1.Completion x = 1 := by
  subst w'
  exact hx

/-- The selected finite-place vanishing transported to the literal
chosen-completion map used by `KillingExtension`. -/
theorem chosen_base_change
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (selection : FiniteCompletionSelection K L
      (finitePlaceSupport K y)
      (localInvariantAnnihilator K data y))
    (P : finitePlaceSupport K y)
    (hbaseChange : SelectedSpectralFormula selection P) :
    brauerLiftingChange K L selection.completion (.inl P.1)
      (y (.inl P.1)).toMul = 1 := by
  have hselected := selected_base_change
    K L data y selection P hbaseChange
  have hchosen := brauer_change_place
    (FinitePlace.mk P.1).val (selection.selected P)
    (hasseChosenPlace selection.completion (.inl P.1))
    (selection.chosen_eq_selected P).symm (y (.inl P.1)).toMul hselected
  simpa only [brauerLiftingChange,
    chosenCompletionExtension, chosenCompletionAlgebra] using hchosen

/-- Direct-cardinality version of the supported finite-place vanishing,
transported to the literal chosen completion used by the killing extension. -/
theorem chosen_change_direct
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (selection : FiniteCompletionSelection K L
      (finitePlaceSupport K y)
      (localInvariantAnnihilator K data y))
    (P : finitePlaceSupport K y) :
    brauerLiftingChange K L selection.completion (.inl P.1)
      (y (.inl P.1)).toMul = 1 := by
  have hselected := selected_change_direct
    K L data y selection P
  have hchosen := brauer_change_place
    (FinitePlace.mk P.1).val (selection.selected P)
    (hasseChosenPlace selection.completion (.inl P.1))
    (selection.chosen_eq_selected P).symm (y (.inl P.1)).toMul hselected
  simpa only [brauerLiftingChange,
    chosenCompletionExtension, chosenCompletionAlgebra] using hchosen

/-- If the selected global extension is totally complex, scalar extension to
every chosen upper infinite completion kills every local Brauer class. -/
theorem change_totally_complex
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [NumberField.IsTotallyComplex L]
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K)
    (x : BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) :
    brauerLiftingChange K L completion (.inr v) x = 1 := by
  let w := completion.infiniteUpper v
  have hwcomplex : InfinitePlace.IsComplex w.1 :=
    NumberField.IsTotallyComplex.isComplex w.1
  letI : IsAlgClosed w.1.1.Completion :=
    alg_closed_ring
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwcomplex).symm
  letI : Subsingleton
      (BrauerGroup (chosenCompletionExtension K L completion (.inr v))) := by
    change Subsingleton (BrauerGroup w.1.1.Completion)
    exact brauer_subsingleton_closed w.1.1.Completion
  exact Subsingleton.elim _ _

/-- The remaining finite arithmetic input: spectral local-invariant base
change for every completion selected in the tailored-extension argument. -/
def FiniteSpectralChange : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (finitePrime K)) (m : ℕ)
    (selection : FiniteCompletionSelection K L S m)
    (P : S),
    SelectedSpectralFormula selection P

/-- Lemma VII.7.3 and finite spectral local-invariant base change construct
the complete coordinate-killing extension required by VIII.4.2. -/
theorem killing_construction_change
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u}) :
    KillingExtension.{u} := by
  intro K _ _ data y _hy
  let S := finitePlaceSupport K y
  let m := localInvariantAnnihilator K data y
  have hm : 0 < m := invariant_annihilator_pos K data y
  obtain ⟨extension, hcyclicCyclotomic, htotallyComplex, hdegrees⟩ :=
    h73 K S m hm
  letI : Field extension.L := extension.fieldL
  letI : NumberField extension.L := extension.numberFieldL
  letI : Algebra K extension.L := extension.algebraKL
  letI : FiniteDimensional K extension.L := extension.finiteDimensionalKL
  letI : IsGalois K extension.L := extension.isGaloisKL
  have hcyclic : IsCyclic Gal(extension.L/K) := hcyclicCyclotomic.1
  letI : IsCyclic Gal(extension.L/K) := hcyclic
  letI : NumberField.IsTotallyComplex extension.L := htotallyComplex
  obtain ⟨selection⟩ :=
    finite_completion_selection K extension S m hdegrees
  refine ⟨extension.L, extension.fieldL, extension.numberFieldL,
    extension.algebraKL, extension.finiteDimensionalKL,
    extension.isGaloisKL, hcyclic, selection.completion, ?_⟩
  intro place
  cases place with
  | inl P =>
      by_cases hP : P ∈ S
      · let Ps : S := ⟨P, hP⟩
        exact chosen_base_change
          K extension.L data y selection Ps
            (hbaseChange K extension.L S m selection Ps)
      · have hyP : y (.inl P) = 0 :=
          coordinate_not_support K y P hP
        rw [hyP]
        change brauerLiftingChange K extension.L
          selection.completion (.inl P) 1 = 1
        exact (brauerLiftingChange K extension.L
          selection.completion (.inl P)).map_one
  | inr v =>
      exact change_totally_complex
        K extension.L selection.completion v (y (.inr v)).toMul

/-- Lemma VII.7.3 alone constructs the complete killing extension.  At
finite places the direct Herbrand cardinality replaces the stronger local
invariant base-change formula; the infinite branch is unchanged. -/
theorem killing_cyclotomic_construction
    (h73 : FinitePrime.{u}) :
    KillingExtension.{u} := by
  intro K _ _ data y _hy
  let S := finitePlaceSupport K y
  let m := localInvariantAnnihilator K data y
  have hm : 0 < m := invariant_annihilator_pos K data y
  obtain ⟨extension, hcyclicCyclotomic, htotallyComplex, hdegrees⟩ :=
    h73 K S m hm
  letI : Field extension.L := extension.fieldL
  letI : NumberField extension.L := extension.numberFieldL
  letI : Algebra K extension.L := extension.algebraKL
  letI : FiniteDimensional K extension.L := extension.finiteDimensionalKL
  letI : IsGalois K extension.L := extension.isGaloisKL
  have hcyclic : IsCyclic Gal(extension.L/K) := hcyclicCyclotomic.1
  letI : IsCyclic Gal(extension.L/K) := hcyclic
  letI : NumberField.IsTotallyComplex extension.L := htotallyComplex
  obtain ⟨selection⟩ :=
    finite_completion_selection K extension S m hdegrees
  refine ⟨extension.L, extension.fieldL, extension.numberFieldL,
    extension.algebraKL, extension.finiteDimensionalKL,
    extension.isGaloisKL, hcyclic, selection.completion, ?_⟩
  intro place
  cases place with
  | inl P =>
      by_cases hP : P ∈ S
      · let Ps : S := ⟨P, hP⟩
        exact chosen_change_direct
          K extension.L data y selection Ps
      · have hyP : y (.inl P) = 0 :=
          coordinate_not_support K y P hP
        rw [hyP]
        change brauerLiftingChange K extension.L
          selection.completion (.inl P) 1 = 1
        exact (brauerLiftingChange K extension.L
          selection.completion (.inl P)).map_one
  | inr v =>
      exact change_totally_complex
        K extension.L selection.completion v (y (.inr v)).toMul

/-- The absolute killing extension used in VIII.4.2 is unconditional after
the completed proof of Lemma VII.7.3. -/
theorem killingExtension : KillingExtension.{u} :=
  killing_cyclotomic_construction rationalBaseChange

/-- Final VIII.4.2 route with the killing-extension input expanded into
Lemma VII.7.3 and finite spectral local-invariant base change. -/
theorem killing_selection_arithmetic
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hrelative : RelativeBrauerLifting.{u}) :
    GlobalLocalizationSequence.{u} :=
  lifting_assembly_components h51 hArtin h81
    (killing_construction_change
      h73 hbaseChange)
    hrelative

/-- Expanded arithmetic endpoint after removing the unnecessary finite
spectral-base-change hypothesis from the killing-extension construction. -/
theorem killing_selection_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hrelative : RelativeBrauerLifting.{u}) :
    GlobalLocalizationSequence.{u} :=
  lifting_assembly_components h51 hArtin h81
    (killing_cyclotomic_construction h73) hrelative

/-- Lemma VII.7.3 already supplies a totally complex cyclic cyclotomic
extension together with a compatible simultaneous completion selection on
the prescribed finite support. -/
def TailoredExtensionSelection : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K)) (m : ℕ),
    0 < m →
      ∃ data : FEData K,
        data.IsCyclicCyclotomic ∧ data.IsTotallyComplex ∧
          letI : Field data.L := data.fieldL
          letI : NumberField data.L := data.numberFieldL
          letI : Algebra K data.L := data.algebraKL
          letI : FiniteDimensional K data.L := data.finiteDimensionalKL
          letI : IsGalois K data.L := data.isGaloisKL
          Nonempty (FiniteCompletionSelection K data.L S m)

theorem tailored_selection_construction
    (h73 : FinitePrime.{u}) :
    TailoredExtensionSelection.{u} := by
  intro K _ _ S m hm
  obtain ⟨data, hcyclic, hcomplex, hdegrees⟩ := h73 K S m hm
  refine ⟨data, hcyclic, hcomplex, ?_⟩
  exact finite_completion_selection K data S m hdegrees

/-- Unconditional tailored completion selection supplied by Lemma VII.7.3. -/
theorem tailoredExtensionSelection :
    TailoredExtensionSelection.{u} :=
  tailored_selection_construction rationalBaseChange

end

end Submission.CField.BLoc
