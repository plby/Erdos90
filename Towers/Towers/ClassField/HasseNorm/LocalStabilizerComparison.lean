import Towers.ClassField.HasseNorm.LocalComparison
import Towers.ClassField.Shifting.TransportAlongEquivalences

/-!
# Local Hasse norm cohomology and decomposition groups

The local norm comparison is naturally stated for the Galois group of a
completed extension.  The idèle decomposition instead uses the stabilizer of
the chosen global place.  This file transports degree-two cohomology between
those two presentations, including the universe lift of `ℤ` used by the
Hasse norm argument.

This is only the placewise comparison.  Proposition VII.2.5(b), which
assembles the completion products into the restricted idèle representation,
is a separate input.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The stabilizer of a place in the subtype of places above `v` is the
absolute-value decomposition group of its underlying absolute value. -/
theorem hasse_stabilizer_decomposition
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    CompletionPlaceStabilizer v w =
      absoluteValueDecomposition v w.1 := by
  rw [absolute_decomposition_stabilizer]
  ext sigma
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- The universe-resized representation on the units of one chosen
completion, with the action of its global place stabilizer. -/
noncomputable def hasseUnitsRepresentation
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    Rep (ULift.{u} ℤ) (CompletionPlaceStabilizer v w) := by
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ :=
    completionDistribAction v w
  exact uliftMulRepresentation
    (G := CompletionPlaceStabilizer v w) (M := w.1.Completionˣ)

section AbstractTransport

variable {F E H : Type u} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]
  [Group H] [MulDistribMulAction H Eˣ]

/-- Identity on completed units, regarded as a representation isomorphism
after the acting local Galois group has been relabelled by an equivalence. -/
noncomputable def hasseRestrictIso
    (e : H ≃* Gal(E/F))
    (hintertwines : ∀ h : H,
      (hasseGlobalRepresentation F E).ρ (e h) =
        (uliftMulRepresentation (G := H) (M := Eˣ)).ρ h) :
    Rep.res e.toMonoidHom (hasseGlobalRepresentation F E) ≅
      uliftMulRepresentation (G := H) (M := Eˣ) := by
  exact Rep.mkIso
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ) (Additive Eˣ)
      isIntertwining' := fun h => by
        simpa using hintertwines h }

/-- Degree-two cohomology is unchanged when the local Galois action on
completed units is rewritten as an equivalent stabilizer action. -/
noncomputable def hasseHMul
    (e : H ≃* Gal(E/F))
    (hintertwines : ∀ h : H,
      (hasseGlobalRepresentation F E).ρ (e h) =
        (uliftMulRepresentation (G := H) (M := Eˣ)).ρ h) :
    H2 (hasseGlobalRepresentation F E) ≃+
      H2 (uliftMulRepresentation (G := H) (M := Eˣ)) :=
  ((cohomologyMulIso e
      (hasseGlobalRepresentation F E) 2).trans
    ((groupCohomology.functor (ULift.{u} ℤ) H 2).mapIso
      (hasseRestrictIso e hintertwines))).toLinearEquiv.toAddEquiv

end AbstractTransport

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The two continuous actions of the decomposition group on the chosen
completion agree.  One is constructed in Chapter VII from the place
stabilizer; the other is the action underlying the local Galois group. -/
theorem stabilizer_decomposition_action
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w)
    (x : w.1.Completion) :
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    let d : absoluteValueDecomposition v w.1 :=
      MulEquiv.subgroupCongr
        (hasse_stabilizer_decomposition v w) sigma
    stabilizerRingHom v w sigma x =
      decompositionCompletionEquiv v w.1 d x := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  dsimp only
  let d : absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w) sigma
  have hfun :
      (fun y : w.1.Completion ↦
        stabilizerRingHom v w sigma y) =
      fun y ↦ decompositionCompletionEquiv v w.1 d y :=
    (dense_range_embedding w.1).equalizer
      (place_stabilizer_isometry v w sigma).continuous
      (decomposition_alg_continuous v w.1 d)
      (funext fun y => by
        change stabilizerRingHom v w sigma
            (completionEmbedding w.1 y) =
          decompositionCompletionEquiv v w.1 d
            (completionEmbedding w.1 y)
        rw [place_stabilizer_embedding,
          decomposition_alg_embedding]
        rfl)
  exact congrFun hfun x

set_option synthInstance.maxHeartbeats 500000 in
-- The completion Galois and two cohomology representations elaborate together.
set_option maxHeartbeats 4000000 in
/-- At a nonarchimedean place, the `ULift ℤ` local-completion cohomology is
the cohomology of the same completed units under the chosen global place
stabilizer. -/
noncomputable def h2Stabilizer
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
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    H2 (hasseGlobalRepresentation
        v.Completion w.1.Completion) ≃+
      H2 (hasseUnitsRepresentation v w) := by
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
    placeCompletionDimensional v w
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
  exact hasseHMul e hintertwines

set_option synthInstance.maxHeartbeats 500000 in
-- The archimedean completion and two cohomology representations elaborate together.
set_option maxHeartbeats 4000000 in
/-- The archimedean analogue of
`h2Stabilizer`. -/
noncomputable def infiniteHStabilizer
    (v : InfinitePlace K)
    (w : Ideles.InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      Ideles.infinite_completion_module
        (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    H2 (hasseGlobalRepresentation
        v.1.Completion w.1.1.Completion) ≃+
      H2 (hasseUnitsRepresentation v.1 w0) := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    Ideles.infinite_completion_module
      (K := K) (L := L) v w
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
  exact hasseHMul e hintertwines

/-- The literal finite local norm quotient, now expressed as degree-two
cohomology for the global decomposition group at the chosen completion. -/
noncomputable def hasseStabilizer2
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let Q := completion.finiteUpper P
    let model := hasseCompletionModel K L P Q
    Additive (HasseLocalQuotient completion (.inl P)) ≃+
      H2 (hasseUnitsRepresentation
        (FinitePlace.mk P).val model.place) := by
  let Q := completion.finiteUpper P
  let model := hasseCompletionModel K L P Q
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  exact (hasseH2
      K L hcyclic completion P).trans
    (h2Stabilizer
      (K := K) (L := L) (FinitePlace.mk P).val model.place
      (fun x y => (FinitePlace.mk P).add_le x y))

/-- The literal infinite local norm quotient, expressed as degree-two
cohomology for the corresponding global decomposition group. -/
noncomputable def infiniteHasseStabilizer
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K) :
    let w := completion.infiniteUpper v
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    Additive (HasseLocalQuotient completion (.inr v)) ≃+
      H2 (hasseUnitsRepresentation v.1 w0) := by
  let w := completion.infiniteUpper v
  exact (infiniteHasse2
      K L hcyclic completion v).trans
    (infiniteHStabilizer
      (K := K) (L := L) v w)

end

end Towers.CField.HNorm
