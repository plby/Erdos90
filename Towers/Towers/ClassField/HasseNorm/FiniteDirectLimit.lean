import Towers.ClassField.HasseNorm.ExceptionalDirectSum
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The finite-place idèle-stage direct limit

We fix one finite set containing every ramified finite base prime and enlarge
it by arbitrary finite sets of places.  The resulting system is cofinal in
the finite idèle stages, and all local-unit factors outside every stage have
trivial degree-two cohomology.

The maps in this file are the actual maps induced by inclusion of the
finite-stage representations.  Their exceptional-coordinate descriptions
are compatible with extension by zero.  Taking the direct limit therefore
identifies the finite-place degree-two cohomology with the direct sum of the
unrestricted finite completion-orbit cohomology groups.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
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

local instance finiteStageLimitNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) :=
  Classical.decEq _

/-- Inclusion of one finite-prime orbit stage into a larger stage. -/
noncomputable def stageOrbitInclusion
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IdeleStageOrbit (K := K) (L := L) S P →*
      IdeleStageOrbit (K := K) (L := L) T P where
  toFun x := ⟨x.1, fun Q hPT => x.2 Q (fun hPS => hPT (hST hPS))⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the equivariant inclusion between dependent orbit products
-- requires a larger normalization budget.
set_option synthInstance.maxHeartbeats 300000 in
/-- The equivariant resized representation morphism induced by inclusion of
one finite-prime orbit stage into a larger stage. -/
noncomputable def stageOrbitTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    stageOrbitRepresentation (K := K) (L := L) S P ⟶
      stageOrbitRepresentation (K := K) (L := L) T P := by
  apply Rep.ofHom
  let f := stageOrbitInclusion (K := K) (L := L) hST P
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (f x.toMul)
          map_add' := fun x y => congrArg Additive.ofMul (f.map_mul x.toMul y.toMul)
          map_smul' := fun r x => map_zsmul f.toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

set_option maxHeartbeats 1000000 in
-- The pointwise stage inclusion expands a dependent family of finite-prime
-- orbit maps.
set_option synthInstance.maxHeartbeats 300000 in
/-- Inclusion of the pointwise product of all finite-prime stage orbits. -/
noncomputable def ideleStageInclusion
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      IdeleStageOrbit (K := K) (L := L) S P) →*
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        IdeleStageOrbit (K := K) (L := L) T P) where
  toFun x P := stageOrbitInclusion (K := K) (L := L) hST P (x P)
  map_one' := by funext P; rfl
  map_mul' := fun _ _ => by funext P; rfl

set_option maxHeartbeats 1000000 in
-- Packaging the stage inclusion as a representation morphism resolves a
-- large dependent action-compatibility term.
set_option synthInstance.maxHeartbeats 300000 in
/-- The actual resized representation morphism between finite-stage product
representations. -/
noncomputable def ideleStageTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    resizedStageRepresentation (K := K) (L := L) S ⟶
      resizedStageRepresentation (K := K) (L := L) T := by
  apply Rep.ofHom
  let f := ideleStageInclusion (K := K) (L := L) hST
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (f x.toMul)
          map_add' := fun x y => congrArg Additive.ofMul (f.map_mul x.toMul y.toMul)
          map_smul' := fun r x => map_zsmul f.toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  funext P
  apply Subtype.ext
  rfl

set_option maxHeartbeats 1000000 in
-- Evaluation at one base prime unfolds the categorical product and resized
-- representation equivalences.
set_option synthInstance.maxHeartbeats 300000 in
/-- Evaluation of the pointwise product representation at one finite base
prime. -/
noncomputable def resizedStageEvaluation
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedStageRepresentation (K := K) (L := L) S ⟶
      stageOrbitRepresentation (K := K) (L := L) S P := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (x.toMul P)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

omit [FiniteDimensional K L] in
/-- Evaluation commutes with enlargement of a finite idèle stage. -/
theorem resized_stage_evaluation
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ideleStageTransition (K := K) (L := L) hST ≫
        resizedStageEvaluation (K := K) (L := L) T P =
      resizedStageEvaluation (K := K) (L := L) S P ≫
        stageOrbitTransition (K := K) (L := L) hST P := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- The canonical coordinate map on degree-two cohomology of a pointwise
finite-stage product. -/
noncomputable def stageHPi
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedStageRepresentation (K := K) (L := L) S) →+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H2 (stageOrbitRepresentation
          (K := K) (L := L) S P)) where
  toFun q P := groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedStageEvaluation (K := K) (L := L) S P) 2 q
  map_zero' := by
    funext P
    exact map_zero _
  map_add' x y := by
    funext P
    exact map_add _ x y

omit [FiniteDimensional K L] in
/-- Every family of orbit-valued degree-two classes is represented by one
cocycle with values in the pointwise stage product. -/
theorem resized_stage_surjective
    (S : Finset (NumberFieldPlace K)) :
    Function.Surjective
      (stageHPi (K := K) (L := L) S) := by
  intro q
  have hrepresentative
      (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      ∃ xP : cocycles₂ (stageOrbitRepresentation
          (K := K) (L := L) S P),
        H2π _ xP = q P := by
    induction q P using H2_induction_on with
    | h xP => exact ⟨xP, rfl⟩
  choose x hx using hrepresentative
  let zFun : Gal(L/K) × Gal(L/K) →
      resizedStageRepresentation (K := K) (L := L) S :=
    fun gh => Additive.ofMul (fun P => (x P gh).toMul)
  have hz : zFun ∈ cocycles₂
      (resizedStageRepresentation
        (K := K) (L := L) S) := by
    apply (mem_cocycles₂_iff zFun).2
    intro g h j
    apply Additive.toMul.injective
    funext P
    exact congrArg Additive.toMul
      ((mem_cocycles₂_iff (x P)).1 (x P).2 g h j)
  let z : cocycles₂ (resizedStageRepresentation
      (K := K) (L := L) S) := ⟨zFun, hz⟩
  refine ⟨H2π _ z, ?_⟩
  funext P
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedStageEvaluation (K := K) (L := L) S P) 2
        (H2π _ z) = q P
  rw [H2π_comp_map_apply]
  rw [← hx P]
  congr 1

omit [FiniteDimensional K L] in
/-- The canonical coordinate map on degree-two cohomology of the pointwise
stage product is injective. -/
theorem resized_stage_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (stageHPi (K := K) (L := L) S) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hcoord : stageHPi
      (K := K) (L := L) S (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  clear hqq'
  have hkernel (r : H2 (resizedStageRepresentation
      (K := K) (L := L) S))
      (hr : stageHPi
        (K := K) (L := L) S r = 0) : r = 0 := by
    induction r using H2_induction_on with
    | h z =>
      have hzero (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
          H2π (stageOrbitRepresentation
              (K := K) (L := L) S P)
            (mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedStageEvaluation
                (K := K) (L := L) S P) z) = 0 := by
        rw [← H2π_comp_map_apply]
        exact congrFun hr P
      have hwitness (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
          ∃ aP : Gal(L/K) →
              stageOrbitRepresentation
                (K := K) (L := L) S P,
            d₁₂ _ aP = mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedStageEvaluation
                (K := K) (L := L) S P) z := by
        exact (H2π_eq_zero_iff _).1 (hzero P)
      choose a ha using hwitness
      let aProduct : Gal(L/K) →
          resizedStageRepresentation
            (K := K) (L := L) S :=
        fun g => Additive.ofMul (fun P => (a P g).toMul)
      apply (H2π_eq_zero_iff z).2
      refine ⟨aProduct, ?_⟩
      funext gh
      apply Additive.toMul.injective
      funext P
      have haP := congrFun (ha P) gh
      change
        (stageOrbitRepresentation
          (K := K) (L := L) S P).ρ gh.1 (a P gh.2) -
            a P (gh.1 * gh.2) + a P gh.1 =
          Additive.ofMul ((z gh).toMul P) at haP
      exact congrArg Additive.toMul haP
  exact hkernel (q - q') hcoord

/-- The canonical degree-two coordinate map for a finite-stage product is
an additive equivalence. -/
noncomputable def resizedStagePi
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedStageRepresentation (K := K) (L := L) S) ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H2 (stageOrbitRepresentation
          (K := K) (L := L) S P)) :=
  AddEquiv.ofBijective
    (stageHPi (K := K) (L := L) S)
    ⟨resized_stage_injective (K := K) (L := L) S,
     resized_stage_surjective (K := K) (L := L) S⟩

/-- A fixed finite stage containing all ramified finite base primes. -/
noncomputable def unramifiedBaseStage (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Finset (NumberFieldPlace K) :=
  Classical.choose (stage_unramified_outside
    (K := K) (L := L))

/-- Every upper prime outside the fixed base stage is unramified. -/
theorem unramified_stage_spec
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉
      unramifiedBaseStage K L)
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
      (upperPrime (K := K) (L := L) P Q).asIdeal :=
  Classical.choose_spec (stage_unramified_outside
    (K := K) (L := L)) P hP Q

/-- The cofinal finite stage indexed by `T` is the union of the fixed
ramification-containing stage and `T`. -/
abbrev cofinalIdeleStage (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (NumberFieldPlace K)) : Finset (NumberFieldPlace K) :=
  unramifiedBaseStage K L ∪ T

/-- Enlarging the auxiliary finite set enlarges its cofinal stage. -/
theorem cofinal_stage_mono
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U) :
    cofinalIdeleStage K L T ⊆ cofinalIdeleStage K L U := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ hv
  · exact Finset.mem_union_right _ (hTU hv)

/-- Outside every cofinal stage, the stage-orbit degree-two cohomology is
trivial. -/
theorem cofinal_h_subsingleton
    (T : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉
      cofinalIdeleStage K L T) :
    Subsingleton
      (H2 (stageOrbitRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T) P)) := by
  apply resized_stage_outside
    (K := K) (L := L) (cofinalIdeleStage K L T)
  · intro P' hP' Q
    exact unramified_stage_spec (K := K) (L := L) P'
      (fun h => hP' (Finset.mem_union_left _ h)) Q
  · exact hP

/-- The canonical exceptional-coordinate equivalence at one cofinal finite
stage. -/
noncomputable def cofinalHExceptional
    (T : Finset (NumberFieldPlace K)) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T)) ≃+
      ExceptionalH2 K L (cofinalIdeleStage K L T) :=
  (resizedStagePi
    (K := K) (L := L) (cofinalIdeleStage K L T)).trans
      (ideleStageExceptional
        (K := K) (L := L) (cofinalIdeleStage K L T)
          (cofinal_h_subsingleton
            (K := K) (L := L) T))

/-- The map on degree-two cohomology induced by inclusion of finite-stage
product representations. -/
noncomputable def resizedStageH
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    H2 (resizedStageRepresentation (K := K) (L := L) S) →+
      H2 (resizedStageRepresentation (K := K) (L := L) T) where
  toFun q := groupCohomology.map (MonoidHom.id Gal(L/K))
    (ideleStageTransition (K := K) (L := L) hST) 2 q
  map_zero' := map_zero _
  map_add' := map_add _

omit [FiniteDimensional K L] in
/-- The canonical product coordinate map is natural for inclusion of finite
idèle stages. -/
theorem resized_idele_stage
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : H2 (resizedStageRepresentation
      (K := K) (L := L) S))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    stageHPi (K := K) (L := L) T
        (resizedStageH
          (K := K) (L := L) hST q) P =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (stageOrbitTransition
          (K := K) (L := L) hST P) 2
        (stageHPi
          (K := K) (L := L) S q P) := by
  have hsquare := resized_stage_evaluation
    (K := K) (L := L) hST P
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedStageEvaluation (K := K) (L := L) T P) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleStageTransition
            (K := K) (L := L) hST) 2 q) =
    groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageOrbitTransition
        (K := K) (L := L) hST P) 2
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedStageEvaluation
          (K := K) (L := L) S P) 2 q)
  have hleft := congrArg (fun f => f q)
    (groupCohomology.map_id_comp
      (ideleStageTransition (K := K) (L := L) hST)
      (resizedStageEvaluation (K := K) (L := L) T P) 2)
  have hright := congrArg (fun f => f q)
    (groupCohomology.map_id_comp
      (resizedStageEvaluation (K := K) (L := L) S P)
      (stageOrbitTransition (K := K) (L := L) hST P) 2)
  have hmiddle :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleStageTransition
            (K := K) (L := L) hST ≫
            resizedStageEvaluation
              (K := K) (L := L) T P) 2 q =
        groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedStageEvaluation
            (K := K) (L := L) S P ≫
            stageOrbitTransition
              (K := K) (L := L) hST P) 2 q := by
    exact congrArg (fun f => f q)
      (congrArg (fun φ => groupCohomology.map
        (MonoidHom.id Gal(L/K)) φ 2) hsquare)
  exact hleft.symm.trans (hmiddle.trans hright)

omit [FiniteDimensional K L] in
/-- At an already exceptional prime, inclusion of stages becomes the
identity after identifying both orbit stages with the unrestricted orbit. -/
theorem resized_stage_full
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hPS : (Sum.inl P : NumberFieldPlace K) ∈ S)
    (q : H2 (stageOrbitRepresentation
      (K := K) (L := L) S P)) :
    ideleStageFull
        (K := K) (L := L) T P (hST hPS)
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (stageOrbitTransition
            (K := K) (L := L) hST P) 2 q) =
      ideleStageFull
        (K := K) (L := L) S P hPS q := by
  have hsquare :
      stageOrbitTransition (K := K) (L := L) hST P ≫
          (stageIsoFull
            (K := K) (L := L) T P (hST hPS)).hom =
        (stageIsoFull
          (K := K) (L := L) S P hPS).hom := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageIsoFull
        (K := K) (L := L) T P (hST hPS)).hom 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (stageOrbitTransition
            (K := K) (L := L) hST P) 2 q) =
    groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageIsoFull
        (K := K) (L := L) S P hPS).hom 2 q
  rw [← hsquare]
  exact congrArg (fun f => f q)
    (groupCohomology.map_id_comp
      (stageOrbitTransition (K := K) (L := L) hST P)
      (stageIsoFull
        (K := K) (L := L) T P (hST hPS)).hom 2).symm

/-- The actual inclusion-induced map on cofinal-stage cohomology. -/
noncomputable def resizedCofinalTransition
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T)) →+
      H2 (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L U)) :=
  resizedStageH (K := K) (L := L)
    (cofinal_stage_mono (K := K) (L := L) hTU)

/-- The exceptional-coordinate equivalences commute with actual stage
inclusion and extension by zero. -/
theorem cofinal_exceptional_transition
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T))) :
    cofinalHExceptional (K := K) (L := L) U
        (resizedCofinalTransition
          (K := K) (L := L) hTU q) =
      resizedExceptionalH (K := K) (L := L)
        (cofinal_stage_mono (K := K) (L := L) hTU)
        (cofinalHExceptional
          (K := K) (L := L) T q) := by
  funext P
  let hStage : cofinalIdeleStage K L T ⊆
      cofinalIdeleStage K L U :=
    cofinal_stage_mono (K := K) (L := L) hTU
  have htransition :
      resizedCofinalTransition
          (K := K) (L := L) hTU q =
        resizedStageH
          (K := K) (L := L) hStage q := by
    rfl
  by_cases hPT : (Sum.inl P.1 : NumberFieldPlace K) ∈
      cofinalIdeleStage K L T
  · change ideleStageFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2
        (stageHPi
          (K := K) (L := L) (cofinalIdeleStage K L U)
          (resizedCofinalTransition
            (K := K) (L := L) hTU q) P.1) = _
    rw [htransition]
    rw [resized_idele_stage
      (K := K) (L := L) hStage q P.1]
    rw [exceptional_h_transition
      (K := K) (L := L) hStage _ P hPT]
    exact resized_stage_full
      (K := K) (L := L) hStage P.1 hPT
        (stageHPi
          (K := K) (L := L) (cofinalIdeleStage K L T) q P.1)
  · change ideleStageFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2
        (stageHPi
          (K := K) (L := L) (cofinalIdeleStage K L U)
          (resizedCofinalTransition
            (K := K) (L := L) hTU q) P.1) = _
    rw [htransition]
    rw [resized_exceptional_h
      (K := K) (L := L) hStage _ P hPT]
    rw [resized_idele_stage
      (K := K) (L := L) hStage q P.1]
    letI := cofinal_h_subsingleton
      (K := K) (L := L) T P.1 hPT
    have hzero : stageHPi
        (K := K) (L := L) (cofinalIdeleStage K L T) q P.1 = 0 :=
      Subsingleton.elim _ _
    rw [hzero, map_zero,
      (ideleStageFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2).map_zero]

/-- Map one cofinal finite-stage cohomology group into the fixed global
finite-prime direct sum. -/
noncomputable def cofinalStageDirect
    (T : Finset (NumberFieldPlace K)) :
    H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T)) →+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitH2 K L) :=
  (resizedExceptionalSum
    (K := K) (L := L) (cofinalIdeleStage K L T)).comp
      (cofinalHExceptional
        (K := K) (L := L) T).toAddMonoidHom

/-- The cofinal-stage maps to the global direct sum are compatible with
actual inclusion-induced cohomology maps. -/
theorem cofinal_direct_transition
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T))) :
    cofinalStageDirect (K := K) (L := L) U
        (resizedCofinalTransition
          (K := K) (L := L) hTU q) =
      cofinalStageDirect (K := K) (L := L) T q := by
  change resizedExceptionalSum
      (K := K) (L := L) (cofinalIdeleStage K L U)
        (cofinalHExceptional (K := K) (L := L) U
          (resizedCofinalTransition
            (K := K) (L := L) hTU q)) =
    resizedExceptionalSum
      (K := K) (L := L) (cofinalIdeleStage K L T)
        (cofinalHExceptional
          (K := K) (L := L) T q)
  rw [cofinal_exceptional_transition
    (K := K) (L := L) hTU q]
  exact exceptional_h_direct
    (K := K) (L := L)
      (cofinal_stage_mono (K := K) (L := L) hTU) _

/-- The actual cofinal finite-stage `H²` maps form a directed system. -/
noncomputable instance cofinalDirectedSystem :
    DirectedSystem
      (fun T : Finset (NumberFieldPlace K) =>
        H2 (resizedStageRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)))
      (fun {_ _} h => resizedCofinalTransition
        (K := K) (L := L) h) where
  map_self := by
    intro T q
    have hrep : ideleStageTransition
        (K := K) (L := L)
        (cofinal_stage_mono (K := K) (L := L)
          (show T ⊆ T from fun _ h => h)) =
      𝟙 (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)) := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      funext P
      apply Subtype.ext
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K))
      (ideleStageTransition
        (K := K) (L := L)
        (cofinal_stage_mono (K := K) (L := L)
          (show T ⊆ T from fun _ h => h))) 2 q = q
    rw [hrep, groupCohomology.map_id]
    rfl
  map_map := by
    intro V U T hTU hUV q
    let hStageTU := cofinal_stage_mono (K := K) (L := L) hTU
    let hStageUV := cofinal_stage_mono (K := K) (L := L) hUV
    have hrep : ideleStageTransition
          (K := K) (L := L) hStageTU ≫
        ideleStageTransition
          (K := K) (L := L) hStageUV =
      ideleStageTransition (K := K) (L := L)
        (cofinal_stage_mono (K := K) (L := L)
          (hTU.trans hUV)) := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      funext P
      apply Subtype.ext
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K))
        (ideleStageTransition
          (K := K) (L := L) hStageUV) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleStageTransition
            (K := K) (L := L) hStageTU) 2 q) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (ideleStageTransition (K := K) (L := L)
          (cofinal_stage_mono (K := K) (L := L)
            (hTU.trans hUV))) 2 q
    have hcomp := congrArg (fun f => f q)
      (groupCohomology.map_id_comp
        (ideleStageTransition
          (K := K) (L := L) hStageTU)
        (ideleStageTransition
          (K := K) (L := L) hStageUV) 2)
    have hmap :
        groupCohomology.map (MonoidHom.id Gal(L/K))
            (ideleStageTransition
              (K := K) (L := L) hStageTU ≫
              ideleStageTransition
                (K := K) (L := L) hStageUV) 2 q =
          groupCohomology.map (MonoidHom.id Gal(L/K))
            (ideleStageTransition (K := K) (L := L)
              (cofinal_stage_mono (K := K) (L := L)
                (hTU.trans hUV))) 2 q := by
      exact congrArg (fun f => f q)
        (congrArg (fun φ => groupCohomology.map
          (MonoidHom.id Gal(L/K)) φ 2) hrep)
    exact hcomp.symm.trans hmap

/-- The direct limit of the cofinal finite-stage degree-two cohomology
groups. -/
abbrev ResizedCofinalLimit (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  DirectLimit
    (fun T : Finset (NumberFieldPlace K) =>
      H2 (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)))
    (fun _ _ h => resizedCofinalTransition
      (K := K) (L := L) h)

/-- The canonical map from the cofinal finite-stage direct limit to the
global finite-prime direct sum. -/
noncomputable def resizedCofinalDirect :
    ResizedCofinalLimit K L →+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitH2 K L) where
  toFun := DirectLimit.lift
    (F := fun T : Finset (NumberFieldPlace K) =>
      H2 (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)))
    (fun _ _ h => resizedCofinalTransition
      (K := K) (L := L) h)
    (fun T q => cofinalStageDirect
      (K := K) (L := L) T q)
    (fun _ _ h q => (cofinal_direct_transition
      (K := K) (L := L) h q).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero _
  map_add' q q' := by
    induction q, q' using DirectLimit.induction₂ with
    | _ T x y =>
        rw [DirectLimit.add_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        exact map_add _ x y

/-- The cofinal direct-limit map is injective. -/
theorem resized_cofinal_stage :
    Function.Injective
      (resizedCofinalDirect
        (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : resizedCofinalDirect
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u := fun T =>
    H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L T))
  let f := fun (T U : Finset (NumberFieldPlace K)) (h : T ⊆ U) =>
    resizedCofinalTransition (K := K) (L := L) h
  obtain ⟨T, qT, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  have hstage : cofinalStageDirect
      (K := K) (L := L) T qT = 0 := hzero
  have hqT : qT = 0 := by
    have hezero : (cofinalHExceptional
        (K := K) (L := L) T) qT = 0 := by
      apply resized_direct_injective
        (K := K) (L := L) (cofinalIdeleStage K L T)
      exact hstage.trans (map_zero _).symm
    apply (cofinalHExceptional
      (K := K) (L := L) T).injective
    exact hezero.trans
      (cofinalHExceptional
        (K := K) (L := L) T).map_zero.symm
  rw [hqT]
  exact (DirectLimit.zero_def T).symm

/-- The cofinal direct-limit map is surjective. -/
theorem resized_cofinal_direct :
    Function.Surjective
      (resizedCofinalDirect
        (K := K) (L := L)) := by
  intro y
  obtain ⟨S, x, hx⟩ := exceptional_h_preimage
    (K := K) (L := L) y
  let hS : S ⊆ cofinalIdeleStage K L S := Finset.subset_union_right
  let x' : ExceptionalH2 K L (cofinalIdeleStage K L S) :=
    resizedExceptionalH (K := K) (L := L) hS x
  let qS := (cofinalHExceptional
    (K := K) (L := L) S).symm x'
  refine ⟨(⟦⟨S, qS⟩⟧ : ResizedCofinalLimit K L), ?_⟩
  change cofinalStageDirect
      (K := K) (L := L) S qS = y
  change resizedExceptionalSum
      (K := K) (L := L) (cofinalIdeleStage K L S)
        ((cofinalHExceptional
          (K := K) (L := L) S) qS) = y
  rw [show (cofinalHExceptional
      (K := K) (L := L) S) qS = x' from AddEquiv.apply_symm_apply _ _]
  rw [exceptional_h_direct
    (K := K) (L := L) hS x]
  exact hx

/-- The finite-place cohomology of the cofinal idèle stages is the direct
sum of the unrestricted finite completion-orbit cohomology groups. -/
noncomputable def resizedCofinalStage :
    ResizedCofinalLimit K L ≃+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitH2 K L) :=
  AddEquiv.ofBijective
    (resizedCofinalDirect (K := K) (L := L))
    ⟨resized_cofinal_stage
      (K := K) (L := L),
     resized_cofinal_direct
      (K := K) (L := L)⟩

end

end Towers.CField.HNorm
