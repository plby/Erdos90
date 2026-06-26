import Submission.NumberTheory.Galois.FinitePlaceGroup
import Submission.NumberTheory.Completions.UnramifiedCompletion
import Submission.NumberTheory.Locals.ArbitraryPlaceClassification

namespace Submission.CField.ICohomo

open Filter IsDedekindDomain NumberField HeightOneSpectrum
open scoped Pointwise
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance ringOfIntegersGaloisAction :
    MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (RingOfIntegers K) K L (RingOfIntegers L)

@[reducible]
noncomputable def finitePrimeAction :
    MulAction Gal(L/K) (HeightOneSpectrum (RingOfIntegers L)) where
  smul sigma w := HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv sigma.toRingEquiv) w
  one_smul w := by
    apply HeightOneSpectrum.ext
    ext x
    rfl
  mul_smul sigma tau w := by
    apply HeightOneSpectrum.ext
    ext x
    rfl

omit [FiniteDimensional K L] in
theorem prime_action_ideal (sigma : Gal(L/K))
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma • P).asIdeal = sigma • P.asIdeal := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change (RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm x ∈
      P.asIdeal ↔ sigma⁻¹ • x ∈ P.asIdeal
  have heq : (RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm x =
      sigma⁻¹ • x := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_symm_apply]
    exact (algebraMap_galRestrict_apply
      (A := RingOfIntegers K) (K := K) (L := L)
      (B := RingOfIntegers L) sigma⁻¹ x).symm
  rw [heq]

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
private theorem conjugate_place_nontrivial
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) :
    (sigma • (FinitePlace.mk P).val).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ :=
    Submission.CField.Ideles.absolute_value_nontrivial P
  refine ⟨sigma x, ?_, ?_⟩
  · simpa only [map_zero] using sigma.injective.ne hx0
  · simpa using hx1

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
private theorem conjugate_place_nonarchimedean
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) :
    IsNonarchimedean (sigma • (FinitePlace.mk P).val) := by
  intro x y
  change (FinitePlace.mk P).val (sigma.symm (x + y)) ≤
    max ((FinitePlace.mk P).val (sigma.symm x))
      ((FinitePlace.mk P).val (sigma.symm y))
  rw [map_add]
  exact (place_nonarchimedean (FinitePlace.mk P)) _ _

omit [FiniteDimensional K L] in
theorem conjugate_place_equiv
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma • (FinitePlace.mk P).val).IsEquiv
      (FinitePlace.mk (sigma • P)).val := by
  letI := finitePrimeAction (K := K) (L := L)
  let hw := conjugate_place_nontrivial sigma P
  let hna := conjugate_place_nonarchimedean sigma P
  have hcenterIdeal := centered_smul_ideal
    (K := K) (w := (FinitePlace.mk P).val)
    (Submission.CField.Ideles.absolute_value_nontrivial P)
    (place_nonarchimedean (FinitePlace.mk P)) sigma
  rw [nonarchimedean_height_spectrum] at hcenterIdeal
  have hcenter :
      nonarchimedeanHeightSpectrum
          (sigma • (FinitePlace.mk P).val) hw hna = sigma • P := by
    apply HeightOneSpectrum.ext
    rw [hcenterIdeal, prime_action_ideal]
  have h := place_centered_prime
    (sigma • (FinitePlace.mk P).val) hw hna
  rwa [hcenter] at h

theorem place_adic_isometry
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    Isometry (placeCompletionAdic P) := by
  unfold placeCompletionAdic
  exact (Classical.choose_spec
    (completion_universal (FinitePlace.mk P).val
      (FinitePlace.embedding P) (by
        intro x
        exact (FinitePlace.mk_apply P x).symm))).1.1

theorem adic_symm_continuous
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    Continuous (placeCompletionAdic P).symm := by
  let e : (FinitePlace.mk P).val.Completion ≃ᵢ P.adicCompletion L :=
    { toEquiv := (placeCompletionAdic P).toEquiv
      isometry_toFun := place_adic_isometry P }
  exact e.symm.isometry.continuous

theorem adic_symm_isometry
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    Isometry (placeCompletionAdic P).symm := by
  let e : (FinitePlace.mk P).val.Completion ≃ᵢ P.adicCompletion L :=
    { toEquiv := (placeCompletionAdic P).toEquiv
      isometry_toFun := place_adic_isometry P }
  exact e.symm.isometry

@[simp]
theorem place_adic_symm
    (P : HeightOneSpectrum (RingOfIntegers L)) (x : L) :
    (placeCompletionAdic P).symm
        (FinitePlace.embedding P x) =
      completionEmbedding (FinitePlace.mk P).val x := by
  apply (placeCompletionAdic P).injective
  rw [RingEquiv.apply_symm_apply,
    finite_place_adic]

noncomputable def finitePlaceTransport
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma⁻¹ • P).adicCompletion L ≃+* P.adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  let Q := sigma⁻¹ • P
  let h := conjugate_place_equiv (K := K) sigma⁻¹ P
  exact (((placeCompletionAdic Q).symm.trans
    (completionRing h.symm)).trans
    (completionTransport sigma (FinitePlace.mk P).val)).trans
    (placeCompletionAdic P)

omit [FiniteDimensional K L] in
@[simp]
theorem place_transport_embedding
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) (x : L) :
    letI := finitePrimeAction (K := K) (L := L)
    finitePlaceTransport (K := K) sigma P
        (FinitePlace.embedding (sigma⁻¹ • P) x) =
      FinitePlace.embedding P (sigma x) := by
  letI := finitePrimeAction (K := K) (L := L)
  unfold finitePlaceTransport
  dsimp only [RingEquiv.trans_apply]
  rw [place_adic_symm]
  rw [completion_ring_embedding]
  rw [completion_transport_embedding]
  rw [finite_place_adic]

omit [FiniteDimensional K L] in
theorem finite_transport_continuous
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    Continuous (finitePlaceTransport (K := K) sigma P) := by
  letI := finitePrimeAction (K := K) (L := L)
  unfold finitePlaceTransport
  dsimp only [RingEquiv.coe_trans]
  exact (place_adic_isometry P).continuous.comp
    ((completionTransport_isometry sigma (FinitePlace.mk P).val).continuous.comp
      ((continuous_ring_equiv _).comp
        (adic_symm_continuous _)))

set_option synthInstance.maxHeartbeats 200000 in
-- Comparing the transported norms unfolds several completion instances.
omit [FiniteDimensional K L] in
theorem place_transport_one
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L))
    (x : letI := finitePrimeAction (K := K) (L := L)
      (sigma⁻¹ • P).adicCompletion L) :
    letI := finitePrimeAction (K := K) (L := L)
    ‖finitePlaceTransport (K := K) sigma P x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  letI := finitePrimeAction (K := K) (L := L)
  let Q := sigma⁻¹ • P
  let u := sigma⁻¹ • (FinitePlace.mk P).val
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u
      (conjugate_place_nonarchimedean sigma⁻¹ P)
  unfold finitePlaceTransport
  dsimp only [RingEquiv.trans_apply]
  rw [(place_adic_isometry P).norm_map_of_map_zero
      (map_zero (placeCompletionAdic P)),
    (completionTransport_isometry sigma (FinitePlace.mk P).val).norm_map_of_map_zero
      (map_zero (completionTransport sigma (FinitePlace.mk P).val)),
    completion_ring_one,
    (adic_symm_isometry
      (sigma⁻¹ • P)).norm_map_of_map_zero
      (map_zero (placeCompletionAdic (sigma⁻¹ • P)).symm)]

omit [FiniteDimensional K L] in
theorem transport_preserves_units
    (sigma : Gal(L/K)) (P : HeightOneSpectrum (RingOfIntegers L))
    (x : letI := finitePrimeAction (K := K) (L := L)
      ((sigma⁻¹ • P).adicCompletion L)ˣ)
    (hx : letI := finitePrimeAction (K := K) (L := L)
      x ∈ IdeleUnitSubgroup (RingOfIntegers L) L (sigma⁻¹ • P)) :
    letI := finitePrimeAction (K := K) (L := L)
    Units.map (finitePlaceTransport (K := K) sigma P).toRingHom x ∈
      IdeleUnitSubgroup (RingOfIntegers L) L P := by
  letI := finitePrimeAction (K := K) (L := L)
  change
    (finitePlaceTransport (K := K) sigma P (x : _) ∈
        P.adicCompletionIntegers L) ∧
      ((finitePlaceTransport (K := K) sigma P
          (x⁻¹ : ((sigma⁻¹ • P).adicCompletion L)ˣ) :
            P.adicCompletion L) ∈ P.adicCompletionIntegers L)
  change ((x : (sigma⁻¹ • P).adicCompletion L) ∈
      (sigma⁻¹ • P).adicCompletionIntegers L) ∧
    (((x⁻¹ : ((sigma⁻¹ • P).adicCompletion L)ˣ) :
        (sigma⁻¹ • P).adicCompletion L) ∈
      (sigma⁻¹ • P).adicCompletionIntegers L) at hx
  constructor
  · rw [mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    apply (place_transport_one sigma P (x : _)).2
    rw [Valued.toNormedField.norm_le_one_iff,
      ← mem_adicCompletionIntegers]
    exact hx.1
  · rw [mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    apply (place_transport_one sigma P
      ((x⁻¹ : ((sigma⁻¹ • P).adicCompletion L)ˣ) :
        (sigma⁻¹ • P).adicCompletion L)).2
    rw [Valued.toNormedField.norm_le_one_iff,
      ← mem_adicCompletionIntegers]
    exact hx.2

set_option synthInstance.maxHeartbeats 100000 in
-- The dense-image argument synthesizes both adic-completion topologies.
theorem adic_ext_continuous
    (P Q : HeightOneSpectrum (RingOfIntegers L))
    (e f : P.adicCompletion L ≃+* Q.adicCompletion L)
    (he : Continuous e) (hf : Continuous f)
    (h : ∀ x : L, e (FinitePlace.embedding P x) =
      f (FinitePlace.embedding P x)) :
    e = f := by
  apply RingEquiv.ext
  intro y
  have hfun : (e : P.adicCompletion L → Q.adicCompletion L) = f :=
    (P.denseRange_algebraMap L).equalizer he hf (funext h)
  exact congrFun hfun y

omit [FiniteDimensional K L] in
theorem finite_place_transport
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    finitePlaceTransport (K := K) (1 : Gal(L/K)) P = RingEquiv.refl _ := by
  letI := finitePrimeAction (K := K) (L := L)
  apply adic_ext_continuous
  · exact finite_transport_continuous 1 P
  · exact continuous_id
  · intro x
    rw [place_transport_embedding]
    rfl

omit [FiniteDimensional K L] in
theorem place_transport_mul
    (sigma tau : Gal(L/K))
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    finitePlaceTransport (K := K) (sigma * tau) P =
      (finitePlaceTransport (K := K) tau (sigma⁻¹ • P)).trans
        (finitePlaceTransport (K := K) sigma P) := by
  letI := finitePrimeAction (K := K) (L := L)
  apply adic_ext_continuous
  · exact finite_transport_continuous (sigma * tau) P
  · exact (finite_transport_continuous sigma P).comp
      (finite_transport_continuous tau (sigma⁻¹ • P))
  · intro x
    rw [place_transport_embedding]
    have hplace : (sigma * tau)⁻¹ • P = tau⁻¹ • sigma⁻¹ • P := by
      rw [mul_inv_rev, mul_smul]
    cases hplace
    change FinitePlace.embedding P ((sigma * tau) x) =
      finitePlaceTransport (K := K) sigma P
        (finitePlaceTransport (K := K) tau (sigma⁻¹ • P)
          (FinitePlace.embedding (tau⁻¹ • sigma⁻¹ • P) x))
    rw [place_transport_embedding, place_transport_embedding]
    rfl

@[reducible]
noncomputable def finiteCompletionAction :
    letI := finitePrimeAction (K := K) (L := L)
    MulDistribMulAction Gal(L/K)
      (∀ P : HeightOneSpectrum (RingOfIntegers L), (P.adicCompletion L)ˣ) := by
  letI := finitePrimeAction (K := K) (L := L)
  exact
    { smul := fun sigma x P ↦
        Units.map (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom
          (x (sigma⁻¹ • P))
      one_smul := fun x ↦ by
        funext P
        apply Units.ext
        change finitePlaceTransport (K := K) 1 P
            (x ((1 : Gal(L/K))⁻¹ • P) : _) = (x P : _)
        rw [finite_place_transport]
        rfl
      mul_smul := fun sigma tau x ↦ by
        funext P
        apply Units.ext
        change finitePlaceTransport (K := K) (sigma * tau) P
            (x ((sigma * tau)⁻¹ • P) : _) =
          finitePlaceTransport (K := K) sigma P
            (finitePlaceTransport (K := K) tau (sigma⁻¹ • P)
              (x (tau⁻¹ • sigma⁻¹ • P) : _))
        have hplace : (sigma * tau)⁻¹ • P =
            tau⁻¹ • sigma⁻¹ • P := by
          rw [mul_inv_rev, mul_smul]
        cases hplace
        rw [place_transport_mul]
        rfl
      smul_one := fun sigma ↦ by
        funext P
        exact map_one (Units.map
          (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom)
      smul_mul := fun sigma x y ↦ by
        funext P
        exact map_mul (Units.map
          (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom)
          (x (sigma⁻¹ • P)) (y (sigma⁻¹ • P)) }

omit [FiniteDimensional K L] in
theorem completion_action_coordinate
    (sigma : Gal(L/K))
    (x : ∀ P : HeightOneSpectrum (RingOfIntegers L), (P.adicCompletion L)ˣ)
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteCompletionAction (K := K) (L := L)
    (sigma • x) P =
      Units.map (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom
        (x (sigma⁻¹ • P)) := rfl

omit [FiniteDimensional K L] in
theorem action_preserves_restricted :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteCompletionAction (K := K) (L := L)
    PreservesRestrictedProduct (G := Gal(L/K))
      (fun P : HeightOneSpectrum (RingOfIntegers L) ↦ (P.adicCompletion L)ˣ)
      (IdeleUnitSubgroup (RingOfIntegers L) L) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteCompletionAction (K := K) (L := L)
  apply preserves_restricted_coordinate
    (M := fun P : HeightOneSpectrum (RingOfIntegers L) ↦ (P.adicCompletion L)ˣ)
    (U := IdeleUnitSubgroup (RingOfIntegers L) L)
    (fun sigma P ↦
      Units.map (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom)
  · intro sigma x P
    rfl
  · intro sigma P x hx
    exact transport_preserves_units sigma P x hx

@[reducible]
noncomputable def finiteIdelesAction :
    MulDistribMulAction Gal(L/K) (FiniteIdeles (RingOfIntegers L) L) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteCompletionAction (K := K) (L := L)
  exact restrictedDistribAction
    (fun P : HeightOneSpectrum (RingOfIntegers L) ↦ (P.adicCompletion L)ˣ)
    (IdeleUnitSubgroup (RingOfIntegers L) L)
    (action_preserves_restricted
      (K := K) (L := L))

omit [FiniteDimensional K L] in
theorem ideles_action_coordinate
    (sigma : Gal(L/K)) (x : FiniteIdeles (RingOfIntegers L) L)
    (P : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := L)
    (sigma • x).1 P =
      Units.map (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom
        (x.1 (sigma⁻¹ • P)) := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the finite restricted-product action unfolds transported
-- completion instances.
omit [FiniteDimensional K L] in
theorem ideles_action_continuous (sigma : Gal(L/K)) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := L)
    Continuous (fun x : FiniteIdeles (RingOfIntegers L) L ↦
      (sigma • x : FiniteIdeles (RingOfIntegers L) L)) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteCompletionAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  let f := fun P : HeightOneSpectrum (RingOfIntegers L) ↦ sigma⁻¹ • P
  let phi : ∀ P : HeightOneSpectrum (RingOfIntegers L),
      ((f P).adicCompletion L)ˣ →* (P.adicCompletion L)ˣ :=
    fun P ↦
      Units.map (finitePlaceTransport (K := K) sigma P).toRingHom.toMonoidHom
  have hf : Tendsto f cofinite cofinite :=
    (MulAction.injective sigma⁻¹).tendsto_cofinite
  have hphi : ∀ᶠ P in cofinite,
      Set.MapsTo (phi P)
        (IdeleUnitSubgroup (RingOfIntegers L) L (f P))
        (IdeleUnitSubgroup (RingOfIntegers L) L P) := by
    filter_upwards [] with P x hx
    exact transport_preserves_units sigma P x hx
  change Continuous (RestrictedProduct.mapAlong
    (fun P : HeightOneSpectrum (RingOfIntegers L) ↦ (P.adicCompletion L)ˣ)
    (fun P : HeightOneSpectrum (RingOfIntegers L) ↦ (P.adicCompletion L)ˣ)
    (A₁ := fun P ↦
      (IdeleUnitSubgroup (RingOfIntegers L) L P :
        Set ((P.adicCompletion L)ˣ)))
    (A₂ := fun P ↦
      (IdeleUnitSubgroup (RingOfIntegers L) L P :
        Set ((P.adicCompletion L)ˣ)))
    f hf (fun P x ↦ phi P x) hphi)
  apply RestrictedProduct.mapAlong_continuous
  intro P
  exact (finite_transport_continuous sigma P).units_map

end

end Submission.CField.ICohomo
