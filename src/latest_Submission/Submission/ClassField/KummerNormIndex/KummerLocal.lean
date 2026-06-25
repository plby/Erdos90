import Submission.ClassField.NormIndex.FixedIdeleDescent
import Submission.ClassField.KummerNormIndex.KummerGlobal
import Submission.NumberTheory.Locals.UnramifiedExtensions

/-! # The local Frobenius step in Lemma VII.6.3 -/

namespace Submission.CField.KNIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

set_option synthInstance.maxHeartbeats 1000000 in
-- Prime ideals, normalized absolute-value completions, and prime-adic
-- completions are all present in this comparison.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- At one selected prime in Lemma VII.6.2, local `p`th-power detection is
equivalent to the corresponding arithmetic Frobenius fixing the chosen
global `p`th root. -/
theorem pth_frobenius_fixed
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M]
    (hroot : (primitiveRoots p K).Nonempty)
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (P : FinitePrime K) (Q : FinitePrime M)
    (hunder : Q.under (OK K) = P)
    (hunramified : Algebra.IsUnramifiedAt (OK K) Q.asIdeal)
    (hcompat :
      galMLMK (K := K) (L := L) (M := M)
          (numberFrobeniusElement (K := L) Q) =
        numberFrobeniusElement (K := K) Q)
    (hfrobL_ne : numberFrobeniusElement (K := L) Q ≠ 1)
    (a : Kˣ) (z : M)
    (hzpow : z ^ p = algebraMap K M (a : K)) :
    PthPowerCompletion K p a P ↔
      numberFrobeniusElement (K := K) Q z = z := by
  classical
  subst P
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : MulSemiringAction Gal(M/K) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK K) K M (OK M)
  letI : IsGaloisGroup Gal(M/K) (OK K) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K) (OK K) (OK M) K M
  letI : MulSemiringAction Gal(M/L) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK L) L M (OK M)
  letI : IsGaloisGroup Gal(M/L) (OK L) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/L) (OK L) (OK M) L M
  let P : FinitePrime K := Q.under (OK K)
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  letI : Field (OK K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : Field (OK M ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Finite (OK K ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : Finite (OK M ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsSeparable (OK K ⧸ P.asIdeal) (OK M ⧸ Q.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : Algebra.IsUnramifiedAt (OK K) Q.asIdeal := hunramified
  let frobK : Gal(M/K) := numberFrobeniusElement (K := K) Q
  let frobL : Gal(M/L) := numberFrobeniusElement (K := L) Q
  have hfrobK_ne : frobK ≠ 1 := by
    intro hfrobK
    apply hfrobL_ne
    apply gal_ml_injective (K := K) (L := L) (M := M)
    rw [hcompat]
    exact hfrobK.trans (map_one
      (galMLMK (K := K) (L := L) (M := M))).symm
  have hfrobK_order : orderOf frobK = p :=
    orderOf_eq_prime (hexponent frobK) hfrobK_ne
  have horderK : orderOf frobK = P.asIdeal.inertiaDeg Q.asIdeal := by
    simpa only [frobK, P, numberFrobeniusElement] using
      (frob_inertia_deg
        (R := OK K) (S := OK M) (G := Gal(M/K)) Q.asIdeal)
  have hramification : P.asIdeal.ramificationIdx Q.asIdeal = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt Q.ne_bot
  have hdecompositionCard :
      Nat.card (MulAction.stabilizer Gal(M/K) Q.asIdeal) = p := by
    calc
      Nat.card (MulAction.stabilizer Gal(M/K) Q.asIdeal) =
          P.asIdeal.ramificationIdxIn (OK M) *
            P.asIdeal.inertiaDegIn (OK M) :=
        decomposition_inertia_deg
          P.asIdeal P.ne_bot Q.asIdeal
      _ = P.asIdeal.ramificationIdx Q.asIdeal *
            P.asIdeal.inertiaDeg Q.asIdeal := by
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx
          P.asIdeal Q.asIdeal Gal(M/K),
          Ideal.inertiaDegIn_eq_inertiaDeg
            P.asIdeal Q.asIdeal Gal(M/K)]
      _ = 1 * p := by rw [hramification, ← horderK, hfrobK_order]
      _ = p := one_mul p
  let qFactor := upperPrimeFactor (K := K) (L := M) Q
  let v := (FinitePlace.mk P).val
  let w : CompletionPlacesAbove (L := M) v :=
    (placesAboveFactors
      (K := K) (L := M) P).symm qFactor
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  let W := CompletionPlacesAbove (L := M) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := M) v
  letI : MulAction.IsPretransitive Gal(M/K) W :=
    completion_above_pretransitive P
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  have hfactor :
      placeUpperFactor (K := K) (L := M) P w =
        qFactor := by
    exact place_upper_symm
      (K := K) (L := M) P qFactor
  have hcenter : nonarchimedeanHeightSpectrum w.1 hw hwna = Q := by
    calc
      nonarchimedeanHeightSpectrum w.1 hw hwna =
          upperPrime (K := K) (L := M) P
            (placeUpperFactor
              (K := K) (L := M) P w) :=
        (upper_place_factor
          (K := K) (L := M) P w).symm
      _ = upperPrime (K := K) (L := M) P qFactor := by rw [hfactor]
      _ = Q := upper_prime_factor (K := K) (L := M) Q
  have hidealDecomposition :
      MulAction.stabilizer Gal(M/K) Q.asIdeal =
        absoluteValueDecomposition v w.1 := by
    rw [← hcenter]
    exact centered_stabilizer_decomposition v w.1 hw hwna
  have hcompletionStabilizerCard :
      Nat.card (CompletionPlaceStabilizer v w) = p := by
    calc
      Nat.card (CompletionPlaceStabilizer v w) =
          Nat.card (absoluteValueDecomposition v w.1) :=
        Nat.card_congr
          (MulEquiv.subgroupCongr
            (stabilizer_decomposition_group v w)).toEquiv
      _ = Nat.card (MulAction.stabilizer Gal(M/K) Q.asIdeal) :=
        Nat.card_congr
          (MulEquiv.subgroupCongr hidealDecomposition.symm).toEquiv
      _ = p := hdecompositionCard
  have hfrobIdeal : frobK ∈ MulAction.stabilizer Gal(M/K) Q.asIdeal := by
    simpa only [frobK, numberFrobeniusElement] using
      (frobenius_mem_stabilizer (R := OK K) (G := Gal(M/K)) Q.asIdeal)
  let frobStabilizer : CompletionPlaceStabilizer v w :=
    ⟨frobK, by
      rw [stabilizer_decomposition_group,
        ← hidealDecomposition]
      exact hfrobIdeal⟩
  have hfrobStabilizer_ne : frobStabilizer ≠ 1 := by
    intro h
    apply hfrobK_ne
    exact congrArg Subtype.val h
  have hstabilizerGenerated :
      Subgroup.zpowers frobStabilizer = ⊤ :=
    zpowers_eq_top_of_prime_card hcompletionStabilizerCard
      hfrobStabilizer_ne
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  have hbaseFixed (sigma : CompletionPlaceStabilizer v w)
      (b : v.Completion) :
      stabilizerRingHom v w sigma
          (completionLies v w.1 w.2 b) =
        completionLies v w.1 w.2 b := by
    let d : absoluteValueDecomposition v w.1 :=
      MulEquiv.subgroupCongr
        (stabilizer_decomposition_group v w) sigma
    calc
      stabilizerRingHom v w sigma
          (completionLies v w.1 w.2 b) =
          decompositionCompletionEquiv v w.1 d
            (completionLies v w.1 w.2 b) :=
        stabilizer_decomposition_action
          v w sigma _
      _ = completionLies v w.1 w.2 b := by
        exact (decompositionCompletionEquiv v w.1 d).commutes b
  have hrange_iff_fixed :
      (∃ b : v.Completion,
          completionLies v w.1 w.2 b = completionEmbedding w.1 z) ↔
        frobK z = z := by
    constructor
    · rintro ⟨b, hb⟩
      apply (completionEmbedding w.1).injective
      calc
        completionEmbedding w.1 (frobK z) =
            stabilizerRingHom v w frobStabilizer
              (completionEmbedding w.1 z) := by
          exact (place_stabilizer_embedding
            v w frobStabilizer z).symm
        _ = stabilizerRingHom v w frobStabilizer
              (completionLies v w.1 w.2 b) := by rw [hb]
        _ = completionLies v w.1 w.2 b :=
          hbaseFixed frobStabilizer b
        _ = completionEmbedding w.1 z := hb
    · intro hfrob
      apply fixed_range_stabilizer
        (K := K) (L := M) v w (completionEmbedding w.1 z)
      intro sigma
      rw [place_stabilizer_embedding]
      apply congrArg (completionEmbedding w.1)
      let fixed : Subgroup (CompletionPlaceStabilizer v w) :=
        { carrier := {tau | tau.1 z = z}
          one_mem' := rfl
          mul_mem' := by
            intro tau rho htau hrho
            change tau.1 (rho.1 z) = z
            rw [hrho, htau]
          inv_mem' := by
            intro tau htau
            have h := congrArg (fun y : M ↦ tau.1⁻¹ y) htau
            simpa using h.symm }
      have hfrob_mem : frobStabilizer ∈ fixed := hfrob
      have htop : (⊤ : Subgroup (CompletionPlaceStabilizer v w)) ≤ fixed := by
        rw [← hstabilizerGenerated]
        exact Subgroup.zpowers_le.mpr hfrob_mem
      exact htop trivial
  let eK := placeCompletionAdic P
  have hpower_iff_range :
      PthPowerCompletion K p a P ↔
        ∃ b : v.Completion,
          completionLies v w.1 w.2 b =
            completionEmbedding w.1 z := by
    constructor
    · rintro ⟨bAdic, hbAdic⟩
      change bAdic ^ p = FinitePlace.embedding P (a : K) at hbAdic
      let b : v.Completion := eK.symm bAdic
      have hbAdic_ne : bAdic ≠ 0 := by
        intro hb
        subst bAdic
        have ha_ne : FinitePlace.embedding P (a : K) ≠ 0 :=
          (map_ne_zero (FinitePlace.embedding P)).2 (Units.ne_zero a)
        exact ha_ne (by simpa [hp.ne_zero] using hbAdic.symm)
      have hb_ne : b ≠ 0 :=
        (map_ne_zero eK.symm.toRingHom).2 hbAdic_ne
      have hbpow : b ^ p = completionEmbedding v (a : K) := by
        apply eK.injective
        calc
          eK (b ^ p) = (eK b) ^ p := eK.map_pow b p
          _ = bAdic ^ p := by rw [eK.apply_symm_apply]
          _ = FinitePlace.embedding P (a : K) := hbAdic
          _ = eK (completionEmbedding v (a : K)) :=
            (finite_place_adic P (a : K)).symm
      obtain ⟨zeta, hzeta_mem⟩ := hroot
      have hzetaK : IsPrimitiveRoot zeta p :=
        isPrimitiveRoot_of_mem_primitiveRoots hzeta_mem
      have hzetaV : IsPrimitiveRoot (completionEmbedding v zeta) p :=
        hzetaK.map_of_injective (completionEmbedding v).injective
      have hupperpow : (completionEmbedding w.1 z) ^ p =
          algebraMap v.Completion w.1.Completion (b ^ p) := by
        calc
          (completionEmbedding w.1 z) ^ p =
              completionEmbedding w.1 (z ^ p) := by rw [map_pow]
          _ = completionEmbedding w.1 (algebraMap K M (a : K)) := by
            rw [hzpow]
          _ = completionLies v w.1 w.2
                (completionEmbedding v (a : K)) := by
            exact (RingHom.congr_fun
              (completion_lies_comp v w.1 w.2) (a : K)).symm
          _ = completionLies v w.1 w.2 (b ^ p) := by rw [hbpow]
      exact algebra_pow
        p (completionEmbedding v zeta) hzetaV
        (completionEmbedding w.1 z) b hb_ne hupperpow
    · rintro ⟨b, hb⟩
      have hbpow : b ^ p = completionEmbedding v (a : K) := by
        apply (completionLies v w.1 w.2).injective
        calc
          completionLies v w.1 w.2 (b ^ p) =
              (completionLies v w.1 w.2 b) ^ p := by rw [map_pow]
          _ = (completionEmbedding w.1 z) ^ p := by rw [hb]
          _ = completionEmbedding w.1 (z ^ p) := by rw [map_pow]
          _ = completionEmbedding w.1 (algebraMap K M (a : K)) := by
            rw [hzpow]
          _ = completionLies v w.1 w.2
                (completionEmbedding v (a : K)) := by
            exact (RingHom.congr_fun
              (completion_lies_comp v w.1 w.2) (a : K)).symm
      refine ⟨eK b, ?_⟩
      change (eK b) ^ p = FinitePlace.embedding P (a : K)
      calc
        (eK b) ^ p = eK (b ^ p) := (eK.map_pow b p).symm
        _ = eK (completionEmbedding v (a : K)) := by rw [hbpow]
        _ = FinitePlace.embedding P (a : K) :=
          finite_place_adic P (a : K)
  exact hpower_iff_range.trans hrange_iff_fixed

end

end Submission.CField.KNIndex
