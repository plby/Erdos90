import Submission.NumberTheory.Locals.ArbitraryPlaceClassification
import Submission.NumberTheory.Locals.WeakApproximation
import Submission.ClassField.HasseNorm.IdealMapBridge

/-!
# Weak approximation for Proposition V.4.6

For a fixed modulus, weak approximation lets one multiply any idèle by a
principal idèle so that the resulting representative satisfies every local
ray condition in the modulus.  This proves the surjectivity assertion left
as `WeakApproximation` in the source-statement file.
-/

namespace Submission.CField.HNorm

open AbsoluteValue Filter Ideal IsDedekindDomain NumberField Set Topology
open Submission.NumberTheory.Milne
open Submission.CField.NCorr
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.Ideles
open scoped nonZeroDivisors Pointwise RestrictedProduct Topology

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

variable {K : Type u} [Field K] [NumberField K]

/-- The finite family of places occurring in a modulus. -/
private abbrev ModulusPlaceIndex (m : Modulus K) :=
  {P : HeightOneSpectrum (OK K) // P ∈ m.finiteSupport} ⊕
    {w : RealInfinitePlace K // w ∈ m.infinite}

private def modulusPlace (m : Modulus K) :
    ModulusPlaceIndex m → NumberFieldPlace K
  | .inl P => .inl P.1
  | .inr w => .inr w.1.1

/-- A normalized absolute-value representative for every place in the
modulus. -/
private def modulusAbsoluteValue (m : Modulus K) :
    ModulusPlaceIndex m → AbsoluteValue K ℝ
  | .inl P => (FinitePlace.mk P.1).1
  | .inr w => w.1.1.1

private theorem modulus_absolute_nontrivial (m : Modulus K) :
    ∀ i, (modulusAbsoluteValue m i).IsNontrivial := by
  intro i
  cases i with
  | inl P => exact finite_place_nontrivial (FinitePlace.mk P.1)
  | inr w => exact InfinitePlace.isNontrivial w.1.1

private theorem modulus_absolute_pairwise (m : Modulus K) :
    Pairwise fun i j ↦
      ¬(modulusAbsoluteValue m i).IsEquiv (modulusAbsoluteValue m j) := by
  intro i j hij hequiv
  apply hij
  cases i with
  | inl P =>
      cases j with
      | inl Q =>
          congr 1
          apply Subtype.ext
          exact FinitePlace.mk_eq_iff.mp
            ((finite_place_equiv (FinitePlace.mk P.1)
              (FinitePlace.mk Q.1)).2 hequiv)
      | inr w =>
          exfalso
          apply infinite_place_nonarchimedean w.1.1
          exact (nonarchimedean_equiv hequiv).1
            (place_nonarchimedean (FinitePlace.mk P.1))
  | inr w =>
      cases j with
      | inl P =>
          exfalso
          apply infinite_place_nonarchimedean w.1.1
          exact (nonarchimedean_equiv hequiv).2
            (place_nonarchimedean (FinitePlace.mk P.1))
      | inr z =>
          congr 1
          apply Subtype.ext
          apply Subtype.ext
          exact (InfinitePlace.eq_iff_isEquiv (K := K)).2 hequiv

private def modulusCoordinateMap (m : Modulus K)
    (i : ModulusPlaceIndex m) :
    WithAbs (modulusAbsoluteValue m i) → placeCompletion K (modulusPlace m i) :=
  match i with
  | .inl P => fun x ↦ FinitePlace.embedding P.1 x.ofAbs
  | .inr w => fun x ↦ completionEmbedding w.1.1.1 x.ofAbs

private theorem modulus_coordinate_continuous (m : Modulus K)
    (i : ModulusPlaceIndex m) :
    Continuous (modulusCoordinateMap m i) := by
  cases i with
  | inl P =>
      change Continuous (fun x : WithAbs (FinitePlace.mk P.1).1 ↦
        FinitePlace.embedding P.1 x.ofAbs)
      exact (show Isometry (fun x : WithAbs (FinitePlace.mk P.1).1 ↦
          FinitePlace.embedding P.1 x.ofAbs) by
        apply Isometry.of_dist_eq
        intro x y
        rw [dist_eq_norm, ← map_sub, FinitePlace.norm_embedding,
          dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
        change (HeightOneSpectrum.adicAbv K P.1)
          (x.ofAbs - y.ofAbs) =
            ‖FinitePlace.embedding P.1 (x - y).ofAbs‖
        rw [FinitePlace.norm_embedding, WithAbs.ofAbs_sub]).continuous
  | inr w =>
      simpa only [modulusCoordinateMap, completionEmbedding_apply,
        WithAbs.toAbs_ofAbs] using
        (UniformSpace.Completion.continuous_coe
          (α := WithAbs w.1.1.1))

private theorem modulus_dense_range (m : Modulus K)
    (i : ModulusPlaceIndex m) :
    DenseRange (modulusCoordinateMap m i) := by
  cases i with
  | inl P =>
      apply (P.1.denseRange_algebraMap (K := K)).mono
      rintro y ⟨x, rfl⟩
      refine ⟨(WithAbs.equiv (FinitePlace.mk P.1).1).symm x, ?_⟩
      rfl
  | inr w =>
      simpa only [modulusCoordinateMap, completionEmbedding_apply,
        WithAbs.toAbs_ofAbs] using
        (UniformSpace.Completion.denseRange_coe
          (α := WithAbs w.1.1.1))

/-- Weak approximation in the dependent product of the actual finite and
infinite completions occurring in a modulus. -/
theorem modulus_diagonal_range (m : Modulus K) :
    DenseRange (fun x : K ↦ fun i : ModulusPlaceIndex m ↦
      modulusCoordinateMap m i
        ((WithAbs.equiv (modulusAbsoluteValue m i)).symm x)) := by
  let complete : ((i : ModulusPlaceIndex m) →
      WithAbs (modulusAbsoluteValue m i)) →
      ((i : ModulusPlaceIndex m) → placeCompletion K (modulusPlace m i)) :=
    fun z i ↦ modulusCoordinateMap m i (z i)
  have hdenseComplete : DenseRange complete :=
    DenseRange.piMap fun i ↦ modulus_dense_range m i
  have hcontinuousComplete : Continuous complete := by
    exact continuous_pi fun i ↦
      (modulus_coordinate_continuous m i).comp (continuous_apply i)
  exact hdenseComplete.comp
    (weak_approximation_dense (modulusAbsoluteValue m)
      (modulus_absolute_nontrivial m)
      (modulus_absolute_pairwise m))
    hcontinuousComplete

/-- At a positive ray level, the local ray subgroup is open in the
multiplicative group of the finite completion. -/
private theorem ray_local_open
    (P : HeightOneSpectrum (OK K)) (n : ℕ) (hn : 0 < n) :
    IsOpen (rayLocalSubgroup (K := K) P n :
      Set (P.adicCompletion K)ˣ) := by
  let C := P.adicCompletion K
  let A := P.adicCompletionIntegers K
  let M : Ideal A := IsLocalRing.maximalIdeal A
  let J : Set C := Subtype.val '' ((M ^ n : Ideal A) : Set A)
  have hAopen : IsOpen (A : Set C) := by
    exact Valued.isOpen_valuationSubring _
  have hMopen : IsOpen ((M ^ n : Ideal A) : Set A) := by
    exact open_maximal_integers (K := K) P n
  have hJopen : IsOpen J := by
    exact hAopen.isOpenEmbedding_subtypeVal.isOpenMap _ hMopen
  let f : Cˣ → C := fun x ↦ (x : C) - 1
  have hf : Continuous f := Units.continuous_val.sub continuous_const
  rw [show (rayLocalSubgroup (K := K) P n : Set Cˣ) =
      f ⁻¹' J by
    ext x
    constructor
    · intro hx
      rw [rayLocalSubgroup] at hx
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨(a : A) - 1, ha, ?_⟩
      change (((a : A) - 1 : A) : C) = (x : C) - 1
      rw [← hax]
      rfl
    · rintro ⟨z, hz, hzx⟩
      have hzM : z ∈ M := (Ideal.pow_le_self hn.ne') hz
      let r : A := 1 + z
      have hrunit : IsUnit r := by
        by_contra hr
        have hrM : r ∈ M := (IsLocalRing.mem_maximalIdeal r).2 hr
        have honeM : (1 : A) ∈ M := by
          have := M.sub_mem hrM hzM
          simpa only [r, add_sub_cancel_right] using this
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
          ((Ideal.eq_top_iff_one M).2 honeM)
      let a : Aˣ := hrunit.unit
      have ha : (a : A) = r := IsUnit.unit_spec hrunit
      rw [rayLocalSubgroup]
      refine ⟨a, ?_, ?_⟩
      · change (a : A) - 1 ∈ M ^ n
        simpa only [ha, r, add_sub_cancel_left] using hz
      · apply Units.ext
        change ((A.unitGroupMulEquiv.symm a : Cˣ) : C) = (x : C)
        rw [ValuationSubring.coe_unitGroupMulEquiv_symm_apply]
        change ((a : A) : C) = (x : C)
        rw [ha]
        change ((1 + z : A) : C) = (x : C)
        have hzx' : (z : C) = (x : C) - 1 := hzx
        change (1 : C) + (z : C) = (x : C)
        rw [hzx']
        ring]
  exact hJopen.preimage hf

omit [NumberField K] in
private theorem positive_real_open
    (w : RealInfinitePlace K) :
    IsOpen (positiveRealSubgroup w : Set w.1.Completionˣ) := by
  have hpos : IsOpen (Units.posSubgroup ℝ : Set ℝˣ) := by
    change IsOpen {u : ℝˣ | 0 < (u : ℝ)}
    exact isOpen_lt continuous_const Units.continuous_val
  exact hpos.preimage
    ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      w.property).continuous.units_map _)

private def modulusLocalSubgroup (m : Modulus K)
    (i : ModulusPlaceIndex m) :
    Subgroup (placeCompletion K (modulusPlace m i))ˣ :=
  match i with
  | .inl P => rayLocalSubgroup (K := K) P.1 (m.finite P.1)
  | .inr w => positiveRealSubgroup w.1

private theorem modulus_local_open (m : Modulus K)
    (i : ModulusPlaceIndex m) :
    IsOpen (modulusLocalSubgroup m i :
      Set (placeCompletion K (modulusPlace m i))ˣ) := by
  cases i with
  | inl P =>
      apply ray_local_open P.1 (m.finite P.1)
      rw [Nat.pos_iff_ne_zero, ← Modulus.finite_support_iff]
      exact P.2
  | inr w => exact positive_real_open w.1

private def ideleModulusPlace (m : Modulus K)
    (a : IdeleGroup (OK K) K) (i : ModulusPlaceIndex m) :
    (placeCompletion K (modulusPlace m i))ˣ :=
  match i with
  | .inl P => a.2.1 P.1
  | .inr w => MulEquiv.piUnits a.1 w.1.1

private def localApproximationTarget (m : Modulus K)
    (a : IdeleGroup (OK K) K) (i : ModulusPlaceIndex m) :
    Set (placeCompletion K (modulusPlace m i)) :=
  Units.val ''
    ({ideleModulusPlace m a i} *
      (modulusLocalSubgroup m i :
        Set (placeCompletion K (modulusPlace m i))ˣ))

private theorem approximation_target_open (m : Modulus K)
    (a : IdeleGroup (OK K) K) (i : ModulusPlaceIndex m) :
    IsOpen (localApproximationTarget m a i) := by
  cases i with
  | inl P =>
      simp only [localApproximationTarget, ideleModulusPlace,
        modulusLocalSubgroup, modulusPlace, placeCompletion]
      exact Units.isOpenEmbedding_val.isOpenMap _
        (ray_local_open P.1 (m.finite P.1)
          (by
            rw [Nat.pos_iff_ne_zero, ← Modulus.finite_support_iff]
            exact P.2)).mul_left
  | inr w =>
      simp only [localApproximationTarget, ideleModulusPlace,
        modulusLocalSubgroup, modulusPlace, placeCompletion]
      exact Units.isOpenEmbedding_val.isOpenMap _
        (positive_real_open w.1).mul_left

private theorem modulus_approximation_target
    (m : Modulus K) (a : IdeleGroup (OK K) K) (i : ModulusPlaceIndex m) :
    (ideleModulusPlace m a i : placeCompletion K (modulusPlace m i)) ∈
      localApproximationTarget m a i := by
  refine ⟨ideleModulusPlace m a i, ?_, rfl⟩
  rw [Set.singleton_mul]
  exact ⟨1, (modulusLocalSubgroup m i).one_mem, by simp⟩

private def modulusApproximationTarget (m : Modulus K)
    (a : IdeleGroup (OK K) K) :
    Set ((i : ModulusPlaceIndex m) →
      placeCompletion K (modulusPlace m i)) :=
  Set.univ.pi (localApproximationTarget m a)

private theorem modulus_approximation_open (m : Modulus K)
    (a : IdeleGroup (OK K) K) :
    IsOpen (modulusApproximationTarget m a) := by
  apply isOpen_set_pi Set.finite_univ
  intro i _
  exact approximation_target_open m a i

private theorem modulus_approximation_nonempty (m : Modulus K)
    (a : IdeleGroup (OK K) K) :
    (modulusApproximationTarget m a).Nonempty := by
  refine ⟨fun i ↦ (ideleModulusPlace m a i :
    placeCompletion K (modulusPlace m i)), ?_⟩
  intro i _
  exact modulus_approximation_target m a i

private theorem adjustment_modulus_ideles
    (m : Modulus K) (a : IdeleGroup (OK K) K) :
    ∃ b : Kˣ,
      a * (principalIdele (OK K) K b)⁻¹ ∈ modulusIdeles m := by
  classical
  by_cases hindex : Nonempty (ModulusPlaceIndex m)
  · obtain ⟨b, hb⟩ := (modulus_diagonal_range m).exists_mem_open
      (modulus_approximation_open m a)
      (modulus_approximation_nonempty m a)
    have hb0 : b ≠ 0 := by
      let i₀ : ModulusPlaceIndex m := Classical.choice hindex
      have hi := hb i₀ (Set.mem_univ i₀)
      obtain ⟨c, hc, hcb⟩ := hi
      intro hbzero
      subst b
      have hzero : modulusCoordinateMap m i₀
          ((WithAbs.equiv (modulusAbsoluteValue m i₀)).symm 0) = 0 := by
        cases i₀ <;> rfl
      change (c : placeCompletion K (modulusPlace m i₀)) =
        modulusCoordinateMap m i₀
          ((WithAbs.equiv (modulusAbsoluteValue m i₀)).symm 0) at hcb
      rw [hzero] at hcb
      exact c.ne_zero hcb
    let bu : Kˣ := Units.mk0 b hb0
    refine ⟨bu, ?_⟩
    constructor
    · intro P hP
      let i : ModulusPlaceIndex m := .inl ⟨P, hP⟩
      have hi := hb i (Set.mem_univ i)
      obtain ⟨c, hc, hcb⟩ := hi
      rw [Set.singleton_mul] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      dsimp only [i, modulusPlace, placeCompletion, ideleModulusPlace,
        modulusLocalSubgroup] at h hh hcb
      let aP : (P.adicCompletion K)ˣ := a.2.1 P
      let pP : (P.adicCompletion K)ˣ :=
        (principalIdele (OK K) K bu).2.1 P
      let hP : (P.adicCompletion K)ˣ :=
        Units.mk0 (h : P.adicCompletion K) h.ne_zero
      have hhP : hP ∈ rayLocalSubgroup (K := K) P (m.finite P) := by
        have heq : hP = h := Units.ext rfl
        rw [heq]
        exact hh
      have hprincipal :
          pP = aP * hP := by
        dsimp only [pP]
        rw [principal_idele_finite]
        apply Units.ext
        change algebraMap K (P.adicCompletion K) b =
          ((aP * hP : (P.adicCompletion K)ˣ) : P.adicCompletion K)
        simpa only [i, modulusCoordinateMap, modulusAbsoluteValue,
          aP, hP, Units.val_mk0, RingEquiv.apply_symm_apply,
          FinitePlace.embedding_apply] using hcb.symm
      change aP * pP⁻¹ ∈
        rayLocalSubgroup (K := K) P (m.finite P)
      rw [hprincipal]
      convert (rayLocalSubgroup (K := K) P
        (m.finite P)).inv_mem hhP using 1
      change aP * (aP * hP)⁻¹ = hP⁻¹
      rw [mul_inv_rev]
      calc
        aP * (hP⁻¹ * aP⁻¹) = hP⁻¹ * (aP * aP⁻¹) := by ac_rfl
        _ = hP⁻¹ := by simp
    · intro w hw
      let i : ModulusPlaceIndex m := .inr ⟨w, hw⟩
      have hi := hb i (Set.mem_univ i)
      obtain ⟨c, hc, hcb⟩ := hi
      rw [Set.singleton_mul] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      dsimp only [i, modulusPlace, placeCompletion, ideleModulusPlace,
        modulusLocalSubgroup] at h hh hcb
      let aW : w.1.Completionˣ := MulEquiv.piUnits a.1 w.1
      let pW : w.1.Completionˣ :=
        MulEquiv.piUnits (principalIdele (OK K) K bu).1 w.1
      let hW : w.1.Completionˣ :=
        Units.mk0 (h : w.1.Completion) h.ne_zero
      have hhW : hW ∈ positiveRealSubgroup w := by
        have heq : hW = h := Units.ext rfl
        rw [heq]
        exact hh
      have hprincipal :
          pW = aW * hW := by
        dsimp only [pW]
        rw [principal_idele_infinite]
        apply Units.ext
        change completionEmbedding w.1.1 b =
          ((aW * hW : w.1.Completionˣ) : w.1.Completion)
        simpa only [i, modulusCoordinateMap, modulusAbsoluteValue,
          aW, hW, Units.val_mk0,
          RingEquiv.apply_symm_apply] using hcb.symm
      have hvalue :
          MulEquiv.piUnits
              (a * (principalIdele (OK K) K bu)⁻¹).1 w.1 =
            aW * pW⁻¹ := by
        change MulEquiv.piUnits
            (a.1 * (principalIdele (OK K) K bu).1⁻¹) w.1 = _
        calc
          _ = (MulEquiv.piUnits a.1 *
                MulEquiv.piUnits (principalIdele (OK K) K bu).1⁻¹) w.1 :=
            congrFun (map_mul (MulEquiv.piUnits :
              (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) →
                v.Completionˣ)) a.1
                  (principalIdele (OK K) K bu).1⁻¹) w.1
          _ = (MulEquiv.piUnits a.1 *
                (MulEquiv.piUnits
                  (principalIdele (OK K) K bu).1)⁻¹) w.1 :=
            congrArg (fun z ↦ (MulEquiv.piUnits a.1 * z) w.1)
              (map_inv (MulEquiv.piUnits :
                (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) →
                  v.Completionˣ))
                    (principalIdele (OK K) K bu).1)
          _ = _ := rfl
      rw [hvalue, hprincipal]
      convert (positiveRealSubgroup w).inv_mem hhW using 1
      change aW * (aW * hW)⁻¹ = hW⁻¹
      rw [mul_inv_rev]
      calc
        aW * (hW⁻¹ * aW⁻¹) = hW⁻¹ * (aW * aW⁻¹) := by ac_rfl
        _ = hW⁻¹ := by simp
  · refine ⟨1, ?_⟩
    constructor
    · intro P hP
      exact (hindex ⟨.inl ⟨P, hP⟩⟩).elim
    · intro w hw
      exact (hindex ⟨.inr ⟨w, hw⟩⟩).elim

/-- The unconditional weak-approximation input in Proposition V.4.6(b). -/
theorem weakApproximation (m : Modulus K) :
    WeakApproximation m := by
  intro q
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective (principalIdeles (OK K) K) q
  obtain ⟨b, hb⟩ := adjustment_modulus_ideles m a
  let c : modulusIdeles m :=
    ⟨a * (principalIdele (OK K) K b)⁻¹, hb⟩
  refine ⟨c, ?_⟩
  change QuotientGroup.mk' (principalIdeles (OK K) K)
      (a * (principalIdele (OK K) K b)⁻¹) =
    QuotientGroup.mk' (principalIdeles (OK K) K) a
  rw [map_mul, map_inv]
  have hprincipal : QuotientGroup.mk' (principalIdeles (OK K) K)
      (principalIdele (OK K) K b) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨b, rfl⟩
  rw [hprincipal, inv_one, mul_one]

end

end Submission.CField.HNorm
