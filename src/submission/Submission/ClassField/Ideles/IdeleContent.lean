import Submission.ClassField.Ideles.IdeleIdealMap
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Chapter V, Section 4, Statement 4.4

The content of an idèle is the product of its normalized local absolute
values.  At a finite prime `v`, the normalized absolute value is
`N(v) ^ (-ord_v x_v)`; this is evaluated from the finite-support exponent
vector constructed in Statement 4.1.  At an infinite prime it is the usual
norm, raised to the place multiplicity (one at a real place and two at a
complex place).

We use `(ℝ≥0)ˣ` as the literal group `ℝ_{>0}`: its elements are precisely the
strictly positive nonnegative real numbers.
-/

namespace Submission.CField.Ideles

open IsDedekindDomain NumberField
open scoped NNReal nonZeroDivisors WithZero

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private abbrev O := NumberField.RingOfIntegers K

/-- Forget positivity and view a positive real unit as a real number. -/
private def positiveUnitReal : ℝ≥0ˣ →* ℝ :=
  (Nonneg.coeRingHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
    (Units.coeHom ℝ≥0)

private theorem positive_unit_real (u : ℝ≥0ˣ) :
    positiveUnitReal u = 1 ↔ u = 1 := by
  constructor
  · intro h
    apply Units.ext
    apply NNReal.eq
    exact h
  · rintro rfl
    exact map_one _

/-- The positive real unit given by the absolute norm of a finite prime. -/
private def primeNormUnit (v : HeightOneSpectrum (O K)) : ℝ≥0ˣ :=
  Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v)

/-- Evaluation of a finite prime-exponent vector by
`(n_v) ↦ ∏_v N(v)^(-n_v)`. -/
private noncomputable def finiteExponentContent :
    Multiplicative (HeightOneSpectrum (O K) →₀ ℤ) →* ℝ≥0ˣ :=
  AddMonoidHom.toMultiplicative <|
    Finsupp.liftAddHom fun v ↦
      zmultiplesHom (Additive ℝ≥0ˣ) (Additive.ofMul (primeNormUnit K v)⁻¹)

private theorem finite_exponent_content
    (e : HeightOneSpectrum (O K) →₀ ℤ) :
    finiteExponentContent K (Multiplicative.ofAdd e) =
      e.prod fun v n ↦ (primeNormUnit K v) ^ (-n) := by
  change Additive.toMul
      ((Finsupp.liftAddHom fun v ↦
        zmultiplesHom (Additive ℝ≥0ˣ)
          (Additive.ofMul (primeNormUnit K v)⁻¹)) e) = _
  rw [Finsupp.liftAddHom_apply]
  classical
  simp only [Finsupp.sum, Finsupp.prod, zmultiplesHom_apply]
  change (∏ x ∈ e.support, (primeNormUnit K x)⁻¹ ^ e x) =
    ∏ x ∈ e.support, primeNormUnit K x ^ (-e x)
  apply Finset.prod_congr rfl
  intro x _
  rw [inv_zpow, ← zpow_neg]

/-- The product of the normalized absolute values at all finite places. -/
noncomputable def finiteIdeleContent :
    FiniteIdeles (O K) K →* ℝ≥0ˣ :=
  (finiteExponentContent K).comp
    (ideleExponentHom (O K) K)

private theorem prime_zpow_order
    (v : HeightOneSpectrum (O K)) (z : (v.adicCompletion K)ˣ) :
    (primeNormUnit K v) ^
        (-(-WithZero.log (Valued.v (z : v.adicCompletion K)))) =
      Units.map nnnormHom.toMonoidHom z := by
  have hz : Valued.v (z : v.adicCompletion K) ≠ 0 := by simp
  apply Units.ext
  simp only [primeNormUnit, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    Units.coe_map]
  change (v.asIdeal.absNorm : ℝ≥0) ^
      (-(-WithZero.log (Valued.v (z : v.adicCompletion K)))) =
        ‖(z : v.adicCompletion K)‖₊
  have hnorm : ‖(z : v.adicCompletion K)‖₊ =
      WithZeroMulInt.toNNReal
        (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
          (Valued.v (z : v.adicCompletion K)) := by
    apply NNReal.eq
    simpa only [coe_nnnorm] using
      (FinitePlace.norm_def (v := v) (z : v.adicCompletion K))
  rw [hnorm, WithZeroMulInt.toNNReal_neg_apply
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hz]
  congr 1
  rw [neg_neg]
  calc
    WithZero.log (Valued.v (z : v.adicCompletion K)) =
        WithZero.log (↑(WithZero.unzero hz) : ℤᵐ⁰) :=
      congrArg WithZero.log (WithZero.coe_unzero hz).symm
    _ = (WithZero.unzero hz).toAdd := rfl

/-- The finite content is the finite product of the normalized norms of all
finite coordinates. -/
theorem idele_content_finprod (x : FiniteIdeles (O K) K) :
    finiteIdeleContent K x =
      ∏ᶠ v : HeightOneSpectrum (O K),
        Units.map nnnormHom.toMonoidHom (x.1 v) := by
  let e := (ideleExponentHom (O K) K x).toAdd
  have hcontent : finiteIdeleContent K x =
      e.prod fun v n ↦ (primeNormUnit K v) ^ (-n) := by
    change finiteExponentContent K (ideleExponentHom (O K) K x) = _
    simpa [e] using finite_exponent_content K e
  rw [hcontent]
  have hsupp : (fun v : HeightOneSpectrum (O K) ↦
      Units.map nnnormHom.toMonoidHom (x.1 v)).mulSupport ⊆ e.support := by
    intro v hv
    by_contra hnot
    have he0 : e v = 0 := by simpa using hnot
    apply hv
    change Units.map nnnormHom.toMonoidHom (x.1 v) = 1
    rw [← prime_zpow_order K v (x.1 v),
      ← idele_exponent_hom (O K) K x v]
    change (primeNormUnit K v) ^ (-(e v)) = 1
    rw [he0, neg_zero, zpow_zero]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro v _
  change (primeNormUnit K v) ^ (-(e v)) =
    Units.map nnnormHom.toMonoidHom (x.1 v)
  rw [idele_exponent_hom]
  exact prime_zpow_order K v (x.1 v)

private theorem positive_idele_content
    (x : FiniteIdeles (O K) K) :
    positiveUnitReal (finiteIdeleContent K x) =
      ∏ᶠ v : HeightOneSpectrum (O K),
        ‖((x.1 v : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := by
  rw [idele_content_finprod]
  rw [MonoidHom.map_finprod_of_preimage_one (positiveUnitReal)
    (fun u hu ↦ (positive_unit_real u).mp hu)]
  apply finprod_congr
  intro v
  rfl

/-- The product of the normalized absolute values at all infinite places. -/
noncomputable def infiniteIdeleContent :
    (InfiniteAdeleRing K)ˣ →* ℝ≥0ˣ where
  toFun x := ∏ v : InfinitePlace K,
    (Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits x) v)) ^ v.mult
  map_one' := by
    change (∏ v : InfinitePlace K,
      (Units.map nnnormHom.toMonoidHom
        ((MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ)) v)) ^ v.mult) = 1
    apply Finset.prod_eq_one
    intro v _
    have h := congrFun (map_one (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ))) v
    calc
      (Units.map nnnormHom.toMonoidHom
          ((MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ)) v)) ^ v.mult =
          (Units.map nnnormHom.toMonoidHom (1 : v.Completionˣ)) ^ v.mult :=
        congrArg (fun z : v.Completionˣ ↦
          (Units.map nnnormHom.toMonoidHom z) ^ v.mult) h
      _ = 1 := by rw [map_one, one_pow]
  map_mul' x y := by
    change (∏ v : InfinitePlace K,
      (Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits (x * y)) v)) ^ v.mult) = _
    calc
      _ = ∏ v : InfinitePlace K,
          ((Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits x) v)) *
            (Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits y) v))) ^ v.mult := by
        apply Finset.prod_congr rfl
        intro v _
        have h := congrFun (map_mul (MulEquiv.piUnits :
          (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ)) x y) v
        calc
          (Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits (x * y)) v)) ^ v.mult =
              (Units.map nnnormHom.toMonoidHom
                (((MulEquiv.piUnits x) v) * ((MulEquiv.piUnits y) v))) ^ v.mult :=
            congrArg (fun z : v.Completionˣ ↦
              (Units.map nnnormHom.toMonoidHom z) ^ v.mult) h
          _ = _ := by rw [map_mul]
      _ = _ := by
        simp only [mul_pow, Finset.prod_mul_distrib]

private theorem positive_real_content
    (x : (InfiniteAdeleRing K)ˣ) :
    positiveUnitReal (infiniteIdeleContent K x) =
      ‖(x : InfiniteAdeleRing K)‖ := by
  unfold infiniteIdeleContent
  rw [InfiniteAdeleRing.norm_def]
  change positiveUnitReal
      (∏ v : InfinitePlace K,
        (Units.map nnnormHom.toMonoidHom ((MulEquiv.piUnits x) v)) ^ v.mult) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro v _
  rw [map_pow]
  congr 1

/-- The content of an idèle supported at one infinite place is its normalized
local absolute value. -/
theorem infinite_content_embedding
    (v : InfinitePlace K) (x : v.Completionˣ) :
    infiniteIdeleContent K (infiniteLocalEmbedding K v x) =
      (Units.map nnnormHom.toMonoidHom x) ^ v.mult := by
  classical
  unfold infiniteIdeleContent
  have h : MulEquiv.piUnits (infiniteLocalEmbedding K v x) =
      Pi.mulSingle v x := by
    change MulEquiv.piUnits (MulEquiv.piUnits.symm (Pi.mulSingle v x)) = _
    exact MulEquiv.apply_symm_apply _ _
  change (∏ w : InfinitePlace K,
    (Units.map nnnormHom.toMonoidHom
      ((MulEquiv.piUnits (infiniteLocalEmbedding K v x)) w)) ^ w.mult) = _
  rw [h, Finset.prod_eq_single v]
  · rw [Pi.mulSingle_eq_same]
  · intro w _ hwv
    rw [Pi.mulSingle_eq_of_ne hwv, map_one, one_pow]
  · simp

set_option maxHeartbeats 1000000 in
-- Choosing a square root at a complex place makes the normalized local
-- absolute value attain an arbitrary positive real number.
/-- The infinite-place content homomorphism is onto `ℝ_{>0}`. -/
theorem infinite_content_surjective :
    Function.Surjective (infiniteIdeleContent K) := by
  intro r
  let v : InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (InfinitePlace K))
  rcases v.isReal_or_isComplex with hv | hv
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have hr : 0 < (r : ℝ≥0) := (pos_iff_ne_zero).2 r.ne_zero
    have hrreal : 0 < ((r : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr hr
    let z0 : v.Completion := e.symm ((r : ℝ≥0) : ℝ)
    have hz0 : z0 ≠ 0 := by
      intro hz
      apply hrreal.ne'
      calc
        ((r : ℝ≥0) : ℝ) = e z0 := by simp [z0]
        _ = e 0 := congrArg e hz
        _ = 0 := map_zero e
    let z : v.Completionˣ := Units.mk0 z0 hz0
    refine ⟨infiniteLocalEmbedding K v z, ?_⟩
    rw [infinite_content_embedding,
      InfinitePlace.mult_isReal ⟨v, hv⟩, pow_one]
    apply Units.ext
    change ‖z0‖₊ = (r : ℝ≥0)
    have heIso : Isometry e :=
      InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
    rw [← heIso.nnnorm_map_of_map_zero (map_zero e) z0]
    simp [z0, e]
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    have hr : 0 < (r : ℝ≥0) := (pos_iff_ne_zero).2 r.ne_zero
    have hrreal : 0 < ((r : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr hr
    have hsqrt : 0 < Real.sqrt ((r : ℝ≥0) : ℝ) :=
      Real.sqrt_pos.2 hrreal
    let z0 : v.Completion :=
      e.symm (Real.sqrt ((r : ℝ≥0) : ℝ) : ℂ)
    have hz0 : z0 ≠ 0 := by
      intro hz
      apply Complex.ofReal_ne_zero.mpr hsqrt.ne'
      calc
        (Real.sqrt ((r : ℝ≥0) : ℝ) : ℂ) = e z0 := by simp [z0]
        _ = e 0 := congrArg e hz
        _ = 0 := map_zero e
    let z : v.Completionˣ := Units.mk0 z0 hz0
    refine ⟨infiniteLocalEmbedding K v z, ?_⟩
    rw [infinite_content_embedding,
      InfinitePlace.mult_isComplex ⟨v, hv⟩]
    apply Units.ext
    change ‖z0‖₊ ^ (2 : ℕ) = (r : ℝ≥0)
    apply NNReal.eq
    simp only [NNReal.coe_pow, coe_nnnorm]
    have heIso : Isometry e :=
      InfinitePlace.Completion.isometry_extensionEmbedding v
    rw [← heIso.norm_map_of_map_zero (map_zero e) z0]
    simp [z0, e, Real.sq_sqrt hrreal.le]

/-- **Statement V.4.4, the canonical content homomorphism.** -/
noncomputable def ideleContent :
    IdeleGroup (O K) K →* ℝ≥0ˣ where
  toFun x := infiniteIdeleContent K x.1 * finiteIdeleContent K x.2
  map_one' := by
    change infiniteIdeleContent K 1 * finiteIdeleContent K 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change infiniteIdeleContent K (x.1 * y.1) *
        finiteIdeleContent K (x.2 * y.2) = _
    rw [map_mul, map_mul]
    ac_rfl

/-- **Statement V.4.4, surjectivity.** -/
theorem ideleContent_surjective : Function.Surjective (ideleContent K) := by
  intro r
  obtain ⟨x, hx⟩ := infinite_content_surjective K r
  refine ⟨(x, 1), ?_⟩
  change infiniteIdeleContent K x * finiteIdeleContent K 1 = r
  rw [map_one, mul_one, hx]

private theorem positive_real_principal (x : Kˣ) :
    positiveUnitReal
        (infiniteIdeleContent K
          (principalIdele (O K) K x).1) =
      |Algebra.norm ℚ (x : K)| := by
  rw [positive_real_content]
  change ‖algebraMap K (InfiniteAdeleRing K) (x : K)‖ = _
  exact InfiniteAdeleRing.coe_norm_eq_abs_norm (x : K)

private theorem positive_unit_principal (x : Kˣ) :
    positiveUnitReal
        (finiteIdeleContent K
          (principalIdele (O K) K x).2) =
      |Algebra.norm ℚ (x : K)|⁻¹ := by
  rw [positive_idele_content]
  change (∏ᶠ v : HeightOneSpectrum (O K),
    ‖FinitePlace.embedding v (x : K)‖) = _
  simpa only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply] using
      (FinitePlace.prod_eq_inv_abs_norm (K := K) x.ne_zero)

/-- The product formula says precisely that every principal idèle has
content one. -/
theorem ideleContent_principal (x : Kˣ) :
    ideleContent K (principalIdele (O K) K x) = 1 := by
  apply (positive_unit_real
    (ideleContent K (principalIdele (O K) K x))).mp
  change positiveUnitReal
      (infiniteIdeleContent K (principalIdele (O K) K x).1 *
        finiteIdeleContent K (principalIdele (O K) K x).2) = 1
  rw [map_mul, positive_real_principal,
    positive_unit_principal]
  norm_cast
  exact mul_inv_cancel₀ (abs_ne_zero.mpr
    ((Algebra.norm_ne_zero_iff (R := ℚ) (S := K)).2 x.ne_zero))

/-- The norm-one idèles `ℐ¹ = ker(c)`. -/
def normOneIdeles : Subgroup (IdeleGroup (O K) K) :=
  (ideleContent K).ker

/-- Equivalently, the subgroup of principal idèles is contained in
`ℐ¹ = ker(c)`. -/
theorem principal_ideles_one :
    principalIdeles (O K) K ≤ normOneIdeles K := by
  rintro _ ⟨x, rfl⟩
  exact ideleContent_principal K x

/-- The displayed description `ℐ¹ = {a | c(a)=1}` in Statement V.4.4. -/
theorem norm_one_ideles (a : IdeleGroup (O K) K) :
    a ∈ normOneIdeles K ↔ ideleContent K a = 1 :=
  Iff.rfl

end

end Submission.CField.Ideles
