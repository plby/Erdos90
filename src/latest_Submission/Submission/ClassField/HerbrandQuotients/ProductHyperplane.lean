import Submission.ClassField.HerbrandQuotients.UpperPlaceCardinality
import Submission.NumberTheory.Locals.NumberFieldFormula
import Mathlib.LinearAlgebra.Span.TensorProduct

/-!
# The product-formula hyperplane in Proposition VII.3.1

The completion places used to build the common ambient representation lie
literally over the base absolute values.  At a finite place this can differ
from the globally normalized finite-place absolute value by a positive real
power; at a complex infinite place the product formula uses multiplicity
two.  We record those weights explicitly and obtain Milne's hyperplane
containing the logarithmic image.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open scoped BigOperators NNReal

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The chosen upper completion coordinate centered at a finite prime in
`T`. -/
noncomputable def upperPlacePrime
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    upperPlacesAt (K := K) (L := L) S := by
  let P : FinitePrime K := Q.1.under (NumberField.RingOfIntegers K)
  let vS : S := ⟨Sum.inl P, Q.2⟩
  let Qabove : PrimesAboveBase (K := K) (L := L) P := ⟨Q.1, rfl⟩
  let qFactor : UpperPrimeFactors (K := K) (L := L) P :=
    (upperAboveBase
      (K := K) (L := L) P).symm Qabove
  exact ⟨vS, (placesAboveFactors
    (K := K) (L := L) P).symm qFactor⟩

/-- The chosen upper coordinate representing an infinite place of `L`. -/
noncomputable def infiniteUpperPlace
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (w : InfinitePlace L) :
    upperPlacesAt (K := K) (L := L) S :=
  let v : InfinitePlace K := w.comap (algebraMap K L)
  ⟨⟨Sum.inr v, hSinf v⟩,
    ⟨w.1, infinite_lies_comap v w rfl⟩⟩

private theorem upper_place_equiv
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    (upperPlacePrime (K := K) (L := L) S Q).2.1.IsEquiv
      (FinitePlace.mk Q.1).val := by
  let P : FinitePrime K := Q.1.under (NumberField.RingOfIntegers K)
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let Qabove : PrimesAboveBase (K := K) (L := L) P := ⟨Q.1, rfl⟩
  let qFactor : UpperPrimeFactors (K := K) (L := L) P :=
    (upperAboveBase
      (K := K) (L := L) P).symm Qabove
  let z := (placesAboveFactors
    (K := K) (L := L) P).symm qFactor
  have hfac : placeUpperFactor (K := K) (L := L) P z = qFactor :=
    (placesAboveFactors
      (K := K) (L := L) P).apply_symm_apply qFactor
  have hcenter : placeAboveBase
      (K := K) (L := L) P z = Qabove := by
    apply (upperAboveBase
      (K := K) (L := L) P).symm.injective
    change placeUpperFactor (K := K) (L := L) P z = qFactor
    exact hfac
  have hcenter' : nonarchimedeanHeightSpectrum z.1
      (absolute_extension_nontrivial (FinitePlace.mk P).val z)
      (absolute_extension_nonarchimedean (FinitePlace.mk P).val z) = Q.1 := by
    have := congrArg (fun R : PrimesAboveBase
      (K := K) (L := L) P => R.1) hcenter
    simpa only [placeAboveBase] using this
  change z.1.IsEquiv (FinitePlace.mk Q.1).val
  have h := place_centered_prime z.1
    (absolute_extension_nontrivial (FinitePlace.mk P).val z)
    (absolute_extension_nonarchimedean (FinitePlace.mk P).val z)
  rwa [hcenter'] at h

/-- The positive exponent converting the upper completion absolute value
at `Q` to the globally normalized finite-place absolute value. -/
noncomputable def placeLogScale
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) : ℝ :=
  Classical.choose (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (upper_place_equiv (K := K) (L := L) S Q))

theorem log_scale_pos
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    0 < placeLogScale (K := K) (L := L) S Q :=
  (Classical.choose_spec (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (upper_place_equiv (K := K) (L := L) S Q))).1

theorem rpow_log_scale
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S)
    (x : L) :
    (upperPlacePrime (K := K) (L := L) S Q).2.1 x ^
        placeLogScale (K := K) (L := L) S Q =
      (FinitePlace.mk Q.1).1 x := by
  exact congrFun
    (Classical.choose_spec (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
      (upper_place_equiv (K := K) (L := L) S Q))).2 x

/-- The weighted sum of coordinates whose vanishing is the logarithmic
form of the number-field product formula. -/
noncomputable def upperPlaceLog
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    (upperPlacesAt (K := K) (L := L) S → ℝ) →ₗ[ℝ] ℝ := by
  letI : Fintype (primesAbovePlaces (K := K) (L := L) S) :=
    (primes_above_places (K := K) (L := L) S).fintype
  exact
    { toFun := fun f =>
        (∑ Q : primesAbovePlaces (K := K) (L := L) S,
          placeLogScale (K := K) (L := L) S Q *
            f (upperPlacePrime (K := K) (L := L) S Q)) +
        ∑ w : InfinitePlace L, (w.mult : ℝ) *
          f (infiniteUpperPlace (K := K) (L := L) S hSinf w)
      map_add' := by
        intro f g
        simp only [Pi.add_apply]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro r f
        simp only [Pi.smul_apply, smul_eq_mul]
        calc
          (∑ Q : primesAbovePlaces (K := K) (L := L) S,
              placeLogScale (K := K) (L := L) S Q *
                (r * f (upperPlacePrime (K := K) (L := L) S Q))) +
              ∑ w : InfinitePlace L, (w.mult : ℝ) *
                (r * f (infiniteUpperPlace
                  (K := K) (L := L) S hSinf w)) =
            (∑ Q : primesAbovePlaces (K := K) (L := L) S,
              r * (placeLogScale (K := K) (L := L) S Q *
                f (upperPlacePrime (K := K) (L := L) S Q))) +
              ∑ w : InfinitePlace L, r * ((w.mult : ℝ) *
                f (infiniteUpperPlace
                  (K := K) (L := L) S hSinf w)) := by
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro Q _
              ring
            · apply Finset.sum_congr rfl
              intro w _
              ring
          _ = r * (∑ Q : primesAbovePlaces
                (K := K) (L := L) S,
              placeLogScale (K := K) (L := L) S Q *
                f (upperPlacePrime (K := K) (L := L) S Q)) +
              r * (∑ w : InfinitePlace L, (w.mult : ℝ) *
                f (infiniteUpperPlace
                  (K := K) (L := L) S hSinf w)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
          _ = r * ((∑ Q : primesAbovePlaces
                (K := K) (L := L) S,
              placeLogScale (K := K) (L := L) S Q *
                f (upperPlacePrime (K := K) (L := L) S Q)) +
              ∑ w : InfinitePlace L, (w.mult : ℝ) *
                f (infiniteUpperPlace
                  (K := K) (L := L) S hSinf w)) := by ring }

/-- Valuation one is equivalent to value one for the normalized finite
absolute value. -/
private theorem place_value_valuation
    (Q : FinitePrime L) {x : L} (hx : Q.valuation L x = 1) :
    (FinitePlace.mk Q).1 x = 1 := by
  have h' :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero Q)
          (Q.valuation L x) = 1 :=
    (WithZeroMulInt.toNNReal_eq_one_iff
      (Q.valuation L x)
      (HeightOneSpectrum.absNorm_ne_zero Q)
      (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal Q))).mpr hx
  have hnorm : ‖FinitePlace.embedding Q x‖ = 1 := by
    rw [FinitePlace.norm_embedding']
    exact_mod_cast h'
  simpa only [FinitePlace.mk_apply] using hnorm

theorem place_log_zmultiples
    (Q : FinitePrime L) (x : Lˣ) :
    Real.log ((FinitePlace.mk Q).1 (x : L)) ∈
      AddSubgroup.zmultiples
        (Real.log (Ideal.absNorm Q.asIdeal : ℝ)) := by
  rw [AddSubgroup.mem_zmultiples_iff]
  let k : ℤ := Multiplicative.toAdd (Q.valuationOfNeZero x)
  refine ⟨k, ?_⟩
  rw [show (FinitePlace.mk Q).1 (x : L) =
      ‖FinitePlace.embedding Q (x : L)‖ by rfl,
    FinitePlace.norm_embedding']
  have hval := Q.valuationOfNeZero_eq x
  rw [← hval]
  let m : Multiplicative ℤ := Q.valuationOfNeZero x
  have hm : ((m : WithZero (Multiplicative ℤ)) ≠ 0) := WithZero.coe_ne_zero
  have hu : WithZero.unzero hm = m := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
  have hto :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero Q)
          (m : WithZero (Multiplicative ℤ)) =
        (Ideal.absNorm Q.asIdeal : ℝ≥0) ^ k := by
    rw [WithZeroMulInt.toNNReal_neg_apply
      (HeightOneSpectrum.absNorm_ne_zero Q) hm, hu]
  rw [hto, NNReal.coe_zpow, Real.log_zpow, zsmul_eq_mul]
  norm_num

omit [FiniteDimensional K L] [IsGalois K L] in
/-- For a `T`-unit, the finite part of the global product formula is
supported on the finite primes belonging to `T`. -/
theorem finprod_above_places
    (S : Finset (NumberFieldPlace K))
    (x : unitsAtPlaces (K := K) (L := L) S) :
    (∏ᶠ Q : FinitePrime L,
        (FinitePlace.mk Q).1 (((x : Lˣ) : L))) =
      ∏ Q : primesAbovePlaces (K := K) (L := L) S,
        (FinitePlace.mk Q.1).1 (((x : Lˣ) : L)) := by
  let T := primesAbovePlaces (K := K) (L := L) S
  have hT : T.Finite :=
    primes_above_places (K := K) (L := L) S
  letI : Fintype T := hT.fintype
  let f : FinitePrime L → ℝ := fun Q =>
    (FinitePlace.mk Q).1 (((x : Lˣ) : L))
  have hsupp : Function.mulSupport f ⊆ T := by
    intro Q hQ
    by_contra hQT
    apply hQ
    exact place_value_valuation Q (x.property Q hQT)
  calc
    (∏ᶠ Q : FinitePrime L, f Q) =
        ∏ Q ∈ hT.toFinset, f Q :=
      finprod_eq_prod_of_mulSupport_subset_of_finite f hsupp hT
    _ = ∏ Q : T, f Q.1 := (Finset.prod_set_coe T).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Logarithmic form of the number-field product formula, with the finite
product restricted to the actual finite part of `T`. -/
theorem number_normalized_log
    (S : Finset (NumberFieldPlace K))
    (x : unitsAtPlaces (K := K) (L := L) S) :
    (∑ Q : primesAbovePlaces (K := K) (L := L) S,
        Real.log ((FinitePlace.mk Q.1).1 (((x : Lˣ) : L)))) +
      ∑ w : InfinitePlace L,
        (w.mult : ℝ) * Real.log (w (((x : Lˣ) : L))) = 0 := by
  letI : Fintype (primesAbovePlaces (K := K) (L := L) S) :=
    (primes_above_places (K := K) (L := L) S).fintype
  let xL : L := (((x : Lˣ) : L))
  have hxL : xL ≠ 0 := (x : Lˣ).ne_zero
  have hp := number_product_formula (K := L) hxL
  have hreindex : (∏ᶠ w : FinitePlace L, w xL) =
      ∏ᶠ Q : FinitePrime L, (FinitePlace.mk Q).1 xL := by
    simpa [FinitePlace.equivHeightOneSpectrum] using (finprod_comp_equiv
      (FinitePlace.equivHeightOneSpectrum (K := L))
      (f := fun Q : FinitePrime L => (FinitePlace.mk Q).1 xL))
  rw [hreindex,
    finprod_above_places
      (K := K) (L := L) S x] at hp
  have hInfNe : (∏ w : InfinitePlace L, w xL ^ w.mult) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun w _ =>
      pow_ne_zero _ (w.1.ne_zero hxL)
  have hFinNe : (∏ Q : primesAbovePlaces
      (K := K) (L := L) S, (FinitePlace.mk Q.1).1 xL) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun Q _ =>
      (FinitePlace.mk Q.1).1.ne_zero hxL
  have hlog := congrArg Real.log hp
  rw [Real.log_mul hInfNe hFinNe, Real.log_one,
    Real.log_prod (fun w _ => pow_ne_zero _ (w.1.ne_zero hxL)),
    Real.log_prod (fun Q _ => (FinitePlace.mk Q.1).1.ne_zero hxL)] at hlog
  simp_rw [Real.log_pow] at hlog
  simpa [xL, add_comm] using hlog

/-- A rescaled finite coordinate of the raw upper-place logarithm is the
globally normalized finite-place logarithm. -/
theorem log_scale_upper
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S)) :
    placeLogScale (K := K) (L := L) S Q *
        upperUnitLog (K := K) (L := L) S x
          (upperPlacePrime (K := K) (L := L) S Q) =
      Real.log ((FinitePlace.mk Q.1).1
        ((((Additive.toMul x : unitsAtPlaces
          (K := K) (L := L) S) : Lˣ) : L))) := by
  rw [upper_unit_log, ← Real.log_rpow
    ((upperPlacePrime (K := K) (L := L) S Q).2.1.pos
      ((Additive.toMul x : unitsAtPlaces
        (K := K) (L := L) S) : Lˣ).ne_zero)
    (placeLogScale (K := K) (L := L) S Q),
    rpow_log_scale (K := K) (L := L) S Q]

/-- Milne's logarithmic image lies in the weighted product-formula
hyperplane. -/
theorem upper_log_linear
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S)) :
    upperPlaceLog (K := K) (L := L) S hSinf
        (upperUnitLog (K := K) (L := L) S x) = 0 := by
  let xU : unitsAtPlaces (K := K) (L := L) S := Additive.toMul x
  let xL : L := (((xU : Lˣ) : L))
  change
    (∑ Q : primesAbovePlaces (K := K) (L := L) S,
        placeLogScale (K := K) (L := L) S Q *
          Real.log ((upperPlacePrime
            (K := K) (L := L) S Q).2.1 xL)) +
      ∑ w : InfinitePlace L,
        (w.mult : ℝ) * Real.log (w xL) = 0
  have hfinite (Q : primesAbovePlaces (K := K) (L := L) S) :
      placeLogScale (K := K) (L := L) S Q *
          Real.log ((upperPlacePrime
            (K := K) (L := L) S Q).2.1 xL) =
        Real.log ((FinitePlace.mk Q.1).1 xL) := by
    rw [← Real.log_rpow
      ((upperPlacePrime (K := K) (L := L) S Q).2.1.pos
        (xU : Lˣ).ne_zero)
      (placeLogScale (K := K) (L := L) S Q),
      rpow_log_scale (K := K) (L := L) S Q xL]
  simp_rw [hfinite]
  exact number_normalized_log
    (K := K) (L := L) S xU

/-- The constant vector does not lie in the product-formula hyperplane. -/
theorem upper_log_pos
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    0 < upperPlaceLog (K := K) (L := L) S hSinf
      (upperConstantVector (K := K) (L := L) S) := by
  letI : Fintype (primesAbovePlaces (K := K) (L := L) S) :=
    (primes_above_places (K := K) (L := L) S).fintype
  have heval :
      upperPlaceLog (K := K) (L := L) S hSinf
          (upperConstantVector (K := K) (L := L) S) =
        (∑ Q : primesAbovePlaces (K := K) (L := L) S,
          placeLogScale (K := K) (L := L) S Q) +
            ∑ w : InfinitePlace L, (w.mult : ℝ) := by
    simp [upperPlaceLog, upperConstantVector]
  rw [heval]
  have hfinite : 0 ≤
      ∑ Q : primesAbovePlaces (K := K) (L := L) S,
        placeLogScale (K := K) (L := L) S Q :=
    Finset.sum_nonneg fun Q _ =>
      (log_scale_pos (K := K) (L := L) S Q).le
  have hinfinite : 0 < ∑ w : InfinitePlace L, (w.mult : ℝ) := by
    apply Finset.sum_pos
    · intro w _
      exact_mod_cast InfinitePlace.mult_pos (w := w)
    · exact ⟨Classical.choice (inferInstance : Nonempty (InfinitePlace L)),
        Finset.mem_univ _⟩
  linarith

/-- The real span of `M⁰` is contained in the product-formula hyperplane. -/
theorem upper_place_log
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Submodule.span ℝ
        (upperLogLattice (K := K) (L := L) S :
          Set (upperPlacesAt (K := K) (L := L) S → ℝ)) ≤
      LinearMap.ker
        (upperPlaceLog (K := K) (L := L) S hSinf) := by
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact upper_log_linear
    (K := K) (L := L) S hSinf x

/-- The constant vector is outside the real span of `M⁰`. -/
theorem upper_log_real
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    upperConstantVector (K := K) (L := L) S ∉
      Submodule.span ℝ
        (upperLogLattice (K := K) (L := L) S :
          Set (upperPlacesAt (K := K) (L := L) S → ℝ)) := by
  intro he
  have hker := upper_place_log
    (K := K) (L := L) S hSinf he
  exact (ne_of_gt (upper_log_pos
    (K := K) (L := L) S hSinf)) hker

end

end Submission.CField.HQuotie
