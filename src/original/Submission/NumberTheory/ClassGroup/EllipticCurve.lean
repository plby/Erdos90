import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Jacobson.Ring


/-!
# Milne, Algebraic Number Theory, Example 3.22

We prove that the nonsingular affine cubic has a Dedekind coordinate ring and prove the
uncountability assertion in the example.  The analytic identification over `ℂ` with `ℂ / Λ` is
cited by Milne from his algebraic geometry notes; it is not currently available in Mathlib.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

/-- The short Weierstrass curve `Y² = X³ + aX + b` from Example 3.22. -/
def Curve (a b : ℂ) : WeierstrassCurve.Affine ℂ :=
  ⟨0, 0, 0, a, b⟩

@[simp]
theorem Curve_discriminant (a b : ℂ) :
    (Curve a b).Δ = 16 * (-4 * a ^ 3 - 27 * b ^ 2) := by
  simp only [Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A nonzero short discriminant makes the curve in Example 3.22 elliptic. -/
theorem Curve_isElliptic {a b : ℂ} (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0) :
    (Curve a b).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, Curve_discriminant]
  exact mul_ne_zero (by norm_num) hΔ

private noncomputable def ellipticCurve22 (a b : ℂ) :
    (Curve a b).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.XClass (Curve a b) 0

private noncomputable def ellipticCurveY (a b : ℂ) :
    (Curve a b).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.YClass (Curve a b) 0

private theorem YClass_sq (a b : ℂ) :
    ellipticCurveY a b ^ 2 =
      ellipticCurve22 a b ^ 3 +
        algebraMap ℂ (Curve a b).CoordinateRing a *
          ellipticCurve22 a b +
        algebraMap ℂ (Curve a b).CoordinateRing b := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp [Curve, WeierstrassCurve.Affine.polynomial]

private theorem XClass_eq (a b x : ℂ) :
    WeierstrassCurve.Affine.CoordinateRing.XClass (Curve a b) x =
      ellipticCurve22 a b -
        algebraMap ℂ (Curve a b).CoordinateRing x := by
  apply AdjoinRoot.mk_eq_mk.mpr
  exact ⟨0, by simp [Curve]⟩

private theorem YClass_eq (a b y : ℂ) :
    WeierstrassCurve.Affine.CoordinateRing.YClass
        (Curve a b) (C y) =
      ellipticCurveY a b -
        algebraMap ℂ (Curve a b).CoordinateRing y := by
  apply AdjoinRoot.mk_eq_mk.mpr
  exact ⟨0, by simp [Curve]⟩

private theorem coordinate_relation
    (a b x y : ℂ) (h : (Curve a b).Equation x y) :
    WeierstrassCurve.Affine.CoordinateRing.YClass
          (Curve a b) (C y) *
        (ellipticCurveY a b +
          algebraMap ℂ (Curve a b).CoordinateRing y) =
      WeierstrassCurve.Affine.CoordinateRing.XClass
          (Curve a b) x *
        (ellipticCurve22 a b ^ 2 +
          algebraMap ℂ (Curve a b).CoordinateRing x *
            ellipticCurve22 a b +
          algebraMap ℂ (Curve a b).CoordinateRing (x ^ 2 + a)) := by
  have heq : y ^ 2 = x ^ 3 + a * x + b := by
    rw [WeierstrassCurve.Affine.equation_iff] at h
    simpa [Curve] using h
  have heq' := congrArg
    (algebraMap ℂ (Curve a b).CoordinateRing) heq
  simp only [map_pow, map_add, map_mul] at heq'
  rw [XClass_eq, YClass_eq]
  simp only [map_add, map_pow]
  linear_combination (YClass_sq a b) - heq'

private theorem maximal_ideal_xy
    (a b : ℂ) (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0)
    (M : Ideal (Curve a b).CoordinateRing) [M.IsMaximal] :
    ∃ x y : ℂ,
      (Curve a b).Nonsingular x y ∧
        M = WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          (Curve a b) x (C y) := by
  let Q := (Curve a b).CoordinateRing ⧸ M
  letI : Field Q := Ideal.Quotient.field M
  let q : (Curve a b).CoordinateRing →ₐ[ℂ] Q :=
    Ideal.Quotient.mkₐ ℂ M
  letI : Algebra.FiniteType ℂ (Curve a b).CoordinateRing := by
    exact Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ ℂ
        (Ideal.span {(Curve a b).polynomial}))
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  letI : Algebra.FiniteType ℂ Q :=
    Algebra.FiniteType.of_surjective q Ideal.Quotient.mk_surjective
  letI : Module.Finite ℂ Q :=
    finite_of_finite_type_of_isJacobsonRing ℂ Q
  have hsurj : Function.Surjective (algebraMap ℂ Q) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2
  obtain ⟨x, hx⟩ := hsurj (q (ellipticCurve22 a b))
  obtain ⟨y, hy⟩ := hsurj (q (ellipticCurveY a b))
  have hrelation := congrArg q (YClass_sq a b)
  have hequation : y ^ 2 = x ^ 3 + a * x + b := by
    apply (algebraMap ℂ Q).injective
    simpa only [map_pow, map_add, map_mul, q.commutes, hx, hy] using hrelation
  have hcurve : (Curve a b).Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simpa [Curve] using hequation
  letI := Curve_isElliptic hΔ
  have hnonsingular : (Curve a b).Nonsingular x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hcurve
  refine ⟨x, y, hnonsingular, ?_⟩
  let J := WeierstrassCurve.Affine.CoordinateRing.XYIdeal
    (Curve a b) x (C y)
  have hpolynomial : ((Curve a b).polynomial.eval (C y)).eval x = 0 := by
    simpa [WeierstrassCurve.Affine.Equation] using hcurve
  have hJfield : IsField ((Curve a b).CoordinateRing ⧸ J) :=
    (WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv hpolynomial).toRingEquiv
      |>.toMulEquiv.isField (Field.toIsField ℂ)
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hJfield
  symm
  apply Ideal.IsMaximal.eq_of_le hJmax (Ideal.IsMaximal.ne_top inferInstance)
  dsimp [J]
  rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · rw [XClass_eq]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (ellipticCurve22 a b -
      algebraMap ℂ (Curve a b).CoordinateRing x) = 0
    rw [map_sub, q.commutes, ← hx, sub_self]
  · rw [YClass_eq]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (ellipticCurveY a b -
      algebraMap ℂ (Curve a b).CoordinateRing y) = 0
    rw [map_sub, q.commutes, ← hy, sub_self]

private theorem localized_maximal_principal
    (a b : ℂ) (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0)
    (M : Ideal (Curve a b).CoordinateRing) [M.IsMaximal] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime M)).IsPrincipal := by
  letI : M.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  obtain ⟨x, y, hnonsingular, hM⟩ :=
    maximal_ideal_xy a b hΔ M
  let U := WeierstrassCurve.Affine.CoordinateRing.XClass
    (Curve a b) x
  let V := WeierstrassCurve.Affine.CoordinateRing.YClass
    (Curve a b) (C y)
  let Cplus := ellipticCurveY a b +
    algebraMap ℂ (Curve a b).CoordinateRing y
  let D := ellipticCurve22 a b ^ 2 +
    algebraMap ℂ (Curve a b).CoordinateRing x * ellipticCurve22 a b +
    algebraMap ℂ (Curve a b).CoordinateRing (x ^ 2 + a)
  let f := algebraMap (Curve a b).CoordinateRing (Localization.AtPrime M)
  have hrelation : V * Cplus = U * D := by
    exact coordinate_relation a b x y hnonsingular.left
  have hUmem : U ∈ M := by
    rw [hM, WeierstrassCurve.Affine.CoordinateRing.XYIdeal]
    exact Ideal.subset_span (by simp [U])
  have hVmem : V ∈ M := by
    rw [hM, WeierstrassCurve.Affine.CoordinateRing.XYIdeal]
    exact Ideal.subset_span (by simp [V])
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
  rcases ((WeierstrassCurve.Affine.nonsingular_iff' ..).mp hnonsingular).right with hx | hy
  · have hx' : 3 * x ^ 2 + a ≠ 0 := by
      apply neg_ne_zero.mp
      simpa [Curve] using hx
    have hDnot : D ∉ M := by
      intro hD
      have hmul : U * (ellipticCurve22 a b +
          2 * algebraMap ℂ (Curve a b).CoordinateRing x) ∈ M :=
        M.mul_mem_right _ hUmem
      have hscalar := M.sub_mem hD hmul
      have : algebraMap ℂ (Curve a b).CoordinateRing
          (3 * x ^ 2 + a) ∈ M := by
        convert hscalar using 1
        dsimp [D, U]
        rw [XClass_eq]
        simp only [map_add, map_pow, map_mul, map_ofNat]
        ring
      exact (Ideal.IsMaximal.ne_top inferInstance) <|
        M.eq_top_of_isUnit_mem this <|
          (isUnit_iff_ne_zero.mpr hx').map
            (algebraMap ℂ (Curve a b).CoordinateRing)
    have hDunit : IsUnit (f D) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime M) M D).2 hDnot
    rcases hDunit with ⟨d, hd⟩
    have hmaprelation : f V * f Cplus = f U * f D := by
      simpa only [map_mul] using congrArg f hrelation
    have hUspan : f U ∈ Ideal.span {f V} := by
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨f Cplus * ↑d⁻¹, ?_⟩
      calc
        (f Cplus * ↑d⁻¹) * f V = (f V * f Cplus) * ↑d⁻¹ := by ring
        _ = (f U * f D) * ↑d⁻¹ := by rw [hmaprelation]
        _ = f U := by rw [← hd]; simp
    have hmap : Ideal.map f M = Ideal.span {f V} := by
      calc
        Ideal.map f M = Ideal.map f
            (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
              (Curve a b) x (C y)) := congrArg (Ideal.map f) hM
        _ = Ideal.span {f V} := by
          rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.map_span]
          simp only [Set.image_insert_eq, Set.image_singleton]
          rw [Ideal.span_insert, sup_eq_right]
          exact Ideal.span_le.2 (by simpa using hUspan)
    rw [hmap]
    infer_instance
  · have hy' : 2 * y ≠ 0 := by
      simpa [Curve] using hy
    have hCnot : Cplus ∉ M := by
      intro hC
      have hscalar := M.sub_mem hC hVmem
      have : algebraMap ℂ (Curve a b).CoordinateRing (2 * y) ∈ M := by
        convert hscalar using 1
        dsimp [Cplus, V]
        rw [YClass_eq]
        simp only [map_mul, map_ofNat]
        ring
      exact (Ideal.IsMaximal.ne_top inferInstance) <|
        M.eq_top_of_isUnit_mem this <|
          (isUnit_iff_ne_zero.mpr hy').map
            (algebraMap ℂ (Curve a b).CoordinateRing)
    have hCunit : IsUnit (f Cplus) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime M) M Cplus).2 hCnot
    rcases hCunit with ⟨c, hc⟩
    have hmaprelation : f V * f Cplus = f U * f D := by
      simpa only [map_mul] using congrArg f hrelation
    have hVspan : f V ∈ Ideal.span {f U} := by
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨f D * ↑c⁻¹, ?_⟩
      calc
        (f D * ↑c⁻¹) * f U = (f U * f D) * ↑c⁻¹ := by ring
        _ = (f V * f Cplus) * ↑c⁻¹ := by rw [← hmaprelation]
        _ = f V := by rw [← hc]; simp
    have hmap : Ideal.map f M = Ideal.span {f U} := by
      calc
        Ideal.map f M = Ideal.map f
            (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
              (Curve a b) x (C y)) := congrArg (Ideal.map f) hM
        _ = Ideal.span {f U} := by
          rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.map_span]
          simp only [Set.image_insert_eq, Set.image_singleton]
          rw [Ideal.span_insert, sup_eq_left]
          exact Ideal.span_le.2 (by simpa using hVspan)
    rw [hmap]
    infer_instance

/-- The affine coordinate ring of a Weierstrass curve over a field is Noetherian. -/
theorem elliptic_curve_noetherian
    (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    IsNoetherianRing W.CoordinateRing := by
  infer_instance

/-- The affine coordinate ring of a Weierstrass curve over a field has Krull dimension at most
one.  This is the dimension part of the Dedekind-domain assertion in Example 3.22. -/
theorem elliptic_curve_dimension
    (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    Ring.DimensionLEOne W.CoordinateRing := by
  letI : Module.Finite F[X] W.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)
  letI : Algebra.IsIntegral F[X] W.CoordinateRing :=
    Algebra.IsIntegral.of_finite F[X] W.CoordinateRing
  constructor
  intro p hp hprime
  letI : p.IsPrime := hprime
  have hcomapprime : (p.comap (algebraMap F[X] W.CoordinateRing)).IsPrime :=
    hprime.comap _
  have hcomapne : p.comap (algebraMap F[X] W.CoordinateRing) ≠ (⊥ : Ideal F[X]) := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx
      (Algebra.IsIntegral.isIntegral x).isAlgebraic
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p
    (hcomapprime.isMaximal hcomapne)

/-- The coordinate ring of the nonsingular affine cubic in Example 3.22 is a Dedekind domain.
The proof identifies every maximal ideal with a complex point and uses the nonvanishing of one
partial derivative to make its localization principal. -/
theorem coordinate_dedekind_domain
    (a b : ℂ) (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0) :
    IsDedekindDomain (Curve a b).CoordinateRing := by
  letI : Ring.DimensionLEOne (Curve a b).CoordinateRing :=
    elliptic_curve_dimension ℂ (Curve a b)
  letI : IsDedekindDomainDvr (Curve a b).CoordinateRing := {
    is_dvr_at_nonzero_prime := by
      intro P hP hprime
      letI : P.IsPrime := hprime
      letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP hprime
      letI : IsNoetherianRing (Localization.AtPrime P) :=
        IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
      letI : IsLocalRing (Localization.AtPrime P) :=
        IsLocalization.AtPrime.isLocalRing _ P
      have hprincipal :
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal :=
        localized_maximal_principal a b hΔ P
      exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P)
        (IsLocalization.AtPrime.not_isField
          (Curve a b).CoordinateRing hP _)).out 4 0).mp hprincipal }
  infer_instance

/-- For an arbitrary affine Weierstrass curve, the remaining condition in the Dedekind-domain
definition is integral closedness. -/
theorem elliptic_curve_integrally
    (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    IsDedekindDomain W.CoordinateRing ↔ IsIntegrallyClosed W.CoordinateRing := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    letI : Ring.DimensionLEOne W.CoordinateRing :=
      elliptic_curve_dimension F W
    exact { }

/-- The natural injection from elliptic-curve points to the ideal class group of the affine
coordinate ring, which is the algebraic core of Example 3.22. -/
theorem elliptic_curve_inject
    (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) :
    ∃ f : W.Point →+ Additive (ClassGroup W.CoordinateRing),
      Function.Injective f := by
  exact ⟨WeierstrassCurve.Affine.Point.toClass,
    WeierstrassCurve.Affine.Point.toClass_injective⟩

/-- A chosen square root of `x³ + ax + b`. -/
noncomputable def elliptic22Y (a b x : ℂ) : ℂ :=
  Classical.choose ((Complex.isOpenQuotientMap_pow 2).surjective (x ^ 3 + a * x + b))

@[simp]
theorem Y_sq (a b x : ℂ) :
    elliptic22Y a b x ^ 2 = x ^ 3 + a * x + b :=
  Classical.choose_spec ((Complex.isOpenQuotientMap_pow 2).surjective (x ^ 3 + a * x + b))

/-- A point of the curve above every complex `x`-coordinate. -/
noncomputable def ellipticCurvePoint (a b : ℂ) (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0)
    (x : ℂ) : (Curve a b).Point := by
  letI := Curve_isElliptic hΔ
  exact WeierstrassCurve.Affine.Point.mk (x := x) (y := elliptic22Y a b x) <| by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [Curve]

/-- Distinct complex `x`-coordinates give distinct points in Example 3.22. -/
theorem Point_injective (a b : ℂ) (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0) :
    Function.Injective (ellipticCurvePoint a b hΔ) := by
  intro x y hxy
  change WeierstrassCurve.Affine.Point.some x (elliptic22Y a b x) _ =
    WeierstrassCurve.Affine.Point.some y (elliptic22Y a b y) _ at hxy
  injection hxy

/-- The complex points of the elliptic curve in Example 3.22 are uncountable. -/
theorem points_uncountable (a b : ℂ)
    (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0) :
    Uncountable (Curve a b).Point := by
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  exact (Point_injective a b hΔ).uncountable

/-- The class group in Example 3.22 is uncountable. -/
theorem classGroup_uncountable (a b : ℂ)
    (hΔ : -4 * a ^ 3 - 27 * b ^ 2 ≠ 0) :
    Uncountable (ClassGroup (Curve a b).CoordinateRing) := by
  letI := Curve_isElliptic hΔ
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  exact (WeierstrassCurve.Affine.Point.toClass_injective.comp
    (Point_injective a b hΔ)).uncountable

end Submission.NumberTheory.Milne
