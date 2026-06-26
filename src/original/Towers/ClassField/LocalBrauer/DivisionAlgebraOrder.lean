import Towers.ClassField.LocalBrauer.DivisionAbsoluteValue
import Towers.ClassField.LocalBrauer.LocalField


/-!
# Chapter IV, Section 4: the order on a local division algebra

The normalized multiplicative valuation of a nonarchimedean local field has
value group `WithZero (Multiplicative ℤ)`.  Taking the negative logarithm on
nonzero elements gives the usual additive integer order.  Pulling this order
back along the regular norm and dividing by `[D : K]` gives the rational order
on the unit group of a finite-dimensional division algebra.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open scoped WithZero

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The normalized additive order on the multiplicative group of a
nonarchimedean local field.  Mathlib's multiplicative value `exp (-n)` has
order `n`. -/
def localUnitOrder : Additive Kˣ →+ ℤ where
  toFun x :=
    -WithZero.log
      (local_value_int K
        (valuation K (x.toMul : K)))
  map_zero' := by
    simp
  map_add' x y := by
    have hx :
        local_value_int K
            (valuation K (x.toMul : K)) ≠ 0 := by
      rw [ne_eq, map_eq_zero, map_eq_zero]
      exact x.toMul.ne_zero
    have hy :
        local_value_int K
            (valuation K (y.toMul : K)) ≠ 0 := by
      rw [ne_eq, map_eq_zero, map_eq_zero]
      exact y.toMul.ne_zero
    change
      -WithZero.log
          (local_value_int K
            (valuation K ((x.toMul : K) * (y.toMul : K)))) = _
    rw [map_mul, map_mul, WithZero.log_mul hx hy]
    abel

@[simp]
theorem local_field_order (x : Additive Kˣ) :
    localUnitOrder K x =
      -WithZero.log
        (local_value_int K
          (valuation K (x.toMul : K))) :=
  rfl

/-- Every integer occurs as the normalized order of an element of `Kˣ`. -/
theorem local_order_surjective :
    Function.Surjective (localUnitOrder K) := by
  intro z
  let e := local_value_int K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective
    (e.symm (WithZero.exp (-z : ℤ)))
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    have h := congrArg e hx
    have h' : (0 : ℤᵐ⁰) = WithZero.exp (-z : ℤ) := by
      simpa [e] using h
    exact WithZero.coe_ne_zero h'.symm
  refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
  change -WithZero.log (e (valuation K x)) = z
  rw [hx, e.apply_symm_apply]
  simp

/-- Order comparison is the reverse of comparison for the rank-one norm
attached to the local valuation. -/
theorem local_order_norm (x y : Additive Kˣ) :
    localUnitOrder K x ≤ localUnitOrder K y ↔
      (valuation K).norm (y.toMul : K) ≤
        (valuation K).norm (x.toMul : K) := by
  let e := local_value_int K
  have hx : e (valuation K (x.toMul : K)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]
    exact x.toMul.ne_zero
  have hy : e (valuation K (y.toMul : K)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]
    exact y.toMul.ne_zero
  rw [local_field_order, local_field_order,
    neg_le_neg_iff, WithZero.log_le_log hy hx]
  change
    e (valuation K (y.toMul : K)) ≤
        e (valuation K (x.toMul : K)) ↔ _
  rw [map_le_map_iff e]
  rw [Valuation.norm_def, Valuation.norm_def, NNReal.coe_le_coe,
    (Valuation.RankOne.strictMono (valuation K)).le_iff_le]
  exact (valuation K).restrict_le_iff.symm

variable (D : Type u) [DivisionRing D] [Algebra K D] [Module.Finite K D]

/-- The regular norm on unit groups. -/
def regularNormUnits : Dˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The integer-valued order of the regular norm.  The rational order below
is this homomorphism divided by `[D : K]`. -/
def regularUnitOrder : Additive Dˣ →+ ℤ :=
  (localUnitOrder K).comp
    (MonoidHom.toAdditive (regularNormUnits K D))

omit [Module.Finite K D] in
@[simp]
theorem regular_unit_order (x : Additive Dˣ) :
    regularUnitOrder K D x =
      localUnitOrder K
        (Additive.ofMul (Units.map (Algebra.norm K) x.toMul)) :=
  rfl

/-- The rational order on a finite-dimensional division algebra, restricted
to its multiplicative group. -/
def divisionUnitOrder : Additive Dˣ →+ ℚ where
  toFun x :=
    (regularUnitOrder K D x : ℚ) / (Module.finrank K D : ℚ)
  map_zero' := by simp
  map_add' x y := by
    rw [map_add]
    push_cast
    ring

omit [Module.Finite K D] in
@[simp]
theorem division_unit_order (x : Additive Dˣ) :
    divisionUnitOrder K D x =
      (regularUnitOrder K D x : ℚ) /
        (Module.finrank K D : ℚ) :=
  rfl

/-- Before dividing by `[D : K]`, the order of a scalar's regular norm is
`[D : K]` times its base-field order. -/
theorem regular_order_algebra (x : Additive Kˣ) :
    regularUnitOrder K D
        (Additive.ofMul (Units.map (algebraMap K D).toMonoidHom x.toMul)) =
      (Module.finrank K D : ℤ) * localUnitOrder K x := by
  have hnorm :
      Units.map (Algebra.norm K)
          (Units.map (algebraMap K D).toMonoidHom x.toMul) =
        x.toMul ^ Module.finrank K D := by
    apply Units.ext
    simp [Algebra.norm_algebraMap]
  rw [regular_unit_order]
  change
    localUnitOrder K
        (Additive.ofMul
          (Units.map (Algebra.norm K)
            (Units.map (algebraMap K D).toMonoidHom x.toMul))) = _
  rw [hnorm]
  change localUnitOrder K (Module.finrank K D • x) = _
  rw [map_nsmul]
  simp

/-- The rational order on `Dˣ` restricts to the normalized integer order on
the embedded copy of `Kˣ`. -/
theorem division_algebra_order (x : Additive Kˣ) :
    divisionUnitOrder K D
        (Additive.ofMul (Units.map (algebraMap K D).toMonoidHom x.toMul)) =
      (localUnitOrder K x : ℚ) := by
  rw [division_unit_order,
    regular_order_algebra]
  push_cast
  field_simp [Module.finrank_pos.ne']

omit [Module.Finite K D] in
/-- Every order in `Dˣ` is an integer divided by `[D : K]`. -/
theorem division_div_finrank (x : Additive Dˣ) :
    ∃ z : ℤ,
      divisionUnitOrder K D x =
        (z : ℚ) / (Module.finrank K D : ℚ) := by
  exact ⟨regularUnitOrder K D x, rfl⟩

/-- The positive real magnitude obtained from the rank-one norm of the
regular norm.  This is the local-field presentation of the division-algebra
absolute value. -/
def localRegularMagnitude (x : D) : ℝ :=
  (valuation K).norm (Algebra.norm K x) ^
    (1 / (Module.finrank K D : ℝ))

/-- The rational unit order reverses comparison of the corresponding local
regular-norm magnitudes. -/
theorem division_algebra_magnitude
    (x y : Additive Dˣ) :
    divisionUnitOrder K D x ≤ divisionUnitOrder K D y ↔
      localRegularMagnitude K D (y.toMul : D) ≤
        localRegularMagnitude K D (x.toMul : D) := by
  have hdimQ : (0 : ℚ) < Module.finrank K D := by
    exact_mod_cast Module.finrank_pos (R := K) (M := D)
  have hdimR : (0 : ℝ) < Module.finrank K D := by
    exact_mod_cast Module.finrank_pos (R := K) (M := D)
  rw [division_unit_order, division_unit_order,
    div_le_div_iff_of_pos_right hdimQ]
  norm_cast
  rw [regular_unit_order, regular_unit_order,
    local_order_norm]
  change
    (valuation K).norm (Algebra.norm K (y.toMul : D)) ≤
        (valuation K).norm (Algebra.norm K (x.toMul : D)) ↔ _
  unfold localRegularMagnitude
  rw [Real.rpow_le_rpow_iff (Valuation.norm_nonneg _ _)
    (Valuation.norm_nonneg _ _) (one_div_pos.mpr hdimR)]

/-- The local regular-norm magnitude is ultrametric on the whole division
algebra. -/
theorem regular_magnitude_max (x y : D) :
    localRegularMagnitude K D (x + y) ≤
      max (localRegularMagnitude K D x)
        (localRegularMagnitude K D y) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  change regularValueCandidate K D (x + y) ≤
    max (regularValueCandidate K D x)
      (regularValueCandidate K D y)
  exact regular_absolute_max K D x y

/-- The rational order on all of `D`, with the conventional value `∞` at
zero. -/
noncomputable def divisionAlgebraOrder (x : D) : WithTop ℚ := by
  classical
  exact if hx : x = 0 then ⊤
    else
      (divisionUnitOrder K D
        (Additive.ofMul (Units.mk0 x hx)) : ℚ)

omit [Module.Finite K D] in
@[simp]
theorem division_algebra_zero :
    divisionAlgebraOrder K (D := D) 0 = ⊤ := by
  simp [divisionAlgebraOrder]

omit [Module.Finite K D] in
theorem division_ne_zero (x : D) (hx : x ≠ 0) :
    divisionAlgebraOrder K (D := D) x =
      (divisionUnitOrder K D
        (Additive.ofMul (Units.mk0 x hx)) : ℚ) := by
  simp [divisionAlgebraOrder, hx]

omit [Module.Finite K D] in
@[simp]
theorem division_algebra_one :
    divisionAlgebraOrder K (D := D) 1 = 0 := by
  rw [division_ne_zero K (D := D) 1 one_ne_zero]
  have hone : Units.mk0 (1 : D) one_ne_zero = 1 := by
    apply Units.ext
    rfl
  rw [hone]
  simp

omit [Module.Finite K D] in
theorem division_algebra_mul (x y : D) :
    divisionAlgebraOrder K (D := D) (x * y) =
      divisionAlgebraOrder K (D := D) x +
        divisionAlgebraOrder K (D := D) y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rw [division_ne_zero K (D := D) (x * y) hxy,
    division_ne_zero K (D := D) x hx,
    division_ne_zero K (D := D) y hy]
  have hunit :
      Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by
    apply Units.ext
    rfl
  rw [hunit]
  change
    ((divisionUnitOrder K D)
        (Additive.ofMul (Units.mk0 x hx) +
          Additive.ofMul (Units.mk0 y hy)) : WithTop ℚ) = _
  rw [map_add]
  simp

theorem division_algebra_min (x y : D) :
    min (divisionAlgebraOrder K (D := D) x)
        (divisionAlgebraOrder K (D := D) y) ≤
      divisionAlgebraOrder K (D := D) (x + y) := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  by_cases hxy : x + y = 0
  · rw [hxy, division_algebra_zero]
    exact le_top
  rw [division_ne_zero K (D := D) x hx,
    division_ne_zero K (D := D) y hy,
    division_ne_zero K (D := D) (x + y) hxy]
  have hmag := regular_magnitude_max K D x y
  rcases le_total (localRegularMagnitude K D x)
      (localRegularMagnitude K D y) with h | h
  · have hsum :
        localRegularMagnitude K D (x + y) ≤
          localRegularMagnitude K D y := by
      simpa [max_eq_right h] using hmag
    have hord :
        divisionUnitOrder K D
            (Additive.ofMul (Units.mk0 y hy)) ≤
          divisionUnitOrder K D
            (Additive.ofMul (Units.mk0 (x + y) hxy)) := by
      apply (division_algebra_magnitude K D _ _).2
      simpa using hsum
    exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr hord)
  · have hsum :
        localRegularMagnitude K D (x + y) ≤
          localRegularMagnitude K D x := by
      simpa [max_eq_left h] using hmag
    have hord :
        divisionUnitOrder K D
            (Additive.ofMul (Units.mk0 x hx)) ≤
          divisionUnitOrder K D
            (Additive.ofMul (Units.mk0 (x + y) hxy)) := by
      apply (division_algebra_magnitude K D _ _).2
      simpa using hsum
    exact (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hord)

/-- The normalized additive valuation on a finite-dimensional division
algebra over a nonarchimedean local field. -/
def divisionAlgebraValuation : AddValuation D (WithTop ℚ) :=
  AddValuation.of (divisionAlgebraOrder K (D := D))
    (division_algebra_zero K (D := D))
    (division_algebra_one K (D := D))
    (division_algebra_min K (D := D))
    (division_algebra_mul K (D := D))

@[simp]
theorem division_algebra_valuation (x : D) :
    divisionAlgebraValuation K (D := D) x =
      divisionAlgebraOrder K (D := D) x :=
  rfl

end

end Towers.CField.LBrauer
