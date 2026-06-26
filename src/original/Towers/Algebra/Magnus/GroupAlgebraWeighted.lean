import Towers.Algebra.Magnus.MagnusWeighted
import Towers.Algebra.OnePlusIdeal
import Mathlib.Algebra.MonoidAlgebra.Lift
import Towers.Algebra.Augmentation
import Towers.Group.GolodShafarevichCore


/-!
# Weighted augmentation ideals

This file proves the group-algebra constructive inclusion in
Efrat--Chapman, Theorem 4.3:

`∏_{i=1}^n (γ_i F)^(e(n,i)) ≤ F ∩ (1 + c_R^(e,n))`.

Here the intersection is represented as the preimage, under the canonical
map from the free group to its group algebra, of the elements congruent to
one modulo the weighted augmentation ideal.
-/

namespace EChapma
namespace GAWt

variable {R X : Type*} [CommRing R]

/-- A coefficient, viewed as a constant Magnus series. -/
def constantSeries (r : R) : MSeries R X :=
  MSeries.leftScale r 1

@[simp]
theorem constant_series_one (r : R) :
    constantSeries (X := X) r 1 = r := by
  simp [constantSeries]

theorem constantSeries_mul (r : R) (f : MSeries R X) :
    constantSeries (X := X) r * f = MSeries.leftScale r f := by
  change MSeries.leftScale r 1 * f = MSeries.leftScale r f
  rw [MSeries.leftScale_mul, one_mul]

theorem mul_constantSeries (f : MSeries R X) (r : R) :
    f * constantSeries (X := X) r = MSeries.leftScale r f := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one =>
      simp [constantSeries, MSeries.leftScale, mul_comm]
  | mul_of x w ih =>
      rw [MSeries.apply_of_mul]
      simp only [constantSeries, MSeries.leftScale_apply,
        MSeries.one_apply_of, mul_zero, zero_add]
      change
        (MSeries.shift x f * constantSeries (X := X) r) w =
          r * f (FreeMonoid.of x * w)
      rw [ih]
      rfl

@[simp]
theorem constantSeries_one :
    constantSeries (X := X) (1 : R) = 1 := by
  ext w
  simp [constantSeries, MSeries.leftScale]

/-- The central ring homomorphism embedding coefficients as constant
Magnus series. -/
def constantSeriesHom : R →+* MSeries R X where
  toFun := constantSeries (X := X)
  map_zero' := by
    ext w
    simp [constantSeries, MSeries.leftScale]
  map_one' := by
    ext w
    simp [constantSeries, MSeries.leftScale]
  map_add' r s := by
    ext w
    by_cases hw : w.length = 0
    · simp [constantSeries, MSeries.leftScale, hw]
    · simp [constantSeries, MSeries.leftScale, hw]
  map_mul' r s := by
    rw [constantSeries_mul]
    ext w
    simp [constantSeries, MSeries.leftScale]

theorem constantSeries_commute (r : R) (f : MSeries R X) :
    Commute (constantSeries (X := X) r) f := by
  change constantSeries (X := X) r * f =
    f * constantSeries (X := X) r
  rw [constantSeries_mul, mul_constantSeries]

/-- The series-valued form of the Magnus homomorphism. -/
noncomputable def magnusMonoidHom :
    FreeGroup X →* MSeries R X :=
  (Units.coeHom (MSeries R X)).comp
    (MSeries.magnusUnitHom (R := R) (X := X))

@[simp]
theorem magnus_monoid_hom (g : FreeGroup X) :
    magnusMonoidHom (R := R) (X := X) g =
      MSeries.magnusSeries (R := R) g :=
  rfl

/-- The ring homomorphism from the free-group algebra induced by the
Magnus homomorphism. -/
noncomputable def groupAlgebraMagnus :
    MonoidAlgebra R (FreeGroup X) →+* MSeries R X :=
  MonoidAlgebra.liftNCRingHom
    (constantSeriesHom (R := R) (X := X))
    (magnusMonoidHom (R := R) (X := X))
    fun r _g => constantSeries_commute r _

@[simp]
theorem algebra_magnus (g : FreeGroup X) :
    groupAlgebraMagnus (R := R) (X := X)
        (MonoidAlgebra.of R (FreeGroup X) g) =
      MSeries.magnusSeries (R := R) g := by
  change
    MonoidAlgebra.liftNCRingHom
        (constantSeriesHom (R := R) (X := X))
        (magnusMonoidHom (R := R) (X := X))
        _ (MonoidAlgebra.single g 1) =
      MSeries.magnusSeries (R := R) g
  rw [MonoidAlgebra.liftNCRingHom_single]
  simp [constantSeriesHom]

/-- The two augmentation-ideal APIs used in the repository agree. -/
theorem augmentation_ideal_algebra :
    Towers.GShafar.augmentationIdeal R (FreeGroup X) =
      Towers.GroupAlgebra.augmentationIdeal R (FreeGroup X) := by
  unfold Towers.GShafar.augmentationIdeal
    Towers.GroupAlgebra.augmentationIdeal
  congr 1

/-- Powers of the augmentation ideal, regarded as a multiplicative
additive filtration of the group algebra. -/
noncomputable def augmentationAddFiltration :
    MAFilt (MonoidAlgebra R (FreeGroup X)) where
  term n :=
    (Towers.GShafar.augmentationIdeal R (FreeGroup X) ^ n).toAddSubgroup
  antitone := by
    intro m n hmn
    exact Ideal.pow_le_pow_right hmn
  mul_mem := by
    intro i j x y hx hy
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hx hy

/-- The weighted augmentation ideal
`c_R^(e,n) = Σ_{i=1}^n e(n,i)c_R^i`. -/
noncomputable def weightedAugmentationIdeal
    (e : MDescen) (n : ℕ) :
    Ideal (MonoidAlgebra R (FreeGroup X)) where
  carrier :=
    (augmentationAddFiltration (R := R) (X := X)).weightedSubgroup e n
  zero_mem' := AddSubgroup.zero_mem _
  add_mem' := AddSubgroup.add_mem _
  smul_mem' a f hf := by
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
        change a * (e n i • y) ∈ _
        rw [show a * (e n i • y) = e n i • (a * y) by
          simpa only [AddMonoidHom.coe_mulLeft] using
            (AddMonoidHom.mulLeft a).map_nsmul (e n i) y]
        exact
          (augmentationAddFiltration (R := R) (X := X)).weightedGenerator_mem
            e hi hin
              (Ideal.mul_mem_left
                (Towers.GShafar.augmentationIdeal
                  R (FreeGroup X) ^ i) a hy)
    | zero => simp
    | add f g _ _ hf hg =>
        change a * (f + g) ∈ _
        rw [mul_add]
        exact AddSubgroup.add_mem _ hf hg
    | neg f _ hf =>
        change a * -f ∈ _
        rw [mul_neg]
        exact AddSubgroup.neg_mem _ hf

instance weighted_augmentation_sided
    (e : MDescen) (n : ℕ) :
    (weightedAugmentationIdeal (R := R) (X := X) e n).IsTwoSided where
  mul_mem_of_left {f} a hf := by
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
        rw [show (e n i • y) * a = e n i • (y * a) by
          simpa only [AddMonoidHom.coe_mulRight] using
            (AddMonoidHom.mulRight a).map_nsmul (e n i) y]
        exact
          (augmentationAddFiltration (R := R) (X := X)).weightedGenerator_mem
            e hi hin
              (Ideal.mul_mem_right a
                (Towers.GShafar.augmentationIdeal
                  R (FreeGroup X) ^ i) hy)
    | zero => simp
    | add f g _ _ hf hg =>
        rw [add_mul]
        exact AddSubgroup.add_mem _ hf hg
    | neg f _ hf =>
        rw [neg_mul]
        exact AddSubgroup.neg_mem _ hf

@[simp]
theorem weighted_augmentation_ideal
    {e : MDescen} {n : ℕ}
    {f : MonoidAlgebra R (FreeGroup X)} :
    f ∈ weightedAugmentationIdeal (R := R) (X := X) e n ↔
      f ∈
        (augmentationAddFiltration (R := R) (X := X)).weightedSubgroup e n :=
  Iff.rfl

/-- Products of series of orders at least `m` and `n` have order at
least `m+n`. -/
theorem order_least_mul (m n : ℕ) :
    MSeries.orderLeastIdeal (R := R) (X := X) m *
        MSeries.orderLeastIdeal (R := R) (X := X) n ≤
      MSeries.orderLeastIdeal (R := R) (X := X) (m + n) := by
  rw [Ideal.mul_le]
  intro f hf g hg
  exact MSeries.vanishes_below_add hf hg

/-- The `i`th power of the positive-order ideal has order at least `i`. -/
theorem order_least_pow (i : ℕ) :
    MSeries.orderLeastIdeal (R := R) (X := X) 1 ^ i ≤
      MSeries.orderLeastIdeal (R := R) (X := X) i := by
  induction i with
  | zero =>
      intro f hf
      exact MSeries.vanishesBelow_zero f
  | succ i ih =>
      rw [Submodule.pow_succ]
      exact
        (mul_le_mul' ih le_rfl).trans
          (by simpa using
            order_least_mul (R := R) (X := X) i 1)

/-- The Magnus extension sends the augmentation ideal into the
positive-order ideal. -/
theorem augmentation_order_least :
    Ideal.map (groupAlgebraMagnus (R := R) (X := X))
        (Towers.GShafar.augmentationIdeal R (FreeGroup X)) ≤
      MSeries.orderLeastIdeal (R := R) (X := X) 1 := by
  rw [Ideal.map_le_iff_le_comap, augmentation_ideal_algebra,
    ← Towers.GroupAlgebra.augmentation_generator_ideal]
  apply Ideal.span_le.mpr
  rintro f ⟨g, rfl⟩
  change
    groupAlgebraMagnus (R := R) (X := X)
        (MonoidAlgebra.of R (FreeGroup X) g - 1) ∈
      MSeries.orderLeastIdeal (R := R) (X := X) 1
  simp only [map_sub, map_one, algebra_magnus]
  exact MSeries.magnus_vanishes_below g

/-- The Magnus extension sends the `i`th augmentation power into
series of order at least `i`. -/
theorem magnus_least_pow
    {i : ℕ} {f : MonoidAlgebra R (FreeGroup X)}
    (hf :
      f ∈ Towers.GShafar.augmentationIdeal R (FreeGroup X) ^ i) :
    groupAlgebraMagnus (R := R) (X := X) f ∈
      MSeries.orderLeastIdeal (R := R) (X := X) i := by
  have hmap :
      groupAlgebraMagnus (R := R) (X := X) f ∈
        Ideal.map (groupAlgebraMagnus (R := R) (X := X))
          (Towers.GShafar.augmentationIdeal
            R (FreeGroup X) ^ i) :=
    Ideal.mem_map_of_mem _ hf
  exact order_least_pow (R := R) (X := X) i
    (Towers.GroupAlgebra.map_le_le
      (groupAlgebraMagnus (R := R) (X := X))
      (Towers.GShafar.augmentationIdeal R (FreeGroup X))
      (MSeries.orderLeastIdeal (R := R) (X := X) 1)
      (augmentation_order_least (R := R) (X := X))
      i hmap)

/-- The weighted augmentation ideal maps into the corresponding weighted
Magnus ideal. -/
theorem magnus_weighted_ideal
    (e : MDescen) (n : ℕ)
    {f : MonoidAlgebra R (FreeGroup X)}
    (hf : f ∈ weightedAugmentationIdeal (R := R) (X := X) e n) :
    groupAlgebraMagnus (R := R) (X := X) f ∈
      MSeries.weightedIdeal (R := R) (X := X) e n := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
      rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
      rw [map_nsmul]
      exact
        (MSeries.magnusAddFiltration (R := R) (X := X)).weightedGenerator_mem
          e hi hin
            ((MSeries.order_least_ideal).mp
              (magnus_least_pow
                (R := R) (X := X) hy))
  | zero => simp
  | add f g _ _ hf hg =>
      rw [map_add]
      exact Ideal.add_mem _ hf hg
  | neg f _ hf =>
      rw [map_neg]
      exact neg_mem hf

/-- The weighted dimension subgroup in the free group. -/
noncomputable def weightedDimensionSubgroup
    (e : MDescen) (n : ℕ) :
    Subgroup (FreeGroup X) :=
  plusIdealSubgroup
    (MonoidAlgebra.of R (FreeGroup X))
    (weightedAugmentationIdeal (R := R) (X := X) e n)

instance weighted_dimension_normal
    (e : MDescen) (n : ℕ) :
    (weightedDimensionSubgroup (R := R) (X := X) e n).Normal := by
  unfold weightedDimensionSubgroup
  infer_instance

@[simp]
theorem weighted_dimension
    {e : MDescen} {n : ℕ} {g : FreeGroup X} :
    g ∈ weightedDimensionSubgroup (R := R) (X := X) e n ↔
      MonoidAlgebra.of R (FreeGroup X) g - 1 ∈
        weightedAugmentationIdeal (R := R) (X := X) e n :=
  Iff.rfl

/-- The group-algebra weighted dimension subgroup is contained in the
corresponding weighted Magnus subgroup. -/
theorem weighted_subgroup_magnus
    (e : MDescen) (n : ℕ) :
    weightedDimensionSubgroup (R := R) (X := X) e n ≤
      MSeries.magnusWeightedSubgroup (R := R) (X := X) e n := by
  intro g hg
  rw [weighted_dimension] at hg
  rw [MSeries.magnus_weighted_subgroup]
  have hmap :=
    magnus_weighted_ideal
      (R := R) (X := X) e n hg
  change
    groupAlgebraMagnus (R := R) (X := X)
        (MonoidAlgebra.of R (FreeGroup X) g - 1) ∈
      MSeries.weightedIdeal (R := R) (X := X) e n at hmap
  rw [map_sub, map_one, algebra_magnus] at hmap
  exact hmap

/-- An `e(n,i)`th power of an element of `γ_i(F)` has weighted
augmentation difference. -/
theorem difference_weighted_ideal
    (e : MDescen) (he : e.IsBinomial)
    {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (i - 1)) :
    MonoidAlgebra.of R (FreeGroup X) (g ^ e n i) - 1 ∈
      weightedAugmentationIdeal (R := R) (X := X) e n := by
  let x : MonoidAlgebra R (FreeGroup X) :=
    MonoidAlgebra.of R (FreeGroup X) g - 1
  have hx :
      x ∈ (augmentationAddFiltration (R := R) (X := X)).term i := by
    have hpower :=
      Towers.GShafar.lower_series_succ
        (R := R) (G := FreeGroup X) (i - 1) hg
    simpa [x, augmentationAddFiltration, Nat.sub_add_cancel hi] using hpower
  have htail :
      MAFilt.binomialTail e n i x ∈
        (augmentationAddFiltration (R := R) (X := X)).weightedSubgroup e n :=
    (augmentationAddFiltration (R := R) (X := X)).binomial_weighted_subgroup
      e he hi hin hx
  have hof : MonoidAlgebra.of R (FreeGroup X) g = 1 + x := by
    dsimp [x]
    noncomm_ring
  have hdiff :
      MonoidAlgebra.of R (FreeGroup X) (g ^ e n i) - 1 =
        MAFilt.binomialTail e n i x := by
    calc
      MonoidAlgebra.of R (FreeGroup X) (g ^ e n i) - 1 =
          (MonoidAlgebra.of R (FreeGroup X) g) ^ e n i - 1 := by
            rw [map_pow]
      _ = (1 + x) ^ e n i - 1 := by rw [hof]
      _ = MAFilt.binomialTail e n i x :=
        MAFilt.sub_binomial_tail
          e n i x
  rw [hdiff]
  exact htail

/-- The group-algebra constructive inclusion in Theorem 4.3. -/
theorem weighted_dimension_subgroup
    (e : MDescen) (he : e.IsBinomial) (n : ℕ) :
    MSeries.weightedLowerProduct (X := X) e n ≤
      weightedDimensionSubgroup (R := R) (X := X) e n := by
  unfold MSeries.weightedLowerProduct
  apply iSup_le
  intro i
  unfold subgroupPower
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨g, hg, rfl⟩
  exact difference_weighted_ideal
    e he i.property.1 i.property.2 hg

end GAWt
end EChapma
