import Towers.Algebra.FilteredPowers
import Towers.Algebra.Magnus.MagnusEmbedding
import Towers.Group.Zassenhaus.ZassenhausRecursive

/-!
# Weighted ideals and the constructive inclusion of Theorem 4.3

This file connects the abstract filtered binomial calculation to the
actual Magnus homomorphism.  It proves

`∏_{i=1}^n (γ_i F)^(e(n,i)) ≤ μ⁻¹(1 + d^(e,n))`

for every binomial multiplicatively descending map `e`.
-/

namespace EChapma
namespace MSeries

variable {R X : Type*} [Ring R]

/-- The order filtration on the Magnus ring as a multiplicative additive
filtration. -/
def magnusAddFiltration :
    MAFilt (MSeries R X) where
  term := orderLeastSubgroup (R := R) (X := X)
  antitone := by
    intro m n hmn f hf w hw
    exact hf w (hw.trans_le hmn)
  mul_mem := by
    intro i j f g hf hg
    exact vanishes_below_add hf hg

/-- The weighted ideal
`d_R^(e,n) = Σ_{i=1}^n e(n,i)d_R^i` in the actual Magnus ring. -/
def weightedIdeal
    (e : MDescen) (n : ℕ) :
    Ideal (MSeries R X) where
  carrier :=
    (magnusAddFiltration (R := R) (X := X)).weightedSubgroup e n
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
          (magnusAddFiltration (R := R) (X := X)).weightedGenerator_mem
            e hi hin (vanishes_below_right hy a)
    | zero => simp
    | add f g _ _ hf hg =>
        change a * (f + g) ∈ _
        rw [mul_add]
        exact AddSubgroup.add_mem _ hf hg
    | neg f _ hf =>
        change a * -f ∈ _
        rw [mul_neg]
        exact AddSubgroup.neg_mem _ hf

instance weighted_ideal_sided
    (e : MDescen) (n : ℕ) :
    (weightedIdeal (R := R) (X := X) e n).IsTwoSided where
  mul_mem_of_left {f} a hf := by
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
        rw [show (e n i • y) * a = e n i • (y * a) by
          simpa only [AddMonoidHom.coe_mulRight] using
            (AddMonoidHom.mulRight a).map_nsmul (e n i) y]
        exact
          (magnusAddFiltration (R := R) (X := X)).weightedGenerator_mem
            e hi hin (vanishes_below_left hy a)
    | zero => simp
    | add f g _ _ hf hg =>
        rw [add_mul]
        exact AddSubgroup.add_mem _ hf hg
    | neg f _ hf =>
        rw [neg_mul]
        exact AddSubgroup.neg_mem _ hf

@[simp]
theorem mem_weightedIdeal
    {e : MDescen} {n : ℕ}
    {f : MSeries R X} :
    f ∈ weightedIdeal (R := R) (X := X) e n ↔
      f ∈
        (magnusAddFiltration (R := R) (X := X)).weightedSubgroup e n :=
  Iff.rfl

/-- The subgroup of the free group whose Magnus expansion is congruent to
one modulo the weighted ideal. -/
noncomputable def magnusWeightedSubgroup
    (e : MDescen) (n : ℕ) :
    Subgroup (FreeGroup X) :=
  (plusIdealSubgroup
      (weightedIdeal (R := R) (X := X) e n)).comap
    (magnusUnitHom (R := R) (X := X))

instance magnus_weighted_normal
    (e : MDescen) (n : ℕ) :
    (magnusWeightedSubgroup (R := R) (X := X) e n).Normal := by
  unfold magnusWeightedSubgroup
  infer_instance

@[simp]
theorem magnus_weighted_subgroup
    {e : MDescen} {n : ℕ}
    {g : FreeGroup X} :
    g ∈ magnusWeightedSubgroup (R := R) (X := X) e n ↔
      magnusDifference (R := R) g ∈
        weightedIdeal (R := R) (X := X) e n :=
  Iff.rfl

/-- The Magnus difference of an `e(n,i)`th power from `γ_i(F)` belongs
to the weighted ideal. -/
theorem magnus_difference_weighted
    (e : MDescen) (he : e.IsBinomial)
    {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (i - 1)) :
    magnusDifference (R := R) (g ^ e n i) ∈
      weightedIdeal (R := R) (X := X) e n := by
  let x : MSeries R X := magnusDifference (R := R) g
  have hx :
      x ∈
        (magnusAddFiltration (R := R) (X := X)).term i := by
    have horder :=
      lower_magnus_subgroup
        (R := R) (X := X) (i - 1) hg
    simpa [x, magnusAddFiltration, Nat.sub_add_cancel hi] using horder
  have htail :
      MAFilt.binomialTail e n i x ∈
        (magnusAddFiltration (R := R) (X := X)).weightedSubgroup e n :=
    (magnusAddFiltration (R := R) (X := X)).binomial_weighted_subgroup
      e he hi hin hx
  have hseries :
      magnusSeries (R := R) g = 1 + x := by
    dsimp [x, magnusDifference]
    noncomm_ring
  have hdiff :
      magnusDifference (R := R) (g ^ e n i) =
        MAFilt.binomialTail e n i x := by
    calc
      magnusDifference (R := R) (g ^ e n i) =
          magnusSeries (R := R) g ^ e n i - 1 := by
            simp [magnusDifference, map_pow, magnusSeries,
              magnusUnitHom]
      _ = (1 + x) ^ e n i - 1 := by rw [hseries]
      _ = MAFilt.binomialTail e n i x :=
        MAFilt.sub_binomial_tail
          e n i x
  rw [hdiff]
  exact htail

/-- The product
`∏_{i=1}^n (γ_i(F))^(e(n,i))`, represented as the supremum of its
normal power-subgroup factors. -/
def weightedLowerProduct
    (e : MDescen) (n : ℕ) :
    Subgroup (FreeGroup X) :=
  ⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ n},
    subgroupPower
      (Subgroup.lowerCentralSeries (FreeGroup X) (i.1 - 1)) (e n i.1)

/-- The constructive inclusion in Efrat--Chapman, Theorem 4.3. -/
theorem weighted_magnus_subgroup
    (e : MDescen) (he : e.IsBinomial) (n : ℕ) :
    weightedLowerProduct (X := X) e n ≤
      magnusWeightedSubgroup (R := R) (X := X) e n := by
  unfold weightedLowerProduct
  apply iSup_le
  intro i
  unfold subgroupPower
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨g, hg, rfl⟩
  exact magnus_difference_weighted
    e he i.property.1 i.property.2 hg

end MSeries
end EChapma
