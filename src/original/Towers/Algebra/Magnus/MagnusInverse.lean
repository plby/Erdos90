import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Range
import Mathlib.RingTheory.Ideal.Basic
import Towers.Algebra.Magnus.MagnusSeries

/-!
# Geometric inverses in the Magnus ring

This file formalizes Efrat--Chapman, Lemma 2.1.  A series with zero
constant coefficient is topologically nilpotent degree by degree, so its
geometric series is a well-defined two-sided inverse of `1 - α`.
-/

namespace EChapma
namespace MSeries

open Finset

variable {R X : Type*} [Ring R]

/-- A series vanishes in every degree strictly below `n`. -/
def VanishesBelow (f : MSeries R X) (n : ℕ) : Prop :=
  ∀ w, w.length < n → f w = 0

theorem vanishesBelow_zero (f : MSeries R X) : VanishesBelow f 0 := by
  intro w hw
  omega

theorem shift_vanishesBelow {f : MSeries R X} {n : ℕ}
    (hf : VanishesBelow f (n + 1)) (x : X) :
    VanishesBelow (shift x f) n := by
  intro w hw
  exact hf (FreeMonoid.of x * w) (by
    simpa [Nat.add_comm] using Nat.add_lt_add_left hw 1)

/--
Right multiplication by a series with zero constant coefficient raises
the vanishing order by one.
-/
theorem vanishes_below_succ {a : MSeries R X} (ha : a 1 = 0) :
    ∀ n (f : MSeries R X), VanishesBelow f n → VanishesBelow (f * a) (n + 1)
  | 0, f, _ => by
      intro w hw
      have hw0 : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
      subst w
      simp [ha]
  | n + 1, f, hf => by
      intro w
      refine FreeMonoid.casesOn
        (C := fun w => w.length < n + 1 + 1 → (f * a) w = 0) w ?_ ?_
      · intro hw
        simp [ha]
      · intro x v hw
        rw [apply_of_mul, hf 1 (by simp)]
        simp only [MulZeroClass.zero_mul, zero_add]
        exact vanishes_below_succ ha n (shift x f)
          (shift_vanishesBelow hf x) v (by
            simp only [FreeMonoid.length_mul, FreeMonoid.length_of] at hw
            omega)

/-- Powers of an augmentation series have order at least their exponent. -/
theorem pow_vanishesBelow {a : MSeries R X} (ha : a 1 = 0) :
    ∀ n, VanishesBelow (a ^ n) n
  | 0 => vanishesBelow_zero _
  | n + 1 => by
      rw [pow_succ]
      exact vanishes_below_succ ha n (a ^ n) (pow_vanishesBelow ha n)

/--
The coefficientwise geometric series.  At a word `w`, powers through
`w.length` are enough because all later powers have zero coefficient.
-/
def geometricInverse (a : MSeries R X) : MSeries R X :=
  ⟨fun w => ∑ k ∈ range (w.length + 1), (a ^ k) w⟩

@[simp]
theorem geometricInverse_apply (a : MSeries R X) (w : FreeMonoid X) :
    geometricInverse a w = ∑ k ∈ range (w.length + 1), (a ^ k) w :=
  rfl

theorem sum_apply_series {ι : Type*} (s : Finset ι)
    (f : ι → MSeries R X) (w : FreeMonoid X) :
    (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

/--
Every sufficiently long finite geometric sum has the same coefficient as
`geometricInverse`.
-/
theorem geometric_inverse_range {a : MSeries R X}
    (ha : a 1 = 0) {N : ℕ} {w : FreeMonoid X} (hw : w.length < N) :
    geometricInverse a w = (∑ k ∈ range N, a ^ k) w := by
  rw [geometricInverse_apply, sum_apply_series]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hkN hkSmall
  simp only [mem_range] at hkN
  have hwk : w.length < k := by
    simpa only [mem_range, Nat.not_lt] using hkSmall
  exact pow_vanishesBelow ha k w hwk

/--
The coefficient of a product at `w` depends only on coefficients of both
factors at words of length at most `w.length`.
-/
theorem mul_apply_congr {f f' g g' : MSeries R X} {w : FreeMonoid X}
    (hf : ∀ v, v.length ≤ w.length → f v = f' v)
    (hg : ∀ v, v.length ≤ w.length → g v = g' v) :
    (f * g) w = (f' * g') w := by
  induction w using FreeMonoid.inductionOn' generalizing f f' g g' with
  | one =>
      simp [hf 1 le_rfl, hg 1 le_rfl]
  | mul_of x w ih =>
      rw [apply_of_mul, apply_of_mul]
      rw [hf 1 (by simp), hg (FreeMonoid.of x * w) le_rfl]
      congr 1
      apply ih
      · intro v hv
        exact hf (FreeMonoid.of x * v) (by simpa using Nat.succ_le_succ hv)
      · intro v hv
        exact hg v (by simpa [Nat.add_comm] using hv.trans (Nat.le_succ _))

theorem sub_geometric_inverse {a : MSeries R X} (ha : a 1 = 0) :
    (1 - a) * geometricInverse a = 1 := by
  ext w
  let N := w.length + 1
  let s : MSeries R X := ∑ k ∈ range N, a ^ k
  have hs : ∀ v, v.length ≤ w.length → geometricInverse a v = s v := by
    intro v hv
    exact geometric_inverse_range ha (by simp only [N]; omega)
  calc
    ((1 - a) * geometricInverse a) w = ((1 - a) * s) w :=
      mul_apply_congr (fun _ _ => rfl) hs
    _ = (1 - a ^ N) w := by
      simpa only [s] using congrArg (fun z : MSeries R X => z w) (mul_neg_geom_sum a N)
    _ = (1 : MSeries R X) w := by
      rw [sub_apply, pow_vanishesBelow ha N w (by simp only [N]; omega), sub_zero]

theorem geometric_inverse_sub {a : MSeries R X} (ha : a 1 = 0) :
    geometricInverse a * (1 - a) = 1 := by
  ext w
  let N := w.length + 1
  let s : MSeries R X := ∑ k ∈ range N, a ^ k
  have hs : ∀ v, v.length ≤ w.length → geometricInverse a v = s v := by
    intro v hv
    exact geometric_inverse_range ha (by simp only [N]; omega)
  calc
    (geometricInverse a * (1 - a)) w = (s * (1 - a)) w :=
      mul_apply_congr hs (fun _ _ => rfl)
    _ = (1 - a ^ N) w := by
      simpa only [s] using congrArg (fun z : MSeries R X => z w) (geom_sum_mul_neg a N)
    _ = (1 : MSeries R X) w := by
      rw [sub_apply, pow_vanishesBelow ha N w (by simp only [N]; omega), sub_zero]

/-- The geometric series is the unique two-sided inverse of `1 - a`. -/
theorem geometricInverse_unique {a b : MSeries R X} (ha : a 1 = 0)
    (hbLeft : b * (1 - a) = 1) (_hbRight : (1 - a) * b = 1) :
    b = geometricInverse a :=
  left_inv_eq_right_inv hbLeft (sub_geometric_inverse ha)

/-- The augmentation ideal of the Magnus series ring. -/
def augmentationIdeal : Ideal (MSeries R X) where
  carrier := {f | f 1 = 0}
  zero_mem' := rfl
  add_mem' {a b} hf hg := by
    change a 1 = 0 at hf
    change b 1 = 0 at hg
    change a 1 + b 1 = 0
    simp [hf, hg]
  smul_mem' c f hf := by
    change f 1 = 0 at hf
    change (c * f) 1 = 0
    simp [hf]

@[simp]
theorem mem_augmentationIdeal {f : MSeries R X} :
    f ∈ augmentationIdeal (R := R) (X := X) ↔ f 1 = 0 :=
  Iff.rfl

instance augmentation_ideal_sided :
    (augmentationIdeal (R := R) (X := X)).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    change a 1 = 0 at ha
    change (a * b) 1 = 0
    simp [ha]

@[simp]
theorem geometric_inverse_one {a : MSeries R X} :
    geometricInverse a 1 = 1 := by
  simp [geometricInverse]

theorem geometric_sub_ideal {a : MSeries R X} :
    geometricInverse a - 1 ∈ augmentationIdeal (R := R) (X := X) := by
  simp

/--
The unit `1 + a`, for `a` in the augmentation ideal.  Its inverse is the
geometric series in `-a`.
-/
def oneAddUnit (a : MSeries R X)
    (ha : a ∈ augmentationIdeal (R := R) (X := X)) :
    (MSeries R X)ˣ where
  val := 1 + a
  inv := geometricInverse (-a)
  val_inv := by
    simpa only [sub_neg_eq_add] using sub_geometric_inverse (a := -a) (by simpa using ha)
  inv_val := by
    simpa only [sub_neg_eq_add] using geometric_inverse_sub (a := -a) (by simpa using ha)

@[simp]
theorem add_unit_val (a : MSeries R X)
    (ha : a ∈ augmentationIdeal (R := R) (X := X)) :
    (oneAddUnit a ha : MSeries R X) = 1 + a :=
  rfl

/--
The subgroup of units congruent to `1` modulo a two-sided ideal.
-/
def plusIdealSubgroup (J : Ideal (MSeries R X)) [J.IsTwoSided] :
    Subgroup (MSeries R X)ˣ where
  carrier := {u | (u : MSeries R X) - 1 ∈ J}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    change (↑u * ↑v : MSeries R X) - 1 ∈ J
    have h₁ : (u : MSeries R X) * ((v : MSeries R X) - 1) ∈ J :=
      J.mul_mem_left _ hv
    have h₂ : (u : MSeries R X) - 1 ∈ J := hu
    rw [show (↑u * ↑v : MSeries R X) - 1 =
      ↑u * (↑v - 1) + (↑u - 1) by noncomm_ring]
    exact J.add_mem h₁ h₂
  inv_mem' {u} hu := by
    change (↑(u⁻¹) : MSeries R X) - 1 ∈ J
    have h :
        -(↑(u⁻¹) : MSeries R X) * ((u : MSeries R X) - 1) ∈ J :=
      J.mul_mem_left _ hu
    rw [show (↑(u⁻¹) : MSeries R X) - 1 =
      -↑(u⁻¹) * (↑u - 1) by
        rw [neg_mul, mul_sub, Units.inv_mul]
        noncomm_ring]
    exact h

instance plus_ideal_normal
    (J : Ideal (MSeries R X)) [J.IsTwoSided] :
    (plusIdealSubgroup J).Normal where
  conj_mem u hu v := by
    change (↑(v * u * v⁻¹) : MSeries R X) - 1 ∈ J
    have hleft :
        (v : MSeries R X) * ((u : MSeries R X) - 1) ∈ J :=
      J.mul_mem_left _ hu
    have hright :
        (v : MSeries R X) * ((u : MSeries R X) - 1) *
            (v⁻¹ : (MSeries R X)ˣ) ∈ J :=
      J.mul_mem_right _ hleft
    rw [show (↑(v * u * v⁻¹) : MSeries R X) - 1 =
      ↑v * (↑u - 1) * ↑(v⁻¹) by
        simp only [Units.val_mul]
        rw [mul_sub, sub_mul, mul_one, Units.mul_inv]]
    exact hright

@[simp]
theorem one_plus_subgroup {J : Ideal (MSeries R X)} [J.IsTwoSided]
    {u : (MSeries R X)ˣ} :
    u ∈ plusIdealSubgroup J ↔ (u : MSeries R X) - 1 ∈ J :=
  Iff.rfl

/--
Every element `1 + a` with `a ∈ J ⊆ augmentationIdeal` belongs to the
subgroup of units congruent to `1` modulo `J`.
-/
theorem plus_ideal_subgroup
    (J : Ideal (MSeries R X)) [J.IsTwoSided]
    (hJ : J ≤ augmentationIdeal (R := R) (X := X))
    {a : MSeries R X} (ha : a ∈ J) :
    oneAddUnit a (hJ ha) ∈ plusIdealSubgroup J := by
  change (1 + a : MSeries R X) - 1 ∈ J
  simpa using ha

end MSeries
end EChapma
