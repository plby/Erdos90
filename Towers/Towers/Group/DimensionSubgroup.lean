import Towers.Algebra.Augmentation
import Towers.Group.Filtration
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

open scoped commutatorElement

/-!
# Dimension subgroups from augmentation ideals

For any power of the augmentation ideal, we can take the subgroup of group elements
whose `g - 1` lies in that ideal.  Over suitable coefficient rings/indices this is the
usual dimension-subgroup presentation of the Zassenhaus filtration.
-/

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (R G : Type*) [CommRing R] [Group G]

private theorem mul_sub_identity {A : Type*} [Ring A] (x y : A) :
    x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul]
  abel_nf

private theorem conj_sub_identity {A : Type*} [Ring A] (x z xi : A) (h : x * xi = 1) :
    x * z * xi - 1 = x * (z - 1) * xi := by
  calc
    x * z * xi - 1 = x * z * xi - x * xi := by rw [h]
    _ = x * (z - 1) * xi := by
      simp only [sub_eq_add_neg, mul_add, mul_neg, mul_one]
      simp only [mul_assoc]
      rw [add_mul]
      simp only [neg_mul]
      rw [← mul_assoc x z xi]

private theorem inv_sub_identity {A : Type*} [Ring A] (x y : A) (h : y * x = 1) :
    y - 1 = - y * (x - 1) := by
  simp only [sub_eq_add_neg, mul_add, mul_neg, mul_one]
  rw [neg_mul y x, h]
  abel

private theorem comm_sub_identity {A : Type*} [Ring A] (x y xi yi : A)
    (hyxi : y * x * xi * yi = 1) :
    x * y * xi * yi - 1 =
      ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * xi * yi := by
  calc
    x * y * xi * yi - 1 = x * y * xi * yi - y * x * xi * yi := by rw [hyxi]
    _ = (x * y - y * x) * xi * yi := by noncomm_ring
    _ = ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * xi * yi := by noncomm_ring

/-- The subgroup cut out by the `n`th augmentation power: `g ∈ D_n` iff `g - 1 ∈ I^n`.
This is the dimension-subgroup form of the Zassenhaus filtration. -/
def dSubgro (n : ℕ) : Subgroup G where
  carrier :=
    {g : G |
      (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
        augmentationPower R G n}
  one_mem' := by
    change (_root_.MonoidAlgebra.of R G (1 : G) - 1 : MonoidAlgebra R G) ∈
      augmentationPower R G n
    rw [map_one]
    simp
  mul_mem' := by
    intro g h hg hh
    let I := augmentationPower R G n
    haveI : I.IsTwoSided := augmentation_two_sided R G n
    let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
    let y : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h
    change (_root_.MonoidAlgebra.of R G (g * h) - 1 : MonoidAlgebra R G) ∈ I
    rw [map_mul]
    change (x * y - 1 : MonoidAlgebra R G) ∈ I
    rw [mul_sub_identity x y]
    have hprod : (x - 1) * (y - 1) ∈ I := Ideal.mul_mem_right (y - 1) I hg
    exact I.add_mem (I.add_mem hprod hg) hh
  inv_mem' := by
    intro g hg
    let I := augmentationPower R G n
    let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
    let y : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g⁻¹
    change (y - 1 : MonoidAlgebra R G) ∈ I
    have hyx0 :
        (_root_.MonoidAlgebra.of R G g⁻¹) * (_root_.MonoidAlgebra.of R G g) =
          (1 : MonoidAlgebra R G) := by
      rw [← map_mul]
      simp only [inv_mul_cancel]
      rfl
    have hyx : y * x = 1 := by
      simpa [x, y] using hyx0
    rw [inv_sub_identity x y hyx]
    have hmem : y * (x - 1) ∈ I := by
      exact Ideal.mul_mem_left I y hg
    rw [neg_mul]
    exact Submodule.neg_mem I hmem

@[simp] theorem mem_dimensionSubgroup {n : ℕ} {g : G} :
    g ∈ dSubgro R G n ↔
      (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈ augmentationPower R G n := Iff.rfl



/-- Dimension subgroups are normal: the defining ideal condition is stable under conjugation. -/
theorem dimensionSubgroup_normal (n : ℕ) : (dSubgro R G n).Normal where
  conj_mem := by
    intro g hg k
    rw [mem_dimensionSubgroup] at hg ⊢
    let I := augmentationPower R G n
    haveI : I.IsTwoSided := augmentation_two_sided R G n
    let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G k
    let z : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
    let xi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G k⁻¹
    change (_root_.MonoidAlgebra.of R G (k * g * k⁻¹) - 1 : MonoidAlgebra R G) ∈
      I
    have hword0 : _root_.MonoidAlgebra.of R G (k * g * k⁻¹) =
        (_root_.MonoidAlgebra.of R G k) * (_root_.MonoidAlgebra.of R G g) *
          (_root_.MonoidAlgebra.of R G k⁻¹) := by
      rw [map_mul, map_mul]
    have hword : _root_.MonoidAlgebra.of R G (k * g * k⁻¹) = x * z * xi := by
      simp [x, z, xi, hword0]
    rw [hword]
    have hxxi0 :
        (_root_.MonoidAlgebra.of R G k) * (_root_.MonoidAlgebra.of R G k⁻¹) =
          (1 : MonoidAlgebra R G) := by
      rw [← map_mul]
      simp only [mul_inv_cancel]
      rfl
    have hxxi : x * xi = 1 := by
      simpa [x, xi] using hxxi0
    rw [conj_sub_identity x z xi hxxi]
    have hleft : x * (z - 1) ∈ I := Ideal.mul_mem_left I x hg
    exact Ideal.mul_mem_right xi I hleft

@[simp] theorem dimension_subgroup_top : dSubgro R G 0 = ⊤ := by
  ext g
  simp [dSubgro, augmentationPower_zero]

@[simp] theorem dimension_one_top : dSubgro R G 1 = ⊤ := by
  ext g
  constructor
  · intro _; trivial
  · intro _
    rw [mem_dimensionSubgroup, augmentationPower_one]
    exact sub_augmentation_ideal R G g

/-- The dimension subgroups are descending with the index. -/
theorem dimensionSubgroup_antitone : Antitone (dSubgro R G) := by
  intro m n hmn g hg
  rw [mem_dimensionSubgroup] at hg ⊢
  dsimp [augmentationPower] at hg ⊢
  exact Ideal.pow_le_pow_right hmn hg

/-- Consecutive dimension subgroups are nested. -/
theorem dimension_subgroup_succ (n : ℕ) :
    dSubgro R G (n + 1) ≤ dSubgro R G n :=
  dimensionSubgroup_antitone R G (Nat.le_succ n)






/-- Joins of two terms in the descending dimension filtration are the term at the
smaller index. -/
theorem dimension_sup_min (m n : ℕ) :
    dSubgro R G m ⊔ dSubgro R G n =
      dSubgro R G (min m n) := by
  rcases le_total m n with hmn | hnm
  · have hle : dSubgro R G n ≤ dSubgro R G m :=
      dimensionSubgroup_antitone R G hmn
    simpa [min_eq_left hmn] using (sup_eq_left.mpr hle)
  · have hle : dSubgro R G m ≤ dSubgro R G n :=
      dimensionSubgroup_antitone R G hnm
    simpa [min_eq_right hnm] using (sup_eq_right.mpr hle)

/-- Intersections of two terms in the descending dimension filtration are the term at
the larger index. -/
theorem dimension_inf_max (m n : ℕ) :
    dSubgro R G m ⊓ dSubgro R G n =
      dSubgro R G (max m n) := by
  apply le_antisymm
  · intro g hg
    have hpair : g ∈ dSubgro R G m ∧ g ∈ dSubgro R G n := by
      simpa using hg
    rcases le_total m n with hmn | hnm
    · simpa [max_eq_right hmn] using hpair.2
    · simpa [max_eq_left hnm] using hpair.1
  · intro g hg
    constructor
    · exact dimensionSubgroup_antitone R G (Nat.le_max_left m n) hg
    · exact dimensionSubgroup_antitone R G (Nat.le_max_right m n) hg

/-- The basic commutator estimate for positive dimension-subgroup indices:
if `g ∈ D_m` and `h ∈ D_n` with `m,n > 0`, then `[g,h] ∈ D_{m+n}`.

The positivity hypotheses are the mild bookkeeping needed for the noncommutative
ideal-power lemma used by mathlib (`Submodule.pow_add`). -/
theorem commutator_dimension_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {g h : G} (hg : g ∈ dSubgro R G m) (hh : h ∈ dSubgro R G n) :
    ⁅g, h⁆ ∈ dSubgro R G (m + n) := by
  rw [mem_dimensionSubgroup] at hg hh ⊢
  let Im := augmentationPower R G m
  let In := augmentationPower R G n
  let J := augmentationPower R G (m + n)
  let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
  let y : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h
  let xi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g⁻¹
  let yi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h⁻¹
  change (_root_.MonoidAlgebra.of R G ⁅g, h⁆ - 1 : MonoidAlgebra R G) ∈ J
  have hword : _root_.MonoidAlgebra.of R G ⁅g, h⁆ = x * y * xi * yi := by
    simp [x, y, xi, yi, commutatorElement_def, map_mul]
  rw [hword]
  have hxi : x * xi = 1 := by
    change (_root_.MonoidAlgebra.of R G g) * _ = 1
    rw [← map_mul, mul_inv_cancel]
    exact map_one (_root_.MonoidAlgebra.of R G)
  have hyxi : y * x * xi * yi = 1 := by
    calc
      y * x * xi * yi = y * (x * xi) * yi := by noncomm_ring
      _ = y * 1 * yi := by rw [hxi]
      _ = 1 := by
        change (_root_.MonoidAlgebra.of R G h) * 1 * _ = 1
        simp only [mul_one]
        rw [← map_mul, mul_inv_cancel]
        exact map_one (_root_.MonoidAlgebra.of R G)
  rw [comm_sub_identity x y xi yi hyxi]
  have hx : x - 1 ∈ Im := by simpa [x, Im, augmentationPower] using hg
  have hy : y - 1 ∈ In := by simpa [y, In, augmentationPower] using hh
  have hxy : (x - 1) * (y - 1) ∈ J := by
    dsimp [J, Im, In, augmentationPower] at hx hy ⊢
    simpa [Submodule.pow_add _ hn] using (Ideal.mul_mem_mul hx hy)
  have hyx : (y - 1) * (x - 1) ∈ J := by
    dsimp [J, Im, In, augmentationPower] at hx hy ⊢
    have hmem : (y - 1) * (x - 1) ∈
        augmentationIdeal R G ^ n * augmentationIdeal R G ^ m :=
      Ideal.mul_mem_mul hy hx
    have hpow : augmentationIdeal R G ^ (n + m) =
        augmentationIdeal R G ^ n * augmentationIdeal R G ^ m :=
      Submodule.pow_add _ hm
    rw [← hpow] at hmem
    simpa [Nat.add_comm] using hmem
  have hdiff : (x - 1) * (y - 1) - (y - 1) * (x - 1) ∈ J := J.sub_mem hxy hyx
  have hright1 : ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * xi ∈ J :=
    Ideal.mul_mem_right xi J hdiff
  exact Ideal.mul_mem_right yi J hright1

/-- General commutator estimate for dimension subgroups, including zero indices.
The zero cases are handled by the ideal-absorption form of augmentation-power
multiplication, so no positivity hypotheses are needed. -/
theorem commutator_dimension_any {m n : ℕ}
    {g h : G} (hg : g ∈ dSubgro R G m) (hh : h ∈ dSubgro R G n) :
    ⁅g, h⁆ ∈ dSubgro R G (m + n) := by
  rw [mem_dimensionSubgroup] at hg hh ⊢
  let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
  let y : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h
  let xi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g⁻¹
  let yi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h⁻¹
  change (_root_.MonoidAlgebra.of R G ⁅g, h⁆ - 1 : MonoidAlgebra R G) ∈
    augmentationPower R G (m + n)
  have hword : _root_.MonoidAlgebra.of R G ⁅g, h⁆ = x * y * xi * yi := by
    simp [x, y, xi, yi, commutatorElement_def, map_mul]
  rw [hword]
  have hxi : x * xi = 1 := by
    change (_root_.MonoidAlgebra.of R G g) * _ = 1
    rw [← map_mul, mul_inv_cancel]
    exact map_one (_root_.MonoidAlgebra.of R G)
  have hyxi : y * x * xi * yi = 1 := by
    calc
      y * x * xi * yi = y * (x * xi) * yi := by noncomm_ring
      _ = y * 1 * yi := by rw [hxi]
      _ = 1 := by
        change (_root_.MonoidAlgebra.of R G h) * 1 * _ = 1
        simp only [mul_one]
        rw [← map_mul, mul_inv_cancel]
        exact map_one (_root_.MonoidAlgebra.of R G)
  rw [comm_sub_identity x y xi yi hyxi]
  have hx : x - 1 ∈ augmentationPower R G m := by simpa [x] using hg
  have hy : y - 1 ∈ augmentationPower R G n := by simpa [y] using hh
  have hxy : (x - 1) * (y - 1) ∈ augmentationPower R G (m + n) :=
    mul_augmentation_add (R := R) (G := G) hx hy
  have hyx : (y - 1) * (x - 1) ∈ augmentationPower R G (m + n) :=
    mul_augmentation_comm (R := R) (G := G) hx hy
  let J := augmentationPower R G (m + n)
  have hdiff : (x - 1) * (y - 1) - (y - 1) * (x - 1) ∈ J := by
    exact J.sub_mem hxy hyx
  have hright1 : ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * xi ∈ J :=
    Ideal.mul_mem_right xi J hdiff
  exact Ideal.mul_mem_right yi J hright1

/-- Subgroup form of the all-index commutator estimate. -/
theorem dimension_add_any {m n : ℕ} :
    ⁅dSubgro R G m, dSubgro R G n⁆ ≤
      dSubgro R G (m + n) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutator_dimension_any R G hg hh

/-- Subgroup form of the positive-index commutator estimate. -/
theorem dimension_subgroup_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⁅dSubgro R G m, dSubgro R G n⁆ ≤
      dSubgro R G (m + n) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutator_dimension_add R G hm hn hg hh

/-- Commutators lie in the second dimension subgroup.  This is the easy
`[G,G] ≤ D₂` half of the degree-one control story, valid over any coefficient ring. -/
theorem commutator_dimension_two (g h : G) :
    ⁅g, h⁆ ∈ dSubgro R G 2 := by
  rw [mem_dimensionSubgroup]
  let I := augmentationIdeal R G
  let J := augmentationPower R G 2
  let x : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g
  let y : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h
  let xi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G g⁻¹
  let yi : MonoidAlgebra R G := _root_.MonoidAlgebra.of R G h⁻¹
  change (_root_.MonoidAlgebra.of R G ⁅g, h⁆ - 1 : MonoidAlgebra R G) ∈ J
  have hword : _root_.MonoidAlgebra.of R G ⁅g, h⁆ = x * y * xi * yi := by
    simp [x, y, xi, yi, commutatorElement_def, map_mul]
  rw [hword]
  have hxi : x * xi = 1 := by
    change (_root_.MonoidAlgebra.of R G g) * (_root_.MonoidAlgebra.of R G g⁻¹) = 1
    rw [← map_mul, mul_inv_cancel]
    exact map_one (_root_.MonoidAlgebra.of R G)
  have hyxi : y * x * xi * yi = 1 := by
    calc
      y * x * xi * yi = y * (x * xi) * yi := by noncomm_ring
      _ = y * 1 * yi := by rw [hxi]
      _ = 1 := by
        change (_root_.MonoidAlgebra.of R G h) * 1 *
            (_root_.MonoidAlgebra.of R G h⁻¹) = 1
        simp only [mul_one]
        rw [← map_mul, mul_inv_cancel]
        exact map_one (_root_.MonoidAlgebra.of R G)
  rw [comm_sub_identity x y xi yi hyxi]
  have hxI : x - 1 ∈ I := by
    simp [x, I]
  have hyI : y - 1 ∈ I := by
    simp [y, I]
  have hJ : J = I * I := by
    dsimp [J, I, augmentationPower]
    change augmentationIdeal R G ^ (1 + 1) = _
    rw [Submodule.pow_succ, Submodule.pow_one]
  have hxy : (x - 1) * (y - 1) ∈ J := by
    rw [hJ]
    exact Ideal.mul_mem_mul hxI hyI
  have hyx : (y - 1) * (x - 1) ∈ J := by
    rw [hJ]
    exact Ideal.mul_mem_mul hyI hxI
  have hdiff : (x - 1) * (y - 1) - (y - 1) * (x - 1) ∈ J := by
    exact J.sub_mem hxy hyx
  have hright1 : ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * xi ∈ J :=
    Ideal.mul_mem_right xi J hdiff
  exact Ideal.mul_mem_right yi J hright1


/-- Predicate form: `g` has dimension depth at least `n` over `R`. -/
def dimensionDepthLeast (g : G) (n : ℕ) : Prop :=
  g ∈ dSubgro R G n

@[simp] theorem dimension_depth {g : G} {n : ℕ} :
    dimensionDepthLeast R G g n ↔ g ∈ dSubgro R G n := Iff.rfl

/-- Predicate form of the max/intersection rule for dimension depth. -/
theorem dimension_least_max {g : G} {m n : ℕ} :
    dimensionDepthLeast R G g (max m n) ↔
      dimensionDepthLeast R G g m ∧ dimensionDepthLeast R G g n := by
  change g ∈ dSubgro R G (max m n) ↔
    g ∈ dSubgro R G m ∧ g ∈ dSubgro R G n
  rw [← dimension_inf_max (R := R) (G := G) m n]
  simp


/-- Predicate form of the min/join rule for dimension depth.  Since the filtration is
a chain, membership in the shallower of two terms is equivalent to membership in at
least one of them. -/
theorem dimension_least_min {g : G} {m n : ℕ} :
    dimensionDepthLeast R G g (min m n) ↔
      dimensionDepthLeast R G g m ∨ dimensionDepthLeast R G g n := by
  rcases le_total m n with hmn | hnm
  · simp only [min_eq_left hmn]
    constructor
    · intro hg; exact Or.inl hg
    · rintro (hg | hg)
      · exact hg
      · exact dimensionSubgroup_antitone R G hmn hg
  · simp only [min_eq_right hnm]
    constructor
    · intro hg; exact Or.inr hg
    · rintro (hg | hg)
      · exact dimensionSubgroup_antitone R G hnm hg
      · exact hg

@[simp] theorem dimension_least_zero (g : G) :
    dimensionDepthLeast R G g 0 := by
  change g ∈ dSubgro R G 0
  simp

@[simp] theorem dimension_least_one (g : G) :
    dimensionDepthLeast R G g 1 := by
  change g ∈ dSubgro R G 1
  simp

/-- Same-depth certificates are closed under multiplication. -/
theorem dimension_least_mul {g h : G} {n : ℕ}
    (hg : dimensionDepthLeast R G g n) (hh : dimensionDepthLeast R G h n) :
    dimensionDepthLeast R G (g * h) n :=
  (dSubgro R G n).mul_mem hg hh

/-- The identity element has every dimension depth. -/
@[simp] theorem dimension_least_elem (n : ℕ) :
    dimensionDepthLeast R G (1 : G) n :=
  (dSubgro R G n).one_mem

/-- Inverses preserve dimension depth. -/
theorem dimension_least_inv {g : G} {n : ℕ}
    (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R G g⁻¹ n :=
  (dSubgro R G n).inv_mem hg

/-- Quotients of same-depth elements preserve dimension depth. -/
theorem dimension_least_div {g h : G} {n : ℕ}
    (hg : dimensionDepthLeast R G g n) (hh : dimensionDepthLeast R G h n) :
    dimensionDepthLeast R G (g / h) n :=
  (dSubgro R G n).div_mem hg hh

/-- Integer powers preserve a fixed dimension-depth certificate. -/
theorem dimension_least_zpow {g : G} {n : ℕ} (k : ℤ)
    (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R G (g ^ k) n :=
  (dSubgro R G n).zpow_mem hg k

/-- Ordinary natural powers preserve a fixed dimension-depth certificate. -/
theorem dimension_least_pow {g : G} {n k : ℕ}
    (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R G (g ^ k) n := by
  induction k with
  | zero => simp [dimensionDepthLeast]
  | succ k ih =>
      simpa [pow_succ] using (dSubgro R G n).mul_mem ih hg

/-- Conjugation preserves dimension depth. -/
theorem dimension_depth_conj {g x : G} {n : ℕ}
    (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R G (x * g * x⁻¹) n :=
  (dimensionSubgroup_normal R G n).conj_mem g hg x

/-- Conjugation preserves and reflects dimension depth. -/
theorem dimension_least_conj {g x : G} {n : ℕ} :
    dimensionDepthLeast R G (x * g * x⁻¹) n ↔ dimensionDepthLeast R G g n := by
  constructor
  · intro h
    have h' := dimension_depth_conj (R := R) (G := G)
      (g := x * g * x⁻¹) (x := x⁻¹) h
    simpa [mul_assoc] using h'
  · intro h
    exact dimension_depth_conj (R := R) (G := G) (x := x) h

/-- Deeper membership implies shallower membership. -/
theorem dimension_least {g : G} {m n : ℕ} (hmn : m ≤ n)
    (hg : dimensionDepthLeast R G g n) : dimensionDepthLeast R G g m :=
  dimensionSubgroup_antitone R G hmn hg

/-- Products preserve the minimum of two dimension-depth certificates. -/
theorem dimension_depth_min {g h : G} {m n : ℕ}
    (hg : dimensionDepthLeast R G g m) (hh : dimensionDepthLeast R G h n) :
    dimensionDepthLeast R G (g * h) (min m n) := by
  exact (dSubgro R G (min m n)).mul_mem
    (dimension_least (R := R) (G := G) (Nat.min_le_left m n) hg)
    (dimension_least (R := R) (G := G) (Nat.min_le_right m n) hh)

/-- All-index commutator depth estimate in predicate form. -/
theorem dimension_least_commutator {m n : ℕ} {g h : G}
    (hg : dimensionDepthLeast R G g m) (hh : dimensionDepthLeast R G h n) :
    dimensionDepthLeast R G ⁅g, h⁆ (m + n) :=
  commutator_dimension_any R G hg hh

/-- Commutators have dimension depth at least two. -/
theorem dimension_least_two (g h : G) :
    dimensionDepthLeast R G ⁅g, h⁆ 2 :=
  commutator_dimension_two R G g h

/-- Commuting a positive-depth element with an arbitrary element raises depth by one. -/
theorem dimension_least_any {n : ℕ} (hn : n ≠ 0)
    {g : G} (hg : dimensionDepthLeast R G g n) (h : G) :
    dimensionDepthLeast R G ⁅g, h⁆ (n + 1) := by
  have hh : dimensionDepthLeast R G h 1 := dimension_least_one R G h
  exact commutator_dimension_add R G hn (by decide : (1 : ℕ) ≠ 0) hg hh

/-- Commuting an arbitrary element with a positive-depth element raises depth by one. -/
theorem dimension_depth_any {n : ℕ} (hn : n ≠ 0)
    (h : G) {g : G} (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R G ⁅h, g⁆ (1 + n) := by
  have hh : dimensionDepthLeast R G h 1 := dimension_least_one R G h
  exact commutator_dimension_add R G (by decide : (1 : ℕ) ≠ 0) hn hh hg

/-- The augmentation/dimension subgroups bundled as a descending filtration. -/
def dimensionFiltration : DFilt G where
  term := dSubgro R G
  antitone' := dimensionSubgroup_antitone R G
  normal' := dimensionSubgroup_normal R G
  one_eq_top' := dimension_one_top R G


end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (R : Type*) [CommRing R] {G H : Type*} [Group G] [Group H]

/-- Group homomorphisms preserve dimension subgroups: the induced group-algebra map
sends augmentation powers into augmentation powers. -/
theorem dimension_subgroup_comap (φ : G →* H) (n : ℕ) :
    dSubgro R G n ≤ (dSubgro R H n).comap φ := by
  intro g hg
  rw [mem_dimensionSubgroup] at hg
  change φ g ∈ dSubgro R H n
  rw [mem_dimensionSubgroup]
  let f := (MonoidAlgebra.mapDomainAlgHom R R φ).toRingHom
  have hx : f (_root_.MonoidAlgebra.of R G g - 1) ∈
      Ideal.map f (augmentationPower R G n) := Ideal.mem_map_of_mem f hg
  have hle := augmentation_power_domain (R := R) (G := G) φ n
  have hx' := hle hx
  simpa [f, MonoidAlgebra.mapDomainAlgHom, map_sub] using hx'


/-- Homomorphisms preserve dimension-depth certificates. -/
theorem at_least_map (φ : G →* H) {g : G} {n : ℕ}
    (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R H (φ g) n := by
  change φ g ∈ dSubgro R H n
  exact dimension_subgroup_comap R φ n hg

/-- Isomorphisms reflect and preserve dimension-depth certificates. -/
theorem dimension_depth_least (e : G ≃* H) {g : G} {n : ℕ} :
    dimensionDepthLeast R H (e g) n ↔ dimensionDepthLeast R G g n := by
  constructor
  · intro h
    have h' := at_least_map (R := R) e.symm.toMonoidHom h
    simpa using h'
  · intro h
    exact at_least_map (R := R) e.toMonoidHom h


/-- Dimension subgroups commute with finite binary products. -/
theorem dimensionSubgroup_prod (G H : Type*) [Group G] [Group H] (n : ℕ) :
    dSubgro R (G × H) n =
      (dSubgro R G n).prod (dSubgro R H n) := by
  apply le_antisymm
  · intro x hx
    rcases x with ⟨g, h⟩
    rw [Subgroup.mem_prod]
    constructor
    · exact dimension_subgroup_comap R (MonoidHom.fst G H) n hx
    · exact dimension_subgroup_comap R (MonoidHom.snd G H) n hx
  · intro x hx
    rcases x with ⟨g, h⟩
    rw [Subgroup.mem_prod] at hx
    rcases hx with ⟨hg, hh⟩
    have hg' : (g, (1 : H)) ∈ dSubgro R (G × H) n := by
      change MonoidHom.inl G H g ∈ dSubgro R (G × H) n
      exact dimension_subgroup_comap R (MonoidHom.inl G H) n hg
    have hh' : ((1 : G), h) ∈ dSubgro R (G × H) n := by
      change MonoidHom.inr G H h ∈ dSubgro R (G × H) n
      exact dimension_subgroup_comap R (MonoidHom.inr G H) n hh
    have hm := (dSubgro R (G × H) n).mul_mem hg' hh'
    simpa using hm

/-- Predicate-level product criterion for dimension depth.  This is the
elementwise form of `dimensionSubgroup_prod`, useful in relator-depth
bookkeeping without rewriting subgroup equalities. -/
theorem dimension_least_prod (G H : Type*) [Group G] [Group H]
    (g : G) (h : H) (n : ℕ) :
    dimensionDepthLeast R (G × H) (g, h) n ↔
      dimensionDepthLeast R G g n ∧ dimensionDepthLeast R H h n := by
  change (g, h) ∈ dSubgro R (G × H) n ↔
    g ∈ dSubgro R G n ∧ h ∈ dSubgro R H n
  rw [dimensionSubgroup_prod (R := R) G H n, Subgroup.mem_prod]

/-- Left product inclusion preserves dimension depth, in predicate form. -/
theorem dimension_least_inl {G H : Type*} [Group G] [Group H]
    {g : G} {n : ℕ} (hg : dimensionDepthLeast R G g n) :
    dimensionDepthLeast R (G × H) (g, 1) n := by
  exact (dimension_least_prod (R := R) G H g 1 n).2
    ⟨hg, dimension_least_elem (R := R) (G := H) n⟩

/-- Right product inclusion preserves dimension depth, in predicate form. -/
theorem dimension_least_inr {G H : Type*} [Group G] [Group H]
    {h : H} {n : ℕ} (hh : dimensionDepthLeast R H h n) :
    dimensionDepthLeast R (G × H) (1, h) n := by
  exact (dimension_least_prod (R := R) G H 1 h n).2
    ⟨dimension_least_elem (R := R) (G := G) n, hh⟩

/-- First projection of a product-depth certificate. -/
theorem dimension_least_fst {G H : Type*} [Group G] [Group H]
    {x : G × H} {n : ℕ}
    (hx : dimensionDepthLeast R (G × H) x n) :
    dimensionDepthLeast R G x.1 n := by
  rcases x with ⟨g, h⟩
  exact ((dimension_least_prod (R := R) G H g h n).1 hx).1

/-- Second projection of a product-depth certificate. -/
theorem dimension_least_snd {G H : Type*} [Group G] [Group H]
    {x : G × H} {n : ℕ}
    (hx : dimensionDepthLeast R (G × H) x n) :
    dimensionDepthLeast R H x.2 n := by
  rcases x with ⟨g, h⟩
  exact ((dimension_least_prod (R := R) G H g h n).1 hx).2

/-- Swapping product coordinates preserves and reflects dimension depth. -/
theorem dimension_least_swap {G H : Type*} [Group G] [Group H]
    (g : G) (h : H) (n : ℕ) :
    dimensionDepthLeast R (H × G) (h, g) n ↔
      dimensionDepthLeast R (G × H) (g, h) n := by
  rw [dimension_least_prod (R := R) H G h g n,
    dimension_least_prod (R := R) G H g h n]
  exact and_comm

/-- Diagonal product depth is exactly the original dimension depth. -/
theorem dimension_least_diag {G : Type*} [Group G]
    (g : G) (n : ℕ) :
    dimensionDepthLeast R (G × G) (g, g) n ↔
      dimensionDepthLeast R G g n := by
  rw [dimension_least_prod (R := R) G G g g n]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- Dimension subgroups are normal as typeclass instances in this product-quotient block. -/
local instance dimensionSubgroupNormalInst (K : Type*) [Group K] (n : ℕ) :
    (dSubgro R K n).Normal := dimensionSubgroup_normal R K n

/-- Quotients by dimension subgroups commute with binary products. -/
noncomputable def dimensionProdEquiv (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (G × H) ⧸ dSubgro R (G × H) n ≃*
      (G ⧸ dSubgro R G n) × (H ⧸ dSubgro R H n) :=
  (QuotientGroup.quotientMulEquivOfEq (dimensionSubgroup_prod (R := R) G H n)).trans
    (Towers.quotientProdEquiv (dSubgro R G n) (dSubgro R H n))

@[simp] theorem dimension_equiv_mk (G H : Type*) [Group G] [Group H]
    (n : ℕ) (g : G) (h : H) :
    dimensionProdEquiv R G H n
        (QuotientGroup.mk' (dSubgro R (G × H) n) (g, h)) =
      (QuotientGroup.mk' (dSubgro R G n) g,
        QuotientGroup.mk' (dSubgro R H n) h) := rfl


@[simp] theorem dimension_prod_mk (G H : Type*) [Group G] [Group H]
    (n : ℕ) (g : G) (h : H) :
    (dimensionProdEquiv R G H n).symm
        (QuotientGroup.mk' (dSubgro R G n) g,
          QuotientGroup.mk' (dSubgro R H n) h) =
      QuotientGroup.mk' (dSubgro R (G × H) n) (g, h) := by
  apply (dimensionProdEquiv R G H n).injective
  simp only [MulEquiv.apply_symm_apply]
  change (QuotientGroup.mk' (dSubgro R G n) g,
      QuotientGroup.mk' (dSubgro R H n) h) = _
  rw [dimension_equiv_mk]

/-- Cardinality formula for dimension quotients of products, using `Nat.card` for
uniform finite/infinite statements. -/
theorem nat_card_dimension (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card ((G × H) ⧸ dSubgro R (G × H) n) =
      Nat.card (G ⧸ dSubgro R G n) *
        Nat.card (H ⧸ dSubgro R H n) := by
  rw [Nat.card_congr (dimensionProdEquiv R G H n).toEquiv, Nat.card_prod]

/-- The product formula as a concrete multiplicative equivalence of term subgroups. -/
noncomputable def dimensionSubgroupProd (G H : Type*) [Group G] [Group H] (n : ℕ) :
    dSubgro R (G × H) n ≃*
      (dSubgro R G n × dSubgro R H n) where
  toFun x := by
    refine ⟨⟨(x : G × H).1, ?_⟩, ⟨(x : G × H).2, ?_⟩⟩
    · have hxprod : (x : G × H) ∈
          (dSubgro R G n).prod (dSubgro R H n) := by
        simpa [dimensionSubgroup_prod (R := R) G H n] using x.property
      exact (Subgroup.mem_prod.mp hxprod).1
    · have hxprod : (x : G × H) ∈
          (dSubgro R G n).prod (dSubgro R H n) := by
        simpa [dimensionSubgroup_prod (R := R) G H n] using x.property
      exact (Subgroup.mem_prod.mp hxprod).2
  invFun y := by
    refine ⟨((y.1 : G), (y.2 : H)), ?_⟩
    rw [dimensionSubgroup_prod (R := R) G H n, Subgroup.mem_prod]
    exact ⟨y.1.property, y.2.property⟩
  left_inv x := by
    ext <;> rfl
  right_inv y := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

@[simp] theorem dimension_subgroup_prod (G H : Type*) [Group G] [Group H]
    (n : ℕ) (x : dSubgro R (G × H) n) :
    dimensionSubgroupProd R G H n x =
      (⟨(x : G × H).1, by
          have hxprod : (x : G × H) ∈
              (dSubgro R G n).prod (dSubgro R H n) := by
            simpa [dimensionSubgroup_prod (R := R) G H n] using x.property
          exact (Subgroup.mem_prod.mp hxprod).1⟩,
       ⟨(x : G × H).2, by
          have hxprod : (x : G × H) ∈
              (dSubgro R G n).prod (dSubgro R H n) := by
            simpa [dimensionSubgroup_prod (R := R) G H n] using x.property
          exact (Subgroup.mem_prod.mp hxprod).2⟩) := rfl

/-- The dimension filtration is functorial for group homomorphisms. -/
theorem dimensionFiltration_preserves (φ : G →* H) :
    DFilt.Preserves (dimensionFiltration R G) (dimensionFiltration R H) φ := by
  intro n
  rw [Subgroup.map_le_iff_le_comap]
  exact dimension_subgroup_comap R φ n



/-- A homomorphism restricts to a map between corresponding dimension subgroups. -/
noncomputable def dSubgro.termMap {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    dSubgro R G n →* dSubgro R H n :=
  DFilt.termMap (dimensionFiltration_preserves R φ) n

@[simp] theorem dSubgro.termMap_coe {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dSubgro R G n) :
    ((dSubgro.termMap (R := R) φ n x : dSubgro R H n) : H) =
      φ (x : G) := rfl

@[simp] theorem dSubgro.termMap_id (G : Type*) [Group G] (n : ℕ) :
    dSubgro.termMap (R := R) (MonoidHom.id G) n =
      MonoidHom.id (dSubgro R G n) :=
  DFilt.termMap_id (dimensionFiltration R G) n

@[simp] theorem dSubgro.termMap_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dSubgro.termMap (R := R) (ψ.comp φ) n =
      (dSubgro.termMap (R := R) ψ n).comp
        (dSubgro.termMap (R := R) φ n) :=
  DFilt.termMap_comp (dimensionFiltration_preserves R φ)
    (dimensionFiltration_preserves R ψ) n

/-- Termwise-onto maps induce surjections on dimension subgroup terms. -/
theorem dSubgro.term_surjective_maps {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    Function.Surjective (dSubgro.termMap (R := R) φ n) := by
  simpa [dSubgro.termMap] using
    DFilt.term_surjective_maps honto n

/-- Range form of termwise onto for dimension subgroup terms. -/
theorem dSubgro.term_range_onto {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    (dSubgro.termMap (R := R) φ n).range = ⊤ := by
  simpa [dSubgro.termMap] using
    DFilt.term_range_onto honto n

/-- The `n`th dimension layer, represented as the kernel of the transition
`G/D_{n+1} → G/D_n`. -/
def dLKern (G : Type*) [Group G] (n : ℕ) :
    Subgroup (G ⧸ dSubgro R G (n + 1)) :=
  DFilt.lKern (dimensionFiltration R G) n

/-- The zeroth dimension layer kernel is trivial. -/
theorem dLKern.subsingleton_zero (G : Type*) [Group G] :
    Subsingleton (dLKern R G 0) := by
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  haveI : Subsingleton (G ⧸ dSubgro R G 1) := by
    rw [dimension_one_top]
    exact QuotientGroup.subsingleton_quotient_top
  exact Subsingleton.elim (x : G ⧸ dSubgro R G 1)
    (y : G ⧸ dSubgro R G 1)

/-- Every element of the zeroth dimension layer kernel is trivial. -/
theorem dLKern.eq_one_zero {G : Type*} [Group G]
    (x : dLKern R G 0) : x = 1 := by
  haveI : Subsingleton (dLKern R G 0) :=
    dLKern.subsingleton_zero (R := R) G
  exact Subsingleton.elim x 1

/-- The canonical map from a dimension term to its layer kernel. -/
noncomputable def dLKern.ofTerm {G : Type*} [Group G] (n : ℕ) :
    dSubgro R G n →* dLKern R G n :=
  DFilt.layerOfTerm (dimensionFiltration R G) n

@[simp] theorem dLKern.ofTerm_coe {G : Type*} [Group G] (n : ℕ)
    (x : dSubgro R G n) :
    ((dLKern.ofTerm (R := R) n x : dLKern R G n) :
        G ⧸ dSubgro R G (n + 1)) =
      QuotientGroup.mk' (dSubgro R G (n + 1)) (x : G) := rfl

/-- Every dimension layer-kernel element is represented by an element of the term. -/
theorem dLKern.ofTerm_surjective {G : Type*} [Group G] (n : ℕ) :
    Function.Surjective (dLKern.ofTerm (R := R) (G := G) n) :=
  DFilt.layer_term_surjective (dimensionFiltration R G) n

@[simp] theorem dLKern.mem_ker_term {G : Type*} [Group G] (n : ℕ)
    (x : dSubgro R G n) :
    x ∈ MonoidHom.ker (dLKern.ofTerm (R := R) n) ↔
      (x : G) ∈ dSubgro R G (n + 1) :=
  DFilt.ker_term (dimensionFiltration R G) n x

/-- The next dimension term, viewed as a subgroup of the current term. -/
def dNTerm (G : Type*) [Group G] (n : ℕ) :
    Subgroup (dSubgro R G n) :=
  DFilt.nextTermSubgroup (dimensionFiltration R G) n

@[simp] theorem dimension_next {G : Type*} [Group G] (n : ℕ)
    (x : dSubgro R G n) :
    x ∈ dNTerm R G n ↔
      (x : G) ∈ dSubgro R G (n + 1) :=
  DFilt.next_term_subgroup (dimensionFiltration R G) n x

instance dimension_next_normal {G : Type*} [Group G] (n : ℕ) :
    (dNTerm R G n).Normal :=
  DFilt.next_subgroup_normal (dimensionFiltration R G) n

/-- Concrete quotient description `Dₙ/Dₙ₊₁ ≃` the `n`th dimension layer kernel. -/
noncomputable def dLKern.nextQuotientEquiv {G : Type*} [Group G] (n : ℕ) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      dLKern R G n :=
  DFilt.layerNextEquiv (dimensionFiltration R G) n

/-- The zeroth consecutive dimension quotient is trivial. -/
theorem dNQuot.subsingleton_zero (G : Type*) [Group G] :
    Subsingleton (dSubgro R G 0 ⧸ dNTerm R G 0) := by
  refine ⟨fun x y => ?_⟩
  apply (dLKern.nextQuotientEquiv (R := R) (G := G) 0).injective
  haveI : Subsingleton (dLKern R G 0) :=
    dLKern.subsingleton_zero (R := R) G
  exact Subsingleton.elim _ _

/-- Every element of the zeroth consecutive dimension quotient is trivial. -/
theorem dNQuot.eq_one_zero {G : Type*} [Group G]
    (x : dSubgro R G 0 ⧸ dNTerm R G 0) : x = 1 := by
  haveI : Subsingleton (dSubgro R G 0 ⧸ dNTerm R G 0) :=
    dNQuot.subsingleton_zero (R := R) G
  exact Subsingleton.elim x 1

@[simp] theorem dLKern.next_quot_equivmk {G : Type*} [Group G] (n : ℕ)
    (x : dSubgro R G n) :
    dLKern.nextQuotientEquiv (R := R) n
        (QuotientGroup.mk' (dNTerm R G n) x) =
      dLKern.ofTerm (R := R) n x := rfl

/-- Characterize the inverse of the concrete dimension layer quotient equivalence. -/
theorem dLKern.nextquot_equivsymm_applyeq {G : Type*} [Group G]
    (n : ℕ) (y : dLKern R G n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dLKern.nextQuotientEquiv (R := R) (G := G) n).symm y = x ↔
      y = dLKern.nextQuotientEquiv (R := R) (G := G) n x := by
  rw [MulEquiv.symm_apply_eq]



/-- The map induced by a homomorphism on concrete consecutive dimension quotients. -/
noncomputable def dNQuot.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    (dSubgro R G n ⧸ dNTerm R G n) →*
      (dSubgro R H n ⧸ dNTerm R H n) :=
  DFilt.nextTermQuotient (dimensionFiltration_preserves R φ) n

/-- Maps into the zeroth consecutive dimension quotient are trivial. -/
theorem dNQuot.map_applyeq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (x : dSubgro R G 0 ⧸ dNTerm R G 0) :
    dNQuot.map (R := R) φ 0 x = 1 :=
  dNQuot.eq_one_zero (R := R) _

/-- At level zero, the induced map on consecutive dimension quotients is the trivial hom. -/
theorem dNQuot.map_eq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    dNQuot.map (R := R) φ 0 = 1 := by
  ext x
  exact dNQuot.map_applyeq_onezero (R := R) φ x

/-- The kernel of the level-zero consecutive quotient map is the whole source. -/
theorem dNQuot.ker_mapzero_eqtop {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    MonoidHom.ker (dNQuot.map (R := R) φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, dNQuot.map_applyeq_onezero (R := R) φ x]

/-- The range of the level-zero consecutive quotient map is the bottom subgroup. -/
theorem dNQuot.range_mapzero_eqbot {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    (dNQuot.map (R := R) φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [dNQuot.map_applyeq_onezero (R := R) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem dNQuot.map_mk {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dSubgro R G n) :
    dNQuot.map (R := R) φ n
        (QuotientGroup.mk' (dNTerm R G n) x) =
      QuotientGroup.mk' (dNTerm R H n)
        (dSubgro.termMap (R := R) φ n x) := rfl

@[simp] theorem dNQuot.mem_ker_mapmk {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dSubgro R G n) :
    QuotientGroup.mk' (dNTerm R G n) x ∈
        MonoidHom.ker (dNQuot.map (R := R) φ n) ↔
      φ (x : G) ∈ dSubgro R H (n + 1) :=
  DFilt.ker_next_mk
    (dimensionFiltration_preserves R φ) n x


/-- Kernel of a concrete consecutive dimension quotient map as a quotient of the
exact preimage subgroup inside the source term. -/
noncomputable def dNQuot.kernelEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    ((dNTerm R H n).comap (dSubgro.termMap (R := R) φ n)) ⧸
      ((dNTerm R G n).subgroupOf
        ((dNTerm R H n).comap (dSubgro.termMap (R := R) φ n))) ≃*
        MonoidHom.ker (dNQuot.map (R := R) φ n) :=
  DFilt.nextTermEquiv
    (dimensionFiltration_preserves R φ) n

@[simp] theorem dNQuot.map_id (G : Type*) [Group G] (n : ℕ) :
    dNQuot.map (R := R) (MonoidHom.id G) n =
      MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n) :=
  DFilt.next_term_id (dimensionFiltration R G) n

@[simp] theorem dNQuot.map_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dNQuot.map (R := R) (ψ.comp φ) n =
      (dNQuot.map (R := R) ψ n).comp
        (dNQuot.map (R := R) φ n) :=
  DFilt.next_quotient_comp
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R ψ) n

/-- A split epimorphism induces surjective maps on concrete consecutive dimension quotients. -/
theorem dNQuot.map_surj_rightinv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (dNQuot.map (R := R) φ n) :=
  DFilt.next_surjective_onto
    (DFilt.MapsOnto.of_rightInverse
      (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ) n

/-- Injectivity criterion for maps on concrete consecutive dimension quotients. -/
theorem dNQuot.map_inj_comaple {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {n : ℕ}
    (hpre : (dSubgro R H (n + 1)).comap φ ≤
      dSubgro R G (n + 1)) :
    Function.Injective (dNQuot.map (R := R) φ n) :=
  DFilt.next_injective_comap
    (dimensionFiltration_preserves R φ) hpre

/-- Exact injectivity criterion phrased inside the source and target terms. -/
theorem dNQuot.map_injiff_comaple {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {n : ℕ} :
    Function.Injective (dNQuot.map (R := R) φ n) ↔
      (dNTerm R H n).comap (dSubgro.termMap (R := R) φ n) ≤
        dNTerm R G n :=
  DFilt.next_term_comap
    (dimensionFiltration_preserves R φ)

/-- For a split epimorphism, injectivity on consecutive dimension quotients is
controlled by the kernel intersection with the current term. -/
theorem dNQuot.mapinj_iffinfker_lerightinv
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (dNQuot.map (R := R) φ n) ↔
      φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1) :=
  DFilt.next_inf_inverse
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ

/-- For a split epimorphism, bijectivity on consecutive dimension quotients is
controlled by the same kernel intersection. -/
theorem dNQuot.mapbij_iffinfker_lerightinv
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (dNQuot.map (R := R) φ n) ↔
      φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1) :=
  DFilt.next_bijective_inf
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ

/-- A termwise-onto injective map induces an equivalence on consecutive dimension quotients. -/
noncomputable def dNQuot.equiv_maps_ontoinj {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      (dSubgro R H n ⧸ dNTerm R H n) :=
  DFilt.nextOntoInjective honto hinj n

@[simp] theorem dNQuot.equiv_mapsonto_injapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equiv_maps_ontoinj (R := R) φ honto hinj n x =
      dNQuot.map (R := R) φ n x := rfl

@[simp] theorem dNQuot.equivmaps_ontoinj_monoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (dNQuot.equiv_maps_ontoinj (R := R) φ honto hinj n).toMonoidHom =
      dNQuot.map (R := R) φ n := rfl

theorem dNQuot.equivmaps_ontoinj_symmapplyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : dSubgro R H n ⧸ dNTerm R H n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equiv_maps_ontoinj (R := R) φ honto hinj n).symm y = x ↔
      y = dNQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of dimension filtrations whose kernel lies in the next
source term induces an equivalence on consecutive dimension quotients. -/
noncomputable def dNQuot.equiv_mapsonto_kerle {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      (dSubgro R H n ⧸ dNTerm R H n) :=
  DFilt.nextMapsKer honto n hker

@[simp] theorem dNQuot.equivmaps_ontoker_leapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equiv_mapsonto_kerle (R := R) φ honto n hker x =
      dNQuot.map (R := R) φ n x := rfl

@[simp] theorem dNQuot.equivmaps_ontoker_lemonoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    (dNQuot.equiv_mapsonto_kerle (R := R) φ honto n hker).toMonoidHom =
      dNQuot.map (R := R) φ n := rfl

/-- Inverse-characterization for consecutive dimension quotient equivalences from
termwise-onto maps with kernel in the next source term. -/
theorem dNQuot.equivmaps_ontokerle_symmapplyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1))
    (y : dSubgro R H n ⧸ dNTerm R H n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equiv_mapsonto_kerle (R := R) φ honto n hker).symm y = x ↔
      y = dNQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
consecutive dimension quotients. -/
noncomputable def dNQuot.equivmaps_ontoker_lele {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      (dSubgro R H n ⧸ dNTerm R H n) :=
  DFilt.nextOntoKer honto n hker hnk

@[simp] theorem dNQuot.equivmaps_ontoker_leleapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equivmaps_ontoker_lele (R := R) φ honto n hker hnk x =
      dNQuot.map (R := R) φ n x := rfl

@[simp] theorem dNQuot.equivmaps_ontokerle_lemonoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    (dNQuot.equivmaps_ontoker_lele (R := R) φ honto n hker hnk).toMonoidHom =
      dNQuot.map (R := R) φ n := rfl

theorem dNQuot.equivm_kerle_symma {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k)
    (y : dSubgro R H n ⧸ dNTerm R H n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equivmaps_ontoker_lele (R := R) φ honto n hker hnk).symm y = x ↔
      y = dNQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A split epimorphism induces an equivalence on consecutive dimension quotients
when its kernel meets `Dₙ` inside `Dₙ₊₁`. -/
noncomputable def dNQuot.rightInverseEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1)) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      (dSubgro R H n ⧸ dNTerm R H n) :=
  MulEquiv.ofBijective (dNQuot.map (R := R) φ n)
    ((dNQuot.mapbij_iffinfker_lerightinv
      (R := R) φ σ hσ).2 hker)

@[simp] theorem dNQuot.equiv_right_invapply {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1))
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.rightInverseEquiv (R := R) φ σ hσ hker x =
      dNQuot.map (R := R) φ n x := rfl

@[simp] theorem dNQuot.equiv_rightinv_monoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1)) :
    (dNQuot.rightInverseEquiv (R := R) φ σ hσ hker).toMonoidHom =
      dNQuot.map (R := R) φ n := rfl

/-- Inverse-characterization for the split-epi consecutive dimension quotient equivalence. -/
theorem dNQuot.equivright_invsymm_applyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1))
    (y : dSubgro R H n ⧸ dNTerm R H n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.rightInverseEquiv (R := R) φ σ hσ hker).symm y = x ↔
      y = dNQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A group equivalence restricts to an equivalence of dimension terms. -/
noncomputable def dSubgro.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    dSubgro R G n ≃* dSubgro R H n :=
{ toFun := dSubgro.termMap (R := R) e.toMonoidHom n
  invFun := dSubgro.termMap (R := R) e.symm.toMonoidHom n
  left_inv := by
    intro x
    ext
    change e.symm (e (x : G)) = (x : G)
    simp
  right_inv := by
    intro x
    ext
    change e (e.symm (x : H)) = (x : H)
    simp
  map_mul' := by
    intro x y
    exact map_mul (dSubgro.termMap (R := R) e.toMonoidHom n) x y }

@[simp] theorem dSubgro.congr_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dSubgro R G n) :
    dSubgro.congr (R := R) e n x =
      dSubgro.termMap (R := R) e.toMonoidHom n x := rfl


@[simp] theorem dSubgro.congr_apply_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dSubgro R G n) :
    ((dSubgro.congr (R := R) e n x : dSubgro R H n) : H) =
      e (x : G) := rfl

@[simp] theorem dSubgro.congr_monoid_hom {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dSubgro.congr (R := R) e n).toMonoidHom =
      dSubgro.termMap (R := R) e.toMonoidHom n := rfl

@[simp] theorem dSubgro.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dSubgro.congr (R := R) e n).symm =
      dSubgro.congr (R := R) e.symm n := by
  ext x
  rfl

/-- Inverse-application criterion for congruences of dimension terms. -/
theorem dSubgro.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (y : dSubgro R H n)
    (x : dSubgro R G n) :
    (dSubgro.congr (R := R) e n).symm y = x ↔
      y = dSubgro.congr (R := R) e n x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem dSubgro.congr_refl {G : Type*} [Group G] (n : ℕ) :
    dSubgro.congr (R := R) (MulEquiv.refl G) n =
      MulEquiv.refl (dSubgro R G n) := by
  ext x
  rfl

@[simp] theorem dSubgro.congr_trans {G H K : Type*} [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dSubgro.congr (R := R) e n).trans
        (dSubgro.congr (R := R) f n) =
      dSubgro.congr (R := R) (e.trans f) n := by
  ext x
  rfl

/-- A group equivalence induces an equivalence on concrete consecutive dimension quotients. -/
noncomputable def dNQuot.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dSubgro R G n ⧸ dNTerm R G n) ≃*
      (dSubgro R H n ⧸ dNTerm R H n) :=
{ toFun := dNQuot.map (R := R) e.toMonoidHom n
  invFun := dNQuot.map (R := R) e.symm.toMonoidHom n
  left_inv := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (dNTerm R G n)
        (dSubgro.termMap (R := R) e.symm.toMonoidHom n
          (dSubgro.termMap (R := R) e.toMonoidHom n x)) =
      QuotientGroup.mk' (dNTerm R G n) x
    congr 1
    ext
    simp
  right_inv := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (dNTerm R H n)
        (dSubgro.termMap (R := R) e.toMonoidHom n
          (dSubgro.termMap (R := R) e.symm.toMonoidHom n x)) =
      QuotientGroup.mk' (dNTerm R H n) x
    congr 1
    ext
    simp
  map_mul' := by
    intro a b
    exact map_mul (dNQuot.map (R := R) e.toMonoidHom n) a b }

@[simp] theorem dNQuot.congr_mk {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dSubgro R G n) :
    dNQuot.congr (R := R) e n
        (QuotientGroup.mk' (dNTerm R G n) x) =
      QuotientGroup.mk' (dNTerm R H n)
        (dSubgro.termMap (R := R) e.toMonoidHom n x) := rfl


@[simp] theorem dNQuot.congr_monoid_hom {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dNQuot.congr (R := R) e n).toMonoidHom =
      dNQuot.map (R := R) e.toMonoidHom n := rfl

@[simp] theorem dNQuot.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dNQuot.congr (R := R) e n).symm =
      dNQuot.congr (R := R) e.symm n := by
  ext q
  rfl

/-- Inverse-application criterion for congruences of consecutive dimension quotients. -/
theorem dNQuot.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ)
    (y : dSubgro R H n ⧸ dNTerm R H n)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.congr (R := R) e n).symm y = x ↔
      y = dNQuot.congr (R := R) e n x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem dNQuot.congr_refl (G : Type*) [Group G] (n : ℕ) :
    dNQuot.congr (R := R) (MulEquiv.refl G) n =
      MulEquiv.refl (dSubgro R G n ⧸ dNTerm R G n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dNQuot.congr_trans {G H K : Type*} [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dNQuot.congr (R := R) e n).trans
        (dNQuot.congr (R := R) f n) =
      dNQuot.congr (R := R) (e.trans f) n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Coordinate swap on consecutive dimension quotients. -/
noncomputable def dNQuot.prodCommEquiv (G H : Type*) [Group G] [Group H]
    (n : ℕ) :
    (dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) ≃*
      (dSubgro R (H × G) n ⧸ dNTerm R (H × G) n) :=
  dNQuot.congr (R := R)
    (MulEquiv.prodComm : G × H ≃* H × G) n

@[simp] theorem dNQuot.prod_commequiv_monoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom =
      dNQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := rfl

@[simp] theorem dNQuot.prod_comm_equivapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) G H n x =
      dNQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := by
  change ((dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dNQuot.prod_commequiv_monoidhom]

@[simp] theorem dNQuot.map_fstprod_commequiv
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.map (R := R) (MonoidHom.fst H G) n
        (dNQuot.prodCommEquiv (R := R) G H n x) =
      dNQuot.map (R := R) (MonoidHom.snd G H) n x := by
  change ((dNQuot.map (R := R) (MonoidHom.fst H G) n).comp
      (dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dNQuot.prod_commequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.fst H G) n]
  rfl

@[simp] theorem dNQuot.map_sndprod_commequiv
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.map (R := R) (MonoidHom.snd H G) n
        (dNQuot.prodCommEquiv (R := R) G H n x) =
      dNQuot.map (R := R) (MonoidHom.fst G H) n x := by
  change ((dNQuot.map (R := R) (MonoidHom.snd H G) n).comp
      (dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dNQuot.prod_commequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.snd H G) n]
  rfl

@[simp] theorem dNQuot.prod_commequiv_mapinl
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.prodCommEquiv (R := R) G H n
        (dNQuot.map (R := R) (MonoidHom.inl G H) n x) =
      dNQuot.map (R := R) (MonoidHom.inr H G) n x := by
  change ((dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom.comp
      (dNQuot.map (R := R) (MonoidHom.inl G H) n)) x = _
  rw [dNQuot.prod_commequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inl G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

@[simp] theorem dNQuot.prod_commequiv_mapinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.prodCommEquiv (R := R) G H n
        (dNQuot.map (R := R) (MonoidHom.inr G H) n x) =
      dNQuot.map (R := R) (MonoidHom.inl H G) n x := by
  change ((dNQuot.prodCommEquiv (R := R) G H n).toMonoidHom.comp
      (dNQuot.map (R := R) (MonoidHom.inr G H) n)) x = _
  rw [dNQuot.prod_commequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inr G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

@[simp] theorem dNQuot.prod_commequiv_symmeq
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.prodCommEquiv (R := R) G H n).symm =
      dNQuot.prodCommEquiv (R := R) H G n := by
  change (dNQuot.congr (R := R)
      (MulEquiv.prodComm : G × H ≃* H × G) n).symm =
    dNQuot.congr (R := R)
      (MulEquiv.prodComm : H × G ≃* G × H) n
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dNQuot.prod_commequiv_applyapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) H G n
      (dNQuot.prodCommEquiv (R := R) G H n x) = x := by
  rw [← dNQuot.prod_commequiv_symmeq (R := R) G H n]
  exact MulEquiv.symm_apply_apply
    (dNQuot.prodCommEquiv (R := R) G H n) x

/-- Reassociation on consecutive dimension quotients. -/
noncomputable def dNQuot.prodAssocEquiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dSubgro R ((G × H) × K) n ⧸
        dNTerm R ((G × H) × K) n) ≃*
      (dSubgro R (G × (H × K)) n ⧸
        dNTerm R (G × (H × K)) n) :=
  dNQuot.congr (R := R)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n

@[simp] theorem dNQuot.prod_assocequiv_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom =
      dNQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := rfl

@[simp] theorem dNQuot.prod_assocequiv_symmeq
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm =
      dNQuot.congr (R := R)
        (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm n := by
  change (dNQuot.congr (R := R)
      (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n).symm = _
  simp only [dNQuot.congr_symm]

/-- Automorphisms of `G` act on concrete consecutive dimension quotients. -/
noncomputable def dNQuot.mulAutMap (G : Type*) [Group G] (n : ℕ) :
    MulAut G →* MulAut (dSubgro R G n ⧸ dNTerm R G n) where
  toFun e := dNQuot.congr (R := R) e n
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl

@[simp] theorem dNQuot.mul_aut_mapapply {G : Type*} [Group G] {n : ℕ}
    (e : MulAut G) (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.mulAutMap (R := R) G n e x =
      dNQuot.congr (R := R) e n x := rfl


/-- Under the product equivalence on dimension terms, the next term is the product
of the next terms. -/
theorem dimension_next_term (G H : Type*) [Group G] [Group H]
    (n : ℕ) :
    (dNTerm R (G × H) n).map
      (dimensionSubgroupProd R G H n).toMonoidHom =
    (dNTerm R G n).prod (dNTerm R H n) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hxnext, rfl⟩
    rw [Subgroup.mem_prod]
    have hxnextG : (x : G × H) ∈ dSubgro R (G × H) (n + 1) :=
      (dimension_next (R := R) (G := G × H) n x).1 hxnext
    have hxprod : (x : G × H) ∈
        (dSubgro R G (n + 1)).prod (dSubgro R H (n + 1)) := by
      simpa [dimensionSubgroup_prod (R := R) G H (n + 1)] using hxnextG
    constructor
    · exact (dimension_next (R := R) (G := G) n _).2
        (Subgroup.mem_prod.mp hxprod).1
    · exact (dimension_next (R := R) (G := H) n _).2
        (Subgroup.mem_prod.mp hxprod).2
  · intro hy
    rcases y with ⟨yg, yh⟩
    rw [Subgroup.mem_prod] at hy
    rcases hy with ⟨hyg, hyh⟩
    refine ⟨(dimensionSubgroupProd R G H n).symm (yg, yh), ?_, ?_⟩
    · apply (dimension_next (R := R) (G := G × H) n _).2
      have hg : (yg : G) ∈ dSubgro R G (n + 1) :=
        (dimension_next (R := R) (G := G) n yg).1 hyg
      have hh : (yh : H) ∈ dSubgro R H (n + 1) :=
        (dimension_next (R := R) (G := H) n yh).1 hyh
      have hp : (((dimensionSubgroupProd R G H n).symm (yg, yh) :
          dSubgro R (G × H) n) : G × H) ∈
          (dSubgro R G (n + 1)).prod (dSubgro R H (n + 1)) := by
        rw [Subgroup.mem_prod]
        constructor
        · simpa using hg
        · simpa using hh
      simpa [dimensionSubgroup_prod (R := R) G H (n + 1)] using hp
    · simp

/-- Consecutive dimension quotients commute with binary products. -/
noncomputable def dNQuot.prodEquiv (G H : Type*) [Group G] [Group H]
    (n : ℕ) :
    (dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) ≃*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n)) :=
  (QuotientGroup.congr (dNTerm R (G × H) n)
    ((dNTerm R G n).prod (dNTerm R H n))
    (dimensionSubgroupProd R G H n)
    (dimension_next_term (R := R) G H n)).trans
    (Towers.quotientProdEquiv (dNTerm R G n)
      (dNTerm R H n))

@[simp] theorem dNQuot.prodEquiv_mk (G H : Type*) [Group G] [Group H]
    (n : ℕ) (x : dSubgro R (G × H) n) :
    dNQuot.prodEquiv (R := R) G H n
        (QuotientGroup.mk' (dNTerm R (G × H) n) x) =
      (QuotientGroup.mk' (dNTerm R G n)
          ((dimensionSubgroupProd R G H n x).1),
        QuotientGroup.mk' (dNTerm R H n)
          ((dimensionSubgroupProd R G H n x).2)) := rfl

@[simp] theorem dNQuot.prod_equiv_symmmk (G H : Type*) [Group G] [Group H]
    (n : ℕ) (x : dSubgro R G n) (y : dSubgro R H n) :
    (dNQuot.prodEquiv (R := R) G H n).symm
        (QuotientGroup.mk' (dNTerm R G n) x,
          QuotientGroup.mk' (dNTerm R H n) y) =
      QuotientGroup.mk' (dNTerm R (G × H) n)
        ((dimensionSubgroupProd R G H n).symm (x, y)) := by
  apply (dNQuot.prodEquiv (R := R) G H n).injective
  simp only [MulEquiv.apply_symm_apply]
  rw [dNQuot.prodEquiv_mk]
  rfl

/-- Cardinality formula for consecutive dimension quotients of products. -/
theorem dimension_next_prod (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card (dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) =
      Nat.card (dSubgro R G n ⧸ dNTerm R G n) *
        Nat.card (dSubgro R H n ⧸ dNTerm R H n) := by
  rw [Nat.card_congr (dNQuot.prodEquiv (R := R) G H n).toEquiv,
    Nat.card_prod]

/-- Dimension layer kernels commute with binary products. -/
noncomputable def dLKern.prodEquiv (G H : Type*) [Group G] [Group H]
    (n : ℕ) :
    dLKern R (G × H) n ≃*
      (dLKern R G n × dLKern R H n) :=
  (dLKern.nextQuotientEquiv (R := R) (G := G × H) n).symm.trans
    ((dNQuot.prodEquiv (R := R) G H n).trans
      (MulEquiv.prodCongr
        (dLKern.nextQuotientEquiv (R := R) (G := G) n)
        (dLKern.nextQuotientEquiv (R := R) (G := H) n)))


@[simp] theorem dLKern.prod_equiv_term (G H : Type*) [Group G] [Group H]
    (n : ℕ) (x : dSubgro R (G × H) n) :
    dLKern.prodEquiv (R := R) G H n
        (dLKern.ofTerm (R := R) n x) =
      (dLKern.ofTerm (R := R) n
          ((dimensionSubgroupProd R G H n x).1),
        dLKern.ofTerm (R := R) n
          ((dimensionSubgroupProd R G H n x).2)) := by
  let a := dLKern.nextQuotientEquiv (R := R) (G := G × H) n
  have ha : a.symm (dLKern.ofTerm (R := R) n x) =
      QuotientGroup.mk' (dNTerm R (G × H) n) x := by
    apply a.injective
    rw [MulEquiv.apply_symm_apply]
    change (dLKern.ofTerm (R := R) n x) =
      dLKern.nextQuotientEquiv (R := R) (G := G × H) n
        (QuotientGroup.mk' (dNTerm R (G × H) n) x)
    rw [dLKern.next_quot_equivmk]
  dsimp [dLKern.prodEquiv]
  change (MulEquiv.prodCongr _ _) ((dNQuot.prodEquiv (R := R) G H n)
      ((dLKern.nextQuotientEquiv (R := R) (G := G × H) n).symm
        (dLKern.ofTerm (R := R) n x))) = _
  rw [ha]
  rw [dNQuot.prodEquiv_mk]
  rfl

@[simp] theorem dLKern.prod_equiv_symmterm (G H : Type*) [Group G] [Group H]
    (n : ℕ) (x : dSubgro R G n) (y : dSubgro R H n) :
    (dLKern.prodEquiv (R := R) G H n).symm
        (dLKern.ofTerm (R := R) n x,
          dLKern.ofTerm (R := R) n y) =
      dLKern.ofTerm (R := R) n
        ((dimensionSubgroupProd R G H n).symm (x, y)) := by
  apply (dLKern.prodEquiv (R := R) G H n).injective
  simp only [MulEquiv.apply_symm_apply]
  rw [dLKern.prod_equiv_term]
  rfl

/-- Cardinality formula for dimension layer kernels of products. -/
theorem nat_dimension_prod (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card (dLKern R (G × H) n) =
      Nat.card (dLKern R G n) * Nat.card (dLKern R H n) := by
  rw [Nat.card_congr (dLKern.prodEquiv (R := R) G H n).toEquiv,
    Nat.card_prod]

/-- A homomorphism induces a map on dimension layer kernels. -/
noncomputable def dLKern.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    dLKern R G n →* dLKern R H n :=
  DFilt.layerMap (dimensionFiltration_preserves R φ) n

/-- Maps into the zeroth dimension layer kernel are trivial. -/
theorem dLKern.map_applyeq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (x : dLKern R G 0) :
    dLKern.map (R := R) φ 0 x = 1 :=
  dLKern.eq_one_zero (R := R) _

/-- At level zero, the induced map on dimension layer kernels is the trivial hom. -/
theorem dLKern.map_eq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    dLKern.map (R := R) φ 0 = 1 := by
  ext x
  exact congrArg (fun y : dLKern R H 0 =>
      (y : H ⧸ dSubgro R H (0 + 1)))
    (dLKern.map_applyeq_onezero (R := R) φ x)

/-- The kernel of the level-zero layer-kernel map is the whole source. -/
theorem dLKern.ker_mapzero_eqtop {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    MonoidHom.ker (dLKern.map (R := R) φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, dLKern.map_applyeq_onezero (R := R) φ x]

/-- The range of the level-zero layer-kernel map is the bottom subgroup. -/
theorem dLKern.range_mapzero_eqbot {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    (dLKern.map (R := R) φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [dLKern.map_applyeq_onezero (R := R) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem dLKern.map_coe {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dLKern R G n) :
    ((dLKern.map (R := R) φ n x : dLKern R H n) :
        H ⧸ dSubgro R H (n + 1)) =
      DFilt.quotientMap (dimensionFiltration_preserves R φ) (n + 1)
        (x : G ⧸ dSubgro R G (n + 1)) := rfl

/-- Naturality of the concrete quotient description of dimension layers. -/
theorem dLKern.next_quot_equivnatural {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ)
    (q : dSubgro R G n ⧸ dNTerm R G n) :
    dLKern.nextQuotientEquiv (R := R) (G := H) n
        (dNQuot.map (R := R) φ n q) =
      dLKern.map (R := R) φ n
        (dLKern.nextQuotientEquiv (R := R) (G := G) n q) :=
  DFilt.layer_next_naturality
    (dimensionFiltration_preserves R φ) n q

/-- Term-to-layer maps are natural for homomorphisms. -/
theorem dLKern.ofTerm_naturality {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    (dLKern.map (R := R) φ n).comp
        (dLKern.ofTerm (R := R) (G := G) n) =
      (dLKern.ofTerm (R := R) (G := H) n).comp
        (dSubgro.termMap (R := R) φ n) :=
  DFilt.layer_term_naturality (dimensionFiltration_preserves R φ) n

@[simp] theorem dLKern.mem_ker_mapterm {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dSubgro R G n) :
    dLKern.ofTerm (R := R) n x ∈
        MonoidHom.ker (dLKern.map (R := R) φ n) ↔
      φ (x : G) ∈ dSubgro R H (n + 1) :=
  DFilt.ker_layer_term (dimensionFiltration_preserves R φ) n x

@[simp] theorem dLKern.map_id (G : Type*) [Group G] (n : ℕ) :
    dLKern.map (R := R) (MonoidHom.id G) n =
      MonoidHom.id (dLKern R G n) :=
  DFilt.layerMap_id (dimensionFiltration R G) n

@[simp] theorem dLKern.map_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dLKern.map (R := R) (ψ.comp φ) n =
      (dLKern.map (R := R) ψ n).comp
        (dLKern.map (R := R) φ n) :=
  DFilt.layerMap_comp (dimensionFiltration_preserves R φ)
    (dimensionFiltration_preserves R ψ) n

/-- Additive version of the induced map on dimension layer kernels.  This is a
convenient interface once the layer is known to be abelian. -/
def dLKern.mapAdd {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    Additive (dLKern R G n) →+
      Additive (dLKern R H n) :=
  (dLKern.map (R := R) φ n).toAdditive

@[simp] theorem dLKern.map_add_mul {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (x : dLKern R G n) :
    dLKern.mapAdd (R := R) φ n (Additive.ofMul x) =
      Additive.ofMul (dLKern.map (R := R) φ n x) := rfl

@[simp] theorem dLKern.mapAdd_id (G : Type*) [Group G] (n : ℕ) :
    dLKern.mapAdd (R := R) (MonoidHom.id G) n =
      AddMonoidHom.id (Additive (dLKern R G n)) := by
  ext x
  rcases x with ⟨y⟩
  simp [dLKern.mapAdd]

@[simp] theorem dLKern.mapAdd_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dLKern.mapAdd (R := R) (ψ.comp φ) n =
      (dLKern.mapAdd (R := R) ψ n).comp
        (dLKern.mapAdd (R := R) φ n) := by
  ext x
  rcases x with ⟨y⟩
  simp [dLKern.mapAdd]

/-- A split epimorphism induces surjective maps on dimension layer kernels. -/
theorem dLKern.map_surj_rightinv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (dLKern.map (R := R) φ n) :=
  DFilt.layer_surjective_onto
    (DFilt.MapsOnto.of_rightInverse
      (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ) n

/-- For a split epimorphism, injectivity on dimension layer kernels is controlled
by the kernel intersection with the current term. -/
theorem dLKern.mapinj_iffinfker_lerightinv
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (dLKern.map (R := R) φ n) ↔
      φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1) :=
  DFilt.injective_inf_inverse
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ

/-- For a split epimorphism, bijectivity on dimension layer kernels is controlled
by the same kernel intersection. -/
theorem dLKern.mapbij_iffinfker_lerightinv
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (dLKern.map (R := R) φ n) ↔
      φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1) :=
  DFilt.bijective_inf_inverse
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ

/-- Termwise-onto maps induce surjections on consecutive dimension quotients. -/
theorem dNQuot.map_surj_mapsonto {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    Function.Surjective (dNQuot.map (R := R) φ n) := by
  simpa [dNQuot.map] using
    DFilt.next_surjective_onto honto n

/-- Range form of surjectivity on consecutive dimension quotients. -/
theorem dNQuot.maprange_eqtop_mapsonto {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    (dNQuot.map (R := R) φ n).range = ⊤ := by
  simpa [dNQuot.map] using
    DFilt.next_top_onto honto n

/-- Termwise-onto maps induce surjections on dimension layer kernels. -/
theorem dLKern.map_surj_mapsonto {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    Function.Surjective (dLKern.map (R := R) φ n) := by
  simpa [dLKern.map] using
    DFilt.layer_surjective_onto honto n

/-- Range form of surjectivity on dimension layer kernels. -/
theorem dLKern.maprange_eqtop_mapsonto {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    (dLKern.map (R := R) φ n).range = ⊤ := by
  simpa [dLKern.map] using
    DFilt.layer_top_onto honto n

/-- Bijectivity on consecutive dimension quotients from termwise-onto plus kernel
containment in the next source term. -/
theorem dNQuot.mapbij_mapsonto_kerle {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    Function.Bijective (dNQuot.map (R := R) φ n) := by
  simpa [dNQuot.map] using
    DFilt.next_bijective_maps honto hker

/-- Bijectivity on dimension layer kernels from termwise-onto plus kernel containment
in the next source term. -/
theorem dLKern.mapbij_mapsonto_kerle {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    Function.Bijective (dLKern.map (R := R) φ n) := by
  simpa [dLKern.map] using
    DFilt.layer_bijective_maps honto hker

/-- Deeper kernel containment gives bijectivity on earlier consecutive dimension quotients. -/
theorem dNQuot.mapbij_mapsonto_kerlele {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    Function.Bijective (dNQuot.map (R := R) φ n) := by
  simpa [dNQuot.map] using
    DFilt.next_bijective_ker
      honto n hker hnk

/-- Deeper kernel containment gives bijectivity on earlier dimension layer kernels. -/
theorem dLKern.mapbij_mapsonto_kerlele {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    Function.Bijective (dLKern.map (R := R) φ n) := by
  simpa [dLKern.map] using
    DFilt.layer_bijective_ker honto n hker hnk

/-- Termwise-onto injective maps give bijectivity on consecutive dimension quotients. -/
theorem dNQuot.map_bijmaps_ontoinj {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (dNQuot.map (R := R) φ n) := by
  simpa [dNQuot.map] using
    DFilt.next_bijective_injective honto hinj n

/-- Termwise-onto injective maps give bijectivity on dimension layer kernels. -/
theorem dLKern.map_bijmaps_ontoinj {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (dLKern.map (R := R) φ n) := by
  simpa [dLKern.map] using
    DFilt.layer_bijective_injective honto hinj n

/-- A termwise-onto injective map induces an equivalence on dimension layer kernels. -/
noncomputable def dLKern.equiv_maps_ontoinj {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    dLKern R G n ≃* dLKern R H n :=
  DFilt.layerOntoInjective honto hinj n

@[simp] theorem dLKern.equiv_mapsonto_injapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dLKern R G n) :
    dLKern.equiv_maps_ontoinj (R := R) φ honto hinj n x =
      dLKern.map (R := R) φ n x := rfl

@[simp] theorem dLKern.equivmaps_ontoinj_monoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (dLKern.equiv_maps_ontoinj (R := R) φ honto hinj n).toMonoidHom =
      dLKern.map (R := R) φ n := rfl

theorem dLKern.equivmaps_ontoinj_symmapplyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : dLKern R H n) (x : dLKern R G n) :
    (dLKern.equiv_maps_ontoinj (R := R) φ honto hinj n).symm y = x ↔
      y = dLKern.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of dimension filtrations whose kernel lies in the next
source term induces an equivalence on dimension layer kernels. -/
noncomputable def dLKern.equiv_mapsonto_kerle {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    dLKern R G n ≃* dLKern R H n :=
  DFilt.layerMapsKer honto n hker

@[simp] theorem dLKern.equivmaps_ontoker_leapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1)) (x : dLKern R G n) :
    dLKern.equiv_mapsonto_kerle (R := R) φ honto n hker x =
      dLKern.map (R := R) φ n x := rfl

@[simp] theorem dLKern.equivmaps_ontoker_lemonoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1)) :
    (dLKern.equiv_mapsonto_kerle (R := R) φ honto n hker).toMonoidHom =
      dLKern.map (R := R) φ n := rfl

/-- A split epimorphism induces an equivalence on dimension layer kernels under
the same kernel-intersection condition. -/
noncomputable def dLKern.rightInverseEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1)) :
    dLKern R G n ≃* dLKern R H n :=
  MulEquiv.ofBijective (dLKern.map (R := R) φ n)
    ((dLKern.mapbij_iffinfker_lerightinv
      (R := R) φ σ hσ).2 hker)

@[simp] theorem dLKern.equiv_right_invapply {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1))
    (x : dLKern R G n) :
    dLKern.rightInverseEquiv (R := R) φ σ hσ hker x =
      dLKern.map (R := R) φ n x := rfl

@[simp] theorem dLKern.equiv_rightinv_monoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1)) :
    (dLKern.rightInverseEquiv (R := R) φ σ hσ hker).toMonoidHom =
      dLKern.map (R := R) φ n := rfl

/-- Inverse-characterization for the split-epi dimension layer equivalence. -/
theorem dLKern.equivright_invsymm_applyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ dSubgro R G n ≤ dSubgro R G (n + 1))
    (y : dLKern R H n) (x : dLKern R G n) :
    (dLKern.rightInverseEquiv (R := R) φ σ hσ hker).symm y = x ↔
      y = dLKern.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the small-kernel dimension layer equivalence. -/
theorem dLKern.equivmaps_ontokerle_symmapplyeq {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ)
    (hker : φ.ker ≤ dSubgro R G (n + 1))
    (y : dLKern R H n) (x : dLKern R G n) :
    (dLKern.equiv_mapsonto_kerle (R := R) φ honto n hker).symm y = x ↔
      y = dLKern.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
dimension layer kernels. -/
noncomputable def dLKern.equivmaps_ontoker_lele {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    dLKern R G n ≃* dLKern R H n :=
  DFilt.layerOntoKer honto n hker hnk

@[simp] theorem dLKern.equivmaps_ontoker_leleapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k)
    (x : dLKern R G n) :
    dLKern.equivmaps_ontoker_lele (R := R) φ honto n hker hnk x =
      dLKern.map (R := R) φ n x := rfl

@[simp] theorem dLKern.equivmaps_ontokerle_lemonoidhom {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k) :
    (dLKern.equivmaps_ontoker_lele (R := R) φ honto n hker hnk).toMonoidHom =
      dLKern.map (R := R) φ n := rfl

theorem dLKern.equivm_kerle_symma {G H : Type*}
    [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n + 1 ≤ k)
    (y : dLKern R H n) (x : dLKern R G n) :
    (dLKern.equivmaps_ontoker_lele (R := R) φ honto n hker hnk).symm y = x ↔
      y = dLKern.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A group equivalence induces an equivalence on dimension layer kernels. -/
noncomputable def dLKern.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    dLKern R G n ≃* dLKern R H n :=
{ dLKern.map (R := R) e.toMonoidHom n with
  invFun := dLKern.map (R := R) e.symm.toMonoidHom n
  left_inv := by
    intro x
    have h := congrArg
      (fun f : dLKern R G n →* dLKern R G n => f x)
      (dLKern.map_comp (R := R) e.toMonoidHom e.symm.toMonoidHom n)
    change dLKern.map (R := R) (e.symm.toMonoidHom.comp e.toMonoidHom) n x = _ at h
    simpa using h.symm
  right_inv := by
    intro x
    have h := congrArg
      (fun f : dLKern R H n →* dLKern R H n => f x)
      (dLKern.map_comp (R := R) e.symm.toMonoidHom e.toMonoidHom n)
    change dLKern.map (R := R) (e.toMonoidHom.comp e.symm.toMonoidHom) n x = _ at h
    simpa using h.symm }

@[simp] theorem dLKern.congr_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dLKern R G n) :
    dLKern.congr (R := R) e n x =
      dLKern.map (R := R) e.toMonoidHom n x := rfl

@[simp] theorem dLKern.congr_monoid_hom {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dLKern.congr (R := R) e n).toMonoidHom =
      dLKern.map (R := R) e.toMonoidHom n := rfl

@[simp] theorem dLKern.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dLKern.congr (R := R) e n).symm =
      dLKern.congr (R := R) e.symm n := by
  ext x
  rfl

@[simp] theorem dLKern.congr_refl {G : Type*} [Group G] (n : ℕ) :
    dLKern.congr (R := R) (MulEquiv.refl G) n =
      MulEquiv.refl (dLKern R G n) := by
  ext x
  have h := congrArg (fun u : dLKern R G n →* dLKern R G n => u x)
    (dLKern.map_id (R := R) G n)
  exact congrArg (fun y : dLKern R G n =>
      (y : G ⧸ dSubgro R G (n + 1))) h

@[simp] theorem dLKern.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dLKern.congr (R := R) e n).trans
        (dLKern.congr (R := R) f n) =
      dLKern.congr (R := R) (e.trans f) n := by
  ext x
  have h := congrArg (fun u : dLKern R G n →* dLKern R K n => u x)
    (dLKern.map_comp (R := R) e.toMonoidHom f.toMonoidHom n)
  exact congrArg (fun y : dLKern R K n =>
      (y : K ⧸ dSubgro R K (n + 1))) h.symm

/-- Coordinate swap on dimension layer kernels. -/
noncomputable def dLKern.prodCommEquiv (G H : Type*) [Group G] [Group H]
    (n : ℕ) :
    dLKern R (G × H) n ≃* dLKern R (H × G) n :=
  dLKern.congr (R := R)
    (MulEquiv.prodComm : G × H ≃* H × G) n

@[simp] theorem dLKern.prod_commequiv_monoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prodCommEquiv (R := R) G H n).toMonoidHom =
      dLKern.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := rfl

@[simp] theorem dLKern.prod_comm_equivapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) G H n x =
      dLKern.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := by
  change ((dLKern.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dLKern.prod_commequiv_monoidhom]

@[simp] theorem dLKern.map_fstprod_commequiv
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.map (R := R) (MonoidHom.fst H G) n
        (dLKern.prodCommEquiv (R := R) G H n x) =
      dLKern.map (R := R) (MonoidHom.snd G H) n x := by
  change ((dLKern.map (R := R) (MonoidHom.fst H G) n).comp
      (dLKern.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dLKern.prod_commequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.fst H G) n]
  rfl

@[simp] theorem dLKern.map_sndprod_commequiv
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.map (R := R) (MonoidHom.snd H G) n
        (dLKern.prodCommEquiv (R := R) G H n x) =
      dLKern.map (R := R) (MonoidHom.fst G H) n x := by
  change ((dLKern.map (R := R) (MonoidHom.snd H G) n).comp
      (dLKern.prodCommEquiv (R := R) G H n).toMonoidHom) x = _
  rw [dLKern.prod_commequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.snd H G) n]
  rfl

@[simp] theorem dLKern.prod_commequiv_mapinl
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R G n) :
    dLKern.prodCommEquiv (R := R) G H n
        (dLKern.map (R := R) (MonoidHom.inl G H) n x) =
      dLKern.map (R := R) (MonoidHom.inr H G) n x := by
  change ((dLKern.prodCommEquiv (R := R) G H n).toMonoidHom.comp
      (dLKern.map (R := R) (MonoidHom.inl G H) n)) x = _
  rw [dLKern.prod_commequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inl G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

@[simp] theorem dLKern.prod_commequiv_mapinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R H n) :
    dLKern.prodCommEquiv (R := R) G H n
        (dLKern.map (R := R) (MonoidHom.inr G H) n x) =
      dLKern.map (R := R) (MonoidHom.inl H G) n x := by
  change ((dLKern.prodCommEquiv (R := R) G H n).toMonoidHom.comp
      (dLKern.map (R := R) (MonoidHom.inr G H) n)) x = _
  rw [dLKern.prod_commequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inr G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

@[simp] theorem dLKern.prod_commequiv_symmeq
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prodCommEquiv (R := R) G H n).symm =
      dLKern.prodCommEquiv (R := R) H G n := by
  change (dLKern.congr (R := R)
      (MulEquiv.prodComm : G × H ≃* H × G) n).symm =
    dLKern.congr (R := R)
      (MulEquiv.prodComm : H × G ≃* G × H) n
  ext x
  rfl

@[simp] theorem dLKern.prod_commequiv_applyapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) H G n
      (dLKern.prodCommEquiv (R := R) G H n x) = x := by
  rw [← dLKern.prod_commequiv_symmeq (R := R) G H n]
  exact MulEquiv.symm_apply_apply
    (dLKern.prodCommEquiv (R := R) G H n) x

/-- Reassociation on dimension layer kernels. -/
noncomputable def dLKern.prodAssocEquiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern R ((G × H) × K) n ≃*
      dLKern R (G × (H × K)) n :=
  dLKern.congr (R := R)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n

@[simp] theorem dLKern.prod_assocequiv_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom =
      dLKern.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := rfl

@[simp] theorem dLKern.prod_assocequiv_symmeq
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm =
      dLKern.congr (R := R)
        (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm n := by
  change (dLKern.congr (R := R)
      (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n).symm = _
  simp only [dLKern.congr_symm]

@[simp] theorem dLKern.congr_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dLKern R G n) :
    ((dLKern.congr (R := R) e n x : dLKern R H n) :
        H ⧸ dSubgro R H (n + 1)) =
      DFilt.quotientMap (dimensionFiltration_preserves R e.toMonoidHom) (n + 1)
        (x : G ⧸ dSubgro R G (n + 1)) := by
  rw [dLKern.congr_apply, dLKern.map_coe]

/-- Inverse-application criterion for the layer-kernel congruence induced by an equivalence. -/
theorem dLKern.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (y : dLKern R H n)
    (x : dLKern R G n) :
    (dLKern.congr (R := R) e n).symm y = x ↔
      y = dLKern.congr (R := R) e n x := by
  rw [MulEquiv.symm_apply_eq]

/-- The concrete consecutive-quotient equivalence is compatible with group equivalences. -/
theorem dLKern.next_quot_equivcongr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ)
    (q : dSubgro R G n ⧸ dNTerm R G n) :
    dLKern.nextQuotientEquiv (R := R) (G := H) n
        (dNQuot.congr (R := R) e n q) =
      dLKern.congr (R := R) e n
        (dLKern.nextQuotientEquiv (R := R) (G := G) n q) :=
  dLKern.next_quot_equivnatural (R := R) e.toMonoidHom n q

/-- The concrete `Dₙ/Dₙ₊₁` equivalence intertwines coordinate swaps. -/
@[simp] theorem dLKern.next_quotequiv_prodcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (q : dSubgro R (G × H) n ⧸
      dNTerm R (G × H) n) :
    dLKern.nextQuotientEquiv (R := R) (G := H × G) n
        (dNQuot.prodCommEquiv (R := R) G H n q) =
      dLKern.prodCommEquiv (R := R) G H n
        (dLKern.nextQuotientEquiv (R := R) (G := G × H) n q) := by
  exact dLKern.next_quot_equivcongr (R := R)
    (MulEquiv.prodComm : G × H ≃* H × G) n q

/-- The concrete `Dₙ/Dₙ₊₁` equivalence intertwines reassociation. -/
@[simp] theorem dLKern.next_quotequiv_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (q : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dLKern.nextQuotientEquiv (R := R) (G := G × (H × K)) n
        (dNQuot.prodAssocEquiv (R := R) G H K n q) =
      dLKern.prodAssocEquiv (R := R) G H K n
        (dLKern.nextQuotientEquiv (R := R)
          (G := (G × H) × K) n q) := by
  exact dLKern.next_quot_equivcongr (R := R)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n q

/-- Automorphisms of `G` act on each dimension layer kernel. -/
noncomputable def dLKern.mulAutMap (G : Type*) [Group G] (n : ℕ) :
    MulAut G →* MulAut (dLKern R G n) where
  toFun e := dLKern.congr (R := R) e n
  map_one' := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl
  map_mul' e f := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl

@[simp] theorem dLKern.mul_aut_mapapply {G : Type*} [Group G] {n : ℕ}
    (e : MulAut G) (x : dLKern R G n) :
    dLKern.mulAutMap (R := R) G n e x =
      dLKern.congr (R := R) e n x := rfl

/-- Representative membership criterion for dimension layer kernels. -/
@[simp] theorem dimension_layer_mk {G : Type*} [Group G] (n : ℕ) (g : G) :
    QuotientGroup.mk' (dSubgro R G (n + 1)) g ∈
      dLKern R G n ↔
    g ∈ dSubgro R G n :=
  DFilt.layer_kernel_mk (dimensionFiltration R G) n g

/-- The zero-index dimension layer kernel is the whole (trivial) quotient. -/
@[simp] theorem dimension_layer_top {G : Type*} [Group G] :
    dLKern R G 0 = ⊤ := by
  ext q
  simp only [Subgroup.mem_top, iff_true]
  refine QuotientGroup.induction_on q ?_
  intro g
  exact (dimension_layer_mk (R := R) (G := G) 0 g).2 (by
    simp [dimension_subgroup_top])

/-- The first dimension layer kernel is the whole quotient, since `D₁ = G`. -/
@[simp] theorem dimension_kernel_top {G : Type*} [Group G] :
    dLKern R G 1 = ⊤ := by
  ext q
  simp only [Subgroup.mem_top, iff_true]
  refine QuotientGroup.induction_on q ?_
  intro g
  exact (dimension_layer_mk (R := R) (G := G) 1 g).2 (by
    simp [dimension_one_top])

/-- The first dimension layer kernel is multiplicatively equivalent to the ambient
quotient `G/D₂` (because `D₁ = G`). -/
def dimensionLayerEquiv {G : Type*} [Group G] :
    dLKern R G 1 ≃* (G ⧸ dSubgro R G 2) where
  toFun x := x.1
  invFun q := ⟨q, by rw [dimension_kernel_top]; trivial⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_mul' := by intro x y; rfl

@[simp] theorem dimension_layer_equiv {G : Type*} [Group G]
    (x : dLKern R G 1) :
    dimensionLayerEquiv (R := R) x = x.1 := rfl

@[simp] theorem dimension_mul_symm {G : Type*} [Group G]
    (q : G ⧸ dSubgro R G 2) :
    (dimensionLayerEquiv (R := R) (G := G)).symm q =
      ⟨q, by rw [dimension_kernel_top]; trivial⟩ := rfl


/-- Positive dimension layers are abelian: commutators vanish in the next quotient. -/
theorem dimension_commutator_one {G : Type*} [Group G] {n : ℕ}
    (hn : 1 ≤ n) {q r : G ⧸ dSubgro R G (n + 1)}
    (hq : q ∈ dLKern R G n) (hr : r ∈ dLKern R G n) :
    ⁅q, r⁆ = 1 := by
  refine QuotientGroup.induction_on q ?_ hq
  intro g hqg
  refine QuotientGroup.induction_on r ?_ hr
  intro h hrh
  have hg : g ∈ dSubgro R G n :=
    (dimension_layer_mk (R := R) (G := G) n g).1 hqg
  have hh : h ∈ dSubgro R G n :=
    (dimension_layer_mk (R := R) (G := G) n h).1 hrh
  change QuotientGroup.mk' (dSubgro R G (n + 1)) ⁅g, h⁆ = 1
  apply (QuotientGroup.eq_one_iff ⁅g, h⁆).mpr
  have hc : ⁅g, h⁆ ∈ dSubgro R G (n + n) :=
    commutator_dimension_add R G (by omega) (by omega) hg hh
  exact dimensionSubgroup_antitone R G (by omega : n + 1 ≤ n + n) hc

/-- Elements of a positive dimension layer commute in the truncated quotient. -/
theorem dimension_layer_comm {G : Type*} [Group G] {n : ℕ} (hn : 1 ≤ n)
    {q r : G ⧸ dSubgro R G (n + 1)}
    (hq : q ∈ dLKern R G n) (hr : r ∈ dLKern R G n) :
    q * r = r * q :=
  (commutatorElement_eq_one_iff_mul_comm).1
    (dimension_commutator_one (R := R) hn hq hr)

/-- Dimension layer elements commute for every index (the zero case is trivial). -/
theorem dimension_comm_any {G : Type*} [Group G] {n : ℕ}
    {q r : G ⧸ dSubgro R G (n + 1)}
    (hq : q ∈ dLKern R G n) (hr : r ∈ dLKern R G n) :
    q * r = r * q := by
  cases n with
  | zero =>
      refine QuotientGroup.induction_on q ?_ hq
      intro g _
      refine QuotientGroup.induction_on r ?_ hr
      intro h _
      change QuotientGroup.mk' (dSubgro R G 1) (g * h) =
        QuotientGroup.mk' (dSubgro R G 1) (h * g)
      have hl : QuotientGroup.mk' (dSubgro R G 1) (g * h) = 1 := by
        apply (QuotientGroup.eq_one_iff (g * h)).mpr
        simp [dimension_one_top]
      have hr' : QuotientGroup.mk' (dSubgro R G 1) (h * g) = 1 := by
        apply (QuotientGroup.eq_one_iff (h * g)).mpr
        simp [dimension_one_top]
      exact hl.trans hr'.symm
  | succ k =>
      exact dimension_layer_comm (R := R) (G := G) (Nat.succ_pos k) hq hr

/-- Each dimension layer kernel is a commutative group. -/
instance instCommDimension {G : Type*} [Group G] (n : ℕ) :
    CommGroup (dLKern R G n) := by
  let base : Group (dLKern R G n) := inferInstance
  refine { base with mul_comm := ?_ }
  intro a b
  ext
  exact dimension_comm_any (R := R) a.property b.property

/-- The additive incarnation of a dimension layer is canonically a `ℤ`-module,
and induced maps are integer-linear. -/
noncomputable def dLKern.mapIntLinear {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    Additive (dLKern R G n) →ₗ[ℤ]
      Additive (dLKern R H n) :=
  (dLKern.mapAdd (R := R) φ n).toIntLinearMap

@[simp] theorem dLKern.map_int_linapply {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ)
    (x : Additive (dLKern R G n)) :
    dLKern.mapIntLinear (R := R) φ n x =
      dLKern.mapAdd (R := R) φ n x := rfl

@[simp] theorem dLKern.map_int_linid {G : Type*} [Group G] (n : ℕ) :
    dLKern.mapIntLinear (R := R) (MonoidHom.id G) n = LinearMap.id := by
  ext x
  rcases x with ⟨y⟩
  simp [dLKern.mapIntLinear]

@[simp] theorem dLKern.map_int_lincomp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dLKern.mapIntLinear (R := R) (ψ.comp φ) n =
      (dLKern.mapIntLinear (R := R) ψ n).comp
        (dLKern.mapIntLinear (R := R) φ n) := by
  ext x
  rcases x with ⟨y⟩
  simp [dLKern.mapIntLinear]

/-- Additive equivalence on dimension layers induced by a group equivalence. -/
def dLKern.congrAdd {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    Additive (dLKern R G n) ≃+
      Additive (dLKern R H n) :=
  MulEquiv.toAdditive (dLKern.congr (R := R) e n)

@[simp] theorem dLKern.congr_add_mul {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dLKern R G n) :
    dLKern.congrAdd (R := R) e n (Additive.ofMul x) =
      Additive.ofMul (dLKern.congr (R := R) e n x) := rfl

/-- Integer-linear equivalence on dimension layers induced by a group equivalence. -/
noncomputable def dLKern.congrIntLinear {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    Additive (dLKern R G n) ≃ₗ[ℤ]
      Additive (dLKern R H n) :=
  LinearEquiv.ofBijective
    ((dLKern.congrAdd (R := R) e n).toAddMonoidHom.toIntLinearMap) <| by
      constructor
      · intro x y h
        exact (dLKern.congrAdd (R := R) e n).injective h
      · intro y
        rcases (dLKern.congrAdd (R := R) e n).surjective y with ⟨x, hx⟩
        exact ⟨x, hx⟩

@[simp] theorem dLKern.congr_int_linapply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) e n x =
      dLKern.congrAdd (R := R) e n x := rfl

/-- Automorphisms of `G` act integer-linearly on each additive dimension layer. -/
noncomputable def dLKern.linearAutMap (G : Type*) [Group G] (n : ℕ) :
    MulAut G →* (Additive (dLKern R G n) ≃ₗ[ℤ]
      Additive (dLKern R G n)) where
  toFun e := dLKern.congrIntLinear (R := R) e n
  map_one' := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl
  map_mul' e f := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl


/-- The quotient of a group by its `n`th dimension subgroup. -/
abbrev dQuot (G : Type*) [Group G] (n : ℕ) : Type _ :=
  G ⧸ dSubgro R G n

/-- The zeroth dimension quotient is trivial. -/
theorem dQuot.subsingleton_zero (G : Type*) [Group G] :
    Subsingleton (dQuot R G 0) := by
  change Subsingleton (G ⧸ dSubgro R G 0)
  rw [dimension_subgroup_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- The first dimension quotient is trivial (with the present indexing convention). -/
theorem dQuot.subsingleton_one (G : Type*) [Group G] :
    Subsingleton (dQuot R G 1) := by
  change Subsingleton (G ⧸ dSubgro R G 1)
  rw [dimension_one_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- Every element of the zeroth dimension quotient is trivial. -/
theorem dQuot.eq_one_zero {G : Type*} [Group G]
    (x : dQuot R G 0) : x = 1 := by
  haveI : Subsingleton (dQuot R G 0) :=
    dQuot.subsingleton_zero (R := R) G
  exact Subsingleton.elim x 1

/-- Every element of the first dimension quotient is trivial. -/
theorem dQuot.eq_one_one {G : Type*} [Group G]
    (x : dQuot R G 1) : x = 1 := by
  haveI : Subsingleton (dQuot R G 1) :=
    dQuot.subsingleton_one (R := R) G
  exact Subsingleton.elim x 1

/-- The map induced by a homomorphism on dimension quotients. -/
noncomputable def dQuot.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) :
    dQuot R G n →* dQuot R H n :=
  DFilt.quotientMap (dimensionFiltration_preserves R φ) n

/-- Maps into the zeroth dimension quotient are the trivial map. -/
theorem dQuot.map_applyeq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (x : dQuot R G 0) :
    dQuot.map (R := R) φ 0 x = 1 :=
  dQuot.eq_one_zero (R := R) _

/-- At level zero, the induced map on dimension quotients is the trivial hom. -/
theorem dQuot.map_eq_onezero {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    dQuot.map (R := R) φ 0 = 1 := by
  ext x
  exact dQuot.map_applyeq_onezero (R := R) φ x

/-- The kernel of the level-zero dimension quotient map is the whole source. -/
theorem dQuot.ker_mapzero_eqtop {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    MonoidHom.ker (dQuot.map (R := R) φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, dQuot.map_applyeq_onezero (R := R) φ x]

/-- The range of the level-zero dimension quotient map is the bottom subgroup. -/
theorem dQuot.range_mapzero_eqbot {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    (dQuot.map (R := R) φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [dQuot.map_applyeq_onezero (R := R) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

/-- Maps into the first dimension quotient are the trivial map. -/
theorem dQuot.map_applyeq_oneone {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (x : dQuot R G 1) :
    dQuot.map (R := R) φ 1 x = 1 :=
  dQuot.eq_one_one (R := R) _

/-- At level one, the induced map on dimension quotients is the trivial hom. -/
theorem dQuot.map_eq_oneone {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    dQuot.map (R := R) φ 1 = 1 := by
  ext x
  exact dQuot.map_applyeq_oneone (R := R) φ x

/-- The kernel of the level-one dimension quotient map is the whole source. -/
theorem dQuot.ker_mapone_eqtop {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    MonoidHom.ker (dQuot.map (R := R) φ 1) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, dQuot.map_applyeq_oneone (R := R) φ x]

/-- The range of the level-one dimension quotient map is the bottom subgroup. -/
theorem dQuot.range_mapone_eqbot {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    (dQuot.map (R := R) φ 1).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [dQuot.map_applyeq_oneone (R := R) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem dQuot.map_mk {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (n : ℕ) (g : G) :
    dQuot.map (R := R) φ n
        (QuotientGroup.mk' (dSubgro R G n) g) =
      QuotientGroup.mk' (dSubgro R H n) (φ g) := rfl

@[simp] theorem dQuot.map_id (G : Type*) [Group G] (n : ℕ) :
    dQuot.map (R := R) (MonoidHom.id G) n = MonoidHom.id (dQuot R G n) := by
  ext g
  rfl

@[simp] theorem dQuot.map_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    dQuot.map (R := R) (ψ.comp φ) n =
      (dQuot.map (R := R) ψ n).comp (dQuot.map (R := R) φ n) := by
  ext g
  rfl

/-- Transition map between dimension quotients for `m ≤ n` (so `D_n ≤ D_m`). -/
noncomputable def mapOfLe {G : Type*} [Group G] {m n : ℕ}
    (hmn : m ≤ n) :
    dQuot R G n →* dQuot R G m := by
  refine QuotientGroup.lift (dSubgro R G n)
    (QuotientGroup.mk' (dSubgro R G m)) ?_
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mpr
    (dimensionSubgroup_antitone R G hmn hx)

@[simp] theorem dimension_mk {G : Type*} [Group G] {m n : ℕ}
    (hmn : m ≤ n) (g : G) :
    mapOfLe (R := R) (G := G) hmn
        (QuotientGroup.mk' (dSubgro R G n) g) =
      QuotientGroup.mk' (dSubgro R G m) g := rfl

/-- The concrete dimension transition map is the generic filtration transition map. -/
theorem dimension_quotient_transition {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    mapOfLe (R := R) (G := G) hmn =
      DFilt.quotientTransition (dimensionFiltration R G) hmn := by
  ext g
  rfl

/-- Representative criterion for the kernel of an arbitrary dimension quotient transition. -/
@[simp] theorem dimension_quotient_mk {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (g : G) :
    QuotientGroup.mk' (dSubgro R G n) g ∈
        MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ↔
      g ∈ dSubgro R G m := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff g

/-- Kernel of an arbitrary dimension quotient transition as the image of the target term. -/
theorem dimension_ker {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) =
      (dSubgro R G m).map (QuotientGroup.mk' (dSubgro R G n)) := by
  rw [dimension_quotient_transition]
  exact DFilt.ker_quotient_transition (dimensionFiltration R G) hmn

/-- Dimension quotient transition maps are surjective. -/
theorem dimension_quotient_surjective {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (mapOfLe (R := R) (G := G) hmn) := by
  rw [dimension_quotient_transition]
  exact DFilt.quotientTransition_surjective (dimensionFiltration R G) hmn

/-- The deeper dimension subgroup, viewed as a subgroup of the shallower one. -/
abbrev dTSubgro {G : Type*} [Group G] {m n : ℕ} (hmn : m ≤ n) :
    Subgroup (dSubgro R G m) :=
  DFilt.tSOf (dimensionFiltration R G) hmn

instance dimension_term_normal {G : Type*} [Group G] {m n : ℕ}
    (hmn : m ≤ n) : (dTSubgro (R := R) (G := G) hmn).Normal :=
  DFilt.term_subgroup_normal (dimensionFiltration R G) hmn

@[simp] theorem dimension_subgroup {G : Type*} [Group G] {m n : ℕ}
    (hmn : m ≤ n) (x : dSubgro R G m) :
    x ∈ dTSubgro (R := R) (G := G) hmn ↔
      (x : G) ∈ dSubgro R G n := by
  exact DFilt.mem_term_of (dimensionFiltration R G) hmn x

/-- First-isomorphism-theorem form of an arbitrary dimension-quotient transition kernel. -/
noncomputable def dimensionTransitionEquiv {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) := by
  rw [dimension_quotient_transition]
  exact DFilt.transitionKernelEquiv (dimensionFiltration R G) hmn

@[simp] theorem dimension_mk_coe {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (x : dSubgro R G m) :
    ((dimensionTransitionEquiv (R := R) (G := G) hmn
        (QuotientGroup.mk' (dTSubgro (R := R) (G := G) hmn) x) :
        MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
        dQuot R G n) =
      QuotientGroup.mk' (dSubgro R G n) (x : G) := by
  simpa [dimensionTransitionEquiv,
    dimension_quotient_transition]
    using DFilt.transition_kernel_coe
      (dimensionFiltration R G) hmn x

/-- Characterize the inverse of the arbitrary dimension transition-kernel equivalence. -/
theorem dimension_transition_quotient
    {G : Type*} [Group G] {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn))
    (x : dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) :
    (dimensionTransitionEquiv (R := R) (G := G) hmn).symm y = x ↔
      y = dimensionTransitionEquiv (R := R) (G := G) hmn x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem dimension_symm_mk {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (g : G) (hg : g ∈ dSubgro R G m) :
    (dimensionTransitionEquiv (R := R) (G := G) hmn).symm
        ⟨QuotientGroup.mk' (dSubgro R G n) g, by
          rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff g).2 hg⟩ =
      QuotientGroup.mk' (dTSubgro (R := R) (G := G) hmn)
        (⟨g, hg⟩ : dSubgro R G m) := by
  simpa [dimensionTransitionEquiv,
    dimension_quotient_transition]
    using DFilt.transition_kernel_mk
      (dimensionFiltration R G) hmn g hg

/-- A homomorphism induces maps on arbitrary concrete dimension-term quotients. -/
noncomputable def dimensionTerm {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) →*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :=
  DFilt.termQuotient (dimensionFiltration_preserves R φ) hmn

@[simp] theorem dimension_term_mk {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) (x : dSubgro R G m) :
    dimensionTerm (R := R) φ hmn
        (QuotientGroup.mk' (dTSubgro (R := R) (G := G) hmn) x) =
      QuotientGroup.mk' (dTSubgro (R := R) (G := H) hmn)
        (DFilt.termMap (dimensionFiltration_preserves R φ) m x) := rfl

@[simp] theorem dimension_quotient_id {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionTerm (R := R) (MonoidHom.id G) hmn =
      MonoidHom.id
        (dSubgro R G m ⧸
          dTSubgro (R := R) (G := G) hmn) := by
  ext x
  rfl

@[simp] theorem dimension_comp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionTerm (R := R) (ψ.comp φ) hmn =
      (dimensionTerm (R := R) ψ hmn).comp
        (dimensionTerm (R := R) φ hmn) := by
  ext x
  rfl

/-- A group isomorphism induces an isomorphism on arbitrary dimension-term quotients. -/
noncomputable def dTQuot.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) where
  toFun := dimensionTerm (R := R) e.toMonoidHom hmn
  invFun := dimensionTerm (R := R) e.symm.toMonoidHom hmn
  left_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change dimensionTerm (R := R) e.symm.toMonoidHom hmn
        (dimensionTerm (R := R) e.toMonoidHom hmn
          (QuotientGroup.mk' (dTSubgro (R := R) (G := G) hmn) x)) = _
    rw [← MonoidHom.comp_apply]
    rw [← dimension_comp (R := R) e.toMonoidHom e.symm.toMonoidHom hmn]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    rw [he]
    simp
  right_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change dimensionTerm (R := R) e.toMonoidHom hmn
        (dimensionTerm (R := R) e.symm.toMonoidHom hmn
          (QuotientGroup.mk' (dTSubgro (R := R) (G := H) hmn) x)) = _
    rw [← MonoidHom.comp_apply]
    rw [← dimension_comp (R := R) e.symm.toMonoidHom e.toMonoidHom hmn]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext h
      simp
    rw [he]
    simp
  map_mul' x y := map_mul _ x y

@[simp] theorem dTQuot.congr_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) (q) :
    dTQuot.congr (R := R) e hmn q =
      dimensionTerm (R := R) e.toMonoidHom hmn q := rfl

@[simp] theorem dTQuot.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) e hmn).symm =
      dTQuot.congr (R := R) e.symm hmn := by
  ext q
  rfl

/-- Inverse-application criterion for congruences of dimension term quotients. -/
theorem dTQuot.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dTQuot.congr (R := R) e hmn).symm y = x ↔
      y = dTQuot.congr (R := R) e hmn x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem dTQuot.congr_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTQuot.congr (R := R) (MulEquiv.refl G) hmn =
      MulEquiv.refl (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dTQuot.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K)
    {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) e hmn).trans
        (dTQuot.congr (R := R) f hmn) =
      dTQuot.congr (R := R) (e.trans f) hmn := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dTQuot.congr_mk {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) (x : dSubgro R G m) :
    dTQuot.congr (R := R) e hmn
        (QuotientGroup.mk' (dTSubgro (R := R) (G := G) hmn) x) =
      QuotientGroup.mk' (dTSubgro (R := R) (G := H) hmn)
        (DFilt.termMap (dimensionFiltration_preserves R e.toMonoidHom) m x) := rfl

/-- Automorphisms act on arbitrary dimension-term quotients. -/
noncomputable def dTQuot.mulAutMap (G : Type*) [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut
      (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) where
  toFun e := dTQuot.congr (R := R) e hmn
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl

@[simp] theorem dTQuot.mul_aut_mapapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) (q) :
    dTQuot.mulAutMap (R := R) G hmn e q =
      dTQuot.congr (R := R) e hmn q := rfl

/-- A homomorphism induces maps on kernels of arbitrary dimension quotient transitions. -/
noncomputable def dimensionTransition {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) →*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) where
  toFun y :=
    ⟨dQuot.map (R := R) φ n (y : dQuot R G n), by
      rw [MonoidHom.mem_ker]
      have hy : mapOfLe (R := R) (G := G) hmn
          (y : dQuot R G n) = 1 := (MonoidHom.mem_ker).1 y.property
      have hnat := congrArg
        (fun f : (dQuot R G n) →* (dQuot R H m) =>
          f (y : dQuot R G n))
        (DFilt.quotientTransition_naturality
          (dimensionFiltration_preserves R φ) hmn)
      calc
        mapOfLe (R := R) (G := H) hmn
            (dQuot.map (R := R) φ n (y : dQuot R G n)) =
            dQuot.map (R := R) φ m
              (mapOfLe (R := R) (G := G) hmn
                (y : dQuot R G n)) := by
          simpa [MonoidHom.comp_apply, dQuot.map,
            dimension_quotient_transition] using hnat
        _ = dQuot.map (R := R) φ m 1 := by rw [hy]
        _ = 1 := map_one _⟩
  map_one' := by
    ext
    simp [dQuot.map]
  map_mul' x y := by
    ext
    simp [dQuot.map]

@[simp] theorem dimension_transition_coe {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    ((dimensionTransition (R := R) φ hmn y :
        MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
        dQuot R H n) =
      dQuot.map (R := R) φ n (y : dQuot R G n) := rfl

@[simp] theorem dimension_kernel_id {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionTransition (R := R) (MonoidHom.id G) hmn =
      MonoidHom.id (MonoidHom.ker
        (mapOfLe (R := R) (G := G) hmn)) := by
  ext y
  simp

@[simp] theorem dimension_transition {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionTransition (R := R) (ψ.comp φ) hmn =
      (dimensionTransition (R := R) ψ hmn).comp
        (dimensionTransition (R := R) φ hmn) := by
  ext y
  simp [dQuot.map_comp]

/-- A group isomorphism induces an isomorphism on arbitrary dimension transition kernels. -/
noncomputable def dTKern.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) where
  toFun := dimensionTransition (R := R) e.toMonoidHom hmn
  invFun := dimensionTransition (R := R) e.symm.toMonoidHom hmn
  left_inv y := by
    rw [← MonoidHom.comp_apply]
    rw [← dimension_transition (R := R) e.toMonoidHom e.symm.toMonoidHom hmn]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext g; simp
    rw [he]
    simp
  right_inv y := by
    rw [← MonoidHom.comp_apply]
    rw [← dimension_transition (R := R) e.symm.toMonoidHom e.toMonoidHom hmn]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext h; simp
    rw [he]
    simp
  map_mul' x y := map_mul _ x y

@[simp] theorem dTKern.congr_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.congr (R := R) e hmn y =
      dimensionTransition (R := R) e.toMonoidHom hmn y := rfl

@[simp] theorem dTKern.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) e hmn).symm =
      dTKern.congr (R := R) e.symm hmn := by
  ext y
  rfl

/-- Inverse-application criterion for congruences of dimension transition kernels. -/
theorem dTKern.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn))
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dTKern.congr (R := R) e hmn).symm y = x ↔
      y = dTKern.congr (R := R) e hmn x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem dTKern.congr_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTKern.congr (R := R) (MulEquiv.refl G) hmn =
      MulEquiv.refl (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  ext y
  simp [dTKern.congr_apply]

@[simp] theorem dTKern.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K)
    {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) e hmn).trans
        (dTKern.congr (R := R) f hmn) =
      dTKern.congr (R := R) (e.trans f) hmn := by
  ext y
  change dQuot.map (R := R) f.toMonoidHom n
      (dQuot.map (R := R) e.toMonoidHom n (y : dQuot R G n)) =
    dQuot.map (R := R) (f.toMonoidHom.comp e.toMonoidHom) n y
  have h := congrArg (fun u : dQuot R G n →* dQuot R K n =>
      u (y : dQuot R G n))
    (dQuot.map_comp (R := R) e.toMonoidHom f.toMonoidHom n)
  simpa only [MonoidHom.comp_apply] using h.symm

@[simp] theorem dTKern.congr_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    ((dTKern.congr (R := R) e hmn y :
        MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
        dQuot R H n) =
      dQuot.map (R := R) e.toMonoidHom n (y : dQuot R G n) := rfl

/-- Automorphisms act on arbitrary dimension transition kernels. -/
noncomputable def dTKern.mulAutMap {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut
      (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) where
  toFun e := dTKern.congr (R := R) e hmn
  map_one' := by
    ext y
    change dQuot.map (R := R) (1 : MulAut G).toMonoidHom n
        (y : dQuot R G n) = (y : dQuot R G n)
    refine QuotientGroup.induction_on (y : dQuot R G n) ?_
    intro g
    rfl
  map_mul' e f := by
    ext y
    change dQuot.map (R := R) (e * f).toMonoidHom n
        (y : dQuot R G n) =
      dQuot.map (R := R) e.toMonoidHom n
        (dQuot.map (R := R) f.toMonoidHom n (y : dQuot R G n))
    refine QuotientGroup.induction_on (y : dQuot R G n) ?_
    intro g
    rfl


@[simp] theorem dTKern.mul_aut_mapapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) (y) :
    dTKern.mulAutMap (R := R) hmn e y =
      dTKern.congr (R := R) e hmn y := rfl

/-- Naturality of the arbitrary dimension transition-kernel quotient equivalence. -/
theorem dimension_transition_naturality {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (q : dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) :
    dimensionTransition (R := R) φ hmn
        (dimensionTransitionEquiv (R := R) (G := G) hmn q) =
      dimensionTransitionEquiv (R := R) (G := H) hmn
        (dimensionTerm (R := R) φ hmn q) := by
  simpa [dimensionTransition, dimensionTransitionEquiv,
    dimensionTerm, dimension_quotient_transition]
    using DFilt.transition_kernel_naturality
      (dimensionFiltration_preserves R φ) hmn q

/-- The quotient-kernel equivalence is compatible with isomorphism-induced congruences. -/
theorem dimension_transition_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) :
    dTKern.congr (R := R) e hmn
        (dimensionTransitionEquiv (R := R) (G := G) hmn q) =
      dimensionTransitionEquiv (R := R) (G := H) hmn
        (dTQuot.congr (R := R) e hmn q) := by
  simpa [dTKern.congr_apply, dTQuot.congr_apply]
    using dimension_transition_naturality (R := R)
      e.toMonoidHom hmn q

/-- Equivariance of the quotient-kernel equivalence for automorphisms. -/
theorem dimension_transition_aut {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (q : dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) :
    dTKern.mulAutMap (R := R) hmn e
        (dimensionTransitionEquiv (R := R) (G := G) hmn q) =
      dimensionTransitionEquiv (R := R) (G := G) hmn
        (dTQuot.mulAutMap (R := R) G hmn e q) := by
  simpa [dTKern.mul_aut_mapapply,
    dTQuot.mul_aut_mapapply]
    using dimension_transition_congr (R := R) e hmn q

@[simp] theorem dimension_quotient_refl {G : Type*} [Group G] (n : ℕ) :
    mapOfLe (R := R) (G := G) (le_rfl : n ≤ n) =
      MonoidHom.id (dQuot R G n) := by
  ext g
  rfl

@[simp] theorem quotient_comp {G : Type*} [Group G]
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    (mapOfLe (R := R) (G := G) hlm).comp
        (mapOfLe (R := R) (G := G) hmn) =
      mapOfLe (R := R) (G := G) (le_trans hlm hmn) := by
  ext g
  rfl

/-- Transition maps commute with maps induced by homomorphisms. -/
theorem dimension_quotient_naturality {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    (mapOfLe (R := R) (G := H) hmn).comp
        (dQuot.map (R := R) φ n) =
      (dQuot.map (R := R) φ m).comp
        (mapOfLe (R := R) (G := G) hmn) := by
  ext g
  rfl

/-- The kernel of the successive transition quotient map is the dimension layer kernel. -/
@[simp] theorem dimension_succ_ker {G : Type*} [Group G] (n : ℕ) :
    MonoidHom.ker
        (mapOfLe (R := R) (G := G) (Nat.le_succ n)) =
      dLKern R G n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro g
  change QuotientGroup.mk' (dSubgro R G n) g = 1 ↔
    QuotientGroup.mk' (dSubgro R G (n + 1)) g ∈
      dLKern R G n
  constructor
  · intro hg
    exact (dimension_layer_mk (R := R) (G := G) n g).2
      ((QuotientGroup.eq_one_iff g).1 hg)
  · intro hg
    exact (QuotientGroup.eq_one_iff g).2
      ((dimension_layer_mk (R := R) (G := G) n g).1 hg)

/-- Representative form of the successive-transition kernel criterion. -/
@[simp] theorem ker_dimension_mk {G : Type*} [Group G]
    (n : ℕ) (g : G) :
    QuotientGroup.mk' (dSubgro R G (n + 1)) g ∈
        MonoidHom.ker
          (mapOfLe (R := R) (G := G) (Nat.le_succ n)) ↔
      g ∈ dSubgro R G n := by
  change QuotientGroup.mk' (dSubgro R G (n + 1)) g ∈
      dLKern R G n ↔ g ∈ dSubgro R G n
  exact dimension_layer_mk (R := R) (G := G) n g

/-- A surjective homomorphism induces a surjective map on every dimension quotient. -/
theorem dQuot.map_surjective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) (n : ℕ) :
    Function.Surjective (dQuot.map (R := R) φ n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  rcases hs h with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (dSubgro R G n) g, rfl⟩

/-- Range form of surjectivity on dimension quotients. -/
theorem dQuot.map_rangeeq_topsurj {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) (n : ℕ) :
    (dQuot.map (R := R) φ n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (dQuot.map_surjective (R := R) φ hs n)

/-- The first nontrivial dimension quotient `G/D₂` is abelian. -/
theorem dimension_two_comm {G : Type*} [Group G]
    (a b : dQuot R G 2) : a * b = b * a := by
  refine QuotientGroup.induction_on a ?_
  intro g
  refine QuotientGroup.induction_on b ?_
  intro h
  apply (commutatorElement_eq_one_iff_mul_comm).1
  change ⁅QuotientGroup.mk' (dSubgro R G 2) g,
      QuotientGroup.mk' (dSubgro R G 2) h⁆ = 1
  rw [← map_commutatorElement]
  change QuotientGroup.mk' (dSubgro R G 2) ⁅g, h⁆ = 1
  exact (QuotientGroup.eq_one_iff ⁅g, h⁆).mpr
    (commutator_dimension_two R G g h)

/-- Commutative-group structure on the first nontrivial dimension quotient. -/
instance dQTwo.instCommGroup {G : Type*} [Group G] :
    CommGroup (dQuot R G 2) :=
  { (inferInstance : Group (dQuot R G 2)) with
    mul_comm := dimension_two_comm (R := R) }

/-- Additive avatar of the first nontrivial dimension quotient. -/
abbrev dTAdditi (G : Type*) [Group G] : Type _ :=
  Additive (dQuot R G 2)

/-- Additive map on first dimension quotients induced by a group homomorphism. -/
def dTAdditi.mapAdd {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    dTAdditi R G →+ dTAdditi R H :=
  (dQuot.map (R := R) φ 2).toAdditive

@[simp] theorem dTAdditi.map_add_mul {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (q : dQuot R G 2) :
    dTAdditi.mapAdd (R := R) φ (Additive.ofMul q) =
      Additive.ofMul (dQuot.map (R := R) φ 2 q) := rfl

/-- Integer-linear map on first dimension quotients induced by a homomorphism. -/
noncomputable def dTAdditi.mapIntLinear {G H : Type*}
    [Group G] [Group H] (φ : G →* H) :
    dTAdditi R G →ₗ[ℤ] dTAdditi R H :=
  (dTAdditi.mapAdd (R := R) φ).toIntLinearMap

@[simp] theorem dTAdditi.map_int_linapply {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (x : dTAdditi R G) :
    dTAdditi.mapIntLinear (R := R) φ x =
      dTAdditi.mapAdd (R := R) φ x := rfl

/-- A surjective homomorphism induces a surjective additive map on `G/D₂`. -/
theorem dTAdditi.mapAdd_surjective {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (hs : Function.Surjective φ) :
    Function.Surjective (dTAdditi.mapAdd (R := R) φ) := by
  intro y
  rcases y with ⟨q⟩
  rcases dQuot.map_surjective (R := R) φ hs 2 q with ⟨x, hx⟩
  refine ⟨Additive.ofMul x, ?_⟩
  simpa [dTAdditi.mapAdd] using congrArg Additive.ofMul hx

/-- A surjective homomorphism induces a surjective integer-linear map on `G/D₂`. -/
theorem dTAdditi.map_int_linsurj {G H : Type*}
    [Group G] [Group H] (φ : G →* H) (hs : Function.Surjective φ) :
    Function.Surjective (dTAdditi.mapIntLinear (R := R) φ) := by
  simpa [dTAdditi.map_int_linapply] using
    dTAdditi.mapAdd_surjective (R := R) φ hs

@[simp] theorem dTAdditi.mapAdd_id (G : Type*) [Group G] :
    dTAdditi.mapAdd (R := R) (MonoidHom.id G) =
      AddMonoidHom.id (dTAdditi R G) := by
  ext x
  rfl

@[simp] theorem dTAdditi.mapAdd_comp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K) :
    dTAdditi.mapAdd (R := R) (ψ.comp φ) =
      (dTAdditi.mapAdd (R := R) ψ).comp
        (dTAdditi.mapAdd (R := R) φ) := by
  ext x
  rfl

@[simp] theorem dTAdditi.map_int_linid (G : Type*) [Group G] :
    dTAdditi.mapIntLinear (R := R) (MonoidHom.id G) =
      LinearMap.id := by
  ext x
  simp [dTAdditi.mapIntLinear]

@[simp] theorem dTAdditi.map_int_lincomp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K) :
    dTAdditi.mapIntLinear (R := R) (ψ.comp φ) =
      (dTAdditi.mapIntLinear (R := R) ψ).comp
        (dTAdditi.mapIntLinear (R := R) φ) := by
  ext x
  simp [dTAdditi.mapIntLinear]

/-- An automorphism of `G` induces an integer-linear automorphism of `G/D₂`. -/
noncomputable def dTAdditi.congrIntLinear {G : Type*} [Group G]
    (e : MulAut G) :
    dTAdditi R G ≃ₗ[ℤ] dTAdditi R G :=
{ dTAdditi.mapIntLinear (R := R) e.toMonoidHom with
  invFun := dTAdditi.mapIntLinear (R := R) e.symm.toMonoidHom
  left_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        change Additive.ofMul (QuotientGroup.mk' (dSubgro R G 2) (e.symm (e g))) =
          Additive.ofMul (QuotientGroup.mk' (dSubgro R G 2) g)
        simp
  right_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        change Additive.ofMul (QuotientGroup.mk' (dSubgro R G 2) (e (e.symm g))) =
          Additive.ofMul (QuotientGroup.mk' (dSubgro R G 2) g)
        simp }

@[simp] theorem dTAdditi.congr_int_linapply {G : Type*} [Group G]
    (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) e x =
      dTAdditi.mapIntLinear (R := R) e.toMonoidHom x := rfl

/-- The induced integer-linear action of automorphisms on `G/D₂`. -/
noncomputable def dTAdditi.linearAutMap (G : Type*) [Group G] :
    MulAut G →* (dTAdditi R G ≃ₗ[ℤ]
      dTAdditi R G) where
  toFun e := dTAdditi.congrIntLinear (R := R) e
  map_one' := by
    ext x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        rfl
  map_mul' e f := by
    ext x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        rfl

/-- Additive version of the equivalence between the first dimension layer kernel
and the first nontrivial quotient `G/D₂`. -/
def dimensionAddEquiv {G : Type*} [Group G] :
    Additive (dLKern R G 1) ≃+ dTAdditi R G :=
  MulEquiv.toAdditive (dimensionLayerEquiv (R := R) (G := G))

@[simp] theorem dimension_add_equiv {G : Type*} [Group G]
    (x : dLKern R G 1) :
    dimensionAddEquiv (R := R) (Additive.ofMul x) =
      Additive.ofMul (x : dQuot R G 2) := rfl

@[simp] theorem dimension_layer_symm {G : Type*} [Group G]
    (q : dQuot R G 2) :
    (dimensionAddEquiv (R := R) (G := G)).symm (Additive.ofMul q) =
      Additive.ofMul ((dimensionLayerEquiv (R := R) (G := G)).symm q) := rfl

/-- Integer-linear version of the first-layer/first-quotient equivalence. -/
noncomputable def dimensionIntLinear {G : Type*} [Group G] :
    Additive (dLKern R G 1) ≃ₗ[ℤ] dTAdditi R G :=
  LinearEquiv.ofBijective
    ((dimensionAddEquiv (R := R) (G := G)).toAddMonoidHom.toIntLinearMap) <| by
      constructor
      · intro x y h
        exact (dimensionAddEquiv (R := R) (G := G)).injective h
      · intro y
        rcases (dimensionAddEquiv (R := R) (G := G)).surjective y with ⟨x, hx⟩
        exact ⟨x, hx⟩

@[simp] theorem dimension_int_linear {G : Type*} [Group G]
    (x : Additive (dLKern R G 1)) :
    dimensionIntLinear (R := R) (G := G) x =
      dimensionAddEquiv (R := R) (G := G) x := rfl

/-- Naturality of the first-layer additive equivalence. -/
theorem dimension_layer_naturality {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (x : Additive (dLKern R G 1)) :
    dTAdditi.mapAdd (R := R) φ
        (dimensionAddEquiv (R := R) (G := G) x) =
      dimensionAddEquiv (R := R) (G := H)
        (dLKern.mapAdd (R := R) φ 1 x) := by
  rcases x with ⟨y⟩
  rfl

/-- Naturality of the first-layer integer-linear equivalence. -/
theorem dimension_int_naturality {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (x : Additive (dLKern R G 1)) :
    dTAdditi.mapIntLinear (R := R) φ
        (dimensionIntLinear (R := R) (G := G) x) =
      dimensionIntLinear (R := R) (G := H)
        (dLKern.mapIntLinear (R := R) φ 1 x) := by
  rcases x with ⟨y⟩
  rfl



/-- The first projection after the product equivalence on dimension quotients is the
map induced by the first projection of groups. -/
@[simp] theorem dimension_prod_fst
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp (dimensionProdEquiv R G H n).toMonoidHom =
      dQuot.map (R := R) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  cases x
  rfl

/-- The second projection after the product equivalence on dimension quotients is the
map induced by the second projection of groups. -/
@[simp] theorem dimension_prod_snd
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp (dimensionProdEquiv R G H n).toMonoidHom =
      dQuot.map (R := R) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  cases x
  rfl


/-- Product equivalence on dimension quotients is pointwise the pair of projection maps. -/
@[simp] theorem dimension_prod_equiv
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    dimensionProdEquiv R G H n x =
      (dQuot.map (R := R) (MonoidHom.fst G H) n x,
        dQuot.map (R := R) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : dQuot R (G × H) n →*
        dQuot R G n => f x)
      (dimension_prod_fst (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : dQuot R (G × H) n →*
        dQuot R H n => f x)
      (dimension_prod_snd (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h

/-- The product equivalence carries the quotient map induced by the left inclusion to
the left inclusion of quotient factors. -/
@[simp] theorem dimension_prod_inl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dimensionProdEquiv R G H n).toMonoidHom.comp
        (dQuot.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- The product equivalence carries the quotient map induced by the right inclusion to
the right inclusion of quotient factors. -/
@[simp] theorem dimension_prod_inr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dimensionProdEquiv R G H n).toMonoidHom.comp
        (dQuot.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl


/-- The inverse product equivalence sends a left-factor dimension quotient element to
the map induced by the left product inclusion. -/
@[simp] theorem dimension_symm_inl
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dQuot R G n) :
    (dimensionProdEquiv R G H n).symm (x, 1) =
      dQuot.map (R := R) (MonoidHom.inl G H) n x := by
  apply (dimensionProdEquiv R G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : dQuot R G n →*
      (dQuot R G n × dQuot R H n) => f x)
    (dimension_prod_inl (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor dimension quotient element to
the map induced by the right product inclusion. -/
@[simp] theorem dimension_symm_inr
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dQuot R H n) :
    (dimensionProdEquiv R G H n).symm (1, x) =
      dQuot.map (R := R) (MonoidHom.inr G H) n x := by
  apply (dimensionProdEquiv R G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : dQuot R H n →*
      (dQuot R G n × dQuot R H n) => f x)
    (dimension_prod_inr (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- Every product dimension quotient element splits into projected inclusion components. -/
theorem dQuot.eq_inl_mulinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    x = dQuot.map (R := R) (MonoidHom.inl G H) n
          (dQuot.map (R := R) (MonoidHom.fst G H) n x) *
        dQuot.map (R := R) (MonoidHom.inr G H) n
          (dQuot.map (R := R) (MonoidHom.snd G H) n x) := by
  let e := dimensionProdEquiv R G H n
  have hf : (e x).1 = dQuot.map (R := R) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : dQuot R (G × H) n →*
        dQuot R G n => f x)
      (dimension_prod_fst (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = dQuot.map (R := R) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : dQuot R (G × H) n →*
        dQuot R H n => f x)
      (dimension_prod_snd (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = dQuot.map (R := R) (MonoidHom.inl G H) n
          (dQuot.map (R := R) (MonoidHom.fst G H) n x) *
        dQuot.map (R := R) (MonoidHom.inr G H) n
          (dQuot.map (R := R) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]

/-- Left- and right-inclusion images commute in a product dimension quotient. -/
theorem dQuot.map_inlmul_inrcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R G n) (y : dQuot R H n) :
    dQuot.map (R := R) (MonoidHom.inl G H) n x *
        dQuot.map (R := R) (MonoidHom.inr G H) n y =
      dQuot.map (R := R) (MonoidHom.inr G H) n y *
        dQuot.map (R := R) (MonoidHom.inl G H) n x := by
  let e := dimensionProdEquiv R G H n
  apply e.injective
  have hx : e (dQuot.map (R := R) (MonoidHom.inl G H) n x) = (x, 1) := by
    have h := congrArg (fun f : dQuot R G n →*
        (dQuot R G n × dQuot R H n) => f x)
      (dimension_prod_inl (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (dQuot.map (R := R) (MonoidHom.inr G H) n y) = (1, y) := by
    have h := congrArg (fun f : dQuot R H n →*
        (dQuot R G n × dQuot R H n) => f y)
      (dimension_prod_inr (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first dimension quotient factor is trivial. -/
@[simp] theorem dQuot.map_fst_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.fst G H) n).comp
        (dQuot.map (R := R) (MonoidHom.inr G H) n) =
      (1 : dQuot R H n →* dQuot R G n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : dQuot R H n →*
      (dQuot R G n × dQuot R H n) => f x)
    (dimension_prod_inr (R := R) G H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, dimension_prod_equiv] using hf

/-- Projecting the left-inclusion map to the second dimension quotient factor is trivial. -/
@[simp] theorem dQuot.map_snd_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.snd G H) n).comp
        (dQuot.map (R := R) (MonoidHom.inl G H) n) =
      (1 : dQuot R G n →* dQuot R H n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : dQuot R G n →*
      (dQuot R G n × dQuot R H n) => f x)
    (dimension_prod_inl (R := R) G H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, dimension_prod_equiv] using hs

@[simp] theorem dQuot.map_fst_inrapply
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dQuot R H n) :
    dQuot.map (R := R) (MonoidHom.fst G H) n
        (dQuot.map (R := R) (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : dQuot R H n →* dQuot R G n => f x)
    (dQuot.map_fst_compinr (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem dQuot.map_snd_inlapply
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dQuot R G n) :
    dQuot.map (R := R) (MonoidHom.snd G H) n
        (dQuot.map (R := R) (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : dQuot R G n →* dQuot R H n => f x)
    (dQuot.map_snd_compinl (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product dimension-quotient element lies in the right-inclusion range iff its first
projection is trivial. -/
theorem dQuot.memrange_inriffmap_fsteqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    x ∈ (dQuot.map (R := R) (MonoidHom.inr G H) n).range ↔
      dQuot.map (R := R) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : dQuot R H n →*
        dQuot R G n => f y)
      (dQuot.map_fst_compinr (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dQuot.map (R := R) (MonoidHom.snd G H) n x, ?_⟩
    have h := dQuot.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product dimension-quotient element lies in the left-inclusion range iff its second
projection is trivial. -/
theorem dQuot.memrange_inliffmap_sndeqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    x ∈ (dQuot.map (R := R) (MonoidHom.inl G H) n).range ↔
      dQuot.map (R := R) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : dQuot R G n →*
        dQuot R H n => f y)
      (dQuot.map_snd_compinl (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dQuot.map (R := R) (MonoidHom.fst G H) n x, ?_⟩
    have h := dQuot.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product dimension quotient is the
right-inclusion range. -/
theorem dQuot.kermap_fsteq_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.fst G H) n).ker =
      (dQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  ext x
  exact (dQuot.memrange_inriffmap_fsteqone (R := R) G H n x).symm

/-- The kernel of the second projection on a product dimension quotient is the
left-inclusion range. -/
theorem dQuot.kermap_sndeq_rangeinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.snd G H) n).ker =
      (dQuot.map (R := R) (MonoidHom.inl G H) n).range := by
  ext x
  exact (dQuot.memrange_inliffmap_sndeqone (R := R) G H n x).symm

/-- The left- and right-inclusion ranges in a product dimension quotient meet only at `1`. -/
theorem dQuot.eqone_memrangeinl_memrangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    {x : dQuot R (G × H) n}
    (hxL : x ∈ (dQuot.map (R := R) (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (dQuot.map (R := R) (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (dQuot.memrange_inriffmap_fsteqone
    (R := R) G H n x).1 hxR
  have hsnd := (dQuot.memrange_inliffmap_sndeqone
    (R := R) G H n x).1 hxL
  have h := dQuot.eq_inl_mulinr (R := R) G H n x
  simpa [hfst, hsnd] using h

/-- The left- and right-inclusion ranges in a product dimension quotient are disjoint. -/
theorem dQuot.disjoint_rangeinl_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Disjoint (dQuot.map (R := R) (MonoidHom.inl G H) n).range
      (dQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact dQuot.eqone_memrangeinl_memrangeinr
    (R := R) G H n hxL hxR

/-- Projecting after the left-inclusion map on dimension quotients is the identity. -/
@[simp] theorem dQuot.map_fst_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.fst G H) n).comp
        (dQuot.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.id (dQuot R G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← dQuot.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, dQuot.map_id]

/-- Projecting after the right-inclusion map on dimension quotients is the identity. -/
@[simp] theorem dQuot.map_snd_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.snd G H) n).comp
        (dQuot.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.id (dQuot R H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← dQuot.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, dQuot.map_id]


/-- The quotient map induced by the first product projection is surjective. -/
theorem dQuot.map_fst_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dQuot.map (R := R) (MonoidHom.fst G H) n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  refine ⟨QuotientGroup.mk' (dSubgro R (G × H) n) (g, 1), ?_⟩
  rfl

/-- The quotient map induced by the second product projection is surjective. -/
theorem dQuot.map_snd_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dQuot.map (R := R) (MonoidHom.snd G H) n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  refine ⟨QuotientGroup.mk' (dSubgro R (G × H) n) (1, h), ?_⟩
  rfl

/-- The first projection map on product dimension quotients has full range. -/
theorem dQuot.range_mapfst_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dQuot.map_fst_surjective (R := R) G H n)

/-- The second projection map on product dimension quotients has full range. -/
theorem dQuot.range_mapsnd_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dQuot.map_snd_surjective (R := R) G H n)

/-- The quotient map induced by the left product inclusion is injective. -/
theorem dQuot.map_inl_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dQuot.map (R := R) (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (dQuot.map (R := R) (MonoidHom.fst G H) n)
      (dQuot.map (R := R) (MonoidHom.inl G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  exact hleft.injective

/-- The quotient map induced by the right product inclusion is injective. -/
theorem dQuot.map_inr_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dQuot.map (R := R) (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (dQuot.map (R := R) (MonoidHom.snd G H) n)
      (dQuot.map (R := R) (MonoidHom.inr G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro h
    rfl
  exact hleft.injective

/-- The left product-inclusion map on dimension quotients has trivial kernel. -/
theorem dQuot.ker_mapinl_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dQuot.map_inl_injective (R := R) G H n)

/-- The right product-inclusion map on dimension quotients has trivial kernel. -/
theorem dQuot.ker_mapinr_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dQuot.map (R := R) (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dQuot.map_inr_injective (R := R) G H n)

/-- Naturality of the dimension-quotient product equivalence. -/
theorem dimension_equiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (dimensionProdEquiv R G₂ H₂ n).toMonoidHom.comp
        (dQuot.map (R := R) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (dQuot.map (R := R) f n)
        (dQuot.map (R := R) g n)).comp
        (dimensionProdEquiv R G₁ H₁ n).toMonoidHom := by
  ext x <;> rfl


/-- Associator followed by its inverse is identity on dimension quotients. -/
@[simp] theorem dQuot.mapprod_assocsymm_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (dQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dQuot R ((G × H) × K) n →*
      dQuot R ((G × H) × K) n => f x)
    (dQuot.map_id (R := R) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on dimension quotients. -/
@[simp] theorem dQuot.mapprod_assocprod_assocsymm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × H × K) n) :
    dQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (dQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dQuot R (G × H × K) n →*
      dQuot R (G × H × K) n => f x)
    (dQuot.map_id (R := R) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Associativity coherence for dimension-quotient product equivalences. -/
theorem dimension_assoc_naturality
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap (MonoidHom.id (dQuot R G n))
        (dimensionProdEquiv R H K n).toMonoidHom).comp
      (dimensionProdEquiv R G (H × K) n).toMonoidHom).comp
        (dQuot.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        (dQuot R G n × dQuot R H n) ×
          dQuot R K n ≃*
        dQuot R G n × dQuot R H n ×
          dQuot R K n).toMonoidHom).comp
      ((MonoidHom.prodMap (dimensionProdEquiv R G H n).toMonoidHom
        (MonoidHom.id (dQuot R K n))).comp
        (dimensionProdEquiv R (G × H) K n).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro ghk
  rfl

/-- Pointwise associativity coherence for dimension-quotient product equivalences. -/
@[simp] theorem dimension_prod_assoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    (MonoidHom.prodMap (MonoidHom.id (dQuot R G n))
        (dimensionProdEquiv R H K n).toMonoidHom)
      (dimensionProdEquiv R G (H × K) n
        (dQuot.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        (dQuot R G n × dQuot R H n) ×
          dQuot R K n ≃*
        dQuot R G n × dQuot R H n ×
          dQuot R K n)
        ((MonoidHom.prodMap (dimensionProdEquiv R G H n).toMonoidHom
          (MonoidHom.id (dQuot R K n)))
          (dimensionProdEquiv R (G × H) K n x)) := by
  have h := congrArg (fun f : dQuot R ((G × H) × K) n →*
      (dQuot R G n × dQuot R H n ×
        dQuot R K n) => f x)
    (dimension_assoc_naturality (R := R) G H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Inverse-form associativity coherence for dimension-quotient product equivalences. -/
@[simp] theorem dimension_assoc_symm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (a : dQuot R G n) (b : dQuot R H n)
    (c : dQuot R K n) :
    dQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((dimensionProdEquiv R (G × H) K n).symm
        ((dimensionProdEquiv R G H n).symm (a, b), c)) =
      (dimensionProdEquiv R G (H × K) n).symm
        (a, (dimensionProdEquiv R H K n).symm (b, c)) := by
  apply (dimensionProdEquiv R G (H × K) n).injective
  let x : dQuot R ((G × H) × K) n :=
    (dimensionProdEquiv R (G × H) K n).symm
      ((dimensionProdEquiv R G H n).symm (a, b), c)
  have h := dimension_prod_assoc (R := R) G H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (dimensionProdEquiv R H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Pointwise form of naturality for dimension-quotient product equivalences. -/
@[simp] theorem dimension_prod_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dQuot R (G₁ × H₁) n) :
    dimensionProdEquiv R G₂ H₂ n
        (dQuot.map (R := R) (MonoidHom.prodMap f g) n x) =
      (dQuot.map (R := R) f n (dimensionProdEquiv R G₁ H₁ n x).1,
        dQuot.map (R := R) g n (dimensionProdEquiv R G₁ H₁ n x).2) := by
  have h := congrArg (fun F : dQuot R (G₁ × H₁) n →*
      (dQuot R G₂ n × dQuot R H₂ n) => F x)
    (dimension_equiv_naturality (R := R) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality, written on inverse product representatives, for dimension quotients. -/
@[simp] theorem dimension_symm_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : dQuot R G₁ n × dQuot R H₁ n) :
    dQuot.map (R := R) (MonoidHom.prodMap f g) n
        ((dimensionProdEquiv R G₁ H₁ n).symm y) =
      (dimensionProdEquiv R G₂ H₂ n).symm
        (dQuot.map (R := R) f n y.1,
          dQuot.map (R := R) g n y.2) := by
  apply (dimensionProdEquiv R G₂ H₂ n).injective
  have h := dimension_prod_naturality (R := R) f g n
    ((dimensionProdEquiv R G₁ H₁ n).symm y)
  simpa using h

/-- Product-commuting the factors is compatible with the dimension-quotient product equivalence. -/
theorem dimension_swap_naturality
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dimensionProdEquiv R H G n).toMonoidHom.comp
        (dQuot.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm : dQuot R G n × dQuot R H n ≃*
          dQuot R H n × dQuot R G n).toMonoidHom).comp
        (dimensionProdEquiv R G H n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro gh
  rfl

/-- Applying the product-commuting map twice on dimension quotients is the identity. -/
@[simp] theorem dQuot.map_prodcomm_prodcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    dQuot.map (R := R)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (dQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dQuot R (G × H) n →*
      dQuot R (G × H) n => f x)
    (dQuot.map_id (R := R) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Pointwise form of swap-naturality for dimension-quotient product equivalences. -/
@[simp] theorem dimension_prod_swap
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dQuot R (G × H) n) :
    dimensionProdEquiv R H G n
        (dQuot.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((dimensionProdEquiv R G H n x).2,
        (dimensionProdEquiv R G H n x).1) := by
  have h := congrArg (fun f : dQuot R (G × H) n →*
      (dQuot R H n × dQuot R G n) => f x)
    (dimension_swap_naturality (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h

/-- For any termwise-onto map of dimension filtrations, the preimage of a target term
is the source term times the ordinary kernel. -/
theorem dimension_sup_onto (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    (dSubgro R H n).comap φ = dSubgro R G n ⊔ φ.ker :=
  DFilt.MapsOnto.comap_eq_supker honto n


/-- For a termwise-onto map of dimension filtrations, exact preimage at a term is
equivalent to kernel containment in that term. -/
theorem dimension_comap_onto (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    (dSubgro R H n).comap φ = dSubgro R G n ↔
      φ.ker ≤ dSubgro R G n :=
  DFilt.MapsOnto.comap_eqiff_kerle honto n

/-- For a split epimorphism, the preimage of a dimension subgroup is the source
dimension subgroup times the kernel. -/
theorem dimension_comap_sup (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (n : ℕ) :
    (dSubgro R H n).comap φ = dSubgro R G n ⊔ φ.ker :=
  DFilt.comap_sup_ker
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ n


/-- A split epimorphism maps each dimension subgroup onto the corresponding
target dimension subgroup. -/
theorem dimension_right_inverse (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (n : ℕ) :
    (dSubgro R G n).map φ = dSubgro R H n := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact dimension_subgroup_comap R φ n
  · intro h hh
    refine ⟨σ h, ?_, hσ h⟩
    exact dimension_subgroup_comap R σ n hh


/-- If a split epimorphism is injective, its preimage of each dimension term is exactly
the corresponding source term. -/
theorem dimension_comap_injective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (dSubgro R H n).comap φ = dSubgro R G n :=
  DFilt.MapsOnto.comap_eq_inj
    (DFilt.MapsOnto.of_rightInverse
      (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ) hinj n

/-- Split epimorphisms are termwise onto for the dimension filtration. -/
theorem dimension_filtration_inverse (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) :
    DFilt.MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ :=
  DFilt.MapsOnto.of_rightInverse
    (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ


/-- A surjective homomorphism is termwise onto for dimension filtrations if the
preimage of every target dimension term is contained in the corresponding source term. -/
theorem dimension_surjective_comap
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (dSubgro R H n).comap φ ≤ dSubgro R G n) :
    DFilt.MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ :=
  DFilt.MapsOnto.surj_comap_le
    (dimensionFiltration_preserves R φ) hs hpre

/-- Equality of all dimension-term preimages is a convenient sufficient condition for
termwise onto compatibility under a surjective homomorphism. -/
theorem dimension_filtration_comap
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (dSubgro R H n).comap φ = dSubgro R G n) :
    DFilt.MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ :=
  DFilt.MapsOnto.surj_comap_eq
    (dimensionFiltration_preserves R φ) hs hpre


/-- Exact preimages of all dimension terms imply termwise onto compatibility for a
surjective homomorphism, with preservation inferred automa. -/
theorem dimension_comap_exact
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (dSubgro R H n).comap φ = dSubgro R G n) :
    DFilt.MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ :=
  DFilt.MapsOnto.surj_comap_eqexact hs hpre


/-- A split epimorphism induces surjective maps on dimension quotients. -/
theorem dQuot.map_surj_rightinv (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (dQuot.map (R := R) φ n) := by
  simpa [dQuot.map] using
    DFilt.quotient_surjective_onto
      (dimension_filtration_inverse R φ σ hσ) n

/-- A split epimorphism that is also injective induces bijections on dimension quotients. -/
theorem dQuot.map_bijright_invinj
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (dQuot.map (R := R) φ n) := by
  simpa [dQuot.map] using
    DFilt.quotient_bijective_injective
      (dimension_filtration_inverse R φ σ hσ) hinj n


/-- A split epimorphism that is also injective induces bijections on arbitrary
dimension term quotients. -/
theorem dimension_bijective_injective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (dimensionTerm (R := R) φ hmn) := by
  simpa [dimensionTerm] using
    DFilt.term_bijective_injective
      (dimension_filtration_inverse R φ σ hσ) hinj hmn

/-- A split epimorphism that is also injective induces bijections on arbitrary
dimension transition kernels. -/
theorem dimension_bijective_inverse
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (dimensionTransition (R := R) φ hmn) := by
  simpa [dimensionTransition] using
    DFilt.kernel_bijective_injective
      (dimension_filtration_inverse R φ σ hσ) hinj hmn


/-- A split epimorphism that is also injective induces an equivalence on dimension
quotients.  This is the convenient packaged form of
`dQuot.map_bijright_invinj`. -/
noncomputable def dQuot.equiv_right_invinj
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    dQuot R G n ≃* dQuot R H n :=
  DFilt.quotientOntoInjective
    (dimension_filtration_inverse R φ σ hσ) hinj n

@[simp] theorem dQuot.equiv_rightinv_injapply
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : dQuot R G n) :
    dQuot.equiv_right_invinj (R := R) φ σ hσ hinj n x =
      dQuot.map (R := R) φ n x := rfl

@[simp] theorem dQuot.equivright_invinj_monoidhom
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (dQuot.equiv_right_invinj (R := R) φ σ hσ hinj n).toMonoidHom =
      dQuot.map (R := R) φ n := rfl

/-- A split epimorphism that is also injective induces an equivalence on arbitrary
dimension term quotients. -/
noncomputable def dimensionTermInjective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :=
  DFilt.termMapsInjective
    (dimension_filtration_inverse R φ σ hσ) hinj hmn

@[simp] theorem dimension_right_injective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTermInjective (R := R) φ σ hσ hinj hmn x =
      dimensionTerm (R := R) φ hmn x := rfl

@[simp] theorem dimension_term_monoid
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    (dimensionTermInjective (R := R) φ σ hσ hinj hmn).toMonoidHom =
      dimensionTerm (R := R) φ hmn := rfl

/-- A split epimorphism that is also injective induces an equivalence on arbitrary
dimension transition kernels. -/
noncomputable def dimensionTransitionInjective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) :=
  DFilt.transitionOntoInjective
    (dimension_filtration_inverse R φ σ hσ) hinj hmn

@[simp] theorem dimension_inverse_injective
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionInjective (R := R) φ σ hσ hinj hmn x =
      dimensionTransition (R := R) φ hmn x := rfl

@[simp] theorem dimension_injective_monoid
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    (dimensionTransitionInjective (R := R) φ σ hσ hinj hmn).toMonoidHom =
      dimensionTransition (R := R) φ hmn := rfl


/-- Inverse-characterization for the split-epi/injective dimension quotient equivalence. -/
theorem dQuot.equivright_invinj_symmapplyeq
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (y : dQuot R H n) (x : dQuot R G n) :
    (dQuot.equiv_right_invinj (R := R) φ σ hσ hinj n).symm y = x ↔
      y = dQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the split-epi/injective dimension term-quotient equivalence. -/
theorem dimension_inverse_symm
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionTermInjective (R := R) φ σ hσ hinj hmn).symm y = x ↔
      y = dimensionTerm (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the split-epi/injective dimension transition-kernel equivalence. -/
theorem dimension_injective_symm
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn))
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionTransitionInjective (R := R) φ σ hσ hinj hmn).symm y = x ↔
      y = dimensionTransition (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- For any termwise-onto map of dimension filtrations, injectivity on a dimension
quotient is equivalent to kernel containment in the source term. -/
theorem dQuot.mapinj_iffker_lemapsonto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    Function.Injective (dQuot.map (R := R) φ n) ↔
      φ.ker ≤ dSubgro R G n := by
  simpa [dQuot.map] using
    DFilt.injective_maps_onto honto (n := n)

/-- For any termwise-onto map of dimension filtrations, bijectivity on a dimension
quotient is equivalent to kernel containment in the source term. -/
theorem dQuot.mapbij_iffker_lemapsonto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (n : ℕ) :
    Function.Bijective (dQuot.map (R := R) φ n) ↔
      φ.ker ≤ dSubgro R G n := by
  simpa [dQuot.map] using
    DFilt.bijective_ker_onto honto (n := n)

/-- A termwise-onto map of dimension filtrations whose kernel lies in the source term
induces an equivalence on dimension quotients. -/
noncomputable def dQuot.equiv_mapsonto_kerle
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) :
    dQuot R G n ≃* dQuot R H n :=
  DFilt.quotientMapsKer honto hker

@[simp] theorem dQuot.equivmaps_ontoker_leapply
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (x : dQuot R G n) :
    dQuot.equiv_mapsonto_kerle (R := R) φ honto hker x =
      dQuot.map (R := R) φ n x := rfl

@[simp] theorem dQuot.equivmaps_ontoker_lemonoidhom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) :
    (dQuot.equiv_mapsonto_kerle (R := R) φ honto hker).toMonoidHom =
      dQuot.map (R := R) φ n := rfl

/-- Inverse-characterization for dimension quotient equivalences from termwise-onto maps
with kernel contained in the source term. -/
theorem dQuot.equivmaps_ontokerle_symmapplyeq
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n)
    (y : dQuot R H n) (x : dQuot R G n) :
    (dQuot.equiv_mapsonto_kerle (R := R) φ honto hker).symm y = x ↔
      y = dQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on all earlier
dimension quotients. -/
noncomputable def dQuot.equivmaps_ontoker_lele
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n) :
    dQuot R G m ≃* dQuot R H m :=
  DFilt.quotientOntoKer honto hker hmn

@[simp] theorem dQuot.equivmaps_ontoker_leleapply
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (x : dQuot R G m) :
    dQuot.equivmaps_ontoker_lele (R := R) φ honto hker hmn x =
      dQuot.map (R := R) φ m x := rfl

@[simp] theorem dQuot.equivmaps_ontokerle_lemonoidhom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n) :
    (dQuot.equivmaps_ontoker_lele (R := R) φ honto hker hmn).toMonoidHom =
      dQuot.map (R := R) φ m := rfl

/-- Inverse-characterization for monotone-kernel dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_symma
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (y : dQuot R H m) (x : dQuot R G m) :
    (dQuot.equivmaps_ontoker_lele (R := R) φ honto hker hmn).symm y = x ↔
      y = dQuot.map (R := R) φ m x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Termwise-onto maps induce surjections on dimension term quotients. -/
theorem dimension_surjective_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (dimensionTerm (R := R) φ hmn) := by
  simpa [dimensionTerm] using
    DFilt.term_surjective_onto honto hmn

/-- Range form of surjectivity on dimension term quotients. -/
theorem dimension_top_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (dimensionTerm (R := R) φ hmn).range = ⊤ := by
  simpa [dimensionTerm] using
    DFilt.term_top_onto honto hmn

/-- Termwise-onto maps induce surjections on dimension transition kernels. -/
theorem dimension_transition_surjective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (dimensionTransition (R := R) φ hmn) := by
  simpa [dimensionTransition] using
    DFilt.transition_surjective_maps honto hmn

/-- Range form of surjectivity on dimension transition kernels. -/
theorem dimension_range_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (dimensionTransition (R := R) φ hmn).range = ⊤ := by
  simpa [dimensionTransition] using
    DFilt.transition_top_onto honto hmn

/-- Bijectivity on dimension term quotients from termwise-onto plus kernel containment. -/
theorem dimension_bijective_maps
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    Function.Bijective (dimensionTerm (R := R) φ hmn) := by
  simpa [dimensionTerm] using
    DFilt.term_bijective_maps
      honto hmn hker

/-- Deeper kernel containment gives bijectivity on earlier dimension term quotients. -/
theorem dimension_bijective_ker
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    Function.Bijective (dimensionTerm (R := R) φ hmn) := by
  simpa [dimensionTerm] using
    DFilt.term_bijective_ker
      honto hmn hker hnk

/-- Termwise-onto injective maps give bijectivity on dimension term quotients. -/
theorem bijective_maps_injective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (dimensionTerm (R := R) φ hmn) := by
  simpa [dimensionTerm] using
    DFilt.term_bijective_injective
      honto hinj hmn

/-- Bijectivity on dimension transition kernels from termwise-onto plus kernel containment. -/
theorem dimension_bijective_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    Function.Bijective (dimensionTransition (R := R) φ hmn) := by
  simpa [dimensionTransition] using
    DFilt.transition_kernel_bijective
      honto hmn hker

/-- Deeper kernel containment gives bijectivity on earlier dimension transition kernels. -/
theorem dimension_transition_bijective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    Function.Bijective (dimensionTransition (R := R) φ hmn) := by
  simpa [dimensionTransition] using
    DFilt.transition_bijective_ker
      honto hmn hker hnk

/-- Termwise-onto injective maps give bijectivity on dimension transition kernels. -/
theorem transition_bijective_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (dimensionTransition (R := R) φ hmn) := by
  simpa [dimensionTransition] using
    DFilt.kernel_bijective_injective
      honto hinj hmn

/-- A termwise-onto map of dimension filtrations with kernel contained in the deeper
term induces an equivalence on the corresponding dimension term quotient. -/
noncomputable def dimensionTermKer
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :=
  DFilt.termMapsOnto honto hmn hker

@[simp] theorem dimension_term_equiv
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTermKer (R := R) φ honto hmn hker x =
      dimensionTerm (R := R) φ hmn x := rfl

@[simp] theorem dimension_maps_monoid
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    (dimensionTermKer (R := R) φ honto hmn hker).toMonoidHom =
      dimensionTerm (R := R) φ hmn := rfl

/-- Inverse-characterization for dimension term quotient equivalences from termwise-onto
maps with kernel contained in the deeper term. -/
theorem dimension_quotient_onto
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionTermKer (R := R) φ honto hmn hker).symm y = x ↔
      y = dimensionTerm (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
dimension term quotients. -/
noncomputable def dimensionOntoKer
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :=
  DFilt.termMapsKer honto hmn hker hnk

@[simp] theorem dimension_term_quotient
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionOntoKer (R := R) φ honto hmn hker hnk x =
      dimensionTerm (R := R) φ hmn x := rfl

@[simp] theorem dimension_onto_monoid
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    (dimensionOntoKer (R := R) φ honto hmn hker hnk).toMonoidHom =
      dimensionTerm (R := R) φ hmn := rfl

theorem dimension_quotient_symm
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionOntoKer (R := R) φ honto hmn hker hnk).symm y = x ↔
      y = dimensionTerm (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of dimension filtrations with kernel contained in the deeper
term induces an equivalence on the corresponding transition kernels. -/
noncomputable def dimensionMapsKer
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) :=
  DFilt.transitionMapsOnto honto hmn hker

@[simp] theorem dimension_kernel_equiv
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionMapsKer (R := R) φ honto hmn hker x =
      dimensionTransition (R := R) φ hmn x := rfl

@[simp] theorem dimension_transition_monoid
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n) :
    (dimensionMapsKer (R := R) φ honto hmn hker).toMonoidHom =
      dimensionTransition (R := R) φ hmn := rfl

/-- Inverse-characterization for dimension transition-kernel equivalences from termwise-onto
maps with kernel contained in the deeper term. -/
theorem dimension_kernel_maps
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn))
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionMapsKer (R := R) φ honto hmn hker).symm y = x ↔
      y = dimensionTransition (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
dimension transition kernels. -/
noncomputable def dimensionTransitionKer
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) :=
  DFilt.transitionOntoKer honto hmn hker hnk

@[simp] theorem dimension_transition_equiv
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionKer (R := R) φ honto hmn hker hnk x =
      dimensionTransition (R := R) φ hmn x := rfl

@[simp] theorem dimension_monoid_hom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k) :
    (dimensionTransitionKer (R := R) φ honto hmn hker
      hnk).toMonoidHom =
      dimensionTransition (R := R) φ hmn := rfl

theorem dimension_equiv_symm
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn))
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionTransitionKer (R := R) φ honto hmn hker hnk).symm y = x ↔
      y = dimensionTransition (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A termwise-onto injective map induces an equivalence on dimension quotients. -/
noncomputable def dQuot.equiv_maps_ontoinj
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    dQuot R G n ≃* dQuot R H n :=
  DFilt.quotientOntoInjective honto hinj n

@[simp] theorem dQuot.equiv_mapsonto_injapply
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dQuot R G n) :
    dQuot.equiv_maps_ontoinj (R := R) φ honto hinj n x =
      dQuot.map (R := R) φ n x := rfl

@[simp] theorem dQuot.equivmaps_ontoinj_monoidhom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (dQuot.equiv_maps_ontoinj (R := R) φ honto hinj n).toMonoidHom =
      dQuot.map (R := R) φ n := rfl

theorem dQuot.equivmaps_ontoinj_symmapplyeq
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : dQuot R H n) (x : dQuot R G n) :
    (dQuot.equiv_maps_ontoinj (R := R) φ honto hinj n).symm y = x ↔
      y = dQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto injective map induces an equivalence on dimension term quotients. -/
noncomputable def dimensionMapsInjective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
      (dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :=
  DFilt.termMapsInjective honto hinj hmn

@[simp] theorem dimension_quotient_equiv
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionMapsInjective (R := R) φ honto hinj hmn x =
      dimensionTerm (R := R) φ hmn x := rfl

@[simp] theorem dimension_onto_hom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (dimensionMapsInjective (R := R) φ honto hinj hmn).toMonoidHom =
      dimensionTerm (R := R) φ hmn := rfl

theorem dimension_term_injective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionMapsInjective (R := R) φ honto hinj hmn).symm y = x ↔
      y = dimensionTerm (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto injective map induces an equivalence on dimension transition kernels. -/
noncomputable def dimensionOntoInjective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
      MonoidHom.ker (mapOfLe (R := R) (G := H) hmn) :=
  DFilt.transitionOntoInjective honto hinj hmn

@[simp] theorem kernel_equiv_injective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionOntoInjective (R := R) φ honto hinj hmn x =
      dimensionTransition (R := R) φ hmn x := rfl

@[simp] theorem dimension_transition_hom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (dimensionOntoInjective (R := R) φ honto hinj hmn).toMonoidHom =
      dimensionTransition (R := R) φ hmn := rfl

theorem dimension_kernel_injective
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn))
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionOntoInjective (R := R) φ honto hinj hmn).symm y = x ↔
      y = dimensionTransition (R := R) φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A termwise-onto injective map identifies corresponding dimension subgroup terms. -/
noncomputable def dSubgro.equiv_maps_ontoinj
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    dSubgro R G n ≃* dSubgro R H n :=
  DFilt.termEquivInjective honto hinj n

@[simp] theorem dSubgro.equivmaps_ontoinj_applycoe
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n) :
    ((dSubgro.equiv_maps_ontoinj (R := R) φ honto hinj n x :
        dSubgro R H n) : H) = φ (x : G) := rfl

@[simp] theorem dSubgro.equivmaps_ontoinj_monoidhom
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (dSubgro.equiv_maps_ontoinj (R := R) φ honto hinj n).toMonoidHom =
      dSubgro.termMap (R := R) φ n := rfl

@[simp] theorem dSubgro.equivm_ontoi_monoi
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n) :
    (((dSubgro.equiv_maps_ontoinj (R := R) φ honto hinj n).toMonoidHom x :
        dSubgro R H n) : H) = φ (x : G) := rfl


/-- The inverse of the dimension-term equivalence chooses a preimage under the map. -/
theorem dSubgro.equivmaps_ontoinj_symmapplycoe
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : dSubgro R H n) :
    φ (((dSubgro.equiv_maps_ontoinj (R := R) φ honto hinj n).symm y :
        dSubgro R G n) : G) = (y : H) :=
  DFilt.term_symm_coe honto hinj n y

/-- Inverse characterization for the dimension-subgroup term equivalence. -/
theorem dSubgro.equivmaps_ontoinj_symmapplyeq
    (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : dSubgro R H n) (x : dSubgro R G n) :
    (dSubgro.equiv_maps_ontoinj (R := R) φ honto hinj n).symm y = x ↔
      y = DFilt.termMap (DFilt.MapsOnto.preserves honto) n x := by
  exact DFilt.maps_symm honto hinj n y x

/-- For a split epimorphism, injectivity on a dimension quotient is equivalent to
having kernel contained in the source term. -/
theorem dQuot.mapinj_iffker_lerightinv
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Injective (dQuot.map (R := R) φ n) ↔
      φ.ker ≤ dSubgro R G n := by
  simpa [dQuot.map] using
    DFilt.injective_ker_inverse
      (F := dimensionFiltration R G) (E := dimensionFiltration R H)
      (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ (n := n)

/-- For a split epimorphism, bijectivity on a dimension quotient is equivalent to
the same kernel containment. -/
theorem dQuot.mapbij_iffker_lerightinv
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Bijective (dQuot.map (R := R) φ n) ↔
      φ.ker ≤ dSubgro R G n := by
  simpa [dQuot.map] using
    DFilt.bijective_ker_inverse
      (F := dimensionFiltration R G) (E := dimensionFiltration R H)
      (dimensionFiltration_preserves R φ) (dimensionFiltration_preserves R σ) hσ (n := n)


/-- The dimension quotient equivalence induced by a split epimorphism whose kernel
lies in the relevant source term. -/
noncomputable def dQuot.rightInverseEquiv (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) :
    dQuot R G n ≃* dQuot R H n :=
  MulEquiv.ofBijective (dQuot.map (R := R) φ n)
    ((dQuot.mapbij_iffker_lerightinv (R := R) φ σ hσ n).2 hker)

@[simp] theorem dQuot.equiv_right_invapply (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (x : dQuot R G n) :
    dQuot.rightInverseEquiv (R := R) φ σ hσ hker x =
      dQuot.map (R := R) φ n x := rfl


@[simp] theorem dQuot.equiv_rightinv_monoidhom
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) :
    (dQuot.rightInverseEquiv (R := R) φ σ hσ hker).toMonoidHom =
      dQuot.map (R := R) φ n := rfl

/-- Inverse-characterization for the kernel-contained split-epi dimension quotient equivalence. -/
theorem dQuot.equivright_invsymm_applyeq
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n)
    (y : dQuot R H n) (x : dQuot R G n) :
    (dQuot.rightInverseEquiv (R := R) φ σ hσ hker).symm y = x ↔
      y = dQuot.map (R := R) φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- For a surjective homomorphism, membership of an image in a target dimension subgroup
is equivalent to the source augmentation difference lying in the source power plus the
kernel-relation ideal.  This is the group-level form of the algebraic preimage formula. -/
theorem dimension_sup_surjective
    (φ : G →* H) (hs : Function.Surjective φ) (n : ℕ) (g : G) :
    φ g ∈ dSubgro R H n ↔
      (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
        augmentationPower R G n ⊔ kRIdeal (R := R) φ := by
  rw [mem_dimensionSubgroup]
  have hmem := domain_sup_surjective
    (R := R) φ hs n (_root_.MonoidAlgebra.of R G g - 1)
  have hmap : (MonoidAlgebra.mapDomainAlgHom R R φ)
      (_root_.MonoidAlgebra.of R G g - 1) =
      (_root_.MonoidAlgebra.of R H (φ g) - 1 : MonoidAlgebra R H) := by
    rw [map_sub, map_one]
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapDomain_single]
    rfl
  rw [← hmap]
  exact hmem



/-- Projecting after the left-inclusion map on consecutive dimension quotients is the identity. -/
@[simp] theorem dNQuot.map_fst_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.fst G H) n).comp
        (dNQuot.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, dNQuot.map_id]

/-- Projecting after the right-inclusion map on consecutive dimension quotients is the identity. -/
@[simp] theorem dNQuot.map_snd_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.snd G H) n).comp
        (dNQuot.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.id (dSubgro R H n ⧸ dNTerm R H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, dNQuot.map_id]


/-- The next-quotient map induced by the first product projection is surjective. -/
theorem dNQuot.map_fst_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dNQuot.map (R := R) (MonoidHom.fst G H) n) := by
  intro q
  refine ⟨dNQuot.map (R := R) (MonoidHom.inl G H) n q, ?_⟩
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The next-quotient map induced by the second product projection is surjective. -/
theorem dNQuot.map_snd_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dNQuot.map (R := R) (MonoidHom.snd G H) n) := by
  intro q
  refine ⟨dNQuot.map (R := R) (MonoidHom.inr G H) n q, ?_⟩
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The first projection map on product consecutive dimension quotients has full range. -/
theorem dNQuot.range_mapfst_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dNQuot.map_fst_surjective (R := R) G H n)

/-- The second projection map on product consecutive dimension quotients has full range. -/
theorem dNQuot.range_mapsnd_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dNQuot.map_snd_surjective (R := R) G H n)

/-- The next-quotient map induced by the left product inclusion is injective. -/
theorem dNQuot.map_inl_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dNQuot.map (R := R) (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (dNQuot.map (R := R) (MonoidHom.fst G H) n)
      (dNQuot.map (R := R) (MonoidHom.inl G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  exact hleft.injective

/-- The next-quotient map induced by the right product inclusion is injective. -/
theorem dNQuot.map_inr_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dNQuot.map (R := R) (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (dNQuot.map (R := R) (MonoidHom.snd G H) n)
      (dNQuot.map (R := R) (MonoidHom.inr G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  exact hleft.injective

/-- The left product-inclusion map on consecutive dimension quotients has trivial kernel. -/
theorem dNQuot.ker_mapinl_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dNQuot.map_inl_injective (R := R) G H n)

/-- The right product-inclusion map on consecutive dimension quotients has trivial kernel. -/
theorem dNQuot.ker_mapinr_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dNQuot.map_inr_injective (R := R) G H n)

/-- The product equivalence carries the next-quotient map induced by the left inclusion
to the left inclusion of quotient factors. -/
@[simp] theorem dNQuot.prodEquiv_inl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.prodEquiv (R := R) G H n).toMonoidHom.comp
        (dNQuot.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The product equivalence carries the next-quotient map induced by the right inclusion
to the right inclusion of quotient factors. -/
@[simp] theorem dNQuot.prodEquiv_inr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.prodEquiv (R := R) G H n).toMonoidHom.comp
        (dNQuot.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The inverse product equivalence sends a left-factor consecutive quotient element to
the map induced by the left product inclusion. -/
@[simp] theorem dNQuot.prod_equiv_symminl
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.prodEquiv (R := R) G H n).symm (x, 1) =
      dNQuot.map (R := R) (MonoidHom.inl G H) n x := by
  apply (dNQuot.prodEquiv (R := R) G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : (dSubgro R G n ⧸
      dNTerm R G n) →*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n)) => f x)
    (dNQuot.prodEquiv_inl (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor consecutive quotient element to
the map induced by the right product inclusion. -/
@[simp] theorem dNQuot.prod_equiv_symminr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    (dNQuot.prodEquiv (R := R) G H n).symm (1, x) =
      dNQuot.map (R := R) (MonoidHom.inr G H) n x := by
  apply (dNQuot.prodEquiv (R := R) G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : (dSubgro R H n ⧸
      dNTerm R H n) →*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n)) => f x)
    (dNQuot.prodEquiv_inr (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The first projection after the product equivalence on consecutive dimension quotients
is the map induced by the first projection of groups. -/
@[simp] theorem dNQuot.prodEquiv_fst
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp
        (dNQuot.prodEquiv (R := R) G H n).toMonoidHom =
      dNQuot.map (R := R) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The second projection after the product equivalence on consecutive dimension quotients
is the map induced by the second projection of groups. -/
@[simp] theorem dNQuot.prodEquiv_snd
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp
        (dNQuot.prodEquiv (R := R) G H n).toMonoidHom =
      dNQuot.map (R := R) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl



/-- Product equivalence on consecutive dimension quotients is the pair of projections. -/
@[simp] theorem dNQuot.prodEquiv_apply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodEquiv (R := R) G H n x =
      (dNQuot.map (R := R) (MonoidHom.fst G H) n x,
        dNQuot.map (R := R) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : (dSubgro R (G × H) n ⧸
        dNTerm R (G × H) n) →*
        (dSubgro R G n ⧸ dNTerm R G n) => f x)
      (dNQuot.prodEquiv_fst (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : (dSubgro R (G × H) n ⧸
        dNTerm R (G × H) n) →*
        (dSubgro R H n ⧸ dNTerm R H n) => f x)
      (dNQuot.prodEquiv_snd (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h

/-- Every product consecutive dimension quotient element splits as the product of its
projected inclusion components. -/
theorem dNQuot.eq_inl_mulinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    x = dNQuot.map (R := R) (MonoidHom.inl G H) n
          (dNQuot.map (R := R) (MonoidHom.fst G H) n x) *
        dNQuot.map (R := R) (MonoidHom.inr G H) n
          (dNQuot.map (R := R) (MonoidHom.snd G H) n x) := by
  let e := dNQuot.prodEquiv (R := R) G H n
  have hf : (e x).1 = dNQuot.map (R := R) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : (dSubgro R (G × H) n ⧸
        dNTerm R (G × H) n) →*
        (dSubgro R G n ⧸ dNTerm R G n) => f x)
      (dNQuot.prodEquiv_fst (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = dNQuot.map (R := R) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : (dSubgro R (G × H) n ⧸
        dNTerm R (G × H) n) →*
        (dSubgro R H n ⧸ dNTerm R H n) => f x)
      (dNQuot.prodEquiv_snd (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = dNQuot.map (R := R) (MonoidHom.inl G H) n
          (dNQuot.map (R := R) (MonoidHom.fst G H) n x) *
        dNQuot.map (R := R) (MonoidHom.inr G H) n
          (dNQuot.map (R := R) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]


/-- Left- and right-inclusion images commute in a product consecutive dimension quotient. -/
theorem dNQuot.map_inlmul_inrcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) (MonoidHom.inl G H) n x *
        dNQuot.map (R := R) (MonoidHom.inr G H) n y =
      dNQuot.map (R := R) (MonoidHom.inr G H) n y *
        dNQuot.map (R := R) (MonoidHom.inl G H) n x := by
  let e := dNQuot.prodEquiv (R := R) G H n
  apply e.injective
  have hx : e (dNQuot.map (R := R) (MonoidHom.inl G H) n x) =
      (x, 1) := by
    have h := congrArg (fun f : (dSubgro R G n ⧸
        dNTerm R G n) →*
        ((dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n)) => f x)
      (dNQuot.prodEquiv_inl (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (dNQuot.map (R := R) (MonoidHom.inr G H) n y) =
      (1, y) := by
    have h := congrArg (fun f : (dSubgro R H n ⧸
        dNTerm R H n) →*
        ((dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n)) => f y)
      (dNQuot.prodEquiv_inr (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first consecutive dimension quotient is trivial. -/
@[simp] theorem dNQuot.map_fst_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.fst G H) n).comp
        (dNQuot.map (R := R) (MonoidHom.inr G H) n) =
      (1 : (dSubgro R H n ⧸ dNTerm R H n) →*
        (dSubgro R G n ⧸ dNTerm R G n)) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : (dSubgro R H n ⧸
      dNTerm R H n) →*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n)) => f x)
    (dNQuot.prodEquiv_inr (R := R) G H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, dNQuot.prodEquiv_apply] using hf

/-- Projecting the left-inclusion map to the second consecutive dimension quotient is trivial. -/
@[simp] theorem dNQuot.map_snd_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.snd G H) n).comp
        (dNQuot.map (R := R) (MonoidHom.inl G H) n) =
      (1 : (dSubgro R G n ⧸ dNTerm R G n) →*
        (dSubgro R H n ⧸ dNTerm R H n)) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : (dSubgro R G n ⧸
      dNTerm R G n) →*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n)) => f x)
    (dNQuot.prodEquiv_inl (R := R) G H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, dNQuot.prodEquiv_apply] using hs

@[simp] theorem dNQuot.map_fst_inrapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) (MonoidHom.fst G H) n
        (dNQuot.map (R := R) (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : (dSubgro R H n ⧸
      dNTerm R H n) →*
      (dSubgro R G n ⧸ dNTerm R G n) => f x)
    (dNQuot.map_fst_compinr (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem dNQuot.map_snd_inlapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) (MonoidHom.snd G H) n
        (dNQuot.map (R := R) (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : (dSubgro R G n ⧸
      dNTerm R G n) →*
      (dSubgro R H n ⧸ dNTerm R H n) => f x)
    (dNQuot.map_snd_compinl (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product consecutive dimension-quotient element lies in the right-inclusion range iff
its first projection is trivial. -/
theorem dNQuot.memrange_inriffmap_fsteqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    x ∈ (dNQuot.map (R := R) (MonoidHom.inr G H) n).range ↔
      dNQuot.map (R := R) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : (dSubgro R H n ⧸
        dNTerm R H n) →*
        (dSubgro R G n ⧸ dNTerm R G n) => f y)
      (dNQuot.map_fst_compinr (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dNQuot.map (R := R) (MonoidHom.snd G H) n x, ?_⟩
    have h := dNQuot.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product consecutive dimension-quotient element lies in the left-inclusion range iff
its second projection is trivial. -/
theorem dNQuot.memrange_inliffmap_sndeqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    x ∈ (dNQuot.map (R := R) (MonoidHom.inl G H) n).range ↔
      dNQuot.map (R := R) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : (dSubgro R G n ⧸
        dNTerm R G n) →*
        (dSubgro R H n ⧸ dNTerm R H n) => f y)
      (dNQuot.map_snd_compinl (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dNQuot.map (R := R) (MonoidHom.fst G H) n x, ?_⟩
    have h := dNQuot.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product consecutive dimension quotient is the
right-inclusion range. -/
theorem dNQuot.kermap_fsteq_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.fst G H) n).ker =
      (dNQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  ext x
  exact (dNQuot.memrange_inriffmap_fsteqone
    (R := R) G H n x).symm

/-- The kernel of the second projection on a product consecutive dimension quotient is the
left-inclusion range. -/
theorem dNQuot.kermap_sndeq_rangeinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.map (R := R) (MonoidHom.snd G H) n).ker =
      (dNQuot.map (R := R) (MonoidHom.inl G H) n).range := by
  ext x
  exact (dNQuot.memrange_inliffmap_sndeqone
    (R := R) G H n x).symm

/-- Swap transports the left-inclusion range to the right-inclusion range on
consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivmem_rangeinliff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) G H n x ∈
        (dNQuot.map (R := R) (MonoidHom.inr H G) n).range ↔
      x ∈ (dNQuot.map (R := R) (MonoidHom.inl G H) n).range := by
  rw [dNQuot.memrange_inriffmap_fsteqone (R := R) H G n,
    dNQuot.map_fstprod_commequiv (R := R) G H n,
    ← dNQuot.memrange_inliffmap_sndeqone (R := R) G H n]

/-- Swap transports the right-inclusion range to the left-inclusion range on
consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivmem_rangeinriff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) G H n x ∈
        (dNQuot.map (R := R) (MonoidHom.inl H G) n).range ↔
      x ∈ (dNQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [dNQuot.memrange_inliffmap_sndeqone (R := R) H G n,
    dNQuot.map_sndprod_commequiv (R := R) G H n,
    ← dNQuot.memrange_inriffmap_fsteqone (R := R) G H n]

/-- Swap transports the first-projection kernel to the second-projection kernel on
consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivmem_kerfstiff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) G H n x ∈
        (dNQuot.map (R := R) (MonoidHom.fst H G) n).ker ↔
      x ∈ (dNQuot.map (R := R) (MonoidHom.snd G H) n).ker := by
  change dNQuot.map (R := R) (MonoidHom.fst H G) n
        (dNQuot.prodCommEquiv (R := R) G H n x) = 1 ↔
      dNQuot.map (R := R) (MonoidHom.snd G H) n x = 1
  rw [dNQuot.map_fstprod_commequiv]

/-- Swap transports the second-projection kernel to the first-projection kernel on
consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivmem_kersndiff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodCommEquiv (R := R) G H n x ∈
        (dNQuot.map (R := R) (MonoidHom.snd H G) n).ker ↔
      x ∈ (dNQuot.map (R := R) (MonoidHom.fst G H) n).ker := by
  change dNQuot.map (R := R) (MonoidHom.snd H G) n
        (dNQuot.prodCommEquiv (R := R) G H n x) = 1 ↔
      dNQuot.map (R := R) (MonoidHom.fst G H) n x = 1
  rw [dNQuot.map_sndprod_commequiv]

/-- The left- and right-inclusion ranges in a product consecutive dimension quotient
meet only at `1`. -/
theorem dNQuot.eqone_memrangeinl_memrangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    {x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n}
    (hxL : x ∈ (dNQuot.map (R := R) (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (dNQuot.map (R := R) (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (dNQuot.memrange_inriffmap_fsteqone
    (R := R) G H n x).1 hxR
  have hsnd := (dNQuot.memrange_inliffmap_sndeqone
    (R := R) G H n x).1 hxL
  have h := dNQuot.eq_inl_mulinr (R := R) G H n x
  simpa [hfst, hsnd] using h

/-- The left- and right-inclusion ranges in a product consecutive dimension quotient
are disjoint. -/
theorem dNQuot.disjoint_rangeinl_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Disjoint (dNQuot.map (R := R) (MonoidHom.inl G H) n).range
      (dNQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact dNQuot.eqone_memrangeinl_memrangeinr
    (R := R) G H n hxL hxR

/-- Projecting after the left-inclusion map on dimension layer kernels is the identity. -/
@[simp] theorem dLKern.map_fst_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.fst G H) n).comp
        (dLKern.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.id (dLKern R G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← dLKern.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, dLKern.map_id]

/-- Projecting after the right-inclusion map on dimension layer kernels is the identity. -/
@[simp] theorem dLKern.map_snd_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.snd G H) n).comp
        (dLKern.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.id (dLKern R H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← dLKern.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, dLKern.map_id]

/-- The dimension layer-kernel map induced by the first product projection is surjective. -/
theorem dLKern.map_fst_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dLKern.map (R := R) (MonoidHom.fst G H) n) := by
  intro x
  refine ⟨dLKern.map (R := R) (MonoidHom.inl G H) n x, ?_⟩
  have h := congrArg (fun f : dLKern R G n →* dLKern R G n => f x)
    (dLKern.map_fst_compinl (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The dimension layer-kernel map induced by the second product projection is surjective. -/
theorem dLKern.map_snd_surjective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Surjective (dLKern.map (R := R) (MonoidHom.snd G H) n) := by
  intro x
  refine ⟨dLKern.map (R := R) (MonoidHom.inr G H) n x, ?_⟩
  have h := congrArg (fun f : dLKern R H n →* dLKern R H n => f x)
    (dLKern.map_snd_compinr (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The first projection map on product dimension layer kernels has full range. -/
theorem dLKern.range_mapfst_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dLKern.map_fst_surjective (R := R) G H n)

/-- The second projection map on product dimension layer kernels has full range. -/
theorem dLKern.range_mapsnd_eqtop
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (dLKern.map_snd_surjective (R := R) G H n)

/-- The dimension layer-kernel map induced by the left product inclusion is injective. -/
theorem dLKern.map_inl_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dLKern.map (R := R) (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (dLKern.map (R := R) (MonoidHom.fst G H) n)
      (dLKern.map (R := R) (MonoidHom.inl G H) n) := by
    intro x
    have h := congrArg (fun f : dLKern R G n →* dLKern R G n => f x)
      (dLKern.map_fst_compinl (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  exact hleft.injective

/-- The dimension layer-kernel map induced by the right product inclusion is injective. -/
theorem dLKern.map_inr_injective
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Function.Injective (dLKern.map (R := R) (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (dLKern.map (R := R) (MonoidHom.snd G H) n)
      (dLKern.map (R := R) (MonoidHom.inr G H) n) := by
    intro x
    have h := congrArg (fun f : dLKern R H n →* dLKern R H n => f x)
      (dLKern.map_snd_compinr (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  exact hleft.injective

/-- The left product-inclusion map on dimension layer kernels has trivial kernel. -/
theorem dLKern.ker_mapinl_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dLKern.map_inl_injective (R := R) G H n)

/-- The right product-inclusion map on dimension layer kernels has trivial kernel. -/
theorem dLKern.ker_mapinr_eqbot
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (dLKern.map_inr_injective (R := R) G H n)

/-- The product equivalence carries the layer-kernel map induced by the left inclusion
to the left inclusion of layer factors. -/
@[simp] theorem dLKern.prodEquiv_inl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prodEquiv (R := R) G H n).toMonoidHom.comp
        (dLKern.map (R := R) (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := G) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  have h := congrArg (fun (u : dSubgro R G n →* dLKern R (G × H) n) => u t)
    (dLKern.ofTerm_naturality (R := R) (φ := MonoidHom.inl G H) n)
  dsimp [MonoidHom.comp_apply] at h
  rw [h]
  rw [dLKern.prod_equiv_term]
  rfl

/-- The product equivalence carries the layer-kernel map induced by the right inclusion
to the right inclusion of layer factors. -/
@[simp] theorem dLKern.prodEquiv_inr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prodEquiv (R := R) G H n).toMonoidHom.comp
        (dLKern.map (R := R) (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := H) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  have h := congrArg (fun (u : dSubgro R H n →* dLKern R (G × H) n) => u t)
    (dLKern.ofTerm_naturality (R := R) (φ := MonoidHom.inr G H) n)
  dsimp [MonoidHom.comp_apply] at h
  rw [h]
  rw [dLKern.prod_equiv_term]
  rfl

/-- The inverse product equivalence sends a left-factor layer element to the map induced
by the left product inclusion. -/
@[simp] theorem dLKern.prod_equiv_symminl
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dLKern R G n) :
    (dLKern.prodEquiv (R := R) G H n).symm (x, 1) =
      dLKern.map (R := R) (MonoidHom.inl G H) n x := by
  apply (dLKern.prodEquiv (R := R) G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : dLKern R G n →*
      (dLKern R G n × dLKern R H n) => f x)
    (dLKern.prodEquiv_inl (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor layer element to the map induced
by the right product inclusion. -/
@[simp] theorem dLKern.prod_equiv_symminr
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dLKern R H n) :
    (dLKern.prodEquiv (R := R) G H n).symm (1, x) =
      dLKern.map (R := R) (MonoidHom.inr G H) n x := by
  apply (dLKern.prodEquiv (R := R) G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : dLKern R H n →*
      (dLKern R G n × dLKern R H n) => f x)
    (dLKern.prodEquiv_inr (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The first projection after the product equivalence on dimension layer kernels
is the map induced by the first projection of groups. -/
@[simp] theorem dLKern.prodEquiv_fst
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp
        (dLKern.prodEquiv (R := R) G H n).toMonoidHom =
      dLKern.map (R := R) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := G × H) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  rw [dLKern.prod_equiv_term]
  rfl

/-- The second projection after the product equivalence on dimension layer kernels
is the map induced by the second projection of groups. -/
@[simp] theorem dLKern.prodEquiv_snd
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp
        (dLKern.prodEquiv (R := R) G H n).toMonoidHom =
      dLKern.map (R := R) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := G × H) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  rw [dLKern.prod_equiv_term]
  rfl


/-- Product equivalence on dimension layer kernels is the pair of projection maps. -/
@[simp] theorem dLKern.prodEquiv_apply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodEquiv (R := R) G H n x =
      (dLKern.map (R := R) (MonoidHom.fst G H) n x,
        dLKern.map (R := R) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : dLKern R (G × H) n →*
        dLKern R G n => f x)
      (dLKern.prodEquiv_fst (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : dLKern R (G × H) n →*
        dLKern R H n => f x)
      (dLKern.prodEquiv_snd (R := R) G H n)
    simpa [MonoidHom.comp_apply] using h

/-- Every product dimension-layer element splits as the product of its two projected
inclusion components. -/
theorem dLKern.eq_inl_mulinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    x = dLKern.map (R := R) (MonoidHom.inl G H) n
          (dLKern.map (R := R) (MonoidHom.fst G H) n x) *
        dLKern.map (R := R) (MonoidHom.inr G H) n
          (dLKern.map (R := R) (MonoidHom.snd G H) n x) := by
  let e := dLKern.prodEquiv (R := R) G H n
  have hf : (e x).1 = dLKern.map (R := R) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : dLKern R (G × H) n →*
        dLKern R G n => f x)
      (dLKern.prodEquiv_fst (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = dLKern.map (R := R) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : dLKern R (G × H) n →*
        dLKern R H n => f x)
      (dLKern.prodEquiv_snd (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = dLKern.map (R := R) (MonoidHom.inl G H) n
          (dLKern.map (R := R) (MonoidHom.fst G H) n x) *
        dLKern.map (R := R) (MonoidHom.inr G H) n
          (dLKern.map (R := R) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]
/-- Left- and right-inclusion images commute in a product dimension layer kernel. -/
theorem dLKern.map_inlmul_inrcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R G n) (y : dLKern R H n) :
    dLKern.map (R := R) (MonoidHom.inl G H) n x *
        dLKern.map (R := R) (MonoidHom.inr G H) n y =
      dLKern.map (R := R) (MonoidHom.inr G H) n y *
        dLKern.map (R := R) (MonoidHom.inl G H) n x := by
  let e := dLKern.prodEquiv (R := R) G H n
  apply e.injective
  have hx : e (dLKern.map (R := R) (MonoidHom.inl G H) n x) =
      (x, 1) := by
    have h := congrArg (fun f : dLKern R G n →*
        (dLKern R G n × dLKern R H n) => f x)
      (dLKern.prodEquiv_inl (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (dLKern.map (R := R) (MonoidHom.inr G H) n y) =
      (1, y) := by
    have h := congrArg (fun f : dLKern R H n →*
        (dLKern R G n × dLKern R H n) => f y)
      (dLKern.prodEquiv_inr (R := R) G H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first dimension layer kernel is trivial. -/
@[simp] theorem dLKern.map_fst_compinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.fst G H) n).comp
        (dLKern.map (R := R) (MonoidHom.inr G H) n) =
      (1 : dLKern R H n →* dLKern R G n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : dLKern R H n →*
      (dLKern R G n × dLKern R H n) => f x)
    (dLKern.prodEquiv_inr (R := R) G H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, dLKern.prodEquiv_apply] using hf

/-- Projecting the left-inclusion map to the second dimension layer kernel is trivial. -/
@[simp] theorem dLKern.map_snd_compinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.snd G H) n).comp
        (dLKern.map (R := R) (MonoidHom.inl G H) n) =
      (1 : dLKern R G n →* dLKern R H n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : dLKern R G n →*
      (dLKern R G n × dLKern R H n) => f x)
    (dLKern.prodEquiv_inl (R := R) G H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, dLKern.prodEquiv_apply] using hs

@[simp] theorem dLKern.map_fst_inrapply
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dLKern R H n) :
    dLKern.map (R := R) (MonoidHom.fst G H) n
        (dLKern.map (R := R) (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : dLKern R H n →*
      dLKern R G n => f x)
    (dLKern.map_fst_compinr (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem dLKern.map_snd_inlapply
    (G H : Type*) [Group G] [Group H] (n : ℕ) (x : dLKern R G n) :
    dLKern.map (R := R) (MonoidHom.snd G H) n
        (dLKern.map (R := R) (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : dLKern R G n →*
      dLKern R H n => f x)
    (dLKern.map_snd_compinl (R := R) G H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product dimension-layer element lies in the right-inclusion range iff its first
projection is trivial. -/
theorem dLKern.memrange_inriffmap_fsteqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    x ∈ (dLKern.map (R := R) (MonoidHom.inr G H) n).range ↔
      dLKern.map (R := R) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : dLKern R H n →*
        dLKern R G n => f y)
      (dLKern.map_fst_compinr (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dLKern.map (R := R) (MonoidHom.snd G H) n x, ?_⟩
    have h := dLKern.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product dimension-layer element lies in the left-inclusion range iff its second
projection is trivial. -/
theorem dLKern.memrange_inliffmap_sndeqone
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    x ∈ (dLKern.map (R := R) (MonoidHom.inl G H) n).range ↔
      dLKern.map (R := R) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : dLKern R G n →*
        dLKern R H n => f y)
      (dLKern.map_snd_compinl (R := R) G H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨dLKern.map (R := R) (MonoidHom.fst G H) n x, ?_⟩
    have h := dLKern.eq_inl_mulinr (R := R) G H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product dimension layer kernel is the
right-inclusion range. -/
theorem dLKern.kermap_fsteq_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.fst G H) n).ker =
      (dLKern.map (R := R) (MonoidHom.inr G H) n).range := by
  ext x
  exact (dLKern.memrange_inriffmap_fsteqone
    (R := R) G H n x).symm

/-- The kernel of the second projection on a product dimension layer kernel is the
left-inclusion range. -/
theorem dLKern.kermap_sndeq_rangeinl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.map (R := R) (MonoidHom.snd G H) n).ker =
      (dLKern.map (R := R) (MonoidHom.inl G H) n).range := by
  ext x
  exact (dLKern.memrange_inliffmap_sndeqone
    (R := R) G H n x).symm

/-- Swap transports the left-inclusion range to the right-inclusion range on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivmem_rangeinliff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) G H n x ∈
        (dLKern.map (R := R) (MonoidHom.inr H G) n).range ↔
      x ∈ (dLKern.map (R := R) (MonoidHom.inl G H) n).range := by
  rw [dLKern.memrange_inriffmap_fsteqone (R := R) H G n,
    dLKern.map_fstprod_commequiv (R := R) G H n,
    ← dLKern.memrange_inliffmap_sndeqone (R := R) G H n]

/-- Swap transports the right-inclusion range to the left-inclusion range on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivmem_rangeinriff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) G H n x ∈
        (dLKern.map (R := R) (MonoidHom.inl H G) n).range ↔
      x ∈ (dLKern.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [dLKern.memrange_inliffmap_sndeqone (R := R) H G n,
    dLKern.map_sndprod_commequiv (R := R) G H n,
    ← dLKern.memrange_inriffmap_fsteqone (R := R) G H n]

/-- Swap transports the first-projection kernel to the second-projection kernel on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivmem_kerfstiff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) G H n x ∈
        (dLKern.map (R := R) (MonoidHom.fst H G) n).ker ↔
      x ∈ (dLKern.map (R := R) (MonoidHom.snd G H) n).ker := by
  change dLKern.map (R := R) (MonoidHom.fst H G) n
        (dLKern.prodCommEquiv (R := R) G H n x) = 1 ↔
      dLKern.map (R := R) (MonoidHom.snd G H) n x = 1
  rw [dLKern.map_fstprod_commequiv]

/-- Swap transports the second-projection kernel to the first-projection kernel on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivmem_kersndiff
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodCommEquiv (R := R) G H n x ∈
        (dLKern.map (R := R) (MonoidHom.snd H G) n).ker ↔
      x ∈ (dLKern.map (R := R) (MonoidHom.fst G H) n).ker := by
  change dLKern.map (R := R) (MonoidHom.snd H G) n
        (dLKern.prodCommEquiv (R := R) G H n x) = 1 ↔
      dLKern.map (R := R) (MonoidHom.fst G H) n x = 1
  rw [dLKern.map_sndprod_commequiv]

/-- The left- and right-inclusion ranges in a product dimension layer kernel meet only at `1`. -/
theorem dLKern.eqone_memrangeinl_memrangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    {x : dLKern R (G × H) n}
    (hxL : x ∈ (dLKern.map (R := R) (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (dLKern.map (R := R) (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (dLKern.memrange_inriffmap_fsteqone
    (R := R) G H n x).1 hxR
  have hsnd := (dLKern.memrange_inliffmap_sndeqone
    (R := R) G H n x).1 hxL
  have h := dLKern.eq_inl_mulinr (R := R) G H n x
  simpa [hfst, hsnd] using h


/-- The left- and right-inclusion ranges in a product dimension layer kernel are disjoint. -/
theorem dLKern.disjoint_rangeinl_rangeinr
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Disjoint (dLKern.map (R := R) (MonoidHom.inl G H) n).range
      (dLKern.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact dLKern.eqone_memrangeinl_memrangeinr
    (R := R) G H n hxL hxR


end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (R : Type*) [CommRing R] (G : Type*) [Group G]

/-- Dimension subgroups are characteristic: every automorphism preserves them. -/
instance dSubgro.instCharacteristic (n : ℕ) :
    (dSubgro R G n).Characteristic where
  fixed e := by
    ext g
    constructor
    · intro hg
      change e g ∈ dSubgro R G n at hg
      have h := dimension_subgroup_comap R e.symm.toMonoidHom n hg
      simpa using h
    · intro hg
      change e g ∈ dSubgro R G n
      exact dimension_subgroup_comap R e.toMonoidHom n hg

/-- A group isomorphism carries dimension subgroups onto dimension subgroups. -/
theorem dimension_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dSubgro R G n).map e.toMonoidHom = dSubgro R H n := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact dimension_subgroup_comap R e.toMonoidHom n
  · intro h hh
    refine ⟨e.symm h, ?_, ?_⟩
    · have hinv := dimension_subgroup_comap R e.symm.toMonoidHom n hh
      simpa using hinv
    · simp

/-- A group isomorphism pulls back dimension subgroups to dimension subgroups. -/
theorem dimension_comap_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dSubgro R H n).comap e.toMonoidHom = dSubgro R G n := by
  apply le_antisymm
  · intro g hg
    have h := dimension_subgroup_comap R e.symm.toMonoidHom n hg
    simpa using h
  · exact dimension_subgroup_comap R e.toMonoidHom n

/-- Membership in a dimension term is invariant under a group equivalence.  This
non-simp iff is often more convenient than rewriting a whole `map`/`comap`
statement when transporting depth hypotheses. -/
theorem dimension_subgroup_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (g : G) :
    e g ∈ dSubgro R H n ↔ g ∈ dSubgro R G n := by
  constructor
  · intro hg
    have h := dimension_subgroup_comap R e.symm.toMonoidHom n hg
    simpa using h
  · intro hg
    exact dimension_subgroup_comap R e.toMonoidHom n hg

/-- Symmetric form of `dimension_subgroup_equiv`, useful when the element
already lives in the target group. -/
theorem dimension_subgroup_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (h : H) :
    e.symm h ∈ dSubgro R G n ↔ h ∈ dSubgro R H n := by
  simpa using (dimension_subgroup_equiv (R := R) (G := H) e.symm n h)

/-- Symmetric predicate-level transport of dimension depth across a group equivalence. -/
theorem dimension_least_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (h : H) :
    dimensionDepthLeast R G (e.symm h) n ↔ dimensionDepthLeast R H h n := by
  exact dimension_subgroup_symm (R := R) (G := G) e n h




/-- Isomorphic groups have isomorphic dimension quotients. -/
noncomputable def dQuot.congr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    dQuot R G n ≃* dQuot R H n :=
  QuotientGroup.congr (dSubgro R G n) (dSubgro R H n) e
    (dimension_equiv R G e n)

@[simp] theorem dQuot.congr_mk {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (g : G) :
    dQuot.congr R G e n
        (QuotientGroup.mk' (dSubgro R G n) g) =
      QuotientGroup.mk' (dSubgro R H n) (e g) := rfl

@[simp] theorem dQuot.congr_monoid_hom {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dQuot.congr R G e n).toMonoidHom =
      dQuot.map (R := R) e.toMonoidHom n := by
  ext g
  rfl

@[simp] theorem dQuot.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dQuot.congr R G e n).symm =
      dQuot.congr R H e.symm n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl

/-- Inverse-application criterion for congruences of dimension quotients. -/
theorem dQuot.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (y : dQuot R H n)
    (x : dQuot R G n) :
    (dQuot.congr R G e n).symm y = x ↔
      y = dQuot.congr R G e n x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem dQuot.congr_refl (n : ℕ) :
    dQuot.congr R G (MulEquiv.refl G) n =
      MulEquiv.refl (dQuot R G n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem dQuot.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dQuot.congr R G e n).trans (dQuot.congr R H f n) =
      dQuot.congr R G (e.trans f) n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Coordinate swap as an equivalence of dimension quotients.  This is the
`dQuot.congr` specialization for `MulEquiv.prodComm`, packaged under
the quotient namespace for use in product-coherence statements. -/
noncomputable def dQuot.prodCommEquiv (H : Type*) [Group H] (n : ℕ) :
    dQuot R (G × H) n ≃* dQuot R (H × G) n :=
  dQuot.congr R (G × H)
    (MulEquiv.prodComm : G × H ≃* H × G) n

@[simp] theorem dQuot.prod_comm_equivmk (H : Type*) [Group H]
    (n : ℕ) (g : G) (h : H) :
    dQuot.prodCommEquiv R G H n
        (QuotientGroup.mk' (dSubgro R (G × H) n) (g, h)) =
      QuotientGroup.mk' (dSubgro R (H × G) n) (h, g) := rfl

@[simp] theorem dQuot.prod_commequiv_monoidhom (H : Type*) [Group H]
    (n : ℕ) :
    (dQuot.prodCommEquiv R G H n).toMonoidHom =
      dQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := by
  exact dQuot.congr_monoid_hom (R := R) (G := G × H)
    (MulEquiv.prodComm : G × H ≃* H × G) n

@[simp] theorem dQuot.prod_commequiv_symmeq (H : Type*) [Group H]
    (n : ℕ) :
    (dQuot.prodCommEquiv R G H n).symm =
      dQuot.prodCommEquiv R H G n := by
  change (dQuot.congr R (G × H)
      (MulEquiv.prodComm : G × H ≃* H × G) n).symm =
    dQuot.congr R (H × G)
      (MulEquiv.prodComm : H × G ≃* G × H) n
  ext q
  refine QuotientGroup.induction_on q ?_
  intro hg
  rcases hg with ⟨h, g⟩
  rfl

@[simp] theorem dQuot.prod_commequiv_applyapply (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R H G n
        (dQuot.prodCommEquiv R G H n x) = x := by
  rw [← dQuot.prod_commequiv_symmeq (R := R) (G := G) H n]
  exact MulEquiv.symm_apply_apply (dQuot.prodCommEquiv R G H n) x

@[simp] theorem dQuot.prod_commequiv_symmmk (H : Type*) [Group H]
    (n : ℕ) (h : H) (g : G) :
    (dQuot.prodCommEquiv R G H n).symm
        (QuotientGroup.mk' (dSubgro R (H × G) n) (h, g)) =
      QuotientGroup.mk' (dSubgro R (G × H) n) (g, h) := by
  rw [dQuot.prod_commequiv_symmeq]
  rfl

/-- Reassociation as an equivalence of dimension quotients. -/
noncomputable def dQuot.prodAssocEquiv (H K : Type*) [Group H] [Group K]
    (n : ℕ) :
    dQuot R ((G × H) × K) n ≃*
      dQuot R (G × (H × K)) n :=
  dQuot.congr R ((G × H) × K)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n

@[simp] theorem dQuot.prod_assoc_equivmk (H K : Type*) [Group H] [Group K]
    (n : ℕ) (g : G) (h : H) (k : K) :
    dQuot.prodAssocEquiv R G H K n
        (QuotientGroup.mk' (dSubgro R ((G × H) × K) n) ((g, h), k)) =
      QuotientGroup.mk' (dSubgro R (G × (H × K)) n) (g, (h, k)) := rfl

@[simp] theorem dQuot.prod_assocequiv_monoidhom (H K : Type*)
    [Group H] [Group K] (n : ℕ) :
    (dQuot.prodAssocEquiv R G H K n).toMonoidHom =
      dQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := by
  exact dQuot.congr_monoid_hom (R := R) (G := (G × H) × K)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n

@[simp] theorem dQuot.prod_assocequiv_symmeq (H K : Type*)
    [Group H] [Group K] (n : ℕ) :
    (dQuot.prodAssocEquiv R G H K n).symm =
      dQuot.congr R (G × (H × K))
        (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm n := by
  change (dQuot.congr R ((G × H) × K)
      (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n).symm = _
  simp only [dQuot.congr_symm]

@[simp] theorem dQuot.prod_assocequiv_symmmk (H K : Type*)
    [Group H] [Group K] (n : ℕ) (g : G) (h : H) (k : K) :
    (dQuot.prodAssocEquiv R G H K n).symm
        (QuotientGroup.mk' (dSubgro R (G × (H × K)) n) (g, (h, k))) =
      QuotientGroup.mk' (dSubgro R ((G × H) × K) n) ((g, h), k) := by
  rw [dQuot.prod_assocequiv_symmeq]
  rfl

/-- Applying the quotient swap is the same as the functorial map induced by
coordinate swap. -/
@[simp] theorem dQuot.prod_comm_equivapply (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R G H n x =
      dQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := by
  change ((dQuot.prodCommEquiv R G H n).toMonoidHom) x = _
  rw [dQuot.prod_commequiv_monoidhom]

/-- Applying the quotient associator is the same as the functorial map induced by
the group associator. -/
@[simp] theorem dQuot.prod_assoc_equivapply (H K : Type*)
    [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.prodAssocEquiv R G H K n x =
      dQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := by
  change ((dQuot.prodAssocEquiv R G H K n).toMonoidHom) x = _
  rw [dQuot.prod_assocequiv_monoidhom]

/-- Applying the inverse quotient associator is the functorial map induced by the
inverse group associator. -/
@[simp] theorem dQuot.prod_assocequiv_symmapply (H K : Type*)
    [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    (dQuot.prodAssocEquiv R G H K n).symm x =
      dQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x := by
  rw [dQuot.prod_assocequiv_symmeq]
  change (dQuot.congr R (G × (H × K))
      (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm n).toMonoidHom x = _
  rw [dQuot.congr_monoid_hom]

/-- Projecting the swapped quotient on the first factor equals the original
second projection. -/
@[simp] theorem dQuot.map_fstprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.map (R := R) (MonoidHom.fst H G) n
        (dQuot.prodCommEquiv R G H n x) =
      dQuot.map (R := R) (MonoidHom.snd G H) n x := by
  change ((dQuot.map (R := R) (MonoidHom.fst H G) n).comp
      (dQuot.prodCommEquiv R G H n).toMonoidHom) x = _
  rw [dQuot.prod_commequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.fst H G) n]
  rfl

/-- Projecting the swapped quotient on the second factor equals the original
first projection. -/
@[simp] theorem dQuot.map_sndprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.map (R := R) (MonoidHom.snd H G) n
        (dQuot.prodCommEquiv R G H n x) =
      dQuot.map (R := R) (MonoidHom.fst G H) n x := by
  change ((dQuot.map (R := R) (MonoidHom.snd H G) n).comp
      (dQuot.prodCommEquiv R G H n).toMonoidHom) x = _
  rw [dQuot.prod_commequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    (MonoidHom.snd H G) n]
  rfl

/-- Under quotient swap, the left-inclusion range becomes the right-inclusion range. -/
theorem dQuot.prodcomm_equivmem_rangeinliff (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R G H n x ∈
        (dQuot.map (R := R) (MonoidHom.inr H G) n).range ↔
      x ∈ (dQuot.map (R := R) (MonoidHom.inl G H) n).range := by
  rw [dQuot.memrange_inriffmap_fsteqone (R := R) H G n,
    dQuot.map_fstprod_commequiv (R := R) (G := G) H n,
    ← dQuot.memrange_inliffmap_sndeqone (R := R) G H n]

/-- Under quotient swap, the right-inclusion range becomes the left-inclusion range. -/
theorem dQuot.prodcomm_equivmem_rangeinriff (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R G H n x ∈
        (dQuot.map (R := R) (MonoidHom.inl H G) n).range ↔
      x ∈ (dQuot.map (R := R) (MonoidHom.inr G H) n).range := by
  rw [dQuot.memrange_inliffmap_sndeqone (R := R) H G n,
    dQuot.map_sndprod_commequiv (R := R) (G := G) H n,
    ← dQuot.memrange_inriffmap_fsteqone (R := R) G H n]

/-- Under quotient swap, the first-projection kernel becomes the second-projection kernel. -/
theorem dQuot.prodcomm_equivmem_kerfstiff (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R G H n x ∈
        (dQuot.map (R := R) (MonoidHom.fst H G) n).ker ↔
      x ∈ (dQuot.map (R := R) (MonoidHom.snd G H) n).ker := by
  change dQuot.map (R := R) (MonoidHom.fst H G) n
        (dQuot.prodCommEquiv R G H n x) = 1 ↔
      dQuot.map (R := R) (MonoidHom.snd G H) n x = 1
  rw [dQuot.map_fstprod_commequiv]

/-- Under quotient swap, the second-projection kernel becomes the first-projection kernel. -/
theorem dQuot.prodcomm_equivmem_kersndiff (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R (G × H) n) :
    dQuot.prodCommEquiv R G H n x ∈
        (dQuot.map (R := R) (MonoidHom.snd H G) n).ker ↔
      x ∈ (dQuot.map (R := R) (MonoidHom.fst G H) n).ker := by
  change dQuot.map (R := R) (MonoidHom.snd H G) n
        (dQuot.prodCommEquiv R G H n x) = 1 ↔
      dQuot.map (R := R) (MonoidHom.fst G H) n x = 1
  rw [dQuot.map_sndprod_commequiv]

/-- The quotient swap sends the left inclusion to the right inclusion. -/
@[simp] theorem dQuot.prod_commequiv_mapinl (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R G n) :
    dQuot.prodCommEquiv R G H n
        (dQuot.map (R := R) (MonoidHom.inl G H) n x) =
      dQuot.map (R := R) (MonoidHom.inr H G) n x := by
  change ((dQuot.prodCommEquiv R G H n).toMonoidHom.comp
      (dQuot.map (R := R) (MonoidHom.inl G H) n)) x = _
  rw [dQuot.prod_commequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inl G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

/-- The quotient swap sends the right inclusion to the left inclusion. -/
@[simp] theorem dQuot.prod_commequiv_mapinr (H : Type*) [Group H]
    (n : ℕ) (x : dQuot R H n) :
    dQuot.prodCommEquiv R G H n
        (dQuot.map (R := R) (MonoidHom.inr G H) n x) =
      dQuot.map (R := R) (MonoidHom.inl H G) n x := by
  change ((dQuot.prodCommEquiv R G H n).toMonoidHom.comp
      (dQuot.map (R := R) (MonoidHom.inr G H) n)) x = _
  rw [dQuot.prod_commequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inr G H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n]
  rfl

/-- Automorphisms of `G` act on each dimension quotient. -/
noncomputable def dQuot.mulAutMap (n : ℕ) :
    MulAut G →* MulAut (dQuot R G n) where
  toFun e := dQuot.congr R G e n
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl

@[simp] theorem dQuot.mul_autmap_applymk (n : ℕ)
    (e : MulAut G) (g : G) :
    dQuot.mulAutMap R G n e
        (QuotientGroup.mk' (dSubgro R G n) g) =
      QuotientGroup.mk' (dSubgro R G n) (e g) := rfl

/-- Naturality of the product equivalence for consecutive dimension quotients. -/
theorem dNQuot.prodEquiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (dNQuot.prodEquiv (R := R) G₂ H₂ n).toMonoidHom.comp
        (dNQuot.map (R := R) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (dNQuot.map (R := R) f n)
        (dNQuot.map (R := R) g n)).comp
        (dNQuot.prodEquiv (R := R) G₁ H₁ n).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl


/-- Associator followed by its inverse is identity on consecutive quotients. -/
@[simp] theorem dNQuot.mapprod_assocsymm_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (dNQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) →*
      (dSubgro R ((G × H) × K) n ⧸
        dNTerm R ((G × H) × K) n) => f x)
    (dNQuot.map_id (R := R) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Mapping by the product associator and then its inverse is the identity on layer kernels. -/
@[simp] theorem dLKern.mapprod_assocsymm_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (dLKern.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dLKern R ((G × H) × K) n →*
      dLKern R ((G × H) × K) n => f x)
    (dLKern.map_id (R := R) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on consecutive quotients. -/
@[simp] theorem dNQuot.mapprod_assocprod_assocsymm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × H × K) n ⧸
      dNTerm R (G × H × K) n) :
    dNQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (dNQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (dSubgro R (G × H × K) n ⧸
      dNTerm R (G × H × K) n) →*
      (dSubgro R (G × H × K) n ⧸
        dNTerm R (G × H × K) n) => f x)
    (dNQuot.map_id (R := R) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on layer kernels. -/
@[simp] theorem dLKern.mapprod_assocprod_assocsymm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × H × K) n) :
    dLKern.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (dLKern.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dLKern R (G × H × K) n →*
      dLKern R (G × H × K) n => f x)
    (dLKern.map_id (R := R) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Associativity coherence for consecutive dimension-quotient product equivalences. -/
theorem dNQuot.prod_equiv_assocnatural
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap
        (MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n))
        (dNQuot.prodEquiv (R := R) H K n).toMonoidHom).comp
      (dNQuot.prodEquiv (R := R) G (H × K) n).toMonoidHom).comp
        (dNQuot.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        ((dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n)) ×
          (dSubgro R K n ⧸ dNTerm R K n) ≃*
        (dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n) ×
          (dSubgro R K n ⧸ dNTerm R K n)).toMonoidHom).comp
      ((MonoidHom.prodMap
        (dNQuot.prodEquiv (R := R) G H n).toMonoidHom
        (MonoidHom.id (dSubgro R K n ⧸ dNTerm R K n))).comp
        (dNQuot.prodEquiv (R := R) (G × H) K n).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro ghk
  rfl

/-- Pointwise associativity coherence for consecutive dimension quotient products. -/
@[simp] theorem dNQuot.prod_equiv_assocapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    (MonoidHom.prodMap
        (MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n))
        (dNQuot.prodEquiv (R := R) H K n).toMonoidHom)
      (dNQuot.prodEquiv (R := R) G (H × K) n
        (dNQuot.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        ((dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n)) ×
          (dSubgro R K n ⧸ dNTerm R K n) ≃*
        (dSubgro R G n ⧸ dNTerm R G n) ×
          (dSubgro R H n ⧸ dNTerm R H n) ×
          (dSubgro R K n ⧸ dNTerm R K n))
        ((MonoidHom.prodMap
          (dNQuot.prodEquiv (R := R) G H n).toMonoidHom
          (MonoidHom.id (dSubgro R K n ⧸ dNTerm R K n)))
          (dNQuot.prodEquiv (R := R) (G × H) K n x)) := by
  have h := congrArg (fun f : (dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) →*
      ((dSubgro R G n ⧸ dNTerm R G n) ×
        (dSubgro R H n ⧸ dNTerm R H n) ×
        (dSubgro R K n ⧸ dNTerm R K n)) => f x)
    (dNQuot.prod_equiv_assocnatural (R := R) G H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Inverse-form associativity coherence for consecutive dimension quotient products. -/
@[simp] theorem dNQuot.prod_equivassoc_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (a : dSubgro R G n ⧸ dNTerm R G n)
    (b : dSubgro R H n ⧸ dNTerm R H n)
    (c : dSubgro R K n ⧸ dNTerm R K n) :
    dNQuot.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((dNQuot.prodEquiv (R := R) (G × H) K n).symm
        ((dNQuot.prodEquiv (R := R) G H n).symm (a, b), c)) =
      (dNQuot.prodEquiv (R := R) G (H × K) n).symm
        (a, (dNQuot.prodEquiv (R := R) H K n).symm (b, c)) := by
  apply (dNQuot.prodEquiv (R := R) G (H × K) n).injective
  let x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n :=
    (dNQuot.prodEquiv (R := R) (G × H) K n).symm
      ((dNQuot.prodEquiv (R := R) G H n).symm (a, b), c)
  have h := dNQuot.prod_equiv_assocapply (R := R) G H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (dNQuot.prodEquiv (R := R) H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Pointwise form of naturality for consecutive dimension quotient product equivalences. -/
@[simp] theorem dNQuot.prod_equiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dSubgro R (G₁ × H₁) n ⧸
      dNTerm R (G₁ × H₁) n) :
    dNQuot.prodEquiv (R := R) G₂ H₂ n
        (dNQuot.map (R := R) (MonoidHom.prodMap f g) n x) =
      (dNQuot.map (R := R) f n
          (dNQuot.prodEquiv (R := R) G₁ H₁ n x).1,
        dNQuot.map (R := R) g n
          (dNQuot.prodEquiv (R := R) G₁ H₁ n x).2) := by
  have h := congrArg (fun F : (dSubgro R (G₁ × H₁) n ⧸
      dNTerm R (G₁ × H₁) n) →*
      ((dSubgro R G₂ n ⧸ dNTerm R G₂ n) ×
        (dSubgro R H₂ n ⧸ dNTerm R H₂ n)) => F x)
    (dNQuot.prodEquiv_naturality (R := R) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality on inverse product representatives for consecutive dimension quotients. -/
@[simp] theorem dNQuot.prod_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : (dSubgro R G₁ n ⧸ dNTerm R G₁ n) ×
      (dSubgro R H₁ n ⧸ dNTerm R H₁ n)) :
    dNQuot.map (R := R) (MonoidHom.prodMap f g) n
        ((dNQuot.prodEquiv (R := R) G₁ H₁ n).symm y) =
      (dNQuot.prodEquiv (R := R) G₂ H₂ n).symm
        (dNQuot.map (R := R) f n y.1,
          dNQuot.map (R := R) g n y.2) := by
  apply (dNQuot.prodEquiv (R := R) G₂ H₂ n).injective
  have h := dNQuot.prod_equiv_naturalapply (R := R) f g n
    ((dNQuot.prodEquiv (R := R) G₁ H₁ n).symm y)
  simpa using h

/-- Product-commuting the factors is compatible with the consecutive dimension-quotient
product equivalence. -/
theorem dNQuot.prod_equiv_swapnatural
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dNQuot.prodEquiv (R := R) H G n).toMonoidHom.comp
        (dNQuot.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm :
          (dSubgro R G n ⧸ dNTerm R G n) ×
            (dSubgro R H n ⧸ dNTerm R H n) ≃*
          (dSubgro R H n ⧸ dNTerm R H n) ×
            (dSubgro R G n ⧸ dNTerm R G n)).toMonoidHom).comp
        (dNQuot.prodEquiv (R := R) G H n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro gh
  rfl

/-- Product-commuting the factors is compatible with the dimension layer-kernel
product equivalence. -/
theorem dLKern.prod_equiv_swapnatural
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prodEquiv (R := R) H G n).toMonoidHom.comp
        (dLKern.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm : dLKern R G n × dLKern R H n ≃*
          dLKern R H n × dLKern R G n).toMonoidHom).comp
        (dLKern.prodEquiv (R := R) G H n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
        Function.comp_apply, dLKern.prodEquiv_apply, MulEquiv.coe_prodComm,
        Prod.swap_prod_mk]
    have hh : (MonoidHom.fst H G).comp
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) = MonoidHom.snd G H := by
      ext z
      rfl
    have hm : (dLKern.map (R := R) (MonoidHom.fst H G) n).comp
        (dLKern.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
        dLKern.map (R := R) (MonoidHom.snd G H) n := by
      rw [← dLKern.map_comp (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) (MonoidHom.fst H G) n, hh]
    exact congrArg
      (fun f : dLKern R (G × H) n →* dLKern R H n => f x) hm
  · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
        Function.comp_apply, dLKern.prodEquiv_apply, MulEquiv.coe_prodComm,
        Prod.swap_prod_mk]
    have hh : (MonoidHom.snd H G).comp
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) = MonoidHom.fst G H := by
      ext z
      rfl
    have hm : (dLKern.map (R := R) (MonoidHom.snd H G) n).comp
        (dLKern.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
        dLKern.map (R := R) (MonoidHom.fst G H) n := by
      rw [← dLKern.map_comp (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) (MonoidHom.snd H G) n, hh]
    exact congrArg
      (fun f : dLKern R (G × H) n →* dLKern R G n => f x) hm

/-- Applying the product-commuting map twice on consecutive dimension quotients is the identity. -/
@[simp] theorem dNQuot.map_prodcomm_prodcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.map (R := R)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (dNQuot.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (dSubgro R (G × H) n ⧸
      dNTerm R (G × H) n) →*
      (dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) => f x)
    (dNQuot.map_id (R := R) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Applying the product-commuting map twice on dimension layer kernels is the identity. -/
@[simp] theorem dLKern.map_prodcomm_prodcomm
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.map (R := R)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (dLKern.map (R := R)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : dLKern R (G × H) n →*
      dLKern R (G × H) n => f x)
    (dLKern.map_id (R := R) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Pointwise form of swap-naturality for consecutive dimension quotient product equivalences. -/
@[simp] theorem dNQuot.prod_equiv_swapapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dSubgro R (G × H) n ⧸ dNTerm R (G × H) n) :
    dNQuot.prodEquiv (R := R) H G n
        (dNQuot.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((dNQuot.prodEquiv (R := R) G H n x).2,
        (dNQuot.prodEquiv (R := R) G H n x).1) := by
  have h := congrArg (fun f : (dSubgro R (G × H) n ⧸
      dNTerm R (G × H) n) →*
      ((dSubgro R H n ⧸ dNTerm R H n) ×
        (dSubgro R G n ⧸ dNTerm R G n)) => f x)
    (dNQuot.prod_equiv_swapnatural (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h

/-- Pointwise form of swap-naturality for dimension layer-kernel product equivalences. -/
@[simp] theorem dLKern.prod_equiv_swapapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : dLKern R (G × H) n) :
    dLKern.prodEquiv (R := R) H G n
        (dLKern.map (R := R)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((dLKern.prodEquiv (R := R) G H n x).2,
        (dLKern.prodEquiv (R := R) G H n x).1) := by
  have h := congrArg (fun f : dLKern R (G × H) n →*
      (dLKern R H n × dLKern R G n) => f x)
    (dLKern.prod_equiv_swapnatural (R := R) G H n)
  simpa [MonoidHom.comp_apply] using h

/-- Associativity coherence for dimension layer-kernel product equivalences. -/
theorem dLKern.prod_equiv_assocnatural
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap (MonoidHom.id (dLKern R G n))
        (dLKern.prodEquiv (R := R) H K n).toMonoidHom).comp
      (dLKern.prodEquiv (R := R) G (H × K) n).toMonoidHom).comp
        (dLKern.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        (dLKern R G n × dLKern R H n) ×
          dLKern R K n ≃*
        dLKern R G n × dLKern R H n ×
          dLKern R K n).toMonoidHom).comp
      ((MonoidHom.prodMap (dLKern.prodEquiv (R := R) G H n).toMonoidHom
        (MonoidHom.id (dLKern R K n))).comp
        (dLKern.prodEquiv (R := R) (G × H) K n).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := (G × H) × K) n x with ⟨t, rfl⟩
  apply Prod.ext
  · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
      MonoidHom.coe_prodMap, MonoidHom.coe_id, MonoidHom.coe_coe,
      Function.comp_apply, dLKern.prodEquiv_apply,
      Prod.map_apply, id_eq, MulEquiv.coe_prodAssoc, Equiv.prodAssoc_apply]
    have hmap : (dLKern.map (R := R) (MonoidHom.fst G (H × K)) n).comp
          (dLKern.map (R := R)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
        (dLKern.map (R := R) (MonoidHom.fst G H) n).comp
          (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n) := by
      rw [← dLKern.map_comp (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
        (MonoidHom.fst G (H × K)) n]
      rw [← dLKern.map_comp (R := R)
        (MonoidHom.fst (G × H) K) (MonoidHom.fst G H) n]
      congr 1
    exact congrArg (fun f : dLKern R ((G × H) × K) n →*
      dLKern R G n => f ((dLKern.ofTerm (R := R) n) t)) hmap
  · apply Prod.ext
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
      MonoidHom.coe_prodMap, MonoidHom.coe_id, MonoidHom.coe_coe,
      Function.comp_apply, dLKern.prodEquiv_apply,
      Prod.map_apply, id_eq, MulEquiv.coe_prodAssoc, Equiv.prodAssoc_apply]
      have hmap : (dLKern.map (R := R) (MonoidHom.fst H K) n).comp
            ((dLKern.map (R := R) (MonoidHom.snd G (H × K)) n).comp
              (dLKern.map (R := R)
                ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n)) =
          (dLKern.map (R := R) (MonoidHom.snd G H) n).comp
            (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n) := by
        rw [← dLKern.map_comp (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
          (MonoidHom.snd G (H × K)) n]
        rw [← dLKern.map_comp (R := R)
          ((MonoidHom.snd G (H × K)).comp
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
          (MonoidHom.fst H K) n]
        rw [← dLKern.map_comp (R := R)
          (MonoidHom.fst (G × H) K) (MonoidHom.snd G H) n]
        congr 1
      exact congrArg (fun f : dLKern R ((G × H) × K) n →*
        dLKern R H n => f ((dLKern.ofTerm (R := R) n) t)) hmap
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
      MonoidHom.coe_prodMap, MonoidHom.coe_id, MonoidHom.coe_coe,
      Function.comp_apply, dLKern.prodEquiv_apply,
      Prod.map_apply, id_eq, MulEquiv.coe_prodAssoc, Equiv.prodAssoc_apply]
      have hmap : (dLKern.map (R := R) (MonoidHom.snd H K) n).comp
            ((dLKern.map (R := R) (MonoidHom.snd G (H × K)) n).comp
              (dLKern.map (R := R)
                ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n)) =
          dLKern.map (R := R) (MonoidHom.snd (G × H) K) n := by
        rw [← dLKern.map_comp (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
          (MonoidHom.snd G (H × K)) n]
        rw [← dLKern.map_comp (R := R)
          ((MonoidHom.snd G (H × K)).comp
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
          (MonoidHom.snd H K) n]
        congr 1
      exact congrArg (fun f : dLKern R ((G × H) × K) n →*
        dLKern R K n => f ((dLKern.ofTerm (R := R) n) t)) hmap


/-- Pointwise associativity coherence for dimension layer-kernel product equivalences. -/
@[simp] theorem dLKern.prod_equiv_assocapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    (MonoidHom.prodMap (MonoidHom.id (dLKern R G n))
        (dLKern.prodEquiv (R := R) H K n).toMonoidHom)
      (dLKern.prodEquiv (R := R) G (H × K) n
        (dLKern.map (R := R)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        (dLKern R G n × dLKern R H n) ×
          dLKern R K n ≃*
        dLKern R G n × dLKern R H n ×
          dLKern R K n)
        ((MonoidHom.prodMap
          (dLKern.prodEquiv (R := R) G H n).toMonoidHom
          (MonoidHom.id (dLKern R K n)))
          (dLKern.prodEquiv (R := R) (G × H) K n x)) := by
  have h := congrArg (fun f : dLKern R ((G × H) × K) n →*
      (dLKern R G n × dLKern R H n ×
        dLKern R K n) => f x)
    (dLKern.prod_equiv_assocnatural (R := R) G H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Inverse-form associativity coherence for dimension layer-kernel product equivalences. -/
@[simp] theorem dLKern.prod_equivassoc_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (a : dLKern R G n) (b : dLKern R H n)
    (c : dLKern R K n) :
    dLKern.map (R := R)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((dLKern.prodEquiv (R := R) (G × H) K n).symm
        ((dLKern.prodEquiv (R := R) G H n).symm (a, b), c)) =
      (dLKern.prodEquiv (R := R) G (H × K) n).symm
        (a, (dLKern.prodEquiv (R := R) H K n).symm (b, c)) := by
  apply (dLKern.prodEquiv (R := R) G (H × K) n).injective
  let x : dLKern R ((G × H) × K) n :=
    (dLKern.prodEquiv (R := R) (G × H) K n).symm
      ((dLKern.prodEquiv (R := R) G H n).symm (a, b), c)
  have h := dLKern.prod_equiv_assocapply (R := R) G H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (dLKern.prodEquiv (R := R) H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Naturality of the product equivalence for dimension layer kernels. -/
theorem dLKern.prodEquiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (dLKern.prodEquiv (R := R) G₂ H₂ n).toMonoidHom.comp
        (dLKern.map (R := R) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (dLKern.map (R := R) f n)
        (dLKern.map (R := R) g n)).comp
        (dLKern.prodEquiv (R := R) G₁ H₁ n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rcases dLKern.ofTerm_surjective (R := R) (G := G₁ × H₁) n x with ⟨t, rfl⟩
  have hprod := congrArg (fun (u : dSubgro R (G₁ × H₁) n →* 
      dLKern R (G₂ × H₂) n) => u t)
    (dLKern.ofTerm_naturality (R := R) (φ := MonoidHom.prodMap f g) n)
  have hf := congrArg (fun (u : dSubgro R G₁ n →* dLKern R G₂ n) =>
      u ((dimensionSubgroupProd R G₁ H₁ n t).1))
    (dLKern.ofTerm_naturality (R := R) (φ := f) n)
  have hg := congrArg (fun (u : dSubgro R H₁ n →* dLKern R H₂ n) =>
      u ((dimensionSubgroupProd R G₁ H₁ n t).2))
    (dLKern.ofTerm_naturality (R := R) (φ := g) n)
  dsimp [MonoidHom.comp_apply] at hprod hf hg ⊢
  rw [hprod]
  rw [dLKern.prod_equiv_term]
  rw [dLKern.prod_equiv_term]
  dsimp [Prod.map]
  rw [hf, hg]
  rfl


/-- Pointwise form of naturality for dimension layer-kernel product equivalences. -/
@[simp] theorem dLKern.prod_equiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dLKern R (G₁ × H₁) n) :
    dLKern.prodEquiv (R := R) G₂ H₂ n
        (dLKern.map (R := R) (MonoidHom.prodMap f g) n x) =
      (dLKern.map (R := R) f n
          (dLKern.prodEquiv (R := R) G₁ H₁ n x).1,
        dLKern.map (R := R) g n
          (dLKern.prodEquiv (R := R) G₁ H₁ n x).2) := by
  have h := congrArg (fun F : dLKern R (G₁ × H₁) n →*
      (dLKern R G₂ n × dLKern R H₂ n) => F x)
    (dLKern.prodEquiv_naturality (R := R) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality on inverse product representatives for dimension layer kernels. -/
@[simp] theorem dLKern.prod_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : dLKern R G₁ n × dLKern R H₁ n) :
    dLKern.map (R := R) (MonoidHom.prodMap f g) n
        ((dLKern.prodEquiv (R := R) G₁ H₁ n).symm y) =
      (dLKern.prodEquiv (R := R) G₂ H₂ n).symm
        (dLKern.map (R := R) f n y.1,
          dLKern.map (R := R) g n y.2) := by
  apply (dLKern.prodEquiv (R := R) G₂ H₂ n).injective
  have h := dLKern.prod_equiv_naturalapply (R := R) f g n
    ((dLKern.prodEquiv (R := R) G₁ H₁ n).symm y)
  simpa using h



/-- The first projection after reassociating a dimension quotient is the iterated
first projection. -/
@[simp] theorem dQuot.mapfst_fstprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.map (R := R) (MonoidHom.fst G (H × K)) n
        (dQuot.prodAssocEquiv R G H K n x) =
      dQuot.map (R := R) (MonoidHom.fst G H) n
        (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dQuot.map (R := R) (MonoidHom.fst G (H × K)) n).comp
      (dQuot.prodAssocEquiv R G H K n).toMonoidHom) x =
    ((dQuot.map (R := R) (MonoidHom.fst G H) n).comp
      (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.fst G (H × K)) n]
  rw [← dQuot.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.fst G H) n]
  rfl

/-- The last projection after reassociating a dimension quotient is the original
last projection. -/
@[simp] theorem dQuot.mapsnd_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.map (R := R) (MonoidHom.snd H K) n
        (dQuot.map (R := R) (MonoidHom.snd G (H × K)) n
          (dQuot.prodAssocEquiv R G H K n x)) =
      dQuot.map (R := R) (MonoidHom.snd (G × H) K) n x := by
  change ((dQuot.map (R := R) (MonoidHom.snd H K) n).comp
      ((dQuot.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dQuot.prodAssocEquiv R G H K n).toMonoidHom)) x =
    (dQuot.map (R := R) (MonoidHom.snd (G × H) K) n) x
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dQuot.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.snd H K) n]
  rfl


/-- The first projection after reassociating a consecutive dimension quotient is
 the iterated first projection. -/
@[simp] theorem dNQuot.mapfst_fstprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.map (R := R) (MonoidHom.fst G (H × K)) n
        (dNQuot.prodAssocEquiv (R := R) G H K n x) =
      dNQuot.map (R := R) (MonoidHom.fst G H) n
        (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dNQuot.map (R := R) (MonoidHom.fst G (H × K)) n).comp
      (dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom) x =
    ((dNQuot.map (R := R) (MonoidHom.fst G H) n).comp
      (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.fst G (H × K)) n]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.fst G H) n]
  rfl

/-- The last projection after reassociating a consecutive dimension quotient is
 the original last projection. -/
@[simp] theorem dNQuot.mapsnd_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.map (R := R) (MonoidHom.snd H K) n
        (dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n
          (dNQuot.prodAssocEquiv (R := R) G H K n x)) =
      dNQuot.map (R := R) (MonoidHom.snd (G × H) K) n x := by
  change ((dNQuot.map (R := R) (MonoidHom.snd H K) n).comp
      ((dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom)) x =
    (dNQuot.map (R := R) (MonoidHom.snd (G × H) K) n) x
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dNQuot.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.snd H K) n]
  rfl

/-- The first projection after reassociating a dimension layer kernel is the
 iterated first projection. -/
@[simp] theorem dLKern.mapfst_fstprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.map (R := R) (MonoidHom.fst G (H × K)) n
        (dLKern.prodAssocEquiv (R := R) G H K n x) =
      dLKern.map (R := R) (MonoidHom.fst G H) n
        (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dLKern.map (R := R) (MonoidHom.fst G (H × K)) n).comp
      (dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom) x =
    ((dLKern.map (R := R) (MonoidHom.fst G H) n).comp
      (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.fst G (H × K)) n]
  rw [← dLKern.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.fst G H) n]
  rfl

/-- The last projection after reassociating a dimension layer kernel is the
 original last projection. -/
@[simp] theorem dLKern.mapsnd_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.map (R := R) (MonoidHom.snd H K) n
        (dLKern.map (R := R) (MonoidHom.snd G (H × K)) n
          (dLKern.prodAssocEquiv (R := R) G H K n x)) =
      dLKern.map (R := R) (MonoidHom.snd (G × H) K) n x := by
  change ((dLKern.map (R := R) (MonoidHom.snd H K) n).comp
      ((dLKern.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom)) x =
    (dLKern.map (R := R) (MonoidHom.snd (G × H) K) n) x
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dLKern.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.snd H K) n]
  rfl


/-- The middle projection after reassociating a dimension quotient is obtained by
projecting first to `G × H` and then to `H`. -/
@[simp] theorem dQuot.mapfst_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.map (R := R) (MonoidHom.fst H K) n
        (dQuot.map (R := R) (MonoidHom.snd G (H × K)) n
          (dQuot.prodAssocEquiv R G H K n x)) =
      dQuot.map (R := R) (MonoidHom.snd G H) n
        (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dQuot.map (R := R) (MonoidHom.fst H K) n).comp
      ((dQuot.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dQuot.prodAssocEquiv R G H K n).toMonoidHom)) x =
    ((dQuot.map (R := R) (MonoidHom.snd G H) n).comp
      (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dQuot.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.fst H K) n]
  rw [← dQuot.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.snd G H) n]
  rfl

/-- The middle projection after reassociating a consecutive dimension quotient. -/
@[simp] theorem dNQuot.mapfst_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.map (R := R) (MonoidHom.fst H K) n
        (dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n
          (dNQuot.prodAssocEquiv (R := R) G H K n x)) =
      dNQuot.map (R := R) (MonoidHom.snd G H) n
        (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dNQuot.map (R := R) (MonoidHom.fst H K) n).comp
      ((dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom)) x =
    ((dNQuot.map (R := R) (MonoidHom.snd G H) n).comp
      (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dNQuot.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.fst H K) n]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.snd G H) n]
  rfl

/-- The middle projection after reassociating a dimension layer kernel. -/
@[simp] theorem dLKern.mapfst_sndprod_assocequivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.map (R := R) (MonoidHom.fst H K) n
        (dLKern.map (R := R) (MonoidHom.snd G (H × K)) n
          (dLKern.prodAssocEquiv (R := R) G H K n x)) =
      dLKern.map (R := R) (MonoidHom.snd G H) n
        (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n x) := by
  change ((dLKern.map (R := R) (MonoidHom.fst H K) n).comp
      ((dLKern.map (R := R) (MonoidHom.snd G (H × K)) n).comp
        (dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom)) x =
    ((dLKern.map (R := R) (MonoidHom.snd G H) n).comp
      (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n)) x
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    (MonoidHom.snd G (H × K)) n]
  rw [← dLKern.map_comp (R := R)
    ((MonoidHom.snd G (H × K)).comp
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom))
    (MonoidHom.fst H K) n]
  rw [← dLKern.map_comp (R := R) (MonoidHom.fst (G × H) K)
    (MonoidHom.snd G H) n]
  rfl


/-- Reassociation sends the left-left inclusion to the outer left inclusion on
ordinary dimension quotients. -/
@[simp] theorem dQuot.prodassoc_equivmap_inlinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R G n) :
    dQuot.prodAssocEquiv R G H K n
        (dQuot.map (R := R) (MonoidHom.inl (G × H) K) n
          (dQuot.map (R := R) (MonoidHom.inl G H) n x)) =
      dQuot.map (R := R) (MonoidHom.inl G (H × K)) n x := by
  change ((dQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dQuot.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dQuot.map (R := R) (MonoidHom.inl G H) n))) x = _
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dQuot.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inl G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rfl

/-- Reassociation sends the left-right inclusion to the inner-left inclusion on
ordinary dimension quotients. -/
@[simp] theorem dQuot.prodassoc_equivmap_inlinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R H n) :
    dQuot.prodAssocEquiv R G H K n
        (dQuot.map (R := R) (MonoidHom.inl (G × H) K) n
          (dQuot.map (R := R) (MonoidHom.inr G H) n x)) =
      dQuot.map (R := R) (MonoidHom.inr G (H × K)) n
        (dQuot.map (R := R) (MonoidHom.inl H K) n x) := by
  change ((dQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dQuot.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dQuot.map (R := R) (MonoidHom.inr G H) n))) x =
    ((dQuot.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dQuot.map (R := R) (MonoidHom.inl H K) n)) x
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dQuot.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inr G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inl H K)
    (MonoidHom.inr G (H × K)) n]
  rfl

/-- Reassociation sends the right inclusion to the inner-right inclusion on
ordinary dimension quotients. -/
@[simp] theorem dQuot.prod_assocequiv_mapinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R K n) :
    dQuot.prodAssocEquiv R G H K n
        (dQuot.map (R := R) (MonoidHom.inr (G × H) K) n x) =
      dQuot.map (R := R) (MonoidHom.inr G (H × K)) n
        (dQuot.map (R := R) (MonoidHom.inr H K) n x) := by
  change ((dQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      (dQuot.map (R := R) (MonoidHom.inr (G × H) K) n)) x =
    ((dQuot.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dQuot.map (R := R) (MonoidHom.inr H K) n)) x
  rw [dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inr (G × H) K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dQuot.map_comp (R := R) (MonoidHom.inr H K)
    (MonoidHom.inr G (H × K)) n]
  rfl


/-- Reassociation sends the left-left inclusion to the outer left inclusion on
consecutive dimension quotients. -/
@[simp] theorem dNQuot.prodassoc_equivmap_inlinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.prodAssocEquiv (R := R) G H K n
        (dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n
          (dNQuot.map (R := R) (MonoidHom.inl G H) n x)) =
      dNQuot.map (R := R) (MonoidHom.inl G (H × K)) n x := by
  change ((dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      ((dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dNQuot.map (R := R) (MonoidHom.inl G H) n))) x = _
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dNQuot.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inl G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rfl

@[simp] theorem dNQuot.prodassoc_equivmap_inlinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.prodAssocEquiv (R := R) G H K n
        (dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n
          (dNQuot.map (R := R) (MonoidHom.inr G H) n x)) =
      dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n
        (dNQuot.map (R := R) (MonoidHom.inl H K) n x) := by
  change ((dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      ((dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dNQuot.map (R := R) (MonoidHom.inr G H) n))) x =
    ((dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dNQuot.map (R := R) (MonoidHom.inl H K) n)) x
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dNQuot.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inr G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inl H K)
    (MonoidHom.inr G (H × K)) n]
  rfl

@[simp] theorem dNQuot.prod_assocequiv_mapinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R K n ⧸ dNTerm R K n) :
    dNQuot.prodAssocEquiv (R := R) G H K n
        (dNQuot.map (R := R) (MonoidHom.inr (G × H) K) n x) =
      dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n
        (dNQuot.map (R := R) (MonoidHom.inr H K) n x) := by
  change ((dNQuot.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      (dNQuot.map (R := R) (MonoidHom.inr (G × H) K) n)) x =
    ((dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dNQuot.map (R := R) (MonoidHom.inr H K) n)) x
  rw [dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inr (G × H) K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.inr H K)
    (MonoidHom.inr G (H × K)) n]
  rfl

/-- Reassociation sends the left-left inclusion to the outer left inclusion on
layer kernels. -/
@[simp] theorem dLKern.prodassoc_equivmap_inlinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R G n) :
    dLKern.prodAssocEquiv (R := R) G H K n
        (dLKern.map (R := R) (MonoidHom.inl (G × H) K) n
          (dLKern.map (R := R) (MonoidHom.inl G H) n x)) =
      dLKern.map (R := R) (MonoidHom.inl G (H × K)) n x := by
  change ((dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      ((dLKern.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dLKern.map (R := R) (MonoidHom.inl G H) n))) x = _
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inl G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dLKern.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inl G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rfl

@[simp] theorem dLKern.prodassoc_equivmap_inlinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R H n) :
    dLKern.prodAssocEquiv (R := R) G H K n
        (dLKern.map (R := R) (MonoidHom.inl (G × H) K) n
          (dLKern.map (R := R) (MonoidHom.inr G H) n x)) =
      dLKern.map (R := R) (MonoidHom.inr G (H × K)) n
        (dLKern.map (R := R) (MonoidHom.inl H K) n x) := by
  change ((dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      ((dLKern.map (R := R) (MonoidHom.inl (G × H) K) n).comp
        (dLKern.map (R := R) (MonoidHom.inr G H) n))) x =
    ((dLKern.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dLKern.map (R := R) (MonoidHom.inl H K) n)) x
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inr G H)
    (MonoidHom.inl (G × H) K) n]
  rw [← dLKern.map_comp (R := R)
    ((MonoidHom.inl (G × H) K).comp (MonoidHom.inr G H))
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inl H K)
    (MonoidHom.inr G (H × K)) n]
  rfl

@[simp] theorem dLKern.prod_assocequiv_mapinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R K n) :
    dLKern.prodAssocEquiv (R := R) G H K n
        (dLKern.map (R := R) (MonoidHom.inr (G × H) K) n x) =
      dLKern.map (R := R) (MonoidHom.inr G (H × K)) n
        (dLKern.map (R := R) (MonoidHom.inr H K) n x) := by
  change ((dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom.comp
      (dLKern.map (R := R) (MonoidHom.inr (G × H) K) n)) x =
    ((dLKern.map (R := R) (MonoidHom.inr G (H × K)) n).comp
      (dLKern.map (R := R) (MonoidHom.inr H K) n)) x
  rw [dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inr (G × H) K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  rw [← dLKern.map_comp (R := R) (MonoidHom.inr H K)
    (MonoidHom.inr G (H × K)) n]
  rfl


/-- Inverse reassociation sends the outer left inclusion back to the left-left inclusion. -/
@[simp] theorem dQuot.prodassoc_equivsymm_mapinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R G n) :
    (dQuot.prodAssocEquiv R G H K n).symm
        (dQuot.map (R := R) (MonoidHom.inl G (H × K)) n x) =
      dQuot.map (R := R) (MonoidHom.inl (G × H) K) n
        (dQuot.map (R := R) (MonoidHom.inl G H) n x) := by
  apply (dQuot.prodAssocEquiv R G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dQuot.prodassoc_equivmap_inlinl (R := R) G H K n x).symm


@[simp] theorem dQuot.prodassoc_equivsymm_mapinrinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R H n) :
    (dQuot.prodAssocEquiv R G H K n).symm
        (dQuot.map (R := R) (MonoidHom.inr G (H × K)) n
          (dQuot.map (R := R) (MonoidHom.inl H K) n x)) =
      dQuot.map (R := R) (MonoidHom.inl (G × H) K) n
        (dQuot.map (R := R) (MonoidHom.inr G H) n x) := by
  apply (dQuot.prodAssocEquiv R G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dQuot.prodassoc_equivmap_inlinr (R := R) G H K n x).symm

@[simp] theorem dQuot.prodassoc_equivsymm_mapinrinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R K n) :
    (dQuot.prodAssocEquiv R G H K n).symm
        (dQuot.map (R := R) (MonoidHom.inr G (H × K)) n
          (dQuot.map (R := R) (MonoidHom.inr H K) n x)) =
      dQuot.map (R := R) (MonoidHom.inr (G × H) K) n x := by
  apply (dQuot.prodAssocEquiv R G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dQuot.prod_assocequiv_mapinr (R := R) G H K n x).symm

@[simp] theorem dNQuot.prodassoc_equivsymm_mapinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm
        (dNQuot.map (R := R) (MonoidHom.inl G (H × K)) n x) =
      dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n
        (dNQuot.map (R := R) (MonoidHom.inl G H) n x) := by
  apply (dNQuot.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dNQuot.prodassoc_equivmap_inlinl (R := R) G H K n x).symm

@[simp] theorem dNQuot.prodassoc_equivsymm_mapinrinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm
        (dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n
          (dNQuot.map (R := R) (MonoidHom.inl H K) n x)) =
      dNQuot.map (R := R) (MonoidHom.inl (G × H) K) n
        (dNQuot.map (R := R) (MonoidHom.inr G H) n x) := by
  apply (dNQuot.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dNQuot.prodassoc_equivmap_inlinr (R := R) G H K n x).symm

@[simp] theorem dNQuot.prodassoc_equivsymm_mapinrinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R K n ⧸ dNTerm R K n) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm
        (dNQuot.map (R := R) (MonoidHom.inr G (H × K)) n
          (dNQuot.map (R := R) (MonoidHom.inr H K) n x)) =
      dNQuot.map (R := R) (MonoidHom.inr (G × H) K) n x := by
  apply (dNQuot.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dNQuot.prod_assocequiv_mapinr (R := R) G H K n x).symm

@[simp] theorem dLKern.prodassoc_equivsymm_mapinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R G n) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm
        (dLKern.map (R := R) (MonoidHom.inl G (H × K)) n x) =
      dLKern.map (R := R) (MonoidHom.inl (G × H) K) n
        (dLKern.map (R := R) (MonoidHom.inl G H) n x) := by
  apply (dLKern.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dLKern.prodassoc_equivmap_inlinl (R := R) G H K n x).symm

@[simp] theorem dLKern.prodassoc_equivsymm_mapinrinl
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R H n) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm
        (dLKern.map (R := R) (MonoidHom.inr G (H × K)) n
          (dLKern.map (R := R) (MonoidHom.inl H K) n x)) =
      dLKern.map (R := R) (MonoidHom.inl (G × H) K) n
        (dLKern.map (R := R) (MonoidHom.inr G H) n x) := by
  apply (dLKern.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dLKern.prodassoc_equivmap_inlinr (R := R) G H K n x).symm

@[simp] theorem dLKern.prodassoc_equivsymm_mapinrinr
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R K n) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm
        (dLKern.map (R := R) (MonoidHom.inr G (H × K)) n
          (dLKern.map (R := R) (MonoidHom.inr H K) n x)) =
      dLKern.map (R := R) (MonoidHom.inr (G × H) K) n x := by
  apply (dLKern.prodAssocEquiv (R := R) G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (dLKern.prod_assocequiv_mapinr (R := R) G H K n x).symm


/-- Naturality square for equivalence-induced maps on ordinary dimension quotients. -/
theorem dQuot.congr_map_naturality
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ) :
    (dQuot.map (R := R) ψ n).comp
        (dQuot.congr R A e₁ n).toMonoidHom =
      (dQuot.congr R C e₂ n).toMonoidHom.comp
        (dQuot.map (R := R) φ n) := by
  rw [dQuot.congr_monoid_hom, dQuot.congr_monoid_hom]
  rw [← dQuot.map_comp (R := R) e₁.toMonoidHom ψ n]
  rw [← dQuot.map_comp (R := R) φ e₂.toMonoidHom n]
  rw [h]

/-- Pointwise naturality square for equivalence-induced maps on ordinary dimension quotients. -/
theorem dQuot.congr_map_naturalapply
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ)
    (x : dQuot R A n) :
    dQuot.map (R := R) ψ n (dQuot.congr R A e₁ n x) =
      dQuot.congr R C e₂ n (dQuot.map (R := R) φ n x) := by
  exact congrFun (congrArg DFunLike.coe
    (dQuot.congr_map_naturality (R := R) e₁ e₂ φ ψ n h)) x

/-- Naturality square for equivalence-induced maps on consecutive dimension quotients. -/
theorem dNQuot.congr_map_naturality
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ) :
    (dNQuot.map (R := R) ψ n).comp
        (dNQuot.congr (R := R) e₁ n).toMonoidHom =
      (dNQuot.congr (R := R) e₂ n).toMonoidHom.comp
        (dNQuot.map (R := R) φ n) := by
  rw [dNQuot.congr_monoid_hom, dNQuot.congr_monoid_hom]
  rw [← dNQuot.map_comp (R := R) e₁.toMonoidHom ψ n]
  rw [← dNQuot.map_comp (R := R) φ e₂.toMonoidHom n]
  rw [h]

/-- Pointwise naturality square for consecutive dimension quotients. -/
theorem dNQuot.congr_map_naturalapply
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ)
    (x : dSubgro R A n ⧸ dNTerm R A n) :
    dNQuot.map (R := R) ψ n
        (dNQuot.congr (R := R) e₁ n x) =
      dNQuot.congr (R := R) e₂ n
        (dNQuot.map (R := R) φ n x) := by
  exact congrFun (congrArg DFunLike.coe
    (dNQuot.congr_map_naturality (R := R) e₁ e₂ φ ψ n h)) x

/-- Naturality square for equivalence-induced maps on dimension layer kernels. -/
theorem dLKern.congr_map_naturality
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ) :
    (dLKern.map (R := R) ψ n).comp
        (dLKern.congr (R := R) e₁ n).toMonoidHom =
      (dLKern.congr (R := R) e₂ n).toMonoidHom.comp
        (dLKern.map (R := R) φ n) := by
  rw [dLKern.congr_monoid_hom, dLKern.congr_monoid_hom]
  rw [← dLKern.map_comp (R := R) e₁.toMonoidHom ψ n]
  rw [← dLKern.map_comp (R := R) φ e₂.toMonoidHom n]
  rw [h]

/-- Pointwise naturality square for dimension layer kernels. -/
theorem dLKern.congr_map_naturalapply
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e₁ : A ≃* B) (e₂ : C ≃* D) (φ : A →* C) (ψ : B →* D) (n : ℕ)
    (h : ψ.comp e₁.toMonoidHom = e₂.toMonoidHom.comp φ)
    (x : dLKern R A n) :
    dLKern.map (R := R) ψ n
        (dLKern.congr (R := R) e₁ n x) =
      dLKern.congr (R := R) e₂ n
        (dLKern.map (R := R) φ n x) := by
  exact congrFun (congrArg DFunLike.coe
    (dLKern.congr_map_naturality (R := R) e₁ e₂ φ ψ n h)) x


/-- Forward then inverse reassociation is identity on ordinary dimension quotients. -/
@[simp] theorem dQuot.prodassoc_equivsymm_applyapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    (dQuot.prodAssocEquiv R G H K n).symm
        (dQuot.prodAssocEquiv R G H K n x) = x :=
  MulEquiv.symm_apply_apply (dQuot.prodAssocEquiv R G H K n) x

/-- Inverse then forward reassociation is identity on ordinary dimension quotients. -/
@[simp] theorem dQuot.prodassoc_equivapply_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.prodAssocEquiv R G H K n
        ((dQuot.prodAssocEquiv R G H K n).symm x) = x :=
  MulEquiv.apply_symm_apply (dQuot.prodAssocEquiv R G H K n) x

@[simp] theorem dNQuot.prodassoc_equivsymm_eqapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm
        (dNQuot.prodAssocEquiv (R := R) G H K n x) = x :=
  MulEquiv.symm_apply_apply (dNQuot.prodAssocEquiv (R := R) G H K n) x

@[simp] theorem dNQuot.prodassoc_equivapply_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.prodAssocEquiv (R := R) G H K n
        ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x) = x :=
  MulEquiv.apply_symm_apply (dNQuot.prodAssocEquiv (R := R) G H K n) x

@[simp] theorem dLKern.prodassoc_equivsymm_applyapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm
        (dLKern.prodAssocEquiv (R := R) G H K n x) = x :=
  MulEquiv.symm_apply_apply (dLKern.prodAssocEquiv (R := R) G H K n) x

@[simp] theorem dLKern.prodassoc_equivapply_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.prodAssocEquiv (R := R) G H K n
        ((dLKern.prodAssocEquiv (R := R) G H K n).symm x) = x :=
  MulEquiv.apply_symm_apply (dLKern.prodAssocEquiv (R := R) G H K n) x


/-- First-coordinate projection formula for the inverse ordinary quotient associator. -/
@[simp] theorem dQuot.mapfst_fstpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.map (R := R) (MonoidHom.fst G H) n
        (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dQuot.prodAssocEquiv R G H K n).symm x)) =
      dQuot.map (R := R) (MonoidHom.fst G (H × K)) n x := by
  have h := dQuot.mapfst_fstprod_assocequivapply (R := R) G H K n
    ((dQuot.prodAssocEquiv R G H K n).symm x)
  rw [dQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm


@[simp] theorem dQuot.mapfst_sndpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.map (R := R) (MonoidHom.snd G H) n
        (dQuot.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dQuot.prodAssocEquiv R G H K n).symm x)) =
      dQuot.map (R := R) (MonoidHom.fst H K) n
        (dQuot.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dQuot.mapfst_sndprod_assocequivapply (R := R) G H K n
    ((dQuot.prodAssocEquiv R G H K n).symm x)
  rw [dQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dQuot.mapsnd_prodassoc_equivsymmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.map (R := R) (MonoidHom.snd (G × H) K) n
        ((dQuot.prodAssocEquiv R G H K n).symm x) =
      dQuot.map (R := R) (MonoidHom.snd H K) n
        (dQuot.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dQuot.mapsnd_sndprod_assocequivapply (R := R) G H K n
    ((dQuot.prodAssocEquiv R G H K n).symm x)
  rw [dQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dNQuot.mapfst_fstpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.map (R := R) (MonoidHom.fst G H) n
        (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)) =
      dNQuot.map (R := R) (MonoidHom.fst G (H × K)) n x := by
  have h := dNQuot.mapfst_fstprod_assocequivapply (R := R) G H K n
    ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dNQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dNQuot.mapfst_sndpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.map (R := R) (MonoidHom.snd G H) n
        (dNQuot.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)) =
      dNQuot.map (R := R) (MonoidHom.fst H K) n
        (dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dNQuot.mapfst_sndprod_assocequivapply (R := R) G H K n
    ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dNQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dNQuot.mapsnd_prodassoc_equivsymmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.map (R := R) (MonoidHom.snd (G × H) K) n
        ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x) =
      dNQuot.map (R := R) (MonoidHom.snd H K) n
        (dNQuot.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dNQuot.mapsnd_sndprod_assocequivapply (R := R) G H K n
    ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dNQuot.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dLKern.mapfst_fstpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.map (R := R) (MonoidHom.fst G H) n
        (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)) =
      dLKern.map (R := R) (MonoidHom.fst G (H × K)) n x := by
  have h := dLKern.mapfst_fstprod_assocequivapply (R := R) G H K n
    ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dLKern.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dLKern.mapfst_sndpr_equiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.map (R := R) (MonoidHom.snd G H) n
        (dLKern.map (R := R) (MonoidHom.fst (G × H) K) n
          ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)) =
      dLKern.map (R := R) (MonoidHom.fst H K) n
        (dLKern.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dLKern.mapfst_sndprod_assocequivapply (R := R) G H K n
    ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dLKern.prodassoc_equivapply_symmapply] at h
  exact h.symm

@[simp] theorem dLKern.mapsnd_prodassoc_equivsymmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.map (R := R) (MonoidHom.snd (G × H) K) n
        ((dLKern.prodAssocEquiv (R := R) G H K n).symm x) =
      dLKern.map (R := R) (MonoidHom.snd H K) n
        (dLKern.map (R := R) (MonoidHom.snd G (H × K)) n x) := by
  have h := dLKern.mapsnd_sndprod_assocequivapply (R := R) G H K n
    ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)
  rw [dLKern.prodassoc_equivapply_symmapply] at h
  exact h.symm


/-- Pointwise composition law for ordinary dimension quotient congruences. -/
@[simp] theorem dQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : dQuot R A n) :
    dQuot.congr R B f n (dQuot.congr R A e n x) =
      dQuot.congr R A (e.trans f) n x := by
  change ((dQuot.congr R A e n).trans
      (dQuot.congr R B f n)) x = _
  rw [dQuot.congr_trans]

@[simp] theorem dQuot.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : dQuot R A n) :
    dQuot.congr R A (MulEquiv.refl A) n x = x := by
  rw [dQuot.congr_refl]
  rfl

/-- Pointwise composition law for consecutive dimension quotient congruences. -/
@[simp] theorem dNQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ)
    (x : dSubgro R A n ⧸ dNTerm R A n) :
    dNQuot.congr (R := R) f n
        (dNQuot.congr (R := R) e n x) =
      dNQuot.congr (R := R) (e.trans f) n x := by
  change ((dNQuot.congr (R := R) e n).trans
      (dNQuot.congr (R := R) f n)) x = _
  rw [dNQuot.congr_trans]

@[simp] theorem dNQuot.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ)
    (x : dSubgro R A n ⧸ dNTerm R A n) :
    dNQuot.congr (R := R) (MulEquiv.refl A) n x = x := by
  rw [dNQuot.congr_refl]
  rfl

/-- Pointwise composition law for dimension layer-kernel congruences. -/
@[simp] theorem dLKern.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : dLKern R A n) :
    dLKern.congr (R := R) f n
        (dLKern.congr (R := R) e n x) =
      dLKern.congr (R := R) (e.trans f) n x := by
  change ((dLKern.congr (R := R) e n).trans
      (dLKern.congr (R := R) f n)) x = _
  rw [dLKern.congr_trans]

@[simp] theorem dLKern.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : dLKern R A n) :
    dLKern.congr (R := R) (MulEquiv.refl A) n x = x := by
  rw [dLKern.congr_refl]
  rfl

/-- Coordinate swaps are natural for maps of dimension quotients. -/
@[simp] theorem dQuot.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dQuot R (G₁ × H₁) n) :
    dQuot.prodCommEquiv R G₂ H₂ n
        (dQuot.map (R := R) (MonoidHom.prodMap f g) n x) =
      dQuot.map (R := R) (MonoidHom.prodMap g f) n
        (dQuot.prodCommEquiv R G₁ H₁ n x) := by
  change (((dQuot.prodCommEquiv R G₂ H₂ n).toMonoidHom).comp
      (dQuot.map (R := R) (MonoidHom.prodMap f g) n)) x =
    ((dQuot.map (R := R) (MonoidHom.prodMap g f) n).comp
      ((dQuot.prodCommEquiv R G₁ H₁ n).toMonoidHom)) x
  rw [dQuot.prod_commequiv_monoidhom,
    dQuot.prod_commequiv_monoidhom]
  rw [← dQuot.map_comp (R := R) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl

/-- Coordinate swaps are natural for maps of consecutive dimension quotients. -/
@[simp] theorem dNQuot.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dSubgro R (G₁ × H₁) n ⧸
      dNTerm R (G₁ × H₁) n) :
    dNQuot.prodCommEquiv (R := R) G₂ H₂ n
        (dNQuot.map (R := R) (MonoidHom.prodMap f g) n x) =
      dNQuot.map (R := R) (MonoidHom.prodMap g f) n
        (dNQuot.prodCommEquiv (R := R) G₁ H₁ n x) := by
  change (((dNQuot.prodCommEquiv (R := R) G₂ H₂ n).toMonoidHom).comp
      (dNQuot.map (R := R) (MonoidHom.prodMap f g) n)) x =
    ((dNQuot.map (R := R) (MonoidHom.prodMap g f) n).comp
      ((dNQuot.prodCommEquiv (R := R) G₁ H₁ n).toMonoidHom)) x
  rw [dNQuot.prod_commequiv_monoidhom,
    dNQuot.prod_commequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl

/-- Coordinate swaps are natural for maps of dimension layer kernels. -/
@[simp] theorem dLKern.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : dLKern R (G₁ × H₁) n) :
    dLKern.prodCommEquiv (R := R) G₂ H₂ n
        (dLKern.map (R := R) (MonoidHom.prodMap f g) n x) =
      dLKern.map (R := R) (MonoidHom.prodMap g f) n
        (dLKern.prodCommEquiv (R := R) G₁ H₁ n x) := by
  change (((dLKern.prodCommEquiv (R := R) G₂ H₂ n).toMonoidHom).comp
      (dLKern.map (R := R) (MonoidHom.prodMap f g) n)) x =
    ((dLKern.map (R := R) (MonoidHom.prodMap g f) n).comp
      ((dLKern.prodCommEquiv (R := R) G₁ H₁ n).toMonoidHom)) x
  rw [dLKern.prod_commequiv_monoidhom,
    dLKern.prod_commequiv_monoidhom]
  rw [← dLKern.map_comp (R := R) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl


/-- Reassociation is natural for maps of dimension quotients. -/
@[simp] theorem dQuot.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : dQuot R ((G₁ × H₁) × K₁) n) :
    dQuot.prodAssocEquiv R G₂ H₂ K₂ n
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      dQuot.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (dQuot.prodAssocEquiv R G₁ H₁ K₁ n x) := by
  change (((dQuot.prodAssocEquiv R G₂ H₂ K₂ n).toMonoidHom).comp
      (dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((dQuot.map (R := R)
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((dQuot.prodAssocEquiv R G₁ H₁ K₁ n).toMonoidHom)) x
  rw [dQuot.prod_assocequiv_monoidhom,
    dQuot.prod_assocequiv_monoidhom]
  rw [← dQuot.map_comp (R := R)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← dQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl

/-- Reassociation is natural for maps of consecutive dimension quotients. -/
@[simp] theorem dNQuot.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : dSubgro R ((G₁ × H₁) × K₁) n ⧸
      dNTerm R ((G₁ × H₁) × K₁) n) :
    dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      dNQuot.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n x) := by
  change (((dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n).toMonoidHom).comp
      (dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((dNQuot.map (R := R)
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n).toMonoidHom)) x
  rw [dNQuot.prod_assocequiv_monoidhom,
    dNQuot.prod_assocequiv_monoidhom]
  rw [← dNQuot.map_comp (R := R)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl

/-- Reassociation is natural for maps of dimension layer kernels. -/
@[simp] theorem dLKern.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : dLKern R ((G₁ × H₁) × K₁) n) :
    dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      dLKern.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n x) := by
  change (((dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n).toMonoidHom).comp
      (dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((dLKern.map (R := R)
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n).toMonoidHom)) x
  rw [dLKern.prod_assocequiv_monoidhom,
    dLKern.prod_assocequiv_monoidhom]
  rw [← dLKern.map_comp (R := R)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl


/-- Pentagon coherence for ordinary dimension-quotient associator maps. -/
theorem dQuot.map_prod_assocpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dQuot R (((G × H) × K) × L) n) :
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    dQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨abc, d⟩
  rcases abc with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Pentagon coherence for packaged ordinary dimension-quotient associators. -/
theorem dQuot.prod_assoc_equivpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dQuot R (((G × H) × K) × L) n) :
    dQuot.prodAssocEquiv R G H (K × L) n
      (dQuot.prodAssocEquiv R (G × H) K L n x) =
    dQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dQuot.prodAssocEquiv R G (H × K) L n
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [dQuot.prod_assoc_equivapply] using
    dQuot.map_prod_assocpentagon (R := R) G H K L n x


/-- Pentagon coherence for consecutive dimension-quotient associator maps. -/
theorem dNQuot.map_prod_assocpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dSubgro R (((G × H) × K) × L) n ⧸
      dNTerm R (((G × H) × K) × L) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    dNQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  change (((dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n)) x) = _
  rw [← dNQuot.map_comp (R := R)
    (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n]
  change (dNQuot.map (R := R) _ n x) =
    (((dNQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)))) x
  rw [← dNQuot.map_comp (R := R)
    (MonoidHom.prodMap
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
      (MonoidHom.id L))
    (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n]
  rw [← dNQuot.map_comp (R := R)
    ((MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom.comp
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (MonoidHom.id L)))
    (MonoidHom.prodMap (MonoidHom.id G)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n]
  rfl

/-- Pentagon coherence for packaged consecutive dimension-quotient associators. -/
theorem dNQuot.prod_assoc_equivpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dSubgro R (((G × H) × K) × L) n ⧸
      dNTerm R (((G × H) × K) × L) n) :
    dNQuot.prodAssocEquiv (R := R) G H (K × L) n
      (dNQuot.prodAssocEquiv (R := R) (G × H) K L n x) =
    dNQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dNQuot.prodAssocEquiv (R := R) G (H × K) L n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  change dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) = _
  simpa [dNQuot.prod_assocequiv_monoidhom] using
    dNQuot.map_prod_assocpentagon (R := R) G H K L n x

/-- Pentagon coherence for dimension layer-kernel associator maps. -/
theorem dLKern.map_prod_assocpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dLKern R (((G × H) × K) × L) n) :
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    dLKern.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  change (((dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n)) x) = _
  rw [← dLKern.map_comp (R := R)
    (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n]
  change (dLKern.map (R := R) _ n x) =
    (((dLKern.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)))) x
  rw [← dLKern.map_comp (R := R)
    (MonoidHom.prodMap
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
      (MonoidHom.id L))
    (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom.comp
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (MonoidHom.id L)))
    (MonoidHom.prodMap (MonoidHom.id G)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n]
  rfl

/-- Pentagon coherence for packaged dimension layer-kernel associators. -/
theorem dLKern.prod_assoc_equivpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dLKern R (((G × H) × K) × L) n) :
    dLKern.prodAssocEquiv (R := R) G H (K × L) n
      (dLKern.prodAssocEquiv (R := R) (G × H) K L n x) =
    dLKern.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dLKern.prodAssocEquiv (R := R) G (H × K) L n
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  change dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) = _
  simpa [dLKern.prod_assocequiv_monoidhom] using
    dLKern.map_prod_assocpentagon (R := R) G H K L n x


/-- Hexagon coherence for moving a left factor past a binary product on dimension quotients. -/
theorem dQuot.mapprod_commassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor on dimension quotients. -/
theorem dQuot.mapprod_commassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Packaged hexagon coherence for moving a left factor past a binary product
on dimension quotients. -/
theorem dQuot.prodcomm_equivassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (G × (H × K)) n) :
    dQuot.prodCommEquiv R G (H × K) n x =
      (dQuot.prodAssocEquiv R H K G n).symm
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (dQuot.prodAssocEquiv R H G K n
            (dQuot.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((dQuot.prodAssocEquiv R G H K n).symm x)))) := by
  simpa [dQuot.prod_comm_equivapply, dQuot.prod_assoc_equivapply,
    dQuot.prod_assocequiv_symmapply] using
    dQuot.mapprod_commassoc_hexagonleft (R := R) G H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor
on dimension quotients. -/
theorem dQuot.prodcomm_equivassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((G × H) × K) n) :
    dQuot.prodCommEquiv R (G × H) K n x =
      dQuot.prodAssocEquiv R K G H n
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((dQuot.prodAssocEquiv R G K H n).symm
            (dQuot.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (dQuot.prodAssocEquiv R G H K n x)))) := by
  simpa [dQuot.prod_comm_equivapply, dQuot.prod_assoc_equivapply,
    dQuot.prod_assocequiv_symmapply] using
    dQuot.mapprod_commassoc_hexagonright (R := R) G H K n x


/-- Hexagon coherence for moving a left factor past a binary product
on consecutive dimension quotients. -/
theorem dNQuot.mapprod_commassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor
on consecutive dimension quotients. -/
theorem dNQuot.mapprod_commassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Packaged hexagon coherence for moving a left factor past a binary product
on consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    dNQuot.prodCommEquiv (R := R) G (H × K) n x =
      (dNQuot.prodAssocEquiv (R := R) H K G n).symm
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (dNQuot.prodAssocEquiv (R := R) H G K n
            (dNQuot.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((dNQuot.prodAssocEquiv (R := R) G H K n).symm x)))) := by
  simpa [dNQuot.prod_commequiv_monoidhom,
    dNQuot.prod_assocequiv_monoidhom,
    dNQuot.prod_assocequiv_symmeq] using
    dNQuot.mapprod_commassoc_hexagonleft (R := R) G H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor
on consecutive dimension quotients. -/
theorem dNQuot.prodcomm_equivassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) :
    dNQuot.prodCommEquiv (R := R) (G × H) K n x =
      dNQuot.prodAssocEquiv (R := R) K G H n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((dNQuot.prodAssocEquiv (R := R) G K H n).symm
            (dNQuot.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (dNQuot.prodAssocEquiv (R := R) G H K n x)))) := by
  simpa [dNQuot.prod_commequiv_monoidhom,
    dNQuot.prod_assocequiv_monoidhom,
    dNQuot.prod_assocequiv_symmeq] using
    dNQuot.mapprod_commassoc_hexagonright (R := R) G H K n x

/-- Swapping factors preserves the cardinality of dimension quotients. -/
theorem card_dimension_comm (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card (dQuot R (G × H) n) =
      Nat.card (dQuot R (H × G) n) :=
  Nat.card_congr (dQuot.prodCommEquiv R G H n).toEquiv

/-- Reassociating factors preserves the cardinality of dimension quotients. -/
theorem card_dimension_assoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    Nat.card (dQuot R ((G × H) × K) n) =
      Nat.card (dQuot R (G × (H × K)) n) :=
  Nat.card_congr (dQuot.prodAssocEquiv R G H K n).toEquiv

/-- Swapping factors preserves the cardinality of consecutive dimension quotients. -/
theorem dimension_next_comm
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card (dSubgro R (G × H) n ⧸
        dNTerm R (G × H) n) =
      Nat.card (dSubgro R (H × G) n ⧸
        dNTerm R (H × G) n) :=
  Nat.card_congr (dNQuot.prodCommEquiv (R := R) G H n).toEquiv

/-- Reassociating factors preserves the cardinality of consecutive dimension quotients. -/
theorem dimension_next_assoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    Nat.card (dSubgro R ((G × H) × K) n ⧸
        dNTerm R ((G × H) × K) n) =
      Nat.card (dSubgro R (G × (H × K)) n ⧸
        dNTerm R (G × (H × K)) n) :=
  Nat.card_congr (dNQuot.prodAssocEquiv (R := R) G H K n).toEquiv

/-- Swapping factors preserves the cardinality of dimension layer kernels. -/
theorem nat_dimension_comm
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card (dLKern R (G × H) n) =
      Nat.card (dLKern R (H × G) n) :=
  Nat.card_congr (dLKern.prodCommEquiv (R := R) G H n).toEquiv

/-- Reassociating factors preserves the cardinality of dimension layer kernels. -/
theorem nat_dimension_assoc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    Nat.card (dLKern R ((G × H) × K) n) =
      Nat.card (dLKern R (G × (H × K)) n) :=
  Nat.card_congr (dLKern.prodAssocEquiv (R := R) G H K n).toEquiv


/-- Hexagon coherence for moving a left factor past a binary product on dimension
layer kernels. -/
theorem dLKern.mapprod_commassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [dLKern.map_coe]
  exact dQuot.mapprod_commassoc_hexagonleft (R := R) G H K (n + 1)
    (x : dQuot R (G × (H × K)) (n + 1))


/-- Hexagon coherence for moving a binary product past a right factor on dimension
layer kernels. -/
theorem dLKern.mapprod_commassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [dLKern.map_coe]
  exact dQuot.mapprod_commassoc_hexagonright (R := R) G H K (n + 1)
    (x : dQuot R ((G × H) × K) (n + 1))


/-- Applying the layer-kernel associator is the functorial map induced by the
group associator. -/
@[simp] theorem dLKern.prod_assoc_equivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.prodAssocEquiv (R := R) G H K n x =
      dLKern.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := by
  change ((dLKern.prodAssocEquiv (R := R) G H K n).toMonoidHom) x = _
  rw [dLKern.prod_assocequiv_monoidhom]

/-- Applying the inverse layer-kernel associator is the functorial map induced by
the inverse group associator. -/
@[simp] theorem dLKern.prod_assocequiv_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    (dLKern.prodAssocEquiv (R := R) G H K n).symm x =
      dLKern.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x := by
  rw [dLKern.prod_assocequiv_symmeq]
  rw [dLKern.congr_apply]


/-- Packaged hexagon coherence for moving a left factor past a binary product on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivassoc_hexagonleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (G × (H × K)) n) :
    dLKern.prodCommEquiv (R := R) G (H × K) n x =
      (dLKern.prodAssocEquiv (R := R) H K G n).symm
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (dLKern.prodAssocEquiv (R := R) H G K n
            (dLKern.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((dLKern.prodAssocEquiv (R := R) G H K n).symm x)))) := by
  simpa [dLKern.prod_comm_equivapply,
    dLKern.prod_assoc_equivapply,
    dLKern.prod_assocequiv_symmapply] using
    dLKern.mapprod_commassoc_hexagonleft (R := R) G H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor on
dimension layer kernels. -/
theorem dLKern.prodcomm_equivassoc_hexagonright
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((G × H) × K) n) :
    dLKern.prodCommEquiv (R := R) (G × H) K n x =
      dLKern.prodAssocEquiv (R := R) K G H n
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((dLKern.prodAssocEquiv (R := R) G K H n).symm
            (dLKern.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (dLKern.prodAssocEquiv (R := R) G H K n x)))) := by
  simpa [dLKern.prod_comm_equivapply,
    dLKern.prod_assoc_equivapply,
    dLKern.prod_assocequiv_symmapply] using
    dLKern.mapprod_commassoc_hexagonright (R := R) G H K n x


/-- Integer-linear hexagon coherence for moving a left factor past a binary product
on dimension layer kernels. -/
theorem dLKern.mapint_linprodcomm_assohexaleft
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R (G × (H × K)) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.mapprod_commassoc_hexagonleft (R := R) G H K n x'

/-- Integer-linear hexagon coherence for moving a binary product past a right factor
on dimension layer kernels. -/
theorem dLKern.mapint_linprodcomm_assohexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R ((G × H) × K) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.mapprod_commassoc_hexagonright (R := R) G H K n x'


/-- Integer-linear coordinate swap on additive dimension layer kernels. -/
noncomputable def dLKern.prod_commint_linequiv
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Additive (dLKern R (G × H) n) ≃ₗ[ℤ]
      Additive (dLKern R (H × G) n) :=
  dLKern.congrIntLinear (R := R)
    (MulEquiv.prodComm : G × H ≃* H × G) n

/-- Integer-linear reassociation on additive dimension layer kernels. -/
noncomputable def dLKern.prod_assocint_linequiv
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    Additive (dLKern R ((G × H) × K) n) ≃ₗ[ℤ]
      Additive (dLKern R (G × (H × K)) n) :=
  dLKern.congrIntLinear (R := R)
    (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K) n

@[simp] theorem dLKern.prodcomm_intlin_equivapply
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    (x : Additive (dLKern R (G × H) n)) :
    dLKern.prod_commint_linequiv (R := R) G H n x =
      dLKern.mapIntLinear (R := R)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom n x := by
  cases x with | ofMul x' => rfl

@[simp] theorem dLKern.prodassoc_intlin_equivapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R ((G × H) × K) n)) :
    dLKern.prod_assocint_linequiv (R := R) G H K n x =
      dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x := by
  cases x with | ofMul x' => rfl


@[simp] theorem dLKern.prodassoc_intlin_equivsymmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R (G × (H × K)) n)) :
    (dLKern.prod_assocint_linequiv (R := R) G H K n).symm x =
      dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x := by
  apply (dLKern.prod_assocint_linequiv (R := R) G H K n).injective
  rw [LinearEquiv.apply_symm_apply]
  change x = ((dLKern.mapAdd (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      (dLKern.mapAdd (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)) x
  rw [← dLKern.mapAdd_comp (R := R)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n]
  simp


/-- Packaged integer-linear hexagon coherence for moving a left factor past a
binary product on dimension layer kernels. -/
theorem dLKern.prodco_intli_assoh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R (G × (H × K)) n)) :
    dLKern.prod_commint_linequiv (R := R) G (H × K) n x =
      (dLKern.prod_assocint_linequiv (R := R) H K G n).symm
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (dLKern.prod_assocint_linequiv (R := R) H G K n
            (dLKern.mapIntLinear (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((dLKern.prod_assocint_linequiv (R := R) G H K n).symm x)))) := by
  simpa [dLKern.prodcomm_intlin_equivapply,
    dLKern.prodassoc_intlin_equivapply,
    dLKern.prodassoc_intlin_equivsymmapply] using
    dLKern.mapint_linprodcomm_assohexaleft (R := R) G H K n x

/-- Packaged integer-linear hexagon coherence for moving a binary product past a
right factor on dimension layer kernels. -/
theorem dLKern.prodco_intli_assoa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R ((G × H) × K) n)) :
    dLKern.prod_commint_linequiv (R := R) (G × H) K n x =
      dLKern.prod_assocint_linequiv (R := R) K G H n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((dLKern.prod_assocint_linequiv (R := R) G K H n).symm
            (dLKern.mapIntLinear (R := R)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (dLKern.prod_assocint_linequiv (R := R) G H K n x)))) := by
  simpa [dLKern.prodcomm_intlin_equivapply,
    dLKern.prodassoc_intlin_equivapply,
    dLKern.prodassoc_intlin_equivsymmapply] using
    dLKern.mapint_linprodcomm_assohexarigh (R := R) G H K n x


end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for coordinate swaps on dimension quotients. -/
theorem dQuot.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dQuot.prodCommEquiv R G₂ H₂ n).toMonoidHom).comp
        (dQuot.map (R := R) (MonoidHom.prodMap f g) n) =
      (dQuot.map (R := R) (MonoidHom.prodMap g f) n).comp
        ((dQuot.prodCommEquiv R G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prod_commequiv_naturalapply (R := R) f g n x

/-- Naturality square for coordinate swaps on consecutive dimension quotients. -/
theorem dNQuot.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dNQuot.prodCommEquiv (R := R) G₂ H₂ n).toMonoidHom).comp
        (dNQuot.map (R := R) (MonoidHom.prodMap f g) n) =
      (dNQuot.map (R := R) (MonoidHom.prodMap g f) n).comp
        ((dNQuot.prodCommEquiv (R := R) G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prod_commequiv_naturalapply (R := R) f g n x

/-- Naturality square for coordinate swaps on dimension layer kernels. -/
theorem dLKern.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dLKern.prodCommEquiv (R := R) G₂ H₂ n).toMonoidHom).comp
        (dLKern.map (R := R) (MonoidHom.prodMap f g) n) =
      (dLKern.map (R := R) (MonoidHom.prodMap g f) n).comp
        ((dLKern.prodCommEquiv (R := R) G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (dLKern.prod_commequiv_naturalapply (R := R) f g n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for reassociation on dimension quotients. -/
theorem dQuot.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dQuot.prodAssocEquiv R G₂ H₂ K₂ n).toMonoidHom).comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (dQuot.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((dQuot.prodAssocEquiv R G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prod_assocequiv_naturalapply (R := R) f g h n x

/-- Naturality square for reassociation on consecutive dimension quotients. -/
theorem dNQuot.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n).toMonoidHom).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (dNQuot.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  exact
    dNQuot.prod_assocequiv_naturalapply (R := R) f g h n x

/-- Naturality square for reassociation on dimension layer kernels. -/
theorem dLKern.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n).toMonoidHom).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (dLKern.map (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (dLKern.prod_assocequiv_naturalapply (R := R) f g h n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Integer-linear coordinate swaps are natural for maps of dimension layer kernels. -/
@[simp] theorem dLKern.prodcomm_intlin_equinatuappl
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : Additive (dLKern R (G₁ × H₁) n)) :
    dLKern.prod_commint_linequiv (R := R) G₂ H₂ n
        (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap f g) n x) =
      dLKern.mapIntLinear (R := R) (MonoidHom.prodMap g f) n
        (dLKern.prod_commint_linequiv (R := R) G₁ H₁ n x) := by
  cases x with
  | ofMul q =>
      apply congrArg Additive.ofMul
      exact dLKern.prod_commequiv_naturalapply (R := R) f g n q

/-- Integer-linear reassociation is natural for maps of dimension layer kernels. -/
@[simp] theorem dLKern.prodassoc_intlin_equinatuappl
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : Additive (dLKern R ((G₁ × H₁) × K₁) n)) :
    dLKern.prod_assocint_linequiv (R := R) G₂ H₂ K₂ n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (dLKern.prod_assocint_linequiv (R := R) G₁ H₁ K₁ n x) := by
  cases x with
  | ofMul q =>
      apply congrArg Additive.ofMul
      exact dLKern.prod_assocequiv_naturalapply (R := R) f g h n q

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for integer-linear coordinate swaps on dimension layer kernels. -/
theorem dLKern.prodcomm_intlin_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) G₂ H₂ n).toLinearMap.comp
        (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap f g) n) =
      (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap g f) n).comp
        (dLKern.prod_commint_linequiv (R := R) G₁ H₁ n).toLinearMap := by
  ext x
  simpa using congrArg
    (fun y => (Additive.toMul y : dLKern R (H₂ × G₂) n).1)
    (dLKern.prodcomm_intlin_equinatuappl (R := R) f g n x)

/-- Naturality square for integer-linear reassociation on dimension layer kernels. -/
theorem dLKern.prodassoc_intlin_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    (dLKern.prod_assocint_linequiv (R := R) G₂ H₂ K₂ n).toLinearMap.comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        (dLKern.prod_assocint_linequiv (R := R) G₁ H₁ K₁ n).toLinearMap := by
  ext x
  simpa using congrArg
    (fun y => (Additive.toMul y : dLKern R (G₂ × (H₂ × K₂)) n).1)
    (dLKern.prodassoc_intlin_equinatuappl (R := R) f g h n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse coordinate swaps are natural on dimension quotients. -/
@[simp] theorem dQuot.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : dQuot R (H₁ × G₁) n) :
    (dQuot.prodCommEquiv R G₂ H₂ n).symm
        (dQuot.map (R := R) (MonoidHom.prodMap g f) n y) =
      dQuot.map (R := R) (MonoidHom.prodMap f g) n
        ((dQuot.prodCommEquiv R G₁ H₁ n).symm y) := by
  simpa [dQuot.prod_commequiv_symmeq] using
    dQuot.prod_commequiv_naturalapply (R := R)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

/-- Inverse coordinate swaps are natural on consecutive dimension quotients. -/
@[simp] theorem dNQuot.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : dSubgro R (H₁ × G₁) n ⧸
      dNTerm R (H₁ × G₁) n) :
    (dNQuot.prodCommEquiv (R := R) G₂ H₂ n).symm
        (dNQuot.map (R := R) (MonoidHom.prodMap g f) n y) =
      dNQuot.map (R := R) (MonoidHom.prodMap f g) n
        ((dNQuot.prodCommEquiv (R := R) G₁ H₁ n).symm y) := by
  simpa [dNQuot.prod_commequiv_symmeq] using
    dNQuot.prod_commequiv_naturalapply (R := R)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

/-- Inverse coordinate swaps are natural on dimension layer kernels. -/
@[simp] theorem dLKern.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : dLKern R (H₁ × G₁) n) :
    (dLKern.prodCommEquiv (R := R) G₂ H₂ n).symm
        (dLKern.map (R := R) (MonoidHom.prodMap g f) n y) =
      dLKern.map (R := R) (MonoidHom.prodMap f g) n
        ((dLKern.prodCommEquiv (R := R) G₁ H₁ n).symm y) := by
  simpa [dLKern.prod_commequiv_symmeq] using
    dLKern.prod_commequiv_naturalapply (R := R)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse reassociation is natural on dimension quotients. -/
@[simp] theorem dQuot.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : dQuot R (G₁ × (H₁ × K₁)) n) :
    (dQuot.prodAssocEquiv R G₂ H₂ K₂ n).symm
        (dQuot.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((dQuot.prodAssocEquiv R G₁ H₁ K₁ n).symm y) := by
  apply (dQuot.prodAssocEquiv R G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := dQuot.prod_assocequiv_naturalapply (R := R) f g h n
    ((dQuot.prodAssocEquiv R G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

/-- Inverse reassociation is natural on consecutive dimension quotients. -/
@[simp] theorem dNQuot.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : dSubgro R (G₁ × (H₁ × K₁)) n ⧸
      dNTerm R (G₁ × (H₁ × K₁)) n) :
    (dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n).symm
        (dNQuot.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm y) := by
  apply (dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := dNQuot.prod_assocequiv_naturalapply (R := R) f g h n
    ((dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

/-- Inverse reassociation is natural on dimension layer kernels. -/
@[simp] theorem dLKern.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : dLKern R (G₁ × (H₁ × K₁)) n) :
    (dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n).symm
        (dLKern.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm y) := by
  apply (dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := dLKern.prod_assocequiv_naturalapply (R := R) f g h n
    ((dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse integer-linear coordinate swaps are natural on dimension layer kernels. -/
@[simp] theorem dLKern.prodco_intli_symmn
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : Additive (dLKern R (H₁ × G₁) n)) :
    (dLKern.prod_commint_linequiv (R := R) G₂ H₂ n).symm
        (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap g f) n y) =
      dLKern.mapIntLinear (R := R) (MonoidHom.prodMap f g) n
        ((dLKern.prod_commint_linequiv (R := R) G₁ H₁ n).symm y) := by
  apply (dLKern.prod_commint_linequiv (R := R) G₂ H₂ n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hnat := dLKern.prodcomm_intlin_equinatuappl (R := R) f g n
    ((dLKern.prod_commint_linequiv (R := R) G₁ H₁ n).symm y)
  rw [LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm

/-- Inverse integer-linear reassociation is natural on dimension layer kernels. -/
@[simp] theorem dLKern.prodas_intli_symmn
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : Additive (dLKern R (G₁ × (H₁ × K₁)) n)) :
    (dLKern.prod_assocint_linequiv (R := R) G₂ H₂ K₂ n).symm
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((dLKern.prod_assocint_linequiv (R := R) G₁ H₁ K₁ n).symm y) := by
  apply (dLKern.prod_assocint_linequiv (R := R) G₂ H₂ K₂ n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hnat := dLKern.prodassoc_intlin_equinatuappl (R := R) f g h n
    ((dLKern.prod_assocint_linequiv (R := R) G₁ H₁ K₁ n).symm y)
  rw [LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for inverse coordinate swaps on dimension quotients. -/
theorem dQuot.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dQuot.prodCommEquiv R G₂ H₂ n).symm.toMonoidHom).comp
        (dQuot.map (R := R) (MonoidHom.prodMap g f) n) =
      (dQuot.map (R := R) (MonoidHom.prodMap f g) n).comp
        ((dQuot.prodCommEquiv R G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    dQuot.prodcomm_equivsymm_naturalapply (R := R) f g n y

/-- Naturality square for inverse coordinate swaps on consecutive dimension quotients. -/
theorem dNQuot.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dNQuot.prodCommEquiv (R := R) G₂ H₂ n).symm.toMonoidHom).comp
        (dNQuot.map (R := R) (MonoidHom.prodMap g f) n) =
      (dNQuot.map (R := R) (MonoidHom.prodMap f g) n).comp
        ((dNQuot.prodCommEquiv (R := R) G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodcomm_equivsymm_naturalapply (R := R) f g n y

/-- Naturality square for inverse coordinate swaps on dimension layer kernels. -/
theorem dLKern.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dLKern.prodCommEquiv (R := R) G₂ H₂ n).symm.toMonoidHom).comp
        (dLKern.map (R := R) (MonoidHom.prodMap g f) n) =
      (dLKern.map (R := R) (MonoidHom.prodMap f g) n).comp
        ((dLKern.prodCommEquiv (R := R) G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (dLKern.prodcomm_equivsymm_naturalapply (R := R) f g n y)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for inverse reassociation on dimension quotients. -/
theorem dQuot.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dQuot.prodAssocEquiv R G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((dQuot.prodAssocEquiv R G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    dQuot.prodassoc_equivsymm_naturalapply (R := R) f g h n y

/-- Naturality square for inverse reassociation on consecutive dimension quotients. -/
theorem dNQuot.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dNQuot.prodAssocEquiv (R := R) G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((dNQuot.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodassoc_equivsymm_naturalapply (R := R) f g h n y

/-- Naturality square for inverse reassociation on dimension layer kernels. -/
theorem dLKern.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dLKern.prodAssocEquiv (R := R) G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((dLKern.prodAssocEquiv (R := R) G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (dLKern.prodassoc_equivsymm_naturalapply (R := R) f g h n y)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Naturality square for inverse integer-linear coordinate swaps on dimension layer kernels. -/
theorem dLKern.prodcomm_intlin_equisymmnatu
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((dLKern.prod_commint_linequiv (R := R) G₂ H₂ n).symm.toLinearMap).comp
        (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap g f) n) =
      (dLKern.mapIntLinear (R := R) (MonoidHom.prodMap f g) n).comp
        ((dLKern.prod_commint_linequiv (R := R) G₁ H₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg
    (fun z => (Additive.toMul z : dLKern R (G₂ × H₂) n).1)
    (dLKern.prodco_intli_symmn (R := R) f g n y)

/-- Naturality square for inverse integer-linear reassociation on dimension layer kernels. -/
theorem dLKern.prodassoc_intlin_equisymmnatu
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((dLKern.prod_assocint_linequiv (R := R) G₂ H₂ K₂ n).symm.toLinearMap).comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((dLKern.prod_assocint_linequiv (R := R) G₁ H₁ K₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg
    (fun z => (Additive.toMul z : dLKern R ((G₂ × H₂) × K₂) n).1)
    (dLKern.prodas_intli_symmn (R := R) f g h n y)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Reverse pentagon coherence for ordinary dimension-quotient associator maps. -/
theorem dQuot.map_prodassoc_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dQuot R (G × (H × (K × L))) n) :
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    dQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl

/-- Reverse pentagon coherence for consecutive dimension-quotient associator maps. -/
theorem dNQuot.map_prodassoc_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dSubgro R (G × (H × (K × L))) n ⧸
      dNTerm R (G × (H × (K × L))) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    dNQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Reverse pentagon coherence for dimension layer-kernel associator maps. -/
theorem dLKern.map_prodassoc_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dLKern R (G × (H × (K × L))) n) :
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    dLKern.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  change (((dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n)) x) = _
  rw [← dLKern.map_comp (R := R)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom
    (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n]
  change (dLKern.map (R := R) _ n x) =
    (((dLKern.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)))) x
  rw [← dLKern.map_comp (R := R)
    (MonoidHom.prodMap (MonoidHom.id G)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom)
    (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n]
  rw [← dLKern.map_comp (R := R)
    ((MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom.comp
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom))
    (MonoidHom.prodMap
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
      (MonoidHom.id L)) n]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Packaged reverse pentagon coherence for dimension layer-kernel associators. -/
theorem dLKern.prod_assocequiv_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dLKern R (G × (H × (K × L))) n) :
    (dLKern.prodAssocEquiv (R := R) (G × H) K L n).symm
      ((dLKern.prodAssocEquiv (R := R) G H (K × L) n).symm x) =
    dLKern.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((dLKern.prodAssocEquiv (R := R) G (H × K) L n).symm
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [dLKern.prod_assocequiv_symmapply] using
    dLKern.map_prodassoc_symmpentagon (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Packaged reverse pentagon coherence for ordinary dimension-quotient associators. -/
theorem dQuot.prod_assocequiv_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dQuot R (G × (H × (K × L))) n) :
    (dQuot.prodAssocEquiv R (G × H) K L n).symm
      ((dQuot.prodAssocEquiv R G H (K × L) n).symm x) =
    dQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((dQuot.prodAssocEquiv R G (H × K) L n).symm
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  rw [dQuot.prod_assocequiv_symmapply]
  rw [dQuot.prod_assocequiv_symmapply]
  rw [dQuot.prod_assocequiv_symmapply]
  simpa [MonoidHom.comp_apply] using
    dQuot.map_prodassoc_symmpentagon (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Applying the inverse consecutive-quotient associator is the induced inverse map. -/
@[simp] theorem dNQuot.prod_assocequiv_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) :
    (dNQuot.prodAssocEquiv (R := R) G H K n).symm x =
      dNQuot.map (R := R)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x := by
  rw [dNQuot.prod_assocequiv_symmeq]
  change (dNQuot.congr (R := R)
      (MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm n).toMonoidHom x = _
  rw [dNQuot.congr_monoid_hom]

/-- Packaged reverse pentagon coherence for consecutive dimension-quotient associators. -/
theorem dNQuot.prod_assocequiv_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : dSubgro R (G × (H × (K × L))) n ⧸
      dNTerm R (G × (H × (K × L))) n) :
    (dNQuot.prodAssocEquiv (R := R) (G × H) K L n).symm
      ((dNQuot.prodAssocEquiv (R := R) G H (K × L) n).symm x) =
    dNQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((dNQuot.prodAssocEquiv (R := R) G (H × K) L n).symm
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  rw [dNQuot.prod_assocequiv_symmapply]
  rw [dNQuot.prod_assocequiv_symmapply]
  rw [dNQuot.prod_assocequiv_symmapply]
  simpa [MonoidHom.comp_apply] using
    dNQuot.map_prodassoc_symmpentagon (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Integer-linear pentagon coherence for additive dimension layer kernels. -/
theorem dLKern.mapint_linprod_assocpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (dLKern R (((G × H) × K) × L) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.map_prod_assocpentagon (R := R) G H K L n x'

/-- Reverse integer-linear pentagon coherence for additive dimension layer kernels. -/
theorem dLKern.mapint_linprod_assosymmpent
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (dLKern R (G × (H × (K × L))) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.map_prodassoc_symmpentagon (R := R) G H K L n x'

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pentagon coherence for packaged integer-linear dimension layer associators. -/
theorem dLKern.prodassoc_intlin_equivpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (dLKern R (((G × H) × K) × L) n)) :
    dLKern.prod_assocint_linequiv (R := R) G H (K × L) n
      (dLKern.prod_assocint_linequiv (R := R) (G × H) K L n x) =
    dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (dLKern.prod_assocint_linequiv (R := R) G (H × K) L n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [dLKern.prodassoc_intlin_equivapply] using
    dLKern.mapint_linprod_assocpentagon (R := R) G H K L n x

/-- Reverse pentagon coherence for packaged integer-linear dimension layer associators. -/
theorem dLKern.prodassoc_intlin_equisymmpent
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (dLKern R (G × (H × (K × L))) n)) :
    (dLKern.prod_assocint_linequiv (R := R) (G × H) K L n).symm
      ((dLKern.prod_assocint_linequiv (R := R) G H (K × L) n).symm x) =
    dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((dLKern.prod_assocint_linequiv (R := R) G (H × K) L n).symm
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [dLKern.prodassoc_intlin_equivsymmapply] using
    dLKern.mapint_linprod_assosymmpent (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level form of the integer-linear dimension-layer associator pentagon. -/
theorem dLKern.prodas_intli_penta
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.prod_assocint_linequiv (R := R) G H (K × L) n).toLinearMap.comp
      (dLKern.prod_assocint_linequiv (R := R) (G × H) K L n).toLinearMap =
    (dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dLKern.prod_assocint_linequiv (R := R) G (H × K) L n).toLinearMap.comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodassoc_intlin_equivpentagon (R := R) G H K L n x

/-- Hom-level form of the reverse integer-linear dimension-layer associator pentagon. -/
theorem dLKern.prodas_lineq_pentc
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((dLKern.prod_assocint_linequiv (R := R) (G × H) K L n).symm.toLinearMap).comp
      ((dLKern.prod_assocint_linequiv (R := R) G H (K × L) n).symm.toLinearMap) =
    (dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((dLKern.prod_assocint_linequiv (R := R) G (H × K) L n).symm.toLinearMap).comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodassoc_intlin_equisymmpent (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level raw-map integer-linear pentagon for dimension layer kernels. -/
theorem dLKern.mapint_linpr_penta
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_linprod_assocpentagon (R := R) G H K L n x

/-- Hom-level raw-map reverse integer-linear pentagon for dimension layer kernels. -/
theorem dLKern.mapint_proda_penta
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (dLKern.mapIntLinear (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((dLKern.mapIntLinear (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_linprod_assosymmpent (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level pentagon for ordinary dimension quotient associator maps. -/
theorem dQuot.map_prodassoc_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (dQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.map_prod_assocpentagon (R := R) G H K L n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level reverse pentagon for ordinary dimension quotient associator maps. -/
theorem dQuot.mapprod_assocsymm_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (dQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((dQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.map_prodassoc_symmpentagon (R := R) G H K L n x

/-- Hom-level pentagon for consecutive dimension quotient associator maps. -/
theorem dNQuot.map_prodassoc_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (dNQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.map_prod_assocpentagon (R := R) G H K L n x

/-- Hom-level reverse pentagon for consecutive dimension quotient associator maps. -/
theorem dNQuot.mapprod_assocsymm_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (dNQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((dNQuot.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.map_prodassoc_symmpentagon (R := R) G H K L n x

/-- Hom-level pentagon for dimension layer-kernel associator maps. -/
theorem dLKern.map_prodassoc_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (dLKern.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val (dLKern.map_prod_assocpentagon (R := R) G H K L n x)

/-- Hom-level reverse pentagon for dimension layer-kernel associator maps. -/
theorem dLKern.mapprod_assocsymm_pentagonhom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (dLKern.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((dLKern.map (R := R)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val (dLKern.map_prodassoc_symmpentagon (R := R) G H K L n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level hexagon for moving a left factor past a binary product on dimension quotients. -/
theorem dQuot.mapprod_commassoc_hexagonlefthom
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.mapprod_commassoc_hexagonleft (R := R) G H K n x

/-- Hom-level hexagon for moving a binary product past a right factor on dimension quotients. -/
theorem dQuot.mappro_comma_hexag
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.mapprod_commassoc_hexagonright (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level hexagon for moving a left factor past a binary product
on consecutive dimension quotients. -/
theorem dNQuot.mapprod_commassoc_hexagonlefthom
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.mapprod_commassoc_hexagonleft (R := R) G H K n x

/-- Hom-level hexagon for moving a binary product past a right factor
on consecutive dimension quotients. -/
theorem dNQuot.mappro_comma_hexag
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.mapprod_commassoc_hexagonright (R := R) G H K n x

/-- Hom-level hexagon for moving a left factor past a binary product on dimension layer kernels. -/
theorem dLKern.mapprod_commassoc_hexagonlefthom
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.mapprod_commassoc_hexagonleft (R := R) G H K n x)

/-- Hom-level hexagon for moving a binary product past a right factor on dimension layer kernels. -/
theorem dLKern.mappro_comma_hexag
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.mapprod_commassoc_hexagonright (R := R) G H K n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level packaged integer-linear hexagon (left orientation) for dimension layer kernels. -/
theorem dLKern.prodco_lineq_hexla
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) G (H × K) n).toLinearMap =
    ((dLKern.prod_assocint_linequiv (R := R) H K G n).symm.toLinearMap).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dLKern.prod_assocint_linequiv (R := R) H G K n).toLinearMap.comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (((dLKern.prod_assocint_linequiv (R := R)
                G H K n).symm).toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodco_intli_assoh (R := R) G H K n x

/-- Hom-level packaged integer-linear hexagon (right orientation) for dimension layer kernels. -/
theorem dLKern.prodco_lineq_hexra
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) (G × H) K n).toLinearMap =
    (dLKern.prod_assocint_linequiv (R := R) K G H n).toLinearMap.comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((dLKern.prod_assocint_linequiv (R := R) G K H n).symm.toLinearMap).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dLKern.prod_assocint_linequiv (R := R) G H K n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodco_intli_assoa (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level raw integer-linear hexagon (left orientation) for dimension layer-kernel maps. -/
theorem dLKern.mapint_prodc_hexle
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_linprodcomm_assohexaleft (R := R) G H K n x

/-- Hom-level raw integer-linear hexagon (right orientation) for dimension layer-kernel maps. -/
theorem dLKern.mapint_prodc_hexri
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_linprodcomm_assohexarigh (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on dimension quotients. -/
theorem dQuot.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((H × K) × G) n) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨hk, g⟩
  rcases hk with ⟨h, k⟩
  rfl

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on dimension quotients. -/
theorem dQuot.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (K × (G × H)) n) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨k, gh⟩
  rcases gh with ⟨g, h⟩
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on consecutive dimension quotients. -/
theorem dNQuot.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((H × K) × G) n ⧸
      dNTerm R ((H × K) × G) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨hk, g⟩
  rcases hk with ⟨h, k⟩
  rfl

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on consecutive dimension quotients. -/
theorem dNQuot.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (K × (G × H)) n ⧸
      dNTerm R (K × (G × H)) n) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨k, gh⟩
  rcases gh with ⟨g, h⟩
  rfl

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on dimension layer kernels. -/
theorem dLKern.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((H × K) × G) n) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [dLKern.map_coe]
  exact dQuot.mappro_comma_symmh (R := R) G H K (n + 1)
    (x : dQuot R ((H × K) × G) (n + 1))

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on dimension layer kernels. -/
theorem dLKern.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (K × (G × H)) n) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [dLKern.map_coe]
  exact dQuot.mapprod_commassoc_symmhexarigh (R := R) G H K (n + 1)
    (x : dQuot R (K × (G × H)) (n + 1))

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level reverse hexagon for moving a binary product back past a left factor
on dimension quotients. -/
theorem dQuot.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.mappro_comma_symmh (R := R) G H K n x

/-- Hom-level reverse hexagon for moving a right factor back past a binary product
on dimension quotients. -/
theorem dQuot.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dQuot.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (dQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (dQuot.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.mapprod_commassoc_symmhexarigh (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level reverse hexagon for consecutive dimension quotient maps (left orientation). -/
theorem dNQuot.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.mappro_comma_symmh (R := R) G H K n x

/-- Hom-level reverse hexagon for consecutive dimension quotient maps (right orientation). -/
theorem dNQuot.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dNQuot.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (dNQuot.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dNQuot.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (dNQuot.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.mapprod_commassoc_symmhexarigh (R := R) G H K n x

/-- Hom-level reverse hexagon for dimension layer-kernel maps (left orientation). -/
theorem dLKern.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.mappro_comma_symmh (R := R) G H K n x)

/-- Hom-level reverse hexagon for dimension layer-kernel maps (right orientation). -/
theorem dLKern.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.map (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (dLKern.map (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dLKern.map (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (dLKern.map (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.mapprod_commassoc_symmhexarigh (R := R) G H K n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Integer-linear reverse hexagon coherence for dimension layer kernels (left orientation). -/
theorem dLKern.mapint_prodc_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R ((H × K) × G) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.mappro_comma_symmh (R := R) G H K n x'

/-- Integer-linear reverse hexagon coherence for dimension layer kernels (right orientation). -/
theorem dLKern.mapint_prodc_symma
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R (K × (G × H)) n)) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact dLKern.mapprod_commassoc_symmhexarigh (R := R) G H K n x'

/-- Hom-level raw integer-linear reverse hexagon for dimension layer kernels (left). -/
theorem dLKern.mapint_proco_hexle
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_prodc_symmh (R := R) G H K n x

/-- Hom-level raw integer-linear reverse hexagon for dimension layer kernels (right). -/
theorem dLKern.mapint_proco_hexri
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    dLKern.mapIntLinear (R := R)
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (dLKern.mapIntLinear (R := R)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dLKern.mapIntLinear (R := R)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (dLKern.mapIntLinear (R := R)
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.mapint_prodc_symma (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Packaged integer-linear reverse hexagon for dimension layer kernels (left orientation). -/
theorem dLKern.prodco_lineq_symmb
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R ((H × K) × G) n)) :
    dLKern.prod_commint_linequiv (R := R) (H × K) G n x =
      dLKern.prod_assocint_linequiv (R := R) G H K n
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((dLKern.prod_assocint_linequiv (R := R) H G K n).symm
            (dLKern.mapIntLinear (R := R)
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (dLKern.prod_assocint_linequiv (R := R) H K G n x)))) := by
  simpa [dLKern.prodcomm_intlin_equivapply,
    dLKern.prodassoc_intlin_equivapply,
    dLKern.prodassoc_intlin_equivsymmapply] using
    dLKern.mapint_prodc_symmh (R := R) G H K n x

/-- Packaged integer-linear reverse hexagon for dimension layer kernels (right orientation). -/
theorem dLKern.prodco_lineq_symmc
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (dLKern R (K × (G × H)) n)) :
    dLKern.prod_commint_linequiv (R := R) K (G × H) n x =
      (dLKern.prod_assocint_linequiv (R := R) G H K n).symm
        (dLKern.mapIntLinear (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (dLKern.prod_assocint_linequiv (R := R) G K H n
            (dLKern.mapIntLinear (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((dLKern.prod_assocint_linequiv (R := R) K G H n).symm x)))) := by
  simpa [dLKern.prodcomm_intlin_equivapply,
    dLKern.prodassoc_intlin_equivapply,
    dLKern.prodassoc_intlin_equivsymmapply] using
    dLKern.mapint_prodc_symma (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level packaged integer-linear reverse hexagon (left orientation) for dimension layers. -/
theorem dLKern.prodco_lineq_hexle
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) (H × K) G n).toLinearMap =
    (dLKern.prod_assocint_linequiv (R := R) G H K n).toLinearMap.comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((dLKern.prod_assocint_linequiv (R := R) H G K n).symm.toLinearMap).comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dLKern.prod_assocint_linequiv (R := R) H K G n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodco_lineq_symmb (R := R) G H K n x

/-- Hom-level packaged integer-linear reverse hexagon (right orientation) for dimension layers. -/
theorem dLKern.prodco_lineq_hexri
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) K (G × H) n).toLinearMap =
    ((dLKern.prod_assocint_linequiv (R := R) G H K n).symm.toLinearMap).comp
      ((dLKern.mapIntLinear (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dLKern.prod_assocint_linequiv (R := R) G K H n).toLinearMap.comp
          ((dLKern.mapIntLinear (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (((dLKern.prod_assocint_linequiv (R := R)
                K G H n).symm).toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    dLKern.prodco_lineq_symmc (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Packaged reverse hexagon coherence for dimension quotient equivalences (left). -/
theorem dQuot.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R ((H × K) × G) n) :
    dQuot.prodCommEquiv R (H × K) G n x =
      dQuot.prodAssocEquiv R G H K n
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((dQuot.prodAssocEquiv R H G K n).symm
            (dQuot.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (dQuot.prodAssocEquiv R H K G n x)))) := by
  simpa [dQuot.prod_comm_equivapply,
    dQuot.prod_assoc_equivapply,
    dQuot.prod_assocequiv_symmapply] using
    dQuot.mappro_comma_symmh (R := R) G H K n x

/-- Packaged reverse hexagon coherence for dimension quotient equivalences (right). -/
theorem dQuot.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dQuot R (K × (G × H)) n) :
    dQuot.prodCommEquiv R K (G × H) n x =
      (dQuot.prodAssocEquiv R G H K n).symm
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (dQuot.prodAssocEquiv R G K H n
            (dQuot.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((dQuot.prodAssocEquiv R K G H n).symm x)))) := by
  simpa [dQuot.prod_comm_equivapply,
    dQuot.prod_assoc_equivapply,
    dQuot.prod_assocequiv_symmapply] using
    dQuot.mapprod_commassoc_symmhexarigh (R := R) G H K n x

/-- Packaged reverse hexagon coherence for consecutive dimension quotient equivalences (left). -/
theorem dNQuot.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R ((H × K) × G) n ⧸
      dNTerm R ((H × K) × G) n) :
    dNQuot.prodCommEquiv R (H × K) G n x =
      dNQuot.prodAssocEquiv R G H K n
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((dNQuot.prodAssocEquiv R H G K n).symm
            (dNQuot.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (dNQuot.prodAssocEquiv R H K G n x)))) := by
  simpa [dNQuot.prod_commequiv_monoidhom,
    dNQuot.prod_assocequiv_monoidhom,
    dNQuot.prod_assocequiv_symmeq] using
    dNQuot.mappro_comma_symmh (R := R) G H K n x

/-- Packaged reverse hexagon coherence for consecutive dimension quotient equivalences (right). -/
theorem dNQuot.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dSubgro R (K × (G × H)) n ⧸
      dNTerm R (K × (G × H)) n) :
    dNQuot.prodCommEquiv R K (G × H) n x =
      (dNQuot.prodAssocEquiv R G H K n).symm
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (dNQuot.prodAssocEquiv R G K H n
            (dNQuot.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((dNQuot.prodAssocEquiv R K G H n).symm x)))) := by
  simpa [dNQuot.prod_commequiv_monoidhom,
    dNQuot.prod_assocequiv_monoidhom,
    dNQuot.prod_assocequiv_symmeq] using
    dNQuot.mapprod_commassoc_symmhexarigh (R := R) G H K n x

/-- Packaged reverse hexagon coherence for dimension layer-kernel equivalences (left). -/
theorem dLKern.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R ((H × K) × G) n) :
    dLKern.prodCommEquiv R (H × K) G n x =
      dLKern.prodAssocEquiv R G H K n
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((dLKern.prodAssocEquiv R H G K n).symm
            (dLKern.map (R := R)
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (dLKern.prodAssocEquiv R H K G n x)))) := by
  simpa [dLKern.prod_comm_equivapply,
    dLKern.prod_assoc_equivapply,
    dLKern.prod_assocequiv_symmapply] using
    dLKern.mappro_comma_symmh (R := R) G H K n x

/-- Packaged reverse hexagon coherence for dimension layer-kernel equivalences (right). -/
theorem dLKern.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : dLKern R (K × (G × H)) n) :
    dLKern.prodCommEquiv R K (G × H) n x =
      (dLKern.prodAssocEquiv R G H K n).symm
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (dLKern.prodAssocEquiv R G K H n
            (dLKern.map (R := R)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((dLKern.prodAssocEquiv R K G H n).symm x)))) := by
  simpa [dLKern.prod_comm_equivapply,
    dLKern.prod_assoc_equivapply,
    dLKern.prod_assocequiv_symmapply] using
    dLKern.mapprod_commassoc_symmhexarigh (R := R) G H K n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level packaged reverse hexagon for dimension quotient equivalences (left). -/
theorem dQuot.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dQuot.prodCommEquiv R (H × K) G n).toMonoidHom =
    (dQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((dQuot.prodAssocEquiv R H G K n).symm.toMonoidHom).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dQuot.prodAssocEquiv R H K G n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodco_equiv_symmh (R := R) G H K n x

/-- Hom-level packaged reverse hexagon for dimension quotient equivalences (right). -/
theorem dQuot.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dQuot.prodCommEquiv R K (G × H) n).toMonoidHom =
    ((dQuot.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dQuot.prodAssocEquiv R G K H n).toMonoidHom.comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((dQuot.prodAssocEquiv R K G H n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodcomm_equivassoc_symmhexarigh (R := R) G H K n x

/-- Hom-level packaged reverse hexagon for consecutive dimension quotient equivalences (left). -/
theorem dNQuot.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodCommEquiv R (H × K) G n).toMonoidHom =
    (dNQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((dNQuot.prodAssocEquiv R H G K n).symm.toMonoidHom).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dNQuot.prodAssocEquiv R H K G n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodco_equiv_symmh (R := R) G H K n x

/-- Hom-level packaged reverse hexagon for consecutive dimension quotient equivalences (right). -/
theorem dNQuot.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodCommEquiv R K (G × H) n).toMonoidHom =
    ((dNQuot.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dNQuot.prodAssocEquiv R G K H n).toMonoidHom.comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((dNQuot.prodAssocEquiv R K G H n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodcomm_equivassoc_symmhexarigh (R := R) G H K n x

/-- Hom-level packaged reverse hexagon for dimension layer-kernel equivalences (left). -/
theorem dLKern.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodCommEquiv R (H × K) G n).toMonoidHom =
    (dLKern.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((dLKern.prodAssocEquiv R H G K n).symm.toMonoidHom).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (dLKern.prodAssocEquiv R H K G n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodco_equiv_symmh (R := R) G H K n x)

/-- Hom-level packaged reverse hexagon for dimension layer-kernel equivalences (right). -/
theorem dLKern.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodCommEquiv R K (G × H) n).toMonoidHom =
    ((dLKern.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((dLKern.prodAssocEquiv R G K H n).toMonoidHom.comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((dLKern.prodAssocEquiv R K G H n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodcomm_equivassoc_symmhexarigh (R := R) G H K n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level packaged forward hexagon for dimension quotient equivalences (left). -/
theorem dQuot.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dQuot.prodCommEquiv R G (H × K) n).toMonoidHom =
    ((dQuot.prodAssocEquiv R H K G n).symm.toMonoidHom).comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dQuot.prodAssocEquiv R H G K n).toMonoidHom.comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((dQuot.prodAssocEquiv R G H K n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodcomm_equivassoc_hexagonleft (R := R) G H K n x

/-- Hom-level packaged forward hexagon for dimension quotient equivalences (right). -/
theorem dQuot.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dQuot.prodCommEquiv R (G × H) K n).toMonoidHom =
    (dQuot.prodAssocEquiv R K G H n).toMonoidHom.comp
      ((dQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((dQuot.prodAssocEquiv R G K H n).symm.toMonoidHom).comp
          ((dQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dQuot.prodAssocEquiv R G H K n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodcomm_equivassoc_hexagonright (R := R) G H K n x

/-- Hom-level packaged forward hexagon for consecutive dimension quotient equivalences (left). -/
theorem dNQuot.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodCommEquiv R G (H × K) n).toMonoidHom =
    ((dNQuot.prodAssocEquiv R H K G n).symm.toMonoidHom).comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dNQuot.prodAssocEquiv R H G K n).toMonoidHom.comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((dNQuot.prodAssocEquiv R G H K n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodcomm_equivassoc_hexagonleft (R := R) G H K n x

/-- Hom-level packaged forward hexagon for consecutive dimension quotient equivalences (right). -/
theorem dNQuot.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodCommEquiv R (G × H) K n).toMonoidHom =
    (dNQuot.prodAssocEquiv R K G H n).toMonoidHom.comp
      ((dNQuot.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((dNQuot.prodAssocEquiv R G K H n).symm.toMonoidHom).comp
          ((dNQuot.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dNQuot.prodAssocEquiv R G H K n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodcomm_equivassoc_hexagonright (R := R) G H K n x

/-- Hom-level packaged forward hexagon for dimension layer-kernel equivalences (left). -/
theorem dLKern.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodCommEquiv R G (H × K) n).toMonoidHom =
    ((dLKern.prodAssocEquiv R H K G n).symm.toMonoidHom).comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((dLKern.prodAssocEquiv R H G K n).toMonoidHom.comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((dLKern.prodAssocEquiv R G H K n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodcomm_equivassoc_hexagonleft (R := R) G H K n x)

/-- Hom-level packaged forward hexagon for dimension layer-kernel equivalences (right). -/
theorem dLKern.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodCommEquiv R (G × H) K n).toMonoidHom =
    (dLKern.prodAssocEquiv R K G H n).toMonoidHom.comp
      ((dLKern.map (R := R)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((dLKern.prodAssocEquiv R G K H n).symm.toMonoidHom).comp
          ((dLKern.map (R := R)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (dLKern.prodAssocEquiv R G H K n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodcomm_equivassoc_hexagonright (R := R) G H K n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level packaged pentagon for ordinary dimension quotient associators. -/
theorem dQuot.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dQuot.prodAssocEquiv R G H (K × L) n).toMonoidHom.comp
      (dQuot.prodAssocEquiv R (G × H) K L n).toMonoidHom =
    (dQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dQuot.prodAssocEquiv R G (H × K) L n).toMonoidHom.comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prod_assoc_equivpentagon (R := R) G H K L n x

/-- Hom-level packaged pentagon for consecutive dimension quotient associators. -/
theorem dNQuot.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dNQuot.prodAssocEquiv R G H (K × L) n).toMonoidHom.comp
      (dNQuot.prodAssocEquiv R (G × H) K L n).toMonoidHom =
    (dNQuot.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dNQuot.prodAssocEquiv R G (H × K) L n).toMonoidHom.comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prod_assoc_equivpentagon (R := R) G H K L n x

/-- Hom-level packaged pentagon for dimension layer-kernel associators. -/
theorem dLKern.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (dLKern.prodAssocEquiv R G H (K × L) n).toMonoidHom.comp
      (dLKern.prodAssocEquiv R (G × H) K L n).toMonoidHom =
    (dLKern.map (R := R)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((dLKern.prodAssocEquiv R G (H × K) L n).toMonoidHom.comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prod_assoc_equivpentagon (R := R) G H K L n x)

/-- Hom-level packaged reverse pentagon for ordinary dimension quotient associators. -/
theorem dQuot.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((dQuot.prodAssocEquiv R (G × H) K L n).symm.toMonoidHom).comp
      ((dQuot.prodAssocEquiv R G H (K × L) n).symm.toMonoidHom) =
    (dQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((dQuot.prodAssocEquiv R G (H × K) L n).symm.toMonoidHom).comp
        (dQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prod_assocequiv_symmpentagon (R := R) G H K L n x

/-- Hom-level packaged reverse pentagon for consecutive dimension quotient associators. -/
theorem dNQuot.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((dNQuot.prodAssocEquiv R (G × H) K L n).symm.toMonoidHom).comp
      ((dNQuot.prodAssocEquiv R G H (K × L) n).symm.toMonoidHom) =
    (dNQuot.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((dNQuot.prodAssocEquiv R G (H × K) L n).symm.toMonoidHom).comp
        (dNQuot.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prod_assocequiv_symmpentagon (R := R) G H K L n x

/-- Hom-level packaged reverse pentagon for dimension layer-kernel associators. -/
theorem dLKern.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((dLKern.prodAssocEquiv R (G × H) K L n).symm.toMonoidHom).comp
      ((dLKern.prodAssocEquiv R G H (K × L) n).symm.toMonoidHom) =
    (dLKern.map (R := R)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((dLKern.prodAssocEquiv R G (H × K) L n).symm.toMonoidHom).comp
        (dLKern.map (R := R)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prod_assocequiv_symmpentagon (R := R) G H K L n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Swapping twice is the identity on ordinary dimension quotient homs. -/
theorem dQuot.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((dQuot.prodCommEquiv R H G n).toMonoidHom).comp
      ((dQuot.prodCommEquiv R G H n).toMonoidHom) =
    MonoidHom.id (dQuot R (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, dQuot.prod_comm_equivapply] using
    dQuot.map_prodcomm_prodcomm (R := R) G H n x

/-- Swapping twice is the identity on consecutive dimension quotient homs. -/
theorem dNQuot.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((dNQuot.prodCommEquiv R H G n).toMonoidHom).comp
      ((dNQuot.prodCommEquiv R G H n).toMonoidHom) =
    MonoidHom.id (dSubgro R (G × H) n ⧸
      dNTerm R (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, dNQuot.prod_commequiv_monoidhom] using
    dNQuot.map_prodcomm_prodcomm (R := R) G H n x

/-- Swapping twice is the identity on dimension layer-kernel homs. -/
theorem dLKern.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((dLKern.prodCommEquiv R H G n).toMonoidHom).comp
      ((dLKern.prodCommEquiv R G H n).toMonoidHom) =
    MonoidHom.id (dLKern R (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, dLKern.prod_comm_equivapply] using
    congrArg Subtype.val
      (dLKern.map_prodcomm_prodcomm (R := R) G H n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Associator followed by its inverse is identity on dimension quotient homs. -/
theorem dQuot.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((dQuot.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      (dQuot.prodAssocEquiv R G H K n).toMonoidHom =
    MonoidHom.id (dQuot R ((G × H) × K) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodassoc_equivsymm_applyapply (R := R) G H K n x

/-- Inverse associator followed by associator is identity on dimension quotient homs. -/
theorem dQuot.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dQuot.prodAssocEquiv R G H K n).symm.toMonoidHom) =
    MonoidHom.id (dQuot R (G × (H × K)) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dQuot.prodassoc_equivapply_symmapply (R := R) G H K n x

/-- Associator followed by its inverse is identity on consecutive dimension quotient homs. -/
theorem dNQuot.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((dNQuot.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      (dNQuot.prodAssocEquiv R G H K n).toMonoidHom =
    MonoidHom.id (dSubgro R ((G × H) × K) n ⧸
      dNTerm R ((G × H) × K) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodassoc_equivsymm_eqapply (R := R) G H K n x

/-- Inverse associator followed by associator is identity on consecutive dimension quotient homs. -/
theorem dNQuot.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dNQuot.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dNQuot.prodAssocEquiv R G H K n).symm.toMonoidHom) =
    MonoidHom.id (dSubgro R (G × (H × K)) n ⧸
      dNTerm R (G × (H × K)) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    dNQuot.prodassoc_equivapply_symmapply (R := R) G H K n x

/-- Associator followed by its inverse is identity on dimension layer-kernel homs. -/
theorem dLKern.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((dLKern.prodAssocEquiv R G H K n).symm.toMonoidHom).comp
      (dLKern.prodAssocEquiv R G H K n).toMonoidHom =
    MonoidHom.id (dLKern R ((G × H) × K) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodassoc_equivsymm_applyapply (R := R) G H K n x)

/-- Inverse associator followed by associator is identity on dimension layer-kernel homs. -/
theorem dLKern.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prodAssocEquiv R G H K n).toMonoidHom.comp
      ((dLKern.prodAssocEquiv R G H K n).symm.toMonoidHom) =
    MonoidHom.id (dLKern R (G × (H × K)) n) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (dLKern.prodassoc_equivapply_symmapply (R := R) G H K n x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Integer-linear associator followed by its inverse is identity on dimension layer kernels. -/
theorem dLKern.prodas_lineq_compa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((dLKern.prod_assocint_linequiv (R := R) G H K n).symm.toLinearMap).comp
      (dLKern.prod_assocint_linequiv (R := R) G H K n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- Inverse then associator is identity on integer-linear dimension layer kernels. -/
theorem dLKern.prodas_lineq_symma
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (dLKern.prod_assocint_linequiv (R := R) G H K n).toLinearMap.comp
      ((dLKern.prod_assocint_linequiv (R := R) G H K n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp
end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Swapping twice is identity on integer-linear dimension layer-kernel maps. -/
theorem dLKern.prodco_lineq_selfl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) H G n).toLinearMap.comp
      (dLKern.prod_commint_linequiv (R := R) G H n).toLinearMap =
    LinearMap.id := by
  apply LinearMap.ext
  intro x
  cases x with | ofMul x' =>
    simpa [dLKern.prodcomm_intlin_equivapply,
      dLKern.map_int_linapply, dLKern.map_add_mul] using
      dLKern.map_prodcomm_prodcomm (R := R) G H n x'


end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- An integer-linear dimension layer swap followed by its inverse is identity. -/
theorem dLKern.prodco_lineq_compl
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((dLKern.prod_commint_linequiv (R := R) G H n).symm.toLinearMap).comp
      (dLKern.prod_commint_linequiv (R := R) G H n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- The inverse integer-linear dimension layer swap followed by swap is identity. -/
theorem dLKern.prodco_lineq_symml
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (dLKern.prod_commint_linequiv (R := R) G H n).toLinearMap.comp
      ((dLKern.prod_commint_linequiv (R := R) G H n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Congruence followed by its inverse is identity on dimension quotient homs. -/
theorem dQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dQuot.congr R G e n).symm.toMonoidHom).comp
      (dQuot.congr R G e n).toMonoidHom =
    MonoidHom.id (dQuot R G n) := by
  ext x
  change (dQuot.congr R G e n).symm
      ((dQuot.congr R G e n) x) = x
  exact (dQuot.congr R G e n).left_inv x

/-- Inverse congruence followed by congruence is identity on dimension quotient homs. -/
theorem dQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dQuot.congr R G e n).toMonoidHom.comp
      ((dQuot.congr R G e n).symm.toMonoidHom) =
    MonoidHom.id (dQuot R H n) := by
  ext x
  change (dQuot.congr R G e n)
      ((dQuot.congr R G e n).symm x) = x
  exact (dQuot.congr R G e n).right_inv x

/-- Congruence followed by its inverse is identity on dimension consecutive quotient homs. -/
theorem dNQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dNQuot.congr (R := R) e n).symm.toMonoidHom).comp
      (dNQuot.congr (R := R) e n).toMonoidHom =
    MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n) := by
  ext x
  change (dNQuot.congr (R := R) e n).symm
      ((dNQuot.congr (R := R) e n) x) = x
  exact (dNQuot.congr (R := R) e n).left_inv x

/-- Inverse congruence followed by congruence is identity on dimension consecutive quotient homs. -/
theorem dNQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dNQuot.congr (R := R) e n).toMonoidHom.comp
      ((dNQuot.congr (R := R) e n).symm.toMonoidHom) =
    MonoidHom.id (dSubgro R H n ⧸ dNTerm R H n) := by
  ext x
  change (dNQuot.congr (R := R) e n)
      ((dNQuot.congr (R := R) e n).symm x) = x
  exact (dNQuot.congr (R := R) e n).right_inv x

/-- Congruence followed by its inverse is identity on dimension layer-kernel homs. -/
theorem dLKern.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dLKern.congr (R := R) e n).symm.toMonoidHom).comp
      (dLKern.congr (R := R) e n).toMonoidHom =
    MonoidHom.id (dLKern R G n) := by
  ext x
  exact congrArg Subtype.val
    ((dLKern.congr (R := R) e n).left_inv x)

/-- Inverse congruence followed by congruence is identity on dimension layer-kernel homs. -/
theorem dLKern.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dLKern.congr (R := R) e n).toMonoidHom.comp
      ((dLKern.congr (R := R) e n).symm.toMonoidHom) =
    MonoidHom.id (dLKern R H n) := by
  ext x
  exact congrArg Subtype.val
    ((dLKern.congr (R := R) e n).right_inv x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- An integer-linear dimension layer congruence followed by its inverse is identity. -/
theorem dLKern.congrint_linsymm_complinmap
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dLKern.congrIntLinear (R := R) e n).symm.toLinearMap).comp
      (dLKern.congrIntLinear (R := R) e n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- The inverse integer-linear dimension layer congruence followed by congruence is identity. -/
theorem dLKern.congrint_lincomp_symmlinmap
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dLKern.congrIntLinear (R := R) e n).toLinearMap.comp
      ((dLKern.congrIntLinear (R := R) e n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Composition of dimension quotient congruence homs is congruence for the composite. -/
theorem dQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dQuot.congr R H f n).toMonoidHom.comp
      (dQuot.congr R G e n).toMonoidHom =
    (dQuot.congr R G (e.trans f) n).toMonoidHom := by
  ext x
  change ((dQuot.congr R G e n).trans
      (dQuot.congr R H f n)) x =
    (dQuot.congr R G (e.trans f) n) x
  exact congrArg
    (fun E : dQuot R G n ≃* dQuot R K n => E x)
    (dQuot.congr_trans (R := R) (G := G) e f n)

/-- Composition of consecutive dimension quotient congruence homs is congruence for
the composite. -/
theorem dNQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dNQuot.congr (R := R) f n).toMonoidHom.comp
      (dNQuot.congr (R := R) e n).toMonoidHom =
    (dNQuot.congr (R := R) (e.trans f) n).toMonoidHom := by
  ext x
  change ((dNQuot.congr (R := R) e n).trans
      (dNQuot.congr (R := R) f n)) x =
    (dNQuot.congr (R := R) (e.trans f) n) x
  exact congrArg
    (fun E : (dSubgro R G n ⧸ dNTerm R G n) ≃*
        (dSubgro R K n ⧸ dNTerm R K n) => E x)
    (dNQuot.congr_trans (R := R) e f n)

/-- Composition of dimension layer-kernel congruence homs is congruence for the composite. -/
theorem dLKern.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dLKern.congr (R := R) f n).toMonoidHom.comp
      (dLKern.congr (R := R) e n).toMonoidHom =
    (dLKern.congr (R := R) (e.trans f) n).toMonoidHom := by
  ext x
  exact congrArg Subtype.val <| congrArg
    (fun E : dLKern R G n ≃* dLKern R K n => E x)
    (dLKern.congr_trans (R := R) e f n)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The identity equivalence induces the identity hom on dimension quotients. -/
theorem dQuot.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dQuot.congr R G (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (dQuot R G n) := by
  ext x
  simp

/-- The identity equivalence induces the identity hom on consecutive dimension quotients. -/
theorem dNQuot.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dNQuot.congr (R := R) (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (dSubgro R G n ⧸ dNTerm R G n) := by
  ext x
  simp

/-- The identity equivalence induces the identity hom on dimension layer kernels. -/
theorem dLKern.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dLKern.congr (R := R) (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (dLKern R G n) := by
  ext x
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The identity equivalence induces the identity integer-linear map on dimension layer kernels. -/
theorem dLKern.congrint_linrefl_linmap
    (G : Type*) [Group G] (n : ℕ) :
    (dLKern.congrIntLinear (R := R) (MulEquiv.refl G) n).toLinearMap =
    LinearMap.id := by
  ext x
  cases x with
  | ofMul y =>
      simp [dLKern.congrIntLinear]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Composition of integer-linear dimension layer congruences is the composite congruence. -/
theorem dLKern.congrint_lintrans_linmap
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dLKern.congrIntLinear (R := R) f n).toLinearMap.comp
      (dLKern.congrIntLinear (R := R) e n).toLinearMap =
    (dLKern.congrIntLinear (R := R) (e.trans f) n).toLinearMap := by
  ext x
  cases x with
  | ofMul y =>
      simp [dLKern.congrIntLinear]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Term-quotient dimension congruence followed by its inverse is identity. -/
theorem dTQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((dTQuot.congr (R := R) e hmn).symm.toMonoidHom).comp
      (dTQuot.congr (R := R) e hmn).toMonoidHom =
    MonoidHom.id (dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) := by
  ext x
  change (dTQuot.congr (R := R) e hmn).symm
      ((dTQuot.congr (R := R) e hmn) x) = x
  exact (dTQuot.congr (R := R) e hmn).left_inv x

/-- Inverse term-quotient dimension congruence followed by congruence is identity. -/
theorem dTQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) e hmn).toMonoidHom.comp
      ((dTQuot.congr (R := R) e hmn).symm.toMonoidHom) =
    MonoidHom.id (dSubgro R H m ⧸
      dTSubgro (R := R) (G := H) hmn) := by
  ext x
  change (dTQuot.congr (R := R) e hmn)
      ((dTQuot.congr (R := R) e hmn).symm x) = x
  exact (dTQuot.congr (R := R) e hmn).right_inv x

/-- Transition-kernel dimension congruence followed by its inverse is identity. -/
theorem dTKern.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((dTKern.congr (R := R) e hmn).symm.toMonoidHom).comp
      (dTKern.congr (R := R) e hmn).toMonoidHom =
    MonoidHom.id (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  ext x
  exact congrArg Subtype.val
    ((dTKern.congr (R := R) e hmn).left_inv x)

/-- Inverse transition-kernel dimension congruence followed by congruence is identity. -/
theorem dTKern.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) e hmn).toMonoidHom.comp
      ((dTKern.congr (R := R) e hmn).symm.toMonoidHom) =
    MonoidHom.id (MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) := by
  ext x
  exact congrArg Subtype.val
    ((dTKern.congr (R := R) e hmn).right_inv x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Identity equivalence induces identity on arbitrary dimension term quotients. -/
theorem dTQuot.congr_refl_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) (MulEquiv.refl G) hmn).toMonoidHom =
    MonoidHom.id (dSubgro R G m ⧸
      dTSubgro (R := R) (G := G) hmn) := by
  ext x
  simp

/-- Identity equivalence induces identity on arbitrary dimension transition kernels. -/
theorem dTKern.congr_refl_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) (MulEquiv.refl G) hmn).toMonoidHom =
    MonoidHom.id (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  ext x
  simp

/-- Composition of dimension term-quotient congruence homs is congruence for the composite. -/
theorem dTQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) f hmn).toMonoidHom.comp
      (dTQuot.congr (R := R) e hmn).toMonoidHom =
    (dTQuot.congr (R := R) (e.trans f) hmn).toMonoidHom := by
  ext x
  change ((dTQuot.congr (R := R) e hmn).trans
      (dTQuot.congr (R := R) f hmn)) x =
    (dTQuot.congr (R := R) (e.trans f) hmn) x
  exact congrArg
    (fun E : (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) ≃*
        (dSubgro R K m ⧸ dTSubgro (R := R) (G := K) hmn) => E x)
    (dTQuot.congr_trans (R := R) e f hmn)

/-- Composition of dimension transition-kernel congruence homs is congruence for the composite. -/
theorem dTKern.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) f hmn).toMonoidHom.comp
      (dTKern.congr (R := R) e hmn).toMonoidHom =
    (dTKern.congr (R := R) (e.trans f) hmn).toMonoidHom := by
  ext x
  exact congrArg Subtype.val <| congrArg
    (fun E : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn) ≃*
        MonoidHom.ker (mapOfLe (R := R) (G := K) hmn) => E x)
    (dTKern.congr_trans (R := R) e f hmn)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The inverse dimension quotient congruence hom is the congruence hom
for the inverse isomorphism. -/
theorem dQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dQuot.congr R G e n).symm.toMonoidHom) =
      (dQuot.congr R H e.symm n).toMonoidHom := by
  rw [dQuot.congr_symm]

/-- The inverse consecutive dimension quotient congruence hom is induced by
the inverse isomorphism. -/
theorem dNQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dNQuot.congr (R := R) e n).symm.toMonoidHom) =
      (dNQuot.congr (R := R) e.symm n).toMonoidHom := by
  rw [dNQuot.congr_symm]

/-- The inverse dimension layer-kernel congruence hom is induced by
the inverse isomorphism. -/
theorem dLKern.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dLKern.congr (R := R) e n).symm.toMonoidHom) =
      (dLKern.congr (R := R) e.symm n).toMonoidHom := by
  rw [dLKern.congr_symm]

/-- The inverse arbitrary-term dimension quotient congruence hom is induced by
the inverse isomorphism. -/
theorem dTQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((dTQuot.congr (R := R) e hmn).symm.toMonoidHom) =
      (dTQuot.congr (R := R) e.symm hmn).toMonoidHom := by
  rw [dTQuot.congr_symm]

/-- The inverse dimension transition-kernel congruence hom is induced by
the inverse isomorphism. -/
theorem dTKern.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((dTKern.congr (R := R) e hmn).symm.toMonoidHom) =
      (dTKern.congr (R := R) e.symm hmn).toMonoidHom := by
  rw [dTKern.congr_symm]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The inverse integer-linear dimension layer congruence map is induced by
the inverse isomorphism. -/
theorem dLKern.congrint_linsymm_linmap
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((dLKern.congrIntLinear (R := R) e n).symm.toLinearMap) =
      (dLKern.congrIntLinear (R := R) e.symm n).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (dLKern.congrIntLinear (R := R) e n).injective
  cases x with
  | ofMul y =>
      simpa [dLKern.congrAdd] using
        ((dLKern.congr (R := R) e n).right_inv y).symm

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Identity isomorphism induces the identity integer-linear equivalence on dimension layers. -/
@[simp] theorem dLKern.congr_int_linrefl
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.congrIntLinear (R := R) (MulEquiv.refl G) n =
      LinearEquiv.refl ℤ (Additive (dLKern R G n)) := by
  ext x
  cases x with
  | ofMul y =>
      simp [dLKern.congrIntLinear, dLKern.congrAdd]

/-- Composition of integer-linear dimension layer congruences is the composite congruence. -/
@[simp] theorem dLKern.congr_int_lintrans
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dLKern.congrIntLinear (R := R) e n).trans
      (dLKern.congrIntLinear (R := R) f n) =
    dLKern.congrIntLinear (R := R) (e.trans f) n := by
  ext x
  cases x with
  | ofMul y =>
      simp [dLKern.congrIntLinear, dLKern.congrAdd]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The inverse integer-linear dimension layer equivalence is induced by the inverse isomorphism. -/
@[simp] theorem dLKern.congr_int_linsymm
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dLKern.congrIntLinear (R := R) e n).symm =
      dLKern.congrIntLinear (R := R) e.symm n := by
  apply LinearEquiv.ext
  intro x
  apply (dLKern.congrIntLinear (R := R) e n).injective
  cases x with
  | ofMul y =>
      simpa [dLKern.congrIntLinear, dLKern.congrAdd] using
        ((dLKern.congr (R := R) e n).right_inv y).symm

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise form of the automorphism action on dimension layer kernels. -/
@[simp] theorem dLKern.lin_aut_mapapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.linearAutMap (R := R) G n e x =
      dLKern.congrIntLinear (R := R) e n x := rfl

/-- Pointwise form of the automorphism action on the first dimension additive quotient. -/
@[simp] theorem dTAdditi.lin_aut_mapapply
    (G : Type*) [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.linearAutMap (R := R) G e x =
      dTAdditi.congrIntLinear (R := R) e x := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The first-layer integer-linear equivalence intertwines the automorphism actions
on the dimension layer kernel and on `G/D₂`. -/
theorem dimension_congr_naturality
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e).toLinearMap.comp
        (dimensionIntLinear (R := R) (G := G)).toLinearMap =
      (dimensionIntLinear (R := R) (G := G)).toLinearMap.comp
        (dLKern.congrIntLinear (R := R) e 1).toLinearMap := by
  ext x
  simpa [dTAdditi.congrIntLinear,
    dLKern.congrIntLinear]
    using (dimension_int_naturality (R := R)
      (φ := e.toMonoidHom) x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise intertwining form for the first dimension layer equivalence and automorphisms. -/
@[simp] theorem dimension_int_congr
    (G : Type*) [Group G] (e : MulAut G)
    (x : Additive (dLKern R G 1)) :
    dTAdditi.congrIntLinear (R := R) e
        (dimensionIntLinear (R := R) (G := G) x) =
      dimensionIntLinear (R := R) (G := G)
        (dLKern.congrIntLinear (R := R) e 1 x) := by
  have h := congrArg (fun f => f x)
    (dimension_congr_naturality (R := R) G e)
  simpa [LinearMap.comp_apply] using h

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalence-level intertwining of first dimension layer and quotient automorphism actions. -/
theorem dimension_congr_trans
    (G : Type*) [Group G] (e : MulAut G) :
    (dLKern.congrIntLinear (R := R) e 1).trans
        (dimensionIntLinear (R := R) (G := G)) =
      (dimensionIntLinear (R := R) (G := G)).trans
        (dTAdditi.congrIntLinear (R := R) e) := by
  ext x
  symm
  exact dimension_int_congr (R := R) G e x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Identity law for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.lin_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.linearAutMap (R := R) G n 1 = 1 :=
  map_one (dLKern.linearAutMap (R := R) G n)

/-- Multiplication law for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.lin_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    dLKern.linearAutMap (R := R) G n (e * f) =
      dLKern.linearAutMap (R := R) G n e *
        dLKern.linearAutMap (R := R) G n f :=
  map_mul (dLKern.linearAutMap (R := R) G n) e f

/-- Pointwise multiplication law for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.lin_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.linearAutMap (R := R) G n (e * f) x =
      dLKern.linearAutMap (R := R) G n e
        (dLKern.linearAutMap (R := R) G n f x) := by
  simp [dLKern.lin_aut_mapmul]

/-- Identity law for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.lin_aut_mapone
    (G : Type*) [Group G] :
    dTAdditi.linearAutMap (R := R) G 1 = 1 :=
  map_one (dTAdditi.linearAutMap (R := R) G)

/-- Multiplication law for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.lin_aut_mapmul
    (G : Type*) [Group G] (e f : MulAut G) :
    dTAdditi.linearAutMap (R := R) G (e * f) =
      dTAdditi.linearAutMap (R := R) G e *
        dTAdditi.linearAutMap (R := R) G f :=
  map_mul (dTAdditi.linearAutMap (R := R) G) e f

/-- Pointwise multiplication law for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.lin_autmap_mulapply
    (G : Type*) [Group G] (e f : MulAut G) (x : dTAdditi R G) :
    dTAdditi.linearAutMap (R := R) G (e * f) x =
      dTAdditi.linearAutMap (R := R) G e
        (dTAdditi.linearAutMap (R := R) G f x) := by
  simp [dTAdditi.lin_aut_mapmul]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse law for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.lin_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dLKern.linearAutMap (R := R) G n e⁻¹ =
      (dLKern.linearAutMap (R := R) G n e)⁻¹ :=
  map_inv (dLKern.linearAutMap (R := R) G n) e

/-- Left inverse cancellation for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.linaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.linearAutMap (R := R) G n e⁻¹
        (dLKern.linearAutMap (R := R) G n e x) = x := by
  simpa [dLKern.lin_aut_mapinv]
    using LinearEquiv.left_inv (dLKern.linearAutMap (R := R) G n e) x

/-- Inverse law for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.lin_aut_mapinv
    (G : Type*) [Group G] (e : MulAut G) :
    dTAdditi.linearAutMap (R := R) G e⁻¹ =
      (dTAdditi.linearAutMap (R := R) G e)⁻¹ :=
  map_inv (dTAdditi.linearAutMap (R := R) G) e

/-- Left inverse cancellation for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.linaut_mapinv_applyself
    (G : Type*) [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.linearAutMap (R := R) G e⁻¹
        (dTAdditi.linearAutMap (R := R) G e x) = x := by
  simpa [dTAdditi.lin_aut_mapinv]
    using LinearEquiv.left_inv (dTAdditi.linearAutMap (R := R) G e) x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Right inverse cancellation for the automorphism action on a dimension layer. -/
@[simp] theorem dLKern.linaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.linearAutMap (R := R) G n e
        (dLKern.linearAutMap (R := R) G n e⁻¹ x) = x := by
  rw [dLKern.lin_aut_mapinv]
  exact LinearEquiv.right_inv (dLKern.linearAutMap (R := R) G n e) x

/-- Right inverse cancellation for the automorphism action on the first dimension quotient. -/
@[simp] theorem dTAdditi.linaut_mapapply_invself
    (G : Type*) [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.linearAutMap (R := R) G e
        (dTAdditi.linearAutMap (R := R) G e⁻¹ x) = x := by
  rw [dTAdditi.lin_aut_mapinv]
  exact LinearEquiv.right_inv (dTAdditi.linearAutMap (R := R) G e) x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Applying an integer-linear dimension layer congruence and then its inverse cancels. -/
@[simp] theorem dLKern.congrint_linsymm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) e.symm n
        (dLKern.congrIntLinear (R := R) e n x) = x := by
  simpa [dLKern.congr_int_linsymm]
    using LinearEquiv.left_inv (dLKern.congrIntLinear (R := R) e n) x

/-- Applying the inverse integer-linear dimension layer congruence and then the original cancels. -/
@[simp] theorem dLKern.congrint_linapply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : Additive (dLKern R H n)) :
    dLKern.congrIntLinear (R := R) e n
        (dLKern.congrIntLinear (R := R) e.symm n x) = x := by
  simpa [dLKern.congr_int_linsymm]
    using LinearEquiv.right_inv (dLKern.congrIntLinear (R := R) e n) x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Applying a dimension quotient congruence and then its inverse cancels. -/
@[simp] theorem dQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dQuot R G n) :
    dQuot.congr R H e.symm n
        (dQuot.congr R G e n x) = x := by
  rw [← dQuot.congr_symm (R := R) (G := G) e n]
  exact (dQuot.congr R G e n).left_inv x

/-- Applying the inverse dimension quotient congruence and then the original cancels. -/
@[simp] theorem dQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dQuot R H n) :
    dQuot.congr R G e n
        (dQuot.congr R H e.symm n x) = x := by
  rw [← dQuot.congr_symm (R := R) (G := G) e n]
  exact (dQuot.congr R G e n).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Consecutive dimension quotient congruence followed by its inverse cancels. -/
@[simp] theorem dNQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.congr (R := R) e.symm n
        (dNQuot.congr (R := R) e n x) = x := by
  rw [← dNQuot.congr_symm (R := R) e n]
  exact (dNQuot.congr (R := R) e n).left_inv x

/-- Inverse consecutive dimension quotient congruence followed by the original cancels. -/
@[simp] theorem dNQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.congr (R := R) e n
        (dNQuot.congr (R := R) e.symm n x) = x := by
  rw [← dNQuot.congr_symm (R := R) e n]
  exact (dNQuot.congr (R := R) e n).right_inv x

/-- Dimension layer-kernel congruence followed by its inverse cancels. -/
@[simp] theorem dLKern.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dLKern R G n) :
    dLKern.congr (R := R) e.symm n
        (dLKern.congr (R := R) e n x) = x := by
  rw [← dLKern.congr_symm (R := R) e n]
  exact (dLKern.congr (R := R) e n).left_inv x

/-- Inverse dimension layer-kernel congruence followed by the original cancels. -/
@[simp] theorem dLKern.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dLKern R H n) :
    dLKern.congr (R := R) e n
        (dLKern.congr (R := R) e.symm n x) = x := by
  rw [← dLKern.congr_symm (R := R) e n]
  exact (dLKern.congr (R := R) e n).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Dimension term-quotient congruence followed by its inverse cancels. -/
@[simp] theorem dTQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dTQuot.congr (R := R) e.symm hmn
        (dTQuot.congr (R := R) e hmn x) = x := by
  rw [← dTQuot.congr_symm (R := R) e hmn]
  exact (dTQuot.congr (R := R) e hmn).left_inv x

/-- Inverse dimension term-quotient congruence followed by the original cancels. -/
@[simp] theorem dTQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dTQuot.congr (R := R) e hmn
        (dTQuot.congr (R := R) e.symm hmn x) = x := by
  rw [← dTQuot.congr_symm (R := R) e hmn]
  exact (dTQuot.congr (R := R) e hmn).right_inv x

/-- Dimension transition-kernel congruence followed by its inverse cancels. -/
@[simp] theorem dTKern.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.congr (R := R) e.symm hmn
        (dTKern.congr (R := R) e hmn x) = x := by
  rw [← dTKern.congr_symm (R := R) e hmn]
  exact (dTKern.congr (R := R) e hmn).left_inv x

/-- Inverse dimension transition-kernel congruence followed by the original cancels. -/
@[simp] theorem dTKern.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dTKern.congr (R := R) e hmn
        (dTKern.congr (R := R) e.symm hmn x) = x := by
  rw [← dTKern.congr_symm (R := R) e hmn]
  exact (dTKern.congr (R := R) e hmn).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Dimension subgroup congruence followed by its inverse cancels. -/
@[simp] theorem dSubgro.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dSubgro R G n) :
    dSubgro.congr (R := R) e.symm n
        (dSubgro.congr (R := R) e n x) = x := by
  rw [← dSubgro.congr_symm (R := R) e n]
  exact (dSubgro.congr (R := R) e n).left_inv x

/-- Inverse dimension subgroup congruence followed by the original cancels. -/
@[simp] theorem dSubgro.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dSubgro R H n) :
    dSubgro.congr (R := R) e n
        (dSubgro.congr (R := R) e.symm n x) = x := by
  rw [← dSubgro.congr_symm (R := R) e n]
  exact (dSubgro.congr (R := R) e n).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise composition law for dimension subgroup congruences. -/
@[simp] theorem dSubgro.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : dSubgro R A n) :
    dSubgro.congr (R := R) f n (dSubgro.congr (R := R) e n x) =
      dSubgro.congr (R := R) (e.trans f) n x := by
  change ((dSubgro.congr (R := R) e n).trans
      (dSubgro.congr (R := R) f n)) x = _
  rw [dSubgro.congr_trans]

/-- Identity dimension subgroup congruence acts pointwise as identity. -/
@[simp] theorem dSubgro.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : dSubgro R A n) :
    dSubgro.congr (R := R) (MulEquiv.refl A) n x = x := by
  rw [dSubgro.congr_refl]
  rfl

/-- Pointwise composition law for arbitrary dimension term-quotient congruences. -/
@[simp] theorem dTQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R A m ⧸ dTSubgro (R := R) (G := A) hmn) :
    dTQuot.congr (R := R) f hmn
        (dTQuot.congr (R := R) e hmn x) =
      dTQuot.congr (R := R) (e.trans f) hmn x := by
  change ((dTQuot.congr (R := R) e hmn).trans
      (dTQuot.congr (R := R) f hmn)) x = _
  rw [dTQuot.congr_trans]

/-- Identity arbitrary dimension term-quotient congruence acts pointwise as identity. -/
@[simp] theorem dTQuot.congr_refl_apply
    {A : Type*} [Group A] {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R A m ⧸ dTSubgro (R := R) (G := A) hmn) :
    dTQuot.congr (R := R) (MulEquiv.refl A) hmn x = x := by
  rw [dTQuot.congr_refl]
  rfl

/-- Pointwise composition law for dimension transition-kernel congruences. -/
@[simp] theorem dTKern.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := A) hmn)) :
    dTKern.congr (R := R) f hmn
        (dTKern.congr (R := R) e hmn x) =
      dTKern.congr (R := R) (e.trans f) hmn x := by
  change ((dTKern.congr (R := R) e hmn).trans
      (dTKern.congr (R := R) f hmn)) x = _
  rw [dTKern.congr_trans]

/-- Identity dimension transition-kernel congruence acts pointwise as identity. -/
@[simp] theorem dTKern.congr_refl_apply
    {A : Type*} [Group A] {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := A) hmn)) :
    dTKern.congr (R := R) (MulEquiv.refl A) hmn x = x := by
  rw [dTKern.congr_refl]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise composition law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congr_intlin_transapply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ)
    (x : Additive (dLKern R A n)) :
    dLKern.congrIntLinear (R := R) f n
        (dLKern.congrIntLinear (R := R) e n x) =
      dLKern.congrIntLinear (R := R) (e.trans f) n x := by
  change ((dLKern.congrIntLinear (R := R) e n).trans
      (dLKern.congrIntLinear (R := R) f n)) x = _
  rw [dLKern.congr_int_lintrans]

/-- Identity integer-linear dimension layer congruence acts pointwise as identity. -/
@[simp] theorem dLKern.congr_intlin_reflapply
    {A : Type*} [Group A] (n : ℕ)
    (x : Additive (dLKern R A n)) :
    dLKern.congrIntLinear (R := R) (MulEquiv.refl A) n x = x := by
  rw [dLKern.congr_int_linrefl]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism action on dimension quotients sends identity to identity. -/
@[simp] theorem dQuot.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    dQuot.mulAutMap R G n 1 = 1 :=
  map_one (dQuot.mulAutMap R G n)

/-- Automorphism action on dimension quotients preserves multiplication. -/
@[simp] theorem dQuot.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    dQuot.mulAutMap R G n (e * f) =
      dQuot.mulAutMap R G n e * dQuot.mulAutMap R G n f :=
  map_mul (dQuot.mulAutMap R G n) e f

/-- Pointwise multiplication law for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) (x : dQuot R G n) :
    dQuot.mulAutMap R G n (e * f) x =
      dQuot.mulAutMap R G n e (dQuot.mulAutMap R G n f x) := by
  simp [dQuot.mul_aut_mapmul]

/-- Pointwise identity law for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ) (x : dQuot R G n) :
    dQuot.mulAutMap R G n 1 x = x := by
  simp

/-- Automorphism action on consecutive dimension quotients sends identity to identity. -/
@[simp] theorem dNQuot.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    dNQuot.mulAutMap (R := R) G n 1 = 1 :=
  map_one (dNQuot.mulAutMap (R := R) G n)

/-- Automorphism action on consecutive dimension quotients preserves multiplication. -/
@[simp] theorem dNQuot.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    dNQuot.mulAutMap (R := R) G n (e * f) =
      dNQuot.mulAutMap (R := R) G n e *
        dNQuot.mulAutMap (R := R) G n f :=
  map_mul (dNQuot.mulAutMap (R := R) G n) e f

/-- Pointwise multiplication law for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.mulAutMap (R := R) G n (e * f) x =
      dNQuot.mulAutMap (R := R) G n e
        (dNQuot.mulAutMap (R := R) G n f x) := by
  simp [dNQuot.mul_aut_mapmul]

/-- Pointwise identity law for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.mulAutMap (R := R) G n 1 x = x := by
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism action on dimension layer kernels sends identity to identity. -/
@[simp] theorem dLKern.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.mulAutMap (R := R) G n 1 = 1 :=
  map_one (dLKern.mulAutMap (R := R) G n)

/-- Automorphism action on dimension layer kernels preserves multiplication. -/
@[simp] theorem dLKern.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    dLKern.mulAutMap (R := R) G n (e * f) =
      dLKern.mulAutMap (R := R) G n e *
        dLKern.mulAutMap (R := R) G n f :=
  map_mul (dLKern.mulAutMap (R := R) G n) e f

/-- Pointwise multiplication law for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : dLKern R G n) :
    dLKern.mulAutMap (R := R) G n (e * f) x =
      dLKern.mulAutMap (R := R) G n e
        (dLKern.mulAutMap (R := R) G n f x) := by
  simp [dLKern.mul_aut_mapmul]

/-- Pointwise identity law for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ) (x : dLKern R G n) :
    dLKern.mulAutMap (R := R) G n 1 x = x := by
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism action on arbitrary dimension term quotients sends identity to identity. -/
@[simp] theorem dTQuot.mul_aut_mapone
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dTQuot.mulAutMap (R := R) G hmn 1 = 1 :=
  map_one (dTQuot.mulAutMap (R := R) G hmn)

/-- Automorphism action on arbitrary dimension term quotients preserves multiplication. -/
@[simp] theorem dTQuot.mul_aut_mapmul
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    dTQuot.mulAutMap (R := R) G hmn (e * f) =
      dTQuot.mulAutMap (R := R) G hmn e *
        dTQuot.mulAutMap (R := R) G hmn f :=
  map_mul (dTQuot.mulAutMap (R := R) G hmn) e f

/-- Pointwise multiplication law for arbitrary dimension term quotient actions. -/
@[simp] theorem dTQuot.mul_autmap_mulapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dTQuot.mulAutMap (R := R) G hmn (e * f) x =
      dTQuot.mulAutMap (R := R) G hmn e
        (dTQuot.mulAutMap (R := R) G hmn f x) := by
  simp [dTQuot.mul_aut_mapmul]

/-- Pointwise identity law for arbitrary dimension term quotient actions. -/
@[simp] theorem dTQuot.mul_autmap_oneapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dTQuot.mulAutMap (R := R) G hmn 1 x = x := by
  simp

/-- Automorphism action on dimension transition kernels sends identity to identity. -/
@[simp] theorem dTKern.mul_aut_mapone
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dTKern.mulAutMap (R := R) (G := G) hmn 1 = 1 :=
  map_one (dTKern.mulAutMap (R := R) (G := G) hmn)

/-- Automorphism action on dimension transition kernels preserves multiplication. -/
@[simp] theorem dTKern.mul_aut_mapmul
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    dTKern.mulAutMap (R := R) (G := G) hmn (e * f) =
      dTKern.mulAutMap (R := R) (G := G) hmn e *
        dTKern.mulAutMap (R := R) (G := G) hmn f :=
  map_mul (dTKern.mulAutMap (R := R) (G := G) hmn) e f

/-- Pointwise multiplication law for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mul_autmap_mulapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.mulAutMap (R := R) (G := G) hmn (e * f) x =
      dTKern.mulAutMap (R := R) (G := G) hmn e
        (dTKern.mulAutMap (R := R) (G := G) hmn f x) := by
  simp [dTKern.mul_aut_mapmul]

/-- Pointwise identity law for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mul_autmap_oneapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.mulAutMap (R := R) (G := G) hmn 1 x = x := by
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse law for automorphism action on dimension quotients. -/
@[simp] theorem dQuot.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dQuot.mulAutMap R G n e⁻¹ =
      (dQuot.mulAutMap R G n e)⁻¹ :=
  map_inv (dQuot.mulAutMap R G n) e

/-- Left inverse cancellation for dimension quotient actions. -/
@[simp] theorem dQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dQuot R G n) :
    dQuot.mulAutMap R G n e⁻¹ (dQuot.mulAutMap R G n e x) = x := by
  simp [dQuot.mul_aut_mapinv]

/-- Right inverse cancellation for dimension quotient actions. -/
@[simp] theorem dQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dQuot R G n) :
    dQuot.mulAutMap R G n e (dQuot.mulAutMap R G n e⁻¹ x) = x := by
  rw [dQuot.mul_aut_mapinv]
  exact (dQuot.mulAutMap R G n e).right_inv x

/-- Inverse law for automorphism action on consecutive dimension quotients. -/
@[simp] theorem dNQuot.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dNQuot.mulAutMap (R := R) G n e⁻¹ =
      (dNQuot.mulAutMap (R := R) G n e)⁻¹ :=
  map_inv (dNQuot.mulAutMap (R := R) G n) e

/-- Left inverse cancellation for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.mulAutMap (R := R) G n e⁻¹
        (dNQuot.mulAutMap (R := R) G n e x) = x := by
  simpa [dNQuot.mul_aut_mapinv]
    using (dNQuot.mulAutMap (R := R) G n e).left_inv x

/-- Right inverse cancellation for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.mulAutMap (R := R) G n e
        (dNQuot.mulAutMap (R := R) G n e⁻¹ x) = x := by
  rw [dNQuot.mul_aut_mapinv]
  exact (dNQuot.mulAutMap (R := R) G n e).right_inv x

/-- Inverse law for automorphism action on dimension layer kernels. -/
@[simp] theorem dLKern.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dLKern.mulAutMap (R := R) G n e⁻¹ =
      (dLKern.mulAutMap (R := R) G n e)⁻¹ :=
  map_inv (dLKern.mulAutMap (R := R) G n) e

/-- Left inverse cancellation for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dLKern R G n) :
    dLKern.mulAutMap (R := R) G n e⁻¹
        (dLKern.mulAutMap (R := R) G n e x) = x := by
  simpa [dLKern.mul_aut_mapinv]
    using (dLKern.mulAutMap (R := R) G n e).left_inv x

/-- Right inverse cancellation for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dLKern R G n) :
    dLKern.mulAutMap (R := R) G n e
        (dLKern.mulAutMap (R := R) G n e⁻¹ x) = x := by
  rw [dLKern.mul_aut_mapinv]
  exact (dLKern.mulAutMap (R := R) G n e).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse law for automorphism action on arbitrary dimension term quotients. -/
@[simp] theorem dTQuot.mul_aut_mapinv
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTQuot.mulAutMap (R := R) G hmn e⁻¹ =
      (dTQuot.mulAutMap (R := R) G hmn e)⁻¹ :=
  map_inv (dTQuot.mulAutMap (R := R) G hmn) e

/-- Left inverse cancellation for arbitrary dimension term quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dTQuot.mulAutMap (R := R) G hmn e⁻¹
        (dTQuot.mulAutMap (R := R) G hmn e x) = x := by
  simpa [dTQuot.mul_aut_mapinv]
    using (dTQuot.mulAutMap (R := R) G hmn e).left_inv x

/-- Right inverse cancellation for arbitrary dimension term quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dTQuot.mulAutMap (R := R) G hmn e
        (dTQuot.mulAutMap (R := R) G hmn e⁻¹ x) = x := by
  rw [dTQuot.mul_aut_mapinv]
  exact (dTQuot.mulAutMap (R := R) G hmn e).right_inv x

/-- Inverse law for automorphism action on dimension transition kernels. -/
@[simp] theorem dTKern.mul_aut_mapinv
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹ =
      (dTKern.mulAutMap (R := R) (G := G) hmn e)⁻¹ :=
  map_inv (dTKern.mulAutMap (R := R) (G := G) hmn) e

/-- Left inverse cancellation for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapinv_applyself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹
        (dTKern.mulAutMap (R := R) (G := G) hmn e x) = x := by
  simpa [dTKern.mul_aut_mapinv]
    using (dTKern.mulAutMap (R := R) (G := G) hmn e).left_inv x

/-- Right inverse cancellation for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapapply_invself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dTKern.mulAutMap (R := R) (G := G) hmn e
        (dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹ x) = x := by
  rw [dTKern.mul_aut_mapinv]
  exact (dTKern.mulAutMap (R := R) (G := G) hmn e).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Unfold the automorphism action on an ordinary dimension quotient. -/
@[simp] theorem dQuot.mul_aut_mapapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dQuot R G n) :
    dQuot.mulAutMap R G n e x =
      dQuot.congr R G e n x := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Symmetric orientation of the inverse action on dimension quotients. -/
@[simp] theorem dQuot.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dQuot.mulAutMap R G n e).symm =
      dQuot.mulAutMap R G n e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on consecutive dimension quotients. -/
@[simp] theorem dNQuot.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dNQuot.mulAutMap (R := R) G n e).symm =
      dNQuot.mulAutMap (R := R) G n e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on dimension layer kernels. -/
@[simp] theorem dLKern.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.mulAutMap (R := R) G n e).symm =
      dLKern.mulAutMap (R := R) G n e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on arbitrary dimension term quotients. -/
@[simp] theorem dTQuot.mul_aut_mapsymm
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTQuot.mulAutMap (R := R) G hmn e).symm =
      dTQuot.mulAutMap (R := R) G hmn e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on dimension transition kernels. -/
@[simp] theorem dTKern.mul_aut_mapsymm
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTKern.mulAutMap (R := R) (G := G) hmn e).symm =
      dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹ := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise form of the symmetric inverse action on dimension quotients. -/
@[simp] theorem dQuot.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dQuot R G n) :
    (dQuot.mulAutMap R G n e).symm x =
      dQuot.mulAutMap R G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on consecutive dimension quotients. -/
@[simp] theorem dNQuot.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.mulAutMap (R := R) G n e).symm x =
      dNQuot.mulAutMap (R := R) G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on dimension layer kernels. -/
@[simp] theorem dLKern.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : dLKern R G n) :
    (dLKern.mulAutMap (R := R) G n e).symm x =
      dLKern.mulAutMap (R := R) G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on arbitrary dimension term quotients. -/
@[simp] theorem dTQuot.mul_autmap_symmapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dTQuot.mulAutMap (R := R) G hmn e).symm x =
      dTQuot.mulAutMap (R := R) G hmn e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on dimension transition kernels. -/
@[simp] theorem dTKern.mul_autmap_symmapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dTKern.mulAutMap (R := R) (G := G) hmn e).symm x =
      dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹ x := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Coercion of the automorphism action on dimension quotients to its underlying map. -/
@[simp] theorem dQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dQuot.mulAutMap R G n e).toMonoidHom =
      dQuot.map (R := R) e.toMonoidHom n := rfl

/-- Coercion of the automorphism action on consecutive dimension quotients. -/
@[simp] theorem dNQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dNQuot.mulAutMap (R := R) G n e).toMonoidHom =
      dNQuot.map (R := R) e.toMonoidHom n := rfl

/-- Coercion of the automorphism action on dimension layer kernels. -/
@[simp] theorem dLKern.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.mulAutMap (R := R) G n e).toMonoidHom =
      dLKern.map (R := R) e.toMonoidHom n := rfl

/-- Coercion of a term-quotient congruence to its underlying homomorphism. -/
@[simp] theorem dTQuot.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.congr (R := R) e hmn).toMonoidHom =
      dimensionTerm (R := R) e.toMonoidHom hmn := rfl

/-- Coercion of the automorphism action on arbitrary dimension term quotients. -/
@[simp] theorem dTQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTQuot.mulAutMap (R := R) G hmn e).toMonoidHom =
      dimensionTerm (R := R) e.toMonoidHom hmn := rfl

/-- Coercion of a transition-kernel congruence to its underlying homomorphism. -/
@[simp] theorem dTKern.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.congr (R := R) e hmn).toMonoidHom =
      dimensionTransition (R := R) e.toMonoidHom hmn := rfl

/-- Coercion of the automorphism action on dimension transition kernels. -/
@[simp] theorem dTKern.mul_autmap_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTKern.mulAutMap (R := R) (G := G) hmn e).toMonoidHom =
      dimensionTransition (R := R) e.toMonoidHom hmn := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level left inverse for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dQuot.mulAutMap R G n e⁻¹).toMonoidHom).comp
        (dQuot.mulAutMap R G n e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, dQuot.mul_aut_mapsymm]
    using (dQuot.mulAutMap R G n e).left_inv x

/-- Hom-level right inverse for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dQuot.mulAutMap R G n e).toMonoidHom).comp
        (dQuot.mulAutMap R G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp [MonoidHom.comp_apply, dQuot.mul_aut_mapsymm]

/-- Hom-level left inverse for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dNQuot.mulAutMap (R := R) G n e⁻¹).toMonoidHom).comp
        (dNQuot.mulAutMap (R := R) G n e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, dNQuot.mul_aut_mapsymm]
    using (dNQuot.mulAutMap (R := R) G n e).left_inv x

/-- Hom-level right inverse for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dNQuot.mulAutMap (R := R) G n e).toMonoidHom).comp
        (dNQuot.mulAutMap (R := R) G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp [MonoidHom.comp_apply, dNQuot.mul_aut_mapsymm]

/-- Hom-level left inverse for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dLKern.mulAutMap (R := R) G n e⁻¹).toMonoidHom).comp
        (dLKern.mulAutMap (R := R) G n e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, dLKern.mul_aut_mapsymm]
    using (dLKern.mulAutMap (R := R) G n e).left_inv x

/-- Hom-level right inverse for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((dLKern.mulAutMap (R := R) G n e).toMonoidHom).comp
        (dLKern.mulAutMap (R := R) G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp [MonoidHom.comp_apply, dLKern.mul_aut_mapsymm]

/-- Hom-level left inverse for arbitrary dimension term-quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((dTQuot.mulAutMap (R := R) G hmn e⁻¹).toMonoidHom).comp
        (dTQuot.mulAutMap (R := R) G hmn e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, dTQuot.mul_aut_mapsymm]
    using (dTQuot.mulAutMap (R := R) G hmn e).left_inv x

/-- Hom-level right inverse for arbitrary dimension term-quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((dTQuot.mulAutMap (R := R) G hmn e).toMonoidHom).comp
        (dTQuot.mulAutMap (R := R) G hmn e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp [MonoidHom.comp_apply, dTQuot.mul_aut_mapsymm]

/-- Hom-level left inverse for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹).toMonoidHom).comp
        (dTKern.mulAutMap (R := R) (G := G) hmn e).toMonoidHom =
      MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, dTKern.mul_aut_mapsymm]
    using (dTKern.mulAutMap (R := R) (G := G) hmn e).left_inv x

/-- Hom-level right inverse for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((dTKern.mulAutMap (R := R) (G := G) hmn e).toMonoidHom).comp
        (dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹).toMonoidHom =
      MonoidHom.id _ := by
  ext x
  simp [MonoidHom.comp_apply, dTKern.mul_aut_mapsymm]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level identity for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dQuot.mulAutMap R G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((dQuot.mulAutMap R G n e).toMonoidHom).comp
        (dQuot.mulAutMap R G n f).toMonoidHom =
      (dQuot.mulAutMap R G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dNQuot.mulAutMap (R := R) G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((dNQuot.mulAutMap (R := R) G n e).toMonoidHom).comp
        (dNQuot.mulAutMap (R := R) G n f).toMonoidHom =
      (dNQuot.mulAutMap (R := R) G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (dLKern.mulAutMap (R := R) G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((dLKern.mulAutMap (R := R) G n e).toMonoidHom).comp
        (dLKern.mulAutMap (R := R) G n f).toMonoidHom =
      (dLKern.mulAutMap (R := R) G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for arbitrary dimension term-quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (dTQuot.mulAutMap (R := R) G hmn 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for arbitrary dimension term-quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    ((dTQuot.mulAutMap (R := R) G hmn e).toMonoidHom).comp
        (dTQuot.mulAutMap (R := R) G hmn f).toMonoidHom =
      (dTQuot.mulAutMap (R := R) G hmn (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapone_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (dTKern.mulAutMap (R := R) (G := G) hmn 1).toMonoidHom =
      MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    ((dTKern.mulAutMap (R := R) (G := G) hmn e).toMonoidHom).comp
        (dTKern.mulAutMap (R := R) (G := G) hmn f).toMonoidHom =
      (dTKern.mulAutMap (R := R) (G := G) hmn (e * f)).toMonoidHom := by
  ext x; simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Symmetric orientation for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.lin_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e).symm =
      dLKern.linearAutMap (R := R) G n e⁻¹ := by
  change (dLKern.congrIntLinear (R := R) e n).symm =
    dLKern.congrIntLinear (R := R) (e⁻¹ : MulAut G) n
  exact dLKern.congr_int_linsymm (R := R) G G e n

/-- Underlying linear map of an integer-linear dimension layer action. -/
@[simp] theorem dLKern.lin_autmap_linmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e).toLinearMap =
      (dLKern.congrIntLinear (R := R) e n).toLinearMap := rfl

/-- Hom-level identity for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.linaut_mapone_linmap
    (G : Type*) [Group G] (n : ℕ) :
    (dLKern.linearAutMap (R := R) G n 1).toLinearMap = LinearMap.id := by
  ext x; simp

/-- Symmetric orientation for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.lin_aut_mapsymm
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e).symm =
      dTAdditi.linearAutMap (R := R) G e⁻¹ := rfl

/-- Underlying linear map of the first dimension additive automorphism action. -/
@[simp] theorem dTAdditi.lin_autmap_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e).toLinearMap =
      dTAdditi.mapIntLinear (R := R) e.toMonoidHom := rfl

/-- Hom-level identity for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.linaut_mapone_linmap
    (G : Type*) [Group G] :
    (dTAdditi.linearAutMap (R := R) G 1).toLinearMap = LinearMap.id := by
  ext x; simp

/-- Hom-level composition for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.linaut_mapcomp_linmap
    (G : Type*) [Group G] (e f : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e).toLinearMap.comp
        (dTAdditi.linearAutMap (R := R) G f).toLinearMap =
      (dTAdditi.linearAutMap (R := R) G (e * f)).toLinearMap := by
  ext x; simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise symmetric orientation for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.lin_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    (dLKern.linearAutMap (R := R) G n e).symm x =
      dLKern.linearAutMap (R := R) G n e⁻¹ x := by
  rw [dLKern.lin_aut_mapsymm]

/-- Left inverse at the underlying-linear-map level for dimension layer actions. -/
@[simp] theorem dLKern.linaut_mapinv_complinmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e⁻¹).toLinearMap.comp
        (dLKern.linearAutMap (R := R) G n e).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, dLKern.lin_aut_mapsymm]
    using (dLKern.linearAutMap (R := R) G n e).left_inv x

/-- Right inverse at the underlying-linear-map level for dimension layer actions. -/
@[simp] theorem dLKern.linaut_mapcomp_invlinmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e).toLinearMap.comp
        (dLKern.linearAutMap (R := R) G n e⁻¹).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, dLKern.lin_aut_mapsymm]
    using (dLKern.linearAutMap (R := R) G n e).right_inv x

/-- Pointwise symmetric orientation for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.lin_autmap_symmapply
    (G : Type*) [Group G] (e : MulAut G) (x : dTAdditi R G) :
    (dTAdditi.linearAutMap (R := R) G e).symm x =
      dTAdditi.linearAutMap (R := R) G e⁻¹ x := rfl

/-- Left inverse at the underlying-linear-map level for the first dimension action. -/
@[simp] theorem dTAdditi.linaut_mapinv_complinmap
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e⁻¹).toLinearMap.comp
        (dTAdditi.linearAutMap (R := R) G e).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, dTAdditi.lin_aut_mapsymm]
    using (dTAdditi.linearAutMap (R := R) G e).left_inv x

/-- Right inverse at the underlying-linear-map level for the first dimension action. -/
@[simp] theorem dTAdditi.linaut_mapcomp_invlinmap
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e).toLinearMap.comp
        (dTAdditi.linearAutMap (R := R) G e⁻¹).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, dTAdditi.lin_aut_mapsymm]
    using (dTAdditi.linearAutMap (R := R) G e).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level composition for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.linaut_mapcomp_linmap
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e).toLinearMap.comp
        (dLKern.linearAutMap (R := R) G n f).toLinearMap =
      (dLKern.linearAutMap (R := R) G n (e * f)).toLinearMap := by
  ext x
  exact congrArg Subtype.val (congrArg Additive.toMul
    (dLKern.lin_autmap_mulapply (R := R) G n e f x).symm)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Symmetric orientation for the defining integer-linear equivalence on the first
dimension quotient. -/
@[simp] theorem dTAdditi.congr_int_linsymm
    {G : Type*} [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e).symm =
      dTAdditi.congrIntLinear (R := R) e.symm := rfl

/-- Pointwise symmetric orientation for the defining integer-linear equivalence on the first
dimension quotient. -/
@[simp] theorem dTAdditi.congr_intlin_symmapply
    {G : Type*} [Group G] (e : MulAut G) (x : dTAdditi R G) :
    (dTAdditi.congrIntLinear (R := R) e).symm x =
      dTAdditi.congrIntLinear (R := R) e.symm x := rfl

/-- Underlying-map form of the symmetric orientation for the first dimension quotient. -/
@[simp] theorem dTAdditi.congrint_linsymm_linmap
    {G : Type*} [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e).symm.toLinearMap =
      (dTAdditi.congrIntLinear (R := R) e.symm).toLinearMap := by
  rw [dTAdditi.congr_int_linsymm]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level identity for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congrint_linone_linmap
    (G : Type*) [Group G] :
    (dTAdditi.congrIntLinear (R := R) (1 : MulAut G)).toLinearMap =
      LinearMap.id := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.linaut_mapone_linmap (R := R) G)

/-- Hom-level composition for the defining first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congrint_lincomp_linmap
    {G : Type*} [Group G] (e f : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e).toLinearMap.comp
        (dTAdditi.congrIntLinear (R := R) f).toLinearMap =
      (dTAdditi.congrIntLinear (R := R) (e * f)).toLinearMap := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.linaut_mapcomp_linmap (R := R) G e f)

/-- Left inverse at the underlying-linear-map level for first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congrint_lininv_complinmap
    {G : Type*} [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e⁻¹).toLinearMap.comp
        (dTAdditi.congrIntLinear (R := R) e).toLinearMap = LinearMap.id := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.linaut_mapinv_complinmap (R := R) G e)

/-- Right inverse at the underlying-linear-map level for first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congrint_lincomp_invlinmap
    {G : Type*} [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e).toLinearMap.comp
        (dTAdditi.congrIntLinear (R := R) e⁻¹).toLinearMap = LinearMap.id := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.linaut_mapcomp_invlinmap (R := R) G e)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalence-level identity for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congr_int_linone
    (G : Type*) [Group G] :
    dTAdditi.congrIntLinear (R := R) (1 : MulAut G) = 1 := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.lin_aut_mapone (R := R) G)

/-- Equivalence-level multiplication law for the defining first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congr_int_linmul
    {G : Type*} [Group G] (e f : MulAut G) :
    dTAdditi.congrIntLinear (R := R) (e * f) =
      dTAdditi.congrIntLinear (R := R) e *
        dTAdditi.congrIntLinear (R := R) f := by
  simpa [dTAdditi.linearAutMap] using
    (dTAdditi.lin_aut_mapmul (R := R) G e f)

/-- Pointwise identity law for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congr_intlin_oneapply
    (G : Type*) [Group G] (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) (1 : MulAut G) x = x := by
  simp

/-- Pointwise multiplication law for the defining first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congr_intlin_mulapply
    {G : Type*} [Group G] (e f : MulAut G) (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) (e * f) x =
      dTAdditi.congrIntLinear (R := R) e
        (dTAdditi.congrIntLinear (R := R) f x) := by
  exact
    (dTAdditi.lin_autmap_mulapply (R := R) G e f x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalence-level identity law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congr_int_linone
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.congrIntLinear (R := R) (1 : MulAut G) n = 1 := by
  simpa [dLKern.linearAutMap] using
    (dLKern.lin_aut_mapone (R := R) G n)

/-- Equivalence-level multiplication law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congr_int_linmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    dLKern.congrIntLinear (R := R) (e * f) n =
      dLKern.congrIntLinear (R := R) e n *
        dLKern.congrIntLinear (R := R) f n := by
  simpa [dLKern.linearAutMap] using
    (dLKern.lin_aut_mapmul (R := R) G n e f)

/-- Pointwise identity law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congr_intlin_oneapply
    (G : Type*) [Group G] (n : ℕ) (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) (1 : MulAut G) n x = x := by
  simp

/-- Pointwise multiplication law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congr_intlin_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) (e * f) n x =
      dLKern.congrIntLinear (R := R) e n
        (dLKern.congrIntLinear (R := R) f n x) := by
  exact dLKern.lin_autmap_mulapply (R := R) G n e f x

/-- Hom-level identity law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congrint_linone_linmap
    (G : Type*) [Group G] (n : ℕ) :
    (dLKern.congrIntLinear (R := R) (1 : MulAut G) n).toLinearMap =
      LinearMap.id := by
  exact
    (dLKern.linaut_mapone_linmap (R := R) G n)

/-- Hom-level multiplication law for integer-linear dimension layer congruences. -/
@[simp] theorem dLKern.congrint_linmul_linmap
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    (dLKern.congrIntLinear (R := R) e n).toLinearMap.comp
        (dLKern.congrIntLinear (R := R) f n).toLinearMap =
      (dLKern.congrIntLinear (R := R) (e * f) n).toLinearMap := by
  simpa [dLKern.linearAutMap] using
    (dLKern.linaut_mapcomp_linmap (R := R) G n e f)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left inverse at the underlying-linear-map level for dimension layer congruences
in MulAut notation. -/
@[simp] theorem dLKern.congrint_lininv_complinmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.congrIntLinear (R := R) e⁻¹ n).toLinearMap.comp
        (dLKern.congrIntLinear (R := R) e n).toLinearMap = LinearMap.id := by
  simpa [dLKern.linearAutMap] using
    (dLKern.linaut_mapinv_complinmap (R := R) G n e)

/-- Right inverse at the underlying-linear-map level for dimension layer congruences
in MulAut notation. -/
@[simp] theorem dLKern.congrint_lincomp_invlinmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.congrIntLinear (R := R) e n).toLinearMap.comp
        (dLKern.congrIntLinear (R := R) e⁻¹ n).toLinearMap = LinearMap.id := by
  simpa [dLKern.linearAutMap] using
    (dLKern.linaut_mapcomp_invlinmap (R := R) G n e)

/-- Inverse orientation for dimension layer congruences in MulAut notation. -/
@[simp] theorem dLKern.congr_int_lininv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dLKern.congrIntLinear (R := R) e⁻¹ n =
      (dLKern.congrIntLinear (R := R) e n).symm := by
  rw [dLKern.congr_int_linsymm]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left cancellation for inverse first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congrint_lininv_applyself
    {G : Type*} [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) e⁻¹
        (dTAdditi.congrIntLinear (R := R) e x) = x := by
  simpa [dTAdditi.congr_int_linsymm] using
    (dTAdditi.congrIntLinear (R := R) e).left_inv x

/-- Right cancellation for inverse first dimension quotient congruences. -/
@[simp] theorem dTAdditi.congrint_linapply_invself
    {G : Type*} [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) e
        (dTAdditi.congrIntLinear (R := R) e⁻¹ x) = x := by
  simpa [dTAdditi.congr_int_linsymm] using
    (dTAdditi.congrIntLinear (R := R) e).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left cancellation for inverse dimension layer congruences in MulAut notation. -/
@[simp] theorem dLKern.congrint_lininv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) e⁻¹ n
        (dLKern.congrIntLinear (R := R) e n x) = x := by
  simpa using dLKern.congrint_linsymm_applyself (R := R) G G e n x

/-- Right cancellation for inverse dimension layer congruences in MulAut notation. -/
@[simp] theorem dLKern.congrint_linapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) e n
        (dLKern.congrIntLinear (R := R) e⁻¹ n x) = x := by
  simpa using dLKern.congrint_linapply_symmself (R := R) G G e n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse orientation for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congr_int_lininv
    {G : Type*} [Group G] (e : MulAut G) :
    dTAdditi.congrIntLinear (R := R) e⁻¹ =
      (dTAdditi.congrIntLinear (R := R) e).symm := by
  rw [dTAdditi.congr_int_linsymm]
  rfl

/-- Underlying-map inverse orientation for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congrint_lininv_linmap
    {G : Type*} [Group G] (e : MulAut G) :
    (dTAdditi.congrIntLinear (R := R) e⁻¹).toLinearMap =
      (dTAdditi.congrIntLinear (R := R) e).symm.toLinearMap := by
  rw [dTAdditi.congr_int_lininv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Underlying-map inverse orientation for dimension layer congruences in MulAut notation. -/
@[simp] theorem dLKern.congrint_lininv_linmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.congrIntLinear (R := R) e⁻¹ n).toLinearMap =
      (dLKern.congrIntLinear (R := R) e n).symm.toLinearMap := by
  rw [dLKern.congr_int_lininv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise inverse orientation for the defining first dimension quotient congruence. -/
@[simp] theorem dTAdditi.congr_intlin_invapply
    {G : Type*} [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.congrIntLinear (R := R) e⁻¹ x =
      (dTAdditi.congrIntLinear (R := R) e).symm x := by
  rw [dTAdditi.congr_int_lininv]

/-- Pointwise inverse orientation for dimension layer congruences in MulAut notation. -/
@[simp] theorem dLKern.congr_intlin_invapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.congrIntLinear (R := R) e⁻¹ n x =
      (dLKern.congrIntLinear (R := R) e n).symm x := by
  rw [dLKern.congr_int_lininv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Underlying-map inverse orientation for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.linaut_mapinv_linmap
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.linearAutMap (R := R) G n e⁻¹).toLinearMap =
      (dLKern.linearAutMap (R := R) G n e).symm.toLinearMap := by
  rw [dLKern.lin_aut_mapinv]
  rfl

/-- Pointwise inverse orientation for integer-linear dimension layer actions. -/
@[simp] theorem dLKern.lin_autmap_invapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (dLKern R G n)) :
    dLKern.linearAutMap (R := R) G n e⁻¹ x =
      (dLKern.linearAutMap (R := R) G n e).symm x := by
  rw [dLKern.lin_aut_mapinv]
  rfl

/-- Underlying-map inverse orientation for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.linaut_mapinv_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (dTAdditi.linearAutMap (R := R) G e⁻¹).toLinearMap =
      (dTAdditi.linearAutMap (R := R) G e).symm.toLinearMap := by
  rw [dTAdditi.lin_aut_mapinv]
  rfl

/-- Pointwise inverse orientation for the first dimension additive linear action. -/
@[simp] theorem dTAdditi.lin_autmap_invapply
    (G : Type*) [Group G] (e : MulAut G) (x : dTAdditi R G) :
    dTAdditi.linearAutMap (R := R) G e⁻¹ x =
      (dTAdditi.linearAutMap (R := R) G e).symm x := by
  rw [dTAdditi.lin_aut_mapinv]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse orientation for dimension quotient automorphism actions. -/
@[simp] theorem dQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dQuot.mulAutMap R G n e⁻¹).toMonoidHom =
      (dQuot.mulAutMap R G n e).symm.toMonoidHom := by
  rw [dQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for consecutive dimension quotient actions. -/
@[simp] theorem dNQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dNQuot.mulAutMap (R := R) G n e⁻¹).toMonoidHom =
      (dNQuot.mulAutMap (R := R) G n e).symm.toMonoidHom := by
  rw [dNQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for dimension layer-kernel actions. -/
@[simp] theorem dLKern.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dLKern.mulAutMap (R := R) G n e⁻¹).toMonoidHom =
      (dLKern.mulAutMap (R := R) G n e).symm.toMonoidHom := by
  rw [dLKern.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for arbitrary dimension term-quotient actions. -/
@[simp] theorem dTQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTQuot.mulAutMap (R := R) G hmn e⁻¹).toMonoidHom =
      (dTQuot.mulAutMap (R := R) G hmn e).symm.toMonoidHom := by
  rw [dTQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for dimension transition-kernel actions. -/
@[simp] theorem dTKern.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTKern.mulAutMap (R := R) (G := G) hmn e⁻¹).toMonoidHom =
      (dTKern.mulAutMap (R := R) (G := G) hmn e).symm.toMonoidHom := by
  rw [dTKern.mul_aut_mapinv]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism actions on dimension quotients are the corresponding congruences. -/
@[simp] theorem dQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dQuot.mulAutMap R G n e = dQuot.congr (R := R) G e n := rfl

/-- Automorphism actions on consecutive dimension quotients are the corresponding congruences. -/
@[simp] theorem dNQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dNQuot.mulAutMap (R := R) G n e =
      dNQuot.congr (R := R) e n := rfl

/-- Automorphism actions on dimension layer kernels are the corresponding congruences. -/
@[simp] theorem dLKern.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dLKern.mulAutMap (R := R) G n e =
      dLKern.congr (R := R) e n := rfl

/-- Automorphism actions on dimension term quotients are the corresponding congruences. -/
@[simp] theorem dTQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTQuot.mulAutMap (R := R) G hmn e =
      dTQuot.congr (R := R) e hmn := rfl

/-- Automorphism actions on dimension transition kernels are the corresponding congruences. -/
@[simp] theorem dTKern.mul_autmap_eqcongr
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTKern.mulAutMap (R := R) (G := G) hmn e =
      dTKern.congr (R := R) e hmn := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The first dimension additive linear automorphism action is its defining congruence. -/
@[simp] theorem dTAdditi.linaut_mapeq_congrintlin
    (G : Type*) [Group G] (e : MulAut G) :
    dTAdditi.linearAutMap (R := R) G e =
      dTAdditi.congrIntLinear (R := R) e := rfl

/-- The dimension layer linear automorphism action is its defining congruence. -/
@[simp] theorem dLKern.linaut_mapeq_congrintlin
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    dLKern.linearAutMap (R := R) G n e =
      dLKern.congrIntLinear (R := R) e n := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- A group automorphism maps each dimension subgroup onto itself. -/
@[simp] theorem dimension_mul_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dSubgro R G n).map e.toMonoidHom = dSubgro R G n := by
  simpa using (dimension_equiv (R := R) (G := G) e n)

/-- A group automorphism pulls each dimension subgroup back to itself. -/
@[simp] theorem dimension_comap_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (dSubgro R G n).comap e.toMonoidHom = dSubgro R G n := by
  simpa using (dimension_comap_equiv (R := R) (G := G) e n)

/-- Pointwise invariance of dimension-subgroup membership under automorphisms. -/
theorem dimension_subgroup_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    e g ∈ dSubgro R G n ↔ g ∈ dSubgro R G n := by
  simpa using (dimension_subgroup_equiv (R := R) (G := G) e n g)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Dimension depth is invariant under automorphisms, in predicate form. -/
theorem dimension_least_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    dimensionDepthLeast R G (e g) n ↔ dimensionDepthLeast R G g n := by
  exact dimension_subgroup_aut (R := R) G n e g

/-- Symmetric automorphism-invariance form for dimension depth. -/
theorem dimension_aut_symm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    dimensionDepthLeast R G (e.symm g) n ↔ dimensionDepthLeast R G g n := by
  simpa using (dimension_least_aut (R := R) G n e.symm g)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalences of groups carry the next dimension term inside a term onto the next term. -/
theorem dimension_next_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dNTerm R G n).map
        (dSubgro.congr (R := R) e n).toMonoidHom =
      dNTerm R H n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ dSubgro R G (n + 1) :=
      (dimension_next (R := R) n x).1 hx
    change (((dSubgro.congr (R := R) e n) x : dSubgro R H n) : H) ∈
      dSubgro R H (n + 1)
    have h := (dimension_subgroup_equiv (R := R) (G := G) e (n + 1) (x : G)).2 hx'
    simpa using h
  · intro hy
    refine ⟨(dSubgro.congr (R := R) e.symm n) y, ?_, ?_⟩
    · have hy' : (y : H) ∈ dSubgro R H (n + 1) :=
        (dimension_next (R := R) n y).1 hy
      change (((dSubgro.congr (R := R) e.symm n) y : dSubgro R G n) : G) ∈
        dSubgro R G (n + 1)
      have h := (dimension_subgroup_symm (R := R) (G := G) e (n + 1) (y : H)).2 hy'
      simpa using h
    · ext
      simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalences of groups pull the next dimension term inside a term back to the next term. -/
theorem dimension_comap_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dNTerm R H n).comap
        (dSubgro.congr (R := R) e n).toMonoidHom =
      dNTerm R G n := by
  ext x
  constructor
  · intro hx
    have hx' : (((dSubgro.congr (R := R) e n) x :
          dSubgro R H n) : H) ∈ dSubgro R H (n + 1) :=
      (dimension_next (R := R) n _).1 hx
    have h := (dimension_subgroup_equiv (R := R) (G := G) e
      (n + 1) (x : G)).1 (by simpa using hx')
    exact (dimension_next (R := R) n x).2 h
  · intro hx
    have hx' : (x : G) ∈ dSubgro R G (n + 1) :=
      (dimension_next (R := R) n x).1 hx
    have h := (dimension_subgroup_equiv (R := R) (G := G) e
      (n + 1) (x : G)).2 hx'
    exact (dimension_next (R := R) n _).2 (by simpa using h)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The restriction of a group equivalence to the embedded next dimension terms. -/
noncomputable def dNTerm.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    dNTerm R G n ≃* dNTerm R H n :=
  ((dSubgro.congr (R := R) e n).subgroupMap
      (dNTerm R G n)).trans
    (MulEquiv.subgroupCongr (dimension_next_congr (R := R) e n))

/-- Coercion formula for the restricted equivalence on embedded next dimension terms. -/
@[simp] theorem dNTerm.congr_apply_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : dNTerm R G n) :
    (((dNTerm.congr (R := R) e n x :
        dNTerm R H n) : dSubgro R H n) : H) =
      e ((x : dSubgro R G n) : G) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse orientation for restricted equivalences on embedded next dimension terms. -/
@[simp] theorem dNTerm.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (dNTerm.congr (R := R) e n).symm =
      dNTerm.congr (R := R) e.symm n := by
  ext y
  change e.symm ((y : dSubgro R H n) : H) =
    e.symm ((y : dSubgro R H n) : H)
  rfl

/-- Identity law for restricted equivalences on embedded next dimension terms. -/
@[simp] theorem dNTerm.congr_refl {G : Type*} [Group G] (n : ℕ) :
    dNTerm.congr (R := R) (MulEquiv.refl G) n =
      MulEquiv.refl (dNTerm R G n) := by
  ext x
  rfl

/-- Composition law for restricted equivalences on embedded next dimension terms. -/
@[simp] theorem dNTerm.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (dNTerm.congr (R := R) e n).trans
        (dNTerm.congr (R := R) f n) =
      dNTerm.congr (R := R) (e.trans f) n := by
  ext x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left inverse cancellation for restricted dimension next-term congruences. -/
@[simp] theorem dNTerm.congr_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dNTerm R G n) :
    dNTerm.congr (R := R) e.symm n
        (dNTerm.congr (R := R) e n x) = x := by
  rw [← dNTerm.congr_symm (R := R) e n]
  exact (dNTerm.congr (R := R) e n).left_inv x

/-- Right inverse cancellation for restricted dimension next-term congruences. -/
@[simp] theorem dNTerm.congr_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (y : dNTerm R H n) :
    dNTerm.congr (R := R) e n
        (dNTerm.congr (R := R) e.symm n y) = y := by
  rw [← dNTerm.congr_symm (R := R) e n]
  exact (dNTerm.congr (R := R) e n).right_inv y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Parent-term coercion of the restricted dimension next-term congruence. -/
@[simp] theorem dNTerm.congr_apply_parent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : dNTerm R G n) :
    ((dNTerm.congr (R := R) e n x :
        dNTerm R H n) : dSubgro R H n) =
      dSubgro.congr (R := R) e n (x : dSubgro R G n) := by
  rfl

/-- Coercion formula for the inverse restricted dimension next-term congruence. -/
@[simp] theorem dNTerm.congr_symm_applycoe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (y : dNTerm R H n) :
    ((((dNTerm.congr (R := R) e n).symm y :
        dNTerm R G n) : dSubgro R G n) : G) =
      e.symm ((y : dSubgro R H n) : H) := by
  rw [dNTerm.congr_symm]
  exact dNTerm.congr_apply_coe (R := R) e.symm n y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Equivalences carry embedded arbitrary dimension terms onto embedded arbitrary terms. -/
theorem dimension_subgroup_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro (R := R) (G := G) hmn).map
        (dSubgro.congr (R := R) e m).toMonoidHom =
      dTSubgro (R := R) (G := H) hmn := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ dSubgro R G n :=
      (dimension_subgroup (R := R) hmn x).1 hx
    change (((dSubgro.congr (R := R) e m) x :
        dSubgro R H m) : H) ∈ dSubgro R H n
    have h := (dimension_subgroup_equiv (R := R) (G := G) e n (x : G)).2 hx'
    simpa using h
  · intro hy
    refine ⟨(dSubgro.congr (R := R) e.symm m) y, ?_, ?_⟩
    · have hy' : (y : H) ∈ dSubgro R H n :=
        (dimension_subgroup (R := R) hmn y).1 hy
      change (((dSubgro.congr (R := R) e.symm m) y :
          dSubgro R G m) : G) ∈ dSubgro R G n
      have h := (dimension_subgroup_symm (R := R) (G := G) e n (y : H)).2 hy'
      simpa using h
    · ext
      simp

/-- Equivalences pull embedded arbitrary dimension terms back to embedded arbitrary terms. -/
theorem dimension_term_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro (R := R) (G := H) hmn).comap
        (dSubgro.congr (R := R) e m).toMonoidHom =
      dTSubgro (R := R) (G := G) hmn := by
  ext x
  constructor
  · intro hx
    have hx' : (((dSubgro.congr (R := R) e m) x :
        dSubgro R H m) : H) ∈ dSubgro R H n :=
      (dimension_subgroup (R := R) hmn ((dSubgro.congr (R := R) e m) x)).1 hx
    have h := (dimension_subgroup_equiv (R := R) (G := G) e n (x : G)).1
      (by simpa using hx')
    exact (dimension_subgroup (R := R) hmn x).2 h
  · intro hx
    have hx' : (x : G) ∈ dSubgro R G n :=
      (dimension_subgroup (R := R) hmn x).1 hx
    have h := (dimension_subgroup_equiv (R := R) (G := G) e n (x : G)).2 hx'
    exact (dimension_subgroup (R := R) hmn
        ((dSubgro.congr (R := R) e m) x)).2 (by simpa using h)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The restriction of a group equivalence to arbitrary embedded dimension terms. -/
noncomputable def dTSubgro.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro (R := R) (G := G) hmn ≃*
      dTSubgro (R := R) (G := H) hmn :=
  ((dSubgro.congr (R := R) e m).subgroupMap
      (dTSubgro (R := R) (G := G) hmn)).trans
    (MulEquiv.subgroupCongr (dimension_subgroup_congr (R := R) e hmn))

/-- Parent-term coercion of the restricted congruence on arbitrary dimension terms. -/
@[simp] theorem dTSubgro.congr_apply_parent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    ((dTSubgro.congr (R := R) e hmn x :
        dTSubgro (R := R) (G := H) hmn) : dSubgro R H m) =
      dSubgro.congr (R := R) e m (x : dSubgro R G m) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse orientation for restricted equivalences on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e hmn).symm =
      dTSubgro.congr (R := R) e.symm hmn := by
  ext y
  change e.symm (((y : dTSubgro (R := R) (G := H) hmn) :
      dSubgro R H m) : H) =
    e.symm (((y : dTSubgro (R := R) (G := H) hmn) :
      dSubgro R H m) : H)
  rfl

/-- Identity law for restricted equivalences on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.congr_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.congr (R := R) (MulEquiv.refl G) hmn =
      MulEquiv.refl (dTSubgro (R := R) (G := G) hmn) := by
  ext x
  rfl

/-- Composition law for restricted equivalences on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K)
    {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e hmn).trans
        (dTSubgro.congr (R := R) f hmn) =
      dTSubgro.congr (R := R) (e.trans f) hmn := by
  ext x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left inverse cancellation for restricted arbitrary dimension-term congruences. -/
@[simp] theorem dTSubgro.congr_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.congr (R := R) e.symm hmn
        (dTSubgro.congr (R := R) e hmn x) = x := by
  rw [← dTSubgro.congr_symm (R := R) e hmn]
  exact (dTSubgro.congr (R := R) e hmn).left_inv x

/-- Right inverse cancellation for restricted arbitrary dimension-term congruences. -/
@[simp] theorem dTSubgro.congr_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.congr (R := R) e hmn
        (dTSubgro.congr (R := R) e.symm hmn y) = y := by
  rw [← dTSubgro.congr_symm (R := R) e hmn]
  exact (dTSubgro.congr (R := R) e hmn).right_inv y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Underlying-group coercion of the restricted congruence on arbitrary dimension terms. -/
@[simp] theorem dTSubgro.congr_apply_coe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (((dTSubgro.congr (R := R) e hmn x :
        dTSubgro (R := R) (G := H) hmn) :
        dSubgro R H m) : H) =
      e ((x : dSubgro R G m) : G) := by
  rfl

/-- Parent-term coercion of the inverse restricted congruence on arbitrary dimension terms. -/
@[simp] theorem dTSubgro.congr_symm_applyparent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    (((dTSubgro.congr (R := R) e hmn).symm y :
        dTSubgro (R := R) (G := G) hmn) : dSubgro R G m) =
      dSubgro.congr (R := R) e.symm m (y : dSubgro R H m) := by
  rw [dTSubgro.congr_symm]
  exact dTSubgro.congr_apply_parent (R := R) e.symm hmn y

/-- Underlying-group coercion of the inverse restricted congruence on arbitrary dimension terms. -/
@[simp] theorem dTSubgro.congr_symm_applycoe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    ((((dTSubgro.congr (R := R) e hmn).symm y :
        dTSubgro (R := R) (G := G) hmn) :
        dSubgro R G m) : G) =
      e.symm ((y : dSubgro R H m) : H) := by
  rw [dTSubgro.congr_symm]
  exact dTSubgro.congr_apply_coe (R := R) e.symm hmn y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphisms of `G` act on arbitrary embedded dimension terms. -/
noncomputable def dTSubgro.mulAutMap (G : Type*) [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut (dTSubgro (R := R) (G := G) hmn) where
  toFun e := dTSubgro.congr (R := R) e hmn
  map_one' := by
    ext x
    rfl
  map_mul' e f := by
    ext x
    rfl

@[simp] theorem dTSubgro.mul_aut_mapapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.mulAutMap (R := R) G hmn e x =
      dTSubgro.congr (R := R) e hmn x := rfl

@[simp] theorem dTSubgro.mul_aut_mapone {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.mulAutMap (R := R) G hmn 1 = 1 :=
  map_one (dTSubgro.mulAutMap (R := R) G hmn)

@[simp] theorem dTSubgro.mul_aut_mapmul {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    dTSubgro.mulAutMap (R := R) G hmn (e * f) =
      dTSubgro.mulAutMap (R := R) G hmn e *
        dTSubgro.mulAutMap (R := R) G hmn f :=
  map_mul (dTSubgro.mulAutMap (R := R) G hmn) e f

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem dTSubgro.mul_aut_mapinv {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTSubgro.mulAutMap (R := R) G hmn e⁻¹ =
      (dTSubgro.mulAutMap (R := R) G hmn e)⁻¹ :=
  map_inv (dTSubgro.mulAutMap (R := R) G hmn) e

@[simp] theorem dTSubgro.mul_autmap_mulapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.mulAutMap (R := R) G hmn (e * f) x =
      dTSubgro.mulAutMap (R := R) G hmn e
        (dTSubgro.mulAutMap (R := R) G hmn f x) := by
  simp [dTSubgro.mul_aut_mapmul]

@[simp] theorem dTSubgro.mulaut_mapinv_applyself {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.mulAutMap (R := R) G hmn e⁻¹
        (dTSubgro.mulAutMap (R := R) G hmn e x) = x := by
  change dTSubgro.congr (R := R) e.symm hmn
      (dTSubgro.congr (R := R) e hmn x) = x
  exact dTSubgro.congr_symm_applyself (R := R) e hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism actions on arbitrary embedded dimension terms are the corresponding congruences. -/
@[simp] theorem dTSubgro.mul_autmap_eqcongr {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    dTSubgro.mulAutMap (R := R) G hmn e =
      dTSubgro.congr (R := R) e hmn := rfl

/-- Parent-term formula for the automorphism action on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.mul_autmap_applyparent {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    ((dTSubgro.mulAutMap (R := R) G hmn e x :
        dTSubgro (R := R) (G := G) hmn) : dSubgro R G m) =
      dSubgro.congr (R := R) e m (x : dSubgro R G m) := by
  rfl

/-- Underlying-group formula for the automorphism action on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.mul_autmap_applycoe {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (((dTSubgro.mulAutMap (R := R) G hmn e x :
        dTSubgro (R := R) (G := G) hmn) :
        dSubgro R G m) : G) = e ((x : dSubgro R G m) : G) := by
  rfl

/-- Right inverse cancellation for automorphism actions on arbitrary dimension terms. -/
@[simp] theorem dTSubgro.mulaut_mapapply_invself {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.mulAutMap (R := R) G hmn e
        (dTSubgro.mulAutMap (R := R) G hmn e⁻¹ x) = x := by
  change dTSubgro.congr (R := R) e hmn
      (dTSubgro.congr (R := R) e.symm hmn x) = x
  exact dTSubgro.congr_apply_symmself (R := R) e hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse-application criterion for restricted congruences on arbitrary dimension terms. -/
theorem dTSubgro.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (dTSubgro.congr (R := R) e hmn).symm y = x ↔
      y = dTSubgro.congr (R := R) e hmn x := by
  rw [MulEquiv.symm_apply_eq]

/-- Forward-application criterion for restricted congruences on arbitrary dimension terms. -/
theorem dTSubgro.congr_apply_eqiff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.congr (R := R) e hmn x = y ↔
      x = dTSubgro.congr (R := R) e.symm hmn y := by
  rw [← dTSubgro.congr_symm (R := R) e hmn]
  exact (dTSubgro.congr (R := R) e hmn).apply_eq_iff_eq_symm_apply

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level form of the arbitrary dimension-term automorphism action. -/
@[simp] theorem dTSubgro.mul_autmap_monoidhom {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTSubgro.mulAutMap (R := R) G hmn e).toMonoidHom =
      (dTSubgro.congr (R := R) e hmn).toMonoidHom := rfl

/-- Hom-level form of the inverse arbitrary dimension-term automorphism action. -/
@[simp] theorem dTSubgro.mulaut_mapsymm_monoidhom {G : Type*}
    [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((dTSubgro.mulAutMap (R := R) G hmn e).symm).toMonoidHom =
      (dTSubgro.congr (R := R) e.symm hmn).toMonoidHom := by
  rw [← dTSubgro.congr_symm (R := R) e hmn]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Restricted arbitrary-term congruences commute with inclusion into the parent term. -/
theorem dTSubgro.subtype_comp_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro (R := R) (G := H) hmn).subtype.comp
        (dTSubgro.congr (R := R) e hmn).toMonoidHom =
      (dSubgro.congr (R := R) e m).toMonoidHom.comp
        (dTSubgro (R := R) (G := G) hmn).subtype := by
  ext x
  rfl

/-- Pointwise inclusion-square form for arbitrary dimension-term congruences. -/
@[simp] theorem dTSubgro.subtype_congr_apply {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (dTSubgro (R := R) (G := H) hmn).subtype
        (dTSubgro.congr (R := R) e hmn x) =
      dSubgro.congr (R := R) e m
        ((dTSubgro (R := R) (G := G) hmn).subtype x) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Arbitrary dimension-term actions commute with inclusion into the parent term. -/
theorem dTSubgro.subtype_compmul_autmap {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (dTSubgro (R := R) (G := G) hmn).subtype.comp
        (dTSubgro.mulAutMap (R := R) G hmn e).toMonoidHom =
      (dSubgro.congr (R := R) e m).toMonoidHom.comp
        (dTSubgro (R := R) (G := G) hmn).subtype := by
  ext x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Deeper embedded dimension terms are contained in intermediate embedded terms. -/
theorem dimension_term_subgroup {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk) ≤
      dTSubgro (R := R) (G := G) hmn := by
  intro x hx
  rw [dimension_subgroup] at hx ⊢
  exact dimensionSubgroup_antitone R G hnk hx

/-- Inclusion of a deeper embedded dimension term into an intermediate one. -/
def dTSubgro.inclusion {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk) →*
      dTSubgro (R := R) (G := G) hmn :=
  Subgroup.inclusion (dimension_term_subgroup (R := R) hmn hnk)

@[simp] theorem dTSubgro.inclusion_apply {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk)) :
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk x :
        dSubgro R G m) = x := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Nested inclusion maps for embedded dimension terms compose as expected. -/
@[simp] theorem dTSubgro.inclusion_comp {G : Type*} [Group G]
    {m n k l : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (hkl : k ≤ l) :
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk).comp
        (dTSubgro.inclusion (R := R) (G := G) (Nat.le_trans hmn hnk) hkl) =
      dTSubgro.inclusion (R := R) (G := G) hmn (Nat.le_trans hnk hkl) := by
  ext x
  rfl

/-- The reflexive inclusion of an embedded dimension term is the identity. -/
@[simp] theorem dTSubgro.inclusion_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.inclusion (R := R) (G := G) hmn (Nat.le_refl n) =
      MonoidHom.id (dTSubgro (R := R) (G := G) hmn) := by
  ext x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Restricted congruences are natural for inclusions between nested dimension terms. -/
theorem dTSubgro.inclusion_comp_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion (R := R) (G := H) hmn hnk).comp
        (dTSubgro.congr (R := R) e (Nat.le_trans hmn hnk)).toMonoidHom =
      (dTSubgro.congr (R := R) e hmn).toMonoidHom.comp
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk) := by
  ext x
  rfl

/-- Pointwise naturality for nested dimension-term inclusions and congruences. -/
@[simp] theorem dTSubgro.inclusion_congr_apply {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk)) :
    dTSubgro.inclusion (R := R) (G := H) hmn hnk
        (dTSubgro.congr (R := R) e (Nat.le_trans hmn hnk) x) =
      dTSubgro.congr (R := R) e hmn
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk x) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism actions are natural for inclusions between nested dimension terms. -/
theorem dTSubgro.inclusion_compmul_autmap {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G) :
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk).comp
        (dTSubgro.mulAutMap (R := R) G (Nat.le_trans hmn hnk) e).toMonoidHom =
      (dTSubgro.mulAutMap (R := R) G hmn e).toMonoidHom.comp
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk) := by
  ext x
  rfl

/-- Pointwise naturality of automorphism actions for nested dimension-term inclusions. -/
@[simp] theorem dTSubgro.inclusion_mulaut_mapapply {G : Type*}
    [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G)
    (x : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk)) :
    dTSubgro.inclusion (R := R) (G := G) hmn hnk
        (dTSubgro.mulAutMap (R := R) G (Nat.le_trans hmn hnk) e x) =
      dTSubgro.mulAutMap (R := R) G hmn e
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk x) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Canonical inclusions between nested dimension terms are injective. -/
theorem dTSubgro.inclusion_injective {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective (dTSubgro.inclusion (R := R) (G := G) hmn hnk) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : dTSubgro (R := R) (G := G) hmn =>
      (z : dSubgro R G m)) hxy

/-- Equality can be checked after the canonical inclusion between nested dimension terms. -/
@[simp] theorem dTSubgro.inclusion_apply_eqiff {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk)) :
    dTSubgro.inclusion (R := R) (G := G) hmn hnk x =
        dTSubgro.inclusion (R := R) (G := G) hmn hnk y ↔ x = y := by
  constructor
  · intro h
    exact dTSubgro.inclusion_injective (R := R) (G := G) hmn hnk h
  · intro h
    simp [h]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Range criterion for the canonical inclusion between nested dimension terms. -/
theorem dTSubgro.mem_range_inclusioniff {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : dTSubgro (R := R) (G := G) hmn) :
    y ∈ (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range ↔
      ((y : dSubgro R G m) : G) ∈ dSubgro R G k := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (dimension_subgroup (R := R) (Nat.le_trans hmn hnk)
      (x : dSubgro R G m)).1 x.property
  · intro hy
    let x : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk) :=
      ⟨(y : dSubgro R G m),
        (dimension_subgroup (R := R) (Nat.le_trans hmn hnk)
          (y : dSubgro R G m)).2 hy⟩
    refine ⟨x, ?_⟩
    ext
    rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Restricted congruences carry the range of a nested dimension-term inclusion to the
corresponding range after transport. -/
theorem dTSubgro.map_range_inclusioncongr {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    ((dTSubgro.inclusion (R := R) (G := G) hmn hnk).range).map
        (dTSubgro.congr (R := R) e hmn).toMonoidHom =
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz⟩
    refine ⟨dTSubgro.congr (R := R) e (Nat.le_trans hmn hnk) z, ?_⟩
    rw [← hz]
    exact (dTSubgro.inclusion_congr_apply (R := R) e hmn hnk z).symm
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨dTSubgro.inclusion (R := R) (G := G) hmn hnk
        (dTSubgro.congr (R := R) e.symm (Nat.le_trans hmn hnk) z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · rw [dTSubgro.inclusion_congr_apply (R := R) e.symm hmn hnk]
      rw [← hz]
      simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Automorphism actions preserve the range of a nested dimension-term inclusion. -/
theorem dTSubgro.maprange_inclusionmul_autmap {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G) :
    ((dTSubgro.inclusion (R := R) (G := G) hmn hnk).range).map
        (dTSubgro.mulAutMap (R := R) G hmn e).toMonoidHom =
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range := by
  simpa using
    (dTSubgro.map_range_inclusioncongr (R := R) (G := G) (H := G)
      (e := e) hmn hnk)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The range of a nested dimension-term inclusion is normal in the intermediate term. -/
theorem dTSubgro.inclusion_range_normal {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range.Normal := by
  constructor
  intro x hx y
  rw [dTSubgro.mem_range_inclusioniff (R := R) hmn hnk] at hx ⊢
  change ((y : dSubgro R G m) : G) * ((x : dSubgro R G m) : G) *
      ((y : dSubgro R G m) : G)⁻¹ ∈ dSubgro R G k
  exact (dimensionSubgroup_normal (R := R) (G := G) k).conj_mem
    ((x : dSubgro R G m) : G) hx ((y : dSubgro R G m) : G)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- The range of a nested dimension-term inclusion is available as a normal subgroup instance. -/
instance dTSubgro.inclusion_range_normalinst {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range.Normal :=
  dTSubgro.inclusion_range_normal (R := R) (G := G) hmn hnk

/-- A homomorphism induces a map on quotients by ranges of nested dimension-term inclusions. -/
noncomputable def dTSubgro.inclusion_range_quotmap {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro (R := R) (G := G) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) →*
      (dTSubgro (R := R) (G := H) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :=
  DFilt.tSOf.inclusion_range_quotmap
    (dimensionFiltration_preserves R φ) hmn hnk

@[simp] theorem dTSubgro.inclusion_rangequot_mapmk {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.inclusion_range_quotmap φ hmn hnk
        (QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range
        (DFilt.tSOf.map (dimensionFiltration_preserves R φ) hmn x) := rfl

/-- A group isomorphism induces an equivalence on quotients by ranges of nested
 dimension-term inclusions. -/
noncomputable def dTSubgro.inclusion_range_quotcongr {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro (R := R) (G := G) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) ≃*
      (dTSubgro (R := R) (G := H) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :=
  DFilt.tSOf.inclusionrange_quotequiv_mulequiv e
    (dimensionFiltration_preserves R e.toMonoidHom)
    (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn hnk

@[simp] theorem dTSubgro.inclusion_rangequot_congrmk {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.inclusion_range_quotcongr e hmn hnk
        (QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range
        (DFilt.tSOf.map
          (dimensionFiltration_preserves R e.toMonoidHom) hmn x) := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem dTSubgro.inclus_quotc_symmm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (y : dTSubgro (R := R) (G := H) hmn) :
    (dTSubgro.inclusion_range_quotcongr e hmn hnk).symm
        (QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range y) =
      QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range
        (DFilt.tSOf.map
          (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn y) := rfl

@[simp] theorem dTSubgro.inclus_quotc_monoi
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).toMonoidHom =
      dTSubgro.inclusion_range_quotmap e.toMonoidHom hmn hnk := rfl

@[simp] theorem dTSubgro.inclus_quotc_symmb
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm.toMonoidHom =
      dTSubgro.inclusion_range_quotmap e.symm.toMonoidHom hmn hnk := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem dTSubgro.inclusion_rangequot_mapid {G : Type*}
    [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro.inclusion_range_quotmap (R := R) (MonoidHom.id G) hmn hnk =
      MonoidHom.id
        (dTSubgro (R := R) (G := G) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dTSubgro.inclusion_rangequot_mapcomp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro.inclusion_range_quotmap (R := R) (ψ.comp φ) hmn hnk =
      (dTSubgro.inclusion_range_quotmap (R := R) ψ hmn hnk).comp
        (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem dTSubgro.inclusion_rangequot_congrrefl
    {G : Type*} [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro.inclusion_range_quotcongr (R := R) (MulEquiv.refl G) hmn hnk =
      MulEquiv.refl
        (dTSubgro (R := R) (G := G) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dTSubgro.inclusion_rangequot_congrsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm =
      dTSubgro.inclusion_range_quotcongr (R := R) e.symm hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro y
  rfl

@[simp] theorem dTSubgro.inclusion_rangequot_congrtrans
    {G H K : Type*} [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).trans
        (dTSubgro.inclusion_range_quotcongr (R := R) f hmn hnk) =
      dTSubgro.inclusion_range_quotcongr (R := R) (e.trans f) hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem dTSubgro.inclus_quotc_symma
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : dTSubgro (R := R) (G := G) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm
        (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk q) = q :=
  (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).left_inv q

@[simp] theorem dTSubgro.inclus_quotc_apply
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : dTSubgro (R := R) (G := H) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :
    dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk
        ((dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm q) = q :=
  (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).right_inv q

@[simp] theorem dTSubgro.inclus_quotm_symmc
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotmap (R := R) e.symm.toMonoidHom hmn hnk).comp
        (dTSubgro.inclusion_range_quotmap (R := R) e.toMonoidHom hmn hnk) =
      MonoidHom.id
        (dTSubgro (R := R) (G := G) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_symmc
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn hnk

@[simp] theorem dTSubgro.inclus_quotm_comps
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotmap (R := R) e.toMonoidHom hmn hnk).comp
        (dTSubgro.inclusion_range_quotmap (R := R) e.symm.toMonoidHom hmn hnk) =
      MonoidHom.id
        (dTSubgro (R := R) (G := H) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_comps
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse composition for arbitrary embedded dimension-term congruences. -/
@[simp] theorem dTSubgro.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e.symm hmn).toMonoidHom.comp
        (dTSubgro.congr (R := R) e hmn).toMonoidHom =
      MonoidHom.id (dTSubgro (R := R) (G := G) hmn) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e hmn).toMonoidHom.comp
        (dTSubgro.congr (R := R) e.symm hmn).toMonoidHom =
      MonoidHom.id (dTSubgro (R := R) (G := H) hmn) := by
  ext y
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse composition for dimension nested-range quotient congruences. -/
@[simp] theorem dTSubgro.inclus_quotc_homsy
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm.toMonoidHom.comp
        (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).toMonoidHom =
      MonoidHom.id
        (dTSubgro (R := R) (G := G) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) := by
  simpa using dTSubgro.inclus_quotm_symmc (R := R) e hmn hnk

/-- Hom-level inverse composition in the other order for dimension nested-range congruences. -/
@[simp] theorem dTSubgro.inclus_quotc_homco
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).toMonoidHom.comp
        (dTSubgro.inclusion_range_quotcongr (R := R) e hmn hnk).symm.toMonoidHom =
      MonoidHom.id
        (dTSubgro (R := R) (G := H) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) := by
  simpa using dTSubgro.inclus_quotm_comps (R := R) e hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse composition for embedded next dimension-term congruences. -/
@[simp] theorem dNTerm.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dNTerm.congr (R := R) e.symm n).toMonoidHom.comp
        (dNTerm.congr (R := R) e n).toMonoidHom =
      MonoidHom.id (dNTerm R G n) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for embedded next dimension terms. -/
@[simp] theorem dNTerm.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dNTerm.congr (R := R) e n).toMonoidHom.comp
        (dNTerm.congr (R := R) e.symm n).toMonoidHom =
      MonoidHom.id (dNTerm R H n) := by
  ext y
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse composition for dimension subgroup congruences. -/
@[simp] theorem dSubgro.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dSubgro.congr (R := R) e.symm n).toMonoidHom.comp
        (dSubgro.congr (R := R) e n).toMonoidHom =
      MonoidHom.id (dSubgro R G n) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for dimension subgroup congruences. -/
@[simp] theorem dSubgro.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dSubgro.congr (R := R) e n).toMonoidHom.comp
        (dSubgro.congr (R := R) e.symm n).toMonoidHom =
      MonoidHom.id (dSubgro R H n) := by
  ext y
  simp

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Hom-level inverse orientation for dimension subgroup congruences. -/
@[simp] theorem dSubgro.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dSubgro.congr (R := R) e n).symm.toMonoidHom =
      (dSubgro.congr (R := R) e.symm n).toMonoidHom := by
  rw [dSubgro.congr_symm]

/-- Hom-level inverse orientation for embedded next dimension-term congruences. -/
@[simp] theorem dNTerm.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (dNTerm.congr (R := R) e n).symm.toMonoidHom =
      (dNTerm.congr (R := R) e.symm n).toMonoidHom := by
  rw [dNTerm.congr_symm]

/-- Hom-level inverse orientation for arbitrary embedded dimension-term congruences. -/
@[simp] theorem dTSubgro.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e hmn).symm.toMonoidHom =
      (dTSubgro.congr (R := R) e.symm hmn).toMonoidHom := by
  rw [dTSubgro.congr_symm]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise cancellation for inverse maps on arbitrary dimension-term quotients. -/
@[simp] theorem dimension_term_self
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) e.symm.toMonoidHom hmn
        (dimensionTerm (R := R) e.toMonoidHom hmn q) = q := by
  simpa [dimensionTerm] using
    DFilt.quotient_symm_self
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn q

/-- Pointwise cancellation in the other order for arbitrary dimension-term quotient maps. -/
@[simp] theorem dimension_symm_self
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) e.toMonoidHom hmn
        (dimensionTerm (R := R) e.symm.toMonoidHom hmn q) = q := by
  simpa [dimensionTerm] using
    DFilt.term_quotient_self
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn q

/-- Pointwise cancellation for inverse maps on dimension nested-range quotients. -/
@[simp] theorem dTSubgro.inclus_quotm_symma
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : dTSubgro (R := R) (G := G) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap (R := R) e.symm.toMonoidHom hmn hnk
        (dTSubgro.inclusion_range_quotmap (R := R) e.toMonoidHom
          hmn hnk q) = q := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_symma
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn hnk q

/-- Pointwise cancellation in the other order for dimension nested-range quotient maps. -/
@[simp] theorem dTSubgro.inclus_quotm_apply
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : dTSubgro (R := R) (G := H) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap (R := R) e.toMonoidHom hmn hnk
        (dTSubgro.inclusion_range_quotmap (R := R) e.symm.toMonoidHom
          hmn hnk q) = q := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_apply
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn hnk q

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- A homomorphism restricts to arbitrary embedded dimension terms. -/
noncomputable def dTSubgro.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro (R := R) (G := G) hmn →*
      dTSubgro (R := R) (G := H) hmn :=
  DFilt.tSOf.map (dimensionFiltration_preserves R φ) hmn

/-- Coercion formula for maps on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.map_coe {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (((dTSubgro.map (R := R) φ hmn x :
        dTSubgro (R := R) (G := H) hmn) : dSubgro R H m) : H) =
      φ (((x : dTSubgro (R := R) (G := G) hmn) :
        dSubgro R G m) : G) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Identity law for maps on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.map_id {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.map (R := R) (MonoidHom.id G) hmn =
      MonoidHom.id (dTSubgro (R := R) (G := G) hmn) := by
  ext x
  rfl

/-- Composition law for maps on arbitrary embedded dimension terms. -/
@[simp] theorem dTSubgro.map_comp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.map (R := R) (ψ.comp φ) hmn =
      (dTSubgro.map (R := R) ψ hmn).comp
        (dTSubgro.map (R := R) φ hmn) := by
  ext x
  rfl

/-- The restricted congruence has the same underlying hom as the restricted map. -/
@[simp] theorem dTSubgro.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.congr (R := R) e hmn).toMonoidHom =
      dTSubgro.map (R := R) e.toMonoidHom hmn := by
  ext x
  simp [dTSubgro.map_coe, dTSubgro.congr_apply_parent]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Pointwise cancellation for inverse restricted maps on embedded dimension terms. -/
@[simp] theorem dTSubgro.map_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.map (R := R) e.symm.toMonoidHom hmn
        (dTSubgro.map (R := R) e.toMonoidHom hmn x) = x := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_symm_applyself
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn x

/-- Pointwise cancellation in the other order for restricted maps on embedded dimension terms. -/
@[simp] theorem dTSubgro.map_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.map (R := R) e.toMonoidHom hmn
        (dTSubgro.map (R := R) e.symm.toMonoidHom hmn y) = y := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_apply_symmself
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) e
      (dimensionFiltration_preserves R e.toMonoidHom)
      (dimensionFiltration_preserves R e.symm.toMonoidHom) hmn y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Restricted maps commute with nested inclusions of embedded dimension terms. -/
theorem dTSubgro.inclusion_comp_map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion (R := R) (G := H) hmn hnk).comp
        (dTSubgro.map (R := R) φ (Nat.le_trans hmn hnk)) =
      (dTSubgro.map (R := R) φ hmn).comp
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk) := by
  simpa [dTSubgro.map, dTSubgro.inclusion] using
    DFilt.tSOf.inclusion_comp_map
      (F := dimensionFiltration R G) (E := dimensionFiltration R H)
      (dimensionFiltration_preserves R φ) hmn hnk

/-- Pointwise naturality of restricted maps with nested dimension-term inclusions. -/
@[simp] theorem dTSubgro.inclusion_map_apply {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) (Nat.le_trans hmn hnk)) :
    dTSubgro.inclusion (R := R) (G := H) hmn hnk
        (dTSubgro.map (R := R) φ (Nat.le_trans hmn hnk) x) =
      dTSubgro.map (R := R) φ hmn
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk x) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- A restricted dimension-term map sends nested-inclusion ranges into target ranges. -/
theorem dTSubgro.map_range_inclusionle {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((dTSubgro.inclusion (R := R) (G := G) hmn hnk).range).map
        (dTSubgro.map (R := R) φ hmn) ≤
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨z, hz⟩
  refine ⟨dTSubgro.map (R := R) φ (Nat.le_trans hmn hnk) z, ?_⟩
  rw [← hz]
  exact (dTSubgro.inclusion_map_apply (R := R) φ hmn hnk z).symm

/-- An equivalence carries nested-inclusion ranges of dimension terms onto target ranges. -/
theorem dTSubgro.map_rangeinclusion_eqequiv {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((dTSubgro.inclusion (R := R) (G := G) hmn hnk).range).map
        (dTSubgro.map (R := R) e.toMonoidHom hmn) =
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range := by
  apply le_antisymm
  · exact dTSubgro.map_range_inclusionle (R := R) e.toMonoidHom hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    refine ⟨dTSubgro.inclusion (R := R) (G := G) hmn hnk
        (dTSubgro.map (R := R) e.symm.toMonoidHom (Nat.le_trans hmn hnk) z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · rw [dTSubgro.inclusion_map_apply (R := R) e.symm.toMonoidHom hmn hnk z]
      exact dTSubgro.map_apply_symmself (R := R) e hmn
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk z)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Restricted maps on embedded dimension terms are injective for injective ambient maps. -/
theorem dTSubgro.map_injective {G H : Type*} [Group G] [Group H]
    {φ : G →* H} (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (dTSubgro.map (R := R) φ hmn) := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_injective
      (F := dimensionFiltration R G) (E := dimensionFiltration R H)
      (dimensionFiltration_preserves R φ) hinj hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Kernel form of injectivity for restricted dimension-term maps. -/
@[simp] theorem dTSubgro.map_kereq_botinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H} (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.map (R := R) φ hmn).ker = ⊥ := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_kereq_botinj
      (F := dimensionFiltration R G) (E := dimensionFiltration R H)
      (dimensionFiltration_preserves R φ) hinj hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Surjectivity of restricted maps on embedded dimension terms under termwise-onto hypotheses. -/
theorem dTSubgro.map_surj_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (dTSubgro.map (R := R) φ hmn) := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_surjective honto hmn

/-- Range form of surjectivity for restricted maps on embedded dimension terms. -/
@[simp] theorem dTSubgro.maprange_eqtop_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.map (R := R) φ hmn).range = ⊤ := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.maprange_eqtop_mapsonto honto hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Bijectivity of restricted dimension-term maps under termwise-onto and injective hypotheses. -/
theorem dTSubgro.map_bijmaps_ontoinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (dTSubgro.map (R := R) φ hmn) := by
  simpa [dTSubgro.map] using
    DFilt.tSOf.map_bijmaps_ontoinj honto hinj hmn

/-- Equivalence on embedded dimension terms induced by a termwise-onto injective map. -/
noncomputable def dTSubgro.equiv_maps_ontoinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro (R := R) (G := G) hmn ≃*
      dTSubgro (R := R) (G := H) hmn :=
  DFilt.tSOf.equiv_maps_ontoinj honto hinj hmn

@[simp] theorem dTSubgro.equivmaps_ontoinj_monoidhom {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).toMonoidHom =
      dTSubgro.map (R := R) φ hmn := by
  rfl

@[simp] theorem dTSubgro.equiv_mapsonto_injapply {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn x =
      dTSubgro.map (R := R) φ hmn x := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Left inverse cancellation for onto-injective embedded dimension-term equivalences. -/
@[simp] theorem dTSubgro.equivm_ontoi_symma {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).symm
        (dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn x) = x := by
  exact DFilt.tSOf.equivm_ontoi_symma
    honto hinj hmn x

/-- Right inverse cancellation for onto-injective embedded dimension-term equivalences. -/
@[simp] theorem dTSubgro.equivm_ontoi_apply {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn
        ((dTSubgro.equiv_maps_ontoinj (R := R)
          honto hinj hmn).symm y) = y := by
  exact DFilt.tSOf.equivm_ontoi_apply
    honto hinj hmn y

/-- The inverse dimension embedded-term equivalence chooses an ambient preimage. -/
theorem dTSubgro.equivmaps_ontoinj_symmapplycoe {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    φ ((((dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).symm y :
        dTSubgro (R := R) (G := G) hmn) : dSubgro R G m) : G) =
      ((y : dSubgro R H m) : H) := by
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplycoe
    honto hinj hmn y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Surjectivity on nested-inclusion-range quotients of dimension terms under termwise onto maps. -/
theorem dTSubgro.inclus_quotm_surjm {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Surjective (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk) := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_surjm
      honto hmn hnk

/-- Range-top form for nested-inclusion-range quotient maps of dimension terms. -/
@[simp] theorem
    dTSubgro.inclrangquot_maprangeeq_topmapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk).range =
      ⊤ := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclrangquot_maprangeeq_topmapsonto
      honto hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Symmetric inverse-characterization for onto-injective embedded dimension-term equivalences. -/
theorem dTSubgro.equivmaps_ontoinj_symmapplyeq {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).symm y = x ↔
      y = dTSubgro.map (R := R) φ hmn x := by
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplyeq
    honto hinj hmn y x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Termwise-onto maps carry nested-inclusion ranges of dimension terms onto target ranges. -/
theorem dTSubgro.maprange_inclusioneq_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((dTSubgro.inclusion (R := R) (G := G) hmn hnk).range).map
        (dTSubgro.map (R := R) φ hmn) =
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range := by
  apply le_antisymm
  · exact dTSubgro.map_range_inclusionle (R := R) φ hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    rcases dTSubgro.map_surj_mapsonto (R := R) honto
        (Nat.le_trans hmn hnk) z with ⟨w, hw⟩
    refine ⟨dTSubgro.inclusion (R := R) (G := G) hmn hnk w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · rw [← dTSubgro.inclusion_map_apply (R := R) φ hmn hnk w]
      exact congrArg (dTSubgro.inclusion (R := R) (G := H) hmn hnk) hw

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Onto-injective maps induce equivalences on quotients by nested dimension-term ranges. -/
noncomputable def dTSubgro.inclus_quote_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro (R := R) (G := G) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) ≃*
      (dTSubgro (R := R) (G := H) hmn ⧸
        (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) := by
  -- Use quotient congruence with the specialized range equality to avoid definitional mismatch.
  let e := dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn
  refine QuotientGroup.congr
    (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range
    (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range e ?_
  dsimp [e]
  simpa [dTSubgro.equivmaps_ontoinj_monoidhom] using
    dTSubgro.maprange_inclusioneq_mapsonto (R := R) honto hmn hnk

@[simp] theorem dTSubgro.inclus_quote_ontoi
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk
        (QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range
        (dTSubgro.map (R := R) φ hmn x) := by
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem dTSubgro.inclra_equiv_injmo
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).toMonoidHom =
      dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Bijectivity form for nested-range quotient maps of dimension terms. -/
theorem dTSubgro.inclus_quotm_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Bijective
      (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk) := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_mapso
      honto hinj hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse representative formula for nested-range quotient equivalences of dimension terms. -/
@[simp] theorem dTSubgro.inclra_equiv_injsa
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : dTSubgro (R := R) (G := H) hmn) :
    (dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).symm
      (QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range y) =
    QuotientGroup.mk' (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range
      ((dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).symm y) := by
  simpa [dTSubgro.inclus_quote_mapso,
    dTSubgro.equiv_maps_ontoinj,
    dTSubgro.inclusion] using
    DFilt.tSOf.inclra_equiv_injsa
      (F := dimensionFiltration R G) (E := dimensionFiltration R H) honto hinj hmn hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Injectivity form for nested-range quotient maps of dimension terms. -/
theorem dTSubgro.inclus_quotm_mapsa
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective
      (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk) := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_mapsa
      honto hinj hmn hnk

/-- Kernel form for nested-range quotient maps of dimension terms. -/
@[simp] theorem dTSubgro.inclus_quotm_kereq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk).ker = ⊥ := by
  exact (MonoidHom.ker_eq_bot_iff _).2
    (dTSubgro.inclus_quotm_mapsa
      (R := R) honto hinj hmn hnk)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Equality reflection for nested-range quotient maps of dimension terms. -/
theorem dTSubgro.inclus_quotm_eqapp
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : dTSubgro (R := R) (G := G) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk x =
        dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk y ↔ x = y := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    tSOf.inclra_mapap_iffma
      honto hinj hmn hnk x y

/-- One-reflection form for nested-range quotient maps of dimension terms. -/
@[simp] theorem dTSubgro.inclus_quotm_eqone
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk x = 1 ↔ x = 1 := by
  simpa [dTSubgro.inclusion_range_quotmap] using
    tSOf.inclrangquot_mapapplyeqone_iffmapsontoinj
      honto hinj hmn hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Inverse-after-map cancellation for onto-injective dimension embedded-term equivalences. -/
@[simp] theorem dTSubgro.equivsymm_applymap_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    (dTSubgro.equiv_maps_ontoinj (R := R) honto hinj hmn).symm
        (dTSubgro.map (R := R) φ hmn x) = x := by
  change (DFilt.tSOf.equiv_maps_ontoinj
      honto hinj hmn).symm
      (DFilt.tSOf.map
        (DFilt.MapsOnto.preserves honto) hmn x) = x
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplymap
    honto hinj hmn x

/-- Map-after-inverse cancellation for onto-injective dimension embedded-term equivalences. -/
@[simp] theorem dTSubgro.mapapply_equivsymm_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.map (R := R) φ hmn
        ((dTSubgro.equiv_maps_ontoinj
          (R := R) honto hinj hmn).symm y) = y := by
  change DFilt.tSOf.map
      (DFilt.MapsOnto.preserves honto) hmn
      ((DFilt.tSOf.equiv_maps_ontoinj
        honto hinj hmn).symm y) = y
  exact DFilt.tSOf.mapapply_equivmaps_ontoinjsymm
    honto hinj hmn y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Inverse-after-map cancellation for onto-injective dimension nested-range quotients. -/
@[simp] theorem dTSubgro.rangequot_equivsymm_applymap
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    (dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).symm
      (dTSubgro.inclusion_range_quotmap
        (R := R) φ hmn hnk x) = x := by
  change (DFilt.tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm
    (DFilt.tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk x) = x
  exact tSOf.inclra_equiv_injsy
      honto hinj hmn hnk x

/-- Map-after-inverse cancellation for onto-injective dimension nested-range quotients. -/
@[simp] theorem dTSubgro.rangequot_mapapply_equivsymm
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : dTSubgro (R := R) (G := H) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap
        (R := R) φ hmn hnk
      ((dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).symm y) = y := by
  change DFilt.tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk
      ((DFilt.tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm y) = y
  exact tSOf.inclra_mapap_mapso
      honto hinj hmn hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Inverse-characterization for onto-injective dimension nested-range quotient equivalences. -/
theorem dTSubgro.rangequot_equivsymm_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : dTSubgro (R := R) (G := H) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range)
    (x : dTSubgro (R := R) (G := G) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) :
    (dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).symm y = x ↔
      y = dTSubgro.inclusion_range_quotmap
        (R := R) φ hmn hnk x := by
  change (tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm y = x ↔
    y = tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk x
  exact tSOf.inclrangquot_equivmapsonto_injsymmapplyeq
    honto hinj hmn hnk y x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for onto-injective dimension embedded-term equivalences. -/
theorem dTSubgro.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ)
    (hψ : DFilt.MapsOnto (dimensionFiltration R H)
      (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.equiv_maps_ontoinj (R := R)
        (DFilt.MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (dTSubgro.equiv_maps_ontoinj (R := R)
        hφ hinjφ hmn).trans
        (dTSubgro.equiv_maps_ontoinj (R := R)
          hψ hinjψ hmn) := by
  change tSOf.equiv_maps_ontoinj
      (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (tSOf.equiv_maps_ontoinj hφ hinjφ hmn).trans
      (tSOf.equiv_maps_ontoinj hψ hinjψ hmn)
  exact tSOf.equiv_mapsonto_injcomp hφ hψ hinjφ hinjψ hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for onto-injective dimension nested-range quotient equivalences. -/
theorem dTSubgro.range_quot_equivcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ)
    (hψ : DFilt.MapsOnto (dimensionFiltration R H)
      (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro.inclus_quote_mapso
        (R := R) (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn hnk =
      (dTSubgro.inclus_quote_mapso
        (R := R) hφ hinjφ hmn hnk).trans
        (dTSubgro.inclus_quote_mapso
          (R := R) hψ hinjψ hmn hnk) := by
  change tSOf.inclus_quote_mapso
      (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn hnk =
    (tSOf.inclus_quote_mapso
      hφ hinjφ hmn hnk).trans
      (tSOf.inclus_quote_mapso
        hψ hinjψ hmn hnk)
  exact tSOf.inclusionrange_quotequivmaps_ontoinjcomp
    hφ hψ hinjφ hinjψ hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Identity law for onto-injective dimension embedded-term equivalences. -/
@[simp] theorem dTSubgro.equiv_mapsonto_injid
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dTSubgro.equiv_maps_ontoinj (R := R)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
      MulEquiv.refl (dTSubgro (R := R) (G := G) hmn) := by
  change tSOf.equiv_maps_ontoinj
      (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
    MulEquiv.refl (tSOf (dimensionFiltration R G) hmn)
  exact tSOf.equiv_mapsonto_injid (dimensionFiltration R G) hmn

/-- Identity law for onto-injective dimension nested-range quotient equivalences. -/
@[simp] theorem dTSubgro.range_quot_equivid
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dTSubgro.inclus_quote_mapso (R := R)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn hnk =
      MulEquiv.refl
        (dTSubgro (R := R) (G := G) hmn ⧸
          (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range) := by
  change tSOf.inclus_quote_mapso
      (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn hnk =
    MulEquiv.refl (tSOf (dimensionFiltration R G) hmn ⧸
      (tSOf.inclusion (F := dimensionFiltration R G) hmn hnk).range)
  exact tSOf.inclusionrange_quotequivmaps_ontoinjid
    (dimensionFiltration R G) hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for onto-injective dimension embedded-term equivalences. -/
theorem dTSubgro.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn)
    (y : dTSubgro (R := R) (G := H) hmn) :
    dTSubgro.map (R := R) φ hmn x = y ↔
      x = (dTSubgro.equiv_maps_ontoinj
        (R := R) honto hinj hmn).symm y := by
  change tSOf.map (MapsOnto.preserves honto) hmn x = y ↔
    x = (tSOf.equiv_maps_ontoinj honto hinj hmn).symm y
  exact tSOf.equivmaps_ontoinj_applyeq honto hinj hmn x y

/-- Forward-image characterization for dimension nested-range quotient equivalences. -/
theorem dTSubgro.range_quotequiv_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : dTSubgro (R := R) (G := G) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := G) hmn hnk).range)
    (y : dTSubgro (R := R) (G := H) hmn ⧸
      (dTSubgro.inclusion (R := R) (G := H) hmn hnk).range) :
    dTSubgro.inclusion_range_quotmap (R := R) φ hmn hnk x = y ↔
      x = (dTSubgro.inclus_quote_mapso
        (R := R) honto hinj hmn hnk).symm y := by
  change tSOf.inclusion_range_quotmap
      (MapsOnto.preserves honto) hmn hnk x = y ↔
    x = (tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm y
  exact tSOf.inclrangquot_equivmapsonto_injapplyeq
    honto hinj hmn hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Injectivity of dimension embedded-term maps under termwise-onto injective maps. -/
theorem dTSubgro.map_injmaps_ontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (dTSubgro.map (R := R) φ hmn) := by
  change Function.Injective (tSOf.map (MapsOnto.preserves honto) hmn)
  exact tSOf.map_injmaps_ontoinj honto hinj hmn

/-- Equality reflection for dimension embedded-term maps under termwise-onto injective maps. -/
theorem dTSubgro.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x y : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.map (R := R) φ hmn x =
        dTSubgro.map (R := R) φ hmn y ↔ x = y := by
  change tSOf.map (MapsOnto.preserves honto) hmn x =
      tSOf.map (MapsOnto.preserves honto) hmn y ↔ x = y
  exact tSOf.mapapp_eqapp_mapso
    honto hinj hmn x y

/-- One-reflection form for dimension embedded-term maps under termwise-onto injective maps. -/
@[simp] theorem dTSubgro.mapapply_eqoneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dTSubgro (R := R) (G := G) hmn) :
    dTSubgro.map (R := R) φ hmn x = 1 ↔ x = 1 := by
  change tSOf.map (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact tSOf.mapapply_eqoneiff_mapsontoinj
    honto hinj hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Forward-image characterization for onto-injective dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : dQuot R G n) (y : dQuot R H n) :
    dQuot.map (R := R) φ n x = y ↔
      x = (dQuot.equiv_maps_ontoinj
        (R := R) φ honto hinj n).symm y := by
  change DFilt.quotientMap (DFilt.MapsOnto.preserves honto) n x = y ↔
    x = (DFilt.quotientOntoInjective honto hinj n).symm y
  exact DFilt.onto_injective
    honto hinj n x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Identity law for onto-injective dimension quotient equivalences. -/
@[simp] theorem dQuot.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    dQuot.equiv_maps_ontoinj (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) n =
      MulEquiv.refl (dQuot R G n) := by
  change quotientOntoInjective
      (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) n =
    MulEquiv.refl (G ⧸ (dimensionFiltration R G) n)
  exact quotient_injective_id (dimensionFiltration R G) n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for onto-injective dimension quotient equivalences. -/
theorem dQuot.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    dQuot.equiv_maps_ontoinj (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (dQuot.equiv_maps_ontoinj (R := R) φ hφ hinjφ n).trans
        (dQuot.equiv_maps_ontoinj (R := R) ψ hψ hinjψ n) := by
  change quotientOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (quotientOntoInjective hφ hinjφ n).trans
      (quotientOntoInjective hψ hinjψ n)
  exact quotient_injective_comp hφ hψ hinjφ hinjψ n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for dimension term-quotient equivalences. -/
theorem dimension_quotient_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) φ hmn x = y ↔
      x = (dimensionMapsInjective
        (R := R) φ honto hinj hmn).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsInjective honto hinj hmn).symm y
  exact term_injective honto hinj hmn x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Identity law for dimension term-quotient equivalences. -/
@[simp] theorem dimension_term_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dimensionMapsInjective (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
      MulEquiv.refl
        (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) := by
  change termMapsInjective
      (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
    MulEquiv.refl ((dimensionFiltration R G) m ⧸
      tSOf (dimensionFiltration R G) hmn)
  exact term_injective_id (dimensionFiltration R G) hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for dimension term-quotient equivalences. -/
theorem term_injective_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionMapsInjective (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (dimensionMapsInjective (R := R) φ hφ hinjφ hmn).trans
        (dimensionMapsInjective (R := R) ψ hψ hinjψ hmn) := by
  change termMapsInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (termMapsInjective hφ hinjφ hmn).trans
      (termMapsInjective hψ hinjψ hmn)
  exact term_equiv_comp hφ hψ hinjφ hinjψ hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for dimension transition-kernel equivalences. -/
theorem dimension_equiv_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn))
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn x = y ↔
      x = (dimensionOntoInjective
        (R := R) φ honto hinj hmn).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionOntoInjective honto hinj hmn).symm y
  exact transition_injective honto hinj hmn x y

/-- Inverse-after-map cancellation for onto-injective dimension transition kernels. -/
@[simp] theorem kernel_injective_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionOntoInjective
        (R := R) φ honto hinj hmn).symm
      (dimensionTransition (R := R) φ hmn x) = x := by
  change (transitionOntoInjective honto hinj hmn).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact equiv_injective_symm honto hinj hmn x

/-- Map-after-inverse cancellation for onto-injective dimension transition kernels. -/
@[simp] theorem transition_maps_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn
        ((dimensionOntoInjective
          (R := R) φ honto hinj hmn).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionOntoInjective honto hinj hmn).symm y) = y
  exact transition_equiv_injective honto hinj hmn y

/-- Onto-injective dimension transition-kernel maps reflect equality. -/
theorem dimension_transition_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x =
        dimensionTransition (R := R) φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_kernel_injective
    honto hinj hmn x y

/-- Onto-injective dimension transition-kernel maps reflect the identity. -/
theorem dimension_one_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_one_injective honto hinj hmn x

/-- Identity law for dimension transition-kernel equivalences. -/
@[simp] theorem dimension_injective_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dimensionOntoInjective (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
      MulEquiv.refl
        (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  change transitionOntoInjective
      (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) hmn =
    MulEquiv.refl (MonoidHom.ker (quotientTransition (dimensionFiltration R G) hmn))
  exact transition_injective_id (dimensionFiltration R G) hmn

/-- Composition law for dimension transition-kernel equivalences. -/
theorem dimension_injective_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    dimensionOntoInjective (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (dimensionOntoInjective
        (R := R) φ hφ hinjφ hmn).trans
        (dimensionOntoInjective
          (R := R) ψ hψ hinjψ hmn) := by
  change transitionOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (transitionOntoInjective hφ hinjφ hmn).trans
      (transitionOntoInjective hψ hinjψ hmn)
  exact transition_injective_comp hφ hψ hinjφ hinjψ hmn

/-- Forward-image characterization for small-kernel dimension transition equivalences. -/
theorem dimension_equiv_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn))
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn x = y ↔
      x = (dimensionMapsKer
        (R := R) φ honto hmn hker).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionMapsOnto honto hmn hker).symm y
  exact transition_kernel_equiv honto hmn hker x y

/-- Forward-image characterization for monotone small-kernel dimension transition equivalences. -/
theorem dimension_transition_kernel
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn))
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn x = y ↔
      x = (dimensionTransitionKer
        (R := R) φ honto hmn hker hnk).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionOntoKer honto hmn hker hnk).symm y
  exact transition_equiv_ker honto hmn hker hnk x y

/-- Inverse-after-map cancellation for small-kernel dimension transition equivalences. -/
@[simp] theorem dimension_kernel_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionMapsKer
        (R := R) φ honto hmn hker).symm
      (dimensionTransition (R := R) φ hmn x) = x := by
  change (transitionMapsOnto honto hmn hker).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact transition_kernel_onto honto hmn hker x

/-- Map-after-inverse cancellation for small-kernel dimension transition equivalences. -/
@[simp] theorem kernel_ker_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn
        ((dimensionMapsKer
          (R := R) φ honto hmn hker).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionMapsOnto honto hmn hker).symm y) = y
  exact transition_equiv_maps honto hmn hker y

/-- Inverse-after-map cancellation for monotone small-kernel dimension transition equivalences. -/
@[simp] theorem dimension_transition_maps
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    (dimensionTransitionKer
        (R := R) φ honto hmn hker hnk).symm
      (dimensionTransition (R := R) φ hmn x) = x := by
  change (transitionOntoKer honto hmn hker hnk).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact transition_kernel_symm honto hmn hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel dimension transition equivalences. -/
@[simp] theorem dimension_kernel_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (y : MonoidHom.ker (mapOfLe (R := R) (G := H) hmn)) :
    dimensionTransition (R := R) φ hmn
        ((dimensionTransitionKer
          (R := R) φ honto hmn hker hnk).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionOntoKer honto hmn hker hnk).symm y) = y
  exact transition_equiv_symm honto hmn hker hnk y

/-- Small-kernel dimension transition maps reflect equality. -/
theorem dimension_kernel_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x =
        dimensionTransition (R := R) φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_kernel_maps
    honto hmn hker x y

/-- Small-kernel dimension transition maps reflect the identity. -/
theorem dimension_one_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_one_ker honto hmn hker x

/-- Monotone small-kernel dimension transition maps reflect equality. -/
theorem dimension_transition_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x y : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x =
        dimensionTransition (R := R) φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_maps_onto
    honto hmn hker hnk x y

/-- Monotone small-kernel dimension transition maps reflect the identity. -/
theorem dimension_transition_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransition (R := R) φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_kernel_ker
    honto hmn hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]

/-- Forward-image characterization for small-kernel dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n)
    (x : dQuot R G n) (y : dQuot R H n) :
    dQuot.map (R := R) φ n x = y ↔
      x = (dQuot.equiv_mapsonto_kerle
        (R := R) φ honto hker).symm y := by
  change DFilt.quotientMap
      (DFilt.MapsOnto.preserves honto) n x = y ↔
    x = (DFilt.quotientMapsKer
      honto hker).symm y
  exact DFilt.maps_ker
    honto hker x y

/-- Forward-image characterization for monotone small-kernel dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (dimensionFiltration R G)
      (dimensionFiltration R H) φ) {m n : ℕ}
    (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (x : dQuot R G m) (y : dQuot R H m) :
    dQuot.map (R := R) φ m x = y ↔
      x = (dQuot.equivmaps_ontoker_lele
        (R := R) φ honto hker hmn).symm y := by
  change DFilt.quotientMap
      (DFilt.MapsOnto.preserves honto) m x = y ↔
    x = (DFilt.quotientOntoKer
      honto hker hmn).symm y
  exact DFilt.equiv_onto_ker
    honto hker hmn x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for small-kernel dimension term-quotient equivalences. -/
theorem dimension_quotient_maps
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) φ hmn x = y ↔
      x = (dimensionTermKer
        (R := R) φ honto hmn hker).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsOnto honto hmn hker).symm y
  exact term_quotient_equiv honto hmn hker x y

/-- Forward-image characterization for monotone small-kernel dimension term quotients. -/
theorem dimension_equiv_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) φ hmn x = y ↔
      x = (dimensionOntoKer
        (R := R) φ honto hmn hker hnk).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsKer honto hmn hker hnk).symm y
  exact term_equiv_ker honto hmn hker hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Small-kernel dimension quotient maps reflect equality. -/
theorem dQuot.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G n)
    (x y : dQuot R G n) :
    dQuot.map (R := R) φ n x =
        dQuot.map (R := R) φ n y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) n x =
      quotientMap (MapsOnto.preserves honto) n y ↔ x = y
  exact quotient_maps_onto honto hker x y

/-- Small-kernel dimension quotient maps reflect the identity. -/
theorem dQuot.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G n)
    (x : dQuot R G n) :
    dQuot.map (R := R) φ n x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_onto_ker honto hker x

/-- Monotone small-kernel dimension quotient maps reflect equality. -/
theorem dQuot.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (x y : dQuot R G m) :
    dQuot.map (R := R) φ m x =
        dQuot.map (R := R) φ m y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) m x =
      quotientMap (MapsOnto.preserves honto) m y ↔ x = y
  exact quotient_onto_ker
    honto hker hmn x y

/-- Monotone small-kernel dimension quotient maps reflect the identity. -/
theorem dQuot.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (x : dQuot R G m) :
    dQuot.map (R := R) φ m x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) m x = 1 ↔ x = 1
  exact quotient_maps_ker honto hker hmn x

/-- Small-kernel dimension term-quotient maps reflect equality. -/
theorem dimension_term_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x y : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x =
        dimensionTerm (R := R) φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_quotient_ker
    honto hmn hker x y

/-- Small-kernel dimension term-quotient maps reflect the identity. -/
theorem dimension_quotient_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_one_ker honto hmn hker x

/-- Monotone small-kernel dimension term-quotient maps reflect equality. -/
theorem dimension_onto_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x y : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x =
        dimensionTerm (R := R) φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_maps_ker
    honto hmn hker hnk x y

/-- Monotone small-kernel dimension term-quotient maps reflect the identity. -/
theorem dimension_maps_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_maps_onto
    honto hmn hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Identity law for small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    dQuot.equiv_mapsonto_kerle (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G))
        (id_ker_le (dimensionFiltration R G) n) =
      MulEquiv.refl (dQuot R G n) := by
  change quotientMapsKer (mapsOnto_id (dimensionFiltration R G))
      (id_ker_le (dimensionFiltration R G) n) = _
  exact quotient_onto_id (dimensionFiltration R G) n

/-- Identity law for monotone small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.equivmaps_ontoker_leleid
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dQuot.equivmaps_ontoker_lele (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G))
        (id_ker_le (dimensionFiltration R G) n) hmn =
      MulEquiv.refl (dQuot R G m) := by
  change quotientOntoKer
      (mapsOnto_id (dimensionFiltration R G))
      (id_ker_le (dimensionFiltration R G) n) hmn = _
  exact maps_ker_id (dimensionFiltration R G) hmn

/-- Identity law for small-kernel dimension term-quotient equivalences. -/
@[simp] theorem dimension_ker_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dimensionTermKer (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) hmn
        (id_ker_le (dimensionFiltration R G) n) =
      MulEquiv.refl
        (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) := by
  change termMapsOnto
      (mapsOnto_id (dimensionFiltration R G)) hmn
      (id_ker_le (dimensionFiltration R G) n) = _
  exact term_ker_id (dimensionFiltration R G) hmn

/-- Identity law for monotone small-kernel dimension term-quotient equivalences. -/
@[simp] theorem dimension_onto_id
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dimensionOntoKer (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) hmn
        (id_ker_le (dimensionFiltration R G) k) hnk =
      MulEquiv.refl
        (dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) := by
  change termMapsKer
      (mapsOnto_id (dimensionFiltration R G)) hmn
      (id_ker_le (dimensionFiltration R G) k) hnk = _
  exact term_onto_id (dimensionFiltration R G) hmn hnk

/-- Identity law for small-kernel dimension transition-kernel equivalences. -/
@[simp] theorem dimension_maps_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    dimensionMapsKer (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) hmn
        (id_ker_le (dimensionFiltration R G) n) =
      MulEquiv.refl
        (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  change transitionMapsOnto
      (mapsOnto_id (dimensionFiltration R G)) hmn
      (id_ker_le (dimensionFiltration R G) n) = _
  exact transition_ker_id (dimensionFiltration R G) hmn

/-- Identity law for monotone small-kernel dimension transition-kernel equivalences. -/
@[simp] theorem dimension_transition_id
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    dimensionTransitionKer (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) hmn
        (id_ker_le (dimensionFiltration R G) k) hnk =
      MulEquiv.refl
        (MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) := by
  change transitionOntoKer
      (mapsOnto_id (dimensionFiltration R G)) hmn
      (id_ker_le (dimensionFiltration R G) k) hnk = _
  exact transition_onto_id (dimensionFiltration R G) hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Inverse-after-map cancellation for small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G n)
    (x : dQuot R G n) :
    (dQuot.equiv_mapsonto_kerle (R := R) φ honto hker).symm
        (dQuot.map (R := R) φ n x) = x := by
  change (quotientMapsKer honto hker).symm
      (quotientMap (MapsOnto.preserves honto) n x) = x
  exact quotient_equiv_symm honto hker x

/-- Map-after-inverse cancellation for small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G n)
    (y : dQuot R H n) :
    dQuot.map (R := R) φ n
        ((dQuot.equiv_mapsonto_kerle (R := R) φ honto hker).symm y) = y := by
  change quotientMap (MapsOnto.preserves honto) n
      ((quotientMapsKer honto hker).symm y) = y
  exact quotient_equiv_onto honto hker y

/-- Inverse-after-map cancellation for monotone small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (x : dQuot R G m) :
    (dQuot.equivmaps_ontoker_lele
        (R := R) φ honto hker hmn).symm
      (dQuot.map (R := R) φ m x) = x := by
  change (quotientOntoKer honto hker hmn).symm
      (quotientMap (MapsOnto.preserves honto) m x) = x
  exact quotient_onto_symm honto hker hmn x

/-- Map-after-inverse cancellation for monotone small-kernel dimension quotient equivalences. -/
@[simp] theorem dQuot.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hker : φ.ker ≤ dSubgro R G n) (hmn : m ≤ n)
    (y : dQuot R H m) :
    dQuot.map (R := R) φ m
        ((dQuot.equivmaps_ontoker_lele
          (R := R) φ honto hker hmn).symm y) = y := by
  change quotientMap (MapsOnto.preserves honto) m
      ((quotientOntoKer honto hker hmn).symm y) = y
  exact equiv_ker_symm honto hker hmn y

/-- Inverse-after-map cancellation for small-kernel dimension term-quotient equivalences. -/
@[simp] theorem dimension_equiv_maps
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionTermKer
        (R := R) φ honto hmn hker).symm
      (dimensionTerm (R := R) φ hmn x) = x := by
  change (termMapsOnto honto hmn hker).symm
      (termQuotient (MapsOnto.preserves honto) hmn x) = x
  exact term_quotient_onto honto hmn hker x

/-- Map-after-inverse cancellation for small-kernel dimension term-quotient equivalences. -/
@[simp] theorem dimension_term_maps
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ dSubgro R G n)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) φ hmn
        ((dimensionTermKer
          (R := R) φ honto hmn hker).symm y) = y := by
  change termQuotient (MapsOnto.preserves honto) hmn
      ((termMapsOnto honto hmn hker).symm y) = y
  exact term_quotient_maps honto hmn hker y

/-- Inverse-after-map cancellation for monotone small-kernel dimension term quotients. -/
@[simp] theorem dimension_term_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    (dimensionOntoKer
        (R := R) φ honto hmn hker hnk).symm
      (dimensionTerm (R := R) φ hmn x) = x := by
  change (termMapsKer honto hmn hker hnk).symm
      (termQuotient (MapsOnto.preserves honto) hmn x) = x
  exact term_quotient_symm honto hmn hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel dimension term quotients. -/
@[simp] theorem dimension_maps_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ dSubgro R G k) (hnk : n ≤ k)
    (y : dSubgro R H m ⧸ dTSubgro (R := R) (G := H) hmn) :
    dimensionTerm (R := R) φ hmn
        ((dimensionOntoKer
          (R := R) φ honto hmn hker hnk).symm y) = y := by
  change termQuotient (MapsOnto.preserves honto) hmn
      ((termMapsKer honto hmn hker hnk).symm y) = y
  exact term_equiv_symm honto hmn hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Onto-injective dimension quotient maps reflect equality. -/
theorem dQuot.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x y : dQuot R G n) :
    dQuot.map (R := R) φ n x =
        dQuot.map (R := R) φ n y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) n x =
      quotientMap (MapsOnto.preserves honto) n y ↔ x = y
  exact quotient_onto_injective honto hinj n x y

/-- Onto-injective dimension quotient maps reflect the identity. -/
theorem dQuot.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : dQuot R G n) :
    dQuot.map (R := R) φ n x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_onto_injective honto hinj n x

/-- Onto-injective dimension term-quotient maps reflect equality. -/
theorem dimension_onto_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x y : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x =
        dimensionTerm (R := R) φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_maps_injective
    honto hinj hmn x y

/-- Onto-injective dimension term-quotient maps reflect the identity. -/
theorem dimension_maps_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionTerm (R := R) φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_quotient_injective honto hinj hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for onto-injective consecutive dimension
quotient equivalences. -/
theorem dNQuot.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n x = y ↔
      x = (dNQuot.equiv_maps_ontoinj
        (R := R) φ honto hinj n).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoInjective honto hinj n).symm y
  exact next_equiv_injective honto hinj n x y

/-- Forward-image characterization for small-kernel consecutive dimension quotient equivalences. -/
theorem dNQuot.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dSubgro R G n ⧸ dNTerm R G n)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n x = y ↔
      x = (dNQuot.equiv_mapsonto_kerle
        (R := R) φ honto n hker).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextMapsKer honto n hker).symm y
  exact next_equiv_maps honto n hker x y

/-- Forward-image characterization for monotone small-kernel consecutive dimension
quotient equivalences. -/
theorem dNQuot.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n x = y ↔
      x = (dNQuot.equivmaps_ontoker_lele
        (R := R) φ honto n hker hnk).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoKer honto n hker hnk).symm y
  exact next_term_onto honto n hker hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Forward-image characterization for onto-injective dimension layer equivalences. -/
theorem dLKern.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : dLKern R G n) (y : dLKern R H n) :
    dLKern.map (R := R) φ n x = y ↔
      x = (dLKern.equiv_maps_ontoinj
        (R := R) φ honto hinj n).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoInjective honto hinj n).symm y
  exact layer_injective honto hinj n x y

/-- Forward-image characterization for small-kernel dimension layer equivalences. -/
theorem dLKern.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dLKern R G n) (y : dLKern R H n) :
    dLKern.map (R := R) φ n x = y ↔
      x = (dLKern.equiv_mapsonto_kerle
        (R := R) φ honto n hker).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerMapsKer honto n hker).symm y
  exact layer_onto honto n hker x y

/-- Forward-image characterization for monotone small-kernel dimension layer equivalences. -/
theorem dLKern.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (x : dLKern R G n) (y : dLKern R H n) :
    dLKern.map (R := R) φ n x = y ↔
      x = (dLKern.equivmaps_ontoker_lele
        (R := R) φ honto n hker hnk).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoKer honto n hker hnk).symm y
  exact layer_equiv_ker honto n hker hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Onto-injective consecutive dimension quotient maps reflect equality. -/
theorem dNQuot.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x y : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x =
        dNQuot.map (R := R) φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_onto_injective
    honto hinj n x y

/-- Onto-injective consecutive dimension quotient maps reflect the identity. -/
theorem dNQuot.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_quotient_injective honto hinj n x

/-- Small-kernel consecutive dimension quotient maps reflect equality. -/
theorem dNQuot.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x y : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x =
        dNQuot.map (R := R) φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_term_ker honto hker x y

/-- Small-kernel consecutive dimension quotient maps reflect the identity. -/
theorem dNQuot.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_quotient_ker honto hker x

/-- Monotone small-kernel consecutive dimension quotient maps reflect equality. -/
theorem dNQuot.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (x y : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x =
        dNQuot.map (R := R) φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_onto_ker
    honto n hker hnk x y

/-- Monotone small-kernel consecutive dimension quotient maps reflect the identity. -/
theorem dNQuot.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.map (R := R) φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_maps_ker
    honto n hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Onto-injective dimension layer maps reflect equality. -/
theorem dLKern.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x y : dLKern R G n) :
    dLKern.map (R := R) φ n x =
        dLKern.map (R := R) φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact layer_onto_injective honto hinj n x y

/-- Onto-injective dimension layer maps reflect the identity. -/
theorem dLKern.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : dLKern R G n) :
    dLKern.map (R := R) φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_maps_injective honto hinj n x

/-- Small-kernel dimension layer maps reflect equality. -/
theorem dLKern.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x y : dLKern R G n) :
    dLKern.map (R := R) φ n x =
        dLKern.map (R := R) φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact onto_ker honto hker x y

/-- Small-kernel dimension layer maps reflect the identity. -/
theorem dLKern.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    {n : ℕ} (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dLKern R G n) :
    dLKern.map (R := R) φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_maps_ker honto hker x

/-- Monotone small-kernel dimension layer maps reflect equality. -/
theorem dLKern.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k) (x y : dLKern R G n) :
    dLKern.map (R := R) φ n x =
        dLKern.map (R := R) φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact layer_onto_ker honto n hker hnk x y

/-- Monotone small-kernel dimension layer maps reflect the identity. -/
theorem dLKern.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k) (x : dLKern R G n) :
    dLKern.map (R := R) φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact layer_maps_ker honto n hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Identity law for onto-injective dimension consecutive-quotient equivalences. -/
@[simp] theorem dNQuot.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    dNQuot.equiv_maps_ontoinj (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) n =
      MulEquiv.refl (dSubgro R G n ⧸ dNTerm R G n) := by
  exact next_injective_id (dimensionFiltration R G) n

/-- Identity law for small-kernel dimension consecutive-quotient equivalences. -/
@[simp] theorem dNQuot.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    dNQuot.equiv_mapsonto_kerle (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) n (id_ker_le (dimensionFiltration R G) (n + 1)) =
      MulEquiv.refl (dSubgro R G n ⧸ dNTerm R G n) := by
  exact next_maps_id (dimensionFiltration R G) n

/-- Identity law for monotone small-kernel dimension consecutive-quotient equivalences. -/
@[simp] theorem dNQuot.equivmaps_ontoker_leleid
    (G : Type*) [Group G] (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    dNQuot.equivmaps_ontoker_lele (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) n (id_ker_le (dimensionFiltration R G) k) hnk =
      MulEquiv.refl (dSubgro R G n ⧸ dNTerm R G n) := by
  exact next_onto_id (dimensionFiltration R G) n hnk

/-- Identity law for onto-injective dimension layer equivalences. -/
@[simp] theorem dLKern.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.equiv_maps_ontoinj (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) (fun _ _ h => h) n =
      MulEquiv.refl (dLKern R G n) := by
  exact layer_injective_id (dimensionFiltration R G) n

/-- Identity law for small-kernel dimension layer equivalences. -/
@[simp] theorem dLKern.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    dLKern.equiv_mapsonto_kerle (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) n (id_ker_le (dimensionFiltration R G) (n + 1)) =
      MulEquiv.refl (dLKern R G n) := by
  exact layer_maps_id (dimensionFiltration R G) n

/-- Identity law for monotone small-kernel dimension layer equivalences. -/
@[simp] theorem dLKern.equivmaps_ontoker_leleid
    (G : Type*) [Group G] (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    dLKern.equivmaps_ontoker_lele (R := R) (MonoidHom.id G)
        (mapsOnto_id (dimensionFiltration R G)) n (id_ker_le (dimensionFiltration R G) k) hnk =
      MulEquiv.refl (dLKern R G n) := by
  exact layer_onto_id (dimensionFiltration R G) n hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for onto-injective dimension consecutive quotient equivalences. -/
theorem dNQuot.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    dNQuot.equiv_maps_ontoinj (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (dNQuot.equiv_maps_ontoinj (R := R) φ hφ hinjφ n).trans
        (dNQuot.equiv_maps_ontoinj (R := R) ψ hψ hinjψ n) := by
  change nextOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (nextOntoInjective hφ hinjφ n).trans
      (nextOntoInjective hψ hinjψ n)
  exact next_injective_comp hφ hψ hinjφ hinjψ n

/-- Composition law for onto-injective dimension layer-kernel equivalences. -/
theorem dLKern.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    dLKern.equiv_maps_ontoinj (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (dLKern.equiv_maps_ontoinj (R := R) φ hφ hinjφ n).trans
        (dLKern.equiv_maps_ontoinj (R := R) ψ hψ hinjψ n) := by
  change layerOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (layerOntoInjective hφ hinjφ n).trans
      (layerOntoInjective hψ hinjψ n)
  exact layer_injective_comp hφ hψ hinjφ hinjψ n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Inverse-after-map cancellation for onto-injective dimension next quotients. -/
@[simp] theorem dNQuot.equivmaps_ontoinj_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equiv_maps_ontoinj
        (R := R) φ honto hinj n).symm
      (dNQuot.map (R := R) φ n x) = x := by
  change (nextOntoInjective honto hinj n).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_injective_symm honto hinj n x

/-- Map-after-inverse cancellation for onto-injective dimension next quotients. -/
@[simp] theorem dNQuot.mapapply_equivmaps_ontoinjsymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n
        ((dNQuot.equiv_maps_ontoinj
          (R := R) φ honto hinj n).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextOntoInjective honto hinj n).symm y) = y
  exact next_maps_injective honto hinj n y

/-- Inverse-after-map cancellation for small-kernel dimension next quotients. -/
@[simp] theorem dNQuot.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equiv_mapsonto_kerle
        (R := R) φ honto n hker).symm
      (dNQuot.map (R := R) φ n x) = x := by
  change (nextMapsKer honto n hker).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_term_maps honto n hker x

/-- Map-after-inverse cancellation for small-kernel dimension next quotients. -/
@[simp] theorem dNQuot.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n
        ((dNQuot.equiv_mapsonto_kerle
          (R := R) φ honto n hker).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextMapsKer honto n hker).symm y) = y
  exact next_quotient_symm honto n hker y

/-- Inverse-after-map cancellation for monotone small-kernel dimension next quotients. -/
@[simp] theorem dNQuot.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    (dNQuot.equivmaps_ontoker_lele
        (R := R) φ honto n hker hnk).symm
      (dNQuot.map (R := R) φ n x) = x := by
  change (nextOntoKer honto n hker hnk).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_ker_symm
    honto n hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel dimension next quotients. -/
@[simp] theorem dNQuot.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k)
    (y : dSubgro R H n ⧸ dNTerm R H n) :
    dNQuot.map (R := R) φ n
        ((dNQuot.equivmaps_ontoker_lele
          (R := R) φ honto n hker hnk).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextOntoKer honto n hker hnk).symm y) = y
  exact next_term_symm
    honto n hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Inverse-after-map cancellation for onto-injective dimension layer kernels. -/
@[simp] theorem dLKern.equivmaps_ontoinj_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : dLKern R G n) :
    (dLKern.equiv_maps_ontoinj
        (R := R) φ honto hinj n).symm
      (dLKern.map (R := R) φ n x) = x := by
  change (layerOntoInjective honto hinj n).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_maps_injective honto hinj n x

/-- Map-after-inverse cancellation for onto-injective dimension layer kernels. -/
@[simp] theorem dLKern.mapapply_equivmaps_ontoinjsymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (y : dLKern R H n) :
    dLKern.map (R := R) φ n
        ((dLKern.equiv_maps_ontoinj
          (R := R) φ honto hinj n).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerOntoInjective honto hinj n).symm y) = y
  exact layer_injective_symm honto hinj n y

/-- Inverse-after-map cancellation for small-kernel dimension layer kernels. -/
@[simp] theorem dLKern.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (x : dLKern R G n) :
    (dLKern.equiv_mapsonto_kerle
        (R := R) φ honto n hker).symm
      (dLKern.map (R := R) φ n x) = x := by
  change (layerMapsKer honto n hker).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_equiv_onto honto n hker x

/-- Map-after-inverse cancellation for small-kernel dimension layer kernels. -/
@[simp] theorem dLKern.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) (hker : φ.ker ≤ dSubgro R G (n + 1))
    (y : dLKern R H n) :
    dLKern.map (R := R) φ n
        ((dLKern.equiv_mapsonto_kerle
          (R := R) φ honto n hker).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerMapsKer honto n hker).symm y) = y
  exact layer_equiv_maps honto n hker y

/-- Inverse-after-map cancellation for monotone small-kernel dimension layer kernels. -/
@[simp] theorem dLKern.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k) (x : dLKern R G n) :
    (dLKern.equivmaps_ontoker_lele
        (R := R) φ honto n hker hnk).symm
      (dLKern.map (R := R) φ n x) = x := by
  change (layerOntoKer honto n hker hnk).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_maps_onto honto n hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel dimension layer kernels. -/
@[simp] theorem dLKern.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ dSubgro R G k)
    (hnk : n + 1 ≤ k) (y : dLKern R H n) :
    dLKern.map (R := R) φ n
        ((dLKern.equivmaps_ontoker_lele
          (R := R) φ honto n hker hnk).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerOntoKer honto n hker hnk).symm y) = y
  exact layer_ker_symm honto n hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for small-kernel dimension consecutive quotient equivalences. -/
theorem dNQuot.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) (hkφ : φ.ker ≤ dSubgro R G (n + 1))
    (hkψ : ψ.ker ≤ dSubgro R H (n + 1)) :
    dNQuot.equiv_mapsonto_kerle (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (dNQuot.equiv_mapsonto_kerle (R := R) φ hφ n hkφ).trans
        (dNQuot.equiv_mapsonto_kerle (R := R) ψ hψ n hkψ) := by
  change nextMapsKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (nextMapsKer hφ n hkφ).trans
      (nextMapsKer hψ n hkψ)
  exact next_term_comp hφ hψ n hkφ hkψ

/-- Composition law for small-kernel dimension layer-kernel equivalences. -/
theorem dLKern.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) (hkφ : φ.ker ≤ dSubgro R G (n + 1))
    (hkψ : ψ.ker ≤ dSubgro R H (n + 1)) :
    dLKern.equiv_mapsonto_kerle (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (dLKern.equiv_mapsonto_kerle (R := R) φ hφ n hkφ).trans
        (dLKern.equiv_mapsonto_kerle (R := R) ψ hψ n hkψ) := by
  change layerMapsKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (layerMapsKer hφ n hkφ).trans
      (layerMapsKer hψ n hkψ)
  exact equiv_maps_comp hφ hψ n hkφ hkψ

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for monotone small-kernel dimension next equivalences at a common depth. -/
theorem dNQuot.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hnk : n + 1 ≤ k) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (dNQuot.equivmaps_ontoker_lele
        (R := R) φ hφ n hkφ hnk).trans
        (dNQuot.equivmaps_ontoker_lele
          (R := R) ψ hψ n hkψ hnk) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (nextOntoKer hφ n hkφ hnk).trans
      (nextOntoKer hψ n hkψ hnk)
  exact next_same_level
    hφ hψ n hkφ hkψ hnk

/-- Composition law for monotone small-kernel dimension layer equivalences at a common depth. -/
theorem dLKern.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hnk : n + 1 ≤ k) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (dLKern.equivmaps_ontoker_lele
        (R := R) φ hφ n hkφ hnk).trans
        (dLKern.equivmaps_ontoker_lele
          (R := R) ψ hψ n hkψ hnk) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (layerOntoKer hφ n hkφ hnk).trans
      (layerOntoKer hψ n hkψ hnk)
  exact layer_same_level hφ hψ n hkφ hkψ hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Composition law for small-kernel dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {n : ℕ} (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H n) :
    dQuot.equiv_mapsonto_kerle (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (dQuot.equiv_mapsonto_kerle (R := R) φ hφ hkφ).trans
        (dQuot.equiv_mapsonto_kerle (R := R) ψ hψ hkψ) := by
  change quotientMapsKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (quotientMapsKer hφ hkφ).trans
      (quotientMapsKer hψ hkψ)
  exact quotient_ker_comp hφ hψ hkφ hkψ

/-- Composition law for small-kernel dimension term-quotient equivalences. -/
theorem dimension_quotient_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H n) :
    dimensionTermKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (dimensionTermKer (R := R) φ hφ hmn hkφ).trans
        (dimensionTermKer (R := R) ψ hψ hmn hkψ) := by
  change termMapsOnto (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (termMapsOnto hφ hmn hkφ).trans
      (termMapsOnto hψ hmn hkψ)
  exact term_quotient_comp hφ hψ hmn hkφ hkψ

/-- Composition law for small-kernel dimension transition-kernel equivalences. -/
theorem dimension_kernel_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H n) :
    dimensionMapsKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (dimensionMapsKer (R := R) φ hφ hmn hkφ).trans
        (dimensionMapsKer (R := R) ψ hψ hmn hkψ) := by
  change transitionMapsOnto (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (transitionMapsOnto hφ hmn hkφ).trans
      (transitionMapsOnto hψ hmn hkψ)
  exact transition_equiv_comp hφ hψ hmn hkφ hkψ

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Common-depth monotone composition law for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m k : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hmk : m ≤ k) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hmk =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ hmk).trans
        (dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ hmk) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hmk =
    (quotientOntoKer hφ hkφ hmk).trans
      (quotientOntoKer hψ hkψ hmk)
  exact ker_same_level hφ hψ hkφ hkψ hmk

/-- Common-depth monotone composition law for dimension term-quotient equivalences. -/
theorem maps_same_level
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hnk : n ≤ k) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (dimensionOntoKer
        (R := R) φ hφ hmn hkφ hnk).trans
        (dimensionOntoKer
          (R := R) ψ hψ hmn hkψ hnk) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (termMapsKer hφ hmn hkφ hnk).trans
      (termMapsKer hψ hmn hkψ hnk)
  exact term_same_level
    hφ hψ hmn hkφ hkψ hnk

/-- Common-depth monotone composition law for dimension transition-kernel equivalences. -/
theorem dimension_same_level
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hnk : n ≤ k) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (dimensionTransitionKer
        (R := R) φ hφ hmn hkφ hnk).trans
        (dimensionTransitionKer
          (R := R) ψ hψ hmn hkψ hnk) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (transitionOntoKer hφ hmn hkφ hnk).trans
      (transitionOntoKer hψ hmn hkψ hnk)
  exact transition_same_level
    hφ hψ hmn hkφ hkψ hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Heterogeneous-depth composition law for monotone dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk =
      (dQuot.equivmaps_ontoker_lele
        (R := R) φ hφ hkφ (le_trans hmk hka)).trans
        (dQuot.equivmaps_ontoker_lele
          (R := R) ψ hψ hkψ (le_trans hmk hkb)) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk =
    (quotientOntoKer hφ hkφ (le_trans hmk hka)).trans
      (quotientOntoKer hψ hkψ (le_trans hmk hkb))
  exact quotient_maps_comp hφ hψ hkφ hkψ hka hkb hmk

/-- Heterogeneous-depth composition law for monotone dimension term-quotient equivalences. -/
theorem dimension_term_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (dimensionOntoKer
        (R := R) φ hφ hmn hkφ (le_trans hnk hka)).trans
        (dimensionOntoKer
          (R := R) ψ hψ hmn hkψ (le_trans hnk hkb)) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (termMapsKer hφ hmn hkφ (le_trans hnk hka)).trans
      (termMapsKer hψ hmn hkψ (le_trans hnk hkb))
  exact term_ker_comp hφ hψ hmn hkφ hkψ hka hkb hnk

/-- Heterogeneous-depth composition law for monotone dimension transition-kernel equivalences. -/
theorem dimension_ker_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (dimensionTransitionKer
        (R := R) φ hφ hmn hkφ (le_trans hnk hka)).trans
        (dimensionTransitionKer
          (R := R) ψ hψ hmn hkψ (le_trans hnk hkb)) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).trans
      (transitionOntoKer hψ hmn hkψ (le_trans hnk hkb))
  exact transition_kernel_comp hφ hψ hmn hkφ hkψ hka hkb hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Heterogeneous-depth composition law for monotone dimension next-quotient equivalences. -/
theorem dNQuot.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (dNQuot.equivmaps_ontoker_lele
        (R := R) φ hφ n hkφ (le_trans hnk hka)).trans
        (dNQuot.equivmaps_ontoker_lele
          (R := R) ψ hψ n hkψ (le_trans hnk hkb)) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
      (nextOntoKer hψ n hkψ (le_trans hnk hkb))
  exact next_ker_comp hφ hψ n hkφ hkψ hka hkb hnk

/-- Heterogeneous-depth composition law for monotone dimension layer-kernel equivalences. -/
theorem dLKern.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (dLKern.equivmaps_ontoker_lele
        (R := R) φ hφ n hkφ (le_trans hnk hka)).trans
        (dLKern.equivmaps_ontoker_lele
          (R := R) ψ hψ n hkψ (le_trans hnk hkb)) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
      (layerOntoKer hψ n hkψ (le_trans hnk hkb))
  exact layer_ker_comp hφ hψ n hkφ hkψ hka hkb hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Minimum-depth composition law for monotone dimension quotient equivalences. -/
theorem dQuot.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hm : m ≤ min a b) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).trans
        (dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
          (le_trans hm (Nat.min_le_right a b))) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm =
    (quotientOntoKer hφ hkφ
      (le_trans hm (Nat.min_le_left a b))).trans
      (quotientOntoKer hψ hkψ
        (le_trans hm (Nat.min_le_right a b)))
  exact onto_ker_min hφ hψ hkφ hkψ hm

/-- Minimum-depth composition law for monotone dimension term-quotient equivalences. -/
theorem dimension_term_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (dimensionOntoKer (R := R) φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (dimensionOntoKer (R := R) ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (termMapsKer hφ hmn hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (termMapsKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact term_onto_min hφ hψ hmn hkφ hkψ hn

/-- Minimum-depth composition law for monotone dimension transition-kernel equivalences. -/
theorem dimension_maps_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (dimensionTransitionKer (R := R) φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (dimensionTransitionKer (R := R) ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (transitionOntoKer hφ hmn hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (transitionOntoKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact transition_maps_min hφ hψ hmn hkφ hkψ hn

/-- Minimum-depth composition law for monotone dimension next-quotient equivalences. -/
theorem dNQuot.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (nextOntoKer hφ n hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (nextOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact next_onto_min hφ hψ n hkφ hkψ hn

/-- Minimum-depth composition law for monotone dimension layer-kernel equivalences. -/
theorem dLKern.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (layerOntoKer hφ n hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (layerOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact layer_onto_min hφ hψ n hkφ hkψ hn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise minimum-depth composition formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hm : m ≤ min a b)
    (x : dQuot R G m) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm x =
      dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
        (le_trans hm (Nat.min_le_right a b))
        (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
          (le_trans hm (Nat.min_le_left a b)) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm x =
      quotientOntoKer hψ hkψ
        (le_trans hm (Nat.min_le_right a b))
        (quotientOntoKer hφ hkφ
          (le_trans hm (Nat.min_le_left a b)) x)
  exact maps_onto_min hφ hψ hkφ hkψ hm x

/-- Inverse pointwise minimum-depth composition formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hm : m ≤ min a b)
    (z : dQuot R K m) :
    (dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm).symm z =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).symm
        ((dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
          (le_trans hm (Nat.min_le_right a b))).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm).symm z =
      (quotientOntoKer hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).symm
        ((quotientOntoKer hψ hkψ
          (le_trans hm (Nat.min_le_right a b))).symm z)
  exact maps_min_symm hφ hψ hkφ hkψ hm z

/-- Pointwise minimum-depth composition formula for dimension term-quotient equivalences. -/
theorem dimension_onto_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      dimensionOntoKer (R := R) ψ hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (dimensionOntoKer (R := R) φ hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      termMapsKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (termMapsKer hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact term_comp_min hφ hψ hmn hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for dimension term-quotient equivalences. -/
theorem dimension_comp_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b)
    (z : dSubgro R K m ⧸ dTSubgro (R := R) (G := K) hmn) :
    (dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (dimensionOntoKer (R := R) φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((dimensionOntoKer (R := R) ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (termMapsKer hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((termMapsKer hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact term_min_symm hφ hψ hmn hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise minimum-depth composition formula for dimension transition-kernel equivalences. -/
theorem dimension_transition_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      dimensionTransitionKer (R := R) ψ hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (dimensionTransitionKer (R := R) φ hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      transitionOntoKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (transitionOntoKer hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact transition_onto_min hφ hψ hmn hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for dimension
transition-kernel equivalences. -/
theorem dimension_min_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n ≤ min a b)
    (z : MonoidHom.ker (mapOfLe (R := R) (G := K) hmn)) :
    (dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (dimensionTransitionKer (R := R) φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((dimensionTransitionKer (R := R) ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (transitionOntoKer hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((transitionOntoKer hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact transition_min_symm hφ hψ hmn hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise minimum-depth composition formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      nextOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (nextOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact next_comp_min hφ hψ n hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b)
    (z : dSubgro R K n ⧸ dNTerm R K n) :
    (dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (nextOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((nextOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact next_min_symm hφ hψ n hkφ hkψ hn z

/-- Pointwise minimum-depth composition formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b)
    (x : dLKern R G n) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      layerOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (layerOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact layer_comp_min hφ hψ n hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hn : n + 1 ≤ min a b)
    (z : dLKern R K n) :
    (dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (layerOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((layerOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact layer_min_symm hφ hψ n hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise heterogeneous-depth composition formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k)
    (x : dQuot R G m) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk x =
      dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
        (le_trans hmk hkb)
        (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
          (le_trans hmk hka) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk x =
      quotientOntoKer hψ hkψ (le_trans hmk hkb)
        (quotientOntoKer hφ hkφ (le_trans hmk hka) x)
  exact quotient_onto_comp hφ hψ hkφ hkψ hka hkb hmk x

/-- Inverse pointwise heterogeneous-depth composition formula for dimension
quotient equivalences. -/
theorem dQuot.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k)
    (z : dQuot R K m) :
    (dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk).symm z =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
        (le_trans hmk hka)).symm
        ((dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
          (le_trans hmk hkb)).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmk hka)).symm
        ((quotientOntoKer hψ hkψ (le_trans hmk hkb)).symm z)
  exact maps_ker_symm hφ hψ hkφ hkψ hka hkb hmk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise heterogeneous-depth composition formula for dimension term quotients. -/
theorem dimension_maps_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      dimensionOntoKer (R := R) ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (dimensionOntoKer (R := R) φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      termMapsKer hψ hmn hkψ (le_trans hnk hkb)
        (termMapsKer hφ hmn hkφ (le_trans hnk hka) x)
  exact term_onto_comp hφ hψ hmn hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for dimension term quotients. -/
theorem dimension_term_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : dSubgro R K m ⧸ dTSubgro (R := R) (G := K) hmn) :
    (dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (dimensionOntoKer (R := R) φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((dimensionOntoKer (R := R) ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (termMapsKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact term_ker_symm hφ hψ hmn hkφ hkψ hka hkb hnk z

/-- Pointwise heterogeneous-depth composition formula for dimension transition kernels. -/
theorem dimension_transition_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      dimensionTransitionKer (R := R) ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (dimensionTransitionKer (R := R) φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ hmn hkφ (le_trans hnk hka) x)
  exact transition_ker_comp hφ hψ hmn hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for dimension transition kernels. -/
theorem dimension_ker_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (mapOfLe (R := R) (G := K) hmn)) :
    (dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (dimensionTransitionKer (R := R) φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((dimensionTransitionKer (R := R) ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact transition_ker_symm hφ hψ hmn
    hkφ hkψ hka hkb hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise heterogeneous-depth composition formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hnk hkb)
        (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact next_onto_comp hφ hψ n hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for consecutive
dimension quotients. -/
theorem dNQuot.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : dSubgro R K n ⧸ dNTerm R K n) :
    (dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact next_maps_symm hφ hψ n
    hkφ hkψ hka hkb hnk z

/-- Pointwise heterogeneous-depth composition formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : dLKern R G n) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hnk hkb)
        (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact layer_onto_comp hφ hψ n hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : dLKern R K n) :
    (dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact layer_maps_symm hφ hψ n hkφ hkψ hka hkb hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {R : Type*} [CommRing R]
open DFilt

/-- Dimension-filtration same-depth composite-kernel containment. -/
theorem dMOnto.comp_kerle_samelevel
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {n : ℕ}
    (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H n) :
    (ψ.comp φ).ker ≤ dSubgro R G n := by
  exact MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ

/-- Dimension-filtration one-sided composite-kernel containment
(left depth fixed). -/
theorem dMOnto.comp_kerle_leftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {n b : ℕ}
    (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hnb : n ≤ b) :
    (ψ.comp φ).ker ≤ dSubgro R G n := by
  exact MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb

/-- Dimension-filtration one-sided composite-kernel containment
(right depth fixed). -/
theorem dMOnto.comp_kerle_rightle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {a n : ℕ}
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H n) (hna : n ≤ a) :
    (ψ.comp φ).ker ≤ dSubgro R G n := by
  exact MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna

/-- Dimension-filtration successor-depth composite-kernel containment. -/
theorem dMOnto.comp_ker_lesucc
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {n : ℕ}
    (hkφ : φ.ker ≤ dSubgro R G (n + 1))
    (hkψ : ψ.ker ≤ dSubgro R H (n + 1)) :
    (ψ.comp φ).ker ≤ dSubgro R G n := by
  exact MapsOnto.comp_ker_lesucc hφ hψ hkφ hkψ

/-- Dimension-filtration minimum-depth composite-kernel containment. -/
theorem dMOnto.comp_ker_lemin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {a b : ℕ}
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H b) :
    (ψ.comp φ).ker ≤ dSubgro R G (min a b) := by
  exact MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- One-sided (left-depth) composition law for dimension quotient equivalences. -/
theorem dQuot.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hnb : n ≤ b) (hmn : m ≤ n) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ hmn).trans
        (dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
          (le_trans hmn hnb)) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn =
      (quotientOntoKer hφ hkφ hmn).trans
        (quotientOntoKer hψ hkψ (le_trans hmn hnb))
  exact onto_ker_left hφ hψ hkφ hkψ hnb hmn

/-- One-sided (right-depth) composition law for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H n) (hna : n ≤ a) (hmn : m ≤ n) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
        (le_trans hmn hna)).trans
        (dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ hmn) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).trans
        (quotientOntoKer hψ hkψ hmn)
  exact onto_ker_right hφ hψ hkφ hkψ hna hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- One-sided (left-depth) composition law for dimension term quotients. -/
theorem dimension_maps_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (dimensionOntoKer (R := R) φ hφ h hkφ hnk).trans
        (dimensionOntoKer (R := R) ψ hψ h hkψ
          (le_trans hnk hkb)) := by
  change termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (termMapsKer hφ h hkφ hnk).trans
        (termMapsKer hψ h hkψ (le_trans hnk hkb))
  exact term_onto_left hφ hψ h hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for dimension term quotients. -/
theorem dimension_onto_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (dimensionOntoKer (R := R) φ hφ h hkφ
        (le_trans hnk hka)).trans
        (dimensionOntoKer (R := R) ψ hψ h hkψ hnk) := by
  change termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).trans
        (termMapsKer hψ h hkψ hnk)
  exact term_maps_comp hφ hψ h hkφ hkψ hka hnk

/-- One-sided (left-depth) composition law for dimension transition kernels. -/
theorem dimension_transition_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (dimensionTransitionKer (R := R) φ hφ h hkφ hnk).trans
        (dimensionTransitionKer (R := R) ψ hψ h hkψ
          (le_trans hnk hkb)) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (transitionOntoKer hφ h hkφ hnk).trans
        (transitionOntoKer hψ h hkψ (le_trans hnk hkb))
  exact transition_maps_left hφ hψ h hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for dimension transition kernels. -/
theorem dimension_transition_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (dimensionTransitionKer (R := R) φ hφ h hkφ
        (le_trans hnk hka)).trans
        (dimensionTransitionKer (R := R) ψ hψ h hkψ hnk) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).trans
        (transitionOntoKer hψ h hkψ hnk)
  exact transition_onto_right hφ hψ h hkφ hkψ hka hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- One-sided (left-depth) composition law for consecutive dimension quotients. -/
theorem dNQuot.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk).trans
        (dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (nextOntoKer hφ n hkφ hnk).trans
        (nextOntoKer hψ n hkψ (le_trans hnk hkb))
  exact next_onto_left hφ hψ n hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).trans
        (dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (nextOntoKer hψ n hkψ hnk)
  exact next_maps_comp hφ hψ n hkφ hkψ hka hnk

/-- One-sided (left-depth) composition law for dimension layer kernels. -/
theorem dLKern.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk).trans
        (dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (layerOntoKer hφ n hkφ hnk).trans
        (layerOntoKer hψ n hkψ (le_trans hnk hkb))
  exact layer_onto_left hφ hψ n hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for dimension layer kernels. -/
theorem dLKern.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).trans
        (dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (layerOntoKer hψ n hkψ hnk)
  exact layer_maps_comp hφ hψ n hkφ hkψ hka hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise left-depth one-sided composition formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hnb : n ≤ b) (hmn : m ≤ n)
    (x : dQuot R G m) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn x =
      dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
        (le_trans hmn hnb)
        (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ hmn x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn x =
      quotientOntoKer hψ hkψ (le_trans hmn hnb)
        (quotientOntoKer hφ hkφ hmn x)
  exact maps_onto_left hφ hψ hkφ hkψ hnb hmn x

/-- Pointwise right-depth one-sided composition formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H n) (hna : n ≤ a) (hmn : m ≤ n)
    (x : dQuot R G m) :
    dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn x =
      dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ hmn
        (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
          (le_trans hmn hna) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn x =
      quotientOntoKer hψ hkψ hmn
        (quotientOntoKer hφ hkφ (le_trans hmn hna) x)
  exact maps_onto_right hφ hψ hkφ hkψ hna hmn x

/-- Inverse pointwise left-depth one-sided formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ dSubgro R G n)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hnb : n ≤ b) (hmn : m ≤ n)
    (z : dQuot R K m) :
    (dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn).symm z =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ hmn).symm
        ((dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ
          (le_trans hmn hnb)).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn).symm z =
      (quotientOntoKer hφ hkφ hmn).symm
        ((quotientOntoKer hψ hkψ (le_trans hmn hnb)).symm z)
  exact comp_left_symm hφ hψ hkφ hkψ hnb hmn z

/-- Inverse pointwise right-depth one-sided formula for dimension quotient equivalences. -/
theorem dQuot.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H n) (hna : n ≤ a) (hmn : m ≤ n)
    (z : dQuot R K m) :
    (dQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn).symm z =
      (dQuot.equivmaps_ontoker_lele (R := R) φ hφ hkφ
        (le_trans hmn hna)).symm
        ((dQuot.equivmaps_ontoker_lele (R := R) ψ hψ hkψ hmn).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).symm
        ((quotientOntoKer hψ hkψ hmn).symm z)
  exact comp_right_symm hφ hψ hkφ hkψ hna hmn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise left-depth one-sided formula for dimension term quotients. -/
theorem dimension_onto_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      dimensionOntoKer (R := R) ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (dimensionOntoKer (R := R) φ hφ hmn hkφ hnk x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      termMapsKer hψ hmn hkψ (le_trans hnk hkb)
        (termMapsKer hφ hmn hkφ hnk x)
  exact term_comp_left hφ hψ hmn hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for dimension term quotients. -/
theorem dimension_onto_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : dSubgro R G m ⧸ dTSubgro (R := R) (G := G) hmn) :
    dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      dimensionOntoKer (R := R) ψ hψ hmn hkψ hnk
        (dimensionOntoKer (R := R) φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      termMapsKer hψ hmn hkψ hnk
        (termMapsKer hφ hmn hkφ (le_trans hnk hka) x)
  exact term_comp_right hφ hψ hmn hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for dimension term quotients. -/
theorem dimension_maps_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : dSubgro R K m ⧸ dTSubgro (R := R) (G := K) hmn) :
    (dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (dimensionOntoKer (R := R) φ hφ hmn hkφ hnk).symm
        ((dimensionOntoKer (R := R) ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (termMapsKer hφ hmn hkφ hnk).symm
        ((termMapsKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact term_maps_symm hφ hψ hmn
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for dimension term quotients. -/
theorem dimension_onto_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : dSubgro R K m ⧸ dTSubgro (R := R) (G := K) hmn) :
    (dimensionOntoKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (dimensionOntoKer (R := R) φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((dimensionOntoKer (R := R) ψ hψ hmn hkψ hnk).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (termMapsKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ hmn hkψ hnk).symm z)
  exact term_onto_symm hφ hψ hmn
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise left-depth one-sided formula for dimension transition kernels. -/
theorem dimension_comp_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      dimensionTransitionKer (R := R) ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (dimensionTransitionKer (R := R) φ hφ hmn hkφ hnk x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ hmn hkφ hnk x)
  exact transition_onto_left hφ hψ hmn hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for dimension transition kernels. -/
theorem dimension_comp_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : MonoidHom.ker (mapOfLe (R := R) (G := G) hmn)) :
    dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      dimensionTransitionKer (R := R) ψ hψ hmn hkψ hnk
        (dimensionTransitionKer (R := R) φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      transitionOntoKer hψ hmn hkψ hnk
        (transitionOntoKer hφ hmn hkφ (le_trans hnk hka) x)
  exact transition_onto_comp hφ hψ hmn
    hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for dimension transition kernels. -/
theorem dimension_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (mapOfLe (R := R) (G := K) hmn)) :
    (dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (dimensionTransitionKer (R := R) φ hφ hmn hkφ hnk).symm
        ((dimensionTransitionKer (R := R) ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ hnk).symm
        ((transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact transition_maps_symm hφ hψ hmn
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for dimension transition kernels. -/
theorem dimension_transition_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : MonoidHom.ker (mapOfLe (R := R) (G := K) hmn)) :
    (dimensionTransitionKer (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (dimensionTransitionKer (R := R) φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((dimensionTransitionKer (R := R) ψ hψ hmn
          hkψ hnk).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ hmn hkψ hnk).symm z)
  exact transition_onto_symm hφ hψ hmn
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise left-depth one-sided formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hnk hkb)
        (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ hnk x)
  exact next_comp_left hφ hψ n hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : dSubgro R G n ⧸ dNTerm R G n) :
    dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk
        (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      nextOntoKer hψ n hkψ hnk
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact next_comp_right hφ hψ n hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : dSubgro R K n ⧸ dNTerm R K n) :
    (dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk).symm
        ((dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ hnk).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact next_onto_symm hφ hψ n
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for consecutive dimension quotients. -/
theorem dNQuot.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : dSubgro R K n ⧸ dNTerm R K n) :
    (dNQuot.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (dNQuot.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((dNQuot.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ hnk).symm z)
  exact next_comp_symm hφ hψ n
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {R : Type*} [CommRing R]
open DFilt

/-- Pointwise left-depth one-sided formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : dLKern R G n) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
        (le_trans hnk hkb)
        (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ hnk x)
  exact layer_comp_left hφ hψ n hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : dLKern R G n) :
    dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk
        (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      layerOntoKer hψ n hkψ hnk
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact layer_comp_right hφ hψ n hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ dSubgro R G k)
    (hkψ : ψ.ker ≤ dSubgro R H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : dLKern R K n) :
    (dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ hnk).symm
        ((dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ hnk).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact layer_onto_symm hφ hψ n hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for dimension layer kernels. -/
theorem dLKern.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (dimensionFiltration R G) (dimensionFiltration R H) φ)
    (hψ : MapsOnto (dimensionFiltration R H) (dimensionFiltration R K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ dSubgro R G a)
    (hkψ : ψ.ker ≤ dSubgro R H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : dLKern R K n) :
    (dLKern.equivmaps_ontoker_lele (R := R) (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (dLKern.equivmaps_ontoker_lele (R := R) φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((dLKern.equivmaps_ontoker_lele (R := R) ψ hψ n hkψ hnk).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ hnk).symm z)
  exact layer_comp_symm hφ hψ n hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers
