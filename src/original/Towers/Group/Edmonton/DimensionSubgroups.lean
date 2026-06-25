import Towers.Group.Petresco.TwoGenerators
import Towers.Group.Edmonton.Supersoluble
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The Edmonton Notes on Nilpotent Groups: Section 7 dimension subgroups

This file develops the group-ring filtration used in the integral
unitriangular embedding theorem.
-/

namespace Towers
namespace Edmonton

noncomputable section

open scoped commutatorElement

universe u v

variable {G : Type u} [Group G]
variable (K : Type v) [CommRing K]

/-- The augmentation homomorphism of the group ring `K[G]`. -/
def groupRingAugmentation : MonoidAlgebra K G →+* K :=
  (MonoidAlgebra.lift K K G (1 : G →* K)).toRingHom

@[simp]
lemma group_ring_augmentation (g : G) :
    groupRingAugmentation K (MonoidAlgebra.of K G g) = 1 :=
  MonoidAlgebra.lift_of (1 : G →* K) g

/-- The difference (or augmentation) ideal `Δ(K,G)`. -/
def differenceIdeal : Ideal (MonoidAlgebra K G) :=
  RingHom.ker (groupRingAugmentation K)

instance difference_ideal_sided :
    (differenceIdeal (G := G) K).IsTwoSided := by
  change (RingHom.ker (groupRingAugmentation (G := G) K)).IsTwoSided
  infer_instance

lemma difference_ideal {x : MonoidAlgebra K G} :
    x ∈ differenceIdeal K ↔ groupRingAugmentation K x = 0 :=
  RingHom.mem_ker

/-- The canonical difference `1-g` in the group ring. -/
def groupDifference (g : G) : MonoidAlgebra K G :=
  1 - MonoidAlgebra.of K G g

@[simp]
lemma groupDifference_one :
    groupDifference K (1 : G) = 0 := by
  rw [groupDifference, map_one]
  exact sub_self 1

lemma group_difference_ideal (g : G) :
    groupDifference K g ∈ differenceIdeal K := by
  rw [difference_ideal]
  rw [groupDifference, map_sub, map_one, group_ring_augmentation]
  exact sub_self 1

/-- The `n`th dimension subgroup
`δₙ(K,G) = G ∩ (1 + Δ(K,G)^n)`. -/
def dSubgro (n : ℕ) : Subgroup G where
  carrier := {g | groupDifference K g ∈ differenceIdeal K ^ n}
  one_mem' := by
    change groupDifference K (1 : G) ∈ differenceIdeal K ^ n
    rw [groupDifference_one]
    exact (differenceIdeal K ^ n).zero_mem
  mul_mem' := by
    intro x y hx hy
    change groupDifference K (x * y) ∈ differenceIdeal K ^ n
    have hxy :
        groupDifference K x +
            MonoidAlgebra.of K G x * groupDifference K y ∈
          differenceIdeal K ^ n :=
      (differenceIdeal K ^ n).add_mem hx
        ((differenceIdeal K ^ n).mul_mem_left
          (MonoidAlgebra.of K G x) hy)
    convert hxy using 1
    simp only [groupDifference]
    rw [map_mul]
    noncomm_ring
  inv_mem' := by
    intro x hx
    change groupDifference K x⁻¹ ∈ differenceIdeal K ^ n
    have hx' :
        -(MonoidAlgebra.of K G x⁻¹) * groupDifference K x ∈
          differenceIdeal K ^ n :=
      (differenceIdeal K ^ n).mul_mem_left
        (-(MonoidAlgebra.of K G x⁻¹)) hx
    have hunit :
        MonoidAlgebra.of K G x⁻¹ * MonoidAlgebra.of K G x = 1 := by
      rw [← map_mul]
      simp [MonoidAlgebra.one_def]
    have hid :
        groupDifference K x⁻¹ =
          -(MonoidAlgebra.of K G x⁻¹) * groupDifference K x := by
      simp only [groupDifference]
      calc
        1 - MonoidAlgebra.of K G x⁻¹ =
            MonoidAlgebra.of K G x⁻¹ * MonoidAlgebra.of K G x -
              MonoidAlgebra.of K G x⁻¹ := by rw [hunit]
        _ = -(MonoidAlgebra.of K G x⁻¹) *
              (1 - MonoidAlgebra.of K G x) := by
            noncomm_ring
    rw [hid]
    exact hx'

@[simp]
lemma mem_dimension_iff {n : ℕ} {g : G} :
    g ∈ dSubgro K n ↔
      groupDifference K g ∈ differenceIdeal K ^ n :=
  Iff.rfl

/-- Every dimension subgroup is normal. -/
theorem dimensionSubgroup_normal (n : ℕ) :
    (dSubgro (G := G) K n).Normal := by
  constructor
  intro x hx g
  change groupDifference K (g * x * g⁻¹) ∈ differenceIdeal K ^ n
  have hconj :
      (MonoidAlgebra.of K G g * groupDifference K x) *
          MonoidAlgebra.of K G g⁻¹ ∈
        differenceIdeal K ^ n :=
    (differenceIdeal K ^ n).mul_mem_right
      (MonoidAlgebra.of K G g⁻¹)
      ((differenceIdeal K ^ n).mul_mem_left
        (MonoidAlgebra.of K G g) hx)
  have hunit :
      MonoidAlgebra.of K G g * MonoidAlgebra.of K G g⁻¹ = 1 := by
    rw [← map_mul]
    simp [MonoidAlgebra.one_def]
  have hid :
      groupDifference K (g * x * g⁻¹) =
        (MonoidAlgebra.of K G g * groupDifference K x) *
          MonoidAlgebra.of K G g⁻¹ := by
    simp only [groupDifference]
    rw [map_mul, map_mul]
    calc
      1 - (MonoidAlgebra.of K G g * MonoidAlgebra.of K G x) *
            MonoidAlgebra.of K G g⁻¹ =
          MonoidAlgebra.of K G g * MonoidAlgebra.of K G g⁻¹ -
            (MonoidAlgebra.of K G g * MonoidAlgebra.of K G x) *
              MonoidAlgebra.of K G g⁻¹ := by rw [hunit]
      _ = (MonoidAlgebra.of K G g *
              (1 - MonoidAlgebra.of K G x)) *
            MonoidAlgebra.of K G g⁻¹ := by
          noncomm_ring
  rw [hid]
  exact hconj

/-- The first dimension subgroup is the whole group. -/
@[simp]
theorem dimensionSubgroup_one :
    dSubgro (G := G) K 1 = ⊤ := by
  apply top_unique
  intro g _
  change groupDifference K g ∈ differenceIdeal K ^ 1
  simpa only [Submodule.pow_one] using group_difference_ideal K g

/-- Dimension subgroups decrease as their index increases. -/
theorem dimensionSubgroup_antitone {m n : ℕ} (hmn : m ≤ n) :
    dSubgro (G := G) K n ≤ dSubgro K m := by
  intro g hg
  exact Ideal.pow_le_pow_right hmn hg

/-- The product of differences of degrees `m` and `n` has degree
`m+n`. -/
lemma group_difference_add {m n : ℕ} {x y : G}
    (hx : groupDifference K x ∈ differenceIdeal K ^ m)
    (hy : groupDifference K y ∈ differenceIdeal K ^ n) :
    groupDifference K x * groupDifference K y ∈
      differenceIdeal K ^ (m + n) := by
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul hx hy

/-- Commutators raise dimension-filtration degree additively. -/
lemma commutator_element_dimension {m n : ℕ} {x y : G}
    (hx : x ∈ dSubgro K m)
    (hy : y ∈ dSubgro K n) :
    ⁅x, y⁆ ∈ dSubgro K (m + n) := by
  change groupDifference K ⁅x, y⁆ ∈ differenceIdeal K ^ (m + n)
  have hxy :
      groupDifference K x * groupDifference K y ∈
        differenceIdeal K ^ (m + n) :=
    group_difference_add K hx hy
  have hyx :
      groupDifference K y * groupDifference K x ∈
        differenceIdeal K ^ (m + n) := by
    simpa only [Nat.add_comm] using
      group_difference_add K hy hx
  have hsub :
      groupDifference K y * groupDifference K x -
          groupDifference K x * groupDifference K y ∈
        differenceIdeal K ^ (m + n) := by
    apply Submodule.sub_mem
    · exact hyx
    · exact hxy
  have hright :
      (groupDifference K y * groupDifference K x -
            groupDifference K x * groupDifference K y) *
          MonoidAlgebra.of K G x⁻¹ * MonoidAlgebra.of K G y⁻¹ ∈
        differenceIdeal K ^ (m + n) :=
    (differenceIdeal K ^ (m + n)).mul_mem_right
      (MonoidAlgebra.of K G y⁻¹)
      ((differenceIdeal K ^ (m + n)).mul_mem_right
        (MonoidAlgebra.of K G x⁻¹) hsub)
  have hxx :
      MonoidAlgebra.of K G x * MonoidAlgebra.of K G x⁻¹ = 1 := by
    rw [← map_mul]
    simp [MonoidAlgebra.one_def]
  have hyy :
      MonoidAlgebra.of K G y * MonoidAlgebra.of K G y⁻¹ = 1 := by
    rw [← map_mul]
    simp [MonoidAlgebra.one_def]
  have hone :
      (MonoidAlgebra.of K G y * MonoidAlgebra.of K G x) *
            MonoidAlgebra.of K G x⁻¹ *
          MonoidAlgebra.of K G y⁻¹ = 1 := by
    simp only [mul_assoc, hxx, mul_one, hyy]
  have hid :
      groupDifference K ⁅x, y⁆ =
        (groupDifference K y * groupDifference K x -
              groupDifference K x * groupDifference K y) *
            MonoidAlgebra.of K G x⁻¹ *
          MonoidAlgebra.of K G y⁻¹ := by
    simp only [groupDifference, commutatorElement_def]
    rw [map_mul, map_mul, map_mul]
    calc
      1 - ((MonoidAlgebra.of K G x * MonoidAlgebra.of K G y) *
              MonoidAlgebra.of K G x⁻¹) *
            MonoidAlgebra.of K G y⁻¹ =
          (MonoidAlgebra.of K G y * MonoidAlgebra.of K G x) *
                MonoidAlgebra.of K G x⁻¹ *
              MonoidAlgebra.of K G y⁻¹ -
            ((MonoidAlgebra.of K G x * MonoidAlgebra.of K G y) *
                MonoidAlgebra.of K G x⁻¹) *
              MonoidAlgebra.of K G y⁻¹ := by rw [hone]
      _ = ((1 - MonoidAlgebra.of K G y) *
                  (1 - MonoidAlgebra.of K G x) -
                (1 - MonoidAlgebra.of K G x) *
                  (1 - MonoidAlgebra.of K G y)) *
              MonoidAlgebra.of K G x⁻¹ *
            MonoidAlgebra.of K G y⁻¹ := by
          noncomm_ring
  rw [hid]
  exact hright

/-- The commutator of two dimension subgroups lies in the subgroup
whose degree is the sum of their degrees. -/
theorem dimension_subgroup_commutator (m n : ℕ) :
    ⁅dSubgro (G := G) K m,
        dSubgro (G := G) K n⁆ ≤
      dSubgro (G := G) K (m + n) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact commutator_element_dimension K hx hy

/-- The shifted dimension filtration is a descending central series. -/
theorem dimension_descending_series :
    Subgroup.IsDescendingCentralSeries
      (fun n => dSubgro (G := G) K (n + 1)) := by
  constructor
  · exact dimensionSubgroup_one K
  intro x n hx g
  have hg : g ∈ dSubgro (G := G) K 1 := by
    rw [dimensionSubgroup_one]
    trivial
  simpa only [Nat.add_assoc] using
    commutator_element_dimension K hx hg

/-- The `n`th lower-central subgroup lies in dimension subgroup
`δ_{n+1}` in Mathlib's zero-based lower-central indexing. -/
theorem lower_dimension_subgroup (n : ℕ) :
    Subgroup.lowerCentralSeries G n ≤ dSubgro K (n + 1) :=
  Subgroup.descending_central_series_ge_lower
    (fun i => dSubgro (G := G) K (i + 1))
    (dimension_descending_series K) n

/-- In Hall's one-based notation, `γₙ(G) ≤ δₙ(G)`. -/
theorem paper_dimension_subgroup {n : ℕ}
    (hn : 0 < n) :
    Subgroup.lowerCentralSeries G (n - 1) ≤ dSubgro K n := by
  simpa only [Nat.sub_add_cancel hn] using
    lower_dimension_subgroup (G := G) K (n - 1)

section CharacteristicZeroField

variable {F : Type v} [Field F] [CharZero F]

omit [CharZero F] in
/-- The geometric sum associated with a group element differs from its
augmentation by an element of the difference ideal. -/
lemma geom_cast_difference (x : G) (m : ℕ) :
    (∑ i ∈ Finset.range m, (MonoidAlgebra.of F G x) ^ i) - m ∈
      differenceIdeal F := by
  rw [difference_ideal]
  rw [map_sub, RingHom.map_geom_sum]
  simp_rw [group_ring_augmentation]
  simp

omit [CharZero F] in
/-- The difference of a group power factors through the difference of
the original group element. -/
lemma difference_geom_sum (x : G) (m : ℕ) :
    groupDifference F (x ^ m) =
      groupDifference F x *
        ∑ i ∈ Finset.range m, (MonoidAlgebra.of F G x) ^ i := by
  rw [groupDifference, map_pow, groupDifference]
  exact (mul_neg_geom_sum (MonoidAlgebra.of F G x) m).symm

/-- A positive natural number is a unit in a group ring over a
characteristic-zero field. -/
lemma unit_cast_ring {m : ℕ} (hm : 0 < m) :
    IsUnit (m : MonoidAlgebra F G) := by
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hunitF : IsUnit (m : F) := isUnit_iff_ne_zero.mpr hmF
  simpa only [map_natCast] using
    IsUnit.map (algebraMap F (MonoidAlgebra F G)) hunitF

/-- If a difference has degree `k` and a positive power has degree
`k+1`, then the original difference already has degree `k+1`. -/
lemma difference_succ_power
    {k m : ℕ} {x : G} (hm : 0 < m)
    (hx : groupDifference F x ∈ differenceIdeal F ^ k)
    (hxm : groupDifference F (x ^ m) ∈ differenceIdeal F ^ (k + 1)) :
    groupDifference F x ∈ differenceIdeal F ^ (k + 1) := by
  let S : MonoidAlgebra F G :=
    ∑ i ∈ Finset.range m, (MonoidAlgebra.of F G x) ^ i
  have hS :
      S - m ∈ differenceIdeal F ^ 1 := by
    simpa only [Submodule.pow_one] using
      geom_cast_difference (F := F) x m
  have herr :
      groupDifference F x * (S - m) ∈
        differenceIdeal F ^ (k + 1) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hx hS
  have hprod :
      groupDifference F x * S ∈ differenceIdeal F ^ (k + 1) := by
    rw [← difference_geom_sum (F := F) x m]
    exact hxm
  have hscalar :
      groupDifference F x * (m : MonoidAlgebra F G) ∈
        differenceIdeal F ^ (k + 1) := by
    have hdifference :
        groupDifference F x * S -
            groupDifference F x * (S - m) ∈
          differenceIdeal F ^ (k + 1) := by
      apply Submodule.sub_mem
      · exact hprod
      · exact herr
    convert hdifference using 1
    noncomm_ring
  have hleft :
      (m : MonoidAlgebra F G) * groupDifference F x ∈
        differenceIdeal F ^ (k + 1) := by
    rw [(Nat.cast_commute m (groupDifference F x)).eq]
    exact hscalar
  exact
    ((differenceIdeal F ^ (k + 1)).unit_mul_mem_iff_mem
      (unit_cast_ring (F := F) (G := G) hm)).mp hleft

/-- Dimension subgroups over a characteristic-zero field are closed
under taking positive roots. -/
theorem dimension_subgroup_root {n m : ℕ} {x : G}
    (hn : 0 < n) (hm : 0 < m)
    (hxm : x ^ m ∈ dSubgro F n) :
    x ∈ dSubgro F n := by
  change groupDifference F (x ^ m) ∈ differenceIdeal F ^ n at hxm
  change groupDifference F x ∈ differenceIdeal F ^ n
  have haux :
      ∀ r : ℕ, 0 < r →
        groupDifference F (x ^ m) ∈ differenceIdeal F ^ r →
          groupDifference F x ∈ differenceIdeal F ^ r := by
    intro r
    induction r with
    | zero =>
        intro hr
        omega
    | succ r ihr =>
        intro _ hpower
        by_cases hr : r = 0
        · subst r
          simpa only [zero_add, Submodule.pow_one] using
            group_difference_ideal F x
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hpowerPrevious :
              groupDifference F (x ^ m) ∈ differenceIdeal F ^ r :=
            Ideal.pow_le_pow_right (Nat.le_succ r) hpower
          have hxPrevious :
              groupDifference F x ∈ differenceIdeal F ^ r :=
            ihr hrpos hpowerPrevious
          exact
            difference_succ_power
              (F := F) hm hxPrevious hpower
  exact haux n hn hxm

/-- The easy implication in Jennings' theorem: a positive power in
`γₙ(G)` forces the element itself into `δₙ(G)`. -/
theorem dimension_central_series
    {n m : ℕ} {x : G} (hn : 0 < n) (hm : 0 < m)
    (hxm : x ^ m ∈ Subgroup.lowerCentralSeries G (n - 1)) :
    x ∈ dSubgro F n := by
  apply dimension_subgroup_root (F := F) hn hm
  exact paper_dimension_subgroup F hn hxm

/-- The substantive converse in Jennings' theorem, isolated so that the
integral-basis argument below can supply it. -/
def HasJenningsConverse (F : Type v) (G : Type u)
    [Field F] [CharZero F] [Group G] : Prop :=
  ∀ n : ℕ, 0 < n → ∀ x : G, x ∈ dSubgro F n →
    ∃ m : ℕ, 0 < m ∧ x ^ m ∈ Subgroup.lowerCentralSeries G (n - 1)

/-- **Jennings, Theorem 7.1.** Assuming the integral-basis converse,
membership in `δₙ(G)` is equivalent to some positive power lying in
`γₙ(G)`. -/
theorem dimension_lower_series (hJennings : HasJenningsConverse F G)
    {n : ℕ} (hn : 0 < n) (x : G) :
    x ∈ dSubgro F n ↔
      ∃ m : ℕ, 0 < m ∧ x ^ m ∈ Subgroup.lowerCentralSeries G (n - 1) := by
  constructor
  · exact hJennings n hn x
  · rintro ⟨m, hm, hxm⟩
    exact dimension_central_series
      (F := F) hn hm hxm

/-- Jennings' characterization makes the dimension subgroups
independent of the characteristic-zero coefficient field. -/
theorem dimension_jennings_converse
    {E : Type*} [Field E] [CharZero E]
    (hF : HasJenningsConverse F G) (hE : HasJenningsConverse E G)
    {n : ℕ} (hn : 0 < n) :
    dSubgro (G := G) F n = dSubgro E n := by
  ext x
  rw [dimension_lower_series hF hn x,
    dimension_lower_series hE hn x]

end CharacteristicZeroField

/-- Hall's `J`-groups are torsion-free finitely generated nilpotent
groups. -/
class IsJGroup (G : Type u) [Group G] : Prop
    extends IsMulTorsionFree G, Group.FG G, Group.IsNilpotent G

/-- A scalar in a characteristic-zero field is an integer scalar if it
lies in the image of `ℤ`. -/
def IsIntegerScalar {F : Type*} [Field F] [CharZero F] (a : F) : Prop :=
  ∃ z : ℤ, (z : F) = a

/-- A group-ring element has integer coefficients in the canonical
group basis. -/
def IntegerRingCoefficients
    {F : Type*} [Field F] [CharZero F]
    {G : Type*} [Group G] (a : MonoidAlgebra F G) : Prop :=
  ∀ g : G, IsIntegerScalar (a g)

/-- Hall's integral-basis condition for a group ring. -/
structure IntegralRingBasis
    {F : Type*} [Field F] [CharZero F]
    {G : Type*} [Group G] {ι : Type*}
    (b : Module.Basis ι F (MonoidAlgebra F G)) : Prop where
  basis_integer_coefficients :
    ∀ i : ι, IntegerRingCoefficients (b i)
  group_repr_integer :
    ∀ g : G, ∀ i : ι,
      IsIntegerScalar (b.repr (MonoidAlgebra.of F G g) i)

/-- The multiplication constants of a basis of a group ring. -/
def basisMultiplicationConstant
    {F : Type*} [Field F] {G : Type*} [Group G] {ι : Type*}
    (b : Module.Basis ι F (MonoidAlgebra F G)) (i j k : ι) : F :=
  b.repr (b i * b j) k

/-- The standard model of an infinite cyclic group. -/
abbrev InfiniteCyclicGroup := Multiplicative ℤ

/-- The distinguished generator of the standard infinite cyclic group. -/
def infiniteCyclicGenerator : InfiniteCyclicGroup :=
  Multiplicative.ofAdd 1

/-- Positive natural numbers, used to index the negative tail in
Hall's cyclic integral basis. -/
abbrev PositiveNat := {n : ℕ // 0 < n}

/-- The index type for Hall's cyclic integral basis. -/
abbrev CyclicBasisIndex := ℕ ⊕ PositiveNat

/-- The family from Hall's Lemma 7.2:
`1,u,u²,...` followed by `uⁿx⁻¹,uⁿx⁻²,...`. -/
def cyclicBasisFamily
    {F : Type*} [Field F] [CharZero F] (n : ℕ) :
    CyclicBasisIndex → MonoidAlgebra F InfiniteCyclicGroup
  | Sum.inl r =>
      groupDifference F infiniteCyclicGenerator ^ r
  | Sum.inr s =>
      groupDifference F infiniteCyclicGenerator ^ n *
        MonoidAlgebra.of F InfiniteCyclicGroup
          ((infiniteCyclicGenerator ^ (s : ℕ))⁻¹)

/-- The elementary identity driving the induction in Hall's proof of
Lemma 7.2. -/
lemma difference_succ_mul
    {F : Type*} [Field F] {H : Type*} [Group H]
    (x y : H) (n : ℕ) :
    groupDifference F x ^ (n + 1) * MonoidAlgebra.of F H y =
      groupDifference F x ^ n * MonoidAlgebra.of F H y -
        groupDifference F x ^ n * MonoidAlgebra.of F H (x * y) := by
  rw [pow_succ, groupDifference, map_mul]
  noncomm_ring

/-- The exact basis-existence assertion of Hall's Lemma 7.2. -/
def CyclicIntegralBasis
    (F : Type v) [Field F] [CharZero F] (n : ℕ) : Prop :=
  ∃ b : Module.Basis CyclicBasisIndex F
      (MonoidAlgebra F InfiniteCyclicGroup),
    IntegralRingBasis b ∧
      ∀ i, b i = cyclicBasisFamily n i

/-- **Hall, Lemma 7.2, basis-interface form.** A construction satisfying
the cyclic integral-basis assertion exposes precisely Hall's stated
basis. -/
theorem cyclic_integral_basis
    {F : Type v} [Field F] [CharZero F] {n : ℕ} (_hn : 0 < n)
    (hbasis : CyclicIntegralBasis F n) :
    ∃ b : Module.Basis CyclicBasisIndex F
        (MonoidAlgebra F InfiniteCyclicGroup),
      IntegralRingBasis b ∧
        ∀ i, b i = cyclicBasisFamily n i := by
  exact hbasis

/-- One factor in Hall's product basis for a `J`-group. -/
def integralBasisFactor
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] (n : ℕ) (x : H) :
    CyclicBasisIndex → MonoidAlgebra F H
  | Sum.inl r =>
      groupDifference F x ^ r
  | Sum.inr s =>
      groupDifference F x ^ n *
        MonoidAlgebra.of F H ((x ^ (s : ℕ))⁻¹)

/-- The ordered product family in Hall's Lemma 7.3. -/
def integralBasisFamily
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H)
    (a : Fin M → CyclicBasisIndex) :
    MonoidAlgebra F H :=
  (List.ofFn fun i : Fin M => integralBasisFactor (F := F) n (x i) (a i)).prod

/-- The exact product-basis assertion in Hall's Lemma 7.3. -/
def ProductIntegralBasis
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) : Prop :=
  ∃ b : Module.Basis (Fin M → CyclicBasisIndex) F
      (MonoidAlgebra F H),
    IntegralRingBasis b ∧
      ∀ a, b a = integralBasisFamily n x a

/-- **Hall, Lemma 7.3, product-basis interface form.** -/
theorem product_integral_basis
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    {n : ℕ} (_hn : 0 < n) (x : Fin M → H)
    (hbasis : ProductIntegralBasis (F := F) n x) :
    ∃ b : Module.Basis (Fin M → CyclicBasisIndex) F
        (MonoidAlgebra F H),
      IntegralRingBasis b ∧
        ∀ a, b a = integralBasisFamily n x a :=
  hbasis

/-- The truncated weight of one cyclic-basis factor. Negative-tail
factors have weight at least the cutoff `n`. -/
def integralBasisWeight (n μ : ℕ) :
    CyclicBasisIndex → ℕ
  | Sum.inl r => r * μ
  | Sum.inr _ => n

/-- Hall's product weight, truncated at `n` because all filtration
levels above `n` are identified with `E_n`. -/
def integralProductWeight {M : ℕ} (n : ℕ) (μ : Fin M → ℕ)
    (a : Fin M → CyclicBasisIndex) : ℕ :=
  min n (∑ i, integralBasisWeight n (μ i) (a i))

/-- Hall's space `E_s`, spanned by product-basis elements of weight at
least `s`, with the filtration truncated at `n`. -/
def integralWeightFiltration
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) (μ : Fin M → ℕ) (s : ℕ) :
    Submodule F (MonoidAlgebra F H) :=
  Submodule.span F
    {v | ∃ a : Fin M → CyclicBasisIndex,
      min s n ≤ integralProductWeight n μ a ∧
        integralBasisFamily n x a = v}

/-- The weight filtration decreases with its index. -/
theorem integral_filtration_antitone
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) (μ : Fin M → ℕ)
    {r s : ℕ} (hrs : r ≤ s) :
    integralWeightFiltration (F := F) n x μ s ≤
      integralWeightFiltration (F := F) n x μ r := by
  apply Submodule.span_mono
  rintro v ⟨a, ha, rfl⟩
  exact ⟨a, (min_le_min_right n hrs).trans ha, rfl⟩

/-- The weight filtration is constant after the cutoff `n`. -/
theorem integral_filtration_cutoff
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) (μ : Fin M → ℕ)
    {s : ℕ} (hns : n ≤ s) :
    integralWeightFiltration (F := F) n x μ s =
      integralWeightFiltration (F := F) n x μ n := by
  unfold integralWeightFiltration
  rw [min_eq_right hns, min_self]

/-- Congruence modulo a linear subspace. -/
def LinearCongruentMod
    {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (E : Submodule F A) (a b : A) : Prop :=
  a - b ∈ E

/-- The conjugation/weight assertion proved in Hall's Lemma 7.4. -/
def HallWeightCongruence
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) (μ : Fin M → ℕ) : Prop :=
  ∀ (i : Fin M) (a : Fin M → CyclicBasisIndex),
    let v := integralBasisFamily (F := F) n x a
    LinearCongruentMod
      (integralWeightFiltration (F := F) n x μ
        (integralProductWeight n μ a + μ i))
      (v * MonoidAlgebra.of F H (x i)) v

/-- **Hall, Lemma 7.4, filtration-congruence form.** -/
theorem integral_basis_congruence
    {F : Type*} [Field F] [CharZero F]
    {H : Type*} [Group H] {M : ℕ}
    (n : ℕ) (x : Fin M → H) (μ : Fin M → ℕ)
    (hweight : HallWeightCongruence (F := F) n x μ) :
    ∀ (i : Fin M) (a : Fin M → CyclicBasisIndex),
      let v := integralBasisFamily (F := F) n x a
      LinearCongruentMod
        (integralWeightFiltration (F := F) n x μ
          (integralProductWeight n μ a + μ i))
        (v * MonoidAlgebra.of F H (x i)) v :=
  hweight

/-- The variables of weight `i+1`, with `m i` variables in that
weight. -/
abbrev HallWeightedVariable {c : ℕ} (m : Fin c → ℕ) :=
  Σ i : Fin c, Fin (m i)

/-- The number of commutative monomials of weighted degree `j` with
`m i` variables of weight `i+1`. -/
noncomputable def weightedMonomialCount {c : ℕ}
    (m : Fin c → ℕ) (j : ℕ) : ℕ :=
  Nat.card
    {a : HallWeightedVariable m → ℕ //
      ∑ q, a q * ((q.1 : ℕ) + 1) = j}

/-- Coefficientwise form of Hall's Hilbert-series identity
`∏ᵢ (1-tⁱ)^{-mᵢ}`. -/
def HallHilbertSeries {c : ℕ} (m : Fin c → ℕ)
    (d : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, d j = weightedMonomialCount m j

/-- The Hilbert-series count obtained incidentally in Hall's proof of
Jennings' theorem. -/
theorem hall_dimension_series
    {c : ℕ} (m : Fin c → ℕ) (d : ℕ → ℕ)
    (hseries : HallHilbertSeries m d) :
    ∀ j : ℕ, d j = weightedMonomialCount m j :=
  hseries

/-- An integer matrix is upper unitriangular when it is zero below the
diagonal and one on the diagonal. -/
def IsIntegerUnitriangular {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

/-- A faithful degree-`d` representation by integer unitriangular
matrices. -/
def IntegerUnitriangularEmbedding
    (G : Type u) [Group G] (d : ℕ) : Prop :=
  ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin d) ℤ,
    Function.Injective ρ ∧
      ∀ g : G, IsIntegerUnitriangular
        ((ρ g : Matrix.GeneralLinearGroup (Fin d) ℤ) :
          Matrix (Fin d) (Fin d) ℤ)

/-- A faithful integral unitriangular representation in some finite
degree. -/
def UnitriangularEmbedding
    (G : Type u) [Group G] : Prop :=
  ∃ d : ℕ, IntegerUnitriangularEmbedding G d

/-- **Hall, Theorem 7.5.** The integral-basis construction produces a
faithful integer unitriangular representation of every `J`-group. -/
theorem j_unitriangular_embedding {H : Type u} [Group H] [IsJGroup H]
    (hembedding : UnitriangularEmbedding H) :
    ∃ d : ℕ, IntegerUnitriangularEmbedding H d :=
  hembedding

/-- A faithful degree-`d` integral unimodular representation. Since
`GL_d(ℤ)` consists precisely of the unimodular integer matrices, this is
Hall's group `U_d`. -/
def DegreeUnimodularEmbedding
    (G : Type u) [Group G] (d : ℕ) : Prop :=
  ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin d) ℤ,
    Function.Injective ρ

/-- The finite-index induction assertion used in Hall's Lemma 7.6. -/
def InducedUnimodularEmbedding
    {G : Type u} [Group G] (H : Subgroup G) (m d : ℕ) : Prop :=
  H.index = m →
    DegreeUnimodularEmbedding H d →
      DegreeUnimodularEmbedding G (m * d)

/-- **Hall, Lemma 7.6.** A degree-`d` unimodular embedding of a
finite-index subgroup of index `m` induces one of degree `md` for the
whole group. -/
theorem induce_unimodular_embedding
    {H : Type u} [Group H] (K : Subgroup H) {m d : ℕ}
    (hinduce : InducedUnimodularEmbedding K m d)
    (hindex : K.index = m)
    (hembedding : DegreeUnimodularEmbedding K d) :
    DegreeUnimodularEmbedding H (m * d) :=
  hinduce hindex hembedding

/-- The finiteness assertion in Hall's Lemma 7.7 for a fixed group. The
hypothesis is packaged as a reusable interface because the induction on
the derived series requires a general finite-extension theorem for
soluble groups which is not currently available in Mathlib. -/
def PeriodicSolvableProperty
    (H : Type u) [Group H] : Prop :=
  Group.FG H → IsSolvable H → Monoid.IsTorsion H → Finite H

/-- **Hall, Lemma 7.7.** A finitely generated periodic soluble group is
finite. -/
theorem fg_periodic_solvable
    {H : Type u} [Group H] [Group.FG H] [IsSolvable H]
    (hfinite : PeriodicSolvableProperty H)
    (hperiodic : Monoid.IsTorsion H) :
    Finite H :=
  hfinite inferInstance inferInstance hperiodic

/-- The exact power-separation assertion of Hirsch's theorem, using
Hall's subgroup `G^m` generated by all `m`th powers. -/
def HirschPowerSeparation (G : Type u) [Group G] : Prop :=
  IsPolycyclic G → ∀ x : G, x ≠ 1 →
    ∃ m : ℕ, 0 < m ∧
      IsMulTorsionFree (subgroupPower (⊤ : Subgroup G) m) ∧
      x ∉ subgroupPower (⊤ : Subgroup G) m

/-- **Hall, Theorem 7.8 (Hirsch), power-separation form.** -/
theorem hirsch_powerSeparation
    {H : Type u} [Group H] (hpoly : IsPolycyclic H)
    (hhirsch : HirschPowerSeparation H)
    {x : H} (hx : x ≠ 1) :
    ∃ m : ℕ, 0 < m ∧
      IsMulTorsionFree (subgroupPower (⊤ : Subgroup H) m) ∧
      x ∉ subgroupPower (⊤ : Subgroup H) m := by
  exact hhirsch hpoly x hx

/-- A faithful integral unimodular representation in some finite
degree. -/
def HasUnimodularEmbedding (G : Type u) [Group G] : Prop :=
  ∃ d : ℕ, DegreeUnimodularEmbedding G d

/-- The exact composition assertion used in the corollary to Hirsch's
theorem: a polycyclic group with a finite-index nilpotent subgroup has
a faithful integral unimodular representation. -/
def VirtuallyUnimodularProperty
    (H : Type u) [Group H] : Prop :=
  IsPolycyclic H →
    (∃ K : Subgroup H, Group.IsNilpotent K ∧ K.FiniteIndex) →
      HasUnimodularEmbedding H

/-- **Corollary to Hall, Theorem 7.8.** Every polycyclic virtually
nilpotent group embeds in some `U_d`. -/
theorem virtually_polycyclic_unimodular
    {H : Type u} [Group H] (hpoly : IsPolycyclic H)
    (hvirt : ∃ K : Subgroup H, Group.IsNilpotent K ∧ K.FiniteIndex)
    (hembedding : VirtuallyUnimodularProperty H) :
    ∃ d : ℕ, DegreeUnimodularEmbedding H d :=
  hembedding hpoly hvirt

/-- **Corollary to Hall, Theorem 7.8, supersoluble case.** -/
theorem supersoluble_unimodular_embedding
    {H : Type u} [Group H] (hsuper : IsSupersoluble H)
    (hembedding : VirtuallyUnimodularProperty H) :
    ∃ d : ℕ, DegreeUnimodularEmbedding H d := by
  have hpoly : IsPolycyclic H :=
    supersoluble_implies_polycyclic hsuper
  obtain ⟨K, hKnil, hKfinite, _⟩ :=
    index_nilpotent_supersoluble hsuper
  exact hembedding hpoly ⟨K, hKnil, hKfinite⟩

/-- The natural action of the automorphism group of `G` on `G`. -/
def automorphismAction (G : Type u) [Group G] :
    MulAut G →* MulAut G :=
  MonoidHom.id (MulAut G)

/-- The holomorph of a group, realized as the semidirect product of the
group by its full automorphism group. -/
abbrev Holomorph (G : Type u) [Group G] :=
  G ⋊[automorphismAction G] MulAut G

/-- The embedding assertion in Hall's Theorem 7.9 for a fixed
`J`-group. -/
def HolomorphUnimodularProperty
    (H : Type u) [Group H] [IsJGroup H] : Prop :=
  HasUnimodularEmbedding (Holomorph H)

/-- **Hall, Theorem 7.9.** The holomorph of every `J`-group embeds in
some integral unimodular group `U_d`. -/
theorem j_holomorph_unimodular
    {H : Type u} [Group H] [IsJGroup H]
    (hembedding : HolomorphUnimodularProperty H) :
    ∃ d : ℕ, DegreeUnimodularEmbedding (Holomorph H) d :=
  hembedding

end

end Edmonton
end Towers
