import Submission.Group.NilpotentProducts.OrderNine
import Submission.Group.NilpotentProducts.OddSpecializations
import Submission.Group.NilpotentProducts.MagnusUniqueness
import Submission.Group.NilpotentProducts.TripleCommutators
import Submission.Group.PowerWidth.FiniteWidthTopology

open scoped IsMulCommutative


/-!
# Struik's Corollary 2

This file compares the free exponent-three Burnside group with the first
two nilpotent products of cyclic groups of order three.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton

universe u

/-- A group has exponent dividing three when every element has trivial
cube. -/
def HasExponentThree (G : Type u) [Group G] : Prop :=
  ∀ x : G, x ^ 3 = 1

private theorem inv_sq_exponent
    {G : Type u} [Group G]
    (hG : HasExponentThree G) (x : G) :
    x⁻¹ = x ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  simpa [pow_succ] using hG x

private theorem inv_exponent_three
    {G : Type u} [Group G]
    (hG : HasExponentThree G) (x : G) :
    x⁻¹ * x⁻¹ = x := by
  have h := inv_sq_exponent hG x⁻¹
  simpa [pow_two] using h.symm

/-- In an exponent-three group, `xyx` is the inverse of `yxy`. -/
private theorem sandwich_exponent_three
    {G : Type u} [Group G]
    (hG : HasExponentThree G) (x y : G) :
    x * y * x = y⁻¹ * x⁻¹ * y⁻¹ := by
  have hpow := hG (x * y)
  have hproduct :
      (x * y * x) * (y * x * y) = 1 := by
    calc
      (x * y * x) * (y * x * y) = (x * y) ^ 3 := by
        simp [pow_succ]
        group
      _ = 1 := hpow
  calc
    x * y * x = (y * x * y)⁻¹ :=
      eq_inv_of_mul_eq_one_left hproduct
    _ = y⁻¹ * x⁻¹ * y⁻¹ := by group

/-- Every exponent-three group satisfies the repeated-variable
two-Engel identity used in Corollary 2. -/
theorem triple_self_three
    {G : Type u} [Group G]
    (hG : HasExponentThree G) (a b : G) :
    hallTripleCommutator a b a = 1 := by
  rw [hallTripleCommutator,
    commute_paper_1960]
  change hallCommutator a b * a = a * hallCommutator a b
  calc
    hallCommutator a b * a =
        a⁻¹ * b⁻¹ * (a * b * a) := by
      simp only [hallCommutator]
      group
    _ = a⁻¹ * b⁻¹ * (b⁻¹ * a⁻¹ * b⁻¹) := by
      rw [sandwich_exponent_three hG a b]
    _ = a⁻¹ * (b⁻¹ * b⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a⁻¹ * b * a⁻¹ * b⁻¹ := by
      rw [inv_exponent_three hG b]
    _ = (b⁻¹ * a * b⁻¹) * b⁻¹ := by
      rw [sandwich_exponent_three hG a⁻¹ b]
      simp
    _ = b⁻¹ * a * (b⁻¹ * b⁻¹) := by group
    _ = b⁻¹ * a * b := by
      rw [inv_exponent_three hG b]
    _ = a * hallCommutator a b := by
      simp only [hallCommutator]
      group

/-- The constant family of cyclic orders three. -/
def orderThreeFamily {t : ℕ} (_ : Fin t) : ℕ := 3

theorem order_family_odd {t : ℕ} :
    ∀ i, Odd (orderThreeFamily (t := t) i) := by
  intro i
  norm_num [orderThreeFamily]

theorem order_family_admissible {t : ℕ} :
    ∀ i, AOrd (orderThreeFamily (t := t) i) :=
  fun i => AOrd.of_odd (order_family_odd i)

theorem order_family_tame {t : ℕ} :
    TameOrdersCutoff (orderThreeFamily (t := t)) 3 := by
  intro i
  right
  intro p hp hpdvd
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (by simpa [orderThreeFamily] using hpdvd)
  omega

/-- The first nilpotent product of two cyclic groups of order three has
the expected three Hall coordinates and hence order `3³ = 27`. -/
theorem order_nilpotent_card :
    Nat.card
        (NilpotentCyclicProduct
          (orderThreeFamily (t := 2)) 3) =
      27 := by
  let hCoordinateKernel :
      (Function.Bijective
          (generalResidueEval.{0} (orderThreeFamily (t := 2)) 3)) :=
    statement_tame_orders
      (orderThreeFamily (t := 2)) (by omega)
        order_family_tame
  rw [nilpotent_cyclic_card
    (orderThreeFamily (t := 2)) 3 hCoordinateKernel]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  simp only [general_standard_order]
  change
    (∏ i : (standardHallFamily.{0} 2 1).index,
        standardFactorOrder (orderThreeFamily (t := 2)) i) *
      (∏ i : (standardHallFamily.{0} 2 2).index,
        standardFactorOrder (orderThreeFamily (t := 2)) i) =
      27
  rw [← (lowWeightIndex.{0} 2).prod_comp
      (fun i => standardFactorOrder
        (orderThreeFamily (t := 2)) i),
    ← (lowTwoIndex.{0} 2).prod_comp
      (fun i => standardFactorOrder
        (orderThreeFamily (t := 2)) i)]
  norm_num [standard_order_low,
    standard_low_two,
    lowPairOrder, orderThreeFamily]
  have hpair :
      Fintype.card (LowPairIndex.{0} 2) = 1 := by
    calc
      Fintype.card (LowPairIndex.{0} 2) =
          Fintype.card (Pair 2) :=
        Fintype.card_congr (lowPairRank.{0} 2)
      _ = Fintype.card (Set.powersetCard (Fin 2) 2) :=
        Fintype.card_congr (pairPowersetEquiv 2)
      _ = 1 := by
        simpa using
          (Set.powersetCard.card (α := Fin 2) (n := 2))
  rw [hpair]
  norm_num

/-- The first two indices, viewed as an equation-(29) pair. -/
def pairTwo {t : ℕ} (ht : 2 ≤ t) :
    Pair t :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
    by norm_num⟩

/-- The first three indices, viewed as an equation-(29) triple. -/
def tripleThree {t : ℕ} (ht : 3 ≤ t) :
    Triple t :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
    by norm_num, by norm_num⟩

/-- The free Burnside group of exponent three on `t` generators. -/
abbrev FreeBurnsideThree (t : ℕ) :=
  FreeGroup (Fin t) ⧸ powerSubgroup (FreeGroup (Fin t)) 3

/-- The canonical generators of the free exponent-three Burnside group. -/
def freeBurnsideGenerator {t : ℕ} (i : Fin t) :
    FreeBurnsideThree t :=
  QuotientGroup.mk' (powerSubgroup (FreeGroup (Fin t)) 3)
    (FreeGroup.of i)

/-- The canonical Burnside generators generate the whole quotient. -/
theorem closure_burnside_top (t : ℕ) :
    Subgroup.closure
        (Set.range (freeBurnsideGenerator (t := t))) =
      (⊤ : Subgroup (FreeBurnsideThree t)) := by
  let q :=
    QuotientGroup.mk'
      (powerSubgroup (FreeGroup (Fin t)) 3)
  have hgenerator :
      freeBurnsideGenerator (t := t) =
        q ∘ FreeGroup.of := rfl
  rw [hgenerator, Set.range_comp,
    ← MonoidHom.map_closure q,
    FreeGroup.closure_range_of,
    ← MonoidHom.range_eq_map]
  exact
    MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective
        (powerSubgroup (FreeGroup (Fin t)) 3))

theorem free_burnside_exponent (t : ℕ) :
    HasExponentThree (FreeBurnsideThree t) :=
  power_pow_one (FreeGroup (Fin t)) 3

/-- Any assignment of the free generators into an exponent-three group
extends to the free Burnside group. -/
noncomputable def freeBurnsideLift
    {t : ℕ} {G : Type u} [Group G]
    (hG : HasExponentThree G) (f : Fin t → G) :
    FreeBurnsideThree t →* G := by
  let F : FreeGroup (Fin t) →* G := FreeGroup.lift f
  apply QuotientGroup.lift
    (powerSubgroup (FreeGroup (Fin t)) 3) F
  unfold powerSubgroup
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, rfl⟩
  change F (x ^ 3) = 1
  rw [map_pow]
  exact hG (F x)

@[simp] theorem free_burnside_generator
    {t : ℕ} {G : Type u} [Group G]
    (hG : HasExponentThree G) (f : Fin t → G) (i : Fin t) :
    freeBurnsideLift hG f
        (freeBurnsideGenerator i) =
      f i := by
  simp [freeBurnsideLift, freeBurnsideGenerator]

/-- Homomorphisms out of the free exponent-three Burnside group are
determined by the displayed generators. -/
theorem free_burnside_ext
    {t : ℕ} {G : Type u} [Group G]
    {φ ψ : FreeBurnsideThree t →* G}
    (hgenerator :
      ∀ i, φ (freeBurnsideGenerator i) =
        ψ (freeBurnsideGenerator i)) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro w
  let q : FreeGroup (Fin t) →* FreeBurnsideThree t :=
    QuotientGroup.mk' (powerSubgroup (FreeGroup (Fin t)) 3)
  have hlifts :
      (FreeGroup.lift fun i =>
          φ (freeBurnsideGenerator i)) =
        FreeGroup.lift fun i =>
          ψ (freeBurnsideGenerator i) := by
    apply MonoidHom.ext
    intro w
    exact
      FreeGroup.lift_unique
        (FreeGroup.lift fun i =>
          φ (freeBurnsideGenerator i))
        (fun i => by simpa using hgenerator i)
  change φ (q w) = ψ (q w)
  calc
    φ (q w) =
        (FreeGroup.lift fun i =>
          φ (freeBurnsideGenerator i)) w :=
      FreeGroup.lift_unique (φ.comp q) fun i => rfl
    _ =
        (FreeGroup.lift fun i =>
          ψ (freeBurnsideGenerator i)) w := by
      rw [hlifts]
    _ = ψ (q w) :=
      (FreeGroup.lift_unique (ψ.comp q) fun i => rfl).symm

/-- Universal-property form of the last clause of Corollary 2: the group
`S_t` is the free exponent-three group on its displayed generators, i.e.
the third Burnside product in the terminology cited by Struik. -/
theorem thirdBurnsideProduct
    {t : ℕ} {G : Type u} [Group G]
    (hG : HasExponentThree G) (f : Fin t → G) :
    ∃! φ : FreeBurnsideThree t →* G,
      ∀ i, φ (freeBurnsideGenerator i) = f i := by
  refine ⟨freeBurnsideLift hG f,
    free_burnside_generator hG f, ?_⟩
  intro φ hφ
  apply free_burnside_ext
  intro i
  rw [hφ i, free_burnside_generator]

theorem burnside_repeated_triple
    {t : ℕ} (i j : Fin t) :
    hallTripleCommutator
        (freeBurnsideGenerator i)
        (freeBurnsideGenerator j)
        (freeBurnsideGenerator i) =
      1 :=
  triple_self_three
    (free_burnside_exponent t) _ _

/-- In rank two, the basic commutator is central in the free
exponent-three Burnside group. -/
theorem free_burnside_center :
    hallCommutator
        (freeBurnsideGenerator (0 : Fin 2))
        (freeBurnsideGenerator (1 : Fin 2)) ∈
      Subgroup.center (FreeBurnsideThree 2) := by
  let a := freeBurnsideGenerator (0 : Fin 2)
  let b := freeBurnsideGenerator (1 : Fin 2)
  let C := hallCommutator a b
  have hCa : Commute C a := by
    apply
      (commute_paper_1960 C a).mp
    simpa [C, a, b, hallTripleCommutator] using
      (burnside_repeated_triple
        (0 : Fin 2) (1 : Fin 2))
  have hCb : Commute C b := by
    have hswap :
        hallCommutator (hallCommutator b a) b = 1 := by
      simpa [hallTripleCommutator, a, b] using
        (burnside_repeated_triple
          (1 : Fin 2) (0 : Fin 2))
    rw [commutator_swap_inv a b] at hswap
    have hinv :
        Commute C⁻¹ b :=
      (commute_paper_1960 C⁻¹ b).mp
        (by simpa [C] using hswap)
    simpa using hinv.inv_left
  rw [Subgroup.mem_center_iff]
  intro x
  have hle :
      Subgroup.closure
          (Set.range
            (freeBurnsideGenerator (t := 2))) ≤
        Subgroup.centralizer {C} := by
    apply
      (Subgroup.closure_le (Subgroup.centralizer {C})).mpr
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact
        Subgroup.mem_centralizer_singleton_iff.mpr hCa.eq.symm
    · exact
        Subgroup.mem_centralizer_singleton_iff.mpr hCb.eq.symm
  rw [closure_burnside_top 2] at hle
  exact
    Subgroup.mem_centralizer_singleton_iff.mp
      (hle (Subgroup.mem_top x))

/-- The rank-two free exponent-three Burnside group has nilpotency class
at most two. -/
theorem burnside_rank_bot :
    Subgroup.lowerCentralSeries (FreeBurnsideThree 2) 2 = ⊥ := by
  let B := FreeBurnsideThree 2
  change Subgroup.lowerCentralSeries B 2 = ⊥
  let a : B := freeBurnsideGenerator (0 : Fin 2)
  let b : B := freeBurnsideGenerator (1 : Fin 2)
  let C := hallCommutator a b
  have hC : C ∈ Subgroup.center B := by
    exact free_burnside_center
  let q : B →* B ⧸ Subgroup.center B :=
    QuotientGroup.mk' (Subgroup.center B)
  let S : Set (B ⧸ Subgroup.center B) :=
    Set.range fun i : Fin 2 =>
      q (freeBurnsideGenerator i)
  have hclosure : Subgroup.closure S = ⊤ := by
    change
      Subgroup.closure
          (Set.range
            (q ∘ freeBurnsideGenerator (t := 2))) =
        ⊤
    rw [Set.range_comp,
      ← MonoidHom.map_closure q,
      closure_burnside_top 2,
      ← MonoidHom.range_eq_map]
    exact
      MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective (Subgroup.center B))
  have hqC : q C = 1 := by
    exact
      (QuotientGroup.eq_one_iff (N := Subgroup.center B) C).mpr hC
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    fin_cases i <;> fin_cases j
    · rfl
    · have hab :
          hallCommutator (q a) (q b) = 1 := by
        simpa only [C, hallCommutator, map_mul, map_inv] using hqC
      exact
        ((commute_paper_1960
          (q a) (q b)).mp hab).eq
    · have hab :
          hallCommutator (q a) (q b) = 1 := by
        simpa only [C, hallCommutator, map_mul, map_inv] using hqC
      exact
        ((commute_paper_1960
          (q a) (q b)).mp hab).symm.eq
    · rfl
  letI : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure hcomm
  letI : CommGroup (Subgroup.closure S) := inferInstance
  have hquotientCommutative :
      Std.Commutative
        (fun x y : B ⧸ Subgroup.center B => x * y) := by
    constructor
    intro x y
    have hx : x ∈ Subgroup.closure S := by
      rw [hclosure]
      trivial
    have hy : y ∈ Subgroup.closure S := by
      rw [hclosure]
      trivial
    exact
      congrArg Subtype.val
        (mul_comm
          (⟨x, hx⟩ : Subgroup.closure S)
          (⟨y, hy⟩ : Subgroup.closure S))
  have hcommutator :
      commutator B ≤ Subgroup.center B :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      ⟨hquotientCommutative⟩
  have hcentral :
      Subgroup.lowerCentralSeries B 1 ≤ Subgroup.center B := by
    simpa only [Subgroup.lowerCentralSeries_one] using hcommutator
  have hresult :
      Subgroup.lowerCentralSeries B (1 + 1) = ⊥ :=
    Subgroup.lowerCentralSeries_succ_eq_bot hcentral
  simpa only [one_add_one_eq_two] using hresult

/-- The free product of two cyclic groups of order three maps
canonically to the rank-two exponent-three Burnside group. -/
noncomputable def
    orderRankBurnside :
    CyclicFreeProduct (orderThreeFamily (t := 2)) →*
      FreeBurnsideThree 2 := by
  refine PresentedGroup.toGroup (f := freeBurnsideGenerator) ?_
  rintro r ⟨i, rfl⟩
  simpa [orderThreeFamily] using
    (free_burnside_exponent 2
      (freeBurnsideGenerator i))

@[simp] theorem
    order_burnside_generator
    (i : Fin 2) :
    orderRankBurnside
        (cyclicGenerator orderThreeFamily i) =
      freeBurnsideGenerator i := by
  exact PresentedGroup.toGroup.of _

/-- Since `B(2,3)` has class at most two, the preceding map factors
through the first nilpotent product `F/F₃`. -/
noncomputable def
    orderNilpotentBurnside :
    NilpotentCyclicProduct (orderThreeFamily (t := 2)) 3 →*
      FreeBurnsideThree 2 := by
  let f := orderRankBurnside
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (orderThreeFamily (t := 2))) 2) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries (FreeBurnsideThree 2) 2 :=
    Subgroup.lowerCentralSeries.map f 2 (Subgroup.mem_map_of_mem f hx)
  simpa [burnside_rank_bot]
    using hxmap

@[simp] theorem
    nilpotent_burnside_generator
    (i : Fin 2) :
    orderNilpotentBurnside
        (nilpotentCyclicGenerator orderThreeFamily 3 i) =
      freeBurnsideGenerator i := by
  simp [orderNilpotentBurnside,
    nilpotentCyclicGenerator,
    order_burnside_generator]

theorem
    nilpotent_burnside_surjective :
    Function.Surjective
      orderNilpotentBurnside := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← closure_burnside_top 2]
  apply
    (Subgroup.closure_le
      orderNilpotentBurnside.range).mpr
  rintro x ⟨i, rfl⟩
  exact
    ⟨nilpotentCyclicGenerator orderThreeFamily 3 i,
      nilpotent_burnside_generator i⟩

/-- The elementary abelian rank-two quotient used to count the
rank-two Burnside group. -/
abbrev RankElementaryAbelian :=
  Fin 2 → Multiplicative (ZMod 3)

def rankElementaryAbelian (i : Fin 2) :
    RankElementaryAbelian :=
  fun j =>
    Multiplicative.ofAdd
      (if j = i then (1 : ZMod 3) else 0)

theorem rank_elementary_abelian
    (x : RankElementaryAbelian) :
    x ^ 3 = 1 := by
  ext i
  have hpow := pow_card_eq_one' (x := x i)
  have hcard :
      Nat.card (Multiplicative (ZMod 3)) = 3 := by
    simp [Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  rw [hcard] at hpow
  exact hpow

noncomputable def freeBurnsideAbelian :
    FreeBurnsideThree 2 →* RankElementaryAbelian := by
  let f : FreeGroup (Fin 2) →*
      RankElementaryAbelian :=
    FreeGroup.lift rankElementaryAbelian
  apply QuotientGroup.lift
    (powerSubgroup (FreeGroup (Fin 2)) 3) f
  unfold powerSubgroup
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, rfl⟩
  change f (x ^ 3) = 1
  rw [map_pow]
  exact rank_elementary_abelian (f x)

@[simp] theorem burnside_abelian_generator
    (i : Fin 2) :
    freeBurnsideAbelian
        (freeBurnsideGenerator i) =
      rankElementaryAbelian i := by
  simp [freeBurnsideAbelian,
    freeBurnsideGenerator]

theorem burnside_abelian_surjective :
    Function.Surjective freeBurnsideAbelian := by
  intro x
  let n₀ := (Multiplicative.toAdd (x (0 : Fin 2))).val
  let n₁ := (Multiplicative.toAdd (x (1 : Fin 2))).val
  refine
    ⟨freeBurnsideGenerator (0 : Fin 2) ^ n₀ *
        freeBurnsideGenerator (1 : Fin 2) ^ n₁, ?_⟩
  simp only [map_mul, map_pow,
    burnside_abelian_generator]
  ext i
  fin_cases i <;>
    simp [rankElementaryAbelian, n₀, n₁]

/-- A repeated Hall triple commutator is nontrivial in the fourth
nilpotent product of any two selected order-three factors. -/
theorem nilpotent_repeated_triple
    {t : ℕ} (q : Pair t) :
    hallTripleCommutator
        (nilpotentCyclicGenerator orderThreeFamily 4 q.i)
        (nilpotentCyclicGenerator orderThreeFamily 4 q.j)
        (nilpotentCyclicGenerator orderThreeFamily 4 q.i) ≠
      1 := by
  let horder : ∀ i, AOrd (orderThreeFamily (t := t) i) :=
    order_family_admissible
  let f :=
    nilpotentGeneralResidues
      (orderThreeFamily (t := t)) horder
  intro htriple
  have hmapped := congrArg f htriple
  have hgenerator (i : Fin t) :
      f (nilpotentCyclicGenerator orderThreeFamily 4 i) =
        generalResidueGenerator
          (orderThreeFamily (t := t)) horder i := by
    exact
      nilpotent_residues_generator
        (orderThreeFamily (t := t)) horder i
  simp only [hallTripleCommutator, hallCommutator,
    map_mul, map_inv, map_one] at hmapped
  rw [hgenerator q.i, hgenerator q.j] at hmapped
  change
    (hallTripleCommutator
        (generalGenerator q.i)
        (generalGenerator q.j)
        (generalGenerator q.i) :
      GeneralResidueGroup
        (orderThreeFamily (t := t)) horder) =
      1 at hmapped
  have haxis :
      (generalAxis (.pairLeft q) 1 :
          GeneralResidueGroup
            (orderThreeFamily (t := t)) horder) =
        1 := by
    let quotientMap :=
      (generalCon
        (orderThreeFamily (t := t)) horder).mk'
    have hcoerced :
        hallTripleCommutator
            (generalGenerator q.i :
              GeneralResidueGroup
                (orderThreeFamily (t := t)) horder)
            (generalGenerator q.j :
              GeneralResidueGroup
                (orderThreeFamily (t := t)) horder)
            (generalGenerator q.i :
              GeneralResidueGroup
                (orderThreeFamily (t := t)) horder) =
          (generalAxis (.pairLeft q) 1 :
            GeneralResidueGroup
              (orderThreeFamily (t := t)) horder) := by
      have h := congrArg quotientMap
        (general_triple_left q)
      simpa only [hallTripleCommutator, hallCommutator,
        map_mul, map_inv] using h
    rw [hcoerced] at hmapped
    exact hmapped
  have horderAxis :=
    general_axis_order
      (orderThreeFamily (t := t)) horder (.pairLeft q)
  have : orderOf
      (generalAxis (.pairLeft q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t)) horder) = 1 := by
    rw [haxis, orderOf_one]
  rw [horderAxis] at this
  norm_num [generalCoordinateModulus,
    generalPairModulus, orderThreeFamily] at this

/-- The second nilpotent product `F/F₄` cannot be the free
exponent-three Burnside group, already on any chosen pair of generators. -/
theorem preserving_nilpotent_burnside
    {t : ℕ} (q : Pair t) :
    ¬ ∃ e :
        NilpotentCyclicProduct (orderThreeFamily (t := t)) 4 ≃*
          FreeBurnsideThree t,
        ∀ i,
          e (nilpotentCyclicGenerator orderThreeFamily 4 i) =
            freeBurnsideGenerator i := by
  rintro ⟨e, hgenerator⟩
  apply nilpotent_repeated_triple q
  apply e.injective
  rw [map_one]
  have hmapped :
      e (hallTripleCommutator
          (nilpotentCyclicGenerator orderThreeFamily 4 q.i)
          (nilpotentCyclicGenerator orderThreeFamily 4 q.j)
          (nilpotentCyclicGenerator orderThreeFamily 4 q.i)) =
        hallTripleCommutator
          (freeBurnsideGenerator q.i)
          (freeBurnsideGenerator q.j)
          (freeBurnsideGenerator q.i) := by
    simp only [hallTripleCommutator, hallCommutator,
      map_mul, map_inv, hgenerator]
  rw [hmapped]
  exact burnside_repeated_triple q.i q.j

/-- Every Hall triple commutator is trivial in the first nilpotent
product `F/F₃`. -/
theorem order_nilpotent_triple
    {t : ℕ} (i j k : Fin t) :
    hallTripleCommutator
        (nilpotentCyclicGenerator orderThreeFamily 3 i)
        (nilpotentCyclicGenerator orderThreeFamily 3 j)
        (nilpotentCyclicGenerator orderThreeFamily 3 k) =
      1 := by
  have hmem :=
    triple_series_general
      (nilpotentCyclicGenerator orderThreeFamily 3 i)
      (nilpotentCyclicGenerator orderThreeFamily 3 j)
      (nilpotentCyclicGenerator orderThreeFamily 3 k)
  have hbot :
      Subgroup.lowerCentralSeries
          (NilpotentCyclicProduct (orderThreeFamily (t := t)) 3) 2 =
        ⊥ := by
    simpa using
      nilpotent_cyclic_bot
        (orderThreeFamily (t := t)) 3
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- Exact central representatives for the subgroup generated by cubes:
only weight-three coordinates remain, and the two mixed coordinates on
each three-element index set have sum divisible by three. -/
structure GeneralCubeConstraint {t : ℕ}
    (c : GCoordi t) : Prop
    extends GeneralWeightThree c where
  mixedSum : ∀ q, (3 : ℤ) ∣ c.tripleFirst q + c.tripleSecond q

/-- The exact weight-three cube-constraint subgroup in integral
equation-(18) coordinates. -/
def generalCubeConstraint (t : ℕ) :
    Subgroup (GCoordi t) where
  carrier := {c | GeneralCubeConstraint c}
  one_mem' := by
    refine ⟨⟨⟨fun _ => rfl⟩, fun _ => rfl⟩, ?_⟩
    intro q
    exact dvd_zero 3
  mul_mem' := by
    intro c d hc hd
    refine ⟨⟨⟨fun i => ?_⟩, (fun q => ?_)⟩, fun q => ?_⟩
    · change c.single i + d.single i = 0
      simp [hc.single i, hd.single i]
    · change
        c.pair q + d.pair q -
            c.single q.j * d.single q.i =
          0
      simp [hc.pair q, hd.pair q, hc.single q.j, hd.single q.i]
    · change
        (3 : ℤ) ∣
          (GCoordi.mul c d).tripleFirst q +
            (GCoordi.mul c d).tripleSecond q
      simpa [GCoordi.mul,
        hc.single q.i, hc.single q.j, hc.single q.k,
        hd.single q.i, hd.single q.j, hd.single q.k,
        hc.pair q.ij, hc.pair q.ik, hc.pair q.jk,
        hd.pair q.ij, hd.pair q.ik, hd.pair q.jk,
        add_assoc, add_comm, add_left_comm] using
          (hc.mixedSum q).add (hd.mixedSum q)
  inv_mem' := by
    intro c hc
    refine ⟨⟨⟨fun i => ?_⟩, (fun q => ?_)⟩, fun q => ?_⟩
    · change -c.single i = 0
      simp [hc.single i]
    · change -(c.pair q - c.single q.j * -c.single q.i) = 0
      simp [hc.pair q, hc.single q.i, hc.single q.j]
    · change
        (3 : ℤ) ∣
          (GCoordi.rightInv c).tripleFirst q +
            (GCoordi.rightInv c).tripleSecond q
      rcases hc.mixedSum q with ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      simp only [GCoordi.rightInv, hc.single, hc.pair, neg_zero,
        zero_mul, mul_zero, add_zero, sub_zero, mul_neg]
      calc
        -c.tripleFirst q + -c.tripleSecond q =
            -(c.tripleFirst q + c.tripleSecond q) := by ring
        _ = -(3 * z) := by rw [hz]

/-- Remove the lower coordinates of a cube while retaining all
weight-three coordinates. -/
noncomputable def generalCubeTail
    {t : ℕ} (c : GCoordi t) :
    GCoordi t where
  single _ := 0
  pair _ := 0
  pairLeft q := (generalPowCoordinates c 3).pairLeft q
  pairRight q := (generalPowCoordinates c 3).pairRight q
  tripleFirst q := (generalPowCoordinates c 3).tripleFirst q
  tripleSecond q := (generalPowCoordinates c 3).tripleSecond q

private theorem ring_three_two :
    Ring.choose (3 : ℤ) 2 = 3 := by
  decide

private theorem ring_choose_three :
    Ring.choose (3 : ℤ) 3 = 1 := by
  decide

theorem general_cube_constraint
    {t : ℕ} (c : GCoordi t) :
    generalCubeTail c ∈
      generalCubeConstraint t := by
  refine ⟨⟨⟨fun _ => rfl⟩, fun _ => rfl⟩, fun q => ?_⟩
  refine ⟨c.tripleFirst q + c.tripleSecond q +
      c.pair q.ik * c.single q.j +
      c.pair q.ij * c.single q.k +
      c.pair q.jk * c.single q.i +
      c.pair q.ik * c.single q.j -
      6 * c.single q.i * c.single q.j * c.single q.k, ?_⟩
  simp only [generalCubeTail,
    generalPowCoordinates]
  norm_num [ring_three_two,
    ring_choose_three]
  ring

/-- A cube and its exact weight-three tail define the same element in
the order-three residue group. -/
theorem general_cube_tail
    {t : ℕ} (c : GCoordi t) :
    GMEq (orderThreeFamily (t := t))
      (c ^ 3) (generalCubeTail c) := by
  rw [general_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change
      (3 : ℤ) * c.single i ≡ 0
        [ZMOD (orderThreeFamily (t := t) i : ℤ)]
    simp [orderThreeFamily, Int.ModEq]
  · intro q
    change
      (3 : ℤ) * c.pair q -
          Ring.choose (3 : ℤ) 2 *
            c.single q.j * c.single q.i ≡
        0
        [ZMOD (generalPairModulus
          (orderThreeFamily (t := t)) q : ℤ)]
    rw [ring_three_two]
    norm_num [orderThreeFamily, generalPairModulus, Int.ModEq]
    refine ⟨c.single q.j * c.single q.i, ?_⟩
    ring
  · intro q
    exact Int.ModEq.refl _
  · intro q
    exact Int.ModEq.refl _
  · intro q
    exact Int.ModEq.refl _
  · intro q
    exact Int.ModEq.refl _

/-- The cube-constraint subgroup in the finite order-three coordinate
model. -/
noncomputable def orderCubeConstraint (t : ℕ) :
    Subgroup
      (GeneralResidueGroup
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))) :=
  Subgroup.map
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk'
    (generalCubeConstraint t)

theorem cube_constraint_center
    (t : ℕ) :
    orderCubeConstraint t ≤
      Subgroup.center
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) := by
  intro x hx
  rcases hx with ⟨c, hc, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  let quotientMap :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk'
  rcases
      (generalCon
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))).mk'_surjective y with
    ⟨d, rfl⟩
  have hcCenter :
      c ∈ Subgroup.center (GCoordi t) :=
    general_three_center t
      hc.toGeneralWeightThree
  have hcomm :=
    Subgroup.mem_center_iff.mp hcCenter d
  exact congrArg quotientMap hcomm

theorem cube_constraint_normal
    (t : ℕ) :
    (orderCubeConstraint t).Normal := by
  constructor
  intro n hn g
  have hnCenter :=
    cube_constraint_center t hn
  have hcomm :=
    Subgroup.mem_center_iff.mp hnCenter g
  rw [hcomm, mul_assoc, mul_inv_cancel]
  exact
    (orderCubeConstraint t).mul_mem hn
      (orderCubeConstraint t).one_mem

theorem residue_cube_constraint
    {t : ℕ}
    (x :
      GeneralResidueGroup
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))) :
    x ^ 3 ∈ orderCubeConstraint t := by
  let quotientMap :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk'
  rcases
      (generalCon
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))).mk'_surjective x with
    ⟨c, rfl⟩
  change quotientMap c ^ 3 ∈
    orderCubeConstraint t
  rw [← map_pow]
  refine ⟨generalCubeTail c,
    general_cube_constraint c, ?_⟩
  exact
    ((generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).eq.mpr
        (general_cube_tail c)).symm

theorem order_cube_constraint
    (t : ℕ) :
    powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3 ≤
      orderCubeConstraint t := by
  letI : (orderCubeConstraint t).Normal :=
    cube_constraint_normal t
  unfold powerSubgroup
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, rfl⟩
  exact residue_cube_constraint x

theorem axis_cube_constraint
    {t : ℕ} (q : Pair t) :
    (generalAxis (.pair q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) ∉
      orderCubeConstraint t := by
  rintro ⟨c, hc, hcaxis⟩
  change
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk' c =
        (generalCon
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))).mk'
            (generalAxis (.pair q) 1)
      at hcaxis
  have hmod :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).eq.mp hcaxis
  have hone : c.pair q ≡ 1 [ZMOD (3 : ℤ)] := by
    simpa [generalAxis, orderThreeFamily,
      generalPairModulus] using hmod.pair q
  have hzero : c.pair q ≡ 0 [ZMOD (3 : ℤ)] := by
    rw [hc.pair q]
  have hcontra : (1 : ℤ) ≡ 0 [ZMOD (3 : ℤ)] :=
    hone.symm.trans hzero
  norm_num [Int.ModEq] at hcontra

theorem order_pair_axis
    {t : ℕ} (q : Pair t) :
    (generalAxis (.pair q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) ∉
      powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3 := by
  intro h
  exact axis_cube_constraint q
    (order_cube_constraint t h)

theorem mixed_axis_constraint
    {t : ℕ} (q : Triple t) :
    (generalAxis (.tripleFirst q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) ∉
      orderCubeConstraint t := by
  rintro ⟨c, hc, hcaxis⟩
  change
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk' c =
        (generalCon
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))).mk'
            (generalAxis (.tripleFirst q) 1)
      at hcaxis
  have hmod :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).eq.mp hcaxis
  have hone :
      c.tripleFirst q + c.tripleSecond q ≡ 1 [ZMOD (3 : ℤ)] := by
    simpa [generalAxis, orderThreeFamily,
      generalResiduesModulus] using
      (hmod.tripleFirst q).add (hmod.tripleSecond q)
  have hzero :
      c.tripleFirst q + c.tripleSecond q ≡ 0 [ZMOD (3 : ℤ)] := by
    simpa [Int.ModEq] using hc.mixedSum q
  have hcontra : (1 : ℤ) ≡ 0 [ZMOD (3 : ℤ)] :=
    hone.symm.trans hzero
  norm_num [Int.ModEq] at hcontra

theorem order_mixed_axis
    {t : ℕ} (q : Triple t) :
    (generalAxis (.tripleFirst q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) ∉
      powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3 := by
  intro h
  exact mixed_axis_constraint q
    (order_cube_constraint t h)

/-- The order-three equation-(18) model modulo all cubes. -/
abbrev OrderBurnsideModel (t : ℕ) :=
  GeneralResidueGroup
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t)) ⧸
    powerSubgroup
      (GeneralResidueGroup
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))) 3

theorem mixed_triple_axis
    {t : ℕ} (q : Triple t) :
    hallTripleCommutator
        (generalResidueGenerator
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t)) q.i)
        (generalResidueGenerator
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t)) q.j)
        (generalResidueGenerator
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t)) q.k) =
      (generalAxis (.tripleFirst q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) := by
  let quotientMap :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk'
  have h := congrArg quotientMap
    (general_triple_first q)
  simpa only [generalResidueGenerator,
    hallTripleCommutator, hallCommutator,
    map_mul, map_inv] using h

/-- The canonical generators of the coordinate Burnside model. -/
noncomputable def orderBurnsideGenerator
    {t : ℕ} (i : Fin t) :
    OrderBurnsideModel t :=
  QuotientGroup.mk'
      (powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3)
    (generalResidueGenerator
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t)) i)

theorem order_residue_axis
    {t : ℕ} (q : Pair t) :
    hallCommutator
        (generalResidueGenerator
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t)) q.i)
        (generalResidueGenerator
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t)) q.j) =
      (generalAxis (.pair q) 1 :
        GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) := by
  let quotientMap :=
    (generalCon
      (orderThreeFamily (t := t))
      (order_family_admissible (t := t))).mk'
  have h := congrArg quotientMap
    (general_hallCommutator q)
  simpa only [generalResidueGenerator,
    hallCommutator, map_mul, map_inv] using h

theorem order_burnside_pair
    {t : ℕ} (q : Pair t) :
    hallCommutator
        (orderBurnsideGenerator q.i)
        (orderBurnsideGenerator q.j) ≠
      1 := by
  let quotientMap :=
    QuotientGroup.mk'
      (powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3)
  intro hcommutator
  have hmapped := congrArg quotientMap
    (order_residue_axis q)
  have haxis :
      quotientMap
          (generalAxis (.pair q) 1 :
            GeneralResidueGroup
              (orderThreeFamily (t := t))
              (order_family_admissible (t := t))) =
        1 := by
    rw [← hmapped]
    simpa only [orderBurnsideGenerator,
      hallCommutator, map_mul, map_inv] using hcommutator
  exact order_pair_axis q
    ((QuotientGroup.eq_one_iff
      (N := powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3) _).mp haxis)

theorem burnside_mixed_triple
    {t : ℕ} (q : Triple t) :
    hallTripleCommutator
        (orderBurnsideGenerator q.i)
        (orderBurnsideGenerator q.j)
        (orderBurnsideGenerator q.k) ≠
      1 := by
  let quotientMap :=
    QuotientGroup.mk'
      (powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3)
  intro htriple
  have hmapped := congrArg quotientMap
    (mixed_triple_axis q)
  have haxis :
      quotientMap
          (generalAxis (.tripleFirst q) 1 :
            GeneralResidueGroup
              (orderThreeFamily (t := t))
              (order_family_admissible (t := t))) =
        1 := by
    rw [← hmapped]
    simpa only [orderBurnsideGenerator,
      hallTripleCommutator, hallCommutator,
      map_mul, map_inv] using htriple
  exact order_mixed_axis q
    ((QuotientGroup.eq_one_iff
      (N := powerSubgroup
        (GeneralResidueGroup
          (orderThreeFamily (t := t))
          (order_family_admissible (t := t))) 3) _).mp haxis)

/-- The free group map to the coordinate Burnside model. -/
noncomputable def freeBurnsideModel
    (t : ℕ) :
    FreeGroup (Fin t) →* OrderBurnsideModel t :=
  FreeGroup.lift fun i => orderBurnsideGenerator i

@[simp] theorem burnside_model_generator
    {t : ℕ} (i : Fin t) :
    freeBurnsideModel t (FreeGroup.of i) =
      orderBurnsideGenerator i := by
  simp [freeBurnsideModel]

/-- The free exponent-three Burnside group maps to the coordinate
Burnside model. -/
noncomputable def burnsideCoordinateModel
    (t : ℕ) :
    FreeBurnsideThree t →* OrderBurnsideModel t := by
  let f := freeBurnsideModel t
  apply QuotientGroup.lift
    (powerSubgroup (FreeGroup (Fin t)) 3) f
  unfold powerSubgroup
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, rfl⟩
  change f (x ^ 3) = 1
  rw [map_pow]
  exact
    power_pow_one
      (GeneralResidueGroup
        (orderThreeFamily (t := t))
        (order_family_admissible (t := t))) 3 (f x)

@[simp] theorem
    free_burnside_model
    {t : ℕ} (i : Fin t) :
    burnsideCoordinateModel t
        (freeBurnsideGenerator i) =
      orderBurnsideGenerator i := by
  simp [freeBurnsideGenerator,
    burnsideCoordinateModel,
    freeBurnsideModel]

theorem free_burnside_mixed
    {t : ℕ} (q : Triple t) :
    hallTripleCommutator
        (freeBurnsideGenerator q.i)
        (freeBurnsideGenerator q.j)
        (freeBurnsideGenerator q.k) ≠
      1 := by
  intro htriple
  apply burnside_mixed_triple q
  have hmapped :=
    congrArg
      (burnsideCoordinateModel t) htriple
  simpa only [hallTripleCommutator, hallCommutator,
    map_mul, map_inv, map_one,
    free_burnside_model] using hmapped

theorem free_burnside_ne
    {t : ℕ} (q : Pair t) :
    hallCommutator
        (freeBurnsideGenerator q.i)
        (freeBurnsideGenerator q.j) ≠
      1 := by
  intro hcommutator
  apply order_burnside_pair q
  have hmapped :=
    congrArg
      (burnsideCoordinateModel t) hcommutator
  simpa only [hallCommutator, map_mul, map_inv, map_one,
    free_burnside_model] using hmapped

theorem free_burnside_card :
    Nat.card (FreeBurnsideThree 2) = 27 := by
  letI :
      Finite
        (NilpotentCyclicProduct
          (orderThreeFamily (t := 2)) 3) :=
    Nat.finite_of_card_ne_zero
      (by
        rw [order_nilpotent_card]
        norm_num)
  letI : Finite (FreeBurnsideThree 2) :=
    Finite.of_surjective
      orderNilpotentBurnside
      nilpotent_burnside_surjective
  let q : Pair 2 :=
    pairTwo (by omega)
  let C :=
    hallCommutator
      (freeBurnsideGenerator q.i)
      (freeBurnsideGenerator q.j)
  have hCne : C ≠ 1 := by
    exact free_burnside_ne q
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hCorder : orderOf C = 3 :=
    orderOf_eq_prime
      (free_burnside_exponent 2 C) hCne
  let χ := freeBurnsideAbelian
  have hCker : C ∈ χ.ker := by
    change χ C = 1
    simp [χ, C, hallCommutator, mul_comm]
  have hzpowers : Subgroup.zpowers C ≤ χ.ker :=
    Subgroup.zpowers_le_of_mem hCker
  let kernelEmbedding :
      Subgroup.zpowers C → χ.ker :=
    fun x => ⟨x, hzpowers x.2⟩
  have hkernelEmbedding :
      Function.Injective kernelEmbedding := by
    intro x y hxy
    apply Subtype.ext
    exact
      congrArg
        (fun z : χ.ker => (z : FreeBurnsideThree 2)) hxy
  have hkernel : 3 ≤ Nat.card χ.ker := by
    have hcardZpowers :
        Nat.card (Subgroup.zpowers C) = 3 :=
      (Nat.card_zpowers C).trans hCorder
    calc
      3 = Nat.card (Subgroup.zpowers C) :=
        hcardZpowers.symm
      _ ≤ Nat.card χ.ker :=
        Nat.card_le_card_of_injective
          kernelEmbedding hkernelEmbedding
  have htarget :
      Nat.card RankElementaryAbelian = 9 := by
    simp [RankElementaryAbelian,
      Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hrange : χ.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      burnside_abelian_surjective
  have hindex : χ.ker.index = 9 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, htarget]
  have hlower : 27 ≤ Nat.card (FreeBurnsideThree 2) := by
    calc
      27 = 3 * 9 := by norm_num
      _ = 3 * χ.ker.index := by rw [hindex]
      _ ≤ Nat.card χ.ker * χ.ker.index :=
        Nat.mul_le_mul_right χ.ker.index hkernel
      _ = Nat.card (FreeBurnsideThree 2) :=
        χ.ker.card_mul_index
  have hupper : Nat.card (FreeBurnsideThree 2) ≤ 27 := by
    rw [← order_nilpotent_card]
    exact
      Nat.card_le_card_of_surjective
        orderNilpotentBurnside
        nilpotent_burnside_surjective
  exact le_antisymm hupper hlower

theorem nilpotent_burnside_bijective :
    Function.Bijective
      orderNilpotentBurnside := by
  letI :
      Finite
        (NilpotentCyclicProduct
          (orderThreeFamily (t := 2)) 3) :=
    Nat.finite_of_card_ne_zero
      (by
        rw [order_nilpotent_card]
        norm_num)
  letI : Finite (FreeBurnsideThree 2) :=
    Finite.of_surjective
      orderNilpotentBurnside
      nilpotent_burnside_surjective
  apply
    nilpotent_burnside_surjective
      |>.bijective_of_nat_card_le
  rw [order_nilpotent_card,
    free_burnside_card]

/-- **Corollary 2, exceptional rank.**  The free exponent-three
Burnside group on two generators is canonically the first nilpotent
product of two cyclic groups of order three. -/
noncomputable def rankTwoEquiv :
    NilpotentCyclicProduct (orderThreeFamily (t := 2)) 3 ≃*
      FreeBurnsideThree 2 :=
  MulEquiv.ofBijective
    orderNilpotentBurnside
    nilpotent_burnside_bijective

@[simp] theorem rank_burnside_generator
    (i : Fin 2) :
    rankTwoEquiv
        (nilpotentCyclicGenerator orderThreeFamily 3 i) =
      freeBurnsideGenerator i := by
  exact nilpotent_burnside_generator i

/-- The first nilpotent product `F/F₃` cannot be the free
exponent-three Burnside group when three selected generators are
present. -/
theorem no_preserving_burnside
    {t : ℕ} (q : Triple t) :
    ¬ ∃ e :
        NilpotentCyclicProduct (orderThreeFamily (t := t)) 3 ≃*
          FreeBurnsideThree t,
        ∀ i,
          e (nilpotentCyclicGenerator orderThreeFamily 3 i) =
            freeBurnsideGenerator i := by
  rintro ⟨e, hgenerator⟩
  apply free_burnside_mixed q
  rw [← hgenerator q.i, ← hgenerator q.j, ← hgenerator q.k]
  have hmapped :=
    congrArg e
      (order_nilpotent_triple q.i q.j q.k)
  simpa only [hallTripleCommutator, hallCommutator,
    map_mul, map_inv, map_one] using hmapped

/-- **Corollary 2, nonexceptional ranks.**  With at least three cyclic
factors, the free exponent-three Burnside product is neither the first
nor the second nilpotent product, as a product with its displayed
generators. -/
theorem no_nilpotent_three
    {t : ℕ} (ht : 3 ≤ t) :
    (¬ ∃ e :
        NilpotentCyclicProduct (orderThreeFamily (t := t)) 3 ≃*
          FreeBurnsideThree t,
        ∀ i,
          e (nilpotentCyclicGenerator orderThreeFamily 3 i) =
            freeBurnsideGenerator i) ∧
    (¬ ∃ e :
        NilpotentCyclicProduct (orderThreeFamily (t := t)) 4 ≃*
          FreeBurnsideThree t,
        ∀ i,
          e (nilpotentCyclicGenerator orderThreeFamily 4 i) =
            freeBurnsideGenerator i) := by
  exact
    ⟨no_preserving_burnside
        (tripleThree ht),
      preserving_nilpotent_burnside
        (pairTwo (by omega))⟩

/-- Every Hall triple commutator is trivial in the first nilpotent product,
not only those formed from the displayed generators. -/
theorem nilpotent_triple_general
    {t : ℕ}
    (x y z :
      NilpotentCyclicProduct (orderThreeFamily (t := t)) 3) :
    hallTripleCommutator x y z = 1 := by
  have hmem :=
    triple_series_general x y z
  have hbot :
      Subgroup.lowerCentralSeries
          (NilpotentCyclicProduct (orderThreeFamily (t := t)) 3) 2 =
        ⊥ := by
    simpa using
      nilpotent_cyclic_bot
        (orderThreeFamily (t := t)) 3
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- The first nilpotent product and the free exponent-three Burnside group
are not even abstractly isomorphic when three distinct generators exist. -/
theorem no_nilpotent_burnside
    {t : ℕ} (q : Triple t) :
    ¬ Nonempty
      (NilpotentCyclicProduct (orderThreeFamily (t := t)) 3 ≃*
        FreeBurnsideThree t) := by
  rintro ⟨e⟩
  apply free_burnside_mixed q
  let x := e.symm (freeBurnsideGenerator q.i)
  let y := e.symm (freeBurnsideGenerator q.j)
  let z := e.symm (freeBurnsideGenerator q.k)
  have hsource :=
    nilpotent_triple_general x y z
  have hmapped := congrArg e hsource
  simpa only [x, y, z, hallTripleCommutator, hallCommutator,
    map_mul, map_inv, map_one, MulEquiv.apply_symm_apply] using hmapped

/-- The second nilpotent product and the free exponent-three Burnside group
are not even abstractly isomorphic when two distinct generators exist. -/
theorem no_four_burnside
    {t : ℕ} (q : Pair t) :
    ¬ Nonempty
      (NilpotentCyclicProduct (orderThreeFamily (t := t)) 4 ≃*
        FreeBurnsideThree t) := by
  rintro ⟨e⟩
  apply nilpotent_repeated_triple q
  apply e.injective
  rw [map_one]
  simpa only [hallTripleCommutator, hallCommutator,
    map_mul, map_inv] using
      triple_self_three
        (free_burnside_exponent t)
        (e (nilpotentCyclicGenerator orderThreeFamily 4 q.i))
        (e (nilpotentCyclicGenerator orderThreeFamily 4 q.j))

/-- **Corollary 2, abstract-isomorphism form.**  With at least three cyclic
factors, the free exponent-three Burnside product is abstractly isomorphic
to neither the first nor the second nilpotent product. -/
theorem no_abstract_nilpotent
    {t : ℕ} (ht : 3 ≤ t) :
    (¬ Nonempty
      (NilpotentCyclicProduct (orderThreeFamily (t := t)) 3 ≃*
        FreeBurnsideThree t)) ∧
    (¬ Nonempty
      (NilpotentCyclicProduct (orderThreeFamily (t := t)) 4 ≃*
        FreeBurnsideThree t)) :=
  ⟨no_nilpotent_burnside
      (tripleThree ht),
    no_four_burnside
      (pairTwo (by omega))⟩

end P1960
end Struik
