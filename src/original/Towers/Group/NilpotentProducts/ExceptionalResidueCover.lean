import Towers.Group.NilpotentProducts.LowWeightReindexing
import Towers.Group.NilpotentProducts.EvenClassThree
import Towers.Group.NilpotentProducts.RankResidueCover

open scoped IsMulCommutative


/-!
# A Hall-coordinate cover for Struik's Theorem 4

The concrete Hall atom order is implementation-dependent.  For Theorem 4
we map an atom to the cyclic generator indexed by its rank in that order.
Thus the mapped Hall factors are indexed in the numerical order used in
equations (25) and (29).
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex
open scoped commutatorElement

universe u

/-- The inverse-generator map, relabelled so Hall-atom rank is the numerical
generator index in Theorem 4. -/
noncomputable def rankedTruncationMap
    {t : ℕ} (r : Fin t → ℕ) :
    LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) 4 →*
    EvenClassGroup r := by
  let f : FreeGroup (FreeGenerator.{u} t) →*
      EvenClassGroup r :=
    FreeGroup.lift fun i =>
      (evenClassGenerator r (lowHallRank.{u} i.down))⁻¹
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} t)) 3) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries (EvenClassGroup r) 3 :=
    Subgroup.lowerCentralSeries.map f 3 (Subgroup.mem_map_of_mem f hx)
  simpa [nilpotent_four_bot
    (singleModulus r)] using hxmap

@[simp] theorem exceptional_ranked_generator
    {t : ℕ} (r : Fin t → ℕ)
    (i : FreeGenerator.{u} t) :
    rankedTruncationMap r
      (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) 4 (FreeGroup.of i)) =
      (evenClassGenerator r (lowHallRank.{u} i.down))⁻¹ := by
  simp [rankedTruncationMap]

/-- The ranked truncation map still reaches every cyclic generator. -/
theorem ranked_truncation_surjective
    {t : ℕ} (r : Fin t → ℕ) :
    Function.Surjective (rankedTruncationMap.{u} r) := by
  let value : FreeGenerator.{u} t → EvenClassGroup r :=
    fun i => (evenClassGenerator r (lowHallRank.{u} i.down))⁻¹
  have hclosure :
      Subgroup.closure (Set.range value) =
        (⊤ : Subgroup (EvenClassGroup r)) := by
    apply top_unique
    rw [← range_nilpotent_top
      (singleModulus r)]
    refine (Subgroup.closure_le (Subgroup.closure (Set.range value))).2 ?_
    rintro x ⟨i, rfl⟩
    let j : Fin t := (lowWeightRank.{u} t).symm i
    have hvalue :
        value (ULift.up j) ∈ Subgroup.closure (Set.range value) :=
      Subgroup.subset_closure (Set.mem_range_self (ULift.up j))
    have hrank : lowHallRank.{u} j = i :=
      low_weight_symm.{u} i
    have hinv :=
      (Subgroup.closure (Set.range value)).inv_mem hvalue
    change evenClassGenerator r i ∈
      Subgroup.closure (Set.range value)
    simpa only [value, inv_inv, hrank] using hinv
  have hfree :
      Function.Surjective (FreeGroup.lift value) :=
    Towers.Edmonton.free_range_top
      value hclosure
  intro x
  obtain ⟨w, rfl⟩ := hfree x
  refine ⟨lowerCentralTruncation
    (FreeGroup (FreeGenerator.{u} t)) 4 w, ?_⟩
  rfl

/-- Every element of the Theorem 4 group is a mapped standard Hall
product, with atom ranks agreeing with the numerical generator indices. -/
theorem ranked_standard_product
    {t : ℕ} (r : Fin t → ℕ) (x : EvenClassGroup r) :
    ∃ e : StandardExponentFamily.{u} t,
      rankedTruncationMap.{u} r
          (standardHallProduct t 4 e) =
        x := by
  obtain ⟨y, rfl⟩ :=
    ranked_truncation_surjective.{u} r x
  obtain ⟨e, he, _⟩ := unique_hall_coordinates t 4 y
  exact ⟨e, congrArg (rankedTruncationMap.{u} r) he⟩

/-- A weight-one Hall factor maps to the inverse generator bearing its
numerical Hall rank. -/
@[simp] theorem exceptional_truncation_low
    {t : ℕ} (r : Fin t → ℕ) (i : Fin t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 1).commutator
          (lowWeightIndex.{u} t i)
          |>.freeLowerTruncation (n := 4)) =
      (evenClassGenerator r (lowHallRank.{u} i))⁻¹ := by
  change
    rankedTruncationMap.{u} r
        (((concreteCommutatorsWeight.{u} t 1).commutator
          (lowWeightCanonical.{u} i)).word.eval
            (freeTruncationValue t 4)) =
      _
  rw [concrete_basic_word,
    tree_low_canonical,
    CWord.map_eval]
  exact exceptional_ranked_generator r (lowWeightGenerator i)

/-- A weight-two Hall factor maps to the inverse of the numerically oriented
pair commutator. -/
@[simp] theorem exceptional_ranked_truncation
    {t : ℕ} (r : Fin t → ℕ) (q : LowPairIndex.{u} t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 2).commutator
          (lowTwoIndex.{u} t q)
          |>.freeLowerTruncation (n := 4)) =
      (hallCommutator
        (evenClassGenerator r (lowHallRank.{u} q.i))
        (evenClassGenerator r (lowHallRank.{u} q.j)))⁻¹ := by
  change
    rankedTruncationMap.{u} r
        (((concreteCommutatorsWeight.{u} t 2).commutator
          (lowTwoCanonical.{u} q)).word.eval
            (freeTruncationValue t 4)) =
      _
  rw [concrete_basic_word,
    concrete_low_canonical,
    CWord.map_eval]
  simp only [lowPairTree, lowWeightAtom,
    HallTree.to_commutator_commutator,
    HallTree.commutator_word_atom, CWord.eval_commutator,
    CWord.eval_atom, freeTruncationValue,
    exceptional_ranked_generator]
  rw [commutator_element_inv, inv_inv, inv_inv,
    commutator_swap_inv]
  simp [lowWeightGenerator]

/-- A weight-three Hall factor maps to the Hall triple commutator at its
three numerical Hall ranks. -/
@[simp] theorem exceptional_ranked_low
    {t : ℕ} (r : Fin t → ℕ) (q : LowThreeIndex.{u} t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 3).commutator
          (lowIndexEquiv.{u} t q)
          |>.freeLowerTruncation (n := 4)) =
      hallTripleCommutator
        (evenClassGenerator r
          (lowHallRank.{u} (lowThreeLeaves q).1))
        (evenClassGenerator r
          (lowHallRank.{u} (lowThreeLeaves q).2.1))
        (evenClassGenerator r
          (lowHallRank.{u} (lowThreeLeaves q).2.2)) := by
  change
    rankedTruncationMap.{u} r
        (((concreteCommutatorsWeight.{u} t 3).commutator
          (lowThreeCanonical.{u} q)).word.eval
            (freeTruncationValue t 4)) =
      _
  rw [concrete_basic_word,
    concrete_tree_low,
    CWord.map_eval]
  simp only [lowThreeTree, lowTripleTree,
    lowPairTree, lowWeightAtom, HallTree.to_commutator_commutator,
    HallTree.commutator_word_atom, CWord.eval_commutator,
    CWord.eval_atom, freeTruncationValue,
    exceptional_ranked_generator]
  rw [commutator_element_inv, inv_inv]
  rw [commutator_element_inv, inv_inv, inv_inv]
  simp only [lowWeightGenerator]
  have hinner :
      hallCommutator
          (evenClassGenerator r
            (lowHallRank.{u} (lowThreeLeaves q).2.1))
          (evenClassGenerator r
            (lowHallRank.{u} (lowThreeLeaves q).1)) =
        (hallCommutator
          (evenClassGenerator r
            (lowHallRank.{u} (lowThreeLeaves q).1))
          (evenClassGenerator r
            (lowHallRank.{u} (lowThreeLeaves q).2.1)))⁻¹ :=
    commutator_swap_inv _ _
  rw [hinner, inv_inv, hallTripleCommutator]

/-- Read equation-(18) single coordinates as exponents of the mapped
weight-one Hall factors.  The sign compensates for the inverse-generator
truncation map. -/
noncomputable def weightHallExponent
    {t : ℕ} (c : GCoordi t)
    (i : (standardHallFamily.{u} t 1).index) : ℤ :=
  -c.single
    (lowHallRank.{u}
      ((lowWeightIndex.{u} t).symm i))

/-- Read equation-(18) pair coordinates as exponents of the mapped
weight-two Hall factors. -/
noncomputable def weightTwoExponent
    {t : ℕ} (c : GCoordi t)
    (i : (standardHallFamily.{u} t 2).index) : ℤ :=
  -c.pair
    (lowPairRank.{u} t
      ((lowTwoIndex.{u} t).symm i))

/-- Read the four equation-(18) weight-three coordinate families as
exponents of the mapped weight-three Hall factors. -/
noncomputable def weightThreeExponent
    {t : ℕ} (c : GCoordi t)
    (i : (standardHallFamily.{u} t 3).index) : ℤ :=
  match lowCoordinateEquiv.{u} t
      ((lowIndexEquiv.{u} t).symm i) with
  | .pairLeft q => c.pairLeft q
  | .pairRight q => c.pairRight q
  | .tripleFirst q => c.tripleFirst q - c.tripleSecond q
  | .tripleSecond q => c.tripleSecond q

/-- The Hall exponent family attached to one integral equation-(29) tuple. -/
noncomputable def exceptionalHallExponents
    {t : ℕ} (c : ELCoordi t) :
    StandardExponentFamily.{u} t
  | 1 => weightHallExponent
      (toGeneralResidues c)
  | 2 => weightTwoExponent
      (toGeneralResidues c)
  | 3 => weightThreeExponent
      (toGeneralResidues c)
  | _ => fun _ => 0

/-- Reassemble equation-(18) coordinates from arbitrary Hall exponents in
weights one through three. -/
noncomputable def generalExceptionalExponents
    {t : ℕ} (e : StandardExponentFamily.{u} t) :
    GCoordi t where
  single i :=
    -e 1
      (lowWeightIndex.{u} t
        ((lowWeightRank.{u} t).symm i))
  pair q :=
    -e 2
      (lowTwoIndex.{u} t
        ((lowPairRank.{u} t).symm q))
  pairLeft q :=
    e 3
      (lowIndexEquiv.{u} t
        ((lowCoordinateEquiv.{u} t).symm (.pairLeft q)))
  pairRight q :=
    e 3
      (lowIndexEquiv.{u} t
        ((lowCoordinateEquiv.{u} t).symm (.pairRight q)))
  tripleFirst q :=
    e 3
        (lowIndexEquiv.{u} t
          ((lowCoordinateEquiv.{u} t).symm (.tripleFirst q))) +
      e 3
        (lowIndexEquiv.{u} t
          ((lowCoordinateEquiv.{u} t).symm (.tripleSecond q)))
  tripleSecond q :=
    e 3
      (lowIndexEquiv.{u} t
        ((lowCoordinateEquiv.{u} t).symm (.tripleSecond q)))

/-- Reassemble equation-(29) replacement coordinates from arbitrary Hall
exponents. -/
noncomputable def exceptionalCoordinatesExponents
    {t : ℕ} (e : StandardExponentFamily.{u} t) :
    ELCoordi t :=
  generalExceptionalResidues
    (generalExceptionalExponents e)

@[simp] theorem exceptional_exponents_one
    {t : ℕ} (e : StandardExponentFamily.{u} t)
    (i : (standardHallFamily.{u} t 1).index) :
    exceptionalHallExponents
        (exceptionalCoordinatesExponents e) 1 i =
      e 1 i := by
  simp [exceptionalHallExponents, weightHallExponent,
    exceptionalCoordinatesExponents,
    generalExceptionalExponents]

@[simp] theorem exceptional_exponents_two
    {t : ℕ} (e : StandardExponentFamily.{u} t)
    (i : (standardHallFamily.{u} t 2).index) :
    exceptionalHallExponents
        (exceptionalCoordinatesExponents e) 2 i =
      e 2 i := by
  simp [exceptionalHallExponents, weightTwoExponent,
    exceptionalCoordinatesExponents,
    generalExceptionalExponents]

@[simp] theorem exceptional_exponents_three
    {t : ℕ} (e : StandardExponentFamily.{u} t)
    (i : (standardHallFamily.{u} t 3).index) :
    exceptionalHallExponents
        (exceptionalCoordinatesExponents e) 3 i =
      e 3 i := by
  let q := (lowIndexEquiv.{u} t).symm i
  have hi : lowIndexEquiv.{u} t q = i :=
    (lowIndexEquiv.{u} t).apply_symm_apply i
  cases hcoord :
      lowCoordinateEquiv.{u} t q <;>
    simp only [exceptionalHallExponents, weightThreeExponent, hcoord,
      exceptionalCoordinatesExponents, generalExceptionalExponents,
      exceptional_general_residues, add_sub_cancel_right, q] <;>
    rw [← hcoord, Equiv.symm_apply_apply, hi]

private theorem standard_weight_products
    {t : ℕ} (e : StandardExponentFamily.{u} t) :
    standardHallProduct t 4 e =
      (standardHallFamily.{u} t 1).collectedWeightProduct (n := 4) (e 1) *
        (standardHallFamily.{u} t 2).collectedWeightProduct (n := 4) (e 2) *
          (standardHallFamily.{u} t 3).collectedWeightProduct
            (n := 4) (e 3) := by
  norm_num [standardHallProduct, collectedHallProduct,
    collectedPrefixProduct, List.range_succ, mul_assoc]

/-- Evaluate an integral equation-(29) tuple in Struik's fourth nilpotent
product through its corresponding Hall exponents. -/
noncomputable def integralCoordinateEval
    {t : ℕ} (r : Fin t → ℕ) :
    ELCoordi t → EvenClassGroup r :=
  fun c =>
    rankedTruncationMap.{u} r
      (standardHallProduct t 4 (exceptionalHallExponents.{u} c))

/-- Every element of the Theorem 4 group is represented by an integral
equation-(29) tuple. -/
theorem integral_coordinate_surjective
    {t : ℕ} (r : Fin t → ℕ) :
    Function.Surjective (integralCoordinateEval.{u} r) := by
  intro x
  obtain ⟨e, he⟩ :=
    ranked_standard_product.{u} r x
  refine ⟨exceptionalCoordinatesExponents.{u} e, ?_⟩
  change rankedTruncationMap.{u} r
      (standardHallProduct t 4
        (exceptionalHallExponents
          (exceptionalCoordinatesExponents e))) =
    x
  have hprod :
      standardHallProduct t 4
          (exceptionalHallExponents
            (exceptionalCoordinatesExponents e)) =
        standardHallProduct t 4 e := by
    rw [standard_weight_products,
      standard_weight_products]
    have h1 :
        exceptionalHallExponents
            (exceptionalCoordinatesExponents e) 1 =
          e 1 :=
      funext (exceptional_exponents_one e)
    have h2 :
        exceptionalHallExponents
            (exceptionalCoordinatesExponents e) 2 =
          e 2 :=
      funext (exceptional_exponents_two e)
    have h3 :
        exceptionalHallExponents
            (exceptionalCoordinatesExponents e) 3 =
          e 3 :=
      funext (exceptional_exponents_three e)
    rw [h1, h2, h3]
  rw [hprod]
  exact he

/-- The commutator subgroup of the Theorem 4 group. -/
abbrev Derived {t : ℕ} (r : Fin t → ℕ) :=
  Subgroup.lowerCentralSeries (EvenClassGroup r) 1

/-- In a class-three group the commutator subgroup is abelian. -/
noncomputable instance derivedMulCommutative
    {t : ℕ} (r : Fin t → ℕ) :
    IsMulCommutative (Derived r) :=
  ⟨⟨by
    intro x y
    apply Subtype.ext
    have hxy :
        ⁅(x : EvenClassGroup r), (y : EvenClassGroup r)⁆ ∈
          Subgroup.lowerCentralSeries (EvenClassGroup r) 3 := by
      simpa using lower_commutator_succ 1 1
        (Subgroup.commutator_mem_commutator x.property y.property)
    have hcommutator :
        ⁅(x : EvenClassGroup r), (y : EvenClassGroup r)⁆ = 1 := by
      rw [nilpotent_four_bot
        (singleModulus r)] at hxy
      exact Subgroup.mem_bot.mp hxy
    exact (commutatorElement_eq_one_iff_commute.mp hcommutator).eq⟩⟩

/-- The numerically oriented pair commutator, regarded as an element of the
abelian commutator subgroup. -/
def pairDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    Derived r :=
  ⟨hallCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.j), by
    simpa using lower_series_elementary
      (i := 0) (j := 0)
      (x := evenClassGenerator r q.i)
      (y := evenClassGenerator r q.j) (by simp) (by simp)⟩

/-- The repeated-left triple commutator in the abelian commutator
subgroup. -/
def leftTripleDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    Derived r :=
  ⟨hallTripleCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.j)
      (evenClassGenerator r q.i),
    (Subgroup.lowerCentralSeries_antitone (by omega : 1 ≤ 2))
      (triple_series_elementary _ _ _)⟩

/-- The repeated-right triple commutator in the abelian commutator
subgroup. -/
def pairTripleDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    Derived r :=
  ⟨hallTripleCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.j)
      (evenClassGenerator r q.j),
    (Subgroup.lowerCentralSeries_antitone (by omega : 1 ≤ 2))
      (triple_series_elementary _ _ _)⟩

/-- The replacement factor `(aᵢ²,aⱼ) = C²D` in the abelian commutator
subgroup. -/
def leftReplacementDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    Derived r :=
  pairDerived r q ^ (2 : ℤ) *
    leftTripleDerived r q

/-- The replacement factor `(aᵢ,aⱼ²) = C²E` in the abelian commutator
subgroup. -/
def pairReplacementDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    Derived r :=
  pairDerived r q ^ (2 : ℤ) *
    pairTripleDerived r q

/-- The first mixed triple factor in the abelian commutator subgroup. -/
def tripleFirstDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    Derived r :=
  ⟨hallTripleCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.j)
      (evenClassGenerator r q.k),
    (Subgroup.lowerCentralSeries_antitone (by omega : 1 ≤ 2))
      (triple_series_elementary _ _ _)⟩

/-- The second mixed triple factor in the abelian commutator subgroup. -/
def tripleSecondDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    Derived r :=
  ⟨hallTripleCommutator
      (evenClassGenerator r q.j)
      (evenClassGenerator r q.k)
      (evenClassGenerator r q.i),
    (Subgroup.lowerCentralSeries_antitone (by omega : 1 ≤ 2))
      (triple_series_elementary _ _ _)⟩

/-- The second canonical Hall factor on three increasing indices.  Struik
uses a different second mixed factor, related to this one by Hall-Witt. -/
def tripleHallDerived
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    Derived r :=
  ⟨hallTripleCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.k)
      (evenClassGenerator r q.j),
    (Subgroup.lowerCentralSeries_antitone (by omega : 1 ≤ 2))
      (triple_series_elementary _ _ _)⟩

private theorem group_isMetabelian
    {t : ℕ} (r : Fin t → ℕ) :
    Towers.Edmonton.Group.IsMetabelian (EvenClassGroup r) := by
  unfold Towers.Edmonton.Group.IsMetabelian
  rw [← Subgroup.lowerCentralSeries_one]
  apply le_antisymm
  · calc
      ⁅Subgroup.lowerCentralSeries (EvenClassGroup r) 1,
          Subgroup.lowerCentralSeries (EvenClassGroup r) 1⁆ ≤
          Subgroup.lowerCentralSeries (EvenClassGroup r) 3 := by
            simpa using
              (lower_commutator_succ
                (G := EvenClassGroup r) 1 1)
      _ = ⊥ :=
        nilpotent_four_bot
          (singleModulus r)
  · exact bot_le

private theorem triple_swap_three
    {G : Type*} [Group G] (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (x y z : G) :
    hallTripleCommutator y x z =
      (hallTripleCommutator x y z)⁻¹ := by
  unfold hallTripleCommutator
  rw [commutator_swap_inv x y]
  exact commutator_inv_elementary
    (fun g => commute_triple_elementary hG4 g x y z)

/-- Hall-Witt changes the second canonical Hall factor `[i,k,j]` into
Struik's mixed basis as `[i,j,k] [j,k,i]`. -/
theorem triple_second_derived
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    tripleHallDerived r q =
      tripleFirstDerived r q *
        tripleSecondDerived r q := by
  apply Subtype.ext
  let x := evenClassGenerator r q.i
  let y := evenClassGenerator r q.j
  let z := evenClassGenerator r q.k
  let A := hallTripleCommutator x y z
  let H := hallTripleCommutator x z y
  let B := hallTripleCommutator y z x
  have hG4 :
      Subgroup.lowerCentralSeries (EvenClassGroup r) 3 = ⊥ :=
    nilpotent_four_bot
      (singleModulus r)
  have hswap :
      hallTripleCommutator z x y = H⁻¹ := by
    exact triple_swap_three hG4 x z y
  have hcyclic : A * H⁻¹ * B = 1 := by
    simpa only [A, H, B, hswap] using
      cyclic_triple_commutator
        (group_isMetabelian r) x y z
  have hHB : Commute H B :=
    (commute_triple_elementary hG4 B x z y).symm
  have hreorder : A * H⁻¹ * B = (A * B) * H⁻¹ := by
    calc
      A * H⁻¹ * B = A * (H⁻¹ * B) := by rw [mul_assoc]
      _ = A * (B * H⁻¹) := by
        rw [hHB.inv_left.eq]
      _ = (A * B) * H⁻¹ := by rw [mul_assoc]
  have hAB : A * B = H := by
    rw [hreorder, mul_inv_eq_one] at hcyclic
    exact hcyclic
  exact hAB.symm

theorem pair_derived_modulus
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    pairDerived r q ^ exceptionalPairModulus r q = 1 := by
  apply Subtype.ext
  exact pair_pow_modulus r hpos q

theorem pair_replacement_derived
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    leftReplacementDerived r q ^
      leftSquareModulus r q = 1 := by
  apply Subtype.ext
  change
    (hallCommutator
          (evenClassGenerator r q.i)
          (evenClassGenerator r q.j) ^ (2 : ℤ) *
        hallTripleCommutator
          (evenClassGenerator r q.i)
          (evenClassGenerator r q.j)
          (evenClassGenerator r q.i)) ^
      leftSquareModulus r q = 1
  simpa [leftReplacementDerived, pairDerived,
    leftTripleDerived, first_elementary,
    nilpotent_four_bot
      (singleModulus r)] using
    square_pow_modulus r hpos q

theorem replacement_derived_modulus
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    pairReplacementDerived r q ^
      pairSquareModulus r q = 1 := by
  apply Subtype.ext
  change
    (hallCommutator
          (evenClassGenerator r q.i)
          (evenClassGenerator r q.j) ^ (2 : ℤ) *
        hallTripleCommutator
          (evenClassGenerator r q.i)
          (evenClassGenerator r q.j)
          (evenClassGenerator r q.j)) ^
      pairSquareModulus r q = 1
  simpa [pairReplacementDerived, pairDerived,
    pairTripleDerived, second_elementary,
    nilpotent_four_bot
      (singleModulus r)] using
    pair_square_modulus r hpos q

theorem triple_first_derived
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    tripleFirstDerived r q ^
      exceptionalResiduesModulus r q = 1 := by
  apply Subtype.ext
  exact triple_first_modulus r q

theorem triple_derived_modulus
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    tripleSecondDerived r q ^
      exceptionalResiduesModulus r q = 1 := by
  apply Subtype.ext
  exact triple_second_modulus r q

/-- The ordered weight-one part of equation (25).  It is indexed by the
canonical Hall weight-one order, whose ranks are the numerical generator
indices. -/
noncomputable def singleNormalProduct
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    EvenClassGroup r :=
  ((Finset.univ.sort fun i j :
      (standardHallFamily.{u} t 1).index => i ≤ j).map fun i =>
    let k :=
      lowHallRank.{u}
        ((lowWeightIndex.{u} t).symm i)
    evenClassGenerator r k ^ c.single k).prod

/-- The abelian commutator part of equation (25), using the replacement
factors `C²D` and `C²E`. -/
noncomputable def derivedNormalProduct
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    Derived r :=
  (∏ q : Pair t,
      pairDerived r q ^ c.pair q *
        leftReplacementDerived r q ^
          c.pairLeftSquare q *
        pairReplacementDerived r q ^
          c.pairRightSquare q) *
    ∏ q : Triple t,
      tripleFirstDerived r q ^ c.tripleFirst q *
        tripleSecondDerived r q ^ c.tripleSecond q

/-- Struik's equation-(25) normal word attached to an integral tuple. -/
noncomputable def exceptionalResidueCover
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    EvenClassGroup r :=
  singleNormalProduct.{u} r c *
    (derivedNormalProduct r c : EvenClassGroup r)

private theorem unreduced_pair_replacement
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t)
    (q : Pair t) :
    pairDerived r q ^ ELCoordi.alpha c q *
          leftTripleDerived r q ^ c.pairLeftSquare q *
          pairTripleDerived r q ^ c.pairRightSquare q =
      pairDerived r q ^ c.pair q *
          leftReplacementDerived r q ^
            c.pairLeftSquare q *
          pairReplacementDerived r q ^
            c.pairRightSquare q := by
  let C := pairDerived r q
  let D := leftTripleDerived r q
  let E := pairTripleDerived r q
  have hC :
      C ^ ELCoordi.alpha c q =
        C ^ c.pair q *
          (C ^ (2 : ℤ)) ^ c.pairLeftSquare q *
          (C ^ (2 : ℤ)) ^ c.pairRightSquare q := by
    rw [ELCoordi.alpha, zpow_add C, zpow_add C,
      zpow_mul, zpow_mul]
  rw [hC]
  simp only [leftReplacementDerived,
    pairReplacementDerived, C, mul_zpow]
  have hcomm :
      Commute
        ((pairDerived r q ^ (2 : ℤ)) ^
          c.pairRightSquare q)
        (leftTripleDerived r q ^
          c.pairLeftSquare q) :=
    Commute.all _ _
  simp only [mul_assoc]
  rw [hcomm.left_comm]

/-- The equation-(18) version of the abelian commutator block before the
triangular replacement `D,E ↦ C²D,C²E`. -/
noncomputable def unreducedDerivedProduct
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    Derived r :=
  (∏ q : Pair t,
      pairDerived r q ^ ELCoordi.alpha c q *
        leftTripleDerived r q ^ c.pairLeftSquare q *
        pairTripleDerived r q ^ c.pairRightSquare q) *
    ∏ q : Triple t,
      tripleFirstDerived r q ^ c.tripleFirst q *
        tripleSecondDerived r q ^ c.tripleSecond q

theorem unreduced_derived_normal
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    unreducedDerivedProduct r c =
      derivedNormalProduct r c := by
  unfold unreducedDerivedProduct derivedNormalProduct
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  exact unreduced_pair_replacement r c q

private theorem mapped_single_normal
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 1).collectedWeightProduct
          (n := 4) (exceptionalHallExponents c 1)) =
      singleNormalProduct.{u} r c := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  unfold singleNormalProduct
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  let j := (lowWeightIndex.{u} t).symm i
  have hij : lowWeightIndex.{u} t j = i :=
    (lowWeightIndex.{u} t).apply_symm_apply i
  rw [← hij]
  change rankedTruncationMap.{u} r
      (((standardHallFamily.{u} t 1).commutator
        (lowWeightIndex.{u} t j)
        |>.freeLowerTruncation (n := 4)) ^
          exceptionalHallExponents c 1
            (lowWeightIndex.{u} t j)) =
    _
  rw [map_zpow, exceptional_truncation_low]
  simp [exceptionalHallExponents, weightHallExponent,
    toGeneralResidues, j]

/-- Canonical weight-two Hall indices reindexed by numerical pairs. -/
noncomputable def weightTwoCoordinate (t : ℕ) :
    (standardHallFamily.{u} t 2).index ≃ Pair t :=
  (lowTwoIndex.{u} t).symm.trans
    (lowPairRank.{u} t)

/-- Canonical weight-three Hall indices reindexed by Struik's four
weight-three coordinate families. -/
noncomputable def weightCoordinateEquiv (t : ℕ) :
    (standardHallFamily.{u} t 3).index ≃
      WeightCoordinateIndex t :=
  (lowIndexEquiv.{u} t).symm.trans
    (lowCoordinateEquiv.{u} t)

private theorem mapped_pair_product
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 2).collectedWeightProduct
          (n := 4) (exceptionalHallExponents c 2)) =
      ((∏ q : Pair t,
          pairDerived r q ^
            ELCoordi.alpha c q) :
        Derived r) := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  let factor :
      (standardHallFamily.{u} t 2).index →
        Derived r :=
    fun i =>
      pairDerived r
          (weightTwoCoordinate.{u} t i) ^
        ELCoordi.alpha c
          (weightTwoCoordinate.{u} t i)
  have hfactor :
      ∀ i : (standardHallFamily.{u} t 2).index,
        rankedTruncationMap.{u} r
            (((standardHallFamily.{u} t 2).commutator i
              |>.freeLowerTruncation (n := 4)) ^
                exceptionalHallExponents c 2 i) =
          (factor i : EvenClassGroup r) := by
    intro i
    let q := (lowTwoIndex.{u} t).symm i
    have hi : lowTwoIndex.{u} t q = i :=
      (lowTwoIndex.{u} t).apply_symm_apply i
    rw [← hi, map_zpow, exceptional_ranked_truncation]
    simp [factor, weightTwoCoordinate,
      exceptionalHallExponents, weightTwoExponent,
      toGeneralResidues, pairDerived,
      lowPairRank, q]
    rfl
  have hlist :
      ((Finset.univ.sort fun i j :
          (standardHallFamily.{u} t 2).index => i ≤ j).map
        (fun i =>
          rankedTruncationMap.{u} r
            (((standardHallFamily.{u} t 2).commutator i
              |>.evalin_freelower_centtrunterm (n := 4)) ^
                exceptionalHallExponents c 2 i : _))).prod =
        (((Finset.univ.sort fun i j :
            (standardHallFamily.{u} t 2).index => i ≤ j).map
          factor).prod : Derived r) := by
    rw [SubmonoidClass.coe_list_prod]
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    simpa only [Subgroup.coe_zpow] using hfactor i
  rw [hlist]
  apply congrArg Subtype.val
  change
    ((Finset.univ.sort fun i j :
        (standardHallFamily.{u} t 2).index => i ≤ j).map factor).prod =
      ∏ q : Pair t,
        pairDerived r q ^
          ELCoordi.alpha c q
  calc
    _ = ∏ i, factor i := by
      rw [← List.prod_toFinset]
      · simp
      · exact Finset.sort_nodup _ _
    _ = _ := Fintype.prod_equiv
      (weightTwoCoordinate.{u} t) factor
      (fun q => pairDerived r q ^
        ELCoordi.alpha c q) (fun _ => rfl)

private noncomputable def weightDerivedFactor
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    WeightCoordinateIndex t → Derived r
  | .pairLeft q =>
      leftTripleDerived r q ^ c.pairLeftSquare q
  | .pairRight q =>
      pairTripleDerived r q ^ c.pairRightSquare q
  | .tripleFirst q =>
      tripleFirstDerived r q ^
        (c.tripleFirst q - c.tripleSecond q)
  | .tripleSecond q =>
      tripleHallDerived r q ^ c.tripleSecond q

private theorem derived_factor_prod
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    (∏ q : WeightCoordinateIndex t,
        weightDerivedFactor r c q) =
      (∏ q : Pair t,
          leftTripleDerived r q ^ c.pairLeftSquare q) *
        ((∏ q : Pair t,
            pairTripleDerived r q ^ c.pairRightSquare q) *
          ((∏ q : Triple t,
              tripleFirstDerived r q ^ c.tripleFirst q) *
            ∏ q : Triple t,
              tripleSecondDerived r q ^ c.tripleSecond q)) := by
  have hmixed :
      (∏ q : Triple t,
          tripleFirstDerived r q ^
            (c.tripleFirst q - c.tripleSecond q)) *
        (∏ q : Triple t,
          tripleHallDerived r q ^ c.tripleSecond q) =
      (∏ q : Triple t,
          tripleFirstDerived r q ^ c.tripleFirst q) *
        ∏ q : Triple t,
          tripleSecondDerived r q ^ c.tripleSecond q := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    rw [triple_second_derived]
    rw [zpow_sub, mul_zpow]
    group
  rw [← (weightCoordinateIndex t).symm.prod_comp
    (weightDerivedFactor r c)]
  simp only [Subgroup.lowerCentralSeries_one, Fintype.prod_sum_type]
  refine (congrArg (fun z =>
    ((∏ q : Pair t,
        leftTripleDerived r q ^ c.pairLeftSquare q) *
      ∏ q : Pair t,
        pairTripleDerived r q ^ c.pairRightSquare q) * z)
    hmixed).trans ?_
  exact mul_assoc _ _ _

private theorem mapped_coordinate_product
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    rankedTruncationMap.{u} r
        ((standardHallFamily.{u} t 3).collectedWeightProduct
          (n := 4) (exceptionalHallExponents c 3)) =
      ((∏ q : WeightCoordinateIndex t,
          weightDerivedFactor r c q) :
        Derived r) := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  let factor :
      (standardHallFamily.{u} t 3).index →
        Derived r :=
    fun i =>
      weightDerivedFactor r c
        (weightCoordinateEquiv.{u} t i)
  have hfactor :
      ∀ i : (standardHallFamily.{u} t 3).index,
        rankedTruncationMap.{u} r
            (((standardHallFamily.{u} t 3).commutator i
              |>.freeLowerTruncation (n := 4)) ^
                exceptionalHallExponents c 3 i) =
          (factor i : EvenClassGroup r) := by
    intro i
    let q := (lowIndexEquiv.{u} t).symm i
    have hi : lowIndexEquiv.{u} t q = i :=
      (lowIndexEquiv.{u} t).apply_symm_apply i
    rw [← hi, map_zpow, exceptional_ranked_low]
    cases hcoord :
        lowCoordinateEquiv.{u} t q with
    | pairLeft p =>
        have hq :
            q = (lowCoordinateEquiv.{u} t).symm
              (.pairLeft p) := by
          simpa only [Equiv.symm_apply_apply] using
            congrArg (lowCoordinateEquiv.{u} t).symm hcoord
        rw [hq]
        simp [factor, weightCoordinateEquiv,
          exceptionalHallExponents, weightThreeExponent,
          toGeneralResidues,
          weightDerivedFactor,
          leftTripleDerived,
          lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowWeight,
          rankedLowThree, lowThreeLeaves]
        rfl
    | pairRight p =>
        have hq :
            q = (lowCoordinateEquiv.{u} t).symm
              (.pairRight p) := by
          simpa only [Equiv.symm_apply_apply] using
            congrArg (lowCoordinateEquiv.{u} t).symm hcoord
        rw [hq]
        simp [factor, weightCoordinateEquiv,
          exceptionalHallExponents, weightThreeExponent,
          toGeneralResidues,
          weightDerivedFactor,
          pairTripleDerived,
          lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowWeight,
          rankedLowThree, lowThreeLeaves]
        rfl
    | tripleFirst p =>
        have hq :
            q = (lowCoordinateEquiv.{u} t).symm
              (.tripleFirst p) := by
          simpa only [Equiv.symm_apply_apply] using
            congrArg (lowCoordinateEquiv.{u} t).symm hcoord
        rw [hq]
        simp [factor, weightCoordinateEquiv,
          exceptionalHallExponents, weightThreeExponent,
          toGeneralResidues,
          weightDerivedFactor,
          tripleFirstDerived,
          lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowWeight,
          rankedLowThree, lowThreeLeaves,
          p.lt_jk]
        rfl
    | tripleSecond p =>
        have hq :
            q = (lowCoordinateEquiv.{u} t).symm
              (.tripleSecond p) := by
          simpa only [Equiv.symm_apply_apply] using
            congrArg (lowCoordinateEquiv.{u} t).symm hcoord
        rw [hq]
        simp [factor, weightCoordinateEquiv,
          exceptionalHallExponents, weightThreeExponent,
          toGeneralResidues,
          weightDerivedFactor,
          tripleHallDerived,
          lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowWeight,
          rankedLowThree, lowThreeLeaves,
          (not_lt_of_ge p.lt_jk.le)]
        rfl
  have hlist :
      ((Finset.univ.sort fun i j :
          (standardHallFamily.{u} t 3).index => i ≤ j).map
        (fun i =>
          rankedTruncationMap.{u} r
            (((standardHallFamily.{u} t 3).commutator i
              |>.evalin_freelower_centtrunterm (n := 4)) ^
                exceptionalHallExponents c 3 i : _))).prod =
        (((Finset.univ.sort fun i j :
            (standardHallFamily.{u} t 3).index => i ≤ j).map
          factor).prod : Derived r) := by
    rw [SubmonoidClass.coe_list_prod]
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    simpa only [Subgroup.coe_zpow] using hfactor i
  rw [hlist]
  apply congrArg Subtype.val
  change
    ((Finset.univ.sort fun i j :
        (standardHallFamily.{u} t 3).index => i ≤ j).map factor).prod =
      ∏ q : WeightCoordinateIndex t,
        weightDerivedFactor r c q
  calc
    _ = ∏ i, factor i := by
      rw [← List.prod_toFinset]
      · simp
      · exact Finset.sort_nodup _ _
    _ = _ := Fintype.prod_equiv
      (weightCoordinateEquiv.{u} t) factor
      (weightDerivedFactor r c) (fun _ => rfl)

private theorem mapped_derived_weights
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    rankedTruncationMap.{u} r
          ((standardHallFamily.{u} t 2).collectedWeightProduct
            (n := 4) (exceptionalHallExponents c 2)) *
        rankedTruncationMap.{u} r
          ((standardHallFamily.{u} t 3).collectedWeightProduct
            (n := 4) (exceptionalHallExponents c 3)) =
      (unreducedDerivedProduct r c : EvenClassGroup r) := by
  rw [mapped_pair_product,
    mapped_coordinate_product]
  change
    ((((∏ q : Pair t,
          pairDerived r q ^
            ELCoordi.alpha c q) *
        ∏ q : WeightCoordinateIndex t,
          weightDerivedFactor r c q) :
      Derived r) : EvenClassGroup r) =
        (unreducedDerivedProduct r c : EvenClassGroup r)
  apply congrArg Subtype.val
  rw [derived_factor_prod]
  unfold unreducedDerivedProduct
  simp only [Finset.prod_mul_distrib]
  ac_rfl

/-- The Hall-coordinate evaluator is exactly Struik's equation-(25)
normal word. -/
theorem integral_normal_word
    {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    integralCoordinateEval.{u} r c =
      exceptionalResidueCover.{u} r c := by
  unfold integralCoordinateEval exceptionalResidueCover
  rw [standard_weight_products,
    map_mul, map_mul, mapped_single_normal]
  rw [mul_assoc,
    mapped_derived_weights,
    unreduced_derived_normal]

/-- Every element has a Struik equation-(25) normal-word expression. -/
theorem normalWord_surjective
    {t : ℕ} (r : Fin t → ℕ) :
    Function.Surjective (exceptionalResidueCover.{u} r) := by
  intro x
  obtain ⟨c, hc⟩ :=
    integral_coordinate_surjective.{u} r x
  refine ⟨c, ?_⟩
  rw [← integral_normal_word]
  exact hc

private theorem generator_pow_modulus
    {t : ℕ} (r : Fin t → ℕ) (i : Fin t) :
    evenClassGenerator r i ^ singleModulus r i = 1 :=
  nilpotent_cyclic_generator
    (singleModulus r) 4 i

/-- The equation-(25) word depends only on the residue classes prescribed
in Theorem 4. -/
theorem normal_mod
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    {c d : ELCoordi t}
    (hcd : ERMod r c d) :
    exceptionalResidueCover.{u} r c =
      exceptionalResidueCover.{u} r d := by
  have hsingle :
      singleNormalProduct.{u} r c =
        singleNormalProduct r d := by
    unfold singleNormalProduct
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    dsimp only
    apply zpow_mod_pow
      (evenClassGenerator r
        (lowHallRank.{u}
          ((lowWeightIndex.{u} t).symm i)))
      (hcd.single
        (lowHallRank.{u}
          ((lowWeightIndex.{u} t).symm i)))
    exact generator_pow_modulus r _
  have hpair :
      (∏ q : Pair t,
          pairDerived r q ^ c.pair q *
            leftReplacementDerived r q ^
              c.pairLeftSquare q *
            pairReplacementDerived r q ^
              c.pairRightSquare q) =
        ∏ q : Pair t,
          pairDerived r q ^ d.pair q *
            leftReplacementDerived r q ^
              d.pairLeftSquare q *
            pairReplacementDerived r q ^
              d.pairRightSquare q := by
    apply Finset.prod_congr rfl
    intro q _
    rw [zpow_mod_pow
        (pairDerived r q) (hcd.pair q)
        (pair_derived_modulus r hpos q),
      zpow_mod_pow
        (leftReplacementDerived r q)
        (hcd.pairLeftSquare q)
        (pair_replacement_derived
          r hpos q),
      zpow_mod_pow
        (pairReplacementDerived r q)
        (hcd.pairRightSquare q)
        (replacement_derived_modulus
          r hpos q)]
  have htriple :
      (∏ q : Triple t,
          tripleFirstDerived r q ^ c.tripleFirst q *
            tripleSecondDerived r q ^ c.tripleSecond q) =
        ∏ q : Triple t,
          tripleFirstDerived r q ^ d.tripleFirst q *
            tripleSecondDerived r q ^ d.tripleSecond q := by
    apply Finset.prod_congr rfl
    intro q _
    rw [zpow_mod_pow
        (tripleFirstDerived r q) (hcd.tripleFirst q)
        (triple_first_derived r q),
      zpow_mod_pow
        (tripleSecondDerived r q) (hcd.tripleSecond q)
        (triple_derived_modulus r q)]
  unfold exceptionalResidueCover derivedNormalProduct
  rw [hsingle, hpair, htriple]

end P1960
end Struik
