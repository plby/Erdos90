import Submission.Group.NilpotentProducts.LowWeightBasis


/-!
# Reindexing low-weight Hall factors by equation-(18) coordinate positions

The canonical Hall order on atoms is implementation-dependent.  We first
replace each generator position by its rank in that order.  Weight-two Hall
factors then become increasing pairs, while weight-three Hall factors split
into the two repeated-pair and two distinct-triple families in Struik's
normal form.
-/

namespace Struik
namespace P1960

universe u

/-- Hall-oriented pairs, expressed in numeric Hall-rank order. -/
noncomputable def lowPairRank (t : ℕ) :
    LowPairIndex.{u} t ≃ Pair t where
  toFun q :=
    ⟨lowHallRank q.i, lowHallRank q.j,
      (low_hall_rank q.i q.j).2 q.lt⟩
  invFun q := {
    i := (lowWeightRank.{u} t).symm q.i
    j := (lowWeightRank.{u} t).symm q.j
    lt := by
      apply (low_hall_rank _ _).1
      change
        lowWeightRank.{u} t
            ((lowWeightRank.{u} t).symm q.i) <
          lowWeightRank.{u} t
            ((lowWeightRank.{u} t).symm q.j)
      simpa using q.lt }
  left_inv q := by
    ext <;> simp
  right_inv q := by
    ext <;> simp

/-- Numeric triples satisfying the weight-three Hall admissibility
condition. -/
abbrev RankedLowIndex (t : ℕ) :=
  {p : Fin t × Fin t × Fin t // p.1 < p.2.1 ∧ p.1 ≤ p.2.2}

/-- Weight-three Hall indices, expressed in numeric Hall-rank order. -/
noncomputable def lowRankEquiv (t : ℕ) :
    LowThreeIndex.{u} t ≃ RankedLowIndex t where
  toFun q :=
    ⟨(lowHallRank q.1.1,
      lowHallRank q.1.2.1,
      lowHallRank q.1.2.2),
      (low_hall_rank _ _).2 q.2.1,
      (low_weight_rank _ _).2 q.2.2⟩
  invFun q :=
    ⟨((lowWeightRank.{u} t).symm q.1.1,
      (lowWeightRank.{u} t).symm q.1.2.1,
      (lowWeightRank.{u} t).symm q.1.2.2), by
      constructor
      · apply (low_hall_rank _ _).1
        change
          lowWeightRank.{u} t
              ((lowWeightRank.{u} t).symm q.1.1) <
            lowWeightRank.{u} t
              ((lowWeightRank.{u} t).symm q.1.2.1)
        simpa using q.2.1
      · apply (low_weight_rank _ _).1
        change
          lowWeightRank.{u} t
              ((lowWeightRank.{u} t).symm q.1.1) ≤
            lowWeightRank.{u} t
              ((lowWeightRank.{u} t).symm q.1.2.2)
        simpa using q.2.2⟩
  left_inv q := by
    apply Subtype.ext
    ext <;> simp
  right_inv q := by
    apply Subtype.ext
    ext <;> simp

/-- The four weight-three coordinate families in equation (18). -/
inductive WeightCoordinateIndex (t : ℕ)
  | pairLeft : Pair t → WeightCoordinateIndex t
  | pairRight : Pair t → WeightCoordinateIndex t
  | tripleFirst : Triple t → WeightCoordinateIndex t
  | tripleSecond : Triple t → WeightCoordinateIndex t
  deriving DecidableEq, Fintype

/-- The four constructors as two pair families followed by two triple
families. -/
def weightCoordinateIndex (t : ℕ) :
    WeightCoordinateIndex t ≃
      (Pair t ⊕ Pair t) ⊕
        (Triple t ⊕ Triple t) where
  toFun
    | .pairLeft q => .inl (.inl q)
    | .pairRight q => .inl (.inr q)
    | .tripleFirst q => .inr (.inl q)
    | .tripleSecond q => .inr (.inr q)
  invFun
    | .inl (.inl q) => .pairLeft q
    | .inl (.inr q) => .pairRight q
    | .inr (.inl q) => .tripleFirst q
    | .inr (.inr q) => .tripleSecond q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    rcases q with (q | q) <;> rcases q with (q | q) <;> rfl

/-- Split a numeric Hall-admissible triple into Struik's four coordinate
families. -/
def rankedLowThree
    {t : ℕ} (q : RankedLowIndex t) :
    WeightCoordinateIndex t :=
  if hca : q.1.2.2 = q.1.1 then
    .pairLeft ⟨q.1.1, q.1.2.1, q.2.1⟩
  else if hcb : q.1.2.2 = q.1.2.1 then
    .pairRight ⟨q.1.1, q.1.2.1, q.2.1⟩
  else if hbc : q.1.2.1 < q.1.2.2 then
    .tripleFirst
      ⟨q.1.1, q.1.2.1, q.1.2.2, q.2.1, hbc⟩
  else
    .tripleSecond
      ⟨q.1.1, q.1.2.2, q.1.2.1,
        lt_of_le_of_ne q.2.2 (Ne.symm hca),
        lt_of_le_of_ne (le_of_not_gt hbc) hcb⟩

/-- Reassemble a weight-three coordinate position as a Hall-admissible
numeric triple. -/
def rankedLowWeight
    {t : ℕ} :
    WeightCoordinateIndex t →
      RankedLowIndex t
  | .pairLeft q => ⟨(q.i, q.j, q.i), q.lt, le_rfl⟩
  | .pairRight q => ⟨(q.i, q.j, q.j), q.lt, q.lt.le⟩
  | .tripleFirst q =>
      ⟨(q.i, q.j, q.k), q.lt_ij, q.lt_ij.le.trans q.lt_jk.le⟩
  | .tripleSecond q =>
      ⟨(q.i, q.k, q.j), q.lt_ij.trans q.lt_jk, q.lt_ij.le⟩

/-- Weight-three Hall factors are exactly the four coordinate families in
equation (18). -/
def rankedLowCoordinate (t : ℕ) :
    RankedLowIndex t ≃ WeightCoordinateIndex t where
  toFun := rankedLowThree
  invFun := rankedLowWeight
  left_inv q := by
    rcases q with ⟨⟨a, b, c⟩, hab, hac⟩
    apply Subtype.ext
    by_cases hca : c = a
    · subst c
      simp [rankedLowThree,
        rankedLowWeight]
    · by_cases hcb : c = b
      · subst c
        simp [rankedLowThree,
          rankedLowWeight, hca]
      · by_cases hbc : b < c
        · simp [rankedLowThree,
            rankedLowWeight, hca, hcb, hbc]
        · simp [rankedLowThree,
            rankedLowWeight, hca, hcb, hbc]
  right_inv q := by
    cases q with
    | pairLeft q =>
        rcases q with ⟨a, b, hab⟩
        simp [rankedLowThree,
          rankedLowWeight]
    | pairRight q =>
        rcases q with ⟨a, b, hab⟩
        simp [rankedLowThree,
          rankedLowWeight, ne_of_gt hab]
    | tripleFirst q =>
        rcases q with ⟨a, b, c, hab, hbc⟩
        simp [rankedLowThree,
          rankedLowWeight,
          ne_of_gt hbc, ne_of_gt (hab.trans hbc), hbc]
    | tripleSecond q =>
        rcases q with ⟨a, b, c, hab, hbc⟩
        simp [rankedLowThree,
          rankedLowWeight,
          ne_of_gt hab, ne_of_lt hbc,
          not_lt_of_ge hbc.le]

/-- The final reindexing of weight-three Hall factors by equation-(18)
coordinate positions. -/
noncomputable def lowCoordinateEquiv (t : ℕ) :
    LowThreeIndex.{u} t ≃ WeightCoordinateIndex t :=
  (lowRankEquiv.{u} t).trans
    (rankedLowCoordinate t)

/-- The generator orders read in increasing Hall-atom rank. -/
noncomputable def hallRankedOrder
    {t : ℕ} (order : Fin t → ℕ) : Fin t → ℕ :=
  fun i => order ((lowWeightRank.{u} t).symm i)

/-- The modulus carried by one of the four weight-three coordinate
families. -/
def weightCoordinateModulus
    {t : ℕ} (order : Fin t → ℕ) :
    WeightCoordinateIndex t → ℕ
  | .pairLeft q | .pairRight q =>
      generalPairModulus order q
  | .tripleFirst q | .tripleSecond q =>
      generalResiduesModulus order q

@[simp] theorem low_pair_rank
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowPairIndex.{u} t) :
    generalPairModulus (hallRankedOrder.{u} order)
        (lowPairRank.{u} t q) =
      lowPairOrder order q := by
  simp [generalPairModulus, hallRankedOrder,
    lowPairRank, lowPairOrder]

@[simp] theorem low_order_coordinate
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowThreeIndex.{u} t) :
    weightCoordinateModulus (hallRankedOrder.{u} order)
        (lowCoordinateEquiv.{u} t q) =
      lowThreeOrder order q := by
  rcases q with ⟨⟨i, j, k⟩, hij, hik⟩
  by_cases hki : k = i
  · subst k
    simp [lowCoordinateEquiv, lowRankEquiv,
      rankedLowCoordinate,
      rankedLowThree,
            weightCoordinateModulus, hallRankedOrder,
      lowThreeOrder, lowThreeLeaves,
      generalPairModulus]
  · have hrki :
    lowHallRank.{u} k ≠ lowHallRank.{u} i :=
      fun h => hki ((low_rank_bijective.{u} t).1 h)
    by_cases hkj : k = j
    · subst k
      simp [lowCoordinateEquiv, lowRankEquiv,
        rankedLowCoordinate,
        rankedLowThree,
                weightCoordinateModulus, hallRankedOrder,
        lowThreeOrder, lowThreeLeaves,
        generalPairModulus, hrki]
    · have hrkj :
          lowHallRank.{u} k ≠ lowHallRank.{u} j :=
        fun h => hkj ((low_rank_bijective.{u} t).1 h)
      by_cases hjk :
          lowHallRank.{u} j < lowHallRank.{u} k
      · simp [lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowThree,
                    weightCoordinateModulus, hallRankedOrder,
          lowThreeOrder, lowThreeLeaves,
          generalResiduesModulus, hrki, hrkj, hjk]
      · simp [lowCoordinateEquiv, lowRankEquiv,
          rankedLowCoordinate,
          rankedLowThree,
                    weightCoordinateModulus, hallRankedOrder,
          lowThreeOrder, lowThreeLeaves,
          generalResiduesModulus, hrki, hrkj, hjk,
          Nat.gcd_comm, Nat.gcd_left_comm]

end P1960
end Struik
