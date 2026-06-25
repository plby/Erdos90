import Submission.Group.NilpotentProducts.GeneralResidueCover
import Submission.Group.NilpotentProducts.GeneralModel
import Submission.Group.NilpotentProducts.LowWeightReindexing
import Submission.Group.NilpotentProducts.ModulusPermutation
import Submission.Group.NilpotentProducts.GeneralModelSurjectivity
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality bookkeeping for Struik's Theorem 2

This file reduces the finite-order uniqueness statement to the combinatorial
identity matching Hall factors of weights at most three with the coordinate
positions in equation (18).
-/

namespace Struik
namespace P1960

open Submission

universe u

/-- The explicit arbitrary-rank residue tuple as a product of its six
dependent coordinate families. -/
def generalResiduesPi
    {t : ℕ} (order : Fin t → ℕ) :
    GeneralResidues order ≃
      (∀ i : Fin t, ZMod (order i)) ×
      (∀ q : Pair t, ZMod (generalPairModulus order q)) ×
      (∀ q : Pair t, ZMod (generalPairModulus order q)) ×
      (∀ q : Pair t, ZMod (generalPairModulus order q)) ×
      (∀ q : Triple t,
        ZMod (generalResiduesModulus order q)) ×
      (∀ q : Triple t,
        ZMod (generalResiduesModulus order q)) where
  toFun c :=
    ⟨c.single, c.pair, c.pairLeft, c.pairRight,
      c.tripleFirst, c.tripleSecond⟩
  invFun c := {
    single := c.1
    pair := c.2.1
    pairLeft := c.2.2.1
    pairRight := c.2.2.2.1
    tripleFirst := c.2.2.2.2.1
    tripleSecond := c.2.2.2.2.2 }
  left_inv c := by ext <;> rfl
  right_inv c := by
    rcases c with ⟨single, pair, pairLeft, pairRight,
      tripleFirst, tripleSecond⟩
    rfl

/-- Cardinality of Struik's explicit arbitrary-rank residue tuple. -/
theorem generalResidues_card
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card (GeneralResidues order) =
      (∏ i : Fin t, order i) *
        ((∏ q : Pair t,
            generalPairModulus order q) *
          ((∏ q : Pair t,
              generalPairModulus order q) *
            ((∏ q : Pair t,
                generalPairModulus order q) *
              ((∏ q : Triple t,
                  generalResiduesModulus order q) *
                ∏ q : Triple t,
                  generalResiduesModulus order q)))) := by
  rw [Nat.card_congr (generalResiduesPi order)]
  simp only [Nat.card_prod, Nat.card_pi, Nat.card_zmod]

/-- Cardinality of the arbitrary-rank Hall residue cover. -/
theorem residues_up_card
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card (ResiduesUpThree.{u} order) =
      (∏ i : Fin t, order i) *
        ((∏ q : LowPairIndex.{u} t,
            lowPairOrder order q) *
          ∏ q : LowThreeIndex.{u} t,
            lowThreeOrder order q) := by
  simp only [ResiduesUpThree, Nat.card_prod, Nat.card_pi,
    Nat.card_zmod]
  rw [← (lowWeightIndex.{u} t).prod_comp
      (fun i => standardFactorOrder order i),
    ← (lowTwoIndex.{u} t).prod_comp
      (fun i => standardFactorOrder order i),
    ← (lowIndexEquiv.{u} t).prod_comp
      (fun i => standardFactorOrder order i)]
  simp only [standard_order_low,
    standard_low_two,
    standard_low_three]
  ac_rfl

/-- Positive generator orders make the arbitrary-rank Hall residue cover
finite and nonempty. -/
theorem residues_up_ne
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, 0 < order i) :
    Nat.card (ResiduesUpThree.{u} order) ≠ 0 := by
  simp only [ResiduesUpThree, Nat.card_prod, Nat.card_pi,
    Nat.card_zmod]
  apply Nat.mul_ne_zero
  · exact (Finset.prod_pos fun i _ =>
      standard_order_pos order horder i).ne'
  · apply Nat.mul_ne_zero
    · exact (Finset.prod_pos fun i _ =>
        standard_order_pos order horder i).ne'
    · exact (Finset.prod_pos fun i _ =>
        standard_order_pos order horder i).ne'

/-- Reordering generator positions by Hall rank does not change the total
product of their orders. -/
theorem prod_ranked_order
    {t : ℕ} (order : Fin t → ℕ) :
    (∏ i : Fin t, hallRankedOrder.{u} order i) =
      ∏ i : Fin t, order i := by
  rw [← (lowWeightRank.{u} t).prod_comp
    (hallRankedOrder.{u} order)]
  simp [hallRankedOrder]

/-- The product of all weight-three coordinate moduli splits into the two
pair and two triple families. -/
theorem coordinate_modulus_prod
    {t : ℕ} (order : Fin t → ℕ) :
    (∏ q : WeightCoordinateIndex t,
        weightCoordinateModulus order q) =
      (∏ q : Pair t, generalPairModulus order q) *
        ((∏ q : Pair t, generalPairModulus order q) *
          ((∏ q : Triple t,
              generalResiduesModulus order q) *
            ∏ q : Triple t,
              generalResiduesModulus order q)) := by
  rw [← (weightCoordinateIndex t).symm.prod_comp
    (fun q => weightCoordinateModulus order q)]
  simp [weightCoordinateIndex,
    weightCoordinateModulus, mul_assoc]

/-- The Hall residue cover and equation-(18) residues have equal
cardinality after numbering generators by increasing Hall-atom rank. -/
theorem residues_up_ranked
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card (ResiduesUpThree.{u} order) =
      Nat.card
        (GeneralResidues (hallRankedOrder.{u} order)) := by
  rw [residues_up_card,
    generalResidues_card,
    prod_ranked_order]
  rw [← coordinate_modulus_prod]
  rw [← (lowPairRank.{u} t).prod_comp
      (fun q =>
        generalPairModulus (hallRankedOrder.{u} order) q),
    ← (lowCoordinateEquiv.{u} t).prod_comp
      (fun q =>
        weightCoordinateModulus
          (hallRankedOrder.{u} order) q)]
  simp only [low_pair_rank,
    low_order_coordinate]

private theorem pair_modulus_powerset
    {t : ℕ} (order : Fin t → ℕ) :
    (∏ q : Pair t, generalPairModulus order q) =
      ∏ s : Set.powersetCard (Fin t) 2, s.val.gcd order := by
  rw [← (pairPowersetEquiv t).prod_comp
    (fun s => s.val.gcd order)]
  simp

private theorem triple_modulus_powerset
    {t : ℕ} (order : Fin t → ℕ) :
    (∏ q : Triple t, generalResiduesModulus order q) =
      ∏ s : Set.powersetCard (Fin t) 3, s.val.gcd order := by
  rw [← (triplePowersetEquiv t).prod_comp
    (fun s => s.val.gcd order)]
  simp

/-- Permuting the generator orders by Hall rank leaves the total
equation-(18) residue cardinality unchanged. -/
theorem general_residues_ranked
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card
        (GeneralResidues (hallRankedOrder.{u} order)) =
      Nat.card (GeneralResidues order) := by
  have hpair :
      (∏ q : Pair t,
          generalPairModulus (hallRankedOrder.{u} order) q) =
        ∏ q : Pair t,
          generalPairModulus order q := by
    calc
      (∏ q : Pair t,
          generalPairModulus (hallRankedOrder.{u} order) q) =
          ∏ s : Set.powersetCard (Fin t) 2,
            s.val.gcd (hallRankedOrder.{u} order) :=
        pair_modulus_powerset
          (hallRankedOrder.{u} order)
      _ = ∏ s : Set.powersetCard (Fin t) 2,
            s.val.gcd order := by
        symm
        simpa [hallRankedOrder, Function.comp_def] using
          powerset_gcd_comp
            (lowWeightRank.{u} t) 2
            (hallRankedOrder.{u} order)
      _ = ∏ q : Pair t,
            generalPairModulus order q :=
        (pair_modulus_powerset order).symm
  have htriple :
      (∏ q : Triple t,
          generalResiduesModulus (hallRankedOrder.{u} order) q) =
        ∏ q : Triple t,
          generalResiduesModulus order q := by
    calc
      (∏ q : Triple t,
          generalResiduesModulus (hallRankedOrder.{u} order) q) =
          ∏ s : Set.powersetCard (Fin t) 3,
            s.val.gcd (hallRankedOrder.{u} order) :=
        triple_modulus_powerset
          (hallRankedOrder.{u} order)
      _ = ∏ s : Set.powersetCard (Fin t) 3,
            s.val.gcd order := by
        symm
        simpa [hallRankedOrder, Function.comp_def] using
          powerset_gcd_comp
            (lowWeightRank.{u} t) 3
            (hallRankedOrder.{u} order)
      _ = ∏ q : Triple t,
            generalResiduesModulus order q :=
        (triple_modulus_powerset order).symm
  rw [generalResidues_card,
    generalResidues_card,
    prod_ranked_order, hpair, htriple]

/-- The Hall residue cover and the original equation-(18) residue tuple
have equal cardinality. -/
theorem up_card_general
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card (ResiduesUpThree.{u} order) =
      Nat.card (GeneralResidues order) := by
  calc
    Nat.card (ResiduesUpThree.{u} order) =
        Nat.card
          (GeneralResidues (hallRankedOrder.{u} order)) :=
      residues_up_ranked order
    _ = Nat.card (GeneralResidues order) :=
      general_residues_ranked order

theorem residues_up_general
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Nat.card (ResiduesUpThree.{u} order) =
      Nat.card (GeneralResidueGroup order horder) := by
  calc
    Nat.card (ResiduesUpThree.{u} order) =
        Nat.card (GeneralResidues order) :=
      up_card_general order
    _ = Nat.card (GeneralResidueGroup order horder) :=
      (Nat.card_congr
        (generalResidueEquiv order horder)).symm

/-- **Struik's Theorem 2, uniqueness form.**  For any finite family of
finite odd cyclic groups, the canonical equation-(18) model map is
bijective. -/
theorem nilpotent_residues_bijective
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i)) :
    Function.Bijective
      (nilpotentGeneralResidues
        order (fun i => AOrd.of_odd (hodd i))) := by
  let horder : ∀ i, AOrd (order i) :=
    fun i => AOrd.of_odd (hodd i)
  have horderPos : ∀ i, 0 < order i :=
    fun i => (hodd i).pos
  have hHallSurjective :
      Function.Surjective
        (generalHallResidue.{0} order) :=
    general_residue_surjective order horder
  letI : Finite (ResiduesUpThree.{0} order) :=
    Nat.finite_of_card_ne_zero
      (residues_up_ne order horderPos)
  letI : Finite (NilpotentCyclicProduct order 4) :=
    Finite.of_surjective
      (generalHallResidue.{0} order) hHallSurjective
  have hsourceLeCover :
      Nat.card (NilpotentCyclicProduct order 4) ≤
        Nat.card (ResiduesUpThree.{0} order) :=
    Nat.card_le_card_of_surjective
      (generalHallResidue.{0} order) hHallSurjective
  have hcard :
      Nat.card (NilpotentCyclicProduct order 4) ≤
        Nat.card (GeneralResidueGroup order horder) :=
    hsourceLeCover.trans_eq
      (residues_up_general
        order horder)
  exact
    (nilpotent_general_residues
      order horder).bijective_of_nat_card_le hcard

/-- **Struik's Theorem 2.**  The fourth nilpotent product of a finite
family of finite odd cyclic groups is in canonical bijection with the
equation-(18) residue coordinates. -/
noncomputable def generalCardinalityResidue
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i)) :
    NilpotentCyclicProduct order 4 ≃
      GeneralResidues order :=
  (Equiv.ofBijective
      (nilpotentGeneralResidues
        order (fun i => AOrd.of_odd (hodd i)))
      (nilpotent_residues_bijective
        order hodd)).trans
    (generalResidueEquiv order
      (fun i => AOrd.of_odd (hodd i)))

end P1960
end Struik
