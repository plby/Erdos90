import Towers.Group.NilpotentProducts.RankResidueCover
import Mathlib.Tactic.FinCases

/-!
# Cardinality and uniqueness in Struik's Theorem 1

For three finite odd cyclic factors, the finite Hall-residue cover and the
fourteen equation-(18) coordinates have the same cardinality.  The canonical
surjection between `F/F₄` and the coordinate group is therefore bijective.
-/

namespace Struik
namespace P1960

open Towers

universe u

/-- The modulus carried by each of the fourteen named equation-(18)
coordinates. -/
def basisModulus
    (α₁ α₂ α₃ : ℕ) :
    BasisIndex → ℕ
  | .c1 => α₁
  | .c2 => α₂
  | .c3 => α₃
  | .c12 | .c121 | .c122 => modulus12 α₁ α₂
  | .c13 | .c131 | .c133 => modulus13 α₁ α₃
  | .c23 | .c232 | .c233 => modulus23 α₂ α₃
  | .c123 | .c231 => modulus123 α₁ α₂ α₃

/-- Read a residue tuple as a dependent function on the fourteen basis
positions. -/
def residuesToPi
    (α₁ α₂ α₃ : ℕ)
    (c : RankThreeResidues α₁ α₂ α₃) :
    ∀ i : BasisIndex,
      ZMod (basisModulus α₁ α₂ α₃ i)
  | .c1 => c.c1
  | .c2 => c.c2
  | .c3 => c.c3
  | .c12 => c.c12
  | .c13 => c.c13
  | .c23 => c.c23
  | .c121 => c.c121
  | .c131 => c.c131
  | .c232 => c.c232
  | .c122 => c.c122
  | .c133 => c.c133
  | .c233 => c.c233
  | .c123 => c.c123
  | .c231 => c.c231

/-- Reassemble the fourteen dependent coordinates into Struik's residue
tuple. -/
def residuesOfPi
    (α₁ α₂ α₃ : ℕ)
    (c : ∀ i : BasisIndex,
      ZMod (basisModulus α₁ α₂ α₃ i)) :
    RankThreeResidues α₁ α₂ α₃ where
  c1 := c .c1
  c2 := c .c2
  c3 := c .c3
  c12 := c .c12
  c13 := c .c13
  c23 := c .c23
  c121 := c .c121
  c131 := c .c131
  c232 := c .c232
  c122 := c .c122
  c133 := c .c133
  c233 := c .c233
  c123 := c .c123
  c231 := c .c231

/-- The explicit residue structure is exactly the dependent product of its
fourteen coordinate moduli. -/
def cardinalityResiduesPi
    (α₁ α₂ α₃ : ℕ) :
    RankThreeResidues α₁ α₂ α₃ ≃
      ∀ i : BasisIndex,
        ZMod (basisModulus α₁ α₂ α₃ i) where
  toFun := residuesToPi α₁ α₂ α₃
  invFun := residuesOfPi α₁ α₂ α₃
  left_inv c := by ext <;> rfl
  right_inv c := by
    funext i
    cases i <;> rfl

/-- Cardinality of the fourteen explicit residue sets. -/
theorem rank_cardinality_residues
    (α₁ α₂ α₃ : ℕ) :
    Nat.card (RankThreeResidues α₁ α₂ α₃) =
      ∏ i : BasisIndex,
        basisModulus α₁ α₂ α₃ i := by
  rw [Nat.card_congr (cardinalityResiduesPi α₁ α₂ α₃),
    Nat.card_pi]
  simp

/-- Cardinality of the three blocks of rank-three Hall residues. -/
theorem rank_residues_card
    (order : Fin 3 → ℕ) :
    Nat.card (RankHallResidues.{u} order) =
      (∏ i : Fin 3, order i) *
        ((∏ i : RankTwoIndex,
            rankTwoOrder order i) *
          ∏ i : RankThreeIndex,
            rankThreeOrder order i) := by
  simp only [RankHallResidues, Nat.card_prod, Nat.card_pi,
    Nat.card_zmod]
  rw [← (rankThreeIndex.{u}).prod_comp
      (fun i => standardFactorOrder order i),
    ← (rankTwoIndex.{u}).prod_comp
      (fun i => standardFactorOrder order i),
    ← (rankIndexEquiv.{u}).prod_comp
      (fun i => standardFactorOrder order i)]
  simp

/-- Positive generator orders make the Hall residue cover finite. -/
theorem rank_residues_ne
    (order : Fin 3 → ℕ)
    (horder : ∀ i, 0 < order i) :
    Nat.card (RankHallResidues.{u} order) ≠ 0 := by
  simp only [RankHallResidues, Nat.card_prod, Nat.card_pi,
    Nat.card_zmod]
  apply Nat.mul_ne_zero
  · exact (Finset.prod_pos fun i _ =>
      standard_order_pos order horder i).ne'
  · apply Nat.mul_ne_zero
    · exact (Finset.prod_pos fun i _ =>
        standard_order_pos order horder i).ne'
    · exact (Finset.prod_pos fun i _ =>
        standard_order_pos order horder i).ne'

private theorem univ_fin_three :
    (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  ext i
  fin_cases i <;> simp

private theorem univ_two_index :
    (Finset.univ : Finset RankTwoIndex) =
      {.c12, .c13, .c23} := by
  ext i
  cases i <;> simp

private theorem univ_rank_index :
    (Finset.univ : Finset RankThreeIndex) =
      {.c121, .c122, .c123, .c131, .c132, .c133, .c232, .c233} := by
  ext i
  cases i <;> simp

private theorem univ_general_index :
    (Finset.univ : Finset BasisIndex) =
      {.c1, .c2, .c3, .c12, .c13, .c23, .c121, .c131, .c232,
        .c122, .c133, .c233, .c123, .c231} := by
  ext i
  cases i <;> simp

/-- For the three orders of Theorem 1, the Hall cover and the fourteen
residue coordinates have equal cardinality. -/
theorem rank_residues_odd
    (α₁ α₂ α₃ : ℕ) :
    Nat.card
        (RankHallResidues.{u}
          (orders α₁ α₂ α₃)) =
      Nat.card (RankThreeResidues α₁ α₂ α₃) := by
  rw [rank_residues_card, rank_cardinality_residues]
  rw [show (∏ i : Fin 3, orders α₁ α₂ α₃ i) =
      ∏ i ∈ ({0, 1, 2} : Finset (Fin 3)),
        orders α₁ α₂ α₃ i by
      rw [← univ_fin_three],
    show (∏ i : RankTwoIndex,
        rankTwoOrder (orders α₁ α₂ α₃) i) =
      ∏ i ∈
          ({.c12, .c13, .c23} :
            Finset RankTwoIndex),
        rankTwoOrder (orders α₁ α₂ α₃) i by
      rw [← univ_two_index],
    show (∏ i : RankThreeIndex,
        rankThreeOrder (orders α₁ α₂ α₃) i) =
      ∏ i ∈
          ({.c121, .c122, .c123, .c131, .c132, .c133, .c232,
            .c233} : Finset RankThreeIndex),
        rankThreeOrder (orders α₁ α₂ α₃) i by
      rw [← univ_rank_index],
    show (∏ i : BasisIndex,
        basisModulus α₁ α₂ α₃ i) =
      ∏ i ∈
          ({.c1, .c2, .c3, .c12, .c13, .c23, .c121, .c131,
            .c232, .c122, .c133, .c233, .c123, .c231} :
            Finset BasisIndex),
        basisModulus α₁ α₂ α₃ i by
      rw [← univ_general_index]]
  simp [basisModulus,
    modulus12, modulus13, modulus23,
    modulus123, rankTwoOrder,
    rankThreeOrder]
  ac_rfl

/-- The Hall cover also has the same cardinality as the quotient coordinate
group itself. -/
theorem rank_residues_general
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Nat.card
        (RankHallResidues.{u}
          (orders α₁ α₂ α₃)) =
      Nat.card
        (RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) := by
  calc
    Nat.card
        (RankHallResidues.{u}
          (orders α₁ α₂ α₃)) =
        Nat.card (RankThreeResidues α₁ α₂ α₃) :=
      rank_residues_odd
        α₁ α₂ α₃
    _ = Nat.card
          (RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) :=
      (Nat.card_congr
        (rankThreeResidues α₁ α₂ α₃ hα₁ hα₂ hα₃)).symm

/-- **Struik's Theorem 1, uniqueness form.**  For three finite odd cyclic
factors, the canonical map from `F/F₄` to the fourteen-coordinate model is
bijective. -/
theorem odd_residues_bijective
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : Odd α₁)
    (hα₂ : Odd α₂)
    (hα₃ : Odd α₃) :
    Function.Bijective
      (nilpotentOddResidues
        α₁ α₂ α₃ (AOrd.of_odd hα₁)
          (AOrd.of_odd hα₂)
          (AOrd.of_odd hα₃)) := by
  let order := orders α₁ α₂ α₃
  let h₁ : AOrd α₁ := AOrd.of_odd hα₁
  let h₂ : AOrd α₂ := AOrd.of_odd hα₂
  let h₃ : AOrd α₃ := AOrd.of_odd hα₃
  have horder : ∀ i, AOrd (order i) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃
  have horderPos : ∀ i, 0 < order i := by
    intro i
    fin_cases i
    · exact hα₁.pos
    · exact hα₂.pos
    · exact hα₃.pos
  have hHallSurjective :
      Function.Surjective
        (rankResidueEval.{0} order) :=
    rank_residue_surjective order horder
  letI : Finite (RankHallResidues.{0} order) :=
    Nat.finite_of_card_ne_zero
      (rank_residues_ne order horderPos)
  letI : Finite (NilpotentCyclicProduct order 4) :=
    Finite.of_surjective
      (rankResidueEval.{0} order) hHallSurjective
  have hsourceLeCover :
      Nat.card (NilpotentCyclicProduct order 4) ≤
        Nat.card (RankHallResidues.{0} order) :=
    Nat.card_le_card_of_surjective
      (rankResidueEval.{0} order) hHallSurjective
  have hcard :
      Nat.card (NilpotentCyclicProduct order 4) ≤
        Nat.card (RankResiduesResidue α₁ α₂ α₃ h₁ h₂ h₃) := by
    exact hsourceLeCover.trans_eq
      (rank_residues_general
        α₁ α₂ α₃ h₁ h₂ h₃)
  exact
    (nilpotent_odd_residues
      α₁ α₂ α₃ h₁ h₂ h₃).bijective_of_nat_card_le hcard

/-- **Struik's Theorem 1.**  Elements of the fourth nilpotent product of
three finite odd cyclic groups are in canonical bijection with the fourteen
residue coordinates listed in the paper. -/
noncomputable def rankCardinalityResidue
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : Odd α₁)
    (hα₂ : Odd α₂)
    (hα₃ : Odd α₃) :
    NilpotentCyclicProduct (orders α₁ α₂ α₃) 4 ≃
      RankThreeResidues α₁ α₂ α₃ :=
  (Equiv.ofBijective
      (nilpotentOddResidues
        α₁ α₂ α₃ (AOrd.of_odd hα₁)
          (AOrd.of_odd hα₂)
          (AOrd.of_odd hα₃))
      (odd_residues_bijective
        α₁ α₂ α₃ hα₁ hα₂ hα₃)).trans
    (rankThreeResidues α₁ α₂ α₃
      (AOrd.of_odd hα₁)
      (AOrd.of_odd hα₂)
      (AOrd.of_odd hα₃))

end P1960
end Struik
