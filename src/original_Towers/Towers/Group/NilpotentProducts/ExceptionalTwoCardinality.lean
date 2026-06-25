import Towers.Group.NilpotentProducts.GeneralBasis
import Towers.Group.NilpotentProducts.ExceptionalTwoModel
import Mathlib.SetTheory.Cardinal.Finite


/-!
# Cardinality and exact pair orders in Struik's Theorem 4 model
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

/-- The explicit equation-(29) residue tuple as a product of its six
dependent coordinate families. -/
def exceptionalCardinalityPi
    {t : ℕ} (r : Fin t → ℕ) :
    ExceptionalTwoResidues r ≃
      (∀ i : Fin t, ZMod (singleModulus r i)) ×
      (∀ q : Pair t, ZMod (exceptionalPairModulus r q)) ×
      (∀ q : Pair t,
        ZMod (leftSquareModulus r q)) ×
      (∀ q : Pair t,
        ZMod (pairSquareModulus r q)) ×
      (∀ q : Triple t,
        ZMod (exceptionalResiduesModulus r q)) ×
      (∀ q : Triple t,
        ZMod (exceptionalResiduesModulus r q)) where
  toFun c :=
    ⟨c.single, c.pair, c.pairLeftSquare, c.pairRightSquare,
      c.tripleFirst, c.tripleSecond⟩
  invFun c := {
    single := c.1
    pair := c.2.1
    pairLeftSquare := c.2.2.1
    pairRightSquare := c.2.2.2.1
    tripleFirst := c.2.2.2.2.1
    tripleSecond := c.2.2.2.2.2 }
  left_inv c := by ext <;> rfl
  right_inv c := by
    rcases c with
      ⟨single, pair, pairLeftSquare, pairRightSquare,
        tripleFirst, tripleSecond⟩
    rfl

/-- Cardinality of the residue coordinates listed in Theorem 4. -/
theorem exceptional_cardinality_residues
    {t : ℕ} (r : Fin t → ℕ) :
    Nat.card (ExceptionalTwoResidues r) =
      (∏ i : Fin t, singleModulus r i) *
        ((∏ q : Pair t, exceptionalPairModulus r q) *
          ((∏ q : Pair t,
              leftSquareModulus r q) *
            ((∏ q : Pair t,
                pairSquareModulus r q) *
              ((∏ q : Triple t,
                  exceptionalResiduesModulus r q) *
                ∏ q : Triple t,
                  exceptionalResiduesModulus r q)))) := by
  rw [Nat.card_congr (exceptionalCardinalityPi r)]
  simp only [Nat.card_prod, Nat.card_pi, Nat.card_zmod]

/-- The equation-(29) residue tuple is finite and nonempty. -/
theorem residues_card_ne
    {t : ℕ} (r : Fin t → ℕ) :
    Nat.card (ExceptionalTwoResidues r) ≠ 0 := by
  rw [exceptional_cardinality_residues]
  simp only [ne_eq, mul_eq_zero, or_self, not_or]
  have hpow (n : ℕ) : 2 ^ n ≠ 0 := pow_ne_zero n (by decide)
  refine ⟨Finset.prod_ne_zero_iff.mpr ?_, Finset.prod_ne_zero_iff.mpr ?_,
    Finset.prod_ne_zero_iff.mpr ?_, Finset.prod_ne_zero_iff.mpr ?_,
    Finset.prod_ne_zero_iff.mpr ?_⟩
  · intro i _
    exact hpow (r i)
  · intro q _
    exact hpow (r q.i + 1)
  · intro q _
    exact hpow (r q.i - 1)
  · intro q _
    unfold pairSquareModulus
    split <;> exact hpow _
  · intro q _
    exact hpow (r q.i)

/-- The pure weight-two axis in equation-(29) coordinates. -/
def pairAxis
    {t : ℕ} (q : Pair t) (n : ℤ) :
    ELCoordi t := {
  ELCoordi.zero t with
  pair := fun p => if p = q then n else 0 }

@[simp] theorem exceptional_residues_axis
    {t : ℕ} (q : Pair t) (n : ℤ) :
    toGeneralResidues (pairAxis q n) =
      generalAxis (.pair q) n := by
  ext <;>
    simp [pairAxis, toGeneralResidues,
      ELCoordi.alpha, ELCoordi.zero,
      generalAxis, GCoordi.zero]

theorem pairAxis_add
    {t : ℕ} (q : Pair t) (m n : ℤ) :
    pairAxis q m * pairAxis q n =
      pairAxis q (m + n) := by
  apply (mulGeneralResidues t).injective
  rw [map_mul]
  change
    toGeneralResidues (pairAxis q m) *
        toGeneralResidues (pairAxis q n) =
      toGeneralResidues (pairAxis q (m + n))
  rw [exceptional_residues_axis,
    exceptional_residues_axis,
    exceptional_residues_axis]
  exact generalAxis_add (.pair q) m n

theorem pair_axis_pow
    {t : ℕ} (q : Pair t) (n : ℕ) :
    pairAxis q 1 ^ n = pairAxis q n := by
  induction n with
  | zero =>
      change ELCoordi.zero t = pairAxis q 0
      ext <;> simp [pairAxis, ELCoordi.zero]
  | succ n ih =>
      rw [pow_succ, ih, pairAxis_add]
      norm_num

theorem hallCommutator_generator
    {t : ℕ} (q : Pair t) :
    hallCommutator
        (exceptionalTwoModel q.i)
        (exceptionalTwoModel q.j) =
      pairAxis q 1 := by
  apply (mulGeneralResidues t).injective
  have hi :
      (mulGeneralResidues t)
          (exceptionalTwoModel q.i) =
        generalGenerator q.i :=
    exceptional_residues_generator q.i
  have hj :
      (mulGeneralResidues t)
          (exceptionalTwoModel q.j) =
        generalGenerator q.j :=
    exceptional_residues_generator q.j
  have haxis :
      (mulGeneralResidues t)
          (pairAxis q 1) =
        generalAxis (.pair q) 1 :=
    exceptional_residues_axis q 1
  calc
    (mulGeneralResidues t)
        (hallCommutator
          (exceptionalTwoModel q.i)
          (exceptionalTwoModel q.j)) =
        hallCommutator
          (generalGenerator q.i)
          (generalGenerator q.j) := by
      simp only [hallCommutator, map_mul, map_inv, hi, hj]
    _ = generalAxis (.pair q) 1 :=
      general_hallCommutator q
    _ = (mulGeneralResidues t)
          (pairAxis q 1) := by
      exact haxis.symm

theorem residue_commutator_generator
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (q : Pair t) :
    hallCommutator
        (exceptionalModelGenerator r hpos hmono q.i)
        (exceptionalModelGenerator r hpos hmono q.j) =
      (pairAxis q 1 :
        ExceptionalResiduesResidue r hpos hmono) := by
  let quotientMap := (exceptionalResiduesCon r hpos hmono).mk'
  change
    hallCommutator
        (quotientMap (exceptionalTwoModel q.i))
        (quotientMap (exceptionalTwoModel q.j)) =
      quotientMap (pairAxis q 1)
  calc
    hallCommutator
        (quotientMap (exceptionalTwoModel q.i))
        (quotientMap (exceptionalTwoModel q.j)) =
        quotientMap
          (hallCommutator
            (exceptionalTwoModel q.i)
            (exceptionalTwoModel q.j)) := by
      simp [hallCommutator]
    _ = quotientMap (pairAxis q 1) :=
      congrArg quotientMap (hallCommutator_generator q)

theorem residue_pair_axis
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (q : Pair t) (n : ℕ) :
    (pairAxis q 1 :
        ExceptionalResiduesResidue r hpos hmono) ^ n =
      (pairAxis q n :
        ExceptionalResiduesResidue r hpos hmono) := by
  let quotientMap := (exceptionalResiduesCon r hpos hmono).mk'
  change
    (quotientMap (pairAxis q 1)) ^ n =
      quotientMap (pairAxis q n)
  rw [← map_pow]
  exact congrArg quotientMap (pair_axis_pow q n)

/-- The pair commutator in the equation-(29) model has exactly the order
claimed in Theorem 4. -/
theorem residue_pair_order
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (q : Pair t) :
    orderOf
      (hallCommutator
        (exceptionalModelGenerator r hpos hmono q.i)
        (exceptionalModelGenerator r hpos hmono q.j)) =
      exceptionalPairModulus r q := by
  rw [residue_commutator_generator]
  apply (orderOf_eq_iff (by
    simp [exceptionalPairModulus])).2
  constructor
  · rw [residue_pair_axis]
    apply (exceptionalResiduesCon r hpos hmono).eq.mpr
    refine ⟨fun _ => .refl _, ?_, fun _ => .refl _, fun _ => .refl _,
      fun _ => .refl _, fun _ => .refl _⟩
    intro p
    by_cases hpq : p = q
    · subst p
      simp [pairAxis, ELCoordi.zero,
        show (1 : ELCoordi t) =
          ELCoordi.zero t from rfl, Int.ModEq]
    · have hfields : ¬(p.i = q.i ∧ p.j = q.j) := by
        intro h
        exact hpq ((Pair.eq_iff_fields p q).2 h)
      simp [pairAxis, ELCoordi.zero,
        show (1 : ELCoordi t) =
          ELCoordi.zero t from rfl, hfields]
  · intro m hm hmp
    rw [residue_pair_axis]
    intro hone
    have hmod :=
      ((exceptionalResiduesCon r hpos hmono).eq.mp hone).pair q
    have hmod' :
        (m : ℤ) ≡ 0
          [ZMOD (exceptionalPairModulus r q : ℤ)] := by
      simpa [pairAxis, ELCoordi.zero,
        show (1 : ELCoordi t) =
          ELCoordi.zero t from rfl] using hmod
    have hdivInt :
        (exceptionalPairModulus r q : ℤ) ∣ (m : ℤ) := by
      simpa [Int.modEq_iff_dvd] using hmod'
    have hdiv : exceptionalPairModulus r q ∣ m := by
      exact_mod_cast hdivInt
    exact (Nat.not_dvd_of_pos_of_lt hmp hm) hdiv

end P1960
end Struik
