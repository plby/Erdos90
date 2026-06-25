import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Extracting a transposition from odd cycles and one two-cycle

If a permutation consists of one cycle of length two and finitely many
cycles of odd length, raising it to the product of the odd cycle lengths
kills every odd cycle and preserves the two-cycle.  Thus the resulting
permutation is a transposition.
-/

namespace Towers.NumberTheory.Milne

open Equiv Finset

variable {alpha iota : Type*}

/-- A permutation covered by one two-cycle and a finite family of odd cycles
becomes a transposition when raised to the product of the odd cycle lengths.

The cyclic subsets need not be supplied with separate disjointness proofs:
cyclicity and the parity of their cardinalities already force the relevant
behavior pointwise. -/
theorem Equiv.Perm.swappo_prodc_cycle
    [Finite alpha] [DecidableEq alpha]
    (sigma : Equiv.Perm alpha) (sTwo : Finset alpha)
    (indices : Finset iota) (sOdd : iota -> Finset alpha)
    (hTwoCard : sTwo.card = 2)
    (hTwoCycle : sigma.IsCycleOn (sTwo : Set alpha))
    (hOddCard : forall i, i ∈ indices -> Odd (sOdd i).card)
    (hOddCycle : forall i, i ∈ indices -> sigma.IsCycleOn (sOdd i : Set alpha))
    (hcover : forall x, x ∈ sTwo ∨ exists i, i ∈ indices ∧ x ∈ sOdd i) :
    (sigma ^ (indices.prod fun i => (sOdd i).card)).IsSwap := by
  classical
  letI := Fintype.ofFinite alpha
  let exponent := indices.prod fun i => (sOdd i).card
  have odd_prod (u : Finset iota)
      (hu : forall i, i ∈ u -> Odd (sOdd i).card) :
      Odd (u.prod fun i => (sOdd i).card) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih =>
        rw [Finset.prod_insert hi]
        exact (hu i (Finset.mem_insert_self i u)).mul
          (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))
  have hExponentOdd : Odd exponent := odd_prod indices hOddCard
  have hsupport : (sigma ^ exponent).support = sTwo := by
    ext x
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hx
      rcases hcover x with hxTwo | ⟨i, hi, hxi⟩
      · exact hxTwo
      · exfalso
        apply hx
        exact (hOddCycle i hi).pow_apply_eq hxi |>.2
          (Finset.dvd_prod_of_mem (fun j => (sOdd j).card) hi)
    · intro hxTwo hfix
      have hTwoDvd : 2 ∣ exponent := by
        rw [← hTwoCard]
        exact (hTwoCycle.pow_apply_eq hxTwo).mp hfix
      exact hExponentOdd.not_two_dvd_nat hTwoDvd
  rw [← Equiv.Perm.card_support_eq_two, hsupport, hTwoCard]

end Towers.NumberTheory.Milne
