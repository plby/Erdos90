import Submission.Group.NilpotentProducts.ExceptionalResidueCover
import Submission.Group.NilpotentProducts.ExceptionalTwoCardinality
import Submission.Group.NilpotentProducts.ExceptionalTwoSurjectivity
import Mathlib.SetTheory.Cardinal.Finite


/-!
# Struik's Theorem 4 normal form

The equation-(25) word gives a surjection from the finite equation-(29)
residue tuple to the fourth nilpotent product.  Comparison with the explicit
equation-(29) model makes both canonical maps bijective and yields uniqueness.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton

universe u

private noncomputable def exceptionalResidueRepresentative
    {n : ℕ} (x : ZMod n) : ℤ :=
  Classical.choose (ZMod.intCast_surjective x)

@[simp] private theorem exceptional_representative_cast
    {n : ℕ} (x : ZMod n) :
    (exceptionalResidueRepresentative x : ZMod n) = x :=
  Classical.choose_spec (ZMod.intCast_surjective x)

/-- Choose one integral equation-(29) tuple representing a residue tuple. -/
noncomputable def coordinatesOfResidues
    {t : ℕ} {r : Fin t → ℕ} (z : ExceptionalTwoResidues r) :
    ELCoordi t where
  single i := exceptionalResidueRepresentative (z.single i)
  pair q := exceptionalResidueRepresentative (z.pair q)
  pairLeftSquare q :=
    exceptionalResidueRepresentative (z.pairLeftSquare q)
  pairRightSquare q :=
    exceptionalResidueRepresentative (z.pairRightSquare q)
  tripleFirst q :=
    exceptionalResidueRepresentative (z.tripleFirst q)
  tripleSecond q :=
    exceptionalResidueRepresentative (z.tripleSecond q)

@[simp] theorem exceptional_coordinates_residues
    {t : ℕ} (r : Fin t → ℕ) (z : ExceptionalTwoResidues r) :
    exceptionalResiduesCast r (coordinatesOfResidues z) = z := by
  ext <;>
    simp [exceptionalResiduesCast, coordinatesOfResidues]

/-- Evaluate equation-(29) residue coordinates by Struik's equation-(25)
normal word. -/
noncomputable def residueEval
    {t : ℕ} (r : Fin t → ℕ) :
    ExceptionalTwoResidues r → EvenClassGroup r :=
  fun z =>
    exceptionalResidueCover.{u} r (coordinatesOfResidues z)

theorem residue_eval_cast
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (c : ELCoordi t) :
    residueEval.{u} r (exceptionalResiduesCast r c) =
      exceptionalResidueCover.{u} r c := by
  apply normal_mod r hpos
  apply exceptional_residues_cast.mpr
  simp

/-- Every element of the fourth nilpotent product is represented by one
equation-(29) residue tuple. -/
theorem residueEval_surjective
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i) :
    Function.Surjective (residueEval.{u} r) := by
  intro x
  obtain ⟨c, hc⟩ := normalWord_surjective.{u} r x
  refine ⟨exceptionalResiduesCast r c, ?_⟩
  rw [residue_eval_cast r hpos]
  exact hc

/-- **Struik's Theorem 4, model form.**  The canonical map from the fourth
nilpotent product to the equation-(29) residue-coordinate group is
bijective. -/
theorem
    exceptional_residue_bijective
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Function.Bijective
      (nilpotentExceptionalResidues
        r hpos hmono) := by
  have hresidueSurjective :
      Function.Surjective (residueEval.{0} r) :=
    residueEval_surjective r hpos
  letI : Finite (ExceptionalTwoResidues r) :=
    Nat.finite_of_card_ne_zero (residues_card_ne r)
  letI : Finite (EvenClassGroup r) :=
    Finite.of_surjective
      (residueEval.{0} r) hresidueSurjective
  have hsourceLeResidues :
      Nat.card (EvenClassGroup r) ≤
        Nat.card (ExceptionalTwoResidues r) :=
    Nat.card_le_card_of_surjective
      (residueEval.{0} r) hresidueSurjective
  have hresidueCard :
      Nat.card (ExceptionalTwoResidues r) =
        Nat.card (ExceptionalResiduesResidue r hpos hmono) :=
    (Nat.card_congr
      (exceptionalTwoResidues r hpos hmono)).symm
  have hcard :
      Nat.card (EvenClassGroup r) ≤
        Nat.card (ExceptionalResiduesResidue r hpos hmono) :=
    hsourceLeResidues.trans_eq hresidueCard
  exact
    (nilpotent_exceptional_residues
      r hpos hmono).bijective_of_nat_card_le hcard

/-- **Struik's Theorem 4.**  The equation-(29) residue tuple is in
canonical bijection with the fourth nilpotent product. -/
theorem residueEval_bijective
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Function.Bijective (residueEval.{u} r) := by
  have hresidueSurjective :
      Function.Surjective (residueEval.{u} r) :=
    residueEval_surjective r hpos
  letI : Finite (ExceptionalTwoResidues r) :=
    Nat.finite_of_card_ne_zero (residues_card_ne r)
  letI : Finite (EvenClassGroup r) :=
    Finite.of_surjective
      (residueEval.{u} r) hresidueSurjective
  have hmodelBijective :=
    exceptional_residue_bijective
      r hpos hmono
  have hsourceCard :
      Nat.card (EvenClassGroup r) =
        Nat.card (ExceptionalResiduesResidue r hpos hmono) :=
    Nat.card_congr (Equiv.ofBijective
      (nilpotentExceptionalResidues
        r hpos hmono) hmodelBijective)
  have hmodelCard :
      Nat.card (ExceptionalResiduesResidue r hpos hmono) =
        Nat.card (ExceptionalTwoResidues r) :=
    Nat.card_congr (exceptionalTwoResidues r hpos hmono)
  have hresidueLeSource :
      Nat.card (ExceptionalTwoResidues r) ≤
        Nat.card (EvenClassGroup r) := by
    rw [hsourceCard, hmodelCard]
  exact hresidueSurjective.bijective_of_nat_card_le hresidueLeSource

noncomputable def exceptionalTwoResidue
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    ExceptionalTwoResidues r ≃ EvenClassGroup r :=
  Equiv.ofBijective
    (residueEval.{u} r)
    (residueEval_bijective r hpos hmono)

/-- Two equation-(25) integral words are equal exactly when all their
coordinates are congruent modulo the orders listed in equation (29). -/
theorem normal_word_mod
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    {c d : ELCoordi t} :
    exceptionalResidueCover.{u} r c = exceptionalResidueCover.{u} r d ↔
      ERMod r c d := by
  constructor
  · intro hcd
    apply exceptional_residues_cast.mpr
    apply (residueEval_bijective.{u} r hpos hmono).1
    rw [residue_eval_cast r hpos,
      residue_eval_cast r hpos]
    exact hcd
  · exact normal_mod r hpos

/-- The pair commutator in the fourth nilpotent product has the exact
order asserted in Theorem 4. -/
theorem pair_commutator_order
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (q : Pair t) :
    orderOf
      (hallCommutator
        (evenClassGenerator r q.i)
        (evenClassGenerator r q.j)) =
      exceptionalPairModulus r q := by
  let f :=
    nilpotentExceptionalResidues
      r hpos hmono
  have hf :
      Function.Injective f :=
    (exceptional_residue_bijective
      r hpos hmono).1
  have hgen (i : Fin t) :
      f (evenClassGenerator r i) =
        exceptionalModelGenerator r hpos hmono i := by
    change
      cyclicExceptionalResidues r hpos hmono
          (cyclicGenerator (singleModulus r) i) =
        exceptionalModelGenerator r hpos hmono i
    simp [cyclicExceptionalResidues,
      cyclicGenerator, exceptionalModelGenerator]
  rw [← orderOf_injective f hf
    (hallCommutator
      (evenClassGenerator r q.i)
      (evenClassGenerator r q.j))]
  have hcomm :
      f
          (hallCommutator
            (evenClassGenerator r q.i)
            (evenClassGenerator r q.j)) =
        hallCommutator
          (exceptionalModelGenerator r hpos hmono q.i)
          (exceptionalModelGenerator r hpos hmono q.j) := by
    simp only [hallCommutator, map_mul, map_inv, hgen]
  exact (congrArg orderOf hcomm).trans
    (residue_pair_order r hpos hmono q)

end P1960
end Struik
