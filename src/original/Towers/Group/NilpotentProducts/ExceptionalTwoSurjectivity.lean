import Towers.Group.NilpotentProducts.GeneralGeneration
import Towers.Group.NilpotentProducts.ExceptionalTwoModel

/-!
# Surjectivity of the equation-(29) model
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

private theorem subgroup_hall_commutator
    {G : Type*} [Group G] (H : Subgroup G)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    hallCommutator x y ∈ H := by
  simp only [hallCommutator]
  exact H.mul_mem
    (H.mul_mem (H.mul_mem (H.inv_mem hx) (H.inv_mem hy)) hx) hy

private theorem subgroup_triple_commutator
    {G : Type*} [Group G] (H : Subgroup G)
    {x y z : G} (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) :
    hallTripleCommutator x y z ∈ H :=
  subgroup_hall_commutator H
    (subgroup_hall_commutator H hx hy) hz

/-- A subgroup of the equation-(29) residue group containing the
canonical generators is the whole group. -/
theorem residue_group_generators
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (H : Subgroup (ExceptionalResiduesResidue r hpos hmono))
    (hgen : ∀ i, exceptionalModelGenerator r hpos hmono i ∈ H)
    (y : ExceptionalResiduesResidue r hpos hmono) :
    y ∈ H := by
  let quotientMap := (exceptionalResiduesCon r hpos hmono).mk'
  let changeInv :=
    (mulGeneralResidues t).symm.toMonoidHom
  let f : GCoordi t →*
      ExceptionalResiduesResidue r hpos hmono :=
    quotientMap.comp changeInv
  have hgenerator :
      ∀ i, f (generalGenerator i) ∈ H := by
    intro i
    simpa [f, quotientMap, changeInv, exceptionalModelGenerator,
      exceptionalTwoModel, mulGeneralResidues] using
        hgen i
  have haxis :
      ∀ i : GeneralBasisIndex t,
        f (generalAxis i 1) ∈ H := by
    intro i
    cases i with
    | single i =>
        simpa [general_axis_single] using hgenerator i
    | pair q =>
        have heq :
            f (generalAxis (.pair q) 1) =
              hallCommutator
                (f (generalGenerator q.i))
                (f (generalGenerator q.j)) := by
          symm
          simpa [hallCommutator] using congrArg f
            (general_hallCommutator q)
        rw [heq]
        exact subgroup_hall_commutator H
          (hgenerator q.i) (hgenerator q.j)
    | pairLeft q =>
        have heq :
            f (generalAxis (.pairLeft q) 1) =
              hallTripleCommutator
                (f (generalGenerator q.i))
                (f (generalGenerator q.j))
                (f (generalGenerator q.i)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using congrArg f
            (general_triple_left q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.i)
    | pairRight q =>
        have heq :
            f (generalAxis (.pairRight q) 1) =
              hallTripleCommutator
                (f (generalGenerator q.i))
                (f (generalGenerator q.j))
                (f (generalGenerator q.j)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using congrArg f
            (general_triple_pair q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.j)
    | tripleFirst q =>
        have heq :
            f (generalAxis (.tripleFirst q) 1) =
              hallTripleCommutator
                (f (generalGenerator q.i))
                (f (generalGenerator q.j))
                (f (generalGenerator q.k)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using congrArg f
            (general_triple_first q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.k)
    | tripleSecond q =>
        have heq :
            f (generalAxis (.tripleSecond q) 1) =
              hallTripleCommutator
                (f (generalGenerator q.j))
                (f (generalGenerator q.k))
                (f (generalGenerator q.i)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using congrArg f
            (general_triple_second q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.j) (hgenerator q.k) (hgenerator q.i)
  induction y using Con.induction_on with
  | _ c =>
      change quotientMap c ∈ H
      have hmem :=
        general_coordinates_axes
          (H.comap f) haxis (toGeneralResidues c)
      have heq :
          f (toGeneralResidues c) = quotientMap c := by
        change quotientMap
            (generalExceptionalResidues
              (toGeneralResidues c)) =
          quotientMap c
        rw [exceptional_residues_inverse]
      rw [← heq]
      exact hmem

/-- The canonical map from the free product of the `2 ^ rᵢ` cyclic
groups onto the equation-(29) model is surjective. -/
theorem exceptional_residues_surjective
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Function.Surjective
      (cyclicExceptionalResidues r hpos hmono) := by
  let f := cyclicExceptionalResidues r hpos hmono
  let H := f.range
  have hgen :
      ∀ i, exceptionalModelGenerator r hpos hmono i ∈ H := by
    intro i
    refine ⟨cyclicGenerator (singleModulus r) i, ?_⟩
    simp [f, cyclicGenerator,
      cyclicExceptionalResidues,
      exceptionalModelGenerator]
  intro y
  exact residue_group_generators
    r hpos hmono H hgen y

/-- The factored map from Struik's `F/F₄` onto the equation-(29) model
is surjective. -/
theorem
    nilpotent_exceptional_residues
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Function.Surjective
      (nilpotentExceptionalResidues
        r hpos hmono) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    exceptional_residues_surjective
      r hpos hmono y
  refine ⟨QuotientGroup.mk'
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (singleModulus r)) 3) x, ?_⟩
  rfl

end P1960
end Struik
