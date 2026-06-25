import Towers.Group.NilpotentProducts.GeneralGeneration

/-!
# Surjectivity of the arbitrary-rank equation-(18) model
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
    hallTripleCommutator x y z ∈ H := by
  exact subgroup_hall_commutator H
    (subgroup_hall_commutator H hx hy) hz

/-- A subgroup of the residue coordinate group containing the canonical
generators is the whole group. -/
theorem general_residue_generators
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (H : Subgroup (GeneralResidueGroup order horder))
    (hgen :
      ∀ i,
        generalResidueGenerator order horder i ∈ H)
    (y : GeneralResidueGroup order horder) :
    y ∈ H := by
  let quotientMap :=
    (generalCon order horder).mk'
  have hgenerator :
      ∀ i,
        quotientMap (generalGenerator i) ∈ H := by
    intro i
    simpa [quotientMap, generalResidueGenerator] using hgen i
  have haxis :
      ∀ i : GeneralBasisIndex t,
        quotientMap (generalAxis i 1) ∈ H := by
    intro i
    cases i with
    | single i =>
        simpa [general_axis_single] using hgenerator i
    | pair q =>
        have heq :
            quotientMap (generalAxis (.pair q) 1) =
              hallCommutator
                (quotientMap (generalGenerator q.i))
                (quotientMap (generalGenerator q.j)) := by
          symm
          simpa [hallCommutator] using congrArg quotientMap
            (general_hallCommutator q)
        rw [heq]
        exact subgroup_hall_commutator H
          (hgenerator q.i) (hgenerator q.j)
    | pairLeft q =>
        have heq :
            quotientMap (generalAxis (.pairLeft q) 1) =
              hallTripleCommutator
                (quotientMap (generalGenerator q.i))
                (quotientMap (generalGenerator q.j))
                (quotientMap (generalGenerator q.i)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using
            congrArg quotientMap
              (general_triple_left q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.i)
    | pairRight q =>
        have heq :
            quotientMap (generalAxis (.pairRight q) 1) =
              hallTripleCommutator
                (quotientMap (generalGenerator q.i))
                (quotientMap (generalGenerator q.j))
                (quotientMap (generalGenerator q.j)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using
            congrArg quotientMap
              (general_triple_pair q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.j)
    | tripleFirst q =>
        have heq :
            quotientMap (generalAxis (.tripleFirst q) 1) =
              hallTripleCommutator
                (quotientMap (generalGenerator q.i))
                (quotientMap (generalGenerator q.j))
                (quotientMap (generalGenerator q.k)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using
            congrArg quotientMap
              (general_triple_first q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.i) (hgenerator q.j) (hgenerator q.k)
    | tripleSecond q =>
        have heq :
            quotientMap (generalAxis (.tripleSecond q) 1) =
              hallTripleCommutator
                (quotientMap (generalGenerator q.j))
                (quotientMap (generalGenerator q.k))
                (quotientMap (generalGenerator q.i)) := by
          symm
          simpa [hallCommutator, hallTripleCommutator] using
            congrArg quotientMap
              (general_triple_second q)
        rw [heq]
        exact subgroup_triple_commutator H
          (hgenerator q.j) (hgenerator q.k) (hgenerator q.i)
  induction y using Con.induction_on with
  | _ c =>
      change quotientMap c ∈ H
      exact general_coordinates_axes
        (H.comap quotientMap) haxis c

/-- The canonical map from the arbitrary cyclic free product onto the
equation-(18) residue model is surjective. -/
theorem general_residues_surjective
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Surjective
      (cyclicGeneralResidues order horder) := by
  let f := cyclicGeneralResidues order horder
  let H := f.range
  have hgen :
      ∀ i,
        generalResidueGenerator order horder i ∈ H := by
    intro i
    refine ⟨cyclicGenerator order i, ?_⟩
    simp [f, cyclicGenerator,
      cyclicGeneralResidues,
      generalResidueGenerator]
  intro y
  exact general_residue_generators
    order horder H hgen y

/-- The factored map from Struik's arbitrary-rank `F/F₄` is surjective. -/
theorem nilpotent_general_residues
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Surjective
      (nilpotentGeneralResidues
        order horder) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    general_residues_surjective
      order horder y
  refine ⟨QuotientGroup.mk'
    (Subgroup.lowerCentralSeries (CyclicFreeProduct order) 3) x, ?_⟩
  rfl

end P1960
end Struik
