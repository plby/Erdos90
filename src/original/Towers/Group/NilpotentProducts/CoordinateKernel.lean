import Towers.Group.NilpotentProducts.ArbitraryCutoffCover
import Towers.Group.NilpotentProducts.GeneralCardinality
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Struik's Theorem 3

The theorem says that, under the tame-prime hypothesis, the Hall-residue
cover constructed in `GeneralHallCover` is bijective.  This file records
the exact coordinate statement and develops all of its formal consequences.
The general injectivity proof, and hence the complete theorem, is supplied
in `Theorem3General`.
-/

namespace Struik
namespace P1960

open Towers
open Towers.TCTex

universe u

/-- Reduce an integral Hall exponent family modulo the recursive leaf gcd
at every positive weight below the cutoff. -/
noncomputable def generalResiduesFamily
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (e : StandardExponentFamily.{u} t) :
    GeneralHallResidues.{u} order n :=
  fun r i =>
    (e (r + 1) i :
      ZMod (generalStandardOrder order i))

theorem coordinateStatement_iff
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hbound : FactorOrderBound.{u} order n) :
    (Function.Bijective (generalResidueEval.{u} order n)
    ) ↔
      (
        Function.Injective (generalResidueEval.{u} order n)
      ) := by
  constructor
  · exact fun h => h.1
  · intro hinjective
    exact
      ⟨hinjective,
        general_surjective_bound
          order n hbound⟩

/-- Cardinality of the complete Hall-residue coordinate space.  A zero
modulus contributes cardinality zero, reflecting an infinite coordinate. -/
theorem general_residues_card
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :
    Nat.card (GeneralHallResidues.{u} order n) =
      ∏ r : Fin (n - 1),
        ∏ i : (standardHallFamily.{u} t (r + 1)).index,
          generalStandardOrder order i := by
  simp only [GeneralHallResidues, Nat.card_pi, Nat.card_zmod]

/-- If every cyclic factor is finite and nontrivial, the Hall-residue
coordinate space is finite and nonempty. -/
theorem general_residues_ne
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (horder : ∀ i, 0 < order i) :
    Nat.card (GeneralHallResidues.{u} order n) ≠ 0 := by
  rw [general_residues_card]
  exact Finset.prod_ne_zero_iff.mpr fun r _ =>
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      (general_standard_pos order horder i).ne'

/-- At cutoff four, the arbitrary-cutoff residue family is the same finite
coordinate count as the three explicit Hall blocks used in Theorem 2. -/
theorem general_residues_up
    {t : ℕ} (order : Fin t → ℕ) :
    Nat.card (GeneralHallResidues.{u} order 4) =
      Nat.card (ResiduesUpThree.{u} order) := by
  simp only [GeneralHallResidues, ResiduesUpThree,
    Nat.card_pi, Nat.card_prod, Nat.card_zmod]
  norm_num [Fin.prod_univ_succ,
    general_standard_order]
  rfl

/-- Theorem 3 at its first allowed cutoff follows from the arbitrary-rank
class-three normal form already proved as Theorem 2. -/
theorem coordinateStatement_four
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i)) :
    (
      Function.Bijective (generalResidueEval.{0} order 4)) := by
  let horder : ∀ i, AOrd (order i) :=
    fun i => AOrd.of_odd (hodd i)
  have horderPos : ∀ i, 0 < order i :=
    fun i => (hodd i).pos
  have hsurjective :
      Function.Surjective
        (generalResidueEval.{0} order 4) :=
    general_surjective_bound
      order 4 (order_bound_four order horder)
  letI : Finite (GeneralHallResidues.{0} order 4) :=
    Nat.finite_of_card_ne_zero
      (general_residues_ne order 4 horderPos)
  letI : Finite (NilpotentCyclicProduct order 4) :=
    Finite.of_surjective
      (generalResidueEval.{0} order 4) hsurjective
  have htargetCard :
      Nat.card (NilpotentCyclicProduct order 4) =
        Nat.card (ResiduesUpThree.{0} order) := by
    calc
      Nat.card (NilpotentCyclicProduct order 4) =
          Nat.card
            (GeneralResidueGroup order horder) :=
        Nat.card_congr
          (Equiv.ofBijective
            (nilpotentGeneralResidues
              order horder)
            (nilpotent_residues_bijective
              order hodd))
      _ = Nat.card (ResiduesUpThree.{0} order) :=
        (residues_up_general
          order horder).symm
  have hcard :
      Nat.card (GeneralHallResidues.{0} order 4) ≤
        Nat.card (NilpotentCyclicProduct order 4) := by
    rw [general_residues_up,
      htargetCard]
  exact hsurjective.bijective_of_nat_card_le hcard

/-- The uniqueness kernel in Theorem 3 is established at cutoff four. -/
theorem kernelStatement_four
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i)) :
    (Function.Injective (generalResidueEval.{0} order 4)) :=
  (coordinateStatement_four order hodd).1

/-- Bijectivity gives the unique residue tuple representing each element,
which is the main normal-form assertion of Theorem 3. -/
theorem uniqueResidueCoordinates
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (x : NilpotentCyclicProduct order n) :
    ∃! z : GeneralHallResidues.{u} order n,
      generalResidueEval.{u} order n z = x := by
  obtain ⟨z, hz⟩ := hCoordinateKernel.2 x
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact hCoordinateKernel.1 (hw.trans hz.symm)

/-- The unique Hall-residue normal form at cutoff four. -/
theorem unique_coordinates_four
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i))
    (x : NilpotentCyclicProduct order 4) :
    ∃! z : GeneralHallResidues.{0} order 4,
      generalResidueEval.{0} order 4 z = x :=
  uniqueResidueCoordinates
    order 4 (coordinateStatement_four order hodd) x

/-- The bijective Hall-residue evaluator as an equivalence of types. -/
noncomputable def coordinateResidueEquiv
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n))) :
    GeneralHallResidues.{u} order n ≃
      NilpotentCyclicProduct order n :=
  Equiv.ofBijective
    (generalResidueEval.{u} order n) hCoordinateKernel

/-- Multiplication on the residue coordinates, transported from the
nilpotent cyclic product.  The polynomial formulas in Theorem H1 compute
this operation. -/
noncomputable def residueMul
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (c d : GeneralHallResidues.{u} order n) :
    GeneralHallResidues.{u} order n :=
  (coordinateResidueEquiv order n hCoordinateKernel).symm
    (generalResidueEval.{u} order n c *
      generalResidueEval.{u} order n d)

@[simp] theorem general_residue_mul
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (c d : GeneralHallResidues.{u} order n) :
    generalResidueEval.{u} order n
        (residueMul order n hCoordinateKernel c d) =
      generalResidueEval.{u} order n c *
        generalResidueEval.{u} order n d := by
  exact
    (coordinateResidueEquiv order n hCoordinateKernel).apply_symm_apply _

/-- With finite positive generator orders, Theorem 3 gives the expected
product formula for the order of the nilpotent product. -/
theorem nilpotent_cyclic_card
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{0} order n))) :
    Nat.card (NilpotentCyclicProduct order n) =
      ∏ r : Fin (n - 1),
        ∏ i : (standardHallFamily.{0} t (r + 1)).index,
          generalStandardOrder order i := by
  calc
    Nat.card (NilpotentCyclicProduct order n) =
        Nat.card (GeneralHallResidues.{0} order n) :=
      (Nat.card_congr
        (coordinateResidueEquiv order n hCoordinateKernel)).symm
    _ = _ := general_residues_card order n

end P1960
end Struik
