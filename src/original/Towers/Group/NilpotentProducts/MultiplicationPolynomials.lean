import Towers.Group.NilpotentProducts.LowPolynomialOperations
import Towers.Group.NilpotentProducts.MagnusBinomialExpressions
import Towers.Group.NilpotentProducts.MagnusUniqueness

/-!
# Theorem 3 multiplication coordinates

At every cutoff, the arbitrary-cutoff binomial expressions from Theorem H1
can be evaluated on standard integer representatives and reduced modulo the
recursive Hall-factor orders.  Through cutoff four, the sharper weighted
standard Hall recipes give a second explicit description.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex

universe u

noncomputable section

/-- At every cutoff, multiplication in Theorem 3's residue coordinates is
obtained by collecting the product of the standard integer representatives
in the standard Hall basis and reducing the output coordinates modulo their
recursive Hall-factor orders. -/
theorem residue_standard_coordinates
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hbound : FactorOrderBound.{u} order n)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (c d : GeneralHallResidues.{u} order n) :
    let e := generalExponentRepresentatives order n c
    let f := generalExponentRepresentatives order n d
    residueMul order n hCoordinateKernel c d =
      generalResiduesFamily order n
        (standardHallCoordinates t n hn
          (standardHallProduct t n e *
            standardHallProduct t n f)) := by
  dsimp only
  let e := generalExponentRepresentatives order n c
  let f := generalExponentRepresentatives order n d
  let output :=
    standardHallCoordinates t n hn
      (standardHallProduct t n e * standardHallProduct t n f)
  change
    residueMul order n hCoordinateKernel c d =
      generalResiduesFamily order n output
  apply hCoordinateKernel.1
  rw [general_residue_mul]
  symm
  calc
    generalResidueEval.{u} order n
        (generalResiduesFamily order n output) =
        inverseFreeTruncation.{u} order n
          (standardHallProduct t n output) :=
      general_exponent_family
        order hbound output
    _ =
        inverseFreeTruncation.{u} order n
          (standardHallProduct t n e *
            standardHallProduct t n f) := by
      rw [show
        standardHallProduct t n output =
            standardHallProduct t n e *
              standardHallProduct t n f by
        exact
          standard_product_coordinates t n hn
            (standardHallProduct t n e *
              standardHallProduct t n f)]
    _ =
        inverseFreeTruncation.{u} order n
            (standardHallProduct t n e) *
          inverseFreeTruncation.{u} order n
            (standardHallProduct t n f) := by
      rw [map_mul]
    _ =
        generalResidueEval.{u} order n c *
          generalResidueEval.{u} order n d := by
      rw [
        ← general_exponent_family order hbound e,
        ← general_exponent_family order hbound f,
        general_residues_representatives,
        general_residues_representatives]

/-- At every cutoff, each coordinate of Theorem 3's residue multiplication is
the reduction of a compositional binomial expression in the standard integer
representatives of the two input residue tuples. -/
theorem residue_binomial_expression
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hbound : FactorOrderBound.{u} order n)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (r : Fin (n - 1))
    (i : (standardHallFamily.{u} t (r + 1)).index) :
    ∃ p : BExpr (StandardBinaryAddress.{u} t),
      ∀ c d : GeneralHallResidues.{u} order n,
        residueMul order n hCoordinateKernel c d r i =
          ((BExpr.eval
              (fun address =>
                if address.1 = (0 : Fin 2) then
                  generalExponentRepresentatives order n c
                    address.2.1 address.2.2
                else
                  generalExponentRepresentatives order n d
                    address.2.1 address.2.2)
              p : ℤ) :
            ZMod (generalStandardOrder order i)) := by
  obtain ⟨p, hp⟩ :=
    multiplication_binomial_expression
      (d := t) hn (weight := r + 1) (by omega) (by omega) i
  refine ⟨p, ?_⟩
  intro c d
  let e := generalExponentRepresentatives order n c
  let f := generalExponentRepresentatives order n d
  have hcoordinate :
      residueMul order n hCoordinateKernel c d r i =
        ((standardHallCoordinates t n hn
            (standardHallProduct t n e *
              standardHallProduct t n f)
            (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) := by
    have h :=
      congrArg
        (fun z : GeneralHallResidues.{u} order n => z r i)
        (residue_standard_coordinates
          order hn hbound hCoordinateKernel c d)
    simpa [generalResiduesFamily, e, f] using h
  calc
    residueMul order n hCoordinateKernel c d r i =
        ((standardHallCoordinates t n hn
            (standardHallProduct t n e *
              standardHallProduct t n f)
            (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) :=
      hcoordinate
    _ =
        ((BExpr.eval
            (fun address =>
              if address.1 = (0 : Fin 2) then
                generalExponentRepresentatives order n c
                  address.2.1 address.2.2
              else
                generalExponentRepresentatives order n d
                  address.2.1 address.2.2)
            p : ℤ) :
          ZMod (generalStandardOrder order i)) := by
      rw [hp e f]

/-- Under Struik's tame-order hypothesis, the arbitrary-cutoff binomial
coordinate formulas require no separately supplied normal-form or
factor-order assumptions. -/
theorem binomial_expression_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (r : Fin (n - 1))
    (i : (standardHallFamily.{u} t (r + 1)).index) :
    ∃ p : BExpr (StandardBinaryAddress.{u} t),
      ∀ c d : GeneralHallResidues.{u} order n,
        residueMul order n
            (statement_tame_orders order hn htame)
            c d r i =
          ((BExpr.eval
              (fun address =>
                if address.1 = (0 : Fin 2) then
                  generalExponentRepresentatives order n c
                    address.2.1 address.2.2
                else
                  generalExponentRepresentatives order n d
                    address.2.1 address.2.2)
              p : ℤ) :
            ZMod (generalStandardOrder order i)) :=
  residue_binomial_expression
    order hn
      (bound_tame_orders order hn htame)
      (statement_tame_orders order hn htame)
      r i

/-- Through cutoff four, multiplication in Theorem 3's residue coordinates
is obtained by evaluating the universal standard Hall product recipes on the
standard integer representatives and reducing the output coordinates modulo
their recursive Hall-factor orders. -/
theorem residue_recipes_four
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hbound : FactorOrderBound.{u} order n)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (c d : GeneralHallResidues.{u} order n) :
    let inputs : Fin 2 → StandardExponentFamily.{u} t :=
      ![generalExponentRepresentatives order n c,
        generalExponentRepresentatives order n d]
    let recipes :=
      collected_recipes_n
        (k := 2) hn hn4 (standardHallFamily.{u} t)
          (fun r hr hrn =>
            standard_forms_associated
              t n r hr hrn)
    residueMul order n hCoordinateKernel c d =
      generalResiduesFamily order n
        (recipes.eval inputs) := by
  dsimp only
  let inputs : Fin 2 → StandardExponentFamily.{u} t :=
    ![generalExponentRepresentatives order n c,
      generalExponentRepresentatives order n d]
  let recipes :=
    collected_recipes_n
      (k := 2) hn hn4 (standardHallFamily.{u} t)
        (fun r hr hrn =>
          standard_forms_associated
            t n r hr hrn)
  let output : StandardExponentFamily.{u} t :=
    recipes.eval inputs
  have hrecipe :
      standardHallProduct t n output =
        standardHallProduct t n
            (generalExponentRepresentatives order n c) *
          standardHallProduct t n
            (generalExponentRepresentatives order n d) := by
    change
      collectedHallProduct (n := n) (standardHallFamily.{u} t)
          (recipes.eval inputs) =
        collectedHallProduct (n := n) (standardHallFamily.{u} t)
            (generalExponentRepresentatives order n c) *
          collectedHallProduct (n := n) (standardHallFamily.{u} t)
            (generalExponentRepresentatives order n d)
    rw [collected_recipes_spec
      hn hn4 (standardHallFamily.{u} t)
        (fun r hr hrn =>
          standard_forms_associated
            t n r hr hrn)
      inputs]
    simp [inputs, List.finRange_succ]
  change
    residueMul order n hCoordinateKernel c d =
      generalResiduesFamily order n output
  apply hCoordinateKernel.1
  rw [general_residue_mul]
  symm
  calc
    generalResidueEval.{u} order n
        (generalResiduesFamily order n output) =
        inverseFreeTruncation.{u} order n
          (standardHallProduct t n output) :=
      general_exponent_family
        order hbound output
    _ =
        inverseFreeTruncation.{u} order n
          (standardHallProduct t n
              (generalExponentRepresentatives order n c) *
            standardHallProduct t n
              (generalExponentRepresentatives order n d)) := by
      rw [hrecipe]
    _ =
        inverseFreeTruncation.{u} order n
            (standardHallProduct t n
              (generalExponentRepresentatives order n c)) *
          inverseFreeTruncation.{u} order n
            (standardHallProduct t n
              (generalExponentRepresentatives order n d)) := by
      rw [map_mul]
    _ =
        generalResidueEval.{u} order n c *
          generalResidueEval.{u} order n d := by
      rw [
        ← general_exponent_family
          order hbound
            (generalExponentRepresentatives order n c),
        ← general_exponent_family
          order hbound
            (generalExponentRepresentatives order n d),
        general_residues_representatives,
        general_residues_representatives]

/-- Coordinatewise form of
`residue_recipes_four`. -/
theorem residue_n_four
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hbound : FactorOrderBound.{u} order n)
    (hCoordinateKernel : (Function.Bijective (generalResidueEval.{u} order n)))
    (c d : GeneralHallResidues.{u} order n)
    (r : Fin (n - 1))
    (i : (standardHallFamily.{u} t (r + 1)).index) :
    let inputs : Fin 2 → StandardExponentFamily.{u} t :=
      ![generalExponentRepresentatives order n c,
        generalExponentRepresentatives order n d]
    let recipes :=
      collected_recipes_n
        (k := 2) hn hn4 (standardHallFamily.{u} t)
          (fun s hs hsn =>
            standard_forms_associated
              t n s hs hsn)
    residueMul order n hCoordinateKernel c d r i =
      ((recipes.eval inputs (r + 1) i : ℤ) :
        ZMod (generalStandardOrder order i)) := by
  dsimp only
  have h :=
    congrArg
      (fun z : GeneralHallResidues.{u} order n => z r i)
      (residue_recipes_four
        order hn hn4 hbound hCoordinateKernel c d)
  simpa [generalResiduesFamily] using h

/-- Under Struik's tame-order hypothesis, the cutoff-four residue
multiplication formulas require no separately supplied normal-form or
factor-order assumptions. -/
theorem orders_n_four
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (htame : TameOrdersCutoff order n)
    (c d : GeneralHallResidues.{u} order n) :
    let inputs : Fin 2 → StandardExponentFamily.{u} t :=
      ![generalExponentRepresentatives order n c,
        generalExponentRepresentatives order n d]
    let recipes :=
      collected_recipes_n
        (k := 2) hn hn4 (standardHallFamily.{u} t)
          (fun r hr hrn =>
            standard_forms_associated
              t n r hr hrn)
    residueMul order n
        (statement_tame_orders order hn htame) c d =
      generalResiduesFamily order n
        (recipes.eval inputs) := by
  exact
    residue_recipes_four
      order hn hn4
        (bound_tame_orders order hn htame)
        (statement_tame_orders order hn htame)
        c d

end

end P1960
end Struik
