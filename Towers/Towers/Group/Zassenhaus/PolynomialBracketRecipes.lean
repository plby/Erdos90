import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.Zassenhaus.HallSpecialization

/-!
# Universal coordinate recipes through cutoff four

The cutoff-four signed collector produces one finite coordinate recipe system
for each input arity, independent of the values later substituted for the
input Hall coordinates.  This file exposes those recipes and proves that
substitution of polynomial coordinate families preserves the expected degree
bounds.
-/

namespace Towers
namespace TCTex

universe u

namespace WBTerm

/-- Substituting polynomial Hall-coordinate families into one signed recipe
term preserves the weighted degree bound. -/
lemma specialization_valued_most
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (term : WBTerm H ι s) :
    IVMost
      (fun q : ℕ => term.eval (E q)) (s / inputWeight) := by
  have hmonomial :=
    term.2.specialization_valued_most E hE
  have hscaled := hmonomial.smul term.1
  simpa [WHMono.powerSpecialization,
    WBTerm.eval, Pi.smul_apply, smul_eq_mul] using
      hscaled

end WBTerm

namespace WBForm

/-- Substituting polynomial Hall-coordinate families into a finite signed
formula preserves the weighted degree bound. -/
lemma specialization_valued_most
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (formula : WBForm H ι s) :
    IVMost
      (fun q : ℕ => formula.eval (E q)) (s / inputWeight) := by
  unfold WBForm.eval
  generalize formula.terms = terms
  induction terms with
  | nil =>
      simpa using
        IVMost.zero (s / inputWeight)
  | cons term terms ih =>
      have hterm :=
        term.specialization_valued_most
          E hE
      simpa using hterm.add ih

end WBForm

namespace CCRecipe

/-- Evaluating a universal signed coordinate recipe system on polynomial
Hall-coordinate inputs again gives polynomial Hall coordinates. -/
lemma eval_coordinate_family
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (R : κ → CCRecipe H ι)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E) :
    HallCoordinateFamily H κ inputWeight
      (fun q k => (R k).eval (E q)) := by
  intro k s i
  change
    IVMost
      (fun q : ℕ =>
        (((R k).formulas s i).map fun formula => formula.eval (E q)).sum)
      (s / inputWeight)
  induction (R k).formulas s i with
  | nil =>
      simpa using IVMost.zero (s / inputWeight)
  | cons formula formulas ih =>
      have hformula :=
        formula.specialization_valued_most
          E hE
      simpa using hformula.add ih

/-- The one-output specialization of
`eval_coordinate_family`. -/
lemma coordinate_family_single
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E) :
    HallCoordinateFamily H (Fin 1) inputWeight
      (fun q _ => R.eval (E q)) :=
  eval_coordinate_family (fun _ : Fin 1 => R) E hE

end CCRecipe

open SCBuilda

/-- The universal signed coordinate normalization for a product of `k`
collected Hall words through cutoff four. -/
noncomputable def collected_normalization_four
    {d n k : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) :
    SSNorm
      (n := n) (lowerWeight := 1) H
        ((symbolicSourceFactors
          (n := n) H (List.finRange k)).map
            SPFactor.ofMonomial) := by
  let source :=
    (symbolicSourceFactors
      (n := n) H (List.finRange k)).map
        SPFactor.ofMonomial
  let builder :=
    (automatic_recipe_four
      (hn := hn) (H := H) (hH := hH) hn4)
      |>.restrictedRecursiveBuilder
  let normalizer :=
    builder.supportedCoordinateNormalizer hn H hH 1
  let hexists := normalizer.normalize source
      (SPFactor.truncated_monomial
        (SCFactor.truncated_product_factors
          H (List.finRange k)))
      (SPFactor.word_least_one source)
  let coordinates := Classical.choose hexists
  have hcoordinates := (Classical.choose_spec hexists).1
  have heval := (Classical.choose_spec hexists).2
  exact
    {
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      coordinates_raw_source := heval
    }

/-- Universal signed formulas for recollecting a product of `k` Hall normal
forms through cutoff four. -/
noncomputable def collected_recipes_n
    {d n k : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) :
    CCRecipe H (Fin k) :=
  (collected_normalization_four
    hn hn4 H hH).coordinates

/-- The universal product recipes evaluate to the product of the supplied
collected Hall normal forms. -/
theorem collected_recipes_spec
    {d n k : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : Fin k → HEFam H) :
    collectedHallProduct (n := n) H
        ((collected_recipes_n
          hn hn4 H hH).eval e) =
      ((List.finRange k).map fun j =>
        collectedHallProduct (n := n) H (e j)).prod := by
  let normalization :=
    collected_normalization_four
      (k := k) hn hn4 H hH
  let R := normalization.coordinates
  change
    collectedHallProduct (n := n) H (R.eval e) =
      ((List.finRange k).map fun j =>
        collectedHallProduct (n := n) H (e j)).prod
  calc
    collectedHallProduct (n := n) H (R.eval e) =
        SPFactor.listEval (n := n) e
          (R.factors (n := n)) :=
      (R.listEval_factors e).symm
    _ =
        SPFactor.listEval (n := n) e
          ((symbolicSourceFactors
            (n := n) H (List.finRange k)).map
              SPFactor.ofMonomial) :=
      normalization.coordinates_raw_source e
    _ =
        SCFactor.listEval (n := n) e
          (symbolicSourceFactors
            (n := n) H (List.finRange k)) :=
      SPFactor.list_eval_monomial e
        (symbolicSourceFactors
          (n := n) H (List.finRange k))
    _ =
        ((List.finRange k).map fun j =>
          collectedHallProduct (n := n) H (e j)).prod :=
      symbolic_source_factors H e (List.finRange k)

/-- The universal signed coordinate normalization for the inverse of one
collected Hall word through cutoff four. -/
noncomputable def normalization_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) :
    SSNorm
      (n := n) (lowerWeight := 1) H
        ((symbolicInverseFactors (n := n) H).map
          SPFactor.ofMonomial) := by
  let source :=
    (symbolicInverseFactors (n := n) H).map
      SPFactor.ofMonomial
  let builder :=
    (automatic_recipe_four
      (hn := hn) (H := H) (hH := hH) hn4)
      |>.restrictedRecursiveBuilder
  let normalizer :=
    builder.supportedCoordinateNormalizer hn H hH 1
  let hexists := normalizer.normalize source
      (SPFactor.truncated_monomial
        (SCFactor.truncated_symbolic_factors
          H))
      (SPFactor.word_least_one source)
  let coordinates := Classical.choose hexists
  have hcoordinates := (Classical.choose_spec hexists).1
  have heval := (Classical.choose_spec hexists).2
  exact
    {
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      coordinates_raw_source := heval
    }

/-- Universal signed formulas for recollecting an inverse through cutoff
four. -/
noncomputable def collected_recipes_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) :
    CCRecipe H (Fin 1) :=
  (normalization_n_four
    hn hn4 H hH).coordinates

/-- The universal inverse recipes evaluate to the inverse of the supplied
collected Hall normal form. -/
theorem recipes_n_spec
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    collectedHallProduct (n := n) H
        ((collected_recipes_four
          hn hn4 H hH).eval
            (fun _ : Fin 1 => negExponentFamily e)) =
      (collectedHallProduct (n := n) H e)⁻¹ := by
  let normalization :=
    normalization_n_four
      hn hn4 H hH
  let R := normalization.coordinates
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  change
    collectedHallProduct (n := n) H (R.eval input) =
      (collectedHallProduct (n := n) H e)⁻¹
  calc
    collectedHallProduct (n := n) H (R.eval input) =
        SPFactor.listEval (n := n) input
          (R.factors (n := n)) :=
      (R.listEval_factors input).symm
    _ =
        SPFactor.listEval (n := n) input
          ((symbolicInverseFactors (n := n) H).map
            SPFactor.ofMonomial) :=
      normalization.coordinates_raw_source input
    _ =
        SCFactor.listEval (n := n) input
          (symbolicInverseFactors (n := n) H) :=
      SPFactor.list_eval_monomial input
        (symbolicInverseFactors (n := n) H)
    _ = (collectedHallProduct (n := n) H e)⁻¹ :=
      list_symbolic_factors H e

end TCTex
end Towers
