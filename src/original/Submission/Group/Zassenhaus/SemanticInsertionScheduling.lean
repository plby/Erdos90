import Submission.Group.Zassenhaus.CoordinateInsertionScheduling
import Submission.Group.Zassenhaus.ClassTwo

/-!
# Semantic coordinate-endpoint insertion for symbolic Hall powers

An adjacent-swap collector cannot rewrite an internal commutator word into its
atomic Hall normal form.  In a commutative high-weight stratum, however, that
normalization is semantically valid.  This file packages a support-bounded
semantic insertion kernel, folds it across finite source lists, and constructs
the Claim 5 polynomial data from a correctly sourced input.

The high-weight constructor supplies the terminal case needed by a recursive
collector: once all remaining factors have weight at least `lowerWeight` and
`n ≤ 2 * lowerWeight`, each factor can be normalized semantically and merged
into the coordinate endpoint.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A support-bounded semantic endpoint insertion kernel.  Unlike a rewrite-only
kernel, this may replace one commutator word by its Hall-normal coordinates,
but it must preserve evaluation for every repeated-block parameter.
-/
structure TSInserta
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  insert :
    ∀ (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      lowerWeight ≤ factor.word.weight PEAddres.weight →
      factor.word.weight PEAddres.weight < n →
        ∃ next : CCExpans H inputWeight,
          next.NTBelow lowerWeight ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q
                  (next.factors (n := n)) =
                SPFactora.listEval (n := n) q
                  (coordinates.factors (n := n) ++ [factor])

namespace TSInserta

/--
Repeated semantic endpoint insertion normalizes every finite source list in
the supported high-weight stratum.
-/
lemma exists_normalization
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (kernel :
      TSInserta
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H) :
    ∀ source : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n source →
      SPFactora.WordWeightLeast lowerWeight source →
        ∃ coordinates : CCExpans H inputWeight,
          coordinates.NTBelow lowerWeight ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q
                  (coordinates.factors (n := n)) =
                SPFactora.listEval (n := n) q source := by
  intro source hsourceTruncated hsourceSupported
  induction source using List.reverseRecOn with
  | nil =>
      refine
        ⟨CCExpans.empty H inputWeight, ?_, ?_⟩
      · intro s i hs
        rfl
      · intro q
        simp
  | append_singleton initial factor ih =>
      have hinitialTruncated : SPFactora.IsTruncated n initial := by
        intro x hx
        exact hsourceTruncated x (by simp [hx])
      have hinitialSupported :
          SPFactora.WordWeightLeast lowerWeight initial := by
        intro x hx
        exact hsourceSupported x (by simp [hx])
      have hfactorSupported :
          lowerWeight ≤
            factor.word.weight PEAddres.weight :=
        hsourceSupported factor (by simp)
      have hfactorTruncated :
          factor.word.weight PEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases ih hinitialTruncated hinitialSupported with
        ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
      rcases kernel.insert coordinates factor hcoordinatesSupported
          hfactorSupported hfactorTruncated with
        ⟨next, hnextSupported, hnext⟩
      refine ⟨next, hnextSupported, ?_⟩
      intro q
      calc
        SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) :=
          hnext q
        _ = SPFactora.listEval (n := n) q
              (coordinates.factors (n := n)) *
            factor.eval (n := n) q := by
          rw [SPFactora.listEval_append]
          simp
        _ = SPFactora.listEval (n := n) q initial *
            factor.eval (n := n) q := by
          rw [hcoordinates q]
        _ = SPFactora.listEval (n := n) q
              (initial ++ [factor]) := by
          rw [SPFactora.listEval_append]
          simp

/--
In the commutative region `n ≤ 2 * lowerWeight`, semantic Hall-normalization
constructs the supported insertion kernel.
-/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight) :
    TSInserta
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H where
  insert coordinates factor hcoordinates hfactorSupported hfactorTruncated := by
    let X := factor.normalCoordinateExpansions hn H hH
    have hXSupported : X.NTBelow lowerWeight :=
      factor.no_terms_expansions
        hn H hH hfactorSupported
    have hcoordinatesFactorsSupported :
        SPFactora.WordWeightLeast lowerWeight
          (coordinates.factors (n := n)) :=
      CCExpans.no_terms_below
        coordinates hcoordinates
    have hXFactorsSupported :
        SPFactora.WordWeightLeast lowerWeight
          (X.factors (n := n)) :=
      CCExpans.no_terms_below
        X hXSupported
    have hmerge :
        TSRwa (n := n)
          (coordinates.factors (n := n) ++ X.factors (n := n))
          ((coordinates.add X).factors (n := n)) := by
      apply
        CCExpans.factors_append_rewrites
      intro B hB A hA
      have hBSupported := hcoordinatesFactorsSupported B hB
      have hASupported := hXFactorsSupported A hA
      omega
    refine ⟨coordinates.add X, hcoordinates.add hXSupported, ?_⟩
    intro q
    calc
      SPFactora.listEval (n := n) q
            ((coordinates.add X).factors (n := n)) =
          SPFactora.listEval (n := n) q
            (coordinates.factors (n := n) ++ X.factors (n := n)) :=
        hmerge.listEval_eq q
      _ = SPFactora.listEval (n := n) q
            (coordinates.factors (n := n)) *
          SPFactora.listEval (n := n) q
            (X.factors (n := n)) := by
        rw [SPFactora.listEval_append]
      _ = SPFactora.listEval (n := n) q
            (coordinates.factors (n := n)) *
          factor.eval (n := n) q := by
        rw [SPFactora.list_coordinate_expansions
          hn H hH factor hfactorTruncated (by omega) q]
      _ = SPFactora.listEval (n := n) q
            (coordinates.factors (n := n) ++ [factor]) := by
        rw [SPFactora.listEval_append]
        simp

end TSInserta

namespace TSInput

/--
A support-bounded semantic insertion kernel upgrades a correctly sourced list
to Claim 5 polynomial data.
-/
theorem supportedSemanticInsertion
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight input.source)
    (kernel :
      TSInserta
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight := by
  rcases kernel.exists_normalization input.source input.source_isTruncated
      hsourceSupported with
    ⟨coordinates, _hcoordinatesSupported, hcoordinates⟩
  exact
    CEData.toPolynomialData hinputWeight
      (collected_expansion_factors
        coordinates fun q => (hcoordinates q).trans (input.list_eval_source q))

end TSInput

end TCTex
end Submission
